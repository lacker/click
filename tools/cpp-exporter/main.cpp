#include <cstdint>
#include <limits>
#include <filesystem>
#include <memory>
#include <optional>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Index/USRGeneration.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

namespace {

constexpr const char *kClangVersion = "19.1.7";
constexpr const char *kStandard = "c++20";
constexpr const char *kTarget = "x86_64-unknown-linux-gnu";

struct Options {
  std::string logical_source;
  std::string function;
  std::string source;
};

struct ExportState {
  std::optional<llvm::json::Value> artifact;
  std::string error;
};

std::optional<Options> parse_options(int argc, const char **argv) {
  Options result;
  for (int index = 1; index < argc; index += 2) {
    if (index + 1 >= argc) {
      llvm::errs() << "error: every exporter option requires a value\n";
      return std::nullopt;
    }
    const std::string option = argv[index];
    const std::string value = argv[index + 1];
    if (option == "--logical-source") {
      result.logical_source = value;
    } else if (option == "--function") {
      result.function = value;
    } else if (option == "--source") {
      result.source = value;
    } else {
      llvm::errs() << "error: unknown exporter option `" << option << "`\n";
      return std::nullopt;
    }
  }
  if (result.logical_source.empty() || result.function.empty() ||
      result.source.empty()) {
    llvm::errs()
        << "error: --logical-source, --function, and --source are required\n";
    return std::nullopt;
  }
  return result;
}

class SemanticExporter : public clang::RecursiveASTVisitor<SemanticExporter> {
public:
  SemanticExporter(clang::ASTContext &context, std::string logical_source,
                   std::string selected_name, ExportState &state)
      : context_(context), source_manager_(context.getSourceManager()),
        logical_source_(std::move(logical_source)),
        selected_name_(std::move(selected_name)), state_(state) {}

  bool VisitFunctionDecl(clang::FunctionDecl *declaration) {
    if (!llvm::isa<clang::CXXMethodDecl>(declaration) &&
        declaration->isThisDeclarationADefinition() &&
        declaration->getNameAsString() == selected_name_ &&
        source_manager_.isWrittenInMainFile(
            source_manager_.getSpellingLoc(declaration->getLocation()))) {
      matches_.push_back(declaration);
    }
    return true;
  }

  void finish() {
    if (matches_.empty()) {
      fail({}, "selected function `" + selected_name_ + "` was not found");
      return;
    }
    if (matches_.size() != 1) {
      fail(matches_.front()->getLocation(),
           "selected function `" + selected_name_ + "` is overloaded");
      return;
    }
    const clang::FunctionDecl *selected = matches_.front()->getDefinition();
    if (selected == nullptr) {
      fail(matches_.front()->getLocation(),
           "selected function has no reachable definition");
      return;
    }
    known_functions_.insert(selected->getCanonicalDecl());
    auto function = lower_function(selected);
    if (!function) {
      return;
    }
    llvm::json::Array reachable_functions;
    for (std::size_t index = 0; index < reachable_definitions_.size(); ++index) {
      auto reachable = lower_function(reachable_definitions_[index]);
      if (!reachable) {
        return;
      }
      reachable_functions.push_back(std::move(*reachable));
    }
    llvm::json::Array records;
    for (const clang::CXXRecordDecl *record : record_definitions_) {
      auto lowered = lower_record(record);
      if (!lowered) {
        return;
      }
      records.push_back(std::move(*lowered));
    }

    llvm::json::Object profile;
    profile["frontend"] = "clang";
    profile["frontend_version"] = clang::getClangFullVersion();
    profile["standard"] = kStandard;
    profile["target"] = kTarget;
    profile["exceptions"] = false;
    profile["rtti"] = false;

    llvm::json::Object artifact;
    artifact["schema"] = 8;
    artifact["language"] = "c++";
    artifact["profile"] = std::move(profile);
    artifact["logical_source"] = logical_source_;
    artifact["records"] = std::move(records);
    artifact["function"] = std::move(*function);
    artifact["reachable_functions"] = std::move(reachable_functions);
    state_.artifact.emplace(std::move(artifact));
  }

private:
  using Json = llvm::json::Value;

  struct LoweredCall {
    llvm::json::Object callee;
    llvm::json::Array arguments;
    Json span;
  };

  struct LoweredMember {
    Json object;
    Json field;
  };

  std::optional<Json> lower_function(const clang::FunctionDecl *declaration) {
    const auto *constructor =
        llvm::dyn_cast<clang::CXXConstructorDecl>(declaration);
    const auto *prototype =
        declaration->getType()->getAs<clang::FunctionProtoType>();
    if (prototype == nullptr || !prototype->isNothrow()) {
      fail(declaration->getLocation(),
           "the first C++ slice requires an explicit noexcept function");
      return std::nullopt;
    }
    std::optional<Json> return_type;
    llvm::json::Object function_kind;
    if (constructor != nullptr) {
      const auto *record = constructor->getParent()->getDefinition();
      if (record == nullptr || !remember_record(record)) {
        return std::nullopt;
      }
      llvm::json::Object void_type;
      void_type["kind"] = "void";
      return_type.emplace(std::move(void_type));
      function_kind["kind"] = "constructor";
      function_kind["record_declaration_id"] = declaration_id(record);
      function_kind["record_name"] = record->getNameAsString();
    } else {
      return_type =
          lower_type(declaration->getReturnType(),
                     declaration->getReturnTypeSourceRange().getBegin());
      if (!return_type) {
        return std::nullopt;
      }
      function_kind["kind"] = "free";
    }
    llvm::json::Array parameters;
    if (constructor != nullptr) {
      const auto *record = constructor->getParent()->getDefinition();
      llvm::json::Object record_type;
      record_type["kind"] = "record";
      record_type["declaration_id"] = declaration_id(record);
      record_type["name"] = record->getNameAsString();
      llvm::json::Object reference_type;
      reference_type["kind"] = "lvalue_reference";
      reference_type["pointee"] = std::move(record_type);
      llvm::json::Object self;
      self["declaration_id"] = constructor_self_id(constructor);
      self["name"] = "self";
      self["value_type"] = std::move(reference_type);
      self["span"] = span(constructor->getNameInfo().getSourceRange());
      parameters.push_back(std::move(self));
    }
    for (const clang::ParmVarDecl *parameter : declaration->parameters()) {
      auto lowered = lower_parameter(parameter);
      if (!lowered) {
        return std::nullopt;
      }
      parameters.push_back(std::move(*lowered));
    }
    const auto *body =
        llvm::dyn_cast_or_null<clang::CompoundStmt>(declaration->getBody());
    if (body == nullptr || (body->body_empty() && constructor == nullptr)) {
      fail(declaration->getLocation(),
           "the supported C++ function requires a nonempty compound body");
      return std::nullopt;
    }

    llvm::json::Array statements;
    if (constructor != nullptr) {
      const auto *record = constructor->getParent()->getDefinition();
      for (const clang::FieldDecl *field : record->fields()) {
        const clang::CXXCtorInitializer *initializer = nullptr;
        for (const clang::CXXCtorInitializer *candidate : constructor->inits()) {
          if (candidate->isMemberInitializer() &&
              candidate->getMember() == field) {
            initializer = candidate;
            break;
          }
        }
        if (initializer == nullptr) {
          fail(constructor->getLocation(),
               "supported constructor is missing a validated member initializer");
          return std::nullopt;
        }
        auto value = lower_expression(initializer->getInit(), constructor);
        if (!value) {
          return std::nullopt;
        }
        llvm::json::Object object;
        object["declaration_id"] = constructor_self_id(constructor);
        object["name"] = "self";
        object["span"] = span(constructor->getNameInfo().getSourceRange());
        llvm::json::Object field_reference;
        field_reference["record_declaration_id"] = declaration_id(record);
        field_reference["declaration_id"] = declaration_id(field);
        field_reference["name"] = field->getNameAsString();
        field_reference["span"] = span(field->getSourceRange());
        llvm::json::Object statement;
        statement["kind"] = "member_store";
        statement["object"] = std::move(object);
        statement["field"] = std::move(field_reference);
        statement["value"] = std::move(*value);
        statement["span"] = span(initializer->getSourceRange());
        statements.push_back(std::move(statement));
      }
    }
    for (const clang::Stmt *statement : body->body()) {
      auto lowered = lower_statement(statement, declaration, true);
      if (!lowered) {
        return std::nullopt;
      }
      statements.push_back(std::move(*lowered));
    }

    llvm::json::Object result;
    result["declaration_id"] = declaration_id(declaration);
    result["name"] = constructor == nullptr
                         ? declaration->getNameAsString()
                         : constructor_name(constructor);
    result["function_kind"] = std::move(function_kind);
    result["return_type"] = std::move(*return_type);
    result["parameters"] = std::move(parameters);
    result["is_noexcept"] = true;
    result["span"] = span(declaration->getSourceRange());
    result["body"] = std::move(statements);
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<Json> lower_parameter(const clang::ParmVarDecl *parameter) {
    const auto *reference =
        parameter->getType()->getAs<clang::LValueReferenceType>();
    const bool int_reference =
        reference != nullptr &&
        !reference->getPointeeType().isVolatileQualified() &&
        !reference->getPointeeType().isRestrictQualified() &&
        context_.hasSameType(reference->getPointeeType().getUnqualifiedType(),
                             context_.IntTy);
    const clang::CXXRecordDecl *record_reference = nullptr;
    if (reference != nullptr && !reference->getPointeeType().hasQualifiers()) {
      if (const auto *record_type =
              reference->getPointeeType()->getAs<clang::RecordType>()) {
        record_reference = llvm::dyn_cast<clang::CXXRecordDecl>(
            record_type->getDecl()->getDefinition());
      }
    }
    const auto *pointer = parameter->getType()->getAs<clang::PointerType>();
    const bool mutable_int_pointer =
        pointer != nullptr && !parameter->getType().hasQualifiers() &&
        !pointer->getPointeeType().hasQualifiers() &&
        context_.hasSameType(pointer->getPointeeType().getUnqualifiedType(),
                             context_.IntTy);
    const bool by_value_bool =
        reference == nullptr &&
        context_.hasSameType(parameter->getType().getUnqualifiedType(),
                             context_.BoolTy) &&
        !parameter->getType().isConstQualified();
    if (!int_reference && record_reference == nullptr &&
        !mutable_int_pointer && !by_value_bool) {
      fail(parameter->getLocation(),
           "the supported C++ parameter must be a by-value bool, int&, const int&, or mutable int* parameter, or a mutable simple-record reference parameter");
      return std::nullopt;
    }
    if (record_reference != nullptr && !remember_record(record_reference)) {
      return std::nullopt;
    }
    auto value_type =
        lower_type(parameter->getType(), parameter->getLocation());
    if (!value_type) {
      return std::nullopt;
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(parameter);
    result["name"] = parameter->getNameAsString();
    result["value_type"] = std::move(*value_type);
    result["span"] = span(parameter->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<Json> lower_type(clang::QualType type,
                                 clang::SourceLocation location) {
    if (const auto *reference = type->getAs<clang::LValueReferenceType>()) {
      auto pointee = lower_type(reference->getPointeeType(), location);
      if (!pointee) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "lvalue_reference";
      result["pointee"] = std::move(*pointee);
      return Json(std::move(result));
    }
    if (const auto *pointer = type->getAs<clang::PointerType>()) {
      auto pointee = lower_type(pointer->getPointeeType(), location);
      if (!pointee) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "pointer";
      result["pointee"] = std::move(*pointee);
      return Json(std::move(result));
    }
    if (const auto *record_type = type->getAs<clang::RecordType>()) {
      const auto *record = llvm::dyn_cast<clang::CXXRecordDecl>(
          record_type->getDecl()->getDefinition());
      if (type.hasQualifiers() || record == nullptr ||
          !remember_record(record)) {
        if (record == nullptr && state_.error.empty()) {
          fail(location, "the supported C++ record type must be complete");
        } else if (type.hasQualifiers() && state_.error.empty()) {
          fail(location,
               "qualified C++ record objects are outside the supported slice");
        }
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "record";
      result["declaration_id"] = declaration_id(record);
      result["name"] = record->getNameAsString();
      return Json(std::move(result));
    }
    if (context_.hasSameType(type.getUnqualifiedType(), context_.BoolTy)) {
      llvm::json::Object result;
      result["kind"] = "boolean";
      result["bits"] = static_cast<std::int64_t>(context_.getTypeSize(type));
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (!context_.hasSameType(type.getUnqualifiedType(), context_.IntTy)) {
      fail(location,
           "the supported C++ slice supports bool, int, int&, mutable int*, and one simple record-reference type");
      return std::nullopt;
    }
    llvm::json::Object result;
    result["kind"] = "integer";
    result["bits"] = static_cast<std::int64_t>(context_.getTypeSize(type));
    result["signed"] = type->isSignedIntegerType();
    result["is_const"] = type.isConstQualified();
    return Json(std::move(result));
  }

  std::optional<Json> lower_statement(const clang::Stmt *statement,
                                      const clang::FunctionDecl *function,
                                      bool allow_local_declaration) {
    if (const auto *declaration = llvm::dyn_cast<clang::DeclStmt>(statement)) {
      if (!allow_local_declaration) {
        fail(declaration->getBeginLoc(),
             "automatic C++ locals are currently supported only in the function body");
        return std::nullopt;
      }
      return lower_local_declaration(declaration, function);
    }
    if (const auto *call = llvm::dyn_cast<clang::CallExpr>(statement)) {
      return lower_call(call, function);
    }
    if (const auto *binary = llvm::dyn_cast<clang::BinaryOperator>(statement)) {
      if (binary->getOpcode() != clang::BO_Assign) {
        fail(binary->getOperatorLoc(),
             "the first C++ slice supports only simple assignment statements");
        return std::nullopt;
      }
      auto value = lower_expression(binary->getRHS(), function);
      if (!value) {
        return std::nullopt;
      }
      llvm::json::Object result;
      const clang::Expr *left = binary->getLHS()->IgnoreParens();
      if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(left)) {
        auto lowered = lower_member(member, function);
        if (!lowered) {
          return std::nullopt;
        }
        result["kind"] = "member_store";
        result["object"] = std::move(lowered->object);
        result["field"] = std::move(lowered->field);
      } else if (const auto *dereference =
                     llvm::dyn_cast<clang::UnaryOperator>(left);
          dereference != nullptr && dereference->getOpcode() == clang::UO_Deref) {
        auto pointer = lower_expression(dereference->getSubExpr(), function);
        if (!pointer) {
          return std::nullopt;
        }
        result["kind"] = "store";
        result["pointer"] = std::move(*pointer);
      } else {
        auto target = lower_place_reference(left, function);
        if (!target) {
          return std::nullopt;
        }
        result["kind"] = "assign";
        result["target"] = std::move(*target);
      }
      result["value"] = std::move(*value);
      result["span"] = span(binary->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *returned = llvm::dyn_cast<clang::ReturnStmt>(statement)) {
      if (returned->getRetValue() == nullptr) {
        fail(returned->getReturnLoc(),
             "the first C++ slice requires an int return value");
        return std::nullopt;
      }
      auto value = lower_expression(returned->getRetValue(), function);
      if (!value) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "return";
      result["value"] = std::move(*value);
      result["span"] = span(returned->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *conditional = llvm::dyn_cast<clang::IfStmt>(statement)) {
      if (conditional->getInit() != nullptr ||
          conditional->getConditionVariable() != nullptr) {
        fail(conditional->getIfLoc(),
             "the supported C++ if statement cannot declare an initializer or condition variable");
        return std::nullopt;
      }
      auto condition = lower_expression(conditional->getCond(), function);
      auto then_branch = lower_branch(conditional->getThen(), function);
      auto else_branch = lower_branch(conditional->getElse(), function);
      if (!condition || !then_branch || !else_branch) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "if";
      result["condition"] = std::move(*condition);
      result["then_branch"] = std::move(*then_branch);
      result["else_branch"] = std::move(*else_branch);
      result["span"] = span(conditional->getSourceRange());
      return Json(std::move(result));
    }
    fail(statement->getBeginLoc(),
         "unsupported statement in the first C++ slice");
    return std::nullopt;
  }

  std::optional<Json> lower_call(const clang::CallExpr *call,
                                 const clang::FunctionDecl *caller) {
    auto lowered = lower_call_operation(call, caller);
    if (!lowered) {
      return std::nullopt;
    }
    llvm::json::Object result;
    result["kind"] = "call";
    result["callee"] = std::move(lowered->callee);
    result["arguments"] = std::move(lowered->arguments);
    result["span"] = std::move(lowered->span);
    return Json(std::move(result));
  }

  std::optional<Json>
  lower_local_declaration(const clang::DeclStmt *statement,
                          const clang::FunctionDecl *function) {
    if (!statement->isSingleDecl()) {
      fail(statement->getBeginLoc(),
           "the supported C++ local declaration must declare exactly one variable");
      return std::nullopt;
    }
    const auto *local =
        llvm::dyn_cast<clang::VarDecl>(statement->getSingleDecl());
    if (local == nullptr || !local->hasLocalStorage() || local->isStaticLocal()) {
      fail(statement->getBeginLoc(),
           "the supported C++ local must have automatic storage");
      return std::nullopt;
    }
    const bool mutable_int =
        context_.hasSameType(local->getType().getUnqualifiedType(),
                             context_.IntTy) &&
        !local->getType().isConstQualified();
    const auto *record_type = local->getType()->getAs<clang::RecordType>();
    const auto *record =
        record_type == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::CXXRecordDecl>(
                  record_type->getDecl()->getDefinition());
    const bool record_object =
        record != nullptr && !local->getType().hasQualifiers();
    if (!mutable_int && !record_object) {
      fail(local->getLocation(),
           "the supported automatic C++ local must resolve to mutable int or one simple record object");
      return std::nullopt;
    }
    if (!local->hasInit()) {
      fail(local->getLocation(),
           record_object
               ? "a supported C++ record local requires direct aggregate or constructor initialization"
               : "the supported automatic C++ local requires an initializer");
      return std::nullopt;
    }
    if (record_object) {
      const clang::FunctionDecl *canonical = function->getCanonicalDecl();
      if (!functions_with_aggregate_local_.insert(canonical).second) {
        fail(local->getLocation(),
             "the first C++ aggregate-local slice permits one object per function");
        return std::nullopt;
      }
      if (!remember_record(record)) {
        return std::nullopt;
      }
    }

    auto value_type = lower_type(local->getType(), local->getLocation());
    if (!value_type) {
      return std::nullopt;
    }
    llvm::json::Object place;
    place["declaration_id"] = declaration_id(local);
    place["name"] = local->getNameAsString();
    place["value_type"] = std::move(*value_type);
    place["span"] = span(local->getSourceRange());

    llvm::json::Object initializer;
    const clang::Expr *source_initializer = local->getInit();
    const clang::Expr *semantic_initializer =
        source_initializer->IgnoreParenImpCasts();
    if (record_object && record->isAggregate()) {
      const auto *semantic_list =
          llvm::dyn_cast<clang::InitListExpr>(source_initializer);
      const clang::InitListExpr *syntactic_list = semantic_list;
      if (semantic_list != nullptr && semantic_list->getSyntacticForm() != nullptr) {
        syntactic_list = semantic_list->getSyntacticForm();
      }
      const unsigned field_count = std::distance(record->field_begin(),
                                                 record->field_end());
      if (local->getInitStyle() != clang::VarDecl::ListInit ||
          syntactic_list == nullptr || syntactic_list->getNumInits() != field_count) {
        fail(source_initializer->getExprLoc(),
             "a supported C++ aggregate local requires one direct brace initializer per field in declaration order");
        return std::nullopt;
      }
      llvm::json::Array fields;
      unsigned index = 0;
      for (const clang::FieldDecl *field : record->fields()) {
        const clang::Expr *field_source = syntactic_list->getInit(index++);
        const clang::Expr *field_semantic =
            semantic_list->getInit(index - 1);
        auto value = lower_expression(field_semantic, function);
        if (!value) {
          return std::nullopt;
        }
        llvm::json::Object field_reference;
        field_reference["record_declaration_id"] = declaration_id(record);
        field_reference["declaration_id"] = declaration_id(field);
        field_reference["name"] = field->getNameAsString();
        field_reference["span"] = span(field->getSourceRange());
        llvm::json::Object field_initializer;
        field_initializer["field"] = std::move(field_reference);
        field_initializer["value"] = std::move(*value);
        field_initializer["span"] = span(field_source->getSourceRange());
        fields.push_back(std::move(field_initializer));
      }
      initializer["kind"] = "aggregate";
      initializer["fields"] = std::move(fields);
      initializer["span"] = span(source_initializer->getSourceRange());
    } else if (record_object) {
      const auto *construction =
          llvm::dyn_cast<clang::CXXConstructExpr>(semantic_initializer);
      const clang::CXXConstructorDecl *constructor =
          construction == nullptr ? nullptr : construction->getConstructor();
      const auto *definition = constructor == nullptr
                                   ? nullptr
                                   : llvm::dyn_cast_or_null<clang::CXXConstructorDecl>(
                                         constructor->getDefinition());
      if (local->getInitStyle() != clang::VarDecl::CallInit ||
          construction == nullptr || definition == nullptr ||
          construction->getConstructionKind() != clang::CXXConstructionKind::Complete ||
          definition->getParent()->getCanonicalDecl() !=
              record->getCanonicalDecl() ||
          construction->getNumArgs() != definition->getNumParams()) {
        fail(source_initializer->getExprLoc(),
             "a supported C++ object local requires one direct parenthesized call to its explicit constructor");
        return std::nullopt;
      }
      llvm::json::Array arguments;
      for (unsigned index = 0; index < construction->getNumArgs(); ++index) {
        auto argument = lower_call_argument(construction->getArg(index),
                                            definition->getParamDecl(index),
                                            function);
        if (!argument) {
          return std::nullopt;
        }
        arguments.push_back(std::move(*argument));
      }
      const clang::FunctionDecl *canonical = definition->getCanonicalDecl();
      if (known_functions_.insert(canonical).second) {
        reachable_definitions_.push_back(definition);
      }
      llvm::json::Object reference;
      reference["declaration_id"] = declaration_id(definition);
      reference["name"] = constructor_name(definition);
      reference["span"] = span(source_initializer->getSourceRange());
      initializer["kind"] = "constructor";
      initializer["callee"] = std::move(reference);
      initializer["arguments"] = std::move(arguments);
      initializer["span"] = span(source_initializer->getSourceRange());
    } else if (const auto *call =
            llvm::dyn_cast<clang::CallExpr>(semantic_initializer)) {
      auto lowered = lower_call_operation(call, function);
      if (!lowered) {
        return std::nullopt;
      }
      initializer["kind"] = "call";
      initializer["callee"] = std::move(lowered->callee);
      initializer["arguments"] = std::move(lowered->arguments);
      initializer["span"] = std::move(lowered->span);
    } else {
      auto value = lower_expression(source_initializer, function);
      if (!value) {
        return std::nullopt;
      }
      initializer["kind"] = "value";
      initializer["value"] = std::move(*value);
    }

    llvm::json::Object result;
    result["kind"] = "declare";
    result["local"] = std::move(place);
    result["initializer"] = std::move(initializer);
    result["span"] = span(statement->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<LoweredCall>
  lower_call_operation(const clang::CallExpr *call,
                       const clang::FunctionDecl *caller) {
    const clang::FunctionDecl *callee = call->getDirectCallee();
    if (callee == nullptr) {
      fail(call->getExprLoc(),
           "the supported C++ slice requires a direct free-function call");
      return std::nullopt;
    }
    if (llvm::isa<clang::CXXMethodDecl>(callee)) {
      fail(call->getExprLoc(),
           "C++ method calls are outside the supported direct-call slice");
      return std::nullopt;
    }
    const clang::FunctionDecl *definition = callee->getDefinition();
    if (definition == nullptr) {
      fail(call->getExprLoc(),
           "direct C++ call has no reachable function definition");
      return std::nullopt;
    }
    const clang::SourceLocation definition_location =
        source_manager_.getSpellingLoc(definition->getLocation());
    if (!source_manager_.isWrittenInMainFile(definition_location)) {
      fail(call->getExprLoc(),
           "the supported C++ call graph requires definitions in the selected file");
      return std::nullopt;
    }
    if (call->getNumArgs() != definition->getNumParams()) {
      fail(call->getExprLoc(),
           "the supported C++ slice requires a call with one argument per parameter");
      return std::nullopt;
    }

    llvm::json::Array arguments;
    for (unsigned index = 0; index < call->getNumArgs(); ++index) {
      auto argument = lower_call_argument(call->getArg(index),
                                          definition->getParamDecl(index), caller);
      if (!argument) {
        return std::nullopt;
      }
      arguments.push_back(std::move(*argument));
    }

    const clang::FunctionDecl *canonical = definition->getCanonicalDecl();
    if (known_functions_.insert(canonical).second) {
      reachable_definitions_.push_back(definition);
    }

    llvm::json::Object reference;
    reference["declaration_id"] = declaration_id(definition);
    reference["name"] = definition->getNameAsString();
    reference["span"] = span(call->getCallee()->getSourceRange());

    Json call_span = span(call->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return LoweredCall{std::move(reference), std::move(arguments),
                       std::move(call_span)};
  }

  std::optional<Json>
  lower_call_argument(const clang::Expr *argument,
                      const clang::ParmVarDecl *parameter,
                      const clang::FunctionDecl *caller) {
    llvm::json::Object result;
    if (parameter->getType()->getAs<clang::LValueReferenceType>() != nullptr) {
      auto place = lower_place_reference(argument, caller);
      if (!place) {
        return std::nullopt;
      }
      result["kind"] = "reference";
      result["place"] = std::move(*place);
      return Json(std::move(result));
    }
    if (parameter->getType()->getAs<clang::PointerType>() != nullptr) {
      auto value = lower_expression(argument, caller);
      if (!value) {
        return std::nullopt;
      }
      result["kind"] = "value";
      result["value"] = std::move(*value);
      return Json(std::move(result));
    }
    if (context_.hasSameType(parameter->getType().getUnqualifiedType(),
                             context_.BoolTy) &&
        !parameter->getType().isConstQualified()) {
      auto value = lower_expression(argument, caller);
      if (!value) {
        return std::nullopt;
      }
      result["kind"] = "value";
      result["value"] = std::move(*value);
      return Json(std::move(result));
    }
    fail(argument->getExprLoc(),
         "unsupported argument in the direct C++ call slice");
    return std::nullopt;
  }

  std::optional<llvm::json::Array>
  lower_branch(const clang::Stmt *statement,
               const clang::FunctionDecl *function) {
    llvm::json::Array result;
    if (statement == nullptr) {
      return result;
    }
    if (const auto *compound = llvm::dyn_cast<clang::CompoundStmt>(statement)) {
      for (const clang::Stmt *member : compound->body()) {
        auto lowered = lower_statement(member, function, false);
        if (!lowered) {
          return std::nullopt;
        }
        result.push_back(std::move(*lowered));
      }
      return result;
    }
    auto lowered = lower_statement(statement, function, false);
    if (!lowered) {
      return std::nullopt;
    }
    result.push_back(std::move(*lowered));
    return result;
  }

  std::optional<Json> lower_expression(const clang::Expr *expression,
                                       const clang::FunctionDecl *function) {
    if (const auto *parentheses =
            llvm::dyn_cast<clang::ParenExpr>(expression)) {
      return lower_expression(parentheses->getSubExpr(), function);
    }
    if (const auto *cast =
            llvm::dyn_cast<clang::ImplicitCastExpr>(expression)) {
      if (cast->getCastKind() != clang::CK_LValueToRValue) {
        fail(cast->getExprLoc(),
             "unsupported implicit conversion in the first C++ slice");
        return std::nullopt;
      }
      auto value_type = lower_type(cast->getType(), cast->getExprLoc());
      if (!value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      const clang::Expr *source = cast->getSubExpr()->IgnoreParens();
      if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(source)) {
        auto lowered = lower_member(member, function);
        if (!lowered) {
          return std::nullopt;
        }
        result["kind"] = "member_load";
        result["object"] = std::move(lowered->object);
        result["field"] = std::move(lowered->field);
      } else if (const auto *dereference =
              llvm::dyn_cast<clang::UnaryOperator>(source);
          dereference != nullptr && dereference->getOpcode() == clang::UO_Deref) {
        auto pointer = lower_expression(dereference->getSubExpr(), function);
        if (!pointer) {
          return std::nullopt;
        }
        result["kind"] = "dereference";
        result["pointer"] = std::move(*pointer);
      } else {
        auto place = lower_place_reference(source, function);
        if (!place) {
          return std::nullopt;
        }
        result["kind"] = "load";
        result["place"] = std::move(*place);
      }
      result["value_type"] = std::move(*value_type);
      result["span"] = span(cast->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *address = llvm::dyn_cast<clang::UnaryOperator>(expression);
        address != nullptr && address->getOpcode() == clang::UO_AddrOf) {
      const clang::Expr *operand = address->getSubExpr()->IgnoreParenImpCasts();
      const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(operand);
      const auto *parameter =
          reference == nullptr
              ? nullptr
              : llvm::dyn_cast<clang::ParmVarDecl>(reference->getDecl());
      const auto *reference_type =
          parameter == nullptr
              ? nullptr
              : parameter->getType()->getAs<clang::LValueReferenceType>();
      if (parameter == nullptr || parameter->getDeclContext() != function ||
          reference_type == nullptr ||
          reference_type->getPointeeType().isConstQualified() ||
          !context_.hasSameType(
              reference_type->getPointeeType().getUnqualifiedType(),
              context_.IntTy)) {
        fail(address->getOperatorLoc(),
             "supported C++ address-of must name a mutable int& parameter");
        return std::nullopt;
      }
      auto place = lower_place_reference(operand, function);
      auto value_type = lower_type(address->getType(), address->getExprLoc());
      if (!place || !value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "address_of";
      result["place"] = std::move(*place);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(address->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *literal =
            llvm::dyn_cast<clang::IntegerLiteral>(expression)) {
      auto value_type = lower_type(literal->getType(), literal->getExprLoc());
      if (!value_type) {
        return std::nullopt;
      }
      llvm::SmallString<32> value;
      literal->getValue().toString(value, 10, true);
      llvm::json::Object result;
      result["kind"] = "integer_literal";
      result["value"] = value.str().str();
      result["value_type"] = std::move(*value_type);
      result["span"] = span(literal->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *binary =
            llvm::dyn_cast<clang::BinaryOperator>(expression)) {
      if (binary->getOpcode() != clang::BO_Add) {
        fail(binary->getOperatorLoc(),
             "unsupported binary operator in the first C++ slice");
        return std::nullopt;
      }
      if (!context_.hasSameType(binary->getType().getUnqualifiedType(),
                                context_.IntTy)) {
        fail(binary->getOperatorLoc(),
             "the supported C++ slice does not include pointer arithmetic");
        return std::nullopt;
      }
      auto left = lower_expression(binary->getLHS(), function);
      auto right = lower_expression(binary->getRHS(), function);
      auto value_type = lower_type(binary->getType(), binary->getExprLoc());
      if (!left || !right || !value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "binary";
      result["operator"] = "add";
      result["left"] = std::move(*left);
      result["right"] = std::move(*right);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(binary->getSourceRange());
      return Json(std::move(result));
    }
    fail(expression->getExprLoc(),
         "unsupported expression in the first C++ slice");
    return std::nullopt;
  }

  bool remember_record(const clang::CXXRecordDecl *record) {
    const clang::CXXRecordDecl *definition =
        record == nullptr ? nullptr : record->getDefinition();
    if (definition == nullptr) {
      fail({}, "the supported C++ record type must be complete");
      return false;
    }
    const clang::CXXRecordDecl *canonical = definition->getCanonicalDecl();
    if (!known_records_.empty() && known_records_.count(canonical) == 0) {
      fail(definition->getLocation(),
           "the first C++ object slice supports exactly one record type");
      return false;
    }
    if (known_records_.insert(canonical).second) {
      if (!validate_record(definition)) {
        return false;
      }
      record_definitions_.push_back(definition);
    }
    return true;
  }

  bool validate_record(const clang::CXXRecordDecl *record) {
    if (!record->isStruct() || record->getName().empty()) {
      fail(record->getLocation(),
           "the supported C++ record must be a named struct");
      return false;
    }
    if (!source_manager_.isWrittenInMainFile(
            source_manager_.getSpellingLoc(record->getLocation()))) {
      fail(record->getLocation(),
           "the supported C++ record must be declared in the selected file");
      return false;
    }
    if (!record->isStandardLayout() || !record->isTriviallyCopyable() ||
        !record->hasTrivialDestructor() || record->getNumBases() != 0) {
      fail(record->getLocation(),
           "the supported C++ record must be standard-layout and trivially-copyable, have trivial destruction, and have no bases");
      return false;
    }
    if (record->field_empty()) {
      fail(record->getLocation(),
           "the supported C++ record must contain at least one field");
      return false;
    }
    const clang::CXXConstructorDecl *supported_constructor = nullptr;
    for (const clang::Decl *member : record->decls()) {
      if (const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(member);
          method != nullptr && !method->isImplicit()) {
        if (const auto *constructor =
                llvm::dyn_cast<clang::CXXConstructorDecl>(method)) {
          if (supported_constructor != nullptr) {
            fail(constructor->getLocation(),
                 "the first constructor slice supports exactly one explicit constructor");
            return false;
          }
          supported_constructor = constructor;
        } else {
          fail(method->getLocation(),
               "methods and user-declared destructors are outside the constructor-only C++ slice; destruction must remain trivial and implicit");
          return false;
        }
      }
      if (!member->isImplicit() && !llvm::isa<clang::FieldDecl>(member) &&
          !llvm::isa<clang::CXXMethodDecl>(member) &&
          !llvm::isa<clang::AccessSpecDecl>(member)) {
        fail(member->getLocation(),
             "nested declarations and static data members are outside the supported C++ record slice");
        return false;
      }
    }
    if (supported_constructor != nullptr &&
        !validate_constructor(supported_constructor, record)) {
      return false;
    }
    for (const clang::FieldDecl *field : record->fields()) {
      const clang::QualType type = field->getType();
      const auto *pointer = type->getAs<clang::PointerType>();
      const bool mutable_int =
          !type.hasQualifiers() &&
          context_.hasSameType(type.getUnqualifiedType(), context_.IntTy);
      const bool mutable_int_pointer =
          pointer != nullptr && !type.hasQualifiers() &&
          !pointer->getPointeeType().hasQualifiers() &&
          context_.hasSameType(pointer->getPointeeType().getUnqualifiedType(),
                               context_.IntTy);
      if (field->getAccess() != clang::AS_public || field->isBitField() ||
          field->isMutable() || field->hasInClassInitializer() ||
          field->getName().empty() ||
          (!mutable_int && !mutable_int_pointer)) {
        fail(field->getLocation(),
             "the supported C++ record fields must be named public mutable int or mutable int* fields without bit-fields");
        return false;
      }
    }
    return true;
  }

  bool validate_constructor(const clang::CXXConstructorDecl *constructor,
                            const clang::CXXRecordDecl *record) {
    const auto *prototype =
        constructor->getType()->getAs<clang::FunctionProtoType>();
    if (!constructor->isExplicit() || constructor->getAccess() != clang::AS_public ||
        constructor->isDefaultConstructor() ||
        constructor->isCopyOrMoveConstructor() ||
        constructor->isDelegatingConstructor() || constructor->isVariadic() ||
        prototype == nullptr || !prototype->isNothrow()) {
      fail(constructor->getLocation(),
           "the supported constructor must be one public explicit non-default noexcept constructor without copying, moving, delegation, or variadic arguments");
      return false;
    }
    if (!constructor->doesThisDeclarationHaveABody() ||
        constructor->getDefinition() != constructor ||
        !source_manager_.isWrittenInMainFile(source_manager_.getSpellingLoc(
            constructor->getLocation()))) {
      fail(constructor->getLocation(),
           "the supported constructor must have an inline definition in the selected file");
      return false;
    }
    for (const clang::ParmVarDecl *parameter : constructor->parameters()) {
      if (parameter->hasDefaultArg()) {
        fail(parameter->getLocation(),
             "default constructor arguments are outside the supported slice");
        return false;
      }
    }

    const unsigned field_count =
        std::distance(record->field_begin(), record->field_end());
    if (constructor->getNumCtorInitializers() != field_count) {
      fail(constructor->getLocation(),
           "the supported constructor must explicitly initialize every field in declaration order");
      return false;
    }
    std::vector<const clang::CXXCtorInitializer *> source_order(field_count,
                                                                nullptr);
    for (const clang::CXXCtorInitializer *initializer : constructor->inits()) {
      const unsigned order = initializer->getSourceOrder();
      if (!initializer->isWritten() || !initializer->isMemberInitializer() ||
          order >= field_count || source_order[order] != nullptr) {
        fail(constructor->getLocation(),
             "the supported constructor must use one written member initializer per field");
        return false;
      }
      source_order[order] = initializer;
    }
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      if (source_order[index] == nullptr ||
          source_order[index]->getMember() != field) {
        fail(source_order[index] == nullptr
                 ? constructor->getLocation()
                 : source_order[index]->getSourceLocation(),
             "the supported constructor member initializer list must follow declaration order");
        return false;
      }
      ++index;
    }
    return true;
  }

  std::optional<Json> lower_record(const clang::CXXRecordDecl *record) {
    const clang::ASTRecordLayout &layout = context_.getASTRecordLayout(record);
    const std::uint64_t size = layout.getSize().getQuantity();
    const std::uint64_t alignment = layout.getAlignment().getQuantity();
    if (size > std::numeric_limits<std::uint32_t>::max() ||
        alignment > std::numeric_limits<std::uint32_t>::max()) {
      fail(record->getLocation(), "supported C++ record layout is too large");
      return std::nullopt;
    }
    llvm::json::Array fields;
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      const std::uint64_t bit_offset = layout.getFieldOffset(index++);
      const std::uint64_t field_size =
          context_.getTypeSizeInChars(field->getType()).getQuantity();
      if (bit_offset % 8 != 0 ||
          bit_offset / 8 > std::numeric_limits<std::uint32_t>::max() ||
          field_size > std::numeric_limits<std::uint32_t>::max()) {
        fail(field->getLocation(), "supported C++ field layout is too large");
        return std::nullopt;
      }
      auto value_type = lower_type(field->getType(), field->getLocation());
      if (!value_type) {
        return std::nullopt;
      }
      llvm::json::Object lowered;
      lowered["declaration_id"] = declaration_id(field);
      lowered["name"] = field->getNameAsString();
      lowered["value_type"] = std::move(*value_type);
      lowered["offset_bytes"] = static_cast<std::int64_t>(bit_offset / 8);
      lowered["size_bytes"] = static_cast<std::int64_t>(field_size);
      lowered["span"] = span(field->getSourceRange());
      fields.push_back(std::move(lowered));
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(record);
    result["name"] = record->getNameAsString();
    result["size_bytes"] = static_cast<std::int64_t>(size);
    result["alignment_bytes"] = static_cast<std::int64_t>(alignment);
    result["fields"] = std::move(fields);
    result["span"] = span(record->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<LoweredMember>
  lower_member(const clang::MemberExpr *member,
               const clang::FunctionDecl *function) {
    const auto *field = llvm::dyn_cast<clang::FieldDecl>(member->getMemberDecl());
    const auto *record = field == nullptr
                             ? nullptr
                             : llvm::dyn_cast<clang::CXXRecordDecl>(
                                   field->getParent()->getDefinition());
    if (field == nullptr || record == nullptr || !remember_record(record)) {
      if (field == nullptr && state_.error.empty()) {
        fail(member->getMemberLoc(),
             "the supported C++ member access must resolve to a data field");
      }
      return std::nullopt;
    }
    const clang::Expr *base = member->getBase()->IgnoreParenImpCasts();
    const auto *this_expression = llvm::dyn_cast<clang::CXXThisExpr>(base);
    const auto *constructor =
        llvm::dyn_cast<clang::CXXConstructorDecl>(function);
    const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(base);
    const auto *parameter = reference == nullptr
                                ? nullptr
                                : llvm::dyn_cast<clang::ParmVarDecl>(
                                      reference->getDecl());
    const auto *local = reference == nullptr
                            ? nullptr
                            : llvm::dyn_cast<clang::VarDecl>(
                                  reference->getDecl());
    const auto *reference_type =
        parameter == nullptr
            ? nullptr
            : parameter->getType()->getAs<clang::LValueReferenceType>();
    const auto *base_record_type =
        reference_type == nullptr
            ? nullptr
            : reference_type->getPointeeType()->getAs<clang::RecordType>();
    const auto *local_record_type =
        local == nullptr ? nullptr : local->getType()->getAs<clang::RecordType>();
    const bool supported_parameter =
        parameter != nullptr && parameter->getDeclContext() == function &&
        reference_type != nullptr &&
        !reference_type->getPointeeType().hasQualifiers() &&
        base_record_type != nullptr &&
        base_record_type->getDecl()->getCanonicalDecl() ==
            record->getCanonicalDecl();
    const bool supported_local =
        local != nullptr && parameter == nullptr &&
        local->getDeclContext() == function && local->hasLocalStorage() &&
        !local->isStaticLocal() && !local->getType().hasQualifiers() &&
        local_record_type != nullptr &&
        local_record_type->getDecl()->getCanonicalDecl() ==
            record->getCanonicalDecl();
    const bool supported_this =
        this_expression != nullptr && constructor != nullptr &&
        constructor->getParent()->getCanonicalDecl() ==
            record->getCanonicalDecl();
    if (member->isArrow() && !supported_this) {
      fail(member->getOperatorLoc(),
           "the first C++ object slice supports arrow access only for the current constructor object");
      return std::nullopt;
    }
    if (!supported_parameter && !supported_local && !supported_this) {
      fail(member->getMemberLoc(),
           "supported C++ member access must use the current constructor object, a mutable record-reference parameter, or a supported record local directly");
      return std::nullopt;
    }
    auto object = lower_place_reference(base, function);
    if (!object) {
      return std::nullopt;
    }
    llvm::json::Object lowered_field;
    lowered_field["record_declaration_id"] = declaration_id(record);
    lowered_field["declaration_id"] = declaration_id(field);
    lowered_field["name"] = field->getNameAsString();
    lowered_field["span"] = span(member->getMemberNameInfo().getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return LoweredMember{std::move(*object), Json(std::move(lowered_field))};
  }

  std::optional<Json>
  lower_place_reference(const clang::Expr *expression,
                        const clang::FunctionDecl *expected_function) {
    expression = expression->IgnoreParenImpCasts();
    if (llvm::isa<clang::CXXThisExpr>(expression)) {
      const auto *constructor =
          llvm::dyn_cast<clang::CXXConstructorDecl>(expected_function);
      if (constructor == nullptr) {
        fail(expression->getExprLoc(),
             "`this` is supported only inside a constructor body");
        return std::nullopt;
      }
      llvm::json::Object result;
      result["declaration_id"] = constructor_self_id(constructor);
      result["name"] = "self";
      result["span"] = span(constructor->getNameInfo().getSourceRange());
      return Json(std::move(result));
    }
    const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(expression);
    const auto *place =
        reference == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::ValueDecl>(reference->getDecl());
    const auto *variable = llvm::dyn_cast_or_null<clang::VarDecl>(place);
    const bool supported_parameter =
        llvm::isa_and_nonnull<clang::ParmVarDecl>(place);
    const bool supported_local =
        variable != nullptr && !supported_parameter &&
        variable->hasLocalStorage() && !variable->isStaticLocal();
    if (place == nullptr || place->getDeclContext() != expected_function ||
        (!supported_parameter && !supported_local)) {
      fail(expression->getExprLoc(),
           "the supported C++ slice can access only current function parameters and automatic locals");
      return std::nullopt;
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(place);
    result["name"] = place->getNameAsString();
    result["span"] = span(reference->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::string declaration_id(const clang::Decl *declaration) {
    llvm::SmallString<128> result;
    if (clang::index::generateUSRForDecl(declaration, result)) {
      fail(declaration->getLocation(),
           "Clang could not produce a stable declaration identity");
      return {};
    }
    return result.str().str();
  }

  std::string constructor_self_id(
      const clang::CXXConstructorDecl *constructor) {
    return declaration_id(constructor) + "@this";
  }

  std::string constructor_name(
      const clang::CXXConstructorDecl *constructor) const {
    return constructor->getParent()->getNameAsString() + "_constructor";
  }

  Json span(clang::SourceRange range) {
    clang::SourceLocation begin =
        source_manager_.getSpellingLoc(range.getBegin());
    clang::SourceLocation end = source_manager_.getSpellingLoc(range.getEnd());
    if (!begin.isValid() || !end.isValid() ||
        !source_manager_.isWrittenInMainFile(begin) ||
        !source_manager_.isWrittenInMainFile(end)) {
      fail(
          begin,
          "the first C++ slice requires source locations in the selected file");
      return Json(nullptr);
    }
    clang::SourceLocation after = clang::Lexer::getLocForEndOfToken(
        end, 0, source_manager_, context_.getLangOpts());
    const clang::PresumedLoc start = source_manager_.getPresumedLoc(begin);
    const clang::PresumedLoc finish = source_manager_.getPresumedLoc(after);
    if (start.isInvalid() || finish.isInvalid()) {
      fail(begin, "Clang could not resolve a source span");
      return Json(nullptr);
    }
    llvm::json::Object result;
    result["file"] = logical_source_;
    result["start_line"] = static_cast<std::int64_t>(start.getLine());
    result["start_column"] = static_cast<std::int64_t>(start.getColumn());
    result["end_line"] = static_cast<std::int64_t>(finish.getLine());
    result["end_column"] = static_cast<std::int64_t>(finish.getColumn());
    return Json(std::move(result));
  }

  void fail(clang::SourceLocation location, std::string message) {
    if (!state_.error.empty()) {
      return;
    }
    if (location.isValid()) {
      const clang::PresumedLoc presumed =
          source_manager_.getPresumedLoc(location);
      if (presumed.isValid()) {
        state_.error = logical_source_ + ":" +
                       std::to_string(presumed.getLine()) + ":" +
                       std::to_string(presumed.getColumn()) +
                       ": error: " + std::move(message);
        return;
      }
    }
    state_.error = logical_source_ + ": error: " + std::move(message);
  }

  clang::ASTContext &context_;
  clang::SourceManager &source_manager_;
  std::string logical_source_;
  std::string selected_name_;
  ExportState &state_;
  std::vector<clang::FunctionDecl *> matches_;
  std::unordered_set<const clang::FunctionDecl *> known_functions_;
  std::vector<const clang::FunctionDecl *> reachable_definitions_;
  std::unordered_set<const clang::CXXRecordDecl *> known_records_;
  std::vector<const clang::CXXRecordDecl *> record_definitions_;
  std::unordered_set<const clang::FunctionDecl *>
      functions_with_aggregate_local_;
};

class ExportConsumer : public clang::ASTConsumer {
public:
  ExportConsumer(clang::ASTContext &context, const Options &options,
                 ExportState &state)
      : exporter_(context, options.logical_source, options.function, state) {}

  void HandleTranslationUnit(clang::ASTContext &context) override {
    exporter_.TraverseDecl(context.getTranslationUnitDecl());
    exporter_.finish();
  }

private:
  SemanticExporter exporter_;
};

class ExportAction : public clang::ASTFrontendAction {
public:
  ExportAction(const Options &options, ExportState &state)
      : options_(options), state_(state) {}

  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef) override {
    return std::make_unique<ExportConsumer>(compiler.getASTContext(), options_,
                                            state_);
  }

private:
  const Options &options_;
  ExportState &state_;
};

class ExportActionFactory : public clang::tooling::FrontendActionFactory {
public:
  ExportActionFactory(const Options &options, ExportState &state)
      : options_(options), state_(state) {}

  std::unique_ptr<clang::FrontendAction> create() override {
    return std::make_unique<ExportAction>(options_, state_);
  }

private:
  const Options &options_;
  ExportState &state_;
};

} // namespace

int main(int argc, const char **argv) {
  const auto options = parse_options(argc, argv);
  if (!options) {
    return 2;
  }
  const std::string clang_version = clang::getClangFullVersion();
  if (clang_version.find(kClangVersion) == std::string::npos) {
    llvm::errs() << "error: click-cpp-exporter requires Clang " << kClangVersion
                 << "; linked frontend is " << clang_version << "\n";
    return 2;
  }

  const std::vector<std::string> compiler_arguments = {
      "-x",
      "c++",
      "-std=c++20",
      "--target=x86_64-unknown-linux-gnu",
      "-fno-exceptions",
      "-fno-rtti",
      "-funsigned-char",
      "-ffreestanding",
      "-nostdinc",
      "-nostdinc++",
      "-Wno-reorder-ctor",
      "-fsyntax-only",
  };
  clang::tooling::FixedCompilationDatabase database(
      std::filesystem::current_path().string(), compiler_arguments);
  clang::tooling::ClangTool tool(database, {options->source});
  ExportState state;
  ExportActionFactory factory(*options, state);
  const int status = tool.run(&factory);
  if (status != 0) {
    return status;
  }
  if (!state.error.empty()) {
    llvm::errs() << state.error << "\n";
    return 1;
  }
  if (!state.artifact) {
    llvm::errs() << "error: C++ exporter produced no semantic artifact\n";
    return 1;
  }
  llvm::outs() << llvm::formatv("{0:2}", *state.artifact) << "\n";
  return 0;
}
