#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecursiveASTVisitor.h"
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
    if (declaration->isThisDeclarationADefinition() &&
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
    auto function = lower_function(matches_.front());
    if (!function) {
      return;
    }

    llvm::json::Object profile;
    profile["frontend"] = "clang";
    profile["frontend_version"] = clang::getClangFullVersion();
    profile["standard"] = kStandard;
    profile["target"] = kTarget;
    profile["exceptions"] = false;
    profile["rtti"] = false;

    llvm::json::Object artifact;
    artifact["schema"] = 2;
    artifact["language"] = "c++";
    artifact["profile"] = std::move(profile);
    artifact["logical_source"] = logical_source_;
    artifact["function"] = std::move(*function);
    state_.artifact.emplace(std::move(artifact));
  }

private:
  using Json = llvm::json::Value;

  std::optional<Json> lower_function(clang::FunctionDecl *declaration) {
    const auto *prototype =
        declaration->getType()->getAs<clang::FunctionProtoType>();
    if (prototype == nullptr || !prototype->isNothrow()) {
      fail(declaration->getLocation(),
           "the first C++ slice requires an explicit noexcept function");
      return std::nullopt;
    }
    auto return_type =
        lower_type(declaration->getReturnType(),
                   declaration->getReturnTypeSourceRange().getBegin());
    if (!return_type) {
      return std::nullopt;
    }
    llvm::json::Array parameters;
    for (const clang::ParmVarDecl *parameter : declaration->parameters()) {
      auto lowered = lower_parameter(parameter);
      if (!lowered) {
        return std::nullopt;
      }
      parameters.push_back(std::move(*lowered));
    }
    const auto *body =
        llvm::dyn_cast_or_null<clang::CompoundStmt>(declaration->getBody());
    if (body == nullptr || body->body_empty()) {
      fail(declaration->getLocation(),
           "the supported C++ function requires a nonempty compound body");
      return std::nullopt;
    }

    llvm::json::Array statements;
    for (const clang::Stmt *statement : body->body()) {
      auto lowered = lower_statement(statement, declaration);
      if (!lowered) {
        return std::nullopt;
      }
      statements.push_back(std::move(*lowered));
    }

    llvm::json::Object result;
    result["declaration_id"] = declaration_id(declaration);
    result["name"] = declaration->getNameAsString();
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
    const bool mutable_int_reference =
        reference != nullptr &&
        !reference->getPointeeType().isConstQualified() &&
        context_.hasSameType(reference->getPointeeType().getUnqualifiedType(),
                             context_.IntTy);
    const bool by_value_bool =
        reference == nullptr &&
        context_.hasSameType(parameter->getType().getUnqualifiedType(),
                             context_.BoolTy) &&
        !parameter->getType().isConstQualified();
    if (!mutable_int_reference && !by_value_bool) {
      fail(parameter->getLocation(),
           "the supported C++ parameter must be a by-value bool or mutable int& parameter");
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
    if (context_.hasSameType(type.getUnqualifiedType(), context_.BoolTy)) {
      llvm::json::Object result;
      result["kind"] = "boolean";
      result["bits"] = static_cast<std::int64_t>(context_.getTypeSize(type));
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (!context_.hasSameType(type.getUnqualifiedType(), context_.IntTy)) {
      fail(location, "the supported C++ slice supports bool, int, and int& types");
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
                                      const clang::FunctionDecl *function) {
    if (const auto *binary = llvm::dyn_cast<clang::BinaryOperator>(statement)) {
      if (binary->getOpcode() != clang::BO_Assign) {
        fail(binary->getOperatorLoc(),
             "the first C++ slice supports only simple assignment statements");
        return std::nullopt;
      }
      auto target = lower_place_reference(binary->getLHS(), function);
      auto value = lower_expression(binary->getRHS(), function);
      if (!target || !value) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "assign";
      result["target"] = std::move(*target);
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

  std::optional<llvm::json::Array>
  lower_branch(const clang::Stmt *statement,
               const clang::FunctionDecl *function) {
    llvm::json::Array result;
    if (statement == nullptr) {
      return result;
    }
    if (const auto *compound = llvm::dyn_cast<clang::CompoundStmt>(statement)) {
      for (const clang::Stmt *member : compound->body()) {
        auto lowered = lower_statement(member, function);
        if (!lowered) {
          return std::nullopt;
        }
        result.push_back(std::move(*lowered));
      }
      return result;
    }
    auto lowered = lower_statement(statement, function);
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
      auto place = lower_place_reference(cast->getSubExpr(), function);
      auto value_type = lower_type(cast->getType(), cast->getExprLoc());
      if (!place || !value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "load";
      result["place"] = std::move(*place);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(cast->getSourceRange());
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

  std::optional<Json>
  lower_place_reference(const clang::Expr *expression,
                        const clang::FunctionDecl *expected_function) {
    expression = expression->IgnoreParenImpCasts();
    const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(expression);
    const auto *parameter =
        reference == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::ParmVarDecl>(reference->getDecl());
    if (parameter == nullptr || parameter->getDeclContext() != expected_function) {
      fail(expression->getExprLoc(),
           "the supported C++ slice can access only selected function parameters");
      return std::nullopt;
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(parameter);
    result["name"] = parameter->getNameAsString();
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
