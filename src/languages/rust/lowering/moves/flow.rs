//! Recognize disjoint single-entry, single-exit natural while regions. Reject
//! nested/irreducible cycles and extra exits rather than guessing a structure.
use super::*;

/// Interpret the scalar header in assignment order. Only total comparisons,
/// literals, copies, and boolean negation are admitted; no memory reads,
/// arithmetic, calls, borrows, or ownership events can be moved into a guard.
/// Bound substitution growth rather than expanding a shared expression DAG
/// exponentially. The fixed bound makes work linear in header size.
pub(super) fn header_condition(
    mir: &MirBody,
    header: usize,
    condition: &E,
    scalar_names: &BTreeSet<String>,
) -> Result<E, String> {
    let scalar = |name: &str| scalar_names.contains(name);
    fn substitute(
        value: &E,
        definitions: &BTreeMap<String, E>,
        scalar: &impl Fn(&str) -> bool,
        remaining: &mut usize,
    ) -> Result<E, String> {
        if *remaining == 0 {
            return Err("MIR while guard exceeds the 256-node scalar expression bound".into());
        }
        *remaining -= 1;
        Ok(match value {
            E::Local { name } if scalar(name) => {
                if let Some(definition) = definitions.get(name) {
                    // Definitions already denote entry values. Recurse only to
                    // check/copy their size, never substitute them a second time.
                    substitute(definition, &BTreeMap::new(), scalar, remaining)?
                } else {
                    value.clone()
                }
            }
            E::ChunkHasNext { .. }
            | E::Integer { .. }
            | E::UnsignedInteger { .. }
            | E::Boolean { .. } => value.clone(),
            E::Not { value } => E::Not {
                value: Box::new(substitute(value, definitions, scalar, remaining)?),
            },
            E::Binary {
                operator,
                left_type,
                right_type,
                left,
                right,
            } if matches!(operator.as_str(), "eq" | "ne" | "lt" | "le" | "gt" | "ge") => {
                E::Binary {
                    operator: operator.clone(),
                    left_type: left_type.clone(),
                    right_type: right_type.clone(),
                    left: Box::new(substitute(left, definitions, scalar, remaining)?),
                    right: Box::new(substitute(right, definitions, scalar, remaining)?),
                }
            }
            _ => return Err("MIR while header requires pure scalar copies and comparisons".into()),
        })
    }
    let mut definitions = BTreeMap::new();
    for statement in &mir.blocks[header].statements {
        match statement {
            S::Assign {
                target: E::Local { name },
                value,
            } if scalar(name) => {
                let expanded = substitute(value, &definitions, &scalar, &mut 256)?;
                definitions.insert(name.clone(), expanded);
            }
            S::EndStorage { local } if scalar(local) => {}
            _ => return Err("MIR while header requires pure scalar copies and comparisons".into()),
        }
    }
    substitute(condition, &definitions, &scalar, &mut 256)
}

pub(super) struct While {
    pub body: usize,
    pub exit: usize,
    pub body_on_true: bool,
}
pub(super) struct Flow {
    pub order: Vec<usize>,
    pub joins: Vec<usize>,
    pub loops: BTreeMap<usize, While>,
    pub scalar_names: BTreeSet<String>,
}
impl Flow {
    pub fn analyze(function: &Function, mir: &MirBody) -> Result<Self, String> {
        let exit = mir.blocks.len();
        let mut order = Vec::new();
        let mut colors = vec![0_u8; exit];
        let mut stack = vec![(0, false)];
        let mut latches: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        while let Some((block, finished)) = stack.pop() {
            if block >= exit {
                return Err("invalid MIR successor".into());
            }
            if finished {
                colors[block] = 2;
                order.push(block);
                continue;
            }
            if colors[block] == 2 {
                continue;
            }
            colors[block] = 1;
            stack.push((block, true));
            for target in successors(&mir.blocks[block].terminator, exit) {
                if target == exit
                    && matches!(mir.blocks[block].terminator, T::Return | T::Unreachable)
                {
                    continue;
                }
                if target >= exit {
                    return Err("invalid MIR successor".into());
                }
                if colors[target] == 1 {
                    latches.entry(target).or_default().push(block);
                } else {
                    stack.push((target, false));
                }
            }
        }
        let mut predecessors = vec![Vec::new(); exit];
        for &block in &order {
            for target in successors(&mir.blocks[block].terminator, exit) {
                if target < exit {
                    predecessors[target].push(block);
                }
            }
        }
        let mut owners = vec![None; exit];
        let mut loops = BTreeMap::new();
        for (header, tails) in latches {
            let mut members = Vec::new();
            let mut pending = tails;
            pending.push(header);
            while let Some(block) = pending.pop() {
                if let Some(owner) = owners[block] {
                    if owner != header {
                        return Err("nested or overlapping MIR loops are not supported".into());
                    }
                    continue;
                }
                owners[block] = Some(header);
                members.push(block);
                if block != header {
                    pending.extend(&predecessors[block]);
                }
            }
            if owners[0] == Some(header) && header != 0 {
                return Err("MIR loop has an entry bypassing its header".into());
            }
            let T::If {
                then_target,
                else_target,
                ..
            } = mir.blocks[header].terminator
            else {
                return Err("MIR loop requires a conditional while header".into());
            };
            let inside = |target: usize| owners[target] == Some(header);
            let body_on_true = inside(then_target);
            if body_on_true == inside(else_target) {
                return Err("MIR while header requires one body and one exit".into());
            }
            let (body, after) = if body_on_true {
                (then_target, else_target)
            } else {
                (else_target, then_target)
            };
            for block in members {
                if block == header {
                    continue;
                }
                if predecessors[block]
                    .iter()
                    .any(|p| owners[*p] != Some(header))
                {
                    return Err("MIR loop has an entry bypassing its header".into());
                }
                for target in successors(&mir.blocks[block].terminator, exit) {
                    if target == exit || !inside(target) {
                        return Err("MIR while body has an unsupported extra exit".into());
                    }
                }
            }
            loops.insert(
                header,
                While {
                    body,
                    exit: after,
                    body_on_true,
                },
            );
        }
        // Collapse each header to its false successor, and each body backedge
        // to a synthetic region exit. The result is a DAG. Every original
        // block remains available and is emitted once by its owning region.
        let graph = mir
            .blocks
            .iter()
            .enumerate()
            .map(|(block, b)| {
                if let Some(loop_) = loops.get(&block) {
                    vec![loop_.exit]
                } else {
                    successors(&b.terminator, exit)
                        .into_iter()
                        .map(|target| {
                            if owners[block].is_some() && owners[block] == Some(target) {
                                exit
                            } else {
                                target
                            }
                        })
                        .collect()
                }
            })
            .collect::<Vec<_>>();
        let joins = graph_postdominators(&graph, &order);
        Ok(Self {
            order,
            joins,
            loops,
            scalar_names: function
                .parameters
                .iter()
                .chain(&mir.locals)
                .filter(|p| {
                    matches!(
                        p.value_type,
                        Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Bool
                    )
                })
                .map(|p| p.name.clone())
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::{MirBlock, Place, Span};

    fn function(blocks: Vec<MirBlock>) -> Function {
        let span = Span { line: 1, column: 1 };
        Function {
            name: "flow".into(),
            return_type: Type::Unit,
            parameters: vec![],
            body: vec![],
            span: span.clone(),
            mir: Some(MirBody {
                locals: vec![Place {
                    name: "marker".into(),
                    value_type: Type::I32,
                    span,
                }],
                blocks,
            }),
        }
    }
    fn block(terminator: T) -> MirBlock {
        MirBlock {
            statements: vec![],
            terminator,
        }
    }
    fn branch(yes: usize, no: usize) -> T {
        T::If {
            condition: E::Boolean { value: false },
            then_target: yes,
            else_target: no,
        }
    }
    #[test]
    fn mir_while_rejects_extra_exits_nested_cycles_and_invalid_entries() {
        for (blocks, expected) in [
            (vec![block(T::Goto { target: 9 })], "invalid MIR successor"),
            (
                vec![block(T::Goto { target: 1 }), block(T::Goto { target: 0 })],
                "conditional while header",
            ),
            (
                vec![
                    block(branch(1, 3)),
                    block(branch(2, 3)),
                    block(T::Goto { target: 0 }),
                    block(T::Return),
                ],
                "extra exit",
            ),
            (
                vec![
                    block(branch(1, 2)),
                    block(branch(2, 3)),
                    block(T::Goto { target: 1 }),
                    block(T::Return),
                ],
                "entry bypassing",
            ),
            (
                vec![
                    block(branch(1, 4)),
                    block(branch(2, 3)),
                    block(T::Goto { target: 1 }),
                    block(T::Goto { target: 0 }),
                    block(T::Return),
                ],
                "overlapping",
            ),
        ] {
            let f = function(blocks);
            let error = Flow::analyze(&f, f.mir.as_ref().unwrap())
                .err()
                .expect("reject unsupported graph");
            assert!(error.contains(expected), "{error}");
        }
    }
    #[test]
    fn mir_while_diamonds_and_sequential_loops_have_linear_emitted_size() {
        for count in [8, 32, 128] {
            let mut blocks = Vec::new();
            for i in 0..count {
                let h = 4 * i;
                for terminator in [
                    branch(h + 1, h + 4),
                    branch(h + 2, h + 3),
                    T::Goto { target: h },
                    T::Goto { target: h },
                ] {
                    let mut b = block(terminator);
                    b.statements.push(S::Assign {
                        target: E::Local {
                            name: "marker".into(),
                        },
                        value: E::Integer {
                            value: blocks.len() as i32,
                        },
                    });
                    blocks.push(b);
                }
            }
            blocks.push(block(T::Return));
            let f = function(blocks);
            let flow = Flow::analyze(&f, f.mir.as_ref().unwrap()).unwrap();
            assert_eq!(flow.order.len(), 4 * count + 1);
            assert_eq!(flow.loops.len(), count);
            let export = RustExport {
                schema: 2,
                compiler_commit: String::new(),
                target: String::new(),
                edition: "2024".into(),
                overflow_checks: true,
                panic: "abort".into(),
                mir_opt_level: 0,
                logical_source: "flow.rs".into(),
                records: vec![],
                functions: vec![f],
            };
            let (functions, _) = super::super::super::lower(&export).unwrap();
            let kernel = functions[0].to_kernel_function();
            let mut pending = vec![kernel.body()];
            let (mut assignments, mut loops) = (0, 0);
            while let Some(s) = pending.pop() {
                match s {
                    CStatement::Seq(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
                    CStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => pending.extend([then_branch.as_ref(), else_branch.as_ref()]),
                    CStatement::While { body, .. } => {
                        loops += 1;
                        pending.push(body);
                    }
                    CStatement::Assign { name, .. } if name == "marker" => assignments += 1,
                    _ => {}
                }
            }
            assert_eq!(loops, count);
            // Three body blocks once; header once in the body and once on exit.
            assert_eq!(assignments, 5 * count);
        }
    }
    #[test]
    fn mir_while_guard_substitution_preserves_order_and_bounds_expression_growth() {
        let local = |name: &str| E::Local { name: name.into() };
        let assign = |name: &str, value: E| S::Assign {
            target: local(name),
            value,
        };
        let comparison = |a: E, b: E| E::Binary {
            operator: "eq".into(),
            left_type: Type::Bool,
            right_type: Type::Bool,
            left: Box::new(a),
            right: Box::new(b),
        };
        let names = ["i", "m", "b"]
            .into_iter()
            .map(str::to_string)
            .collect::<BTreeSet<_>>();
        let mut mir = MirBody {
            locals: vec![],
            blocks: vec![MirBlock {
                statements: vec![
                    assign("m", local("i")),
                    assign("i", E::Integer { value: 5 }),
                    assign("b", comparison(local("m"), local("i"))),
                ],
                terminator: T::Return,
            }],
        };
        let guard = header_condition(&mir, 0, &local("b"), &names).unwrap();
        let expected = comparison(local("i"), E::Integer { value: 5 });
        assert_eq!(
            serde_json::to_value(guard).unwrap(),
            serde_json::to_value(expected).unwrap()
        );
        let mut names = BTreeSet::from(["t0".into()]);
        mir.blocks[0].statements.clear();
        for i in 1..20 {
            names.insert(format!("t{i}"));
            let previous = local(&format!("t{}", i - 1));
            mir.blocks[0].statements.push(assign(
                &format!("t{i}"),
                comparison(previous.clone(), previous),
            ));
        }
        assert!(
            header_condition(&mir, 0, &local("t19"), &names)
                .unwrap_err()
                .contains("256-node")
        );
        mir.blocks[0].statements = vec![S::Assign {
            target: local("i"),
            value: E::Deref {
                reference: Box::new(local("m")),
                value_type: Type::I32,
            },
        }];
        assert!(
            header_condition(
                &mir,
                0,
                &local("i"),
                &BTreeSet::from(["i".into(), "m".into()])
            )
            .is_err()
        );
    }
}
