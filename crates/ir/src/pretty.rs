use std::fmt;

use crate::{
    expr::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SwitchBranch},
    FnDef, FnId, Module, StructDef, SumTypeDef, VarId,
};
use krypton_typechecker::types::Type;

// --- Display impls for leaf types ---

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl fmt::Display for FnId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "f{}", self.0)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Int(n) => write!(f, "{n}"),
            Literal::Float(v) => {
                if v.fract() == 0.0 && v.is_finite() {
                    write!(f, "{v:.1}")
                } else {
                    write!(f, "{v}")
                }
            }
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::String(s) => write!(f, "\"{s}\""),
            Literal::Unit => write!(f, "()"),
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Var(id) => write!(f, "{id}"),
            Atom::Lit(lit) => write!(f, "{lit}"),
        }
    }
}

impl fmt::Display for PrimOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            PrimOp::AddInt => "add_int",
            PrimOp::SubInt => "sub_int",
            PrimOp::MulInt => "mul_int",
            PrimOp::DivInt => "div_int",
            PrimOp::ModInt => "mod_int",
            PrimOp::NegInt => "neg_int",
            PrimOp::AddFloat => "add_float",
            PrimOp::SubFloat => "sub_float",
            PrimOp::MulFloat => "mul_float",
            PrimOp::DivFloat => "div_float",
            PrimOp::NegFloat => "neg_float",
            PrimOp::EqInt => "eq_int",
            PrimOp::NeqInt => "neq_int",
            PrimOp::LtInt => "lt_int",
            PrimOp::LeInt => "le_int",
            PrimOp::GtInt => "gt_int",
            PrimOp::GeInt => "ge_int",
            PrimOp::EqFloat => "eq_float",
            PrimOp::NeqFloat => "neq_float",
            PrimOp::LtFloat => "lt_float",
            PrimOp::LeFloat => "le_float",
            PrimOp::GtFloat => "gt_float",
            PrimOp::GeFloat => "ge_float",
            PrimOp::Not => "not",
            PrimOp::And => "and",
            PrimOp::Or => "or",
            PrimOp::EqString => "eq_string",
            PrimOp::NeqString => "neq_string",
            PrimOp::ConcatString => "concat_string",
            PrimOp::IntToFloat => "int_to_float",
            PrimOp::FloatToInt => "float_to_int",
            PrimOp::IntToString => "int_to_string",
            PrimOp::FloatToString => "float_to_string",
            PrimOp::BoolToString => "bool_to_string",
        };
        write!(f, "{name}")
    }
}

// --- SimpleExpr Display ---

impl fmt::Display for SimpleExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimpleExpr::Call { func, args } => {
                write!(f, "call {func}({})", fmt_atoms(args))
            }
            SimpleExpr::CallClosure { closure, args } => {
                write!(f, "call_closure {closure}({})", fmt_atoms(args))
            }
            SimpleExpr::MakeClosure { func, captures } => {
                write!(f, "make_closure({func}, [{}])", fmt_atoms(captures))
            }
            SimpleExpr::Construct { type_name, fields } => {
                write!(f, "construct {type_name}({})", fmt_atoms(fields))
            }
            SimpleExpr::ConstructVariant {
                type_name,
                variant,
                tag,
                fields,
            } => {
                write!(
                    f,
                    "construct {type_name}::{variant}#{tag}({})",
                    fmt_atoms(fields)
                )
            }
            SimpleExpr::Project { value, field_index } => {
                write!(f, "project {value}.{field_index}")
            }
            SimpleExpr::Tag { value } => {
                write!(f, "tag {value}")
            }
            SimpleExpr::MakeTuple { elements } => {
                write!(f, "tuple({})", fmt_atoms(elements))
            }
            SimpleExpr::TupleProject { value, index } => {
                write!(f, "tuple_project {value}.{index}")
            }
            SimpleExpr::PrimOp { op, args } => {
                write!(f, "{op}({})", fmt_atoms(args))
            }
        }
    }
}

fn fmt_atoms(atoms: &[Atom]) -> String {
    atoms
        .iter()
        .map(|a| a.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

// --- Indentation-aware expr printing ---

struct IndentWriter<'a, 'b> {
    f: &'a mut fmt::Formatter<'b>,
    indent: usize,
}

impl<'a, 'b> IndentWriter<'a, 'b> {
    fn new(f: &'a mut fmt::Formatter<'b>, indent: usize) -> Self {
        Self { f, indent }
    }

    fn write_indent(&mut self) -> fmt::Result {
        for _ in 0..self.indent {
            write!(self.f, "  ")?;
        }
        Ok(())
    }

    fn write_expr(&mut self, expr: &Expr) -> fmt::Result {
        match &expr.kind {
            ExprKind::Let {
                bind,
                ty,
                value,
                body,
            } => {
                self.write_indent()?;
                writeln!(self.f, "let {bind}: {ty} = {value}")?;
                self.write_expr(body)
            }
            ExprKind::LetRec { bindings, body } => {
                for (i, (var, ty, fn_id, captures)) in bindings.iter().enumerate() {
                    self.write_indent()?;
                    if i == 0 {
                        write!(self.f, "let_rec ")?;
                    } else {
                        write!(self.f, "    and ")?;
                    }
                    writeln!(
                        self.f,
                        "{var}: {ty} = make_closure({fn_id}, [{}])",
                        fmt_atoms(captures)
                    )?;
                }
                self.write_indent()?;
                writeln!(self.f, "in")?;
                self.write_expr(body)
            }
            ExprKind::LetJoin {
                name,
                params,
                join_body,
                body,
            } => {
                self.write_indent()?;
                writeln!(self.f, "let_join {name}({}) =", fmt_params(params))?;
                let mut inner = IndentWriter::new(self.f, self.indent + 1);
                inner.write_expr(join_body)?;
                self.write_indent()?;
                writeln!(self.f, "in")?;
                self.write_expr(body)
            }
            ExprKind::Jump { target, args } => {
                self.write_indent()?;
                writeln!(self.f, "jump {target}({})", fmt_atoms(args))
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                self.write_indent()?;
                writeln!(self.f, "switch {scrutinee} {{")?;
                for branch in branches {
                    self.write_branch(branch)?;
                }
                if let Some(default_expr) = default {
                    self.write_indent()?;
                    writeln!(self.f, "  _ ->")?;
                    let mut inner = IndentWriter::new(self.f, self.indent + 2);
                    inner.write_expr(default_expr)?;
                }
                self.write_indent()?;
                writeln!(self.f, "}}")
            }
            ExprKind::Atom(atom) => {
                self.write_indent()?;
                writeln!(self.f, "{atom}")
            }
        }
    }

    fn write_branch(&mut self, branch: &SwitchBranch) -> fmt::Result {
        self.write_indent()?;
        write!(self.f, "  {} ", branch.tag)?;
        if !branch.bindings.is_empty() {
            write!(self.f, "({}) ", fmt_params(&branch.bindings))?;
        }
        writeln!(self.f, "->")?;
        let mut inner = IndentWriter::new(self.f, self.indent + 2);
        inner.write_expr(&branch.body)
    }
}

fn fmt_params(params: &[(VarId, Type)]) -> String {
    params
        .iter()
        .map(|(v, t)| format!("{v}: {t}"))
        .collect::<Vec<_>>()
        .join(", ")
}

// --- Top-level Display impls ---

impl fmt::Display for StructDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "struct {}", self.name)?;
        if !self.type_params.is_empty() {
            write!(f, "[{}]", fmt_type_params(&self.type_params))?;
        }
        write!(f, " {{ ")?;
        for (i, (name, ty)) in self.fields.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{name}: {ty}")?;
        }
        write!(f, " }}")
    }
}

impl fmt::Display for SumTypeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "type {}", self.name)?;
        if !self.type_params.is_empty() {
            write!(f, "[{}]", fmt_type_params(&self.type_params))?;
        }
        write!(f, " = ")?;
        for (i, variant) in self.variants.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(f, "{}#{}", variant.name, variant.tag)?;
            if !variant.fields.is_empty() {
                write!(f, "(")?;
                for (j, ty) in variant.fields.iter().enumerate() {
                    if j > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for FnDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "fn {} {}({}) -> {} =",
            self.id,
            self.debug_name,
            fmt_params(&self.params),
            self.return_type,
        )?;
        let mut writer = IndentWriter::new(f, 1);
        writer.write_expr(&self.body)
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "module {}", self.name)?;
        writeln!(f)?;
        for s in &self.structs {
            writeln!(f, "{s}")?;
        }
        if !self.structs.is_empty() && (!self.sum_types.is_empty() || !self.functions.is_empty()) {
            writeln!(f)?;
        }
        for s in &self.sum_types {
            writeln!(f, "{s}")?;
        }
        if !self.sum_types.is_empty() && !self.functions.is_empty() {
            writeln!(f)?;
        }
        for (i, func) in self.functions.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{func}")?;
        }
        Ok(())
    }
}

fn fmt_type_params(params: &[krypton_typechecker::types::TypeVarId]) -> String {
    params
        .iter()
        .map(|p| p.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VariantDef;
    use krypton_typechecker::types::TypeVarGen;

    fn gen_type_var_ids(n: usize) -> Vec<krypton_typechecker::types::TypeVarId> {
        let mut gen = TypeVarGen::new();
        (0..n).map(|_| gen.fresh()).collect()
    }

    #[test]
    fn pretty_atom_var() {
        let atom = Atom::Var(VarId(0));
        insta::assert_snapshot!(atom.to_string(), @"v0");
    }

    #[test]
    fn pretty_atom_literals() {
        insta::assert_snapshot!(Literal::Int(42).to_string(), @"42");
        insta::assert_snapshot!(Literal::Float(3.14).to_string(), @"3.14");
        insta::assert_snapshot!(Literal::Float(1.0).to_string(), @"1.0");
        insta::assert_snapshot!(Literal::Bool(true).to_string(), @"true");
        insta::assert_snapshot!(Literal::Bool(false).to_string(), @"false");
        insta::assert_snapshot!(Literal::String("hello".into()).to_string(), @r#""hello""#);
        insta::assert_snapshot!(Literal::Unit.to_string(), @"()");
    }

    #[test]
    fn pretty_simple_expr_call() {
        let expr = SimpleExpr::Call {
            func: FnId(1),
            args: vec![Atom::Var(VarId(0)), Atom::Lit(Literal::Int(42))],
        };
        insta::assert_snapshot!(expr.to_string(), @"call f1(v0, 42)");
    }

    #[test]
    fn pretty_simple_expr_call_closure() {
        let expr = SimpleExpr::CallClosure {
            closure: Atom::Var(VarId(5)),
            args: vec![Atom::Lit(Literal::Int(1))],
        };
        insta::assert_snapshot!(expr.to_string(), @"call_closure v5(1)");
    }

    #[test]
    fn pretty_simple_expr_make_closure() {
        let expr = SimpleExpr::MakeClosure {
            func: FnId(2),
            captures: vec![Atom::Var(VarId(0))],
        };
        insta::assert_snapshot!(expr.to_string(), @"make_closure(f2, [v0])");
    }

    #[test]
    fn pretty_simple_expr_construct() {
        let expr = SimpleExpr::Construct {
            type_name: "Point".into(),
            fields: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
        };
        insta::assert_snapshot!(expr.to_string(), @"construct Point(1, 2)");
    }

    #[test]
    fn pretty_simple_expr_construct_variant() {
        let expr = SimpleExpr::ConstructVariant {
            type_name: "Option".into(),
            variant: "Some".into(),
            tag: 0,
            fields: vec![Atom::Lit(Literal::Int(42))],
        };
        insta::assert_snapshot!(expr.to_string(), @"construct Option::Some#0(42)");
    }

    #[test]
    fn pretty_simple_expr_project() {
        let expr = SimpleExpr::Project {
            value: Atom::Var(VarId(0)),
            field_index: 1,
        };
        insta::assert_snapshot!(expr.to_string(), @"project v0.1");
    }

    #[test]
    fn pretty_simple_expr_tag() {
        let expr = SimpleExpr::Tag {
            value: Atom::Var(VarId(3)),
        };
        insta::assert_snapshot!(expr.to_string(), @"tag v3");
    }

    #[test]
    fn pretty_simple_expr_make_tuple() {
        let expr = SimpleExpr::MakeTuple {
            elements: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Bool(true))],
        };
        insta::assert_snapshot!(expr.to_string(), @"tuple(1, true)");
    }

    #[test]
    fn pretty_simple_expr_tuple_project() {
        let expr = SimpleExpr::TupleProject {
            value: Atom::Var(VarId(0)),
            index: 0,
        };
        insta::assert_snapshot!(expr.to_string(), @"tuple_project v0.0");
    }

    #[test]
    fn pretty_simple_expr_primop() {
        let expr = SimpleExpr::PrimOp {
            op: PrimOp::AddInt,
            args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
        };
        insta::assert_snapshot!(expr.to_string(), @"add_int(1, 2)");
    }

    #[test]
    fn pretty_let_binding() {
        let expr = Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: SimpleExpr::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(0))),
                    ty: Type::Int,
                }),
            },
            ty: Type::Int,
        };
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            debug_name: "add".into(),
            params: vec![],
            return_type: Type::Int,
            body: expr,
        }.to_string(), @r"
        fn f0 add() -> Int =
          let v0: Int = add_int(1, 2)
          v0
        ");
    }

    #[test]
    fn pretty_let_rec() {
        let expr = Expr {
            kind: ExprKind::LetRec {
                bindings: vec![
                    (VarId(0), Type::Fn(vec![Type::Int], Box::new(Type::Int)), FnId(1), vec![]),
                ],
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(0))),
                    ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                }),
            },
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        };
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            debug_name: "test".into(),
            params: vec![],
            return_type: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            body: expr,
        }.to_string(), @r"
        fn f0 test() -> (Int) -> Int =
          let_rec v0: (Int) -> Int = make_closure(f1, [])
          in
          v0
        ");
    }

    #[test]
    fn pretty_let_join() {
        let expr = Expr {
            kind: ExprKind::LetJoin {
                name: VarId(10),
                params: vec![(VarId(11), Type::Int)],
                join_body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(11))),
                    ty: Type::Int,
                }),
                body: Box::new(Expr {
                    kind: ExprKind::Jump {
                        target: VarId(10),
                        args: vec![Atom::Lit(Literal::Int(42))],
                    },
                    ty: Type::Int,
                }),
            },
            ty: Type::Int,
        };
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            debug_name: "test".into(),
            params: vec![],
            return_type: Type::Int,
            body: expr,
        }.to_string(), @r"
        fn f0 test() -> Int =
          let_join v10(v11: Int) =
            v11
          in
          jump v10(42)
        ");
    }

    #[test]
    fn pretty_switch() {
        let expr = Expr {
            kind: ExprKind::Switch {
                scrutinee: Atom::Var(VarId(0)),
                branches: vec![
                    SwitchBranch {
                        tag: 0,
                        bindings: vec![(VarId(1), Type::Int)],
                        body: Expr {
                            kind: ExprKind::Atom(Atom::Var(VarId(1))),
                            ty: Type::Int,
                        },
                    },
                ],
                default: Some(Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Lit(Literal::Int(0))),
                    ty: Type::Int,
                })),
            },
            ty: Type::Int,
        };
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            debug_name: "test".into(),
            params: vec![(VarId(0), Type::Named("Option".into(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr,
        }.to_string(), @r"
        fn f0 test(v0: Option[Int]) -> Int =
          switch v0 {
            0 (v1: Int) ->
              v1
            _ ->
              0
          }
        ");
    }

    #[test]
    fn pretty_struct_def() {
        let s = StructDef {
            name: "Point".into(),
            type_params: vec![],
            fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
        };
        insta::assert_snapshot!(s.to_string(), @"struct Point { x: Int, y: Int }");
    }

    #[test]
    fn pretty_struct_def_generic() {
        let ids = gen_type_var_ids(2);
        let s = StructDef {
            name: "Pair".into(),
            type_params: vec![ids[0], ids[1]],
            fields: vec![
                ("first".into(), Type::Var(ids[0])),
                ("second".into(), Type::Var(ids[1])),
            ],
        };
        insta::assert_snapshot!(s.to_string(), @"struct Pair[a, b] { first: a, second: b }");
    }

    #[test]
    fn pretty_sum_type_def() {
        let ids = gen_type_var_ids(1);
        let s = SumTypeDef {
            name: "Option".into(),
            type_params: vec![ids[0]],
            variants: vec![
                VariantDef {
                    name: "Some".into(),
                    tag: 0,
                    fields: vec![Type::Var(ids[0])],
                },
                VariantDef {
                    name: "None".into(),
                    tag: 1,
                    fields: vec![],
                },
            ],
        };
        insta::assert_snapshot!(s.to_string(), @"type Option[a] = Some#0(a) | None#1");
    }

    #[test]
    fn pretty_module() {
        let ids = gen_type_var_ids(1);
        let module = Module {
            name: "test".into(),
            structs: vec![StructDef {
                name: "Point".into(),
                type_params: vec![],
                fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
            }],
            sum_types: vec![SumTypeDef {
                name: "Option".into(),
                type_params: vec![ids[0]],
                variants: vec![
                    VariantDef {
                        name: "Some".into(),
                        tag: 0,
                        fields: vec![Type::Var(ids[0])],
                    },
                    VariantDef {
                        name: "None".into(),
                        tag: 1,
                        fields: vec![],
                    },
                ],
            }],
            functions: vec![FnDef {
                id: FnId(0),
                debug_name: "main".into(),
                params: vec![],
                return_type: Type::Unit,
                body: Expr {
                    kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                    ty: Type::Unit,
                },
            }],
        };
        insta::assert_snapshot!(module.to_string(), @r"
        module test

        struct Point { x: Int, y: Int }

        type Option[a] = Some#0(a) | None#1

        fn f0 main() -> Unit =
          ()
        ");
    }
}
