use std::fmt;

use std::collections::{HashMap, HashSet};

use crate::Type;
use crate::{
    expr::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SimpleExprKind, SwitchBranch},
    FnDef, FnId, Module, StructDef, SumTypeDef, VarId,
};

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
        match &self.kind {
            SimpleExprKind::Call { func, args } => {
                write!(f, "call {func}({})", fmt_atoms(args))
            }
            SimpleExprKind::TraitCall {
                trait_name,
                method_name,
                args,
            } => {
                write!(
                    f,
                    "trait_call {trait_name}.{method_name}({})",
                    fmt_atoms(args)
                )
            }
            SimpleExprKind::CallClosure { closure, args } => {
                write!(f, "call_closure {closure}({})", fmt_atoms(args))
            }
            SimpleExprKind::MakeClosure { func, captures } => {
                write!(f, "make_closure({func}, [{}])", fmt_atoms(captures))
            }
            SimpleExprKind::Construct { type_name, fields } => {
                write!(f, "construct {type_name}({})", fmt_atoms(fields))
            }
            SimpleExprKind::ConstructVariant {
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
            SimpleExprKind::Project { value, field_index } => {
                write!(f, "project {value}.{field_index}")
            }
            SimpleExprKind::Tag { value } => {
                write!(f, "tag {value}")
            }
            SimpleExprKind::MakeTuple { elements } => {
                write!(f, "tuple({})", fmt_atoms(elements))
            }
            SimpleExprKind::TupleProject { value, index } => {
                write!(f, "tuple_project {value}.{index}")
            }
            SimpleExprKind::PrimOp { op, args } => {
                write!(f, "{op}({})", fmt_atoms(args))
            }
            SimpleExprKind::GetDict { trait_name, ty } => {
                write!(f, "get_dict {trait_name}[{ty}]")
            }
            SimpleExprKind::MakeDict {
                trait_name,
                ty,
                sub_dicts,
            } => {
                write!(f, "make_dict {trait_name}[{ty}]({})", fmt_atoms(sub_dicts))
            }
            SimpleExprKind::MakeVec { elements, .. } => {
                write!(f, "make_vec({})", fmt_atoms(elements))
            }
            SimpleExprKind::Atom(atom) => write!(f, "{atom}"),
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
    fn_names: &'a HashMap<FnId, String>,
}

impl<'a, 'b> IndentWriter<'a, 'b> {
    fn new(
        f: &'a mut fmt::Formatter<'b>,
        indent: usize,
        fn_names: &'a HashMap<FnId, String>,
    ) -> Self {
        Self {
            f,
            indent,
            fn_names,
        }
    }

    fn fmt_fn(&self, id: &FnId) -> String {
        self.fn_names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("{id}"))
    }

    fn write_simple_expr(&mut self, expr: &SimpleExpr) -> fmt::Result {
        match &expr.kind {
            SimpleExprKind::Call { func, args } => {
                write!(self.f, "call {}({})", self.fmt_fn(func), fmt_atoms(args))
            }
            SimpleExprKind::TraitCall {
                trait_name,
                method_name,
                args,
            } => {
                write!(
                    self.f,
                    "trait_call {trait_name}.{method_name}({})",
                    fmt_atoms(args)
                )
            }
            SimpleExprKind::CallClosure { closure, args } => {
                write!(self.f, "call_closure {closure}({})", fmt_atoms(args))
            }
            SimpleExprKind::MakeClosure { func, captures } => {
                write!(
                    self.f,
                    "make_closure({}, [{}])",
                    self.fmt_fn(func),
                    fmt_atoms(captures)
                )
            }
            SimpleExprKind::Construct { type_name, fields } => {
                write!(self.f, "construct {type_name}({})", fmt_atoms(fields))
            }
            SimpleExprKind::ConstructVariant {
                type_name,
                variant,
                tag,
                fields,
            } => {
                write!(
                    self.f,
                    "construct {type_name}::{variant}#{tag}({})",
                    fmt_atoms(fields)
                )
            }
            SimpleExprKind::Project { value, field_index } => {
                write!(self.f, "project {value}.{field_index}")
            }
            SimpleExprKind::Tag { value } => {
                write!(self.f, "tag {value}")
            }
            SimpleExprKind::MakeTuple { elements } => {
                write!(self.f, "tuple({})", fmt_atoms(elements))
            }
            SimpleExprKind::TupleProject { value, index } => {
                write!(self.f, "tuple_project {value}.{index}")
            }
            SimpleExprKind::PrimOp { op, args } => {
                write!(self.f, "{op}({})", fmt_atoms(args))
            }
            SimpleExprKind::GetDict { trait_name, ty } => {
                write!(self.f, "get_dict {trait_name}[{ty}]")
            }
            SimpleExprKind::MakeDict {
                trait_name,
                ty,
                sub_dicts,
            } => {
                write!(
                    self.f,
                    "make_dict {trait_name}[{ty}]({})",
                    fmt_atoms(sub_dicts)
                )
            }
            SimpleExprKind::MakeVec { elements, .. } => {
                write!(self.f, "make_vec({})", fmt_atoms(elements))
            }
            SimpleExprKind::Atom(atom) => write!(self.f, "{atom}"),
        }
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
                write!(self.f, "let {bind}: {ty} = ")?;
                self.write_simple_expr(value)?;
                writeln!(self.f)?;
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
                        "{var}: {ty} = make_closure({}, [{}])",
                        self.fmt_fn(fn_id),
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
                is_recur,
            } => {
                self.write_indent()?;
                if *is_recur {
                    writeln!(self.f, "let_join [recur] {name}({}) =", fmt_params(params))?;
                } else {
                    writeln!(self.f, "let_join {name}({}) =", fmt_params(params))?;
                }
                let mut inner = IndentWriter::new(self.f, self.indent + 1, self.fn_names);
                inner.write_expr(join_body)?;
                self.write_indent()?;
                writeln!(self.f, "in")?;
                self.write_expr(body)
            }
            ExprKind::Jump { target, args } => {
                self.write_indent()?;
                writeln!(self.f, "jump {target}({})", fmt_atoms(args))
            }
            ExprKind::BoolSwitch {
                scrutinee,
                true_body,
                false_body,
            } => {
                self.write_indent()?;
                writeln!(self.f, "if {scrutinee} {{")?;
                let mut inner = IndentWriter::new(self.f, self.indent + 1, self.fn_names);
                inner.write_expr(true_body)?;
                self.write_indent()?;
                writeln!(self.f, "}} else {{")?;
                let mut inner = IndentWriter::new(self.f, self.indent + 1, self.fn_names);
                inner.write_expr(false_body)?;
                self.write_indent()?;
                writeln!(self.f, "}}")
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
                    let mut inner = IndentWriter::new(self.f, self.indent + 2, self.fn_names);
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
        let mut inner = IndentWriter::new(self.f, self.indent + 2, self.fn_names);
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
        let empty = HashMap::new();
        self.fmt_with_names(f, &empty)
    }
}

impl FnDef {
    fn fmt_with_names(
        &self,
        f: &mut fmt::Formatter<'_>,
        fn_names: &HashMap<FnId, String>,
    ) -> fmt::Result {
        writeln!(
            f,
            "fn {}({}) -> {} =",
            self.name,
            fmt_params(&self.params),
            self.return_type,
        )?;
        let mut writer = IndentWriter::new(f, 1, fn_names);
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
        for s in &self.sum_types {
            writeln!(f, "{s}")?;
        }

        for t in self.traits.iter().filter(|t| !t.is_imported) {
            let methods: Vec<String> = t
                .methods
                .iter()
                .map(|m| {
                    let params: Vec<String> =
                        m.param_types.iter().map(|t| format!("{t}")).collect();
                    format!("{}({}): {}", m.name, params.join(", "), m.return_type)
                })
                .collect();
            writeln!(
                f,
                "trait {}[{}] {{ {} }}",
                t.name,
                t.type_var,
                methods.join("; ")
            )?;
        }
        for inst in self.instances.iter().filter(|i| !i.is_imported) {
            let methods: Vec<String> = inst
                .method_fn_ids
                .iter()
                .map(|(name, id)| {
                    let fn_name = self.fn_names.get(id).map(|s| s.as_str()).unwrap_or("?");
                    format!("{name}={fn_name}")
                })
                .collect();
            let intrinsic = if inst.is_intrinsic {
                " [intrinsic]"
            } else {
                ""
            };
            writeln!(
                f,
                "instance {}[{}] {{ {} }}{}",
                inst.trait_name,
                inst.target_type_name,
                methods.join(", "),
                intrinsic
            )?;
        }
        for ext in &self.extern_fns {
            let target = match &ext.target {
                crate::ExternTarget::Java { class } => format!("java \"{class}\""),
                crate::ExternTarget::Js { module } => format!("js \"{module}\""),
            };
            let params: Vec<String> = ext.param_types.iter().map(|t| format!("{t}")).collect();
            writeln!(
                f,
                "extern {target} {}({}): {}",
                ext.name,
                params.join(", "),
                ext.return_type
            )?;
        }
        for ext in &self.extern_types {
            let target = match &ext.target {
                crate::ExternTarget::Java { class } => format!("java \"{class}\""),
                crate::ExternTarget::Js { module } => format!("js \"{module}\""),
            };
            writeln!(f, "extern type {target} {}", ext.name)?;
        }
        for imp in &self.imported_fns {
            let params: Vec<String> = imp.param_types.iter().map(|t| format!("{t}")).collect();
            writeln!(
                f,
                "import {}/{} as {}({}): {}",
                imp.source_module,
                imp.original_name,
                imp.name,
                params.join(", "),
                imp.return_type
            )?;
        }

        // Print declarations for imported/extern functions referenced in bodies
        let local_fn_ids: HashSet<FnId> = self.functions.iter().map(|func| func.id).collect();
        let mut referenced = HashSet::new();
        for func in &self.functions {
            collect_referenced_fns(&func.body, &mut referenced);
        }
        let mut declares: Vec<_> = self
            .fn_names
            .iter()
            .filter(|(id, _)| !local_fn_ids.contains(id) && referenced.contains(id))
            .map(|(id, name)| (name.as_str(), *id))
            .collect();
        declares.sort_by_key(|(name, _)| *name);
        // Build FnId → Type lookup from enriched extern_fns and imported_fns
        let mut fn_type_lookup: HashMap<FnId, String> = HashMap::new();
        for ext in &self.extern_fns {
            let params: Vec<String> = ext.param_types.iter().map(|t| format!("{t}")).collect();
            fn_type_lookup.insert(
                ext.id,
                format!("({}) -> {}", params.join(", "), ext.return_type),
            );
        }
        for imp in &self.imported_fns {
            let params: Vec<String> = imp.param_types.iter().map(|t| format!("{t}")).collect();
            fn_type_lookup.insert(
                imp.id,
                format!("({}) -> {}", params.join(", "), imp.return_type),
            );
        }
        for (name, id) in &declares {
            if let Some(ty) = fn_type_lookup.get(id) {
                writeln!(f, "declare {name}: {ty}")?;
            } else {
                writeln!(f, "declare {name}")?;
            }
        }

        if !self.structs.is_empty() || !self.sum_types.is_empty() || !declares.is_empty() {
            writeln!(f)?;
        }

        for (i, func) in self.functions.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            func.fmt_with_names(f, &self.fn_names)?;
        }
        Ok(())
    }
}

/// Collect all FnIds referenced in Call and MakeClosure nodes.
fn collect_referenced_fns(expr: &Expr, ids: &mut HashSet<FnId>) {
    match &expr.kind {
        ExprKind::Let { value, body, .. } => {
            collect_referenced_fns_simple(value, ids);
            collect_referenced_fns(body, ids);
        }
        ExprKind::LetRec { bindings, body } => {
            for (_, _, fn_id, _) in bindings {
                ids.insert(*fn_id);
            }
            collect_referenced_fns(body, ids);
        }
        ExprKind::LetJoin {
            join_body, body, ..
        } => {
            collect_referenced_fns(join_body, ids);
            collect_referenced_fns(body, ids);
        }
        ExprKind::BoolSwitch {
            true_body,
            false_body,
            ..
        } => {
            collect_referenced_fns(true_body, ids);
            collect_referenced_fns(false_body, ids);
        }
        ExprKind::Switch {
            branches, default, ..
        } => {
            for branch in branches {
                collect_referenced_fns(&branch.body, ids);
            }
            if let Some(d) = default {
                collect_referenced_fns(d, ids);
            }
        }
        ExprKind::Jump { .. } | ExprKind::Atom(_) => {}
    }
}

fn collect_referenced_fns_simple(expr: &SimpleExpr, ids: &mut HashSet<FnId>) {
    match &expr.kind {
        SimpleExprKind::Call { func, .. } | SimpleExprKind::MakeClosure { func, .. } => {
            ids.insert(*func);
        }
        _ => {}
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

    fn simple(kind: SimpleExprKind) -> SimpleExpr {
        SimpleExpr { kind, span: (0, 0) }
    }

    fn expr(ty: Type, kind: ExprKind) -> Expr {
        Expr {
            kind,
            ty,
            span: (0, 0),
        }
    }

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
        let expr = simple(SimpleExprKind::Call {
            func: FnId(1),
            args: vec![Atom::Var(VarId(0)), Atom::Lit(Literal::Int(42))],
        });
        insta::assert_snapshot!(expr.to_string(), @"call f1(v0, 42)");
    }

    #[test]
    fn pretty_simple_expr_call_closure() {
        let expr = simple(SimpleExprKind::CallClosure {
            closure: Atom::Var(VarId(5)),
            args: vec![Atom::Lit(Literal::Int(1))],
        });
        insta::assert_snapshot!(expr.to_string(), @"call_closure v5(1)");
    }

    #[test]
    fn pretty_simple_expr_make_closure() {
        let expr = simple(SimpleExprKind::MakeClosure {
            func: FnId(2),
            captures: vec![Atom::Var(VarId(0))],
        });
        insta::assert_snapshot!(expr.to_string(), @"make_closure(f2, [v0])");
    }

    #[test]
    fn pretty_simple_expr_construct() {
        let expr = simple(SimpleExprKind::Construct {
            type_name: "Point".into(),
            fields: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
        });
        insta::assert_snapshot!(expr.to_string(), @"construct Point(1, 2)");
    }

    #[test]
    fn pretty_simple_expr_construct_variant() {
        let expr = simple(SimpleExprKind::ConstructVariant {
            type_name: "Option".into(),
            variant: "Some".into(),
            tag: 0,
            fields: vec![Atom::Lit(Literal::Int(42))],
        });
        insta::assert_snapshot!(expr.to_string(), @"construct Option::Some#0(42)");
    }

    #[test]
    fn pretty_simple_expr_project() {
        let expr = simple(SimpleExprKind::Project {
            value: Atom::Var(VarId(0)),
            field_index: 1,
        });
        insta::assert_snapshot!(expr.to_string(), @"project v0.1");
    }

    #[test]
    fn pretty_simple_expr_tag() {
        let expr = simple(SimpleExprKind::Tag {
            value: Atom::Var(VarId(3)),
        });
        insta::assert_snapshot!(expr.to_string(), @"tag v3");
    }

    #[test]
    fn pretty_simple_expr_make_tuple() {
        let expr = simple(SimpleExprKind::MakeTuple {
            elements: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Bool(true))],
        });
        insta::assert_snapshot!(expr.to_string(), @"tuple(1, true)");
    }

    #[test]
    fn pretty_simple_expr_tuple_project() {
        let expr = simple(SimpleExprKind::TupleProject {
            value: Atom::Var(VarId(0)),
            index: 0,
        });
        insta::assert_snapshot!(expr.to_string(), @"tuple_project v0.0");
    }

    #[test]
    fn pretty_simple_expr_primop() {
        let expr = simple(SimpleExprKind::PrimOp {
            op: PrimOp::AddInt,
            args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
        });
        insta::assert_snapshot!(expr.to_string(), @"add_int(1, 2)");
    }

    #[test]
    fn pretty_let_binding() {
        let expr = expr(
            Type::Int,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: simple(SimpleExprKind::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                }),
                body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(0))))),
            },
        );
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            name: "add".into(),
            params: vec![],
            return_type: Type::Int,
            body: expr,
        }.to_string(), @r"
        fn add() -> Int =
          let v0: Int = add_int(1, 2)
          v0
        ");
    }

    #[test]
    fn pretty_let_rec() {
        let expr = expr(
            Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            ExprKind::LetRec {
                bindings: vec![(
                    VarId(0),
                    Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                    FnId(1),
                    vec![],
                )],
                body: Box::new(expr(
                    Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                    ExprKind::Atom(Atom::Var(VarId(0))),
                )),
            },
        );
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            name: "test".into(),
            params: vec![],
            return_type: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            body: expr,
        }.to_string(), @r"
        fn test() -> (Int) -> Int =
          let_rec v0: (Int) -> Int = make_closure(f1, [])
          in
          v0
        ");
    }

    #[test]
    fn pretty_let_join() {
        let expr = expr(
            Type::Int,
            ExprKind::LetJoin {
                name: VarId(10),
                params: vec![(VarId(11), Type::Int)],
                join_body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(11))))),
                body: Box::new(expr(
                    Type::Int,
                    ExprKind::Jump {
                        target: VarId(10),
                        args: vec![Atom::Lit(Literal::Int(42))],
                    },
                )),
                is_recur: false,
            },
        );
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            name: "test".into(),
            params: vec![],
            return_type: Type::Int,
            body: expr,
        }.to_string(), @r"
        fn test() -> Int =
          let_join v10(v11: Int) =
            v11
          in
          jump v10(42)
        ");
    }

    #[test]
    fn pretty_switch() {
        let expr = expr(
            Type::Int,
            ExprKind::Switch {
                scrutinee: Atom::Var(VarId(0)),
                branches: vec![SwitchBranch {
                    tag: 0,
                    bindings: vec![(VarId(1), Type::Int)],
                    body: expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1)))),
                }],
                default: Some(Box::new(expr(
                    Type::Int,
                    ExprKind::Atom(Atom::Lit(Literal::Int(0))),
                ))),
            },
        );
        insta::assert_snapshot!(FnDef {
            id: FnId(0),
            name: "test".into(),
            params: vec![(VarId(0), Type::Named("Option".into(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr,
        }.to_string(), @r"
        fn test(v0: Option[Int]) -> Int =
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
            fn_names: std::collections::HashMap::new(),
            extern_fns: vec![],
            extern_types: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: std::collections::BTreeSet::new(),
            module_path: "test".to_string(),
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
                name: "main".into(),
                params: vec![],
                return_type: Type::Unit,
                body: expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit))),
            }],
            imported_dict_refs: vec![],
            fn_dict_requirements: std::collections::HashMap::new(),
            fn_exit_closes: std::collections::HashMap::new(),
            imported_structs: vec![],
            imported_sum_types: vec![],
            imported_extern_types: vec![],
            imported_extern_fns: vec![],
            imported_instances: vec![],
        };
        insta::assert_snapshot!(module.to_string(), @r"
        module test

        struct Point { x: Int, y: Int }
        type Option[a] = Some#0(a) | None#1

        fn main() -> Unit =
          ()
        ");
    }
}
