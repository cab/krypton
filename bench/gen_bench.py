#!/usr/bin/env python3
"""Generate a large multi-file Krypton project for compile-time benchmarking.

Produces a DAG of modules (no circular imports) that exercise records, sum types,
traits, generics, pattern matching, closures, recursion, cross-module usage,
HKT, constrained impls, superclass traits, tuples, struct updates, match guards,
or-patterns, nested patterns, Result/?-operator, mutual recursion, and more.

Usage:
    python3 bench/gen_bench.py                          # defaults: 50 modules
    python3 bench/gen_bench.py --modules 200 --out /tmp/kr_bench
    cargo run --release -- check bench/generated/main.kr --timings
"""

import argparse
import os
import random
import shutil


# ---------------------------------------------------------------------------
# Naming helpers
# ---------------------------------------------------------------------------

def mod_name(i: int) -> str:
    return f"m{i:03d}"


def record_name(mod_idx: int, type_idx: int) -> str:
    return f"R{mod_idx}_{type_idx}"


def enum_name(mod_idx: int, type_idx: int) -> str:
    return f"E{mod_idx}_{type_idx}"


def variant_name(mod_idx: int, type_idx: int, var_idx: int) -> str:
    return f"V{mod_idx}_{type_idx}_{var_idx}"


def trait_name(mod_idx: int) -> str:
    return f"Metric{mod_idx}"


def fn_name(mod_idx: int, fn_idx: int) -> str:
    return f"f{mod_idx}_{fn_idx}"


def opt_type_name(mod_idx: int) -> str:
    return f"Opt{mod_idx}"


def some_name(mod_idx: int) -> str:
    return f"Some{mod_idx}"


def none_name(mod_idx: int) -> str:
    return f"None{mod_idx}"


def pair_type_name(mod_idx: int) -> str:
    return f"Pair{mod_idx}"


def box_name(mod_idx: int) -> str:
    return f"Box{mod_idx}"


# ---------------------------------------------------------------------------
# Type generators
# ---------------------------------------------------------------------------

FIELD_TYPES = ["Int", "Bool", "Int", "Int"]  # weighted toward Int for arithmetic compat


def gen_record(mod_idx: int, type_idx: int, num_fields: int = 3) -> str:
    if type_idx == 0:
        # First record is always all-Int for cross-module arithmetic compatibility
        fields = ", ".join(f"f{j}: Int" for j in range(num_fields))
    else:
        fields = ", ".join(
            f"f{j}: {FIELD_TYPES[(mod_idx + type_idx + j) % len(FIELD_TYPES)]}"
            for j in range(num_fields)
        )
    name = record_name(mod_idx, type_idx)
    if type_idx % 3 == 0:
        deriving = " deriving (Eq, Show, Hash)"
    elif type_idx % 3 == 1:
        deriving = " deriving (Eq, Show)"
    else:
        deriving = ""
    return f"pub type {name} = {{ {fields} }}{deriving}"


def gen_enum(mod_idx: int, type_idx: int, num_variants: int = 4) -> str:
    name = enum_name(mod_idx, type_idx)
    variants = []
    for v in range(num_variants):
        vn = variant_name(mod_idx, type_idx, v)
        if v == 0:
            variants.append(f"{vn}(Int)")
        elif v == 1:
            variants.append(f"{vn}(Int, Int)")
        elif v == 2:
            variants.append(vn)
        else:
            variants.append(f"{vn}(Int)")
    deriving = " deriving (Eq)" if type_idx % 2 == 0 else ""
    return f"pub type {name} = {' | '.join(variants)}{deriving}"


def gen_generic_type(mod_idx: int) -> str:
    bn = box_name(mod_idx)
    return f"pub type {bn}[a] = {bn}(a)"


def gen_option_type(mod_idx: int) -> str:
    return f"pub type {opt_type_name(mod_idx)}[a] = {some_name(mod_idx)}(a) | {none_name(mod_idx)}"


def gen_pair_type(mod_idx: int) -> str:
    pn = pair_type_name(mod_idx)
    return f"pub type {pn}[a, b] = {pn}(a, b)"


# ---------------------------------------------------------------------------
# Trait generators
# ---------------------------------------------------------------------------

def gen_trait(mod_idx: int) -> str:
    tn = trait_name(mod_idx)
    return f"pub trait {tn}[a] {{\n    fun {tn.lower()}(x: a) -> Int\n}}"


def gen_trait_impl_record(mod_idx: int, type_idx: int) -> str:
    tn = trait_name(mod_idx)
    rn = record_name(mod_idx, type_idx)
    fields = " + ".join(f"x.f{j}" for j in range(3))
    return (
        f"impl {tn}[{rn}] {{\n"
        f"    fun {tn.lower()}(x: {rn}) -> Int = {fields}\n"
        f"}}"
    )


def gen_trait_impl_enum(mod_idx: int, type_idx: int) -> str:
    tn = trait_name(mod_idx)
    en = enum_name(mod_idx, type_idx)
    v0 = variant_name(mod_idx, type_idx, 0)
    v1 = variant_name(mod_idx, type_idx, 1)
    return (
        f"impl {tn}[{en}] {{\n"
        f"    fun {tn.lower()}(x: {en}) -> Int = match x {{\n"
        f"        {v0}(n) => n,\n"
        f"        {v1}(a, b) => a + b,\n"
        f"        _ => 0,\n"
        f"    }}\n"
        f"}}"
    )


def gen_hkt_trait(mod_idx: int) -> str:
    """Generate a Functor-like HKT trait + impl for Box type."""
    bn = box_name(mod_idx)
    tn = f"Mappable{mod_idx}"
    fn = f"map{mod_idx}"
    return (
        f"pub trait {tn}[f[_]] {{\n"
        f"    fun {fn}[a, b](fa: f[a], g: (a) -> b) -> f[b]\n"
        f"}}\n"
        f"\n"
        f"impl {tn}[{bn}] {{\n"
        f"    fun {fn}[a, b](fa: {bn}[a], g: (a) -> b) -> {bn}[b] =\n"
        f"        match fa {{ {bn}(x) => {bn}(g(x)) }}\n"
        f"}}"
    )


def gen_constrained_impl(mod_idx: int) -> str:
    """Generate a constrained generic impl: Metric for Opt[a] where a: Metric."""
    tn = trait_name(mod_idx)
    otn = opt_type_name(mod_idx)
    sn = some_name(mod_idx)
    nn = none_name(mod_idx)
    return (
        f"impl {tn}[{otn}[a]] where a: {tn} {{\n"
        f"    fun {tn.lower()}(x: {otn}[a]) -> Int = match x {{\n"
        f"        {sn}(v) => {tn.lower()}(v),\n"
        f"        {nn} => 0,\n"
        f"    }}\n"
        f"}}"
    )


def gen_superclass_trait(mod_idx: int) -> str:
    """Generate a superclass trait that requires Metric."""
    tn = trait_name(mod_idx)
    stn = f"Extended{mod_idx}"
    rn = record_name(mod_idx, 0)
    return (
        f"pub trait {stn}[a] where a: {tn} {{\n"
        f"    fun {stn.lower()}(x: a) -> Int\n"
        f"}}\n"
        f"\n"
        f"impl {stn}[{rn}] {{\n"
        f"    fun {stn.lower()}(x: {rn}) -> Int = {tn.lower()}(x) * 2\n"
        f"}}"
    )


# ---------------------------------------------------------------------------
# Function generators (core)
# ---------------------------------------------------------------------------

def gen_functions(mod_idx: int, num_fns: int, num_record_types: int) -> list[str]:
    fns = []

    rn = record_name(mod_idx, 0)
    en = enum_name(mod_idx, 0)
    v0 = variant_name(mod_idx, 0, 0)
    v1 = variant_name(mod_idx, 0, 1)
    v2 = variant_name(mod_idx, 0, 2)
    tn = trait_name(mod_idx)
    bn = box_name(mod_idx)

    # f_0: constructor
    fields = ", ".join(f"f{j} = x + {j}" for j in range(3))
    fns.append(f"pub fun {fn_name(mod_idx, 0)}(x: Int) -> {rn} = {rn} {{ {fields} }}")

    # f_1: field access + arithmetic
    fns.append(
        f"pub fun {fn_name(mod_idx, 1)}(r: {rn}) -> Int = r.f0 + r.f1 + r.f2"
    )

    # f_2: pattern match on enum
    fns.append(
        f"pub fun {fn_name(mod_idx, 2)}(e: {en}) -> Int = match e {{\n"
        f"    {v0}(n) => n * 2,\n"
        f"    {v1}(a, b) => a + b,\n"
        f"    _ => 0,\n"
        f"}}"
    )

    # f_3: closure + higher-order
    fns.append(
        f"pub fun {fn_name(mod_idx, 3)}(x: Int) -> Int = {{\n"
        f"    let add = n -> n + x;\n"
        f"    let double = n -> n * 2;\n"
        f"    double(add({mod_idx}))\n"
        f"}}"
    )

    # f_4: nested let + if/else
    fns.append(
        f"pub fun {fn_name(mod_idx, 4)}(x: Int) -> Int = {{\n"
        f"    let a = x * 2;\n"
        f"    let b = a + 3;\n"
        f"    let c = if b > 100 {{ b - 50 }} else {{ b + 50 }};\n"
        f"    let d = {{\n"
        f"        let inner = c / 2;\n"
        f"        inner + {mod_idx}\n"
        f"    }};\n"
        f"    d\n"
        f"}}"
    )

    # f_5: trait-constrained generic (with multi-constraint for even modules)
    if mod_idx % 2 == 0:
        fns.append(
            f"pub fun {fn_name(mod_idx, 5)}[a](x: a, y: a) -> Int where a: {tn} + Eq =\n"
            f"    {tn.lower()}(x) + {tn.lower()}(y)"
        )
    else:
        fns.append(
            f"pub fun {fn_name(mod_idx, 5)}[a](x: a, y: a) -> Int where a: {tn} =\n"
            f"    {tn.lower()}(x) + {tn.lower()}(y)"
        )

    # f_6: recursive list-like computation via tail recursion
    fns.append(
        f"pub fun {fn_name(mod_idx, 6)}(n: Int, acc: Int) -> Int =\n"
        f"    if n <= 0 {{ acc }} else {{ recur(n - 1, acc + n) }}"
    )

    # f_7: compose closures with block body
    fns.append(
        f"pub fun {fn_name(mod_idx, 7)}(x: Int) -> Int = {{\n"
        f"    let f = a -> a + 1;\n"
        f"    let g = a -> a * 3;\n"
        f"    let h = (a) -> {{\n"
        f"        let step1 = f(a);\n"
        f"        g(step1)\n"
        f"    }};\n"
        f"    h(h(x))\n"
        f"}}"
    )

    # f_8: use generic box type
    fns.append(
        f"pub fun {fn_name(mod_idx, 8)}(x: Int) -> Int = match {bn}(x + 1) {{\n"
        f"    {bn}(v) => v * 2,\n"
        f"}}"
    )

    # Fill remaining with simple arithmetic fns
    for i in range(9, num_fns):
        fns.append(
            f"pub fun {fn_name(mod_idx, i)}(x: Int) -> Int = x + {i * mod_idx}"
        )

    return fns


# ---------------------------------------------------------------------------
# New feature function generators
# ---------------------------------------------------------------------------

def gen_tuple_fns(mod_idx: int) -> list[str]:
    return [
        (
            f"pub fun tuple{mod_idx}(x: Int, y: Bool) -> (Int, Bool) = (x, y)\n"
            f"\n"
            f"pub fun use_tuple{mod_idx}(x: Int) -> Int = {{\n"
            f"    let pair = tuple{mod_idx}(x, true);\n"
            f"    let (a, _) = pair;\n"
            f"    a + 1\n"
            f"}}"
        )
    ]


def gen_struct_update_fn(mod_idx: int) -> str:
    rn = record_name(mod_idx, 0)
    f0 = fn_name(mod_idx, 0)
    f1 = fn_name(mod_idx, 1)
    return (
        f"pub fun make_and_update{mod_idx}(x: Int) -> Int = {{\n"
        f"    let r = {f0}(x);\n"
        f"    let r2 = {{ r | f0 = 99 }};\n"
        f"    {f1}(r2)\n"
        f"}}"
    )


def gen_guarded_match_fn(mod_idx: int) -> str:
    en = enum_name(mod_idx, 0)
    v0 = variant_name(mod_idx, 0, 0)
    v1 = variant_name(mod_idx, 0, 1)
    # Only match 2 of 4 variants explicitly (with guards), let _ catch the rest
    # to work around compiler bug where guards don't affect redundancy checking
    return (
        f"pub fun guarded{mod_idx}(x: Int) -> Int = {{\n"
        f"    let e: {en} = {v0}(x);\n"
        f"    match e {{\n"
        f"        {v0}(n) if n > 0 => n,\n"
        f"        {v1}(a, b) if a > b => a,\n"
        f"        _ => 0,\n"
        f"    }}\n"
        f"}}"
    )


def gen_or_pattern_fn(mod_idx: int) -> str:
    en = enum_name(mod_idx, 0)
    v0 = variant_name(mod_idx, 0, 0)
    v1 = variant_name(mod_idx, 0, 1)
    return (
        f"pub fun classify{mod_idx}(x: Int) -> Int = {{\n"
        f"    let e: {en} = {v0}(x);\n"
        f"    match e {{\n"
        f"        {v0}(_) | {v1}(_, _) => 1,\n"
        f"        _ => 0,\n"
        f"    }}\n"
        f"}}"
    )


def gen_nested_match_fn(mod_idx: int) -> str:
    en = enum_name(mod_idx, 0)
    v0 = variant_name(mod_idx, 0, 0)
    otn = opt_type_name(mod_idx)
    sn = some_name(mod_idx)
    nn = none_name(mod_idx)
    return (
        f"pub fun nested{mod_idx}(x: Int) -> Int = {{\n"
        f"    let o: {otn}[{en}] = {sn}({v0}(x));\n"
        f"    match o {{\n"
        f"        {sn}({v0}(n)) => n,\n"
        f"        {sn}(_) => 1,\n"
        f"        {nn} => 0,\n"
        f"    }}\n"
        f"}}"
    )


def gen_result_fns(mod_idx: int) -> list[str]:
    return [
        (
            f"pub fun fallible{mod_idx}(x: Int) -> Result[String, Int] = {{\n"
            f"    let a = Ok(x)?;\n"
            f"    let b = Ok(a + 1)?;\n"
            f"    Ok(b)\n"
            f"}}\n"
            f"\n"
            f"pub fun use_fallible{mod_idx}(x: Int) -> Int = match fallible{mod_idx}(x) {{\n"
            f"    Ok(v) => v,\n"
            f"    Err(_) => 0,\n"
            f"}}"
        )
    ]


def gen_mutual_recursion(mod_idx: int) -> str:
    return (
        f"pub fun even{mod_idx}(n: Int) -> Bool = if n == 0 {{ true }} else {{ odd{mod_idx}(n - 1) }}\n"
        f"\n"
        f"pub fun odd{mod_idx}(n: Int) -> Bool = if n == 0 {{ false }} else {{ even{mod_idx}(n - 1) }}"
    )


def gen_explicit_typeapp_fns(mod_idx: int) -> list[str]:
    rn = record_name(mod_idx, 0)
    f0 = fn_name(mod_idx, 0)
    f1 = fn_name(mod_idx, 1)
    return [
        (
            f"pub fun id{mod_idx}[a](x: a) -> a = x\n"
            f"\n"
            f"pub fun use_id{mod_idx}(x: Int) -> Int = {{\n"
            f"    let a = id{mod_idx}[Int](x);\n"
            f"    let r = id{mod_idx}[{rn}]({f0}(a));\n"
            f"    {f1}(r)\n"
            f"}}"
        )
    ]


def gen_shadowing_fn(mod_idx: int) -> str:
    f0 = fn_name(mod_idx, 0)
    f1 = fn_name(mod_idx, 1)
    return (
        f"pub fun shadow{mod_idx}(x: Int) -> Int = {{\n"
        f"    let r = {f0}(x);\n"
        f"    let x = {f1}(r);\n"
        f"    let x = x + 1;\n"
        f"    let x = x * 2;\n"
        f"    x\n"
        f"}}"
    )


def gen_deep_update_type_and_fn(mod_idx: int) -> str:
    """Nested record types + a fn that exercises `with { a.b.c = ... }` deep update."""
    i = mod_idx
    return (
        f"pub type City{i} = {{ zip: Int, street: Int }} deriving (Eq)\n"
        f"pub type Addr{i} = {{ city: City{i}, code: Int }} deriving (Eq)\n"
        f"pub type User{i} = {{ addr: Addr{i}, age: Int }} deriving (Eq)\n"
        f"\n"
        f"pub fun deep_update{i}(x: Int) -> Int = {{\n"
        f"    let u = User{i} {{ addr = Addr{i} {{ city = City{i} {{ zip = 0, street = 0 }}, code = x }}, age = 0 }};\n"
        f"    let u2 = u with {{ addr.city.zip = 94103, addr.city.street = 7, age = x }};\n"
        f"    u2.addr.city.zip + u2.addr.city.street + u2.age\n"
        f"}}"
    )


def gen_hkt_list_fn(mod_idx: int) -> str:
    """Prelude map/flat_map/fold on List — exercises Functor/Monad/Foldable dispatch."""
    i = mod_idx
    return (
        f"pub fun hkt_list{i}(x: Int) -> Int = {{\n"
        f"    let xs = Cons(x, Cons(x + 1, Cons(x + 2, Nil)));\n"
        f"    let ys = map(xs, n -> n * 2);\n"
        f"    let zs = flat_map(ys, n -> Cons(n, Cons(n + 1, Nil)));\n"
        f"    fold(zs, 0, (acc, n) -> acc + n)\n"
        f"}}"
    )


def gen_hkt_typeapp_fn(mod_idx: int) -> str:
    """Explicit TypeApp on prelude HKT method — exercises 4ade8743/77b74dc1 elaboration."""
    i = mod_idx
    return (
        f"pub fun hkt_typeapp{i}(x: Int) -> Int = {{\n"
        f"    let xs = Cons(x, Cons(x + 1, Nil));\n"
        f'    let ys: List[String] = map[List, Int, String](xs, n -> "v");\n'
        f"    fold(ys, 0, (acc, s) -> acc + 1)\n"
        f"}}"
    )


def gen_list_concat_fn(mod_idx: int) -> str:
    """`+` desugar through Semigroup on List."""
    i = mod_idx
    return (
        f"pub fun list_concat{i}(x: Int) -> Int = {{\n"
        f"    let a = Cons(x, Cons(x + 1, Nil));\n"
        f"    let b = Cons(x + 2, Cons(x + 3, Nil));\n"
        f"    let c = a + b;\n"
        f"    fold(c, 0, (acc, n) -> acc + n)\n"
        f"}}"
    )


def gen_vec_ops_fn(mod_idx: int) -> str:
    """Vec builder/freeze + take/drop/reverse/zip — exercises canonical-type overloads."""
    i = mod_idx
    return (
        f"pub fun vec_ops{i}(x: Int) -> Int = {{\n"
        f"    let b0 = builder();\n"
        f"    let b1 = push(b0, x);\n"
        f"    let b2 = push(b1, x + 1);\n"
        f"    let b3 = push(b2, x + 2);\n"
        f"    let b4 = push(b3, x + 3);\n"
        f"    let v: Vec[Int] = freeze(b4);\n"
        f"    let t = take(v, 3);\n"
        f"    let d = drop(v, 1);\n"
        f"    let r = reverse(v);\n"
        f"    let z = zip(t, d);\n"
        f"    len(t) + len(d) + len(r) + len(z)\n"
        f"}}"
    )


def gen_map_ops_fn(mod_idx: int) -> str:
    """Persistent Map via MapBuilder — exercises linear builder flow + overload mangler."""
    i = mod_idx
    return (
        f"pub fun map_ops{i}(x: Int) -> Int = {{\n"
        f"    let b0 = map_builder();\n"
        f"    let b1 = map_put(b0, x, x + 1);\n"
        f"    let b2 = map_put(b1, x + 1, x + 2);\n"
        f"    let b3 = map_put(b2, x + 2, x + 3);\n"
        f"    let m: Map[Int, Int] = map_freeze(b3);\n"
        f"    let got = match get(m, x + 1) {{\n"
        f"        Some(v) => v,\n"
        f"        None => 0,\n"
        f"    }};\n"
        f"    got + size(m)\n"
        f"}}"
    )


def gen_overloads_block(mod_idx: int) -> str:
    """Three process{i} overloads (first-param) + two tag{i} overloads (second-param) + consumer."""
    i = mod_idx
    rn = record_name(mod_idx, 0)
    en = enum_name(mod_idx, 0)
    v0 = variant_name(mod_idx, 0, 0)
    v1 = variant_name(mod_idx, 0, 1)
    bn = box_name(mod_idx)
    f0 = fn_name(mod_idx, 0)
    return (
        f"pub fun process{i}(r: {rn}) -> Int = r.f0 + r.f1 + r.f2\n"
        f"\n"
        f"pub fun process{i}(e: {en}) -> Int = match e {{\n"
        f"    {v0}(n) => n,\n"
        f"    {v1}(a, b) => a + b,\n"
        f"    _ => 0,\n"
        f"}}\n"
        f"\n"
        f"pub fun process{i}(b: {bn}[Int]) -> Int = match b {{ {bn}(n) => n * 2 }}\n"
        f"\n"
        f"pub fun tag{i}(x: Int, marker: {rn}) -> Int = x + marker.f0\n"
        f"\n"
        f"pub fun tag{i}(x: Int, marker: {en}) -> Int = x + match marker {{\n"
        f"    {v0}(n) => n,\n"
        f"    _ => 0,\n"
        f"}}\n"
        f"\n"
        f"pub fun use_overloads{i}(x: Int) -> Int = {{\n"
        f"    let r = {f0}(x);\n"
        f"    let e: {en} = {v0}(x);\n"
        f"    let bx = {bn}(x + 1);\n"
        f"    let a = process{i}(r) + process{i}(e) + process{i}(bx);\n"
        f"    let b = tag{i}(x, r) + tag{i}(x, e);\n"
        f"    a + b\n"
        f"}}"
    )


def gen_xprocess_bridge(mod_idx: int, deps: list) -> str:
    """Cross-module imported-overload under a shared alias — requires len(deps) >= 2.

    Forces the typechecker to disambiguate `xprocess` by first-param canonical
    type across two imports of the same name from two different modules.
    Not called from main — kept alive by being `pub` so typecheck/lower still
    process it.
    """
    dep0, dep1 = deps[0], deps[1]
    dep0_rn = record_name(dep0, 0)
    dep1_rn = record_name(dep1, 0)
    return (
        f"pub fun xprocess_bridge{mod_idx}(a: {dep0_rn}, b: {dep1_rn}) -> Int = "
        f"xprocess(a) + xprocess(b)"
    )


def gen_via_monad_fn(mod_idx: int) -> str:
    """Generic fn constrained by Monad using map/pure via superclass projection."""
    i = mod_idx
    return (
        f"pub fun via_monad{i}[f[_], a](fa: f[a], g: (a) -> a) -> f[a] where f: Monad =\n"
        f"    flat_map(fa, x -> map(pure(g(x)), g))\n"
        f"\n"
        f"pub fun use_via_monad{i}(x: Int) -> Int = {{\n"
        f"    let xs: List[Int] = Cons(x, Cons(x + 1, Nil));\n"
        f"    fold(via_monad{i}(xs, n -> n + 1), 0, (acc, n) -> acc + n)\n"
        f"}}"
    )


def gen_multi_param_codec(mod_idx: int) -> str:
    """Two-parameter trait with superclass entailment through Metric{i}."""
    i = mod_idx
    tn = trait_name(mod_idx)
    tn_lower = tn.lower()
    rn = record_name(mod_idx, 0)
    f0 = fn_name(mod_idx, 0)
    return (
        f"pub trait Codec{i}[fmt, ty] where ty: {tn} {{\n"
        f"    fun encode{i}(x: ty, fmt_hint: fmt) -> Int\n"
        f"}}\n"
        f"\n"
        f"impl Codec{i}[Int, {rn}] {{\n"
        f"    fun encode{i}(x: {rn}, fmt_hint: Int) -> Int = {tn_lower}(x) + fmt_hint\n"
        f"}}\n"
        f"\n"
        f"pub fun describe{i}[fmt, ty](x: ty, fmt_hint: fmt) -> Int where Codec{i}[fmt, ty] =\n"
        f"    {tn_lower}(x) + encode{i}(x, fmt_hint)\n"
        f"\n"
        f"pub fun use_describe{i}(x: Int) -> Int = {{\n"
        f"    let r = {f0}(x);\n"
        f"    describe{i}(r, x)\n"
        f"}}"
    )


def gen_use_hkt_fn(mod_idx: int) -> str:
    bn = box_name(mod_idx)
    fn = f"map{mod_idx}"
    return (
        f"pub fun use_mappable{mod_idx}(x: Int) -> Int = {{\n"
        f"    let boxed = {bn}(x);\n"
        f"    match {fn}(boxed, n -> n + 1) {{\n"
        f"        {bn}(v) => v,\n"
        f"    }}\n"
        f"}}"
    )


def gen_use_constrained_fn(mod_idx: int) -> str:
    tn = trait_name(mod_idx)
    rn = record_name(mod_idx, 0)
    sn = some_name(mod_idx)
    return (
        f"pub fun use_constrained{mod_idx}(x: Int) -> Int = {{\n"
        f"    let r = {rn} {{ f0 = x, f1 = x, f2 = x }};\n"
        f"    let wrapped = {sn}(r);\n"
        f"    {tn.lower()}(wrapped)\n"
        f"}}"
    )


def gen_use_extended_fn(mod_idx: int) -> str:
    f0 = fn_name(mod_idx, 0)
    stn = f"Extended{mod_idx}"
    return (
        f"pub fun use_extended{mod_idx}(x: Int) -> Int = {{\n"
        f"    let r = {f0}(x);\n"
        f"    {stn.lower()}(r)\n"
        f"}}"
    )


# ---------------------------------------------------------------------------
# Cross-module functions
# ---------------------------------------------------------------------------

def gen_cross_module_fns(mod_idx: int, imports: list[int], fn_start: int) -> list[str]:
    """Generate functions that use types/fns from imported modules."""
    fns = []
    for idx, dep in enumerate(imports[:5]):
        dep_rn = record_name(dep, 0)
        dep_fn = fn_name(dep, 1)
        fn_idx = fn_start + len(fns)

        if idx == 0:
            # Original: construct dep record, call dep function
            fns.append(
                f"pub fun {fn_name(mod_idx, fn_idx)}(x: Int) -> Int = {{\n"
                f"    let r = {dep_rn} {{ f0 = x, f1 = x + 1, f2 = x + 2 }};\n"
                f"    {dep_fn}(r)\n"
                f"}}"
            )
        elif idx == 1:
            # Cross-module pattern match with guards on dep's enum
            dep_en = enum_name(dep, 0)
            dep_v0 = variant_name(dep, 0, 0)
            fns.append(
                f"pub fun {fn_name(mod_idx, fn_idx)}(x: Int) -> Int = {{\n"
                f"    let e: {dep_en} = {dep_v0}(x);\n"
                f"    match e {{\n"
                f"        {dep_v0}(n) if n > 0 => n,\n"
                f"        _ => 0,\n"
                f"    }}\n"
                f"}}"
            )
        elif idx == 2:
            # Cross-module: wrap dep's record in own Opt, nested match
            sn = some_name(mod_idx)
            nn = none_name(mod_idx)
            otn = opt_type_name(mod_idx)
            fns.append(
                f"pub fun {fn_name(mod_idx, fn_idx)}(x: Int) -> Int = {{\n"
                f"    let r = {dep_rn} {{ f0 = x, f1 = x + 1, f2 = x + 2 }};\n"
                f"    let o: {otn}[{dep_rn}] = {sn}(r);\n"
                f"    match o {{\n"
                f"        {sn}(r) => {dep_fn}(r),\n"
                f"        {nn} => 0,\n"
                f"    }}\n"
                f"}}"
            )
        elif idx == 3:
            # Cross-module trait usage
            dep_tn = trait_name(dep)
            dep_rn = record_name(dep, 0)
            fns.append(
                f"pub fun {fn_name(mod_idx, fn_idx)}(x: Int) -> Int = {{\n"
                f"    let r = {dep_rn} {{ f0 = x, f1 = x + 1, f2 = x + 2 }};\n"
                f"    {dep_tn.lower()}(r)\n"
                f"}}"
            )
        else:
            # Cross-module struct update
            fns.append(
                f"pub fun {fn_name(mod_idx, fn_idx)}(x: Int) -> Int = {{\n"
                f"    let r = {dep_rn} {{ f0 = x, f1 = x + 1, f2 = x + 2 }};\n"
                f"    let r2 = {{ r | f0 = 42 }};\n"
                f"    {dep_fn}(r2)\n"
                f"}}"
            )
    return fns


# ---------------------------------------------------------------------------
# Module assembly
# ---------------------------------------------------------------------------

def gen_module(mod_idx: int, num_types: int, num_fns: int, deps: list[int]) -> str:
    lines = []

    # Imports
    for dep in deps:
        # Import record, field accessor, enum, first variant, and trait
        dep_rn = record_name(dep, 0)
        dep_fn = fn_name(dep, 1)
        dep_en = enum_name(dep, 0)
        dep_v0 = variant_name(dep, 0, 0)
        dep_tn = trait_name(dep)
        imports = [dep_rn, dep_fn, dep_en, dep_v0, dep_tn, dep_tn.lower()]
        lines.append(f"import {mod_name(dep)}.{{{', '.join(imports)}}}")

    # Stdlib imports for vec/map ops (every module). Map builder/put/freeze are
    # aliased to avoid shadowing Vec's same-named overloads; Vec's are left
    # unaliased so the canonical-type overload resolver picks between
    # `~VecBuilder[a]` and `~MapBuilder[k, v]` arms at each call site.
    lines.append("import core/vec.{Vec, builder, push, freeze, take, drop, reverse, zip, len}")
    lines.append(
        "import core/map.{builder as map_builder, put as map_put, "
        "freeze as map_freeze, get, size}"
    )

    # Monad trait is not in the prelude; import it when we emit via_monad.
    if mod_idx % 3 == 0:
        lines.append("import core/monad.{Monad}")

    # Cross-module overload-under-single-alias: same bare name from two
    # different modules, resolved by first-param canonical type.
    if len(deps) >= 2:
        dep0, dep1 = deps[0], deps[1]
        lines.append(f"import {mod_name(dep0)}.{{process{dep0} as xprocess}}")
        lines.append(f"import {mod_name(dep1)}.{{process{dep1} as xprocess}}")

    lines.append("")

    # Types: records
    num_records = max(1, num_types // 2)
    num_enums = max(1, num_types - num_records - 1)

    for t in range(num_records):
        lines.append(gen_record(mod_idx, t))

    lines.append("")

    # Types: enums (4 variants for richer matching)
    for t in range(num_enums):
        lines.append(gen_enum(mod_idx, t, num_variants=4))

    lines.append("")

    # Types: generic box, option wrapper, pair
    lines.append(gen_generic_type(mod_idx))
    lines.append("")
    lines.append(gen_option_type(mod_idx))
    lines.append("")
    lines.append(gen_pair_type(mod_idx))
    lines.append("")

    # Nested record types + deep-update fn (shared-prefix `with` lowering).
    lines.append(gen_deep_update_type_and_fn(mod_idx))
    lines.append("")

    # Trait + impls
    lines.append(gen_trait(mod_idx))
    lines.append("")
    lines.append(gen_trait_impl_record(mod_idx, 0))
    lines.append("")
    if num_enums > 0:
        lines.append(gen_trait_impl_enum(mod_idx, 0))
        lines.append("")

    # HKT trait (every 5th module)
    has_hkt = mod_idx % 5 == 0
    if has_hkt:
        lines.append(gen_hkt_trait(mod_idx))
        lines.append("")

    # Constrained generic impl (every 3rd module)
    has_constrained = mod_idx % 3 == 0
    if has_constrained:
        lines.append(gen_constrained_impl(mod_idx))
        lines.append("")

    # Superclass trait (every 4th module)
    has_superclass = mod_idx % 4 == 0
    if has_superclass:
        lines.append(gen_superclass_trait(mod_idx))
        lines.append("")

    # Core functions (f_0 through f_N)
    for fn_str in gen_functions(mod_idx, num_fns, num_records):
        lines.append(fn_str)
        lines.append("")

    # New feature functions — all modules
    for fn_str in gen_tuple_fns(mod_idx):
        lines.append(fn_str)
        lines.append("")

    lines.append(gen_struct_update_fn(mod_idx))
    lines.append("")

    lines.append(gen_guarded_match_fn(mod_idx))
    lines.append("")

    lines.append(gen_or_pattern_fn(mod_idx))
    lines.append("")

    lines.append(gen_nested_match_fn(mod_idx))
    lines.append("")

    for fn_str in gen_result_fns(mod_idx):
        lines.append(fn_str)
        lines.append("")

    for fn_str in gen_explicit_typeapp_fns(mod_idx):
        lines.append(fn_str)
        lines.append("")

    lines.append(gen_shadowing_fn(mod_idx))
    lines.append("")

    # Stdlib HKT method dispatch on List (prelude-imported map/flat_map/fold)
    lines.append(gen_hkt_list_fn(mod_idx))
    lines.append("")

    # Explicit TypeApp on prelude HKT method
    lines.append(gen_hkt_typeapp_fn(mod_idx))
    lines.append("")

    # `+` desugar through Semigroup on List
    lines.append(gen_list_concat_fn(mod_idx))
    lines.append("")

    # Vec take/drop/reverse/zip + builder/freeze flow
    lines.append(gen_vec_ops_fn(mod_idx))
    lines.append("")

    # Persistent Map via MapBuilder
    lines.append(gen_map_ops_fn(mod_idx))
    lines.append("")

    # Same-name overload set keyed by first- and second-parameter type
    lines.append(gen_overloads_block(mod_idx))
    lines.append("")

    if len(deps) >= 2:
        lines.append(gen_xprocess_bridge(mod_idx, deps))
        lines.append("")

    # Generic fn constrained by Monad using map/pure via superclass projection
    if mod_idx % 3 == 0:
        lines.append(gen_via_monad_fn(mod_idx))
        lines.append("")

    # Multi-parameter trait with Metric{i} superclass entailment
    if mod_idx % 7 == 0:
        lines.append(gen_multi_param_codec(mod_idx))
        lines.append("")

    # Conditional feature functions
    if has_hkt:
        lines.append(gen_use_hkt_fn(mod_idx))
        lines.append("")

    if has_constrained:
        lines.append(gen_use_constrained_fn(mod_idx))
        lines.append("")

    if has_superclass:
        lines.append(gen_use_extended_fn(mod_idx))
        lines.append("")

    # Mutual recursion (every 6th module)
    has_mutual = mod_idx % 6 == 0
    if has_mutual:
        lines.append(gen_mutual_recursion(mod_idx))
        lines.append("")

    # Cross-module functions
    if deps:
        cross_fns = gen_cross_module_fns(mod_idx, deps, num_fns)
        for fn_str in cross_fns:
            lines.append(fn_str)
            lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main module generation
# ---------------------------------------------------------------------------

def gen_main(num_modules: int, num_fns: int) -> str:
    lines = []

    # Import from a spread of modules
    step = max(1, num_modules // 20)
    imported = list(range(0, num_modules, step))
    if not imported:
        imported = list(range(num_modules))

    for i in imported:
        # Build import list based on what the module has
        names = [
            record_name(i, 0),
            fn_name(i, 0),
            fn_name(i, 1),
            fn_name(i, 3),
            fn_name(i, 6),
            f"use_tuple{i}",
            f"make_and_update{i}",
            f"guarded{i}",
            f"nested{i}",
            f"use_fallible{i}",
            f"shadow{i}",
            f"use_id{i}",
            f"deep_update{i}",
            f"hkt_list{i}",
            f"hkt_typeapp{i}",
            f"list_concat{i}",
            f"vec_ops{i}",
            f"map_ops{i}",
            f"use_overloads{i}",
        ]
        if i % 5 == 0:
            names.append(f"use_mappable{i}")
        if i % 3 == 0:
            names.append(f"use_constrained{i}")
            names.append(f"use_via_monad{i}")
        if i % 4 == 0:
            names.append(f"use_extended{i}")
        if i % 7 == 0:
            names.append(f"use_describe{i}")
        lines.append(f"import {mod_name(i)}.{{{', '.join(names)}}}")

    lines.append("")
    lines.append("pub fun main() -> Unit = {")

    result_vars = []
    for idx, i in enumerate(imported):
        f0 = fn_name(i, 0)
        f1 = fn_name(i, 1)
        f3 = fn_name(i, 3)
        f6 = fn_name(i, 6)
        var = f"r{idx}"

        # Use the core functions
        lines.append(f"    let v{idx} = {f0}({idx});")
        lines.append(f"    let base{idx} = {f1}(v{idx}) + {f3}({idx}) + {f6}({idx}, 0);")

        # Use all the new feature functions
        lines.append(f"    let tup{idx} = use_tuple{i}({idx});")
        lines.append(f"    let upd{idx} = make_and_update{i}({idx});")
        lines.append(f"    let grd{idx} = guarded{i}({idx});")
        lines.append(f"    let nst{idx} = nested{i}({idx});")
        lines.append(f"    let fal{idx} = use_fallible{i}({idx});")
        lines.append(f"    let shd{idx} = shadow{i}({idx});")
        lines.append(f"    let tid{idx} = use_id{i}({idx});")
        lines.append(f"    let dup{idx} = deep_update{i}({idx});")
        lines.append(f"    let hkl{idx} = hkt_list{i}({idx});")
        lines.append(f"    let hkt{idx} = hkt_typeapp{i}({idx});")
        lines.append(f"    let lcc{idx} = list_concat{i}({idx});")
        lines.append(f"    let vop{idx} = vec_ops{i}({idx});")
        lines.append(f"    let mop{idx} = map_ops{i}({idx});")
        lines.append(f"    let ovl{idx} = use_overloads{i}({idx});")

        sum_parts = [f"base{idx}", f"tup{idx}", f"upd{idx}", f"grd{idx}",
                     f"nst{idx}", f"fal{idx}", f"shd{idx}", f"tid{idx}",
                     f"dup{idx}", f"hkl{idx}", f"hkt{idx}", f"lcc{idx}",
                     f"vop{idx}", f"mop{idx}", f"ovl{idx}"]

        # Conditional features
        if i % 5 == 0:
            lines.append(f"    let mpl{idx} = use_mappable{i}({idx});")
            sum_parts.append(f"mpl{idx}")
        if i % 3 == 0:
            lines.append(f"    let cst{idx} = use_constrained{i}({idx});")
            lines.append(f"    let vmd{idx} = use_via_monad{i}({idx});")
            sum_parts.append(f"cst{idx}")
            sum_parts.append(f"vmd{idx}")
        if i % 4 == 0:
            lines.append(f"    let ext{idx} = use_extended{i}({idx});")
            sum_parts.append(f"ext{idx}")
        if i % 7 == 0:
            lines.append(f"    let des{idx} = use_describe{i}({idx});")
            sum_parts.append(f"des{idx}")

        lines.append(f"    let {var} = {' + '.join(sum_parts)};")
        result_vars.append(var)

    # Sum all results and print — keeps every result live through DCE while
    # satisfying `main: Unit`.
    if result_vars:
        sums = " + ".join(result_vars)
        lines.append(f"    println({sums})")
    else:
        lines.append("    println(0)")

    lines.append("}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Generate Krypton compile benchmark")
    parser.add_argument("--modules", type=int, default=50, help="Number of modules (default: 50)")
    parser.add_argument("--types-per", type=int, default=5, help="Types per module (default: 5)")
    parser.add_argument("--fns-per", type=int, default=10, help="Functions per module (default: 10)")
    parser.add_argument("--out", type=str, default="bench/generated", help="Output directory")
    parser.add_argument("--seed", type=int, default=42, help="Random seed for reproducibility")
    args = parser.parse_args()

    random.seed(args.seed)

    out_dir = args.out
    if os.path.exists(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)

    total_lines = 0

    for i in range(args.modules):
        # Each module imports from earlier modules (DAG)
        # More deps for later modules (up to 5) to stress cross-module resolution
        if i == 0:
            deps = []
        else:
            max_deps = min(5, i) if i > 10 else min(3, i)
            num_deps = min(max_deps, i)
            deps = sorted(random.sample(range(i), num_deps))

        source = gen_module(i, args.types_per, args.fns_per, deps)
        path = os.path.join(out_dir, f"{mod_name(i)}.kr")
        with open(path, "w") as f:
            f.write(source)
        lines = source.count("\n") + 1
        total_lines += lines

    # Generate main.kr
    main_source = gen_main(args.modules, args.fns_per)
    main_path = os.path.join(out_dir, "main.kr")
    with open(main_path, "w") as f:
        f.write(main_source)
    total_lines += main_source.count("\n") + 1

    print(f"Generated {args.modules} modules + main.kr in {out_dir}/")
    print(f"Total: ~{total_lines} lines")
    print(f"\nTo benchmark:")
    print(f"  cargo run --release -- check {out_dir}/main.kr --timings")


if __name__ == "__main__":
    main()
