#!/usr/bin/env python3
"""Generate a large multi-file Krypton project for compile-time benchmarking.

Produces a DAG of modules (no circular imports) that exercise records, sum types,
traits, generics, pattern matching, closures, recursion, and cross-module usage.

Usage:
    python3 bench/gen_bench.py                          # defaults: 50 modules
    python3 bench/gen_bench.py --modules 200 --out /tmp/kr_bench
    cargo run --release -- check bench/generated/main.kr --timings
"""

import argparse
import os
import random
import shutil
import textwrap


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


def gen_record(mod_idx: int, type_idx: int, num_fields: int = 3) -> str:
    fields = ", ".join(f"f{j}: Int" for j in range(num_fields))
    name = record_name(mod_idx, type_idx)
    deriving = " deriving (Eq, Show)" if type_idx % 2 == 0 else ""
    return f"pub type {name} = {{ {fields} }}{deriving}"


def gen_enum(mod_idx: int, type_idx: int, num_variants: int = 3) -> str:
    name = enum_name(mod_idx, type_idx)
    variants = []
    for v in range(num_variants):
        vn = variant_name(mod_idx, type_idx, v)
        if v == 0:
            variants.append(f"{vn}(Int)")
        elif v == 1:
            variants.append(f"{vn}(Int, Int)")
        else:
            variants.append(vn)
    deriving = " deriving (Eq)" if type_idx % 2 == 0 else ""
    return f"pub type {name} = {' | '.join(variants)}{deriving}"


def gen_generic_type(mod_idx: int) -> str:
    name = f"Box{mod_idx}"
    return f"pub type {name}[a] = {name}(a)"


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
    v2 = variant_name(mod_idx, type_idx, 2)
    return (
        f"impl {tn}[{en}] {{\n"
        f"    fun {tn.lower()}(x: {en}) -> Int = match x {{\n"
        f"        {v0}(n) => n,\n"
        f"        {v1}(a, b) => a + b,\n"
        f"        {v2} => 0,\n"
        f"    }}\n"
        f"}}"
    )


def gen_functions(mod_idx: int, num_fns: int, num_record_types: int) -> list[str]:
    fns = []

    # f_0: constructor
    rn = record_name(mod_idx, 0)
    fields = ", ".join(f"f{j} = x + {j}" for j in range(3))
    fns.append(f"pub fun {fn_name(mod_idx, 0)}(x: Int) -> {rn} = {rn} {{ {fields} }}")

    # f_1: field access + arithmetic
    fns.append(
        f"pub fun {fn_name(mod_idx, 1)}(r: {rn}) -> Int = r.f0 + r.f1 + r.f2"
    )

    # f_2: pattern match on enum
    en = enum_name(mod_idx, 0)
    v0 = variant_name(mod_idx, 0, 0)
    v1 = variant_name(mod_idx, 0, 1)
    v2 = variant_name(mod_idx, 0, 2)
    fns.append(
        f"pub fun {fn_name(mod_idx, 2)}(e: {en}) -> Int = match e {{\n"
        f"    {v0}(n) => n * 2,\n"
        f"    {v1}(a, b) => a + b,\n"
        f"    {v2} => 0,\n"
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

    # f_5: trait-constrained generic
    tn = trait_name(mod_idx)
    fns.append(
        f"pub fun {fn_name(mod_idx, 5)}[a](x: a, y: a) -> Int where a: {tn} =\n"
        f"    {tn.lower()}(x) + {tn.lower()}(y)"
    )

    # f_6: recursive list-like computation via tail recursion
    fns.append(
        f"pub fun {fn_name(mod_idx, 6)}(n: Int, acc: Int) -> Int =\n"
        f"    if n <= 0 {{ acc }} else {{ recur(n - 1, acc + n) }}"
    )

    # f_7: compose closures
    fns.append(
        f"pub fun {fn_name(mod_idx, 7)}(x: Int) -> Int = {{\n"
        f"    let f = a -> a + 1;\n"
        f"    let g = a -> a * 3;\n"
        f"    let h = a -> g(f(a));\n"
        f"    h(h(x))\n"
        f"}}"
    )

    # f_8: use generic box type
    box_name = f"Box{mod_idx}"
    fns.append(
        f"pub fun {fn_name(mod_idx, 8)}(x: Int) -> Int = match {box_name}(x + 1) {{\n"
        f"    {box_name}(v) => v * 2,\n"
        f"}}"
    )

    # Fill remaining with simple arithmetic fns
    for i in range(9, num_fns):
        fns.append(
            f"pub fun {fn_name(mod_idx, i)}(x: Int) -> Int = x + {i * mod_idx}"
        )

    return fns


def gen_cross_module_fns(mod_idx: int, imports: list[int], fn_start: int) -> list[str]:
    """Generate functions that use types/fns from imported modules."""
    fns = []
    for dep in imports[:3]:  # use up to 3 dependencies
        dep_rn = record_name(dep, 0)
        dep_fn = fn_name(dep, 1)
        fn_idx = fn_start + len(fns)
        fns.append(
            f"pub fun {fn_name(mod_idx, fn_idx)}(x: Int) -> Int = {{\n"
            f"    let r = {dep_rn} {{ f0 = x, f1 = x + 1, f2 = x + 2 }};\n"
            f"    {dep_fn}(r)\n"
            f"}}"
        )
    return fns


def gen_module(mod_idx: int, num_types: int, num_fns: int, deps: list[int]) -> str:
    lines = []

    # Imports (only from modules with lower index = guaranteed DAG)
    for dep in deps:
        dep_rn = record_name(dep, 0)
        dep_fn = fn_name(dep, 1)
        lines.append(f"import {mod_name(dep)}.{{{dep_rn}, {dep_fn}}}")

    if deps:
        lines.append("")

    # Types
    num_records = max(1, num_types // 2)
    num_enums = max(1, num_types - num_records - 1)

    for t in range(num_records):
        lines.append(gen_record(mod_idx, t))

    lines.append("")

    for t in range(num_enums):
        lines.append(gen_enum(mod_idx, t))

    lines.append("")
    lines.append(gen_generic_type(mod_idx))
    lines.append("")

    # Trait + impls
    lines.append(gen_trait(mod_idx))
    lines.append("")
    lines.append(gen_trait_impl_record(mod_idx, 0))
    lines.append("")
    if num_enums > 0:
        lines.append(gen_trait_impl_enum(mod_idx, 0))
        lines.append("")

    # Functions
    for fn_str in gen_functions(mod_idx, num_fns, num_records):
        lines.append(fn_str)
        lines.append("")

    # Cross-module functions
    if deps:
        for fn_str in gen_cross_module_fns(mod_idx, deps, num_fns):
            lines.append(fn_str)
            lines.append("")

    return "\n".join(lines)


def gen_main(num_modules: int, num_fns: int) -> str:
    lines = []

    # Import from a spread of modules
    step = max(1, num_modules // 20)
    imported = list(range(0, num_modules, step))
    if not imported:
        imported = list(range(num_modules))

    for i in imported:
        rn = record_name(i, 0)
        f0 = fn_name(i, 0)
        f1 = fn_name(i, 1)
        f3 = fn_name(i, 3)
        f6 = fn_name(i, 6)
        lines.append(f"import {mod_name(i)}.{{{rn}, {f0}, {f1}, {f3}, {f6}}}")

    lines.append("")
    lines.append("pub fun main() -> Int = {")

    result_vars = []
    for idx, i in enumerate(imported):
        rn = record_name(i, 0)
        f0 = fn_name(i, 0)
        f1 = fn_name(i, 1)
        f3 = fn_name(i, 3)
        f6 = fn_name(i, 6)
        var = f"r{idx}"
        lines.append(f"    let v{idx} = {f0}({idx});")
        lines.append(f"    let {var} = {f1}(v{idx}) + {f3}({idx}) + {f6}({idx}, 0);")
        result_vars.append(var)

    # Sum all results
    if result_vars:
        sums = " + ".join(result_vars)
        lines.append(f"    {sums}")
    else:
        lines.append("    0")

    lines.append("}")
    return "\n".join(lines)


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
        # Each module imports from up to 3 earlier modules (DAG)
        if i == 0:
            deps = []
        else:
            num_deps = min(3, i)
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
