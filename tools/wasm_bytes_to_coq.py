#!/usr/bin/env python3
"""Emit a .wasm file's bytes as a Coq `list byte` literal.

Usage: wasm_bytes_to_coq.py <input.wasm> <output.v> <coq-def-name>

Generates a self-contained Coq file defining `<coq-def-name> : list byte`,
consumed by coq/AddCorrespondence.v to machine-check that WasmCert-Coq's
binary parser, applied to the exact bytes wat2wasm produced from add.wat,
yields the same AST as the hand-encoded term in coq/AddAst.v.
"""
import sys


def main() -> None:
    if len(sys.argv) != 4:
        print(f"usage: {sys.argv[0]} <input.wasm> <output.v> <coq-def-name>", file=sys.stderr)
        sys.exit(1)

    in_path, out_path, def_name = sys.argv[1], sys.argv[2], sys.argv[3]

    with open(in_path, "rb") as f:
        data = f.read()

    # WasmCert-Coq's binary_format_parser.v consumes Coq stdlib's
    # `Strings.Byte.byte` (256 constructors `x00`..`xff`), which is a
    # *different* type from WasmCert-Coq's own `bytes.v` byte (an alias for
    # CompCert's Integers.byte, used inside the AST/memory model). The
    # parser's token type shadows the Wasm one via import order, so this
    # file must use the stdlib hex constructors, not `%N` numerals.
    items = " :: ".join(f"x{b:02x}" for b in data)

    with open(out_path, "w") as f:
        f.write(
            "(* GENERATED FILE -- do not edit by hand.\n"
            f"   Produced by tools/wasm_bytes_to_coq.py from {in_path}.\n"
            "   Regenerate via `make bytes` after any change to add.wat. *)\n\n"
            "Require Import Strings.Byte.\n\n"
            f"Definition {def_name} : list byte := {items} :: nil.\n"
        )

    print(f"wrote {out_path} ({len(data)} bytes)")


if __name__ == "__main__":
    main()
