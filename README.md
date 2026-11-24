# a-to-ratio-lean

Author: Heywood Geblomi. Public snapshot built 24 November 2026.

## What this is

A small Lean 4 (v4.35.0) package. `Statement.lean` was frozen and hashed before `Proof.lean` was written. The statement is a toy two-torus model of one geodesic: it says a stored growth ratio is exactly 2:1. The proof is a plain `decide` check, with no Mathlib and no `native_decide`.

The exact 2:1 in this package depends on the toy model's sign choice. With physical signs the trace ratio is about 1.40. A is not a sub-action of M_plus.

This does not prove a global Masur-Veech exponent, and it does not claim that the toy matrices are the real H1+ action on a surface.

Source numbers come from `data/kz_along_A.json` in the public repo [HeywoodGeblomi/omega-ed6-h1plus-measure](https://github.com/HeywoodGeblomi/omega-ed6-h1plus-measure) at commit `b7c4a7a`, via `gen_matrix.py`.

## How to check it

You need Lean 4.35.0 (see `lean-toolchain`).

```
lake build
```

Or check the frozen hashes against the files in this directory:

```
sha256sum -c FROZEN_v1.sha256
sha256sum -c STATEMENT_FROZEN_v1.sha256
```

## Status

The Lean statements in `Proof.lean` go through `decide` on this toy model. Read `Statement.lean` for what is claimed and what is not. The hash files are the original frozen hashes, unchanged.

No files were skipped from the source tree.
