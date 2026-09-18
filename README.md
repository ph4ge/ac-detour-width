# Detour Width and Cycle Structure for the Andrews–Curtis Move Graph

Lean 4 formalization accompanying a Proof Track submission to the
[SAIR ACC Challenge](https://competition.sair.foundation/competitions/acc/proof-track).

## What this is

A geometric layer on top of the competition's `AC.lean`. It defines
**detour width** (the minimum, over all AC-move paths from the standard
presentation, of the maximum total relator length along the path),
**graph distance**, and the **two-hump property** as the existence of a
cycle whose height exceeds the endpoint's relator length.

The main result: **detour width and graph distance are independent**. No
function `f : ℕ → ℕ` satisfies `detourWidth R = f (graphDist R)` for all
reachable `R`. The proof is entirely machine-checked in Lean 4, with no
`sorry`s.

See [`submission.md`](submission.md) for the full description, definitions,
theorem list, and references.

## Files

- `ACStatement/AC.lean` — copy of the competition's shared definitions
  (unchanged).
- `ACStatement/DetourWidth.lean` — the geometric layer and all proved
  theorems.

## Build

Requires Lean 4 (`leanprover/lean4:v4.29.1`) and Mathlib
(revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6`).

```bash
lake exe cache get
lake build
