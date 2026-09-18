# Detour Width and Cycle Structure for the Andrews–Curtis Move Graph

*Proof Track submission to the [SAIR ACC Challenge](https://competition.sair.foundation/competitions/acc/proof-track).*

## Summary

We formalize a geometric refinement of the Andrews–Curtis (AC) move graph
at fixed rank and prove that two natural invariants of that graph — detour
width and graph distance — are independent. The contribution is a partial
result toward AC, not a resolution of it, and it is entirely machine-checked
in Lean 4 on top of the competition's `AC.lean`
(commit `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e`).

## Definitions

For a balanced presentation `R` of rank `n`:

- **Graph distance** `graphDist R`: the minimum number of AC moves from the
  standard presentation `standard n` to `R`.
- **Detour width** `detourWidth R`: the minimum, over all AC-move paths from
  `standard n` to `R`, of the maximum total relator length attained anywhere
  along the path.

## Main theorem

No function `f : ℕ → ℕ` satisfies `detourWidth R = f (graphDist R)` for all
reachable `R`.

The proof exhibits two witnesses at rank 2:

- `R₁ = ⟨x⁻¹, y⟩`, reached from `⟨x, y⟩` by a single inversion.
  `graphDist R₁ = 1`, `detourWidth R₁ = 2`.
- `R₂ = ⟨x·y, y⟩`, reached by a single Nielsen move.
  `graphDist R₂ = 1`, `detourWidth R₂ = 3`.

Both sit at graph distance 1 from the standard presentation but have
different detour widths, so no such `f` exists.

## On the relationship between the two invariants

The two quantities measure different things, and their relationship is
**asymmetric**.

Graph distance does not bound detour width. A single AC move — conjugation
of a relator by an arbitrarily long word — produces arbitrarily large detour
width at graph distance 1 from the standard presentation.

Conversely, detour width does bound graph distance. Any presentation with
detour width `≤ D` lies within the finite set of presentations of total
relator length `≤ D`, so its graph distance is bounded by a function of `D`
alone (exponentially large in `D`, but finite).

The formalization establishes the direction that matters for the two-hump
phenomenon: **graph distance does not determine detour width**. This is what
the two witnesses `R₁` and `R₂` demonstrate.

## Two-hump as a cycle property

We formalize the *two-hump property* at `S` as the existence of a cycle —
two distinct AC-move paths from `standard n` to `S` — whose height (the
maximum relator length along either path) strictly exceeds `relLen S`. In
this framing, the two-hump phenomenon is precisely the statement that the
move graph contains cycles with a short-high arc and a long-low arc, so that
greedy descent on relator length and shortest-path search diverge. The two
witnesses above illustrate this in a minimal case: the inversion witness
stays at relator length 2, while the Nielsen witness climbs to 3.

## Motivation and connections

The two-hump phenomenon has been observed empirically in recent work on AC
search (Fagan et al., 2026). Our formalization sharpens what that observation
is *about*: it is a statement that detour width is not a function of graph
distance.

The connection to Calude–Stay (2008) — the bimodality of halting times for a
universal machine — is structural: both settings have a c.e. domain, an
unbounded witness, and a distribution concentrated at two extremes with a
thin middle. We do not claim a formal analogue; the correct measure-theoretic
setting (a harmonic measure of the random AC-walk) is a family indexed by the
Poisson boundary rather than a unique object, and we leave its construction
open.

## Machine-checked results

The Lean file establishes fifteen theorems:

**Structural properties of the move graph.**

1. `MovePath.reachable` — every data-carrying `MovePath` yields an
   `AC.Reachable` proof.
2. `MovePath.relLen_le_maxRelLen` — the relator length at the endpoint of a
   path is bounded by the maximum along the path.
3. `detourWidth_le_of_path` — a path with bounded max-relator-length bounds
   detour width from above.
4. `relLen_le_detourWidth` — detour width is bounded below by the endpoint's
   relator length.
5. `detourWidth_standard` — the standard presentation has detour width equal
   to its relator length.
6. `Cycle.detourWidth_le_height` — cycle height bounds detour width from
   above.

**Computations for the two witnesses.**

7. `relLen_R₁` — relator length of `R₁` is 2.
8. `relLen_R₂` — relator length of `R₂` is 3.
9. `detourWidth_R₁` — detour width of `R₁` is 2.
10. `detourWidth_R₂` — detour width of `R₂` is 3.
11. `graphDist_R₁` — graph distance of `R₁` is 1.
12. `graphDist_R₂` — graph distance of `R₂` is 1.

**Distinctness from the standard presentation.**

13. `R₁_ne_standard` — `R₁ ≠ standard 2`.
14. `R₂_ne_standard` — `R₂ ≠ standard 2`.

**Main theorem.**

15. `detourWidth_independent_of_graphDist` — no function `f : ℕ → ℕ`
    satisfies `detourWidth R = f (graphDist R)` for all reachable `R`.

## What remains open

The Bridson (2015) lower bound is on path *length*, not on the *peak relator
length* along the path. Connecting the two would require a Lipschitz bound
on total relator length per AC-move, which does not hold in general:
conjugation by an arbitrarily long word is a single move that can increase
relator length without bound. A restricted version — conjugations by
generators only — would admit a Lipschitz bound, but that restriction changes
the move graph. Whether the full AC move graph exhibits detour widths of
Bridson-type scale is open.

## References

- J. J. Andrews and M. L. Curtis, *Free groups and handlebodies*,
  Proc. Amer. Math. Soc. 16 (1965), 192–195.
- M. R. Bridson, *The complexity of balanced presentations and the
  Andrews–Curtis conjecture*, arXiv:1504.04187 (2015).
- C. S. Calude and M. A. Stay, *Most programs stop quickly or never halt*,
  Adv. Appl. Math. 40 (2008), 295–308.
- L. Fagan, M. Tarquini, A. Shehper, M. Manko, A. Gruen, C. Huang,
  G. Butbaia, D. Passaro, and S. Gukov, *The Two-Hump Problem: Bridging the
  Difficulty Gap in Mathematical Reinforcement Learning*, arXiv:2606.21611
  (2026). To appear at ICML 2026.
- SAIR competition `AC.lean`, commit
  `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e`.

All cited works are used for context and motivation only; no result of theirs
is re-derived or relied on for the proof. The formalization builds on the
SAIR `AC.lean` definitions (`Relators`, `Step`, `Reachable`, `standard`) and
adds the geometric layer described above.
