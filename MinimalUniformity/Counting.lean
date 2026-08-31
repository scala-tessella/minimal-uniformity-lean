/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import MinimalUniformity.Lattice

/-!
# The counting arguments of Theorems 6.5 and 7.2

Both lower bounds for `(3².6²)` end in a chain of per-period counts. These are the steps
where a hand computation is least safe and a machine is most useful: each is a small linear
system over the tile, vertex and edge counts of a torus quotient, and the conclusion is
extracted by cancellation.

* Theorem 6.5(v), the simple category. With `t` triangles, `n₀` species vertices and `nA`,
  `nB` vertices of the tip and notch classes per translation cell, counting triangle corners
  by vertex type gives `nA = 2 nB`; the stabiliser count then pins the tile's period to
  `3` or `6`, and the hexagon-corner count forces `g = 12`, so the translation lattice has
  index `39` or `63` — excluded by `Lattice.lean`.
* Theorem 7.2, the convex category. With `t`, `h`, `r` triangles, hexagons and rhombi and
  `n₁`, `n₂`, `n₃` the vertices of the three types, Euler's relation on the torus together
  with the two hexagon-edge counts forces `h = r` and `n₁ = 0`: there is no species vertex,
  against condition (1) of Definition 2.5.

## Main results

* `MinimalUniformity.tips_eq_two_mul_notches`: `nA = 2 nB` (Theorem 6.5(v)).
* `MinimalUniformity.period_eq_three_or_six`: `p ∈ {3, 6}` (Theorem 6.5(v)).
* `MinimalUniformity.no_species_vertex`: `n₁ = 0` and `h = r` (Theorem 7.2).
* `MinimalUniformity.no_invariant_lattice`: the two surviving cells are not `D₆`-invariant.
-/

namespace MinimalUniformity

/-- **Theorem 6.5(v), the triangle-corner count.**

Every notch is species-apexed and every triangle lies in exactly one notch, so `t = 2 nB`
and `n₀ = nB`; counting the three corners of every triangle by the type of the vertex they
sit at gives `3t = 2n₀ + nA + 2nB`. Hence the tips outnumber the notches two to one. -/
theorem tips_eq_two_mul_notches {t n₀ nA nB : ℕ}
    (htri : t = 2 * nB) (hspecies : n₀ = nB)
    (hcorners : 3 * t = 2 * n₀ + nA + 2 * nB) :
    nA = 2 * nB := by omega

/-- **Theorem 6.5(v), the period.**

A hugged corner carries at most the mirror through it, so its class has `| Stab G P | / sE`
vertices for the `m = 3p - 6` letters `E`, with `| Stab G P | / sE` either `2p` or `p`.
Only `p = 6` and `p = 3` survive — in agreement with the corner-word enumeration, which
finds exactly the hexagram and the 30-gon. -/
theorem period_eq_three_or_six {p m : ℕ} (hm : 3 * p = m + 6) (hcase : m = 2 * p ∨ m = p) :
    p = 6 ∨ p = 3 := by
  rcases hcase with h | h <;> omega

/-- **Theorem 7.2, the convex category for `(3².6²)`.**

Each rhombus has two tips and two obtuse corners and irregular tiles are disjoint, so
`n₂ = n₃ = 2r`; each triangle has exactly one rhombus neighbour and each rhombus two
triangle neighbours, so `t = 2r`. Euler's relation on the torus, `∑_f (n_f - 2) = 2V`,
reads `t + 4h + 2r = 2(n₁ + n₂ + n₃)`. Counting hexagon edges gives `6h = t + 2r + 2H` with
`H` the hexagon–hexagon edges, and counting the ends of those edges — one at each `(3.3.6.6)`
vertex and at each tip, none at an obtuse corner — gives `2H = n₁ + n₂`.

Together these force `h = r` and `n₁ = 0`: the tiling has no all-regular vertex at all, so it
fails condition (1) of Definition 2.5 and is not in the class. -/
theorem no_species_vertex {t h r H n₁ n₂ n₃ : ℕ}
    (htips : n₂ = 2 * r) (hobtuse : n₃ = 2 * r) (htri : t = 2 * r)
    (heuler : t + 4 * h + 2 * r = 2 * (n₁ + n₂ + n₃))
    (hhexEdges : 6 * h = t + 2 * r + 2 * H)
    (hends : 2 * H = n₁ + n₂) :
    n₁ = 0 ∧ h = r := by omega

/-- **The end of Theorem 6.5.**

Every lattice point of a cell is a vertex, a hexagon centre, or interior to a copy of the
irregular tile, so the index of the translation lattice is `V + h + i · I(P)`. Pick's theorem
on the triangular lattice gives `I = 1` for the hexagram (area `12`, `B = 12`) and `I = 19`
for the 30-gon (area `66`, `B = 30`), so the index is `39` or `63`. Neither is of the form
`3^e n²`, so by Lemma 6.4 no such translation lattice exists, and no such tiling either. -/
theorem no_invariant_lattice (e n : ℕ) :
    3 ^ e * n ^ 2 ≠ 30 + 7 + 2 * 1 ∧ 3 ^ e * n ^ 2 ≠ 36 + 8 + 1 * 19 :=
  ⟨by simpa using ne_thirtyNine e n, by simpa using ne_sixtyThree e n⟩

end MinimalUniformity
