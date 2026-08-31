/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Corner orbits of an irregular tile

Lemma 2.9 of the paper. Its proof rests on one consequence of Theorem 2.7(3): no vertex lies
on two irregular tiles. Given that, a symmetry carrying a corner of an irregular tile `P` to
a corner of `P` must fix `P` setwise — `g • P` and `P` are both irregular tiles containing
the image corner, so they coincide. Everything else in the lemma is orbit counting on top of
that.

The statement is made for an abstract group action: `T` is the set of irregular tiles, `X`
the vertices, and `corners` is equivariant with pairwise disjoint values. No geometry is
used, which is why the lemma applies verbatim to every species in the paper.

## Main results

* `MinimalUniformity.smul_tile_eq_self` (Lemma 2.9, core): a symmetry moving a corner of `P`
  to a corner of `P` fixes `P`.
* `MinimalUniformity.smul_tile_eq_of_corners`: corners of irregular tiles in different tile
  orbits lie in different vertex orbits.
-/

namespace MinimalUniformity

open Pointwise

variable {G T X : Type*} [Group G] [MulAction G T] [MulAction G X]

/-- **Lemma 2.9, the core step.**

If `g` carries a corner of the irregular tile `P` to a corner of `P`, then `g` fixes `P`
setwise. Hence the corners of `P` meet the vertex orbits of the tiling in exactly the
`Stab G P`-orbits of corners. -/
theorem smul_tile_eq_self (corners : T → Set X)
    (hequiv : ∀ (g : G) (t : T), corners (g • t) = g • corners t)
    (hdisj : ∀ t t' : T, (corners t ∩ corners t').Nonempty → t = t')
    {g : G} {P : T} {x : X} (hx : x ∈ corners P) (hgx : g • x ∈ corners P) :
    g • P = P := by
  refine hdisj _ _ ⟨g • x, ?_, hgx⟩
  rw [hequiv]
  exact Set.smul_mem_smul_set hx

/-- **Lemma 2.9, the separation statement.**

If a symmetry carries a corner of `P` to a corner of `Q`, then it carries `P` to `Q`. So
irregular tiles in different `G`-orbits have their corners in disjoint vertex orbits, and the
number `r` of vertex orbits carrying irregular corners is the sum, over the orbits of
irregular tiles, of their corner class counts. -/
theorem smul_tile_eq_of_corners (corners : T → Set X)
    (hequiv : ∀ (g : G) (t : T), corners (g • t) = g • corners t)
    (hdisj : ∀ t t' : T, (corners t ∩ corners t').Nonempty → t = t')
    {g : G} {P Q : T} {x y : X} (hx : x ∈ corners P) (hy : y ∈ corners Q) (hg : y = g • x) :
    g • P = Q := by
  refine hdisj _ _ ⟨y, ?_, hy⟩
  rw [hequiv, hg]
  exact Set.smul_mem_smul_set hx

end MinimalUniformity
