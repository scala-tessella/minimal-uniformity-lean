/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# The chamber bound of the class

Lemma 3.1 of the paper: a tiling of uniformity `k` in `U(z)` has at most `2k|z|` chambers.
The proof is a fibre count. A vertex orbit of valence `d` and stabiliser order `s` is a
`(1,2)`-orbit of `2d/s` chambers, and the chambers are partitioned by the vertex orbits; in
`U(z)` the species vertex has `|z|` tiles, and any other vertex has, by condition (3),
exactly one irregular tile and a regular arc of at most `|z| - 1` letters, so every valence
is at most `|z|` — valence-2 orbits included.

The argument is stated here free of Delaney–Dress specifics: `D` is the chamber set, `o`
assigns to each chamber its vertex orbit, and the two geometric inputs enter as hypotheses,
exactly as they are used in the paper's four-line proof.

## Main results

* `MinimalUniformity.card_le_two_mul_length_mul` (Lemma 3.1): `C ≤ 2 k |z|`.
* `MinimalUniformity.card_le_six_mul`, `MinimalUniformity.card_le_eight_mul`: the `6k` and
  `8k` readings for the three- and four-letter species.
-/

namespace MinimalUniformity

open Finset

/-- **Lemma 3.1, the chamber bound of the class.**

If each vertex orbit carries at most `2 * val q` chambers and every valence is at most
`zlen`, then the chamber count is at most `2 * zlen` times the number of vertex orbits. -/
theorem card_le_two_mul_length_mul {D Q : Type*} [Fintype D] [Fintype Q] [DecidableEq Q]
    (o : D → Q) (val : Q → ℕ) (zlen : ℕ)
    (hfiber : ∀ q, ((univ : Finset D).filter fun d => o d = q).card ≤ 2 * val q)
    (hval : ∀ q, val q ≤ zlen) :
    Fintype.card D ≤ 2 * zlen * Fintype.card Q := by
  classical
  have h : (univ : Finset D).card =
      ∑ q ∈ (univ : Finset Q), ((univ : Finset D).filter fun d => o d = q).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => mem_univ _
  have hle : ∑ q ∈ (univ : Finset Q), ((univ : Finset D).filter fun d => o d = q).card ≤
      ∑ _q ∈ (univ : Finset Q), 2 * zlen :=
    Finset.sum_le_sum fun q _ => (hfiber q).trans (Nat.mul_le_mul_left 2 (hval q))
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  rw [Fintype.card, h]
  calc ∑ q ∈ (univ : Finset Q), ((univ : Finset D).filter fun d => o d = q).card
      ≤ Fintype.card Q * (2 * zlen) := hle
    _ = 2 * zlen * Fintype.card Q := by ring

/-- The six three-letter species: at most `6k` chambers. -/
theorem card_le_six_mul {D Q : Type*} [Fintype D] [Fintype Q] [DecidableEq Q]
    (o : D → Q) (val : Q → ℕ)
    (hfiber : ∀ q, ((univ : Finset D).filter fun d => o d = q).card ≤ 2 * val q)
    (hval : ∀ q, val q ≤ 3) :
    Fintype.card D ≤ 6 * Fintype.card Q :=
  card_le_two_mul_length_mul o val 3 hfiber hval

/-- The four four-letter species: at most `8k` chambers. -/
theorem card_le_eight_mul {D Q : Type*} [Fintype D] [Fintype Q] [DecidableEq Q]
    (o : D → Q) (val : Q → ℕ)
    (hfiber : ∀ q, ((univ : Finset D).filter fun d => o d = q).card ≤ 2 * val q)
    (hval : ∀ q, val q ≤ 4) :
    Fintype.card D ≤ 8 * Fintype.card Q :=
  card_le_two_mul_length_mul o val 4 hfiber hval

end MinimalUniformity
