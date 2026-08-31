/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Arcs of a vertex species, and the permanence of word violations

This file formalises Definition 2.3 and the combinatorial core of Lemma 6.11 of

> M. Càllisto, *Minimal uniformity of the non-Archimedean vertex types in unit-edge tilings*
> (2026).

A vertex species `z` is a cyclic sequence of side counts. Condition (3) of Definition 2.5
asks that the regular tiles at every vertex, read in their cyclic order, form an *arc* of
`z` — a run of consecutive entries, read in either direction, possibly wrapping, and **not**
read up to rotation. So `[3, 3]` and `[6, 3, 3]` are arcs of `(3.3.6.6)` while `[3, 3]` is
not an arc of `(3.6.3.6)`: adjacency matters.

The single fact that carries Lemma 6.11 is that `IsArc z` is closed under taking contiguous
blocks (`IsArc.mono`). Its contrapositive, `not_isArc_of_block`, is the permanence
statement: a block whose word is not an arc of `z` cannot sit inside a legal vertex word, so
the violation it records survives into any refinement.

## Main results

* `MinimalUniformity.IsArc.mono`: an infix of an arc of `z` is an arc of `z`.
* `MinimalUniformity.not_isArc_of_block` (Lemma 6.11): a non-arc block refutes the word.
* `MinimalUniformity.not_isArc_of_notMem`: a letter outside `z`'s alphabet is a non-arc
  outright.
-/

namespace MinimalUniformity

/-- A vertex species: the cyclic sequence of side counts of the tiles around a vertex. -/
abbrev Species := List ℕ

/-- **Definition 2.3.** `w` is an *arc* of the cyclic sequence `z` if it occurs in `z` as a
run of consecutive entries, read in either direction. Rotations of `z` supply the runs that
wrap around the cycle; `z.reverse` supplies the ones read backwards. An arc has endpoints, so
it is not read up to rotation. -/
def IsArc (z w : Species) : Prop :=
  ∃ r ∈ Finset.range (z.length + 1), w <:+: z.rotate r ∨ w <:+: z.reverse.rotate r

instance (z w : Species) : Decidable (IsArc z w) := by
  unfold IsArc; infer_instance

/-- The whole cycle is an arc of itself: this is the all-regular vertex of condition (1). -/
theorem isArc_self (z : Species) : IsArc z z :=
  ⟨0, by simp, Or.inl (by simp)⟩

theorem isArc_nil (z : Species) : IsArc z [] :=
  ⟨0, by simp, Or.inl List.nil_infix⟩

/-- **A contiguous block of an arc of `z` is an arc of `z`.**

This is the step the proof of Lemma 6.11 turns on: "a contiguous block of an arc of the
cyclic `z` is a contiguous subword of `z`". -/
theorem IsArc.mono {z w u : Species} (h : IsArc z w) (hu : u <:+: w) : IsArc z u := by
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, hr, h.imp (fun hw => hu.trans hw) (fun hw => hu.trans hw)⟩

/-- **Lemma 6.11 (permanence of word violations), combinatorial core.**

If a contiguous block `u` of the vertex word `w` is not an arc of `z`, then `w` is not one
either — so condition (3) fails at that vertex. In the paper's application `u` is the block
formed by a split piece `Q` together with the original regular tiles adjacent to it: the
further pieces split off elsewhere sit outside the block in the cyclic order, so the block's
corners stay consecutive and the violation cannot be repaired by splitting more. -/
theorem not_isArc_of_block {z w u : Species} (hu : u <:+: w) (h : ¬ IsArc z u) : ¬ IsArc z w :=
  fun hw => h (hw.mono hu)

/-- A word using a letter outside the alphabet of `z` is not an arc of `z` — "a letter
outside `z`'s alphabet being a non-subword outright". -/
theorem not_isArc_of_notMem {z u : Species} {a : ℕ} (ha : a ∈ u) (hz : a ∉ z) :
    ¬ IsArc z u := by
  rintro ⟨r, -, h | h⟩
  · exact hz (List.mem_rotate.1 (h.subset ha))
  · exact hz (List.mem_reverse.1 (List.mem_rotate.1 (h.subset ha)))

end MinimalUniformity
