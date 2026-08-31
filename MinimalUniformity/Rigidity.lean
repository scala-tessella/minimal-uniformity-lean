/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import MinimalUniformity.Arc

/-!
# Rigidity: the forced irregular corner

Theorem 2.7(1) of the paper: at a vertex carrying an irregular tile, the regular tiles form
an arc of `z` whose angles sum to what that arc sums to in `z`, so the irregular corner is
forced — it carries exactly the angle sum of the complementary arc. Nothing is free, and the
tiling is metrically rigid.

Angles are measured in units of `π` and kept in `ℚ`, so every statement here is exact.

## Main results

* `MinimalUniformity.arcSum_rotate`: the angle sum is a cyclic invariant.
* `MinimalUniformity.irregular_corner` (Theorem 2.7(1)): `2 - arcSum u = arcSum v`.
-/

namespace MinimalUniformity

/-- The interior angle of a regular `p`-gon, in units of `π`. -/
def regAngle (p : ℕ) : ℚ := (p - 2 : ℚ) / p

/-- The angle sum of a word of regular tiles, in units of `π`. -/
def arcSum (w : List ℕ) : ℚ := (w.map regAngle).sum

/-- A species closes: its angles sum to `2π`, the condition defining the 21 vertex species. -/
def Closes (z : Species) : Prop := arcSum z = 2

@[simp] theorem arcSum_append (u v : List ℕ) : arcSum (u ++ v) = arcSum u + arcSum v := by
  simp [arcSum]

/-- The angle sum is unchanged by rotation: it is a property of the cycle, not of the reading. -/
@[simp] theorem arcSum_rotate (w : List ℕ) (n : ℕ) : arcSum (w.rotate n) = arcSum w :=
  ((w.rotate_perm n).map regAngle).sum_eq

/-- **Theorem 2.7(1), the forced irregular corner.**

Read the species from the vertex so that the regular arc `u` comes first, and let `v` be the
complementary arc. The regular tiles carry `arcSum u`, so the single irregular corner carries
the remaining `2 - arcSum u` — which is exactly `arcSum v`. The corner is determined by the
combinatorics alone, with no metric freedom left. -/
theorem irregular_corner {z : Species} {r : ℕ} {u v : List ℕ}
    (hz : Closes z) (hsplit : z.rotate r = u ++ v) :
    2 - arcSum u = arcSum v := by
  have h : arcSum u + arcSum v = 2 := by
    rw [← arcSum_append, ← hsplit, arcSum_rotate]; exact hz
  linarith

/-- The complementary reading: the regular arc carries what the irregular corner leaves. -/
theorem regular_arc {z : Species} {r : ℕ} {u v : List ℕ}
    (hz : Closes z) (hsplit : z.rotate r = u ++ v) :
    2 - arcSum v = arcSum u := by
  have h : arcSum u + arcSum v = 2 := by
    rw [← arcSum_append, ← hsplit, arcSum_rotate]; exact hz
  linarith

end MinimalUniformity
