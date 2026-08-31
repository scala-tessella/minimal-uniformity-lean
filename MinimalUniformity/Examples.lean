/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import MinimalUniformity.Rigidity

/-!
# Non-vacuity checks

The examples of Definition 2.3 and the closing conditions of the species, checked by
evaluation. They keep the definitions honest: an `IsArc` that accepted everything, or a
`regAngle` off by a sign, would fail here.
-/

namespace MinimalUniformity

/-! ### Arcs (Definition 2.3) -/

/-- `(3.3)` is an arc of `(3.3.6.6)`. -/
example : IsArc [3, 3, 6, 6] [3, 3] := by decide

/-- `(6.3.3)` is an arc of `(3.3.6.6)` — an arc may wrap around the cycle. -/
example : IsArc [3, 3, 6, 6] [6, 3, 3] := by decide

/-- `(3.3)` is *not* an arc of `(3.6.3.6)`: adjacency matters. -/
example : ¬ IsArc [3, 6, 3, 6] [3, 3] := by decide

/-- `(4.3.4)` is not an arc of `(3.4.4.6)` — the word that refutes the vertex `(3.4.4ᵢ.4)`. -/
example : ¬ IsArc [3, 4, 4, 6] [4, 3, 4] := by decide

/-- `(10.3.10)` is not an arc of `(3.10.15)`: the word behind Remark 6.12, where the
irregular 36-gon presents a `144°` corner but the decagon it invites is illegal. -/
example : ¬ IsArc [3, 10, 15] [10, 3, 10] := by decide

/-- Both adjacent pairs of that word *are* legal arcs — the violation is a property of the
word, not of its letters taken two at a time. -/
example : IsArc [3, 10, 15] [10, 3] ∧ IsArc [3, 10, 15] [3, 10] := by
  constructor <;> decide

/-! ### The species close -/

example : Closes [3, 4, 4, 6] := by norm_num [Closes, arcSum, regAngle]

example : Closes [4, 5, 20] := by norm_num [Closes, arcSum, regAngle]

example : Closes [3, 3, 6, 6] := by norm_num [Closes, arcSum, regAngle]

example : Closes [3, 7, 42] := by norm_num [Closes, arcSum, regAngle]

/-! ### The forced corner

The `(3.4².6)` vertex `(3.4.12ᵢ)`: the regular arc `3.4` carries `60° + 90°`, so the
irregular corner carries `210°` — the `150°/60°` reading of the paper's example, in units
of `π`. -/
example : (2 : ℚ) - arcSum [3, 4] = arcSum [4, 6] := by
  norm_num [arcSum, regAngle]

end MinimalUniformity
