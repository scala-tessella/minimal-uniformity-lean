/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# The crystallographic exclusion behind Theorem 6.5

Lemma 6.4 of the paper classifies the sublattices of the triangular lattice `ℤ[ω]` invariant
under the full point group `D₆`: such a sublattice is an ideal `(α)` with `(α) = (ᾱ)`, and
its index is `3^e n²`. The counting step of Theorem 6.5 pins the translation lattice of a
hypothetical uniformity-≤ 4 member of `U(3².6²)` to index `39` or `63`; neither is of that
form, so no such tiling exists.

What is formalised here is the arithmetic that closes the argument. The obstruction is that
each of `39 = 3 · 13` and `63 = 3² · 7` carries a prime `≡ 1 (mod 3)` to the first power,
while a norm of the classified shape carries every prime other than `3` to an even power.
The general form below says it with the square dividing directly, which avoids invoking the
factorisation of `ℤ[ω]` and is what the two applications need.

The ideal-theoretic half of Lemma 6.4 — that `D₆`-invariance makes the sublattice a
conjugation-stable ideal of `ℤ[ω]`, whose norm therefore has this shape — is not formalised;
see the README.

## Main results

* `MinimalUniformity.ne_pow_three_mul_sq`: `3^e n² ≠ N` when some prime `p ∤ 3` divides `N`
  exactly once.
* `MinimalUniformity.ne_thirtyNine`, `MinimalUniformity.ne_sixtyThree`: the two indices the
  counting step produces are excluded.
-/

namespace MinimalUniformity

/-- If a prime `p` not dividing `3` divides `N` but `p²` does not, then `N` is not of the
form `3^e n²`: the prime would have to enter `n²`, hence `N`, to an even power. -/
theorem ne_pow_three_mul_sq {p N : ℕ} (hp : p.Prime) (h3 : ¬ p ∣ 3) (hdvd : p ∣ N)
    (hsq : ¬ (p * p) ∣ N) (e n : ℕ) : 3 ^ e * n ^ 2 ≠ N := by
  rintro rfl
  have hpn : p ∣ n := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd (hp.dvd_of_dvd_pow h) h3
    · exact hp.dvd_of_dvd_pow h
  obtain ⟨m, rfl⟩ := hpn
  exact hsq ⟨3 ^ e * m ^ 2, by ring⟩

/-- The hexagram's cell — `30` vertices, `7` hexagon centres and `2` copies of the tile with
one interior lattice point each — has `39` lattice points, and `39 = 3 · 13` is not an index
of a `D₆`-invariant sublattice. -/
theorem ne_thirtyNine (e n : ℕ) : 3 ^ e * n ^ 2 ≠ 39 :=
  ne_pow_three_mul_sq (p := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num) e n

/-- The 30-gon's cell — `36` vertices, `8` hexagon centres and one copy of the tile with `19`
interior lattice points — has `63` lattice points, and `63 = 3² · 7` is likewise excluded. -/
theorem ne_sixtyThree (e n : ℕ) : 3 ^ e * n ^ 2 ≠ 63 :=
  ne_pow_three_mul_sq (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) e n

end MinimalUniformity
