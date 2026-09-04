# Lean 4 formalization for *Minimal uniformity of the non-Archimedean vertex types in unit-edge tilings*

A Lean 4 + Mathlib formalization of the pen-and-paper mathematics of

> M. Càllisto, *Minimal uniformity of the non-Archimedean vertex types in unit-edge tilings*
> (2026).

That paper settles the minimal uniformity of all ten non-Archimedean vertex species. Its
lower bounds are exhaustive scans of Delaney–Dress symbol catalogues, certified complete by
DRAT-checked UNSAT proofs at up to two vertex orbits and by cross-validated enumeration
beyond; those computations are already certificate-backed and are **not** the target here.
What remained human-checked is the mathematics that *sharpens* the scans — the chamber
bound, the rigidity of the class, the corner-orbit lemma, the word-permanence lemma, and the
crystallographic and Euler counts that close `(3².6²)` in both categories. This repository
formalizes those.

It is a companion to, and deliberately separate from, the verification artifact, and a
sibling of the formalization for *The 31 types of vertex-transitive tilings of the plane by
convex unit-edge polygons*.

## Contents

| file | contents |
| --- | --- |
| `MinimalUniformity/Arc.lean` | arcs of a cyclic species (Definition 2.3) and **Lemma 6.11**, the permanence of word violations |
| `MinimalUniformity/Rigidity.lean` | exact angle sums and **Theorem 2.7(1)**, the forced irregular corner |
| `MinimalUniformity/ChamberBound.lean` | **Lemma 3.1**, the `2k\|z\|` chamber bound, with the `6k` and `8k` readings |
| `MinimalUniformity/CornerOrbits.lean` | **Lemma 2.9**, corner orbits of an irregular tile |
| `MinimalUniformity/Lattice.lean` | the arithmetic closing **Theorem 6.7**: `39` and `63` are not indices of a `D₆`-invariant sublattice |
| `MinimalUniformity/Counting.lean` | the per-period counts of **Theorem 6.7(v)** and **Theorem 7.2** |
| `MinimalUniformity/Examples.lean` | the arc and closure examples of the paper, checked by evaluation |

Everything is `sorry`-free and `native_decide`-free: each result depends only on `propext`,
`Classical.choice` and `Quot.sound`, and the two corner-orbit lemmas depend on no axioms at
all.

## Main statements

```lean
-- Lemma 6.11: a non-arc block refutes the vertex word, so the violation survives refinement
theorem not_isArc_of_block {z w u : Species} (hu : u <:+: w) (h : ¬ IsArc z u) : ¬ IsArc z w

-- Theorem 2.7(1): the irregular corner carries exactly the complementary arc
theorem irregular_corner {z : Species} {r : ℕ} {u v : List ℕ}
    (hz : Closes z) (hsplit : z.rotate r = u ++ v) : 2 - arcSum u = arcSum v

-- Lemma 3.1: a tiling of uniformity k in U(z) has at most 2k|z| chambers
theorem card_le_two_mul_length_mul (o : D → Q) (val : Q → ℕ) (zlen : ℕ)
    (hfiber : ∀ q, ((univ : Finset D).filter fun d => o d = q).card ≤ 2 * val q)
    (hval : ∀ q, val q ≤ zlen) :
    Fintype.card D ≤ 2 * zlen * Fintype.card Q

-- Lemma 2.9: a symmetry moving a corner of P to a corner of P fixes P
theorem smul_tile_eq_self (corners : T → Set X)
    (hequiv : ∀ (g : G) (t : T), corners (g • t) = g • corners t)
    (hdisj : ∀ t t' : T, (corners t ∩ corners t').Nonempty → t = t')
    {g : G} {P : T} {x : X} (hx : x ∈ corners P) (hgx : g • x ∈ corners P) : g • P = P

-- Theorem 7.2: the convex counting for (3².6²) leaves no species vertex
theorem no_species_vertex {t h r H n₁ n₂ n₃ : ℕ}
    (htips : n₂ = 2 * r) (hobtuse : n₃ = 2 * r) (htri : t = 2 * r)
    (heuler : t + 4 * h + 2 * r = 2 * (n₁ + n₂ + n₃))
    (hhexEdges : 6 * h = t + 2 * r + 2 * H) (hends : 2 * H = n₁ + n₂) :
    n₁ = 0 ∧ h = r

-- Theorem 6.7: neither surviving cell can carry a D₆-invariant translation lattice
theorem no_invariant_lattice (e n : ℕ) :
    3 ^ e * n ^ 2 ≠ 30 + 7 + 2 * 1 ∧ 3 ^ e * n ^ 2 ≠ 36 + 8 + 1 * 19
```

## What is deliberately not formalized

The repository formalizes the *arguments*, not the searches, and states the geometric inputs
as hypotheses — the same division of labour as its sibling repository. Specifically:

- **The symbol enumerations** (Theorems 3.2 and 6.1, and every catalogue scan). These are
  DRAT-certified or cross-validated in the artifact; re-deriving them in Lean would need
  `native_decide` and would replace a machine-checkable certificate with a weaker one.
- **The ideal-theoretic half of Lemma 6.6** — that `D₆`-invariance makes a sublattice of
  `ℤ[ω]` a conjugation-stable ideal, whose norm is therefore `3^e n²`. `Lattice.lean`
  formalizes the exclusion that consumes it, in a form (`p ∣ N`, `p² ∤ N`, `p ∤ 3`) that
  needs no factorisation of `ℤ[ω]`.
- **Pick's theorem on the triangular lattice**, used to get `I = 1` and `I = 19` for the two
  surviving tiles. Mathlib has no Pick's theorem; the two interior counts enter
  `no_invariant_lattice` as the literals `2 * 1` and `1 * 19`.
- **"An equiangular equilateral polygon is regular"**, the geometric last step of Lemma 2.9.
  `CornerOrbits.lean` proves the group-theoretic core the paper's proof actually turns on.
- **The realization certificates** (Proposition 4.1) and the exact cyclotomic closure tests.

## Building

```bash
lake exe cache get
lake build
```

The toolchain is pinned: `lean-toolchain` fixes Lean 4 v4.33.1 and `lake-manifest.json` fixes the
Mathlib revision, so the build a reader reproduces is the build that was checked.

## Archival

Deposited on Zenodo as a supplement to the paper record. **Cite the version DOI of the release you
checked**, not the all-versions concept DOI
[10.5281/zenodo.22239307](https://doi.org/10.5281/zenodo.22239307) — the latter always resolves to
whatever is newest:

| Version | DOI |
|---|---|
| 0.1.2 | [10.5281/zenodo.22307540](https://doi.org/10.5281/zenodo.22307540) |
| 0.1.1 | [10.5281/zenodo.22239308](https://doi.org/10.5281/zenodo.22239308) |

Zenodo assigns a release's version DOI at the moment that release is published, so it cannot be
present in the tree that release archives: the `CITATION.cff` inside a deposit carries no version
DOI. The version DOI is recorded in this table, and in `CITATION.cff` on the main branch, in the
first commit after the tag.

The companion computational artifact, deliberately separate from this formalization, is
[minimal-uniformity-three](https://github.com/scala-tessella/minimal-uniformity-three) v0.2.0,
[10.5281/zenodo.22238750](https://doi.org/10.5281/zenodo.22238750).
