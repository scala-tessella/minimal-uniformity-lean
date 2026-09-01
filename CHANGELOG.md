# Changelog

All notable changes to `minimal-uniformity-lean` are documented here.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). A release is archived on
Zenodo when its GitHub release is published, and it is the archived release — not this branch — that a
citation must name; the DOIs are in the README's archival section.

## [0.1.1] — 2026-09-02

**The archivable release.** No mathematics changed: every statement, proof and axiom footprint is the
one 0.1.0 carried. What the formalization lacked was an identity of its own in an archive.

### Added

- `CITATION.cff`, from which Zenodo takes a deposit's title, abstract, authorship and ORCID. A tree
  without one is archived under its repository slug and credited to a bare account, and the file has
  to be inside the tree the release archives — it cannot be supplied afterwards without the deposit
  and the source disagreeing. It also names the companion computational artifact
  (minimal-uniformity-three v0.2.0, 10.5281/zenodo.22238750) as a related work.
- `CHANGELOG.md`, this file.
- The README's archival section: where the version DOI is recorded, and why it cannot be present in
  the tree its own release archives.
- The README's statement that the toolchain is pinned twice over — `lean-toolchain` at Lean 4 v4.33.1,
  `lake-manifest.json` at the Mathlib revision — so `lake exe cache get && lake build` reproduces the
  build that was checked, not merely a build.

## [0.1.0] — 2026-08-31

**The formalization.** The pen-and-paper core of "Minimal uniformity of the non-Archimedean vertex
types in unit-edge tilings": the mathematics that sharpens the paper's exhaustive scans, as opposed
to the scans themselves, which are certificate-backed in the computational artifact.

### Added

- `Arc.lean` — arcs of a cyclic species (Definition 2.3) and Lemma 6.11, the permanence of word
  violations under refinement.
- `Rigidity.lean` — exact angle sums and Theorem 2.7(1), the forced irregular corner.
- `ChamberBound.lean` — Lemma 3.1, the `2k|z|` chamber bound, with its `6k` and `8k` readings.
- `CornerOrbits.lean` — Lemma 2.9, the corner orbits of an irregular tile.
- `Lattice.lean` — the arithmetic closing Theorem 6.5: 39 and 63 are not indices of a `D₆`-invariant
  sublattice.
- `Counting.lean` — the per-period counts of Theorem 6.5(v) and Theorem 7.2.
- `Examples.lean` — the paper's arc and closure examples, checked by evaluation.

Everything is `sorry`-free and `native_decide`-free: each result depends at most on `propext`,
`Classical.choice` and `Quot.sound`, and the corner-orbit lemmas on no axioms at all.
