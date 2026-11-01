# 循環構造と収束構造の曲率的統一 — Lean formalization

A Lean 4 formalization of the proofs of the manuscript

**「循環構造と収束構造の曲率的統一」**
*A Curvature-Theoretic Unification of Cyclic Structure and Convergent Structure*

(series 領域化運動論としての四色性 / *Four-Colorability as Regionization Dynamics*,
document 7 of 11).

> **Fixed research archive.** This repository is a fixed version of a research result. It is not
> maintained, and questions, requests for explanation, corrections and requests for further
> proofs are not answered individually.
>
> 本リポジトリは固定版の研究アーカイブです。継続的な保守は行わず、質問・説明・修正・追加証明の
> 要求には個別に回答しません。

## What is formalized

Every claim of the manuscript that is a mathematical theorem is a Lean theorem here, checked by
the Lean kernel, with no `sorry` and no axiom other than `propext`, `Classical.choice` and
`Quot.sound`. For the geodesic triangles of §9 this holds under the readings R1–R5 recorded in
[`CLAIMS.md`](CLAIMS.md), which gives the correspondence claim by claim (in Japanese). The
interpretive claims (C3.3, C8.1, §§11–13) are not theorems and are not formalized as such.

The Pythagorean theorem of §10 is proved along the chain named in §12,

    Jacobi field ⇒ S_K ⇒ constant-curvature law of sines ⇒ K → 0 ⇒ Jackson–Johnson second proof,

as one formal dependency: `PythagoreanPaper.CurvatureChain.sec10_pythagoras`, for right
triangles of ℝ². The proof passes through geodesic triangles of the hyperbolic plane of curvature
K < 0, the limit K → 0 and the flat model ℝ². It uses neither Mathlib's law of cosines nor
Mathlib's Pythagorean theorems; `scripts/DependencyReport.lean` checks this over the whole
dependency closure, Mathlib included. As §11 of the manuscript says, the dependence on the
Pythagorean distance structure is not removed but moved to the tangent-space metric and the
curvature; the proof uses, for instance, the Pythagorean relation in a tangent plane and the
metric in geodesic polar coordinates.

| Manuscript | Main Lean theorems (namespace `PythagoreanPaper`) |
|---|---|
| §§3–5 Jacobi equation, S_K, exponential form | `sec3_jacobi_flat`, `sec4_jacobi_normal_eq`, `sec4_jacobi_eq_S`, `sec5_exp_AK` |
| §6 geodesic polar coordinates | `sec6_polar_coordinates`, `sec6_metric`, `sec6_circumference` |
| §7 rotation and Euler's formula | `sec7_exp_J`, `sec7_euler` |
| §9 laws of cosines and sines, K → 0 | `HypPlane.cosine_law`, `SphereModel.sine_law`, `GeodesicTriangle.cosine_law_G`, `CurvatureChain.euclidean_sine_law` |
| §10 the second proof of Jackson–Johnson | `sec10_pythagoras`, `CurvatureChain.sec10_pythagoras` |

## Verification

Lean 4.35.0 and Mathlib v4.35.0 (commit pinned in `lake-manifest.json`).

```sh
lake exe cache get
lake build --wfail
lake env lean scripts/AxiomReport.lean
lake env lean scripts/DependencyReport.lean
```

The workflow `.github/workflows/verify.yml` runs these steps on every push, and replays every
declaration through the Lean kernel with `leanchecker`.

## Provenance

This repository is a snapshot of the verified state of the development repository, commit
`cc13c180ea092d11bf70bc83a28b0dc880fc917f`. The Lean sources, the build files and the two scripts
are identical to that commit. `README.md`, the header of `CLAIMS.md` and the workflow were written
for this snapshot, and `LICENSE` is the official text of the Apache License 2.0.

## License

Licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The manuscript itself is not
included in this repository.
