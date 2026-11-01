import PythagoreanPaper.Riemannian.CosineLawG
import PythagoreanPaper.Riemannian.ModelEuclidean

/-!
# Euclidean triangles as geodesic triangles of the flat model (manuscript §9, C9.8 at `K = 0`)

The Euclidean plane `ℝ²`, with its canonical Riemannian metric, is the model space of curvature
`0` (`PythagoreanPaper.Riemannian.ModelEuclidean`). A triangle `p₁ p₂ p₃` of `ℝ²` (three distinct
points) is a geodesic triangle of this model, with the unit-speed segments
`t ↦ p + t (q - p) / |p q|` as sides (`EuclideanPlane.triangleOf`). Its side lengths are the
distances `|p₂ p₃|, |p₃ p₁|, |p₁ p₂|`, and its angles are the Euclidean angles `∠ p₂ p₁ p₃` etc.
(`EuclideanPlane.angles_triangleOf`).

The cosine law for every `K` (`PythagoreanPaper.Riemannian.CosineLawG`) at `K = 0` then gives:

* `EuclideanPlane.angle_eq_angleK_zero`: the Euclidean angles are the angles `A_0, B_0, C_0` of the
  constant-curvature cosine law (`angleK 0`), i.e. the values at `K = 0` of the angles `A_K` of
  C9.8. This identifies `A_0` with the Euclidean angle through the Riemannian layer (tangent-space
  metric, Jacobi equation) and **without** Mathlib's Euclidean law of cosines `law_cos`, which the
  earlier identification `angleK_zero_eq_angle` (`PythagoreanPaper.Sec09`) uses.
* `EuclideanPlane.cosine_law_G`, `EuclideanPlane.cosine_law_zero`: the formula
  `a² / 2 = b² / 2 + c² / 2 - b c cos A` for geodesic triangles of `ℝ²`, and its form
  `|p₂ p₃|² = |p₃ p₁|² + |p₁ p₂|² - 2 |p₃ p₁| |p₁ p₂| cos ∠ p₂ p₁ p₃` for triangles of `ℝ²`. These
  are the `K = 0` case of the cosine law in the form continuous in `K`; the manuscript does not
  state the Euclidean law of cosines as a claim (CLAIMS.md, C9.3), and these theorems are recorded
  as auxiliary results of the formalization.
-/

noncomputable section

open Bundle Set EuclideanGeometry
open scoped Manifold

namespace PythagoreanPaper

namespace EuclideanPlane

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- The unit-speed segment from `p` towards `q`: `t ↦ p + t (q - p) / |p q|`. -/
def segLine (p q : R2) : ℝ → R2 := fun t ↦ p + t • ((dist p q)⁻¹ • (q - p))

lemma velocity_segLine (p q : R2) (t : ℝ) :
    velocity 𝓘(ℝ, R2) (segLine p q) t = (dist p q)⁻¹ • (q - p) :=
  velocity_line p _ t

lemma norm_dir {p q : R2} (h : p ≠ q) : ‖(dist p q)⁻¹ • (q - p)‖ = 1 := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (dist_pos.2 h), ← dist_eq_norm,
    dist_comm q p, inv_mul_cancel₀ (dist_ne_zero.2 h)]

lemma neg_dir (p q : R2) : -((dist p q)⁻¹ • (q - p)) = (dist q p)⁻¹ • (p - q) := by
  rw [← smul_neg, neg_sub, dist_comm]

/-- The segment from `p` to `q` is a geodesic segment of length `|p q|`. -/
lemma isGeodesicSegment_segLine {p q : R2} (h : p ≠ q) :
    IsGeodesicSegment 𝓘(ℝ, R2) (segLine p q) p q (dist p q) where
  pos := dist_pos.2 h
  exists_Ioo := ⟨-1, dist p q + 1, by norm_num, by linarith,
    (isGeodesicFrom_line p ((dist p q)⁻¹ • (q - p))).isGeodesicOn.mono (subset_univ _)⟩
  unit := by
    rw [norm_tangentSpace_vectorSpace]
    have hv : (NormedSpace.fromTangentSpace (segLine p q 0))
        (velocity 𝓘(ℝ, R2) (segLine p q) 0) = (dist p q)⁻¹ • (q - p) :=
      velocity_segLine p q 0
    rw [hv, norm_dir h]
  apply_zero := by simp [segLine]
  apply_length := by
    show p + dist p q • ((dist p q)⁻¹ • (q - p)) = q
    rw [smul_smul, mul_inv_cancel₀ (dist_ne_zero.2 h), one_smul, add_sub_cancel]

/-- **The triangle `p₁ p₂ p₃` of `ℝ²` as a geodesic triangle of the flat model** (three distinct
points): vertices `A = p₁`, `B = p₂`, `C = p₃`, sides the segments `p₂ → p₃`, `p₃ → p₁`,
`p₁ → p₂`, of lengths `a = |p₂ p₃|`, `b = |p₃ p₁|`, `c = |p₁ p₂|`. -/
def triangleOf {p₁ p₂ p₃ : R2} (h₁₂ : p₁ ≠ p₂) (h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁) :
    GeodesicTriangle 𝓘(ℝ, R2) R2 where
  pA := p₁
  pB := p₂
  pC := p₃
  a := dist p₂ p₃
  b := dist p₃ p₁
  c := dist p₁ p₂
  σa := segLine p₂ p₃
  σb := segLine p₃ p₁
  σc := segLine p₁ p₂
  segment_a := isGeodesicSegment_segLine h₂₃
  segment_b := isGeodesicSegment_segLine h₃₁
  segment_c := isGeodesicSegment_segLine h₁₂

/-- In `ℝ²`, the angle between two tangent vectors (for the canonical metric) is the angle between
the vectors. -/
lemma angle_tangentSpace {x : R2} {u v : TangentSpace 𝓘(ℝ, R2) x} {u' v' : R2}
    (hu : @Eq R2 u u') (hv : @Eq R2 v v') :
    InnerProductGeometry.angle u v = InnerProductGeometry.angle u' v' := by
  subst hu hv
  unfold InnerProductGeometry.angle
  rw [norm_tangentSpace_vectorSpace, norm_tangentSpace_vectorSpace]
  rfl

/-- The angle at `x` between the unit vectors towards `p` and towards `q` is `∠ p x q`. -/
lemma angle_eq_of_dirs {x p q : R2} (hp : x ≠ p) (hq : x ≠ q) {u v : TangentSpace 𝓘(ℝ, R2) x}
    (hu : @Eq R2 u ((dist x p)⁻¹ • (p - x))) (hv : @Eq R2 v ((dist x q)⁻¹ • (q - x))) :
    InnerProductGeometry.angle u v = ∠ p x q := by
  rw [angle_tangentSpace hu hv,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.2 (dist_pos.2 hp)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.2 (dist_pos.2 hq))]
  rfl

/-- The reversed velocity at the end of `segLine p q` is the unit vector from `q` towards `p`. -/
lemma neg_velocity_segLine_end (p q : R2) :
    @Eq R2 (-(velocity 𝓘(ℝ, R2) (segLine p q) (dist p q) : R2)) ((dist q p)⁻¹ • (p - q)) :=
  (congrArg (fun z : R2 ↦ -z) (velocity_segLine p q (dist p q))).trans (neg_dir p q)

/-- **The angles of `triangleOf` are the Euclidean angles**: `A = ∠ p₂ p₁ p₃`, `B = ∠ p₃ p₂ p₁`,
`C = ∠ p₁ p₃ p₂`. -/
theorem angles_triangleOf {p₁ p₂ p₃ : R2} (h₁₂ : p₁ ≠ p₂) (h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁) :
    (triangleOf h₁₂ h₂₃ h₃₁).angleA = ∠ p₂ p₁ p₃ ∧ (triangleOf h₁₂ h₂₃ h₃₁).angleB = ∠ p₃ p₂ p₁ ∧
      (triangleOf h₁₂ h₂₃ h₃₁).angleC = ∠ p₁ p₃ p₂ :=
  ⟨angle_eq_of_dirs h₁₂ h₃₁.symm (velocity_segLine p₁ p₂ 0) (neg_velocity_segLine_end p₃ p₁),
    angle_eq_of_dirs h₂₃ h₁₂.symm (velocity_segLine p₂ p₃ 0) (neg_velocity_segLine_end p₁ p₂),
    angle_eq_of_dirs h₃₁ h₂₃.symm (velocity_segLine p₃ p₁ 0) (neg_velocity_segLine_end p₂ p₃)⟩

/-- **The Euclidean angles are the angles `A_0, B_0, C_0` of the constant-curvature cosine law**
(C9.8 at `K = 0`): for three distinct points of `ℝ²`, `∠ p₂ p₁ p₃ = angleK 0 a b c`,
`∠ p₃ p₂ p₁ = angleK 0 b c a`, `∠ p₁ p₃ p₂ = angleK 0 c a b` with `a = |p₂ p₃|`, `b = |p₃ p₁|`,
`c = |p₁ p₂|`. The proof goes through the flat model and the cosine law for every `K`
(`GeodesicTriangle.angles_eq_angleK_zero`); it does not use Mathlib's `law_cos`. -/
theorem angle_eq_angleK_zero {p₁ p₂ p₃ : R2} (h₁₂ : p₁ ≠ p₂) (h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁) :
    ∠ p₂ p₁ p₃ = angleK 0 (dist p₂ p₃) (dist p₃ p₁) (dist p₁ p₂) ∧
      ∠ p₃ p₂ p₁ = angleK 0 (dist p₃ p₁) (dist p₁ p₂) (dist p₂ p₃) ∧
      ∠ p₁ p₃ p₂ = angleK 0 (dist p₁ p₂) (dist p₂ p₃) (dist p₃ p₁) := by
  obtain ⟨eA, eB, eC⟩ := angles_triangleOf h₁₂ h₂₃ h₃₁
  obtain ⟨hA, hB, hC⟩ := (triangleOf h₁₂ h₂₃ h₃₁).angles_eq_angleK_zero finrank_euclideanSpace_fin
    hasConstSectionalCurvature_euclidean (sidesInNormalBalls _)
  exact ⟨eA.symm.trans hA, eB.symm.trans hB, eC.symm.trans hC⟩

/-- The cosine law in the form continuous in `K` (`GeodesicTriangle.cosine_law_G`) at `K = 0`, for
every geodesic triangle of `ℝ²`: `a² / 2 = b² / 2 + c² / 2 - b c cos A`, and likewise at `B`, `C`.
(Auxiliary result: not a claim of the manuscript.) -/
theorem cosine_law_G (T : GeodesicTriangle 𝓘(ℝ, R2) R2) :
    T.a ^ 2 / 2 = T.b ^ 2 / 2 + T.c ^ 2 / 2 - T.b * T.c * Real.cos T.angleA ∧
      T.b ^ 2 / 2 = T.c ^ 2 / 2 + T.a ^ 2 / 2 - T.c * T.a * Real.cos T.angleB ∧
      T.c ^ 2 / 2 = T.a ^ 2 / 2 + T.b ^ 2 / 2 - T.a * T.b * Real.cos T.angleC := by
  obtain ⟨hA, hB, hC⟩ := T.cosine_law_G finrank_euclideanSpace_fin
    hasConstSectionalCurvature_euclidean (sidesInNormalBalls T)
  simp only [Gk_zero, S_of_eq_zero, zero_mul, sub_zero] at hA hB hC
  exact ⟨hA, hB, hC⟩

/-- For three distinct points of `ℝ²`,
`|p₂ p₃|² = |p₃ p₁|² + |p₁ p₂|² - 2 |p₃ p₁| |p₁ p₂| cos ∠ p₂ p₁ p₃`, obtained from the cosine law
in the form continuous in `K` at `K = 0` in the flat model (`cosine_law_G`, `angles_triangleOf`);
Mathlib's `law_cos` is not used. (Auxiliary result: not a claim of the manuscript.) -/
theorem cosine_law_zero {p₁ p₂ p₃ : R2} (h₁₂ : p₁ ≠ p₂) (h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁) :
    dist p₂ p₃ ^ 2 = dist p₃ p₁ ^ 2 + dist p₁ p₂ ^ 2 -
      2 * dist p₃ p₁ * dist p₁ p₂ * Real.cos (∠ p₂ p₁ p₃) := by
  have h := (cosine_law_G (triangleOf h₁₂ h₂₃ h₃₁)).1
  rw [(angles_triangleOf h₁₂ h₂₃ h₃₁).1] at h
  change dist p₂ p₃ ^ 2 / 2 = dist p₃ p₁ ^ 2 / 2 + dist p₁ p₂ ^ 2 / 2 -
    dist p₃ p₁ * dist p₁ p₂ * Real.cos (∠ p₂ p₁ p₃) at h
  linear_combination 2 * h

end EuclideanPlane

end PythagoreanPaper
