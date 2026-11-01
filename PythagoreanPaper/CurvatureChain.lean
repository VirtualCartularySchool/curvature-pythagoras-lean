import PythagoreanPaper.Riemannian.ModelExistence
import PythagoreanPaper.Riemannian.EuclideanTriangle
import PythagoreanPaper.Sec10OfSineLaw

/-!
# The chain of manuscript §12 as one formal dependency (§9 → §10, through the Riemannian layer)

Manuscript §12 names the chain

  `Jacobi field ⇒ S_K ⇒ constant-curvature sine law ⇒ K = 0 ⇒ foundation of the trigonometric proof
  of the Pythagorean theorem`,

and §11 says that the dependence on the Pythagorean distance structure is moved "from the whole
Euclidean plane to the tangent-space metric and the curvature structure". In
`PythagoreanPaper.Sec09` and `PythagoreanPaper.Sec10` the Euclidean sine law used by §10 is
`sec9_euclidean_sine_law`: the
limit of the sine law for the angles `angleK` given by the cosine-law formula, with `A_0` identified
with the Euclidean angle by Mathlib's Euclidean law of cosines `law_cos` (`angleK_zero_eq_angle`);
the Riemannian layer does not occur in that proof.

This file proves the Euclidean sine law in `ℝ²` and the theorems of §10 for `ℝ²` along the chain:

1. **Jacobi field ⇒ `S_K` ⇒ cosine law** (`PythagoreanPaper.Riemannian`): in geodesic polar
   coordinates, `(S_K(r) r')' = C_K(r)` along geodesics (`hasDerivAt_S_mul_polar`, from the
   Jacobi equation `sec6_jacobi_eq_S`), whence the cosine law in normal balls and for geodesic
   triangles, also in the form continuous in `K` (`GeodesicTriangle.cosine_law_G`).
2. **`K < 0`: the constant-curvature sine law** (`hyperbolic_sine_law`): for the sides `a, b, c`
   of a nondegenerate triangle and every `K < 0` near `0`, the hyperbolic plane of curvature `K`
   contains a geodesic triangle with sides `a, b, c` (`HypPlane.exists_triangle`); its cosine law
   (C9.3, `HypPlane.cosine_law`) gives its sine law (C9.5–C9.7, `sec9_sine_law_of_cos_law`), and
   its angles are `A_K, B_K, C_K` (`HypPlane.angles_eq_angleK`).
3. **`K → 0`** (`sine_law_limit`): `A_K` depends continuously on `K` (`continuousAt_angleK`) and
   `S_K(x) → x` (`continuousAt_S_param`), so the sine law of these triangles passes to the limit:
   `sin A_0 / a = sin B_0 / b = sin C_0 / c`.
4. **`K = 0`** (`EuclideanPlane.angle_eq_angleK_zero`): a triangle of `ℝ²` is a geodesic triangle of
   the flat model, and by the cosine law for every `K` at `K = 0` its angles are `A_0, B_0, C_0`.
   Hence the Euclidean sine law in `ℝ²` (`euclidean_sine_law`).
5. **§10** (`PythagoreanPaper.Sec10OfSineLaw`): the Jackson–Johnson argument from the sine law:
   `sec10_sine_laws`, `sec10_right_ratios`, `sec10_two_expressions`, `sec10_pythagoras` for `ℝ²`.

`scripts/DependencyReport.lean` checks, over the whole dependency closure (Mathlib included), that
`sec10_pythagoras` of this file does not use `law_cos` or Mathlib's Pythagorean theorems, and that
it uses the Riemannian part. As in manuscript §11, this does not remove the dependence on the inner
product. The Riemannian layer uses the Pythagorean relation in a tangent plane,
`‖x‖² = ⟨w₁, x⟩² + ⟨w₂, x⟩²` for an orthonormal pair (`norm_sq_eq_inner_sq_add_inner_sq`, in
`exists_polar_lift`), and the metric in geodesic polar coordinates, `|σ'|² = r'² + S_K(r)² θ'²`
(`sec6_metric`, in `hasDerivAt_S_mul_polar`); the hyperbolic model computes with
`‖x - y‖² = ‖x‖² - 2⟨x, y⟩ + ‖y‖²` in its coordinate plane; and §10 uses Mathlib's angle sum and
betweenness facts of the Euclidean plane.

The one-sided limit `K → 0⁻` (hyperbolic triangles) suffices for the limit of a function continuous
at `K = 0`; triangles for `K > 0` (spheres) are constructed in `sec9_model_triangles`.
-/

noncomputable section

open Real Set Filter Topology EuclideanGeometry
open scoped Manifold

namespace PythagoreanPaper

namespace CurvatureChain

local notation "R2" => EuclideanSpace ℝ (Fin 2)

private theorem not_collinear_rotate {p₁ p₂ p₃ : R2}
    (h : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set R2)) : ¬ Collinear ℝ ({p₂, p₃, p₁} : Set R2) :=
  fun h' => h (h'.subset (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto))

/-- **The constant-curvature sine law for the hyperbolic triangles with sides `a, b, c`** (C9.1 for
`K < 0`, for the triangles of C9.8). For the sides `a, b, c` of a nondegenerate triangle and every
`K < 0` near `0`, the hyperbolic plane of curvature `K` contains a geodesic triangle with sides
`a, b, c`, which satisfies `sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)` and whose angles are
`A_K = angleK K a b c`, `B_K = angleK K b c a`, `C_K = angleK K c a b`. -/
theorem hyperbolic_sine_law {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    ∀ᶠ K in 𝓝[<] (0 : ℝ), ∀ [Fact (K < 0)], ∃ T : GeodesicTriangle 𝓘(ℝ, R2) (hypPlane K),
      T.a = a ∧ T.b = b ∧ T.c = c ∧
      Real.sin T.angleA / S K a = Real.sin T.angleB / S K b ∧
      Real.sin T.angleB / S K b = Real.sin T.angleC / S K c ∧
      T.angleA = angleK K a b c ∧ T.angleB = angleK K b c a ∧ T.angleC = angleK K c a b := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (eventually_cosLaw_mem_Ioo hb hc h1 h2 h3),
    mem_nhdsWithin_of_mem_nhds (eventually_cosLaw_mem_Ioo hc ha h2 h3 h1),
    mem_nhdsWithin_of_mem_nhds (eventually_cosLaw_mem_Ioo ha hb h3 h1 h2)]
    with K hcA hcB hcC hF
  have hK : K < 0 := hF.out
  -- the triangle with sides `a, b, c`
  obtain ⟨T, hTa, hTb, hTc⟩ := HypPlane.exists_triangle ha hb hc hcA
  -- its cosine law (C9.3) and its angles `A_K, B_K, C_K`
  obtain ⟨cA, cB, cC⟩ := HypPlane.cosine_law T
  obtain ⟨eA, eB, eC⟩ := HypPlane.angles_eq_angleK T
  rw [hTa, hTb, hTc] at cA cB cC eA eB eC
  -- its angles lie in `(0, π)`
  have bA := angleK_pos_lt_pi hcA
  have bB := angleK_pos_lt_pi hcB
  have bC := angleK_pos_lt_pi hcC
  rw [← eA] at bA
  rw [← eB] at bB
  rw [← eC] at bC
  -- its sine law (C9.5–C9.7)
  obtain ⟨s1, s2⟩ := sec9_sine_law_of_cos_law hK.ne (S_pos_of_nonpos hK.le ha)
    (S_pos_of_nonpos hK.le hb) (S_pos_of_nonpos hK.le hc) bA.1 bA.2 bB.1 bB.2 bC.1 bC.2 cA cB cC
  exact ⟨T, hTa, hTb, hTc, s1, s2, eA, eB, eC⟩

/-- **C9.8: the limit `K → 0` of the sine law of the hyperbolic triangles.** For the sides
`a, b, c` of a nondegenerate triangle, the sine law of the hyperbolic triangles with sides
`a, b, c` (`hyperbolic_sine_law`) passes to the limit `K → 0⁻`, since `A_K = angleK K a b c`
depends continuously on `K` and `S_K(x) → x`: `sin A_0 / a = sin B_0 / b = sin C_0 / c`. -/
theorem sine_law_limit {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    Real.sin (angleK 0 a b c) / a = Real.sin (angleK 0 b c a) / b ∧
      Real.sin (angleK 0 b c a) / b = Real.sin (angleK 0 c a b) / c := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS0 : ∀ {x y : ℝ}, 0 < x → 0 < y → S 0 x * S 0 y ≠ 0 := fun {x y} hx hy => by
    rw [S_of_eq_zero, S_of_eq_zero]
    exact (mul_pos hx hy).ne'
  have hF : ∀ {x y z : ℝ}, 0 < x → 0 < y → 0 < z →
      ContinuousAt (fun K => Real.sin (angleK K x y z) / S K x) 0 := by
    intro x y z hx hy hz
    exact (Real.continuous_sin.continuousAt.comp (continuousAt_angleK h0 x y z (hS0 hy hz))).div
      (continuousAt_S_param h0 x) (by simpa [S_of_eq_zero] using hx.ne')
  -- the sine law of the hyperbolic triangles, for `K < 0` near `0`, in terms of `A_K, B_K, C_K`
  have hev : ∀ᶠ K in 𝓝[<] (0 : ℝ),
      Real.sin (angleK K a b c) / S K a = Real.sin (angleK K b c a) / S K b ∧
      Real.sin (angleK K b c a) / S K b = Real.sin (angleK K c a b) / S K c := by
    filter_upwards [hyperbolic_sine_law ha hb hc h1 h2 h3, self_mem_nhdsWithin] with K hT hK
    obtain ⟨T, -, -, -, s1, s2, eA, eB, eC⟩ := @hT ⟨hK⟩
    rw [eA, eB] at s1
    rw [eB, eC] at s2
    exact ⟨s1, s2⟩
  -- pass to the limit
  have hle : 𝓝[<] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have e1 := tendsto_nhds_unique ((hF ha hb hc).tendsto.mono_left hle)
    (((hF hb hc ha).tendsto.mono_left hle).congr' (hev.mono fun K hK => hK.1.symm))
  have e2 := tendsto_nhds_unique ((hF hb hc ha).tendsto.mono_left hle)
    (((hF hc ha hb).tendsto.mono_left hle).congr' (hev.mono fun K hK => hK.2.symm))
  simp only [S_of_eq_zero] at e1 e2
  exact ⟨e1, e2⟩

/-- **C9.8 (conclusion) through the Riemannian layer: the Euclidean sine law in `ℝ²`.** For a
nondegenerate triangle `p₁ p₂ p₃` of `ℝ²` with angles `A = ∠ p₂ p₁ p₃`, `B = ∠ p₃ p₂ p₁`,
`C = ∠ p₁ p₃ p₂` and opposite sides `a = |p₂ p₃|`, `b = |p₃ p₁|`, `c = |p₁ p₂|`:
`sin A / a = sin B / b = sin C / c`. The angles are `A_0, B_0, C_0` by the cosine law at `K = 0` in
the flat model (`EuclideanPlane.angle_eq_angleK_zero`), and the sine law for `A_0, B_0, C_0` is the
limit of the sine law of the hyperbolic triangles with sides `a, b, c` (`sine_law_limit`). -/
theorem euclidean_sine_law {p₁ p₂ p₃ : R2} (h : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set R2)) :
    Real.sin (∠ p₂ p₁ p₃) / dist p₂ p₃ = Real.sin (∠ p₃ p₂ p₁) / dist p₃ p₁ ∧
      Real.sin (∠ p₃ p₂ p₁) / dist p₃ p₁ = Real.sin (∠ p₁ p₃ p₂) / dist p₁ p₂ := by
  have h' := not_collinear_rotate h
  have h'' := not_collinear_rotate h'
  have h₁₂ := ne₁₂_of_not_collinear h
  have h₁₃ := ne₁₃_of_not_collinear h
  have h₂₃ := ne₂₃_of_not_collinear h
  have ha : 0 < dist p₂ p₃ := dist_pos.mpr h₂₃
  have hb : 0 < dist p₃ p₁ := dist_pos.mpr h₁₃.symm
  have hc : 0 < dist p₁ p₂ := dist_pos.mpr h₁₂
  have t1 := dist_lt_add_of_not_collinear h
  have t2 := dist_lt_add_of_not_collinear h'
  have t3 := dist_lt_add_of_not_collinear h''
  -- `K = 0`: the Euclidean angles are `A_0, B_0, C_0` (flat model)
  obtain ⟨hA, hB, hC⟩ := EuclideanPlane.angle_eq_angleK_zero h₁₂ h₂₃ h₁₃.symm
  rw [hA, hB, hC]
  -- the limit of the constant-curvature sine law
  exact sine_law_limit ha hb hc t1 t2 t3

/-- The Euclidean sine law in `ℝ²` through the Riemannian layer, as the hypothesis of
`PythagoreanPaper.Sec10OfSineLaw`. -/
theorem euclideanSineLaw : EuclideanSineLaw R2 R2 := fun _ _ _ h ↦ euclidean_sine_law h

/-! ### Manuscript §10 in `ℝ²`, through the chain -/

/-- **C10.5 through the chain**: the sine law in `ACD` and in `ABD`. -/
theorem sec10_sine_laws {A B C D : R2} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hD : Sbtw ℝ C B D) :
    dist C D / Real.sin (∠ C A D) = dist A C / Real.sin (∠ A D C) ∧
      dist B D / Real.sin (∠ B A D) = dist A B / Real.sin (∠ A D B) :=
  sec10_sine_laws_of_sineLaw euclideanSineLaw hAC hBC hright hD

/-- **C10.6 through the chain**: `sin α = a/c`, `cos α = b/c`, `sin β = b/c`, `cos β = a/c`. -/
theorem sec10_right_ratios {A B C : R2} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) :
    Real.sin (∠ B A C) = dist B C / dist A B ∧ Real.cos (∠ B A C) = dist A C / dist A B ∧
      Real.sin (∠ A B C) = dist A C / dist A B ∧ Real.cos (∠ A B C) = dist B C / dist A B :=
  sec10_right_ratios_of_sineLaw euclideanSineLaw hAC hBC hright

/-- **C10.8 through the chain**: the two expressions of `BD`. -/
theorem sec10_two_expressions {A B C D : R2} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) (hab : dist B C < dist A C)
    (hD : Sbtw ℝ C B D) (hDα : ∠ B A D = ∠ B A C) :
    dist C D = 2 * dist B C * dist A C ^ 2 / (dist A C ^ 2 - dist B C ^ 2) ∧
      dist B D = dist B C * (dist B C ^ 2 + dist A C ^ 2) / (dist A C ^ 2 - dist B C ^ 2) ∧
      dist B D = dist B C * dist A B ^ 2 / (dist A C ^ 2 - dist B C ^ 2) :=
  sec10_two_expressions_of_sineLaw euclideanSineLaw hAC hBC hright hab hD hDα

/-- **C10.9 through the chain of manuscript §12**: in a right triangle `ABC` of `ℝ²` with
`∠C = 90°` and `a < b`, `a² + b² = c²`; the sine law used is `euclidean_sine_law`, obtained through
the Jacobi equation, the hyperbolic triangles, the limit `K → 0` and the flat model. -/
theorem sec10_pythagoras {A B C : R2} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hab : dist B C < dist A C) : dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2 :=
  sec10_pythagoras_of_sineLaw euclideanSineLaw hAC hBC hright hab

end CurvatureChain

end PythagoreanPaper
