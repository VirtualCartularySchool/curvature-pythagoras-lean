import PythagoreanPaper.Riemannian.ModelHyperbolic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The sphere as the model space of curvature `K > 0` (manuscript §9)

For `K > 0`, `SphereModel.sph K` is the unit sphere `S² ⊆ ℝ³` with Mathlib's manifold structure
(charts: stereographic projections, the chart at `x` projecting from `−x`), and with the metric
`(1/K)` times the round metric (in the chart at each point `x`, `⟨u, v⟩ / K` at `x`). It is
isometric to the round sphere of radius `1/√K`. This file shows:

* `SphereModel.metricCoord_eq`: in every chart the metric is `16 / (K (‖w‖² + 4)²) ⟨·, ·⟩`;
* `SphereModel.hasConstSectionalCurvature`: it has constant curvature `K`;
* `SphereModel.isGeodesicFrom_gC`, `SphereModel.expMap_eq`: in the chart at `x`, the geodesic
  from `x` with initial velocity `v` is `t ↦ (2 tan(‖v‖ t / 2) / ‖v‖) v`, for `‖v‖ |t| < π`;
* `SphereModel.isNormalBall`: the ball of radius `π/√K` of `T_x` is a normal ball, whose image
  is the sphere minus the antipode of `x` (`SphereModel.mem_expMap_image_of_ne`);
* `SphereModel.sidesInNormalBalls_of_inOpenHemisphere`: a geodesic triangle whose sides lie in an
  open hemisphere satisfies the technical condition `SidesInNormalBalls`.
-/

noncomputable section
open Bundle Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

section ChartDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a map `f : M → F` on the coordinate vector `a` of the chart at `x₀` is the
derivative of `f` read in that chart. -/
lemma mfderiv_symmL_eq_fderiv {f : M → F} {x₀ y : M} (hy : y ∈ (chartAt H x₀).source)
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)) (a : E) :
    mfderiv I 𝓘(ℝ, F) f y ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y a) =
      fderiv ℝ (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y) a := by
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  have heq : f =ᶠ[𝓝 y] (f ∘ (extChartAt I x₀).symm) ∘ extChartAt I x₀ := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hy] with z hz
    simp only [Function.comp_apply]
    rw [(extChartAt I x₀).left_inv (by rwa [extChartAt_source])]
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) (f ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀ y) := hf.mdifferentiableAt
  have hφ : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) y := mdifferentiableAt_extChartAt hy
  rw [heq.mfderiv_eq, mfderiv_comp y hg hφ, mfderiv_eq_fderiv,
    ← TangentBundle.continuousLinearMapAt_trivializationAt hy]
  have h2 := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
    (trivializationAt E (TangentSpace I) x₀) hy' a
  show fderiv ℝ (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y a)) = _
  rw [h2]

end ChartDeriv

namespace SphereModel

instance fact_finrank : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

/-- The sphere, as the carrier of the model space of curvature `K`. -/
def sph (_K : ℝ) : Set E3 := sphere (0 : E3) 1

variable {K : ℝ}

instance instChartedSpace (K : ℝ) : ChartedSpace R2 (sph K) :=
  inferInstanceAs (ChartedSpace R2 (sphere (0 : E3) 1))

instance instIsManifold (K : ℝ) : IsManifold 𝓘(ℝ, R2) ∞ (sph K) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, R2) ∞ (sphere (0 : E3) 1))

example : T2Space (sph K) := inferInstance

/-- The antipode. -/
def antipode (x : sph K) : sph K := ⟨-(x : E3), by simpa [sph] using x.2⟩

lemma norm_coe (x : sph K) : ‖(x : E3)‖ = 1 := by simpa [sph] using x.2

/-- `x` as a point of the unit sphere. -/
def toS (x : sph K) : sphere (0 : E3) 1 := x

lemma chartAt_eq (x : sph K) : chartAt R2 x = stereographic' 2 (-(toS x)) := rfl

/-- The linear isometry from `ℝ²` onto `x₀ᗮ` used by the chart at `x₀`. -/
def U (x₀ : sph K) : (ℝ ∙ ((-(toS x₀) : sphere (0 : E3) 1) : E3))ᗮ ≃ₗᵢ[ℝ] R2 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere (-(toS x₀)))).repr

def ι (x₀ : sph K) : R2 →ₗᵢ[ℝ] E3 := (Submodule.subtypeₗᵢ _).comp (U x₀).symm.toLinearIsometry

lemma ι_apply (x₀ : sph K) (w : R2) : ι x₀ w = ((U x₀).symm w : E3) := rfl

lemma norm_ι (x₀ : sph K) (w : R2) : ‖ι x₀ w‖ = ‖w‖ := (ι x₀).norm_map w

lemma inner_ι (x₀ : sph K) (a b : R2) : inner ℝ (ι x₀ a) (ι x₀ b) = inner ℝ a b :=
  (ι x₀).inner_map_map a b

lemma inner_ι_self (x₀ : sph K) (w : R2) : inner ℝ (x₀ : E3) (ι x₀ w) = 0 := by
  have h : inner ℝ (((-(toS x₀)) : sphere (0 : E3) 1) : E3) (ι x₀ w) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 ((U x₀).symm w).2
  rw [coe_neg_sphere, inner_neg_left, neg_eq_zero] at h
  exact h

/-- The inverse of the chart at `x₀` (stereographic projection from `−x₀`), as a map to `ℝ³`. -/
def Φ (x₀ : sph K) (w : R2) : E3 :=
  (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • ι x₀ w - (‖w‖ ^ 2 - 4) • (x₀ : E3))

lemma chartAt_symm_eq (x₀ : sph K) (w : R2) : ((chartAt R2 x₀).symm w : E3) = Φ x₀ w := by
  refine (stereographic'_symm_apply (n := 2) (-(toS x₀)) w).trans ?_
  show (‖ι x₀ w‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • ι x₀ w +
    (‖ι x₀ w‖ ^ 2 + 4)⁻¹ • (‖ι x₀ w‖ ^ 2 - 4) • (((-(toS x₀)) : sphere (0 : E3) 1) : E3) = Φ x₀ w
  rw [norm_ι, coe_neg_sphere, Φ]
  show _ = _ • (_ - _ • ((toS x₀ : sphere (0 : E3) 1) : E3))
  module

/-- The chart at `x₀` sends `x₀` to `0`. -/
lemma chartAt_self (x₀ : sph K) : chartAt R2 x₀ x₀ = 0 := by
  show (OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere (-(toS x₀)))).repr
      (stereographic (norm_eq_of_mem_sphere (-(toS x₀))) (toS x₀)) = 0
  rw [stereographic_neg_apply, map_zero]

lemma mem_chartAt_source_iff (x₀ y : sph K) :
    y ∈ (chartAt R2 x₀).source ↔ (y : E3) ≠ -(x₀ : E3) := by
  rw [chartAt_eq, stereographic'_source]
  show ¬ (toS y = -(toS x₀)) ↔ _
  rw [Subtype.ext_iff, coe_neg_sphere]
  rfl

lemma inner_ι_self' (x₀ : sph K) (w : R2) : inner ℝ (ι x₀ w) (x₀ : E3) = 0 := by
  rw [real_inner_comm]; exact inner_ι_self x₀ w

/-- The derivative of `Φ x₀` at `w`. -/
def DΦ (x₀ : sph K) (w : R2) : R2 →L[ℝ] E3 :=
  (4 / (‖w‖ ^ 2 + 4)) • (ι x₀).toContinuousLinearMap -
    (8 / (‖w‖ ^ 2 + 4) ^ 2) • (innerSL ℝ w).smulRight (ι x₀ w) -
    (16 / (‖w‖ ^ 2 + 4) ^ 2) • (innerSL ℝ w).smulRight (x₀ : E3)

lemma DΦ_apply (x₀ : sph K) (w a : R2) :
    DΦ x₀ w a = (4 / (‖w‖ ^ 2 + 4)) • ι x₀ a - (8 / (‖w‖ ^ 2 + 4) ^ 2 * inner ℝ w a) • ι x₀ w -
      (16 / (‖w‖ ^ 2 + 4) ^ 2 * inner ℝ w a) • (x₀ : E3) := by
  simp [DΦ, smul_smul]

lemma hasFDerivAt_Φ (x₀ : sph K) (w : R2) : HasFDerivAt (Φ x₀) (DΦ x₀ w) w := by
  have hN0 : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have hN : HasFDerivAt (fun w : R2 ↦ ‖w‖ ^ 2 + 4) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const 4
  have hinv : HasFDerivAt (fun w : R2 ↦ (‖w‖ ^ 2 + 4)⁻¹)
      ((-((‖w‖ ^ 2 + 4) ^ 2)⁻¹) • (2 • innerSL ℝ w)) w :=
    (hasDerivAt_inv hN0).comp_hasFDerivAt w hN
  have hf : HasFDerivAt (fun w : R2 ↦ (4 : ℝ) • ι x₀ w - (‖w‖ ^ 2 - 4) • (x₀ : E3))
      ((4 : ℝ) • (ι x₀).toContinuousLinearMap - (2 • innerSL ℝ w).smulRight (x₀ : E3)) w := by
    have h1 := ((ι x₀).toContinuousLinearMap.hasFDerivAt (x := w)).const_smul (4 : ℝ)
    have h2 := ((hasStrictFDerivAt_norm_sq w).hasFDerivAt.sub_const 4).smul_const (x₀ : E3)
    exact h1.sub h2
  have h : HasFDerivAt (Φ x₀) ((‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • (ι x₀).toContinuousLinearMap -
      (2 • innerSL ℝ w).smulRight (x₀ : E3)) + ((-((‖w‖ ^ 2 + 4) ^ 2)⁻¹) •
      (2 • innerSL ℝ w)).smulRight ((4 : ℝ) • ι x₀ w - (‖w‖ ^ 2 - 4) • (x₀ : E3))) w :=
    hinv.smul hf
  convert h using 1
  ext1 a
  rw [DΦ_apply]
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    LinearIsometry.coe_toContinuousLinearMap, smul_eq_mul]
  match_scalars <;> field_simp <;> ring

lemma inner_DΦ (x₀ : sph K) (w a b : R2) :
    inner ℝ (DΦ x₀ w a) (DΦ x₀ w b) = 16 / (‖w‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  have hN0 : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  rw [DΦ_apply, DΦ_apply]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_ι, inner_ι_self, inner_ι_self', real_inner_self_eq_norm_sq, norm_coe, norm_ι,
    real_inner_comm a w]
  field_simp
  ring

lemma DΦ_zero (x₀ : sph K) (a : R2) : DΦ x₀ 0 a = ι x₀ a := by
  rw [DΦ_apply]; simp

lemma symmL_self' (x : sph K) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).symmL ℝ x = (1 : R2 →L[ℝ] R2) :=
  ContinuousLinearMap.ext fun a ↦ by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source R2 x)]
    exact (tangentBundleCore 𝓘(ℝ, R2) (sph K)).coordChange_self (achart R2 x) x
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source R2 x) a

lemma continuousLinearMapAt_self' (x : sph K) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).continuousLinearMapAt ℝ x =
      (1 : R2 →L[ℝ] R2) :=
  ContinuousLinearMap.ext fun a ↦ by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source R2 x)]
    exact (tangentBundleCore 𝓘(ℝ, R2) (sph K)).coordChange_self (achart R2 x) x
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source R2 x) a

lemma symmL_self (x : sph K) (a : R2) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).symmL ℝ x a = a := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source R2 x)]
  exact (tangentBundleCore 𝓘(ℝ, R2) (sph K)).coordChange_self (achart R2 x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source R2 x) a

lemma continuousLinearMapAt_self (x : sph K) (a : R2) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).continuousLinearMapAt ℝ x a = a := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source R2 x)]
  exact (tangentBundleCore 𝓘(ℝ, R2) (sph K)).coordChange_self (achart R2 x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source R2 x) a

lemma coe_comp_extChartAt_symm (x₀ : sph K) :
    ((Subtype.val : sph K → E3) ∘ (extChartAt 𝓘(ℝ, R2) x₀).symm) = Φ x₀ :=
  funext fun w ↦ chartAt_symm_eq x₀ w

/-- The derivative of the inclusion `S² → ℝ³` on the coordinate vectors of the chart at `x₀`. -/
lemma mfderiv_coe_symmL (x₀ y : sph K) (hy : y ∈ (chartAt R2 x₀).source) (a : R2) :
    mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, E3) (Subtype.val : sph K → E3) y
      ((trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x₀).symmL ℝ y a) =
      DΦ x₀ (chartAt R2 x₀ y) a := by
  have hd : DifferentiableAt ℝ ((Subtype.val : sph K → E3) ∘ (extChartAt 𝓘(ℝ, R2) x₀).symm)
      (extChartAt 𝓘(ℝ, R2) x₀ y) := by
    rw [coe_comp_extChartAt_symm]; exact (hasFDerivAt_Φ x₀ _).differentiableAt
  rw [mfderiv_symmL_eq_fderiv hy hd, coe_comp_extChartAt_symm, (hasFDerivAt_Φ x₀ _).fderiv]
  rfl

/-- At `y`, in the chart at `y`, the derivative of the inclusion `S² → ℝ³` is the linear isometry
`ι y`. -/
lemma mfderiv_coe_self (y : sph K) (u : R2) :
    mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, E3) (Subtype.val : sph K → E3) y u = ι y u := by
  have h := mfderiv_coe_symmL y y (mem_chart_source R2 y) u
  rw [symmL_self, chartAt_self, DΦ_zero] at h
  exact h

/-- The changes of chart are conformal, with factor `4 / (‖w‖² + 4)` at `w`. -/
lemma inner_symmL (x₀ y : sph K) (hy : y ∈ (chartAt R2 x₀).source) (a b : R2) :
    inner ℝ (show R2 from (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x₀).symmL ℝ y a)
      (show R2 from (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x₀).symmL ℝ y b) =
      16 / (‖chartAt R2 x₀ y‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  rw [← inner_ι y, ← mfderiv_coe_self, ← mfderiv_coe_self, mfderiv_coe_symmL x₀ y hy,
    mfderiv_coe_symmL x₀ y hy, inner_DΦ]

lemma symmL_eq_fderiv (x y : sph K) (hy : y ∈ (chartAt R2 x).source) (a : R2) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).symmL ℝ y a =
      fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x y) a := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hy, tangentBundleCore_coordChange_achart]
  simp [fderivWithin_univ]
  rfl

lemma inner_fderiv_chart (x y : sph K) (hy : y ∈ (chartAt R2 x).source) (a b : R2) :
    inner ℝ (fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x y) a)
      (fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x y) b) =
      16 / (‖chartAt R2 x y‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  rw [← symmL_eq_fderiv x y hy a, ← symmL_eq_fderiv x y hy b]
  exact inner_symmL x y hy a b

/-- The conformal factor of the metric in the chart: `λ(w) = 16 / (K (‖w‖² + 4)²)`. -/
def lam (K : ℝ) (w : R2) : ℝ := K⁻¹ * (16 / (‖w‖ ^ 2 + 4) ^ 2)

lemma contDiff_lam (K : ℝ) : ContDiff ℝ ∞ (lam K) :=
  contDiff_const.mul (contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
    fun w ↦ by positivity)

/-- The metric in the chart: `λ(w) ⟨·, ·⟩`. -/
def gS (K : ℝ) (w : R2) : R2 →L[ℝ] R2 →L[ℝ] ℝ :=
  innerBil ∘L (lam K w • ContinuousLinearMap.id ℝ R2)

lemma gS_apply (K : ℝ) (w a b : R2) : gS K w a b = lam K w * inner ℝ a b := by
  simp [gS, innerBil_apply]

lemma contDiff_gS (K : ℝ) : ContDiff ℝ ∞ (gS K) :=
  contDiff_const.clm_comp ((contDiff_lam K).smul contDiff_const)

section Metric

variable [hK : Fact (0 < K)]

set_option backward.isDefEq.respectTransparency false in
/-- The Riemannian metric of the sphere of curvature `K`: `(1/K)` times the round metric (in the
chart at each point `x`, `⟨u, v⟩ / K`). -/
def metric (K : ℝ) [hK : Fact (0 < K)] : ContMDiffRiemannianMetric 𝓘(ℝ, R2) ∞ R2
    (fun x : sph K ↦ TangentSpace 𝓘(ℝ, R2) x) where
  inner _ := (1 / K) • innerBil
  symm x v w := by
    show (1 / K) * inner ℝ (show R2 from v) (show R2 from w) =
      (1 / K) * inner ℝ (show R2 from w) (show R2 from v)
    rw [real_inner_comm]
  pos x v hv := by
    show 0 < (1 / K) * inner ℝ (show R2 from v) (show R2 from v)
    exact mul_pos (by have := hK.out; positivity) (real_inner_self_pos.2 hv)
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : R2 | ((1 / K) • innerBil) v v < 1}
    refine (NormedSpace.isVonNBounded_ball ℝ R2 (√K + 1)).subset fun v hv ↦ ?_
    have hv' : (1 / K) * inner ℝ v v < 1 := hv
    have hK' := hK.out
    rw [real_inner_self_eq_norm_sq, one_div, inv_mul_lt_iff₀ hK', mul_one] at hv'
    rw [mem_ball_zero_iff]
    have h3 : ‖v‖ < √K := by
      rw [← Real.sqrt_sq (norm_nonneg v)]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hv'
    linarith
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have hev : (fun y : sph K ↦ ((trivializationAt (R2 →L[ℝ] R2 →L[ℝ] ℝ)
        (fun x : sph K ↦ TangentSpace 𝓘(ℝ, R2) x →L[ℝ] TangentSpace 𝓘(ℝ, R2) x →L[ℝ] ℝ) x)
        ⟨y, (1 / K) • innerBil⟩).2) =ᶠ[𝓝 x]
        fun y ↦ gS K (extChartAt 𝓘(ℝ, R2) x y) := by
      filter_upwards [(chartAt R2 x).open_source.mem_nhds (mem_chart_source R2 x)] with y hy
      ext a b
      simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        Trivialization.linearMapAt_apply, hy]
      have h := inner_fderiv_chart x y hy a b
      calc _ = K⁻¹ * inner ℝ (fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x y) a)
            (fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x y) b) := rfl
        _ = _ := by
          rw [h, gS_apply, lam]
          ring
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    exact (contDiff_gS K).contMDiff.contMDiffAt.comp x (contMDiffAt_extChartAt (n := ∞))

/-- The Riemannian metric of the sphere of curvature `K`. -/
noncomputable instance instRiemannianBundle :
    RiemannianBundle (fun x : sph K ↦ TangentSpace 𝓘(ℝ, R2) x) :=
  ⟨(metric K).toRiemannianMetric⟩

/-- The Riemannian metric of the sphere is smooth. -/
instance instIsContMDiffRiemannianBundle : IsContMDiffRiemannianBundle 𝓘(ℝ, R2) ∞ R2
    (fun x : sph K ↦ TangentSpace 𝓘(ℝ, R2) x) :=
  inferInstance

lemma inner_eq (x : sph K) (u v : TangentSpace 𝓘(ℝ, R2) x) :
    inner ℝ u v = K⁻¹ * inner ℝ (show R2 from u) (show R2 from v) := by
  show (1 / K) * _ = _
  rw [one_div]
  rfl

lemma norm_tangent_eq (x : sph K) (v : R2) :
    ‖(show TangentSpace 𝓘(ℝ, R2) x from v)‖ = ‖v‖ / √K := by
  rw [norm_eq_sqrt_real_inner, inner_eq]
  show √(K⁻¹ * inner ℝ v v) = _
  rw [real_inner_self_eq_norm_sq, Real.sqrt_mul (inv_nonneg.2 hK.out.le), Real.sqrt_sq
    (norm_nonneg v), Real.sqrt_inv, inv_mul_eq_div]

end Metric

section Curvature

variable [hK : Fact (0 < K)]

omit hK in
lemma mem_target (x : sph K) (q : R2) : q ∈ (extChartAt 𝓘(ℝ, R2) x).target := by
  rw [extChartAt_target]
  simp only [modelWithCornersSelf_coe, range_id, inter_univ, modelWithCornersSelf_coe_symm,
    preimage_id_eq, id_eq]
  rw [chartAt_eq, stereographic'_target]
  trivial

/-- **The metric of the sphere in every chart**: `16 / (K (‖w‖² + 4)²) ⟨·, ·⟩`. -/
lemma metricCoord_eq (x : sph K) (w : R2) : metricCoord 𝓘(ℝ, R2) x w = gS K w := by
  have hw := mem_target x w
  have hy : (extChartAt 𝓘(ℝ, R2) x).symm w ∈ (chartAt R2 x).source := by
    simpa using (extChartAt 𝓘(ℝ, R2) x).map_target hw
  have hxy : chartAt R2 x ((extChartAt 𝓘(ℝ, R2) x).symm w) = w :=
    (extChartAt 𝓘(ℝ, R2) x).right_inv hw
  refine ContinuousLinearMap.ext fun a ↦ ContinuousLinearMap.ext fun b ↦ ?_
  rw [metricCoord_apply, coordField, coordField, trivSection, trivSection, inner_eq,
    inner_symmL x _ hy, hxy, gS_apply, lam]
  ring

lemma metricCoord_fun_eq (x : sph K) : metricCoord 𝓘(ℝ, R2) x = gS K :=
  funext (metricCoord_eq x)

omit hK in
lemma hasFDerivAt_lam (q : R2) :
    HasFDerivAt (lam K) ((-32 * K⁻¹ / (‖q‖ ^ 2 + 4) ^ 3) • (2 • innerSL ℝ q)) q := by
  have hN0 : ‖q‖ ^ 2 + 4 ≠ 0 := by positivity
  have hN : HasFDerivAt (fun w : R2 ↦ ‖w‖ ^ 2 + 4) (2 • innerSL ℝ q) q :=
    (hasStrictFDerivAt_norm_sq q).hasFDerivAt.add_const 4
  have hh : HasDerivAt (fun s : ℝ ↦ K⁻¹ * (16 / s ^ 2)) (-32 * K⁻¹ / (‖q‖ ^ 2 + 4) ^ 3)
      (‖q‖ ^ 2 + 4) := by
    have := ((hasDerivAt_const (‖q‖ ^ 2 + 4) (16 : ℝ)).div (hasDerivAt_pow 2 (‖q‖ ^ 2 + 4))
      (pow_ne_zero 2 hN0)).const_mul K⁻¹
    convert this using 1
    field_simp
    ring
  have h : HasFDerivAt ((fun s : ℝ ↦ K⁻¹ * (16 / s ^ 2)) ∘ (fun w : R2 ↦ ‖w‖ ^ 2 + 4))
      ((-32 * K⁻¹ / (‖q‖ ^ 2 + 4) ^ 3) • (2 • innerSL ℝ q)) q := hh.comp_hasFDerivAt q hN
  exact h

omit hK in
/-- The derivative of the metric coefficients in the chart. -/
lemma fderiv_gS (q a b c : R2) :
    fderiv ℝ (gS K) q a b c = -64 * K⁻¹ * inner ℝ q a / (‖q‖ ^ 2 + 4) ^ 3 * inner ℝ b c := by
  rw [← fderiv_apply_apply ((contDiff_gS K).differentiable (by simp) q) a b c]
  have hfun : (fun q ↦ gS K q b c) = fun q ↦ lam K q * inner ℝ b c :=
    funext fun q ↦ gS_apply K q b c
  rw [hfun, ((hasFDerivAt_lam q).mul_const (inner ℝ b c)).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- **The Christoffel symbols of the sphere** in the chart:
`Γ(q)(a, b) = −(2 / (‖q‖² + 4)) (⟨q, a⟩ b + ⟨q, b⟩ a − ⟨a, b⟩ q)`. -/
lemma christoffelL_eq (x : sph K) (q a b : R2) :
    christoffelL 𝓘(ℝ, R2) x q a b =
      (-2 / (‖q‖ ^ 2 + 4)) • (inner ℝ q a • b + inner ℝ q b • a - inner ℝ a b • q) := by
  have hN0 : ‖q‖ ^ 2 + 4 ≠ 0 := by positivity
  have hK0 : K ≠ 0 := hK.out.ne'
  rw [christoffelL_apply]
  apply (isInvertible_metricCoord x (mem_target x q)).injective
  rw [metricCoord_christoffel x (mem_target x q)]
  refine ContinuousLinearMap.ext fun c ↦ ?_
  rw [christoffelLow_apply, metricCoord_fun_eq, fderiv_gS, fderiv_gS, fderiv_gS, gS_apply, lam]
  simp only [inner_smul_left, inner_add_left, inner_sub_left, conj_trivial]
  simp only [real_inner_comm a c]
  field_simp
  ring

lemma christoffelL_fun_eq (x : sph K) (b c : R2) :
    (fun q ↦ christoffelL 𝓘(ℝ, R2) x q b c) =
      fun q ↦ (-2 / (‖q‖ ^ 2 + 4)) • (inner ℝ q b • c + inner ℝ q c • b - inner ℝ b c • q) :=
  funext fun q ↦ christoffelL_eq x q b c

/-- The derivative of the Christoffel symbols at the center of the chart. -/
lemma christoffelDeriv_zero (x : sph K) (a b c : R2) :
    christoffelDeriv 𝓘(ℝ, R2) x 0 a b c =
      (-1 / 2 : ℝ) • (inner ℝ a b • c + inner ℝ a c • b - inner ℝ b c • a) := by
  set L : R2 →L[ℝ] R2 := (innerSL ℝ b).smulRight c + (innerSL ℝ c).smulRight b -
    inner ℝ b c • ContinuousLinearMap.id ℝ R2 with hL_def
  have hL : ∀ q : R2, inner ℝ q b • c + inner ℝ q c • b - inner ℝ b c • q = L q := by
    intro q
    simp [L, real_inner_comm]
  have hs : DifferentiableAt ℝ (fun q : R2 ↦ -2 / (‖q‖ ^ 2 + 4)) 0 :=
    ((contDiff_const.div ((contDiff_norm_sq ℝ).add contDiff_const) fun q ↦ by positivity :
      ContDiff ℝ ∞ (fun q : R2 ↦ -2 / (‖q‖ ^ 2 + 4))).differentiable (by simp)) 0
  have h : HasFDerivAt (fun q ↦ (-2 / (‖q‖ ^ 2 + 4)) • L q) _ 0 :=
    hs.hasFDerivAt.smul L.hasFDerivAt
  rw [christoffelDeriv, christoffelL_fun_eq]
  simp_rw [hL]
  rw [h.fderiv]
  simp [L, real_inner_comm]
  module

/-- **The curvature tensor at the center of the chart**: `R(a, b) c = ⟨b, c⟩ a − ⟨a, c⟩ b`. -/
lemma curvCoord_zero (x : sph K) (a b c : R2) :
    curvCoord 𝓘(ℝ, R2) x 0 a b c = inner ℝ b c • a - inner ℝ a c • b := by
  rw [curvCoord, christoffelDeriv_zero, christoffelDeriv_zero]
  simp only [christoffelL_eq x 0, inner_zero_left, zero_smul, zero_add, smul_zero, sub_zero,
    real_inner_comm a b]
  module

/-- **The curvature tensor of the sphere**: in the chart at `x`, `R(u, v) w = ⟨v, w⟩ u − ⟨u, w⟩ v`
(Euclidean inner products), i.e. `K (g(v, w) u − g(u, w) v)`. -/
theorem riemannCurvature_eq (x : sph K) (u v w : TangentSpace 𝓘(ℝ, R2) x) :
    riemannCurvature 𝓘(ℝ, R2) x u v w = (K * inner ℝ v w) • u - (K * inner ℝ u w) • v := by
  have hK0 : K ≠ 0 := hK.out.ne'
  have h1 : K * inner ℝ v w = innerBil v w := by
    rw [inner_eq, mul_inv_cancel_left₀ hK0]; rfl
  have h2 : K * inner ℝ u w = innerBil u w := by
    rw [inner_eq, mul_inv_cancel_left₀ hK0]; rfl
  rw [riemannCurvature, continuousLinearMapAt_self', symmL_self',
    show extChartAt 𝓘(ℝ, R2) x x = 0 from chartAt_self x, h1, h2]
  exact curvCoord_zero x u v w

/-- **The sphere `sph K` has constant curvature `K`.** -/
theorem hasConstSectionalCurvature : HasConstSectionalCurvature 𝓘(ℝ, R2) (sph K) K := by
  intro x u v
  rw [riemannCurvature_eq, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm u v]
  ring

end Curvature

section GeodesicDefs

/-- `T_v(t) = tan(‖v‖ t / 2)`. -/
def Tn (v : R2) (t : ℝ) : ℝ := Real.tan (‖v‖ * t / 2)

/-- **The geodesics of the sphere from the center of a chart**, in that chart:
`c(t) = (2 tan(‖v‖ t / 2) / ‖v‖) v` (for `‖v‖ |t| < π`). -/
def cS (v : R2) (t : ℝ) : R2 := (2 * Tn v t / ‖v‖) • v

/-- The derivative `c'(t) = (1 + tan²(‖v‖ t / 2)) v`. -/
def cS' (v : R2) (t : ℝ) : R2 := (1 + Tn v t ^ 2) • v

/-- The second derivative `c''(t)`. -/
def cS'' (v : R2) (t : ℝ) : R2 := (‖v‖ * Tn v t * (1 + Tn v t ^ 2)) • v

/-- The interval of times `‖v‖ |t| < π`. -/
def J (v : R2) : Set ℝ := {t | ‖v‖ * |t| < Real.pi}

/-- The geodesic of the sphere from `x₀` with initial velocity `v` (read in the chart at `x₀`). -/
def gC (x₀ : sph K) (v : R2) (t : ℝ) : sph K := (chartAt R2 x₀).symm (cS v t)

lemma zero_mem_J (v : R2) : (0 : ℝ) ∈ J v := by
  show ‖v‖ * |(0 : ℝ)| < Real.pi
  rw [abs_zero, mul_zero]; exact Real.pi_pos

lemma isOpen_J (v : R2) : IsOpen (J v) :=
  isOpen_lt (continuous_const.mul continuous_abs) continuous_const

lemma isPreconnected_J (v : R2) : IsPreconnected (J v) := by
  refine Set.OrdConnected.isPreconnected ⟨fun a ha b hb t ht ↦ ?_⟩
  have ha' : ‖v‖ * |a| < Real.pi := ha
  have hb' : ‖v‖ * |b| < Real.pi := hb
  show ‖v‖ * |t| < Real.pi
  have h : |t| ≤ max |a| |b| := abs_le_max_abs_abs ht.1 ht.2
  rcases le_total |a| |b| with hab | hab
  · rw [max_eq_right hab] at h
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (norm_nonneg v)) hb'
  · rw [max_eq_left hab] at h
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (norm_nonneg v)) ha'

lemma Icc_subset_J {v : R2} (hv : ‖v‖ < Real.pi) : Icc (0 : ℝ) 1 ⊆ J v := fun t ht ↦ by
  show ‖v‖ * |t| < Real.pi
  rw [abs_of_nonneg ht.1]
  calc ‖v‖ * t ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg v)
    _ < Real.pi := by rwa [mul_one]

lemma cos_pos_of_mem_J {v : R2} {t : ℝ} (ht : t ∈ J v) : 0 < Real.cos (‖v‖ * t / 2) := by
  have h : ‖v‖ * |t| < Real.pi := ht
  have h' : |‖v‖ * t / 2| < Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_norm, abs_two]; linarith
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (‖v‖ * t / 2)],
    by linarith [le_abs_self (‖v‖ * t / 2)]⟩

lemma hasDerivAt_Tn {v : R2} {t : ℝ} (ht : t ∈ J v) :
    HasDerivAt (Tn v) (‖v‖ / 2 * (1 + Tn v t ^ 2)) t := by
  have hc := (cos_pos_of_mem_J ht).ne'
  have h1 : HasDerivAt (fun s : ℝ ↦ ‖v‖ * s / 2) (‖v‖ / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul ‖v‖).div_const 2
  have h2 : HasDerivAt (Tn v) (1 / Real.cos (‖v‖ * t / 2) ^ 2 * (‖v‖ / 2)) t :=
    (Real.hasDerivAt_tan hc).comp t h1
  convert h2 using 1
  have hsc := Real.sin_sq_add_cos_sq (‖v‖ * t / 2)
  rw [Tn, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination ‖v‖ * hsc

lemma hasDerivAt_cS (v : R2) {t : ℝ} (ht : t ∈ J v) : HasDerivAt (cS v) (cS' v t) t := by
  rcases eq_or_ne v 0 with rfl | hv
  · show HasDerivAt (fun t ↦ (2 * Tn 0 t / ‖(0 : R2)‖) • (0 : R2)) ((1 + Tn 0 t ^ 2) • (0 : R2)) t
    simp only [smul_zero]
    exact hasDerivAt_const t 0
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have h : HasDerivAt (cS v) ((2 * (‖v‖ / 2 * (1 + Tn v t ^ 2)) / ‖v‖) • v) t :=
      (((hasDerivAt_Tn ht).const_mul 2).div_const ‖v‖).smul_const v
    convert h using 1
    rw [cS']
    congr 1
    field_simp

lemma hasDerivAt_cS' (v : R2) {t : ℝ} (ht : t ∈ J v) : HasDerivAt (cS' v) (cS'' v t) t := by
  have h : HasDerivAt (cS' v) ((↑2 * Tn v t ^ (2 - 1) * (‖v‖ / 2 * (1 + Tn v t ^ 2))) • v) t :=
    (((hasDerivAt_Tn ht).pow 2).const_add 1).smul_const v
  convert h using 1
  rw [cS'']
  congr 1
  simp only [Nat.add_one_sub_one, pow_one]
  ring

/-- **The geodesic equation in the chart**: `c'' = −Γ(c)(c', c')`. -/
lemma cS''_eq (v : R2) (t : ℝ) :
    cS'' v t = -((-2 / (‖cS v t‖ ^ 2 + 4)) • (inner ℝ (cS v t) (cS' v t) • cS' v t +
      inner ℝ (cS v t) (cS' v t) • cS' v t - inner ℝ (cS' v t) (cS' v t) • cS v t)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [cS, cS', cS'']
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    simp only [cS, cS', cS'', inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
      conj_trivial, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hT : 0 < 1 + Tn v t ^ 2 := by positivity
    match_scalars
    field_simp
    ring

lemma chart_gC (x₀ : sph K) (v : R2) (t : ℝ) : chartAt R2 x₀ (gC x₀ v t) = cS v t :=
  (chartAt R2 x₀).right_inv (by rw [chartAt_eq, stereographic'_target]; trivial)

lemma gC_mem_source (x₀ : sph K) (v : R2) (t : ℝ) : gC x₀ v t ∈ (chartAt R2 x₀).source :=
  (chartAt R2 x₀).map_target (by rw [chartAt_eq, stereographic'_target]; trivial)

lemma extChartAt_comp_gC (x₀ : sph K) (v : R2) : extChartAt 𝓘(ℝ, R2) x₀ ∘ gC x₀ v = cS v :=
  funext fun t ↦ chart_gC x₀ v t

lemma cS_zero (v : R2) : cS v 0 = 0 := by simp [cS, Tn]

lemma gC_zero (x₀ : sph K) (v : R2) : gC x₀ v 0 = x₀ := by
  rw [gC, cS_zero, ← chartAt_self x₀]
  exact (chartAt R2 x₀).left_inv (mem_chart_source R2 x₀)

lemma mdifferentiableAt_gC (x₀ : sph K) (v : R2) {t : ℝ} (ht : t ∈ J v) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) (gC x₀ v) t := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, R2) 𝓘(ℝ, R2) (extChartAt 𝓘(ℝ, R2) x₀).symm (cS v t) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds (mem_target x₀ _))).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) (cS v) t :=
    (hasDerivAt_cS v ht).differentiableAt.mdifferentiableAt
  exact hsymm.comp t hc

lemma deriv_cS_eventuallyEq (v : R2) {t : ℝ} (ht : t ∈ J v) :
    deriv (cS v) =ᶠ[𝓝 t] cS' v := by
  filter_upwards [(isOpen_J v).mem_nhds ht] with s hs using (hasDerivAt_cS v hs).deriv

/-- The velocity of `gC x₀ v`, read in the trivialization at `x₀`. -/
lemma velocity_gC (x₀ : sph K) (v : R2) {t : ℝ} (ht : t ∈ J v) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x₀).continuousLinearMapAt ℝ (gC x₀ v t)
      (velocity 𝓘(ℝ, R2) (gC x₀ v) t) = cS' v t := by
  rw [trivializationAt_velocity x₀ (mdifferentiableAt_gC x₀ v ht) (gC_mem_source x₀ v t),
    extChartAt_comp_gC, (hasDerivAt_cS v ht).deriv]

variable [hK : Fact (0 < K)]

/-- **The curves `gC x₀ v` are geodesics** on the interval `‖v‖ |t| < π`. -/
theorem isGeodesicOn_gC (x₀ : sph K) (v : R2) : IsGeodesicOn 𝓘(ℝ, R2) (gC x₀ v) (J v) := by
  intro t ht
  have hev : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) (gC x₀ v) s ∧
      gC x₀ v s ∈ (chartAt R2 x₀).source := by
    filter_upwards [(isOpen_J v).mem_nhds ht] with s hs
    exact ⟨mdifferentiableAt_gC x₀ v hs, gC_mem_source x₀ v s⟩
  refine (geodesicAt_iff_chart x₀ hev).2 ?_
  rw [extChartAt_comp_gC, (hasDerivAt_cS v ht).deriv]
  show HasDerivAt (deriv (cS v)) (-christoffelL 𝓘(ℝ, R2) x₀ (chartAt R2 x₀ (gC x₀ v t))
    (cS' v t) (cS' v t)) t
  rw [chart_gC, christoffelL_eq, ← cS''_eq]
  exact (hasDerivAt_cS' v ht).congr_of_eventuallyEq (deriv_cS_eventuallyEq v ht)

theorem isGeodesicFrom_gC (x₀ : sph K) (v : R2) :
    IsGeodesicFrom 𝓘(ℝ, R2) x₀ v (gC x₀ v) (J v) where
  isOpen := isOpen_J v
  isPreconnected := isPreconnected_J v
  zero_mem := zero_mem_J v
  isGeodesicOn := isGeodesicOn_gC x₀ v
  apply_zero := gC_zero x₀ v
  velocity_zero := by
    have h := velocity_gC x₀ v (zero_mem_J v)
    have hcl : ∀ y : sph K, y = x₀ → ∀ u : TangentSpace 𝓘(ℝ, R2) y,
        (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x₀).continuousLinearMapAt ℝ y u = u := by
      rintro y rfl u; exact continuousLinearMapAt_self y u
    have h2 := hcl _ (gC_zero x₀ v) (velocity 𝓘(ℝ, R2) (gC x₀ v) 0)
    have h3 : cS' v 0 = v := by simp [cS', Tn]
    exact h2.symm.trans (h.trans h3)

/-- **The exponential map of the sphere** on the ball `‖v‖ < π` of the chart at `x₀`:
`exp_{x₀} v = gC x₀ v 1`. -/
theorem expMap_eq (x₀ : sph K) {v : R2} (hv : ‖v‖ < Real.pi) :
    v ∈ expDomain 𝓘(ℝ, R2) x₀ ∧ expMap 𝓘(ℝ, R2) x₀ v = gC x₀ v 1 :=
  PythagoreanPaper.expMap_eq (isGeodesicFrom_gC x₀ v) (Icc_subset_J hv)

lemma mem_tangentBall_iff (x₀ : sph K) (v : R2) :
    v ∈ tangentBall 𝓘(ℝ, R2) x₀ (Real.pi / √K) ↔ ‖v‖ < Real.pi := by
  have hK' : 0 < √K := Real.sqrt_pos.2 hK.out
  show ‖(show TangentSpace 𝓘(ℝ, R2) x₀ from v)‖ < Real.pi / √K ↔ _
  rw [norm_tangent_eq, div_lt_div_iff_of_pos_right hK']

omit hK in
lemma norm_cS_one {v : R2} (hv : ‖v‖ < Real.pi) : ‖cS v 1‖ = 2 * Real.tan (‖v‖ / 2) := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [cS, Tn]
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have htan : 0 ≤ Real.tan (‖v‖ / 2) :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by positivity) (by linarith)
    rw [cS, Tn, mul_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hn.ne']

/-- **The exponential map is injective on the ball of radius `π/√K`.** -/
theorem injOn_expMap (x₀ : sph K) :
    InjOn (expMap 𝓘(ℝ, R2) x₀) (tangentBall 𝓘(ℝ, R2) x₀ (Real.pi / √K)) := by
  intro v hv w hw h
  rw [mem_tangentBall_iff] at hv hw
  rw [(expMap_eq x₀ hv).2, (expMap_eq x₀ hw).2] at h
  have hc : cS v 1 = cS w 1 := by rw [← chart_gC x₀ v 1, ← chart_gC x₀ w 1, h]
  have hn : ‖v‖ = ‖w‖ := by
    have h1 := norm_cS_one hv
    rw [hc, norm_cS_one hw] at h1
    have h2 : Real.tan (‖w‖ / 2) = Real.tan (‖v‖ / 2) := by linarith
    have hv2 := norm_nonneg v
    have hw2 := norm_nonneg w
    have e1 := Real.arctan_tan (x := ‖v‖ / 2) (by linarith [Real.pi_pos]) (by linarith)
    have e2 := Real.arctan_tan (x := ‖w‖ / 2) (by linarith [Real.pi_pos]) (by linarith)
    rw [h2] at e2
    linarith
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [norm_zero, eq_comm, norm_eq_zero] at hn
    exact hn.symm
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have htan : 0 < Real.tan (‖v‖ / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith)
    rw [cS, cS, Tn, Tn, ← hn, mul_one] at hc
    exact smul_right_injective R2 (div_pos (mul_pos two_pos htan) hpos).ne' hc

/-- **The ball of radius `π/√K` of `T_x` is a normal ball** of the sphere of curvature `K`. -/
theorem isNormalBall (x : sph K) : IsNormalBall 𝓘(ℝ, R2) x (Real.pi / √K) :=
  isNormalBall_of_constCurvature finrank_euclideanSpace_fin hasConstSectionalCurvature
    (div_pos Real.pi_pos (Real.sqrt_pos.2 hK.out)) (fun _ ↦ le_rfl)
    (fun v hv ↦ (expMap_eq x ((mem_tangentBall_iff x v).1 hv)).1) (injOn_expMap x)

/-- **The image of the normal ball of radius `π/√K`** contains every point other than the
antipode `−x₀`. -/
theorem mem_expMap_image_of_ne (x₀ y : sph K) (hy : (y : E3) ≠ -(x₀ : E3)) :
    y ∈ expMap 𝓘(ℝ, R2) x₀ '' tangentBall 𝓘(ℝ, R2) x₀ (Real.pi / √K) := by
  have hys : y ∈ (chartAt R2 x₀).source := (mem_chartAt_source_iff x₀ y).2 hy
  set z := chartAt R2 x₀ y with hz_def
  set r := 2 * Real.arctan (‖z‖ / 2) with hr_def
  set v : R2 := (r / ‖z‖) • z with hv_def
  have hr0 : 0 ≤ r := by
    have := Real.arctan_nonneg.2 (by positivity : (0 : ℝ) ≤ ‖z‖ / 2); linarith
  have hrπ : r < Real.pi := by have := Real.arctan_lt_pi_div_two (‖z‖ / 2); linarith
  have hnv : ‖v‖ = r := by
    rcases eq_or_ne z 0 with hz | hz
    · simp [v, r, hz]
    · rw [hv_def, norm_smul, Real.norm_eq_abs, abs_div, abs_norm, abs_of_nonneg hr0,
        div_mul_cancel₀ _ (norm_ne_zero_iff.2 hz)]
  have hvπ : ‖v‖ < Real.pi := hnv ▸ hrπ
  have hcS : cS v 1 = z := by
    rcases eq_or_ne z 0 with hz | hz
    · simp [cS, v, hz]
    · have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hr : 0 < r := by
        have := Real.arctan_pos.2 (by positivity : (0 : ℝ) < ‖z‖ / 2); linarith
      rw [cS, Tn, hnv, mul_one, show r / 2 = Real.arctan (‖z‖ / 2) by rw [hr_def]; ring,
        Real.tan_arctan, hv_def, smul_smul]
      rw [show 2 * (‖z‖ / 2) / r * (r / ‖z‖) = 1 by field_simp, one_smul]
  refine ⟨v, (mem_tangentBall_iff x₀ v).2 hvπ, ?_⟩
  rw [(expMap_eq x₀ hvπ).2, gC, hcS]
  exact (chartAt R2 x₀).left_inv hys

end GeodesicDefs

section Triangles

variable [hK : Fact (0 < K)]
variable (T : GeodesicTriangle 𝓘(ℝ, R2) (sph K))

/-- If no point of the three sides is the antipode of `X`, then the normal ball of radius `π/√K`
around `X` contains the three sides. -/
theorem sidesInNormalBallAt_of_ne (X : sph K)
    (ha : ∀ t ∈ Icc 0 T.a, ((T.σa t : sph K) : E3) ≠ -(X : E3))
    (hb : ∀ t ∈ Icc 0 T.b, ((T.σb t : sph K) : E3) ≠ -(X : E3))
    (hc : ∀ t ∈ Icc 0 T.c, ((T.σc t : sph K) : E3) ≠ -(X : E3)) :
    T.SidesInNormalBallAt X :=
  ⟨Real.pi / √K, isNormalBall X, fun t ht ↦ mem_expMap_image_of_ne X _ (ha t ht),
    fun t ht ↦ mem_expMap_image_of_ne X _ (hb t ht),
    fun t ht ↦ mem_expMap_image_of_ne X _ (hc t ht)⟩

/-- The three sides of the triangle lie in an open hemisphere `{z | 0 < ⟨z, n⟩}`. -/
def InOpenHemisphere : Prop :=
  ∃ n : E3, (∀ t ∈ Icc 0 T.a, 0 < inner ℝ ((T.σa t : sph K) : E3) n) ∧
    (∀ t ∈ Icc 0 T.b, 0 < inner ℝ ((T.σb t : sph K) : E3) n) ∧
    (∀ t ∈ Icc 0 T.c, 0 < inner ℝ ((T.σc t : sph K) : E3) n)

/-- **A geodesic triangle of the sphere whose sides lie in an open hemisphere satisfies the
technical condition `SidesInNormalBalls`.** -/
theorem sidesInNormalBalls_of_inOpenHemisphere (h : InOpenHemisphere T) :
    T.SidesInNormalBalls := by
  obtain ⟨n, ha, hb, hc⟩ := h
  have hA : 0 < inner ℝ ((T.pA : sph K) : E3) n := by
    rw [← T.segment_c.apply_zero]; exact hc 0 ⟨le_rfl, T.segment_c.pos.le⟩
  have hB : 0 < inner ℝ ((T.pB : sph K) : E3) n := by
    rw [← T.segment_a.apply_zero]; exact ha 0 ⟨le_rfl, T.segment_a.pos.le⟩
  have hC : 0 < inner ℝ ((T.pC : sph K) : E3) n := by
    rw [← T.segment_b.apply_zero]; exact hb 0 ⟨le_rfl, T.segment_b.pos.le⟩
  have key : ∀ X : sph K, 0 < inner ℝ (X : E3) n → T.SidesInNormalBallAt X := by
    intro X hX
    refine sidesInNormalBallAt_of_ne T X (fun t ht h ↦ ?_) (fun t ht h ↦ ?_) (fun t ht h ↦ ?_)
    · have := ha t ht; rw [h, inner_neg_left] at this; linarith
    · have := hb t ht; rw [h, inner_neg_left] at this; linarith
    · have := hc t ht; rw [h, inner_neg_left] at this; linarith
  exact ⟨key _ hA, key _ hB, key _ hC⟩

end Triangles

end SphereModel
end PythagoreanPaper
