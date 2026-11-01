import PythagoreanPaper.Riemannian.NormalBall
import PythagoreanPaper.Riemannian.Triangle

/-!
# The hyperbolic plane as the model space of curvature `K < 0` (manuscript §9)

For `K < 0`, `hypPlane K` is the plane `ℝ²` with the metric
`g_x(a, b) = ⟨a, b⟩ + K ⟨x, a⟩ ⟨x, b⟩ / (1 − K ‖x‖²)` (`HypPlane.gH`): the metric induced on the
upper sheet of the hyperboloid `y₀² + K ‖y‖² = 1` of Minkowski space, in the coordinates `y = x`.
It is a Riemannian manifold in the sense of `PythagoreanPaper.Riemannian` (with the identity chart).
This file shows:

* `HypPlane.hasConstSectionalCurvature`: it has constant curvature `K`
  (Christoffel symbols `Γ(x)(a, b) = K g_x(a, b) x`, `HypPlane.christoffelL_eq`);
* `HypPlane.isGeodesicOn_geoCurve`, `HypPlane.expMap_eq`: the geodesic from `x` with initial
  velocity `v` is `t ↦ C_κ(t) x + S_κ(t) v` with `κ = K g_x(v, v)`, defined for all times;
* `HypPlane.expMap_injective`, `HypPlane.exists_expMap_eq`: `exp_x` is a bijection from `T_x` onto
  the plane (injectivity through the Lorentz pairing `F_x`, `HypPlane.F_geo`);
* `HypPlane.isNormalBall`: every ball of `T_x` is a normal ball;
* `HypPlane.sidesInNormalBalls`: **every** geodesic triangle of the hyperbolic plane satisfies the
  technical condition `SidesInNormalBalls` of `PythagoreanPaper.Riemannian.Triangle`.
-/

noncomputable section

open Bundle Set Filter Function TopologicalSpace
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

local notation "R2" => EuclideanSpace ℝ (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- The inner product of `ℝ²`, as a continuous bilinear map. -/
def innerBil : R2 →L[ℝ] R2 →L[ℝ] ℝ := innerSL ℝ

lemma innerBil_apply (a b : R2) : innerBil a b = inner ℝ a b := rfl

/-! ### Complements on `S_K` and `C_K` -/

lemma contDiff_S (K : ℝ) : ContDiff ℝ ∞ (S K) := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [show S K = fun r ↦ Real.sinh (√(-K) * r) / √(-K) from funext fun r ↦ S_of_neg r hK]
    exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).div_const _
  · rw [show S 0 = fun r ↦ r from funext fun r ↦ S_of_eq_zero r]
    exact contDiff_id
  · rw [show S K = fun r ↦ Real.sin (√K * r) / √K from funext fun r ↦ S_of_pos r hK]
    exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).div_const _

lemma contDiff_C (K : ℝ) : ContDiff ℝ ∞ (C K) := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [show C K = fun r ↦ Real.cosh (√(-K) * r) from funext fun r ↦ C_of_neg r hK]
    exact Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  · rw [show C 0 = fun _ ↦ (1 : ℝ) from funext fun r ↦ C_of_eq_zero r]
    exact contDiff_const
  · rw [show C K = fun r ↦ Real.cos (√K * r) from funext fun r ↦ C_of_pos r hK]
    exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

lemma C_pos_of_nonpos {κ : ℝ} (hκ : κ ≤ 0) (t : ℝ) : 0 < C κ t := by
  rcases hκ.lt_or_eq with h | rfl
  · rw [C_of_neg t h]; exact Real.cosh_pos _
  · rw [C_of_eq_zero]; exact one_pos

lemma C_one_of_nonpos {κ : ℝ} (hκ : κ ≤ 0) : C κ 1 = Real.cosh √(-κ) := by
  rcases hκ.lt_or_eq with h | rfl
  · rw [C_of_neg 1 h, mul_one]
  · rw [C_of_eq_zero, neg_zero, Real.sqrt_zero, Real.cosh_zero]

/-- `κ ↦ C_κ(1) = cosh √(-κ)` is injective on `κ ≤ 0`. -/
lemma C_one_injOn : InjOn (fun κ ↦ C κ 1) (Iic 0) := by
  intro κ₁ h₁ κ₂ h₂ h
  have h' : Real.cosh √(-κ₁) = Real.cosh √(-κ₂) := by
    rw [← C_one_of_nonpos h₁, ← C_one_of_nonpos h₂]; exact h
  have habs : |√(-κ₁)| = |√(-κ₂)| :=
    le_antisymm (Real.cosh_le_cosh.1 h'.le) (Real.cosh_le_cosh.1 h'.ge)
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_inj (neg_nonneg.2 h₁) (neg_nonneg.2 h₂)] at habs
  linarith

/-- Every `c ≥ 1` is `cosh s` for some `0 ≤ s ≤ c`. -/
lemma exists_cosh_eq {c : ℝ} (hc : 1 ≤ c) : ∃ s, 0 ≤ s ∧ s ≤ c ∧ Real.cosh s = c := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hmem : c ∈ Icc (Real.cosh 0) (Real.cosh c) :=
    ⟨by rw [Real.cosh_zero]; exact hc,
      (Real.self_le_sinh_iff.2 hc0).trans (Real.sinh_lt_cosh c).le⟩
  obtain ⟨s, ⟨hs0, hsc⟩, hs⟩ := intermediate_value_Icc hc0 Real.continuous_cosh.continuousOn hmem
  exact ⟨s, hs0, hsc, hs⟩

/-- Expansion of an inner product of two combinations of `p` and `v`. -/
lemma inner_comb (a b c d : ℝ) (p v : R2) :
    inner ℝ (a • p + b • v) (c • p + d • v) =
      a * c * ‖p‖ ^ 2 + (a * d + b * c) * inner ℝ p v + b * d * ‖v‖ ^ 2 := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm p v]
  ring

lemma inner_left_comb (c d : ℝ) (p v : R2) :
    inner ℝ p (c • p + d • v) = c * ‖p‖ ^ 2 + d * inner ℝ p v := by
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

lemma norm_comb_sq (a b : ℝ) (p v : R2) :
    ‖a • p + b • v‖ ^ 2 = a ^ 2 * ‖p‖ ^ 2 + 2 * a * b * inner ℝ p v + b ^ 2 * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_comb]; ring

/-- The hyperbolic plane of curvature `K`: the plane `ℝ²` (as an open subset of itself, so that
it is a manifold with the identity chart), with the metric `hypMetric K` below. -/
def hypPlane (_K : ℝ) : Opens R2 := ⊤

namespace HypPlane

variable {K : ℝ}

lemma mem (K : ℝ) (z : R2) : z ∈ hypPlane K := mem_univ z

/-- The point of the hyperbolic plane with coordinates `z`. -/
def pt (K : ℝ) (z : R2) : hypPlane K := ⟨z, mem K z⟩

@[simp] lemma pt_val (z : R2) : (pt K z : R2) = z := rfl

/-- `N(x) = 1 − K ‖x‖²`, positive for `K ≤ 0`. -/
def N (K : ℝ) (x : R2) : ℝ := 1 - K * ‖x‖ ^ 2

lemma one_le_N (hK : K ≤ 0) (x : R2) : 1 ≤ N K x := by
  unfold N; nlinarith [sq_nonneg ‖x‖]

lemma N_pos (hK : K ≤ 0) (x : R2) : 0 < N K x := lt_of_lt_of_le one_pos (one_le_N hK x)

/-- **The metric of the hyperboloid model**, in the coordinates `x ∈ ℝ²`:
`g_x(a, b) = ⟨a, b⟩ + K ⟨x, a⟩ ⟨x, b⟩ / (1 − K ‖x‖²)`. (It is the metric induced on the sheet
`y₀² − |K| ‖y‖² = 1`, `y₀ > 0`, of a hyperboloid in Minkowski space, through `y = x`.) -/
def gH (K : ℝ) (x : R2) : R2 →L[ℝ] R2 →L[ℝ] ℝ :=
  innerBil + (innerBil x).smulRight ((K / N K x) • innerBil x)

lemma gH_apply (x a b : R2) :
    gH K x a b = inner ℝ a b + K * inner ℝ x a * inner ℝ x b / N K x := by
  simp only [gH, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerBil_apply,
    smul_eq_mul]
  ring

lemma gH_symm (x a b : R2) : gH K x a b = gH K x b a := by
  rw [gH_apply, gH_apply, real_inner_comm a b]; ring

lemma gH_coercive (hK : K ≤ 0) (x a : R2) : ‖a‖ ^ 2 / N K x ≤ gH K x a a := by
  have hN := N_pos hK x
  rw [gH_apply, real_inner_self_eq_norm_sq, div_le_iff₀ hN]
  have hcs : inner ℝ x a ^ 2 ≤ ‖x‖ ^ 2 * ‖a‖ ^ 2 := by
    have := abs_real_inner_le_norm x a
    have h0 : 0 ≤ ‖x‖ * ‖a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc inner ℝ x a ^ 2 = |inner ℝ x a| ^ 2 := (sq_abs _).symm
      _ ≤ (‖x‖ * ‖a‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ‖x‖ ^ 2 * ‖a‖ ^ 2 := by ring
  have hexp : (‖a‖ ^ 2 + K * inner ℝ x a * inner ℝ x a / N K x) * N K x =
      ‖a‖ ^ 2 * N K x + K * inner ℝ x a ^ 2 := by
    field_simp
  rw [hexp]
  unfold N at hN ⊢
  nlinarith [mul_le_mul_of_nonpos_left hcs hK]

lemma gH_pos (hK : K ≤ 0) (x : R2) {a : R2} (ha : a ≠ 0) : 0 < gH K x a a :=
  lt_of_lt_of_le (div_pos (pow_pos (norm_pos_iff.2 ha) 2) (N_pos hK x)) (gH_coercive hK x a)

lemma contDiff_N (K : ℝ) : ContDiff ℝ ∞ (N K) :=
  contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))

lemma contDiff_gH (hK : K ≤ 0) : ContDiff ℝ ∞ (gH K) := by
  have hdiv : ContDiff ℝ ∞ (fun x ↦ K / N K x) :=
    contDiff_const.div (contDiff_N K) fun x ↦ (N_pos hK x).ne'
  have hsr : ContDiff ℝ ∞ (fun x : R2 ↦ (innerBil x).smulRight ((K / N K x) • innerBil x)) :=
    innerBil.contDiff.smulRight (hdiv.smul innerBil.contDiff)
  exact contDiff_const.add hsr

section Charts

/-- All the charts of `hypPlane K` (restrictions of the identity chart of `ℝ²`) are the same. -/
lemma achart_eq (x y : hypPlane K) : achart R2 x = achart R2 y := rfl

lemma chartAt_source (x : hypPlane K) : (chartAt R2 x).source = univ := by
  rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  simp

lemma extChartAt_apply (x y : hypPlane K) : extChartAt 𝓘(ℝ, R2) x y = (y : R2) := rfl

lemma extChartAt_symm_apply (x : hypPlane K) (z : R2) :
    (extChartAt 𝓘(ℝ, R2) x).symm z = pt K z := by
  have hz : z ∈ (extChartAt 𝓘(ℝ, R2) x).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, range_id, inter_univ]
    rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def,
      OpenPartialHomeomorph.trans_target]
    simp [Opens.openPartialHomeomorphSubtypeCoe_target, mem K z]
  apply Subtype.ext
  exact (extChartAt 𝓘(ℝ, R2) x).right_inv hz

lemma coordChange_eq_one (x y z : hypPlane K) :
    (tangentBundleCore 𝓘(ℝ, R2) (hypPlane K)).coordChange (achart R2 x) (achart R2 y) z = 1 := by
  rw [achart_eq y x]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  exact (tangentBundleCore 𝓘(ℝ, R2) (hypPlane K)).coordChange_self (achart R2 x) z
    (by rw [tangentBundleCore_baseSet, coe_achart, chartAt_source]; trivial) v

lemma continuousLinearMapAt_eq (x y : hypPlane K) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).continuousLinearMapAt ℝ y =
      (1 : R2 →L[ℝ] R2) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp [chartAt_source]),
    coordChange_eq_one]

lemma symmL_eq (x y : hypPlane K) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).symmL ℝ y = (1 : R2 →L[ℝ] R2) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by simp [chartAt_source]),
    coordChange_eq_one]

/-- The changes of chart of `hypPlane K` are the identity. -/
lemma fderiv_chart_trans (x y z : hypPlane K) (v : R2) :
    fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x z) v = v := by
  have h : (chartAt R2 y ∘ (chartAt R2 x).symm) =ᶠ[𝓝 (chartAt R2 x z)] id := by
    filter_upwards [(chartAt R2 x).open_target.mem_nhds
      ((chartAt R2 x).map_source (by simp [chartAt_source]))] with q hq
    exact (chartAt R2 x).right_inv hq
  rw [h.fderiv_eq, fderiv_id]
  rfl

end Charts

section Metric

variable [hK : Fact (K < 0)]

set_option backward.isDefEq.respectTransparency false in
/-- The Riemannian metric `gH K` on `hypPlane K`. -/
def metric (K : ℝ) [hK : Fact (K < 0)] : ContMDiffRiemannianMetric 𝓘(ℝ, R2) ∞ R2
    (fun x : hypPlane K ↦ TangentSpace 𝓘(ℝ, R2) x) where
  inner x := gH K x
  symm x v w := gH_symm (x : R2) v w
  pos x v hv := gH_pos hK.out.le (x : R2) hv
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : R2 | gH K x v v < 1}
    refine (NormedSpace.isVonNBounded_ball ℝ R2 (√(N K x) + 1)).subset fun v hv ↦ ?_
    have h1 := gH_coercive hK.out.le (x : R2) v
    have hv' : gH K x v v < 1 := hv
    have hN := N_pos hK.out.le (x : R2)
    have h2 : ‖v‖ ^ 2 < N K x := by
      have := lt_of_le_of_lt h1 hv'
      rwa [div_lt_one hN] at this
    rw [mem_ball_zero_iff]
    have h3 : ‖v‖ < √(N K x) := by
      rw [← Real.sqrt_sq (norm_nonneg v)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) h2
    linarith
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! ((contDiff_gH hK.out.le).contMDiff.comp
      (contMDiff_subtype_val (U := hypPlane K) (I := 𝓘(ℝ, R2)))).contMDiffAt (x := x)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.linearMapAt_apply, chartAt_source]
    erw [fderiv_chart_trans, fderiv_chart_trans]
    rfl

/-- The Riemannian metric of the hyperbolic plane. -/
noncomputable instance instRiemannianBundle :
    RiemannianBundle (fun x : hypPlane K ↦ TangentSpace 𝓘(ℝ, R2) x) :=
  ⟨(metric K).toRiemannianMetric⟩

/-- The Riemannian metric of the hyperbolic plane is smooth. -/
instance instIsContMDiffRiemannianBundle : IsContMDiffRiemannianBundle 𝓘(ℝ, R2) ∞ R2
    (fun x : hypPlane K ↦ TangentSpace 𝓘(ℝ, R2) x) :=
  inferInstance

lemma inner_eq (x : hypPlane K) (u v : TangentSpace 𝓘(ℝ, R2) x) :
    inner ℝ u v = gH K x u v := rfl

end Metric

section Calculus

lemma differentiableAt_gH (hK : K ≤ 0) (q : R2) : DifferentiableAt ℝ (gH K) q :=
  (contDiff_gH hK).differentiable (by simp) q

/-- The derivative of the coefficient `g(b, c)` of the metric in the direction `a`. -/
lemma fderiv_gH (hK : K ≤ 0) (q a b c : R2) :
    fderiv ℝ (gH K) q a b c = K * (inner ℝ a b * inner ℝ q c + inner ℝ q b * inner ℝ a c) /
      N K q + 2 * K ^ 2 * inner ℝ q a * inner ℝ q b * inner ℝ q c / N K q ^ 2 := by
  rw [← fderiv_apply_apply (differentiableAt_gH hK q) a b c]
  have hf : DifferentiableAt ℝ (fun q ↦ gH K q b c) q :=
    ((differentiableAt_gH hK q).clm_apply (differentiableAt_const b)).clm_apply
      (differentiableAt_const c)
  have hline : HasDerivAt (fun t : ℝ ↦ q + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add q
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [← hcomp.deriv]
  -- the function along the line, explicitly
  have hfun : ((fun q ↦ gH K q b c) ∘ fun t : ℝ ↦ q + t • a) = fun t : ℝ ↦
      inner ℝ b c + K * (inner ℝ q b + t * inner ℝ a b) * (inner ℝ q c + t * inner ℝ a c) /
        (N K q - 2 * K * t * inner ℝ q a - K * t ^ 2 * ‖a‖ ^ 2) := by
    funext t
    simp only [Function.comp_apply, gH_apply, inner_add_left, real_inner_smul_left, N]
    rw [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right]
    ring_nf
  rw [hfun]
  have hN0 : N K q - 2 * K * 0 * inner ℝ q a - K * 0 ^ 2 * ‖a‖ ^ 2 ≠ 0 := by
    simp only [mul_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    exact (N_pos hK q).ne'
  have hnum : HasDerivAt (fun t : ℝ ↦ K * (inner ℝ q b + t * inner ℝ a b) *
      (inner ℝ q c + t * inner ℝ a c))
      (K * (inner ℝ a b * inner ℝ q c + inner ℝ q b * inner ℝ a c)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ inner ℝ q b + t * inner ℝ a b) (inner ℝ a b) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ a b)).const_add (inner ℝ q b)
    have h2 : HasDerivAt (fun t : ℝ ↦ inner ℝ q c + t * inner ℝ a c) (inner ℝ a c) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ a c)).const_add (inner ℝ q c)
    convert (h1.const_mul K).mul h2 using 1
    simp
    ring
  have hden : HasDerivAt (fun t : ℝ ↦ N K q - 2 * K * t * inner ℝ q a - K * t ^ 2 * ‖a‖ ^ 2)
      (-(2 * K * inner ℝ q a)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ 2 * K * t * inner ℝ q a) (2 * K * inner ℝ q a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * K)).mul_const (inner ℝ q a)
    have h2 : HasDerivAt (fun t : ℝ ↦ K * t ^ 2 * ‖a‖ ^ 2) 0 0 := by
      simpa using (((hasDerivAt_pow 2 (0 : ℝ)).const_mul K).mul_const (‖a‖ ^ 2))
    convert ((hasDerivAt_const (0 : ℝ) (N K q)).sub h1).sub h2 using 1
    ring
  have := (hnum.div hden hN0).const_add (inner ℝ b c)
  refine this.deriv.trans ?_
  simp only [mul_zero, zero_mul, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  have hN := (N_pos hK q).ne'
  field_simp
  ring

end Calculus

section Curvature

variable [hK : Fact (K < 0)]

omit hK in
lemma mem_target (x : hypPlane K) (q : R2) : q ∈ (extChartAt 𝓘(ℝ, R2) x).target := by
  have h := (extChartAt 𝓘(ℝ, R2) x).map_source
    (x := pt K q) (by rw [extChartAt_source, chartAt_source]; trivial)
  exact h

/-- In the chart of the hyperbolic plane, the metric is `gH K`. -/
lemma metricCoord_eq (x : hypPlane K) (q : R2) : metricCoord 𝓘(ℝ, R2) x q = gH K q := by
  refine ContinuousLinearMap.ext fun a ↦ ContinuousLinearMap.ext fun b ↦ ?_
  rw [metricCoord_apply, coordField, coordField, trivSection, trivSection, symmL_eq,
    extChartAt_symm_apply]
  rfl

lemma metricCoord_fun_eq (x : hypPlane K) : metricCoord 𝓘(ℝ, R2) x = gH K :=
  funext (metricCoord_eq x)

/-- `g_q(q, c) = ⟨q, c⟩ / N(q)`. -/
lemma gH_self_left (q c : R2) : gH K q q c = inner ℝ q c / N K q := by
  have hN := (N_pos hK.out.le q).ne'
  rw [gH_apply, real_inner_self_eq_norm_sq]
  field_simp
  unfold N
  ring

/-- **The Christoffel symbols of the hyperbolic plane**: `Γ(q)(a, b) = K g_q(a, b) q`. -/
lemma christoffelL_eq (x : hypPlane K) (q a b : R2) :
    christoffelL 𝓘(ℝ, R2) x q a b = (K * gH K q a b) • q := by
  rw [christoffelL_apply]
  apply (isInvertible_metricCoord x (mem_target x q)).injective
  rw [metricCoord_christoffel x (mem_target x q)]
  refine ContinuousLinearMap.ext fun c ↦ ?_
  rw [christoffelLow_apply, metricCoord_fun_eq, fderiv_gH hK.out.le, fderiv_gH hK.out.le,
    fderiv_gH hK.out.le, map_smul, smul_apply, smul_eq_mul,
    gH_self_left, gH_apply]
  have hN := (N_pos hK.out.le q).ne'
  simp only [real_inner_comm a b, real_inner_comm a c, real_inner_comm b c]
  field_simp
  ring

lemma christoffelL_fun_eq (x : hypPlane K) (b c : R2) :
    (fun q ↦ christoffelL 𝓘(ℝ, R2) x q b c) = fun q ↦ (K * gH K q b c) • q :=
  funext fun q ↦ christoffelL_eq x q b c

/-- The derivative of the Christoffel symbols. -/
lemma christoffelDeriv_eq (x : hypPlane K) (p a b c : R2) :
    christoffelDeriv 𝓘(ℝ, R2) x p a b c =
      (K * fderiv ℝ (gH K) p a b c) • p + (K * gH K p b c) • a := by
  have hg : HasFDerivAt (fun q ↦ K * gH K q b c) (K • fderiv ℝ (fun q ↦ gH K q b c) p) p :=
    ((((differentiableAt_gH hK.out.le p).clm_apply (differentiableAt_const b)).clm_apply
      (differentiableAt_const c)).hasFDerivAt).const_mul K
  have h : HasFDerivAt (fun q ↦ (K * gH K q b c) • q) ((K * gH K p b c) •
      ContinuousLinearMap.id ℝ R2 + (K • fderiv ℝ (fun q ↦ gH K q b c) p).smulRight p) p :=
    hg.smul (hasFDerivAt_id p)
  rw [christoffelDeriv, christoffelL_fun_eq, h.fderiv, ← fderiv_apply_apply
    (differentiableAt_gH hK.out.le p) a b c]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  abel

/-- **The curvature tensor of the hyperbolic plane in coordinates**:
`R(a, b) c = K (g(b, c) a − g(a, c) b)`. -/
lemma curvCoord_eq (x : hypPlane K) (p a b c : R2) :
    curvCoord 𝓘(ℝ, R2) x p a b c = (K * gH K p b c) • a - (K * gH K p a c) • b := by
  have hN := (N_pos hK.out.le p).ne'
  have hcoef : K * fderiv ℝ (gH K) p a b c - K * fderiv ℝ (gH K) p b a c +
      K * gH K p a ((K * gH K p b c) • p) - K * gH K p b ((K * gH K p a c) • p) = 0 := by
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, gH_symm p a p, gH_symm p b p,
      gH_self_left, gH_self_left, fderiv_gH hK.out.le, fderiv_gH hK.out.le, gH_apply, gH_apply]
    simp only [real_inner_comm a b]
    field_simp
    ring
  rw [curvCoord, christoffelDeriv_eq, christoffelDeriv_eq, christoffelL_eq, christoffelL_eq,
    christoffelL_eq, christoffelL_eq]
  calc (K * fderiv ℝ (gH K) p a b c) • p + (K * gH K p b c) • a -
        ((K * fderiv ℝ (gH K) p b a c) • p + (K * gH K p a c) • b) +
        (K * gH K p a ((K * gH K p b c) • p)) • p - (K * gH K p b ((K * gH K p a c) • p)) • p
      = (K * fderiv ℝ (gH K) p a b c - K * fderiv ℝ (gH K) p b a c +
          K * gH K p a ((K * gH K p b c) • p) - K * gH K p b ((K * gH K p a c) • p)) • p +
        ((K * gH K p b c) • a - (K * gH K p a c) • b) := by module
    _ = _ := by rw [hcoef, zero_smul, zero_add]

/-- **The curvature tensor of the hyperbolic plane**: `R(u, v) w = K (⟨v, w⟩ u − ⟨u, w⟩ v)`. -/
theorem riemannCurvature_eq (x : hypPlane K) (u v w : TangentSpace 𝓘(ℝ, R2) x) :
    riemannCurvature 𝓘(ℝ, R2) x u v w = (K * inner ℝ v w) • u - (K * inner ℝ u w) • v := by
  rw [riemannCurvature, continuousLinearMapAt_eq, symmL_eq]
  exact curvCoord_eq x _ u v w

/-- **The hyperbolic plane `hypPlane K` has constant curvature `K`.** -/
theorem hasConstSectionalCurvature : HasConstSectionalCurvature 𝓘(ℝ, R2) (hypPlane K) K := by
  intro x u v
  rw [riemannCurvature_eq, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm u v]
  ring

end Curvature

section GeodesicDefs

/-- `κ = K g_p(v, v)` (so `-κ` is the square of the speed `√(-K) ‖v‖`). -/
def kap (K : ℝ) (p v : R2) : ℝ := K * gH K p v v

/-- **The geodesics of the hyperbolic plane**, in coordinates: `c(t) = C_κ(t) p + S_κ(t) v`, with
`κ = K g_p(v, v)`. -/
def geo (K : ℝ) (p v : R2) (t : ℝ) : R2 := C (kap K p v) t • p + S (kap K p v) t • v

/-- The derivative `c'(t) = −κ S_κ(t) p + C_κ(t) v` of the geodesic. -/
def geo' (K : ℝ) (p v : R2) (t : ℝ) : R2 :=
  (-kap K p v * S (kap K p v) t) • p + C (kap K p v) t • v

/-- The geodesic from the point with coordinates `p` with initial velocity `v`, as a curve in the
hyperbolic plane. -/
def geoCurve (K : ℝ) (p v : R2) (t : ℝ) : hypPlane K := pt K (geo K p v t)

/-- The Lorentz pairing of the points with coordinates `p` and `y` in the hyperboloid model:
`F_p(y) = √N(p) √N(y) + K ⟨p, y⟩` (it is `cosh (√(-K) d(p, y))`). -/
def F (K : ℝ) (p y : R2) : ℝ := √(N K p) * √(N K y) + K * inner ℝ p y

lemma hasDerivAt_geo (p v : R2) (t : ℝ) : HasDerivAt (geo K p v) (geo' K p v t) t :=
  ((hasDerivAt_C _ t).smul_const p).add ((hasDerivAt_S _ t).smul_const v)

lemma hasDerivAt_geo' (p v : R2) (t : ℝ) :
    HasDerivAt (geo' K p v) (-kap K p v • geo K p v t) t := by
  have h : HasDerivAt (geo' K p v) ((-kap K p v * C (kap K p v) t) • p +
      (-kap K p v * S (kap K p v) t) • v) t :=
    (((hasDerivAt_S (kap K p v) t).const_mul (-kap K p v)).smul_const p).add
      ((hasDerivAt_C (kap K p v) t).smul_const v)
  convert h using 1
  simp only [geo]
  module

lemma deriv_geo (p v : R2) : deriv (geo K p v) = geo' K p v :=
  funext fun t ↦ (hasDerivAt_geo p v t).deriv

lemma geo_zero (p v : R2) : geo K p v 0 = p := by simp [geo]

lemma geo'_zero (p v : R2) : geo' K p v 0 = v := by simp [geo']

lemma contDiff_geo (p v : R2) : ContDiff ℝ ∞ (geo K p v) :=
  ((contDiff_C _).smul contDiff_const).add ((contDiff_S _).smul contDiff_const)

lemma gH_smul (q u : R2) (a : ℝ) : gH K q (a • u) (a • u) = a ^ 2 * gH K q u u := by
  rw [map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]; ring

lemma contMDiffAt_geoCurve (p v : R2) (t : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) ∞ (geoCurve K p v) t := by
  rw [← ContMDiffAt.subtypeVal_comp_iff (hypPlane K) (geoCurve K p v) t]
  exact (contDiff_geo p v).contMDiff.contMDiffAt

lemma mdifferentiableAt_geoCurve (p v : R2) (t : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) (geoCurve K p v) t :=
  (contMDiffAt_geoCurve p v t).mdifferentiableAt (by simp)

lemma chart_comp_geoCurve (x₀ : hypPlane K) (p v : R2) :
    extChartAt 𝓘(ℝ, R2) x₀ ∘ geoCurve K p v = geo K p v := rfl

/-- The velocity of `geoCurve K p v` is `geo' K p v`. -/
lemma velocity_geoCurve (p v : R2) (t : ℝ) :
    (velocity 𝓘(ℝ, R2) (geoCurve K p v) t : R2) = geo' K p v t := by
  have h := trivializationAt_velocity (geoCurve K p v t) (mdifferentiableAt_geoCurve p v t)
    (mem_chart_source R2 _)
  rw [continuousLinearMapAt_eq, chart_comp_geoCurve, deriv_geo] at h
  exact h

end GeodesicDefs

section Geodesics

variable [hK : Fact (K < 0)]

lemma kap_nonpos (p v : R2) : kap K p v ≤ 0 := by
  have h1 := gH_coercive hK.out.le p v
  have h2 : 0 ≤ ‖v‖ ^ 2 / N K p := div_nonneg (sq_nonneg _) (N_pos hK.out.le p).le
  have h3 := hK.out
  unfold kap
  nlinarith

/-- **The geodesics have constant speed**: `g_{c(t)}(c'(t), c'(t)) = g_p(v, v)`. -/
lemma gH_geo' (p v : R2) (t : ℝ) :
    gH K (geo K p v t) (geo' K p v t) (geo' K p v t) = gH K p v v := by
  have hn := (N_pos hK.out.le p).ne'
  have hNc := (N_pos hK.out.le (geo K p v t)).ne'
  have hG : gH K p v v * N K p = ‖v‖ ^ 2 * N K p + K * inner ℝ p v ^ 2 := by
    rw [gH_apply, real_inner_self_eq_norm_sq, add_mul, div_mul_cancel₀ _ hn]; ring
  have hCS := C_sq_add_mul_S_sq (kap K p v) t
  rw [gH_apply, add_div' _ _ _ hNc, div_eq_iff hNc]
  simp only [geo, geo', N, kap, inner_comb, norm_comb_sq] at hG hCS ⊢
  set G := gH K p v v
  set Cs := C (K * G) t
  set Ss := S (K * G) t
  set P := ‖p‖ ^ 2
  set Q := inner ℝ p v
  set V := ‖v‖ ^ 2
  linear_combination (Cs ^ 2 * K * Ss ^ 2 * V - Cs ^ 2 + G * K ^ 2 * Ss ^ 4 * V - G * K * Ss ^ 2 -
      K * Ss ^ 2 * V) * hG + (-Cs ^ 2 * K * P * V + Cs ^ 2 * K * Q ^ 2 + G * K ^ 2 * Q ^ 2 * Ss ^ 2 -
      G * K * Ss ^ 2 * V + G - K ^ 2 * P * Ss ^ 2 * V ^ 2 + K ^ 2 * Q ^ 2 * Ss ^ 2 * V +
      K * Ss ^ 2 * V ^ 2) * hCS

/-- **The curves `geoCurve K p v` are geodesics** of the hyperbolic plane, defined for all times. -/
theorem isGeodesicOn_geoCurve (p v : R2) : IsGeodesicOn 𝓘(ℝ, R2) (geoCurve K p v) univ := by
  intro t _
  have hev : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) (geoCurve K p v) s ∧
      geoCurve K p v s ∈ (chartAt R2 (pt K p)).source :=
    Eventually.of_forall fun s ↦ ⟨mdifferentiableAt_geoCurve p v s, by simp [chartAt_source]⟩
  refine (geodesicAt_iff_chart (pt K p) hev).2 ?_
  rw [chart_comp_geoCurve, deriv_geo]
  show HasDerivAt (geo' K p v)
    (-christoffelL 𝓘(ℝ, R2) (pt K p) (geo K p v t) (geo' K p v t) (geo' K p v t)) t
  rw [christoffelL_eq, gH_geo', ← neg_smul]
  exact hasDerivAt_geo' p v t

theorem isGeodesicFrom_geoCurve (x : hypPlane K) (v : R2) :
    IsGeodesicFrom 𝓘(ℝ, R2) x v (geoCurve K x v) univ where
  isOpen := isOpen_univ
  isPreconnected := isPreconnected_univ
  zero_mem := mem_univ 0
  isGeodesicOn := isGeodesicOn_geoCurve x v
  apply_zero := Subtype.ext (geo_zero (x : R2) v)
  velocity_zero := by rw [velocity_geoCurve, geo'_zero]

/-- **The exponential map of the hyperbolic plane**: `exp_x v = c(1)`, for every `v`. -/
theorem expMap_eq (x : hypPlane K) (v : R2) :
    v ∈ expDomain 𝓘(ℝ, R2) x ∧ expMap 𝓘(ℝ, R2) x v = pt K (geo K x v 1) :=
  PythagoreanPaper.expMap_eq (isGeodesicFrom_geoCurve x v) (subset_univ _)

omit hK in
/-- The algebra behind `F_geo`. -/
lemma F_geo_aux {P Q V G Cs Ss r0 y0 : ℝ} (hKn : K < 0) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hQ : Q ^ 2 ≤ P * V) (hG : G * (1 - K * P) = V * (1 - K * P) + K * Q ^ 2)
    (hCS : Cs ^ 2 + K * G * Ss ^ 2 = 1) (hC : 0 < Cs) (hr0 : r0 ^ 2 = 1 - K * P)
    (hy0 : y0 ^ 2 = 1 - K * (Cs ^ 2 * P + 2 * Cs * Ss * Q + Ss ^ 2 * V)) (hr0nn : 0 ≤ r0)
    (hy0nn : 0 ≤ y0) :
    r0 * y0 + K * (Cs * P + Ss * Q) = Cs := by
  set n := 1 - K * P with hn_def
  have hn : 1 ≤ n := by nlinarith
  have hkey : (Cs * n - K * Q * Ss) ^ 2 =
      n * (1 - K * (Cs ^ 2 * P + 2 * Cs * Ss * Q + Ss ^ 2 * V)) := by
    linear_combination n * hCS + (-K * Ss ^ 2) * hG
  -- `C n − K Q S > 0`
  have h1 : (Cs * n) ^ 2 = n ^ 2 - K * G * Ss ^ 2 * n ^ 2 := by linear_combination n ^ 2 * hCS
  have h2 : -K * G * n ^ 2 - K ^ 2 * Q ^ 2 = -K * (V * n ^ 2 + K * Q ^ 2 * (n + 1)) := by
    linear_combination (-K * n) * hG
  have h3 : V ≤ V * n ^ 2 + K * Q ^ 2 * (n + 1) := by
    have hKn1 : K * (n + 1) ≤ 0 := by nlinarith
    have := mul_le_mul_of_nonpos_left hQ hKn1
    nlinarith
  have h4 : (K * Q * Ss) ^ 2 < (Cs * n) ^ 2 := by
    have h5 : 0 ≤ -K * (V * n ^ 2 + K * Q ^ 2 * (n + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg Ss, mul_nonneg (sq_nonneg Ss) h5]
  have hpos : 0 < Cs * n - K * Q * Ss := by
    have := abs_lt_of_sq_lt_sq h4 (by positivity)
    linarith [le_abs_self (K * Q * Ss)]
  have hry : r0 * y0 = Cs * n - K * Q * Ss := by
    refine (sq_eq_sq₀ (mul_nonneg hr0nn hy0nn) hpos.le).1 ?_
    rw [mul_pow, hr0, hy0, hkey]
  rw [hry]
  ring

/-- Along a geodesic from `p`, `F_p(c(t)) = C_κ(t)` (in the hyperboloid model: `cosh` of the
distance travelled, times `√(-K)`). -/
lemma F_geo (p v : R2) (t : ℝ) : F K p (geo K p v t) = C (kap K p v) t := by
  have hn := N_pos hK.out.le p
  have hNc := N_pos hK.out.le (geo K p v t)
  have hG : gH K p v v * N K p = ‖v‖ ^ 2 * N K p + K * inner ℝ p v ^ 2 := by
    rw [gH_apply, real_inner_self_eq_norm_sq, add_mul, div_mul_cancel₀ _ hn.ne']; ring
  have hQ : inner ℝ p v ^ 2 ≤ ‖p‖ ^ 2 * ‖v‖ ^ 2 := by
    have := real_inner_mul_inner_self_le p v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    nlinarith
  have hy0 : √(N K (geo K p v t)) ^ 2 = N K (geo K p v t) := Real.sq_sqrt hNc.le
  have hr0 : √(N K p) ^ 2 = N K p := Real.sq_sqrt hn.le
  have hCS := C_sq_add_mul_S_sq (kap K p v) t
  have hC := C_pos_of_nonpos (kap_nonpos (K := K) p v) t
  have hsq := Real.sqrt_nonneg (N K (geo K p v t))
  unfold F
  unfold N at hG hy0 hr0 hsq ⊢
  unfold geo at hy0 hsq ⊢
  rw [inner_left_comb]
  rw [norm_comb_sq] at hy0 hsq ⊢
  exact F_geo_aux hK.out (sq_nonneg _) (sq_nonneg _) hQ hG hCS hC hr0 hy0 (Real.sqrt_nonneg _) hsq

/-- **The exponential map of the hyperbolic plane is injective** (on the whole tangent plane). -/
theorem expMap_injective (x : hypPlane K) : Injective (expMap 𝓘(ℝ, R2) x) := by
  intro v w h
  rw [(expMap_eq x v).2, (expMap_eq x w).2] at h
  have hgeo : geo K x v 1 = geo K x w 1 := congrArg Subtype.val h
  have hκ : kap K x v = kap K x w :=
    C_one_injOn (kap_nonpos (x : R2) v) (kap_nonpos (x : R2) w) (by
      show C (kap K x v) 1 = C (kap K x w) 1
      rw [← F_geo, ← F_geo, hgeo])
  have hS : S (kap K x w) 1 ≠ 0 := (S_pos_of_nonpos (kap_nonpos (x : R2) w) one_pos).ne'
  simp only [geo, hκ] at hgeo
  exact smul_right_injective R2 hS (add_left_cancel hgeo)

/-- **Every ball of `T_x` is a normal ball** of the hyperbolic plane. -/
theorem isNormalBall (x : hypPlane K) {ρ : ℝ} (hρ : 0 < ρ) : IsNormalBall 𝓘(ℝ, R2) x ρ :=
  isNormalBall_of_constCurvature finrank_euclideanSpace_fin hasConstSectionalCurvature hρ
    (fun h ↦ absurd h (not_lt.2 hK.out.le)) (fun v _ ↦ (expMap_eq x v).1)
    (expMap_injective x).injOn

/-- The reverse Cauchy–Schwarz inequality of the hyperboloid model: `F_p(y) ≥ 1`. -/
lemma one_le_F (p y : R2) : 1 ≤ F K p y := by
  have hK' := hK.out
  have hn := one_le_N hK'.le p
  have hny := one_le_N hK'.le y
  have h1 : 1 - K * (‖p‖ * ‖y‖) ≤ √(N K p) * √(N K y) := by
    rw [← Real.sqrt_mul (by linarith)]
    have h0 : 0 < 1 - K * (‖p‖ * ‖y‖) := by
      have := mul_nonneg (norm_nonneg p) (norm_nonneg y)
      nlinarith
    rw [Real.le_sqrt' h0]
    unfold N
    nlinarith [mul_nonneg (neg_nonneg.2 hK'.le) (sq_nonneg (‖p‖ - ‖y‖))]
  have h2 : K * (‖p‖ * ‖y‖) ≤ K * inner ℝ p y :=
    mul_le_mul_of_nonpos_left (real_inner_le_norm p y) hK'.le
  unfold F
  linarith

/-- `K g_p(u, u) = 1 − F_p(y)²` for `u = y − F_p(y) p`. -/
lemma K_mul_gH_sub (p y : R2) :
    K * gH K p (y - F K p y • p) (y - F K p y • p) = 1 - F K p y ^ 2 := by
  have hn := N_pos hK.out.le p
  have hny := N_pos hK.out.le y
  have hr0 : √(N K p) ^ 2 = N K p := Real.sq_sqrt hn.le
  have hy0 : √(N K y) ^ 2 = N K y := Real.sq_sqrt hny.le
  have hsub : ∀ c : ℝ, ‖y - c • p‖ ^ 2 = ‖y‖ ^ 2 - 2 * c * inner ℝ p y + c ^ 2 * ‖p‖ ^ 2 := by
    intro c
    rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right,
      real_inner_comm p y]
    ring
  have hsub' : ∀ c : ℝ, inner ℝ p (y - c • p) = inner ℝ p y - c * ‖p‖ ^ 2 := by
    intro c
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [gH_apply, real_inner_self_eq_norm_sq, show ∀ A B : ℝ, K * (A + K * B * B / N K p) =
    K * (A * N K p + K * B ^ 2) / N K p from fun A B ↦ by field_simp, div_eq_iff hn.ne',
    hsub, hsub']
  unfold F N at *
  linear_combination √(1 - K * ‖y‖ ^ 2) ^ 2 * hr0 + (1 - K * ‖p‖ ^ 2) * hy0

lemma norm_tangent_eq (x : hypPlane K) (v : R2) :
    ‖(show TangentSpace 𝓘(ℝ, R2) x from v)‖ = √(gH K x v v) := by
  rw [norm_eq_sqrt_real_inner]; rfl

/-- **The exponential map of the hyperbolic plane is onto**, with a bound on the length of the
preimage: `‖v‖ ≤ F_x(y) / √(-K)`. -/
theorem exists_expMap_eq (x y : hypPlane K) :
    ∃ v : R2, ‖(show TangentSpace 𝓘(ℝ, R2) x from v)‖ ≤ F K x y / √(-K) ∧
      expMap 𝓘(ℝ, R2) x v = y := by
  have hK' := hK.out
  obtain ⟨s, hs0, hsc, hcosh⟩ := exists_cosh_eq (one_le_F (K := K) (x : R2) (y : R2))
  have hκ : -s ^ 2 ≤ 0 := neg_nonpos.2 (sq_nonneg s)
  have hC : C (-s ^ 2) 1 = F K x y := by
    rw [C_one_of_nonpos hκ, neg_neg, Real.sqrt_sq hs0, hcosh]
  have hSpos : 0 < S (-s ^ 2) 1 := S_pos_of_nonpos hκ one_pos
  have hCS := C_sq_add_mul_S_sq (-s ^ 2) 1
  have hgu := K_mul_gH_sub (K := K) (x : R2) (y : R2)
  set u : R2 := (y : R2) - F K x y • (x : R2) with hu
  set v : R2 := (S (-s ^ 2) 1)⁻¹ • u with hv
  have hkap : kap K x v = -s ^ 2 := by
    have h1 : K * gH K x u u = 1 - C (-s ^ 2) 1 ^ 2 := by rw [hC]; exact hgu
    unfold kap
    rw [hv, gH_smul, show K * ((S (-s ^ 2) 1)⁻¹ ^ 2 * gH K x u u) =
      (S (-s ^ 2) 1)⁻¹ ^ 2 * (K * gH K x u u) by ring, h1]
    field_simp
    linear_combination -hCS
  refine ⟨v, ?_, ?_⟩
  · rw [norm_tangent_eq]
    have hg : gH K x v v = s ^ 2 / (-K) := by
      have : K * gH K x v v = -s ^ 2 := hkap
      rw [eq_div_iff (by linarith : -K ≠ 0)]
      linear_combination -this
    rw [hg, Real.sqrt_div (sq_nonneg s), Real.sqrt_sq hs0]
    exact div_le_div_of_nonneg_right hsc (Real.sqrt_nonneg _)
  · rw [(expMap_eq x v).2]
    apply Subtype.ext
    show geo K x v 1 = y
    rw [geo, hkap, hC, hv, smul_smul, mul_inv_cancel₀ hSpos.ne', one_smul, hu]
    abel

omit hK in
lemma continuous_F (p : R2) : Continuous (F K p) := by
  unfold F
  exact (continuous_const.mul (Real.continuous_sqrt.comp (contDiff_N K).continuous)).add
    (continuous_const.mul (continuous_const.inner continuous_id))

/-- `F_X` is bounded on a geodesic segment. -/
lemma exists_bound_segment {γ : ℝ → hypPlane K} {x y : hypPlane K} {L : ℝ}
    (h : IsGeodesicSegment 𝓘(ℝ, R2) γ x y L) (X : hypPlane K) :
    ∃ B, ∀ t ∈ Icc 0 L, F K X (γ t) ≤ B := by
  have hγ : ContinuousOn γ (Icc 0 L) := fun t ht ↦
    (h.mdifferentiableAt ht).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t ↦ F K X (γ t)) (Icc 0 L) :=
    (continuous_F (X : R2)).comp_continuousOn (continuous_subtype_val.comp_continuousOn hγ)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨B, fun t ht ↦ hB ⟨t, ht, rfl⟩⟩

lemma mem_expMap_image (X y : hypPlane K) {ρ : ℝ} (hρ : F K X y / √(-K) < ρ) :
    y ∈ expMap 𝓘(ℝ, R2) X '' tangentBall 𝓘(ℝ, R2) X ρ := by
  obtain ⟨v, hv, hvy⟩ := exists_expMap_eq X y
  exact ⟨v, lt_of_le_of_lt hv hρ, hvy⟩

variable (T : GeodesicTriangle 𝓘(ℝ, R2) (hypPlane K))

/-- Some normal ball around `X` contains the three sides of any geodesic triangle of the hyperbolic
plane. -/
theorem sidesInNormalBallAt (X : hypPlane K) : T.SidesInNormalBallAt X := by
  obtain ⟨Ba, hBa⟩ := exists_bound_segment T.segment_a X
  obtain ⟨Bb, hBb⟩ := exists_bound_segment T.segment_b X
  obtain ⟨Bc, hBc⟩ := exists_bound_segment T.segment_c X
  set ρ := (|Ba| + |Bb| + |Bc|) / √(-K) + 1 with hρ_def
  have hsq : 0 ≤ √(-K) := Real.sqrt_nonneg _
  have hρ : 0 < ρ := by positivity
  have key : ∀ B : ℝ, |B| ≤ |Ba| + |Bb| + |Bc| → ∀ y : hypPlane K, F K X y ≤ B →
      y ∈ expMap 𝓘(ℝ, R2) X '' tangentBall 𝓘(ℝ, R2) X ρ := fun B hB y hy ↦
    mem_expMap_image X y (lt_of_le_of_lt (div_le_div_of_nonneg_right
      (hy.trans ((le_abs_self B).trans hB)) hsq) (lt_add_one _))
  have ha : |Ba| ≤ |Ba| + |Bb| + |Bc| := by linarith [abs_nonneg Bb, abs_nonneg Bc]
  have hb : |Bb| ≤ |Ba| + |Bb| + |Bc| := by linarith [abs_nonneg Ba, abs_nonneg Bc]
  have hc : |Bc| ≤ |Ba| + |Bb| + |Bc| := by linarith [abs_nonneg Ba, abs_nonneg Bb]
  exact ⟨ρ, isNormalBall X hρ, fun t ht ↦ key Ba ha _ (hBa t ht),
    fun t ht ↦ key Bb hb _ (hBb t ht), fun t ht ↦ key Bc hc _ (hBc t ht)⟩

/-- **Every geodesic triangle of the hyperbolic plane satisfies the technical condition.** -/
theorem sidesInNormalBalls : T.SidesInNormalBalls :=
  ⟨sidesInNormalBallAt T T.pA, sidesInNormalBallAt T T.pB, sidesInNormalBallAt T T.pC⟩

end Geodesics

end HypPlane

end PythagoreanPaper
