import PythagoreanPaper.Riemannian.GeodesicFlow

/-!
# The exponential map

For `p ∈ M` and a tangent vector `v ∈ T_pM` (identified with `E`), `expMap I p v = γ_v(1)`, where
`γ_v` is the geodesic with `γ_v(0) = p` and `γ̇_v(0) = v`, whenever `γ_v` is defined on an open
interval of times containing `[0, 1]`; these `v` form `expDomain I p`. The manifold is assumed
Hausdorff, so that geodesics are determined by their initial position and velocity.

* `expMap_eq`: `exp_p v = γ(1)` for every such geodesic `γ`.
* `expMap_smul`: `exp_p (t • v) = γ_v(t)` (geodesics are reparametrized linearly,
  `IsGeodesicOn.comp_mul`).
* `isOpen_expDomain`, `contMDiffOn_expMap`: the domain of `exp_p` is open and `exp_p` is `C^∞`
  on it.

The smoothness is proved by continuation along `[0, 1]`: for `v` near `v₀`, the position and
velocity of `γ_v` at time `t`, read in a chart around `γ_{v₀}(t)`, depend smoothly on `v`; this
property passes from a time to all nearby times (`exists_chartData_flow`, smooth dependence of
solutions of ODEs on initial values, and the change of chart), hence holds on all of `[0, 1]`.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

section Def

variable (I) in
/-- `γ` is a geodesic on the open preconnected set of times `U ∋ 0`, with `γ 0 = p` and
`γ̇ 0 = v`. -/
structure IsGeodesicFrom (p : M) (v : E) (γ : ℝ → M) (U : Set ℝ) : Prop where
  isOpen : IsOpen U
  isPreconnected : IsPreconnected U
  zero_mem : (0 : ℝ) ∈ U
  isGeodesicOn : IsGeodesicOn I γ U
  apply_zero : γ 0 = p
  velocity_zero : (velocity I γ 0 : E) = v

variable (I) in
/-- The domain of the exponential map at `p`: the tangent vectors `v` at `p` such that the
geodesic with initial position `p` and initial velocity `v` is defined on an open interval of
times containing `[0, 1]`. -/
def expDomain (p : M) : Set E :=
  {v | ∃ (γ : ℝ → M) (U : Set ℝ), IsGeodesicFrom I p v γ U ∧ Icc 0 1 ⊆ U}

variable (I) in
open Classical in
/-- **The exponential map** at `p`: `exp_p v = γ_v(1)`. (Outside `expDomain I p` the value `p` is
a placeholder; every statement about `expMap` below is restricted to `expDomain I p`.) -/
def expMap (p : M) (v : E) : M :=
  if h : v ∈ expDomain I p then h.choose 1 else p

variable [T2Space M]

/-- `exp_p v = γ(1)` for every geodesic `γ` from `p` with initial velocity `v` defined on an open
interval containing `[0, 1]`. -/
theorem expMap_eq {p : M} {v : E} {γ : ℝ → M} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (h1 : Icc 0 1 ⊆ U) : v ∈ expDomain I p ∧ expMap I p v = γ 1 := by
  have hv : v ∈ expDomain I p := ⟨γ, U, hγ, h1⟩
  refine ⟨hv, ?_⟩
  rw [expMap, dite_eq_left_of_eq_true (eq_true hv)]
  obtain ⟨U', hγ', h1'⟩ := hv.choose_spec
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  exact (IsGeodesicOn.eqOn (hγ'.isOpen.inter hγ.isOpen)
    (isPreconnected_inter_real hγ'.isPreconnected hγ.isPreconnected)
    (hγ'.isGeodesicOn.mono inter_subset_left) (hγ.isGeodesicOn.mono inter_subset_right)
    ⟨hγ'.zero_mem, hγ.zero_mem⟩ (hγ'.apply_zero.trans hγ.apply_zero.symm)
    (hγ'.velocity_zero.trans hγ.velocity_zero.symm) 1 ⟨h1' h1mem, h1 h1mem⟩).1

end Def

section Scaling

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The velocity of a linearly reparametrized curve. -/
lemma velocity_comp_mul {γ : ℝ → M} {a t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (a * t)) :
    (velocity I (fun s ↦ γ (a * s)) t : E) = a • (velocity I γ (a * t) : E) := by
  set x₀ := γ (a * t)
  have hsrc : γ (a * t) ∈ (chartAt H x₀).source := mem_chart_source H _
  have hb := mem_baseSet_of_mem_chart_source (I := I) hsrc
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ a * s) t :=
    (differentiableAt_id.const_mul a).mdifferentiableAt
  have hγa : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ γ (a * s)) t := hγ.comp t hm
  have e₁ := trivializationAt_velocity x₀ hγa hsrc
  have e₂ := trivializationAt_velocity x₀ hγ hsrc
  have hd : HasDerivAt (extChartAt I x₀ ∘ γ) (deriv (extChartAt I x₀ ∘ γ) (a * t)) (a * t) :=
    (mdifferentiableAt_iff_differentiableAt.1
      ((mdifferentiableAt_extChartAt hsrc).comp _ hγ)).hasDerivAt
  have hd' : deriv (extChartAt I x₀ ∘ fun s ↦ γ (a * s)) t =
      a • deriv (extChartAt I x₀ ∘ γ) (a * t) := by
    have := hd.scomp t ((hasDerivAt_id t).const_mul a)
    simp only [mul_one] at this
    exact this.deriv
  have key : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ (a * t))
      (velocity I (fun s ↦ γ (a * s)) t) =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ (a * t))
        (a • velocity I γ (a * t)) := by
    rw [map_smul, e₂, ← hd']
    exact e₁
  have := congrArg ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ (a * t))) key
  rwa [Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb,
    Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb] at this

/-- **Linear reparametrization of geodesics**: if `γ` is a geodesic, so is `t ↦ γ(a t)`. -/
theorem IsGeodesicOn.comp_mul {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn I γ U)
    (a : ℝ) : IsGeodesicOn I (fun t ↦ γ (a * t)) ((fun t ↦ a * t) ⁻¹' U) := by
  intro t ht
  set x₀ := γ (a * t)
  have hsrc : γ (a * t) ∈ (chartAt H x₀).source := mem_chart_source H _
  have hev := hγ.hasDerivAt_chart hU x₀ ht hsrc
  have htend : Tendsto (fun s : ℝ ↦ a * s) (𝓝 t) (𝓝 (a * t)) :=
    (continuous_const.mul continuous_id).continuousAt
  have hevU : ∀ᶠ s in 𝓝 t, a * s ∈ U := htend.eventually (hU.mem_nhds ht)
  have hev' := htend.eventually hev
  have hevγa : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ γ (a * s)) s ∧
      (fun s ↦ γ (a * s)) s ∈ (chartAt H x₀).source := by
    filter_upwards [hevU, hev'] with s hs hs'
    exact ⟨(hγ.mdifferentiableAt hs).comp s (differentiableAt_id.const_mul a).mdifferentiableAt,
      hs'.2⟩
  rw [geodesicAt_iff_chart x₀ hevγa]
  set c := extChartAt I x₀ ∘ γ with hc_def
  have hderiv_eq : deriv (extChartAt I x₀ ∘ fun s ↦ γ (a * s)) =ᶠ[𝓝 t]
      fun s ↦ a • deriv c (a * s) := by
    filter_upwards [hev'] with s hs
    have hc : HasDerivAt c (deriv c (a * s)) (a * s) :=
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt _ hs.1
    have := hc.scomp s ((hasDerivAt_id s).const_mul a)
    simp only [mul_one] at this
    exact this.deriv
  have hd2 : HasDerivAt (deriv c)
      (-christoffelL I x₀ (c (a * t)) (deriv c (a * t)) (deriv c (a * t))) (a * t) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt _ hev.self_of_nhds.1
  have hd2' : HasDerivAt (fun s ↦ a • deriv c (a * s))
      (a • (a • -christoffelL I x₀ (c (a * t)) (deriv c (a * t)) (deriv c (a * t)))) t := by
    have := hd2.scomp t ((hasDerivAt_id t).const_mul a)
    simp only [mul_one] at this
    exact this.const_smul a
  rw [hderiv_eq.eq_of_nhds]
  refine (hd2'.congr_of_eventuallyEq hderiv_eq).congr_deriv ?_
  show _ = -christoffelL I x₀ (c (a * t)) (a • deriv c (a * t)) (a • deriv c (a * t))
  simp only [map_smul, smul_apply, smul_neg]

/-- A linear reparametrization of a geodesic from `p` with initial velocity `v` is a geodesic
from `p` with initial velocity `a • v`. -/
theorem IsGeodesicFrom.smul {p : M} {v : E} {γ : ℝ → M} {U : Set ℝ}
    (h : IsGeodesicFrom I p v γ U) (a : ℝ) :
    IsGeodesicFrom I p (a • v) (fun t ↦ γ (a * t)) ((fun t ↦ a * t) ⁻¹' U) where
  isOpen := h.isOpen.preimage (continuous_const.mul continuous_id)
  isPreconnected := by
    have hU := isPreconnected_iff_ordConnected.1 h.isPreconnected
    refine isPreconnected_iff_ordConnected.2 ?_
    rcases le_total 0 a with ha | ha
    · exact hU.preimage_mono fun x y hxy ↦ mul_le_mul_of_nonneg_left hxy ha
    · exact hU.preimage_anti fun x y hxy ↦ mul_le_mul_of_nonpos_left hxy ha
  zero_mem := by simpa using h.zero_mem
  isGeodesicOn := h.isGeodesicOn.comp_mul h.isOpen a
  apply_zero := by simpa using h.apply_zero
  velocity_zero := by
    rw [velocity_comp_mul (by simpa using h.isGeodesicOn.mdifferentiableAt h.zero_mem),
      congrArg (fun s ↦ (velocity I γ s : E)) (mul_zero a), h.velocity_zero]
    rfl

variable [T2Space M]

/-- **`exp_p (t • v) = γ_v(t)`**: along a geodesic `γ_v` from `p` with initial velocity `v`, defined
on an open interval containing the times between `0` and `t`. -/
theorem expMap_smul {p : M} {v : E} {γ : ℝ → M} {U : Set ℝ} (h : IsGeodesicFrom I p v γ U)
    {t : ℝ} (ht : uIcc 0 t ⊆ U) : t • v ∈ expDomain I p ∧ expMap I p (t • v) = γ t := by
  have h1 : Icc 0 1 ⊆ (fun r ↦ t * r) ⁻¹' U := by
    intro r hr
    apply ht
    rcases le_total 0 t with h0 | h0
    · rw [uIcc_of_le h0]
      exact ⟨mul_nonneg h0 hr.1, mul_le_of_le_one_right h0 hr.2⟩
    · rw [uIcc_of_ge h0]
      exact ⟨by nlinarith [hr.1, hr.2], mul_nonpos_of_nonpos_of_nonneg h0 hr.1⟩
  obtain ⟨hD, he⟩ := expMap_eq (h.smul t) h1
  exact ⟨hD, by rw [he, mul_one]⟩

end Scaling

section Smooth

variable [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- At its base point, the trivialization of the tangent bundle at `p` is the identity. -/
lemma trivializationAt_self_apply (p : M) (v : E) :
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p v = v := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H p)]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source p)

omit [I.Boundaryless] [T2Space M] in
/-- The chart data at time `0`, in the chart at `p`, of a geodesic from `p` with initial
velocity `v`. -/
lemma IsGeodesicFrom.chartData_zero {p : M} {v : E} {γ : ℝ → M} {U : Set ℝ}
    (h : IsGeodesicFrom I p v γ U) : chartData I p γ 0 = (extChartAt I p p, v) := by
  have hsrc : γ 0 ∈ (chartAt H p).source := by rw [h.apply_zero]; exact mem_chart_source H p
  have e := trivializationAt_velocity p (h.isGeodesicOn.mdifferentiableAt h.zero_mem) hsrc
  refine Prod.ext (by simp [chartData, h.apply_zero]) ?_
  show deriv (extChartAt I p ∘ γ) 0 = _
  rw [← e, ← trivializationAt_self_apply (I := I) p v]
  exact congrArg₂ (fun (b : M) (w : E) ↦
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ b w) h.apply_zero
    h.velocity_zero

variable (I) in
/-- The property propagated along `[0, 1]` in the proof that `exp_p` is smooth near `v₀`: for `v`
near `v₀` the geodesic `γ_v` is defined up to time `t`, and its position and velocity at time `t`,
read in a chart around `γ_{v₀}(t)`, depend smoothly on `v`. -/
def ExpProp (p : M) (v₀ : E) (γ₀ : ℝ → M) (t : ℝ) : Prop :=
  ∃ x₁ : M, γ₀ t ∈ (chartAt H x₁).source ∧ ∃ Ψ : E → E × E, ContDiffAt ℝ ∞ Ψ v₀ ∧
    Ψ v₀ = chartData I x₁ γ₀ t ∧ ∀ᶠ v in 𝓝 v₀, ∃ (γ : ℝ → M) (U : Set ℝ),
      IsGeodesicFrom I p v γ U ∧ Icc 0 t ⊆ U ∧ γ t ∈ (chartAt H x₁).source ∧
      chartData I x₁ γ t = Ψ v

omit [T2Space M] in
lemma ExpProp.zero {p : M} {v₀ : E} {γ₀ : ℝ → M} {U₀ : Set ℝ}
    (h₀ : IsGeodesicFrom I p v₀ γ₀ U₀) : ExpProp I p v₀ γ₀ 0 := by
  refine ⟨p, by rw [h₀.apply_zero]; exact mem_chart_source H p, fun v ↦ (extChartAt I p p, v),
    contDiffAt_const.prodMk contDiffAt_id, h₀.chartData_zero.symm,
    Filter.Eventually.of_forall fun v ↦ ?_⟩
  obtain ⟨ε, hε, γ, hγ0, hγv, -, hγ⟩ := exists_geodesic (I := I) p v
  have hg : IsGeodesicFrom I p v γ (Ioo (-ε) ε) :=
    ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, hε⟩, hγ, hγ0, hγv⟩
  refine ⟨γ, Ioo (-ε) ε, hg, ?_, by rw [hγ0]; exact mem_chart_source H p, hg.chartData_zero⟩
  intro r hr
  have : r = 0 := le_antisymm hr.2 hr.1
  subst this
  exact ⟨by linarith, hε⟩

/-- The continuation step: the property passes between any two nonnegative times in an interval
`(c, d)` on which `γ₀` stays in one chart. -/
lemma ExpProp.step {p : M} {v₀ : E} {γ₀ : ℝ → M} {U₀ : Set ℝ} (h₀ : IsGeodesicFrom I p v₀ γ₀ U₀)
    {x_c : M} {c d : ℝ} (hsub : Icc c d ⊆ U₀)
    (hsrc : ∀ r ∈ Icc c d, γ₀ r ∈ (chartAt H x_c).source) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Ioo c d)
    (hs₂ : s₂ ∈ Ioo c d) (hs₁0 : 0 ≤ s₁) (hP : ExpProp I p v₀ γ₀ s₁) :
    ExpProp I p v₀ γ₀ s₂ := by
  obtain ⟨x₁, hx₁, Ψ₁, hΨ₁, hΨ₁v₀, hev₁⟩ := hP
  have hγ₀s₁c : γ₀ s₁ ∈ (chartAt H x_c).source := hsrc s₁ (Ioo_subset_Icc_self hs₁)
  have hdiff₀ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ₀ s₁ :=
    h₀.isGeodesicOn.mdifferentiableAt (hsub (Ioo_subset_Icc_self hs₁))
  have hsrc₁ : γ₀ s₁ ∈ (extChartAt I x₁).source := by rwa [extChartAt_source]
  have hT : chartData I x_c γ₀ s₁ = chartDataChange I x₁ x_c (chartData I x₁ γ₀ s₁) :=
    chartData_change x₁ x_c hdiff₀ hx₁ hγ₀s₁c
  have hTc : ContDiffAt ℝ ∞ (chartDataChange I x₁ x_c) (Ψ₁ v₀) := by
    rw [hΨ₁v₀]
    refine contDiffAt_chartDataChange x₁ x_c ((extChartAt I x₁).map_source hsrc₁) ?_
    show (extChartAt I x₁).symm (extChartAt I x₁ (γ₀ s₁)) ∈ _
    rw [(extChartAt I x₁).left_inv hsrc₁]
    exact hγ₀s₁c
  obtain ⟨ΨA, hΨA, hΨAγ₀, hevA⟩ :=
    exists_chartData_flow x_c h₀.isOpen h₀.isGeodesicOn hsub hsrc hs₁ hs₂
  set Ψ₂ : E → E × E := ΨA ∘ chartDataChange I x₁ x_c ∘ Ψ₁ with hΨ₂_def
  have hΨ₂ : ContDiffAt ℝ ∞ Ψ₂ v₀ := hΨA.contDiffAt.comp v₀ (hTc.comp v₀ hΨ₁)
  have hΨ₂v₀ : Ψ₂ v₀ = chartData I x_c γ₀ s₂ := by
    simp only [Ψ₂, Function.comp_apply, hΨ₁v₀, ← hT, hΨAγ₀]
  refine ⟨x_c, hsrc s₂ (Ioo_subset_Icc_self hs₂), Ψ₂, hΨ₂, hΨ₂v₀, ?_⟩
  -- near `v₀`, the position at time `s₁` lies in the chart at `x_c`
  have hcont1 : ContinuousAt (fun v ↦ (extChartAt I x₁).symm (Ψ₁ v).1) v₀ := by
    have hmem : (Ψ₁ v₀).1 ∈ (extChartAt I x₁).target := by
      rw [hΨ₁v₀]
      exact (extChartAt I x₁).map_source hsrc₁
    exact ContinuousAt.comp (g := (extChartAt I x₁).symm) (continuousAt_extChartAt_symm'' hmem)
      hΨ₁.continuousAt.fst
  have hev_src : ∀ᶠ v in 𝓝 v₀, (extChartAt I x₁).symm (Ψ₁ v).1 ∈ (chartAt H x_c).source := by
    apply hcont1.preimage_mem_nhds
    show _ ∈ 𝓝 ((extChartAt I x₁).symm (Ψ₁ v₀).1)
    rw [hΨ₁v₀]
    show _ ∈ 𝓝 ((extChartAt I x₁).symm (extChartAt I x₁ (γ₀ s₁)))
    rw [(extChartAt I x₁).left_inv hsrc₁]
    exact (chartAt H x_c).open_source.mem_nhds hγ₀s₁c
  have hTv₀ : (chartDataChange I x₁ x_c ∘ Ψ₁) v₀ = chartData I x_c γ₀ s₁ := by
    simp only [Function.comp_apply, hΨ₁v₀, ← hT]
  rw [← hTv₀] at hevA
  have hev_A := (hTc.continuousAt.comp hΨ₁.continuousAt).tendsto.eventually hevA
  filter_upwards [hev₁, hev_src, hev_A] with v ⟨γ, U, hγ, hU0, hγs₁, hγd⟩ hvsrc
    ⟨γ', hγ', hγ'src, hγ's₁, hγ's₂⟩
  have hpos : γ s₁ = (extChartAt I x₁).symm (Ψ₁ v).1 := by
    rw [← hγd]
    exact ((extChartAt I x₁).left_inv (by rwa [extChartAt_source])).symm
  have hγs₁c : γ s₁ ∈ (chartAt H x_c).source := hpos ▸ hvsrc
  have hs₁U : s₁ ∈ U := hU0 ⟨hs₁0, le_rfl⟩
  have hdiffγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s₁ := hγ.isGeodesicOn.mdifferentiableAt hs₁U
  have hdiffγ' : MDifferentiableAt 𝓘(ℝ, ℝ) I γ' s₁ := hγ'.mdifferentiableAt hs₁
  have hdata : chartData I x_c γ s₁ = chartData I x_c γ' s₁ := by
    rw [chartData_change x₁ x_c hdiffγ hγs₁ hγs₁c, hγd, hγ's₁]
    rfl
  obtain ⟨hp, hv⟩ := (chartData_eq_iff x_c hdiffγ hdiffγ' hγs₁c (hγ'src s₁ hs₁)).1 hdata
  obtain ⟨γ'', hγ'', e₁, e₂⟩ := IsGeodesicOn.glue hγ.isOpen hγ.isPreconnected isOpen_Ioo
    isPreconnected_Ioo hγ.isGeodesicOn hγ' hs₁U hs₁ hp hv
  have hev0 : γ'' =ᶠ[𝓝 0] γ := by
    filter_upwards [hγ.isOpen.mem_nhds hγ.zero_mem] with r hr using e₁ r hr
  have hevs₂ : γ'' =ᶠ[𝓝 s₂] γ' := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₂] with r hr using e₂ r hr
  refine ⟨γ'', U ∪ Ioo c d, ⟨hγ.isOpen.union isOpen_Ioo,
    hγ.isPreconnected.union s₁ hs₁U hs₁ isPreconnected_Ioo, Or.inl hγ.zero_mem, hγ'',
    by rw [e₁ 0 hγ.zero_mem, hγ.apply_zero], by rw [velocity_congr hev0, hγ.velocity_zero]⟩,
    ?_, by rw [e₂ s₂ hs₂]; exact hγ'src s₂ hs₂, by rw [chartData_congr x_c hevs₂, hγ's₂]; rfl⟩
  intro r hr
  by_cases h : r ≤ s₁
  · exact Or.inl (hU0 ⟨hr.1, h⟩)
  · exact Or.inr ⟨hs₁.1.trans (not_le.1 h), hr.2.trans_lt hs₂.2⟩

/-- Near every point `v₀` of `expDomain I p`, the vectors `v` belong to `expDomain I p`, and
`exp_p v`, read in a fixed chart, is a smooth function of `v`. -/
theorem expMap_local {p : M} {v₀ : E} (hv₀ : v₀ ∈ expDomain I p) :
    ∃ x₁ : M, ∃ Ψ : E → E × E, ContDiffAt ℝ ∞ Ψ v₀ ∧ ∀ᶠ v in 𝓝 v₀, v ∈ expDomain I p ∧
      expMap I p v ∈ (chartAt H x₁).source ∧ extChartAt I x₁ (expMap I p v) = (Ψ v).1 := by
  obtain ⟨γ₀, U₀, h₀, h01⟩ := hv₀
  have hloc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Icc 0 1] t,
      (ExpProp I p v₀ γ₀ t ↔ ExpProp I p v₀ γ₀ s) ∧
        (ExpProp I p v₀ γ₀ s ↔ ExpProp I p v₀ γ₀ t) := by
    intro t ht
    have htU := h01 ht
    have hcont : ContinuousAt γ₀ t := (h₀.isGeodesicOn.mdifferentiableAt htU).continuousAt
    have hW : U₀ ∩ γ₀ ⁻¹' (chartAt H (γ₀ t)).source ∈ 𝓝 t :=
      Filter.inter_mem (h₀.isOpen.mem_nhds htU)
        (hcont.preimage_mem_nhds ((chartAt H (γ₀ t)).open_source.mem_nhds (mem_chart_source H _)))
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
    have hcdW : Icc (t - ε / 2) (t + ε / 2) ⊆ U₀ ∩ γ₀ ⁻¹' (chartAt H (γ₀ t)).source := by
      intro r hr
      apply hεW
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hr.1, hr.2]
    have htcd : t ∈ Ioo (t - ε / 2) (t + ε / 2) := ⟨by linarith, by linarith⟩
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds htcd.1 htcd.2), self_mem_nhdsWithin]
      with s hs hsI
    have hiff : ExpProp I p v₀ γ₀ t ↔ ExpProp I p v₀ γ₀ s :=
      ⟨fun h ↦ ExpProp.step h₀ (fun r hr ↦ (hcdW hr).1) (fun r hr ↦ (hcdW hr).2) htcd hs ht.1 h,
        fun h ↦ ExpProp.step h₀ (fun r hr ↦ (hcdW hr).1) (fun r hr ↦ (hcdW hr).2) hs htcd
          hsI.1 h⟩
    exact ⟨hiff, hiff.symm⟩
  have h1 : ExpProp I p v₀ γ₀ 1 :=
    (isPreconnected_Icc.induction₂' (fun x y ↦ (ExpProp I p v₀ γ₀ x ↔ ExpProp I p v₀ γ₀ y))
      hloc (fun x y z _ _ _ hxy hyz ↦ hxy.trans hyz) (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one)).1 (ExpProp.zero h₀)
  obtain ⟨x₁, -, Ψ, hΨ, -, hev⟩ := h1
  refine ⟨x₁, Ψ, hΨ, ?_⟩
  filter_upwards [hev] with v ⟨γ, U, hγ, hU1, hγ1, hγd⟩
  obtain ⟨hvD, hexp⟩ := expMap_eq hγ hU1
  refine ⟨hvD, hexp ▸ hγ1, ?_⟩
  rw [hexp]
  exact congrArg Prod.fst hγd

/-- **The domain of the exponential map is open.** -/
theorem isOpen_expDomain (p : M) : IsOpen (expDomain I p) :=
  isOpen_iff_mem_nhds.2 fun v₀ hv₀ ↦ by
    obtain ⟨x₁, Ψ, -, hev⟩ := expMap_local hv₀
    filter_upwards [hev] with v hv using hv.1

/-- **The exponential map is smooth** at every point of its domain. -/
theorem contMDiffAt_expMap {p : M} {v₀ : E} (hv₀ : v₀ ∈ expDomain I p) :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (expMap I p) v₀ := by
  obtain ⟨x₁, Ψ, hΨ, hev⟩ := expMap_local hv₀
  obtain ⟨_, hsrc₀, hφ₀⟩ := hev.self_of_nhds
  have heq : expMap I p =ᶠ[𝓝 v₀] fun v ↦ (extChartAt I x₁).symm (Ψ v).1 := by
    filter_upwards [hev] with v ⟨_, hsrc, hφ⟩
    rw [← hφ, (extChartAt I x₁).left_inv (by rwa [extChartAt_source])]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hmem : (Ψ v₀).1 ∈ (extChartAt I x₁).target :=
    hφ₀ ▸ (extChartAt I x₁).map_source (by rwa [extChartAt_source])
  have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun v ↦ (Ψ v).1) v₀ :=
    (contDiffAt_fst.comp v₀ hΨ).contMDiffAt
  exact ((contMDiffOn_extChartAt_symm (n := ∞) x₁).contMDiffAt
    ((isOpen_extChartAt_target x₁).mem_nhds hmem)).comp v₀ h1

/-- **The exponential map is `C^∞` on its (open) domain.** -/
theorem contMDiffOn_expMap (p : M) : ContMDiffOn 𝓘(ℝ, E) I ∞ (expMap I p) (expDomain I p) :=
  fun _ hv ↦ (contMDiffAt_expMap hv).contMDiffWithinAt

end Smooth

end PythagoreanPaper
