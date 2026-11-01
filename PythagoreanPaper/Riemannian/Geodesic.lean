import PythagoreanPaper.Riemannian.Curvature

/-!
# Geodesics: the geodesic equation in a chart, local existence, uniqueness

* `geodesicAt_iff_chart`: in the chart at `x₀`, `D_t γ̇ = 0` iff the curve `c = φ ∘ γ` satisfies
  `c'' = -Γ(c)(c', c')`.
* `exists_geodesic`: for every tangent vector `v` at `p` there is a smooth geodesic `γ` on an open
  interval around `0` with `γ 0 = p` and `γ̇ 0 = v` (Picard–Lindelöf for the geodesic spray
  `(c, w) ↦ (w, -Γ(c)(w, w))` in the chart at `p`).
* `IsGeodesicOn.eqOn`: on a Hausdorff manifold, two geodesics on an open interval with the same
  position and velocity at one time agree on the interval.
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

section Chart

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Near a time where the curve is differentiable and in the chart at `x₀`, the coordinates of
its velocity in the trivialization at `x₀` are the derivative of the curve in the chart. -/
lemma coordAlong_velocity_eventuallyEq (x₀ : M) {γ : ℝ → M} {t : ℝ}
    (hγ : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s ∧ γ s ∈ (chartAt H x₀).source) :
    coordAlong (trivializationAt E (TangentSpace I) x₀) γ (velocity I γ) =ᶠ[𝓝 t]
      deriv (extChartAt I x₀ ∘ γ) := by
  filter_upwards [hγ] with s hs
  exact trivializationAt_velocity x₀ hs.1 hs.2

/-- **The geodesic equation in a chart**: if `γ` is differentiable near `t` and stays in the chart
at `x₀` there, then `γ̇` is differentiable along `γ` at `t` with `D_t γ̇ = 0` iff the curve
`c = φ ∘ γ` in the chart satisfies `c''(t) = -Γ(c t)(c' t, c' t)`. -/
theorem geodesicAt_iff_chart (x₀ : M) {γ : ℝ → M} {t : ℝ}
    (hγ : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s ∧ γ s ∈ (chartAt H x₀).source) :
    (MDiffAlongAt I E γ (velocity I γ) t ∧
        covAlong (CovariantDerivative.leviCivitaConnection I M) γ (velocity I γ) t = 0) ↔
      HasDerivAt (deriv (extChartAt I x₀ ∘ γ))
        (-christoffelL I x₀ (extChartAt I x₀ (γ t)) (deriv (extChartAt I x₀ ∘ γ) t)
          (deriv (extChartAt I x₀ ∘ γ) t)) t := by
  have hev := coordAlong_velocity_eventuallyEq x₀ hγ
  rw [parallelAt_iff_hasDerivAt x₀ hγ.self_of_nhds.1 hγ.self_of_nhds.2, hev.eq_of_nhds,
    ptCoeff, neg_apply]
  exact ⟨fun h ↦ h.congr_of_eventuallyEq hev.symm, fun h ↦ h.congr_of_eventuallyEq hev⟩

end Chart

section Existence

variable (I) in
/-- The geodesic spray in the chart at `x₀`: `(c, w) ↦ (w, -Γ(c)(w, w))`. -/
def geodesicSprayCoord (x₀ : M) (y : E × E) : E × E :=
  (y.2, -christoffelL I x₀ y.1 y.2 y.2)

/-- The geodesic spray is smooth over the chart. -/
lemma contDiffOn_geodesicSprayCoord (x₀ : M) :
    ContDiffOn ℝ ∞ (geodesicSprayCoord I x₀) ((extChartAt I x₀).target ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun y : E × E ↦ christoffelL I x₀ y.1)
      ((extChartAt I x₀).target ×ˢ univ) :=
    (contDiffOn_christoffelL x₀).comp contDiffOn_fst (fun y hy ↦ hy.1)
  exact contDiffOn_snd.prodMk ((h1.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).neg

/-- A solution of the geodesic spray in the chart, staying in the chart, gives a smooth curve. -/
lemma contMDiffOn_of_spray (x₀ : M) {α : ℝ → E × E} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (geodesicSprayCoord I x₀ (α t)) t)
    (hmem : ∀ t ∈ Ioo a b, (α t).1 ∈ (extChartAt I x₀).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t ↦ (extChartAt I x₀).symm (α t).1) (Ioo a b) := by
  have hα' : ContDiffOn ℝ ∞ α (Ioo a b) := by
    intro t ht
    obtain ⟨δ, hδ, hδU⟩ := exists_Icc_subset_of_isOpen isOpen_Ioo ht
    have hU : ContDiffOn ℝ ∞ (uncurry fun (_ : ℝ) ↦ geodesicSprayCoord I x₀)
        (Icc (t - δ) (t + δ) ×ˢ ((extChartAt I x₀).target ×ˢ univ)) :=
      (contDiffOn_geodesicSprayCoord x₀).comp contDiffOn_snd (fun y hy ↦ hy.2)
    have h := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hU
      (fun s hs ↦ (hα s (hδU hs)).hasDerivWithinAt) (fun s hs ↦ ⟨hmem s (hδU hs), trivial⟩)
    exact (h.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))).contDiffWithinAt
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t ↦ (α t).1) (Ioo a b) :=
    contMDiffOn_iff_contDiffOn.2 (contDiffOn_fst.comp hα' (mapsTo_univ _ _))
  exact (contMDiffOn_extChartAt_symm (n := ∞) x₀).comp hc hmem

/-- **A solution of the geodesic spray in a chart is a geodesic**: if `α = (c, w)` solves
`α' = (w, -Γ(c)(w, w))` on `(a, b)` and `c` stays in the chart at `x₀`, then `γ = φ⁻¹ ∘ c` is a
smooth geodesic on `(a, b)`, and its position and velocity read in the chart are `α`. -/
theorem isGeodesicOn_of_spray (x₀ : M) {α : ℝ → E × E} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (geodesicSprayCoord I x₀ (α t)) t)
    (hmem : ∀ t ∈ Ioo a b, (α t).1 ∈ (extChartAt I x₀).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t ↦ (extChartAt I x₀).symm (α t).1) (Ioo a b) ∧
      IsGeodesicOn I (fun t ↦ (extChartAt I x₀).symm (α t).1) (Ioo a b) ∧
      ∀ t ∈ Ioo a b, (extChartAt I x₀).symm (α t).1 ∈ (chartAt H x₀).source ∧
        extChartAt I x₀ ((extChartAt I x₀).symm (α t).1) = (α t).1 ∧
        deriv (extChartAt I x₀ ∘ fun t ↦ (extChartAt I x₀).symm (α t).1) t = (α t).2 := by
  set γ : ℝ → M := fun t ↦ (extChartAt I x₀).symm (α t).1 with hγdef
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ioo a b) := contMDiffOn_of_spray x₀ hα hmem
  have hγsrc : ∀ t ∈ Ioo a b, γ t ∈ (chartAt H x₀).source := by
    intro t ht
    have := (extChartAt I x₀).map_target (hmem t ht)
    rw [extChartAt_source] at this
    exact this
  have hφγ : ∀ t ∈ Ioo a b, extChartAt I x₀ (γ t) = (α t).1 := fun t ht ↦
    (extChartAt I x₀).right_inv (hmem t ht)
  have hdiff : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := fun t ht ↦
    (hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds ht)).mdifferentiableAt (by simp)
  have hc1 : ∀ t ∈ Ioo a b, (extChartAt I x₀ ∘ γ) =ᶠ[𝓝 t] fun s ↦ (α s).1 := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hφγ s hs
  have hfst : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ (α s).1) (α t).2 t := fun t ht ↦
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hα t ht)
  have hsnd : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ (α s).2)
      (-christoffelL I x₀ (α t).1 (α t).2 (α t).2) t := fun t ht ↦
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hα t ht)
  have hderiv : ∀ t ∈ Ioo a b, deriv (extChartAt I x₀ ∘ γ) t = (α t).2 := fun t ht ↦
    ((hfst t ht).congr_of_eventuallyEq (hc1 t ht)).deriv
  have hd2 : ∀ t ∈ Ioo a b, deriv (extChartAt I x₀ ∘ γ) =ᶠ[𝓝 t] fun s ↦ (α s).2 := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hderiv s hs
  refine ⟨hsmooth, fun t ht ↦ ?_, fun t ht ↦ ⟨hγsrc t ht, hφγ t ht, hderiv t ht⟩⟩
  have hev : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s ∧ γ s ∈ (chartAt H x₀).source := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ⟨hdiff s hs, hγsrc s hs⟩
  rw [geodesicAt_iff_chart x₀ hev, hderiv t ht, hφγ t ht]
  exact (hsnd t ht).congr_of_eventuallyEq (hd2 t ht)

/-- **Local existence of geodesics**: for every tangent vector `v` at `p` there is a smooth
geodesic `γ` on an open interval around `0` with `γ 0 = p` and `γ̇ 0 = v`. -/
theorem exists_geodesic (p : M) (v : TangentSpace I p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M, γ 0 = p ∧ velocity I γ 0 = v ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ioo (-ε) ε) ∧ IsGeodesicOn I γ (Ioo (-ε) ε) := by
  have hp : p ∈ (chartAt H p).source := mem_chart_source H p
  have hpb := mem_baseSet_of_mem_chart_source (I := I) hp
  have hφp : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source p)
  have hF : ContDiffAt ℝ 1 (geodesicSprayCoord I p)
      (extChartAt I p p, (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p v) :=
    ((contDiffOn_geodesicSprayCoord p).contDiffAt (prod_mem_nhds
      ((isOpen_extChartAt_target p).mem_nhds hφp) univ_mem)).of_le (by simp)
  obtain ⟨α, hα0, ε, hε, hα⟩ := hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hα
  -- shrink the interval so that the curve stays in the chart
  have hcont : ContinuousAt (fun t ↦ (α t).1) 0 :=
    continuous_fst.continuousAt.comp (hα 0 ⟨by linarith, by linarith⟩).continuousAt
  have hnhds : (fun t ↦ (α t).1) ⁻¹' (extChartAt I p).target ∈ 𝓝 (0 : ℝ) := by
    apply hcont.preimage_mem_nhds
    rw [hα0]
    exact (isOpen_extChartAt_target p).mem_nhds hφp
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.mem_nhds_iff.1 hnhds
  set ε' := min ε ε₁ with hε'
  have hε'pos : 0 < ε' := lt_min hε hε₁
  have hsub : Ioo (-ε') ε' ⊆ Ioo (-ε) ε := fun t ht ↦
    ⟨by linarith [ht.1, min_le_left ε ε₁], by linarith [ht.2, min_le_left ε ε₁]⟩
  have hmem : ∀ t ∈ Ioo (-ε') ε', (α t).1 ∈ (extChartAt I p).target := by
    intro t ht
    apply hε₁U
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1, min_le_right ε ε₁], by linarith [ht.2, min_le_right ε ε₁]⟩
  have hα' : ∀ t ∈ Ioo (-ε') ε', HasDerivAt α (geodesicSprayCoord I p (α t)) t :=
    fun t ht ↦ hα t (hsub ht)
  obtain ⟨hsmooth, hgeo, hdata⟩ := isGeodesicOn_of_spray p hα' hmem
  set γ : ℝ → M := fun t ↦ (extChartAt I p).symm (α t).1 with hγdef
  have h0 : (0 : ℝ) ∈ Ioo (-ε') ε' := ⟨by linarith, hε'pos⟩
  have hγ0 : γ 0 = p := by
    show (extChartAt I p).symm (α 0).1 = p
    rw [hα0]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  refine ⟨ε', hε'pos, γ, hγ0, ?_, hsmooth, hgeo⟩
  have hdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    (hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt (by simp)
  have hv0 := trivializationAt_velocity p hdiff0 (hdata 0 h0).1
  rw [(hdata 0 h0).2.2, hα0] at hv0
  have key : ∀ w w' : TangentSpace I p,
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p w =
        (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p w' → w = w' := by
    intro w w' h
    rw [← Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hpb w, h,
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hpb w']
  have hv0' : (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
      (velocity I γ 0) = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p v := by
    convert hv0 using 3
    rw [hγ0]
  exact key _ _ hv0'

end Existence

section Uniqueness

omit [I.Boundaryless] in
/-- A geodesic is differentiable. -/
lemma IsGeodesicOn.mdifferentiableAt {γ : ℝ → M} {U : Set ℝ} (hγ : IsGeodesicOn I γ U) {t : ℝ}
    (ht : t ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
  (hγ t ht).1.mdifferentiableAt_curve

/-- A geodesic, read in a chart, solves the geodesic spray of the chart. -/
lemma IsGeodesicOn.hasDerivAt_chart {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn I γ U) (x₀ : M) {t : ℝ} (ht : t ∈ U)
    (hsrc : γ t ∈ (chartAt H x₀).source) :
    ∀ᶠ s in 𝓝 t, HasDerivAt (fun r ↦ ((extChartAt I x₀ ∘ γ) r, deriv (extChartAt I x₀ ∘ γ) r))
      (geodesicSprayCoord I x₀ ((extChartAt I x₀ ∘ γ) s, deriv (extChartAt I x₀ ∘ γ) s)) s ∧
      γ s ∈ (chartAt H x₀).source := by
  have hcont : ContinuousOn γ U := fun s hs ↦ (hγ.mdifferentiableAt hs).continuousAt.continuousWithinAt
  have hW := hcont.isOpen_inter_preimage hU (chartAt H x₀).open_source
  filter_upwards [hW.mem_nhds ⟨ht, hsrc⟩] with s hs
  have hev : ∀ᶠ r in 𝓝 s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r ∧ γ r ∈ (chartAt H x₀).source := by
    filter_upwards [hW.mem_nhds hs] with r hr
    exact ⟨hγ.mdifferentiableAt hr.1, hr.2⟩
  have hc : HasDerivAt (extChartAt I x₀ ∘ γ) (deriv (extChartAt I x₀ ∘ γ) s) s :=
    (mdifferentiableAt_iff_differentiableAt.1
      ((mdifferentiableAt_extChartAt hs.2).comp s (hγ.mdifferentiableAt hs.1))).hasDerivAt
  exact ⟨hc.prodMk ((geodesicAt_iff_chart x₀ hev).1 (hγ s hs.1)), hs.2⟩

/-- **Local uniqueness of geodesics**: two geodesics on an open set with the same position and
velocity at `t₀` have the same positions and velocities near `t₀`. -/
theorem IsGeodesicOn.eventually_eq {γ₁ γ₂ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (h₁ : IsGeodesicOn I γ₁ U) (h₂ : IsGeodesicOn I γ₂ U) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    (hp : γ₁ t₀ = γ₂ t₀) (hv : (velocity I γ₁ t₀ : E) = velocity I γ₂ t₀) :
    ∀ᶠ t in 𝓝 t₀, γ₁ t = γ₂ t ∧ (velocity I γ₁ t : E) = velocity I γ₂ t := by
  have hs₁ : γ₁ t₀ ∈ (chartAt H (γ₁ t₀)).source := mem_chart_source H _
  have hs₂ : γ₂ t₀ ∈ (chartAt H (γ₁ t₀)).source := hp ▸ hs₁
  have hd₁ := h₁.hasDerivAt_chart hU (γ₁ t₀) ht₀ hs₁
  have hd₂ := h₂.hasDerivAt_chart hU (γ₁ t₀) ht₀ hs₂
  have hdiff₁ : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I γ₁ t := by
    filter_upwards [hU.mem_nhds ht₀] with t ht
    exact h₁.mdifferentiableAt ht
  have hdiff₂ : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I γ₂ t := by
    filter_upwards [hU.mem_nhds ht₀] with t ht
    exact h₂.mdifferentiableAt ht
  -- the velocity in the trivialization is the derivative in the chart
  have hvel : ∀ (γ : ℝ → M) (t : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I γ t →
      γ t ∈ (chartAt H (γ₁ t₀)).source →
      (velocity I γ t : E) = (trivializationAt E (TangentSpace I) (γ₁ t₀)).symmL ℝ (γ t)
        (deriv (extChartAt I (γ₁ t₀) ∘ γ) t) := by
    intro γ t hγt hγs
    rw [← trivializationAt_velocity (γ₁ t₀) hγt hγs]
    exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ) _
      (mem_baseSet_of_mem_chart_source hγs) _).symm
  -- the initial values in the chart agree
  have hy₀ : ((extChartAt I (γ₁ t₀) ∘ γ₁) t₀, deriv (extChartAt I (γ₁ t₀) ∘ γ₁) t₀) =
      ((extChartAt I (γ₁ t₀) ∘ γ₂) t₀, deriv (extChartAt I (γ₁ t₀) ∘ γ₂) t₀) := by
    have e₁ := trivializationAt_velocity (γ₁ t₀) (h₁.mdifferentiableAt ht₀) hs₁
    have e₂ := trivializationAt_velocity (γ₁ t₀) (h₂.mdifferentiableAt ht₀) hs₂
    have key := congrArg₂ (fun (b : M) (w : E) ↦
      (trivializationAt E (TangentSpace I) (γ₁ t₀)).continuousLinearMapAt ℝ b w) hp hv
    refine Prod.ext (by simp [Function.comp_apply, hp]) ?_
    exact e₁.symm.trans (key.trans e₂)
  -- Lipschitz bound for the spray near the initial value
  have hφ : extChartAt I (γ₁ t₀) (γ₁ t₀) ∈ (extChartAt I (γ₁ t₀)).target :=
    (extChartAt I (γ₁ t₀)).map_source (mem_extChartAt_source _)
  obtain ⟨K, S, hS, hlip⟩ := (((contDiffOn_geodesicSprayCoord (γ₁ t₀)).contDiffAt
    (prod_mem_nhds ((isOpen_extChartAt_target (γ₁ t₀)).mem_nhds hφ) univ_mem)).of_le
      (by simp) : ContDiffAt ℝ 1 (geodesicSprayCoord I (γ₁ t₀))
        ((extChartAt I (γ₁ t₀) ∘ γ₁) t₀, deriv (extChartAt I (γ₁ t₀) ∘ γ₁) t₀)).exists_lipschitzOnWith
  have hin₁ : ∀ᶠ t in 𝓝 t₀, ((extChartAt I (γ₁ t₀) ∘ γ₁) t, deriv (extChartAt I (γ₁ t₀) ∘ γ₁) t) ∈ S :=
    hd₁.self_of_nhds.1.continuousAt.preimage_mem_nhds hS
  have hin₂ : ∀ᶠ t in 𝓝 t₀, ((extChartAt I (γ₁ t₀) ∘ γ₂) t, deriv (extChartAt I (γ₁ t₀) ∘ γ₂) t) ∈ S :=
    hd₂.self_of_nhds.1.continuousAt.preimage_mem_nhds (hy₀ ▸ hS)
  have hode := ODE_solution_unique_of_eventually (K := K)
    (v := fun _ ↦ geodesicSprayCoord I (γ₁ t₀)) (s := fun _ ↦ S)
    (Filter.Eventually.of_forall fun _ ↦ hlip)
    ((hd₁.and hin₁).mono fun t h ↦ ⟨h.1.1, h.2⟩) ((hd₂.and hin₂).mono fun t h ↦ ⟨h.1.1, h.2⟩) hy₀
  filter_upwards [hode, hd₁, hd₂, hdiff₁, hdiff₂] with t ht hdt₁ hdt₂ hγ₁ hγ₂
  have hc : (extChartAt I (γ₁ t₀) ∘ γ₁) t = (extChartAt I (γ₁ t₀) ∘ γ₂) t := congrArg Prod.fst ht
  have hd : deriv (extChartAt I (γ₁ t₀) ∘ γ₁) t = deriv (extChartAt I (γ₁ t₀) ∘ γ₂) t :=
    congrArg Prod.snd ht
  have hpt : γ₁ t = γ₂ t := by
    have hx₁ : γ₁ t ∈ (extChartAt I (γ₁ t₀)).source := by simpa using hdt₁.2
    have hx₂ : γ₂ t ∈ (extChartAt I (γ₁ t₀)).source := by simpa using hdt₂.2
    calc γ₁ t = (extChartAt I (γ₁ t₀)).symm (extChartAt I (γ₁ t₀) (γ₁ t)) :=
          ((extChartAt I (γ₁ t₀)).left_inv hx₁).symm
      _ = (extChartAt I (γ₁ t₀)).symm (extChartAt I (γ₁ t₀) (γ₂ t)) :=
          congrArg (extChartAt I (γ₁ t₀)).symm hc
      _ = γ₂ t := (extChartAt I (γ₁ t₀)).left_inv hx₂
  refine ⟨hpt, ?_⟩
  rw [hvel γ₁ t hγ₁ hdt₁.2, hvel γ₂ t hγ₂ hdt₂.2]
  exact congrArg₂ (fun (b : M) (w : E) ↦
    ((trivializationAt E (TangentSpace I) (γ₁ t₀)).symmL ℝ b w : E)) hpt hd

/-- **Uniqueness of geodesics**: on a Hausdorff manifold, two geodesics on an open interval with
the same position and velocity at one time have the same positions and velocities on the whole
interval. -/
theorem IsGeodesicOn.eqOn [T2Space M] {γ₁ γ₂ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hU' : IsPreconnected U) (h₁ : IsGeodesicOn I γ₁ U) (h₂ : IsGeodesicOn I γ₂ U) {t₀ : ℝ}
    (ht₀ : t₀ ∈ U) (hp : γ₁ t₀ = γ₂ t₀) (hv : (velocity I γ₁ t₀ : E) = velocity I γ₂ t₀) :
    ∀ t ∈ U, γ₁ t = γ₂ t ∧ (velocity I γ₁ t : E) = velocity I γ₂ t := by
  intro t ht
  refine (hU'.induction₂' (fun x y ↦ ((γ₁ x = γ₂ x ∧ (velocity I γ₁ x : E) = velocity I γ₂ x) ↔
    (γ₁ y = γ₂ y ∧ (velocity I γ₁ y : E) = velocity I γ₂ y))) (fun x hx ↦ ?_)
    (fun x y z _ _ _ hxy hyz ↦ hxy.trans hyz) ht₀ ht).1 ⟨hp, hv⟩
  apply eventually_nhdsWithin_of_eventually_nhds
  by_cases hQ : γ₁ x = γ₂ x ∧ (velocity I γ₁ x : E) = velocity I γ₂ x
  · filter_upwards [h₁.eventually_eq hU h₂ hx hQ.1 hQ.2] with y hy
    exact ⟨iff_of_true hQ hy, iff_of_true hy hQ⟩
  · suffices h : ∀ᶠ y in 𝓝 x, ¬(γ₁ y = γ₂ y ∧ (velocity I γ₁ y : E) = velocity I γ₂ y) by
      filter_upwards [h] with y hy
      exact ⟨iff_of_false hQ hy, iff_of_false hy hQ⟩
    by_cases hpx : γ₁ x = γ₂ x
    · -- same point, different velocities: compare in the chart at `γ₁ x`
      have hs₁ : γ₁ x ∈ (chartAt H (γ₁ x)).source := mem_chart_source H _
      have hs₂ : γ₂ x ∈ (chartAt H (γ₁ x)).source := hpx ▸ hs₁
      have hd₁ := h₁.hasDerivAt_chart hU (γ₁ x) hx hs₁
      have hd₂ := h₂.hasDerivAt_chart hU (γ₁ x) hx hs₂
      have hne : deriv (extChartAt I (γ₁ x) ∘ γ₁) x ≠ deriv (extChartAt I (γ₁ x) ∘ γ₂) x := by
        intro heq
        apply hQ
        refine ⟨hpx, ?_⟩
        have e₁ := trivializationAt_velocity (γ₁ x) (h₁.mdifferentiableAt hx) hs₁
        have e₂ := trivializationAt_velocity (γ₁ x) (h₂.mdifferentiableAt hx) hs₂
        have hb := mem_baseSet_of_mem_chart_source (I := I) hs₁
        have hb₂ := mem_baseSet_of_mem_chart_source (I := I) hs₂
        have s1 : @Eq E (velocity I γ₁ x) ((trivializationAt E (TangentSpace I) (γ₁ x)).symmL ℝ
            (γ₁ x) (deriv (extChartAt I (γ₁ x) ∘ γ₁) x)) := by
          rw [← e₁]
          exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb _).symm
        have s2 : @Eq E ((trivializationAt E (TangentSpace I) (γ₁ x)).symmL ℝ (γ₁ x)
            (deriv (extChartAt I (γ₁ x) ∘ γ₁) x))
            ((trivializationAt E (TangentSpace I) (γ₁ x)).symmL ℝ (γ₂ x)
              (deriv (extChartAt I (γ₁ x) ∘ γ₂) x)) :=
          congrArg₂ (fun (b : M) (w : E) ↦
            ((trivializationAt E (TangentSpace I) (γ₁ x)).symmL ℝ b w : E)) hpx heq
        have s3 : @Eq E ((trivializationAt E (TangentSpace I) (γ₁ x)).symmL ℝ (γ₂ x)
            (deriv (extChartAt I (γ₁ x) ∘ γ₂) x)) (velocity I γ₂ x) := by
          rw [← e₂]
          exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb₂ _
        exact s1.trans (s2.trans s3)
      have hcd₁ := (hd₁.self_of_nhds.1.continuousAt.snd)
      have hcd₂ := (hd₂.self_of_nhds.1.continuousAt.snd)
      have hneq : ∀ᶠ y in 𝓝 x,
          deriv (extChartAt I (γ₁ x) ∘ γ₁) y ≠ deriv (extChartAt I (γ₁ x) ∘ γ₂) y :=
        (hcd₁.ne_iff_eventually_ne hcd₂).1 hne
      filter_upwards [hneq, hd₁, hd₂, (hU.mem_nhds hx)] with y hy hy₁ hy₂ hyU
      rintro ⟨hpy, hvy⟩
      apply hy
      have e₁ := trivializationAt_velocity (γ₁ x) (h₁.mdifferentiableAt hyU) hy₁.2
      have e₂ := trivializationAt_velocity (γ₁ x) (h₂.mdifferentiableAt hyU) hy₂.2
      have key := congrArg₂ (fun (b : M) (w : E) ↦
        (trivializationAt E (TangentSpace I) (γ₁ x)).continuousLinearMapAt ℝ b w) hpy hvy
      exact e₁.symm.trans (key.trans e₂)
    · -- different points: separate them (Hausdorff)
      have hne := ((h₁.mdifferentiableAt hx).continuousAt.ne_iff_eventually_ne
        (h₂.mdifferentiableAt hx).continuousAt).1 hpx
      filter_upwards [hne] with y hy
      exact fun h ↦ hy h.1

end Uniqueness

end PythagoreanPaper
