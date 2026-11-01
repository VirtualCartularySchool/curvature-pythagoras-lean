import PythagoreanPaper.Riemannian.Geodesic
import PythagoreanPaper.ODE.SmoothFlow

/-!
# Gluing geodesics and smooth dependence in a chart

* `IsGeodesicOn.glue`: on a Hausdorff manifold, two geodesics on open intervals with the same
  position and velocity at a common time glue to a geodesic on the union.
* `chartData I x₀ γ t`: the position and velocity of `γ` at `t`, read in the chart at `x₀`;
  `chartData_change` describes the change of chart.
* `exists_chartData_flow`: near a geodesic which stays in the chart at `x₁` on `[c, d]`, the
  geodesics with nearby position and velocity at a time `s ∈ (c, d)` exist on `(c, d)`, and their
  position and velocity at any `t ∈ (c, d)` depend smoothly on the data at `s` (smooth dependence
  of solutions of ODEs on initial values, `PythagoreanPaper.ODE.SmoothFlow`, applied to the
  geodesic spray of the chart).
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

section Glue

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The velocity of a curve depends only on its germ. -/
lemma velocity_congr {γ γ' : ℝ → M} {t : ℝ} (h : γ' =ᶠ[𝓝 t] γ) :
    (velocity I γ' t : E) = velocity I γ t := by
  unfold velocity
  rw [h.mfderiv_eq]
  rfl

omit [I.Boundaryless] in
lemma IsGeodesicOn.mono {γ : ℝ → M} {U V : Set ℝ} (h : IsGeodesicOn I γ U) (hVU : V ⊆ U) :
    IsGeodesicOn I γ V :=
  fun t ht ↦ h t (hVU ht)

/-- Being a geodesic at `t` depends only on the germ of the curve at `t`. -/
theorem IsGeodesicOn.of_eventuallyEq {γ γ' : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn I γ U) {t : ℝ} (ht : t ∈ U) (h : γ' =ᶠ[𝓝 t] γ) :
    MDiffAlongAt I E γ' (velocity I γ') t ∧
      covAlong (CovariantDerivative.leviCivitaConnection I M) γ' (velocity I γ') t = 0 := by
  have hsrc : γ t ∈ (chartAt H (γ t)).source := mem_chart_source H _
  have hev := hγ.hasDerivAt_chart hU (γ t) ht hsrc
  have hevγ : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ s ∧
      γ s ∈ (chartAt H (γ t)).source := by
    filter_upwards [hev, hU.mem_nhds ht] with s hs hsU
    exact ⟨hγ.mdifferentiableAt hsU, hs.2⟩
  have hevγ' : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ' s ∧
      γ' s ∈ (chartAt H (γ t)).source := by
    filter_upwards [hevγ, h.eventuallyEq_nhds] with s hs hs'
    exact ⟨hs.1.congr_of_eventuallyEq hs', hs'.self_of_nhds ▸ hs.2⟩
  rw [geodesicAt_iff_chart (γ t) hevγ']
  have key := (geodesicAt_iff_chart (γ t) hevγ).1 (hγ t ht)
  have hd : deriv (extChartAt I (γ t) ∘ γ') =ᶠ[𝓝 t] deriv (extChartAt I (γ t) ∘ γ) :=
    (h.fun_comp (extChartAt I (γ t))).deriv
  rw [hd.eq_of_nhds, h.eq_of_nhds]
  exact key.congr_of_eventuallyEq hd

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The intersection of two preconnected subsets of `ℝ` is preconnected. -/
lemma isPreconnected_inter_real {U V : Set ℝ} (hU : IsPreconnected U) (hV : IsPreconnected V) :
    IsPreconnected (U ∩ V) :=
  isPreconnected_iff_ordConnected.2
    ((isPreconnected_iff_ordConnected.1 hU).inter (isPreconnected_iff_ordConnected.1 hV))

/-- **Gluing geodesics**: on a Hausdorff manifold, two geodesics on open preconnected sets of times
with the same position and velocity at a common time glue to a geodesic on the union. -/
theorem IsGeodesicOn.glue [T2Space M] {γ₁ γ₂ : ℝ → M} {U₁ U₂ : Set ℝ} (hU₁ : IsOpen U₁)
    (hU₁' : IsPreconnected U₁) (hU₂ : IsOpen U₂) (hU₂' : IsPreconnected U₂)
    (h₁ : IsGeodesicOn I γ₁ U₁) (h₂ : IsGeodesicOn I γ₂ U₂) {s : ℝ} (hs₁ : s ∈ U₁) (hs₂ : s ∈ U₂)
    (hp : γ₁ s = γ₂ s) (hv : (velocity I γ₁ s : E) = velocity I γ₂ s) :
    ∃ γ : ℝ → M, IsGeodesicOn I γ (U₁ ∪ U₂) ∧ (∀ t ∈ U₁, γ t = γ₁ t) ∧ ∀ t ∈ U₂, γ t = γ₂ t := by
  classical
  have hagree : ∀ t ∈ U₁ ∩ U₂, γ₁ t = γ₂ t := fun t ht ↦
    (IsGeodesicOn.eqOn (hU₁.inter hU₂) (isPreconnected_inter_real hU₁' hU₂')
      (h₁.mono inter_subset_left) (h₂.mono inter_subset_right) ⟨hs₁, hs₂⟩ hp hv t ht).1
  set γ : ℝ → M := fun t ↦ if t ∈ U₁ then γ₁ t else γ₂ t with hγ
  have e₁ : ∀ t ∈ U₁, γ t = γ₁ t := fun t ht ↦ by simp [hγ, ht]
  have e₂ : ∀ t ∈ U₂, γ t = γ₂ t := fun t ht ↦ by
    by_cases h : t ∈ U₁
    · rw [e₁ t h, hagree t ⟨h, ht⟩]
    · simp [hγ, h]
  refine ⟨γ, fun t ht ↦ ?_, e₁, e₂⟩
  rcases ht with ht | ht
  · exact h₁.of_eventuallyEq hU₁ ht (by filter_upwards [hU₁.mem_nhds ht] with r hr using e₁ r hr)
  · exact h₂.of_eventuallyEq hU₂ ht (by filter_upwards [hU₂.mem_nhds ht] with r hr using e₂ r hr)

end Glue

section ChartData

variable (I) in
/-- The position and velocity of a curve `γ` at time `t`, read in the chart at `x₀`. -/
def chartData (x₀ : M) (γ : ℝ → M) (t : ℝ) : E × E :=
  (extChartAt I x₀ (γ t), deriv (extChartAt I x₀ ∘ γ) t)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The position and velocity in the chart determine the position and the velocity. -/
lemma chartData_eq_iff (x₀ : M) {γ₁ γ₂ : ℝ → M} {t₁ t₂ : ℝ}
    (h₁ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ₁ t₁) (h₂ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ₂ t₂)
    (hs₁ : γ₁ t₁ ∈ (chartAt H x₀).source) (hs₂ : γ₂ t₂ ∈ (chartAt H x₀).source) :
    chartData I x₀ γ₁ t₁ = chartData I x₀ γ₂ t₂ ↔
      γ₁ t₁ = γ₂ t₂ ∧ (velocity I γ₁ t₁ : E) = velocity I γ₂ t₂ := by
  have e₁ := trivializationAt_velocity x₀ h₁ hs₁
  have e₂ := trivializationAt_velocity x₀ h₂ hs₂
  have hb₁ := mem_baseSet_of_mem_chart_source (I := I) hs₁
  have hb₂ := mem_baseSet_of_mem_chart_source (I := I) hs₂
  constructor
  · intro h
    have hpos : γ₁ t₁ = γ₂ t₂ := by
      have h1 : extChartAt I x₀ (γ₁ t₁) = extChartAt I x₀ (γ₂ t₂) := congrArg Prod.fst h
      rw [← (extChartAt I x₀).left_inv (by rwa [extChartAt_source] : γ₁ t₁ ∈ _),
        h1, (extChartAt I x₀).left_inv (by rwa [extChartAt_source] : γ₂ t₂ ∈ _)]
    refine ⟨hpos, ?_⟩
    have h2 : deriv (extChartAt I x₀ ∘ γ₁) t₁ = deriv (extChartAt I x₀ ∘ γ₂) t₂ :=
      congrArg Prod.snd h
    have s1 : @Eq E (velocity I γ₁ t₁) ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
        (γ₁ t₁) (deriv (extChartAt I x₀ ∘ γ₁) t₁)) := by
      rw [← e₁]
      exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb₁ _).symm
    have s2 : @Eq E ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ₁ t₁)
        (deriv (extChartAt I x₀ ∘ γ₁) t₁))
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ₂ t₂)
          (deriv (extChartAt I x₀ ∘ γ₂) t₂)) :=
      congrArg₂ (fun (b : M) (w : E) ↦
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ b w : E)) hpos h2
    have s3 : @Eq E ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ₂ t₂)
        (deriv (extChartAt I x₀ ∘ γ₂) t₂)) (velocity I γ₂ t₂) := by
      rw [← e₂]
      exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb₂ _
    exact s1.trans (s2.trans s3)
  · rintro ⟨hpos, hvel⟩
    refine Prod.ext (congrArg (extChartAt I x₀) hpos) ?_
    show deriv (extChartAt I x₀ ∘ γ₁) t₁ = deriv (extChartAt I x₀ ∘ γ₂) t₂
    rw [← e₁, ← e₂]
    exact congrArg₂ (fun (b : M) (w : E) ↦
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b w) hpos hvel

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The chart data depend only on the germ of the curve. -/
lemma chartData_congr (x₀ : M) {γ γ' : ℝ → M} {t : ℝ} (h : γ' =ᶠ[𝓝 t] γ) :
    chartData I x₀ γ' t = chartData I x₀ γ t :=
  Prod.ext (congrArg (extChartAt I x₀) h.eq_of_nhds)
    (h.fun_comp (extChartAt I x₀)).deriv_eq

variable (I) in
/-- The change of chart data from the chart at `x₁` to the chart at `x₂`. -/
def chartDataChange (x₁ x₂ : M) (y : E × E) : E × E :=
  (extChartAt I x₂ ((extChartAt I x₁).symm y.1),
    fderiv ℝ (extChartAt I x₂ ∘ (extChartAt I x₁).symm) y.1 y.2)

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The coordinate change between two charts is smooth on its (open) domain. -/
lemma contDiffOn_coordChange (x₁ x₂ : M) :
    IsOpen ((extChartAt I x₁).target ∩ (extChartAt I x₁).symm ⁻¹' (chartAt H x₂).source) ∧
      ContDiffOn ℝ ∞ (extChartAt I x₂ ∘ (extChartAt I x₁).symm)
        ((extChartAt I x₁).target ∩ (extChartAt I x₁).symm ⁻¹' (chartAt H x₂).source) := by
  refine ⟨(continuousOn_extChartAt_symm x₁).isOpen_inter_preimage (isOpen_extChartAt_target x₁)
    (chartAt H x₂).open_source, ?_⟩
  have := contDiffOn_ext_coord_change (I := I) (n := ∞) x₂ x₁
  rwa [PartialEquiv.trans_source, extChartAt_source, PartialEquiv.symm_source] at this

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The change of chart data is smooth near data of a point in both chart domains. -/
lemma contDiffAt_chartDataChange (x₁ x₂ : M) {y : E × E} (hy : y.1 ∈ (extChartAt I x₁).target)
    (hy₂ : (extChartAt I x₁).symm y.1 ∈ (chartAt H x₂).source) :
    ContDiffAt ℝ ∞ (chartDataChange I x₁ x₂) y := by
  obtain ⟨hS, hτ⟩ := contDiffOn_coordChange (I := I) x₁ x₂
  have hyS : y.1 ∈ (extChartAt I x₁).target ∩ (extChartAt I x₁).symm ⁻¹' (chartAt H x₂).source :=
    ⟨hy, hy₂⟩
  have h1 := (hτ.contDiffAt (hS.mem_nhds hyS)).comp y contDiffAt_fst
  have h2 := ((hτ.fderiv_of_isOpen hS (m := ∞) (by simp)).contDiffAt (hS.mem_nhds hyS)).comp y
    contDiffAt_fst
  exact h1.prodMk (h2.clm_apply contDiffAt_snd)

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Change of chart for chart data.** -/
lemma chartData_change (x₁ x₂ : M) {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (h₁ : γ t ∈ (chartAt H x₁).source) (h₂ : γ t ∈ (chartAt H x₂).source) :
    chartData I x₂ γ t = chartDataChange I x₁ x₂ (chartData I x₁ γ t) := by
  have hsrc₁ : γ t ∈ (extChartAt I x₁).source := by rwa [extChartAt_source]
  have hleft : (extChartAt I x₁).symm (extChartAt I x₁ (γ t)) = γ t :=
    (extChartAt I x₁).left_inv hsrc₁
  refine Prod.ext ?_ ?_
  · show extChartAt I x₂ (γ t) = extChartAt I x₂ ((extChartAt I x₁).symm (extChartAt I x₁ (γ t)))
    rw [hleft]
  · obtain ⟨hS, hτ⟩ := contDiffOn_coordChange (I := I) x₁ x₂
    have hyS : extChartAt I x₁ (γ t) ∈
        (extChartAt I x₁).target ∩ (extChartAt I x₁).symm ⁻¹' (chartAt H x₂).source :=
      ⟨(extChartAt I x₁).map_source hsrc₁, by rw [mem_preimage, hleft]; exact h₂⟩
    have hτd : HasFDerivAt (extChartAt I x₂ ∘ (extChartAt I x₁).symm)
        (fderiv ℝ (extChartAt I x₂ ∘ (extChartAt I x₁).symm) (extChartAt I x₁ (γ t)))
        (extChartAt I x₁ (γ t)) :=
      ((hτ.contDiffAt (hS.mem_nhds hyS)).differentiableAt (by simp)).hasFDerivAt
    have hd₁ : HasDerivAt (extChartAt I x₁ ∘ γ) (deriv (extChartAt I x₁ ∘ γ) t) t :=
      (mdifferentiableAt_iff_differentiableAt.1
        ((mdifferentiableAt_extChartAt h₁).comp t hγ)).hasDerivAt
    have hev : (extChartAt I x₂ ∘ γ) =ᶠ[𝓝 t]
        (extChartAt I x₂ ∘ (extChartAt I x₁).symm) ∘ (extChartAt I x₁ ∘ γ) := by
      filter_upwards [hγ.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source x₁).mem_nhds hsrc₁)] with s hs
      simp only [Function.comp_apply, (extChartAt I x₁).left_inv hs]
    exact ((hτd.comp_hasDerivAt t hd₁).congr_of_eventuallyEq hev).deriv

end ChartData

section Flow

/-- **Smooth dependence of geodesics in a chart.** Let `γ₀` be a geodesic on an open set
`U₀ ⊇ [c, d]` which stays in the chart at `x₁` on `[c, d]`, and let `s, t ∈ (c, d)`. Then every
position and velocity at time `s` near those of `γ₀` (read in the chart) are those of a geodesic
on `(c, d)` staying in the chart, and its position and velocity at time `t` are a smooth function
`Ψ` of the data at time `s`. -/
theorem exists_chartData_flow (x₁ : M) {γ₀ : ℝ → M} {U₀ : Set ℝ} (hU₀ : IsOpen U₀)
    (hγ₀ : IsGeodesicOn I γ₀ U₀) {c d : ℝ} (hsub : Icc c d ⊆ U₀)
    (hsrc : ∀ r ∈ Icc c d, γ₀ r ∈ (chartAt H x₁).source) {s t : ℝ} (hs : s ∈ Ioo c d)
    (ht : t ∈ Ioo c d) :
    ∃ Ψ : E × E → E × E, ContDiff ℝ ∞ Ψ ∧ Ψ (chartData I x₁ γ₀ s) = chartData I x₁ γ₀ t ∧
      ∀ᶠ y in 𝓝 (chartData I x₁ γ₀ s), ∃ γ : ℝ → M, IsGeodesicOn I γ (Ioo c d) ∧
        (∀ r ∈ Ioo c d, γ r ∈ (chartAt H x₁).source) ∧ chartData I x₁ γ s = y ∧
        chartData I x₁ γ t = Ψ y := by
  have hcd : c ≤ d := (hs.1.trans hs.2).le
  set α₀ : ℝ → E × E := chartData I x₁ γ₀ with hα₀def
  have hderiv : ∀ r ∈ Icc c d, HasDerivAt α₀ (geodesicSprayCoord I x₁ (α₀ r)) r := fun r hr ↦
    (hγ₀.hasDerivAt_chart hU₀ x₁ (hsub hr) (hsrc r hr)).self_of_nhds.1
  have hα₀c : ContinuousOn α₀ (Icc c d) := fun r hr ↦ (hderiv r hr).continuousAt.continuousWithinAt
  have hα₀U : ∀ r ∈ Icc c d, α₀ r ∈ (extChartAt I x₁).target ×ˢ (univ : Set E) := fun r hr ↦
    ⟨(extChartAt I x₁).map_source (by rw [extChartAt_source]; exact hsrc r hr), mem_univ _⟩
  obtain ⟨Φ, hΦ, hΦα₀, hev⟩ := exists_contDiff_flow_near hcd ⟨s, Ioo_subset_Icc_self hs⟩
    ((isOpen_extChartAt_target x₁).prod isOpen_univ) (contDiffOn_geodesicSprayCoord x₁) hα₀c
    (fun r hr ↦ hderiv r (Ioo_subset_Icc_self hr)) hα₀U
  set tt : Icc c d := ⟨t, Ioo_subset_Icc_self ht⟩
  have hΨ : ContDiff ℝ ∞ (fun y ↦ Φ y tt) := by
    have := (ContinuousMap.evalCLM ℝ tt : C(Icc c d, E × E) →L[ℝ] E × E).contDiff.comp hΦ
    exact this
  refine ⟨fun y ↦ Φ y tt, hΨ, hΦα₀ tt, ?_⟩
  filter_upwards [hev] with y ⟨hy0, hyU, hyd⟩
  set α : ℝ → E × E := IccExtend hcd (Φ y)
  obtain ⟨-, hgeo, hdata⟩ := isGeodesicOn_of_spray x₁ (α := α) hyd
    (fun r _ ↦ (hyU (projIcc c d hcd r)).1)
  have hdata' : ∀ r ∈ Ioo c d, chartData I x₁ (fun r ↦ (extChartAt I x₁).symm (α r).1) r = α r :=
    fun r hr ↦ Prod.ext (hdata r hr).2.1 (hdata r hr).2.2
  refine ⟨_, hgeo, fun r hr ↦ (hdata r hr).1, ?_, ?_⟩
  · rw [hdata' s hs]
    show IccExtend hcd (Φ y) s = y
    rw [IccExtend_of_mem hcd _ (Ioo_subset_Icc_self hs)]
    exact hy0
  · rw [hdata' t ht]
    exact IccExtend_of_mem hcd _ (Ioo_subset_Icc_self ht)

end Flow

end PythagoreanPaper
