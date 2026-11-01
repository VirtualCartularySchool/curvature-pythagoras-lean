import PythagoreanPaper.Riemannian.Coordinates
import PythagoreanPaper.ODE.Linear

/-!
# Parallel transport for the Levi-Civita connection

Let `γ` be a `C¹` curve, defined on an open interval `U`, in a Riemannian manifold `M`.

* `exists_isParallelAlongOn`: for every `t₀ ∈ U` and every tangent vector `v` at `γ t₀` there is a
  parallel field along `γ` on `U` (for the Levi-Civita connection) with value `v` at `t₀`;
* `IsParallelAlongOn.eq_of_eq`: two parallel fields along `γ` on `U` which agree at one point agree
  on `U`.

In the chart at `x₀`, the parallel transport equation `D_t σ = 0` is the linear equation
`x' = -Γ(c)(c', x)` (`parallelAt_iff_hasDerivAt`), where `x` are the coordinates of `σ` and `c` is
the curve in the chart. Local solutions are glued with `ODE.Gluing`.

Manifolds are assumed boundaryless (as Riemannian manifolds in the manuscript are) and
finite-dimensional.
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

variable (I) in
/-- The coefficient `t ↦ -Γ(c t)(c' t, ·)` of the parallel transport equation in the chart at `x₀`,
where `c = φ ∘ γ` is the curve in the chart. -/
def ptCoeff (x₀ : M) (γ : ℝ → M) (t : ℝ) : E →L[ℝ] E :=
  -(christoffelL I x₀ (extChartAt I x₀ (γ t)) (deriv (extChartAt I x₀ ∘ γ) t))

/-- **The parallel transport equation in a chart**: at a time `t` where the curve is differentiable
and lies in the chart at `x₀`, `σ` is differentiable along `γ` with `D_t σ = 0` iff its coordinates
`x` satisfy `x'(t) = -Γ(c t)(c' t, x t)`. -/
theorem parallelAt_iff_hasDerivAt (x₀ : M) {γ : ℝ → M} {σ : (t : ℝ) → TangentSpace I (γ t)}
    {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : γ t ∈ (chartAt H x₀).source) :
    (MDiffAlongAt I E γ σ t ∧ covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t = 0) ↔
      HasDerivAt (coordAlong (trivializationAt E (TangentSpace I) x₀) γ σ)
        (ptCoeff I x₀ γ t (coordAlong (trivializationAt E (TangentSpace I) x₀) γ σ t)) t := by
  have he := mem_baseSet_of_mem_chart_source (I := I) ht
  constructor
  · rintro ⟨hσ, hcov⟩
    have hd := hσ.differentiableAt_coord (trivializationAt E (TangentSpace I) x₀) he
    have h1 := covAlong_leviCivita_chart x₀ ht hσ
    rw [hcov, map_zero] at h1
    have h2 : deriv (coordAlong (trivializationAt E (TangentSpace I) x₀) γ σ) t =
        ptCoeff I x₀ γ t (coordAlong (trivializationAt E (TangentSpace I) x₀) γ σ t) := by
      rw [ptCoeff, neg_apply]
      exact eq_neg_of_add_eq_zero_left h1.symm
    exact h2 ▸ hd.hasDerivAt
  · intro h
    have hσ : MDiffAlongAt I E γ σ t :=
      (mdiffAlongAt_iff (trivializationAt E (TangentSpace I) x₀) he).2 ⟨hγ, h.differentiableAt⟩
    refine ⟨hσ, ?_⟩
    have h1 := covAlong_leviCivita_chart x₀ ht hσ
    rw [h.deriv, ptCoeff, neg_apply, neg_add_cancel] at h1
    calc covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t)
            ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t)
              (covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t)) :=
          ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt he _).symm
      _ = 0 := by rw [h1, map_zero]

variable {γ : ℝ → M} {U : Set ℝ}

/-- The part of `U` on which `γ` stays in the chart at `x₀` is open. -/
lemma isOpen_inter_preimage_chart (hU : IsOpen U) (hγ : ContinuousOn γ U) (x₀ : M) :
    IsOpen (U ∩ γ ⁻¹' (chartAt H x₀).source) :=
  hγ.isOpen_inter_preimage hU (chartAt H x₀).open_source

/-- The coefficient of the parallel transport equation is continuous where `γ` is `C¹` and stays in
the chart. -/
lemma continuousOn_ptCoeff (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U) (x₀ : M) :
    ContinuousOn (ptCoeff I x₀ γ) (U ∩ γ ⁻¹' (chartAt H x₀).source) := by
  have hU₁ := isOpen_inter_preimage_chart (H := H) hU hγ.continuousOn x₀
  have hc : ContDiffOn ℝ 1 (extChartAt I x₀ ∘ γ) (U ∩ γ ⁻¹' (chartAt H x₀).source) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (n := 1)).comp (hγ.mono inter_subset_left)
      (fun t ht ↦ ht.2)
  have hc' : ContinuousOn (deriv (extChartAt I x₀ ∘ γ)) (U ∩ γ ⁻¹' (chartAt H x₀).source) :=
    hc.continuousOn_deriv_of_isOpen hU₁ le_rfl
  have hΓ : ContinuousOn (fun t ↦ christoffelL I x₀ (extChartAt I x₀ (γ t)))
      (U ∩ γ ⁻¹' (chartAt H x₀).source) :=
    (contDiffOn_christoffelL x₀).continuousOn.comp hc.continuousOn
      (fun t ht ↦ (extChartAt I x₀).map_source (by simpa using ht.2))
  exact (hΓ.clm_apply hc').neg

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Differentiability along a curve depends only on the germ of the field. -/
lemma MDiffAlongAt.congr_of_eventuallyEq {σ τ : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hσ : MDiffAlongAt I E γ σ t) (h : ∀ᶠ s in 𝓝 t, σ s = τ s) : MDiffAlongAt I E γ τ t := by
  unfold MDiffAlongAt at *
  exact hσ.congr_of_eventuallyEq (h.mono fun s hs ↦ by simp only [hs])

omit [I.Boundaryless] in
/-- The parallel transport condition depends only on the germ of the field. -/
lemma germLocal_parallel :
    GermLocal (β := fun t ↦ TangentSpace I (γ t))
      (fun t σ ↦ MDiffAlongAt I E γ σ t ∧
        covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t = 0) := by
  rintro t σ τ hστ ⟨hσ, hcov⟩
  exact ⟨hσ.congr_of_eventuallyEq hστ, (covAlong_congr _ hστ).symm.trans hcov⟩

/-- **Local uniqueness** of parallel fields. -/
lemma locallyUniqueOn_parallel (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U) :
    LocallyUniqueOn (β := fun t ↦ TangentSpace I (γ t))
      (fun t σ ↦ MDiffAlongAt I E γ σ t ∧
        covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t = 0) U := by
  intro t₁ ht₁
  have hU₁ := isOpen_inter_preimage_chart (H := H) hU hγ.continuousOn (γ t₁)
  have ht₁' : t₁ ∈ U ∩ γ ⁻¹' (chartAt H (γ t₁)).source := ⟨ht₁, mem_chart_source H (γ t₁)⟩
  obtain ⟨N, hN, hNu⟩ := locallyUniqueOn_linearODESol (b := fun _ ↦ (0 : E)) hU₁
    (continuousOn_ptCoeff hU hγ (γ t₁)) t₁ ht₁'
  refine ⟨N ∩ (U ∩ γ ⁻¹' (chartAt H (γ t₁)).source), inter_mem hN (hU₁.mem_nhds ht₁'),
    fun K hK hKc σ τ hσ hτ s hs hst t ht ↦ ?_⟩
  have hKU : ∀ t ∈ K, t ∈ U ∩ γ ⁻¹' (chartAt H (γ t₁)).source := fun t ht ↦ (hK ht).2
  have hode : ∀ ρ : (t : ℝ) → TangentSpace I (γ t),
      (∀ t ∈ K, MDiffAlongAt I E γ ρ t ∧
        covAlong (CovariantDerivative.leviCivitaConnection I M) γ ρ t = 0) →
      ∀ t ∈ K, LinearODESol (ptCoeff I (γ t₁) γ) (fun _ ↦ 0) t
        (coordAlong (trivializationAt E (TangentSpace I) (γ t₁)) γ ρ) := by
    intro ρ hρ t ht
    have h := (parallelAt_iff_hasDerivAt (γ t₁) (hρ t ht).1.mdifferentiableAt_curve
      (hKU t ht).2).1 (hρ t ht)
    simpa [LinearODESol] using h
  have hx := hNu K (fun t ht ↦ (hK ht).1) hKc _ _ (hode σ hσ) (hode τ hτ) s hs
    (by simp [coordAlong, hst]) t ht
  have he := mem_baseSet_of_mem_chart_source (I := I) (hKU t ht).2
  calc σ t = (trivializationAt E (TangentSpace I) (γ t₁)).symmL ℝ (γ t)
        (coordAlong (trivializationAt E (TangentSpace I) (γ t₁)) γ σ t) :=
        ((trivializationAt E (TangentSpace I) (γ t₁)).symmL_continuousLinearMapAt he _).symm
    _ = τ t := by
      rw [hx]
      exact (trivializationAt E (TangentSpace I) (γ t₁)).symmL_continuousLinearMapAt he _

/-- **Local solvability** of the parallel transport equation, with an existence interval independent
of the initial value. -/
lemma locallySolvableOn_parallel (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U) :
    LocallySolvableOn (β := fun t ↦ TangentSpace I (γ t))
      (fun t σ ↦ MDiffAlongAt I E γ σ t ∧
        covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t = 0) U := by
  intro t₁ ht₁
  have hU₁ := isOpen_inter_preimage_chart (H := H) hU hγ.continuousOn (γ t₁)
  have ht₁' : t₁ ∈ U ∩ γ ⁻¹' (chartAt H (γ t₁)).source := ⟨ht₁, mem_chart_source H (γ t₁)⟩
  obtain ⟨J, hJo, hJc, ht₁J, hJU, hsol⟩ := locallySolvableOn_linearODESol
    (b := fun _ ↦ (0 : E)) hU₁ (continuousOn_ptCoeff hU hγ (γ t₁)) continuousOn_const t₁ ht₁'
  have he : ∀ t ∈ J, γ t ∈ (trivializationAt E (TangentSpace I) (γ t₁)).baseSet :=
    fun t ht ↦ mem_baseSet_of_mem_chart_source (hJU ht).2
  refine ⟨J, hJo, hJc, ht₁J, fun t ht ↦ (hJU ht).1, fun s hs v ↦ ?_⟩
  obtain ⟨x, hx, hxs⟩ := hsol s hs
    ((trivializationAt E (TangentSpace I) (γ t₁)).continuousLinearMapAt ℝ (γ s) v)
  refine ⟨fun t ↦ (trivializationAt E (TangentSpace I) (γ t₁)).symmL ℝ (γ t) (x t),
    fun t ht ↦ ?_, ?_⟩
  · have hcoord : coordAlong (trivializationAt E (TangentSpace I) (γ t₁)) γ
        (fun t ↦ (trivializationAt E (TangentSpace I) (γ t₁)).symmL ℝ (γ t) (x t)) =ᶠ[𝓝 t] x := by
      filter_upwards [hJo.mem_nhds ht] with t' ht'
      exact (trivializationAt E (TangentSpace I) (γ t₁)).continuousLinearMapAt_symmL (he t' ht') _
    have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      (hγ.contMDiffAt (hU.mem_nhds (hJU ht).1)).mdifferentiableAt one_ne_zero
    beta_reduce
    rw [parallelAt_iff_hasDerivAt (γ t₁) hγt (hJU ht).2, hcoord.eq_of_nhds]
    have h := hx t ht
    simp only [LinearODESol, add_zero] at h
    exact h.congr_of_eventuallyEq hcoord
  · show (trivializationAt E (TangentSpace I) (γ t₁)).symmL ℝ (γ s) (x s) = v
    rw [hxs]
    exact (trivializationAt E (TangentSpace I) (γ t₁)).symmL_continuousLinearMapAt (he s hs) v

/-- **Existence of parallel transport** along a `C¹` curve on an open interval `U`: every tangent
vector at `γ t₀` is the value at `t₀` of a parallel field along `γ` on `U`. -/
theorem exists_isParallelAlongOn (hU : IsOpen U) (hU' : IsPreconnected U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U) {t₀ : ℝ} (ht₀ : t₀ ∈ U) (v : TangentSpace I (γ t₀)) :
    ∃ σ : (t : ℝ) → TangentSpace I (γ t),
      IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ σ U ∧ σ t₀ = v :=
  exists_of_locallySolvableOn (β := fun t ↦ TangentSpace I (γ t)) germLocal_parallel
    (locallyUniqueOn_parallel hU hγ) (locallySolvableOn_parallel hU hγ) hU' ht₀ v

/-- **Uniqueness of parallel transport**: two parallel fields along a `C¹` curve on an open
interval which agree at one time agree at all times. -/
theorem IsParallelAlongOn.eq_of_eq (hU : IsOpen U) (hU' : IsPreconnected U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U) {σ τ : (t : ℝ) → TangentSpace I (γ t)}
    (hσ : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ σ U)
    (hτ : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ τ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) (h : σ t₀ = τ t₀) : ∀ t ∈ U, σ t = τ t :=
  eqOn_of_locallyUniqueOn (β := fun t ↦ TangentSpace I (γ t)) (locallyUniqueOn_parallel hU hγ)
    subset_rfl hU' hσ hτ ht₀ h

end PythagoreanPaper
