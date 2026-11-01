import PythagoreanPaper.Riemannian.ParallelTransport

/-!
# Metric compatibility along curves; parallel transport is an isometry

* `hasDerivAt_inner_along`: for fields `σ, τ` differentiable along a curve `γ`,
  `d/dt ⟨σ, τ⟩ = ⟨D_t σ, τ⟩ + ⟨σ, D_t τ⟩` for the Levi-Civita connection. The proof is a chart
  computation: in the chart at `γ t`, `⟨σ, τ⟩ = g(c)(x, y)` and `D_t σ = x' + Γ(c)(c', x)`, and
  `Γ♭(a, b, c) + Γ♭(a, c, b) = ∂_a g_bc` (`christoffelLow_add_swap`).
* `IsParallelAlongOn.inner_eq`: two parallel fields along a curve on an open interval have constant
  inner product. Hence parallel transport preserves inner products, lengths and angles.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The metric in a chart is symmetric. -/
lemma metricCoord_symm (x₀ : M) (p w v : E) :
    metricCoord I x₀ p w v = metricCoord I x₀ p v w := by
  rw [metricCoord_apply, metricCoord_apply, real_inner_comm]

/-- The inner product of two tangent vectors at a point of the chart domain, computed in the
chart. -/
lemma inner_eq_metricCoord (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    (X₀ Y₀ : TangentSpace I y) :
    inner ℝ X₀ Y₀ = metricCoord I x₀ (extChartAt I x₀ y)
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y X₀)
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y Y₀) := by
  have hy' := mem_baseSet_of_mem_chart_source (I := I) hy
  rw [metricCoord_extChartAt x₀ hy]
  congr 1
  · exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hy' X₀).symm
  · exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hy' Y₀).symm

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless]
  [FiniteDimensional ℝ E]

/-- The derivative of the metric in a chart is symmetric in its last two arguments. -/
lemma fderiv_metricCoord_symm (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target)
    (a w v : E) :
    fderiv ℝ (metricCoord I x₀) p a w v = fderiv ℝ (metricCoord I x₀) p a v w := by
  have hG := differentiableAt_metricCoord (I := I) x₀ hp
  rw [← fderiv_apply_apply hG a w v, ← fderiv_apply_apply hG a v w]
  have h : (fun q ↦ metricCoord I x₀ q w v) = fun q ↦ metricCoord I x₀ q v w :=
    funext fun q ↦ metricCoord_symm x₀ q w v
  rw [h]

/-- `Γ♭(a, b, c) + Γ♭(a, c, b) = ∂_a g_bc`: the metric compatibility of the Christoffel symbols. -/
lemma christoffelLow_add_swap (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target)
    (a b c : E) :
    christoffelLow I x₀ p a b c + christoffelLow I x₀ p a c b =
      fderiv ℝ (metricCoord I x₀) p a b c := by
  rw [christoffelLow_apply, christoffelLow_apply, fderiv_metricCoord_symm x₀ hp a c b,
    fderiv_metricCoord_symm x₀ hp c b a, fderiv_metricCoord_symm x₀ hp b a c]
  ring

/-- The algebraic identity behind metric compatibility along curves, in a chart:
`(∂_{c'} g)(x, y) + g(x', y) + g(x, y') = g(x' + Γ(c', x), y) + g(x, y' + Γ(c', y))`. -/
lemma metricCoord_along_identity (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target)
    (c' x x' y y' : E) :
    (fderiv ℝ (metricCoord I x₀) p c' x + metricCoord I x₀ p x') y + metricCoord I x₀ p x y' =
      metricCoord I x₀ p (x' + christoffelL I x₀ p c' x) y +
        metricCoord I x₀ p x (y' + christoffelL I x₀ p c' y) := by
  have hΓσ : metricCoord I x₀ p (christoffelL I x₀ p c' x) y = christoffelLow I x₀ p c' x y := by
    rw [christoffelL_apply, metricCoord_christoffel x₀ hp]
  have hΓτ : metricCoord I x₀ p x (christoffelL I x₀ p c' y) = christoffelLow I x₀ p c' y x := by
    rw [metricCoord_symm, christoffelL_apply, metricCoord_christoffel x₀ hp]
  have hsw := christoffelLow_add_swap x₀ hp c' x y
  simp only [map_add, add_apply]
  linarith

/-- **Metric compatibility along a curve**: for fields `σ, τ` differentiable along `γ` at `t`,
`d/dt ⟨σ, τ⟩ = ⟨D_t σ, τ⟩ + ⟨σ, D_t τ⟩` (Levi-Civita connection). -/
theorem hasDerivAt_inner_along {γ : ℝ → M} {σ τ : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hσ : MDiffAlongAt I E γ σ t) (hτ : MDiffAlongAt I E γ τ t) :
    HasDerivAt (fun s ↦ inner ℝ (σ s) (τ s))
      (inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t) (τ t) +
        inner ℝ (σ t) (covAlong (CovariantDerivative.leviCivitaConnection I M) γ τ t)) t := by
  have hγ := hσ.mdifferentiableAt_curve
  have ht : γ t ∈ (chartAt H (γ t)).source := mem_chart_source H (γ t)
  have he := mem_baseSet_of_mem_chart_source (I := I) ht
  have hφ : extChartAt I (γ t) (γ t) ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source (by simp)
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H (γ t)).source :=
    hγ.continuousAt.preimage_mem_nhds ((chartAt H (γ t)).open_source.mem_nhds ht)
  have hloc : (fun s ↦ inner ℝ (σ s) (τ s)) =ᶠ[𝓝 t]
      fun s ↦ metricCoord I (γ t) (extChartAt I (γ t) (γ s))
        (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ σ s)
        (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ τ s) := by
    filter_upwards [hev] with s hs
    exact inner_eq_metricCoord (γ t) hs (σ s) (τ s)
  have hc : HasDerivAt (fun s ↦ extChartAt I (γ t) (γ s)) (deriv (extChartAt I (γ t) ∘ γ) t) t :=
    (mdifferentiableAt_iff_differentiableAt.1
      ((mdifferentiableAt_extChartAt ht).comp t hγ)).hasDerivAt
  have hx := (hσ.differentiableAt_coord (trivializationAt E (TangentSpace I) (γ t)) he).hasDerivAt
  have hy := (hτ.differentiableAt_coord (trivializationAt E (TangentSpace I) (γ t)) he).hasDerivAt
  have h := hasDerivAt_apply_apply (differentiableAt_metricCoord (I := I) (γ t) hφ) hc hx hy
  refine (h.congr_of_eventuallyEq hloc).congr_deriv ?_
  have h1 : inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t) (τ t) =
      metricCoord I (γ t) (extChartAt I (γ t) (γ t))
        (deriv (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ σ) t +
          christoffelL I (γ t) (extChartAt I (γ t) (γ t)) (deriv (extChartAt I (γ t) ∘ γ) t)
            (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ σ t))
        (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ τ t) := by
    rw [inner_eq_metricCoord (γ t) ht, covAlong_leviCivita_chart (γ t) ht hσ]
    rfl
  have h2 : inner ℝ (σ t) (covAlong (CovariantDerivative.leviCivitaConnection I M) γ τ t) =
      metricCoord I (γ t) (extChartAt I (γ t) (γ t))
        (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ σ t)
        (deriv (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ τ) t +
          christoffelL I (γ t) (extChartAt I (γ t) (γ t)) (deriv (extChartAt I (γ t) ∘ γ) t)
            (coordAlong (trivializationAt E (TangentSpace I) (γ t)) γ τ t)) := by
    rw [inner_eq_metricCoord (γ t) ht, covAlong_leviCivita_chart (γ t) ht hτ]
    rfl
  rw [h1, h2]
  exact metricCoord_along_identity (γ t) hφ _ _ _ _ _

/-- **Parallel transport is an isometry**: two parallel fields along a curve on an open interval
have constant inner product. -/
theorem IsParallelAlongOn.inner_eq {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hU' : IsPreconnected U) {σ τ : (t : ℝ) → TangentSpace I (γ t)}
    (hσ : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ σ U)
    (hτ : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ τ U)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ U) (ht : t ∈ U) :
    inner ℝ (σ t) (τ t) = inner ℝ (σ t₀) (τ t₀) := by
  have hd : ∀ s ∈ U, HasDerivAt (fun s ↦ inner ℝ (σ s) (τ s)) 0 s := by
    intro s hs
    have h := hasDerivAt_inner_along (hσ s hs).1 (hτ s hs).1
    rwa [(hσ s hs).2, (hτ s hs).2, inner_zero_left, inner_zero_right, add_zero] at h
  exact hU.is_const_of_deriv_eq_zero hU'
    (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hd s hs).deriv) ht ht₀

/-- Parallel transport preserves lengths. -/
theorem IsParallelAlongOn.norm_eq {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hU' : IsPreconnected U) {σ : (t : ℝ) → TangentSpace I (γ t)}
    (hσ : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ σ U)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ U) (ht : t ∈ U) : ‖σ t‖ = ‖σ t₀‖ := by
  have h := hσ.inner_eq hU hU' hσ ht₀ ht
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

end PythagoreanPaper
