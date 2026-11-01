import PythagoreanPaper.Riemannian.AlongCurve
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The Levi-Civita connection in a chart: coordinate fields and Christoffel symbols

Fix a point `x₀` of a Riemannian manifold `M` and the chart `φ = extChartAt I x₀`. Mathlib's
trivialization of `TM` at `x₀` is the derivative of `φ`; the sections which are constant in it are
the coordinate vector fields `∂_w` (`coordField I x₀ w`). This file proves:

* `mlieBracket_coordField`: coordinate fields have vanishing Lie brackets on the chart domain;
* `contDiffOn_metricCoord`: the metric in the chart, `g_u (w, v) = ⟨∂_w, ∂_v⟩`, is smooth;
* `inner_leviCivita_coordField`: the Koszul formula for coordinate fields, i.e.
  `⟨∇_{∂_u} ∂_w, ∂_v⟩ = Γ♭(u, w, v)` with the Christoffel symbols of the first kind
  `Γ♭ = ½ (∂_u g_wv + ∂_w g_vu - ∂_v g_uw)`.
-/

noncomputable section

open Bundle Set Filter Function VectorField
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a coefficient `g (w, v)` of a bilinear-form-valued function. -/
lemma fderiv_apply_apply {G : E → E →L[ℝ] E →L[ℝ] ℝ} {p : E} (hG : DifferentiableAt ℝ G p)
    (a w v : E) : fderiv ℝ (fun q ↦ G q w v) p a = fderiv ℝ G p a w v := by
  have h1 : DifferentiableAt ℝ (fun q ↦ G q w) p := hG.clm_apply (differentiableAt_const w)
  rw [fderiv_clm_apply h1 (differentiableAt_const v), fderiv_clm_apply hG (differentiableAt_const w)]
  simp

/-- The derivative of `s ↦ G (c s) (x s) (y s)` for a bilinear-form-valued `G`. (The normed
structure of the space of bilinear forms is given explicitly: instance synthesis does not find the
one matching the topology and group structure used in the statement.) -/
lemma hasDerivAt_apply_apply {G : E → E →L[ℝ] E →L[ℝ] ℝ} {c x y : ℝ → E} {c' x' y' : E} {t : ℝ}
    (hG : DifferentiableAt ℝ G (c t)) (hc : HasDerivAt c c' t) (hx : HasDerivAt x x' t)
    (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s ↦ G (c s) (x s) (y s))
      ((fderiv ℝ G (c t) c' (x t) + G (c t) x') (y t) + G (c t) (x t) y') t :=
  ((@HasFDerivAt.comp_hasDerivAt ℝ _ E _ _ (E →L[ℝ] E →L[ℝ] ℝ)
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace c c' t G _
    hG.hasFDerivAt hc).clm_apply hx).clm_apply hy

end Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section CoordinateFields

variable [IsManifold I ∞ M]

variable (I) in
/-- The coordinate vector field `∂_w` of the chart at `x₀`: the section of `TM` which is constant,
equal to `w`, in the trivialization of `TM` at `x₀` (and zero outside the chart domain). -/
def coordField (x₀ : M) (w : E) : Π x : M, TangentSpace I x :=
  trivSection (trivializationAt E (TangentSpace I) x₀) w

lemma mem_baseSet_of_mem_chart_source {x₀ y : M} (hy : y ∈ (chartAt H x₀).source) :
    y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
  simpa using hy

/-- Coordinate fields are smooth on the chart domain. -/
lemma contMDiffAt_coordField (x₀ : M) (w : E) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ TotalSpace.mk' E x (coordField I x₀ w x)) y := by
  have hy' := mem_baseSet_of_mem_chart_source (I := I) hy
  rw [(trivializationAt E (TangentSpace I) x₀).contMDiffAt_section_iff hy']
  apply (contMDiffAt_const (c := w)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hy'] with z hz
  simp [coordField, trivSection, Trivialization.symmL_apply _ hz, Trivialization.apply_mk_symm _ hz]

lemma mdifferentiableAt_coordField (x₀ : M) (w : E) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    MDiffAt (T% (coordField I x₀ w)) y :=
  (contMDiffAt_coordField x₀ w hy).mdifferentiableAt (by simp)

/-- The constant vector field `w` on the model space. -/
def constField (w : E) : Π x : E, TangentSpace 𝓘(ℝ, E) x := fun _ ↦ w

lemma mdifferentiableAt_constField (w : E) (x : E) : MDiffAt (T% (constField w)) x :=
  mdifferentiableAt_tangentSection_iff.2 (differentiableAt_const w)

/-- Constant vector fields on the model space commute. -/
lemma mlieBracket_constField (u w : E) (x : E) :
    mlieBracket 𝓘(ℝ, E) (constField u) (constField w) x = 0 := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  show fderivWithin ℝ (fun _ : E ↦ w) univ x u - fderivWithin ℝ (fun _ : E ↦ u) univ x w = 0
  simp [fderivWithin_const_apply]

/-- On the chart domain, the coordinate field `∂_w` is the pullback by the chart of the constant
vector field `w` of the model space. -/
lemma coordField_eq_mpullback (x₀ : M) (w : E) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    coordField I x₀ w y = mpullback I 𝓘(ℝ, E) (extChartAt I x₀) (constField w) y := by
  have hy' : y ∈ (extChartAt I x₀).source := by simpa using hy
  rw [mpullback_apply, coordField, trivSection, TangentBundle.symmL_trivializationAt hy,
    ContinuousLinearMap.inverse_eq (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hy')
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy')]
  rfl

/-- **Coordinate fields commute**: the Lie bracket of two coordinate fields of a chart vanishes on
the chart domain. -/
theorem mlieBracket_coordField [CompleteSpace E] (x₀ : M) (u w : E) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    mlieBracket I (coordField I x₀ u) (coordField I x₀ w) y = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hev : ∀ v : E,
      coordField I x₀ v =ᶠ[𝓝 y] mpullback I 𝓘(ℝ, E) (extChartAt I x₀) (constField v) := by
    intro v
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hy] with z hz
    exact coordField_eq_mpullback x₀ v hz
  rw [(hev u).mlieBracket_vectorField_eq (hev w),
    ← mpullback_mlieBracket (mdifferentiableAt_constField u _) (mdifferentiableAt_constField w _)
      (contMDiffAt_extChartAt' (n := ∞) hy) (by simp), mpullback_apply, mlieBracket_constField,
    map_zero]

/-- In the chart at `x₀`, the coordinate field `∂_u` at `y` has coordinates `u`. -/
lemma mfderiv_extChartAt_coordField (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) (u : E) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y (coordField I x₀ u y) = u := by
  exact (congrArg (fun L : TangentSpace I y →L[ℝ] E ↦ L (coordField I x₀ u y))
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) hy).symm).trans
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL
      (mem_baseSet_of_mem_chart_source hy) u)

/-- The velocity of a curve, read in the trivialization of `TM` at `x₀`, is the derivative of the
curve in the chart at `x₀`. -/
theorem trivializationAt_velocity (x₀ : M) {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (ht : γ t ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (velocity I γ t) =
      deriv (extChartAt I x₀ ∘ γ) t := by
  have h1 := mfderiv_comp_apply t (mdifferentiableAt_extChartAt ht) hγ (1 : ℝ)
  have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (extChartAt I x₀ ∘ γ) t (1 : ℝ) =
      deriv (extChartAt I x₀ ∘ γ) t := by
    rw [mfderiv_eq_fderiv]
    rfl
  exact ((congrArg (fun L : TangentSpace I (γ t) →L[ℝ] E ↦ L (velocity I γ t))
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) ht)).trans
    h1.symm).trans h2

end CoordinateFields

section Metric

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The Riemannian metric in the chart at `x₀`: at the point with coordinates `p`, the bilinear form
`(w, v) ↦ ⟨∂_w, ∂_v⟩` (the matrix `g_ij (p)` of the metric). -/
def metricCoord (x₀ : M) (p : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace I ((extChartAt I x₀).symm p))).bilinearComp
    ((trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm p))
    ((trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm p))

lemma metricCoord_apply (x₀ : M) (p w v : E) :
    metricCoord I x₀ p w v = inner ℝ (coordField I x₀ w ((extChartAt I x₀).symm p))
      (coordField I x₀ v ((extChartAt I x₀).symm p)) :=
  rfl

/-- The metric in the chart, at the image of a point `y` of the chart domain. -/
lemma metricCoord_extChartAt (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) (w v : E) :
    metricCoord I x₀ (extChartAt I x₀ y) w v =
      inner ℝ (coordField I x₀ w y) (coordField I x₀ v y) := by
  rw [metricCoord_apply, (extChartAt I x₀).left_inv (by simpa using hy)]

variable (I) in
/-- The Christoffel symbols of the first kind in the chart at `x₀`, as the linear form
`c ↦ Γ♭(p)(a, b, c) = ½ (∂_a g_bc + ∂_b g_ca - ∂_c g_ab)` at the point with coordinates `p`. -/
def christoffelLow (x₀ : M) (p a b : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (fderiv ℝ (metricCoord I x₀) p a b + (fderiv ℝ (metricCoord I x₀) p b).flip a -
    ((fderiv ℝ (metricCoord I x₀) p).flip a).flip b)

lemma christoffelLow_apply (x₀ : M) (p a b c : E) :
    christoffelLow I x₀ p a b c = (fderiv ℝ (metricCoord I x₀) p a b c +
      fderiv ℝ (metricCoord I x₀) p b c a - fderiv ℝ (metricCoord I x₀) p c a b) / 2 := by
  simp [christoffelLow]
  ring

/-- Two tangent vectors at a point of the chart domain with the same inner products with all
coordinate fields are equal. -/
lemma eq_of_inner_coordField (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    {X₀ Y₀ : TangentSpace I y}
    (h : ∀ v : E, inner ℝ X₀ (coordField I x₀ v y) = inner ℝ Y₀ (coordField I x₀ v y)) :
    X₀ = Y₀ := by
  have hy' := mem_baseSet_of_mem_chart_source (I := I) hy
  have hv : coordField I x₀
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (X₀ - Y₀)) y =
      X₀ - Y₀ :=
    (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hy' _
  have h1 := h ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (X₀ - Y₀))
  rw [hv] at h1
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, h1, sub_self]

/-- **The metric in a chart is invertible** as a map `E → E*` (it is positive definite). -/
theorem isInvertible_metricCoord [FiniteDimensional ℝ E] (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target) :
    (metricCoord I x₀ p).IsInvertible := by
  have hy : (extChartAt I x₀).symm p ∈ (chartAt H x₀).source := by
    simpa using (extChartAt I x₀).map_target hp
  have hinj : Function.Injective (metricCoord I x₀ p) := by
    intro w w' hww'
    have h0 : metricCoord I x₀ p (w - w') = 0 := by rw [map_sub, hww', sub_self]
    have h1 : metricCoord I x₀ p (w - w') (w - w') = 0 := by
      rw [h0, zero_apply]
    rw [metricCoord_apply, inner_self_eq_zero] at h1
    have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm p) (coordField I x₀ (w - w') ((extChartAt I x₀).symm p)) =
        w - w' :=
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL
        (mem_baseSet_of_mem_chart_source hy) _
    rw [h1, map_zero] at h2
    exact sub_eq_zero.1 h2.symm
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  have hsurj : Function.Surjective (metricCoord I x₀ p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (metricCoord I x₀ p : E →ₗ[ℝ] E →L[ℝ] ℝ))).1 hinj
  exact ⟨(LinearEquiv.ofBijective (metricCoord I x₀ p : E →ₗ[ℝ] E →L[ℝ] ℝ)
    ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

variable (I) in
/-- **The Christoffel symbols** (of the second kind) in the chart at `x₀`: `Γ(p)(a, b)` is the vector
with `g_p (Γ(p)(a, b), c) = Γ♭(p)(a, b, c)` for all `c`. -/
def christoffel (x₀ : M) (p a b : E) : E :=
  (metricCoord I x₀ p).inverse (christoffelLow I x₀ p a b)

lemma metricCoord_christoffel [FiniteDimensional ℝ E] (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target) (a b : E) :
    metricCoord I x₀ p (christoffel I x₀ p a b) = christoffelLow I x₀ p a b :=
  (isInvertible_metricCoord x₀ hp).self_apply_inverse _

set_option synthInstance.maxHeartbeats 400000 in
variable (I) in
/-- The Christoffel symbols of the second kind as a continuous bilinear map `(a, b) ↦ Γ(p)(a, b)`.
(The three terms are `Γ♭`'s three terms, each composed with the inverse of the metric; we avoid
naming spaces of trilinear maps, on which instance synthesis is not reliable.) -/
def christoffelL (x₀ : M) (p : E) : E →L[ℝ] E →L[ℝ] E :=
  (1 / 2 : ℝ) •
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (metricCoord I x₀ p).inverse).comp
        (fderiv ℝ (metricCoord I x₀) p) +
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (metricCoord I x₀ p).inverse).comp
        ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap.comp
          (fderiv ℝ (metricCoord I x₀) p)).flip -
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (metricCoord I x₀ p).inverse).comp
        ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap.comp
          (fderiv ℝ (metricCoord I x₀) p).flip))

lemma christoffelL_apply (x₀ : M) (p a b : E) :
    christoffelL I x₀ p a b = christoffel I x₀ p a b := by
  simp [christoffelL, christoffel, christoffelLow, map_add, map_sub, map_smul]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The inner product of two coordinate fields is smooth on the chart domain. -/
lemma contMDiffAt_inner_coordField (x₀ : M) (w v : E) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun z ↦ inner ℝ (coordField I x₀ w z) (coordField I x₀ v z)) y :=
  ContMDiffAt.inner_bundle (contMDiffAt_coordField x₀ w hy) (contMDiffAt_coordField x₀ v hy)

/-- **The metric in a chart is smooth.** -/
theorem contDiffOn_metricCoord [FiniteDimensional ℝ E] (x₀ : M) :
    ContDiffOn ℝ ∞ (metricCoord I x₀) (extChartAt I x₀).target := by
  rw [contDiffOn_clm_apply]
  intro w
  rw [contDiffOn_clm_apply]
  intro v
  have h1 : ContMDiffOn I 𝓘(ℝ) ∞
      (fun y ↦ inner ℝ (coordField I x₀ w y) (coordField I x₀ v y)) (chartAt H x₀).source :=
    fun y hy ↦ (contMDiffAt_inner_coordField x₀ w v hy).contMDiffWithinAt
  have h2 := h1.comp (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀)
    (fun p hp ↦ by simpa using (extChartAt I x₀).map_target hp)
  exact contMDiffOn_iff_contDiffOn.1 h2

variable [I.Boundaryless] [FiniteDimensional ℝ E]

lemma differentiableAt_metricCoord (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target) :
    DifferentiableAt ℝ (metricCoord I x₀) p :=
  ((contDiffOn_metricCoord x₀).differentiableOn (by simp) p hp).differentiableAt
    ((isOpen_extChartAt_target x₀).mem_nhds hp)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The Christoffel symbols are smooth** on the chart. -/
theorem contDiffOn_christoffelL (x₀ : M) :
    ContDiffOn ℝ ∞ (christoffelL I x₀) (extChartAt I x₀).target := by
  have hG := contDiffOn_metricCoord (I := I) x₀
  have ho := isOpen_extChartAt_target (I := I) x₀
  have hD := hG.fderiv_of_isOpen ho (m := ∞) (by simp)
  have h3 : ∀ u v w : E, ContDiffOn ℝ ∞ (fun p ↦ fderiv ℝ (metricCoord I x₀) p u v w)
      (extChartAt I x₀).target := fun u v w ↦
    ((hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hlow : ∀ a b, ContDiffOn ℝ ∞ (fun p ↦ christoffelLow I x₀ p a b)
      (extChartAt I x₀).target := by
    intro a b
    rw [contDiffOn_clm_apply]
    intro c
    simp only [christoffelLow_apply]
    exact (((h3 a b c).add (h3 b c a)).sub (h3 c a b)).div_const 2
  have hinv : ContDiffOn ℝ ∞ (fun p ↦ (metricCoord I x₀ p).inverse)
      (extChartAt I x₀).target := by
    intro p hp
    exact ((isInvertible_metricCoord x₀ hp).contDiffAt_map_inverse.comp p
      (hG.contDiffAt (ho.mem_nhds hp))).contDiffWithinAt
  rw [contDiffOn_clm_apply]
  intro a
  rw [contDiffOn_clm_apply]
  intro b
  simp only [christoffelL_apply, christoffel]
  exact hinv.clm_apply (hlow a b)

/-- **Derivative of the metric along a coordinate field**: `∂_u ⟨∂_w, ∂_v⟩ = ∂_u g_wv`. -/
theorem mvfderiv_inner_coordField (x₀ : M) (u w v : E) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    d% (fun z ↦ inner ℝ (coordField I x₀ w z) (coordField I x₀ v z)) y (coordField I x₀ u y) =
      fderiv ℝ (metricCoord I x₀) (extChartAt I x₀ y) u w v := by
  have hy' : y ∈ (extChartAt I x₀).source := by simpa using hy
  have hφy : extChartAt I x₀ y ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hy'
  have hG := differentiableAt_metricCoord (I := I) x₀ hφy
  let g : E → ℝ := fun q ↦ metricCoord I x₀ q w v
  have hg : DifferentiableAt ℝ g (extChartAt I x₀ y) :=
    (hG.clm_apply (differentiableAt_const w)).clm_apply (differentiableAt_const v)
  have hf : (fun z ↦ inner ℝ (coordField I x₀ w z) (coordField I x₀ v z)) =ᶠ[𝓝 y]
      g ∘ extChartAt I x₀ := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hy] with z hz
    simp only [g, Function.comp_apply, metricCoord_extChartAt x₀ hz]
  have hd : d% (fun z ↦ inner ℝ (coordField I x₀ w z) (coordField I x₀ v z)) y =
      d% (g ∘ extChartAt I x₀) y := by
    simp only [mvfderiv, hf.mfderiv_eq]
    rfl
  rw [hd, mvfderiv_comp y hg.mdifferentiableAt (mdifferentiableAt_extChartAt hy),
    ContinuousLinearMap.comp_apply, mfderiv_extChartAt_coordField x₀ hy u, mvfderiv_eq_fderiv]
  exact fderiv_apply_apply hG u w v

/-- **The Koszul formula for coordinate fields**: `⟨∇_{∂_u} ∂_w, ∂_v⟩ = Γ♭(u, w, v)`. -/
theorem inner_leviCivita_coordField (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    (u w v : E) :
    inner ℝ (CovariantDerivative.leviCivitaConnection I M (coordField I x₀ w) y
      (coordField I x₀ u y)) (coordField I x₀ v y) =
      christoffelLow I x₀ (extChartAt I x₀ y) u w v := by
  rw [CovariantDerivative.leviCivitaConnection_apply_inner I (mdifferentiableAt_coordField x₀ u hy)
    (mdifferentiableAt_coordField x₀ w hy) (mdifferentiableAt_coordField x₀ v hy)]
  beta_reduce
  rw [mlieBracket_coordField x₀ u v hy, mlieBracket_coordField x₀ w u hy,
    mlieBracket_coordField x₀ v w hy, mvfderiv_inner_coordField x₀ u w v hy,
    mvfderiv_inner_coordField x₀ w v u hy, mvfderiv_inner_coordField x₀ v u w hy,
    christoffelLow_apply]
  simp

/-- **The Levi-Civita connection in a chart**: `∇_{∂_u} ∂_w = Γ(u, w)` at every point of the chart
domain. -/
theorem leviCivita_coordField (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) (u w : E) :
    CovariantDerivative.leviCivitaConnection I M (coordField I x₀ w) y (coordField I x₀ u y) =
      coordField I x₀ (christoffel I x₀ (extChartAt I x₀ y) u w) y := by
  have hy' : y ∈ (extChartAt I x₀).source := by simpa using hy
  apply eq_of_inner_coordField x₀ hy
  intro v
  rw [inner_leviCivita_coordField x₀ hy u w v, ← metricCoord_extChartAt x₀ hy,
    metricCoord_christoffel x₀ ((extChartAt I x₀).map_source hy')]

/-- The Levi-Civita connection of a coordinate field, read in the trivialization of `TM` at `x₀`:
`e (∇_X ∂_w) = Γ(e X, w)`. -/
theorem leviCivita_coordField_apply (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    (X₀ : TangentSpace I y) (w : E) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
      (CovariantDerivative.leviCivitaConnection I M (coordField I x₀ w) y X₀) =
      christoffel I x₀ (extChartAt I x₀ y)
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y X₀) w := by
  have hy' := mem_baseSet_of_mem_chart_source (I := I) hy
  have hX : X₀ = coordField I x₀
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y X₀) y :=
    ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hy' X₀).symm
  conv_lhs => rw [hX]
  rw [leviCivita_coordField x₀ hy]
  exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL hy' _

/-- **The covariant derivative along a curve in a chart**: in the trivialization of `TM` at `x₀`,
`D_t σ = x' + Γ(c)(c', x)`, where `x` are the coordinates of `σ` and `c` is the curve in the
chart. -/
theorem covAlong_leviCivita_chart (x₀ : M) {γ : ℝ → M} {σ : (t : ℝ) → TangentSpace I (γ t)}
    {t : ℝ} (ht : γ t ∈ (chartAt H x₀).source) (hσ : MDiffAlongAt I E γ σ t) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t)
      (covAlong (CovariantDerivative.leviCivitaConnection I M) γ σ t) =
      deriv (coordAlong (trivializationAt E (TangentSpace I) x₀) γ σ) t +
        christoffelL I x₀ (extChartAt I x₀ (γ t)) (deriv (extChartAt I x₀ ∘ γ) t)
          (coordAlong (trivializationAt E (TangentSpace I) x₀) γ σ t) := by
  have he := mem_baseSet_of_mem_chart_source (I := I) ht
  rw [covAlong_eq_covAlongIn _ (trivializationAt E (TangentSpace I) x₀) he hσ, covAlongIn,
    map_add, Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ he]
  congr 1
  rw [christoffelL_apply, ← trivializationAt_velocity x₀ hσ.mdifferentiableAt_curve ht]
  exact leviCivita_coordField_apply x₀ ht (velocity I γ t) _

end Metric

end PythagoreanPaper
