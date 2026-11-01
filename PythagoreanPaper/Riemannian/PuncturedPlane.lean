import PythagoreanPaper.Sec04Jacobi
import PythagoreanPaper.Riemannian.ExpMap
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# The punctured plane: flat, but without the global structure of the Euclidean plane (C3.4)

The manuscript (§3) remarks that a Riemannian manifold of curvature zero need not have the same
global structure as the Euclidean plane if its global topology is different (C3.4). This file
proves it for the punctured plane `P = ℝ² \ {0}` (`puncturedPlane`, an open subset of
`ℝ² = EuclideanSpace ℝ (Fin 2)`), with the Euclidean metric restricted to it.

* **Two-dimensional Riemannian structure.** `P` is a smooth manifold modelled on `ℝ²` (Mathlib's
  structure of an open subset); its metric (`PuncturedPlane.metric`) is, on every tangent space
  `T_x P = ℝ²`, the inner product of `ℝ²`, and it is smooth. It is the restriction of the
  Euclidean metric: the pull-back of the metric of `ℝ²` by the inclusion `P → ℝ²`, whose derivative
  is the identity of `ℝ²` (`PuncturedPlane.inner_eq_inner_mfderiv`).
* **Curvature zero** (`PuncturedPlane.riemannCurvature_eq_zero`,
  `PuncturedPlane.hasConstSectionalCurvature_zero`): all charts of `P` are restrictions of the
  identity of `ℝ²`, so the metric is constant in them and the Christoffel symbols vanish.
* **Not homeomorphic to `ℝ²`** (`PuncturedPlane.not_homeomorphic`): `P` is homeomorphic to
  `ℂ \ {0}`, whose fundamental group is isomorphic to `2πiℤ` through the covering map
  `exp : ℂ → ℂ \ {0}` (Mathlib's `Complex.isAddQuotientCoveringMap_exp` and
  `IsAddQuotientCoveringMap.fundamentalGroupEquiv`); so `P` is not simply connected, while `ℝ²` is
  (it is contractible).
* **Geodesically incomplete** (`PuncturedPlane.not_isGeodesicallyComplete`): the geodesic
  `t ↦ (1 − t) e₁` (`PuncturedPlane.ray`, `t < 1`) tends to the origin, which is not a point of `P`,
  at the finite time `t = 1`, and cannot be extended: every geodesic with initial position `e₁`
  and initial velocity `−e₁` is defined only at times `t < 1`
  (`PuncturedPlane.subset_Iio_of_isGeodesicFrom`, by uniqueness of geodesics, continuity at `t = 1`
  and uniqueness of limits). Hence not every geodesic of `P` is defined on all of `ℝ`, and the
  exponential map at `e₁` is not defined on all of `T_{e₁} P`
  (`PuncturedPlane.neg_e1_notMem_expDomain`).

`sec3_punctured_plane` (**C3.4**) collects the four facts.
-/

noncomputable section

open Bundle Set Filter Function TopologicalSpace
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

section Completeness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- `M` is **geodesically complete**: for every point `p` and every tangent vector `v` at `p`, the
geodesic with initial position `p` and initial velocity `v` is defined on all of `ℝ`. -/
def IsGeodesicallyComplete : Prop :=
  ∀ (p : M) (v : E), ∃ γ : ℝ → M, IsGeodesicFrom I p v γ univ

end Completeness

/-- The punctured plane `ℝ² \ {0}`, an open subset of the Euclidean plane. -/
def puncturedPlane : Opens (EuclideanSpace ℝ (Fin 2)) :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

lemma mem_puncturedPlane {x : EuclideanSpace ℝ (Fin 2)} : x ∈ puncturedPlane ↔ x ≠ 0 :=
  Iff.rfl

namespace PuncturedPlane

local notation "R2" => EuclideanSpace ℝ (Fin 2)

section Charts

/-- All the charts of the punctured plane (restrictions of the identity chart of `ℝ²`) are the
same. -/
lemma achart_eq (x y : puncturedPlane) : achart R2 x = achart R2 y := rfl

lemma chartAt_source (x : puncturedPlane) : (chartAt R2 x).source = univ := by
  rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  simp

lemma coordChange_eq_one (x y z : puncturedPlane) :
    (tangentBundleCore 𝓘(ℝ, R2) puncturedPlane).coordChange (achart R2 x) (achart R2 y) z = 1 := by
  rw [achart_eq y x]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  exact (tangentBundleCore 𝓘(ℝ, R2) puncturedPlane).coordChange_self (achart R2 x) z
    (by rw [tangentBundleCore_baseSet, coe_achart, chartAt_source]; trivial) v

lemma continuousLinearMapAt_eq (x y : puncturedPlane) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).continuousLinearMapAt ℝ y =
      (1 : R2 →L[ℝ] R2) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp [chartAt_source]),
    coordChange_eq_one]

lemma symmL_eq (x y : puncturedPlane) :
    (trivializationAt R2 (TangentSpace 𝓘(ℝ, R2)) x).symmL ℝ y = (1 : R2 →L[ℝ] R2) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by simp [chartAt_source]),
    coordChange_eq_one]

/-- The changes of chart of the punctured plane are the identity. -/
lemma fderiv_chart_trans (x y z : puncturedPlane) (v : R2) :
    fderiv ℝ (chartAt R2 y ∘ (chartAt R2 x).symm) (chartAt R2 x z) v = v := by
  have h : (chartAt R2 y ∘ (chartAt R2 x).symm) =ᶠ[𝓝 (chartAt R2 x z)] id := by
    filter_upwards [(chartAt R2 x).open_target.mem_nhds
      ((chartAt R2 x).map_source (by simp [chartAt_source]))] with q hq
    exact (chartAt R2 x).right_inv hq
  rw [h.fderiv_eq, fderiv_id]
  rfl

end Charts

section Metric

set_option backward.isDefEq.respectTransparency false in
/-- The Euclidean metric of `ℝ²` on the punctured plane: on every tangent space `T_x P = ℝ²`, the
inner product of `ℝ²`. -/
def metric : ContMDiffRiemannianMetric 𝓘(ℝ, R2) ∞ R2
    (fun x : puncturedPlane ↦ TangentSpace 𝓘(ℝ, R2) x) where
  inner x := (riemannianMetricVectorSpace R2).inner (x : R2)
  symm x := (riemannianMetricVectorSpace R2).symm (x : R2)
  pos x := (riemannianMetricVectorSpace R2).pos (x : R2)
  isVonNBounded x := (riemannianMetricVectorSpace R2).isVonNBounded (x : R2)
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := innerSL ℝ)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.linearMapAt_apply, chartAt_source]
    erw [fderiv_chart_trans, fderiv_chart_trans]
    rfl

/-- The Riemannian metric of the punctured plane. -/
noncomputable instance instRiemannianBundle :
    RiemannianBundle (fun x : puncturedPlane ↦ TangentSpace 𝓘(ℝ, R2) x) :=
  ⟨metric.toRiemannianMetric⟩

/-- The Riemannian metric of the punctured plane is smooth. -/
instance instIsContMDiffRiemannianBundle : IsContMDiffRiemannianBundle 𝓘(ℝ, R2) ∞ R2
    (fun x : puncturedPlane ↦ TangentSpace 𝓘(ℝ, R2) x) :=
  inferInstance

/-- The inclusion `P → ℝ²` has derivative the identity of `ℝ²` at every point. -/
lemma mfderiv_val_apply (x : puncturedPlane) (v : TangentSpace 𝓘(ℝ, R2) x) :
    (show R2 from mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, R2) (Subtype.val : puncturedPlane → R2) x v) =
      (show R2 from v) := by
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := 𝓘(ℝ, R2))
    (mem_chart_source R2 x)
  rw [continuousLinearMapAt_eq] at h
  have h' := congrArg (fun L : TangentSpace 𝓘(ℝ, R2) x →L[ℝ] R2 ↦ L v) h
  exact h'.symm

/-- **The metric of the punctured plane is the restriction of the Euclidean metric of `ℝ²`**: it
is the pull-back of the metric of `ℝ²` by the inclusion `P → ℝ²`. -/
theorem inner_eq_inner_mfderiv (x : puncturedPlane) (u v : TangentSpace 𝓘(ℝ, R2) x) :
    inner ℝ u v = inner ℝ (mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, R2) (Subtype.val : puncturedPlane → R2) x u)
      (mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, R2) (Subtype.val : puncturedPlane → R2) x v) := by
  have hu := mfderiv_val_apply x u
  have hv := mfderiv_val_apply x v
  change (riemannianMetricVectorSpace R2).inner (x : R2) u v =
    (riemannianMetricVectorSpace R2).inner (x : R2)
      (mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, R2) (Subtype.val : puncturedPlane → R2) x u)
      (mfderiv 𝓘(ℝ, R2) 𝓘(ℝ, R2) (Subtype.val : puncturedPlane → R2) x v)
  simp only at hu hv
  rw [hu, hv]

end Metric

section Curvature

/-- In every chart of the punctured plane, the metric is the inner product of `ℝ²`. -/
lemma metricCoord_eq (x : puncturedPlane) (p w v : R2) :
    metricCoord 𝓘(ℝ, R2) x p w v = inner ℝ w v := by
  rw [metricCoord_apply, coordField, coordField, trivSection, trivSection, symmL_eq]
  rfl

/-- The Christoffel symbols of the punctured plane vanish. -/
lemma christoffelL_eq_zero (x : puncturedPlane) (p : R2) : christoffelL 𝓘(ℝ, R2) x p = 0 := by
  have hconst : metricCoord 𝓘(ℝ, R2) x = fun _ ↦ metricCoord 𝓘(ℝ, R2) x 0 := by
    funext q
    refine ContinuousLinearMap.ext fun w ↦ ContinuousLinearMap.ext fun v ↦ ?_
    rw [metricCoord_eq, metricCoord_eq]
  have hD : fderiv ℝ (metricCoord 𝓘(ℝ, R2) x) p = 0 := by
    rw [hconst, fderiv_const_apply]
  refine ContinuousLinearMap.ext fun a ↦ ContinuousLinearMap.ext fun b ↦ ?_
  rw [christoffelL_apply, christoffel]
  have hlow : christoffelLow 𝓘(ℝ, R2) x p a b = 0 := by
    refine ContinuousLinearMap.ext fun c ↦ ?_
    rw [christoffelLow_apply, hD]
    simp
  rw [hlow, map_zero]
  rfl

/-- **The punctured plane has curvature zero**: its Riemann curvature tensor vanishes. -/
theorem riemannCurvature_eq_zero (x : puncturedPlane) (u v w : TangentSpace 𝓘(ℝ, R2) x) :
    riemannCurvature 𝓘(ℝ, R2) x u v w = 0 := by
  have hD : ∀ p a b c : R2, christoffelDeriv 𝓘(ℝ, R2) x p a b c = 0 := by
    intro p a b c
    have h : (fun q ↦ christoffelL 𝓘(ℝ, R2) x q b c) = fun _ ↦ (0 : R2) := by
      funext q
      rw [christoffelL_eq_zero, zero_apply, zero_apply]
    rw [christoffelDeriv, h, fderiv_const_apply, zero_apply]
  rw [riemannCurvature, curvCoord, hD, hD, christoffelL_eq_zero]
  simp only [zero_apply, sub_self, add_zero, map_zero]

/-- The punctured plane has constant sectional curvature `0`. -/
theorem hasConstSectionalCurvature_zero :
    HasConstSectionalCurvature 𝓘(ℝ, R2) puncturedPlane 0 := by
  intro x u v
  rw [riemannCurvature_eq_zero, inner_zero_left, zero_mul]

end Curvature

section Geodesic

/-- The unit vector `e₁ = (1, 0)` of `ℝ²`. -/
def e1 : R2 := EuclideanSpace.single 0 1

lemma e1_ne_zero : e1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : R2 ↦ v 0) h
  simp [e1] at h0

/-- The point `e₁` of the punctured plane. -/
def p1 : puncturedPlane := ⟨e1, e1_ne_zero⟩

lemma smul_e1_mem {t : ℝ} (ht : t < 1) : (1 - t) • e1 ∈ puncturedPlane :=
  smul_ne_zero (sub_ne_zero.2 ht.ne') e1_ne_zero

/-- **The geodesic ray `t ↦ (1 − t) e₁`**, for `t < 1`. At the time `t = 1` it would reach the
origin, which is not a point of the punctured plane. (The value `e₁` for `t ≥ 1` is a placeholder;
only `t < 1` is used.) -/
def ray (t : ℝ) : puncturedPlane :=
  if ht : t < 1 then ⟨(1 - t) • e1, smul_e1_mem ht⟩ else p1

lemma ray_apply {t : ℝ} (ht : t < 1) : (ray t : R2) = (1 - t) • e1 := by
  simp [ray, ht]

lemma ray_zero : ray 0 = p1 :=
  Subtype.ext (by rw [ray_apply zero_lt_one, sub_zero, one_smul]; rfl)

lemma val_ray_eventuallyEq {t : ℝ} (ht : t < 1) :
    (Subtype.val ∘ ray) =ᶠ[𝓝 t] fun s ↦ (1 - s) • e1 := by
  filter_upwards [Iio_mem_nhds ht] with s hs using ray_apply hs

lemma hasDerivAt_line (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (1 - s) • e1) (-e1) t := by
  simpa using ((hasDerivAt_id t).const_sub 1).smul_const e1

lemma contMDiffAt_ray {t : ℝ} (ht : t < 1) : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) ∞ ray t := by
  rw [← ContMDiffAt.subtypeVal_comp_iff puncturedPlane ray t]
  have h : ContDiffAt ℝ ∞ (fun s : ℝ ↦ (1 - s) • e1) t := by fun_prop
  exact h.contMDiffAt.congr_of_eventuallyEq (val_ray_eventuallyEq ht)

lemma mdifferentiableAt_ray {t : ℝ} (ht : t < 1) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) ray t :=
  (contMDiffAt_ray ht).mdifferentiableAt (by simp)

lemma deriv_val_ray {t : ℝ} (ht : t < 1) : deriv (Subtype.val ∘ ray) t = -e1 := by
  rw [(val_ray_eventuallyEq ht).deriv_eq, (hasDerivAt_line t).deriv]

/-- The velocity of the ray is `−e₁`. -/
lemma velocity_ray {t : ℝ} (ht : t < 1) : (velocity 𝓘(ℝ, R2) ray t : R2) = -e1 := by
  have h := trivializationAt_velocity (ray t) (mdifferentiableAt_ray ht)
    (mem_chart_source R2 (ray t))
  rw [continuousLinearMapAt_eq] at h
  exact h.trans (deriv_val_ray ht)

/-- **The ray is a geodesic** of the punctured plane on `(−∞, 1)`. -/
theorem ray_isGeodesicOn : IsGeodesicOn 𝓘(ℝ, R2) ray (Iio 1) := by
  intro t ht
  have hev : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R2) ray s ∧
      ray s ∈ (chartAt R2 p1).source := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact ⟨mdifferentiableAt_ray hs, by simp [chartAt_source]⟩
  refine (geodesicAt_iff_chart p1 hev).2 ?_
  rw [christoffelL_eq_zero, zero_apply, zero_apply, neg_zero]
  have hd : deriv (extChartAt 𝓘(ℝ, R2) p1 ∘ ray) =ᶠ[𝓝 t] fun _ ↦ -e1 := by
    filter_upwards [Iio_mem_nhds ht] with s hs using deriv_val_ray hs
  exact (hasDerivAt_const t (-e1)).congr_of_eventuallyEq hd

/-- The ray tends to the origin of `ℝ²` (which is not a point of the punctured plane) at the finite
time `t = 1`. -/
theorem tendsto_ray : Tendsto (fun t ↦ (ray t : R2)) (𝓝[<] 1) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ ↦ (1 - t) • e1) (𝓝 1) (𝓝 ((1 - 1 : ℝ) • e1)) :=
    ((continuous_const.sub continuous_id).smul continuous_const).tendsto 1
  rw [sub_self, zero_smul] at h
  exact (h.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun t ht ↦ (ray_apply ht).symm)

/-- **The ray cannot be extended past `t = 1`**: every geodesic `γ` of the punctured plane on an
open interval `U ∋ 0` (open preconnected set of times) with `γ(0) = e₁` and `γ̇(0) = −e₁` has
`U ⊆ (−∞, 1)`. Proof: on `U ∩ (−∞, 1)`, `γ` agrees with the ray (uniqueness of geodesics); if
`1 ∈ U`, the continuity of `γ` at `1` and the limit of the ray at `1` would give `γ(1) = 0`, which
is not a point of the punctured plane. -/
theorem subset_Iio_of_isGeodesicFrom {γ : ℝ → puncturedPlane} {U : Set ℝ}
    (hγ : IsGeodesicFrom 𝓘(ℝ, R2) p1 (-e1) γ U) : U ⊆ Iio 1 := by
  have h1 : (1 : ℝ) ∉ U := by
    intro h1U
    have hV : IsOpen (U ∩ Iio 1) := hγ.isOpen.inter isOpen_Iio
    have hV' : IsPreconnected (U ∩ Iio 1) :=
      isPreconnected_inter_real hγ.isPreconnected isPreconnected_Iio
    have h0 : (0 : ℝ) ∈ U ∩ Iio 1 := ⟨hγ.zero_mem, mem_Iio.2 zero_lt_one⟩
    have heq := IsGeodesicOn.eqOn hV hV' (hγ.isGeodesicOn.mono inter_subset_left)
      (ray_isGeodesicOn.mono inter_subset_right) h0 (hγ.apply_zero.trans ray_zero.symm)
      (hγ.velocity_zero.trans (velocity_ray zero_lt_one).symm)
    have hev : (fun t ↦ (ray t : R2)) =ᶠ[𝓝[<] 1] fun t ↦ (γ t : R2) := by
      filter_upwards [inter_mem_nhdsWithin (Iio 1) (hγ.isOpen.mem_nhds h1U)] with t ht
      exact congrArg Subtype.val (heq t ⟨ht.2, ht.1⟩).1.symm
    have hlim : Tendsto (fun t ↦ (γ t : R2)) (𝓝[<] 1) (𝓝 (γ 1 : R2)) :=
      ((continuous_subtype_val.continuousAt).comp
        (hγ.isGeodesicOn.mdifferentiableAt h1U).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
    exact (γ 1).2 (tendsto_nhds_unique hlim (tendsto_ray.congr' hev))
  intro t ht
  by_contra hle
  exact h1 (hγ.isPreconnected.Icc_subset hγ.zero_mem ht ⟨zero_le_one, not_lt.1 hle⟩)

/-- The ray is the geodesic with initial position `e₁` and initial velocity `−e₁`, on `(−∞, 1)`. -/
theorem ray_isGeodesicFrom : IsGeodesicFrom 𝓘(ℝ, R2) p1 (-e1) ray (Iio 1) where
  isOpen := isOpen_Iio
  isPreconnected := isPreconnected_Iio
  zero_mem := mem_Iio.2 zero_lt_one
  isGeodesicOn := ray_isGeodesicOn
  apply_zero := ray_zero
  velocity_zero := velocity_ray zero_lt_one

/-- **The punctured plane is geodesically incomplete**: the geodesic with initial position `e₁` and
initial velocity `−e₁` is not defined on all of `ℝ`. -/
theorem not_isGeodesicallyComplete : ¬ IsGeodesicallyComplete 𝓘(ℝ, R2) puncturedPlane := by
  intro h
  obtain ⟨γ, hγ⟩ := h p1 (-e1)
  exact lt_irrefl _ (mem_Iio.1 (subset_Iio_of_isGeodesicFrom hγ (mem_univ 1)))

/-- The exponential map of the punctured plane at `e₁` is not defined at `−e₁ ∈ T_{e₁} P`. -/
theorem neg_e1_notMem_expDomain : -e1 ∉ expDomain 𝓘(ℝ, R2) p1 := by
  rintro ⟨γ, U, hγ, hU⟩
  exact lt_irrefl _ (mem_Iio.1 (subset_Iio_of_isGeodesicFrom hγ (hU ⟨zero_le_one, le_rfl⟩)))

end Geodesic

section Topology

/-- `ℂ \ {0}` is not simply connected: through the covering map `exp : ℂ → ℂ \ {0}`, whose deck
group is `2πiℤ` and whose total space `ℂ` is simply connected, the fundamental group of `ℂ \ {0}`
is isomorphic to `2πiℤ` (Mathlib's `IsAddQuotientCoveringMap.fundamentalGroupEquiv`), which is
not trivial. -/
theorem not_simplyConnectedSpace_complex : ¬ SimplyConnectedSpace {z : ℂ // z ≠ 0} := by
  intro hsc
  let x : {z : ℂ // z ≠ 0} := ⟨1, one_ne_zero⟩
  have hx : (0 : ℂ) ∈ (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ⁻¹' {x} := by
    simp [x]
  let φ := Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv (x := x) ⟨0, hx⟩
  have hsub : Subsingleton
      (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi * Complex.I)))ᵐᵒᵖ :=
    φ.symm.toEquiv.subsingleton
  have h := congrArg (fun g ↦ ((Multiplicative.toAdd (MulOpposite.unop g) :
      AddSubgroup.zmultiples (2 * Real.pi * Complex.I)) : ℂ))
    (Subsingleton.elim (MulOpposite.op (Multiplicative.ofAdd
      (⟨2 * Real.pi * Complex.I, AddSubgroup.mem_zmultiples _⟩ :
        AddSubgroup.zmultiples (2 * Real.pi * Complex.I)))) 1)
  simp [Real.pi_ne_zero, Complex.I_ne_zero] at h

/-- The punctured plane is homeomorphic to `ℂ \ {0}` (through the isometry `ℝ² ≃ ℂ` of the
orthonormal basis `1, i`). -/
def homeomorphComplex : puncturedPlane ≃ₜ {z : ℂ // z ≠ 0} :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.symm.subtype fun _ ↦
    (not_congr Complex.orthonormalBasisOneI.repr.symm.map_eq_zero_iff).symm

/-- **The punctured plane is not homeomorphic to `ℝ²`**: `ℝ²` is simply connected (it is
contractible), while the punctured plane, homeomorphic to `ℂ \ {0}`, is not. -/
theorem not_homeomorphic : IsEmpty (puncturedPlane ≃ₜ R2) := by
  refine ⟨fun f ↦ not_simplyConnectedSpace_complex ?_⟩
  have : SimplyConnectedSpace puncturedPlane := f.toHomotopyEquiv.simplyConnectedSpace
  exact homeomorphComplex.symm.toHomotopyEquiv.simplyConnectedSpace

end Topology

end PuncturedPlane

open PuncturedPlane in
/-- **C3.4.** A Riemannian manifold of curvature zero whose global topology is different from that
of the Euclidean plane need not have the global structure of the Euclidean plane. The punctured
plane `P = ℝ² \ {0}`, with the Euclidean metric restricted to it, is:

1. a two-dimensional smooth Riemannian manifold, whose metric is the restriction of the Euclidean
   metric (the pull-back by the inclusion `P → ℝ²`);
2. of curvature zero (the curvature tensor vanishes; constant sectional curvature `0`);
3. not homeomorphic to `ℝ²`;
4. geodesically incomplete: the geodesic `t ↦ (1 − t) e₁` (`t < 1`) with initial position `e₁` and
   initial velocity `−e₁` tends, at the finite time `t = 1`, to the origin, which is not a point of
   `P`; every geodesic with this initial position and velocity is defined only at times `t < 1`;
   so not every geodesic of `P` is defined on all of `ℝ`. -/
theorem sec3_punctured_plane :
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 ∧
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ puncturedPlane ∧
      IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (EuclideanSpace ℝ (Fin 2))
        (fun x : puncturedPlane ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x) ∧
      ∀ (x : puncturedPlane) (u v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x),
        inner ℝ u v =
          inner ℝ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
              (Subtype.val : puncturedPlane → EuclideanSpace ℝ (Fin 2)) x u)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
              (Subtype.val : puncturedPlane → EuclideanSpace ℝ (Fin 2)) x v)) ∧
    ((∀ (x : puncturedPlane) (u v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x),
        riemannCurvature 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x u v w = 0) ∧
      HasConstSectionalCurvature 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) puncturedPlane 0) ∧
    IsEmpty (puncturedPlane ≃ₜ EuclideanSpace ℝ (Fin 2)) ∧
    (IsGeodesicFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p1 (-e1) ray (Iio 1) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∉ puncturedPlane ∧
      Tendsto (fun t ↦ (ray t : EuclideanSpace ℝ (Fin 2))) (𝓝[<] 1) (𝓝 0) ∧
      (∀ (γ : ℝ → puncturedPlane) (U : Set ℝ),
        IsGeodesicFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p1 (-e1) γ U → U ⊆ Iio 1) ∧
      ¬ IsGeodesicallyComplete 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) puncturedPlane) :=
  ⟨⟨finrank_euclideanSpace_fin, inferInstance, inferInstance, inner_eq_inner_mfderiv⟩,
    ⟨riemannCurvature_eq_zero, hasConstSectionalCurvature_zero⟩, not_homeomorphic,
    ⟨ray_isGeodesicFrom, fun h ↦ h rfl, tendsto_ray, fun _ _ ↦ subset_Iio_of_isGeodesicFrom,
      not_isGeodesicallyComplete⟩⟩

end PythagoreanPaper
