import PythagoreanPaper.Riemannian.NormalBall
import PythagoreanPaper.Riemannian.Triangle
import PythagoreanPaper.Sec04Jacobi

/-!
# The Euclidean plane as the model space of curvature `0` (manuscript §9)

The Euclidean plane `ℝ² = EuclideanSpace ℝ (Fin 2)`, with its canonical Riemannian metric, has
curvature `0` (`hasConstSectionalCurvature_euclidean`). This file shows:

* `EuclideanPlane.expMap_eq`: `exp_p v = p + v` for every `v` (lines are geodesics);
* `EuclideanPlane.isNormalBall`: every ball `B_ρ` of `T_p ℝ²` is a normal ball;
* `EuclideanPlane.sidesInNormalBalls`: **every** geodesic triangle of `ℝ²` satisfies the technical
  condition `SidesInNormalBalls` of `PythagoreanPaper.Riemannian.Triangle`.

So the theorems of `PythagoreanPaper.Riemannian.Triangle` apply to every geodesic triangle of the
Euclidean plane, with no further hypothesis (`PythagoreanPaper.Riemannian.ModelTriangles`).
-/

noncomputable section

open Bundle Set Filter Function NormedSpace
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

namespace EuclideanPlane

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- In the Euclidean plane, the derivative of a curve is its velocity. -/
lemma deriv_eq_velocity {γ : ℝ → R2} {t : ℝ} (hγ : DifferentiableAt ℝ γ t) :
    deriv γ t = velocity 𝓘(ℝ, R2) γ t := by
  have h := deriv_chart_eq_velocity (I := 𝓘(ℝ, R2)) hγ.mdifferentiableAt
  rwa [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h

/-- The line `t ↦ p + t v` has velocity `v`. -/
lemma velocity_line (p v : R2) (t : ℝ) : velocity 𝓘(ℝ, R2) (fun s ↦ p + s • v) t = v := by
  have hd : HasDerivAt (fun s : ℝ ↦ p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  rw [← deriv_eq_velocity hd.differentiableAt, hd.deriv]

/-- **Lines are geodesics** of the Euclidean plane. -/
theorem isGeodesicFrom_line (p v : R2) :
    IsGeodesicFrom 𝓘(ℝ, R2) p v (fun s ↦ p + s • v) univ where
  isOpen := isOpen_univ
  isPreconnected := isPreconnected_univ
  zero_mem := mem_univ 0
  isGeodesicOn := by
    have hd : ∀ t ∈ (univ : Set ℝ), DifferentiableAt ℝ (fun s : ℝ ↦ p + s • v) t := fun t _ ↦
      ((differentiableAt_id.smul_const v).const_add p)
    rw [IsGeodesicOn, euclidean_isParallelAlongOn_iff isOpen_univ isPreconnected_univ hd]
    intro s _ t _
    show velocity 𝓘(ℝ, R2) (fun s ↦ p + s • v) s = velocity 𝓘(ℝ, R2) (fun s ↦ p + s • v) t
    rw [velocity_line, velocity_line]
  apply_zero := by simp
  velocity_zero := velocity_line p v 0

/-- `exp_p v = p + v`, for every `v`. -/
theorem expMap_eq (p v : R2) : v ∈ expDomain 𝓘(ℝ, R2) p ∧ expMap 𝓘(ℝ, R2) p v = p + v := by
  obtain ⟨h1, h2⟩ := PythagoreanPaper.expMap_eq (isGeodesicFrom_line p v) (subset_univ _)
  exact ⟨h1, by rw [h2, one_smul]⟩

/-- **Every ball of `T_p ℝ²` is a normal ball.** -/
theorem isNormalBall (p : R2) {ρ : ℝ} (hρ : 0 < ρ) : IsNormalBall 𝓘(ℝ, R2) p ρ :=
  isNormalBall_of_constCurvature finrank_euclideanSpace_fin hasConstSectionalCurvature_euclidean
    hρ (fun h ↦ absurd h (lt_irrefl 0)) (fun v _ ↦ (expMap_eq p v).1) fun v _ w _ h ↦ by
      rw [(expMap_eq p v).2, (expMap_eq p w).2] at h
      exact add_left_cancel h

/-- The image of the ball `B_ρ` of `T_p ℝ²` under `exp_p` is the open ball of radius `ρ`
around `p`. -/
lemma mem_expMap_image_iff (p x : R2) (ρ : ℝ) :
    x ∈ expMap 𝓘(ℝ, R2) p '' tangentBall 𝓘(ℝ, R2) p ρ ↔ dist x p < ρ := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [(expMap_eq p v).2, dist_eq_norm, add_sub_cancel_left]
    have h : ‖(show TangentSpace 𝓘(ℝ, R2) p from v)‖ < ρ := hv
    rwa [norm_tangentSpace_vectorSpace] at h
  · intro h
    refine ⟨x - p, ?_, by rw [(expMap_eq p _).2, add_sub_cancel]⟩
    show ‖(show TangentSpace 𝓘(ℝ, R2) p from x - p)‖ < ρ
    rw [norm_tangentSpace_vectorSpace]
    rwa [dist_eq_norm] at h

/-- A geodesic segment stays in a bounded part of the plane. -/
lemma exists_bound_segment {γ : ℝ → R2} {x y : R2} {L : ℝ}
    (h : IsGeodesicSegment 𝓘(ℝ, R2) γ x y L) (p : R2) :
    ∃ R, ∀ t ∈ Icc 0 L, dist (γ t) p ≤ R := by
  have hc : ContinuousOn γ (Icc 0 L) := fun t ht ↦
    (h.mdifferentiableAt ht).continuousAt.continuousWithinAt
  obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.subset_closedBall p
  exact ⟨R, fun t ht ↦ hR ⟨t, ht, rfl⟩⟩

variable (T : GeodesicTriangle 𝓘(ℝ, R2) R2)

/-- Some normal ball around `X` contains the three sides of any geodesic triangle of `ℝ²`. -/
theorem sidesInNormalBallAt (X : R2) : T.SidesInNormalBallAt X := by
  obtain ⟨Ra, hRa⟩ := exists_bound_segment T.segment_a X
  obtain ⟨Rb, hRb⟩ := exists_bound_segment T.segment_b X
  obtain ⟨Rc, hRc⟩ := exists_bound_segment T.segment_c X
  set ρ := max (max Ra Rb) Rc + 1 with hρ_def
  have hρa : ∀ t ∈ Icc 0 T.a, dist (T.σa t) X < ρ := fun t ht ↦ by
    have := hRa t ht
    have : Ra ≤ max (max Ra Rb) Rc := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hρb : ∀ t ∈ Icc 0 T.b, dist (T.σb t) X < ρ := fun t ht ↦ by
    have := hRb t ht
    have : Rb ≤ max (max Ra Rb) Rc := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hρc : ∀ t ∈ Icc 0 T.c, dist (T.σc t) X < ρ := fun t ht ↦ by
    have := hRc t ht
    have : Rc ≤ max (max Ra Rb) Rc := le_max_right _ _
    linarith
  have hρ : 0 < ρ := lt_of_le_of_lt dist_nonneg (hρa 0 ⟨le_rfl, T.segment_a.pos.le⟩)
  exact ⟨ρ, isNormalBall X hρ, fun t ht ↦ (mem_expMap_image_iff X _ ρ).2 (hρa t ht),
    fun t ht ↦ (mem_expMap_image_iff X _ ρ).2 (hρb t ht),
    fun t ht ↦ (mem_expMap_image_iff X _ ρ).2 (hρc t ht)⟩

/-- **Every geodesic triangle of the Euclidean plane satisfies the technical condition.** -/
theorem sidesInNormalBalls : T.SidesInNormalBalls :=
  ⟨sidesInNormalBallAt T T.pA, sidesInNormalBallAt T T.pB, sidesInNormalBallAt T T.pC⟩

end EuclideanPlane

end PythagoreanPaper
