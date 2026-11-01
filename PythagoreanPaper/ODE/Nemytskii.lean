import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Composition operators on spaces of continuous functions

Let `X` be a compact space and `g : F → G` a `C^∞` map between real normed spaces, `F`
finite-dimensional. On the Banach space `C(X, F)` (sup norm), the composition operator
`x ↦ g ∘ x` is `C^∞` (`contDiff_compLeft`), with derivative `h ↦ (t ↦ Dg (x t) (h t))`
(`hasFDerivAt_compLeft`).

This is the analytic input for the smooth dependence of solutions of ordinary differential
equations on their initial values (`PythagoreanPaper.ODE.SmoothFlow`).
-/

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace PythagoreanPaper

universe u w

variable {X : Type w} [TopologicalSpace X] [CompactSpace X]

section PtApply

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

variable (X F G) in
/-- Pointwise application `(A, h) ↦ (t ↦ A t (h t))`, a continuous bilinear map. -/
def ptApply : C(X, F →L[ℝ] G) →L[ℝ] C(X, F) →L[ℝ] C(X, G) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (A : C(X, F →L[ℝ] G)) (h : C(X, F)) ↦
        (⟨fun t ↦ A t (h t), A.continuous.clm_apply h.continuous⟩ : C(X, G)))
      (fun A₁ A₂ h ↦ by ext t; simp)
      (fun c A h ↦ by ext t; simp)
      (fun A h₁ h₂ ↦ by ext t; simp)
      (fun c A h ↦ by ext t; simp))
    1 (fun A h ↦ by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun t ↦ ?_
      calc ‖A t (h t)‖ ≤ ‖A t‖ * ‖h t‖ := (A t).le_opNorm (h t)
        _ ≤ ‖A‖ * ‖h‖ := mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t)
          (norm_nonneg _) ((norm_nonneg _).trans (A.norm_coe_le_norm t)))

@[simp] lemma ptApply_apply (A : C(X, F →L[ℝ] G)) (h : C(X, F)) (t : X) :
    ptApply X F G A h t = A t (h t) := rfl

omit [CompactSpace X] [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- Composition on the left with a continuous map. -/
def compLeft (g : F → G) (hg : Continuous g) (x : C(X, F)) : C(X, G) :=
  ⟨g ∘ x, hg.comp x.continuous⟩

omit [CompactSpace X] [NormedSpace ℝ F] [NormedSpace ℝ G] in
@[simp] lemma compLeft_apply (g : F → G) (hg : Continuous g) (x : C(X, F)) (t : X) :
    compLeft g hg x t = g (x t) := rfl

end PtApply

section Derivative

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Derivative of a composition operator**: for `g` of class `C¹`, the derivative of
`x ↦ g ∘ x` on `C(X, F)` at `x` is `h ↦ (t ↦ Dg (x t) (h t))`. -/
theorem hasFDerivAt_compLeft {g : F → G} (hg : ContDiff ℝ 1 g) (x : C(X, F)) :
    HasFDerivAt (compLeft (X := X) g hg.continuous)
      (ptApply X F G (compLeft (fderiv ℝ g) (hg.continuous_fderiv one_ne_zero) x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hK' : IsCompact (cthickening 1 (range x)) := (isCompact_range x.continuous).cthickening
  have hDg : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hDg.continuousOn) c hc
  filter_upwards [Metric.ball_mem_nhds (0 : C(X, F)) (lt_min hδ one_pos)] with h hh
  rw [mem_ball_zero_iff] at hh
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t ↦ ?_
  show ‖g (x t + h t) - g (x t) - fderiv ℝ g (x t) (h t)‖ ≤ c * ‖h‖
  have hht : ‖h t‖ < min δ 1 := (h.norm_coe_le_norm t).trans_lt hh
  have hderiv : ∀ z ∈ ball (x t) (min δ 1), HasFDerivWithinAt
      (fun z ↦ g z - fderiv ℝ g (x t) z) (fderiv ℝ g z - fderiv ℝ g (x t))
      (ball (x t) (min δ 1)) z := fun z _ ↦
    (((hg.differentiable one_ne_zero) z).hasFDerivAt.sub (fderiv ℝ g (x t)).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ ball (x t) (min δ 1), ‖fderiv ℝ g z - fderiv ℝ g (x t)‖ ≤ c := by
    intro z hz
    rw [mem_ball] at hz
    have hz1 : z ∈ cthickening 1 (range x) :=
      mem_cthickening_of_dist_le z (x t) 1 _ (mem_range_self t)
        (le_of_lt (hz.trans_le (min_le_right _ _)))
    have hx1 : x t ∈ cthickening 1 (range x) := self_subset_cthickening _ (mem_range_self t)
    rw [← dist_eq_norm]
    exact le_of_lt (hunif z hz1 (x t) hx1 (hz.trans_le (min_le_left _ _)))
  have key := (convex_ball (x t) (min δ 1)).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv
    hbound (mem_ball_self (lt_min hδ one_pos)) (show x t + h t ∈ ball (x t) (min δ 1) by
      rwa [mem_ball, dist_eq_norm, add_sub_cancel_left])
  rw [map_add, add_sub_cancel_left] at key
  calc ‖g (x t + h t) - g (x t) - fderiv ℝ g (x t) (h t)‖
      = ‖g (x t + h t) - (fderiv ℝ g (x t) (x t) + fderiv ℝ g (x t) (h t)) -
          (g (x t) - fderiv ℝ g (x t) (x t))‖ := by congr 1; abel
    _ ≤ c * ‖h t‖ := key
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hc.le

/-- A composition operator by a `C¹` map is continuous. -/
lemma continuous_compLeft {g : F → G} (hg : ContDiff ℝ 1 g) :
    Continuous (compLeft (X := X) g hg.continuous) :=
  continuous_iff_continuousAt.2 fun x ↦ (hasFDerivAt_compLeft hg x).continuousAt

end Derivative

section Smooth

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A composition operator by a `C^∞` map is `C^n` for every `n`. -/
theorem contDiff_compLeft_nat (n : ℕ) : ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : F → G} (hg : ContDiff ℝ ∞ g), ContDiff ℝ n (compLeft (X := X) g hg.continuous) := by
  induction n with
  | zero =>
    intro G _ _ g hg
    exact contDiff_zero.2 (continuous_compLeft (hg.of_le (by simp)))
  | succ n ih =>
    intro G _ _ g hg
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x ↦ (hasFDerivAt_compLeft hg1 x).differentiableAt, by simp, ?_⟩
    have hfd : fderiv ℝ (compLeft (X := X) g hg.continuous) =
        fun x ↦ ptApply X F G (compLeft (fderiv ℝ g) (hg1.continuous_fderiv one_ne_zero) x) :=
      funext fun x ↦ (hasFDerivAt_compLeft hg1 x).fderiv
    rw [hfd]
    exact (ptApply X F G).contDiff.comp (ih (hg.fderiv_right (by simp)))

/-- **A composition operator by a `C^∞` map is `C^∞`.** -/
theorem contDiff_compLeft {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (compLeft (X := X) g hg.continuous) :=
  contDiff_infty.2 fun n ↦ contDiff_compLeft_nat n hg

end Smooth

end PythagoreanPaper
