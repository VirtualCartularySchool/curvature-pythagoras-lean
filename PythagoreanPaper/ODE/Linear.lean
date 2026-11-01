import PythagoreanPaper.ODE.Gluing
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Linear ordinary differential equations on an interval

For continuous coefficients `A : ℝ → (F →L[ℝ] F)` and `b : ℝ → F` on an open interval `U`, the
linear equation `x' = A t (x t) + b t` has, for every initial value, a solution defined on the
whole of `U` (`linearODE_exists`), and solutions with the same value at one point agree on `U`
(`linearODE_unique`).

Mathlib provides the local existence theorem (Picard–Lindelöf) and uniqueness (via Gronwall's
inequality). The point of this file is global existence on the whole interval: for a linear
equation the local existence time near a point can be chosen independently of the initial value
(`locallySolvableOn_linearODESol`), and the local solutions are then continued along `U` by
`exists_of_locallySolvableOn` (`PythagoreanPaper.ODE.Gluing`).

This is used for parallel transport and for Jacobi fields along a curve (manuscript §4).
-/

open Set Filter Metric
open scoped Topology NNReal

namespace PythagoreanPaper

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `x` solves `x' = A t (x t) + b t` at time `t`. -/
def LinearODESol (A : ℝ → F →L[ℝ] F) (b : ℝ → F) (t : ℝ) (x : ℝ → F) : Prop :=
  HasDerivAt x (A t (x t) + b t) t

variable {A : ℝ → F →L[ℝ] F} {b : ℝ → F} {U : Set ℝ}

lemma germLocal_linearODESol : GermLocal (β := fun _ ↦ F) (LinearODESol A b) := by
  intro t x y hxy hx
  have hval : x t = y t := hxy.self_of_nhds
  unfold LinearODESol at *
  rw [← hval]
  exact hx.congr_of_eventuallyEq (hxy.mono fun s hs ↦ hs.symm)

/-- A closed interval around a point of an open set, inside the set. -/
lemma exists_Icc_subset_of_isOpen (hU : IsOpen U) {t₁ : ℝ} (ht₁ : t₁ ∈ U) :
    ∃ δ > 0, Icc (t₁ - δ) (t₁ + δ) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU t₁ ht₁
  refine ⟨ε / 2, by positivity, fun t ht ↦ hεU ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- On a set where `‖A t‖ ≤ K`, the right-hand side is `K`-Lipschitz in `x`. -/
lemma lipschitzWith_linear {K : ℝ} (hK : 0 ≤ K) {t : ℝ} (hAt : ‖A t‖ ≤ K) :
    LipschitzWith (Real.toNNReal K) (fun x ↦ A t x + b t) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal K hK]
  exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hAt (norm_nonneg _))

/-- Local uniqueness for the linear equation. -/
lemma locallyUniqueOn_linearODESol (hU : IsOpen U) (hA : ContinuousOn A U) :
    LocallyUniqueOn (β := fun _ ↦ F) (LinearODESol A b) U := by
  intro t₁ ht₁
  obtain ⟨δ, hδ, hδU⟩ := exists_Icc_subset_of_isOpen hU ht₁
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.mono hδU)
  set K := max K₀ 0
  have hK : ∀ t ∈ Icc (t₁ - δ) (t₁ + δ), ‖A t‖ ≤ K := fun t ht ↦ (hK₀ t ht).trans (le_max_left _ _)
  refine ⟨Icc (t₁ - δ) (t₁ + δ), Icc_mem_nhds (by linarith) (by linarith),
    fun S hSN hS x y hx hy s hs hxy t ht ↦ ?_⟩
  have hSo : S.OrdConnected := isPreconnected_iff_ordConnected.1 hS
  have hlip : ∀ τ ∈ S, LipschitzOnWith (Real.toNNReal K) (fun z ↦ A τ z + b τ) univ :=
    fun τ hτ ↦ (lipschitzWith_linear (le_max_right _ _) (hK τ (hSN hτ))).lipschitzOnWith
  have hcont : ∀ z : ℝ → F, (∀ τ ∈ S, LinearODESol A b τ z) → ∀ p q, p ∈ S → q ∈ S →
      ContinuousOn z (Icc p q) := fun z hz p q hp hq ↦ fun τ hτ ↦
    (hz τ (hSo.out hp hq hτ)).continuousAt.continuousWithinAt
  rcases le_total s t with hst | hts
  · exact ODE_solution_unique_of_mem_Icc_right (v := fun τ z ↦ A τ z + b τ) (s := fun _ ↦ univ)
      (fun τ hτ ↦ hlip τ (hSo.out hs ht (Ico_subset_Icc_self hτ)))
      (hcont x hx s t hs ht)
      (fun τ hτ ↦ (hx τ (hSo.out hs ht (Ico_subset_Icc_self hτ))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (hcont y hy s t hs ht)
      (fun τ hτ ↦ (hy τ (hSo.out hs ht (Ico_subset_Icc_self hτ))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) hxy ⟨hst, le_rfl⟩
  · exact ODE_solution_unique_of_mem_Icc_left (v := fun τ z ↦ A τ z + b τ) (s := fun _ ↦ univ)
      (fun τ hτ ↦ hlip τ (hSo.out ht hs (Ioc_subset_Icc_self hτ)))
      (hcont x hx t s ht hs)
      (fun τ hτ ↦ (hx τ (hSo.out ht hs (Ioc_subset_Icc_self hτ))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (hcont y hy t s ht hs)
      (fun τ hτ ↦ (hy τ (hSo.out ht hs (Ioc_subset_Icc_self hτ))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) hxy ⟨le_rfl, hts⟩

variable [CompleteSpace F]

/-- Local existence for the linear equation, with an existence interval independent of the
initial value. -/
lemma locallySolvableOn_linearODESol (hU : IsOpen U) (hA : ContinuousOn A U)
    (hb : ContinuousOn b U) :
    LocallySolvableOn (β := fun _ ↦ F) (LinearODESol A b) U := by
  intro t₁ ht₁
  obtain ⟨δ, hδ, hδU⟩ := exists_Icc_subset_of_isOpen hU ht₁
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.mono hδU)
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hb.mono hδU)
  set M := max M₀ 0
  set B := max B₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  set h := min δ (1 / (4 * (M + 1))) with hh_def
  have hh0 : 0 < h := lt_min hδ (by positivity)
  have hhδ : h ≤ δ := min_le_left _ _
  have hhM : h * (4 * (M + 1)) ≤ 1 := by
    have : h ≤ 1 / (4 * (M + 1)) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  have hIcc : Icc (t₁ - h) (t₁ + h) ⊆ Icc (t₁ - δ) (t₁ + δ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hAb : ∀ t ∈ Icc (t₁ - h) (t₁ + h), ‖A t‖ ≤ M := fun t ht ↦
    (hM₀ t (hIcc ht)).trans (le_max_left _ _)
  have hbb : ∀ t ∈ Icc (t₁ - h) (t₁ + h), ‖b t‖ ≤ B := fun t ht ↦
    (hB₀ t (hIcc ht)).trans (le_max_left _ _)
  refine ⟨Ioo (t₁ - h) (t₁ + h), isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, by linarith⟩,
    Ioo_subset_Icc_self.trans (hIcc.trans hδU), fun s hs v ↦ ?_⟩
  have hs' : s ∈ Icc (t₁ - h) (t₁ + h) := Ioo_subset_Icc_self hs
  let a : ℝ≥0 := ⟨‖v‖ + B + 1, by positivity⟩
  let L : ℝ≥0 := ⟨M * (2 * ‖v‖ + B + 1) + B, by positivity⟩
  have hPL : IsPicardLindelof (fun t x ↦ A t x + b t) (tmin := t₁ - h) (tmax := t₁ + h)
      ⟨s, hs'⟩ v a 0 L (Real.toNNReal M) :=
    { lipschitzOnWith := fun t ht ↦ (lipschitzWith_linear hM0 (hAb t ht)).lipschitzOnWith
      continuousOn := fun x _ ↦
        (((hA.mono (hIcc.trans hδU)).clm_apply continuousOn_const).add
          (hb.mono (hIcc.trans hδU)))
      norm_le := fun t ht x hx ↦ by
        have hx' : ‖x‖ ≤ ‖v‖ + (‖v‖ + B + 1) := by
          have := norm_le_norm_add_norm_sub' x v
          rw [mem_closedBall, dist_eq_norm] at hx
          have hx2 : ‖x - v‖ ≤ ‖v‖ + B + 1 := hx
          linarith
        calc ‖A t x + b t‖ ≤ ‖A t x‖ + ‖b t‖ := norm_add_le _ _
          _ ≤ ‖A t‖ * ‖x‖ + B := add_le_add ((A t).le_opNorm x) (hbb t ht)
          _ ≤ M * (‖v‖ + (‖v‖ + B + 1)) + B := by
            gcongr
            · exact hAb t ht
          _ = (L : ℝ) := by
            show _ = M * (2 * ‖v‖ + B + 1) + B
            ring
      mul_max_le := by
        have hmax : max (t₁ + h - s) (s - (t₁ - h)) ≤ 2 * h :=
          max_le (by linarith [hs.1]) (by linarith [hs.2])
        rw [NNReal.coe_zero, sub_zero]
        show (M * (2 * ‖v‖ + B + 1) + B) * max (t₁ + h - s) (s - (t₁ - h)) ≤ ‖v‖ + B + 1
        calc (M * (2 * ‖v‖ + B + 1) + B) * max (t₁ + h - s) (s - (t₁ - h))
            ≤ (M * (2 * ‖v‖ + B + 1) + B) * (2 * h) := by gcongr
          _ ≤ ((M + 1) * (2 * ‖v‖ + B + 1)) * (2 * h) := by gcongr; nlinarith [norm_nonneg v]
          _ = (2 * ‖v‖ + B + 1) * (h * (4 * (M + 1))) / 2 := by ring
          _ ≤ (2 * ‖v‖ + B + 1) * 1 / 2 := by gcongr
          _ ≤ ‖v‖ + B + 1 := by linarith [norm_nonneg v] }
  obtain ⟨x, hx₀, hx⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨x, fun t ht ↦ (hx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2), hx₀⟩

/-- **Global existence** for linear equations with continuous coefficients on an open interval. -/
theorem linearODE_exists (hU : IsOpen U) (hU' : IsPreconnected U) (hA : ContinuousOn A U)
    (hb : ContinuousOn b U) {t₀ : ℝ} (ht₀ : t₀ ∈ U) (x₀ : F) :
    ∃ x : ℝ → F, x t₀ = x₀ ∧ ∀ t ∈ U, HasDerivAt x (A t (x t) + b t) t := by
  obtain ⟨x, hx, hx₀⟩ := exists_of_locallySolvableOn (β := fun _ ↦ F) germLocal_linearODESol
    (locallyUniqueOn_linearODESol hU hA) (locallySolvableOn_linearODESol hU hA hb) hU' ht₀ x₀
  exact ⟨x, hx₀, hx⟩

omit [CompleteSpace F] in
/-- **Uniqueness** for linear equations with continuous coefficients on an open interval. -/
theorem linearODE_unique (hU : IsOpen U) (hU' : IsPreconnected U) (hA : ContinuousOn A U)
    {x y : ℝ → F} (hx : ∀ t ∈ U, HasDerivAt x (A t (x t) + b t) t)
    (hy : ∀ t ∈ U, HasDerivAt y (A t (y t) + b t) t) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    (h : x t₀ = y t₀) : ∀ t ∈ U, x t = y t :=
  eqOn_of_locallyUniqueOn (β := fun _ ↦ F) (locallyUniqueOn_linearODESol hU hA) subset_rfl hU'
    hx hy ht₀ h

end PythagoreanPaper
