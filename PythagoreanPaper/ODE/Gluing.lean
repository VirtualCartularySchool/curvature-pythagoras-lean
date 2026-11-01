import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# From local to global solutions on intervals

Parallel transport, Jacobi fields and linear ordinary differential equations along a curve are
solved locally (in a chart, or for a short time) and then continued along the whole interval of
definition. This file isolates the continuation argument.

A *solution* of a family of conditions `Q t σ` (for fields `σ : (t : ℝ) → β t`) on a set `J` is a
field with `Q t σ` for every `t ∈ J`. If

* `Q t σ` depends only on the germ of `σ` at `t` (`GermLocal Q`),
* solutions are locally unique (`LocallyUniqueOn Q U`), and
* every point of `U` has an open interval around it on which every initial value is attained by
  a solution (`LocallySolvableOn Q U`),

then on an open interval `U` solutions are unique (`eqOn_of_locallyUniqueOn`) and every initial
value is attained by a solution defined on the whole of `U` (`exists_of_locallySolvableOn`).
-/

open Set Filter
open scoped Topology

namespace PythagoreanPaper

variable {β : ℝ → Type*}

/-- `Q t σ` depends only on the germ of `σ` at `t`. -/
def GermLocal (Q : (t : ℝ) → ((s : ℝ) → β s) → Prop) : Prop :=
  ∀ t (σ τ : (s : ℝ) → β s), (∀ᶠ s in 𝓝 t, σ s = τ s) → Q t σ → Q t τ

/-- Local uniqueness of solutions: around every point of `U` there is a neighbourhood `N` such that
two solutions on a preconnected set `K ⊆ N` which agree at one point of `K` agree on `K`. -/
def LocallyUniqueOn (Q : (t : ℝ) → ((s : ℝ) → β s) → Prop) (U : Set ℝ) : Prop :=
  ∀ t₁ ∈ U, ∃ N ∈ 𝓝 t₁, ∀ K ⊆ N, IsPreconnected K → ∀ σ τ : (s : ℝ) → β s,
    (∀ t ∈ K, Q t σ) → (∀ t ∈ K, Q t τ) → ∀ s ∈ K, σ s = τ s → ∀ t ∈ K, σ t = τ t

/-- Local solvability: every point of `U` lies in an open interval `J ⊆ U` such that every initial
value at every point of `J` is attained by a solution on `J`. -/
def LocallySolvableOn (Q : (t : ℝ) → ((s : ℝ) → β s) → Prop) (U : Set ℝ) : Prop :=
  ∀ t₁ ∈ U, ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ t₁ ∈ J ∧ J ⊆ U ∧
    ∀ s ∈ J, ∀ v : β s, ∃ σ : (t : ℝ) → β t, (∀ t ∈ J, Q t σ) ∧ σ s = v

variable {Q : (t : ℝ) → ((s : ℝ) → β s) → Prop} {U : Set ℝ}

/-- **Uniqueness**: two solutions on a preconnected subset `W ⊆ U` which agree at one point agree on
`W`. -/
theorem eqOn_of_locallyUniqueOn (hQ : LocallyUniqueOn Q U) {W : Set ℝ} (hWU : W ⊆ U)
    (hW : IsPreconnected W) {σ τ : (s : ℝ) → β s} (hσ : ∀ t ∈ W, Q t σ)
    (hτ : ∀ t ∈ W, Q t τ) {s : ℝ} (hs : s ∈ W) (hst : σ s = τ s) :
    ∀ t ∈ W, σ t = τ t := by
  have hW' : W.OrdConnected := isPreconnected_iff_ordConnected.1 hW
  intro t ht
  refine (hW.induction₂' (fun x y ↦ (σ x = τ x ↔ σ y = τ y)) (fun x hx ↦ ?_)
    (fun x y z _ _ _ hxy hyz ↦ hxy.trans hyz) hs ht).1 hst
  obtain ⟨N, hN, hNuniq⟩ := hQ x (hWU hx)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hε), self_mem_nhdsWithin]
    with y hy hyW
  have hK : uIcc x y ⊆ N := by
    have hball : (Metric.ball x ε).OrdConnected := by
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    exact (hball.uIcc_subset (Metric.mem_ball_self hε) hy).trans hεN
  have hKW : uIcc x y ⊆ W := hW'.uIcc_subset hx hyW
  have hu := hNuniq (uIcc x y) hK isPreconnected_uIcc σ τ (fun t ht ↦ hσ t (hKW ht))
    (fun t ht ↦ hτ t (hKW ht))
  exact ⟨⟨fun h ↦ hu x left_mem_uIcc h y right_mem_uIcc,
    fun h ↦ hu y right_mem_uIcc h x left_mem_uIcc⟩,
    ⟨fun h ↦ hu y right_mem_uIcc h x left_mem_uIcc,
    fun h ↦ hu x left_mem_uIcc h y right_mem_uIcc⟩⟩

/-- Gluing two solutions on open intervals which share a point at which they agree. -/
theorem exists_glue (hQ : GermLocal Q) (hu : LocallyUniqueOn Q U) {J J₁ : Set ℝ}
    (hJ : IsOpen J) (hJ' : IsPreconnected J) (hJU : J ⊆ U)
    (hJ₁ : IsOpen J₁) (hJ₁' : IsPreconnected J₁)
    {σ σ₁ : (t : ℝ) → β t} (hσ : ∀ t ∈ J, Q t σ) (hσ₁ : ∀ t ∈ J₁, Q t σ₁) {x : ℝ}
    (hxJ : x ∈ J) (hxJ₁ : x ∈ J₁) (hx : σ x = σ₁ x) :
    ∃ σ' : (t : ℝ) → β t, (∀ t ∈ J ∪ J₁, Q t σ') ∧ ∀ t ∈ J, σ' t = σ t := by
  classical
  have hagree : ∀ t ∈ J ∩ J₁, σ t = σ₁ t :=
    eqOn_of_locallyUniqueOn hu (inter_subset_left.trans hJU)
      (isPreconnected_iff_ordConnected.2
        ((isPreconnected_iff_ordConnected.1 hJ').inter (isPreconnected_iff_ordConnected.1 hJ₁')))
      (fun t ht ↦ hσ t ht.1) (fun t ht ↦ hσ₁ t ht.2) ⟨hxJ, hxJ₁⟩ hx
  let σ' : (t : ℝ) → β t := fun t ↦ if t ∈ J then σ t else σ₁ t
  have h1 : ∀ t ∈ J, σ' t = σ t := fun t ht ↦ by simp [σ', ht]
  have h2 : ∀ t ∈ J₁, σ' t = σ₁ t := fun t ht ↦ by
    by_cases htJ : t ∈ J
    · simp [σ', htJ, hagree t ⟨htJ, ht⟩]
    · simp [σ', htJ]
  refine ⟨σ', fun t ht ↦ ?_, h1⟩
  rcases ht with ht | ht
  · refine hQ t σ σ' ?_ (hσ t ht)
    filter_upwards [hJ.mem_nhds ht] with s hs using (h1 s hs).symm
  · refine hQ t σ₁ σ' ?_ (hσ₁ t ht)
    filter_upwards [hJ₁.mem_nhds ht] with s hs using (h2 s hs).symm

/-- **Existence**: on an open interval `U`, every initial value is attained by a solution on `U`. -/
theorem exists_of_locallySolvableOn (hQ : GermLocal Q) (hu : LocallyUniqueOn Q U)
    (he : LocallySolvableOn Q U) (hU' : IsPreconnected U) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    (v : β t₀) :
    ∃ σ : (t : ℝ) → β t, (∀ t ∈ U, Q t σ) ∧ σ t₀ = v := by
  classical
  -- `A t`: there is a solution with initial value `v` on an open interval containing `[t₀, t]`
  let A : ℝ → Prop := fun t ↦ ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ J ⊆ U ∧
    uIcc t₀ t ⊆ J ∧ ∃ σ : (t : ℝ) → β t, (∀ t ∈ J, Q t σ) ∧ σ t₀ = v
  -- extending `A` to the local solvability interval of a point
  have step : ∀ x ∈ U, ∃ J₁ : Set ℝ, IsOpen J₁ ∧ x ∈ J₁ ∧ J₁ ⊆ U ∧
      ∀ y ∈ J₁, ∀ z ∈ J₁, A z → A y := by
    intro x hx
    obtain ⟨J₁, hJ₁, hJ₁', hxJ₁, hJ₁U, hsol⟩ := he x hx
    refine ⟨J₁, hJ₁, hxJ₁, hJ₁U, fun y hy z hz hAz ↦ ?_⟩
    obtain ⟨J, hJ, hJ', hJU, hzJ, σ, hσ, hσ₀⟩ := hAz
    have hz' : z ∈ J := hzJ right_mem_uIcc
    obtain ⟨σ₁, hσ₁, hσ₁z⟩ := hsol z hz (σ z)
    obtain ⟨σ', hσ', hσ'J⟩ :=
      exists_glue hQ hu hJ hJ' hJU hJ₁ hJ₁' hσ hσ₁ hz' hz hσ₁z.symm
    refine ⟨J ∪ J₁, hJ.union hJ₁, hJ'.union z hz' hz hJ₁', union_subset hJU hJ₁U, ?_,
      σ', hσ', ?_⟩
    · intro w hw
      rcases Set.uIcc_subset_uIcc_union_uIcc hw with hw | hw
      · exact Or.inl (hzJ hw)
      · exact Or.inr ((isPreconnected_iff_ordConnected.1 hJ₁').uIcc_subset hz hy hw)
    · rw [hσ'J t₀ (hzJ left_mem_uIcc), hσ₀]
  have hA : ∀ t ∈ U, A t := by
    intro t ht
    refine hU'.induction₂' (fun x y ↦ (A x ↔ A y)) (fun x hx ↦ ?_)
      (fun x y z _ _ _ hxy hyz ↦ hxy.trans hyz) ht₀ ht |>.1 ?_
    · obtain ⟨J₁, hJ₁, hxJ₁, -, hJ₁A⟩ := step x hx
      filter_upwards [nhdsWithin_le_nhds (hJ₁.mem_nhds hxJ₁)] with y hy
      exact ⟨⟨hJ₁A y hy x hxJ₁, hJ₁A x hxJ₁ y hy⟩, ⟨hJ₁A x hxJ₁ y hy, hJ₁A y hy x hxJ₁⟩⟩
    · obtain ⟨J₀, hJ₀, hJ₀', ht₀J₀, hJ₀U, hsol⟩ := he t₀ ht₀
      obtain ⟨σ₀, hσ₀, hσ₀t₀⟩ := hsol t₀ ht₀J₀ v
      exact ⟨J₀, hJ₀, hJ₀', hJ₀U, by simpa using ht₀J₀, σ₀, hσ₀, hσ₀t₀⟩
  have hne : Nonempty ((t : ℝ) → β t) := by
    obtain ⟨J₀, -, -, ht₀J₀, -, hsol⟩ := he t₀ ht₀
    obtain ⟨σ₀, -, -⟩ := hsol t₀ ht₀J₀ v
    exact ⟨σ₀⟩
  choose! J hJ hJ' hJU hJt σt hσt hσt₀ using hA
  refine ⟨fun t ↦ σt t t, fun t ht ↦ ?_, hσt₀ t₀ ht₀⟩
  refine hQ t (σt t) _ ?_ (hσt t ht t (hJt t ht right_mem_uIcc))
  filter_upwards [(hJ t ht).mem_nhds (hJt t ht right_mem_uIcc)] with s hs
  have hsU : s ∈ U := hJU t ht hs
  -- `σt s` and `σt t` are solutions on `J s ∩ J t ∋ t₀` with the same value at `t₀`
  refine (eqOn_of_locallyUniqueOn hu (inter_subset_left.trans (hJU s hsU))
    (isPreconnected_iff_ordConnected.2 ((isPreconnected_iff_ordConnected.1 (hJ' s hsU)).inter
      (isPreconnected_iff_ordConnected.1 (hJ' t ht))))
    (fun r hr ↦ hσt s hsU r hr.1) (fun r hr ↦ hσt t ht r hr.2)
    ⟨hJt s hsU left_mem_uIcc, hJt t ht left_mem_uIcc⟩
    ((hσt₀ s hsU).trans (hσt₀ t ht).symm) s ⟨hJt s hsU right_mem_uIcc, hs⟩).symm

end PythagoreanPaper
