import PythagoreanPaper.ODE.Nemytskii
import PythagoreanPaper.ODE.Linear
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth dependence of solutions of ODEs on the initial value

Let `f : F → F` be a vector field on a finite-dimensional real normed space, `a ≤ b` and
`t₀ ∈ [a, b]`. On the Banach space `C([a, b], F)`, a continuous `x` solves `x' = f(x)` with
`x(t₀) = ξ` iff `Φ(ξ, x) = 0`, where `Φ(ξ, x) = x - ξ - ∫_{t₀}^t f(x(s)) ds` (`flowEqn`;
`hasDerivAt_of_flowEqn_eq_zero`, `flowEqn_restrict_eq_zero`).

For `f` of class `C^∞`, `Φ` is `C^∞` (the composition operator `x ↦ f ∘ x` is `C^∞` by
`PythagoreanPaper.ODE.Nemytskii`), and its partial derivative in `x` is
`h ↦ h - ∫_{t₀}^t Df(x(s)) h(s) ds`. This operator is invertible: it is injective by the
uniqueness of solutions of linear equations (`eq_of_integral_eq`) and surjective by their global
existence (`linearODE_exists`), hence an isomorphism by the open mapping theorem. The implicit
function theorem then shows that solutions depend smoothly on the initial value. For `f` with
compact support every initial value has a solution on `[a, b]`, and the solution map
`F → C([a, b], F)` is `C^∞` (`exists_contDiff_flow`).
-/

noncomputable section

open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff NNReal

namespace PythagoreanPaper

universe u

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

section Operators

variable (hab : a ≤ b)

omit [NormedSpace ℝ F] in
/-- A continuous function on `[a, b]`, extended to `ℝ` (constant outside `[a, b]`), is
continuous. -/
lemma continuous_IccExtend_continuousMap (y : C(Icc a b, F)) : Continuous (IccExtend hab y) :=
  y.continuous.Icc_extend'

omit [NormedSpace ℝ F] in
lemma IccExtend_continuousMap_apply (y : C(Icc a b, F)) (s : ℝ) :
    IccExtend hab y s = y (projIcc a b hab s) := rfl

omit [NormedSpace ℝ F] in
lemma norm_IccExtend_le (y : C(Icc a b, F)) (s : ℝ) : ‖IccExtend hab y s‖ ≤ ‖y‖ :=
  y.norm_coe_le_norm _

/-- The constant functions, as a continuous linear map `F → C([a, b], F)`. -/
def constCLM : F →L[ℝ] C(Icc a b, F) :=
  LinearMap.mkContinuous
    { toFun := fun ξ ↦ ContinuousMap.const _ ξ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun ξ ↦ by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun _ ↦ le_rfl)

@[simp] lemma constCLM_apply (ξ : F) (t : Icc a b) : constCLM (a := a) (b := b) ξ t = ξ := rfl

variable [CompleteSpace F]

/-- The integration operator `y ↦ (t ↦ ∫_{t₀}^t y)` on `C([a, b], F)`. -/
def intOp (t₀ : Icc a b) : C(Icc a b, F) →L[ℝ] C(Icc a b, F) :=
  LinearMap.mkContinuous
    { toFun := fun y ↦ ⟨fun t ↦ ∫ s in (t₀ : ℝ)..t, IccExtend hab y s,
        (continuous_iff_continuousAt.2 fun t ↦
          ((continuous_IccExtend_continuousMap hab y).integral_hasStrictDerivAt _
            t).hasDerivAt.continuousAt).comp continuous_subtype_val⟩
      map_add' := fun y z ↦ by
        ext t
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [← integral_add ((continuous_IccExtend_continuousMap hab y).intervalIntegrable _ _)
          ((continuous_IccExtend_continuousMap hab z).intervalIntegrable _ _)]
        rfl
      map_smul' := fun c y ↦ by
        ext t
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply]
        rw [← intervalIntegral.integral_smul]
        rfl }
    (b - a) (fun y ↦ by
      refine (ContinuousMap.norm_le _ (mul_nonneg (by linarith) (norm_nonneg _))).2 fun t ↦ ?_
      show ‖∫ s in (t₀ : ℝ)..t, IccExtend hab y s‖ ≤ (b - a) * ‖y‖
      have h1 : ∀ s ∈ Set.uIoc (t₀ : ℝ) t, ‖IccExtend hab y s‖ ≤ ‖y‖ := fun s _ ↦
        norm_IccExtend_le hab y s
      have ht : |(t : ℝ) - t₀| ≤ b - a :=
        abs_sub_le_iff.2 ⟨by linarith [t.2.2, t₀.2.1], by linarith [t.2.1, t₀.2.2]⟩
      calc ‖∫ s in (t₀ : ℝ)..t, IccExtend hab y s‖ ≤ ‖y‖ * |(t : ℝ) - t₀| :=
            norm_integral_le_of_norm_le_const h1
        _ ≤ ‖y‖ * (b - a) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
        _ = (b - a) * ‖y‖ := mul_comm _ _)

@[simp] lemma intOp_apply (t₀ : Icc a b) (y : C(Icc a b, F)) (t : Icc a b) :
    intOp hab t₀ y t = ∫ s in (t₀ : ℝ)..t, IccExtend hab y s := rfl

end Operators

section Uniqueness

variable [CompleteSpace F] (hab : a ≤ b) (t₀ : Icc a b)

/-- A continuous function satisfying an integral equation `z = ξ + ∫_{t₀} g` solves the
corresponding differential equation on `[a, b]`: it has the right one-sided derivatives. -/
lemma hasDerivWithinAt_of_eq_integral {ξ : F} {z g : C(Icc a b, F)}
    (hz : z = constCLM ξ + intOp hab t₀ g) :
    (∀ t ∈ Ico (t₀ : ℝ) b, HasDerivWithinAt (IccExtend hab z) (IccExtend hab g t) (Ici t) t) ∧
    (∀ t ∈ Ioc a (t₀ : ℝ), HasDerivWithinAt (IccExtend hab z) (IccExtend hab g t) (Iic t) t) ∧
    ∀ t ∈ Ioo a b, HasDerivAt (IccExtend hab z) (IccExtend hab g t) t := by
  set P : ℝ → F := fun t ↦ ξ + ∫ s in (t₀ : ℝ)..t, IccExtend hab g s with hP
  have hPd : ∀ t, HasDerivAt P (IccExtend hab g t) t := fun t ↦
    ((continuous_IccExtend_continuousMap hab g).integral_hasStrictDerivAt _ t).hasDerivAt.const_add ξ
  have hzP : ∀ t ∈ Icc a b, IccExtend hab z t = P t := by
    intro t ht
    rw [IccExtend_of_mem hab _ ht, hz]
    rfl
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have htI : t ∈ Icc a b := ⟨t₀.2.1.trans ht.1, ht.2.le⟩
    refine (hPd t).hasDerivWithinAt.congr_of_eventuallyEq ?_ (hzP t htI)
    filter_upwards [Icc_mem_nhdsGE ht.2] with s hs
    exact hzP s ⟨htI.1.trans hs.1, hs.2⟩
  · have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.trans t₀.2.2⟩
    refine (hPd t).hasDerivWithinAt.congr_of_eventuallyEq ?_ (hzP t htI)
    filter_upwards [Icc_mem_nhdsLE ht.1] with s hs
    exact hzP s ⟨hs.1, hs.2.trans htI.2⟩
  · refine (hPd t).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hzP s hs

/-- **Uniqueness for integral equations** `x = ξ + ∫_{t₀} V(s, x(s)) ds` with `V(s, ·)`
Lipschitz. -/
theorem eq_of_integral_eq {K : ℝ≥0} {V : Icc a b → F → F} (hV : ∀ t, LipschitzWith K (V t))
    {ξ : F} {x y gx gy : C(Icc a b, F)} (hgx : ∀ t, gx t = V t (x t))
    (hgy : ∀ t, gy t = V t (y t)) (hx : x = constCLM ξ + intOp hab t₀ gx)
    (hy : y = constCLM ξ + intOp hab t₀ gy) : x = y := by
  set v : ℝ → F → F := fun t ↦ V (projIcc a b hab t)
  have hv : ∀ t, LipschitzOnWith K (v t) univ := fun t ↦ (hV _).lipschitzOnWith
  have hgxv : ∀ t, IccExtend hab gx t = v t (IccExtend hab x t) := fun t ↦ hgx _
  have hgyv : ∀ t, IccExtend hab gy t = v t (IccExtend hab y t) := fun t ↦ hgy _
  obtain ⟨hx₁, hx₂, -⟩ := hasDerivWithinAt_of_eq_integral hab t₀ hx
  obtain ⟨hy₁, hy₂, -⟩ := hasDerivWithinAt_of_eq_integral hab t₀ hy
  have h₀ : IccExtend hab x t₀ = IccExtend hab y t₀ := by
    rw [IccExtend_val, IccExtend_val, hx, hy]
    simp
  have hcx := (continuous_IccExtend_continuousMap hab x).continuousOn (s := Icc a b)
  have hcy := (continuous_IccExtend_continuousMap hab y).continuousOn (s := Icc a b)
  have hR : EqOn (IccExtend hab x) (IccExtend hab y) (Icc (t₀ : ℝ) b) :=
    ODE_solution_unique_of_mem_Icc_right (v := v) (s := fun _ ↦ univ) (fun t _ ↦ hv t)
      (hcx.mono (Icc_subset_Icc_left t₀.2.1))
      (fun t ht ↦ (hgxv t) ▸ hx₁ t ht) (fun _ _ ↦ mem_univ _)
      (hcy.mono (Icc_subset_Icc_left t₀.2.1))
      (fun t ht ↦ (hgyv t) ▸ hy₁ t ht) (fun _ _ ↦ mem_univ _) h₀
  have hL : EqOn (IccExtend hab x) (IccExtend hab y) (Icc a (t₀ : ℝ)) :=
    ODE_solution_unique_of_mem_Icc_left (v := v) (s := fun _ ↦ univ) (fun t _ ↦ hv t)
      (hcx.mono (Icc_subset_Icc_right t₀.2.2))
      (fun t ht ↦ (hgxv t) ▸ hx₂ t ht) (fun _ _ ↦ mem_univ _)
      (hcy.mono (Icc_subset_Icc_right t₀.2.2))
      (fun t ht ↦ (hgyv t) ▸ hy₂ t ht) (fun _ _ ↦ mem_univ _) h₀
  ext t
  rw [← IccExtend_val hab x t, ← IccExtend_val hab y t]
  rcases le_total (t : ℝ) t₀ with h | h
  · exact hL ⟨t.2.1, h⟩
  · exact hR ⟨h, t.2.2⟩

end Uniqueness

section Flow

variable [CompleteSpace F] (hab : a ≤ b) (t₀ : Icc a b)

/-- The integral equation of `x' = f(x)`, `x(t₀) = ξ` on `[a, b]`:
`Φ(ξ, x) = x - ξ - ∫_{t₀}^t f(x(s)) ds`. -/
def flowEqn {f : F → F} (hf : Continuous f) (p : F × C(Icc a b, F)) : C(Icc a b, F) :=
  p.2 - constCLM p.1 - intOp hab t₀ (compLeft f hf p.2)

lemma flowEqn_eq_zero_iff {f : F → F} (hf : Continuous f) {ξ : F} {x : C(Icc a b, F)} :
    flowEqn hab t₀ hf (ξ, x) = 0 ↔ x = constCLM ξ + intOp hab t₀ (compLeft f hf x) := by
  unfold flowEqn
  rw [sub_sub, sub_eq_zero]

/-- A zero of `flowEqn` solves the differential equation, with the initial value `ξ` at `t₀`. -/
lemma hasDerivAt_of_flowEqn_eq_zero {f : F → F} (hf : Continuous f) {ξ : F}
    {x : C(Icc a b, F)} (h : flowEqn hab t₀ hf (ξ, x) = 0) :
    x t₀ = ξ ∧ ∀ t ∈ Ioo a b, HasDerivAt (IccExtend hab x) (f (IccExtend hab x t)) t := by
  rw [flowEqn_eq_zero_iff] at h
  refine ⟨?_, fun t ht ↦ (hasDerivWithinAt_of_eq_integral hab t₀ h).2.2 t ht⟩
  rw [h]
  simp

/-- The restriction to `[a, b]` of a solution of the differential equation is a zero of
`flowEqn`. -/
lemma flowEqn_restrict_eq_zero {f : F → F} (hf : Continuous f) {α : ℝ → F}
    (hα : ContinuousOn α (Icc a b)) (hα' : ∀ t ∈ Ioo a b, HasDerivAt α (f (α t)) t) :
    flowEqn hab t₀ hf (α t₀, ⟨fun t : Icc a b ↦ α t, hα.domRestrict⟩) = 0 := by
  rw [flowEqn_eq_zero_iff]
  ext t
  simp only [ContinuousMap.add_apply, constCLM_apply, intOp_apply]
  have hsub : uIcc (t₀ : ℝ) t ⊆ Icc a b := uIcc_subset_Icc t₀.2 t.2
  have hcongr : EqOn (IccExtend hab (compLeft f hf ⟨fun t : Icc a b ↦ α t, hα.domRestrict⟩))
      (fun s ↦ f (α s)) (uIcc (t₀ : ℝ) t) := by
    intro s hs
    rw [IccExtend_of_mem hab _ (hsub hs)]
    rfl
  rw [integral_congr hcongr, integral_eq_sub_of_hasDeriv_right (hα.mono hsub)
    (fun s hs ↦ (hα' s (Ioo_subset_Ioo (le_min t₀.2.1 t.2.1) (max_le t₀.2.2 t.2.2) hs)).hasDerivWithinAt)
    ((hf.comp_continuousOn (hα.mono hsub)).intervalIntegrable)]
  abel

variable [FiniteDimensional ℝ F]

/-- `flowEqn` is `C^∞` for a `C^∞` vector field. -/
lemma contDiff_flowEqn {f : F → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (flowEqn hab t₀ hf.continuous) := by
  unfold flowEqn
  exact (contDiff_snd.sub ((constCLM (a := a) (b := b)).contDiff.comp contDiff_fst)).sub
    ((intOp hab t₀).contDiff.comp ((contDiff_compLeft hf).comp contDiff_snd))

/-- The derivative of `flowEqn`. -/
lemma hasFDerivAt_flowEqn {f : F → F} (hf : ContDiff ℝ 1 f) (p : F × C(Icc a b, F)) :
    HasFDerivAt (flowEqn hab t₀ hf.continuous)
      (ContinuousLinearMap.snd ℝ F C(Icc a b, F) -
        (constCLM (a := a) (b := b)).comp (ContinuousLinearMap.fst ℝ F C(Icc a b, F)) -
        ((intOp hab t₀).comp (ptApply (Icc a b) F F
          (compLeft (fderiv ℝ f) (hf.continuous_fderiv one_ne_zero) p.2))).comp
          (ContinuousLinearMap.snd ℝ F C(Icc a b, F))) p := by
  unfold flowEqn
  exact (hasFDerivAt_snd.sub ((constCLM (a := a) (b := b)).hasFDerivAt.comp p hasFDerivAt_fst)).sub
    ((intOp hab t₀).hasFDerivAt.comp p ((hasFDerivAt_compLeft hf p.2).comp p hasFDerivAt_snd))

omit [FiniteDimensional ℝ F] in
/-- **The linearized operator `h ↦ h - ∫_{t₀} A h` is invertible**: it is injective by the
uniqueness and surjective by the global existence of solutions of linear equations. -/
theorem isInvertible_id_sub_intOp_ptApply (A : C(Icc a b, F →L[ℝ] F)) :
    (ContinuousLinearMap.id ℝ C(Icc a b, F) -
      (intOp hab t₀).comp (ptApply (Icc a b) F F A)).IsInvertible := by
  set L := ContinuousLinearMap.id ℝ C(Icc a b, F) - (intOp hab t₀).comp (ptApply (Icc a b) F F A)
  have hL : ∀ h, L h = h - intOp hab t₀ (ptApply (Icc a b) F F A h) := fun _ ↦ rfl
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    rw [hL, sub_eq_zero] at hh
    have hV : ∀ t : Icc a b, LipschitzWith ‖A‖₊ (fun z ↦ A t z) := fun t ↦
      (A t).lipschitzWith.weaken (by
        rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
        exact A.norm_coe_le_norm t)
    refine eq_of_integral_eq hab t₀ hV (ξ := 0) (gx := ptApply (Icc a b) F F A h)
      (gy := ptApply (Icc a b) F F A 0) (fun t ↦ rfl) (fun t ↦ rfl) ?_ ?_
    · rw [map_zero, zero_add]
      exact hh
    · rw [map_zero, map_zero, map_zero, zero_add]
  have hsurj : Function.Surjective L := by
    intro g
    set Aext : ℝ → F →L[ℝ] F := IccExtend hab A
    set bext : ℝ → F := fun t ↦ Aext t (IccExtend hab g t)
    have hAc : Continuous Aext := continuous_IccExtend_continuousMap hab A
    have hbc : Continuous bext := hAc.clm_apply (continuous_IccExtend_continuousMap hab g)
    obtain ⟨k, hk₀, hk⟩ := linearODE_exists (U := univ) isOpen_univ isPreconnected_univ
      hAc.continuousOn hbc.continuousOn (mem_univ (t₀ : ℝ)) (0 : F)
    have hkc : Continuous k := continuous_iff_continuousAt.2 fun t ↦
      (hk t (mem_univ t)).continuousAt
    set kc : C(Icc a b, F) := ⟨fun t ↦ k t, hkc.comp continuous_subtype_val⟩
    refine ⟨kc + g, ?_⟩
    suffices hkey : kc = intOp hab t₀ (ptApply (Icc a b) F F A (kc + g)) by
      rw [hL, ← hkey]
      abel
    ext t
    show k t = ∫ s in (t₀ : ℝ)..t, IccExtend hab (ptApply (Icc a b) F F A (kc + g)) s
    have hsub : uIcc (t₀ : ℝ) t ⊆ Icc a b := uIcc_subset_Icc t₀.2 t.2
    have hcongr : EqOn (IccExtend hab (ptApply (Icc a b) F F A (kc + g)))
        (fun s ↦ Aext s (k s) + bext s) (uIcc (t₀ : ℝ) t) := by
      intro s hs
      have h1 := IccExtend_of_mem hab (ptApply (Icc a b) F F A (kc + g)) (hsub hs)
      have h2 : Aext s = A ⟨s, hsub hs⟩ := IccExtend_of_mem hab A (hsub hs)
      have h3 := IccExtend_of_mem hab g (hsub hs)
      show _ = Aext s (k s) + Aext s (IccExtend hab g s)
      rw [h1, h2, h3, ptApply_apply, ContinuousMap.add_apply, map_add]
      rfl
    rw [integral_congr hcongr, integral_eq_sub_of_hasDerivAt (fun s _ ↦ hk s (mem_univ s))
      (((hAc.clm_apply hkc).add hbc).intervalIntegrable _ _), hk₀, sub_zero]
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The partial derivative of `flowEqn` in the second variable is invertible. -/
lemma isInvertible_fderiv_flowEqn_inr {f : F → F} (hf : ContDiff ℝ 1 f) (p : F × C(Icc a b, F)) :
    (fderiv ℝ (flowEqn hab t₀ hf.continuous) p ∘L
      ContinuousLinearMap.inr ℝ F C(Icc a b, F)).IsInvertible := by
  rw [(hasFDerivAt_flowEqn hab t₀ hf p).fderiv]
  convert isInvertible_id_sub_intOp_ptApply hab t₀
    (compLeft (fderiv ℝ f) (hf.continuous_fderiv one_ne_zero) p.2) using 1
  ext h t
  simp

omit [FiniteDimensional ℝ F] in
/-- **Uniqueness**: for a Lipschitz vector field, `flowEqn` has at most one zero with a given
initial value. -/
lemma eq_of_flowEqn_eq_zero {f : F → F} (hf : Continuous f) {K : ℝ≥0} (hK : LipschitzWith K f)
    {ξ : F} {x y : C(Icc a b, F)} (hx : flowEqn hab t₀ hf (ξ, x) = 0)
    (hy : flowEqn hab t₀ hf (ξ, y) = 0) : x = y :=
  eq_of_integral_eq hab t₀ (V := fun _ ↦ f) (fun _ ↦ hK) (fun _ ↦ rfl) (fun _ ↦ rfl)
    ((flowEqn_eq_zero_iff hab t₀ hf).1 hx) ((flowEqn_eq_zero_iff hab t₀ hf).1 hy)

/-- **Smooth dependence on the initial value near a solution** (implicit function theorem). -/
theorem exists_contDiffAt_of_flowEqn_eq_zero {f : F → F} (hf : ContDiff ℝ ∞ f) {ξ₀ : F}
    {x₀ : C(Icc a b, F)} (h₀ : flowEqn hab t₀ hf.continuous (ξ₀, x₀) = 0) :
    ∃ ψ : F → C(Icc a b, F), ContDiffAt ℝ ∞ ψ ξ₀ ∧ ψ ξ₀ = x₀ ∧
      ∀ᶠ ξ in 𝓝 ξ₀, flowEqn hab t₀ hf.continuous (ξ, ψ ξ) = 0 := by
  have cdf : ContDiffAt ℝ ∞ (flowEqn hab t₀ hf.continuous) (ξ₀, x₀) :=
    (contDiff_flowEqn hab t₀ hf).contDiffAt
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have if₂ := isInvertible_fderiv_flowEqn_inr hab t₀ (hf.of_le (by simp)) (ξ₀, x₀)
  refine ⟨cdf.implicitFunction pn if₂, cdf.contDiffAt_implicitFunction pn if₂,
    cdf.implicitFunction_apply_self pn if₂, ?_⟩
  filter_upwards [cdf.eventually_apply_implicitFunction pn if₂] with ξ hξ
  rw [hξ, h₀]

omit [FiniteDimensional ℝ F] in
/-- Every initial value has a solution on `[a, b]`, for a `C^∞` vector field with compact
support (Picard–Lindelöf). -/
theorem exists_flowEqn_eq_zero {f : F → F} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (ξ : F) : ∃ x : C(Icc a b, F), flowEqn hab t₀ hf.continuous (ξ, x) = 0 := by
  obtain ⟨L, hL⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by simp)
  set L' : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  set R : ℝ≥0 := ⟨max L 0 * (b - a), mul_nonneg (le_max_right _ _) (by linarith)⟩
  have hPL : IsPicardLindelof (fun _ ↦ f) t₀ ξ R 0 L' K :=
    IsPicardLindelof.of_time_independent (fun x _ ↦ (hL x).trans (le_max_left _ _))
      hK.lipschitzOnWith (by
        simp only [L', R, NNReal.coe_zero, sub_zero]
        exact mul_le_mul_of_nonneg_left
          (max_le (by linarith [t₀.2.1]) (by linarith [t₀.2.2])) (le_max_right _ _))
  obtain ⟨α, hα₀, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hαc : ContinuousOn α (Icc a b) := fun t ht ↦ (hα t ht).continuousWithinAt
  refine ⟨⟨fun t : Icc a b ↦ α t, hαc.domRestrict⟩, ?_⟩
  have := flowEqn_restrict_eq_zero hab t₀ hf.continuous hαc
    (fun t ht ↦ (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  rwa [hα₀] at this

/-- **The flow is smooth**: for a `C^∞` vector field with compact support, the solution of
`x' = f(x)`, `x(t₀) = ξ` on `[a, b]` exists for every `ξ` and depends smoothly on `ξ`, as a map
into `C([a, b], F)`. -/
theorem exists_contDiff_flow {f : F → F} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ Φ : F → C(Icc a b, F), ContDiff ℝ ∞ Φ ∧ ∀ ξ, flowEqn hab t₀ hf.continuous (ξ, Φ ξ) = 0 := by
  choose Φ hΦ using exists_flowEqn_eq_zero hab t₀ hf hfc
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by simp)
  refine ⟨Φ, contDiff_iff_contDiffAt.2 fun ξ₁ ↦ ?_, hΦ⟩
  obtain ⟨ψ, hψ, -, hψ0⟩ := exists_contDiffAt_of_flowEqn_eq_zero hab t₀ hf (hΦ ξ₁)
  refine hψ.congr_of_eventuallyEq ?_
  filter_upwards [hψ0] with ξ hξ
  exact eq_of_flowEqn_eq_zero hab t₀ hf.continuous hK (hΦ ξ) hξ

/-- **Smooth dependence near a solution in an open set**: let `f` be `C^∞` on an open set `U` and
`α₀` a solution of `x' = f(x)` on `[a, b]` with values in `U`. Then for initial values `ξ` at `t₀`
near `α₀(t₀)` the solutions exist on `[a, b]`, stay in `U`, and depend smoothly on `ξ`.

The proof multiplies `f` by a smooth cutoff function which is `1` near the compact set
`α₀([a, b])` and has compact support in `U`, and applies `exists_contDiff_flow`. -/
theorem exists_contDiff_flow_near {U : Set F} (hU : IsOpen U) {f : F → F}
    (hf : ContDiffOn ℝ ∞ f U) {α₀ : ℝ → F} (hα₀ : ContinuousOn α₀ (Icc a b))
    (hα₀' : ∀ t ∈ Ioo a b, HasDerivAt α₀ (f (α₀ t)) t) (hα₀U : ∀ t ∈ Icc a b, α₀ t ∈ U) :
    ∃ Φ : F → C(Icc a b, F), ContDiff ℝ ∞ Φ ∧ (∀ t : Icc a b, Φ (α₀ t₀) t = α₀ t) ∧
      ∀ᶠ ξ in 𝓝 (α₀ t₀), Φ ξ t₀ = ξ ∧ (∀ t, Φ ξ t ∈ U) ∧
        ∀ t ∈ Ioo a b, HasDerivAt (IccExtend hab (Φ ξ)) (f (IccExtend hab (Φ ξ) t)) t := by
  set K := α₀ '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hα₀
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hα₀U t ht
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
    (cthickening_subset_thickening' hδ (by linarith) K)
  have htsupp : tsupport χ ⊆ cthickening δ K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening δ K
  set g : F → F := fun y ↦ χ y • f y with hg_def
  have hg : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ U
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hy))
    · have hyχ : y ∉ tsupport χ := fun h ↦ hy (hδU (htsupp h))
      refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hyχ] with z hz
      simp [g, hz]
  have hgc : HasCompactSupport g := by
    refine IsCompact.of_isClosed_subset (hK.cthickening (r := δ)) isClosed_closure ?_
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro y hy
    rw [← hχs]
    intro h
    apply hy
    simp [g, h]
  have hg1 : ∀ y ∈ cthickening (δ / 2) K, g y = f y := fun y hy ↦ by
    simp [g, (hχ1 y).1 hy]
  obtain ⟨Kl, hKl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by simp)
  obtain ⟨Φ, hΦ, hΦ0⟩ := exists_contDiff_flow hab t₀ hg hgc
  -- the given solution is the solution for the cutoff field
  have hα₀K : ∀ t ∈ Icc a b, α₀ t ∈ cthickening (δ / 2) K := fun t ht ↦
    self_subset_cthickening K ⟨t, ht, rfl⟩
  have hα₀g := flowEqn_restrict_eq_zero hab t₀ hg.continuous hα₀
    (fun t ht ↦ (hg1 _ (hα₀K t (Ioo_subset_Icc_self ht))).symm ▸ hα₀' t ht)
  have hΦα₀ : Φ (α₀ t₀) = ⟨fun t : Icc a b ↦ α₀ t, hα₀.domRestrict⟩ :=
    eq_of_flowEqn_eq_zero hab t₀ hg.continuous hKl (hΦ0 _) hα₀g
  refine ⟨Φ, hΦ, fun t ↦ by rw [hΦα₀]; rfl, ?_⟩
  -- nearby solutions stay where the cutoff is `1`
  have hnear : ∀ᶠ ξ in 𝓝 (α₀ t₀), dist (Φ ξ) (Φ (α₀ t₀)) < δ / 2 :=
    hΦ.continuous.continuousAt.eventually (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [hnear] with ξ hξ
  have hmem : ∀ t : Icc a b, Φ ξ t ∈ cthickening (δ / 2) K := by
    intro t
    refine thickening_subset_cthickening _ _ (mem_thickening_iff.2 ⟨α₀ t, ⟨t, t.2, rfl⟩, ?_⟩)
    calc dist (Φ ξ t) (α₀ t) = dist (Φ ξ t) (Φ (α₀ t₀) t) := by rw [hΦα₀]; rfl
      _ ≤ dist (Φ ξ) (Φ (α₀ t₀)) := ContinuousMap.dist_apply_le_dist t
      _ < δ / 2 := hξ
  obtain ⟨h0, hd⟩ := hasDerivAt_of_flowEqn_eq_zero hab t₀ hg.continuous (hΦ0 ξ)
  refine ⟨h0, fun t ↦ hδU (cthickening_mono (by linarith) K (hmem t)), fun t ht ↦ ?_⟩
  have hm : IccExtend hab (Φ ξ) t ∈ cthickening (δ / 2) K := hmem (projIcc a b hab t)
  have := hd t ht
  rwa [hg1 _ hm] at this

end Flow

end PythagoreanPaper
