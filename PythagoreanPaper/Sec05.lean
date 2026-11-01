import PythagoreanPaper.ExpQuadratic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Manuscript §5 — the convergent structure as an exponential

* C5.1: with `u = (j, j')`, the equation `j'' + K j = 0` is the first-order system `u' = A_K u`
  (`sec5_first_order`, and conversely `sec5_second_order_of_first_order`).
* C5.2: `A_K² = -K I` (`sec5_AK_sq`).
* C5.3: a solution of `u' = A_K u` is `u(r) = exp(r A_K) u(0)` (`sec5_solution_exp`): the curve
  `r ↦ exp(r A_K) u(0)` solves the system (`hasDerivAt_exp_AK_mulVec`), and solutions are unique.
* C5.4: `exp(r A_K) = C_K(r) I + S_K(r) A_K` with
  `C_K(r) = ∑ (-K)^m r^(2m) / (2m)!` and `S_K(r) = ∑ (-K)^m r^(2m+1) / (2m+1)!`
  (`sec5_exp_AK`, `sec5_exp_AK_series`; the series converge by `hasSum_C`, `hasSum_S`).

Statements are about matrices with their usual (product) topology. Where the theory of the
exponential needs a norm on matrices, the proofs use the `L∞` operator norm, as Mathlib's own
matrix-exponential lemmas do.
-/

noncomputable section

open NormedSpace Matrix Set Nat

namespace PythagoreanPaper

/-- `A_K = (0 1; -K 0)` of §5. -/
def AK (K : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -K, 0]

/-- **C5.2.** `A_K² = -K I`. -/
theorem sec5_AK_sq (K : ℝ) : AK K * AK K = -K • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AK, Matrix.mul_apply, Fin.sum_univ_two]

theorem AK_mulVec (K a b : ℝ) : AK K *ᵥ ![a, b] = ![b, -K * a] := by
  ext i
  fin_cases i <;> simp [AK, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **C5.1.** On an open interval `I`, a solution `j` of `j'' + K j = 0` gives a solution
`u = (j, j')` of `u' = A_K u`. -/
theorem sec5_first_order {K a b : ℝ} {j j' j'' : ℝ → ℝ}
    (hj : ∀ r ∈ Ioo a b, HasDerivAt j (j' r) r) (hj' : ∀ r ∈ Ioo a b, HasDerivAt j' (j'' r) r)
    (hode : ∀ r ∈ Ioo a b, j'' r + K * j r = 0) :
    ∀ r ∈ Ioo a b, HasDerivAt (fun r => ![j r, j' r]) (AK K *ᵥ ![j r, j' r]) r := by
  intro r hr
  rw [AK_mulVec, hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using hj r hr
  · have h2 : j'' r = -K * j r := by linarith [hode r hr]
    simpa [h2] using hj' r hr

/-- **C5.1** (converse). On an open interval `I`, a solution `u` of `u' = A_K u` has the form
`u = (j, j')` with `j = u₀`, `j' = u₁`, `j'' = u₁' = -K j`, i.e. `j'' + K j = 0`. -/
theorem sec5_second_order_of_first_order {K a b : ℝ} {u : ℝ → Fin 2 → ℝ}
    (hu : ∀ r ∈ Ioo a b, HasDerivAt u (AK K *ᵥ u r) r) :
    ∀ r ∈ Ioo a b, HasDerivAt (fun r => u r 0) (u r 1) r ∧
      HasDerivAt (fun r => u r 1) (-K * u r 0) r := by
  intro r hr
  have h := hasDerivAt_pi.mp (hu r hr)
  have hv : AK K *ᵥ u r = ![u r 1, -K * u r 0] := by
    ext i
    fin_cases i <;> simp [AK, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv] at h
  exact ⟨by simpa using h 0, by simpa using h 1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The curve `t ↦ exp(t A_K) v` has derivative `A_K exp(t A_K) v`. -/
theorem hasDerivAt_exp_AK_mulVec (K : ℝ) (v : Fin 2 → ℝ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => exp (t • AK K) *ᵥ v) (AK K *ᵥ (exp (r • AK K) *ᵥ v)) r := by
  open scoped Matrix.Norms.Operator in
  (have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (AK K) r
   let mv : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] (Fin 2 → ℝ) :=
     LinearMap.mkContinuous ((Matrix.mulVecBilin ℝ ℝ).flip v) ‖v‖
       (fun M => by
         rw [mul_comm]
         exact Matrix.linfty_opNorm_mulVec M v)
   have hmv : ∀ M, mv M = M *ᵥ v := fun M => rfl
   have h2 := mv.hasFDerivAt.comp_hasDerivAt r h
   rw [hmv, ← Matrix.mulVec_mulVec] at h2
   exact h2)

/-- **C5.3.** On an open interval `I ∋ 0`, a solution of `u' = A_K u` is
`u(r) = exp(r A_K) u(0)`. -/
theorem sec5_solution_exp {K a b : ℝ} {u : ℝ → Fin 2 → ℝ} (hI : (0 : ℝ) ∈ Ioo a b)
    (hu : ∀ r ∈ Ioo a b, HasDerivAt u (AK K *ᵥ u r) r) :
    ∀ r ∈ Ioo a b, u r = exp (r • AK K) *ᵥ u 0 := by
  -- `w ↦ A_K w` as a continuous linear map
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (AK K))
  have hL : ∀ w, L w = AK K *ᵥ w := fun w => rfl
  have hf : ∀ t ∈ Ioo a b, HasDerivAt u (L (u t)) t ∧ u t ∈ (univ : Set (Fin 2 → ℝ)) :=
    fun t ht => ⟨by rw [hL]; exact hu t ht, mem_univ _⟩
  have hg : ∀ t ∈ Ioo a b, HasDerivAt (fun t => exp (t • AK K) *ᵥ u 0)
      (L (exp (t • AK K) *ᵥ u 0)) t ∧ exp (t • AK K) *ᵥ u 0 ∈ (univ : Set (Fin 2 → ℝ)) :=
    fun t _ => ⟨by rw [hL]; exact hasDerivAt_exp_AK_mulVec K (u 0) t, mem_univ _⟩
  have h := ODE_solution_unique_of_mem_Ioo (v := fun _ => L) (s := fun _ => univ)
    (fun _ _ => L.lipschitzWith.lipschitzOnWith) hI hf hg (by simp)
  intro r hr
  exact h hr

/-- **C5.3** for `u = (j, j')` with `j'' + K j = 0` (combining C5.1 and C5.3). -/
theorem sec5_solution_exp_of_ode {K a b : ℝ} {j j' j'' : ℝ → ℝ} (hI : (0 : ℝ) ∈ Ioo a b)
    (hj : ∀ r ∈ Ioo a b, HasDerivAt j (j' r) r) (hj' : ∀ r ∈ Ioo a b, HasDerivAt j' (j'' r) r)
    (hode : ∀ r ∈ Ioo a b, j'' r + K * j r = 0) :
    ∀ r ∈ Ioo a b, ![j r, j' r] = exp (r • AK K) *ᵥ ![j 0, j' 0] :=
  sec5_solution_exp (u := fun r => ![j r, j' r]) hI (sec5_first_order hj hj' hode)

set_option backward.isDefEq.respectTransparency false in
/-- **C5.4.** `exp(r A_K) = C_K(r) I + S_K(r) A_K`. -/
theorem sec5_exp_AK (K r : ℝ) :
    exp (r • AK K) = C K r • (1 : Matrix (Fin 2) (Fin 2) ℝ) + S K r • AK K := by
  open scoped Matrix.Norms.Operator in
  exact exp_smul_eq_of_mul_self (sec5_AK_sq K) r

/-- **C5.4** with `C_K` and `S_K` written as the series of §5. -/
theorem sec5_exp_AK_series (K r : ℝ) :
    exp (r • AK K) =
      (∑' m : ℕ, (-K) ^ m * r ^ (2 * m) / ↑(2 * m)!) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (∑' m : ℕ, (-K) ^ m * r ^ (2 * m + 1) / ↑(2 * m + 1)!) • AK K := by
  rw [(hasSum_C K r).tsum_eq, (hasSum_S K r).tsum_eq]
  exact sec5_exp_AK K r

end PythagoreanPaper
