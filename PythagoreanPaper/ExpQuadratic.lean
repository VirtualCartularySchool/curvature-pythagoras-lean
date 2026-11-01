import PythagoreanPaper.SK
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Exponentials of elements whose square is a scalar

Manuscript §5 (`exp(r A_K) = C_K(r) I + S_K(r) A_K`, from `A_K² = -K I`) and §7
(`exp(θ J) = cos θ I + sin θ J`, from `J² = -I`) both split the exponential series into its even
and odd terms. `exp_smul_eq_of_mul_self` is that computation in an arbitrary complete normed
`ℝ`-algebra; `Sec05` and `Sec07` apply it.
-/

noncomputable section

open NormedSpace Nat

namespace PythagoreanPaper

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- If `A * A = -K • 1`, then `exp (r • A) = C_K(r) • 1 + S_K(r) • A`. -/
theorem exp_smul_eq_of_mul_self {K : ℝ} {A : 𝔸} (hA : A * A = -K • (1 : 𝔸)) (r : ℝ) :
    exp (r • A) = C K r • (1 : 𝔸) + S K r • A := by
  have hsq : ∀ m : ℕ, A ^ (2 * m) = (-K) ^ m • (1 : 𝔸) := by
    intro m
    rw [pow_mul, sq, hA, smul_pow, one_pow]
  have heven : HasSum (fun m : ℕ => ((2 * m)! : ℝ)⁻¹ • (r • A) ^ (2 * m))
      (C K r • (1 : 𝔸)) := by
    have h := (hasSum_C K r).smul_const (1 : 𝔸)
    convert h using 1
    funext m
    rw [smul_pow, hsq m, smul_smul, smul_smul]
    congr 1
    ring
  have hodd : HasSum (fun m : ℕ => ((2 * m + 1)! : ℝ)⁻¹ • (r • A) ^ (2 * m + 1))
      (S K r • A) := by
    have h := (hasSum_S K r).smul_const A
    convert h using 1
    funext m
    rw [smul_pow, pow_succ A (2 * m), hsq m, smul_mul_assoc, one_mul, smul_smul, smul_smul]
    congr 1
    ring
  exact (exp_series_hasSum_exp' (𝕂 := ℝ) (r • A)).unique
    (HasSum.even_add_odd (f := fun n : ℕ => ((n ! : ℝ))⁻¹ • (r • A) ^ n) heven hodd)

end PythagoreanPaper
