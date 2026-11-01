import PythagoreanPaper.SK
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Manuscript §9 — the constant-curvature sine law

Notation of the manuscript: `X = C_K(a)`, `Y = C_K(b)`, `Z = C_K(c)`, `P = S_K(a)`,
`Q = S_K(b)`, `R = S_K(c)`; in Lean the angle `C` of the manuscript is written `C'`, because `C` is
the function `C_K`.

* C9.2 is `S_pos` and C9.4 is `hasDerivAt_S`, `C_sq_add_mul_S_sq` (in `PythagoreanPaper.SK`).
* C9.5: from the cosine law `C_K(a) = C_K(b) C_K(c) + K S_K(b) S_K(c) cos A`,
  `sin² A / P² = (1 - X² - Y² - Z² + 2XYZ) / (K² P² Q² R²)` (`sec9_sin_sq_div_eq`).
* C9.6: hence `sin² A / P² = sin² B / Q² = sin² C / R²` (`sec9_sin_sq_ratios_eq`).
* C9.7: for `0 < A, B, C < π` and `P, Q, R > 0`, taking square roots gives the sine law
  `sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)` (`sec9_sine_law_of_cos_law`).
* C9.8: for fixed side lengths `a, b, c` of a nondegenerate triangle, the angles `A_K, B_K, C_K`
  determined by the constant-curvature cosine law (`angleK`) depend continuously on `K` near `0`,
  `A_K → A_0` etc., `S_K(x) → x` by the series of `S_K`, and the sine law passes to the limit
  `sin A_0 / a = sin B_0 / b = sin C_0 / c` (`sec9_limit`). `A_0` is the Euclidean angle
  (`angleK_zero_eq_angle`, by the Euclidean law of cosines), so this is the Euclidean sine law
  (`sec9_euclidean_sine_law`).

C9.1 and C9.3 (the sine and cosine laws for geodesic triangles in a two-dimensional Riemannian
manifold of constant curvature `K`) need Riemannian geometry and are not in this file (see
`PythagoreanPaper.Riemannian.Triangle`). Here the cosine law is the hypothesis of C9.5–C9.7,
exactly as in the manuscript's derivation, and the angles `A_K` of C9.8 are the angles given by the
cosine law.
-/

noncomputable section

open Real Nat Set Filter Topology EuclideanGeometry

namespace PythagoreanPaper

/-! ### C9.5–C9.7: from the cosine law to the sine law, `K ≠ 0` -/

/-- **C9.5.** From the cosine law `C_K(a) = C_K(b) C_K(c) + K S_K(b) S_K(c) cos A`:
`sin² A / P² = (1 - X² - Y² - Z² + 2XYZ) / (K² P² Q² R²)`. -/
theorem sec9_sin_sq_div_eq {K a b c A : ℝ} (hK : K ≠ 0) (hQ : S K b ≠ 0) (hR : S K c ≠ 0)
    (hcos : C K a = C K b * C K c + K * S K b * S K c * Real.cos A) :
    Real.sin A ^ 2 / S K a ^ 2 =
      (1 - C K a ^ 2 - C K b ^ 2 - C K c ^ 2 + 2 * C K a * C K b * C K c) /
        (K ^ 2 * S K a ^ 2 * S K b ^ 2 * S K c ^ 2) := by
  rcases eq_or_ne (S K a) 0 with hP | hP
  · simp [hP]
  have hY := C_sq_add_mul_S_sq K b
  have hZ := C_sq_add_mul_S_sq K c
  -- `K² Q² R² - (X - YZ)² = 1 - X² - Y² - Z² + 2XYZ`, from `Y² + K Q² = 1`, `Z² + K R² = 1`
  have key : (K * S K b * S K c) ^ 2 - (C K a - C K b * C K c) ^ 2 =
      1 - C K a ^ 2 - C K b ^ 2 - C K c ^ 2 + 2 * C K a * C K b * C K c := by
    linear_combination (K * S K c ^ 2) * hY + (1 - C K b ^ 2) * hZ
  have hden : K ^ 2 * S K a ^ 2 * S K b ^ 2 * S K c ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hK) (pow_ne_zero 2 hP))
      (pow_ne_zero 2 hQ)) (pow_ne_zero 2 hR)
  rw [div_eq_div_iff (pow_ne_zero 2 hP) hden]
  -- `cos A = (X - YZ) / (K Q R)` and `sin² A = 1 - cos² A`
  linear_combination (S K a ^ 2 * (K * S K b * S K c) ^ 2) * Real.sin_sq_add_cos_sq A +
    (S K a ^ 2 * (K * S K b * S K c * Real.cos A + (C K a - C K b * C K c))) * hcos +
    S K a ^ 2 * key

/-- **C9.6.** The right-hand side of C9.5 is symmetric in `X, Y, Z`, so
`sin² A / P² = sin² B / Q² = sin² C / R²`. -/
theorem sec9_sin_sq_ratios_eq {K a b c A B C' : ℝ} (hK : K ≠ 0)
    (hP : S K a ≠ 0) (hQ : S K b ≠ 0) (hR : S K c ≠ 0)
    (hA : C K a = C K b * C K c + K * S K b * S K c * Real.cos A)
    (hB : C K b = C K c * C K a + K * S K c * S K a * Real.cos B)
    (hC : C K c = C K a * C K b + K * S K a * S K b * Real.cos C') :
    Real.sin A ^ 2 / S K a ^ 2 = Real.sin B ^ 2 / S K b ^ 2 ∧
      Real.sin B ^ 2 / S K b ^ 2 = Real.sin C' ^ 2 / S K c ^ 2 := by
  rw [sec9_sin_sq_div_eq hK hQ hR hA, sec9_sin_sq_div_eq hK hR hP hB,
    sec9_sin_sq_div_eq hK hP hQ hC]
  constructor <;> ring

/-- **C9.7.** For `0 < A, B, C < π` (so `sin A, sin B, sin C > 0`) and `S_K(a), S_K(b), S_K(c) > 0`,
square roots give the sine law `sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)` (`K ≠ 0`). -/
theorem sec9_sine_law_of_cos_law {K a b c A B C' : ℝ} (hK : K ≠ 0)
    (hP : 0 < S K a) (hQ : 0 < S K b) (hR : 0 < S K c)
    (hA0 : 0 < A) (hAπ : A < π) (hB0 : 0 < B) (hBπ : B < π) (hC0 : 0 < C') (hCπ : C' < π)
    (hA : C K a = C K b * C K c + K * S K b * S K c * Real.cos A)
    (hB : C K b = C K c * C K a + K * S K c * S K a * Real.cos B)
    (hC : C K c = C K a * C K b + K * S K a * S K b * Real.cos C') :
    Real.sin A / S K a = Real.sin B / S K b ∧ Real.sin B / S K b = Real.sin C' / S K c := by
  obtain ⟨h1, h2⟩ := sec9_sin_sq_ratios_eq hK hP.ne' hQ.ne' hR.ne' hA hB hC
  have pA : 0 ≤ Real.sin A / S K a := div_nonneg (sin_pos_of_pos_of_lt_pi hA0 hAπ).le hP.le
  have pB : 0 ≤ Real.sin B / S K b := div_nonneg (sin_pos_of_pos_of_lt_pi hB0 hBπ).le hQ.le
  have pC : 0 ≤ Real.sin C' / S K c := div_nonneg (sin_pos_of_pos_of_lt_pi hC0 hCπ).le hR.le
  rw [← div_pow, ← div_pow] at h1
  rw [← div_pow, ← div_pow] at h2
  exact ⟨(pow_left_inj₀ pA pB two_ne_zero).mp h1, (pow_left_inj₀ pB pC two_ne_zero).mp h2⟩

/-! ### C9.8: the limit `K → 0` -/

/-- `G_K(x) = ∑ (-K)^m x^(2m+2) / (2m+2)!`, so that `C_K(x) = 1 - K G_K(x)`
(`C_eq_one_sub_mul_Gk`) and `G_0(x) = x² / 2` (`Gk_zero`). -/
def Gk (K x : ℝ) : ℝ := ∑' m : ℕ, (-K) ^ m * x ^ (2 * m + 2) / ↑(2 * m + 2)!

/-- `C_K(x) = 1 - K G_K(x)`, from the series of `C_K` (§5). -/
theorem C_eq_one_sub_mul_Gk (K x : ℝ) : C K x = 1 - K * Gk K x := by
  rcases eq_or_ne K 0 with rfl | hK
  · rw [C_of_eq_zero, zero_mul, sub_zero]
  -- drop the term `m = 0` of the series of `C_K`
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_C K x)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, one_mul,
    Nat.factorial_zero, Nat.cast_one, div_one] at h
  have h' : HasSum (fun m : ℕ => -K * ((-K) ^ m * x ^ (2 * m + 2) / ↑(2 * m + 2)!))
      (C K x - 1) := by
    convert h using 1
    funext m
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_succ]
    ring
  have h3 : HasSum (fun m : ℕ => (-K) ^ m * x ^ (2 * m + 2) / ↑(2 * m + 2)!)
      ((-K)⁻¹ * (C K x - 1)) := by
    convert h'.mul_left (-K)⁻¹ using 1
    funext m
    rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hK), one_mul]
  have hK' : K * (-K)⁻¹ = -1 := by rw [inv_neg, mul_neg, mul_inv_cancel₀ hK]
  rw [Gk, h3.tsum_eq, ← mul_assoc, hK']
  ring

theorem Gk_zero (x : ℝ) : Gk 0 x = x ^ 2 / 2 := by
  rw [Gk, tsum_eq_single 0]
  · simp
  · intro m hm
    simp [zero_pow hm]

/-- Bound for the M-test: on `|K| ≤ 1`, `|(-K)^m y| ≤ |y|`. -/
private theorem abs_term_le {K : ℝ} (hK : K ∈ Icc (-1 : ℝ) 1) (m : ℕ) (y : ℝ) :
    |(-K) ^ m * y| ≤ |y| := by
  rw [abs_mul, abs_pow, abs_neg]
  exact mul_le_of_le_one_left (abs_nonneg y) (pow_le_one₀ (abs_nonneg K) (abs_le.mpr hK))

/-- `K ↦ G_K(x)` is continuous on `[-1, 1]` (uniform convergence of its series). -/
theorem continuousOn_Gk (x : ℝ) : ContinuousOn (fun K => Gk K x) (Icc (-1 : ℝ) 1) := by
  have hsum : Summable (fun m : ℕ => |x| ^ (2 * m + 2) / ↑(2 * m + 2)!) :=
    (Real.summable_pow_div_factorial |x|).comp_injective
      (i := fun m : ℕ => 2 * m + 2) (fun m n (h : 2 * m + 2 = 2 * n + 2) => by omega)
  have h : ContinuousOn (fun K : ℝ => ∑' m : ℕ, (-K) ^ m * x ^ (2 * m + 2) / ↑(2 * m + 2)!)
      (Icc (-1 : ℝ) 1) := by
    refine continuousOn_tsum (fun m => (by fun_prop : Continuous fun K : ℝ =>
      (-K) ^ m * x ^ (2 * m + 2) / ↑(2 * m + 2)!).continuousOn) hsum (fun m K hK => ?_)
    rw [Real.norm_eq_abs, mul_div_assoc]
    calc |(-K) ^ m * (x ^ (2 * m + 2) / ↑(2 * m + 2)!)|
        ≤ |x ^ (2 * m + 2) / ↑(2 * m + 2)!| := abs_term_le hK m _
      _ = |x| ^ (2 * m + 2) / ↑(2 * m + 2)! := by rw [abs_div, abs_pow, Nat.abs_cast]
  exact h

/-- `K ↦ S_K(x)` is continuous on `[-1, 1]` (uniform convergence of the series of `S_K`). -/
theorem continuousOn_S_param (x : ℝ) : ContinuousOn (fun K => S K x) (Icc (-1 : ℝ) 1) := by
  have hsum : Summable (fun m : ℕ => |x| ^ (2 * m + 1) / ↑(2 * m + 1)!) :=
    (Real.summable_pow_div_factorial |x|).comp_injective
      (i := fun m : ℕ => 2 * m + 1) (fun m n (h : 2 * m + 1 = 2 * n + 1) => by omega)
  have h : ContinuousOn (fun K : ℝ => ∑' m : ℕ, (-K) ^ m * x ^ (2 * m + 1) / ↑(2 * m + 1)!)
      (Icc (-1 : ℝ) 1) := by
    refine continuousOn_tsum (fun m => (by fun_prop : Continuous fun K : ℝ =>
      (-K) ^ m * x ^ (2 * m + 1) / ↑(2 * m + 1)!).continuousOn) hsum (fun m K hK => ?_)
    rw [Real.norm_eq_abs, mul_div_assoc]
    calc |(-K) ^ m * (x ^ (2 * m + 1) / ↑(2 * m + 1)!)|
        ≤ |x ^ (2 * m + 1) / ↑(2 * m + 1)!| := abs_term_le hK m _
      _ = |x| ^ (2 * m + 1) / ↑(2 * m + 1)! := by rw [abs_div, abs_pow, Nat.abs_cast]
  exact h.congr fun K _ => (hasSum_S K x).tsum_eq.symm

theorem continuousAt_Gk {K₀ : ℝ} (h : K₀ ∈ Ioo (-1 : ℝ) 1) (x : ℝ) :
    ContinuousAt (fun K => Gk K x) K₀ :=
  (continuousOn_Gk x).continuousAt (Icc_mem_nhds h.1 h.2)

theorem continuousAt_S_param {K₀ : ℝ} (h : K₀ ∈ Ioo (-1 : ℝ) 1) (x : ℝ) :
    ContinuousAt (fun K => S K x) K₀ :=
  (continuousOn_S_param x).continuousAt (Icc_mem_nhds h.1 h.2)

/-- **C9.8** (`S_K(x) → x`). Because `S_K(x)` is given by its series, `lim_{K → 0} S_K(x) = x`. -/
theorem tendsto_S_zero (x : ℝ) : Tendsto (fun K => S K x) (𝓝 0) (𝓝 x) := by
  have h := (continuousAt_S_param (K₀ := 0) ⟨by norm_num, by norm_num⟩ x).tendsto
  simpa [S_of_eq_zero] using h

/-- The cosine of the angle opposite the side `a` of a triangle with sides `a, b, c` in curvature
`K`, as given by the constant-curvature cosine law: for `K ≠ 0` it is
`(C_K(a) - C_K(b) C_K(c)) / (K S_K(b) S_K(c))` (`cosLaw_of_ne_zero`), and for `K = 0` it is
`(b² + c² - a²) / (2bc)` (`cosLaw_zero`). -/
def cosLaw (K a b c : ℝ) : ℝ :=
  (Gk K b + Gk K c - Gk K a - K * Gk K b * Gk K c) / (S K b * S K c)

/-- The angle opposite the side `a` given by the constant-curvature cosine law. -/
def angleK (K a b c : ℝ) : ℝ := Real.arccos (cosLaw K a b c)

theorem cosLaw_of_ne_zero {K : ℝ} (hK : K ≠ 0) (a b c : ℝ) :
    cosLaw K a b c = (C K a - C K b * C K c) / (K * S K b * S K c) := by
  have h : C K a - C K b * C K c = K * (Gk K b + Gk K c - Gk K a - K * Gk K b * Gk K c) := by
    rw [C_eq_one_sub_mul_Gk K a, C_eq_one_sub_mul_Gk K b, C_eq_one_sub_mul_Gk K c]
    ring
  rw [cosLaw, h, show K * S K b * S K c = K * (S K b * S K c) by ring,
    mul_div_mul_left _ _ hK]

theorem cosLaw_zero (a b c : ℝ) : cosLaw 0 a b c = (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) := by
  rw [cosLaw, Gk_zero, Gk_zero, Gk_zero, S_of_eq_zero, S_of_eq_zero]
  ring

/-- For `K ≠ 0`, the angle `angleK K a b c` satisfies the constant-curvature cosine law. -/
theorem cos_law_angleK {K a b c : ℝ} (hK : K ≠ 0) (hb : S K b ≠ 0) (hc : S K c ≠ 0)
    (h : cosLaw K a b c ∈ Ioo (-1 : ℝ) 1) :
    C K a = C K b * C K c + K * S K b * S K c * Real.cos (angleK K a b c) := by
  have hd : K * S K b * S K c ≠ 0 := mul_ne_zero (mul_ne_zero hK hb) hc
  rw [angleK, Real.cos_arccos h.1.le h.2.le, cosLaw_of_ne_zero hK,
    mul_comm (K * S K b * S K c), div_mul_cancel₀ _ hd]
  ring

theorem angleK_pos_lt_pi {K a b c : ℝ} (h : cosLaw K a b c ∈ Ioo (-1 : ℝ) 1) :
    0 < angleK K a b c ∧ angleK K a b c < π :=
  ⟨Real.arccos_pos.mpr h.2, Real.arccos_lt_pi.mpr h.1⟩

theorem continuousAt_cosLaw {K₀ : ℝ} (hK₀ : K₀ ∈ Ioo (-1 : ℝ) 1) (a b c : ℝ)
    (hbc : S K₀ b * S K₀ c ≠ 0) : ContinuousAt (fun K => cosLaw K a b c) K₀ := by
  show ContinuousAt
    (fun K => (Gk K b + Gk K c - Gk K a - K * Gk K b * Gk K c) / (S K b * S K c)) K₀
  exact ((((continuousAt_Gk hK₀ b).add (continuousAt_Gk hK₀ c)).sub
    (continuousAt_Gk hK₀ a)).sub ((continuousAt_id.mul (continuousAt_Gk hK₀ b)).mul
    (continuousAt_Gk hK₀ c))).div
    ((continuousAt_S_param hK₀ b).mul (continuousAt_S_param hK₀ c)) hbc

theorem continuousAt_angleK {K₀ : ℝ} (hK₀ : K₀ ∈ Ioo (-1 : ℝ) 1) (a b c : ℝ)
    (hbc : S K₀ b * S K₀ c ≠ 0) : ContinuousAt (fun K => angleK K a b c) K₀ :=
  Real.continuous_arccos.continuousAt.comp (continuousAt_cosLaw hK₀ a b c hbc)

/-- For side lengths with the strict triangle inequalities, `cos A_0 ∈ (-1, 1)`. -/
theorem cosLaw_zero_mem_Ioo {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) : cosLaw 0 a b c ∈ Ioo (-1 : ℝ) 1 := by
  rw [cosLaw_zero, Set.mem_Ioo]
  have hbc : 0 < 2 * b * c := by positivity
  constructor
  · rw [lt_div_iff₀ hbc]
    nlinarith [mul_pos (sub_pos.mpr h1) (show 0 < a + b + c by linarith)]
  · rw [div_lt_iff₀ hbc]
    nlinarith [mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]

/-- For fixed sides of a nondegenerate triangle and `K ≠ 0` near `0`, the angles given by the
cosine law satisfy the constant-curvature sine law (C9.5–C9.7). -/
theorem sec9_sine_law_near_zero {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    ∀ᶠ K in 𝓝[≠] (0 : ℝ),
      Real.sin (angleK K a b c) / S K a = Real.sin (angleK K b c a) / S K b ∧
      Real.sin (angleK K b c a) / S K b = Real.sin (angleK K c a b) / S K c := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS : ∀ {x : ℝ}, 0 < x → ∀ᶠ K in 𝓝 (0 : ℝ), 0 < S K x := fun {x} hx =>
    (continuousAt_S_param h0 x).tendsto.eventually (lt_mem_nhds (by simpa [S_of_eq_zero] using hx))
  have hcos : ∀ {x y z : ℝ}, 0 < y → 0 < z → cosLaw 0 x y z ∈ Ioo (-1 : ℝ) 1 →
      ∀ᶠ K in 𝓝 (0 : ℝ), cosLaw K x y z ∈ Ioo (-1 : ℝ) 1 := fun {x y z} hy hz hm =>
    (continuousAt_cosLaw h0 x y z (by simpa [S_of_eq_zero] using (mul_pos hy hz).ne')).tendsto
      |>.eventually (Ioo_mem_nhds (by simpa using hm.1) (by simpa using hm.2))
  have hI : ∀ᶠ K in 𝓝 (0 : ℝ), K ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hS ha), mem_nhdsWithin_of_mem_nhds (hS hb),
    mem_nhdsWithin_of_mem_nhds (hS hc),
    mem_nhdsWithin_of_mem_nhds (hcos hb hc (cosLaw_zero_mem_Ioo hb hc h1 h2 h3)),
    mem_nhdsWithin_of_mem_nhds (hcos hc ha (cosLaw_zero_mem_Ioo hc ha h2 h3 h1)),
    mem_nhdsWithin_of_mem_nhds (hcos ha hb (cosLaw_zero_mem_Ioo ha hb h3 h1 h2)),
    self_mem_nhdsWithin] with K hSa hSb hSc hA hB hC hK
  have hK0 : K ≠ 0 := hK
  exact sec9_sine_law_of_cos_law hK0 hSa hSb hSc
    (angleK_pos_lt_pi hA).1 (angleK_pos_lt_pi hA).2
    (angleK_pos_lt_pi hB).1 (angleK_pos_lt_pi hB).2
    (angleK_pos_lt_pi hC).1 (angleK_pos_lt_pi hC).2
    (cos_law_angleK hK0 hSb.ne' hSc.ne' hA) (cos_law_angleK hK0 hSc.ne' hSa.ne' hB)
    (cos_law_angleK hK0 hSa.ne' hSb.ne' hC)

/-- **C9.8.** Fix side lengths `a, b, c` of a nondegenerate triangle. The angles
`A_K = angleK K a b c`, `B_K = angleK K b c a`, `C_K = angleK K c a b` given by the
constant-curvature cosine law depend continuously on `K` near `0`, and `A_K → A_0`, `B_K → B_0`,
`C_K → C_0`; `S_K(x) → x` (`tendsto_S_zero`); and the constant-curvature sine law passes to the
limit: `sin A_0 / a = sin B_0 / b = sin C_0 / c`. -/
theorem sec9_limit {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    (∀ᶠ K in 𝓝 (0 : ℝ), ContinuousAt (fun K => angleK K a b c) K ∧
        ContinuousAt (fun K => angleK K b c a) K ∧ ContinuousAt (fun K => angleK K c a b) K) ∧
    Tendsto (fun K => angleK K a b c) (𝓝 0) (𝓝 (angleK 0 a b c)) ∧
    Tendsto (fun K => angleK K b c a) (𝓝 0) (𝓝 (angleK 0 b c a)) ∧
    Tendsto (fun K => angleK K c a b) (𝓝 0) (𝓝 (angleK 0 c a b)) ∧
    (Real.sin (angleK 0 a b c) / a = Real.sin (angleK 0 b c a) / b ∧
      Real.sin (angleK 0 b c a) / b = Real.sin (angleK 0 c a b) / c) := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS0 : ∀ {x y : ℝ}, 0 < x → 0 < y → S 0 x * S 0 y ≠ 0 := fun {x y} hx hy => by
    rw [S_of_eq_zero, S_of_eq_zero]
    exact (mul_pos hx hy).ne'
  -- continuity near `0`
  have hcont : ∀ {x y z : ℝ}, 0 < y → 0 < z →
      ∀ᶠ K in 𝓝 (0 : ℝ), ContinuousAt (fun K => angleK K x y z) K := by
    intro x y z hy hz
    have hne : ∀ᶠ K in 𝓝 (0 : ℝ), S K y * S K z ≠ 0 :=
      ((continuousAt_S_param h0 y).mul (continuousAt_S_param h0 z)).tendsto.eventually
        (isOpen_ne.mem_nhds (hS0 hy hz))
    filter_upwards [hne, Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with K hK hKI
    exact continuousAt_angleK hKI x y z hK
  have hA := continuousAt_angleK h0 a b c (hS0 hb hc)
  have hB := continuousAt_angleK h0 b c a (hS0 hc ha)
  have hC := continuousAt_angleK h0 c a b (hS0 ha hb)
  refine ⟨?_, hA.tendsto, hB.tendsto, hC.tendsto, ?_⟩
  · filter_upwards [hcont (x := a) hb hc, hcont (x := b) hc ha, hcont (x := c) ha hb]
      with K h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- pass to the limit in the sine law
  have hF : ∀ {x y z : ℝ}, 0 < x → 0 < y → 0 < z →
      ContinuousAt (fun K => Real.sin (angleK K x y z) / S K x) 0 := by
    intro x y z hx hy hz
    exact (Real.continuous_sin.continuousAt.comp (continuousAt_angleK h0 x y z (hS0 hy hz))).div
      (continuousAt_S_param h0 x) (by simpa [S_of_eq_zero] using hx.ne')
  have hev := sec9_sine_law_near_zero ha hb hc h1 h2 h3
  have hle : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have e1 := tendsto_nhds_unique ((hF ha hb hc).tendsto.mono_left hle)
    (((hF hb hc ha).tendsto.mono_left hle).congr' (hev.mono fun K hK => hK.1.symm))
  have e2 := tendsto_nhds_unique ((hF hb hc ha).tendsto.mono_left hle)
    (((hF hc ha hb).tendsto.mono_left hle).congr' (hev.mono fun K hK => hK.2.symm))
  simp only [S_of_eq_zero] at e1 e2
  exact ⟨e1, e2⟩

/-! ### `K = 0`: the Euclidean triangle -/

section Euclidean

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- For a Euclidean triangle, the angle given by the cosine law with `K = 0` is the Euclidean
angle (Euclidean law of cosines). -/
theorem angleK_zero_eq_angle {p₁ p₂ p₃ : P} (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) :
    angleK 0 (dist p₂ p₃) (dist p₁ p₃) (dist p₁ p₂) = ∠ p₂ p₁ p₃ := by
  have hlaw := law_cos p₂ p₁ p₃
  rw [dist_comm p₂ p₁, dist_comm p₃ p₁] at hlaw
  have hb : dist p₁ p₃ ≠ 0 := dist_ne_zero.mpr h₁₃
  have hc : dist p₁ p₂ ≠ 0 := dist_ne_zero.mpr h₁₂
  have hcos : (dist p₁ p₃ ^ 2 + dist p₁ p₂ ^ 2 - dist p₂ p₃ ^ 2) /
      (2 * dist p₁ p₃ * dist p₁ p₂) = Real.cos (∠ p₂ p₁ p₃) := by
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero hb) hc)]
    linear_combination -hlaw
  rw [angleK, cosLaw_zero, hcos, Real.arccos_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _)]

/-- Strict triangle inequality for a nondegenerate triangle. -/
theorem dist_lt_add_of_not_collinear {p₁ p₂ p₃ : P}
    (h : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₂ p₃ < dist p₃ p₁ + dist p₁ p₂ := by
  have hw : ¬ Wbtw ℝ p₂ p₁ p₃ := fun hw => h (hw.collinear.subset (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto))
  have := dist_lt_dist_add_dist_iff.mpr hw
  rw [dist_comm p₂ p₁, dist_comm p₁ p₃] at this
  linarith

private theorem not_collinear_rotate {p₁ p₂ p₃ : P} (h : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ¬ Collinear ℝ ({p₂, p₃, p₁} : Set P) := fun h' => h (h'.subset (by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto))

/-- **C9.8** (conclusion). The Euclidean sine law, obtained as the `K → 0` limit of the
constant-curvature sine law: for a nondegenerate triangle `p₁ p₂ p₃` with angles
`A = ∠ p₂ p₁ p₃`, `B = ∠ p₃ p₂ p₁`, `C = ∠ p₁ p₃ p₂` and opposite sides
`a = |p₂ p₃|`, `b = |p₃ p₁|`, `c = |p₁ p₂|`: `sin A / a = sin B / b = sin C / c`. -/
theorem sec9_euclidean_sine_law {p₁ p₂ p₃ : P} (h : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    Real.sin (∠ p₂ p₁ p₃) / dist p₂ p₃ = Real.sin (∠ p₃ p₂ p₁) / dist p₃ p₁ ∧
      Real.sin (∠ p₃ p₂ p₁) / dist p₃ p₁ = Real.sin (∠ p₁ p₃ p₂) / dist p₁ p₂ := by
  have h' := not_collinear_rotate h
  have h'' := not_collinear_rotate h'
  have h₁₂ := ne₁₂_of_not_collinear h
  have h₁₃ := ne₁₃_of_not_collinear h
  have h₂₃ := ne₂₃_of_not_collinear h
  have ha : 0 < dist p₂ p₃ := dist_pos.mpr h₂₃
  have hb : 0 < dist p₃ p₁ := dist_pos.mpr h₁₃.symm
  have hc : 0 < dist p₁ p₂ := dist_pos.mpr h₁₂
  have t1 := dist_lt_add_of_not_collinear h
  have t2 := dist_lt_add_of_not_collinear h'
  have t3 := dist_lt_add_of_not_collinear h''
  have hA : angleK 0 (dist p₂ p₃) (dist p₃ p₁) (dist p₁ p₂) = ∠ p₂ p₁ p₃ := by
    rw [dist_comm p₃ p₁]
    exact angleK_zero_eq_angle h₁₂ h₁₃
  have hB : angleK 0 (dist p₃ p₁) (dist p₁ p₂) (dist p₂ p₃) = ∠ p₃ p₂ p₁ := by
    rw [dist_comm p₁ p₂]
    exact angleK_zero_eq_angle h₂₃ h₁₂.symm
  have hC : angleK 0 (dist p₁ p₂) (dist p₂ p₃) (dist p₃ p₁) = ∠ p₁ p₃ p₂ := by
    rw [dist_comm p₂ p₃]
    exact angleK_zero_eq_angle h₁₃.symm h₂₃.symm
  have hlim := (sec9_limit ha hb hc t1 t2 t3).2.2.2.2
  rwa [hA, hB, hC] at hlim

end Euclidean

end PythagoreanPaper
