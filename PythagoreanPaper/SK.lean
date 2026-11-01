import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The geodesic-deviation function `S_K` and its companion `C_K`

Manuscript references (「循環構造と収束構造の曲率的統一」):

* §4: `S_K` is the solution of `j'' + K j = 0`, `j(0) = 0`, `j'(0) = 1`, given by cases on the
  sign of `K`: `sin (√K r) / √K`, `r`, `sinh (√(-K) r) / √(-K)`.
* §5: `C_K(r) = ∑ (-K)^m r^(2m) / (2m)!` and `S_K(r) = ∑ (-K)^m r^(2m+1) / (2m+1)!`.
* §9: `C_K = S_K'` and `C_K² + K S_K² = 1`; for `K > 0` and `0 < x < π/√K`, `S_K(x) > 0`.

`S` and `C` are defined below by these closed forms. Every property quoted above is a theorem of
this file: `hasDerivAt_S`, `hasDerivAt_C`, `S_zero`, `C_zero` (the initial value problem),
`eq_of_ode` and `eq_S_of_ode` (uniqueness), `hasSum_C`, `hasSum_S` (the series of §5),
`C_sq_add_mul_S_sq` and `S_pos` (§9).
-/

noncomputable section

open Real Nat

namespace PythagoreanPaper

/-- `S_K(r)` of manuscript §4. -/
def S (K r : ℝ) : ℝ :=
  if 0 < K then Real.sin (√K * r) / √K
  else if K = 0 then r
  else Real.sinh (√(-K) * r) / √(-K)

/-- `C_K(r)`: the closed form of the series that defines `C_K` in manuscript §5
(the series identity is `hasSum_C`). -/
def C (K r : ℝ) : ℝ :=
  if 0 < K then Real.cos (√K * r)
  else if K = 0 then 1
  else Real.cosh (√(-K) * r)

section Cases

variable {K : ℝ} (r : ℝ)

theorem S_of_pos (hK : 0 < K) : S K r = Real.sin (√K * r) / √K := by
  rw [S, ite_eq_left hK]

theorem S_of_eq_zero : S 0 r = r := by
  rw [S, ite_eq_right (lt_irrefl 0), ite_eq_left rfl]

theorem S_of_neg (hK : K < 0) : S K r = Real.sinh (√(-K) * r) / √(-K) := by
  rw [S, ite_eq_right (not_lt.mpr hK.le), ite_eq_right hK.ne]

theorem C_of_pos (hK : 0 < K) : C K r = Real.cos (√K * r) := by
  rw [C, ite_eq_left hK]

theorem C_of_eq_zero : C 0 r = 1 := by
  rw [C, ite_eq_right (lt_irrefl 0), ite_eq_left rfl]

theorem C_of_neg (hK : K < 0) : C K r = Real.cosh (√(-K) * r) := by
  rw [C, ite_eq_right (not_lt.mpr hK.le), ite_eq_right hK.ne]

end Cases

/-! ### The initial value problem of §4 -/

@[simp] theorem S_zero (K : ℝ) : S K 0 = 0 := by
  unfold S
  split_ifs <;> simp

@[simp] theorem C_zero (K : ℝ) : C K 0 = 1 := by
  unfold C
  split_ifs <;> simp

/-- `S_K' = C_K` (manuscript §9: `C_K(x) = S_K'(x)`). -/
theorem hasDerivAt_S (K r : ℝ) : HasDerivAt (S K) (C K r) r := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · have hs : √(-K) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hK)).ne'
    have h := (((hasDerivAt_id' r).const_mul (√(-K))).sinh).div_const (√(-K))
    have hfun : S K = fun x => Real.sinh (√(-K) * x) / √(-K) := funext fun x => S_of_neg x hK
    rw [hfun, C_of_neg r hK]
    convert h using 1
    rw [mul_one, mul_div_assoc, div_self hs, mul_one]
  · have hfun : S 0 = fun x => x := funext fun x => S_of_eq_zero x
    rw [hfun, C_of_eq_zero]
    exact hasDerivAt_id' r
  · have hs : √K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
    have h := (((hasDerivAt_id' r).const_mul (√K)).sin).div_const (√K)
    have hfun : S K = fun x => Real.sin (√K * x) / √K := funext fun x => S_of_pos x hK
    rw [hfun, C_of_pos r hK]
    convert h using 1
    rw [mul_one, mul_div_assoc, div_self hs, mul_one]

/-- `C_K' = -K S_K`. -/
theorem hasDerivAt_C (K r : ℝ) : HasDerivAt (C K) (-K * S K r) r := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · have hs : √(-K) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hK)).ne'
    have hsq : -K = √(-K) * √(-K) := (Real.mul_self_sqrt (neg_nonneg.mpr hK.le)).symm
    have hKs : -K / √(-K) = √(-K) := by rw [div_eq_iff hs]; exact hsq
    have h := ((hasDerivAt_id' r).const_mul (√(-K))).cosh
    have hfun : C K = fun x => Real.cosh (√(-K) * x) := funext fun x => C_of_neg x hK
    rw [hfun, S_of_neg r hK]
    convert h using 1
    calc -K * (Real.sinh (√(-K) * r) / √(-K))
        = (-K / √(-K)) * Real.sinh (√(-K) * r) := by ring
      _ = √(-K) * Real.sinh (√(-K) * r) := by rw [hKs]
      _ = Real.sinh (√(-K) * r) * (√(-K) * 1) := by ring
  · have hfun : C 0 = fun _ => (1 : ℝ) := funext fun x => C_of_eq_zero x
    rw [hfun]
    convert hasDerivAt_const r (1 : ℝ) using 1
    ring
  · have hs : √K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
    have hsq : K = √K * √K := (Real.mul_self_sqrt hK.le).symm
    have hKs : K / √K = √K := by rw [div_eq_iff hs]; exact hsq
    have h := ((hasDerivAt_id' r).const_mul (√K)).cos
    have hfun : C K = fun x => Real.cos (√K * x) := funext fun x => C_of_pos x hK
    rw [hfun, S_of_pos r hK]
    convert h using 1
    calc -K * (Real.sin (√K * r) / √K)
        = -(K / √K) * Real.sin (√K * r) := by ring
      _ = -√K * Real.sin (√K * r) := by rw [hKs]
      _ = -Real.sin (√K * r) * (√K * 1) := by ring

/-- `S_K` solves the initial value problem of §4: `S_K'' + K S_K = 0`, `S_K(0) = 0`,
`S_K'(0) = 1` (with `S_K' = C_K` and `S_K'' = C_K' = -K S_K`). -/
theorem S_solves_ivp (K : ℝ) :
    (∀ r, HasDerivAt (S K) (C K r) r) ∧ (∀ r, HasDerivAt (C K) (-K * S K r) r) ∧
      (∀ r, -K * S K r + K * S K r = 0) ∧ S K 0 = 0 ∧ C K 0 = 1 :=
  ⟨hasDerivAt_S K, hasDerivAt_C K, fun r => by ring, S_zero K, C_zero K⟩

/-- Uniqueness for `j'' + K j = 0` on an open interval `I ∋ 0`: on `I`, a solution is determined
by `j(0)` and `j'(0)`, namely `j = j(0) C_K + j'(0) S_K`. -/
theorem eqOn_of_ode {K a b : ℝ} {j j' j'' : ℝ → ℝ} (hI : (0 : ℝ) ∈ Set.Ioo a b)
    (hj : ∀ r ∈ Set.Ioo a b, HasDerivAt j (j' r) r)
    (hj' : ∀ r ∈ Set.Ioo a b, HasDerivAt j' (j'' r) r)
    (hode : ∀ r ∈ Set.Ioo a b, j'' r + K * j r = 0) :
    Set.EqOn j (fun r => j 0 * C K r + j' 0 * S K r) (Set.Ioo a b) := by
  -- the linear vector field `(x, y) ↦ (y, -K x)` of the first-order system
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-K • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hL : ∀ x y : ℝ, L (x, y) = (y, -K * x) := by
    intro x y
    simp [L]
  have hf : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun t => (j t, j' t)) (L (j t, j' t)) t ∧
      (j t, j' t) ∈ (Set.univ : Set (ℝ × ℝ)) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    have h2 : j'' t = -K * j t := by linarith [hode t ht]
    have h := (hj t ht).prodMk (hj' t ht)
    rw [h2] at h
    rw [hL]
    exact h
  have hg : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun t => (j 0 * C K t + j' 0 * S K t, -K * j 0 * S K t + j' 0 * C K t))
        (L (j 0 * C K t + j' 0 * S K t, -K * j 0 * S K t + j' 0 * C K t)) t ∧
      (j 0 * C K t + j' 0 * S K t, -K * j 0 * S K t + j' 0 * C K t) ∈
        (Set.univ : Set (ℝ × ℝ)) := by
    intro t _
    refine ⟨?_, Set.mem_univ _⟩
    have h1 := ((hasDerivAt_C K t).const_mul (j 0)).add ((hasDerivAt_S K t).const_mul (j' 0))
    have h2 :=
      ((hasDerivAt_S K t).const_mul (-K * j 0)).add ((hasDerivAt_C K t).const_mul (j' 0))
    rw [hL]
    convert h1.prodMk h2 using 1
    rw [Prod.mk.injEq]
    constructor <;> ring
  have h := ODE_solution_unique_of_mem_Ioo (v := fun _ => L) (s := fun _ => Set.univ)
    (fun _ _ => L.lipschitzWith.lipschitzOnWith) hI hf hg (by simp)
  intro r hr
  exact congrArg Prod.fst (h hr)

/-- Uniqueness for `j'' + K j = 0` on `ℝ`. -/
theorem eq_of_ode {K : ℝ} {j j' j'' : ℝ → ℝ}
    (hj : ∀ r, HasDerivAt j (j' r) r) (hj' : ∀ r, HasDerivAt j' (j'' r) r)
    (hode : ∀ r, j'' r + K * j r = 0) :
    j = fun r => j 0 * C K r + j' 0 * S K r := by
  funext r
  have hI : (0 : ℝ) ∈ Set.Ioo (-(|r| + 1)) (|r| + 1) :=
    ⟨by linarith [abs_nonneg r], by linarith [abs_nonneg r]⟩
  exact eqOn_of_ode hI (fun t _ => hj t) (fun t _ => hj' t) (fun t _ => hode t)
    ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩

/-- §4: on an open interval `I ∋ 0`, the solution of `j'' + K j = 0` with `j(0) = 0`,
`j'(0) = 1` is `S_K`. -/
theorem eqOn_S_of_ode {K a b : ℝ} {j j' j'' : ℝ → ℝ} (hI : (0 : ℝ) ∈ Set.Ioo a b)
    (hj : ∀ r ∈ Set.Ioo a b, HasDerivAt j (j' r) r)
    (hj' : ∀ r ∈ Set.Ioo a b, HasDerivAt j' (j'' r) r)
    (hode : ∀ r ∈ Set.Ioo a b, j'' r + K * j r = 0) (h0 : j 0 = 0) (h1 : j' 0 = 1) :
    Set.EqOn j (S K) (Set.Ioo a b) := by
  intro r hr
  have h := eqOn_of_ode hI hj hj' hode hr
  simp only [h0, h1, zero_mul, one_mul, zero_add] at h
  exact h

/-- §4: the solution on `ℝ` of `j'' + K j = 0` with `j(0) = 0`, `j'(0) = 1` is `S_K`. -/
theorem eq_S_of_ode {K : ℝ} {j j' j'' : ℝ → ℝ}
    (hj : ∀ r, HasDerivAt j (j' r) r) (hj' : ∀ r, HasDerivAt j' (j'' r) r)
    (hode : ∀ r, j'' r + K * j r = 0) (h0 : j 0 = 0) (h1 : j' 0 = 1) :
    j = S K := by
  funext r
  have h := congrFun (eq_of_ode hj hj' hode) r
  simp only [h0, h1, zero_mul, one_mul, zero_add] at h
  exact h

/-! ### The series of §5 -/

theorem hasSum_C (K r : ℝ) :
    HasSum (fun m : ℕ => (-K) ^ m * r ^ (2 * m) / ↑(2 * m)!) (C K r) := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [C_of_neg r hK]
    convert Real.hasSum_cosh (√(-K) * r) using 1
    funext m
    rw [mul_pow, pow_mul (√(-K)) 2 m, Real.sq_sqrt (neg_nonneg.mpr hK.le)]
  · rw [C_of_eq_zero]
    convert hasSum_single (f := fun m : ℕ => (-(0 : ℝ)) ^ m * r ^ (2 * m) / ↑(2 * m)!) 0
      (fun m hm => by simp [zero_pow hm]) using 1
    simp
  · rw [C_of_pos r hK]
    convert Real.hasSum_cos (√K * r) using 1
    funext m
    rw [mul_pow, pow_mul (√K) 2 m, Real.sq_sqrt hK.le, neg_pow K m]
    ring

theorem hasSum_S (K r : ℝ) :
    HasSum (fun m : ℕ => (-K) ^ m * r ^ (2 * m + 1) / ↑(2 * m + 1)!) (S K r) := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · have hs : √(-K) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hK)).ne'
    rw [S_of_neg r hK]
    convert (Real.hasSum_sinh (√(-K) * r)).div_const (√(-K)) using 1
    funext m
    rw [eq_div_iff hs, mul_pow, pow_succ (√(-K)) (2 * m), pow_mul (√(-K)) 2 m,
      Real.sq_sqrt (neg_nonneg.mpr hK.le)]
    ring
  · rw [S_of_eq_zero]
    convert hasSum_single (f := fun m : ℕ => (-(0 : ℝ)) ^ m * r ^ (2 * m + 1) / ↑(2 * m + 1)!) 0
      (fun m hm => by simp [zero_pow hm]) using 1
    simp
  · have hs : √K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
    rw [S_of_pos r hK]
    convert (Real.hasSum_sin (√K * r)).div_const (√K) using 1
    funext m
    rw [eq_div_iff hs, mul_pow, pow_succ (√K) (2 * m), pow_mul (√K) 2 m, Real.sq_sqrt hK.le,
      neg_pow K m]
    ring

/-! ### The identities of §9 -/

/-- `C_K² + K S_K² = 1` (manuscript §9). -/
theorem C_sq_add_mul_S_sq (K r : ℝ) : C K r ^ 2 + K * S K r ^ 2 = 1 := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · have hs : √(-K) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hK)).ne'
    have hsq : √(-K) ^ 2 = -K := Real.sq_sqrt (neg_nonneg.mpr hK.le)
    have h : K * (Real.sinh (√(-K) * r) / √(-K)) ^ 2 = -Real.sinh (√(-K) * r) ^ 2 := by
      rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hs), hsq]
      ring
    rw [C_of_neg r hK, S_of_neg r hK, h, ← sub_eq_add_neg, Real.cosh_sq_sub_sinh_sq]
  · rw [C_of_eq_zero]
    ring
  · have hs : √K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
    have hsq : √K ^ 2 = K := Real.sq_sqrt hK.le
    have h : K * (Real.sin (√K * r) / √K) ^ 2 = Real.sin (√K * r) ^ 2 := by
      rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hs), hsq]
      ring
    rw [C_of_pos r hK, S_of_pos r hK, h, Real.cos_sq_add_sin_sq]

/-- Manuscript §9: for `K > 0` and `0 < x < π/√K`, `S_K(x) > 0`. -/
theorem S_pos {K x : ℝ} (hK : 0 < K) (hx : 0 < x) (hxK : x < π / √K) : 0 < S K x := by
  have hs : 0 < √K := Real.sqrt_pos.mpr hK
  rw [S_of_pos x hK]
  refine div_pos ?_ hs
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hs hx)
  rw [lt_div_iff₀ hs] at hxK
  linarith

/-- For `K ≤ 0` and `x > 0`, `S_K(x) > 0` (used in §9 for `K < 0`). -/
theorem S_pos_of_nonpos {K x : ℝ} (hK : K ≤ 0) (hx : 0 < x) : 0 < S K x := by
  rcases hK.lt_or_eq with hK | rfl
  · have hs : 0 < √(-K) := Real.sqrt_pos.mpr (neg_pos.mpr hK)
    rw [S_of_neg x hK]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hs hx)) hs
  · rw [S_of_eq_zero]
    exact hx

/-- `S_K(x) ≥ 0` for `x ≥ 0`, and `x ≤ π/√K` if `K > 0`. -/
theorem S_nonneg {K x : ℝ} (hx : 0 ≤ x) (hxK : 0 < K → x ≤ π / √K) : 0 ≤ S K x := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · rw [S_zero]
  rcases lt_or_ge 0 K with hK | hK
  · rcases eq_or_lt_of_le (hxK hK) with h | h
    · have hs : √K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
      rw [h, S_of_pos _ hK, mul_div_cancel₀ _ hs, Real.sin_pi, zero_div]
    · exact (S_pos hK hx0 h).le
  · exact (S_pos_of_nonpos hK hx0).le

/-- `C_K` is even. -/
theorem C_neg (K x : ℝ) : C K (-x) = C K x := by
  unfold C
  split_ifs <;> simp [Real.cos_neg, Real.cosh_neg, mul_neg]

/-- `S_K` is odd. -/
theorem S_neg (K x : ℝ) : S K (-x) = -S K x := by
  unfold S
  split_ifs <;> simp [Real.sin_neg, Real.sinh_neg, mul_neg, neg_div]

/-- **Addition formula**: `C_K(x - y) = C_K(x) C_K(y) + K S_K(x) S_K(y)`. -/
theorem C_sub (K x y : ℝ) : C K (x - y) = C K x * C K y + K * S K x * S K y := by
  have hj : ∀ s, HasDerivAt (fun s ↦ C K (s - y)) (-K * S K (s - y)) s := fun s ↦ by
    have h1 := (hasDerivAt_C K (s - y)).comp s ((hasDerivAt_id' s).sub_const y)
    rw [mul_one] at h1
    exact h1
  have hj' : ∀ s, HasDerivAt (fun s ↦ -K * S K (s - y)) (-K * C K (s - y)) s := fun s ↦ by
    have h1 := ((hasDerivAt_S K (s - y)).comp s ((hasDerivAt_id' s).sub_const y)).const_mul (-K)
    rw [mul_one] at h1
    exact h1
  have h := congrFun (eq_of_ode hj hj' (fun s ↦ by ring)) x
  simp only [zero_sub, C_neg, S_neg] at h
  rw [h]
  ring

end PythagoreanPaper
