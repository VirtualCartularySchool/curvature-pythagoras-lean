import PythagoreanPaper.SK

/-!
# Manuscript §4 — the solution `S_K` of the initial value problem

* C4.3: the solution of `j'' + K j = 0`, `j(0) = 0`, `j'(0) = 1` is `S_K`, which is
  `sin (√K r) / √K` for `K > 0`, `r` for `K = 0`, `sinh (√(-K) r) / √(-K)` for `K < 0`
  (the definition `S` and `S_of_pos`, `S_of_eq_zero`, `S_of_neg`).

* C4.4 (the reading of the descriptive sentences is to be confirmed): for `K > 0` the width
  `S_K` opens and then closes again (`sec4_opens_then_closes`); for `K = 0` it opens linearly
  (`sec4_opens_linearly`); for `K < 0` it opens hyperbolically, strictly increasing and faster
  than linearly (`sec4_opens_hyperbolically`).

C4.1 and C4.2 (the Jacobi equation on a Riemannian manifold and its normal-component reduction)
need Riemannian geometry and are not in this file.
-/

open Real

namespace PythagoreanPaper

/-- **C4.3.** `S_K` solves `j'' + K j = 0` with `j(0) = 0`, `j'(0) = 1` on `ℝ` (here `S_K' = C_K`
and `S_K'' = C_K' = -K S_K`), and on every open interval containing `0` it is the only
solution. -/
theorem sec4_S_is_the_solution (K : ℝ) :
    ((∀ r, HasDerivAt (S K) (C K r) r) ∧ (∀ r, HasDerivAt (C K) (-K * S K r) r) ∧
      (∀ r, -K * S K r + K * S K r = 0) ∧ S K 0 = 0 ∧ C K 0 = 1) ∧
    ∀ {a b : ℝ} {j j' j'' : ℝ → ℝ}, (0 : ℝ) ∈ Set.Ioo a b →
      (∀ r ∈ Set.Ioo a b, HasDerivAt j (j' r) r) →
      (∀ r ∈ Set.Ioo a b, HasDerivAt j' (j'' r) r) →
      (∀ r ∈ Set.Ioo a b, j'' r + K * j r = 0) → j 0 = 0 → j' 0 = 1 →
      Set.EqOn j (S K) (Set.Ioo a b) :=
  ⟨S_solves_ivp K, fun hI hj hj' hode h0 h1 => eqOn_S_of_ode hI hj hj' hode h0 h1⟩

/-- **C4.4**, `K > 0` (reading to be confirmed): the width opens and then closes again. `S_K` is
strictly increasing on `[0, π/(2√K)]`, strictly decreasing on `[π/(2√K), π/√K]`, positive on
`(0, π/√K)`, and `S_K(π/√K) = 0`. -/
theorem sec4_opens_then_closes {K : ℝ} (hK : 0 < K) :
    StrictMonoOn (S K) (Set.Icc 0 (π / 2 / √K)) ∧
      StrictAntiOn (S K) (Set.Icc (π / 2 / √K) (π / √K)) ∧
      (∀ r ∈ Set.Ioo 0 (π / √K), 0 < S K r) ∧ S K (π / √K) = 0 := by
  have hs : 0 < √K := Real.sqrt_pos.mpr hK
  have hS : S K = fun r => Real.sin (√K * r) / √K := funext fun r => S_of_pos r hK
  have hle : ∀ {x y : ℝ}, x ≤ y / √K → √K * x ≤ y := fun {x y} h => by
    rw [le_div_iff₀ hs] at h
    linarith
  refine ⟨?_, ?_, fun r hr => S_pos hK hr.1 hr.2, ?_⟩
  · intro x hx y hy hxy
    rw [hS]
    apply div_lt_div_of_pos_right _ hs
    apply strictMonoOn_sin ⟨_, hle hx.2⟩ ⟨_, hle hy.2⟩ (mul_lt_mul_of_pos_left hxy hs)
    · nlinarith [hx.1, pi_pos]
    · nlinarith [hy.1, pi_pos]
  · intro x hx y hy hxy
    rw [hS]
    apply div_lt_div_of_pos_right _ hs
    rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two]
    have hx1 : π / 2 ≤ √K * x := by
      have := hx.1
      rw [div_le_iff₀ hs] at this
      linarith
    have hy1 : π / 2 ≤ √K * y := by
      have := hy.1
      rw [div_le_iff₀ hs] at this
      linarith
    have hx2 : √K * x ≤ π := hle hx.2
    have hy2 : √K * y ≤ π := hle hy.2
    apply strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    linarith [mul_lt_mul_of_pos_left hxy hs]
  · rw [S_of_pos _ hK, mul_div_cancel₀ _ hs.ne', sin_pi, zero_div]

/-- **C4.4**, `K = 0`: the width opens linearly, `S_0(r) = r`. -/
theorem sec4_opens_linearly : S 0 = fun r => r := funext fun r => S_of_eq_zero r

/-- **C4.4**, `K < 0` (reading to be confirmed): the width opens hyperbolically. `S_K` is strictly
increasing, and for `r > 0` it is larger than the linear width: `r < S_K(r)`. -/
theorem sec4_opens_hyperbolically {K : ℝ} (hK : K < 0) :
    StrictMono (S K) ∧ ∀ r, 0 < r → r < S K r := by
  have hs : 0 < √(-K) := Real.sqrt_pos.mpr (neg_pos.mpr hK)
  have hS : S K = fun r => Real.sinh (√(-K) * r) / √(-K) := funext fun r => S_of_neg r hK
  refine ⟨?_, fun r hr => ?_⟩
  · intro x y hxy
    rw [hS]
    exact div_lt_div_of_pos_right (Real.sinh_strictMono (mul_lt_mul_of_pos_left hxy hs)) hs
  · rw [hS, lt_div_iff₀ hs, mul_comm]
    exact Real.self_lt_sinh_iff.mpr (mul_pos hs hr)

end PythagoreanPaper
