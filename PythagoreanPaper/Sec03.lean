import PythagoreanPaper.SK

/-!
# Manuscript §3 — the claims that are statements about functions of one variable

* C3.2: `j'' = 0`, `j(0) = 0`, `j'(0) = 1` give `j(r) = r` — on any open interval containing `0`
  (`sec3_linear_deviation`) and on `ℝ` (`sec3_linear_deviation_univ`).

C3.1 (the normal component of a Jacobi field satisfies `j'' = 0` in zero curvature) and C3.4
(flat manifolds with another global topology) need Riemannian geometry and are not in this file.
C3.3 is an interpretive proposition (the manuscript itself calls it 解釈的命題) and is not
formalized as a theorem.
-/

namespace PythagoreanPaper

/-- **C3.2.** On an open interval `I ∋ 0`: if `j'' = 0` on `I`, `j(0) = 0` and `j'(0) = 1`, then
`j(r) = r` on `I`. -/
theorem sec3_linear_deviation {a b : ℝ} {j j' j'' : ℝ → ℝ} (hI : (0 : ℝ) ∈ Set.Ioo a b)
    (hj : ∀ r ∈ Set.Ioo a b, HasDerivAt j (j' r) r)
    (hj' : ∀ r ∈ Set.Ioo a b, HasDerivAt j' (j'' r) r)
    (hode : ∀ r ∈ Set.Ioo a b, j'' r = 0) (h0 : j 0 = 0) (h1 : j' 0 = 1) :
    ∀ r ∈ Set.Ioo a b, j r = r := by
  intro r hr
  have h := eqOn_S_of_ode (K := 0) hI hj hj' (fun t ht => by simp [hode t ht]) h0 h1 hr
  rw [h, S_of_eq_zero]

/-- **C3.2** on `ℝ`. -/
theorem sec3_linear_deviation_univ {j j' j'' : ℝ → ℝ}
    (hj : ∀ r, HasDerivAt j (j' r) r) (hj' : ∀ r, HasDerivAt j' (j'' r) r)
    (hode : ∀ r, j'' r = 0) (h0 : j 0 = 0) (h1 : j' 0 = 1) : ∀ r, j r = r := by
  have h := eq_S_of_ode (K := 0) hj hj' (fun r => by simp [hode r]) h0 h1
  intro r
  rw [h, S_of_eq_zero]

end PythagoreanPaper
