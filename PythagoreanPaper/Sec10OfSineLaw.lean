import PythagoreanPaper.Sec10

/-!
# Manuscript §10 from a Euclidean sine law

The Jackson–Johnson argument of §10 (`PythagoreanPaper.Sec10`) uses the Euclidean sine law (the
conclusion of C9.8) together with basic facts of Euclidean geometry from Mathlib (angle sum,
betweenness and addition of angles, continuity of angles, `C–B–D` order of points). In
`PythagoreanPaper.Sec10` the sine law is the theorem `sec9_euclidean_sine_law`.

This file repeats the argument with the sine law as a hypothesis `hSL : EuclideanSineLaw V P`, so
that it can be combined with any proof of the sine law. The proofs are those of
`PythagoreanPaper.Sec10`, with `sec9_euclidean_sine_law` replaced by `hSL` and `sec10_*` by
`sec10_*_of_sineLaw`; the statements are those of `PythagoreanPaper.Sec10` with the extra
hypothesis. The theorems of `PythagoreanPaper.Sec10` are not changed.

`PythagoreanPaper.CurvatureChain` combines this file with the sine law obtained through the
Riemannian layer (`CurvatureChain.euclidean_sine_law`), realizing the chain of manuscript §12 as
one formal dependency.
-/

noncomputable section

open Real Set Filter Topology EuclideanGeometry

namespace PythagoreanPaper

/-- **The Euclidean sine law in `P`** (the statement of `sec9_euclidean_sine_law`): for a
nondegenerate triangle `p₁ p₂ p₃` with angles `A = ∠ p₂ p₁ p₃`, `B = ∠ p₃ p₂ p₁`, `C = ∠ p₁ p₃ p₂`
and opposite sides `a = |p₂ p₃|`, `b = |p₃ p₁|`, `c = |p₁ p₂|`: `sin A / a = sin B / b = sin C / c`.
-/
def EuclideanSineLaw (V P : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] : Prop :=
  ∀ ⦃p₁ p₂ p₃ : P⦄, ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P) →
    Real.sin (∠ p₂ p₁ p₃) / dist p₂ p₃ = Real.sin (∠ p₃ p₂ p₁) / dist p₃ p₁ ∧
      Real.sin (∠ p₃ p₂ p₁) / dist p₃ p₁ = Real.sin (∠ p₁ p₃ p₂) / dist p₁ p₂

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

private theorem not_collinear_mono {s t : Set P} (h : ¬ Collinear ℝ s) (hst : s ⊆ t) :
    ¬ Collinear ℝ t := fun ht => h (ht.subset hst)

/-- **C10.1.** In a right triangle `ABC` with `∠C = 90°`: `α + β = 90°`, and `a < b` iff
`α < 45° < β`. -/
theorem sec10_setting_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2) :
    ∠ B A C + ∠ A B C = π / 2 ∧
      (dist B C < dist A C ↔ ∠ B A C < π / 4 ∧ π / 4 < ∠ A B C) := by
  have hsum : ∠ B A C + ∠ A B C = π / 2 := by
    have h := angle_add_angle_add_angle_eq_pi B hAC
    rw [angle_comm C A B, angle_comm B C A, hright] at h
    linarith
  refine ⟨hsum, ?_⟩
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hα0 : 0 < ∠ B A C := angle_pos_of_not_collinear (not_collinear_mono hnc (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto))
  have hβ0 : 0 < ∠ A B C := angle_pos_of_not_collinear hnc
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  -- the sine law of §9 in the triangle `ABC`
  have hsine : Real.sin (∠ B A C) / dist B C = Real.sin (∠ A B C) / dist A C := by
    have h := (hSL hnc).1
    rwa [angle_comm C B A, dist_comm C A] at h
  have hsα : 0 < Real.sin (∠ B A C) := sin_pos_of_pos_of_lt_pi hα0 (by linarith [pi_pos])
  have hsβ : 0 < Real.sin (∠ A B C) := sin_pos_of_pos_of_lt_pi hβ0 (by linarith [pi_pos])
  have hcross : Real.sin (∠ B A C) * dist A C = Real.sin (∠ A B C) * dist B C :=
    (div_eq_div_iff ha.ne' hb.ne').mp hsine
  -- `sin` is strictly increasing on `[-π/2, π/2]`
  have hmono : Real.sin (∠ B A C) < Real.sin (∠ A B C) ↔ ∠ B A C < ∠ A B C :=
    strictMonoOn_sin.lt_iff_lt ⟨by linarith [pi_pos], by linarith⟩
      ⟨by linarith [pi_pos], by linarith⟩
  constructor
  · intro hab
    have h1 : Real.sin (∠ B A C) < Real.sin (∠ A B C) := by
      nlinarith [mul_lt_mul_of_pos_left hab hsα]
    have h2 := hmono.mp h1
    constructor <;> linarith
  · rintro ⟨h1, -⟩
    have h2 : Real.sin (∠ B A C) < Real.sin (∠ A B C) := hmono.mpr (by linarith)
    nlinarith [mul_lt_mul_of_pos_right h2 ha]

/-- **C10.2** (the monotonicity argument). As `X(t)` moves from `B` along the extension of `CB`
beyond `B`, the angle `∠BAX(t)` is continuous and strictly increasing in `t ≥ 0`, starts at `0`,
stays below `β` and tends to `β`. -/
theorem sec10_angle_increases_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) :
    Continuous (fun t => ∠ B A (extPt B C t)) ∧
    StrictMonoOn (fun t => ∠ B A (extPt B C t)) (Ici 0) ∧
    ∠ B A (extPt B C 0) = 0 ∧
    (∀ t, 0 ≤ t → ∠ B A (extPt B C t) < ∠ A B C) ∧
    Tendsto (fun t => ∠ B A (extPt B C t)) atTop (𝓝 (∠ A B C)) := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hAB : A ≠ B := ne₁₂_of_not_collinear hnc
  have hsum := (sec10_setting_of_sineLaw hSL hAC hBC hright).1
  have hα0 : 0 < ∠ B A C := angle_pos_of_not_collinear (not_collinear_mono hnc (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto))
  have hβ0 : 0 < ∠ A B C := angle_pos_of_not_collinear hnc
  -- continuity
  have hcont : Continuous (fun t => ∠ B A (extPt B C t)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hc : Continuous (fun t : ℝ => (B, A, extPt B C t)) := by
      unfold extPt
      fun_prop
    exact (continuousAt_angle (x := (B, A, extPt B C t)) hAB.symm (extPt_ne hnc t)).comp
      (f := fun t : ℝ => (B, A, extPt B C t)) hc.continuousAt
  -- the value `0` at `t = 0`
  have h0 : ∠ B A (extPt B C 0) = 0 := by
    rw [extPt_zero]
    exact angle_self_of_ne hAB.symm
  -- strictly increasing: `∠BAX(s) + ∠X(s)AX(t) = ∠BAX(t)` and `∠X(s)AX(t) > 0`
  have hmono : StrictMonoOn (fun t => ∠ B A (extPt B C t)) (Ici 0) := by
    intro s hs t _ hst
    have hadd := angle_add_of_ne_of_ne hAB (extPt_ne hnc t).symm (wbtw_extPt B C hs hst.le)
    have hpos := angle_pos_of_not_collinear (not_collinear_extPt hnc hBC hst.ne)
    show ∠ B A (extPt B C s) < ∠ B A (extPt B C t)
    linarith
  -- in the triangle `A B X(t)`: `∠BAX(t) = β - ∠BX(t)A`
  have hncX : ∀ t, 0 < t → ¬ Collinear ℝ ({B, extPt B C t, A} : Set P) := by
    intro t ht
    have h1 := not_collinear_extPt hnc hBC (show (0 : ℝ) ≠ t from ht.ne)
    rw [extPt_zero] at h1
    exact not_collinear_mono h1 (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hrel : ∀ t, 0 < t → ∠ B A (extPt B C t) = ∠ A B C - ∠ B (extPt B C t) A := by
    intro t ht
    have hpi : ∠ C B (extPt B C t) = π := (sbtw_extPt hBC ht).angle₁₂₃_eq_pi
    have hext := angle_add_angle_eq_pi_of_angle_eq_pi A hpi
    have hs := angle_add_angle_add_angle_eq_pi (extPt B C t) hAB.symm
    rw [angle_comm (extPt B C t) A B] at hs
    linarith
  have hg0 : ∀ t, 0 < t → 0 < ∠ B (extPt B C t) A := fun t ht =>
    angle_pos_of_not_collinear (hncX t ht)
  have hlt : ∀ t, 0 ≤ t → ∠ B A (extPt B C t) < ∠ A B C := by
    intro t ht
    rcases ht.lt_or_eq with ht | rfl
    · rw [hrel t ht]
      linarith [hg0 t ht]
    · rw [h0]
      exact hβ0
  refine ⟨hcont, hmono, h0, hlt, ?_⟩
  -- the limit: `∠BX(t)A → 0`, since `sin ∠BX(t)A ≤ c / AX(t)` (sine law) and `AX(t) → ∞`
  have hc : 0 < dist A B := dist_pos.mpr hAB
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hden : Tendsto (fun t : ℝ => t * dist B C - dist A B) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-dist A B) (tendsto_id.atTop_mul_const ha)
    simpa [sub_eq_add_neg] using h
  have hup : Tendsto (fun t : ℝ => π / 2 * (dist A B / (t * dist B C - dist A B))) atTop
      (𝓝 0) := by
    simpa using (hden.const_div_atTop (dist A B)).const_mul (π / 2)
  have hbound : ∀ᶠ t in atTop,
      ∠ B (extPt B C t) A ≤ π / 2 * (dist A B / (t * dist B C - dist A B)) := by
    filter_upwards [eventually_gt_atTop 0, hden.eventually (eventually_gt_atTop 0)]
      with t ht hpos
    -- `dist X(t) A ≥ t a - c`
    have hXB : dist (extPt B C t) B = t * dist B C := by
      rw [extPt, dist_vadd_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        dist_eq_norm_vsub V B C]
    have hXA : t * dist B C - dist A B ≤ dist (extPt B C t) A := by
      linarith [dist_triangle (extPt B C t) A B]
    have hXA0 : 0 < dist (extPt B C t) A := lt_of_lt_of_le hpos hXA
    -- the sine law of §9 in the triangle `B X(t) A`
    have hsl := (hSL (hncX t ht)).1
    -- `hsl : sin ∠ X B A / dist X A = sin ∠ A X B / dist A B`
    have hsin : Real.sin (∠ B (extPt B C t) A) ≤ dist A B / (t * dist B C - dist A B) := by
      rw [angle_comm]
      have e : Real.sin (∠ A (extPt B C t) B) =
          dist A B * (Real.sin (∠ (extPt B C t) B A) / dist (extPt B C t) A) := by
        rw [hsl, mul_div_cancel₀ _ hc.ne']
      rw [e]
      calc dist A B * (Real.sin (∠ (extPt B C t) B A) / dist (extPt B C t) A)
          ≤ dist A B * (1 / dist (extPt B C t) A) := by
            gcongr
            exact sin_le_one _
        _ = dist A B / dist (extPt B C t) A := by rw [mul_one_div]
        _ ≤ dist A B / (t * dist B C - dist A B) := by gcongr
    -- Jordan's inequality: `x ≤ (π/2) sin x` on `[0, π/2]`
    have hg : ∠ B (extPt B C t) A ≤ π / 2 := by
      have := hrel t ht
      linarith [angle_nonneg B A (extPt B C t)]
    have hj := mul_le_sin (angle_nonneg B (extPt B C t) A) hg
    calc ∠ B (extPt B C t) A = π / 2 * (2 / π * ∠ B (extPt B C t) A) := by
          field_simp
      _ ≤ π / 2 * Real.sin (∠ B (extPt B C t) A) := by gcongr
      _ ≤ π / 2 * (dist A B / (t * dist B C - dist A B)) := by gcongr
  have hgt : Tendsto (fun t => ∠ B (extPt B C t) A) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun t => angle_nonneg _ _ _) hbound
  have h := (tendsto_const_nhds (x := ∠ A B C)).sub hgt
  rw [sub_zero] at h
  exact h.congr' ((eventually_gt_atTop 0).mono fun t ht => (hrel t ht).symm)

/-- **C10.2.** For `a < b` there is exactly one point `D` on the extension of `CB` beyond `B`
(`C–B–D`) with `∠BAD = α`. -/
theorem sec10_exists_unique_D_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) (hab : dist B C < dist A C) :
    ∃! D : P, Sbtw ℝ C B D ∧ ∠ B A D = ∠ B A C := by
  obtain ⟨hcont, hmono, h0, -, hlim⟩ := sec10_angle_increases_of_sineLaw hSL hAC hBC hright
  obtain ⟨hsum, hiff⟩ := sec10_setting_of_sineLaw hSL hAC hBC hright
  have hαβ : ∠ B A C < ∠ A B C := by
    have := hiff.mp hab
    linarith [this.1, this.2]
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hα0 : 0 < ∠ B A C := angle_pos_of_not_collinear (not_collinear_mono hnc (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto))
  -- a parameter `T > 0` with `∠BAX(T) > α`
  obtain ⟨T, hT, hT0⟩ := ((hlim.eventually (lt_mem_nhds hαβ)).and (eventually_gt_atTop 0)).exists
  -- intermediate value theorem on `[0, T]`
  have hmem : ∠ B A C ∈ Icc (∠ B A (extPt B C 0)) (∠ B A (extPt B C T)) :=
    ⟨by rw [h0]; exact hα0.le, hT.le⟩
  obtain ⟨t, ⟨ht0, -⟩, ht⟩ :=
    intermediate_value_Icc hT0.le hcont.continuousOn hmem
  have ht' : ∠ B A (extPt B C t) = ∠ B A C := ht
  have htpos : 0 < t := lt_of_le_of_ne ht0 (by
    rintro rfl
    rw [h0] at ht'
    linarith)
  refine ⟨extPt B C t, ⟨sbtw_extPt hBC htpos, ht'⟩, ?_⟩
  rintro D ⟨hD, hDα⟩
  obtain ⟨s, hs, rfl⟩ := exists_extPt_of_sbtw hD
  rw [hmono.injOn (mem_Ici.mpr hs.le) (mem_Ici.mpr htpos.le) (hDα.trans ht'.symm)]

/-- **C10.4.** `∠CAD = 2α`, `∠ACD = 90°`, `∠ADC = β - α` and `∠ADB = β - α`. -/
theorem sec10_angles_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C D : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hD : Sbtw ℝ C B D) (hDα : ∠ B A D = ∠ B A C) :
    ∠ C A D = 2 * ∠ B A C ∧ ∠ A C D = π / 2 ∧ ∠ A D C = ∠ A B C - ∠ B A C ∧
      ∠ A D B = ∠ A B C - ∠ B A C := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hsum := (sec10_setting_of_sineLaw hSL hAC hBC hright).1
  -- the ray `AB` lies between `AC` and `AD`
  have hCAD : ∠ C A D = 2 * ∠ B A C := by
    have h := angle_add_angle_eq_of_sbtw (p := A) hD
    rw [angle_comm C A B, hDα] at h
    linarith
  have hACD : ∠ A C D = π / 2 := by rw [← hD.angle_eq_right A, hright]
  have hAD : A ≠ D := fun h =>
    not_mem_line_of_not_collinear hnc (h ▸ mem_line_of_sbtw hBC hD)
  -- the angle sum of `ACD`
  have hADC : ∠ A D C = ∠ A B C - ∠ B A C := by
    have h := angle_add_angle_add_angle_eq_pi C hAD
    rw [angle_comm D A C, angle_comm C D A, hCAD, hACD] at h
    linarith
  have hADB : ∠ A D B = ∠ A D C := hD.symm.angle_eq_right A
  exact ⟨hCAD, hACD, hADC, hADB.trans hADC⟩

/-- **C10.5.** The sine law in `ACD` and in `ABD`: `CD / sin ∠CAD = AC / sin ∠ADC` and
`BD / sin ∠BAD = AB / sin ∠ADB`. -/
theorem sec10_sine_laws_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C D : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hD : Sbtw ℝ C B D) :
    dist C D / Real.sin (∠ C A D) = dist A C / Real.sin (∠ A D C) ∧
      dist B D / Real.sin (∠ B A D) = dist A B / Real.sin (∠ A D B) := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hDl := mem_line_of_sbtw hBC hD
  have hA := not_mem_line_of_not_collinear hnc
  have hACD : ¬ Collinear ℝ ({A, C, D} : Set P) := by
    intro h
    exact hA (affineSpan_pair_le_of_mem_of_mem (right_mem_affineSpan_pair ℝ B C) hDl
      (h.mem_affineSpan_of_mem_of_ne (p₁ := C) (p₂ := D) (p₃ := A) (by simp) (by simp)
        (by simp) hD.left_ne_right))
  have hABD : ¬ Collinear ℝ ({A, B, D} : Set P) := by
    intro h
    exact hA (affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair ℝ B C) hDl
      (h.mem_affineSpan_of_mem_of_ne (p₁ := B) (p₂ := D) (p₃ := A) (by simp) (by simp)
        (by simp) hD.ne_right))
  obtain ⟨h1, h2⟩ := hSL hACD
  obtain ⟨h3, h4⟩ := hSL hABD
  constructor
  · rw [← inv_div, h1.trans h2, inv_div]
  · rw [← inv_div, h3.trans h4, inv_div]

/-- **C10.6.** In the right triangle `ABC`: `sin α = a/c`, `cos α = b/c`, `sin β = b/c`,
`cos β = a/c`. -/
theorem sec10_right_ratios_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2) :
    Real.sin (∠ B A C) = dist B C / dist A B ∧ Real.cos (∠ B A C) = dist A C / dist A B ∧
      Real.sin (∠ A B C) = dist A C / dist A B ∧ Real.cos (∠ A B C) = dist B C / dist A B := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hsum := (sec10_setting_of_sineLaw hSL hAC hBC hright).1
  have hc : 0 < dist A B := dist_pos.mpr (ne₁₂_of_not_collinear hnc)
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  obtain ⟨h1, h2⟩ := hSL hnc
  rw [angle_comm C B A, dist_comm C A] at h1
  rw [angle_comm C B A, dist_comm C A, hright, Real.sin_pi_div_two] at h2
  -- `h1 : sin α / a = sin β / b`, `h2 : sin β / b = 1 / c`
  have hsβ : Real.sin (∠ A B C) = dist A C / dist A B := by
    rw [div_eq_div_iff hb.ne' hc.ne', one_mul] at h2
    rw [eq_div_iff hc.ne', h2]
  have hsα : Real.sin (∠ B A C) = dist B C / dist A B := by
    have h := h1.trans h2
    rw [div_eq_div_iff ha.ne' hc.ne', one_mul] at h
    rw [eq_div_iff hc.ne', h]
  have hcα : Real.cos (∠ B A C) = dist A C / dist A B := by
    rw [← Real.sin_pi_div_two_sub, show π / 2 - ∠ B A C = ∠ A B C by linarith, hsβ]
  have hcβ : Real.cos (∠ A B C) = dist B C / dist A B := by
    rw [← Real.sin_pi_div_two_sub, show π / 2 - ∠ A B C = ∠ B A C by linarith, hsα]
  exact ⟨hsα, hcα, hsβ, hcβ⟩

/-- **C10.7.** `sin 2α = 2 sin α cos α = 2ab/c²` and
`sin(β - α) = sin β cos α - cos β sin α = (b² - a²)/c²`. -/
theorem sec10_double_and_difference_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) :
    Real.sin (2 * ∠ B A C) = 2 * dist B C * dist A C / dist A B ^ 2 ∧
      Real.sin (∠ A B C - ∠ B A C) = (dist A C ^ 2 - dist B C ^ 2) / dist A B ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := sec10_right_ratios_of_sineLaw hSL hAC hBC hright
  constructor
  · rw [Real.sin_two_mul, h1, h2]
    ring
  · rw [Real.sin_sub, h3, h2, h4, h1]
    ring

/-- **C10.8.** The two expressions of `BD`: from `ACD`, `CD = 2ab²/(b² - a²)` and
`BD = CD - a = a(a² + b²)/(b² - a²)`; from `ABD`, `BD = ac²/(b² - a²)`. -/
theorem sec10_two_expressions_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C D : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) (hab : dist B C < dist A C)
    (hD : Sbtw ℝ C B D) (hDα : ∠ B A D = ∠ B A C) :
    dist C D = 2 * dist B C * dist A C ^ 2 / (dist A C ^ 2 - dist B C ^ 2) ∧
      dist B D = dist B C * (dist B C ^ 2 + dist A C ^ 2) / (dist A C ^ 2 - dist B C ^ 2) ∧
      dist B D = dist B C * dist A B ^ 2 / (dist A C ^ 2 - dist B C ^ 2) := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  obtain ⟨hCAD, -, hADC, hADB⟩ := sec10_angles_of_sineLaw hSL hAC hBC hright hD hDα
  obtain ⟨hs1, hs2⟩ := sec10_sine_laws_of_sineLaw hSL hAC hBC hright hD
  obtain ⟨hd1, hd2⟩ := sec10_double_and_difference_of_sineLaw hSL hAC hBC hright
  obtain ⟨hr1, -, -, -⟩ := sec10_right_ratios_of_sineLaw hSL hAC hBC hright
  have hBD := sec10_BD_eq hD
  have hc : 0 < dist A B := dist_pos.mpr (ne₁₂_of_not_collinear hnc)
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hba : 0 < dist A C ^ 2 - dist B C ^ 2 := by nlinarith
  rw [hCAD, hADC, hd1, hd2] at hs1
  rw [hDα, hADB, hr1, hd2] at hs2
  have hX : 2 * dist B C * dist A C / dist A B ^ 2 ≠ 0 := by positivity
  have hα : dist B C / dist A B ≠ 0 := by positivity
  have hY : (dist A C ^ 2 - dist B C ^ 2) / dist A B ^ 2 ≠ 0 := (div_pos hba (by positivity)).ne'
  -- the first expression, from `ACD`
  have hCD : dist C D = 2 * dist B C * dist A C ^ 2 / (dist A C ^ 2 - dist B C ^ 2) := by
    rw [div_eq_iff hX] at hs1
    rw [hs1]
    field_simp
  -- the second expression, from `ABD`
  have hBD2 : dist B D = dist B C * dist A B ^ 2 / (dist A C ^ 2 - dist B C ^ 2) := by
    rw [div_eq_iff hα] at hs2
    rw [hs2]
    field_simp
  refine ⟨hCD, ?_, hBD2⟩
  rw [hBD, hCD]
  field_simp
  ring

/-- **C10.9.** Equating the two expressions of `BD` and cancelling the common factor
`a / (b² - a²)` gives `a² + b² = c²`. -/
theorem sec10_pythagoras_of_sineLaw (hSL : EuclideanSineLaw V P)
    {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hab : dist B C < dist A C) : dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2 := by
  obtain ⟨D, ⟨hD, hDα⟩, -⟩ := sec10_exists_unique_D_of_sineLaw hSL hAC hBC hright hab
  obtain ⟨-, h2, h3⟩ := sec10_two_expressions_of_sineLaw hSL hAC hBC hright hab hD hDα
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hba : 0 < dist A C ^ 2 - dist B C ^ 2 := by nlinarith
  have h := h2.symm.trans h3
  rw [div_left_inj' hba.ne'] at h
  exact mul_left_cancel₀ ha.ne' h

end PythagoreanPaper
