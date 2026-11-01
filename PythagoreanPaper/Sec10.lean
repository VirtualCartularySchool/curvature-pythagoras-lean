import PythagoreanPaper.Sec09
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Manuscript §10 — the Jackson–Johnson second proof, without a figure

Setting (C10.1): a right triangle `ABC` with `∠C = 90°`, `a = BC`, `b = AC`, `c = AB`,
`α = ∠A = ∠BAC`, `β = ∠B = ∠ABC`. In Lean the right angle is `∠ A C B = π / 2` together with
`A ≠ C` and `B ≠ C` (Mathlib gives the angle at a vertex equal to an endpoint the value `π / 2`,
so the two inequalities are what makes the triangle a triangle).

* C10.1: `α + β = 90°`, and `a < b` iff `α < 45° < β` (`sec10_setting`).
* C10.2: as `X` moves from `B` along the extension of `CB` beyond `B`, `∠BAX` increases
  continuously and strictly from `0`, stays below `β` and tends to `β`
  (`sec10_angle_increases`); hence, for `a < b`, there is exactly one `D` on the extension beyond
  `B` (`C–B–D`) with `∠BAD = α` (`sec10_exists_unique_D`).
* C10.3: `BD = CD - a` (`sec10_BD_eq`).
* C10.4: `∠CAD = 2α`, `∠ACD = 90°`, `∠ADC = ∠ADB = β - α` (`sec10_angles`).
* C10.5: the sine law in the triangles `ACD` and `ABD` (`sec10_sine_laws`).
* C10.6: `sin α = a/c`, `cos α = b/c`, `sin β = b/c`, `cos β = a/c` (`sec10_right_ratios`).
* C10.7: `sin 2α = 2ab/c²`, `sin(β - α) = (b² - a²)/c²` (`sec10_double_and_difference`).
* C10.8: `CD = 2ab²/(b² - a²)`, `BD = a(a² + b²)/(b² - a²)`, `BD = ac²/(b² - a²)`
  (`sec10_two_expressions`).
* C10.9: `a² + b² = c²` (`sec10_pythagoras`).

Every sine law used in this file is `sec9_euclidean_sine_law`, the Euclidean sine law obtained in
§9 as the `K → 0` limit of the constant-curvature sine law. The ratios of C10.6 are derived from
that sine law and the angle sum. C10.10 (the character of the proof) is a statement about the
proof, not a theorem, and is not formalized.
-/

noncomputable section

open Real Set Filter Topology EuclideanGeometry

namespace PythagoreanPaper

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

private theorem not_collinear_mono {s t : Set P} (h : ¬ Collinear ℝ s) (hst : s ⊆ t) :
    ¬ Collinear ℝ t := fun ht => h (ht.subset hst)

/-- A right angle at `C`, with `A ≠ C` and `B ≠ C`, gives a nondegenerate triangle. -/
theorem not_collinear_of_right_angle {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) : ¬ Collinear ℝ ({A, B, C} : Set P) := by
  intro h
  have h' : Collinear ℝ ({A, C, B} : Set P) := h.subset (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  rcases collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp h' with h1 | h1 | h1 | h1
  · exact hAC h1
  · exact hBC h1
  · linarith [pi_pos, hright.symm.trans h1]
  · linarith [pi_pos, hright.symm.trans h1]

/-! ### C10.1 -/

/-- **C10.1.** In a right triangle `ABC` with `∠C = 90°`: `α + β = 90°`, and `a < b` iff
`α < 45° < β`. -/
theorem sec10_setting {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2) :
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
    have h := (sec9_euclidean_sine_law hnc).1
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

/-! ### C10.2: the point `D` -/

/-- `X(t) = B + t (B - C)`. For `t > 0` these are the points of the extension of `CB` beyond `B`
(`sbtw_extPt`, `exists_extPt_of_sbtw`), and `X(0) = B`. -/
def extPt (B C : P) (t : ℝ) : P := t • (B -ᵥ C) +ᵥ B

theorem extPt_zero (B C : P) : extPt B C 0 = B := by
  rw [extPt, zero_smul, zero_vadd]

theorem extPt_mem_line (B C : P) (t : ℝ) : extPt B C t ∈ line[ℝ, B, C] := by
  rw [extPt, vadd_left_mem_affineSpan_pair]
  exact ⟨-t, by rw [neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]⟩

theorem extPt_injective {B C : P} (hBC : B ≠ C) : Function.Injective (extPt B C) := by
  intro s t h
  exact smul_left_injective ℝ (vsub_ne_zero.mpr hBC) (vadd_right_cancel B h)

theorem wbtw_extPt (B C : P) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Wbtw ℝ B (extPt B C s) (extPt B C t) :=
  wbtw_smul_vadd_smul_vadd_of_nonneg_of_le B (B -ᵥ C) hs hst

theorem sbtw_extPt {B C : P} (hBC : B ≠ C) {t : ℝ} (ht : 0 < t) :
    Sbtw ℝ C B (extPt B C t) := by
  have hw := wbtw_smul_vadd_smul_vadd_of_nonneg_of_le C (B -ᵥ C) zero_le_one
    (show (1 : ℝ) ≤ 1 + t by linarith)
  have h1 : (1 : ℝ) • (B -ᵥ C) +ᵥ C = B := by rw [one_smul, vsub_vadd]
  have h2 : (1 + t) • (B -ᵥ C) +ᵥ C = extPt B C t := by
    rw [extPt, add_smul, one_smul, add_comm, ← vadd_vadd, vsub_vadd]
  rw [h1, h2] at hw
  refine ⟨hw, hBC, fun h => ?_⟩
  have := extPt_injective hBC (h.symm.trans (extPt_zero B C).symm)
  linarith

theorem exists_extPt_of_sbtw {B C D : P} (h : Sbtw ℝ C B D) : ∃ t, 0 < t ∧ D = extPt B C t := by
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hsB⟩, hBC, hBD⟩ := h
  rw [AffineMap.lineMap_apply] at hsB
  have hs0' : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_vadd] at hsB
    exact hBC hsB.symm
  have hs1' : s ≠ 1 := by
    rintro rfl
    rw [one_smul, vsub_vadd] at hsB
    exact hBD hsB.symm
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs0')
  have hslt : s < 1 := lt_of_le_of_ne hs1 hs1'
  refine ⟨s⁻¹ - 1, sub_pos.mpr ((one_lt_inv₀ hspos).mpr hslt), ?_⟩
  rw [extPt, ← hsB, vadd_vsub, smul_smul, vadd_vadd, ← add_smul,
    show (s⁻¹ - 1) * s + s = 1 by rw [sub_mul, inv_mul_cancel₀ hs0', one_mul, sub_add_cancel],
    one_smul, vsub_vadd]

theorem not_mem_line_of_not_collinear {A B C : P} (h : ¬ Collinear ℝ ({A, B, C} : Set P)) :
    A ∉ line[ℝ, B, C] := fun hA => h (collinear_insert_of_mem_affineSpan_pair hA)

theorem extPt_ne {A B C : P} (h : ¬ Collinear ℝ ({A, B, C} : Set P)) (t : ℝ) :
    extPt B C t ≠ A := fun he => not_mem_line_of_not_collinear h (he ▸ extPt_mem_line B C t)

theorem not_collinear_extPt {A B C : P} (h : ¬ Collinear ℝ ({A, B, C} : Set P)) (hBC : B ≠ C)
    {s t : ℝ} (hst : s ≠ t) : ¬ Collinear ℝ ({extPt B C s, A, extPt B C t} : Set P) := by
  intro hc
  have hA : A ∈ line[ℝ, extPt B C s, extPt B C t] :=
    hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp)
      (fun he => hst (extPt_injective hBC he))
  exact not_mem_line_of_not_collinear h
    (affineSpan_pair_le_of_mem_of_mem (extPt_mem_line B C s) (extPt_mem_line B C t) hA)

/-- **C10.2** (the monotonicity argument). As `X(t)` moves from `B` along the extension of `CB`
beyond `B`, the angle `∠BAX(t)` is continuous and strictly increasing in `t ≥ 0`, starts at `0`,
stays below `β` and tends to `β`. -/
theorem sec10_angle_increases {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) :
    Continuous (fun t => ∠ B A (extPt B C t)) ∧
    StrictMonoOn (fun t => ∠ B A (extPt B C t)) (Ici 0) ∧
    ∠ B A (extPt B C 0) = 0 ∧
    (∀ t, 0 ≤ t → ∠ B A (extPt B C t) < ∠ A B C) ∧
    Tendsto (fun t => ∠ B A (extPt B C t)) atTop (𝓝 (∠ A B C)) := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hAB : A ≠ B := ne₁₂_of_not_collinear hnc
  have hsum := (sec10_setting hAC hBC hright).1
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
    have hsl := (sec9_euclidean_sine_law (hncX t ht)).1
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
theorem sec10_exists_unique_D {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) (hab : dist B C < dist A C) :
    ∃! D : P, Sbtw ℝ C B D ∧ ∠ B A D = ∠ B A C := by
  obtain ⟨hcont, hmono, h0, -, hlim⟩ := sec10_angle_increases hAC hBC hright
  obtain ⟨hsum, hiff⟩ := sec10_setting hAC hBC hright
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

/-! ### C10.3–C10.9 -/

/-- **C10.3.** With the order `C–B–D`, `BD = CD - BC`. -/
theorem sec10_BD_eq {B C D : P} (h : Sbtw ℝ C B D) : dist B D = dist C D - dist B C := by
  have := h.wbtw.dist_add_dist
  rw [dist_comm C B] at this
  linarith

theorem mem_line_of_sbtw {B C D : P} (hBC : B ≠ C) (h : Sbtw ℝ C B D) : D ∈ line[ℝ, B, C] :=
  AffineSubspace.right_mem_of_wbtw h.wbtw (right_mem_affineSpan_pair ℝ B C)
    (left_mem_affineSpan_pair ℝ B C) hBC.symm

/-- **C10.4.** `∠CAD = 2α`, `∠ACD = 90°`, `∠ADC = β - α` and `∠ADB = β - α`. -/
theorem sec10_angles {A B C D : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hD : Sbtw ℝ C B D) (hDα : ∠ B A D = ∠ B A C) :
    ∠ C A D = 2 * ∠ B A C ∧ ∠ A C D = π / 2 ∧ ∠ A D C = ∠ A B C - ∠ B A C ∧
      ∠ A D B = ∠ A B C - ∠ B A C := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hsum := (sec10_setting hAC hBC hright).1
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
theorem sec10_sine_laws {A B C D : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
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
  obtain ⟨h1, h2⟩ := sec9_euclidean_sine_law hACD
  obtain ⟨h3, h4⟩ := sec9_euclidean_sine_law hABD
  constructor
  · rw [← inv_div, h1.trans h2, inv_div]
  · rw [← inv_div, h3.trans h4, inv_div]

/-- **C10.6.** In the right triangle `ABC`: `sin α = a/c`, `cos α = b/c`, `sin β = b/c`,
`cos β = a/c`. -/
theorem sec10_right_ratios {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2) :
    Real.sin (∠ B A C) = dist B C / dist A B ∧ Real.cos (∠ B A C) = dist A C / dist A B ∧
      Real.sin (∠ A B C) = dist A C / dist A B ∧ Real.cos (∠ A B C) = dist B C / dist A B := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  have hsum := (sec10_setting hAC hBC hright).1
  have hc : 0 < dist A B := dist_pos.mpr (ne₁₂_of_not_collinear hnc)
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  obtain ⟨h1, h2⟩ := sec9_euclidean_sine_law hnc
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
theorem sec10_double_and_difference {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) :
    Real.sin (2 * ∠ B A C) = 2 * dist B C * dist A C / dist A B ^ 2 ∧
      Real.sin (∠ A B C - ∠ B A C) = (dist A C ^ 2 - dist B C ^ 2) / dist A B ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := sec10_right_ratios hAC hBC hright
  constructor
  · rw [Real.sin_two_mul, h1, h2]
    ring
  · rw [Real.sin_sub, h3, h2, h4, h1]
    ring

/-- **C10.8.** The two expressions of `BD`: from `ACD`, `CD = 2ab²/(b² - a²)` and
`BD = CD - a = a(a² + b²)/(b² - a²)`; from `ABD`, `BD = ac²/(b² - a²)`. -/
theorem sec10_two_expressions {A B C D : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (hright : ∠ A C B = π / 2) (hab : dist B C < dist A C)
    (hD : Sbtw ℝ C B D) (hDα : ∠ B A D = ∠ B A C) :
    dist C D = 2 * dist B C * dist A C ^ 2 / (dist A C ^ 2 - dist B C ^ 2) ∧
      dist B D = dist B C * (dist B C ^ 2 + dist A C ^ 2) / (dist A C ^ 2 - dist B C ^ 2) ∧
      dist B D = dist B C * dist A B ^ 2 / (dist A C ^ 2 - dist B C ^ 2) := by
  have hnc := not_collinear_of_right_angle hAC hBC hright
  obtain ⟨hCAD, -, hADC, hADB⟩ := sec10_angles hAC hBC hright hD hDα
  obtain ⟨hs1, hs2⟩ := sec10_sine_laws hAC hBC hright hD
  obtain ⟨hd1, hd2⟩ := sec10_double_and_difference hAC hBC hright
  obtain ⟨hr1, -, -, -⟩ := sec10_right_ratios hAC hBC hright
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
theorem sec10_pythagoras {A B C : P} (hAC : A ≠ C) (hBC : B ≠ C) (hright : ∠ A C B = π / 2)
    (hab : dist B C < dist A C) : dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2 := by
  obtain ⟨D, ⟨hD, hDα⟩, -⟩ := sec10_exists_unique_D hAC hBC hright hab
  obtain ⟨-, h2, h3⟩ := sec10_two_expressions hAC hBC hright hab hD hDα
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hba : 0 < dist A C ^ 2 - dist B C ^ 2 := by nlinarith
  have h := h2.symm.trans h3
  rw [div_left_inj' hba.ne'] at h
  exact mul_left_cancel₀ ha.ne' h

end PythagoreanPaper
