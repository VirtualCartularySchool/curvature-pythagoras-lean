import PythagoreanPaper.Riemannian.Triangle

/-!
# The cosine law for every `K`, `K = 0` included (manuscript §9: C9.3 and C9.8)

The cosine law of `PythagoreanPaper.Riemannian.CosineLaw`,
`C_K(c) = C_K(a) C_K(b) + K S_K(a) S_K(b) cos C`, carries no information at `K = 0`: both sides
are `1`. Written with `G_K(x) = ∑ (-K)^m x^(2m+2) / (2m+2)!` (`Gk`), for which
`C_K = 1 - K G_K` (`C_eq_one_sub_mul_Gk`) and `G_0(x) = x² / 2` (`Gk_zero`), it reads

  `G_K(c) = G_K(a) + G_K(b) - K G_K(a) G_K(b) - S_K(a) S_K(b) cos C`.

For `K ≠ 0` this is the same formula (subtract both sides from `1` and divide by `K`); at `K = 0`
it is `c² / 2 = a² / 2 + b² / 2 - a b cos C`. This is the form in which the manuscript's C9.8 lets
the angles `A_K` of the constant-curvature cosine law depend continuously on `K` (`cosLaw`,
`angleK`, `continuousAt_angleK` in `PythagoreanPaper.Sec09`).

This file proves this form for **every** `K` by the argument of `cosine_law_normalBall`, without
dividing by `K`: in geodesic polar coordinates around `p`, `(S_K(r) r')' = C_K(r)` along a
unit-speed geodesic (`hasDerivAt_S_mul_polar`, from the Jacobi equation), so `g = G_K ∘ r ∘ σ`
satisfies `g'' + K g = 1` (`G_K' = S_K`, `S_K' = C_K = 1 - K G_K`).

* `hasDerivAt_Gk`: `G_K' = S_K`; `Gk_zero_right`: `G_K(0) = 0`; `Gk_sub`: subtraction formula;
* `cosine_law_normalBall_G`, `cosine_law_normalBall_G_of_mem`, `cosine_law_normalBall_G'`: the
  cosine law in a normal ball (the counterparts of `cosine_law_normalBall` etc.);
* `cosine_law_segments_G`, `GeodesicTriangle.cosine_law_G`: for geodesic triangles under the
  technical condition `SidesInNormalBalls`;
* `GeodesicTriangle.angles_eq_angleK_of_S_pos`: the angles of a geodesic triangle are the angles
  `A_K = angleK K a b c` etc. of the cosine law, for every `K` with `S_K(a), S_K(b), S_K(c) > 0`;
  `GeodesicTriangle.angles_eq_angleK_zero`: the case `K = 0`.

The existing theorems of `PythagoreanPaper.Riemannian.CosineLaw` and
`PythagoreanPaper.Riemannian.Triangle` are not changed.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

/-! ### The function `G_K` -/

/-- `G_K(0) = 0`. -/
theorem Gk_zero_right (K : ℝ) : Gk K 0 = 0 := by
  simp [Gk]

/-- `G_K' = S_K`. -/
theorem hasDerivAt_Gk (K x : ℝ) : HasDerivAt (Gk K) (S K x) x := by
  rcases eq_or_ne K 0 with rfl | hK
  · have h : Gk 0 = fun y ↦ y ^ 2 / 2 := funext Gk_zero
    rw [h, S_of_eq_zero]
    convert (hasDerivAt_pow 2 x).div_const 2 using 1
    ring
  · have h : Gk K = fun y ↦ (1 - C K y) / K := by
      funext y
      rw [C_eq_one_sub_mul_Gk K y]
      field_simp
      ring
    rw [h]
    convert ((hasDerivAt_C K x).const_sub 1).div_const K using 1
    field_simp

/-- Subtraction formula: `G_K(x - y) = G_K(x) + G_K(y) - K G_K(x) G_K(y) - S_K(x) S_K(y)`. -/
theorem Gk_sub (K x y : ℝ) :
    Gk K (x - y) = Gk K x + Gk K y - K * Gk K x * Gk K y - S K x * S K y := by
  rcases eq_or_ne K 0 with rfl | hK
  · rw [Gk_zero, Gk_zero, Gk_zero, S_of_eq_zero, S_of_eq_zero]
    ring
  · apply mul_left_cancel₀ hK
    have h := C_sub K x y
    rw [C_eq_one_sub_mul_Gk K (x - y), C_eq_one_sub_mul_Gk K x, C_eq_one_sub_mul_Gk K y] at h
    linear_combination (-1 : ℝ) * h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M]

/-! ### The cosine law in a normal ball -/

/-- **The cosine law in a normal ball, for every `K`** (manuscript C9.3 in the form continuous in
`K`; dimension two, constant curvature `K`). Hypotheses as in `cosine_law_normalBall`: `σ` is a
unit-speed geodesic whose points `σ(t)`, `0 ≤ t ≤ b`, lie in `exp_p(B_ρ) ∖ {p}`, from
`σ(0) = γ(a)` to `σ(b) = exp_p(c w)`. Then, with `cos C = ⟨σ'(0), -γ'(a)⟩`,
`G_K(c) = G_K(a) + G_K(b) - K G_K(a) G_K(b) - S_K(a) S_K(b) cos C`. -/
theorem cosine_law_normalBall_G (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p : M} {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) {b : ℝ} (hb : 0 ≤ b) (hJb : Icc 0 b ⊆ J)
    (hσ : IsGeodesicOn I σ J) (hσ1 : ‖velocity I σ 0‖ = 1)
    (hσU : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ ∧ σ t ≠ p)
    {γ : ℝ → M} {v : E} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (hv1 : ‖(show TangentSpace I p from v)‖ = 1) {a : ℝ} (ha : 0 < a) (haU : Icc 0 a ⊆ U)
    (haρ : a < ρ) (hγσ : γ a = σ 0)
    {c : ℝ} (hc : 0 ≤ c) (hcρ : c < ρ) {w : E} (hw1 : ‖(show TangentSpace I p from w)‖ = 1)
    (hσb : σ b = expMap I p (c • w)) :
    Gk K c = Gk K a + Gk K b - K * Gk K a * Gk K b - S K a * S K b *
      inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
        (show TangentSpace I (σ 0) from -(velocity I γ a : E)) := by
  obtain ⟨L, hL, hLexp⟩ := hρ.exists_inv
  have hLmem : ∀ x ∈ expMap I p '' tangentBall I p ρ,
      L x ∈ tangentBall I p ρ ∧ expMap I p (L x) = x := by
    rintro x ⟨v', hv', rfl⟩
    rw [hLexp v' hv']
    exact ⟨hv', rfl⟩
  -- an open interval of times around `[0, b]` on which `σ` stays in the punctured normal ball
  have hσc : ContinuousOn σ J := fun t ht ↦
    (hσ.mdifferentiableAt ht).continuousAt.continuousWithinAt
  have hJ'o : IsOpen (J ∩ σ ⁻¹' (expMap I p '' tangentBall I p ρ \ {p})) :=
    hσc.isOpen_inter_preimage hJ (hρ.isOpen.sdiff isClosed_singleton)
  obtain ⟨δ, hδ, hδJ⟩ := exists_Ioo_subset_of_Icc_subset hJ'o hb
    (fun t ht ↦ ⟨hJb ht, (hσU t ht).1, (hσU t ht).2⟩)
  set Jδ := Ioo (-δ) (b + δ) with hJδ_def
  have h0δ : (0 : ℝ) ∈ Jδ := ⟨by linarith, by linarith⟩
  have hbδ : b ∈ Jδ := ⟨by linarith, by linarith⟩
  -- the curve `u = exp_p⁻¹ ∘ σ` of nonzero tangent vectors at `p`
  set u : ℝ → E := fun t ↦ L (σ t) with hu_def
  have hud : ∀ t ∈ Jδ, DifferentiableAt ℝ u t := fun t ht ↦ by
    have h1 : MDifferentiableAt I 𝓘(ℝ, E) L (σ t) :=
      (hL.contMDiffAt (hρ.isOpen.mem_nhds (hδJ ht).2.1)).mdifferentiableAt (by simp)
    exact mdifferentiableAt_iff_differentiableAt.1 (h1.comp t (hσ.mdifferentiableAt (hδJ ht).1))
  have hu0 : ∀ t ∈ Jδ, (show TangentSpace I p from u t) ≠ 0 := fun t ht h ↦ by
    have h1 := (hLmem _ (hδJ ht).2.1).2
    rw [show L (σ t) = 0 from h, expMap_zero] at h1
    exact (hδJ ht).2.2 h1.symm
  have hspeed : ∀ t ∈ Jδ, ‖velocity I σ t‖ = 1 := fun t ht ↦ by
    rw [IsParallelAlongOn.norm_eq isOpen_Ioo isPreconnected_Ioo
      (hσ.mono fun s hs ↦ (hδJ hs).1) h0δ ht, hσ1]
  obtain ⟨e₁, e₂, he⟩ := exists_orthonormal_pair (I := I) hdim p
  set r : ℝ → ℝ := fun t ↦ ‖(show TangentSpace I p from u t)‖ with hr_def
  -- local analysis: `r` is differentiable and `(S_K(r) r')' = C_K(r)`
  have hloc : ∀ t₁ ∈ Jδ, HasDerivAt r (deriv r t₁) t₁ ∧
      HasDerivAt (fun t ↦ S K (r t) * deriv r t) (C K (r t₁)) t₁ ∧
      ∃ w₁ w₂ : TangentSpace I p, Orthonormal ℝ ![w₁, w₂] ∧ ∃ ℓ : ℝ → ℝ × ℝ,
        (ℓ t₁).1 = r t₁ ∧ polarVec I w₁ w₂ (ℓ t₁) = u t₁ ∧
        HasDerivAt ℓ (deriv ℓ t₁) t₁ ∧ deriv r t₁ = (deriv ℓ t₁).1 ∧
        ℓ t₁ ∈ polarDomain I p w₁ w₂ ∧
        (fun t ↦ polarMap I p w₁ w₂ (ℓ t)) =ᶠ[𝓝 t₁] σ := by
    intro t₁ ht₁
    obtain ⟨w₁, w₂, hw, ℓ, V', hV'o, ht₁V', hV'J, hℓ⟩ :=
      exists_polar_lift hdim he isOpen_Ioo hud ht₁ (hu0 t₁ ht₁)
    have hrℓ : ∀ t ∈ V', r t = (ℓ t).1 := fun t ht ↦ (hℓ t ht).2.2.symm
    have hev : ∀ t ∈ V', r =ᶠ[𝓝 t] fun s ↦ (ℓ s).1 := fun t ht ↦ by
      filter_upwards [hV'o.mem_nhds ht] with s hs using hrℓ s hs
    have hℓd : ∀ t ∈ V', HasDerivAt ℓ (deriv ℓ t) t := fun t ht ↦ (hℓ t ht).1.hasDerivAt
    have hrd : ∀ t ∈ V', HasDerivAt r (deriv ℓ t).1 t := fun t ht ↦
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
        (hℓd t ht)).congr_of_eventuallyEq (hev t ht)
    have hderiv : ∀ t ∈ V', deriv r t = (deriv ℓ t).1 := fun t ht ↦ (hrd t ht).deriv
    have hFℓ : ∀ t ∈ V', polarMap I p w₁ w₂ (ℓ t) = σ t := fun t ht ↦ by
      show expMap I p (polarVec I w₁ w₂ (ℓ t)) = σ t
      rw [(hℓ t ht).2.1]
      exact (hLmem _ (hδJ (hV'J ht)).2.1).2
    have hℓD : ∀ t ∈ V', ℓ t ∈ polarDomain I p w₁ w₂ := fun t ht ↦ by
      show polarVec I w₁ w₂ (ℓ t) ∈ expDomain I p
      rw [(hℓ t ht).2.1]
      exact hρ.subset (hLmem _ (hδJ (hV'J ht)).2.1).1
    have hevF : ∀ t ∈ V', (fun s ↦ polarMap I p w₁ w₂ (ℓ s)) =ᶠ[𝓝 t] σ := fun t ht ↦ by
      filter_upwards [hV'o.mem_nhds ht] with s hs using hFℓ s hs
    have hgeo : IsGeodesicOn I (fun t ↦ polarMap I p w₁ w₂ (ℓ t)) V' := fun t ht ↦
      hσ.of_eventuallyEq hJ (hδJ (hV'J ht)).1 (hevF t ht)
    have hH := hasDerivAt_S_mul_polar hdim hK hw hV'o hℓd hℓD hgeo ht₁V'
    rw [norm_velocity_congr (hevF t₁ ht₁V'), hspeed t₁ ht₁, one_pow, mul_one,
      ← hrℓ t₁ ht₁V'] at hH
    refine ⟨by rw [hderiv t₁ ht₁V']; exact hrd t₁ ht₁V', ?_, w₁, w₂, hw, ℓ,
      (hrℓ t₁ ht₁V').symm, (hℓ t₁ ht₁V').2.1, hℓd t₁ ht₁V', hderiv t₁ ht₁V', hℓD t₁ ht₁V',
      hevF t₁ ht₁V'⟩
    refine hH.congr_of_eventuallyEq ?_
    filter_upwards [hV'o.mem_nhds ht₁V'] with t ht
    rw [hrℓ t ht, hderiv t ht]
  -- `g = G_K ∘ r` satisfies `g'' + K g = 1`; so `f = g - G_K` satisfies `f'' + K f = 0`
  have hf : ∀ t ∈ Jδ, HasDerivAt (fun t ↦ Gk K (r t) - Gk K t)
      (S K (r t) * deriv r t - S K t) t := fun t ht ↦
    ((hasDerivAt_Gk K (r t)).comp t (hloc t ht).1).sub (hasDerivAt_Gk K t)
  have hf' : ∀ t ∈ Jδ, HasDerivAt (fun t ↦ S K (r t) * deriv r t - S K t)
      (C K (r t) - C K t) t := fun t ht ↦ (hloc t ht).2.1.sub (hasDerivAt_S K t)
  have hsol := eqOn_of_ode h0δ hf hf' (fun t _ ↦ by
    rw [C_eq_one_sub_mul_Gk K (r t), C_eq_one_sub_mul_Gk K t]
    ring) hbδ
  -- the boundary values
  have hav : a • v ∈ tangentBall I p ρ := by
    show ‖(show TangentSpace I p from (a • v : E))‖ < ρ
    rw [norm_smul_tangent ha.le, hv1, mul_one]
    exact haρ
  have hγa : γ a = expMap I p (a • v) :=
    (expMap_smul hγ (by rw [uIcc_of_le ha.le]; exact haU)).2.symm
  have hu0v : u 0 = a • v := by
    show L (σ 0) = a • v
    rw [← hγσ, hγa, hLexp _ hav]
  have hr0 : r 0 = a := by
    show ‖(show TangentSpace I p from u 0)‖ = a
    rw [hu0v, norm_smul_tangent ha.le, hv1, mul_one]
  have hcw : c • w ∈ tangentBall I p ρ := by
    show ‖(show TangentSpace I p from (c • w : E))‖ < ρ
    rw [norm_smul_tangent hc, hw1, mul_one]
    exact hcρ
  have hrb : r b = c := by
    show ‖(show TangentSpace I p from L (σ b))‖ = c
    rw [hσb, hLexp _ hcw, norm_smul_tangent hc, hw1, mul_one]
  -- the initial slope: `r'(0) = ⟨σ'(0), γ'(a)⟩`
  obtain ⟨-, -, w₁, w₂, hw, ℓ, hℓr, hℓu, hℓd, hderiv, hℓD, hevF⟩ := hloc 0 h0δ
  have hdir : (polarDir I w₁ w₂ (ℓ 0).2 : E) = v := by
    have h1 : polarVec I w₁ w₂ (ℓ 0) = a • v := hℓu.trans hu0v
    have h2 : (ℓ 0).1 = a := hℓr.trans hr0
    have h3 : a • (polarDir I w₁ w₂ (ℓ 0).2 : E) = a • v := by
      rw [← h1, ← h2]
      rfl
    exact smul_right_injective E ha.ne' h3
  have hpR : (pR I (polarMap I p w₁ w₂) (ℓ 0) : E) = velocity I γ a := by
    show (velocity I (fun s ↦ polarMap I p w₁ w₂ (s, (ℓ 0).2)) (ℓ 0).1 : E) = _
    have hfun : (fun s ↦ polarMap I p w₁ w₂ (s, (ℓ 0).2)) = fun s ↦ expMap I p (s • v) := by
      funext s
      show expMap I p (s • (polarDir I w₁ w₂ (ℓ 0).2 : E)) = _
      rw [hdir]
      rfl
    rw [hfun, hℓr, hr0]
    exact velocity_congr (hγ.expMap_smul_eventuallyEq (haU ⟨ha.le, le_rfl⟩))
  have hvel : (velocity I (fun t ↦ polarMap I p w₁ w₂ (ℓ t)) 0 : E) = velocity I σ 0 :=
    velocity_congr hevF
  have hinner : deriv r 0 = inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
      (show TangentSpace I (σ 0) from (velocity I γ a : E)) := by
    rw [hderiv, fst_eq_inner_velocity_pR hw hℓd hℓD]
    exact (congrArg₂ (fun x y : E ↦ inner ℝ (show TangentSpace I (polarMap I p w₁ w₂ (ℓ 0)) from x)
      (show TangentSpace I (polarMap I p w₁ w₂ (ℓ 0)) from y)) hvel hpR).trans
      (inner_transport (I := I) hevF.eq_of_nhds _ _)
  have hneg : inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
      (show TangentSpace I (σ 0) from -(velocity I γ a : E)) =
      -inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
        (show TangentSpace I (σ 0) from (velocity I γ a : E)) :=
    inner_neg_right _ _
  have hfin : Gk K (r b) - Gk K b = (Gk K (r 0) - Gk K 0) * C K b +
      (S K (r 0) * deriv r 0 - S K 0) * S K b := hsol
  rw [hrb, hr0, hinner, Gk_zero_right, S_zero, C_eq_one_sub_mul_Gk K b] at hfin
  rw [hneg]
  linear_combination hfin

/-- The cosine law of `cosine_law_normalBall_G` when the geodesic side passes through the centre
`p` (the degenerate case: `cos C = 1`, `a + c = b`, and the law is the subtraction formula
`Gk_sub`). -/
theorem cosine_law_normalBall_G_of_mem {K : ℝ} {p : M} {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) {b : ℝ} (hb : 0 ≤ b) (hJb : Icc 0 b ⊆ J)
    (hσ : IsGeodesicOn I σ J) (hσ1 : ‖velocity I σ 0‖ = 1)
    (hσU : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    {tB : ℝ} (htB : tB ∈ Icc 0 b) (hσtB : σ tB = p)
    {γ : ℝ → M} {v : E} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (hv1 : ‖(show TangentSpace I p from v)‖ = 1) {a : ℝ} (ha : 0 < a) (haU : Icc 0 a ⊆ U)
    (haρ : a < ρ) (hγσ : γ a = σ 0)
    {c : ℝ} (hc : 0 ≤ c) (hcρ : c < ρ) {w : E} (hw1 : ‖(show TangentSpace I p from w)‖ = 1)
    (hσb : σ b = expMap I p (c • w)) :
    Gk K c = Gk K a + Gk K b - K * Gk K a * Gk K b - S K a * S K b *
      inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
        (show TangentSpace I (σ 0) from -(velocity I γ a : E)) := by
  obtain ⟨δ, hδ, hδJ⟩ := exists_Ioo_subset_of_Icc_subset hJ hb hJb
  have hσδ : IsGeodesicOn I σ (Ioo (-δ) (b + δ)) := hσ.mono hδJ
  have htBδ : tB ∈ Ioo (-δ) (b + δ) := ⟨by linarith [htB.1], by linarith [htB.2]⟩
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) (b + δ) := ⟨by linarith, by linarith⟩
  -- unit speed at `tB`
  set w₀ : E := velocity I σ tB with hw₀_def
  have hw₀1 : ‖(show TangentSpace I p from w₀)‖ = 1 := by
    rw [← norm_transport (I := I) hσtB w₀]
    show ‖velocity I σ tB‖ = 1
    rw [IsParallelAlongOn.norm_eq isOpen_Ioo isPreconnected_Ioo hσδ h0δ htBδ, hσ1]
  -- the two halves of `σ`, seen from `p`
  have hback := hσδ.isGeodesicFrom_affine isOpen_Ioo isPreconnected_Ioo htBδ (-1)
  have hfwd := hσδ.isGeodesicFrom_affine isOpen_Ioo isPreconnected_Ioo htBδ 1
  rw [← hw₀_def, hσtB] at hback hfwd
  have hbackI : Icc 0 tB ⊆ (fun t ↦ -1 * t + tB) ⁻¹' Ioo (-δ) (b + δ) := fun t ht ↦
    ⟨by simp only; linarith [ht.2], by simp only; linarith [ht.1, htB.2]⟩
  have hfwdI : Icc 0 (b - tB) ⊆ (fun t ↦ 1 * t + tB) ⁻¹' Ioo (-δ) (b + δ) := fun t ht ↦
    ⟨by simp only; linarith [ht.1, htB.1], by simp only; linarith [ht.2]⟩
  have hbackB := hback.smul_mem_tangentBall hρ hbackI fun t ht ↦
    hσU _ ⟨by linarith [ht.2], by linarith [ht.1, htB.2]⟩
  have hfwdB := hfwd.smul_mem_tangentBall hρ hfwdI fun t ht ↦
    hσU _ ⟨by linarith [ht.1, htB.1], by linarith [ht.2]⟩
  have hσ0 : σ 0 = expMap I p (tB • ((-1 : ℝ) • w₀)) := by
    have := (expMap_smul hback (t := tB) (by rw [uIcc_of_le htB.1]; exact hbackI)).2
    exact (congrArg σ (by ring : (0 : ℝ) = -1 * tB + tB)).trans this.symm
  have hσb' : σ b = expMap I p ((b - tB) • ((1 : ℝ) • w₀)) := by
    have := (expMap_smul hfwd (t := b - tB)
      (by rw [uIcc_of_le (by linarith [htB.2])]; exact hfwdI)).2
    exact (congrArg σ (by ring : b = 1 * (b - tB) + tB)).trans this.symm
  -- comparing with `γ` and with `exp_p (c w)`
  have hav : a • v ∈ tangentBall I p ρ := by
    show ‖(show TangentSpace I p from (a • v : E))‖ < ρ
    rw [norm_smul_tangent ha.le, hv1, mul_one]
    exact haρ
  have hγa : γ a = expMap I p (a • v) :=
    (expMap_smul hγ (by rw [uIcc_of_le ha.le]; exact haU)).2.symm
  have h1 : a • v = tB • ((-1 : ℝ) • w₀) :=
    hρ.injOn hav (hbackB tB ⟨htB.1, le_rfl⟩) (by rw [← hγa, hγσ, hσ0])
  have hcw : c • w ∈ tangentBall I p ρ := by
    show ‖(show TangentSpace I p from (c • w : E))‖ < ρ
    rw [norm_smul_tangent hc, hw1, mul_one]
    exact hcρ
  have h2 : c • w = (b - tB) • ((1 : ℝ) • w₀) :=
    hρ.injOn hcw (hfwdB (b - tB) ⟨by linarith [htB.2], le_rfl⟩) (by rw [← hσb, hσb'])
  have hnorm1 : ‖(show TangentSpace I p from ((-1 : ℝ) • w₀ : E))‖ = 1 := by
    show ‖(-1 : ℝ) • (show TangentSpace I p from w₀)‖ = 1
    rw [norm_smul, hw₀1]
    norm_num
  have hnorm2 : ‖(show TangentSpace I p from ((1 : ℝ) • w₀ : E))‖ = 1 := by
    show ‖(1 : ℝ) • (show TangentSpace I p from w₀)‖ = 1
    rw [norm_smul, hw₀1]
    norm_num
  have haB : a = tB := by
    have := congrArg (fun x : E ↦ ‖(show TangentSpace I p from x)‖) h1
    simp only at this
    rwa [norm_smul_tangent ha.le, norm_smul_tangent htB.1, hv1, hnorm1, mul_one,
      mul_one] at this
  have hcB : c = b - tB := by
    have := congrArg (fun x : E ↦ ‖(show TangentSpace I p from x)‖) h2
    simp only at this
    rwa [norm_smul_tangent hc, norm_smul_tangent (by linarith [htB.2]), hw1, hnorm2, mul_one,
      mul_one] at this
  have hv : v = (-1 : ℝ) • w₀ := by
    rw [← haB] at h1
    exact smul_right_injective E ha.ne' h1
  -- `γ` is the backward half of `σ`, so `γ'(a) = -σ'(0)`
  rw [hv] at hγ
  have hU' := hγ.isOpen.inter hback.isOpen
  have hUp := isPreconnected_inter_real hγ.isPreconnected hback.isPreconnected
  have haI : a ∈ U ∩ (fun t ↦ -1 * t + tB) ⁻¹' Ioo (-δ) (b + δ) :=
    ⟨haU ⟨ha.le, le_rfl⟩, hbackI ⟨ha.le, haB.le⟩⟩
  have heq := IsGeodesicOn.eqOn hU' hUp (hγ.isGeodesicOn.mono inter_subset_left)
    (hback.isGeodesicOn.mono inter_subset_right) ⟨hγ.zero_mem, hback.zero_mem⟩
    (hγ.apply_zero.trans hback.apply_zero.symm)
    (hγ.velocity_zero.trans hback.velocity_zero.symm) a haI
  have hvelγ : (show E from velocity I γ a) = -(show E from velocity I σ 0) := by
    have h3 : -1 * a + tB = 0 := by rw [haB]; ring
    have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I σ (-1 * a + tB) := by
      rw [h3]; exact hσ.mdifferentiableAt (hJb ⟨le_rfl, hb⟩)
    rw [heq.2, velocity_comp_affine hd]
    have h4 : ((-1 : ℝ) • (velocity I σ (-1 * a + tB) : E)) = (-1 : ℝ) • (velocity I σ 0 : E) :=
      congrArg (fun s ↦ (-1 : ℝ) • (velocity I σ s : E)) h3
    rw [h4, neg_one_smul]
    rfl
  have hx : -(show E from velocity I γ a) = (show E from velocity I σ 0) := by
    rw [hvelγ, neg_neg]
  have hinner : inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
      (show TangentSpace I (σ 0) from -(velocity I γ a : E)) = 1 := by
    refine (congrArg (fun y : E ↦ inner ℝ (show TangentSpace I (σ 0) from (velocity I σ 0 : E))
      (show TangentSpace I (σ 0) from y)) hx).trans ?_
    show inner ℝ (velocity I σ 0) (velocity I σ 0) = 1
    rw [real_inner_self_eq_norm_sq, hσ1, one_pow]
  rw [hinner, hcB, haB, Gk_sub]
  ring

/-- **The cosine law in a normal ball, for every `K`** (manuscript C9.3 in the form continuous in
`K`), in all cases: for a unit-speed geodesic `σ` whose points `σ(t)`, `0 ≤ t ≤ b`, lie in the
normal ball `exp_p(B_ρ)` (possibly passing through `p`), from `σ(0) = γ(a)` to
`σ(b) = exp_p(c w)`, `G_K(c) = G_K(a) + G_K(b) - K G_K(a) G_K(b) - S_K(a) S_K(b) cos C` with
`cos C = ⟨σ'(0), -γ'(a)⟩`. -/
theorem cosine_law_normalBall_G' (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p : M} {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) {b : ℝ} (hb : 0 ≤ b) (hJb : Icc 0 b ⊆ J)
    (hσ : IsGeodesicOn I σ J) (hσ1 : ‖velocity I σ 0‖ = 1)
    (hσU : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    {γ : ℝ → M} {v : E} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (hv1 : ‖(show TangentSpace I p from v)‖ = 1) {a : ℝ} (ha : 0 < a) (haU : Icc 0 a ⊆ U)
    (haρ : a < ρ) (hγσ : γ a = σ 0)
    {c : ℝ} (hc : 0 ≤ c) (hcρ : c < ρ) {w : E} (hw1 : ‖(show TangentSpace I p from w)‖ = 1)
    (hσb : σ b = expMap I p (c • w)) :
    Gk K c = Gk K a + Gk K b - K * Gk K a * Gk K b - S K a * S K b *
      inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
        (show TangentSpace I (σ 0) from -(velocity I γ a : E)) := by
  by_cases h : ∀ t ∈ Icc 0 b, σ t ≠ p
  · exact cosine_law_normalBall_G hdim hK hρ hJ hb hJb hσ hσ1 (fun t ht ↦ ⟨hσU t ht, h t ht⟩)
      hγ hv1 ha haU haρ hγσ hc hcρ hw1 hσb
  · obtain ⟨tB, htB, hσtB⟩ := not_forall₂.1 h
    exact cosine_law_normalBall_G_of_mem hρ hJ hb hJb hσ hσ1 hσU htB (not_not.1 hσtB) hγ hv1 ha
      haU haρ hγσ hc hcρ hw1 hσb

/-! ### Geodesic triangles -/

/-- **The cosine law at a vertex, for every `K`** (dimension two, constant curvature `K`). With
`γ`, `σ`, `τ` as in `cosine_law_segments` (geodesic segments `p → x`, `x → y`, `y → p` of lengths
`a`, `b`, `c`, contained in a normal ball around `p`) and `C` the angle at `x` between `σ` and the
reverse of `γ`: `G_K(c) = G_K(a) + G_K(b) - K G_K(a) G_K(b) - S_K(a) S_K(b) cos C`. -/
theorem cosine_law_segments_G (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p x y : M} {a b c : ℝ} {γ σ τ : ℝ → M}
    (hγ : IsGeodesicSegment I γ p x a) (hσ : IsGeodesicSegment I σ x y b)
    (hτ : IsGeodesicSegment I τ y p c) {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    (hγB : ∀ t ∈ Icc 0 a, γ t ∈ expMap I p '' tangentBall I p ρ)
    (hσB : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    (hτB : ∀ t ∈ Icc 0 c, τ t ∈ expMap I p '' tangentBall I p ρ) :
    Gk K c = Gk K a + Gk K b - K * Gk K a * Gk K b - S K a * S K b *
      Real.cos (InnerProductGeometry.angle (show TangentSpace I x from (velocity I σ 0 : E))
        (show TangentSpace I x from -(velocity I γ a : E))) := by
  -- `γ`, seen from `p`, is radial
  obtain ⟨Uγ, hγF, hγU⟩ := hγ.exists_isGeodesicFrom
  have hv1 := hγ.norm_velocity_zero
  have haB := hγF.smul_mem_tangentBall hρ hγU hγB a ⟨hγ.pos.le, le_rfl⟩
  have haρ : a < ρ := by
    have h := (smul_mem_tangentBall_iff (I := I) (v := (velocity I γ 0 : E)) hγ.pos.le).1 haB
    rwa [hv1, mul_one] at h
  -- the reverse of `τ`, seen from `p`, is radial
  have hτr := hτ.reverse
  obtain ⟨Uτ, hτF, hτU⟩ := hτr.exists_isGeodesicFrom
  have hw1 := hτr.norm_velocity_zero
  have hcB := hτF.smul_mem_tangentBall hρ hτU (fun t ht ↦ hτB _
    ⟨by linarith [ht.2], by linarith [ht.1]⟩) c ⟨hτ.pos.le, le_rfl⟩
  have hcρ : c < ρ := by
    have h := (smul_mem_tangentBall_iff (I := I)
      (v := (velocity I (fun t ↦ τ (-1 * t + c)) 0 : E)) hτ.pos.le).1 hcB
    rwa [hw1, mul_one] at h
  have hσb : σ b = expMap I p (c • (show E from velocity I (fun t ↦ τ (-1 * t + c)) 0)) := by
    rw [hσ.apply_length, (expMap_smul hτF (t := c) (by rw [uIcc_of_le hτ.pos.le]; exact hτU)).2]
    show y = τ (-1 * c + c)
    rw [show -1 * c + c = 0 by ring, hτ.apply_zero]
  -- the cosine law in the normal ball
  obtain ⟨ασ, βσ, hασ, hβσ, hσg⟩ := hσ.exists_Ioo
  have h := cosine_law_normalBall_G' hdim hK hρ isOpen_Ioo hσ.pos.le
    (fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩) hσg hσ.unit hσB hγF hv1 hγ.pos hγU
    haρ (hγ.apply_length.trans hσ.apply_zero.symm) hτ.pos.le hcρ hw1 hσb
  rw [h]
  congr 1
  -- the inner product at `σ 0` is the cosine of the angle at `x`
  have hu : ‖(show TangentSpace I x from (velocity I σ 0 : E))‖ = 1 := hσ.norm_velocity_zero
  have hv : ‖(show TangentSpace I x from -(velocity I γ a : E))‖ = 1 := by
    have h1 : ‖(show TangentSpace I x from -(velocity I γ a : E))‖ =
        ‖(show TangentSpace I x from (velocity I γ a : E))‖ := norm_neg _
    rw [h1]
    exact hγ.norm_velocity_length
  rw [cos_angle_of_norm_eq_one hu hv]
  congr 1
  exact (inner_transport (I := I) hσ.apply_zero _ _)

namespace GeodesicTriangle

variable (T : GeodesicTriangle I M)

/-- **The cosine law for every `K`** (C9.3 in the form continuous in `K`, under the technical
condition `SidesInNormalBalls`): in a two-dimensional Riemannian manifold of constant curvature
`K`, `G_K(a) = G_K(b) + G_K(c) - K G_K(b) G_K(c) - S_K(b) S_K(c) cos A`, and likewise at `B` and
`C`. At `K = 0`: `a² / 2 = b² / 2 + c² / 2 - b c cos A`. -/
theorem cosine_law_G (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (hT : T.SidesInNormalBalls) :
    Gk K T.a = Gk K T.b + Gk K T.c - K * Gk K T.b * Gk K T.c -
        S K T.b * S K T.c * Real.cos T.angleA ∧
      Gk K T.b = Gk K T.c + Gk K T.a - K * Gk K T.c * Gk K T.a -
        S K T.c * S K T.a * Real.cos T.angleB ∧
      Gk K T.c = Gk K T.a + Gk K T.b - K * Gk K T.a * Gk K T.b -
        S K T.a * S K T.b * Real.cos T.angleC := by
  obtain ⟨⟨ρA, hρA, hAa, hAb, hAc⟩, ⟨ρB, hρB, hBa, hBb, hBc⟩, ⟨ρC, hρC, hCa, hCb, hCc⟩⟩ := hT
  exact ⟨cosine_law_segments_G hdim hK T.segment_b T.segment_c T.segment_a hρC hCb hCc hCa,
    cosine_law_segments_G hdim hK T.segment_c T.segment_a T.segment_b hρA hAc hAa hAb,
    cosine_law_segments_G hdim hK T.segment_a T.segment_b T.segment_c hρB hBa hBb hBc⟩

/-- **The angles are those given by the cosine law, for every `K`** (C9.8, under the technical
condition `SidesInNormalBalls`): if `S_K(a), S_K(b), S_K(c) > 0`, then `A = A_K = angleK K a b c`,
`B = angleK K b c a`, `C = angleK K c a b`. Unlike `angles_eq_angleK`, this includes `K = 0`. -/
theorem angles_eq_angleK_of_S_pos (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (hT : T.SidesInNormalBalls)
    (hPa : 0 < S K T.a) (hPb : 0 < S K T.b) (hPc : 0 < S K T.c) :
    T.angleA = angleK K T.a T.b T.c ∧ T.angleB = angleK K T.b T.c T.a ∧
      T.angleC = angleK K T.c T.a T.b := by
  obtain ⟨hA, hB, hC⟩ := T.cosine_law_G hdim hK hT
  have key : ∀ {x y z θ : ℝ}, 0 < S K y → 0 < S K z → 0 ≤ θ → θ ≤ Real.pi →
      Gk K x = Gk K y + Gk K z - K * Gk K y * Gk K z - S K y * S K z * Real.cos θ →
      θ = angleK K x y z := by
    intro x y z θ hy hz h0 hπ hG
    have hc : Real.cos θ = cosLaw K x y z := by
      rw [cosLaw, eq_div_iff (mul_pos hy hz).ne']
      linear_combination hG
    rw [angleK, ← hc, Real.arccos_cos h0 hπ]
  exact ⟨key hPb hPc (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _) hA,
    key hPc hPa (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _) hB,
    key hPa hPb (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _) hC⟩

/-- **The angles are those given by the cosine law at `K = 0`** (C9.8 at `K = 0`, under the
technical condition `SidesInNormalBalls`): in a flat two-dimensional Riemannian manifold,
`A = A_0 = angleK 0 a b c`, `B = angleK 0 b c a`, `C = angleK 0 c a b`, where
`cos A_0 = (b² + c² - a²) / (2 b c)` (`cosLaw_zero`). -/
theorem angles_eq_angleK_zero (hdim : Module.finrank ℝ E = 2)
    (hK : HasConstSectionalCurvature I M 0) (hT : T.SidesInNormalBalls) :
    T.angleA = angleK 0 T.a T.b T.c ∧ T.angleB = angleK 0 T.b T.c T.a ∧
      T.angleC = angleK 0 T.c T.a T.b :=
  T.angles_eq_angleK_of_S_pos hdim hK hT (by rw [S_of_eq_zero]; exact T.segment_a.pos)
    (by rw [S_of_eq_zero]; exact T.segment_b.pos) (by rw [S_of_eq_zero]; exact T.segment_c.pos)

end GeodesicTriangle

end PythagoreanPaper
