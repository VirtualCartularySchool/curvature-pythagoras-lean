import PythagoreanPaper.Riemannian.CosineLaw

/-!
# Normal balls of a given radius in constant curvature

* `isNormalBall_of_injOn`: if the ball `B_ρ` of `T_p M` lies in the domain of `exp_p`, `exp_p` is
  injective on `B_ρ`, and the differential of `exp_p` is invertible at every point of `B_ρ`, then
  `B_ρ` is a normal ball (`IsNormalBall`): `exp_p(B_ρ)` is open and `exp_p` has a smooth inverse
  on it (inverse function theorem at every point of `B_ρ`, and injectivity).
* `exists_hasFDerivAt_expMap`: in a two-dimensional Riemannian manifold of constant curvature
  `K`, the differential of `exp_p` at a point `v` of its domain is invertible if `‖v‖ < π/√K`
  (when `K > 0`; when `K ≤ 0`, at every point of the domain). For `v = r v_θ ≠ 0` it sends `v_θ`
  and `r ∂_θ v_θ` to `∂_r F` and `∂_θ F` of the geodesic polar coordinates
  `F(r, θ) = exp_p(r v_θ)`, which are orthogonal, with `|∂_r F| = 1` and `|∂_θ F| = |S_K(r)| ≠ 0`
  (C6.2–C6.4).
* `isNormalBall_of_constCurvature` combines them: in constant curvature `K`, a ball of radius `ρ`
  (`ρ ≤ π/√K` if `K > 0`) contained in the domain of `exp_p`, on which `exp_p` is injective, is a
  normal ball.

These are used for the two-dimensional model spaces of constant curvature (manuscript §9).
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M]

section Criterion

/-- `exp_p`, read in a chart at `x₀`, is smooth wherever `exp_p` stays in that chart. -/
lemma contDiffAt_chart_expMap {p x₀ : M} {w : E} (hw : w ∈ expDomain I p)
    (hsrc : expMap I p w ∈ (chartAt H x₀).source) :
    ContDiffAt ℝ ∞ (fun u : E ↦ extChartAt I x₀ (expMap I p u)) w :=
  contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_extChartAt' hsrc).comp w (contMDiffAt_expMap hw))

/-- **Local inverse of `exp_p`.** Near a point `v` of an open set `D` of the domain of `exp_p`
where the differential of `exp_p` is invertible, there are an open neighbourhood `S ⊆ D` of `v`,
an open neighbourhood `N ⊆ exp_p(S)` of `exp_p v` and a map `L`, smooth on `N`, with
`L (exp_p w) = w` for `w ∈ S`. -/
lemma exists_local_inverse_expMap {p : M} {v : E} {D : Set E} (hD : IsOpen D) (hvD : v ∈ D)
    (hDdom : D ⊆ expDomain I p) {e : E ≃L[ℝ] E}
    (he : HasFDerivAt (fun u ↦ extChartAt I (expMap I p v) (expMap I p u)) (e : E →L[ℝ] E) v) :
    ∃ (S : Set E) (N : Set M) (L : M → E), IsOpen N ∧ expMap I p v ∈ N ∧ S ⊆ D ∧
      N ⊆ expMap I p '' S ∧ ContMDiffOn I 𝓘(ℝ, E) ∞ L N ∧ ∀ w ∈ S, L (expMap I p w) = w := by
  set x₀ := expMap I p v with hx₀
  set G : E → E := fun u ↦ extChartAt I x₀ (expMap I p u) with hG_def
  set W : Set E := expDomain I p ∩ expMap I p ⁻¹' (chartAt H x₀).source with hW_def
  have hWo : IsOpen W := (contMDiffOn_expMap p).continuousOn.isOpen_inter_preimage
    (isOpen_expDomain p) (chartAt H x₀).open_source
  have hvW : v ∈ W := ⟨hDdom hvD, mem_chart_source H x₀⟩
  have hGW : ∀ w ∈ W, ContDiffAt ℝ ∞ G w := fun w hw ↦ contDiffAt_chart_expMap hw.1 hw.2
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Φ := (hGW v hvW).toOpenPartialHomeomorph G he hn with hΦ_def
  have hΦG : ∀ w, Φ w = G w := fun w ↦ rfl
  -- the differential of `G` is invertible near `v`
  have hDv : ∀ᶠ w in 𝓝 v, fderiv ℝ G w ∈ range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) := by
    have hcont : ContinuousAt (fderiv ℝ G) v :=
      ((hGW v hvW).fderiv_right (m := 0) (by simp)).continuousAt
    refine hcont.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds ?_)
    rw [he.fderiv]
    exact mem_range_self _
  obtain ⟨S, hSsub, hSo, hvS⟩ : ∃ S, S ⊆ Φ.source ∩ W ∩ D ∩
      {w | fderiv ℝ G w ∈ range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)} ∧ IsOpen S ∧ v ∈ S :=
    mem_nhds_iff.1 (inter_mem (inter_mem (inter_mem (Φ.open_source.mem_nhds
      ((hGW v hvW).mem_toOpenPartialHomeomorph_source he hn)) (hWo.mem_nhds hvW))
      (hD.mem_nhds hvD)) hDv)
  have hSsrc : S ⊆ Φ.source := fun w hw ↦ (hSsub hw).1.1.1
  refine ⟨S, (chartAt H x₀).source ∩ extChartAt I x₀ ⁻¹' (Φ '' S),
    fun x ↦ Φ.symm (extChartAt I x₀ x), ?_, ?_, fun w hw ↦ (hSsub hw).1.2, ?_, ?_, ?_⟩
  · exact isOpen_extChartAt_preimage x₀ (Φ.isOpen_image_of_subset_source hSo hSsrc)
  · exact ⟨mem_chart_source H x₀, v, hvS, rfl⟩
  · rintro x ⟨hx, w, hw, hwx⟩
    refine ⟨w, hw, ?_⟩
    have hsrc : expMap I p w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact (hSsub hw).1.1.2.2
    exact (extChartAt I x₀).injOn hsrc (by rwa [extChartAt_source]) ((hΦG w).symm.trans hwx)
  · rintro x ⟨hx, w, hw, hwx⟩
    obtain ⟨⟨⟨hwΦ, hwW⟩, -⟩, e', he'⟩ := hSsub hw
    have hdiff : HasFDerivAt Φ (e' : E →L[ℝ] E) (Φ.symm (Φ w)) := by
      rw [Φ.left_inv hwΦ, he']
      exact ((hGW w hwW).differentiableAt (by simp)).hasFDerivAt
    have hsymm : ContDiffAt ℝ ∞ Φ.symm (Φ w) :=
      Φ.contDiffAt_symm (Φ.map_source hwΦ) hdiff (by rw [Φ.left_inv hwΦ]; exact hGW w hwW)
    have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ.symm (extChartAt I x₀ x) := by
      rw [← hwx]; exact hsymm.contMDiffAt
    exact (h1.comp x (contMDiffAt_extChartAt' hx)).contMDiffWithinAt
  · intro w hw
    exact (congrArg Φ.symm (hΦG w)).symm.trans (Φ.left_inv (hSsrc hw))

/-- **A criterion for normal balls.** If the ball `B_ρ` of `T_p M` lies in the domain of `exp_p`,
`exp_p` is injective on `B_ρ`, and at every `v ∈ B_ρ` the differential of `exp_p` (read in the
chart at `exp_p v`) is invertible, then `B_ρ` is a normal ball. -/
theorem isNormalBall_of_injOn {p : M} {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : tangentBall I p ρ ⊆ expDomain I p) (hinj : InjOn (expMap I p) (tangentBall I p ρ))
    (hD : ∀ v ∈ tangentBall I p ρ, ∃ e : E ≃L[ℝ] E,
      HasFDerivAt (fun u ↦ extChartAt I (expMap I p v) (expMap I p u)) (e : E →L[ℝ] E) v) :
    IsNormalBall I p ρ := by
  classical
  set B := tangentBall I p ρ with hB
  have hBo : IsOpen B := isOpen_tangentBall p ρ
  have hloc : ∀ v ∈ B, ∃ (S : Set E) (N : Set M) (L : M → E), IsOpen N ∧ expMap I p v ∈ N ∧
      S ⊆ B ∧ N ⊆ expMap I p '' S ∧ ContMDiffOn I 𝓘(ℝ, E) ∞ L N ∧
      ∀ w ∈ S, L (expMap I p w) = w := fun v hv ↦ by
    obtain ⟨e, he⟩ := hD v hv
    exact exists_local_inverse_expMap hBo hv hdom he
  set Lg : M → E := Function.invFunOn (expMap I p) B with hLg_def
  have hLg : ∀ w ∈ B, Lg (expMap I p w) = w := fun w hw ↦
    hinj (Function.invFunOn_mem ⟨w, hw, rfl⟩) hw (Function.invFunOn_eq ⟨w, hw, rfl⟩)
  refine ⟨hρ, hdom, hinj, ?_, Lg, ?_, hLg⟩
  · rw [isOpen_iff_forall_mem_open]
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨S, N, L, hNo, hvN, hSB, hNS, -, -⟩ := hloc v hv
    exact ⟨N, fun y hy ↦ image_mono hSB (hNS hy), hNo, hvN⟩
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨S, N, L, hNo, hvN, hSB, hNS, hL, hLS⟩ := hloc v hv
    have hev : Lg =ᶠ[𝓝 (expMap I p v)] L := by
      filter_upwards [hNo.mem_nhds hvN] with y hy
      obtain ⟨w, hw, rfl⟩ := hNS hy
      rw [hLg w (hSB hw), hLS w hw]
    exact (((hL _ hvN).contMDiffAt (hNo.mem_nhds hvN)).congr_of_eventuallyEq
      hev).contMDiffWithinAt

end Criterion

section Differential

variable {p : M}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- In the chart at `γ t`, the derivative of a curve at `t` is its velocity. -/
lemma deriv_chart_eq_velocity {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    deriv (extChartAt I (γ t) ∘ γ) t = velocity I γ t := by
  rw [← trivializationAt_velocity (γ t) hγ (mem_chart_source H (γ t))]
  exact trivializationAt_self_apply (γ t) _

/-- **The differential of `exp_p` is invertible below the first conjugate radius.** In a
two-dimensional Riemannian manifold of constant curvature `K`, at a point `v` of the domain of
`exp_p` with `‖v‖ < π/√K` if `K > 0`, the differential of `exp_p` (read in the chart at
`exp_p v`) is invertible. -/
theorem exists_hasFDerivAt_expMap (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {v : E} (hv : v ∈ expDomain I p)
    (hvK : 0 < K → ‖(show TangentSpace I p from v)‖ < Real.pi / √K) :
    ∃ e : E ≃L[ℝ] E,
      HasFDerivAt (fun u ↦ extChartAt I (expMap I p v) (expMap I p u)) (e : E →L[ℝ] E) v := by
  by_cases hv0 : v = 0
  · subst hv0
    refine ⟨ContinuousLinearEquiv.refl ℝ E, ?_⟩
    rw [ContinuousLinearEquiv.coe_refl]
    have h := hasFDerivAt_extChartAt_expMap_zero (I := I) p
    rwa [expMap_zero p]
  set x₀ := expMap I p v with hx₀
  set G : E → E := fun u ↦ extChartAt I x₀ (expMap I p u) with hG
  have hGv : ContDiffAt ℝ ∞ G v := contDiffAt_chart_expMap hv (mem_chart_source H x₀)
  have hd : HasFDerivAt G (fderiv ℝ G v) v := (hGv.differentiableAt (by simp)).hasFDerivAt
  suffices hinj : Function.Injective (fderiv ℝ G v) by
    refine ⟨(LinearEquiv.ofInjectiveEndo (fderiv ℝ G v : E →ₗ[ℝ] E)
      hinj).toContinuousLinearEquiv, ?_⟩
    convert hd using 1
    exact ContinuousLinearMap.ext fun _ ↦ rfl
  -- polar decomposition `v = r v_θ`
  obtain ⟨e₁, e₂, he⟩ := exists_orthonormal_pair (I := I) hdim p
  have hdim' : Module.finrank ℝ (TangentSpace I p) = 2 := hdim
  obtain ⟨θ, hθ⟩ := exists_eq_norm_smul_cos_add_sin hdim' he (show TangentSpace I p from v)
  set r := ‖(show TangentSpace I p from v)‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 hv0
  have hvpol : polarVec I e₁ e₂ (r, θ) = v := hθ.symm
  have hq : (r, θ) ∈ polarDomain I p e₁ e₂ := by
    show polarVec I e₁ e₂ (r, θ) ∈ expDomain I p
    rw [hvpol]; exact hv
  have hFq : polarMap I p e₁ e₂ (r, θ) = x₀ := by
    show expMap I p (polarVec I e₁ e₂ (r, θ)) = expMap I p v
    rw [hvpol]
  have hGd : HasFDerivAt G (fderiv ℝ G v) (polarVec I e₁ e₂ (r, θ)) := by rw [hvpol]; exact hd
  have hFsmooth : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (polarMap I p e₁ e₂) (r, θ) :=
    contMDiffOn_polarMap.contMDiffAt (isOpen_polarDomain.mem_nhds hq)
  set dE : E := show E from polarDir I e₁ e₂ θ with hdE
  set d'E : E := show E from polarDir' I e₁ e₂ θ with hd'E
  set pRE : E := show E from pR I (polarMap I p e₁ e₂) (r, θ) with hpRE
  set pθE : E := show E from pθ I (polarMap I p e₁ e₂) (r, θ) with hpθE
  -- `∂_r F (r, θ)` is the image of `v_θ`
  have hR : pRE = fderiv ℝ G v dE := by
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ polarMap I p e₁ e₂ (s, θ)) r := by
      have h2 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ ↦ (s, θ)) r :=
        (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
      exact (hFsmooth.comp r h2).mdifferentiableAt (by simp)
    have hcurve : HasDerivAt (fun s : ℝ ↦ polarVec I e₁ e₂ (s, θ)) dE r := by
      have h := (hasDerivAt_id r).smul_const dE
      exact h.congr_deriv (one_smul ℝ dE)
    have hfun : (extChartAt I (polarMap I p e₁ e₂ (r, θ)) ∘ fun s ↦ polarMap I p e₁ e₂ (s, θ)) =
        G ∘ fun s ↦ polarVec I e₁ e₂ (s, θ) := by
      rw [hFq]; rfl
    have h := deriv_chart_eq_velocity hmd
    rw [hfun, (hGd.comp_hasDerivAt r hcurve).deriv] at h
    exact h.symm
  -- `∂_θ F (r, θ)` is the image of `r ∂_θ v_θ`
  have hΘ : pθE = fderiv ℝ G v (r • d'E) := by
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ polarMap I p e₁ e₂ (r, s)) θ := by
      have h2 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ ↦ (r, s)) θ :=
        (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
      exact (hFsmooth.comp θ h2).mdifferentiableAt (by simp)
    have hcurve : HasDerivAt (fun s : ℝ ↦ polarVec I e₁ e₂ (r, s)) (r • d'E) θ := by
      have h : (fun s : ℝ ↦ polarVec I e₁ e₂ (r, s)) = fun s : ℝ ↦
          r • (Real.cos s • (show E from e₁) + Real.sin s • (show E from e₂)) := rfl
      rw [h]
      have h' := (((Real.hasDerivAt_cos θ).smul_const (show E from e₁)).add
        ((Real.hasDerivAt_sin θ).smul_const (show E from e₂))).const_smul r
      exact h'.congr_deriv rfl
    have hfun : (extChartAt I (polarMap I p e₁ e₂ (r, θ)) ∘ fun s ↦ polarMap I p e₁ e₂ (r, s)) =
        G ∘ fun s ↦ polarVec I e₁ e₂ (r, s) := by
      rw [hFq]; rfl
    have h := deriv_chart_eq_velocity hmd
    rw [hfun, (hGd.comp_hasDerivAt θ hcurve).deriv] at h
    exact h.symm
  have hfd' : fderiv ℝ G v d'E = r⁻¹ • pθE := by
    rw [hΘ, map_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  -- orthogonality and lengths of `∂_r F`, `∂_θ F`
  have hunit : ∀ φ, ‖polarDir I e₁ e₂ φ‖ = 1 := fun φ ↦ (polarDir_orthonormal he φ).1
  have h1 := norm_pR_polarMap hq (hunit θ)
  have h2 := norm_pθ_polarMap hdim hK he hq
  have h3 := inner_pR_pθ_polarMap hunit hq
  have hS : S K r ≠ 0 := by
    rcases lt_or_ge 0 K with hK0 | hK0
    · exact (S_pos hK0 hr (hvK hK0)).ne'
    · exact (S_pos_of_nonpos hK0 hr).ne'
  -- decomposition of `u` in the orthonormal basis `v_θ, ∂_θ v_θ`
  obtain ⟨hn1, hn2, hn12⟩ := polarDir_orthonormal (I := I) he θ
  refine (injective_iff_map_eq_zero (fderiv ℝ G v)).2 fun u hu ↦ ?_
  set α : ℝ := inner ℝ (polarDir I e₁ e₂ θ) (show TangentSpace I p from u) with hα
  set w : TangentSpace I p := (show TangentSpace I p from u) - α • polarDir I e₁ e₂ θ with hw_def
  have hwd : inner ℝ w (polarDir I e₁ e₂ θ) = (0 : ℝ) := by
    rw [hw_def, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn1,
      real_inner_comm, ← hα]
    ring
  have hw : w = inner ℝ w (polarDir' I e₁ e₂ θ) • polarDir' I e₁ e₂ θ :=
    eq_inner_smul_of_orthonormal_two hdim' hn1 hn2 hn12 hwd
  set β : ℝ := inner ℝ w (polarDir' I e₁ e₂ θ) with hβ
  have hudec : u = α • dE + β • d'E := by
    have h : (show TangentSpace I p from u) = α • polarDir I e₁ e₂ θ + β • polarDir' I e₁ e₂ θ := by
      rw [← hw, hw_def]; abel
    exact h
  have himg : (0 : E) = α • pRE + (β * r⁻¹) • pθE := by
    rw [← hu, hudec, map_add, map_smul, map_smul, ← hR, hfd', smul_smul]
  -- take inner products at `F(r, θ)`
  have himg' : (0 : TangentSpace I (polarMap I p e₁ e₂ (r, θ))) =
      α • pR I (polarMap I p e₁ e₂) (r, θ) + (β * r⁻¹) • pθ I (polarMap I p e₁ e₂) (r, θ) := himg
  have hαz : α = 0 := by
    have := congrArg (fun z ↦ inner ℝ z (pR I (polarMap I p e₁ e₂) (r, θ))) himg'
    simp only [inner_zero_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, h1] at this
    rw [real_inner_comm, h3] at this
    linarith
  have hβz : β = 0 := by
    have := congrArg (fun z ↦ inner ℝ z (pθ I (polarMap I p e₁ e₂) (r, θ))) himg'
    simp only [inner_zero_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, h2, h3] at this
    have hS2 : |S K r| ^ 2 ≠ 0 := pow_ne_zero 2 (abs_ne_zero.2 hS)
    have h0 : β * r⁻¹ * |S K r| ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact h'
      · exact absurd h' (inv_ne_zero hr.ne')
    · exact absurd h hS2
  rw [hudec, hαz, hβz, zero_smul, zero_smul, add_zero]

end Differential

/-- **Normal balls in constant curvature.** In a two-dimensional Riemannian manifold of constant
curvature `K`, let `0 < ρ`, with `ρ ≤ π/√K` if `K > 0`. If the ball `B_ρ` of `T_p M` lies in the
domain of `exp_p` and `exp_p` is injective on it, then `B_ρ` is a normal ball. -/
theorem isNormalBall_of_constCurvature (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p : M} {ρ : ℝ} (hρ : 0 < ρ)
    (hρK : 0 < K → ρ ≤ Real.pi / √K) (hdom : tangentBall I p ρ ⊆ expDomain I p)
    (hinj : InjOn (expMap I p) (tangentBall I p ρ)) : IsNormalBall I p ρ :=
  isNormalBall_of_injOn hρ hdom hinj fun _ hv ↦
    exists_hasFDerivAt_expMap hdim hK (hdom hv) fun hK0 ↦ lt_of_lt_of_le hv (hρK hK0)

end PythagoreanPaper
