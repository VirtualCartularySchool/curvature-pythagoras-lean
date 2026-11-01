import PythagoreanPaper.Riemannian.Polar

/-!
# The cosine law in a normal ball (manuscript §9, C9.3)

In a two-dimensional Riemannian manifold of constant curvature `K`, let `σ` be a unit-speed
geodesic which stays in a punctured normal ball around a point `p`. In geodesic polar coordinates
around `p`, the function `h = C_K ∘ r ∘ σ` (`r`: the polar radius) satisfies `h'' + K h = 0`:
this is `hasDerivAt_S_mul_polar`, from `D_θ ∂_r F = (C_K / S_K) ∂_θ F`. Solving this equation
gives the cosine law `cosine_law_normalBall` for a triangle with a vertex at `p`.

* `exists_polar_lift`: local polar coordinates of a curve of nonzero tangent vectors at `p`;
* `IsNormalBall`, `exists_isNormalBall`: balls of `T_p M` on which `exp_p` is a diffeomorphism;
* `IsGeodesicFrom.smul_mem_tangentBall`: a geodesic from `p` which stays in a normal ball is
  radial;
* `cosine_law_normalBall`: the cosine law
  `C_K(c) = C_K(a) C_K(b) + K S_K(a) S_K(b) cos C` when the side avoids `p`;
  `cosine_law_normalBall_of_mem`: the degenerate case where the side passes through `p` (then the
  law is the addition formula `C_sub`); `cosine_law_normalBall'`: both cases.

The application to geodesic triangles is in `PythagoreanPaper.Riemannian.Triangle`.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

section PlaneExpansion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Expansion in an orthonormal basis `w₁, w₂` of a Euclidean plane. -/
lemma eq_inner_smul_add_inner_smul (hdim : Module.finrank ℝ V = 2) {w₁ w₂ : V}
    (hw : Orthonormal ℝ ![w₁, w₂]) (x : V) : x = inner ℝ w₁ x • w₁ + inner ℝ w₂ x • w₂ := by
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![w₁, w₂]) := by
    rw [hw.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [hdim])]
  have hb : ⇑(OrthonormalBasis.mk hw hsp) = ![w₁, w₂] := OrthonormalBasis.coe_mk hw hsp
  have := (OrthonormalBasis.mk hw hsp).sum_repr' x
  rw [Fin.sum_univ_two, hb] at this
  simpa using this.symm

/-- Parseval's identity in a Euclidean plane. -/
lemma norm_sq_eq_inner_sq_add_inner_sq (hdim : Module.finrank ℝ V = 2) {w₁ w₂ : V}
    (hw : Orthonormal ℝ ![w₁, w₂]) (x : V) :
    ‖x‖ ^ 2 = inner ℝ w₁ x ^ 2 + inner ℝ w₂ x ^ 2 := by
  obtain ⟨h1, h2, h12⟩ := orthonormal_two_facts hw
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [eq_inner_smul_add_inner_smul hdim hw x]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm w₁ w₂, h12]
  ring

end PlaneExpansion

/-- An open interval around a compact interval `[0, b]` inside an open set. -/
lemma exists_Ioo_subset_of_Icc_subset {s : Set ℝ} (hs : IsOpen s) {b : ℝ} (hb : 0 ≤ b)
    (h : Icc 0 b ⊆ s) : ∃ δ > 0, Ioo (-δ) (b + δ) ⊆ s := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hs h
  refine ⟨δ, hδ, fun x hx ↦ hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨max 0 (min x b), ⟨le_max_left _ _, max_le hb (min_le_right _ _)⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith [hx.1, hx.2])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

section Reparametrization

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The velocity of an affinely reparametrized curve. -/
lemma velocity_comp_affine {γ : ℝ → M} {a c t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (a * t + c)) :
    (velocity I (fun s ↦ γ (a * s + c)) t : E) = a • (velocity I γ (a * t + c) : E) := by
  set x₀ := γ (a * t + c)
  have hsrc : γ (a * t + c) ∈ (chartAt H x₀).source := mem_chart_source H _
  have hb := mem_baseSet_of_mem_chart_source (I := I) hsrc
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ a * s + c) t :=
    ((differentiableAt_id.const_mul a).add_const c).mdifferentiableAt
  have hγa : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ γ (a * s + c)) t := hγ.comp t hm
  have e₁ := trivializationAt_velocity x₀ hγa hsrc
  have e₂ := trivializationAt_velocity x₀ hγ hsrc
  have hd : HasDerivAt (extChartAt I x₀ ∘ γ) (deriv (extChartAt I x₀ ∘ γ) (a * t + c))
      (a * t + c) :=
    (mdifferentiableAt_iff_differentiableAt.1
      ((mdifferentiableAt_extChartAt hsrc).comp _ hγ)).hasDerivAt
  have hd' : deriv (extChartAt I x₀ ∘ fun s ↦ γ (a * s + c)) t =
      a • deriv (extChartAt I x₀ ∘ γ) (a * t + c) := by
    have := hd.scomp t (((hasDerivAt_id t).const_mul a).add_const c)
    simp only [mul_one] at this
    exact this.deriv
  have key : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ (a * t + c))
      (velocity I (fun s ↦ γ (a * s + c)) t) =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ (a * t + c))
        (a • velocity I γ (a * t + c)) := by
    rw [map_smul, e₂, ← hd']
    exact e₁
  have := congrArg ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ (a * t + c))) key
  rwa [Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb,
    Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb] at this

/-- **Affine reparametrization of geodesics**: if `γ` is a geodesic, so is `t ↦ γ(a t + c)`. -/
theorem IsGeodesicOn.comp_affine {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn I γ U) (a c : ℝ) :
    IsGeodesicOn I (fun t ↦ γ (a * t + c)) ((fun t ↦ a * t + c) ⁻¹' U) := by
  intro t ht
  set x₀ := γ (a * t + c)
  have hsrc : γ (a * t + c) ∈ (chartAt H x₀).source := mem_chart_source H _
  have hev := hγ.hasDerivAt_chart hU x₀ ht hsrc
  have htend : Tendsto (fun s : ℝ ↦ a * s + c) (𝓝 t) (𝓝 (a * t + c)) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt
  have hevU : ∀ᶠ s in 𝓝 t, a * s + c ∈ U := htend.eventually (hU.mem_nhds ht)
  have hev' := htend.eventually hev
  have hevγa : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ γ (a * s + c)) s ∧
      (fun s ↦ γ (a * s + c)) s ∈ (chartAt H x₀).source := by
    filter_upwards [hevU, hev'] with s hs hs'
    exact ⟨(hγ.mdifferentiableAt hs).comp s
      ((differentiableAt_id.const_mul a).add_const c).mdifferentiableAt, hs'.2⟩
  rw [geodesicAt_iff_chart x₀ hevγa]
  set k := extChartAt I x₀ ∘ γ with hk_def
  have hderiv_eq : deriv (extChartAt I x₀ ∘ fun s ↦ γ (a * s + c)) =ᶠ[𝓝 t]
      fun s ↦ a • deriv k (a * s + c) := by
    filter_upwards [hev'] with s hs
    have hk : HasDerivAt k (deriv k (a * s + c)) (a * s + c) :=
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt _ hs.1
    have := hk.scomp s (((hasDerivAt_id s).const_mul a).add_const c)
    simp only [mul_one] at this
    exact this.deriv
  have hd2 : HasDerivAt (deriv k)
      (-christoffelL I x₀ (k (a * t + c)) (deriv k (a * t + c)) (deriv k (a * t + c)))
      (a * t + c) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt _ hev.self_of_nhds.1
  have hd2' : HasDerivAt (fun s ↦ a • deriv k (a * s + c))
      (a • (a • -christoffelL I x₀ (k (a * t + c)) (deriv k (a * t + c))
        (deriv k (a * t + c)))) t := by
    have := hd2.scomp t (((hasDerivAt_id t).const_mul a).add_const c)
    simp only [mul_one] at this
    exact this.const_smul a
  rw [hderiv_eq.eq_of_nhds]
  refine (hd2'.congr_of_eventuallyEq hderiv_eq).congr_deriv ?_
  show _ = -christoffelL I x₀ (k (a * t + c)) (a • deriv k (a * t + c))
    (a • deriv k (a * t + c))
  simp only [map_smul, smul_apply, smul_neg]

/-- An affine reparametrization of a geodesic on an open interval, seen from one of its points. -/
theorem IsGeodesicOn.isGeodesicFrom_affine {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hJ' : IsPreconnected J) (hσ : IsGeodesicOn I σ J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (a : ℝ) :
    IsGeodesicFrom I (σ t₀) (a • (velocity I σ t₀ : E)) (fun t ↦ σ (a * t + t₀))
      ((fun t ↦ a * t + t₀) ⁻¹' J) where
  isOpen := hJ.preimage ((continuous_const.mul continuous_id).add continuous_const)
  isPreconnected := by
    have hU := isPreconnected_iff_ordConnected.1 hJ'
    refine isPreconnected_iff_ordConnected.2 ?_
    rcases le_total 0 a with ha | ha
    · exact hU.preimage_mono fun x y hxy ↦ by
        show a * x + t₀ ≤ a * y + t₀
        nlinarith
    · exact hU.preimage_anti fun x y hxy ↦ by
        show a * y + t₀ ≤ a * x + t₀
        nlinarith
  zero_mem := by simpa using ht₀
  isGeodesicOn := hσ.comp_affine hJ a t₀
  apply_zero := by simp
  velocity_zero := by
    rw [velocity_comp_affine (by simpa using hσ.mdifferentiableAt ht₀)]
    exact congrArg (fun s ↦ a • (velocity I σ s : E)) (by ring)

end Reparametrization

section Lift

variable {p : M} {e₁ e₂ : TangentSpace I p}

omit [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- A two-dimensional tangent space has an orthonormal basis. -/
lemma exists_orthonormal_pair (hdim : Module.finrank ℝ E = 2) (p : M) :
    ∃ e₁ e₂ : TangentSpace I p, Orthonormal ℝ ![e₁, e₂] := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have hdim' : Module.finrank ℝ (TangentSpace I p) = 2 := hdim
  let b := (stdOrthonormalBasis ℝ (TangentSpace I p)).reindex (finCongr hdim')
  refine ⟨b 0, b 1, ?_⟩
  have h : ![b 0, b 1] = ⇑b := by
    ext i
    fin_cases i <;> rfl
  rw [h]
  exact b.orthonormal

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Local polar coordinates of a curve in `T_p M ∖ {0}`** (dimension two): near a time `t₀` with
`u(t₀) ≠ 0`, a differentiable curve `u` of tangent vectors at `p` is `u(t) = r(t) v_θ(t)` with
`(r, θ)` differentiable, `r = |u|`, for an orthonormal pair `w₁, w₂` adapted to `u(t₀)`. -/
lemma exists_polar_lift (hdim : Module.finrank ℝ E = 2) (he : Orthonormal ℝ ![e₁, e₂])
    {u : ℝ → E} {V : Set ℝ} (hV : IsOpen V) (hu : ∀ t ∈ V, DifferentiableAt ℝ u t) {t₀ : ℝ}
    (ht₀ : t₀ ∈ V) (hu0 : (show TangentSpace I p from u t₀) ≠ 0) :
    ∃ w₁ w₂ : TangentSpace I p, Orthonormal ℝ ![w₁, w₂] ∧ ∃ (ℓ : ℝ → ℝ × ℝ) (V' : Set ℝ),
      IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ ∀ t ∈ V', DifferentiableAt ℝ ℓ t ∧
        polarVec I w₁ w₂ (ℓ t) = u t ∧ (ℓ t).1 = ‖(show TangentSpace I p from u t)‖ := by
  have hdim' : Module.finrank ℝ (TangentSpace I p) = 2 := hdim
  obtain ⟨θ₀, hθ₀⟩ := exists_eq_norm_smul_cos_add_sin hdim' he (show TangentSpace I p from u t₀)
  obtain ⟨h1, h2, h21⟩ := polarDir_orthonormal he θ₀
  set w₁ := polarDir I e₁ e₂ θ₀ with hw₁
  set w₂ := polarDir' I e₁ e₂ θ₀ with hw₂
  have hw : Orthonormal ℝ ![w₁, w₂] := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · fin_cases i
      · exact h1
      · exact h2
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · show inner ℝ w₁ w₂ = 0
        rw [real_inner_comm]; exact h21
      · exact h21
      · exact absurd rfl hij
  refine ⟨w₁, w₂, hw, ?_⟩
  set ι : E →L[ℝ] TangentSpace I p := ContinuousLinearMap.id ℝ E
  set f₁ : E →L[ℝ] ℝ := (innerSL ℝ w₁).comp ι
  set f₂ : E →L[ℝ] ℝ := (innerSL ℝ w₂).comp ι
  set z : ℝ → ℂ := fun t ↦ (f₁ (u t) : ℂ) + (f₂ (u t) : ℂ) * Complex.I with hz_def
  have hzd : ∀ t ∈ V, DifferentiableAt ℝ z t := by
    intro t ht
    have hf₁ : DifferentiableAt ℝ (fun t ↦ f₁ (u t)) t := f₁.differentiableAt.comp t (hu t ht)
    have hf₂ : DifferentiableAt ℝ (fun t ↦ f₂ (u t)) t := f₂.differentiableAt.comp t (hu t ht)
    exact (Complex.ofRealCLM.differentiableAt.comp t hf₁).add
      ((Complex.ofRealCLM.differentiableAt.comp t hf₂).mul_const Complex.I)
  have hzc : ContinuousOn z V := fun t ht ↦ (hzd t ht).continuousAt.continuousWithinAt
  have hre : ∀ t, (z t).re = inner ℝ w₁ (show TangentSpace I p from u t) := fun t ↦ by
    rw [show (z t).re = f₁ (u t) by simp [z]]
    rfl
  have him : ∀ t, (z t).im = inner ℝ w₂ (show TangentSpace I p from u t) := fun t ↦ by
    rw [show (z t).im = f₂ (u t) by simp [z]]
    rfl
  have hu₀ : (show TangentSpace I p from u t₀) = ‖(show TangentSpace I p from u t₀)‖ • w₁ := hθ₀
  have hz₀ : z t₀ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre, hu₀, real_inner_smul_right, real_inner_self_eq_norm_sq, h1, one_pow, mul_one]
    exact norm_pos_iff.2 hu0
  refine ⟨fun t ↦ (‖z t‖, Complex.arg (z t)), V ∩ z ⁻¹' Complex.slitPlane,
    hzc.isOpen_inter_preimage hV Complex.isOpen_slitPlane, ⟨ht₀, hz₀⟩, inter_subset_left,
    fun t ht ↦ ⟨?_, ?_, ?_⟩⟩
  · have hz0 : z t ≠ 0 := Complex.slitPlane_ne_zero ht.2
    have hlog := HasDerivAt.clog_real (hzd t ht.1).hasDerivAt ht.2
    have harg : HasDerivAt (fun t ↦ Complex.arg (z t))
        (Complex.imCLM (deriv z t / z t)) t := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
      simpa [Function.comp_def, Complex.log_im] using this
    exact ((hzd t ht.1).norm ℝ hz0).prodMk harg.differentiableAt
  · show (‖z t‖ • polarDir I w₁ w₂ (Complex.arg (z t)) : TangentSpace I p) = u t
    rw [polarDir, smul_add, smul_smul, smul_smul, Complex.norm_mul_cos_arg,
      Complex.norm_mul_sin_arg, hre, him]
    exact (eq_inner_smul_add_inner_smul hdim' hw _).symm
  · show ‖z t‖ = _
    have hsq : ‖z t‖ ^ 2 = ‖(show TangentSpace I p from u t)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him,
        norm_sq_eq_inner_sq_add_inner_sq hdim' hw]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end Lift

section PolarHessian

variable [T2Space M] {p : M} {e₁ e₂ : TangentSpace I p}

/-- In geodesic polar coordinates built from an orthonormal pair, the radial component of the
velocity of `t ↦ F(ℓ(t))` is `r' = ⟨σ', ∂_r F⟩`. -/
lemma fst_eq_inner_velocity_pR (he : Orthonormal ℝ ![e₁, e₂]) {ℓ : ℝ → ℝ × ℝ} {ℓ' : ℝ × ℝ}
    {t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ polarDomain I p e₁ e₂) :
    ℓ'.1 = inner ℝ (velocity I (fun t ↦ polarMap I p e₁ e₂ (ℓ t)) t)
      (pR I (polarMap I p e₁ e₂) (ℓ t)) := by
  have hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1 := fun θ ↦ (polarDir_orthonormal he θ).1
  have hS : SmoothInChart I (polarMap I p e₁ e₂) (polarMap I p e₁ e₂ (ℓ t))
      (polarDomain I p e₁ e₂ ∩ polarMap I p e₁ e₂ ⁻¹'
        (chartAt H (polarMap I p e₁ e₂ (ℓ t))).source) :=
    smoothInChart_of_contMDiffOn isOpen_polarDomain contMDiffOn_polarMap _
  rw [hS.velocity_eq hℓ ⟨hq, mem_chart_source H _⟩, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, norm_pR_polarMap hq (hunit _),
    real_inner_comm, inner_pR_pθ_polarMap hunit hq]
  ring

/-- In dimension two with constant curvature `K`: `S_K(r) D_θ ∂_r F = C_K(r) ∂_θ F` on the polar
domain. -/
theorem S_smul_covθ_pR_polarMap (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) {q : ℝ × ℝ}
    (hq : q ∈ polarDomain I p e₁ e₂) :
    S K q.1 • covθ I (polarMap I p e₁ e₂) (pR I (polarMap I p e₁ e₂)) q =
      C K q.1 • pθ I (polarMap I p e₁ e₂) q := by
  rcases q with ⟨r, θ⟩
  obtain ⟨a, b, hab, h0, hr⟩ := exists_Ioo_polarDomain hq
  obtain ⟨ν, hν, -, -, -, -, -, -, hmain, -⟩ := sec6_jacobi_eq_S hdim hK he θ hab h0
  have hS : SmoothInChart I (polarMap I p e₁ e₂) (polarMap I p e₁ e₂ (r, θ))
      (polarDomain I p e₁ e₂ ∩ polarMap I p e₁ e₂ ⁻¹'
        (chartAt H (polarMap I p e₁ e₂ (r, θ))).source) :=
    smoothInChart_of_contMDiffOn isOpen_polarDomain contMDiffOn_polarMap _
  have hsym := hS.covR_pθ ⟨hq, mem_chart_source H _⟩
  have hev : ∀ᶠ s in 𝓝 r, pθ I (polarMap I p e₁ e₂) (s, θ) = S K s • ν s := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs using (hmain s hs).1
  have hcov : covR I (polarMap I p e₁ e₂) (pθ I (polarMap I p e₁ e₂)) (r, θ) =
      C K r • ν r := by
    show covAlong (CovariantDerivative.leviCivitaConnection I M)
      (fun s ↦ polarMap I p e₁ e₂ (s, θ)) (fun s ↦ pθ I (polarMap I p e₁ e₂) (s, θ)) r = _
    rw [covAlong_congr (CovariantDerivative.leviCivitaConnection I M) hev,
      covAlong_smul (CovariantDerivative.leviCivitaConnection I M) (hasDerivAt_S K r).differentiableAt
        (hν r hr).1, (hν r hr).2, smul_zero,
      add_zero, (hasDerivAt_S K r).deriv]
  show S K r • covθ I (polarMap I p e₁ e₂) (pR I (polarMap I p e₁ e₂)) (r, θ) =
    C K r • pθ I (polarMap I p e₁ e₂) (r, θ)
  rw [← hsym, hcov, smul_smul, mul_comm, ← smul_smul, ← (hmain r hr).1]

/-- **The Hessian of `C_K ∘ r` along geodesics** (dimension two, constant curvature `K`). Let
`σ = F ∘ ℓ` be a geodesic on an open set `U` of times, written in geodesic polar coordinates
`ℓ = (r, θ)`, with `ℓ' = (r', θ')` the derivative of `ℓ`. Then `(S_K(r) r')' = C_K(r) |σ'|²`. -/
theorem hasDerivAt_S_mul_polar (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂])
    {ℓ ℓ' : ℝ → ℝ × ℝ} {U : Set ℝ} (hU : IsOpen U) (hℓ : ∀ t ∈ U, HasDerivAt ℓ (ℓ' t) t)
    (hℓD : ∀ t ∈ U, ℓ t ∈ polarDomain I p e₁ e₂)
    (hgeo : IsGeodesicOn I (fun t ↦ polarMap I p e₁ e₂ (ℓ t)) U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun t ↦ S K (ℓ t).1 * (ℓ' t).1)
      (C K (ℓ s).1 * ‖velocity I (fun t ↦ polarMap I p e₁ e₂ (ℓ t)) s‖ ^ 2) s := by
  have hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1 := fun θ ↦ (polarDir_orthonormal he θ).1
  have hSm : ∀ q, SmoothInChart I (polarMap I p e₁ e₂) (polarMap I p e₁ e₂ q)
      (polarDomain I p e₁ e₂ ∩ polarMap I p e₁ e₂ ⁻¹'
        (chartAt H (polarMap I p e₁ e₂ q)).source) := fun q ↦
    smoothInChart_of_contMDiffOn isOpen_polarDomain contMDiffOn_polarMap _
  -- `r' = ⟨σ', ∂_r F⟩`
  have hr' : ∀ t ∈ U, (ℓ' t).1 = inner ℝ (velocity I (fun t ↦ polarMap I p e₁ e₂ (ℓ t)) t)
      (pR I (polarMap I p e₁ e₂) (ℓ t)) := fun t ht ↦
    fst_eq_inner_velocity_pR he (hℓ t ht) (hℓD t ht)
  have hev : (fun t ↦ S K (ℓ t).1 * inner ℝ
      (velocity I (fun t ↦ polarMap I p e₁ e₂ (ℓ t)) t) (pR I (polarMap I p e₁ e₂) (ℓ t))) =ᶠ[𝓝 s]
      fun t ↦ S K (ℓ t).1 * (ℓ' t).1 := by
    filter_upwards [hU.mem_nhds hs] with t ht
    rw [hr' t ht]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  -- the derivative of `⟨σ', ∂_r F ∘ ℓ⟩`
  have hqN : ℓ s ∈ polarDomain I p e₁ e₂ ∩ polarMap I p e₁ e₂ ⁻¹'
      (chartAt H (polarMap I p e₁ e₂ (ℓ s))).source := ⟨hℓD s hs, mem_chart_source H _⟩
  have hwd := (((hSm (ℓ s)).contDiffOn_fderiv_apply (1, 0)).differentiableOn (by simp) (ℓ s)
    hqN).differentiableAt ((hSm (ℓ s)).isOpen.mem_nhds hqN)
  have hpR := (hSm (ℓ s)).covAlong_coord (fun q hq ↦ (hSm (ℓ s)).pR_coord hq) (hℓ s hs) hqN hwd
  have hD := (hSm (ℓ s)).covAlong_eq (fun q hq ↦ (hSm (ℓ s)).pR_coord hq) (hℓ s hs) hqN hwd
  have hin := hasDerivAt_inner_along (hgeo s hs).1 hpR.1
  have h0 : covR I (polarMap I p e₁ e₂) (pR I (polarMap I p e₁ e₂)) (ℓ s) = 0 :=
    isGeodesicVariation_polarMap.isGeodesic _ (hℓD s hs)
  rw [(hgeo s hs).2, inner_zero_left, zero_add, hD, h0, smul_zero, zero_add] at hin
  have hfst : HasDerivAt (fun t ↦ (ℓ t).1) (ℓ' s).1 s :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s (hℓ s hs)
  have hSr' := (hasDerivAt_S K (ℓ s).1).comp s hfst
  have hSr : HasDerivAt (fun t ↦ S K (ℓ t).1) (C K (ℓ s).1 * (ℓ' s).1) s := hSr'
  convert hSr.mul hin using 1
  -- the algebra
  have hσ' := (hSm (ℓ s)).velocity_eq (hℓ s hs) hqN
  have hK1 := S_smul_covθ_pR_polarMap hdim hK he (hℓD s hs)
  have hpθ := norm_pθ_polarMap hdim hK he (hℓD s hs)
  have hgauss := inner_pR_pθ_polarMap hunit (hℓD s hs)
  have hmetric := sec6_metric hdim hK he (hℓ s hs) (hℓD s hs)
  have hB : S K (ℓ s).1 * inner ℝ (velocity I (fun t ↦ polarMap I p e₁ e₂ (ℓ t)) s)
      ((ℓ' s).2 • covθ I (polarMap I p e₁ e₂) (pR I (polarMap I p e₁ e₂)) (ℓ s)) =
      C K (ℓ s).1 * ((ℓ' s).2 ^ 2 * S K (ℓ s).1 ^ 2) := by
    rw [real_inner_smul_right, ← mul_assoc, mul_comm (S K (ℓ s).1) ((ℓ' s).2), mul_assoc,
      ← real_inner_smul_right, hK1, real_inner_smul_right, hσ', inner_add_left,
      real_inner_smul_left, real_inner_smul_left, hgauss, real_inner_self_eq_norm_sq, hpθ,
      sq_abs]
    ring
  rw [hB, hmetric, ← hr' s hs]
  ring

end PolarHessian

section WithT2

variable [T2Space M]

section NormalBall

variable (I) in
/-- **Normal ball**: `exp_p` maps the ball `B_ρ` of `T_p M` diffeomorphically onto the open set
`exp_p(B_ρ)` (`B_ρ` lies in the domain of `exp_p`, on which `exp_p` is smooth; `exp_p` is injective
on `B_ρ`, and has a smooth inverse on `exp_p(B_ρ)`). -/
structure IsNormalBall (p : M) (ρ : ℝ) : Prop where
  pos : 0 < ρ
  subset : tangentBall I p ρ ⊆ expDomain I p
  injOn : InjOn (expMap I p) (tangentBall I p ρ)
  isOpen : IsOpen (expMap I p '' tangentBall I p ρ)
  exists_inv : ∃ L : M → E, ContMDiffOn I 𝓘(ℝ, E) ∞ L (expMap I p '' tangentBall I p ρ) ∧
    ∀ v ∈ tangentBall I p ρ, L (expMap I p v) = v

/-- Small balls are normal balls (`exists_normal_nbhd`). -/
theorem exists_isNormalBall (p : M) : ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, IsNormalBall I p ε := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_normal_nbhd (I := I) p
  refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h ε hε
  exact ⟨hε.1, h1, h2, h3, h4⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma norm_smul_tangent {p : M} {v : E} {s : ℝ} (hs : 0 ≤ s) :
    ‖(show TangentSpace I p from (s • v : E))‖ = s * ‖(show TangentSpace I p from v)‖ := by
  show ‖s • (show TangentSpace I p from v)‖ = _
  rw [norm_smul, Real.norm_of_nonneg hs]

/-- **Geodesics from `p` which stay in a normal ball are radial**: if a geodesic `γ` from `p` with
initial velocity `v` stays in `exp_p(B_ρ)` for `0 ≤ t ≤ T`, then `t v ∈ B_ρ` (and
`γ(t) = exp_p(t v)`, `expMap_smul`) for `0 ≤ t ≤ T`. -/
theorem IsGeodesicFrom.smul_mem_tangentBall {p : M} {γ : ℝ → M} {v : E} {U : Set ℝ}
    (hγ : IsGeodesicFrom I p v γ U) {ρ T : ℝ} (hρ : IsNormalBall I p ρ) (hTU : Icc 0 T ⊆ U)
    (hγB : ∀ t ∈ Icc 0 T, γ t ∈ expMap I p '' tangentBall I p ρ) :
    ∀ t ∈ Icc 0 T, t • v ∈ tangentBall I p ρ := by
  obtain ⟨L, hL, hLexp⟩ := hρ.exists_inv
  have hexp : ∀ t ∈ Icc 0 T, expMap I p (t • v) = γ t := fun t ht ↦
    (expMap_smul hγ (by rw [uIcc_of_le ht.1]; exact (Icc_subset_Icc_right ht.2).trans hTU)).2
  by_contra hcon
  obtain ⟨t, ht, htB⟩ := not_forall₂.1 hcon
  set n := ‖(show TangentSpace I p from v)‖ with hn_def
  have hρt : ρ ≤ t * n := by
    have h : ¬ ‖(show TangentSpace I p from (t • v : E))‖ < ρ := htB
    rw [norm_smul_tangent ht.1, not_lt] at h
    exact h
  have hn : 0 < n := by
    by_contra hn0
    have hn0' : n = 0 := le_antisymm (not_lt.1 hn0) (norm_nonneg _)
    rw [hn0', mul_zero] at hρt
    exact absurd hρt (not_le.2 hρ.pos)
  set t₁ := ρ / n with ht₁_def
  have ht₁ : 0 < t₁ := div_pos hρ.pos hn
  have ht₁n : t₁ * n = ρ := div_mul_cancel₀ _ hn.ne'
  have ht₁t : t₁ ≤ t := by
    rw [ht₁_def, div_le_iff₀ hn]
    exact hρt
  have ht₁I : t₁ ∈ Icc 0 T := ⟨ht₁.le, ht₁t.trans ht.2⟩
  have hbefore : ∀ s ∈ Ico 0 t₁, L (γ s) = s • v := by
    intro s hs
    have hsB : s • v ∈ tangentBall I p ρ := by
      show ‖(show TangentSpace I p from (s • v : E))‖ < ρ
      rw [norm_smul_tangent hs.1, ← ht₁n]
      exact mul_lt_mul_of_pos_right hs.2 hn
    rw [← hexp s ⟨hs.1, hs.2.le.trans ht₁I.2⟩, hLexp _ hsB]
  have hcont : ContinuousAt (fun s ↦ L (γ s)) t₁ := by
    have hγc : ContinuousAt γ t₁ := (hγ.isGeodesicOn.mdifferentiableAt (hTU ht₁I)).continuousAt
    have hLc : ContinuousAt L (γ t₁) :=
      hL.continuousOn.continuousAt (hρ.isOpen.mem_nhds (hγB t₁ ht₁I))
    exact hLc.comp hγc
  have hlim1 : Tendsto (fun s ↦ L (γ s)) (𝓝[<] t₁) (𝓝 (L (γ t₁))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun s ↦ L (γ s)) (𝓝[<] t₁) (𝓝 (t₁ • v)) := by
    have h1 : Tendsto (fun s : ℝ ↦ s • v) (𝓝[<] t₁) (𝓝 (t₁ • v)) :=
      ((continuous_id.smul continuous_const).tendsto t₁).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht₁] with s hs
    exact (hbefore s ⟨hs.1.le, hs.2⟩).symm
  have heq : L (γ t₁) = t₁ • v := tendsto_nhds_unique hlim1 hlim2
  obtain ⟨w, hwB, hw⟩ := hγB t₁ ht₁I
  have hmem : L (γ t₁) ∈ tangentBall I p ρ := by
    rw [← hw, hLexp w hwB]
    exact hwB
  rw [heq] at hmem
  have h2 : ‖(show TangentSpace I p from (t₁ • v : E))‖ < ρ := hmem
  rw [norm_smul_tangent ht₁.le, ht₁n] at h2
  exact lt_irrefl _ h2

end NormalBall

section CosineLaw

/-- **The cosine law in a normal ball** (manuscript C9.3; dimension two, constant curvature `K`).
Let `exp_p(B_ρ)` be a normal ball around `p`. Let `σ` be a unit-speed geodesic, defined on an open
set containing `[0, b]`, whose points `σ(t)`, `0 ≤ t ≤ b`, lie in `exp_p(B_ρ) ∖ {p}`. Suppose that
`σ(0) = γ(a)` for a unit-speed geodesic `γ` from `p` (`0 < a < ρ`), and that
`σ(b) = exp_p(c w)` with `‖w‖ = 1`, `0 ≤ c < ρ`. Then, with `cos C = ⟨σ'(0), -γ'(a)⟩` (the cosine of
the angle at `σ(0)` between `σ` and the geodesic back to `p`),
`C_K(c) = C_K(a) C_K(b) + K S_K(a) S_K(b) cos C`. -/
theorem cosine_law_normalBall (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p : M} {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) {b : ℝ} (hb : 0 ≤ b) (hJb : Icc 0 b ⊆ J)
    (hσ : IsGeodesicOn I σ J) (hσ1 : ‖velocity I σ 0‖ = 1)
    (hσU : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ ∧ σ t ≠ p)
    {γ : ℝ → M} {v : E} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (hv1 : ‖(show TangentSpace I p from v)‖ = 1) {a : ℝ} (ha : 0 < a) (haU : Icc 0 a ⊆ U)
    (haρ : a < ρ) (hγσ : γ a = σ 0)
    {c : ℝ} (hc : 0 ≤ c) (hcρ : c < ρ) {w : E} (hw1 : ‖(show TangentSpace I p from w)‖ = 1)
    (hσb : σ b = expMap I p (c • w)) :
    C K c = C K a * C K b + K * S K a * S K b *
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
  -- the equation `h'' + K h = 0` for `h = C_K ∘ r`
  have hh : ∀ t ∈ Jδ, HasDerivAt (fun t ↦ C K (r t)) (-K * (S K (r t) * deriv r t)) t := by
    intro t ht
    have h1 := (hasDerivAt_C K (r t)).comp t (hloc t ht).1
    have h2 : -K * S K (r t) * deriv r t = -K * (S K (r t) * deriv r t) := by ring
    rw [h2] at h1
    exact h1
  have hh' : ∀ t ∈ Jδ, HasDerivAt (fun t ↦ -K * (S K (r t) * deriv r t)) (-K * C K (r t)) t :=
    fun t ht ↦ (hloc t ht).2.1.const_mul (-K)
  have hsol := eqOn_of_ode h0δ hh hh' (fun t _ ↦ by ring) hbδ
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
  have hfin : C K (r b) = C K (r 0) * C K b + -K * (S K (r 0) * deriv r 0) * S K b := hsol
  rw [hrb, hr0, hinner] at hfin
  rw [hfin, hneg]
  ring

/-- The cosine law in a normal ball, when the geodesic side passes through the centre `p` (the
degenerate case: then `cos C = 1`, `a + c = b`, and the law is the addition formula). -/
theorem cosine_law_normalBall_of_mem {K : ℝ} {p : M} {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) {b : ℝ} (hb : 0 ≤ b) (hJb : Icc 0 b ⊆ J)
    (hσ : IsGeodesicOn I σ J) (hσ1 : ‖velocity I σ 0‖ = 1)
    (hσU : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    {tB : ℝ} (htB : tB ∈ Icc 0 b) (hσtB : σ tB = p)
    {γ : ℝ → M} {v : E} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (hv1 : ‖(show TangentSpace I p from v)‖ = 1) {a : ℝ} (ha : 0 < a) (haU : Icc 0 a ⊆ U)
    (haρ : a < ρ) (hγσ : γ a = σ 0)
    {c : ℝ} (hc : 0 ≤ c) (hcρ : c < ρ) {w : E} (hw1 : ‖(show TangentSpace I p from w)‖ = 1)
    (hσb : σ b = expMap I p (c • w)) :
    C K c = C K a * C K b + K * S K a * S K b *
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
  rw [hinner, hcB, haB, C_sub]
  ring

/-- **The cosine law in a normal ball** (manuscript C9.3), in all cases: for a unit-speed geodesic
`σ` whose points `σ(t)`, `0 ≤ t ≤ b`, lie in the normal ball `exp_p(B_ρ)` (possibly passing
through `p`), from `σ(0) = γ(a)` to `σ(b) = exp_p(c w)`,
`C_K(c) = C_K(a) C_K(b) + K S_K(a) S_K(b) cos C` with `cos C = ⟨σ'(0), -γ'(a)⟩`. -/
theorem cosine_law_normalBall' (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p : M} {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    {σ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) {b : ℝ} (hb : 0 ≤ b) (hJb : Icc 0 b ⊆ J)
    (hσ : IsGeodesicOn I σ J) (hσ1 : ‖velocity I σ 0‖ = 1)
    (hσU : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    {γ : ℝ → M} {v : E} {U : Set ℝ} (hγ : IsGeodesicFrom I p v γ U)
    (hv1 : ‖(show TangentSpace I p from v)‖ = 1) {a : ℝ} (ha : 0 < a) (haU : Icc 0 a ⊆ U)
    (haρ : a < ρ) (hγσ : γ a = σ 0)
    {c : ℝ} (hc : 0 ≤ c) (hcρ : c < ρ) {w : E} (hw1 : ‖(show TangentSpace I p from w)‖ = 1)
    (hσb : σ b = expMap I p (c • w)) :
    C K c = C K a * C K b + K * S K a * S K b *
      inner ℝ (show TangentSpace I (σ 0) from velocity I σ 0)
        (show TangentSpace I (σ 0) from -(velocity I γ a : E)) := by
  by_cases h : ∀ t ∈ Icc 0 b, σ t ≠ p
  · exact cosine_law_normalBall hdim hK hρ hJ hb hJb hσ hσ1 (fun t ht ↦ ⟨hσU t ht, h t ht⟩)
      hγ hv1 ha haU haρ hγσ hc hcρ hw1 hσb
  · obtain ⟨tB, htB, hσtB⟩ := not_forall₂.1 h
    exact cosine_law_normalBall_of_mem hρ hJ hb hJb hσ hσ1 hσU htB (not_not.1 hσtB) hγ hv1 ha
      haU haρ hγσ hc hcρ hw1 hσb

end CosineLaw

end WithT2

end PythagoreanPaper
