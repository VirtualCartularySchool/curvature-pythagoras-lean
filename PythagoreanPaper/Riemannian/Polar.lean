import PythagoreanPaper.Riemannian.TwoParam
import PythagoreanPaper.Riemannian.ExpMap
import PythagoreanPaper.Sec04Jacobi
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Geodesic polar coordinates (manuscript §6)

Fix a point `p` of a Riemannian manifold `M` and an orthonormal pair `e₁, e₂` in `T_p M`, and let
`v_θ = cos θ e₁ + sin θ e₂`. The map `F(r, θ) = exp_p(r v_θ)` (`polarMap`) is defined on the open
set `polarDomain` of parameters with `r v_θ` in the domain of `exp_p`, and is a variation through
geodesics: `r ↦ F(r, θ)` is the geodesic with initial velocity `v_θ`.

* `norm_pR_polarMap`: `|∂_r F| = 1`;
* `inner_pR_pθ_polarMap` (**Gauss lemma**): `⟨∂_r F, ∂_θ F⟩ = 0`;
* `isJacobiFieldOn_polarMap`: `J(r) = ∂_θ F(r, θ)` is a Jacobi field along the geodesic, with
  `J(0) = 0` and `D_r J(0) = ∂_θ v_θ`;
* in dimension two with constant curvature `K`: `|∂_θ F(r, θ)| = |S_K(r)|`, the metric
  `ds² = dr² + S_K(r)² dθ²`, and the length `2π |S_K(r)|` of the geodesic circle of radius `r`;
* `exists_normal_nbhd`: for small `ε`, `exp_p` maps the ball `‖v‖ < ε` of `T_p M`
  diffeomorphically onto an open neighbourhood of `p` (inverse function theorem in the chart at
  `p`, the differential of `exp_p` at `0` being the identity);
* `sec6_polar_coordinates`: `(r, θ)` are coordinates on a punctured neighbourhood of `p`.
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

section ExpLemmas

/-- `s ↦ exp_p (s • v)` coincides with the geodesic `γ_v` on its interval of definition. -/
lemma IsGeodesicFrom.expMap_smul_eqOn {p : M} {v : E} {γ : ℝ → M} {U : Set ℝ}
    (h : IsGeodesicFrom I p v γ U) : EqOn (fun s ↦ expMap I p (s • v)) γ U := by
  intro s hs
  have hU := isPreconnected_iff_ordConnected.1 h.isPreconnected
  exact (expMap_smul h (hU.uIcc_subset h.zero_mem hs)).2

lemma IsGeodesicFrom.expMap_smul_eventuallyEq {p : M} {v : E} {γ : ℝ → M} {U : Set ℝ}
    (h : IsGeodesicFrom I p v γ U) {t : ℝ} (ht : t ∈ U) :
    (fun s ↦ expMap I p (s • v)) =ᶠ[𝓝 t] γ := by
  filter_upwards [h.isOpen.mem_nhds ht] with s hs using h.expMap_smul_eqOn hs

omit [T2Space M] in
/-- If `t • v` is in the domain of `exp_p`, the geodesic with initial velocity `v` is defined on an
open interval containing the times between `0` and `t`. -/
lemma exists_isGeodesicFrom_of_smul_mem {p : M} {v : E} {t : ℝ} (h : t • v ∈ expDomain I p) :
    ∃ (γ : ℝ → M) (U : Set ℝ), IsGeodesicFrom I p v γ U ∧ uIcc 0 t ⊆ U := by
  rcases eq_or_ne t 0 with rfl | ht
  · obtain ⟨ε, hε, γ, hγ0, hγv, -, hγ⟩ := exists_geodesic (I := I) p v
    refine ⟨γ, Ioo (-ε) ε, ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, hε⟩, hγ, hγ0, hγv⟩, ?_⟩
    rw [uIcc_self]
    exact singleton_subset_iff.2 ⟨by linarith, hε⟩
  · obtain ⟨γ', U', hγ', h1⟩ := h
    have hγ := hγ'.smul t⁻¹
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul] at hγ
    refine ⟨_, _, hγ, fun s hs ↦ ?_⟩
    apply h1
    rcases le_total 0 t with h0 | h0
    · rw [uIcc_of_le h0] at hs
      have ht0 : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht)
      exact ⟨mul_nonneg (inv_nonneg.2 h0) hs.1, by
        rw [inv_mul_le_iff₀ ht0, mul_one]; exact hs.2⟩
    · rw [uIcc_of_ge h0] at hs
      have ht0 : t < 0 := lt_of_le_of_ne h0 ht
      refine ⟨mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 h0) hs.2, ?_⟩
      calc t⁻¹ * s ≤ t⁻¹ * t := mul_le_mul_of_nonpos_left hs.1 (inv_nonpos.2 h0)
        _ = 1 := inv_mul_cancel₀ ht

omit [T2Space M] in
lemma zero_mem_expDomain (p : M) : (0 : E) ∈ expDomain I p := by
  obtain ⟨ε, hε, γ, hγ0, hγv, -, hγ⟩ := exists_geodesic (I := I) p (0 : E)
  have h := IsGeodesicFrom.smul (I := I)
    ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, hε⟩, hγ, hγ0, hγv⟩ 0
  rw [smul_zero] at h
  exact ⟨_, _, h, fun r _ ↦ by simpa using (⟨by linarith, hε⟩ : (0 : ℝ) ∈ Ioo (-ε) ε)⟩

/-- `exp_p 0 = p`. -/
lemma expMap_zero (p : M) : expMap I p 0 = p := by
  obtain ⟨ε, hε, γ, hγ0, hγv, -, hγ⟩ := exists_geodesic (I := I) p (0 : E)
  have h : IsGeodesicFrom I p 0 γ (Ioo (-ε) ε) :=
    ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, hε⟩, hγ, hγ0, hγv⟩
  have := (expMap_smul h (t := 0) (by rw [uIcc_self]; exact singleton_subset_iff.2 h.zero_mem)).2
  rwa [zero_smul, hγ0] at this

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- Curves with the same germ have velocities of the same length. -/
lemma norm_velocity_congr {c₁ c₂ : ℝ → M} {t : ℝ} (h : c₁ =ᶠ[𝓝 t] c₂) :
    ‖velocity I c₁ t‖ = ‖velocity I c₂ t‖ :=
  congrArg₂ (fun (x : M) (v : E) ↦ ‖(show TangentSpace I x from v)‖) h.eq_of_nhds
    (velocity_congr h)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- Transporting a norm computation between equal base points. -/
lemma norm_transport {x y : M} (h : x = y) (u : E) :
    ‖(show TangentSpace I x from u)‖ = ‖(show TangentSpace I y from u)‖ := by
  subst h
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- Transporting an inner product computation between equal base points. -/
lemma inner_transport {x y : M} (h : x = y) (u v : E) :
    inner ℝ (show TangentSpace I x from u) (show TangentSpace I x from v) =
      inner ℝ (show TangentSpace I y from u) (show TangentSpace I y from v) := by
  subst h
  rfl

end ExpLemmas

section PolarDefs

variable (I) in
/-- The unit vector `v_θ = cos θ e₁ + sin θ e₂` of `T_p M`. -/
def polarDir {p : M} (e₁ e₂ : TangentSpace I p) (θ : ℝ) : TangentSpace I p :=
  Real.cos θ • e₁ + Real.sin θ • e₂

variable (I) in
/-- The derivative `∂_θ v_θ = -sin θ e₁ + cos θ e₂`. -/
def polarDir' {p : M} (e₁ e₂ : TangentSpace I p) (θ : ℝ) : TangentSpace I p :=
  -Real.sin θ • e₁ + Real.cos θ • e₂

variable (I) in
/-- The vector `r v_θ` of `T_p M`, for `q = (r, θ)` (as an element of the model space `E`). -/
def polarVec {p : M} (e₁ e₂ : TangentSpace I p) (q : ℝ × ℝ) : E :=
  q.1 • polarDir I e₁ e₂ q.2

variable (I) in
/-- **Geodesic polar coordinates** `F(r, θ) = exp_p(r v_θ)`. -/
def polarMap (p : M) (e₁ e₂ : TangentSpace I p) (q : ℝ × ℝ) : M :=
  expMap I p (polarVec I e₁ e₂ q)

variable (I) in
/-- The parameters `(r, θ)` with `r v_θ` in the domain of `exp_p`. -/
def polarDomain (p : M) (e₁ e₂ : TangentSpace I p) : Set (ℝ × ℝ) :=
  polarVec I e₁ e₂ ⁻¹' expDomain I p

end PolarDefs

section PolarBasic

variable {p : M} {e₁ e₂ : TangentSpace I p}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma contDiff_polarVec : ContDiff ℝ ∞ (polarVec I e₁ e₂) := by
  have h : polarVec I e₁ e₂ = fun q : ℝ × ℝ ↦
      q.1 • (Real.cos q.2 • (show E from e₁) + Real.sin q.2 • (show E from e₂)) := rfl
  rw [h]
  fun_prop

lemma isOpen_polarDomain : IsOpen (polarDomain I p e₁ e₂) :=
  (isOpen_expDomain p).preimage contDiff_polarVec.continuous

lemma contMDiffOn_polarMap :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (polarMap I p e₁ e₂) (polarDomain I p e₁ e₂) :=
  (contMDiffOn_expMap p).comp contDiff_polarVec.contMDiff.contMDiffOn fun _ hq ↦ hq

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma polarVec_zero (θ : ℝ) : polarVec I e₁ e₂ (0, θ) = 0 :=
  zero_smul ℝ (polarDir I e₁ e₂ θ)

omit [T2Space M] in
lemma zero_mem_polarDomain (θ : ℝ) : ((0 : ℝ), θ) ∈ polarDomain I p e₁ e₂ := by
  show polarVec I e₁ e₂ (0, θ) ∈ expDomain I p
  rw [polarVec_zero]
  exact zero_mem_expDomain p

lemma polarMap_zero (θ : ℝ) : polarMap I p e₁ e₂ (0, θ) = p := by
  show expMap I p (polarVec I e₁ e₂ (0, θ)) = p
  rw [polarVec_zero]
  exact expMap_zero p

/-- Along the line `r ↦ (r, θ)`, the polar map is the geodesic with initial velocity `v_θ`. -/
lemma exists_polarMap_geodesic {q : ℝ × ℝ} (hq : q ∈ polarDomain I p e₁ e₂) :
    ∃ (γ : ℝ → M) (U : Set ℝ), IsGeodesicFrom I p (show E from polarDir I e₁ e₂ q.2) γ U ∧
      q.1 ∈ U ∧
      EqOn (fun r ↦ polarMap I p e₁ e₂ (r, q.2)) γ U ∧ ∀ r ∈ U, (r, q.2) ∈ polarDomain I p e₁ e₂ := by
  obtain ⟨γ, U, hγ, hU⟩ := exists_isGeodesicFrom_of_smul_mem (I := I) hq
  have hU' := isPreconnected_iff_ordConnected.1 hγ.isPreconnected
  refine ⟨γ, U, hγ, hU right_mem_uIcc, hγ.expMap_smul_eqOn, fun r hr ↦ ?_⟩
  exact (expMap_smul hγ (hU'.uIcc_subset hγ.zero_mem hr)).1

/-- The parameters `r` with `(r, θ)` in the polar domain form an interval containing `0`. -/
lemma isPreconnected_polarDomain_slice (θ : ℝ) :
    IsPreconnected {r : ℝ | (r, θ) ∈ polarDomain I p e₁ e₂} := by
  refine isPreconnected_iff_ordConnected.2 ⟨fun r₁ hr₁ r₂ hr₂ r hr ↦ ?_⟩
  -- the slice is star-shaped around `0`
  have star : ∀ s ∈ {r : ℝ | (r, θ) ∈ polarDomain I p e₁ e₂}, ∀ r ∈ uIcc 0 s,
      (r, θ) ∈ polarDomain I p e₁ e₂ := by
    intro s hs r hr
    obtain ⟨γ, U, hγ, hU⟩ := exists_isGeodesicFrom_of_smul_mem (I := I) (t := s)
      (v := show E from polarDir I e₁ e₂ θ) hs
    have hU' := isPreconnected_iff_ordConnected.1 hγ.isPreconnected
    exact (expMap_smul hγ (hU'.uIcc_subset hγ.zero_mem (hU hr))).1
  rcases le_total 0 r with h | h
  · exact star r₂ hr₂ r (by rw [uIcc_of_le (h.trans hr.2)]; exact ⟨h, hr.2⟩)
  · exact star r₁ hr₁ r (by rw [uIcc_of_ge (hr.1.trans h)]; exact ⟨hr.1, h⟩)

lemma isOpen_polarDomain_slice (θ : ℝ) : IsOpen {r : ℝ | (r, θ) ∈ polarDomain I p e₁ e₂} :=
  isOpen_polarDomain.preimage (continuous_id.prodMk continuous_const)

/-- **The polar map is a variation through geodesics.** -/
theorem isGeodesicVariation_polarMap :
    IsGeodesicVariation (I := I) (polarMap I p e₁ e₂) (polarDomain I p e₁ e₂) where
  isOpen := isOpen_polarDomain
  contMDiffOn := contMDiffOn_polarMap
  isGeodesic := fun q hq ↦ by
    obtain ⟨γ, U, hγ, hqU, heq, -⟩ := exists_polarMap_geodesic hq
    have hev : (fun r ↦ polarMap I p e₁ e₂ (r, q.2)) =ᶠ[𝓝 q.1] γ := by
      filter_upwards [hγ.isOpen.mem_nhds hqU] with r hr using heq hr
    exact (hγ.isGeodesicOn.of_eventuallyEq hγ.isOpen hqU hev).2

/-- **C6.2 (radial unit speed)**: if `v_θ` is a unit vector, `|∂_r F| = 1`. -/
theorem norm_pR_polarMap {q : ℝ × ℝ} (hq : q ∈ polarDomain I p e₁ e₂)
    (hunit : ‖polarDir I e₁ e₂ q.2‖ = 1) : ‖pR I (polarMap I p e₁ e₂) q‖ = 1 := by
  obtain ⟨γ, U, hγ, hqU, heq, -⟩ := exists_polarMap_geodesic hq
  have hev : (fun r ↦ polarMap I p e₁ e₂ (r, q.2)) =ᶠ[𝓝 q.1] γ := by
    filter_upwards [hγ.isOpen.mem_nhds hqU] with r hr using heq hr
  rw [pR, norm_velocity_congr hev, IsParallelAlongOn.norm_eq hγ.isOpen hγ.isPreconnected
    hγ.isGeodesicOn hγ.zero_mem hqU]
  rw [← hunit]
  exact congrArg₂ (fun (x : M) (v : E) ↦ ‖(show TangentSpace I x from v)‖) hγ.apply_zero
    hγ.velocity_zero

/-- `∂_θ F (0, θ) = 0`: the polar map is constant `= p` at `r = 0`. -/
lemma pθ_polarMap_zero (θ : ℝ) : pθ I (polarMap I p e₁ e₂) (0, θ) = 0 := by
  have hc : (fun s ↦ polarMap I p e₁ e₂ ((0, θ).1, s)) = fun _ ↦ p :=
    funext fun s ↦ polarMap_zero s
  have h : (velocity I (fun s ↦ polarMap I p e₁ e₂ ((0, θ).1, s)) θ : E) =
      velocity I (fun _ : ℝ ↦ p) θ := velocity_congr (Filter.EventuallyEq.of_eq hc)
  have h0 : (velocity I (fun _ : ℝ ↦ p) θ : E) = 0 := by
    show mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ ↦ p) θ 1 = 0
    rw [mfderiv_const]
    rfl
  exact h.trans h0

/-- `∂_r F (0, θ) = v_θ`. -/
lemma pR_polarMap_zero (θ : ℝ) :
    (pR I (polarMap I p e₁ e₂) (0, θ) : E) = polarDir I e₁ e₂ θ := by
  obtain ⟨γ, U, hγ, hqU, heq, -⟩ := exists_polarMap_geodesic (zero_mem_polarDomain (I := I)
    (e₁ := e₁) (e₂ := e₂) θ)
  have hev : (fun r ↦ polarMap I p e₁ e₂ (r, ((0 : ℝ), θ).2)) =ᶠ[𝓝 ((0 : ℝ), θ).1] γ := by
    filter_upwards [hγ.isOpen.mem_nhds hqU] with r hr using heq hr
  exact (velocity_congr hev).trans hγ.velocity_zero

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma hasDerivAt_polarDir (θ : ℝ) :
    HasDerivAt (fun θ ↦ (polarDir I e₁ e₂ θ : E)) (polarDir' I e₁ e₂ θ : E) θ := by
  have h : (fun θ ↦ (polarDir I e₁ e₂ θ : E)) =
      fun θ ↦ Real.cos θ • (show E from e₁) + Real.sin θ • (show E from e₂) := rfl
  rw [h]
  exact ((Real.hasDerivAt_cos θ).smul_const _).add ((Real.hasDerivAt_sin θ).smul_const _)

/-- `D_θ ∂_r F (0, θ) = ∂_θ v_θ`: at `r = 0` the field `∂_r F = v_θ` lies in the fixed tangent space
`T_p M`. -/
lemma covθ_pR_polarMap_zero (θ₀ : ℝ) :
    (covθ I (polarMap I p e₁ e₂) (pR I (polarMap I p e₁ e₂)) (0, θ₀) : E) =
      polarDir' I e₁ e₂ θ₀ := by
  set F := polarMap I p e₁ e₂
  have hF0 : ∀ θ, F (0, θ) = p := fun θ ↦ polarMap_zero θ
  set N := polarDomain I p e₁ e₂ ∩ F ⁻¹' (chartAt H p).source
  have hS : SmoothInChart I F p N :=
    smoothInChart_of_contMDiffOn isOpen_polarDomain contMDiffOn_polarMap p
  have hmem : ∀ θ : ℝ, ((0 : ℝ), θ) ∈ N := fun θ ↦
    ⟨zero_mem_polarDomain θ, by rw [mem_preimage, hF0]; exact mem_chart_source H p⟩
  set q₀ : ℝ × ℝ := (0, θ₀)
  set X : ℝ × ℝ → E := fun q ↦ extChartAt I p (F q)
  set w : ℝ × ℝ → E := fun q ↦ fderiv ℝ X q (1, 0)
  have hXd : DifferentiableAt ℝ X q₀ := hS.differentiableAt (hmem θ₀)
  have hwd : DifferentiableAt ℝ w q₀ :=
    ((hS.contDiffOn_fderiv_apply (1, 0)).differentiableOn (by simp) q₀
      (hmem θ₀)).differentiableAt (hS.isOpen.mem_nhds (hmem θ₀))
  -- the trivialization at `p` is the identity at the points `F (0, θ) = p`
  have hid : ∀ θ (u : E), (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ
      (F (0, θ)) u = u := fun θ u ↦
    (congrArg₂ (fun (b : M) (v : E) ↦
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ b v)
      (hF0 θ) rfl).trans (trivializationAt_self_apply p u)
  -- `X` is constant along `r = 0`
  have hX0 : fderiv ℝ X q₀ (0, 1) = 0 := by
    have hconst : (fun s ↦ X (q₀.1, s)) = fun _ ↦ extChartAt I p p :=
      funext fun s ↦ by simp only [X, q₀]; rw [hF0]
    have h := hasDerivAt_line_snd hXd
    rw [hconst] at h
    exact h.unique (hasDerivAt_const _ _)
  -- `w = v_θ` along `r = 0`
  have hw0 : (fun s ↦ w (q₀.1, s)) = fun s ↦ (polarDir I e₁ e₂ s : E) := by
    funext s
    exact (hS.pR_coord (hmem s)).symm.trans ((hid s (pR I F (0, s))).trans (pR_polarMap_zero s))
  have hwθ : fderiv ℝ w q₀ (0, 1) = polarDir' I e₁ e₂ θ₀ := by
    have h := hasDerivAt_line_snd hwd
    rw [hw0] at h
    exact h.unique (hasDerivAt_polarDir θ₀)
  have h := (hid θ₀ (covθ I F (pR I F) q₀)).symm.trans
    (hS.covθ_coord (fun q hq ↦ hS.pR_coord hq) (hmem θ₀) hwd).2
  rw [h]
  show fderiv ℝ w q₀ (0, 1) + christoffelL I p (X q₀) (fderiv ℝ X q₀ (0, 1)) (w q₀) = _
  rw [hX0, map_zero, zero_apply, add_zero, hwθ]

end PolarBasic

section Gauss

variable {p : M} {e₁ e₂ : TangentSpace I p}

/-- `⟨∂_r F, D_θ ∂_r F⟩ = 0` on the polar domain: `|∂_r F| = 1` does not depend on `θ`. -/
lemma inner_pR_covθ_pR_polarMap (hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1) {q : ℝ × ℝ}
    (hq : q ∈ polarDomain I p e₁ e₂) :
    inner ℝ (pR I (polarMap I p e₁ e₂) q)
      (covθ I (polarMap I p e₁ e₂) (pR I (polarMap I p e₁ e₂)) q) = 0 := by
  have hV := isGeodesicVariation_polarMap (I := I) (p := p) (e₁ := e₁) (e₂ := e₂)
  have h2 := hV.hasDerivAt_inner_pR_pR hq
  have hopen : IsOpen {θ' : ℝ | (q.1, θ') ∈ polarDomain I p e₁ e₂} :=
    isOpen_polarDomain.preimage (continuous_const.prodMk continuous_id)
  have hconst : (fun _ : ℝ ↦ (1 : ℝ)) =ᶠ[𝓝 q.2] fun θ' ↦ inner ℝ
      (pR I (polarMap I p e₁ e₂) (q.1, θ')) (pR I (polarMap I p e₁ e₂) (q.1, θ')) := by
    filter_upwards [hopen.mem_nhds hq] with θ' hθ'
    rw [real_inner_self_eq_norm_sq, norm_pR_polarMap hθ' (hunit θ'), one_pow]
  have h3 := (h2.congr_of_eventuallyEq hconst).unique (hasDerivAt_const q.2 (1 : ℝ))
  linarith

/-- **C6.3 (Gauss lemma)**: `⟨∂_r F, ∂_θ F⟩ = 0` for geodesic polar coordinates built from unit
vectors `v_θ`. -/
theorem inner_pR_pθ_polarMap (hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1) {q : ℝ × ℝ}
    (hq : q ∈ polarDomain I p e₁ e₂) :
    inner ℝ (pR I (polarMap I p e₁ e₂) q) (pθ I (polarMap I p e₁ e₂) q) = 0 := by
  have hV := isGeodesicVariation_polarMap (I := I) (p := p) (e₁ := e₁) (e₂ := e₂)
  set F := polarMap I p e₁ e₂
  set U := {r : ℝ | (r, q.2) ∈ polarDomain I p e₁ e₂}
  set f : ℝ → ℝ := fun r ↦ inner ℝ (pR I F (r, q.2)) (pθ I F (r, q.2))
  have hderiv : ∀ r ∈ U, HasDerivAt f 0 r := by
    intro r hr
    have h1 := hV.hasDerivAt_inner_pR_pθ (q := (r, q.2)) hr
    rw [inner_pR_covθ_pR_polarMap hunit hr] at h1
    exact h1
  have hconst := (isOpen_polarDomain_slice q.2).is_const_of_deriv_eq_zero
    (isPreconnected_polarDomain_slice q.2)
    (fun r hr ↦ (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hderiv r hr).deriv) (show q.1 ∈ U from hq)
    (show (0 : ℝ) ∈ U from zero_mem_polarDomain q.2)
  have hf0 : f 0 = 0 := by
    simp only [f]
    rw [pθ_polarMap_zero, inner_zero_right]
  exact hconst.trans hf0

/-- **C6.3 (form of the metric)**: from `|∂_r F| = 1` and the Gauss lemma, the metric in geodesic
polar coordinates has the form `ds² = dr² + f² dθ²` with `f = |∂_θ F|`: for every differentiable
curve `t ↦ (r(t), θ(t))` in the polar domain, the image curve `t ↦ F(r(t), θ(t))` has speed
`|γ'|² = r'² + |∂_θ F|² θ'²`. (In dimension two with constant curvature `K`, `f = |S_K(r)|` depends
on `r` only: `norm_pθ_polarMap`, `sec6_metric`.) -/
theorem sec6_metric_form (hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1) {ℓ : ℝ → ℝ × ℝ}
    {ℓ' : ℝ × ℝ} {t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ polarDomain I p e₁ e₂) :
    ‖velocity I (fun s ↦ polarMap I p e₁ e₂ (ℓ s)) t‖ ^ 2 =
      ℓ'.1 ^ 2 + ‖pθ I (polarMap I p e₁ e₂) (ℓ t)‖ ^ 2 * ℓ'.2 ^ 2 := by
  have hS : SmoothInChart I (polarMap I p e₁ e₂) (polarMap I p e₁ e₂ (ℓ t))
      (polarDomain I p e₁ e₂ ∩ polarMap I p e₁ e₂ ⁻¹'
        (chartAt H (polarMap I p e₁ e₂ (ℓ t))).source) :=
    smoothInChart_of_contMDiffOn isOpen_polarDomain contMDiffOn_polarMap _
  rw [hS.velocity_eq hℓ ⟨hq, mem_chart_source H _⟩, ← real_inner_self_eq_norm_sq]
  have h1 := norm_pR_polarMap hq (hunit (ℓ t).2)
  have h3 := inner_pR_pθ_polarMap hunit hq
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h3, real_inner_comm, h3]
  ring

/-- **C6.4 (first part)**: the angular variation field `J(r) = ∂_θ F(r, θ)` is a Jacobi field along
the geodesic `r ↦ F(r, θ)`. -/
theorem isJacobiFieldOn_polarMap (θ : ℝ) :
    IsJacobiFieldOn I (fun r ↦ polarMap I p e₁ e₂ (r, θ))
      (fun r ↦ pθ I (polarMap I p e₁ e₂) (r, θ)) {r | (r, θ) ∈ polarDomain I p e₁ e₂} :=
  (isGeodesicVariation_polarMap (I := I)).isJacobiFieldOn θ

end Gauss

section ConstCurv

variable {p : M} {e₁ e₂ : TangentSpace I p}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- For an orthonormal pair `e₁, e₂`, the vectors `v_θ` and `∂_θ v_θ` are orthonormal. -/
lemma polarDir_orthonormal (he : Orthonormal ℝ ![e₁, e₂]) (θ : ℝ) :
    ‖polarDir I e₁ e₂ θ‖ = 1 ∧ ‖polarDir' I e₁ e₂ θ‖ = 1 ∧
      inner ℝ (polarDir' I e₁ e₂ θ) (polarDir I e₁ e₂ θ) = (0 : ℝ) := by
  have h1 : ‖e₁‖ = 1 := by simpa using he.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using he.1 1
  have h12 : inner ℝ e₁ e₂ = (0 : ℝ) := by simpa using he.2 (show (0 : Fin 2) ≠ 1 by decide)
  have hn : ∀ v : TangentSpace I p, ‖v‖ ^ 2 = 1 → ‖v‖ = 1 := fun v hv ↦ by
    have := norm_nonneg v
    nlinarith
  refine ⟨hn _ ?_, hn _ ?_, ?_⟩
  · rw [← real_inner_self_eq_norm_sq]
    simp only [polarDir, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm e₁ e₂, h12]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  · rw [← real_inner_self_eq_norm_sq]
    simp only [polarDir', inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm e₁ e₂, h12]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  · simp only [polarDir, polarDir', inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm e₁ e₂, h12]
    ring

set_option maxHeartbeats 400000 in
/-- **C4.4 (geometric correspondence, second half) and C6.4.** In a two-dimensional Riemannian
manifold of constant sectional curvature `K`, fix `θ` and an open interval `(a, b) ∋ 0` of radii on
which the geodesic `γ(r) = F(r, θ)` is defined, and let `ν` be the parallel field along `γ` with
`ν(0) = ∂_θ v_θ`. Then `ν` is a unit normal field along `γ`; the variation field
`J(r) = ∂_θ F(r, θ)` of the variation through the geodesics from `p` with initial directions
`v_θ` is a Jacobi field with `J ⟂ γ̇`, `J(0) = 0` and `D_r J(0) = ν(0)`; and `J = S_K ν`,
`|J| = |S_K|`. Moreover every Jacobi field along `γ` with these properties is this variation
field. -/
theorem sec6_jacobi_eq_S (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) (θ : ℝ) {a b : ℝ}
    (hab : Ioo a b ⊆ {r | (r, θ) ∈ polarDomain I p e₁ e₂}) (h0 : (0 : ℝ) ∈ Ioo a b) :
    ∃ ν : (r : ℝ) → TangentSpace I (polarMap I p e₁ e₂ (r, θ)),
      IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M)
        (fun r ↦ polarMap I p e₁ e₂ (r, θ)) ν (Ioo a b) ∧
      (ν 0 : E) = polarDir' I e₁ e₂ θ ∧
      (∀ r ∈ Ioo a b, ‖ν r‖ = 1 ∧ inner ℝ (ν r) (pR I (polarMap I p e₁ e₂) (r, θ)) = (0 : ℝ)) ∧
      IsJacobiFieldOn I (fun r ↦ polarMap I p e₁ e₂ (r, θ))
        (fun r ↦ pθ I (polarMap I p e₁ e₂) (r, θ)) (Ioo a b) ∧
      (∀ r ∈ Ioo a b, inner ℝ (pθ I (polarMap I p e₁ e₂) (r, θ))
        (pR I (polarMap I p e₁ e₂) (r, θ)) = (0 : ℝ)) ∧
      pθ I (polarMap I p e₁ e₂) (0, θ) = 0 ∧
      covAlong (CovariantDerivative.leviCivitaConnection I M) (fun r ↦ polarMap I p e₁ e₂ (r, θ))
        (fun r ↦ pθ I (polarMap I p e₁ e₂) (r, θ)) 0 = ν 0 ∧
      (∀ r ∈ Ioo a b, pθ I (polarMap I p e₁ e₂) (r, θ) = S K r • ν r ∧
        ‖pθ I (polarMap I p e₁ e₂) (r, θ)‖ = |S K r|) ∧
      ∀ J : (r : ℝ) → TangentSpace I (polarMap I p e₁ e₂ (r, θ)),
        IsJacobiFieldOn I (fun r ↦ polarMap I p e₁ e₂ (r, θ)) J (Ioo a b) →
        (∀ r ∈ Ioo a b, inner ℝ (J r) (pR I (polarMap I p e₁ e₂) (r, θ)) = (0 : ℝ)) →
        J 0 = 0 →
        covAlong (CovariantDerivative.leviCivitaConnection I M)
          (fun r ↦ polarMap I p e₁ e₂ (r, θ)) J 0 = ν 0 →
        ∀ r ∈ Ioo a b, J r = pθ I (polarMap I p e₁ e₂) (r, θ) := by
  have hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1 := fun θ ↦ (polarDir_orthonormal he θ).1
  have hV := isGeodesicVariation_polarMap (I := I) (p := p) (e₁ := e₁) (e₂ := e₂)
  have hgeo : IsGeodesicOn I (fun r ↦ polarMap I p e₁ e₂ (r, θ)) (Ioo a b) :=
    (hV.isGeodesicOn θ).mono hab
  have hγs : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun r ↦ polarMap I p e₁ e₂ (r, θ)) (Ioo a b) :=
    ((contMDiffOn_polarMap (I := I) (p := p) (e₁ := e₁) (e₂ := e₂)).comp
      ((contDiff_id.prodMk contDiff_const : ContDiff ℝ ∞ (fun s : ℝ ↦ (s, θ))).contMDiff.contMDiffOn)
      (fun r hr ↦ hab hr)).of_le (by simp)
  have hγ0 : polarMap I p e₁ e₂ (0, θ) = p := polarMap_zero θ
  obtain ⟨ν, hν, hν0⟩ := exists_isParallelAlongOn isOpen_Ioo isPreconnected_Ioo hγs h0
    (show TangentSpace I (polarMap I p e₁ e₂ (0, θ)) from polarDir' I e₁ e₂ θ)
  have hv0 : (pR I (polarMap I p e₁ e₂) (0, θ) : E) = polarDir I e₁ e₂ θ := pR_polarMap_zero θ
  have hunitγ : ∀ r ∈ Ioo a b, ‖pR I (polarMap I p e₁ e₂) (r, θ)‖ = 1 := fun r hr ↦
    norm_pR_polarMap (hab hr) (hunit θ)
  have hv0' : velocity I (fun r ↦ polarMap I p e₁ e₂ (r, θ)) 0 =
      (show TangentSpace I (polarMap I p e₁ e₂ (0, θ)) from polarDir I e₁ e₂ θ) := hv0
  have hν1 : ∀ r ∈ Ioo a b, ‖ν r‖ = 1 := by
    intro r hr
    rw [IsParallelAlongOn.norm_eq isOpen_Ioo isPreconnected_Ioo hν h0 hr, hν0]
    exact (norm_transport (I := I) hγ0 (polarDir' I e₁ e₂ θ)).trans
      (polarDir_orthonormal he θ).2.1
  have hνγ : ∀ r ∈ Ioo a b, inner ℝ (ν r) (pR I (polarMap I p e₁ e₂) (r, θ)) = (0 : ℝ) := by
    intro r hr
    show inner ℝ (ν r) (velocity I (fun r ↦ polarMap I p e₁ e₂ (r, θ)) r) = 0
    rw [IsParallelAlongOn.inner_eq isOpen_Ioo isPreconnected_Ioo hν hgeo h0 hr, hν0, hv0']
    exact (inner_transport (I := I) hγ0 (polarDir' I e₁ e₂ θ) (polarDir I e₁ e₂ θ)).trans
      (polarDir_orthonormal he θ).2.2
  have hJ : IsJacobiFieldOn I (fun r ↦ polarMap I p e₁ e₂ (r, θ))
      (fun r ↦ pθ I (polarMap I p e₁ e₂) (r, θ)) (Ioo a b) := fun r hr ↦
    isJacobiFieldOn_polarMap θ r (hab hr)
  have hJγ : ∀ r ∈ Ioo a b, inner ℝ (pθ I (polarMap I p e₁ e₂) (r, θ))
      (pR I (polarMap I p e₁ e₂) (r, θ)) = (0 : ℝ) := fun r hr ↦ by
    rw [real_inner_comm]
    exact inner_pR_pθ_polarMap hunit (hab hr)
  have hDJ0 : covAlong (CovariantDerivative.leviCivitaConnection I M)
      (fun r ↦ polarMap I p e₁ e₂ (r, θ)) (fun r ↦ pθ I (polarMap I p e₁ e₂) (r, θ)) 0 = ν 0 := by
    have hS : SmoothInChart I (polarMap I p e₁ e₂) (polarMap I p e₁ e₂ (0, θ))
        (polarDomain I p e₁ e₂ ∩ polarMap I p e₁ e₂ ⁻¹'
          (chartAt H (polarMap I p e₁ e₂ (0, θ))).source) :=
      smoothInChart_of_contMDiffOn isOpen_polarDomain contMDiffOn_polarMap _
    have hsym := hS.covR_pθ ⟨zero_mem_polarDomain θ, mem_chart_source H _⟩
    exact hsym.trans ((covθ_pR_polarMap_zero θ).trans hν0.symm)
  have hmain := sec4_jacobi_eq_S hdim hK h0 hunitγ hν hν1 hνγ hJ hJγ (pθ_polarMap_zero θ) hDJ0
  refine ⟨ν, hν, hν0, fun r hr ↦ ⟨hν1 r hr, hνγ r hr⟩, hJ, hJγ, pθ_polarMap_zero θ, hDJ0,
    hmain, fun J hJ' hJγ' hJ0' hDJ0' r hr ↦ ?_⟩
  rw [(sec4_jacobi_eq_S hdim hK h0 hunitγ hν hν1 hνγ hJ' hJγ' hJ0' hDJ0' r hr).1,
    (hmain r hr).1]

/-- An open interval `(a, b)` of radii containing `0` and a given radius `r` of the polar domain,
on which the radial geodesic is defined. -/
lemma exists_Ioo_polarDomain {q : ℝ × ℝ} (hq : q ∈ polarDomain I p e₁ e₂) :
    ∃ a b : ℝ, Ioo a b ⊆ {r | (r, q.2) ∈ polarDomain I p e₁ e₂} ∧ (0 : ℝ) ∈ Ioo a b ∧
      q.1 ∈ Ioo a b := by
  have hU := isOpen_polarDomain_slice (I := I) (p := p) (e₁ := e₁) (e₂ := e₂) q.2
  have hU' := isPreconnected_iff_ordConnected.1
    (isPreconnected_polarDomain_slice (I := I) (p := p) (e₁ := e₁) (e₂ := e₂) q.2)
  obtain ⟨ε₀, hε₀, h₀⟩ := Metric.isOpen_iff.1 hU 0 (zero_mem_polarDomain q.2)
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 hU q.1 hq
  have hmem₀ : ∀ x, |x| < ε₀ → x ∈ {r | (r, q.2) ∈ polarDomain I p e₁ e₂} := fun x hx ↦
    h₀ (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero])
  have hmem₁ : ∀ x, |x - q.1| < ε₁ → x ∈ {r | (r, q.2) ∈ polarDomain I p e₁ e₂} := fun x hx ↦
    h₁ (by rwa [Metric.mem_ball, Real.dist_eq])
  have ha : min (-(ε₀ / 2)) (q.1 - ε₁ / 2) ∈ {r | (r, q.2) ∈ polarDomain I p e₁ e₂} := by
    rcases min_choice (-(ε₀ / 2)) (q.1 - ε₁ / 2) with h | h <;> rw [h]
    · exact hmem₀ _ (by rw [abs_neg, abs_of_pos (half_pos hε₀)]; linarith)
    · exact hmem₁ _ (by rw [show q.1 - ε₁ / 2 - q.1 = -(ε₁ / 2) by ring, abs_neg,
        abs_of_pos (half_pos hε₁)]; linarith)
  have hb : max (ε₀ / 2) (q.1 + ε₁ / 2) ∈ {r | (r, q.2) ∈ polarDomain I p e₁ e₂} := by
    rcases max_choice (ε₀ / 2) (q.1 + ε₁ / 2) with h | h <;> rw [h]
    · exact hmem₀ _ (by rw [abs_of_pos (half_pos hε₀)]; linarith)
    · exact hmem₁ _ (by rw [show q.1 + ε₁ / 2 - q.1 = ε₁ / 2 by ring,
        abs_of_pos (half_pos hε₁)]; linarith)
  refine ⟨min (-(ε₀ / 2)) (q.1 - ε₁ / 2), max (ε₀ / 2) (q.1 + ε₁ / 2),
    fun r hr ↦ hU'.out ha hb (Ioo_subset_Icc_self hr), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

/-- **C6.4 (length of the angular variation field)**: in a two-dimensional Riemannian manifold
of constant sectional curvature `K`, `|∂_θ F(r, θ)| = |S_K(r)|` on the whole polar domain. -/
theorem norm_pθ_polarMap (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) {q : ℝ × ℝ}
    (hq : q ∈ polarDomain I p e₁ e₂) : ‖pθ I (polarMap I p e₁ e₂) q‖ = |S K q.1| := by
  obtain ⟨a, b, hab, h0, hq1⟩ := exists_Ioo_polarDomain hq
  obtain ⟨ν, -, -, -, -, -, -, -, hmain, -⟩ := sec6_jacobi_eq_S hdim hK he q.2 hab h0
  exact (hmain q.1 hq1).2

/-- **C6.4, in the form `|J(r)| = S_K(r)`** of the manuscript: for radii `r ≥ 0`, and
`r ≤ π / √K` if `K > 0` (where `S_K(r) ≥ 0`). -/
theorem norm_pθ_polarMap_eq_S (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) {q : ℝ × ℝ}
    (hq : q ∈ polarDomain I p e₁ e₂) (hr : 0 ≤ q.1) (hrK : 0 < K → q.1 ≤ Real.pi / √K) :
    ‖pθ I (polarMap I p e₁ e₂) q‖ = S K q.1 := by
  rw [norm_pθ_polarMap hdim hK he hq, abs_of_nonneg (S_nonneg hr hrK)]

/-- **C6.5 (the metric in geodesic polar coordinates)**: `ds² = dr² + S_K(r)² dθ²`. For every
differentiable curve `t ↦ (r(t), θ(t))` in the polar domain, the image curve
`t ↦ F(r(t), θ(t))` has speed `|γ'|² = r'² + S_K(r)² θ'²`. -/
theorem sec6_metric (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) {ℓ : ℝ → ℝ × ℝ}
    {ℓ' : ℝ × ℝ} {t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ polarDomain I p e₁ e₂) :
    ‖velocity I (fun s ↦ polarMap I p e₁ e₂ (ℓ s)) t‖ ^ 2 =
      ℓ'.1 ^ 2 + S K (ℓ t).1 ^ 2 * ℓ'.2 ^ 2 := by
  rw [sec6_metric_form (fun θ ↦ (polarDir_orthonormal he θ).1) hℓ hq,
    norm_pθ_polarMap hdim hK he hq, sq_abs]

/-- **C6.6 (circumference of geodesic circles)**: in a two-dimensional Riemannian manifold of
constant sectional curvature `K`, if the geodesic circle `θ ↦ F(r, θ)` of radius `r` is defined
(`(r, θ)` lies in the polar domain for every `θ`), its length over `0 ≤ θ ≤ 2π` is
`2π |S_K(r)|`. -/
theorem sec6_circumference (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) {r : ℝ}
    (hr : ∀ θ, (r, θ) ∈ polarDomain I p e₁ e₂) :
    Manifold.pathELength I (fun θ ↦ polarMap I p e₁ e₂ (r, θ)) 0 (2 * Real.pi) =
      ENNReal.ofReal (2 * Real.pi * |S K r|) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have h : ∀ θ, ‖mfderiv 𝓘(ℝ, ℝ) I (fun θ ↦ polarMap I p e₁ e₂ (r, θ)) θ 1‖ₑ =
      ENNReal.ofReal |S K r| := by
    intro θ
    rw [← ofReal_norm]
    exact congrArg ENNReal.ofReal (norm_pθ_polarMap hdim hK he (hr θ))
  simp_rw [h]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm,
    ← ENNReal.ofReal_mul (by positivity)]

/-- **C6.6, in the form `2π S_K(r)`** of the manuscript: for radii `r ≥ 0`, and `r ≤ π / √K` if
`K > 0` (where `S_K(r) ≥ 0`). -/
theorem sec6_circumference_eq_S (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) {r : ℝ}
    (hr : ∀ θ, (r, θ) ∈ polarDomain I p e₁ e₂) (hr0 : 0 ≤ r) (hrK : 0 < K → r ≤ Real.pi / √K) :
    Manifold.pathELength I (fun θ ↦ polarMap I p e₁ e₂ (r, θ)) 0 (2 * Real.pi) =
      ENNReal.ofReal (2 * Real.pi * S K r) := by
  rw [sec6_circumference hdim hK he hr, abs_of_nonneg (S_nonneg hr0 hrK)]

end ConstCurv

section PlanePolar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma orthonormal_two_facts {e₁ e₂ : V} (he : Orthonormal ℝ ![e₁, e₂]) :
    ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = (0 : ℝ) :=
  ⟨by simpa using he.1 0, by simpa using he.1 1,
    by simpa using he.2 (show (0 : Fin 2) ≠ 1 by decide)⟩

lemma norm_cos_smul_add_sin_smul {e₁ e₂ : V} (he : Orthonormal ℝ ![e₁, e₂]) (θ : ℝ) :
    ‖Real.cos θ • e₁ + Real.sin θ • e₂‖ = 1 := by
  obtain ⟨h1, h2, h12⟩ := orthonormal_two_facts he
  have hsq : ‖Real.cos θ • e₁ + Real.sin θ • e₂‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm e₁ e₂, h12]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have := norm_nonneg (Real.cos θ • e₁ + Real.sin θ • e₂)
  nlinarith

/-- **Polar decomposition** in a Euclidean plane with an orthonormal basis `e₁, e₂`. -/
lemma exists_eq_norm_smul_cos_add_sin (hdim : Module.finrank ℝ V = 2) {e₁ e₂ : V}
    (he : Orthonormal ℝ ![e₁, e₂]) (v : V) :
    ∃ θ : ℝ, v = ‖v‖ • (Real.cos θ • e₁ + Real.sin θ • e₂) := by
  obtain ⟨h1, h2, h12⟩ := orthonormal_two_facts he
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![e₁, e₂]) := by
    rw [he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [hdim])]
  set b := OrthonormalBasis.mk he hsp
  have hb : ⇑b = ![e₁, e₂] := OrthonormalBasis.coe_mk he hsp
  have hv : v = inner ℝ e₁ v • e₁ + inner ℝ e₂ v • e₂ := by
    have := b.sum_repr' v
    rw [Fin.sum_univ_two, hb] at this
    simpa using this.symm
  set a : ℝ := inner ℝ e₁ v
  set c : ℝ := inner ℝ e₂ v
  have hnv : ‖v‖ ^ 2 = a ^ 2 + c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [hv]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm e₁ e₂, h12]
    ring
  set z : ℂ := ⟨a, c⟩
  have hz : ‖z‖ = ‖v‖ := by
    have h1' : ‖z‖ ^ 2 = a ^ 2 + c ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      ring
    have := norm_nonneg z
    have := norm_nonneg v
    nlinarith
  by_cases hv0 : v = 0
  · exact ⟨0, by rw [hv0, norm_zero, zero_smul]⟩
  have hz0 : z ≠ 0 := by
    intro h
    apply hv0
    rw [← norm_eq_zero, ← hz, h, norm_zero]
  refine ⟨Complex.arg z, ?_⟩
  rw [Complex.cos_arg hz0, Complex.sin_arg, hz, smul_add, smul_smul, smul_smul]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  conv_lhs => rw [hv]
  congr 2
  · show a = ‖v‖ * (a / ‖v‖)
    field_simp
  · show c = ‖v‖ * (c / ‖v‖)
    field_simp

/-- **Uniqueness of polar coordinates.** -/
lemma smul_cos_add_sin_inj {e₁ e₂ : V} (he : Orthonormal ℝ ![e₁, e₂]) {r r' θ θ' : ℝ}
    (hr : 0 < r) (hr' : 0 < r') :
    r • (Real.cos θ • e₁ + Real.sin θ • e₂) = r' • (Real.cos θ' • e₁ + Real.sin θ' • e₂) ↔
      r = r' ∧ ∃ k : ℤ, θ' = θ + 2 * Real.pi * k := by
  obtain ⟨h1, h2, h12⟩ := orthonormal_two_facts he
  constructor
  · intro h
    have hrr : r = r' := by
      have := congrArg norm h
      rwa [norm_smul, norm_smul, norm_cos_smul_add_sin_smul he, norm_cos_smul_add_sin_smul he,
        Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le, mul_one, mul_one] at this
    subst hrr
    have hu := smul_right_injective V hr.ne' h
    have hc : Real.cos θ = Real.cos θ' := by
      have := congrArg (fun w ↦ inner ℝ e₁ w) hu
      simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, h1, h12] at this
      simpa using this
    have hs : Real.sin θ = Real.sin θ' := by
      have := congrArg (fun w ↦ inner ℝ e₂ w) hu
      simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, h2,
        real_inner_comm e₁ e₂, h12] at this
      simpa using this
    refine ⟨rfl, ?_⟩
    have hexp : Complex.exp (θ' * Complex.I) = Complex.exp (θ * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  · rintro ⟨rfl, k, rfl⟩
    rw [show θ + 2 * Real.pi * k = θ + k * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi,
      Real.sin_add_int_mul_two_pi]

end PlanePolar

section NormalNbhd

/-- `exp_p`, read in the chart at `p`, is smooth wherever `exp_p` stays in that chart. -/
lemma contDiffAt_extChartAt_expMap {p : M} {v : E} (hv : v ∈ expDomain I p)
    (hsrc : expMap I p v ∈ (chartAt H p).source) :
    ContDiffAt ℝ ∞ (fun w : E ↦ extChartAt I p (expMap I p w)) v :=
  contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_extChartAt' hsrc).comp v (contMDiffAt_expMap hv))

/-- **The differential of `exp_p` at `0` is the identity** (read in the chart at `p`). -/
lemma hasFDerivAt_extChartAt_expMap_zero (p : M) :
    HasFDerivAt (fun v : E ↦ extChartAt I p (expMap I p v)) (ContinuousLinearMap.id ℝ E) 0 := by
  have hG : ContDiffAt ℝ ∞ (fun v : E ↦ extChartAt I p (expMap I p v)) 0 :=
    contDiffAt_extChartAt_expMap (zero_mem_expDomain p)
      (by rw [expMap_zero]; exact mem_chart_source H p)
  have hd := (hG.differentiableAt (by simp)).hasFDerivAt
  convert hd using 1
  refine ContinuousLinearMap.ext fun w ↦ ?_
  obtain ⟨ε, hε, γ, hγ0, hγv, -, hγ⟩ := exists_geodesic (I := I) p w
  have hg : IsGeodesicFrom I p w γ (Ioo (-ε) ε) :=
    ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, hε⟩, hγ, hγ0, hγv⟩
  have hev : (fun t : ℝ ↦ extChartAt I p (expMap I p (t • w))) =ᶠ[𝓝 0] extChartAt I p ∘ γ := by
    filter_upwards [hg.expMap_smul_eventuallyEq hg.zero_mem] with t ht
    simp only [Function.comp_apply]
    rw [ht]
  have hline : HasDerivAt (fun t : ℝ ↦ t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hcomp := hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hderiv : deriv (extChartAt I p ∘ γ) 0 = w := congrArg Prod.snd hg.chartData_zero
  rw [ContinuousLinearMap.id_apply]
  calc w = deriv (extChartAt I p ∘ γ) 0 := hderiv.symm
    _ = deriv (fun t : ℝ ↦ extChartAt I p (expMap I p (t • w))) 0 := hev.deriv_eq.symm
    _ = _ := hcomp.deriv

variable (I) in
/-- The ball `B_ε = {v ∈ T_p M | ‖v‖ < ε}` for the Riemannian norm at `p`, as a subset of the
model space `E`. -/
def tangentBall (p : M) (ε : ℝ) : Set E := {v | ‖(show TangentSpace I p from v)‖ < ε}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma isOpen_tangentBall (p : M) (ε : ℝ) : IsOpen (tangentBall I p ε) := by
  have h : IsOpen (Metric.ball (0 : TangentSpace I p) ε) := Metric.isOpen_ball
  have heq : (Metric.ball (0 : TangentSpace I p) ε : Set (TangentSpace I p)) =
      tangentBall I p ε := by
    ext v
    exact mem_ball_zero_iff
  rw [heq] at h
  exact h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma zero_mem_tangentBall (p : M) {ε : ℝ} (hε : 0 < ε) : (0 : E) ∈ tangentBall I p ε := by
  show ‖(0 : TangentSpace I p)‖ < ε
  rw [norm_zero]
  exact hε

/-- **Normal neighbourhoods.** There is `ε₀ > 0` such that for every `0 < ε ≤ ε₀`, `exp_p` maps the
ball `B_ε` of `T_p M` diffeomorphically onto the open neighbourhood `exp_p(B_ε)` of `p`: `B_ε` lies
in the domain of `exp_p`, `exp_p` is injective on `B_ε`, `exp_p(B_ε)` is open, and the inverse
`exp_p(B_ε) → B_ε` is smooth. (`exp_p` itself is smooth on its domain, `contMDiffOn_expMap`.) -/
theorem exists_normal_nbhd (p : M) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      tangentBall I p ε ⊆ expDomain I p ∧ InjOn (expMap I p) (tangentBall I p ε) ∧
      IsOpen (expMap I p '' tangentBall I p ε) ∧
      ∃ L : M → E, ContMDiffOn I 𝓘(ℝ, E) ∞ L (expMap I p '' tangentBall I p ε) ∧
        ∀ v ∈ tangentBall I p ε, L (expMap I p v) = v := by
  set G : E → E := fun v ↦ extChartAt I p (expMap I p v) with hG_def
  set W : Set E := expDomain I p ∩ expMap I p ⁻¹' (chartAt H p).source with hW_def
  have hWo : IsOpen W := (contMDiffOn_expMap p).continuousOn.isOpen_inter_preimage
    (isOpen_expDomain p) (chartAt H p).open_source
  have hW0 : (0 : E) ∈ W :=
    ⟨zero_mem_expDomain p, by rw [mem_preimage, expMap_zero]; exact mem_chart_source H p⟩
  have hGW : ∀ v ∈ W, ContDiffAt ℝ ∞ G v := fun v hv ↦ contDiffAt_extChartAt_expMap hv.1 hv.2
  have hG0 : HasFDerivAt G ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasFDerivAt_extChartAt_expMap_zero p
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Φ := (hGW 0 hW0).toOpenPartialHomeomorph G hG0 hn with hΦ_def
  have hΦG : ∀ v, Φ v = G v := fun v ↦ rfl
  -- the differential of `G` is invertible near `0`
  have hD : ∀ᶠ v in 𝓝 (0 : E), fderiv ℝ G v ∈ range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) := by
    have hcont : ContinuousAt (fderiv ℝ G) 0 :=
      ((hGW 0 hW0).fderiv_right (m := 0) (by simp)).continuousAt
    refine hcont.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds ?_)
    rw [hG0.fderiv]
    exact mem_range_self _
  have hN : Φ.source ∩ W ∩ {v | fderiv ℝ G v ∈ range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)} ∈
      𝓝 (0 : E) :=
    inter_mem (inter_mem (Φ.open_source.mem_nhds
      ((hGW 0 hW0).mem_toOpenPartialHomeomorph_source hG0 hn)) (hWo.mem_nhds hW0)) hD
  obtain ⟨ε₀, hε₀, hball⟩ := (@Metric.mem_nhds_iff (TangentSpace I p) _ 0 _).1 hN
  refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
  have hBN : ∀ v ∈ tangentBall I p ε, v ∈ Φ.source ∧ v ∈ W ∧
      fderiv ℝ G v ∈ range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) := by
    intro v hv
    have h := hball (show (show TangentSpace I p from v) ∈ Metric.ball (0 : TangentSpace I p) ε₀
      by rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hv hε.2)
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hBo := isOpen_tangentBall (I := I) p ε
  have hBsrc : tangentBall I p ε ⊆ Φ.source := fun v hv ↦ (hBN v hv).1
  have hinj : InjOn (expMap I p) (tangentBall I p ε) := by
    intro v hv w hw h
    have hG : Φ v = Φ w := by rw [hΦG, hΦG]; exact congrArg (extChartAt I p) h
    exact Φ.injOn (hBsrc hv) (hBsrc hw) hG
  -- `exp_p(B_ε)` is the part of the chart domain mapped into `Φ(B_ε)`
  have himg : expMap I p '' tangentBall I p ε =
      (chartAt H p).source ∩ extChartAt I p ⁻¹' (Φ '' tangentBall I p ε) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(hBN v hv).2.1.2, v, hv, hΦG v⟩
    · rintro ⟨hx, v, hv, hvx⟩
      refine ⟨v, hv, ?_⟩
      have hsrc : expMap I p v ∈ (extChartAt I p).source := by
        rw [extChartAt_source]; exact (hBN v hv).2.1.2
      exact (extChartAt I p).injOn hsrc (by rwa [extChartAt_source]) ((hΦG v).symm.trans hvx)
  refine ⟨fun v hv ↦ (hBN v hv).2.1.1, hinj, ?_, fun x ↦ Φ.symm (extChartAt I p x), ?_, ?_⟩
  · rw [himg]
    exact isOpen_extChartAt_preimage p (Φ.isOpen_image_of_subset_source hBo hBsrc)
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨-, ⟨-, hsrc⟩, e, he⟩ := hBN v hv
    have hdiff : HasFDerivAt Φ (e : E →L[ℝ] E) (Φ.symm (Φ v)) := by
      rw [Φ.left_inv (hBsrc hv), he]
      exact ((hGW v (hBN v hv).2.1).differentiableAt (by simp)).hasFDerivAt
    have hsymm : ContDiffAt ℝ ∞ Φ.symm (Φ v) :=
      Φ.contDiffAt_symm (Φ.map_source (hBsrc hv)) hdiff
        (by rw [Φ.left_inv (hBsrc hv)]; exact hGW v (hBN v hv).2.1)
    have hx : extChartAt I p (expMap I p v) = Φ v := (hΦG v).symm
    refine ContMDiffAt.contMDiffWithinAt ?_
    have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ.symm (extChartAt I p (expMap I p v)) := by
      rw [hx]; exact hsymm.contMDiffAt
    exact h1.comp (expMap I p v) (contMDiffAt_extChartAt' hsrc)
  · intro v hv
    exact (congrArg Φ.symm (hΦG v)).symm.trans (Φ.left_inv (hBsrc hv))


end NormalNbhd

section PolarCoordinates

variable {p : M} {e₁ e₂ : TangentSpace I p}

/-- **C6.1 (geodesic polar coordinates).** Let `M` be a two-dimensional Riemannian manifold of
constant sectional curvature `K`, `p ∈ M`, `e₁, e₂` an orthonormal basis of `T_p M`, and
`F(r, θ) = exp_p(r (cos θ e₁ + sin θ e₂))`. There is `ε₀ > 0` such that for every `0 < ε ≤ ε₀`,
with `B_ε = {v ∈ T_p M | ‖v‖ < ε}` and `U = exp_p(B_ε)`:
* `U` is an open neighbourhood of `p`, and `exp_p : B_ε → U` is a diffeomorphism: `B_ε` lies in the
  domain of `exp_p`, `exp_p` is smooth and injective on `B_ε`, and has a smooth inverse on `U`;
* `F` is smooth on its domain, `F(0, θ) = p`, and for `0 < r < ε`, `F(r, θ)` is defined and lies
  in `U ∖ {p}`;
* every point of `U ∖ {p}` is `F(r, θ)` for some `0 < r < ε` and some `θ`;
* for `0 < r, r' < ε`, `F(r, θ) = F(r', θ')` if and only if `r = r'` and `θ' ∈ θ + 2πℤ`;
* for `0 < r < ε`, `∂_r F(r, θ)` and `∂_θ F(r, θ)` form a basis of the tangent space at `F(r, θ)`.
So `(r, θ)`, with `θ` taken modulo `2π`, are coordinates on the punctured neighbourhood `U ∖ {p}`
of `p`. -/
theorem sec6_polar_coordinates (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (he : Orthonormal ℝ ![e₁, e₂]) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      IsOpen (expMap I p '' tangentBall I p ε) ∧ p ∈ expMap I p '' tangentBall I p ε ∧
      tangentBall I p ε ⊆ expDomain I p ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ (expMap I p) (tangentBall I p ε) ∧
      InjOn (expMap I p) (tangentBall I p ε) ∧
      (∃ L : M → E, ContMDiffOn I 𝓘(ℝ, E) ∞ L (expMap I p '' tangentBall I p ε) ∧
        ∀ v ∈ tangentBall I p ε, L (expMap I p v) = v) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (polarMap I p e₁ e₂) (polarDomain I p e₁ e₂) ∧
      (∀ θ, polarMap I p e₁ e₂ (0, θ) = p) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ, (r, θ) ∈ polarDomain I p e₁ e₂ ∧
        polarMap I p e₁ e₂ (r, θ) ∈ expMap I p '' tangentBall I p ε ∧
        polarMap I p e₁ e₂ (r, θ) ≠ p) ∧
      (∀ x ∈ expMap I p '' tangentBall I p ε, x ≠ p →
        ∃ r ∈ Ioo 0 ε, ∃ θ, polarMap I p e₁ e₂ (r, θ) = x) ∧
      (∀ r ∈ Ioo 0 ε, ∀ r' ∈ Ioo 0 ε, ∀ θ θ' : ℝ,
        polarMap I p e₁ e₂ (r, θ) = polarMap I p e₁ e₂ (r', θ') ↔
          r = r' ∧ ∃ k : ℤ, θ' = θ + 2 * Real.pi * k) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ,
        LinearIndependent ℝ
          ![pR I (polarMap I p e₁ e₂) (r, θ), pθ I (polarMap I p e₁ e₂) (r, θ)] ∧
        Submodule.span ℝ
          (range ![pR I (polarMap I p e₁ e₂) (r, θ), pθ I (polarMap I p e₁ e₂) (r, θ)]) = ⊤) := by
  obtain ⟨ε₁, hε₁, hN⟩ := exists_normal_nbhd (I := I) p
  obtain ⟨ε₀, hε₀, hε₀₁, hε₀K⟩ : ∃ ε₀ > 0, ε₀ ≤ ε₁ ∧ (0 < K → ε₀ ≤ Real.pi / √K) := by
    by_cases hK0 : 0 < K
    · exact ⟨min ε₁ (Real.pi / √K), lt_min hε₁ (div_pos Real.pi_pos (Real.sqrt_pos.2 hK0)),
        min_le_left _ _, fun _ ↦ min_le_right _ _⟩
    · exact ⟨ε₁, hε₁, le_rfl, fun h ↦ absurd h hK0⟩
  refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
  obtain ⟨hBdom, hinj, hopen, L, hL, hLexp⟩ := hN ε ⟨hε.1, hε.2.trans hε₀₁⟩
  have hunit : ∀ θ, ‖polarDir I e₁ e₂ θ‖ = 1 := fun θ ↦ (polarDir_orthonormal he θ).1
  have h0B : (0 : E) ∈ tangentBall I p ε := zero_mem_tangentBall p hε.1
  have hnormVec : ∀ r θ, 0 ≤ r → ‖(show TangentSpace I p from (polarVec I e₁ e₂ (r, θ) : E))‖ = r := by
    intro r θ hr
    show ‖r • polarDir I e₁ e₂ θ‖ = r
    rw [norm_smul, hunit, mul_one, Real.norm_of_nonneg hr]
  have hvecB : ∀ r ∈ Ioo 0 ε, ∀ θ, polarVec I e₁ e₂ (r, θ) ∈ tangentBall I p ε := by
    intro r hr θ
    show ‖(show TangentSpace I p from (polarVec I e₁ e₂ (r, θ) : E))‖ < ε
    rw [hnormVec r θ hr.1.le]
    exact hr.2
  have hdim' : Module.finrank ℝ (TangentSpace I p) = 2 := hdim
  refine ⟨hopen, ⟨0, h0B, expMap_zero p⟩, hBdom, (contMDiffOn_expMap p).mono hBdom, hinj,
    ⟨L, hL, hLexp⟩, contMDiffOn_polarMap, polarMap_zero, ?_, ?_, ?_, ?_⟩
  · intro r hr θ
    refine ⟨hBdom (hvecB r hr θ), ⟨_, hvecB r hr θ, rfl⟩, fun hp ↦ ?_⟩
    have h0 : polarVec I e₁ e₂ (r, θ) = 0 :=
      hinj (hvecB r hr θ) h0B (hp.trans (expMap_zero p).symm)
    have h := hnormVec r θ hr.1.le
    rw [h0] at h
    have h' : ‖(0 : TangentSpace I p)‖ = r := h
    rw [norm_zero] at h'
    linarith [hr.1]
  · rintro x ⟨v, hv, rfl⟩ hxp
    have hv0 : (show TangentSpace I p from v) ≠ 0 := by
      intro h
      apply hxp
      rw [show v = 0 from h]
      exact expMap_zero p
    obtain ⟨θ, hθ⟩ := exists_eq_norm_smul_cos_add_sin hdim' he (show TangentSpace I p from v)
    refine ⟨‖(show TangentSpace I p from v)‖, ⟨norm_pos_iff.2 hv0, hv⟩, θ, ?_⟩
    show expMap I p (polarVec I e₁ e₂ _) = expMap I p v
    congr 1
    exact hθ.symm
  · intro r hr r' hr' θ θ'
    rw [← smul_cos_add_sin_inj he hr.1 hr'.1]
    constructor
    · intro h
      exact hinj (hvecB r hr θ) (hvecB r' hr' θ') h
    · intro h
      show expMap I p (polarVec I e₁ e₂ (r, θ)) = expMap I p (polarVec I e₁ e₂ (r', θ'))
      rw [show polarVec I e₁ e₂ (r, θ) = polarVec I e₁ e₂ (r', θ') from h]
  · intro r hr θ
    have hq : (r, θ) ∈ polarDomain I p e₁ e₂ := hBdom (hvecB r hr θ)
    have h1 := norm_pR_polarMap hq (hunit θ)
    have h2 := norm_pθ_polarMap hdim hK he hq
    have h3 := inner_pR_pθ_polarMap hunit hq
    have hS : 0 < S K r := by
      rcases lt_or_ge 0 K with hK0 | hK0
      · exact S_pos hK0 hr.1 (lt_of_lt_of_le hr.2 (hε.2.trans (hε₀K hK0)))
      · exact S_pos_of_nonpos hK0 hr.1
    have hR0 : pR I (polarMap I p e₁ e₂) (r, θ) ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hθ0 : pθ I (polarMap I p e₁ e₂) (r, θ) ≠ 0 := by
      intro h
      rw [h, norm_zero] at h2
      have : |S K r| = 0 := h2.symm
      rw [abs_eq_zero] at this
      linarith
    have hli : LinearIndependent ℝ
        ![pR I (polarMap I p e₁ e₂) (r, θ), pθ I (polarMap I p e₁ e₂) (r, θ)] := by
      refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
      · intro i
        fin_cases i
        · exact hR0
        · exact hθ0
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact h3
        · show inner ℝ (pθ I (polarMap I p e₁ e₂) (r, θ)) (pR I (polarMap I p e₁ e₂) (r, θ)) = 0
          rw [real_inner_comm]
          exact h3
        · exact absurd rfl hij
    refine ⟨hli, hli.span_eq_top_of_card_eq_finrank ?_⟩
    rw [Fintype.card_fin]
    exact hdim.symm

end PolarCoordinates

end PythagoreanPaper
