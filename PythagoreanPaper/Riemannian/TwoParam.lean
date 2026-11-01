import PythagoreanPaper.Riemannian.Curvature

/-!
# Two-parameter maps: covariant derivatives, symmetry and curvature

For a map `F : ℝ × ℝ → M`, `pR I F q` and `pθ I F q` are the velocities at `q = (r, θ)` of the
curves `s ↦ F (s, θ)` and `s ↦ F (r, s)` (the partial derivatives `∂_r F`, `∂_θ F`), and
`covR I F V q`, `covθ I F V q` are the covariant derivatives of a field `V` along `F` along these
curves. When `F` is smooth in a chart:

* `SmoothInChart.covAlong_coord`: the covariant derivative of a field along `F ∘ ℓ`, for a curve
  `ℓ` in the parameter plane, in coordinates (in particular `D_t (V ∘ ℓ)` depends linearly on
  `ℓ'`);
* `SmoothInChart.covR_pθ`: the **symmetry lemma** `D_r ∂_θ F = D_θ ∂_r F` (torsion-freeness);
* `SmoothInChart.covR_covθ_sub`: the **curvature identity**
  `D_r D_θ ∂_r F − D_θ D_r ∂_r F = R(∂_r F, ∂_θ F) ∂_r F`.

These are the tools for geodesic variations (manuscript §6): a variation through geodesics has a
Jacobi field as variation field.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative of a function of two real variables along the first variable. -/
lemma hasDerivAt_line_fst {g : ℝ × ℝ → G} {q : ℝ × ℝ} (hg : DifferentiableAt ℝ g q) :
    HasDerivAt (fun s ↦ g (s, q.2)) (fderiv ℝ g q (1, 0)) q.1 := by
  have hℓ : HasDerivAt (fun s : ℝ ↦ (s, q.2)) ((1 : ℝ), (0 : ℝ)) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hq : ((q.1, q.2) : ℝ × ℝ) = q := Prod.mk.eta
  exact (hq ▸ hg).hasFDerivAt.comp_hasDerivAt q.1 hℓ |>.congr_deriv (by rw [hq])

/-- The derivative of a function of two real variables along the second variable. -/
lemma hasDerivAt_line_snd {g : ℝ × ℝ → G} {q : ℝ × ℝ} (hg : DifferentiableAt ℝ g q) :
    HasDerivAt (fun s ↦ g (q.1, s)) (fderiv ℝ g q (0, 1)) q.2 := by
  have hℓ : HasDerivAt (fun s : ℝ ↦ (q.1, s)) ((0 : ℝ), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hq : ((q.1, q.2) : ℝ × ℝ) = q := Prod.mk.eta
  exact (hq ▸ hg).hasFDerivAt.comp_hasDerivAt q.2 hℓ |>.congr_deriv (by rw [hq])

/-- The derivative of a coefficient `B (w, v)` of a bilinear-map-valued function. -/
lemma fderiv_apply_apply' {B : E → E →L[ℝ] E →L[ℝ] G} {p : E} (hB : DifferentiableAt ℝ B p)
    (a w v : E) : fderiv ℝ (fun q ↦ B q w v) p a = fderiv ℝ B p a w v := by
  have h1 : DifferentiableAt ℝ (fun q ↦ B q w) p := hB.clm_apply (differentiableAt_const w)
  rw [fderiv_clm_apply h1 (differentiableAt_const v), fderiv_clm_apply hB (differentiableAt_const w)]
  simp

set_option synthInstance.maxHeartbeats 400000 in
/-- The derivative of `s ↦ B (c s) (x s) (y s)` for a bilinear-map-valued `B`. -/
lemma hasDerivAt_apply_apply' {B : E → E →L[ℝ] E →L[ℝ] G} {c x y : ℝ → E} {c' x' y' : E}
    {t : ℝ} (hB : DifferentiableAt ℝ B (c t)) (hc : HasDerivAt c c' t) (hx : HasDerivAt x x' t)
    (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s ↦ B (c s) (x s) (y s))
      (fderiv ℝ B (c t) c' (x t) (y t) + B (c t) x' (y t) + B (c t) (x t) y') t := by
  have h := ((@HasFDerivAt.comp_hasDerivAt ℝ _ E _ _ (E →L[ℝ] E →L[ℝ] G)
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace c c' t B _
    hB.hasFDerivAt hc).clm_apply hx).clm_apply hy
  convert h using 1 <;> rfl

/-- **Symmetry of mixed partial derivatives** of a `C^∞` function of two real variables, in the
form used below. -/
lemma fderiv_fderiv_apply_comm {g : ℝ × ℝ → G} {q : ℝ × ℝ} (hg : ContDiffAt ℝ ∞ g q)
    (v w : ℝ × ℝ) :
    fderiv ℝ (fun q ↦ fderiv ℝ g q v) q w = fderiv ℝ (fun q ↦ fderiv ℝ g q w) q v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) q :=
    (hg.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp
  exact (hg.isSymmSndFDerivAt (by simp)).eq w v

end Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

section Defs

variable (I) in
/-- `∂_r F (q)`: the velocity at `q.1` of the curve `s ↦ F (s, q.2)`. -/
def pR (F : ℝ × ℝ → M) (q : ℝ × ℝ) : TangentSpace I (F q) :=
  velocity I (fun s ↦ F (s, q.2)) q.1

variable (I) in
/-- `∂_θ F (q)`: the velocity at `q.2` of the curve `s ↦ F (q.1, s)`. -/
def pθ (F : ℝ × ℝ → M) (q : ℝ × ℝ) : TangentSpace I (F q) :=
  velocity I (fun s ↦ F (q.1, s)) q.2

variable (I) in
/-- The covariant derivative `D_r V` of a field `V` along `F`, along the curves `s ↦ F (s, θ)`. -/
def covR (F : ℝ × ℝ → M) (V : ∀ q, TangentSpace I (F q)) (q : ℝ × ℝ) : TangentSpace I (F q) :=
  covAlong (CovariantDerivative.leviCivitaConnection I M) (fun s ↦ F (s, q.2))
    (fun s ↦ V (s, q.2)) q.1

variable (I) in
/-- The covariant derivative `D_θ V` of a field `V` along `F`, along the curves `s ↦ F (r, s)`. -/
def covθ (F : ℝ × ℝ → M) (V : ∀ q, TangentSpace I (F q)) (q : ℝ × ℝ) : TangentSpace I (F q) :=
  covAlong (CovariantDerivative.leviCivitaConnection I M) (fun s ↦ F (q.1, s))
    (fun s ↦ V (q.1, s)) q.2

variable (I) in
/-- `F` maps the open set `N` of parameters into the domain of the chart at `x₀`, and is `C^∞`
there, read in that chart. -/
structure SmoothInChart (F : ℝ × ℝ → M) (x₀ : M) (N : Set (ℝ × ℝ)) : Prop where
  isOpen : IsOpen N
  mem_source : ∀ q ∈ N, F q ∈ (chartAt H x₀).source
  contDiffOn : ContDiffOn ℝ ∞ (fun q ↦ extChartAt I x₀ (F q)) N

end Defs

section Symmetric

/-- The Christoffel symbols of a chart are symmetric (the Levi-Civita connection is
torsion-free). -/
lemma christoffelLow_symm (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target) (a b : E) :
    christoffelLow I x₀ p a b = christoffelLow I x₀ p b a := by
  ext c
  rw [christoffelLow_apply, christoffelLow_apply, fderiv_metricCoord_symm x₀ hp b a c,
    fderiv_metricCoord_symm x₀ hp a c b, fderiv_metricCoord_symm x₀ hp c b a]
  ring

lemma christoffelL_symm (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target) (a b : E) :
    christoffelL I x₀ p a b = christoffelL I x₀ p b a := by
  rw [christoffelL_apply, christoffelL_apply, christoffel, christoffel,
    christoffelLow_symm x₀ hp a b]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Two tangent vectors at a point of the chart domain with the same coordinates are equal. -/
lemma eq_of_trivializationAt_eq (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    {u v : TangentSpace I y}
    (h : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y u =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y v) : u = v := by
  have hb := mem_baseSet_of_mem_chart_source (I := I) hy
  rw [← Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb u, h,
    Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hb v]

end Symmetric

namespace SmoothInChart

variable {F : ℝ × ℝ → M} {x₀ : M} {N : Set (ℝ × ℝ)}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
lemma differentiableAt (hF : SmoothInChart I F x₀ N) {q : ℝ × ℝ} (hq : q ∈ N) :
    DifferentiableAt ℝ (fun q ↦ extChartAt I x₀ (F q)) q :=
  (hF.contDiffOn.differentiableOn (by simp) q hq).differentiableAt (hF.isOpen.mem_nhds hq)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
lemma mem_target (hF : SmoothInChart I F x₀ N) {q : ℝ × ℝ} (hq : q ∈ N) :
    extChartAt I x₀ (F q) ∈ (extChartAt I x₀).target :=
  (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hF.mem_source q hq)

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The image under `F` of a differentiable curve in `N` is differentiable. -/
lemma mdifferentiableAt_comp (hF : SmoothInChart I F x₀ N) {ℓ : ℝ → ℝ × ℝ} {t : ℝ}
    (hℓ : DifferentiableAt ℝ ℓ t) (hq : ℓ t ∈ N) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ F (ℓ s)) t := by
  have hev : (fun s ↦ F (ℓ s)) =ᶠ[𝓝 t]
      fun s ↦ (extChartAt I x₀).symm (extChartAt I x₀ (F (ℓ s))) := by
    filter_upwards [hℓ.continuousAt.preimage_mem_nhds (hF.isOpen.mem_nhds hq)] with s hs
    exact ((extChartAt I x₀).left_inv
      (by rw [extChartAt_source]; exact hF.mem_source _ hs)).symm
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hX : DifferentiableAt ℝ (fun s ↦ extChartAt I x₀ (F (ℓ s))) t :=
    (hF.differentiableAt hq).comp t hℓ
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ (F (ℓ t))) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds (hF.mem_target hq))).mdifferentiableAt (by simp)
  exact hsymm.comp t hX.mdifferentiableAt

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The velocity of the image of a curve in `N`, in coordinates. -/
lemma velocity_coord (hF : SmoothInChart I F x₀ N) {ℓ : ℝ → ℝ × ℝ} {ℓ' : ℝ × ℝ} {t : ℝ}
    (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ N) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F (ℓ t))
      (velocity I (fun s ↦ F (ℓ s)) t) = fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) (ℓ t) ℓ' := by
  rw [trivializationAt_velocity x₀ (hF.mdifferentiableAt_comp hℓ.differentiableAt hq)
    (hF.mem_source _ hq)]
  exact ((hF.differentiableAt hq).hasFDerivAt.comp_hasDerivAt t hℓ).deriv

/-- **Covariant derivatives along `F ∘ ℓ` in coordinates.** If a field `V` along `F` has
coordinates `v` on `N` in the chart at `x₀`, then along the image of a curve `ℓ` in `N` the field is
differentiable, and `D_t (V ∘ ℓ) = v'(ℓ') + Γ(F ∘ ℓ)((F ∘ ℓ)', v)` in coordinates. -/
theorem covAlong_coord (hF : SmoothInChart I F x₀ N) {V : ∀ q, TangentSpace I (F q)}
    {v : ℝ × ℝ → E}
    (hv : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (V q) =
      v q) {ℓ : ℝ → ℝ × ℝ} {ℓ' : ℝ × ℝ} {t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ N)
    (hvd : DifferentiableAt ℝ v (ℓ t)) :
    MDiffAlongAt I E (fun s ↦ F (ℓ s)) (fun s ↦ V (ℓ s)) t ∧
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F (ℓ t))
        (covAlong (CovariantDerivative.leviCivitaConnection I M) (fun s ↦ F (ℓ s))
          (fun s ↦ V (ℓ s)) t) =
        fderiv ℝ v (ℓ t) ℓ' + christoffelL I x₀ (extChartAt I x₀ (F (ℓ t)))
          (fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) (ℓ t) ℓ') (v (ℓ t)) := by
  have hcoord : coordAlong (trivializationAt E (TangentSpace I) x₀) (fun s ↦ F (ℓ s))
      (fun s ↦ V (ℓ s)) =ᶠ[𝓝 t] fun s ↦ v (ℓ s) := by
    filter_upwards [hℓ.continuousAt.preimage_mem_nhds (hF.isOpen.mem_nhds hq)] with s hs
    exact hv _ hs
  have hvℓ : HasDerivAt (fun s ↦ v (ℓ s)) (fderiv ℝ v (ℓ t) ℓ') t :=
    hvd.hasFDerivAt.comp_hasDerivAt t hℓ
  have hmd : MDiffAlongAt I E (fun s ↦ F (ℓ s)) (fun s ↦ V (ℓ s)) t := by
    rw [mdiffAlongAt_iff (trivializationAt E (TangentSpace I) x₀)
      (mem_baseSet_of_mem_chart_source (hF.mem_source _ hq))]
    exact ⟨hF.mdifferentiableAt_comp hℓ.differentiableAt hq,
      hvℓ.differentiableAt.congr_of_eventuallyEq hcoord⟩
  refine ⟨hmd, ?_⟩
  have hd : deriv (extChartAt I x₀ ∘ fun s ↦ F (ℓ s)) t =
      fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) (ℓ t) ℓ' :=
    ((hF.differentiableAt hq).hasFDerivAt.comp_hasDerivAt t hℓ).deriv
  rw [covAlong_leviCivita_chart x₀ (hF.mem_source _ hq) hmd, hcoord.deriv_eq, hvℓ.deriv,
    hcoord.eq_of_nhds, hd]

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- `∂_r F` in coordinates. -/
lemma pR_coord (hF : SmoothInChart I F x₀ N) {q : ℝ × ℝ} (hq : q ∈ N) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (pR I F q) =
      fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q (1, 0) :=
  hF.velocity_coord (ℓ := fun s ↦ (s, q.2)) (t := q.1)
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)) hq

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- `∂_θ F` in coordinates. -/
lemma pθ_coord (hF : SmoothInChart I F x₀ N) {q : ℝ × ℝ} (hq : q ∈ N) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (pθ I F q) =
      fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q (0, 1) :=
  hF.velocity_coord (ℓ := fun s ↦ (q.1, s)) (t := q.2)
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)) hq

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The partial derivatives of the coordinate expression are smooth on `N`. -/
lemma contDiffOn_fderiv_apply (hF : SmoothInChart I F x₀ N) (v : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (fun q ↦ fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q v) N :=
  (hF.contDiffOn.fderiv_of_isOpen hF.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const

/-- `D_r V` in coordinates, for a field `V` with coordinates `v` on `N`. -/
theorem covR_coord (hF : SmoothInChart I F x₀ N) {V : ∀ q, TangentSpace I (F q)} {v : ℝ × ℝ → E}
    (hv : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (V q) =
      v q) {q : ℝ × ℝ} (hq : q ∈ N) (hvd : DifferentiableAt ℝ v q) :
    MDiffAlongAt I E (fun s ↦ F (s, q.2)) (fun s ↦ V (s, q.2)) q.1 ∧
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (covR I F V q) =
        fderiv ℝ v q (1, 0) + christoffelL I x₀ (extChartAt I x₀ (F q))
          (fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q (1, 0)) (v q) :=
  hF.covAlong_coord hv (ℓ := fun s ↦ (s, q.2)) (t := q.1)
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)) hq hvd

/-- `D_θ V` in coordinates, for a field `V` with coordinates `v` on `N`. -/
theorem covθ_coord (hF : SmoothInChart I F x₀ N) {V : ∀ q, TangentSpace I (F q)} {v : ℝ × ℝ → E}
    (hv : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (V q) =
      v q) {q : ℝ × ℝ} (hq : q ∈ N) (hvd : DifferentiableAt ℝ v q) :
    MDiffAlongAt I E (fun s ↦ F (q.1, s)) (fun s ↦ V (q.1, s)) q.2 ∧
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (covθ I F V q) =
        fderiv ℝ v q (0, 1) + christoffelL I x₀ (extChartAt I x₀ (F q))
          (fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q (0, 1)) (v q) :=
  hF.covAlong_coord hv (ℓ := fun s ↦ (q.1, s)) (t := q.2)
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)) hq hvd

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Chain rule**: the velocity of `F ∘ ℓ` is `ℓ'₁ ∂_r F + ℓ'₂ ∂_θ F`. -/
theorem velocity_eq (hF : SmoothInChart I F x₀ N) {ℓ : ℝ → ℝ × ℝ} {ℓ' : ℝ × ℝ} {t : ℝ}
    (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ N) :
    velocity I (fun s ↦ F (ℓ s)) t = ℓ'.1 • pR I F (ℓ t) + ℓ'.2 • pθ I F (ℓ t) := by
  refine eq_of_trivializationAt_eq x₀ (hF.mem_source _ hq) ?_
  rw [hF.velocity_coord hℓ hq, map_add, map_smul, map_smul, hF.pR_coord hq, hF.pθ_coord hq,
    ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- **Chain rule for covariant derivatives**: along the image `F ∘ ℓ` of a curve in `N`,
`D_t (V ∘ ℓ) = ℓ'₁ D_r V + ℓ'₂ D_θ V`, for a field `V` along `F` with coordinates `v` on `N`. -/
theorem covAlong_eq (hF : SmoothInChart I F x₀ N) {V : ∀ q, TangentSpace I (F q)}
    {v : ℝ × ℝ → E}
    (hv : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q) (V q) =
      v q) {ℓ : ℝ → ℝ × ℝ} {ℓ' : ℝ × ℝ} {t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t) (hq : ℓ t ∈ N)
    (hvd : DifferentiableAt ℝ v (ℓ t)) :
    covAlong (CovariantDerivative.leviCivitaConnection I M) (fun s ↦ F (ℓ s))
        (fun s ↦ V (ℓ s)) t = ℓ'.1 • covR I F V (ℓ t) + ℓ'.2 • covθ I F V (ℓ t) := by
  refine eq_of_trivializationAt_eq x₀ (hF.mem_source _ hq) ?_
  rw [(hF.covAlong_coord hv hℓ hq hvd).2, map_add, map_smul, map_smul,
    (hF.covR_coord hv hq hvd).2, (hF.covθ_coord hv hq hvd).2]
  have hℓ' : ℓ' = ℓ'.1 • ((1 : ℝ), (0 : ℝ)) + ℓ'.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hℓ']
  simp only [map_add, map_smul, add_apply, smul_apply, smul_add]
  abel

/-- **Symmetry lemma**: `D_r ∂_θ F = D_θ ∂_r F` (the Levi-Civita connection is torsion-free). -/
theorem covR_pθ (hF : SmoothInChart I F x₀ N) {q : ℝ × ℝ} (hq : q ∈ N) :
    covR I F (pθ I F) q = covθ I F (pR I F) q := by
  have hX : ContDiffAt ℝ ∞ (fun q ↦ extChartAt I x₀ (F q)) q :=
    hF.contDiffOn.contDiffAt (hF.isOpen.mem_nhds hq)
  have hdθ : DifferentiableAt ℝ (fun q ↦ fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q (0, 1)) q :=
    ((hF.contDiffOn_fderiv_apply (0, 1)).differentiableOn (by simp) q hq).differentiableAt
      (hF.isOpen.mem_nhds hq)
  have hdr : DifferentiableAt ℝ (fun q ↦ fderiv ℝ (fun q ↦ extChartAt I x₀ (F q)) q (1, 0)) q :=
    ((hF.contDiffOn_fderiv_apply (1, 0)).differentiableOn (by simp) q hq).differentiableAt
      (hF.isOpen.mem_nhds hq)
  refine eq_of_trivializationAt_eq x₀ (hF.mem_source q hq) ?_
  have h1 := (hF.covR_coord (fun q hq ↦ hF.pθ_coord hq) hq hdθ).2
  have h2 := (hF.covθ_coord (fun q hq ↦ hF.pR_coord hq) hq hdr).2
  rw [h1, h2, fderiv_fderiv_apply_comm hX (0, 1) (1, 0),
    christoffelL_symm x₀ (hF.mem_target hq)]

/-- **Curvature identity for two-parameter maps**:
`D_r D_θ ∂_r F − D_θ D_r ∂_r F = R(∂_r F, ∂_θ F) ∂_r F` at `q₀`, computed in the chart at
`F q₀`. -/
theorem covR_covθ_sub {q₀ : ℝ × ℝ} (hF : SmoothInChart I F (F q₀) N) (hq₀ : q₀ ∈ N) :
    covR I F (covθ I F (pR I F)) q₀ - covθ I F (covR I F (pR I F)) q₀ =
      riemannCurvature I (F q₀) (pR I F q₀) (pθ I F q₀) (pR I F q₀) := by
  set x₀ := F q₀ with hx₀
  set X : ℝ × ℝ → E := fun q ↦ extChartAt I x₀ (F q) with hX_def
  set w : ℝ × ℝ → E := fun q ↦ fderiv ℝ X q (1, 0) with hw_def
  set j : ℝ × ℝ → E := fun q ↦ fderiv ℝ X q (0, 1) with hj_def
  set Γ : E → E →L[ℝ] E →L[ℝ] E := christoffelL I x₀ with hΓ_def
  have hN : N ∈ 𝓝 q₀ := hF.isOpen.mem_nhds hq₀
  have hXs : ContDiffOn ℝ ∞ X N := hF.contDiffOn
  have hws : ContDiffOn ℝ ∞ w N := hF.contDiffOn_fderiv_apply (1, 0)
  have hjs : ContDiffOn ℝ ∞ j N := hF.contDiffOn_fderiv_apply (0, 1)
  have hΓs : ContDiffOn ℝ ∞ Γ (extChartAt I x₀).target := contDiffOn_christoffelL x₀
  have hXN : MapsTo X N (extChartAt I x₀).target := fun q hq ↦ hF.mem_target hq
  have hΓX : ContDiffOn ℝ ∞ (fun q ↦ Γ (X q)) N := hΓs.comp hXs hXN
  -- coordinates of `D_θ ∂_r F` and `D_r ∂_r F` on `N`
  set c₁ : ℝ × ℝ → E := fun q ↦ fderiv ℝ w q (0, 1) + Γ (X q) (j q) (w q) with hc₁_def
  set c₂ : ℝ × ℝ → E := fun q ↦ fderiv ℝ w q (1, 0) + Γ (X q) (w q) (w q) with hc₂_def
  have hwd : ∀ q ∈ N, DifferentiableAt ℝ w q := fun q hq ↦
    (hws.differentiableOn (by simp) q hq).differentiableAt (hF.isOpen.mem_nhds hq)
  have hc₁ : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q)
      (covθ I F (pR I F) q) = c₁ q := fun q hq ↦
    (hF.covθ_coord (fun q hq ↦ hF.pR_coord hq) hq (hwd q hq)).2
  have hc₂ : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q)
      (covR I F (pR I F) q) = c₂ q := fun q hq ↦
    (hF.covR_coord (fun q hq ↦ hF.pR_coord hq) hq (hwd q hq)).2
  have hc₁s : ContDiffOn ℝ ∞ c₁ N :=
    ((hws.fderiv_of_isOpen hF.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).add
      ((hΓX.clm_apply hjs).clm_apply hws)
  have hc₂s : ContDiffOn ℝ ∞ c₂ N :=
    ((hws.fderiv_of_isOpen hF.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).add
      ((hΓX.clm_apply hws).clm_apply hws)
  have hc₁d : DifferentiableAt ℝ c₁ q₀ :=
    (hc₁s.differentiableOn (by simp) q₀ hq₀).differentiableAt hN
  have hc₂d : DifferentiableAt ℝ c₂ q₀ :=
    (hc₂s.differentiableOn (by simp) q₀ hq₀).differentiableAt hN
  have e₁ : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q₀)
      (covR I F (covθ I F (pR I F)) q₀) = fderiv ℝ c₁ q₀ (1, 0) + Γ (X q₀) (w q₀) (c₁ q₀) :=
    (hF.covR_coord hc₁ hq₀ hc₁d).2
  have e₂ : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q₀)
      (covθ I F (covR I F (pR I F)) q₀) = fderiv ℝ c₂ q₀ (0, 1) + Γ (X q₀) (j q₀) (c₂ q₀) :=
    (hF.covθ_coord hc₂ hq₀ hc₂d).2
  -- the derivatives of `c₁` along `r` and of `c₂` along `θ`
  have hXd : DifferentiableAt ℝ X q₀ := hF.differentiableAt hq₀
  have hjd : DifferentiableAt ℝ j q₀ :=
    (hjs.differentiableOn (by simp) q₀ hq₀).differentiableAt hN
  have hΓd : DifferentiableAt ℝ Γ (X q₀) :=
    (hΓs.differentiableOn (by simp) _ (hF.mem_target hq₀)).differentiableAt
      ((isOpen_extChartAt_target x₀).mem_nhds (hF.mem_target hq₀))
  have hwθd : DifferentiableAt ℝ (fun q ↦ fderiv ℝ w q (0, 1)) q₀ :=
    (((hws.fderiv_of_isOpen hF.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).differentiableOn
      (by simp) q₀ hq₀).differentiableAt hN
  have hwrd : DifferentiableAt ℝ (fun q ↦ fderiv ℝ w q (1, 0)) q₀ :=
    (((hws.fderiv_of_isOpen hF.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).differentiableOn
      (by simp) q₀ hq₀).differentiableAt hN
  have hD₁ : HasDerivAt (fun s ↦ c₁ (s, q₀.2))
      (fderiv ℝ (fun q ↦ fderiv ℝ w q (0, 1)) q₀ (1, 0) +
        (fderiv ℝ Γ (X q₀) (w q₀) (j q₀) (w q₀) + Γ (X q₀) (fderiv ℝ j q₀ (1, 0)) (w q₀) +
          Γ (X q₀) (j q₀) (fderiv ℝ w q₀ (1, 0)))) q₀.1 :=
    (hasDerivAt_line_fst hwθd).add (hasDerivAt_apply_apply' hΓd (hasDerivAt_line_fst hXd)
      (hasDerivAt_line_fst hjd) (hasDerivAt_line_fst (hwd q₀ hq₀)))
  have hD₂ : HasDerivAt (fun s ↦ c₂ (q₀.1, s))
      (fderiv ℝ (fun q ↦ fderiv ℝ w q (1, 0)) q₀ (0, 1) +
        (fderiv ℝ Γ (X q₀) (j q₀) (w q₀) (w q₀) + Γ (X q₀) (fderiv ℝ w q₀ (0, 1)) (w q₀) +
          Γ (X q₀) (w q₀) (fderiv ℝ w q₀ (0, 1)))) q₀.2 :=
    (hasDerivAt_line_snd hwrd).add (hasDerivAt_apply_apply' hΓd (hasDerivAt_line_snd hXd)
      (hasDerivAt_line_snd (hwd q₀ hq₀)) (hasDerivAt_line_snd (hwd q₀ hq₀)))
  have hf₁ := (hasDerivAt_line_fst hc₁d).unique hD₁
  have hf₂ := (hasDerivAt_line_snd hc₂d).unique hD₂
  -- symmetry of mixed partial derivatives
  have hXc : ContDiffAt ℝ ∞ X q₀ := hXs.contDiffAt hN
  have hwc : ContDiffAt ℝ ∞ w q₀ := hws.contDiffAt hN
  have hm₁ : fderiv ℝ j q₀ (1, 0) = fderiv ℝ w q₀ (0, 1) :=
    fderiv_fderiv_apply_comm hXc (0, 1) (1, 0)
  have hm₂ : fderiv ℝ (fun q ↦ fderiv ℝ w q (0, 1)) q₀ (1, 0) =
      fderiv ℝ (fun q ↦ fderiv ℝ w q (1, 0)) q₀ (0, 1) :=
    fderiv_fderiv_apply_comm hwc (0, 1) (1, 0)
  -- the curvature in the chart at `x₀ = F q₀`
  have hx₀b : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_of_mem_chart_source (mem_chart_source H x₀)
  have hR : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀
      (riemannCurvature I x₀ (pR I F q₀) (pθ I F q₀) (pR I F q₀)) =
      curvCoord I x₀ (X q₀) (w q₀) (j q₀) (w q₀) := by
    rw [riemannCurvature, Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hx₀b,
      hF.pR_coord hq₀, hF.pθ_coord hq₀]
  refine eq_of_trivializationAt_eq x₀ (hF.mem_source q₀ hq₀) ?_
  rw [map_sub, e₁, e₂, hR, hf₁, hf₂, hm₁, hm₂]
  simp only [curvCoord, christoffelDeriv]
  rw [← hΓ_def]
  simp only [fderiv_apply_apply' hΓd, hc₁_def, hc₂_def, map_add]
  abel

end SmoothInChart

section Variation

variable {F : ℝ × ℝ → M} {D : Set (ℝ × ℝ)}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- A map which is `C^∞` on an open set of parameters is smooth in every chart. -/
lemma smoothInChart_of_contMDiffOn (hD : IsOpen D) (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ F D)
    (x₀ : M) : SmoothInChart I F x₀ (D ∩ F ⁻¹' (chartAt H x₀).source) where
  isOpen := hF.continuousOn.isOpen_inter_preimage hD (chartAt H x₀).open_source
  mem_source := fun _ hq ↦ hq.2
  contDiffOn := fun q hq ↦ by
    have h := (contMDiffAt_extChartAt' (I := I) (n := ∞) hq.2).comp q
      (hF.contMDiffAt (hD.mem_nhds hq.1))
    exact (contMDiffAt_iff_contDiffAt.1 h).contDiffWithinAt

/-- `F` is a **variation through geodesics** on the open set `D`: `F` is `C^∞` on `D` and every curve
`r ↦ F (r, θ)` is a geodesic where it is defined. -/
structure IsGeodesicVariation (F : ℝ × ℝ → M) (D : Set (ℝ × ℝ)) : Prop where
  isOpen : IsOpen D
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ F D
  isGeodesic : ∀ q ∈ D, covR I F (pR I F) q = 0

namespace IsGeodesicVariation

/-- The **variation field of a variation through geodesics is a Jacobi field**:
`D_r² ∂_θ F + R(∂_θ F, ∂_r F) ∂_r F = 0` along each geodesic `r ↦ F (r, θ₀)`. -/
theorem isJacobiFieldOn (hF : IsGeodesicVariation (I := I) F D) (θ₀ : ℝ) :
    IsJacobiFieldOn I (fun r ↦ F (r, θ₀)) (fun r ↦ pθ I F (r, θ₀)) {r | (r, θ₀) ∈ D} := by
  intro r₀ hr₀
  set q₀ : ℝ × ℝ := (r₀, θ₀)
  set x₀ := F q₀
  set N := D ∩ F ⁻¹' (chartAt H x₀).source
  have hS : SmoothInChart I F x₀ N := smoothInChart_of_contMDiffOn hF.isOpen hF.contMDiffOn x₀
  have hq₀ : q₀ ∈ N := ⟨hr₀, mem_chart_source H x₀⟩
  have hN : N ∈ 𝓝 q₀ := hS.isOpen.mem_nhds hq₀
  -- coordinates of the fields involved
  set X : ℝ × ℝ → E := fun q ↦ extChartAt I x₀ (F q)
  set w : ℝ × ℝ → E := fun q ↦ fderiv ℝ X q (1, 0)
  set j : ℝ × ℝ → E := fun q ↦ fderiv ℝ X q (0, 1)
  have hws : ContDiffOn ℝ ∞ w N := hS.contDiffOn_fderiv_apply (1, 0)
  have hjs : ContDiffOn ℝ ∞ j N := hS.contDiffOn_fderiv_apply (0, 1)
  have hjd : ∀ q ∈ N, DifferentiableAt ℝ j q := fun q hq ↦
    (hjs.differentiableOn (by simp) q hq).differentiableAt (hS.isOpen.mem_nhds hq)
  have hΓX : ContDiffOn ℝ ∞ (fun q ↦ christoffelL I x₀ (X q)) N :=
    (contDiffOn_christoffelL x₀).comp hS.contDiffOn (fun q hq ↦ hS.mem_target hq)
  set c₃ : ℝ × ℝ → E := fun q ↦ fderiv ℝ j q (1, 0) + christoffelL I x₀ (X q) (w q) (j q)
  have hc₃ : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q)
      (covR I F (pθ I F) q) = c₃ q := fun q hq ↦
    (hS.covR_coord (fun q hq ↦ hS.pθ_coord hq) hq (hjd q hq)).2
  have hc₃s : ContDiffOn ℝ ∞ c₃ N :=
    ((hjs.fderiv_of_isOpen hS.isOpen (m := ∞) (by simp)).clm_apply contDiffOn_const).add
      ((hΓX.clm_apply hws).clm_apply hjs)
  have hc₃d : DifferentiableAt ℝ c₃ q₀ :=
    (hc₃s.differentiableOn (by simp) q₀ hq₀).differentiableAt hN
  refine ⟨(hS.covR_coord (fun q hq ↦ hS.pθ_coord hq) hq₀ (hjd q₀ hq₀)).1,
    (hS.covR_coord hc₃ hq₀ hc₃d).1, ?_⟩
  -- `D_r D_r ∂_θ F = D_r D_θ ∂_r F` (symmetry lemma near `q₀`)
  have hsymm : covAlong (CovariantDerivative.leviCivitaConnection I M) (fun r ↦ F (r, θ₀))
      (fun r ↦ covR I F (pθ I F) (r, θ₀)) r₀ = covR I F (covθ I F (pR I F)) q₀ := by
    have hline : Tendsto (fun r : ℝ ↦ ((r, θ₀) : ℝ × ℝ)) (𝓝 r₀) (𝓝 q₀) :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hev : ∀ᶠ r in 𝓝 r₀, covR I F (pθ I F) (r, θ₀) = covθ I F (pR I F) (r, θ₀) := by
      filter_upwards [hline.eventually (hS.isOpen.mem_nhds hq₀)] with r hr
      exact hS.covR_pθ hr
    exact covAlong_congr (CovariantDerivative.leviCivitaConnection I M) hev
  -- `D_θ D_r ∂_r F = 0` since `D_r ∂_r F = 0` on `D`
  have hzero : covθ I F (covR I F (pR I F)) q₀ = 0 := by
    have hv : ∀ q ∈ N, (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (F q)
        (covR I F (pR I F) q) = (fun _ ↦ (0 : E)) q := fun q hq ↦ by
      rw [hF.isGeodesic q hq.1, map_zero]
    have h := (hS.covθ_coord hv hq₀ (differentiableAt_const 0)).2
    simp only [fderiv_const_apply, zero_apply, map_zero, add_zero] at h
    exact eq_of_trivializationAt_eq x₀ (hS.mem_source q₀ hq₀) (h.trans (map_zero _).symm)
  have hcurv := hS.covR_covθ_sub (q₀ := q₀) hq₀
  rw [hzero, sub_zero] at hcurv
  show covAlong (CovariantDerivative.leviCivitaConnection I M) (fun r ↦ F (r, θ₀))
      (fun r ↦ covR I F (pθ I F) (r, θ₀)) r₀ +
    riemannCurvature I (F q₀) (pθ I F q₀) (pR I F q₀) (pR I F q₀) = 0
  rw [hsymm, hcurv, riemannCurvature_swap, neg_add_cancel]

/-- The curves `r ↦ F (r, θ)` of a variation through geodesics are geodesics. -/
theorem isGeodesicOn (hF : IsGeodesicVariation (I := I) F D) (θ : ℝ) :
    IsGeodesicOn I (fun r ↦ F (r, θ)) {r | (r, θ) ∈ D} := by
  intro r hr
  set N := D ∩ F ⁻¹' (chartAt H (F (r, θ))).source
  have hS : SmoothInChart I F (F (r, θ)) N :=
    smoothInChart_of_contMDiffOn hF.isOpen hF.contMDiffOn (F (r, θ))
  have hqN : (r, θ) ∈ N := ⟨hr, mem_chart_source H _⟩
  have hwd := ((hS.contDiffOn_fderiv_apply (1, 0)).differentiableOn (by simp) (r, θ)
    hqN).differentiableAt (hS.isOpen.mem_nhds hqN)
  exact ⟨(hS.covR_coord (fun q hq ↦ hS.pR_coord hq) hqN hwd).1, hF.isGeodesic (r, θ) hr⟩

/-- In a variation through geodesics, `∂_r ⟨∂_r F, ∂_θ F⟩ = ⟨∂_r F, D_θ ∂_r F⟩`. -/
theorem hasDerivAt_inner_pR_pθ (hF : IsGeodesicVariation (I := I) F D) {q : ℝ × ℝ}
    (hq : q ∈ D) :
    HasDerivAt (fun r ↦ inner ℝ (pR I F (r, q.2)) (pθ I F (r, q.2)))
      (inner ℝ (pR I F q) (covθ I F (pR I F) q)) q.1 := by
  set N := D ∩ F ⁻¹' (chartAt H (F q)).source
  have hS : SmoothInChart I F (F q) N :=
    smoothInChart_of_contMDiffOn hF.isOpen hF.contMDiffOn (F q)
  have hqN : q ∈ N := ⟨hq, mem_chart_source H (F q)⟩
  have hwd := ((hS.contDiffOn_fderiv_apply (1, 0)).differentiableOn (by simp) q
    hqN).differentiableAt (hS.isOpen.mem_nhds hqN)
  have hjd := ((hS.contDiffOn_fderiv_apply (0, 1)).differentiableOn (by simp) q
    hqN).differentiableAt (hS.isOpen.mem_nhds hqN)
  have h := hasDerivAt_inner_along (hS.covR_coord (fun q hq ↦ hS.pR_coord hq) hqN hwd).1
    (hS.covR_coord (fun q hq ↦ hS.pθ_coord hq) hqN hjd).1
  have h0 : covR I F (pR I F) q = 0 := hF.isGeodesic q hq
  have hsym : covR I F (pθ I F) q = covθ I F (pR I F) q := hS.covR_pθ hqN
  simp only [covR] at h0 hsym
  rw [h0, inner_zero_left, zero_add, hsym] at h
  exact h

/-- `∂_θ ⟨∂_r F, ∂_r F⟩ = 2 ⟨∂_r F, D_θ ∂_r F⟩` (metric compatibility). -/
theorem hasDerivAt_inner_pR_pR (hF : IsGeodesicVariation (I := I) F D) {q : ℝ × ℝ}
    (hq : q ∈ D) :
    HasDerivAt (fun θ ↦ inner ℝ (pR I F (q.1, θ)) (pR I F (q.1, θ)))
      (2 * inner ℝ (pR I F q) (covθ I F (pR I F) q)) q.2 := by
  set N := D ∩ F ⁻¹' (chartAt H (F q)).source
  have hS : SmoothInChart I F (F q) N :=
    smoothInChart_of_contMDiffOn hF.isOpen hF.contMDiffOn (F q)
  have hqN : q ∈ N := ⟨hq, mem_chart_source H (F q)⟩
  have hwd := ((hS.contDiffOn_fderiv_apply (1, 0)).differentiableOn (by simp) q
    hqN).differentiableAt (hS.isOpen.mem_nhds hqN)
  have hmd := (hS.covθ_coord (fun q hq ↦ hS.pR_coord hq) hqN hwd).1
  have h := hasDerivAt_inner_along hmd hmd
  have hc : covAlong (CovariantDerivative.leviCivitaConnection I M) (fun s ↦ F (q.1, s))
      (fun s ↦ pR I F (q.1, s)) q.2 = covθ I F (pR I F) q := rfl
  rw [hc] at h
  have hcomm : inner ℝ (covθ I F (pR I F) q) (pR I F (q.1, q.2)) =
      inner ℝ (pR I F q) (covθ I F (pR I F) q) := real_inner_comm _ _
  rw [hcomm] at h
  convert h using 1
  ring

end IsGeodesicVariation

end Variation

end PythagoreanPaper
