import PythagoreanPaper.Riemannian.InnerAlong

/-!
# The Riemann curvature tensor of the Levi-Civita connection

We use the convention `R(X, Y) Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`, for which the Jacobi
equation of the manuscript reads `D_t² J + R(J, γ̇) γ̇ = 0` and the round sphere has positive
sectional curvature `⟨R(u, v) v, u⟩ / (|u|² |v|² − ⟨u, v⟩²)`.

* `curvCoord`: in the chart at `x₀`, `R(a, b) c = ∂_a Γ(b, c) − ∂_b Γ(a, c) + Γ(a, Γ(b, c)) −
  Γ(b, Γ(a, c))`, with the Christoffel symbols `Γ` of `PythagoreanPaper.Riemannian.Coordinates`.
* `riemannCurvature I x u v w`: the curvature at `x`, computed in the chart at `x`.
* `riemannCurvature_coordField`: for the coordinate fields `∂_a, ∂_b, ∂_c` of the chart at `x`,
  `R(∂_a, ∂_b) ∂_c = ∇_{∂_a} ∇_{∂_b} ∂_c − ∇_{∂_b} ∇_{∂_a} ∂_c − ∇_{[∂_a, ∂_b]} ∂_c` at `x`, for
  Mathlib's Levi-Civita connection. Since the coordinate fields at `x` span `T_x M`, this
  identifies `riemannCurvature` with the curvature tensor of Mathlib's Levi-Civita connection.
* `HasConstSectionalCurvature I M K`: every tangent plane has sectional curvature `K`.
* `IsGeodesicOn`, `IsJacobiFieldOn`: geodesics (`D_t γ̇ = 0`) and Jacobi fields
  (`D_t² J + R(J, γ̇) γ̇ = 0`, manuscript C4.1).
-/

noncomputable section

open Bundle Set Filter Function VectorField
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

section Coordinates

variable (I) in
/-- The derivative `∂_a Γ(b, c)` of the Christoffel symbols in the chart at `x₀`, at the point with
coordinates `p`. -/
def christoffelDeriv (x₀ : M) (p a b c : E) : E :=
  fderiv ℝ (fun q ↦ christoffelL I x₀ q b c) p a

variable (I) in
/-- The Riemann curvature in the chart at `x₀`, at the point with coordinates `p`:
`R(a, b) c = ∂_a Γ(b, c) − ∂_b Γ(a, c) + Γ(a, Γ(b, c)) − Γ(b, Γ(a, c))`. -/
def curvCoord (x₀ : M) (p a b c : E) : E :=
  christoffelDeriv I x₀ p a b c - christoffelDeriv I x₀ p b a c +
    christoffelL I x₀ p a (christoffelL I x₀ p b c) -
    christoffelL I x₀ p b (christoffelL I x₀ p a c)

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
lemma curvCoord_swap (x₀ : M) (p a b c : E) :
    curvCoord I x₀ p b a c = -curvCoord I x₀ p a b c := by
  simp only [curvCoord]
  abel

/-- The Christoffel symbols with fixed arguments are smooth on the chart. -/
lemma contDiffOn_christoffelL_apply (x₀ : M) (b c : E) :
    ContDiffOn ℝ ∞ (fun q ↦ christoffelL I x₀ q b c) (extChartAt I x₀).target :=
  ((contDiffOn_christoffelL x₀).clm_apply contDiffOn_const).clm_apply contDiffOn_const

lemma differentiableAt_christoffelL_apply (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target)
    (b c : E) : DifferentiableAt ℝ (fun q ↦ christoffelL I x₀ q b c) p :=
  ((contDiffOn_christoffelL_apply x₀ b c).differentiableOn (by simp) p hp).differentiableAt
    ((isOpen_extChartAt_target x₀).mem_nhds hp)

/-- `∂_a Γ(b, c)` is linear in `b`. -/
lemma christoffelDeriv_smul_mid (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target)
    (s : ℝ) (a b c : E) :
    christoffelDeriv I x₀ p a (s • b) c = s • christoffelDeriv I x₀ p a b c := by
  have h : (fun q ↦ christoffelL I x₀ q (s • b) c) = fun q ↦ s • christoffelL I x₀ q b c := by
    funext q
    rw [map_smul, smul_apply]
  have h2 : fderiv ℝ (fun q ↦ s • christoffelL I x₀ q b c) p =
      s • fderiv ℝ (fun q ↦ christoffelL I x₀ q b c) p :=
    ((differentiableAt_christoffelL_apply x₀ hp b c).hasFDerivAt.const_smul s).fderiv
  simp only [christoffelDeriv, h, h2, smul_apply]

/-- The curvature in a chart is homogeneous in its first argument. -/
lemma curvCoord_smul_left (x₀ : M) {p : E} (hp : p ∈ (extChartAt I x₀).target) (s : ℝ)
    (a b c : E) : curvCoord I x₀ p (s • a) b c = s • curvCoord I x₀ p a b c := by
  simp only [curvCoord, christoffelDeriv_smul_mid x₀ hp]
  simp only [christoffelDeriv, map_smul, smul_apply, smul_sub, smul_add]

/-- The derivative of a coordinate expression of the Christoffel symbols along a coordinate field:
`∂_a (Γ(b, c))` at `y`. -/
lemma mvfderiv_christoffelL_apply (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    (a b c : E) :
    d% (fun z ↦ christoffelL I x₀ (extChartAt I x₀ z) b c) y (coordField I x₀ a y) =
      christoffelDeriv I x₀ (extChartAt I x₀ y) a b c := by
  have hy' : y ∈ (extChartAt I x₀).source := by simpa using hy
  have hg := differentiableAt_christoffelL_apply (I := I) x₀
    ((extChartAt I x₀).map_source hy') b c
  have hd : d% (fun z ↦ christoffelL I x₀ (extChartAt I x₀ z) b c) y =
      d% ((fun q ↦ christoffelL I x₀ q b c) ∘ extChartAt I x₀) y := rfl
  rw [hd, mvfderiv_comp y hg.mdifferentiableAt (mdifferentiableAt_extChartAt hy),
    ContinuousLinearMap.comp_apply, mfderiv_extChartAt_coordField x₀ hy a, mvfderiv_eq_fderiv]
  rfl

/-- **Second covariant derivatives of coordinate fields**: in the chart at `x₀`,
`∇_{∂_a} ∇_{∂_b} ∂_c = ∂_a Γ(b, c) + Γ(a, Γ(b, c))`. -/
theorem leviCivita_leviCivita_coordField (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source)
    (a b c : E) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
      (CovariantDerivative.leviCivitaConnection I M
        (fun z ↦ CovariantDerivative.leviCivitaConnection I M (coordField I x₀ c) z
          (coordField I x₀ b z)) y (coordField I x₀ a y)) =
      christoffelDeriv I x₀ (extChartAt I x₀ y) a b c +
        christoffelL I x₀ (extChartAt I x₀ y) a
          (christoffelL I x₀ (extChartAt I x₀ y) b c) := by
  have hy' := mem_baseSet_of_mem_chart_source (I := I) hy
  have hφy : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by simpa using hy)
  have hh : MDiffAt (fun z ↦ christoffelL I x₀ (extChartAt I x₀ z) b c) y :=
    (differentiableAt_christoffelL_apply (I := I) x₀ hφy b c).mdifferentiableAt.comp y
      (mdifferentiableAt_extChartAt hy)
  have heq : ∀ᶠ z in 𝓝 y, CovariantDerivative.leviCivitaConnection I M (coordField I x₀ c) z
      (coordField I x₀ b z) = (trivializationAt E (TangentSpace I) x₀).symmL ℝ z
        (christoffelL I x₀ (extChartAt I x₀ z) b c) := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hy] with z hz
    rw [leviCivita_coordField x₀ hz b c, christoffelL_apply]
    rfl
  have hτ := mdifferentiableAt_symmL_comp (trivializationAt E (TangentSpace I) x₀) hy' hh
  have hσ : MDiffAt (T% (fun z ↦ CovariantDerivative.leviCivitaConnection I M
      (coordField I x₀ c) z (coordField I x₀ b z))) y :=
    hτ.congr_of_eventuallyEq (heq.mono fun z hz ↦ by simp only [hz])
  rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hσ hτ Filter.univ_mem heq,
    cov_symmL_comp (CovariantDerivative.leviCivitaConnection I M)
      (trivializationAt E (TangentSpace I) x₀) hy' hh,
    add_apply, map_add, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hy',
    mvfderiv_christoffelL_apply x₀ hy a b c]
  congr 1
  have h1 := leviCivita_coordField_apply x₀ hy (coordField I x₀ a y)
    (christoffelL I x₀ (extChartAt I x₀ y) b c)
  have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
      (coordField I x₀ a y) = a :=
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL hy' a
  rw [h2] at h1
  simp only [christoffelL_apply] at h1 ⊢
  exact h1

end Coordinates

section Curvature

variable (I) in
/-- **The Riemann curvature tensor** of the Levi-Civita connection at `x`,
`R(u, v) w = ∇_u ∇_v w − ∇_v ∇_u w − ∇_{[u,v]} w`, computed in the chart at `x`
(see `riemannCurvature_coordField`). -/
def riemannCurvature (x : M) (u v w : TangentSpace I x) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ x
    (curvCoord I x (extChartAt I x x)
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w))

/-- **The curvature tensor on coordinate fields**: for the coordinate fields of the chart at `x`,
`R(∂_a, ∂_b) ∂_c = ∇_{∂_a} ∇_{∂_b} ∂_c − ∇_{∂_b} ∇_{∂_a} ∂_c − ∇_{[∂_a, ∂_b]} ∂_c` at `x`, for
Mathlib's Levi-Civita connection. -/
theorem riemannCurvature_coordField (x : M) (a b c : E) :
    riemannCurvature I x (coordField I x a x) (coordField I x b x) (coordField I x c x) =
      CovariantDerivative.leviCivitaConnection I M
          (fun z ↦ CovariantDerivative.leviCivitaConnection I M (coordField I x c) z
            (coordField I x b z)) x (coordField I x a x) -
        CovariantDerivative.leviCivitaConnection I M
          (fun z ↦ CovariantDerivative.leviCivitaConnection I M (coordField I x c) z
            (coordField I x a z)) x (coordField I x b x) -
        CovariantDerivative.leviCivitaConnection I M (coordField I x c) x
          (mlieBracket I (coordField I x a) (coordField I x b) x) := by
  have hx : x ∈ (chartAt H x).source := mem_chart_source H x
  have hx' := mem_baseSet_of_mem_chart_source (I := I) hx
  have he : ∀ w : E, (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x
      (coordField I x w x) = w := fun w ↦
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt_symmL hx' w
  have hinj : ∀ u v : TangentSpace I x,
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v → u = v := by
    intro u v h
    rw [← Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hx' u, h,
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hx' v]
  rw [mlieBracket_coordField x a b hx, map_zero, sub_zero]
  apply hinj
  rw [map_sub, leviCivita_leviCivita_coordField x hx a b c,
    leviCivita_leviCivita_coordField x hx b a c, riemannCurvature,
    Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hx', he, he, he]
  simp only [curvCoord]
  abel

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The curvature tensor is antisymmetric in its first two arguments. -/
theorem riemannCurvature_swap (x : M) (u v w : TangentSpace I x) :
    riemannCurvature I x v u w = -riemannCurvature I x u v w := by
  rw [riemannCurvature, riemannCurvature, curvCoord_swap, map_neg]

/-- The curvature tensor is homogeneous in its first argument. -/
theorem riemannCurvature_smul_left (x : M) (s : ℝ) (u v w : TangentSpace I x) :
    riemannCurvature I x (s • u) v w = s • riemannCurvature I x u v w := by
  have hx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  rw [riemannCurvature, riemannCurvature, map_smul, curvCoord_smul_left x hx, map_smul]

end Curvature

section Definitions

variable (I M) in
/-- `M` has **constant sectional curvature** `K`: at every point, for all tangent vectors `u, v`,
`⟨R(u, v) v, u⟩ = K (|u|² |v|² − ⟨u, v⟩²)`; that is, every tangent plane has sectional curvature
`K`. (For linearly dependent `u, v` both sides vanish.) In dimension two the sectional curvature
of the unique tangent plane is the Gaussian curvature, so this says that the Gaussian curvature is
`K` everywhere. -/
def HasConstSectionalCurvature (K : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x),
    inner ℝ (riemannCurvature I x u v v) u = K * (‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2)

variable (I) in
/-- `γ` is a **geodesic** on `U`: its velocity is a parallel field along it, `D_t γ̇ = 0`. -/
def IsGeodesicOn (γ : ℝ → M) (U : Set ℝ) : Prop :=
  IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ (velocity I γ) U

variable (I) in
/-- **Jacobi fields** (manuscript C4.1). `J` is a Jacobi field along the curve `γ` on `U` if `J` and
`D_t J` are differentiable along `γ` and the Jacobi equation `D_t² J + R(J, γ̇) γ̇ = 0` holds on `U`
(`D_t`: covariant derivative along `γ` of the Levi-Civita connection; `R`: its curvature tensor).
This defines Jacobi fields as the solutions of the Jacobi equation; that the variation fields of
geodesic variations satisfy it is a separate theorem. -/
def IsJacobiFieldOn (γ : ℝ → M) (J : (t : ℝ) → TangentSpace I (γ t)) (U : Set ℝ) : Prop :=
  ∀ t ∈ U, MDiffAlongAt I E γ J t ∧
    MDiffAlongAt I E γ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J) t ∧
    covAlong (CovariantDerivative.leviCivitaConnection I M) γ
        (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J) t +
      riemannCurvature I (γ t) (J t) (velocity I γ t) (velocity I γ t) = 0

end Definitions

end PythagoreanPaper
