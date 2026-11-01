import PythagoreanPaper.Riemannian.Curvature
import PythagoreanPaper.Riemannian.Euclidean
import PythagoreanPaper.SK

/-!
# Manuscript §3–§4: the normal component of a Jacobi field

Let `M` be a two-dimensional Riemannian manifold of constant curvature `K`, `γ` a unit-speed curve
(in the manuscript, a geodesic) on an open interval `U`, and `E` a parallel unit normal field
along `γ`. For a Jacobi field `J` orthogonal to `γ̇` (C4.1: `D_t² J + R(J, γ̇) γ̇ = 0`):

* `sec4_jacobi_normal_eq` (**C4.2**): `J = j E` with `j = ⟨J, E⟩`, and `j'' + K j = 0`;
* `sec3_jacobi_flat` (**C3.1**): for curvature zero, `j'' = 0`; the Euclidean plane has curvature
  zero (`hasConstSectionalCurvature_euclidean`);
* `sec4_jacobi_eq_S` (first half of the geometric part of **C4.4**): if moreover `0 ∈ U`,
  `J(0) = 0` and `D_t J(0) = E(0)`, then `J = S_K E` on `U`, so `|J| = |S_K|`.

The derivation is the manuscript's: `j' = ⟨D_t J, E⟩` and `j'' = ⟨D_t² J, E⟩` because `E` is
parallel and the connection is metric (`hasDerivAt_inner_along`), and
`⟨R(J, γ̇) γ̇, E⟩ = j ⟨R(E, γ̇) γ̇, E⟩ = K j` by constant curvature.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace PythagoreanPaper

/-- In a two-dimensional real inner product space, if `u, e` are orthonormal and `w ⟂ u`, then
`w = ⟨w, e⟩ e`. -/
lemma eq_inner_smul_of_orthonormal_two {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (hV : Module.finrank ℝ V = 2) {u e w : V} (hu : ‖u‖ = 1)
    (he : ‖e‖ = 1) (hue : inner ℝ e u = 0) (hw : inner ℝ w u = 0) :
    w = inner ℝ w e • e := by
  by_contra hne
  have hw'0 : w - inner ℝ w e • e ≠ 0 := sub_ne_zero.2 hne
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hee : inner ℝ e e = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have h1 : inner ℝ u e = (0 : ℝ) := by
    rw [real_inner_comm]
    exact hue
  have h2 : inner ℝ u (w - inner ℝ w e • e) = (0 : ℝ) := by
    rw [inner_sub_right, real_inner_smul_right, h1, real_inner_comm, hw]
    ring
  have h3 : inner ℝ e (w - inner ℝ w e • e) = (0 : ℝ) := by
    rw [inner_sub_right, real_inner_smul_right, hee, real_inner_comm]
    ring
  have hli : LinearIndependent ℝ ![u, e, w - inner ℝ w e • e] := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i
      · exact hu0
      · exact he0
      · exact hw'0
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact h1
      · exact h2
      · exact hue
      · exact absurd rfl hij
      · exact h3
      · simpa [real_inner_comm] using h2
      · simpa [real_inner_comm] using h3
      · exact absurd rfl hij
  have : Module.Finite ℝ V := Module.finite_of_finrank_pos (by omega)
  have h := hli.fintype_card_le_finrank
  rw [hV, Fintype.card_fin] at h
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The component of a Jacobi field on a parallel field: `⟨J, P⟩' = ⟨D_t J, P⟩` and
`⟨D_t J, P⟩' = ⟨D_t² J, P⟩ = -⟨R(J, γ̇) γ̇, P⟩`. -/
theorem IsJacobiFieldOn.hasDerivAt_inner_parallel {γ : ℝ → M} {U : Set ℝ}
    {J P : (t : ℝ) → TangentSpace I (γ t)} (hJ : IsJacobiFieldOn I γ J U)
    (hP : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ P U) {t : ℝ}
    (ht : t ∈ U) :
    HasDerivAt (fun s ↦ inner ℝ (J s) (P s))
        (inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J t) (P t)) t ∧
      HasDerivAt
        (fun s ↦ inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J s) (P s))
        (-inner ℝ (riemannCurvature I (γ t) (J t) (velocity I γ t) (velocity I γ t)) (P t)) t := by
  obtain ⟨hJt, hDJt, hjac⟩ := hJ t ht
  obtain ⟨hPt, hPcov⟩ := hP t ht
  constructor
  · have h := hasDerivAt_inner_along hJt hPt
    rwa [hPcov, inner_zero_right, add_zero] at h
  · have h := hasDerivAt_inner_along hDJt hPt
    rwa [hPcov, inner_zero_right, add_zero, eq_neg_of_add_eq_zero_left hjac,
      inner_neg_left] at h

/-- The ODE for the normal component, in first-order form: for `j = ⟨J, E⟩`, `j' = ⟨D_t J, E⟩`
and `(⟨D_t J, E⟩)' = -K j`. -/
theorem jacobi_normal_hasDerivAt (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {γ : ℝ → M} {U : Set ℝ}
    (hunit : ∀ t ∈ U, ‖velocity I γ t‖ = 1) {e : (t : ℝ) → TangentSpace I (γ t)}
    (he : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ e U)
    (he1 : ∀ t ∈ U, ‖e t‖ = 1) (heγ : ∀ t ∈ U, inner ℝ (e t) (velocity I γ t) = (0 : ℝ))
    {J : (t : ℝ) → TangentSpace I (γ t)} (hJ : IsJacobiFieldOn I γ J U)
    (hJγ : ∀ t ∈ U, inner ℝ (J t) (velocity I γ t) = (0 : ℝ)) {t : ℝ} (ht : t ∈ U) :
    J t = inner ℝ (J t) (e t) • e t ∧
      HasDerivAt (fun s ↦ inner ℝ (J s) (e s))
        (inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J t) (e t)) t ∧
      HasDerivAt
        (fun s ↦ inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J s) (e s))
        (-(K * inner ℝ (J t) (e t))) t := by
  have hdec : J t = inner ℝ (J t) (e t) • e t :=
    eq_inner_smul_of_orthonormal_two (V := TangentSpace I (γ t)) hdim (hunit t ht) (he1 t ht)
      (heγ t ht) (hJγ t ht)
  obtain ⟨h1, h2⟩ := hJ.hasDerivAt_inner_parallel he ht
  refine ⟨hdec, h1, ?_⟩
  have hR : inner ℝ (riemannCurvature I (γ t) (J t) (velocity I γ t) (velocity I γ t)) (e t) =
      K * inner ℝ (J t) (e t) := by
    have hJe : riemannCurvature I (γ t) (J t) (velocity I γ t) (velocity I γ t) =
        riemannCurvature I (γ t) (inner ℝ (J t) (e t) • e t) (velocity I γ t)
          (velocity I γ t) := congrArg (fun w ↦ riemannCurvature I (γ t) w _ _) hdec
    rw [hJe, riemannCurvature_smul_left, real_inner_smul_left, hK (γ t) (e t) (velocity I γ t),
      he1 t ht, hunit t ht, heγ t ht]
    ring
  rwa [hR] at h2

/-- **C4.2.** In a two-dimensional Riemannian manifold of constant curvature `K`, let `γ` be a
unit-speed curve (a geodesic in the manuscript) on an open set `U`, `E` a parallel field along `γ`
with `|E| = 1` and `E ⟂ γ̇`, and `J` a Jacobi field along `γ` with `J ⟂ γ̇`. Then `J = j E` with
`j = ⟨J, E⟩`, and `j'' + K j = 0` on `U`. -/
theorem sec4_jacobi_normal_eq (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hunit : ∀ t ∈ U, ‖velocity I γ t‖ = 1) {e : (t : ℝ) → TangentSpace I (γ t)}
    (he : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ e U)
    (he1 : ∀ t ∈ U, ‖e t‖ = 1) (heγ : ∀ t ∈ U, inner ℝ (e t) (velocity I γ t) = (0 : ℝ))
    {J : (t : ℝ) → TangentSpace I (γ t)} (hJ : IsJacobiFieldOn I γ J U)
    (hJγ : ∀ t ∈ U, inner ℝ (J t) (velocity I γ t) = (0 : ℝ)) :
    (∀ t ∈ U, J t = inner ℝ (J t) (e t) • e t) ∧
      (∀ t ∈ U, DifferentiableAt ℝ (fun s ↦ inner ℝ (J s) (e s)) t) ∧
      ∀ t ∈ U, deriv (deriv fun s ↦ inner ℝ (J s) (e s)) t + K * inner ℝ (J t) (e t) = 0 := by
  have H := fun t (ht : t ∈ U) ↦
    jacobi_normal_hasDerivAt hdim hK hunit he he1 heγ hJ hJγ ht
  refine ⟨fun t ht ↦ (H t ht).1, fun t ht ↦ (H t ht).2.1.differentiableAt, fun t ht ↦ ?_⟩
  have hev : (deriv fun s ↦ inner ℝ (J s) (e s)) =ᶠ[𝓝 t]
      fun s ↦ inner ℝ (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J s) (e s) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (H s hs).2.1.deriv
  rw [hev.deriv_eq, (H t ht).2.2.deriv]
  ring

/-- **C3.1.** In a two-dimensional Riemannian manifold of curvature zero, with the notation of
`sec4_jacobi_normal_eq`, the normal component `j = ⟨J, E⟩` of the Jacobi field satisfies
`j'' = 0`. -/
theorem sec3_jacobi_flat (hdim : Module.finrank ℝ E = 2) (hK : HasConstSectionalCurvature I M 0)
    {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U) (hunit : ∀ t ∈ U, ‖velocity I γ t‖ = 1)
    {e : (t : ℝ) → TangentSpace I (γ t)}
    (he : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ e U)
    (he1 : ∀ t ∈ U, ‖e t‖ = 1) (heγ : ∀ t ∈ U, inner ℝ (e t) (velocity I γ t) = (0 : ℝ))
    {J : (t : ℝ) → TangentSpace I (γ t)} (hJ : IsJacobiFieldOn I γ J U)
    (hJγ : ∀ t ∈ U, inner ℝ (J t) (velocity I γ t) = (0 : ℝ)) :
    (∀ t ∈ U, J t = inner ℝ (J t) (e t) • e t) ∧
      ∀ t ∈ U, deriv (deriv fun s ↦ inner ℝ (J s) (e s)) t = 0 := by
  obtain ⟨h1, -, h3⟩ := sec4_jacobi_normal_eq hdim hK hU hunit he he1 heγ hJ hJγ
  exact ⟨h1, fun t ht ↦ by simpa using h3 t ht⟩

/-- **C4.4, geometric part, first half.** With the notation of `sec4_jacobi_normal_eq`, on an open
interval `U = (a, b)` containing `0`, if `J(0) = 0` and `D_t J(0) = E(0)`, then `J = S_K E` on `U`;
hence `|J| = |S_K|` there. -/
theorem sec4_jacobi_eq_S (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {γ : ℝ → M} {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (hunit : ∀ t ∈ Ioo a b, ‖velocity I γ t‖ = 1) {e : (t : ℝ) → TangentSpace I (γ t)}
    (he : IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ e (Ioo a b))
    (he1 : ∀ t ∈ Ioo a b, ‖e t‖ = 1)
    (heγ : ∀ t ∈ Ioo a b, inner ℝ (e t) (velocity I γ t) = (0 : ℝ))
    {J : (t : ℝ) → TangentSpace I (γ t)} (hJ : IsJacobiFieldOn I γ J (Ioo a b))
    (hJγ : ∀ t ∈ Ioo a b, inner ℝ (J t) (velocity I γ t) = (0 : ℝ)) (hJ0 : J 0 = 0)
    (hDJ0 : covAlong (CovariantDerivative.leviCivitaConnection I M) γ J 0 = e 0) :
    ∀ t ∈ Ioo a b, J t = S K t • e t ∧ ‖J t‖ = |S K t| := by
  have H := fun t (ht : t ∈ Ioo a b) ↦
    jacobi_normal_hasDerivAt hdim hK hunit he he1 heγ hJ hJγ ht
  have hS : EqOn (fun s ↦ inner ℝ (J s) (e s)) (S K) (Ioo a b) := by
    refine eqOn_S_of_ode (j' := fun s ↦ inner ℝ
        (covAlong (CovariantDerivative.leviCivitaConnection I M) γ J s) (e s))
      (j'' := fun s ↦ -(K * inner ℝ (J s) (e s))) h0 (fun r hr ↦ (H r hr).2.1)
      (fun r hr ↦ (H r hr).2.2) (fun r _ ↦ by ring) ?_ ?_
    · simp [hJ0]
    · simp only [hDJ0]
      rw [real_inner_self_eq_norm_sq, he1 0 h0]
      norm_num
  intro t ht
  have hJt : J t = S K t • e t := by
    rw [(H t ht).1]
    congr 1
    exact hS ht
  refine ⟨hJt, ?_⟩
  rw [hJt, norm_smul, he1 t ht, mul_one, Real.norm_eq_abs]

/-- **The parallel unit normal along a geodesic** used in C4.2 exists: in dimension two, along a
`C¹` geodesic `γ` on an open interval `U` with `|γ̇(t₀)| = 1`, the speed is `1` on `U`, and there is
a parallel field `E` along `γ` with `|E| = 1` and `E ⟂ γ̇` on `U`. -/
theorem exists_parallel_unit_normal (hdim : Module.finrank ℝ E = 2) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U)
    (hgeo : IsGeodesicOn I γ U) {t₀ : ℝ} (ht₀ : t₀ ∈ U) (hv : ‖velocity I γ t₀‖ = 1) :
    (∀ t ∈ U, ‖velocity I γ t‖ = 1) ∧
      ∃ e : (t : ℝ) → TangentSpace I (γ t),
        IsParallelAlongOn (CovariantDerivative.leviCivitaConnection I M) γ e U ∧
          (∀ t ∈ U, ‖e t‖ = 1) ∧ ∀ t ∈ U, inner ℝ (e t) (velocity I γ t) = (0 : ℝ) := by
  have hfact : Fact (Module.finrank ℝ (TangentSpace I (γ t₀)) = 2) := ⟨hdim⟩
  have : Module.Finite ℝ (TangentSpace I (γ t₀)) :=
    Module.finite_of_finrank_pos (by rw [hfact.out]; norm_num)
  let o : Orientation ℝ (TangentSpace I (γ t₀)) (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ (TangentSpace I (γ t₀)) hfact.out).orientation
  obtain ⟨e, he, he₀⟩ := exists_isParallelAlongOn hU hU' hγ ht₀ (Jrot o (velocity I γ t₀))
  have hJ := sec7_J_metric o (velocity I γ t₀)
  refine ⟨fun t ht ↦ (IsParallelAlongOn.norm_eq hU hU' hgeo ht₀ ht).trans hv, e, he,
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · rw [IsParallelAlongOn.norm_eq hU hU' he ht₀ ht, he₀, hJ.1, hv]
  · rw [IsParallelAlongOn.inner_eq hU hU' he hgeo ht₀ ht, he₀, hJ.2]

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- In the chart at any point, the canonical metric of a Euclidean space is the inner product. -/
lemma metricCoord_euclidean (x p w v : F) :
    metricCoord 𝓘(ℝ, F) x p w v = inner ℝ w v := by
  rw [metricCoord_apply, coordField, coordField, trivSection, trivSection,
    TangentBundle.symmL_model_space]
  rfl

/-- The Christoffel symbols of a Euclidean space vanish (in every chart of its atlas). -/
lemma christoffelL_euclidean (x p : F) : christoffelL 𝓘(ℝ, F) x p = 0 := by
  have hp : p ∈ (extChartAt 𝓘(ℝ, F) x).target := by simp
  have hG := differentiableAt_metricCoord (I := 𝓘(ℝ, F)) x hp
  have hD : ∀ a b c : F, fderiv ℝ (metricCoord 𝓘(ℝ, F) x) p a b c = 0 := by
    intro a b c
    rw [← fderiv_apply_apply hG a b c]
    have h : (fun q ↦ metricCoord 𝓘(ℝ, F) x q b c) = fun _ ↦ inner ℝ b c :=
      funext fun q ↦ metricCoord_euclidean x q b c
    rw [h, fderiv_const_apply, zero_apply]
  ext a b
  rw [christoffelL_apply, christoffel]
  have hlow : christoffelLow 𝓘(ℝ, F) x p a b = 0 := by
    ext c
    rw [christoffelLow_apply, hD, hD, hD, zero_apply]
    norm_num
  rw [hlow, map_zero, zero_apply, zero_apply]

/-- **A Euclidean space has curvature zero.** -/
theorem riemannCurvature_euclidean (x : F) (u v w : TangentSpace 𝓘(ℝ, F) x) :
    riemannCurvature 𝓘(ℝ, F) x u v w = 0 := by
  have hD : ∀ p a b c : F, christoffelDeriv 𝓘(ℝ, F) x p a b c = 0 := by
    intro p a b c
    have h : (fun q ↦ christoffelL 𝓘(ℝ, F) x q b c) = fun _ ↦ (0 : F) := by
      funext q
      rw [christoffelL_euclidean, zero_apply, zero_apply]
    rw [christoffelDeriv, h, fderiv_const_apply, zero_apply]
  rw [riemannCurvature, curvCoord, hD, hD, christoffelL_euclidean]
  simp only [zero_apply, sub_self, add_zero, map_zero]

/-- A Euclidean space has constant sectional curvature `0`. -/
theorem hasConstSectionalCurvature_euclidean : HasConstSectionalCurvature 𝓘(ℝ, F) F 0 := by
  intro x u v
  rw [riemannCurvature_euclidean, inner_zero_left, zero_mul]

/-- **C3.1 in the Euclidean plane**: the hypotheses of `sec3_jacobi_flat` on the curvature and the
dimension hold for the Euclidean plane `ℝ²` with its canonical metric. -/
theorem sec3_euclidean_plane_flat :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 ∧
      HasConstSectionalCurvature 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 0 :=
  ⟨finrank_euclideanSpace_fin, hasConstSectionalCurvature_euclidean⟩

end Euclidean

end PythagoreanPaper
