import PythagoreanPaper.Riemannian.ModelTriangles

/-!
# Geodesic triangles with prescribed sides in the model spaces (manuscript §9, C9.8)

In C9.8 the manuscript fixes the side lengths `a, b, c` and considers, for each curvature `K`,
"the geodesic triangle determined by `K`" with these sides, whose angles `A_K, B_K, C_K` tend to
the Euclidean angles as `K → 0`. This file constructs such triangles in the model spaces:

* `HypPlane.exists_triangle`: for `K < 0`, if `cos A_K = cosLaw K a b c ∈ (−1, 1)`, the hyperbolic
  plane of curvature `K` contains a geodesic triangle with sides `a, b, c`;
* `SphereModel.exists_triangle`: for `K > 0`, if moreover `√K a, √K b, √K c < π/2`, the sphere of
  curvature `K` contains a geodesic triangle with sides `a, b, c` lying in an open hemisphere.

`sec9_model_triangles` combines these with `sec9_limit`: for the sides of a nondegenerate
triangle, for every `K ≠ 0` near `0` the model space of curvature `K` contains a geodesic triangle
with sides `a, b, c` (in an open hemisphere if `K > 0`), its angles are `A_K, B_K, C_K`, and these
tend to the angles `A_0, B_0, C_0` of the Euclidean triangle, which satisfy the sine law.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology

namespace PythagoreanPaper

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- Rescaling the curvature parameter: `C_{κ s²}(t) = C_κ(s t)` for `s ≥ 0`. -/
lemma C_mul_sq (κ s t : ℝ) (hs : 0 ≤ s) : C (κ * s ^ 2) t = C κ (s * t) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [C_of_eq_zero]
  rcases lt_trichotomy κ 0 with hκ | rfl | hκ
  · have h : κ * s ^ 2 < 0 := mul_neg_of_neg_of_pos hκ (by positivity)
    rw [C_of_neg t h, C_of_neg _ hκ, show -(κ * s ^ 2) = -κ * s ^ 2 by ring,
      Real.sqrt_mul (neg_nonneg.2 hκ.le), Real.sqrt_sq hs.le, mul_assoc]
  · simp [C_of_eq_zero]
  · have h : 0 < κ * s ^ 2 := by positivity
    rw [C_of_pos t h, C_of_pos _ hκ, Real.sqrt_mul hκ.le, Real.sqrt_sq hs.le, mul_assoc]

/-- An orthonormal pair of `ℝ²`. -/
lemma exists_orthonormal_pair_R2 : ∃ e₁ e₂ : R2, ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  exact ⟨b 0, b 1, b.orthonormal.1 0, b.orthonormal.1 1, b.orthonormal.2 (by decide)⟩

/-- The unit vector at angle `θ` from `e₁` in the plane of the orthonormal pair `e₁, e₂`. -/
lemma unit_rotate {e₁ e₂ : R2} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = 0)
    (θ : ℝ) :
    ‖Real.cos θ • e₁ + Real.sin θ • e₂‖ = 1 ∧
      inner ℝ e₁ (Real.cos θ • e₁ + Real.sin θ • e₂) = Real.cos θ := by
  constructor
  · have h : ‖Real.cos θ • e₁ + Real.sin θ • e₂‖ ^ 2 = 1 := by
      rw [norm_comb_sq, h₁, h₂, h₁₂]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have h0 := norm_nonneg (Real.cos θ • e₁ + Real.sin θ • e₂)
    nlinarith
  · rw [inner_left_comb, h₁, h₁₂]; ring

/-! ### The hyperbolic plane -/

namespace HypPlane

variable {K : ℝ} [hK : Fact (K < 0)]

lemma norm_velocity_geoCurve (p v : R2) (t : ℝ) :
    ‖velocity 𝓘(ℝ, R2) (geoCurve K p v) t‖ = √(gH K p v v) := by
  have h1 : ‖velocity 𝓘(ℝ, R2) (geoCurve K p v) t‖ =
      √(gH K (geo K p v t) (velocity 𝓘(ℝ, R2) (geoCurve K p v) t)
        (velocity 𝓘(ℝ, R2) (geoCurve K p v) t)) :=
    norm_tangent_eq (geoCurve K p v t) _
  rw [h1, velocity_geoCurve, gH_geo']

omit hK in
lemma gH_zero (w : R2) : gH K 0 w w = ‖w‖ ^ 2 := by
  rw [gH_apply, real_inner_self_eq_norm_sq]; simp

omit hK in
lemma kap_zero_unit {e : R2} (he : ‖e‖ = 1) : kap K 0 e = K := by
  rw [kap, gH_zero, he]; ring

omit hK in
lemma geo_zero_unit {e : R2} (he : ‖e‖ = 1) (t : ℝ) : geo K 0 e t = S K t • e := by
  rw [geo, kap_zero_unit he, smul_zero, zero_add]

/-- A unit-speed geodesic segment from the origin. -/
lemma isGeodesicSegment_origin {e : R2} (he : ‖e‖ = 1) {L : ℝ} (hL : 0 < L) :
    IsGeodesicSegment 𝓘(ℝ, R2) (geoCurve K 0 e) (pt K 0) (geoCurve K 0 e L) L where
  pos := hL
  exists_Ioo := ⟨-1, L + 1, by norm_num, by linarith,
    (isGeodesicOn_geoCurve 0 e).mono (subset_univ _)⟩
  unit := by rw [norm_velocity_geoCurve, gH_zero, he, one_pow, Real.sqrt_one]
  apply_zero := Subtype.ext (geo_zero 0 e)
  apply_length := rfl

/-- `√N(s e) = C_K(s)` for a unit vector `e`. -/
lemma sqrt_N_smul_unit {e : R2} (he : ‖e‖ = 1) (s : ℝ) : √(N K (S K s • e)) = C K s := by
  have hC := C_pos_of_nonpos hK.out.le s
  have h : N K (S K s • e) = C K s ^ 2 := by
    rw [N, norm_smul, mul_pow, he, Real.norm_eq_abs, sq_abs]
    linarith [C_sq_add_mul_S_sq K s]
  rw [h, Real.sqrt_sq hC.le]

/-- **Existence of hyperbolic triangles with prescribed sides**: for `K < 0` and sides
`a, b, c > 0` with `cosLaw K a b c ∈ (−1, 1)`, the hyperbolic plane of curvature `K` contains a
geodesic triangle with sides `a, b, c`. (It is built with the vertex `A` at the origin and the angle
`A_K = angleK K a b c` there; the third side has length `a` by the Lorentz pairing `F`.) -/
theorem exists_triangle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcos : cosLaw K a b c ∈ Ioo (-1 : ℝ) 1) :
    ∃ T : GeodesicTriangle 𝓘(ℝ, R2) (hypPlane K), T.a = a ∧ T.b = b ∧ T.c = c := by
  have hK' := hK.out
  have hK0 : K ≠ 0 := hK'.ne
  obtain ⟨e₁, e₂, h₁, h₂, h₁₂⟩ := exists_orthonormal_pair_R2
  set θ := angleK K a b c with hθ
  set d := Real.cos θ • e₁ + Real.sin θ • e₂ with hd_def
  obtain ⟨hd, hed⟩ := unit_rotate h₁ h₂ h₁₂ θ
  have segc := isGeodesicSegment_origin (K := K) h₁ hc
  have segτ := isGeodesicSegment_origin (K := K) hd hb
  set B := geoCurve K 0 e₁ c with hB
  set C' := geoCurve K 0 d b with hC'
  -- the Lorentz pairing of `B` and `C'` is `C_K(a)`
  have hF : F K B C' = C K a := by
    have hBc : (B : R2) = S K c • e₁ := geo_zero_unit h₁ c
    have hCc : (C' : R2) = S K b • d := geo_zero_unit hd b
    have hcosθ : Real.cos θ = cosLaw K a b c := Real.cos_arccos hcos.1.le hcos.2.le
    have hlaw := cos_law_angleK hK0 (S_pos_of_nonpos hK'.le hb).ne'
      (S_pos_of_nonpos hK'.le hc).ne' hcos
    rw [F, hBc, hCc, sqrt_N_smul_unit h₁, sqrt_N_smul_unit hd, real_inner_smul_left,
      real_inner_smul_right, hed, hcosθ, hlaw, ← hθ, hcosθ]
    ring
  -- the third side
  obtain ⟨v, -, hv⟩ := exists_expMap_eq B C'
  have hgeo : geo K B v 1 = (C' : R2) :=
    congrArg Subtype.val ((expMap_eq B v).2.symm.trans hv)
  have hkap : kap K B v = K * a ^ 2 := by
    refine C_one_injOn (kap_nonpos (K := K) (B : R2) v)
      (mul_nonpos_of_nonpos_of_nonneg hK'.le (sq_nonneg a)) ?_
    show C (kap K B v) 1 = C (K * a ^ 2) 1
    rw [← F_geo, hgeo, hF, C_mul_sq _ _ _ ha.le, mul_one]
  have hL : gH K B v v = a ^ 2 := mul_left_cancel₀ hK0 hkap
  set u : R2 := a⁻¹ • v with hu
  have hgu : gH K B u u = 1 := by
    rw [hu, gH_smul, hL, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')]
  have sega : IsGeodesicSegment 𝓘(ℝ, R2) (geoCurve K B u) B C' a :=
    { pos := ha
      exists_Ioo := ⟨-1, a + 1, by norm_num, by linarith,
        (isGeodesicOn_geoCurve (B : R2) u).mono (subset_univ _)⟩
      unit := by rw [norm_velocity_geoCurve, hgu, Real.sqrt_one]
      apply_zero := Subtype.ext (geo_zero (B : R2) u)
      apply_length := by
        have h := (expMap_smul (t := a) (isGeodesicFrom_geoCurve B u) (subset_univ _)).2
        rw [hu, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hv] at h
        exact h.symm }
  exact ⟨⟨pt K 0, B, C', a, b, c, geoCurve K B u, _, geoCurve K 0 e₁, sega, segτ.reverse,
    segc⟩, rfl, rfl, rfl⟩

end HypPlane

/-! ### The sphere -/

namespace SphereModel

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : ℝ}

/-- A point of the sphere. -/
def basePt (K : ℝ) : sph K :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    show _ ∈ Metric.sphere (0 : E3) 1
    rw [mem_sphere_zero_iff_norm]; exact (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0⟩

/-- **The geodesics from `x₀` in `ℝ³` are great circles**:
`gC x₀ v t = C_{‖v‖²}(t) x₀ + S_{‖v‖²}(t) ι(v)` for `‖v‖ |t| < π`. -/
lemma coe_gC (x₀ : sph K) (v : R2) {t : ℝ} (ht : t ∈ J v) :
    ((gC x₀ v t : sph K) : E3) = C (‖v‖ ^ 2) t • (x₀ : E3) + S (‖v‖ ^ 2) t • ι x₀ v := by
  rw [gC, chartAt_symm_eq, Φ, cS]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [C_of_eq_zero]
  · have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hr0 : ‖v‖ ≠ 0 := hr.ne'
    have hcα := (cos_pos_of_mem_J ht).ne'
    have hK2 : 0 < ‖v‖ ^ 2 := by positivity
    rw [C_of_pos t hK2, S_of_pos t hK2, Real.sqrt_sq hr.le, map_smul, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, Tn, Real.tan_eq_sin_div_cos]
    set α := ‖v‖ * t / 2 with hα
    have h2 : ‖v‖ * t = 2 * α := by rw [hα]; ring
    rw [h2, Real.cos_two_mul, Real.sin_two_mul]
    have hsc := Real.sin_sq_add_cos_sq α
    match_scalars
    · field_simp
      linear_combination (-4 * Real.sin α) * hsc
    · field_simp
      linear_combination (-8 * Real.cos α ^ 2) * hsc

variable [hK : Fact (0 < K)]

lemma norm_tangent_of_eq (x : sph K) (w : TangentSpace 𝓘(ℝ, R2) x) (v : R2) (h : w = v) :
    ‖w‖ = ‖v‖ / √K := by
  subst h; exact norm_tangent_eq x w

lemma Ioo_subset_J {u : R2} (hu : ‖u‖ = √K) : Ioo (-(Real.pi / √K)) (Real.pi / √K) ⊆ J u := by
  intro t ht
  show ‖u‖ * |t| < Real.pi
  have hs := Real.sqrt_pos.2 hK.out
  have h : |t| < Real.pi / √K := abs_lt.2 ⟨ht.1, ht.2⟩
  rw [hu]
  calc √K * |t| < √K * (Real.pi / √K) := mul_lt_mul_of_pos_left h hs
    _ = Real.pi := by field_simp

omit hK in
lemma mem_J_of {u : R2} (hu : ‖u‖ = √K) {t : ℝ} (ht : √K * |t| < Real.pi) : t ∈ J u := by
  show ‖u‖ * |t| < Real.pi
  rw [hu]; exact ht

/-- A unit-speed geodesic segment from `x₀` (chart velocity `u`, `‖u‖ = √K`) of length
`L < π/√K`. -/
lemma isGeodesicSegment_gC (x₀ : sph K) {u : R2} (hu : ‖u‖ = √K) {L : ℝ} (hL : 0 < L)
    (hLπ : √K * L < Real.pi) :
    IsGeodesicSegment 𝓘(ℝ, R2) (gC x₀ u) x₀ (gC x₀ u L) L where
  pos := hL
  exists_Ioo := by
    have hs := Real.sqrt_pos.2 hK.out
    refine ⟨-(Real.pi / √K), Real.pi / √K, by have := div_pos Real.pi_pos hs; linarith, ?_,
      (isGeodesicOn_gC x₀ u).mono (Ioo_subset_J hu)⟩
    rw [lt_div_iff₀ hs]; linarith [mul_comm L √K]
  unit := by
    rw [norm_tangent_of_eq _ _ u (isGeodesicFrom_gC x₀ u).velocity_zero, hu,
      div_self (Real.sqrt_pos.2 hK.out).ne']
  apply_zero := gC_zero x₀ u
  apply_length := rfl

lemma C_K_eq (t : ℝ) : C K t = Real.cos (√K * t) := C_of_pos t hK.out

lemma inner_coe_gC_self (x₀ : sph K) {u : R2} (hu : ‖u‖ = √K) {t : ℝ} (ht : t ∈ J u) :
    inner ℝ ((gC x₀ u t : sph K) : E3) (x₀ : E3) = Real.cos (√K * t) := by
  rw [coe_gC x₀ u ht, hu, Real.sq_sqrt hK.out.le, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, norm_coe, inner_ι_self', C_K_eq]
  ring

lemma cos_pos_of_lt {x : ℝ} (h0 : 0 ≤ x) (h : x < Real.pi / 2) : 0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩

/-- **Existence of spherical triangles with prescribed sides**: for `K > 0` and sides
`a, b, c > 0` with `√K a, √K b, √K c < π/2` and `cosLaw K a b c ∈ (−1, 1)`, the sphere of
curvature `K` contains a geodesic triangle with sides `a, b, c` lying in an open hemisphere.
(It is built with the vertex `A` at a point `x₀` and the angle `A_K = angleK K a b c` there; the
third side has length `a` by the inner product of `ℝ³`.) -/
theorem exists_triangle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsa : √K * a < Real.pi / 2) (hsb : √K * b < Real.pi / 2) (hsc : √K * c < Real.pi / 2)
    (hcos : cosLaw K a b c ∈ Ioo (-1 : ℝ) 1) :
    ∃ T : GeodesicTriangle 𝓘(ℝ, R2) (sph K), InOpenHemisphere T ∧ T.a = a ∧ T.b = b ∧
      T.c = c := by
  have hK' := hK.out
  have hK0 : K ≠ 0 := hK'.ne'
  have hs : 0 < √K := Real.sqrt_pos.2 hK'
  have hpi := Real.pi_pos
  obtain ⟨e₁, e₂, h₁, h₂, h₁₂⟩ := exists_orthonormal_pair_R2
  set θ := angleK K a b c with hθ
  set d := Real.cos θ • e₁ + Real.sin θ • e₂ with hd_def
  obtain ⟨hd, hed⟩ := unit_rotate h₁ h₂ h₁₂ θ
  set x₀ := basePt K
  set u₁ : R2 := √K • e₁ with hu₁_def
  set u₂ : R2 := √K • d with hu₂_def
  have hu₁ : ‖u₁‖ = √K := by rw [norm_smul, Real.norm_of_nonneg hs.le, h₁, mul_one]
  have hu₂ : ‖u₂‖ = √K := by rw [norm_smul, Real.norm_of_nonneg hs.le, hd, mul_one]
  have hcπ : √K * c < Real.pi := by linarith
  have hbπ : √K * b < Real.pi := by linarith
  have haπ : √K * a < Real.pi := by linarith
  have segc := isGeodesicSegment_gC x₀ hu₁ hc hcπ
  have segτ := isGeodesicSegment_gC x₀ hu₂ hb hbπ
  set B := gC x₀ u₁ c with hB
  set C' := gC x₀ u₂ b with hC'
  have hcJ : c ∈ J u₁ := mem_J_of hu₁ (by rwa [abs_of_pos hc])
  have hbJ : b ∈ J u₂ := mem_J_of hu₂ (by rwa [abs_of_pos hb])
  -- the inner product of `B` and `C'` in `ℝ³` is `C_K(a)`
  have hbK : b < Real.pi / √K := by rw [lt_div_iff₀ hs]; linarith [mul_comm b √K]
  have hcK : c < Real.pi / √K := by rw [lt_div_iff₀ hs]; linarith [mul_comm c √K]
  have hBC : inner ℝ (B : E3) (C' : E3) = C K a := by
    have hu12 : inner ℝ u₁ u₂ = K * Real.cos θ := by
      rw [hu₁_def, hu₂_def, real_inner_smul_left, real_inner_smul_right, hed, ← mul_assoc,
        Real.mul_self_sqrt hK'.le]
    have hcosθ : Real.cos θ = cosLaw K a b c := Real.cos_arccos hcos.1.le hcos.2.le
    have hlaw := cos_law_angleK hK0 (S_pos hK' hb hbK).ne' (S_pos hK' hc hcK).ne' hcos
    rw [coe_gC x₀ u₁ hcJ, coe_gC x₀ u₂ hbJ, hu₁, hu₂, Real.sq_sqrt hK'.le]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_coe, inner_ι_self, inner_ι_self', inner_ι]
    rw [hu12, hlaw, ← hθ, hcosθ]
    ring
  -- `C'` is not the antipode of `B`
  have hCa : 0 < C K a := by rw [C_K_eq]; exact cos_pos_of_lt (by positivity) hsa
  have hne : (C' : E3) ≠ -(B : E3) := by
    intro h
    have h1 : inner ℝ (B : E3) (C' : E3) = -1 := by
      rw [h, inner_neg_right, real_inner_self_eq_norm_sq, norm_coe]; ring
    linarith
  obtain ⟨v, hvball, hv⟩ := mem_expMap_image_of_ne B C' hne
  rw [mem_tangentBall_iff] at hvball
  have hvJ : (1 : ℝ) ∈ J v := by
    show ‖v‖ * |(1 : ℝ)| < Real.pi
    rw [abs_one, mul_one]; exact hvball
  have hcoe : (C' : E3) = C (‖v‖ ^ 2) 1 • (B : E3) + S (‖v‖ ^ 2) 1 • ι B v := by
    rw [← hv, (expMap_eq B hvball).2, coe_gC B v hvJ]
  -- the length of the third side is `a`
  have hnv : ‖v‖ = √K * a := by
    have h1 : inner ℝ (B : E3) (C' : E3) = Real.cos ‖v‖ := by
      rw [hcoe, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_coe, inner_ι_self, mul_zero, add_zero, one_pow,
        mul_one]
      rcases eq_or_ne v 0 with h0 | h0
      · simp [h0, C_of_eq_zero]
      · rw [C_of_pos 1 (by positivity), Real.sqrt_sq (norm_nonneg v), mul_one]
    rw [hBC, C_K_eq] at h1
    exact Real.injOn_cos ⟨norm_nonneg v, hvball.le⟩ ⟨by positivity, haπ.le⟩ h1.symm
  -- the third side, from `B` to `C'`
  set u : R2 := a⁻¹ • v with hu_def
  have hu : ‖u‖ = √K := by
    rw [hu_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le), hnv]; field_simp
  have sega0 := isGeodesicSegment_gC B hu ha haπ
  have hσa : gC B u a = C' := by
    have hJ : uIcc 0 a ⊆ J u := by
      rw [uIcc_of_le ha.le]
      intro t ht
      refine mem_J_of hu ?_
      rw [abs_of_nonneg ht.1]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hs.le) haπ
    have h := (expMap_smul (t := a) (isGeodesicFrom_gC B u) hJ).2
    rw [hu_def, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hv] at h
    exact h.symm
  rw [hσa] at sega0
  refine ⟨⟨x₀, B, C', a, b, c, gC B u, _, gC x₀ u₁, sega0, segτ.reverse, segc⟩, ?_, rfl, rfl,
    rfl⟩
  -- the three sides lie in the open hemisphere around `x₀`
  have hβ : inner ℝ (B : E3) (x₀ : E3) = Real.cos (√K * c) := inner_coe_gC_self x₀ hu₁ hcJ
  have hγ : inner ℝ (C' : E3) (x₀ : E3) = Real.cos (√K * b) := inner_coe_gC_self x₀ hu₂ hbJ
  have hβpos : 0 < Real.cos (√K * c) := cos_pos_of_lt (by positivity) hsc
  have hγpos : 0 < Real.cos (√K * b) := cos_pos_of_lt (by positivity) hsb
  refine ⟨(x₀ : E3), ?_, ?_, ?_⟩
  · -- the side `a`: a positive combination of `B` and `C'`
    intro t ht
    show 0 < inner ℝ ((gC B u t : sph K) : E3) (x₀ : E3)
    have htJ : t ∈ J u := mem_J_of hu (by
      rw [abs_of_nonneg ht.1]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hs.le) haπ)
    have haJ : a ∈ J u := mem_J_of hu (by rwa [abs_of_pos ha])
    have hCa' : (C' : E3) = C K a • (B : E3) + S K a • ι B u := by
      rw [← hσa, coe_gC B u haJ, hu, Real.sq_sqrt hK'.le]
    set δ := inner ℝ (ι B u) (x₀ : E3)
    have hγ' : Real.cos (√K * b) = Real.cos (√K * a) * Real.cos (√K * c) +
        Real.sin (√K * a) / √K * δ := by
      rw [← hγ, ← hβ, hCa', inner_add_left, real_inner_smul_left, real_inner_smul_left,
        C_K_eq, S_of_pos a hK']
    have hval : inner ℝ ((gC B u t : sph K) : E3) (x₀ : E3) =
        Real.cos (√K * t) * Real.cos (√K * c) + Real.sin (√K * t) / √K * δ := by
      rw [coe_gC B u htJ, hu, Real.sq_sqrt hK'.le, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hβ, C_K_eq, S_of_pos t hK']
    have hsinA : 0 < Real.sin (√K * a) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) haπ
    have hkey : inner ℝ ((gC B u t : sph K) : E3) (x₀ : E3) * Real.sin (√K * a) =
        Real.cos (√K * c) * Real.sin (√K * a - √K * t) +
          Real.cos (√K * b) * Real.sin (√K * t) := by
      rw [hval, hγ', Real.sin_sub]
      field_simp
      ring
    have hp0 : 0 ≤ √K * t := mul_nonneg hs.le ht.1
    have hpa : √K * t ≤ √K * a := mul_le_mul_of_nonneg_left ht.2 hs.le
    have hs1 : 0 ≤ Real.sin (√K * a - √K * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hs2 : 0 ≤ Real.sin (√K * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hp0 (by linarith)
    have hsum : 0 < Real.cos (√K * c) * Real.sin (√K * a - √K * t) +
        Real.cos (√K * b) * Real.sin (√K * t) := by
      rcases hp0.eq_or_lt with h0 | h0
      · rw [← h0, sub_zero, Real.sin_zero, mul_zero, add_zero]
        exact mul_pos hβpos hsinA
      · have := mul_pos hγpos (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith))
        nlinarith [mul_nonneg hβpos.le hs1]
    rw [← hkey] at hsum
    exact pos_of_mul_pos_left hsum hsinA.le
  · -- the side `b`, the reverse of a radial segment
    intro t ht
    show 0 < inner ℝ ((gC x₀ u₂ (-1 * t + b) : sph K) : E3) (x₀ : E3)
    have h0 : 0 ≤ -1 * t + b := by linarith [ht.2]
    have h1 : -1 * t + b ≤ b := by linarith [ht.1]
    rw [inner_coe_gC_self x₀ hu₂ (mem_J_of hu₂ (by
      rw [abs_of_nonneg h0]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hs.le) hbπ))]
    exact cos_pos_of_lt (mul_nonneg hs.le h0)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hs.le) hsb)
  · -- the side `c`, a radial segment
    intro t ht
    show 0 < inner ℝ ((gC x₀ u₁ t : sph K) : E3) (x₀ : E3)
    rw [inner_coe_gC_self x₀ hu₁ (mem_J_of hu₁ (by
      rw [abs_of_nonneg ht.1]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hs.le) hcπ))]
    exact cos_pos_of_lt (mul_nonneg hs.le ht.1)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 hs.le) hsc)

end SphereModel

/-- `cos A_K ∈ (−1, 1)` for `K` near `0`, for the sides of a nondegenerate triangle. -/
lemma eventually_cosLaw_mem_Ioo {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    ∀ᶠ K in 𝓝 (0 : ℝ), cosLaw K a b c ∈ Ioo (-1 : ℝ) 1 := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hm := cosLaw_zero_mem_Ioo hb hc h1 h2 h3
  exact (continuousAt_cosLaw h0 a b c (by simpa [S_of_eq_zero] using (mul_pos hb hc).ne')).tendsto
    |>.eventually (Ioo_mem_nhds (by simpa using hm.1) (by simpa using hm.2))

/-- `√K x < π/2` for `K` near `0`. -/
lemma eventually_sqrt_mul_lt (x : ℝ) : ∀ᶠ K in 𝓝 (0 : ℝ), √K * x < Real.pi / 2 := by
  have h : Tendsto (fun K : ℝ ↦ √K * x) (𝓝 0) (𝓝 (√0 * x)) :=
    (Real.continuous_sqrt.tendsto 0).mul_const x
  rw [Real.sqrt_zero, zero_mul] at h
  exact h.eventually (gt_mem_nhds (by positivity))

/-- **C9.8 in the model spaces.** Fix the sides `a, b, c` of a nondegenerate triangle. For every
`K < 0` near `0`, the hyperbolic plane of curvature `K` contains a geodesic triangle with sides
`a, b, c`; for every `K > 0` near `0`, the sphere of curvature `K` contains a geodesic triangle with
sides `a, b, c` lying in an open hemisphere. The angles of these triangles are
`A_K = angleK K a b c`, `B_K = angleK K b c a`, `C_K = angleK K c a b`; these tend to `A_0, B_0, C_0`
as `K → 0`, and `sin A_0 / a = sin B_0 / b = sin C_0 / c` (`sec9_limit`; `A_0, B_0, C_0` are the
angles of the Euclidean triangle with sides `a, b, c`, `angleK_zero_eq_angle`). -/
theorem sec9_model_triangles {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    (∀ᶠ K in 𝓝[<] (0 : ℝ), ∀ [Fact (K < 0)], ∃ T : GeodesicTriangle 𝓘(ℝ, R2) (hypPlane K),
      T.a = a ∧ T.b = b ∧ T.c = c ∧ T.angleA = angleK K a b c ∧ T.angleB = angleK K b c a ∧
        T.angleC = angleK K c a b) ∧
    (∀ᶠ K in 𝓝[>] (0 : ℝ), ∀ [Fact (0 < K)],
      ∃ T : GeodesicTriangle 𝓘(ℝ, R2) (SphereModel.sph K), SphereModel.InOpenHemisphere T ∧
        T.a = a ∧ T.b = b ∧ T.c = c ∧ T.angleA = angleK K a b c ∧ T.angleB = angleK K b c a ∧
          T.angleC = angleK K c a b) ∧
    Tendsto (fun K => angleK K a b c) (𝓝 0) (𝓝 (angleK 0 a b c)) ∧
    Tendsto (fun K => angleK K b c a) (𝓝 0) (𝓝 (angleK 0 b c a)) ∧
    Tendsto (fun K => angleK K c a b) (𝓝 0) (𝓝 (angleK 0 c a b)) ∧
    (Real.sin (angleK 0 a b c) / a = Real.sin (angleK 0 b c a) / b ∧
      Real.sin (angleK 0 b c a) / b = Real.sin (angleK 0 c a b) / c) := by
  obtain ⟨-, hlimA, hlimB, hlimC, hsine⟩ := sec9_limit ha hb hc h1 h2 h3
  have hcos := eventually_cosLaw_mem_Ioo hb hc h1 h2 h3
  refine ⟨?_, ?_, hlimA, hlimB, hlimC, hsine⟩
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hcos] with K hK _
    obtain ⟨T, hTa, hTb, hTc⟩ := HypPlane.exists_triangle ha hb hc hK
    obtain ⟨hA, hB, hC⟩ := HypPlane.angles_eq_angleK T
    rw [hTa, hTb, hTc] at hA hB hC
    exact ⟨T, hTa, hTb, hTc, hA, hB, hC⟩
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hcos,
      mem_nhdsWithin_of_mem_nhds (eventually_sqrt_mul_lt a),
      mem_nhdsWithin_of_mem_nhds (eventually_sqrt_mul_lt b),
      mem_nhdsWithin_of_mem_nhds (eventually_sqrt_mul_lt c)] with K hK hsa hsb hsc hKpos
    obtain ⟨T, hT, hTa, hTb, hTc⟩ := SphereModel.exists_triangle ha hb hc hsa hsb hsc hK
    have hs : 0 < √K := Real.sqrt_pos.2 hKpos.out
    have hlt : ∀ x : ℝ, √K * x < Real.pi / 2 → x < Real.pi / √K := fun x hx ↦ by
      rw [lt_div_iff₀ hs]; nlinarith [Real.pi_pos]
    obtain ⟨hA, hB, hC⟩ := SphereModel.angles_eq_angleK T hT
      ⟨hTa ▸ hlt a hsa, hTb ▸ hlt b hsb, hTc ▸ hlt c hsc⟩
    rw [hTa, hTb, hTc] at hA hB hC
    exact ⟨T, hT, hTa, hTb, hTc, hA, hB, hC⟩

end PythagoreanPaper
