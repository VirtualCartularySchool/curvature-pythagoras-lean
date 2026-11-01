import PythagoreanPaper.Riemannian.CosineLaw
import PythagoreanPaper.Sec09

/-!
# Geodesic triangles (manuscript §9)

A geodesic triangle is given by three vertices and three selected geodesic segments between them
(`GeodesicTriangle`). Its side lengths are the lengths of the segments, and its angle at a vertex
is the angle between the initial velocities of the two segments leaving that vertex.

The theorems below assume the **technical condition** `GeodesicTriangle.SidesInNormalBalls`: for
each vertex, some normal ball around it (the image of a ball of the tangent space on which the
exponential map is a diffeomorphism) contains the three sides. It is the condition under which the
cosine law in a normal ball (`cosine_law_normalBall'`) applies to the triangle. It is a sufficient
condition used for the proofs, **not** the manuscript's definition of a convex geodesic triangle:
how the manuscript's convexity is to be formalized is left open (review of 2026-10-31). Where the
manuscript assumes `0 < a, b, c < π/√K` for `K > 0`, that hypothesis is kept separately.

* `GeodesicTriangle.cosine_law`: the three cosine laws
  `C_K(c) = C_K(a) C_K(b) + K S_K(a) S_K(b) cos C` etc. (C9.3 under the technical condition);
* `GeodesicTriangle.angle_pos_lt_pi`: a nondegenerate triangle (no vertex lies on the opposite
  side) has its angles in `(0, π)` (C9.7);
* `GeodesicTriangle.sine_law`: `sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)` for `K ≠ 0`
  (C9.1);
* `GeodesicTriangle.angleA_eq_angleK` etc.: for `K ≠ 0` the angles are the angles `A_K` given by
  the cosine law (C9.8).
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

section Segment

variable (I) in
/-- `γ` is a **geodesic segment** from `x` to `y` of length `L > 0`: a unit-speed geodesic with
`γ(0) = x` and `γ(L) = y`, given as a geodesic on an open interval containing `[0, L]`. -/
structure IsGeodesicSegment (γ : ℝ → M) (x y : M) (L : ℝ) : Prop where
  pos : 0 < L
  exists_Ioo : ∃ α β : ℝ, α < 0 ∧ L < β ∧ IsGeodesicOn I γ (Ioo α β)
  unit : ‖velocity I γ 0‖ = 1
  apply_zero : γ 0 = x
  apply_length : γ L = y

namespace IsGeodesicSegment

variable {γ : ℝ → M} {x y : M} {L : ℝ}

omit [I.Boundaryless] [T2Space M] in
/-- A geodesic segment is a geodesic from its initial point, on an open interval containing
`[0, L]`. -/
lemma exists_isGeodesicFrom (h : IsGeodesicSegment I γ x y L) :
    ∃ U : Set ℝ, IsGeodesicFrom I x (velocity I γ 0 : E) γ U ∧ Icc 0 L ⊆ U := by
  obtain ⟨α, β, hα, hβ, hγ⟩ := h.exists_Ioo
  exact ⟨Ioo α β, ⟨isOpen_Ioo, isPreconnected_Ioo, ⟨hα, by linarith [h.pos]⟩, hγ, h.apply_zero,
    rfl⟩, fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

omit [T2Space M] in
/-- A geodesic segment has unit speed on `[0, L]`. -/
lemma norm_velocity (h : IsGeodesicSegment I γ x y L) {t : ℝ} (ht : t ∈ Icc 0 L) :
    ‖velocity I γ t‖ = 1 := by
  obtain ⟨α, β, hα, hβ, hγ⟩ := h.exists_Ioo
  rw [IsParallelAlongOn.norm_eq isOpen_Ioo isPreconnected_Ioo hγ
    (⟨hα, by linarith [h.pos]⟩ : (0 : ℝ) ∈ Ioo α β)
    (⟨by linarith [ht.1], by linarith [ht.2]⟩ : t ∈ Ioo α β), h.unit]

omit [I.Boundaryless] [T2Space M] in
/-- The initial velocity of a geodesic segment is a unit vector of `T_x M`. -/
lemma norm_velocity_zero (h : IsGeodesicSegment I γ x y L) :
    ‖(show TangentSpace I x from (velocity I γ 0 : E))‖ = 1 :=
  (norm_transport (I := I) h.apply_zero _).symm.trans h.unit

omit [T2Space M] in
/-- The final velocity of a geodesic segment is a unit vector of `T_y M`. -/
lemma norm_velocity_length (h : IsGeodesicSegment I γ x y L) :
    ‖(show TangentSpace I y from (velocity I γ L : E))‖ = 1 :=
  (norm_transport (I := I) h.apply_length _).symm.trans (h.norm_velocity ⟨h.pos.le, le_rfl⟩)

omit [I.Boundaryless] [T2Space M] in
lemma mdifferentiableAt (h : IsGeodesicSegment I γ x y L) {t : ℝ} (ht : t ∈ Icc 0 L) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
  obtain ⟨α, β, hα, hβ, hγ⟩ := h.exists_Ioo
  exact hγ.mdifferentiableAt ⟨by linarith [ht.1], by linarith [ht.2]⟩

omit [T2Space M] in
/-- The reverse `t ↦ γ(L - t)` of a geodesic segment from `x` to `y` is a geodesic segment from
`y` to `x`. -/
lemma reverse (h : IsGeodesicSegment I γ x y L) :
    IsGeodesicSegment I (fun t ↦ γ (-1 * t + L)) y x L where
  pos := h.pos
  exists_Ioo := by
    obtain ⟨α, β, hα, hβ, hγ⟩ := h.exists_Ioo
    refine ⟨L - β, L - α, by linarith, by linarith, ?_⟩
    have h1 := hγ.comp_affine isOpen_Ioo (-1) L
    have h2 : (fun t ↦ -1 * t + L) ⁻¹' Ioo α β = Ioo (L - β) (L - α) := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rwa [h2] at h1
  unit := by
    rw [norm_velocity_congr (c₂ := fun t ↦ γ (-1 * t + L)) Filter.EventuallyEq.rfl]
    have h1 : (velocity I (fun t ↦ γ (-1 * t + L)) 0 : E) = (-1 : ℝ) • (velocity I γ (-1 * 0 + L) : E) :=
      velocity_comp_affine (by simpa using h.mdifferentiableAt ⟨h.pos.le, le_rfl⟩)
    have h2 : ‖velocity I (fun t ↦ γ (-1 * t + L)) 0‖ = ‖velocity I γ (-1 * 0 + L)‖ := by
      show ‖(show TangentSpace I (γ (-1 * 0 + L)) from (velocity I (fun t ↦ γ (-1 * t + L)) 0 : E))‖ = _
      rw [h1]
      show ‖(-1 : ℝ) • velocity I γ (-1 * 0 + L)‖ = _
      rw [norm_smul]
      norm_num
    rw [h2, congrArg (fun s ↦ ‖velocity I γ s‖) (by ring : -1 * 0 + L = L)]
    exact h.norm_velocity ⟨h.pos.le, le_rfl⟩
  apply_zero := by simpa using h.apply_length
  apply_length := by simpa using h.apply_zero

omit [I.Boundaryless] [T2Space M] in
lemma velocity_reverse_zero (h : IsGeodesicSegment I γ x y L) :
    (velocity I (fun t ↦ γ (-1 * t + L)) 0 : E) = -(show E from velocity I γ L) := by
  rw [velocity_comp_affine (by simpa using h.mdifferentiableAt ⟨h.pos.le, le_rfl⟩),
    congrArg (fun s ↦ (-1 : ℝ) • (velocity I γ s : E)) (by ring : -1 * 0 + L = L), neg_one_smul]
  rfl

omit [I.Boundaryless] [T2Space M] in
lemma velocity_reverse_length (h : IsGeodesicSegment I γ x y L) :
    (velocity I (fun t ↦ γ (-1 * t + L)) L : E) = -(show E from velocity I γ 0) := by
  rw [velocity_comp_affine (by simpa using h.mdifferentiableAt ⟨le_rfl, h.pos.le⟩),
    congrArg (fun s ↦ (-1 : ℝ) • (velocity I γ s : E)) (by ring : -1 * L + L = 0), neg_one_smul]
  rfl

end IsGeodesicSegment

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
lemma smul_mem_tangentBall_iff {p : M} {v : E} {s ρ : ℝ} (hs : 0 ≤ s) :
    s • v ∈ tangentBall I p ρ ↔ s * ‖(show TangentSpace I p from v)‖ < ρ := by
  show ‖(show TangentSpace I p from (s • v : E))‖ < ρ ↔ _
  rw [norm_smul_tangent hs]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [T2Space M] in
/-- For unit vectors, the cosine of the angle is the inner product. -/
lemma cos_angle_of_norm_eq_one {x : M} {u v : TangentSpace I x} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.cos (InnerProductGeometry.angle u v) = inner ℝ u v := by
  rw [InnerProductGeometry.cos_angle, hu, hv, mul_one, div_one]

/-- **The cosine law at a vertex** (dimension two, constant curvature `K`). Let `γ`, `σ`, `τ` be
geodesic segments `p → x` (length `a`), `x → y` (length `b`) and `y → p` (length `c`), contained in
a normal ball `exp_p(B_ρ)` around `p`. Then, with `C` the angle at `x` between `σ` and the reverse
of `γ`, `C_K(c) = C_K(a) C_K(b) + K S_K(a) S_K(b) cos C`. -/
theorem cosine_law_segments (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) {p x y : M} {a b c : ℝ} {γ σ τ : ℝ → M}
    (hγ : IsGeodesicSegment I γ p x a) (hσ : IsGeodesicSegment I σ x y b)
    (hτ : IsGeodesicSegment I τ y p c) {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    (hγB : ∀ t ∈ Icc 0 a, γ t ∈ expMap I p '' tangentBall I p ρ)
    (hσB : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    (hτB : ∀ t ∈ Icc 0 c, τ t ∈ expMap I p '' tangentBall I p ρ) :
    C K c = C K a * C K b + K * S K a * S K b *
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
  have h := cosine_law_normalBall' hdim hK hρ isOpen_Ioo hσ.pos.le
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

/-- **The angles of a nondegenerate triangle lie in `(0, π)`** (C9.7). With `γ`, `σ`, `τ` as in
`cosine_law_segments` (contained in a normal ball around `p`), if no vertex lies on the opposite
side (`y ∉ γ`, `p ∉ σ`, `x ∉ τ`), the angle at `x` between `σ` and the reverse of `γ` lies in
`(0, π)`. -/
theorem angle_pos_lt_pi_segments {p x y : M} {a b c : ℝ} {γ σ τ : ℝ → M}
    (hγ : IsGeodesicSegment I γ p x a) (hσ : IsGeodesicSegment I σ x y b)
    (hτ : IsGeodesicSegment I τ y p c) {ρ : ℝ} (hρ : IsNormalBall I p ρ)
    (hγB : ∀ t ∈ Icc 0 a, γ t ∈ expMap I p '' tangentBall I p ρ)
    (hσB : ∀ t ∈ Icc 0 b, σ t ∈ expMap I p '' tangentBall I p ρ)
    (hτB : ∀ t ∈ Icc 0 c, τ t ∈ expMap I p '' tangentBall I p ρ)
    (hy : y ∉ γ '' Icc 0 a) (hp : p ∉ σ '' Icc 0 b) (hx : x ∉ τ '' Icc 0 c) :
    0 < InnerProductGeometry.angle (show TangentSpace I x from (velocity I σ 0 : E))
        (show TangentSpace I x from -(velocity I γ a : E)) ∧
      InnerProductGeometry.angle (show TangentSpace I x from (velocity I σ 0 : E))
        (show TangentSpace I x from -(velocity I γ a : E)) < Real.pi := by
  have hu1 : ‖(show TangentSpace I x from (velocity I σ 0 : E))‖ = 1 := hσ.norm_velocity_zero
  have hv1 : ‖(show TangentSpace I x from -(velocity I γ a : E))‖ = 1 := by
    have h1 : ‖(show TangentSpace I x from -(velocity I γ a : E))‖ =
        ‖(show TangentSpace I x from (velocity I γ a : E))‖ := norm_neg _
    rw [h1]
    exact hγ.norm_velocity_length
  have hcos := cos_angle_of_norm_eq_one hu1 hv1
  obtain ⟨αγ, βγ, hαγ, hβγ, hγg⟩ := hγ.exists_Ioo
  obtain ⟨ασ, βσ, hασ, hβσ, hσg⟩ := hσ.exists_Ioo
  refine ⟨lt_of_le_of_ne (InnerProductGeometry.angle_nonneg _ _) (Ne.symm fun h0 ↦ ?_),
    lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _) fun hπ ↦ ?_⟩
  · -- angle `0`: `σ` continues the reverse of `γ`, so a vertex lies on a side
    rw [h0, Real.cos_zero] at hcos
    have heqv := (inner_eq_one_iff_of_norm_eq_one hu1 hv1).1 hcos.symm
    have hrev := hγ.reverse
    obtain ⟨αr, βr, hαr, hβr, hrg⟩ := hrev.exists_Ioo
    have hvel : (velocity I σ 0 : E) = velocity I (fun t ↦ γ (-1 * t + a)) 0 :=
      heqv.trans hγ.velocity_reverse_zero.symm
    have heq := IsGeodesicOn.eqOn (isOpen_Ioo.inter isOpen_Ioo)
      (isPreconnected_inter_real isPreconnected_Ioo isPreconnected_Ioo)
      (hσg.mono inter_subset_left) (hrg.mono inter_subset_right)
      (⟨⟨hασ, by linarith [hσ.pos]⟩, ⟨hαr, by linarith [hγ.pos]⟩⟩ :
        (0 : ℝ) ∈ Ioo ασ βσ ∩ Ioo αr βr)
      (hσ.apply_zero.trans hrev.apply_zero.symm) hvel
    rcases le_total b a with hba | hab
    · have h1 := (heq b ⟨⟨by linarith [hσ.pos], hβσ⟩, ⟨by linarith [hσ.pos], by linarith⟩⟩).1
      rw [hσ.apply_length] at h1
      exact hy ⟨-1 * b + a, ⟨by linarith, by linarith [hσ.pos]⟩, h1.symm⟩
    · have h1 := (heq a ⟨⟨by linarith [hγ.pos], by linarith⟩, ⟨by linarith [hγ.pos], hβr⟩⟩).1
      have h2 : σ a = p := by
        rw [h1]
        show γ (-1 * a + a) = p
        rw [show -1 * a + a = 0 by ring, hγ.apply_zero]
      exact hp ⟨a, ⟨hγ.pos.le, hab⟩, h2⟩
  · -- angle `π`: `σ` continues `γ`; comparing with the reverse of `τ` in the normal ball at `p`
    rw [hπ, Real.cos_pi] at hcos
    have hv1' : ‖-(show TangentSpace I x from -(velocity I γ a : E))‖ = 1 := by
      rw [norm_neg]; exact hv1
    have hin : inner ℝ (show TangentSpace I x from (velocity I σ 0 : E))
        (-(show TangentSpace I x from -(velocity I γ a : E))) = 1 := by
      rw [inner_neg_right, ← hcos, neg_neg]
    have heqv := (inner_eq_one_iff_of_norm_eq_one hu1 hv1').1 hin
    have hneg : -(show TangentSpace I x from -(velocity I γ a : E)) =
        (show TangentSpace I x from (velocity I γ a : E)) := neg_neg _
    have hvelσγ : (velocity I σ 0 : E) = velocity I γ a := heqv.trans hneg
    -- glue `γ` and the shifted `σ`
    have hsh := hσg.comp_affine isOpen_Ioo 1 (-a)
    have hdom : (fun t ↦ 1 * t + -a) ⁻¹' Ioo ασ βσ = Ioo (ασ + a) (βσ + a) := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rw [hdom] at hsh
    have haγ : a ∈ Ioo αγ βγ := ⟨by linarith [hγ.pos], hβγ⟩
    have haσ : a ∈ Ioo (ασ + a) (βσ + a) := ⟨by linarith, by linarith [hσ.pos]⟩
    have hpt : γ a = (fun t ↦ σ (1 * t + -a)) a := by
      show γ a = σ (1 * a + -a)
      rw [show 1 * a + -a = 0 by ring, hγ.apply_length, hσ.apply_zero]
    have hvt : (velocity I γ a : E) = velocity I (fun t ↦ σ (1 * t + -a)) a := by
      rw [velocity_comp_affine (by
        rw [show 1 * a + -a = 0 by ring]; exact hσ.mdifferentiableAt ⟨le_rfl, hσ.pos.le⟩),
        one_smul]
      exact hvelσγ.symm.trans (congrArg (fun s ↦ (velocity I σ s : E)) (by ring))
    obtain ⟨g, hg, hg₁, hg₂⟩ := IsGeodesicOn.glue isOpen_Ioo isPreconnected_Ioo isOpen_Ioo
      isPreconnected_Ioo hγg hsh haγ haσ hpt hvt
    have h0γ : (0 : ℝ) ∈ Ioo αγ βγ := ⟨hαγ, by linarith [hγ.pos]⟩
    have hgF : IsGeodesicFrom I p (velocity I γ 0 : E) g (Ioo αγ βγ ∪ Ioo (ασ + a) (βσ + a)) :=
      ⟨isOpen_Ioo.union isOpen_Ioo, isPreconnected_Ioo.union a haγ haσ isPreconnected_Ioo,
        Or.inl h0γ, hg, by rw [hg₁ 0 h0γ, hγ.apply_zero],
        velocity_congr (by filter_upwards [isOpen_Ioo.mem_nhds h0γ] with t ht using hg₁ t ht)⟩
    have hgU : Icc 0 (a + b) ⊆ Ioo αγ βγ ∪ Ioo (ασ + a) (βσ + a) := by
      intro t ht
      rcases le_total t a with hta | hat
      · exact Or.inl ⟨by linarith [ht.1], by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith [ht.2]⟩
    have hgB : ∀ t ∈ Icc 0 (a + b), g t ∈ expMap I p '' tangentBall I p ρ := by
      intro t ht
      rcases le_total t a with hta | hat
      · rw [hg₁ t ⟨by linarith [ht.1], by linarith⟩]
        exact hγB t ⟨ht.1, hta⟩
      · rw [hg₂ t ⟨by linarith, by linarith [ht.2]⟩]
        exact hσB _ ⟨by linarith, by linarith [ht.2]⟩
    have hab0 : 0 ≤ a + b := by linarith [hγ.pos, hσ.pos]
    have hgBall := hgF.smul_mem_tangentBall hρ hgU hgB (a + b) ⟨hab0, le_rfl⟩
    have hgy : expMap I p ((a + b) • (show E from velocity I γ 0)) = y := by
      rw [(expMap_smul hgF (t := a + b) (by rw [uIcc_of_le hab0]; exact hgU)).2,
        hg₂ (a + b) ⟨by linarith [hσ.pos], by linarith [hσ.pos]⟩]
      show σ (1 * (a + b) + -a) = y
      rw [show 1 * (a + b) + -a = b by ring, hσ.apply_length]
    -- the reverse of `τ`
    have hτr := hτ.reverse
    obtain ⟨Uτ, hτF, hτU⟩ := hτr.exists_isGeodesicFrom
    have hτB' : ∀ t ∈ Icc 0 c, (fun t ↦ τ (-1 * t + c)) t ∈ expMap I p '' tangentBall I p ρ :=
      fun t ht ↦ hτB _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hτBall := hτF.smul_mem_tangentBall hρ hτU hτB' c ⟨hτ.pos.le, le_rfl⟩
    have hτy : expMap I p (c • (show E from velocity I (fun t ↦ τ (-1 * t + c)) 0)) = y := by
      rw [(expMap_smul hτF (t := c) (by rw [uIcc_of_le hτ.pos.le]; exact hτU)).2]
      show τ (-1 * c + c) = y
      rw [show -1 * c + c = 0 by ring, hτ.apply_zero]
    have hinj := hρ.injOn hgBall hτBall (hgy.trans hτy.symm)
    -- lengths and directions agree
    have hn1 := hγ.norm_velocity_zero
    have hn2 := hτr.norm_velocity_zero
    have hlen : a + b = c := by
      have e1 := norm_smul_tangent (I := I) (p := p) (v := (velocity I γ 0 : E)) hab0
      have e2 := norm_smul_tangent (I := I) (p := p)
        (v := (velocity I (fun t ↦ τ (-1 * t + c)) 0 : E)) hτ.pos.le
      have h1 := congrArg (fun z : E ↦ ‖(show TangentSpace I p from z)‖) hinj
      have h2 : (a + b) * ‖(show TangentSpace I p from (velocity I γ 0 : E))‖ =
          c * ‖(show TangentSpace I p from (velocity I (fun t ↦ τ (-1 * t + c)) 0 : E))‖ :=
        e1.symm.trans (h1.trans e2)
      rwa [hn1, hn2, mul_one, mul_one] at h2
    have hdir : (velocity I γ 0 : E) = velocity I (fun t ↦ τ (-1 * t + c)) 0 := by
      have hinj' := hinj.trans (congrArg (fun s : ℝ ↦
        s • (show E from velocity I (fun t ↦ τ (-1 * t + c)) 0)) hlen.symm)
      exact smul_right_injective E (by linarith [hγ.pos, hσ.pos] : a + b ≠ 0) hinj'
    have heq := IsGeodesicOn.eqOn (hgF.isOpen.inter hτF.isOpen)
      (isPreconnected_inter_real hgF.isPreconnected hτF.isPreconnected)
      (hgF.isGeodesicOn.mono inter_subset_left) (hτF.isGeodesicOn.mono inter_subset_right)
      ⟨hgF.zero_mem, hτF.zero_mem⟩ (hgF.apply_zero.trans hτF.apply_zero.symm)
      (hgF.velocity_zero.trans (hdir.trans hτF.velocity_zero.symm)) a
      ⟨hgU ⟨hγ.pos.le, by linarith [hσ.pos]⟩, hτU ⟨hγ.pos.le, by linarith [hσ.pos]⟩⟩
    have h1 : x = τ (-1 * a + c) := by
      rw [← hγ.apply_length, ← hg₁ a haγ]
      exact heq.1
    exact hx ⟨-1 * a + c, ⟨by linarith [hσ.pos], by linarith [hγ.pos]⟩, h1.symm⟩

end Segment

section Triangle

variable (I M) in
/-- A **geodesic triangle**: vertices `A, B, C` (`pA`, `pB`, `pC`) and three selected geodesic
segments: `σa` from `B` to `C` of length `a`, `σb` from `C` to `A` of length `b`, and `σc` from `A`
to `B` of length `c`. The side lengths are the lengths of the selected segments. -/
structure GeodesicTriangle where
  pA : M
  pB : M
  pC : M
  a : ℝ
  b : ℝ
  c : ℝ
  σa : ℝ → M
  σb : ℝ → M
  σc : ℝ → M
  segment_a : IsGeodesicSegment I σa pB pC a
  segment_b : IsGeodesicSegment I σb pC pA b
  segment_c : IsGeodesicSegment I σc pA pB c

namespace GeodesicTriangle

variable (T : GeodesicTriangle I M)

/-- The angle at `A`, between the initial velocities of the two sides leaving `A`: the segment to
`B` (`σc`) and the segment to `C` (the reverse of `σb`). -/
def angleA : ℝ :=
  InnerProductGeometry.angle (show TangentSpace I T.pA from (velocity I T.σc 0 : E))
    (show TangentSpace I T.pA from -(velocity I T.σb T.b : E))

/-- The angle at `B`, between the segment to `C` (`σa`) and the segment to `A` (the reverse of
`σc`). -/
def angleB : ℝ :=
  InnerProductGeometry.angle (show TangentSpace I T.pB from (velocity I T.σa 0 : E))
    (show TangentSpace I T.pB from -(velocity I T.σc T.c : E))

/-- The angle at `C`, between the segment to `A` (`σb`) and the segment to `B` (the reverse of
`σa`). -/
def angleC : ℝ :=
  InnerProductGeometry.angle (show TangentSpace I T.pC from (velocity I T.σb 0 : E))
    (show TangentSpace I T.pC from -(velocity I T.σa T.a : E))

/-- Some normal ball around `X` contains the three sides. -/
def SidesInNormalBallAt (X : M) : Prop :=
  ∃ ρ, IsNormalBall I X ρ ∧ (∀ t ∈ Icc 0 T.a, T.σa t ∈ expMap I X '' tangentBall I X ρ) ∧
    (∀ t ∈ Icc 0 T.b, T.σb t ∈ expMap I X '' tangentBall I X ρ) ∧
    (∀ t ∈ Icc 0 T.c, T.σc t ∈ expMap I X '' tangentBall I X ρ)

/-- **Technical condition**: for each vertex, some normal ball around it contains the three sides.
This is the condition under which the cosine law in a normal ball applies; it is a sufficient
condition used for the proofs, not the manuscript's definition of a convex geodesic triangle. -/
def SidesInNormalBalls : Prop :=
  T.SidesInNormalBallAt T.pA ∧ T.SidesInNormalBallAt T.pB ∧ T.SidesInNormalBallAt T.pC

/-- The triangle is **nondegenerate**: no vertex lies on the opposite side. -/
def Nondegenerate : Prop :=
  T.pA ∉ T.σa '' Icc 0 T.a ∧ T.pB ∉ T.σb '' Icc 0 T.b ∧ T.pC ∉ T.σc '' Icc 0 T.c

/-- **The cosine law** (C9.3, under the technical condition `SidesInNormalBalls`): in a
two-dimensional Riemannian manifold of constant curvature `K`,
`C_K(a) = C_K(b) C_K(c) + K S_K(b) S_K(c) cos A`, and likewise at `B` and `C`. -/
theorem cosine_law (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (hT : T.SidesInNormalBalls) :
    C K T.a = C K T.b * C K T.c + K * S K T.b * S K T.c * Real.cos T.angleA ∧
      C K T.b = C K T.c * C K T.a + K * S K T.c * S K T.a * Real.cos T.angleB ∧
      C K T.c = C K T.a * C K T.b + K * S K T.a * S K T.b * Real.cos T.angleC := by
  obtain ⟨⟨ρA, hρA, hAa, hAb, hAc⟩, ⟨ρB, hρB, hBa, hBb, hBc⟩, ⟨ρC, hρC, hCa, hCb, hCc⟩⟩ := hT
  exact ⟨cosine_law_segments hdim hK T.segment_b T.segment_c T.segment_a hρC hCb hCc hCa,
    cosine_law_segments hdim hK T.segment_c T.segment_a T.segment_b hρA hAc hAa hAb,
    cosine_law_segments hdim hK T.segment_a T.segment_b T.segment_c hρB hBa hBb hBc⟩

/-- **The angles of a nondegenerate triangle lie in `(0, π)`** (C9.7, under the technical condition
`SidesInNormalBalls`). -/
theorem angle_pos_lt_pi (hT : T.SidesInNormalBalls) (hnd : T.Nondegenerate) :
    (0 < T.angleA ∧ T.angleA < Real.pi) ∧ (0 < T.angleB ∧ T.angleB < Real.pi) ∧
      (0 < T.angleC ∧ T.angleC < Real.pi) := by
  obtain ⟨⟨ρA, hρA, hAa, hAb, hAc⟩, ⟨ρB, hρB, hBa, hBb, hBc⟩, ⟨ρC, hρC, hCa, hCb, hCc⟩⟩ := hT
  obtain ⟨h1, h2, h3⟩ := hnd
  exact ⟨angle_pos_lt_pi_segments T.segment_b T.segment_c T.segment_a hρC hCb hCc hCa h2 h3 h1,
    angle_pos_lt_pi_segments T.segment_c T.segment_a T.segment_b hρA hAc hAa hAb h3 h1 h2,
    angle_pos_lt_pi_segments T.segment_a T.segment_b T.segment_c hρB hBa hBb hBc h1 h2 h3⟩

omit [I.Boundaryless] [T2Space M] in
/-- Under the manuscript's side-length condition (`0 < a, b, c < π/√K` if `K > 0`),
`S_K(a), S_K(b), S_K(c) > 0` (C9.2). -/
lemma S_pos_sides {K : ℝ} (hK0 : K ≠ 0)
    (hsides : 0 < K → T.a < Real.pi / √K ∧ T.b < Real.pi / √K ∧ T.c < Real.pi / √K) :
    0 < S K T.a ∧ 0 < S K T.b ∧ 0 < S K T.c := by
  rcases lt_or_gt_of_ne hK0 with hneg | hpos
  · exact ⟨S_pos_of_nonpos hneg.le T.segment_a.pos, S_pos_of_nonpos hneg.le T.segment_b.pos,
      S_pos_of_nonpos hneg.le T.segment_c.pos⟩
  · obtain ⟨ha, hb, hc⟩ := hsides hpos
    exact ⟨S_pos hpos T.segment_a.pos ha, S_pos hpos T.segment_b.pos hb,
      S_pos hpos T.segment_c.pos hc⟩

/-- **The sine law** (C9.1 for `K ≠ 0`, under the technical condition `SidesInNormalBalls`): for a
nondegenerate geodesic triangle in a two-dimensional Riemannian manifold of constant curvature
`K ≠ 0`, with `0 < a, b, c < π/√K` if `K > 0`,
`sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)`. -/
theorem sine_law (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (hK0 : K ≠ 0) (hT : T.SidesInNormalBalls)
    (hnd : T.Nondegenerate)
    (hsides : 0 < K → T.a < Real.pi / √K ∧ T.b < Real.pi / √K ∧ T.c < Real.pi / √K) :
    Real.sin T.angleA / S K T.a = Real.sin T.angleB / S K T.b ∧
      Real.sin T.angleB / S K T.b = Real.sin T.angleC / S K T.c := by
  obtain ⟨hA, hB, hC⟩ := T.cosine_law hdim hK hT
  obtain ⟨⟨hA0, hAπ⟩, ⟨hB0, hBπ⟩, ⟨hC0, hCπ⟩⟩ := T.angle_pos_lt_pi hT hnd
  obtain ⟨hPa, hPb, hPc⟩ := T.S_pos_sides hK0 hsides
  exact sec9_sine_law_of_cos_law hK0 hPa hPb hPc hA0 hAπ hB0 hBπ hC0 hCπ hA hB hC

/-- **The angles are those given by the cosine law** (C9.8 for `K ≠ 0`, under the technical
condition `SidesInNormalBalls`): `A = A_K = angleK K a b c`, `B = angleK K b c a`,
`C = angleK K c a b`, where `angleK` is the angle determined by the constant-curvature cosine law
(whose limit `K → 0` is `sec9_limit`). -/
theorem angles_eq_angleK (hdim : Module.finrank ℝ E = 2) {K : ℝ}
    (hK : HasConstSectionalCurvature I M K) (hK0 : K ≠ 0) (hT : T.SidesInNormalBalls)
    (hsides : 0 < K → T.a < Real.pi / √K ∧ T.b < Real.pi / √K ∧ T.c < Real.pi / √K) :
    T.angleA = angleK K T.a T.b T.c ∧ T.angleB = angleK K T.b T.c T.a ∧
      T.angleC = angleK K T.c T.a T.b := by
  obtain ⟨hA, hB, hC⟩ := T.cosine_law hdim hK hT
  obtain ⟨hPa, hPb, hPc⟩ := T.S_pos_sides hK0 hsides
  have key : ∀ {x y z θ : ℝ}, 0 < S K y → 0 < S K z → 0 ≤ θ → θ ≤ Real.pi →
      C K x = C K y * C K z + K * S K y * S K z * Real.cos θ → θ = angleK K x y z := by
    intro x y z θ hy hz h0 hπ hcos
    have hd : K * S K y * S K z ≠ 0 := mul_ne_zero (mul_ne_zero hK0 hy.ne') hz.ne'
    have hc : Real.cos θ = cosLaw K x y z := by
      rw [cosLaw_of_ne_zero hK0, eq_div_iff hd]
      linarith
    rw [angleK, ← hc, Real.arccos_cos h0 hπ]
  exact ⟨key hPb hPc (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _) hA,
    key hPc hPa (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _) hB,
    key hPa hPb (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _) hC⟩

end GeodesicTriangle

end Triangle

end PythagoreanPaper
