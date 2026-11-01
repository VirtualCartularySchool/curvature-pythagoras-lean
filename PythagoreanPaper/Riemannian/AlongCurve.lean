import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Covariant derivative along a curve

Let `V → M` be a vector bundle with a covariant derivative `∇` (Mathlib's `CovariantDerivative`,
whose argument order is `cov σ x v = ∇_v σ (x)`). For a curve `γ : ℝ → M` and a field `σ` along
`γ` (`σ t ∈ V (γ t)`), the covariant derivative of `σ` along `γ` is, in a local trivialization `e`
of `V` around `γ t` in which `σ (s) = e⁻¹ (c (s))`,

  `D_t σ (t) = e⁻¹ (c'(t)) + ∇_{γ'(t)} (e⁻¹ w)`,   where `w = c (t)`

and `e⁻¹ w` is the section which is constant equal to `w` in the trivialization. This is the usual
local formula `D_t σ = Σ (c_i)' E_i + c_i ∇_{γ'} E_i` in the local frame `E_i = e⁻¹ (b_i)`.

We define `covAlong` with Mathlib's preferred trivialization `trivializationAt` at `γ t`, and prove

* `covAlong_eq_covAlongIn`: the same formula holds in **every** trivialization of the atlas around
  `γ t`, so the definition does not depend on the choice of trivialization;
* `covAlong_comp`: if `σ = X ∘ γ` for a section `X` differentiable at `γ t`, then
  `D_t σ (t) = ∇_{γ'(t)} X`;
* `covAlong_add`, `covAlong_smul`: linearity and the Leibniz rule `D_t (f σ) = f' σ + f D_t σ`;
* `covAlong_congr`: `D_t σ (t)` depends only on the germ of `σ` at `t`.

These are the defining properties of the covariant derivative along a curve (Lee, *Introduction to
Riemannian Manifolds*, 2nd ed., Theorem 4.24). They are used for the Jacobi equation
`D_t² J + R(J, γ') γ' = 0` of manuscript §4 and for parallel transport in §§4, 7.

The core computation is `cov_symmL_comp`: in a trivialization, `∇` satisfies a Leibniz rule with
respect to the coordinates of a section.
-/

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology

namespace PythagoreanPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Velocity

variable (I) in
/-- The velocity `γ'(t) ∈ T_{γ t} M` of a curve `γ : ℝ → M`. -/
def velocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chain rule for a vector-valued function along a curve: `(h ∘ γ)'(t) = dh (γ'(t))`. -/
theorem deriv_comp_eq_mvfderiv_velocity {h : M → F} {γ : ℝ → M} {t : ℝ}
    (hh : MDiffAt h (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    deriv (h ∘ γ) t = d% h (γ t) (velocity I γ t) := by
  have h1 := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] F ↦ L (1 : ℝ))
    (mvfderiv_comp t hh hγ)
  rw [mvfderiv_eq_fderiv] at h1
  exact h1

/-- The derivative of a continuous linear functional composed with a function. -/
lemma mvfderiv_clm_comp (L : F →L[ℝ] ℝ) {h : M → F} {x : M} (hh : MDiffAt h x) :
    d% (fun y ↦ L (h y)) x = L.comp (d% h x) := by
  have h1 : (fun y ↦ L (h y)) = (L : F → ℝ) ∘ h := rfl
  rw [h1, mvfderiv_comp x L.differentiableAt.mdifferentiableAt hh, mvfderiv_eq_fderiv,
    L.fderiv]
  rfl

end Velocity

section ModelSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a normed space, a vector field is differentiable as a section of the tangent bundle iff it
is differentiable as a map `F → F`. -/
lemma mdifferentiableAt_tangentSection_iff {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F} :
    MDiffAt (T% σ) x ↔ DifferentiableAt ℝ (fun y ↦ (σ y : F)) x := by
  rw [mdifferentiableAt_section, mdifferentiableAt_iff_differentiableAt]
  simp only [trivializationAt_model_space_apply]

end ModelSpace

section Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

section TrivSection

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

/-- The section of `V` equal to `w` in the trivialization `e` (and to `0` outside the base set of
`e`). For a basis `b` of `F`, the sections `trivSection e (b i)` form the local frame of `e`. -/
def trivSection (w : F) : Π x : M, V x :=
  fun x ↦ e.symmL ℝ x w

@[simp]
lemma trivSection_apply (w : F) (x : M) : trivSection e w x = e.symmL ℝ x w :=
  rfl

lemma trivSection_add (w w' : F) :
    trivSection e (w + w') = trivSection e w + trivSection e w' := by
  funext x
  simp [trivSection]

lemma trivSection_smul (a : ℝ) (w : F) : trivSection e (a • w) = a • trivSection e w := by
  funext x
  simp [trivSection]

lemma trivSection_sum {ι : Type*} (s : Finset ι) (w : ι → F) :
    trivSection e (∑ i ∈ s, w i) = ∑ i ∈ s, trivSection e (w i) := by
  funext x
  simp [trivSection, Finset.sum_apply]

/-- In a trivialization, a vector `w = Σ wᵢ bᵢ` of `F` corresponds to `Σ wᵢ e⁻¹(bᵢ)`. -/
lemma symmL_eq_sum_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F) (x : M) (w : F) :
    e.symmL ℝ x w = ∑ i, b.repr w i • e.symmL ℝ x (b i) := by
  conv_lhs => rw [← b.sum_repr w]
  simp only [map_sum, map_smul]

variable [ContMDiffVectorBundle 1 F V I]

/-- A section whose coordinates in a trivialization are differentiable is differentiable. -/
lemma mdifferentiableAt_symmL_comp {x : M} (hx : x ∈ e.baseSet) {h : M → F}
    (hh : MDiffAt h x) : MDiffAt (T% (fun y ↦ e.symmL ℝ y (h y))) x := by
  rw [e.mdifferentiableAt_section_iff I _ hx]
  apply hh.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simp [e.symmL_apply hy, e.apply_mk_symm hy]

lemma mdifferentiableAt_trivSection {x : M} (hx : x ∈ e.baseSet) (w : F) :
    MDiffAt (T% (trivSection e w)) x :=
  mdifferentiableAt_symmL_comp e hx (h := fun _ ↦ w) mdifferentiableAt_const

end TrivSection

section CurveBasics

/-- The coordinates in the trivialization `e` of a field `σ` along `γ`. -/
def coordAlong (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (γ : ℝ → M)
    (σ : (t : ℝ) → V (γ t)) (t : ℝ) : F :=
  e.continuousLinearMapAt ℝ (γ t) (σ t)

variable (I F) in
/-- `σ` is a differentiable field along `γ` at `t`: the map `s ↦ (γ s, σ s)` into the total space
of `V` is differentiable at `t`. -/
def MDiffAlongAt (γ : ℝ → M) (σ : (t : ℝ) → V (γ t)) (t : ℝ) : Prop :=
  MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) (fun s ↦ (⟨γ s, σ s⟩ : TotalSpace F V)) t

variable {γ : ℝ → M} {σ τ : (t : ℝ) → V (γ t)} {t : ℝ}

section Coord

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

lemma coordAlong_add :
    coordAlong e γ (fun s ↦ σ s + τ s) = coordAlong e γ σ + coordAlong e γ τ := by
  funext s
  simp [coordAlong]

lemma coordAlong_smul (f : ℝ → ℝ) :
    coordAlong e γ (fun s ↦ f s • σ s) = f • coordAlong e γ σ := by
  funext s
  simp [coordAlong]

lemma coordAlong_sum {ι : Type*} (u : Finset ι) (σ : ι → (t : ℝ) → V (γ t)) :
    coordAlong e γ (fun s ↦ ∑ i ∈ u, σ i s) = ∑ i ∈ u, coordAlong e γ (σ i) := by
  funext s
  simp [coordAlong, Finset.sum_apply]

variable [ContMDiffVectorBundle 1 F V I]

/-- A field along a curve is differentiable iff the curve is differentiable and the coordinates of
the field in a trivialization of the atlas are differentiable. -/
theorem mdiffAlongAt_iff (he : γ t ∈ e.baseSet) :
    MDiffAlongAt I F γ σ t ↔
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ t ∧ DifferentiableAt ℝ (coordAlong e γ σ) t := by
  unfold MDiffAlongAt
  rw [e.mdifferentiableAt_totalSpace_iff I (fun s ↦ (⟨γ s, σ s⟩ : TotalSpace F V))
    (e.mem_source.2 he)]
  refine and_congr_right fun hγ ↦ ?_
  rw [← mdifferentiableAt_iff_differentiableAt]
  have heq : (fun s ↦ (e ⟨γ s, σ s⟩).2) =ᶠ[𝓝 t] coordAlong e γ σ := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with s hs
    exact (e.continuousLinearMapAt_apply_of_mem ℝ hs (σ s)).symm
  exact ⟨fun h ↦ h.congr_of_eventuallyEq heq.symm, fun h ↦ h.congr_of_eventuallyEq heq⟩

end Coord

variable [ContMDiffVectorBundle 1 F V I]

lemma MDiffAlongAt.mdifferentiableAt_curve (h : MDiffAlongAt I F γ σ t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
  ((mdiffAlongAt_iff _ (mem_baseSet_trivializationAt F V (γ t))).1 h).1

lemma MDiffAlongAt.differentiableAt_coord (h : MDiffAlongAt I F γ σ t)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (he : γ t ∈ e.baseSet) :
    DifferentiableAt ℝ (coordAlong e γ σ) t :=
  ((mdiffAlongAt_iff e he).1 h).2

omit [(x : M) → AddCommGroup (V x)] [(x : M) → Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] in
/-- The restriction `X ∘ γ` of a differentiable section to a differentiable curve is a
differentiable field along the curve. -/
lemma mdiffAlongAt_comp (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) {X : Π x : M, V x}
    (hX : MDiffAt (T% X) (γ t)) : MDiffAlongAt I F γ (fun s ↦ X (γ s)) t :=
  hX.comp t hγ

lemma MDiffAlongAt.add (hσ : MDiffAlongAt I F γ σ t) (hτ : MDiffAlongAt I F γ τ t) :
    MDiffAlongAt I F γ (fun s ↦ σ s + τ s) t := by
  have he := mem_baseSet_trivializationAt F V (γ t)
  rw [mdiffAlongAt_iff _ he] at hσ hτ ⊢
  refine ⟨hσ.1, ?_⟩
  rw [coordAlong_add]
  exact hσ.2.add hτ.2

lemma MDiffAlongAt.smul {f : ℝ → ℝ} (hσ : MDiffAlongAt I F γ σ t) (hf : DifferentiableAt ℝ f t) :
    MDiffAlongAt I F γ (fun s ↦ f s • σ s) t := by
  have he := mem_baseSet_trivializationAt F V (γ t)
  rw [mdiffAlongAt_iff _ he] at hσ ⊢
  refine ⟨hσ.1, ?_⟩
  rw [coordAlong_smul]
  exact hf.smul hσ.2

end CurveBasics

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

section CovSum

variable (cov : CovariantDerivative I F V)

/-- `∇` is additive on finite sums of sections differentiable at the point. -/
theorem cov_finset_sum {ι : Type*} (s : Finset ι) {σ : ι → Π x : M, V x} {x : M}
    (hσ : ∀ i ∈ s, MDiffAt (T% (σ i)) x) :
    cov (∑ i ∈ s, σ i) x = ∑ i ∈ s, cov (σ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have h1 : MDiffAt (T% (σ i)) x := hσ i (Finset.mem_insert_self i s)
    have h2 : ∀ j ∈ s, MDiffAt (T% (σ j)) x := fun j hj ↦ hσ j (Finset.mem_insert_of_mem hj)
    have h3 : MDiffAt (T% (∑ j ∈ s, σ j)) x := by
      have hfun : (∑ j ∈ s, σ j) = fun y ↦ ∑ j ∈ s, σ j y :=
        funext fun y ↦ Finset.sum_apply y s σ
      rw [hfun]
      exact MDifferentiableAt.sum_section h2
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      cov.isCovariantDerivativeOnUniv.add h1 h3, ih h2]

end CovSum

section Core

variable [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V) (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

/-- `∇` of the section `e⁻¹ w`, which is constant equal to `w` in the trivialization `e`, written
in the local frame `e⁻¹(bᵢ)`: it is linear in `w`. -/
lemma cov_trivSection_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F) {x : M}
    (hx : x ∈ e.baseSet) (w : F) :
    cov (trivSection e w) x = ∑ i, b.repr w i • cov (trivSection e (b i)) x := by
  have hd : ∀ i ∈ Finset.univ, MDiffAt (T% (trivSection e (b.repr w i • b i))) x :=
    fun i _ ↦ mdifferentiableAt_trivSection e hx _
  conv_lhs => rw [← b.sum_repr w]
  rw [trivSection_sum, cov_finset_sum cov Finset.univ hd]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [trivSection_smul, cov.isCovariantDerivativeOnUniv.smul_const _
    (mdifferentiableAt_trivSection e hx _)]

/-- **Leibniz rule in a trivialization.** If the section `σ` has coordinates `h` in the
trivialization `e` near `x`, then `∇σ (x) = e⁻¹ ∘ dh (x) + ∇ (e⁻¹ (h x)) (x)`: the covariant
derivative is the ordinary derivative of the coordinates plus the covariant derivative of the
section which is constant in the trivialization. -/
theorem cov_symmL_comp [FiniteDimensional ℝ F] {x : M} (hx : x ∈ e.baseSet) {h : M → F}
    (hh : MDiffAt h x) :
    cov (fun y ↦ e.symmL ℝ y (h y)) x =
      (e.symmL ℝ x).comp (d% h x) + cov (trivSection e (h x)) x := by
  classical
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℝ F)) ℝ F) :=
    ⟨Module.finBasis ℝ F⟩
  let L : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i w, L i w = b.repr w i := fun i w ↦ by simp [L]
  let g : Fin (Module.finrank ℝ F) → M → ℝ := fun i y ↦ L i (h y)
  have hg : ∀ i, MDiffAt (g i) x := fun i ↦
    (L i).differentiableAt.comp_mdifferentiableAt hh
  have hdg : ∀ i, d% (g i) x = (L i).comp (d% h x) := fun i ↦ mvfderiv_clm_comp (L i) hh
  have hgx : ∀ i, g i x = b.repr (h x) i := fun i ↦ hL i (h x)
  have hs : ∀ i, MDiffAt (T% (trivSection e (b i))) x := fun i ↦
    mdifferentiableAt_trivSection e hx (b i)
  -- the section, expanded in the local frame
  have hdec : (fun y ↦ e.symmL ℝ y (h y)) = ∑ i, g i • trivSection e (b i) := by
    funext y
    rw [Finset.sum_apply, symmL_eq_sum_repr e b y (h y)]
    simp [g, hL]
  rw [hdec, cov_finset_sum cov _ (fun i _ ↦ (hg i).smul_section (hs i)),
    cov_trivSection_eq_sum cov e b hx (h x)]
  have hterm : ∀ i, cov (g i • trivSection e (b i)) x =
      g i x • cov (trivSection e (b i)) x + (d% (g i) x).smulRight (trivSection e (b i) x) :=
    fun i ↦ cov.isCovariantDerivativeOnUniv.leibniz (hs i) (hg i)
  have key : ∑ i, (d% (g i) x).smulRight (trivSection e (b i) x) =
      (e.symmL ℝ x).comp (d% h x) := by
    ext v
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      hdg, trivSection_apply, hL]
    exact (symmL_eq_sum_repr e b x (d% h x v)).symm
  simp only [hterm, Finset.sum_add_distrib, key]
  simp only [hgx]
  abel

end Core

section CovAlongDef

/-- The covariant derivative along `γ`, computed in the trivialization `e`. -/
def covAlongIn (cov : CovariantDerivative I F V) (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (γ : ℝ → M) (σ : (t : ℝ) → V (γ t)) (t : ℝ) : V (γ t) :=
  e.symmL ℝ (γ t) (deriv (coordAlong e γ σ) t) +
    cov (trivSection e (coordAlong e γ σ t)) (γ t) (velocity I γ t)

/-- **The covariant derivative `D_t σ` of a field `σ` along a curve `γ`**, computed in Mathlib's
preferred trivialization at `γ t`. By `covAlong_eq_covAlongIn`, any other trivialization of the
atlas gives the same value. -/
def covAlong (cov : CovariantDerivative I F V) (γ : ℝ → M) (σ : (t : ℝ) → V (γ t)) (t : ℝ) :
    V (γ t) :=
  covAlongIn cov (trivializationAt F V (γ t)) γ σ t

/-- `σ` is a **parallel field** along `γ` on the set `U ⊆ ℝ`: at every `t ∈ U` it is
differentiable along `γ` and `D_t σ (t) = 0`. -/
def IsParallelAlongOn (cov : CovariantDerivative I F V) (γ : ℝ → M) (σ : (t : ℝ) → V (γ t))
    (U : Set ℝ) : Prop :=
  ∀ t ∈ U, MDiffAlongAt I F γ σ t ∧ covAlong cov γ σ t = 0

end CovAlongDef

section CovAlongIn

variable {γ : ℝ → M} {σ τ : (t : ℝ) → V (γ t)} {t : ℝ}
  (cov : CovariantDerivative I F V) (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

/-- `covAlongIn` depends only on the germ of the field. -/
lemma covAlongIn_congr (h : ∀ᶠ s in 𝓝 t, σ s = τ s) :
    covAlongIn cov e γ σ t = covAlongIn cov e γ τ t := by
  have hc : coordAlong e γ σ =ᶠ[𝓝 t] coordAlong e γ τ :=
    h.mono fun s hs ↦ by simp [coordAlong, hs]
  simp only [covAlongIn, hc.deriv_eq, hc.eq_of_nhds]

variable [ContMDiffVectorBundle 1 F V I]

lemma covAlongIn_add (he : γ t ∈ e.baseSet) (hσ : DifferentiableAt ℝ (coordAlong e γ σ) t)
    (hτ : DifferentiableAt ℝ (coordAlong e γ τ) t) :
    covAlongIn cov e γ (fun s ↦ σ s + τ s) t =
      covAlongIn cov e γ σ t + covAlongIn cov e γ τ t := by
  have hadd := cov.isCovariantDerivativeOnUniv.add
    (mdifferentiableAt_trivSection e he (coordAlong e γ σ t))
    (mdifferentiableAt_trivSection e he (coordAlong e γ τ t))
  simp only [covAlongIn, coordAlong_add, Pi.add_apply, deriv_add hσ hτ, map_add, trivSection_add,
    hadd, add_apply]
  abel

/-- **Leibniz rule** for `covAlongIn`. -/
lemma covAlongIn_smul (he : γ t ∈ e.baseSet) {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f t)
    (hσ : DifferentiableAt ℝ (coordAlong e γ σ) t) :
    covAlongIn cov e γ (fun s ↦ f s • σ s) t =
      deriv f t • σ t + f t • covAlongIn cov e γ σ t := by
  have hsm := cov.isCovariantDerivativeOnUniv.smul_const (f t)
    (mdifferentiableAt_trivSection e he (coordAlong e γ σ t))
  have hσt : e.symmL ℝ (γ t) (coordAlong e γ σ t) = σ t :=
    e.symmL_continuousLinearMapAt he (σ t)
  simp only [covAlongIn, coordAlong_smul, Pi.smul_apply', deriv_smul hf hσ, map_add, map_smul,
    trivSection_smul, hsm, smul_apply, hσt, smul_add]
  abel

lemma covAlongIn_sum (he : γ t ∈ e.baseSet) {ι : Type*} (u : Finset ι)
    {σ : ι → (s : ℝ) → V (γ s)} (h : ∀ i ∈ u, DifferentiableAt ℝ (coordAlong e γ (σ i)) t) :
    covAlongIn cov e γ (fun s ↦ ∑ i ∈ u, σ i s) t = ∑ i ∈ u, covAlongIn cov e γ (σ i) t := by
  have hcs : cov (∑ i ∈ u, trivSection e (coordAlong e γ (σ i) t)) (γ t) =
      ∑ i ∈ u, cov (trivSection e (coordAlong e γ (σ i) t)) (γ t) :=
    cov_finset_sum cov u (fun i _ ↦ mdifferentiableAt_trivSection e he _)
  simp only [covAlongIn, coordAlong_sum, deriv_sum h, map_sum, Finset.sum_apply, trivSection_sum,
    hcs, sum_apply, Finset.sum_add_distrib]

/-- If the field is the restriction `X ∘ γ` of a section `X` differentiable at `γ t`, then its
covariant derivative along `γ` is `∇_{γ'(t)} X`. -/
theorem covAlongIn_comp [FiniteDimensional ℝ F] (he : γ t ∈ e.baseSet)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) {X : Π x : M, V x} (hX : MDiffAt (T% X) (γ t)) :
    covAlongIn cov e γ (fun s ↦ X (γ s)) t = cov X (γ t) (velocity I γ t) := by
  let h : M → F := fun y ↦ e.continuousLinearMapAt ℝ y (X y)
  have hh : MDiffAt h (γ t) := by
    have h1 := (e.mdifferentiableAt_section_iff I X he).1 hX
    apply h1.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy (X y)
  have hXeq : cov X (γ t) = cov (fun y ↦ e.symmL ℝ y (h y)) (γ t) := by
    apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hX
      (mdifferentiableAt_symmL_comp e he hh) Filter.univ_mem
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact (e.symmL_continuousLinearMapAt hy (X y)).symm
  have hcoord : coordAlong e γ (fun s ↦ X (γ s)) = h ∘ γ := rfl
  rw [covAlongIn, hcoord, deriv_comp_eq_mvfderiv_velocity hh hγ, hXeq,
    cov_symmL_comp cov e he hh]
  rfl

end CovAlongIn

section CovAlong

variable {γ : ℝ → M} {σ τ : (t : ℝ) → V (γ t)} {t : ℝ}
  (cov : CovariantDerivative I F V)

/-- **Locality**: `D_t σ (t)` depends only on the germ of `σ` at `t`. -/
theorem covAlong_congr (h : ∀ᶠ s in 𝓝 t, σ s = τ s) :
    covAlong cov γ σ t = covAlong cov γ τ t :=
  covAlongIn_congr cov _ h

variable [ContMDiffVectorBundle 1 F V I]

theorem covAlong_add (hσ : MDiffAlongAt I F γ σ t) (hτ : MDiffAlongAt I F γ τ t) :
    covAlong cov γ (fun s ↦ σ s + τ s) t = covAlong cov γ σ t + covAlong cov γ τ t :=
  covAlongIn_add cov _ (mem_baseSet_trivializationAt F V (γ t))
    (hσ.differentiableAt_coord _ (mem_baseSet_trivializationAt F V (γ t)))
    (hτ.differentiableAt_coord _ (mem_baseSet_trivializationAt F V (γ t)))

/-- **Leibniz rule** `D_t (f σ) = f' σ + f D_t σ`. -/
theorem covAlong_smul {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f t) (hσ : MDiffAlongAt I F γ σ t) :
    covAlong cov γ (fun s ↦ f s • σ s) t = deriv f t • σ t + f t • covAlong cov γ σ t :=
  covAlongIn_smul cov _ (mem_baseSet_trivializationAt F V (γ t)) hf
    (hσ.differentiableAt_coord _ (mem_baseSet_trivializationAt F V (γ t)))

/-- **Restriction of a section**: `D_t (X ∘ γ) = ∇_{γ'} X`. -/
theorem covAlong_comp [FiniteDimensional ℝ F] (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {X : Π x : M, V x} (hX : MDiffAt (T% X) (γ t)) :
    covAlong cov γ (fun s ↦ X (γ s)) t = cov X (γ t) (velocity I γ t) :=
  covAlongIn_comp cov _ (mem_baseSet_trivializationAt F V (γ t)) hγ hX

/-- **Independence of the trivialization**: `D_t σ (t)` is given by the local formula in every
trivialization of the atlas whose base set contains `γ t`. -/
theorem covAlong_eq_covAlongIn [FiniteDimensional ℝ F] (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (he : γ t ∈ e.baseSet) (hσ : MDiffAlongAt I F γ σ t) :
    covAlong cov γ σ t = covAlongIn cov e γ σ t := by
  classical
  have he₀ : γ t ∈ (trivializationAt F V (γ t)).baseSet :=
    mem_baseSet_trivializationAt F V (γ t)
  have hγ := hσ.mdifferentiableAt_curve
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℝ F)) ℝ F) :=
    ⟨Module.finBasis ℝ F⟩
  have hc : DifferentiableAt ℝ (coordAlong e γ σ) t := hσ.differentiableAt_coord e he
  let L : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i w, L i w = b.repr w i := fun i w ↦ by simp [L]
  let ci : Fin (Module.finrank ℝ F) → ℝ → ℝ := fun i s ↦ L i (coordAlong e γ σ s)
  have hci : ∀ i, DifferentiableAt ℝ (ci i) t := fun i ↦ (L i).differentiableAt.comp t hc
  have hdci : ∀ i, deriv (ci i) t = b.repr (deriv (coordAlong e γ σ) t) i := fun i ↦ by
    rw [← hL]
    exact ((L i).hasFDerivAt.comp_hasDerivAt t hc.hasDerivAt).deriv
  have hcit : ∀ i, ci i t = b.repr (coordAlong e γ σ t) i := fun i ↦ hL i _
  let X : Fin (Module.finrank ℝ F) → Π x : M, V x := fun i ↦ trivSection e (b i)
  have hX : ∀ i, MDiffAt (T% (X i)) (γ t) := fun i ↦ mdifferentiableAt_trivSection e he (b i)
  have hXt : ∀ i, X i (γ t) = e.symmL ℝ (γ t) (b i) := fun i ↦ rfl
  -- near `t`, `σ` is `Σ cᵢ (X i ∘ γ)`
  have hloc : ∀ᶠ s in 𝓝 t, σ s = ∑ i, ci i s • X i (γ s) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with s hs
    calc σ s = e.symmL ℝ (γ s) (coordAlong e γ σ s) :=
          (e.symmL_continuousLinearMapAt hs (σ s)).symm
      _ = ∑ i, ci i s • X i (γ s) := by
        rw [symmL_eq_sum_repr e b (γ s) (coordAlong e γ σ s)]
        simp [ci, hL, X]
  have hterm : ∀ i, MDiffAlongAt I F γ (fun s ↦ ci i s • X i (γ s)) t := fun i ↦
    (mdiffAlongAt_comp hγ (hX i)).smul (hci i)
  have hA : ∀ i, covAlongIn cov (trivializationAt F V (γ t)) γ (fun s ↦ ci i s • X i (γ s)) t =
      deriv (ci i) t • X i (γ t) + ci i t • cov (X i) (γ t) (velocity I γ t) := fun i ↦ by
    rw [covAlongIn_smul cov _ he₀ (hci i)
      ((mdiffAlongAt_comp hγ (hX i)).differentiableAt_coord _ he₀),
      covAlongIn_comp cov _ he₀ hγ (hX i)]
  rw [covAlong, covAlongIn_congr cov _ hloc,
    covAlongIn_sum cov _ he₀ Finset.univ (σ := fun i s ↦ ci i s • X i (γ s))
      (fun i _ ↦ (hterm i).differentiableAt_coord _ he₀)]
  simp only [hA, Finset.sum_add_distrib, hdci, hcit, hXt]
  -- the right-hand side, expanded in the same frame
  rw [covAlongIn, cov_trivSection_eq_sum cov e b he,
    symmL_eq_sum_repr e b (γ t) (deriv (coordAlong e γ σ) t)]
  simp only [sum_apply, smul_apply, X]

end CovAlong

end Bundle

end PythagoreanPaper
