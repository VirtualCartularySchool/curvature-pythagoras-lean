import PythagoreanPaper.Riemannian.AlongCurve
import PythagoreanPaper.Sec07
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Euclidean space: Levi-Civita connection and parallel transport (manuscript §7, C7.3)

Let `F` be a finite-dimensional real inner product space, regarded as a Riemannian manifold with
its canonical metric (Mathlib's instance: the inner product of `F` on every tangent space
`T_x F`, which Mathlib identifies with `F`). This file proves:

* `isLeviCivitaConnection_trivialCov`: the ordinary derivative of vector fields `F → F` is a
  Levi-Civita connection (it is metric and torsion-free). By uniqueness of the Levi-Civita
  connection, Mathlib's `leviCivitaConnection` agrees with it on differentiable vector fields
  (`leviCivitaConnection_euclidean`).
* `covAlong_euclidean`: along any curve, the covariant derivative of a field is its ordinary
  derivative.
* `euclidean_isParallelAlongOn_iff`: along a curve differentiable on an open interval, a field is
  parallel iff it is constant. Hence parallel transport along any curve is the identity of `F`
  (`euclidean_parallelTransport`): it identifies all tangent spaces with `F`, and the
  identification does not depend on the curve.

A field along a curve `γ` is a function `σ` with `σ t ∈ T_{γ t} F`; since Mathlib's tangent spaces
of `F` are `F` itself, such a field is the same as a function `ℝ → F`, which is how the statements
below are written.

For the Euclidean plane this is the first half of C7.3 ("in the Euclidean plane, parallel transport
identifies all tangent spaces globally"); the second half ("under this identification `J`
corresponds to multiplication by `i`") is `sec7_euclidean_plane_J`, combining the above with
`sec7_J_corresponds_to_I` and `sec7_exists_complex_identification` of `PythagoreanPaper.Sec07`.
`sec7_euclidean_plane_tangent_J` states the second half for the rotations `J_x` of the tangent
spaces `T_x ℝ²` themselves (C7.1, built from the Riemannian metric at `x`), each tangent space
carrying the orientation transported from `ℝ²`: one orientation-preserving isometry `ℝ² ≃ ℂ`
turns every `J_x` into multiplication by `i`.
-/

noncomputable section

open Bundle Set Filter Function NormedSpace VectorField
open scoped Manifold Topology

namespace PythagoreanPaper

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section TrivialConnection

variable (F) in
/-- The ordinary derivative of vector fields on a normed space, as a covariant derivative on its
tangent bundle. -/
def trivialCov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _) where
  toFun σ x := fderiv ℝ (fun y ↦ (σ y : F)) x
  isCovariantDerivativeOnUniv :=
    { add := fun {σ σ' x} hσ hσ' _ ↦ by
        rw [mdifferentiableAt_tangentSection_iff] at hσ hσ'
        exact fderiv_add hσ hσ'
      leibniz := fun {σ g x} hσ hg _ ↦ by
        rw [mdifferentiableAt_tangentSection_iff] at hσ
        rw [mdifferentiableAt_iff_differentiableAt] at hg
        rw [mvfderiv_eq_fderiv]
        exact fderiv_smul hg hσ }

lemma trivialCov_apply (σ : Π x : F, TangentSpace 𝓘(ℝ, F) x) (x : F) :
    trivialCov F σ x = fderiv ℝ (fun y ↦ (σ y : F)) x :=
  rfl

/-- The ordinary derivative of a constant vector field vanishes. -/
lemma trivialCov_const (w x : F) : trivialCov F (fun y ↦ (fromTangentSpace y).symm w) x = 0 := by
  ext v
  change fderiv ℝ (Function.const F w) x (fromTangentSpace x v) = 0
  rw [fderiv_const]
  rfl

/-- The canonical metric of `F` is smooth (of every order). -/
instance {n : WithTop ℕ∞} :
    IsContMDiffRiemannianBundle 𝓘(ℝ, F) n F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  ⟨(riemannianMetricVectorSpace F).inner, (riemannianMetricVectorSpace F).contMDiff.of_le le_top,
    fun _ _ _ ↦ rfl⟩

variable [FiniteDimensional ℝ F]

/-- **The Levi-Civita connection of a Euclidean space is the ordinary derivative**: the ordinary
derivative is compatible with the canonical metric and torsion-free. -/
theorem isLeviCivitaConnection_trivialCov : (trivialCov F).IsLeviCivitaConnection := by
  constructor
  · rw [CovariantDerivative.isMetricCompatible_iff]
    intro x X σ τ _ hσ hτ
    rw [mdifferentiableAt_tangentSection_iff] at hσ hτ
    rw [mvfderiv_eq_fderiv]
    exact (fderiv_inner_apply ℝ hσ hτ (X x)).trans (add_comm _ _)
  · rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x _ _
    rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
    calc _ = lieBracket ℝ X Y x := rfl
      _ = _ := (congrFun lieBracketWithin_univ x).symm

/-- The Levi-Civita connection of `F`. -/
local notation "∇F" => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F

/-- Mathlib's Levi-Civita connection of `F` is the ordinary derivative, on vector fields
differentiable at the point. -/
theorem leviCivitaConnection_euclidean {Y : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F}
    (hY : MDiffAt (T% Y) x) : ∇F Y x = trivialCov F Y x := by
  ext v
  exact (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection 𝓘(ℝ, F)
    (M := F)).uniqueness 𝓘(ℝ, F) isLeviCivitaConnection_trivialCov hY v

end TrivialConnection

section AlongCurves

variable [FiniteDimensional ℝ F]

/-- The Levi-Civita connection of `F`. -/
local notation "∇F" => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F

omit [FiniteDimensional ℝ F] in
/-- In the trivialization of the tangent bundle of `F`, the coordinates of a field along a curve
are the field itself, read in `F` through the canonical identification `T_x F = F`. -/
lemma coordAlong_euclidean (x₀ : F) (γ : ℝ → F) (σ : (t : ℝ) → TangentSpace 𝓘(ℝ, F) (γ t)) :
    coordAlong (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀) γ σ =
      fun s ↦ fromTangentSpace (γ s) (σ s) := by
  funext s
  change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt ℝ (γ s) (σ s) = _
  rw [TangentBundle.continuousLinearMapAt_model_space]
  rfl

/-- **In a Euclidean space, the covariant derivative along a curve is the ordinary derivative**
(read in `F` through the canonical identification `T_x F = F`). No differentiability hypothesis is
needed: both sides use `deriv`. -/
theorem covAlong_euclidean (γ : ℝ → F) (σ : (t : ℝ) → TangentSpace 𝓘(ℝ, F) (γ t)) (t : ℝ) :
    fromTangentSpace (γ t) (covAlong ∇F γ σ t) =
      deriv (fun s ↦ fromTangentSpace (γ s) (σ s)) t := by
  have h2 : ∀ w : F, trivSection (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (γ t)) w =
      fun x ↦ (fromTangentSpace x).symm w := fun w ↦ by
    funext x
    change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (γ t)).symmL ℝ x w = _
    rw [TangentBundle.symmL_model_space]
    rfl
  have h3 : ∀ w : F, ∇F (fun x ↦ (fromTangentSpace x).symm w) (γ t) = 0 := fun w ↦ by
    rw [leviCivitaConnection_euclidean (Y := fun x ↦ (fromTangentSpace x).symm w)
      (mdifferentiableAt_tangentSection_iff.2 (differentiableAt_const w))]
    exact trivialCov_const w (γ t)
  have h4 : ∀ d : F, (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (γ t)).symmL ℝ (γ t) d =
      (fromTangentSpace (γ t)).symm d := fun d ↦ by
    rw [TangentBundle.symmL_model_space]
    rfl
  rw [covAlong, covAlongIn, coordAlong_euclidean, h2, h3, zero_apply,
    add_zero, h4, ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ F] in
/-- In a Euclidean space, a field along a curve is differentiable along it iff the curve and the
field (read in `F`) are differentiable. -/
lemma mdiffAlongAt_euclidean_iff {γ : ℝ → F} {σ : (t : ℝ) → TangentSpace 𝓘(ℝ, F) (γ t)}
    {t : ℝ} :
    MDiffAlongAt 𝓘(ℝ, F) F γ σ t ↔
      DifferentiableAt ℝ γ t ∧ DifferentiableAt ℝ (fun s ↦ fromTangentSpace (γ s) (σ s)) t := by
  rw [mdiffAlongAt_iff (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (γ t))
    (mem_baseSet_trivializationAt F _ (γ t)), mdifferentiableAt_iff_differentiableAt,
    coordAlong_euclidean]

/-- **Parallel fields in a Euclidean space.** Along a curve differentiable on an open
preconnected set `U` (an open interval), a field is parallel on `U` iff it is constant on `U`
(read in `F`). -/
theorem euclidean_isParallelAlongOn_iff {γ : ℝ → F}
    {σ : (t : ℝ) → TangentSpace 𝓘(ℝ, F) (γ t)} {U : Set ℝ} (hU : IsOpen U)
    (hU' : IsPreconnected U) (hγ : ∀ t ∈ U, DifferentiableAt ℝ γ t) :
    IsParallelAlongOn ∇F γ σ U ↔
      ∀ s ∈ U, ∀ t ∈ U, fromTangentSpace (γ s) (σ s) = fromTangentSpace (γ t) (σ t) := by
  constructor
  · intro h s hs t ht
    have hd : DifferentiableOn ℝ (fun s ↦ fromTangentSpace (γ s) (σ s)) U := fun t ht ↦
      (mdiffAlongAt_euclidean_iff.1 (h t ht).1).2.differentiableWithinAt
    refine hU.is_const_of_deriv_eq_zero hU' hd (fun t ht ↦ ?_) hs ht
    have h0 := congrArg (fromTangentSpace (γ t)) (h t ht).2
    rw [covAlong_euclidean, map_zero] at h0
    exact h0
  · intro h t ht
    have hloc : (fun s ↦ fromTangentSpace (γ s) (σ s)) =ᶠ[𝓝 t]
        fun _ ↦ fromTangentSpace (γ t) (σ t) := by
      filter_upwards [hU.mem_nhds ht] with s hs using h s hs t ht
    refine ⟨mdiffAlongAt_euclidean_iff.2
      ⟨hγ t ht, (differentiableAt_const _).congr_of_eventuallyEq hloc⟩, ?_⟩
    apply (fromTangentSpace (γ t)).injective
    rw [covAlong_euclidean, hloc.deriv_eq, deriv_const, map_zero]

/-- **Parallel transport in a Euclidean space is the identity.** Along a curve `γ` differentiable
on an open preconnected set `U`, for every `t₀ ∈ U` and every `v ∈ F`, the field which is `v` at
every point (read in `F`) is parallel, and every parallel field equal to `v` at `t₀` is equal to
`v` at every `t ∈ U`. Thus parallel transport identifies every tangent space `T_x F` with `F`,
independently of the curve. -/
theorem euclidean_parallelTransport {γ : ℝ → F} {U : Set ℝ} (hU : IsOpen U)
    (hU' : IsPreconnected U) (hγ : ∀ t ∈ U, DifferentiableAt ℝ γ t) {t₀ : ℝ} (ht₀ : t₀ ∈ U)
    (v : F) :
    IsParallelAlongOn ∇F γ (fun t ↦ (fromTangentSpace (γ t)).symm v) U ∧
      ∀ σ : (t : ℝ) → TangentSpace 𝓘(ℝ, F) (γ t), IsParallelAlongOn ∇F γ σ U →
        fromTangentSpace (γ t₀) (σ t₀) = v → ∀ t ∈ U, fromTangentSpace (γ t) (σ t) = v := by
  refine ⟨(euclidean_isParallelAlongOn_iff hU hU' hγ).2 fun s _ t _ ↦ by simp,
    fun σ hσ hσ₀ t ht ↦ ?_⟩
  rw [← hσ₀]
  exact (euclidean_isParallelAlongOn_iff hU hU' hγ).1 hσ t ht t₀ ht₀

end AlongCurves

section Plane

/-- **C7.3** (first half) for the Euclidean plane `ℝ² = EuclideanSpace ℝ (Fin 2)` with its canonical
Riemannian metric and Levi-Civita connection: parallel transport along any curve differentiable on
an open interval is the identity of `ℝ²` (under the canonical identification `T_x ℝ² = ℝ²`). It
therefore identifies all tangent spaces with `ℝ²`, independently of the curve. -/
theorem sec7_euclidean_plane_parallelTransport {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {U : Set ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hγ : ∀ t ∈ U, DifferentiableAt ℝ γ t) {t₀ : ℝ}
    (ht₀ : t₀ ∈ U) (v : EuclideanSpace ℝ (Fin 2)) :
    IsParallelAlongOn (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace ℝ (Fin 2))) γ (fun t ↦ (fromTangentSpace (γ t)).symm v) U ∧
      ∀ σ : (t : ℝ) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (γ t),
        IsParallelAlongOn (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (EuclideanSpace ℝ (Fin 2))) γ σ U →
        fromTangentSpace (γ t₀) (σ t₀) = v → ∀ t ∈ U, fromTangentSpace (γ t) (σ t) = v :=
  euclidean_parallelTransport hU hU' hγ ht₀ v

/-- **C7.3** (second half) for the Euclidean plane. Let `o` be an orientation of the plane `ℝ²`.
By `euclidean_parallelTransport`, parallel transport identifies every tangent space `T_x ℝ²` with
`ℝ²` itself, so the orientation `o` and the rotation `J = Jrot o` are the same in every tangent
space. There is an orientation-preserving linear isometry `φ : ℝ² ≃ ℂ`, and for any such `φ`,
`J` corresponds to multiplication by `i`: `φ (J v) = i · φ v`. -/
theorem sec7_euclidean_plane_J (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∃ φ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ,
      Orientation.map (Fin 2) φ.toLinearEquiv o = Complex.orientation ∧
        ∀ v, φ (Jrot o v) = Complex.I * φ v :=
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  let ⟨φ, hφ⟩ := sec7_exists_complex_identification o
  ⟨φ, hφ, fun v ↦ sec7_J_corresponds_to_I o φ hφ v⟩

/-- Transporting an orientation along `e` and then along `f` is transporting it along
`e.trans f`. -/
lemma orientation_map_map {M N P : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] [AddCommGroup P] [Module ℝ P] {ι : Type*} (e : M ≃ₗ[ℝ] N) (f : N ≃ₗ[ℝ] P)
    (o : Orientation ℝ M ι) :
    Orientation.map ι f (Orientation.map ι e o) = Orientation.map ι (e.trans f) o := by
  induction o using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply]
    congr 1

/-- The canonical identification `T_x F = F` is a linear isometry for the canonical Riemannian
metric of `F`. -/
def fromTangentSpaceₗᵢ (x : F) : TangentSpace 𝓘(ℝ, F) x ≃ₗᵢ[ℝ] F :=
  { (fromTangentSpace x).toLinearEquiv with
    norm_map' := fun _ ↦ norm_tangentSpace_vectorSpace.symm }

/-- **C7.3** for the Euclidean plane, stated with the tangent-space rotations of C7.1. Let `o` be
an orientation of `ℝ²`, and give each tangent space `T_x ℝ²` the orientation `o_x` corresponding
to `o` under the identification `T_x ℝ² = ℝ²`, which is parallel transport along any curve
(`sec7_euclidean_plane_parallelTransport`). There is an orientation-preserving linear isometry
`φ : ℝ² ≃ ℂ` such that in **every** tangent space, the rotation `J_x = Jrot o_x` of C7.1 (built
from the Riemannian metric at `x` and `o_x`) is multiplication by `i`:
`φ (J_x v) = i · φ v`. -/
theorem sec7_euclidean_plane_tangent_J (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∃ φ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ,
      Orientation.map (Fin 2) φ.toLinearEquiv o = Complex.orientation ∧
      ∀ (x : EuclideanSpace ℝ (Fin 2)) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x),
        haveI : Fact (Module.finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x) = 2) :=
          ⟨finrank_euclideanSpace_fin⟩
        φ (fromTangentSpace x (Jrot (Orientation.map (Fin 2)
            (fromTangentSpaceₗᵢ x).symm.toLinearEquiv o) v)) =
          Complex.I * φ (fromTangentSpace x v) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨φ, hφ⟩ := sec7_exists_complex_identification o
  refine ⟨φ, hφ, fun x v ↦ ?_⟩
  have : Fact (Module.finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x) = 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hψ : Orientation.map (Fin 2) ((fromTangentSpaceₗᵢ x).trans φ).toLinearEquiv
      (Orientation.map (Fin 2) (fromTangentSpaceₗᵢ x).symm.toLinearEquiv o) =
        Complex.orientation := by
    rw [orientation_map_map, ← hφ]
    congr 1
  exact sec7_J_corresponds_to_I _ ((fromTangentSpaceₗᵢ x).trans φ) hψ v

end Plane

end PythagoreanPaper
