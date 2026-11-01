import PythagoreanPaper.ExpQuadratic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Manuscript §7 — angular cyclicity and Euler's formula

On an oriented two-dimensional real inner product space `V` (the algebraic structure of each
tangent space `T_pM` of an oriented two-dimensional Riemannian manifold):

* C7.1: the 90° rotation `J` is compatible with the metric and the orientation, and `J² = -I`
  (`sec7_J_metric`, `sec7_J_orientation`, `sec7_J_sq`).
* C7.2: `exp(θ J) = cos θ I + sin θ J`, by splitting the exponential series into even and odd
  terms (`sec7_exp_J`); the rotation by the angle `θ` is `exp(θ J)` (`sec7_rotation_eq_exp`).
* C7.3 (linear-algebra part): `V` can be identified with the complex plane by an
  orientation-preserving linear isometry (`sec7_exists_complex_identification`), and under any
  such identification `J` is multiplication by `i` (`sec7_J_corresponds_to_I`); for `V = ℂ`
  itself, `J z = i z` (`sec7_J_complex`).
* C7.4: Euler's formula `e^{iθ} = cos θ + i sin θ` follows: identifying `J` with multiplication
  by `i` turns `exp(θ J) = cos θ I + sin θ J` into `e^{iθ} = cos θ + i sin θ`
  (`sec7_exp_J_complex`, `sec7_euler`).

The part of C7.3 that identifies all tangent spaces of the Euclidean plane by parallel transport,
and the application to the tangent spaces of a Riemannian manifold, need Riemannian geometry and
are not in this file.
-/

noncomputable section

open NormedSpace
open scoped RealInnerProductSpace

namespace PythagoreanPaper

section Rotation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- The 90° rotation `J` of §7, as a continuous linear map. -/
def Jrot : V →L[ℝ] V := (o.rightAngleRotation.toContinuousLinearEquiv : V →L[ℝ] V)

@[simp] theorem Jrot_apply (x : V) : Jrot o x = o.rightAngleRotation x := rfl

/-- **C7.1** (metric): `J` preserves norms, and `J x` is orthogonal to `x`. -/
theorem sec7_J_metric (x : V) : ‖Jrot o x‖ = ‖x‖ ∧ ⟪Jrot o x, x⟫ = 0 :=
  ⟨o.rightAngleRotation.norm_map x, o.inner_rightAngleRotation_self x⟩

/-- **C7.1** (orientation): for `x ≠ 0` the oriented angle from `x` to `J x` is `π / 2`. -/
theorem sec7_J_orientation {x : V} (hx : x ≠ 0) :
    o.oangle x (Jrot o x) = ((Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [Jrot_apply, ← o.rotation_pi_div_two]
  exact o.oangle_rotation_self_right hx _

/-- **C7.1.** `J² = -I`. -/
theorem sec7_J_sq : Jrot o * Jrot o = -1 := by
  ext x
  simp [o.rightAngleRotation_rightAngleRotation]

/-- **C7.2.** `exp(θ J) = cos θ I + sin θ J`. -/
theorem sec7_exp_J (θ : ℝ) :
    exp (θ • Jrot o) = Real.cos θ • (1 : V →L[ℝ] V) + Real.sin θ • Jrot o := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ (Fact.out : _ = 2)
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hA : Jrot o * Jrot o = -(1 : ℝ) • (1 : V →L[ℝ] V) := by
    rw [sec7_J_sq, neg_smul, one_smul]
  rw [exp_smul_eq_of_mul_self hA θ, C_of_pos θ one_pos, S_of_pos θ one_pos, Real.sqrt_one,
    one_mul, div_one]

/-- **C7.2.** The rotation by the angle `θ` is `exp(θ J)`. -/
theorem sec7_rotation_eq_exp (θ : ℝ) (x : V) :
    o.rotation (θ : Real.Angle) x = exp (θ • Jrot o) x := by
  rw [sec7_exp_J, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
  simp

/-- **C7.3** (linear-algebra part). Under an orientation-preserving linear isometry
`f : V ≃ ℂ`, `J` corresponds to multiplication by `i`. -/
theorem sec7_J_corresponds_to_I (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) :
    f (Jrot o x) = Complex.I * f x :=
  o.rightAngleRotation_map_complex f hf x

/-- **C7.3** (linear-algebra part). An oriented two-dimensional real inner product space can be
identified with the complex plane by an orientation-preserving linear isometry. -/
theorem sec7_exists_complex_identification :
    ∃ f : V ≃ₗᵢ[ℝ] ℂ, Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation := by
  have h2 : Module.finrank ℝ V = 2 := Fact.out
  -- a positively oriented orthonormal basis `b`, sent to the basis `1, i` of `ℂ`
  let b : OrthonormalBasis (Fin 2) ℝ V := o.finOrthonormalBasis two_pos h2
  let f : V ≃ₗᵢ[ℝ] ℂ := b.repr.trans Complex.orthonormalBasisOneI.repr.symm
  refine ⟨f, ?_⟩
  have hb : b.toBasis.orientation = o := o.finOrthonormalBasis_orientation two_pos h2
  have hmap : b.toBasis.map f.toLinearEquiv = Complex.basisOneI := by
    ext i
    fin_cases i <;> simp [f]
  calc Orientation.map (Fin 2) f.toLinearEquiv o
      = Orientation.map (Fin 2) f.toLinearEquiv b.toBasis.orientation := by rw [hb]
    _ = (b.toBasis.map f.toLinearEquiv).orientation := (b.toBasis.orientation_map _).symm
    _ = Complex.basisOneI.orientation := by rw [hmap]
    _ = Complex.orientation := rfl

end Rotation

section Complex

attribute [local instance] Complex.finrank_real_complex_fact

/-- **C7.3** (linear-algebra part). On `ℂ` with its standard orientation, `J` is multiplication
by `i`. -/
theorem sec7_J_complex (z : ℂ) : Jrot Complex.orientation z = Complex.I * z := by
  rw [Jrot_apply, Complex.rightAngleRotation]

/-- Multiplication by a complex number, as a ring homomorphism into the real-linear operators
on `ℂ`. It identifies `ℂ` with the operators `z ↦ c z`. -/
def lmul : ℂ →+* (ℂ →L[ℝ] ℂ) where
  toFun c := ContinuousLinearMap.mul ℝ ℂ c
  map_one' := ContinuousLinearMap.ext fun z => by simp
  map_mul' c d := ContinuousLinearMap.ext fun z => by simp [mul_assoc]
  map_zero' := ContinuousLinearMap.ext fun z => by simp
  map_add' c d := ContinuousLinearMap.ext fun z => by simp

@[simp] theorem lmul_apply (c z : ℂ) : lmul c z = c * z := rfl

/-- `J` of `ℂ` is the operator of multiplication by `i`. -/
theorem sec7_J_eq_lmul_I : Jrot Complex.orientation = lmul Complex.I :=
  ContinuousLinearMap.ext fun z => by rw [sec7_J_complex, lmul_apply]

/-- **C7.4.** Under the identification of `J` with multiplication by `i`, `exp(θ J)` is
multiplication by `e^{iθ}`. -/
theorem sec7_exp_J_complex (θ : ℝ) :
    exp (θ • Jrot Complex.orientation) = lmul (exp ((θ : ℂ) * Complex.I)) := by
  let : Algebra ℚ (ℂ →L[ℝ] ℂ) := Algebra.compHom _ (algebraMap ℚ ℝ)
  have hc : Continuous lmul := (ContinuousLinearMap.mul ℝ ℂ).continuous
  have hθ : lmul ((θ : ℂ) * Complex.I) = θ • Jrot Complex.orientation := by
    rw [sec7_J_eq_lmul_I]
    refine ContinuousLinearMap.ext fun z => ?_
    simp [Complex.real_smul]
  rw [map_exp lmul hc, hθ]

/-- **C7.4.** Euler's formula `e^{iθ} = cos θ + i sin θ`, obtained from
`exp(θ J) = cos θ I + sin θ J` (C7.2) by identifying `J` with multiplication by `i` (C7.3). -/
theorem sec7_euler (θ : ℝ) :
    Complex.exp (θ * Complex.I) = Real.cos θ + Real.sin θ * Complex.I := by
  have h1 : exp (θ • Jrot Complex.orientation) 1 = exp ((θ : ℂ) * Complex.I) := by
    rw [sec7_exp_J_complex, lmul_apply, mul_one]
  have h2 : exp (θ • Jrot Complex.orientation) 1 = Real.cos θ + Real.sin θ * Complex.I := by
    rw [sec7_exp_J]
    simp [Complex.real_smul]
  rw [Complex.exp_eq_exp_ℂ, ← h1, h2]

end Complex

end PythagoreanPaper
