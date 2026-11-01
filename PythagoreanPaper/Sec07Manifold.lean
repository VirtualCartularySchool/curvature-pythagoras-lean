import PythagoreanPaper.Sec07
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Manuscript §7 on the tangent spaces of a Riemannian manifold

C7.1 and C7.2 are statements about each tangent space `T_pM` of an oriented two-dimensional
Riemannian manifold `M`: there is a 90° rotation `J : T_pM → T_pM` compatible with the metric and
the orientation, `J² = -I`, and the rotation by the angle `θ` in `T_pM` is
`exp(θ J) = cos θ I + sin θ J`.

In Mathlib a Riemannian manifold is a manifold whose tangent bundle carries a `RiemannianBundle`
structure (see the module docstring of `Mathlib.Geometry.Manifold.Riemannian.Basic`). With
`open scoped Bundle`, every tangent space `TangentSpace I x` is then a real inner product space,
whose inner product is the Riemannian metric at `x`. The theorems of `PythagoreanPaper.Sec07`,
proved for an arbitrary oriented two-dimensional real inner product space, therefore apply to
every tangent space; this file records that application.

Mathlib has no notion of an orientation of a manifold. The theorems below hold for **every**
orientation `o` of every tangent space `T_xM`, in particular for the orientation of `T_xM` induced
by an orientation of `M`. The hypothesis `Fact (finrank ℝ (TangentSpace I x) = 2)` says that `M`
is two-dimensional at `x`; it holds as soon as the model space `E` is two-dimensional
(`fact_finrank_tangentSpace`).

* C7.1: `sec7_tangent_J_metric`, `sec7_tangent_J_orientation`, `sec7_tangent_J_sq`.
* C7.2: `sec7_tangent_exp_J`, `sec7_tangent_rotation_eq_exp`.

`sec7_tangent_J_sq_euclideanPlane` instantiates C7.1 for the Euclidean plane with its canonical
Riemannian metric, which shows that the hypotheses are satisfiable.
-/

noncomputable section

open NormedSpace Bundle
open scoped RealInnerProductSpace

namespace PythagoreanPaper

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent spaces of a manifold modelled on a two-dimensional space are two-dimensional. -/
theorem fact_finrank_tangentSpace (hE : Module.finrank ℝ E = 2) (x : M) :
    Fact (Module.finrank ℝ (TangentSpace I x) = 2) :=
  ⟨hE⟩

/- The inner products of the tangent spaces. These pointwise statements use neither the smoothness
of the metric nor that of `M`, so they hold in particular for Mathlib's `C^∞` Riemannian
manifolds (`[IsManifold I ∞ M]`, `[IsContMDiffRiemannianBundle I ∞ E (TangentSpace I)]`). -/
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (x : M) [Fact (Module.finrank ℝ (TangentSpace I x) = 2)]
  (o : Orientation ℝ (TangentSpace I x) (Fin 2))

/-- **C7.1** (metric) on `T_xM`: `J` preserves the Riemannian norm, and `J v ⟂ v` for the
Riemannian inner product. -/
theorem sec7_tangent_J_metric (v : TangentSpace I x) :
    ‖Jrot o v‖ = ‖v‖ ∧ ⟪Jrot o v, v⟫ = 0 :=
  sec7_J_metric o v

/-- **C7.1** (orientation) on `T_xM`: for `v ≠ 0` the oriented angle from `v` to `J v` is
`π / 2`. -/
theorem sec7_tangent_J_orientation {v : TangentSpace I x} (hv : v ≠ 0) :
    o.oangle v (Jrot o v) = ((Real.pi / 2 : ℝ) : Real.Angle) :=
  sec7_J_orientation o hv

/-- **C7.1** on `T_xM`: `J² = -I`. -/
theorem sec7_tangent_J_sq : Jrot o * Jrot o = -1 :=
  sec7_J_sq o

/-- **C7.2** on `T_xM`: `exp(θ J) = cos θ I + sin θ J`. -/
theorem sec7_tangent_exp_J (θ : ℝ) :
    exp (θ • Jrot o) =
      Real.cos θ • (1 : TangentSpace I x →L[ℝ] TangentSpace I x) + Real.sin θ • Jrot o :=
  sec7_exp_J o θ

/-- **C7.2** on `T_xM`: the rotation of `T_xM` by the angle `θ` is `exp(θ J)`. -/
theorem sec7_tangent_rotation_eq_exp (θ : ℝ) (v : TangentSpace I x) :
    o.rotation (θ : Real.Angle) v = exp (θ • Jrot o) v :=
  sec7_rotation_eq_exp o θ v

end Manifold

section EuclideanPlane

/-- C7.1 for a tangent space of the Euclidean plane with its canonical Riemannian metric
(`J² = -I` for every orientation of `T_x ℝ²`). This shows that the hypotheses of this file are
satisfiable. -/
theorem sec7_tangent_J_sq_euclideanPlane (x : EuclideanSpace ℝ (Fin 2))
    (o : Orientation ℝ (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x)
      (Fin 2)) :
    haveI : Fact (Module.finrank ℝ
        (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x) = 2) :=
      fact_finrank_tangentSpace finrank_euclideanSpace_fin x
    Jrot o * Jrot o = -1 :=
  haveI : Fact (Module.finrank ℝ
      (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x) = 2) :=
    fact_finrank_tangentSpace finrank_euclideanSpace_fin x
  sec7_tangent_J_sq x o

end EuclideanPlane

end PythagoreanPaper
