import PythagoreanPaper.Riemannian.ModelEuclidean
import PythagoreanPaper.Riemannian.ModelHyperbolic
import PythagoreanPaper.Riemannian.ModelSphere

/-!
# Geodesic triangles of the model spaces (manuscript §9: C9.1, C9.3, C9.7, C9.8)

The theorems of `PythagoreanPaper.Riemannian.Triangle` (cosine law, angles in `(0, π)`, sine law,
angles `A_K`) assume the technical condition `GeodesicTriangle.SidesInNormalBalls`. In the model
spaces of curvature `K` that condition is **proved** here, so the theorems hold with the following
hypotheses only:

* `K = 0`, the Euclidean plane `ℝ²` (`PythagoreanPaper.Riemannian.ModelEuclidean`): every geodesic
  triangle;
* `K < 0`, the hyperbolic plane `hypPlane K` (`PythagoreanPaper.Riemannian.ModelHyperbolic`): every
  geodesic triangle;
* `K > 0`, the sphere `SphereModel.sph K` of curvature `K` (`PythagoreanPaper.Riemannian.ModelSphere`):
  every geodesic triangle whose three sides lie in an open hemisphere
  (`SphereModel.InOpenHemisphere`), together with the manuscript's side-length hypothesis
  `0 < a, b, c < π/√K` where the manuscript uses it.

**Distinctions from the manuscript** (recorded in `CLAIMS.md` and `RIEMANNIAN_LAYER.md`):

* "two-dimensional geometry of constant curvature `K`" is read as the model space of curvature `K`
  (the plane, the hyperbolic plane, the sphere of radius `1/√K`). For a general Riemannian surface
  of constant curvature the technical condition is not implied by convexity (the punctured plane
  gives a convex triangle that violates it, review of 2026-11-01), and the theorems of
  `PythagoreanPaper.Riemannian.Triangle` are kept there under the technical condition.
* For `K > 0`, the manuscript's "convex geodesic triangle" is read as: the three sides lie in an
  open hemisphere. For `K ≤ 0` no convexity hypothesis is needed.
* A geodesic triangle is `GeodesicTriangle` (three vertices and three selected unit-speed geodesic
  segments; the angle at a vertex is the angle between the initial velocities of the two sides
  leaving it); "nondegenerate" is `GeodesicTriangle.Nondegenerate` (no vertex lies on the opposite
  side).
-/

noncomputable section

open Set
open scoped Manifold

namespace PythagoreanPaper

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-! ### The Euclidean plane (`K = 0`) -/

namespace EuclideanPlane

variable (T : GeodesicTriangle 𝓘(ℝ, R2) R2)

/-- The cosine law (C9.3) for every geodesic triangle of the Euclidean plane (at `K = 0` the
formula `C_0(a) = C_0(b) C_0(c) + 0` holds trivially). -/
theorem cosine_law :
    C 0 T.a = C 0 T.b * C 0 T.c + 0 * S 0 T.b * S 0 T.c * Real.cos T.angleA ∧
      C 0 T.b = C 0 T.c * C 0 T.a + 0 * S 0 T.c * S 0 T.a * Real.cos T.angleB ∧
      C 0 T.c = C 0 T.a * C 0 T.b + 0 * S 0 T.a * S 0 T.b * Real.cos T.angleC :=
  T.cosine_law finrank_euclideanSpace_fin hasConstSectionalCurvature_euclidean
    (sidesInNormalBalls T)

/-- **The angles of a nondegenerate geodesic triangle of the Euclidean plane lie in `(0, π)`**
(C9.7). -/
theorem angle_pos_lt_pi (hnd : T.Nondegenerate) :
    (0 < T.angleA ∧ T.angleA < Real.pi) ∧ (0 < T.angleB ∧ T.angleB < Real.pi) ∧
      (0 < T.angleC ∧ T.angleC < Real.pi) :=
  T.angle_pos_lt_pi (sidesInNormalBalls T) hnd

end EuclideanPlane

/-! ### The hyperbolic plane (`K < 0`) -/

namespace HypPlane

variable {K : ℝ} [hK : Fact (K < 0)] (T : GeodesicTriangle 𝓘(ℝ, R2) (hypPlane K))

/-- **The cosine law** (C9.3) for every geodesic triangle of the hyperbolic plane of curvature
`K`. -/
theorem cosine_law :
    C K T.a = C K T.b * C K T.c + K * S K T.b * S K T.c * Real.cos T.angleA ∧
      C K T.b = C K T.c * C K T.a + K * S K T.c * S K T.a * Real.cos T.angleB ∧
      C K T.c = C K T.a * C K T.b + K * S K T.a * S K T.b * Real.cos T.angleC :=
  T.cosine_law finrank_euclideanSpace_fin hasConstSectionalCurvature (sidesInNormalBalls T)

/-- **The angles of a nondegenerate geodesic triangle of the hyperbolic plane lie in `(0, π)`**
(C9.7). -/
theorem angle_pos_lt_pi (hnd : T.Nondegenerate) :
    (0 < T.angleA ∧ T.angleA < Real.pi) ∧ (0 < T.angleB ∧ T.angleB < Real.pi) ∧
      (0 < T.angleC ∧ T.angleC < Real.pi) :=
  T.angle_pos_lt_pi (sidesInNormalBalls T) hnd

/-- **The sine law** (C9.1) for every nondegenerate geodesic triangle of the hyperbolic plane:
`sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)`. -/
theorem sine_law (hnd : T.Nondegenerate) :
    Real.sin T.angleA / S K T.a = Real.sin T.angleB / S K T.b ∧
      Real.sin T.angleB / S K T.b = Real.sin T.angleC / S K T.c :=
  T.sine_law finrank_euclideanSpace_fin hasConstSectionalCurvature hK.out.ne
    (sidesInNormalBalls T) hnd fun h ↦ absurd h (not_lt.2 hK.out.le)

/-- **The angles are the angles `A_K` of the cosine law** (C9.8, `K < 0`): for every geodesic
triangle of the hyperbolic plane, `A = angleK K a b c`, `B = angleK K b c a`,
`C = angleK K c a b`. -/
theorem angles_eq_angleK :
    T.angleA = angleK K T.a T.b T.c ∧ T.angleB = angleK K T.b T.c T.a ∧
      T.angleC = angleK K T.c T.a T.b :=
  T.angles_eq_angleK finrank_euclideanSpace_fin hasConstSectionalCurvature hK.out.ne
    (sidesInNormalBalls T) fun h ↦ absurd h (not_lt.2 hK.out.le)

end HypPlane

/-! ### The sphere (`K > 0`) -/

namespace SphereModel

variable {K : ℝ} [hK : Fact (0 < K)] (T : GeodesicTriangle 𝓘(ℝ, R2) (sph K))

/-- **The cosine law** (C9.3) for every geodesic triangle of the sphere of curvature `K` whose sides
lie in an open hemisphere. -/
theorem cosine_law (hT : InOpenHemisphere T) :
    C K T.a = C K T.b * C K T.c + K * S K T.b * S K T.c * Real.cos T.angleA ∧
      C K T.b = C K T.c * C K T.a + K * S K T.c * S K T.a * Real.cos T.angleB ∧
      C K T.c = C K T.a * C K T.b + K * S K T.a * S K T.b * Real.cos T.angleC :=
  T.cosine_law finrank_euclideanSpace_fin hasConstSectionalCurvature
    (sidesInNormalBalls_of_inOpenHemisphere T hT)

/-- **The angles of a nondegenerate geodesic triangle of the sphere lie in `(0, π)`** (C9.7), for
triangles whose sides lie in an open hemisphere. -/
theorem angle_pos_lt_pi (hT : InOpenHemisphere T) (hnd : T.Nondegenerate) :
    (0 < T.angleA ∧ T.angleA < Real.pi) ∧ (0 < T.angleB ∧ T.angleB < Real.pi) ∧
      (0 < T.angleC ∧ T.angleC < Real.pi) :=
  T.angle_pos_lt_pi (sidesInNormalBalls_of_inOpenHemisphere T hT) hnd

/-- **The sine law** (C9.1) on the sphere of curvature `K`: for a nondegenerate geodesic triangle
whose sides lie in an open hemisphere, with `0 < a, b, c < π/√K`,
`sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c)`. -/
theorem sine_law (hT : InOpenHemisphere T) (hnd : T.Nondegenerate)
    (hsides : T.a < Real.pi / √K ∧ T.b < Real.pi / √K ∧ T.c < Real.pi / √K) :
    Real.sin T.angleA / S K T.a = Real.sin T.angleB / S K T.b ∧
      Real.sin T.angleB / S K T.b = Real.sin T.angleC / S K T.c :=
  T.sine_law finrank_euclideanSpace_fin hasConstSectionalCurvature hK.out.ne'
    (sidesInNormalBalls_of_inOpenHemisphere T hT) hnd fun _ ↦ hsides

/-- **The angles are the angles `A_K` of the cosine law** (C9.8, `K > 0`), for triangles whose
sides lie in an open hemisphere, with `0 < a, b, c < π/√K`. -/
theorem angles_eq_angleK (hT : InOpenHemisphere T)
    (hsides : T.a < Real.pi / √K ∧ T.b < Real.pi / √K ∧ T.c < Real.pi / √K) :
    T.angleA = angleK K T.a T.b T.c ∧ T.angleB = angleK K T.b T.c T.a ∧
      T.angleC = angleK K T.c T.a T.b :=
  T.angles_eq_angleK finrank_euclideanSpace_fin hasConstSectionalCurvature hK.out.ne'
    (sidesInNormalBalls_of_inOpenHemisphere T hT) fun _ ↦ hsides

end SphereModel

end PythagoreanPaper
