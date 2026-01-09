import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace ARK.Physics
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Energy Landscape f(x) -/
structure PotentialFunction (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  val : E → ℝ
  smooth : ContDiff ℝ 2 val

/-- Gradient via Riesz Representation -/
def gradient (f : PotentialFunction E) (x : E) : E :=
  let df := fderiv ℝ f.val x
  (InnerProductSpace.toDual ℝ E).symm df

/-- Hessian via Second Derivative -/
def hessian (f : PotentialFunction E) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient f) x

/-- The Witten-Laplacian: Δ_f = -Δ + |∇f|² + Hess(f) -/
def WittenLaplacian (f : PotentialFunction E) (x : E) : E →L[ℝ] E :=
  let term_laplacian := -(ContinuousLinearMap.id ℝ E)
  let term_potential := (‖gradient f x‖ ^ 2) • (ContinuousLinearMap.id ℝ E)
  let term_hessian := hessian f x
  term_laplacian + term_potential + term_hessian

end
end ARK.Physics
