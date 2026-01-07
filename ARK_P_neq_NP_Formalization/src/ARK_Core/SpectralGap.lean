import «ARK_Core».WittenOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace ARK.Spectral
open ARK.Physics
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def OperatorSpectrum (f : PotentialFunction E) (x : E) : Set ℝ :=
  spectrum ℝ (WittenLaplacian f x)

/-- The Spectral Gap: Infimum of positive eigenvalues -/
def SpectralGap (f : PotentialFunction E) (x : E) : ℝ :=
  sInf { v | v ∈ OperatorSpectrum f x ∧ v > 0 }

end
end ARK.Spectral
