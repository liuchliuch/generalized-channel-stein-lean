import QuantumChannelStein.PinchingGramBound

/-! # Concrete matrix Cauchy--Schwarz for finite branch sums -/
noncomputable section
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The checked variance identity for finite Gram sums. -/
theorem sum_gram_domination {ι u v : Type*} [Fintype ι] [Fintype u] [Fintype v]
    [DecidableEq u] [DecidableEq v] (A : ι → Matrix u v ℂ) :
    ((Fintype.card ι : ℝ) • (∑ i, A i * (A i)ᴴ) -
      (∑ i, A i) * (∑ i, A i)ᴴ).PosSemidef :=
  SpectralPinching.gram_sum_le_card A

end GeneralizedChannelStein
