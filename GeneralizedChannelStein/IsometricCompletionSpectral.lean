import GeneralizedChannelStein.IsometricCompletion

/-! Proposition 30 with the actual minimum eigenvalues used by the source. -/
noncomputable section
namespace GeneralizedChannelStein.IsometricCompletion
open QuantumChannelStein
open scoped ComplexOrder MatrixOrder

/-- No separate lower-bound or dimension-divisibility hypothesis is needed:
the specified faithful states supply their literal spectral minima. The
returned property remains uniform over every physical witness with these minima. -/
theorem proposition_30_minEigen {a d : ℕ} (ha : 0<a) (hd : 0<d)
    (τ : State a) (hτ : τ.matrix.PosDef) (ω : State d) (hω : ω.matrix.PosDef)
    (c : ℝ) (hc : 0<c) :
    ∃ K : ℝ, IsometricCompletionProperty a d
      (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hd) c K :=
  proposition_30 ha hd
    (DimensionDomination.minEigenvalue_pos τ ha hτ) (DimensionDomination.minEigenvalue_le_one τ ha)
    (DimensionDomination.minEigenvalue_pos ω hd hω) (DimensionDomination.minEigenvalue_le_one ω hd) hc

end GeneralizedChannelStein.IsometricCompletion
