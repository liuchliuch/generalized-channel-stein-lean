import GeneralizedChannelStein.DominatedEntropyContinuity
import GeneralizedChannelStein.CanonicalConcavity
import GeneralizedChannelStein.DimensionDomination
import QuantumChannelStein.CovariantOptimization
import QuantumChannelStein.FaithfulDensity

/-! Genuine canonical entropy maximizers, including the symmetric optimizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CanonicalAttainment
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy CanonicalInput DominatedEntropyContinuity
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {n m : ℕ}

def toDensity (ρ : State n) : densitySet n := ⟨ρ.matrix,ρ.positive,ρ.trace_one⟩
@[simp] theorem ofDensity_toDensity (ρ : State n) : ofDensity (toDensity ρ)=ρ := by cases ρ; rfl

def finiteValue (N M : KrausChannel n m) (ρ : densitySet n) : ℝ :=
  traceFormula (output N (ofDensity ρ)) (output M (ofDensity ρ))

def canonicalPair (N M : KrausChannel n m) (K : ℝ)
    (hdom : MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap)) (ρ : densitySet n) : dominatedPairs (n*m) K :=
  ⟨(toDensity (output N (ofDensity ρ)),toDensity (output M (ofDensity ρ))),
    pureOutput_domination N M K hdom (input (ofDensity ρ))⟩

theorem continuous_output_matrix (N : KrausChannel n m) :
    Continuous (fun ρ : densitySet n => (output N (ofDensity ρ)).matrix) := by
  have h := continuous_outputFromChoi.comp (continuous_id.prodMk (continuous_const (y:=N.choi)))
  convert h using 1
  funext ρ
  exact output_matrix N (ofDensity ρ)

theorem continuous_canonicalPair (N M : KrausChannel n m) (K : ℝ)
    (hdom : MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap)) : Continuous (canonicalPair N M K hdom) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact (continuous_output_matrix N).subtype_mk _
  · exact (continuous_output_matrix M).subtype_mk _

/-- Actual finiteness and continuity for every input under one fixed CP bound. -/
theorem continuous_finiteValue (N M : KrausChannel n m) (K : ℝ) (hK : 0≤K)
    (hdom : MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap)) : Continuous (finiteValue N M) := by
  have hf := continuous_traceFormula (n:=n*m) K hK
  have hc := continuous_canonicalPair N M K hdom
  have h := hf.comp hc
  simpa only [finiteValue,canonicalPair,pairFirst,pairSecond,ofDensity_toDensity] using h

theorem value_eq_finiteValue (N M : KrausChannel n m) (K : ℝ)
    (hdom : MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap)) (ρ : densitySet n) :
    value N M (ofDensity ρ) = (finiteValue N M ρ : EReal) :=
  umegaki_dominated K (canonicalPair N M K hdom ρ)

/-- The input supremum is attained on the literal compact density domain. -/
theorem exists_maximizer_of_cpLe (N M : KrausChannel n m) (K : ℝ) (hK : 0≤K)
    (hdom : MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap)) (hn : 0<n) :
    ∃ ρ : State n, value N M ρ=channelD N M := by
  letI : CompactSpace (densitySet n) := (isCompact_iff_compactSpace).mp (isCompact_densitySet n)
  letI : Nonempty (densitySet n) := ⟨toDensity (FaithfulDensity.maximallyMixed n hn)⟩
  obtain ⟨ρ,_,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_finiteValue N M K hK hdom).continuousOn
  refine ⟨ofDensity ρ,le_antisymm (value_le_channelD N M _) ?_⟩
  rw [channelD_eq_sup]
  apply iSup_le
  intro σ
  have h := hmax (Set.mem_univ (toDensity σ))
  rw [← ofDensity_toDensity σ,value_eq_finiteValue N M K hdom,value_eq_finiteValue N M K hdom]
  exact EReal.coe_le_coe_iff.mpr h

/-- For finite-group covariance the maximum has an invariant physical
input marginal. The orbit flag and its recovery are actual channels. -/
theorem exists_invariant_maximizer_of_cpLe
    {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (p : G→*Equiv.Perm (Fin n)) (q : G→*Equiv.Perm (Fin m))
    (N M : KrausChannel n m) (hN : CovariantOrbitRecovery.Covariant p q N)
    (hM : CovariantOrbitRecovery.Covariant p q M)
    (K : ℝ) (hK : 0≤K) (hdom : MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap)) (hn : 0<n) :
    ∃ ρ : State n, (∀ g, Matrix.reindex (p g) (p g) ρ.matrix=ρ.matrix) ∧ value N M ρ=channelD N M := by
  obtain ⟨ρ,hρ⟩ := exists_maximizer_of_cpLe N M K hK hdom hn
  let ω := CovariantOrbitInput.averageDensity p (PureReferenceRecovery.inputDensity (input ρ))
  refine ⟨transposeState ω,?_,?_⟩
  · intro g
    have h := congrArg Matrix.transpose (CovariantOrbitInput.averageDensity_invariant p
      (PureReferenceRecovery.inputDensity (input ρ)) g)
    exact h
  · have h := CovariantOptimization.pure_le_invariant_canonical
      (fun ρ σ => umegaki ρ σ) (fun Φ ρ σ => umegaki_data_processing Φ ρ σ)
      p q N M hN hM (input ρ)
    have heq : value N M (transposeState ω) =
        umegaki (pureOutput N (TestingPrimal.densityInput ω)) (pureOutput M (TestingPrimal.densityInput ω)) := by
      simp only [value,output,input,transposeState_transpose]
    rw [← heq] at h
    change value N M ρ≤value N M (transposeState ω) at h
    rw [hρ] at h
    exact le_antisymm (value_le_channelD N M _) h

/-- Rescale an actual positive channel component, without assuming a
representation or entropy comparison. -/
theorem cpLe_of_positive_component (N R M : KrausChannel n m) (c η : ℝ)
    (hc : 0≤c) (hη : 0<η)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap))
    (hRM : MatrixMap.CPLe ((η:ℂ)•R.toLinearMap) M.toLinearMap) :
    MatrixMap.CPLe N.toLinearMap (((c/η:ℝ):ℂ)•M.toLinearMap) := by
  apply MatrixMap.cpLe_trans hNR
  have h := MatrixMap.completelyPositive_smul (div_nonneg hc hη.le) hRM
  change MatrixMap.CompletelyPositive _
  convert h using 1
  rw [smul_sub,smul_smul]
  have heq : (((c/η:ℝ):ℂ)*(η:ℂ))=(c:ℂ) := by exact_mod_cast div_mul_cancel₀ c hη.ne'
  rw [heq]

theorem exists_domination_of_positive_replacer (N M : KrausChannel n m) (ω : State m)
    (hω : ω.matrix.PosDef) (η : ℝ) (hη : 0<η)
    (hM : MatrixMap.CPLe ((η:ℂ)•(ReplacerChannel.channel n ω).toLinearMap) M.toLinearMap) :
    ∃ K : ℝ, 0≤K ∧ MatrixMap.CPLe N.toLinearMap ((K:ℂ)•M.toLinearMap) := by
  let hm := MatrixOperatorBridge.state_dimension_pos ω
  let w := DimensionDomination.minEigenvalue ω hm
  have hw : 0<w := DimensionDomination.minEigenvalue_pos ω hm hω
  have hbound := DimensionDomination.cpLe_replacer_of_lower_bound N ω w hw
    (DimensionDomination.scalar_le_of_eigenvalue_lower ω w (DimensionDomination.minEigenvalue_le ω hm))
  refine ⟨((m:ℝ)/w)/η,div_nonneg (div_nonneg (Nat.cast_nonneg _) hw.le) hη.le,?_⟩
  exact cpLe_of_positive_component N (ReplacerChannel.channel n ω) M ((m:ℝ)/w) η
    (div_nonneg (Nat.cast_nonneg _) hw.le) hη hbound hM

/-- The exact fixed-channel symmetric-maximizer clause of Lemma32, stated
for any finite permutation action and a genuine faithful replacer component. -/
theorem exists_invariant_maximizer_of_positive_replacer
    {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (p : G→*Equiv.Perm (Fin n)) (q : G→*Equiv.Perm (Fin m))
    (N M : KrausChannel n m) (hN : CovariantOrbitRecovery.Covariant p q N)
    (hM : CovariantOrbitRecovery.Covariant p q M) (hn : 0<n)
    (ω : State m) (hω : ω.matrix.PosDef) (η : ℝ) (hη : 0<η)
    (hR : MatrixMap.CPLe ((η:ℂ)•(ReplacerChannel.channel n ω).toLinearMap) M.toLinearMap) :
    ∃ ρ : State n, (∀ g, Matrix.reindex (p g) (p g) ρ.matrix=ρ.matrix) ∧ value N M ρ=channelD N M := by
  obtain ⟨K,hK,hdom⟩ := exists_domination_of_positive_replacer N M ω hω η hη hR
  exact exists_invariant_maximizer_of_cpLe p q N M hN hM K hK hdom hn

end GeneralizedChannelStein.CanonicalAttainment
