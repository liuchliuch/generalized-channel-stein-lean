import GeneralizedChannelStein.TestingMinimax
import Mathlib.Topology.Order.Monotone

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal OperationalTesting Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {a b : ℕ}

/-- Single-alternative optimum with an actual reference-assisted pure tester. -/
def singleBeta (N M : KrausChannel a b) (ε : ℝ) : ENNReal :=
  ⨅ t : {t : UnitPureInput a a × Effect (a*b) //
    1-ε ≤ t.2.probability (pureOutput N t.1)},
    ENNReal.ofReal (t.val.2.probability (pureOutput M t.val.1))

/-- Operational composite optimization expressed in actual raw primal coordinates. -/
def primalBeta (N : KrausChannel a b) (F : Set (MatrixMap a b)) (ε : ℝ) : ENNReal :=
  ⨅ x : testerSet N ε, ⨆ M : FreeChannel F, ENNReal.ofReal (testerValue x.val M.val.choi)

def primalSingleBeta (N M : KrausChannel a b) (ε : ℝ) : ENNReal :=
  ⨅ x : testerSet N ε, ENNReal.ofReal (testerValue x.val M.choi)

def choiBeta (N : KrausChannel a b) (C : Set (BipartiteOperator a b)) (ε : ℝ) : ENNReal :=
  ⨅ x : testerSet N ε, ⨆ M : C, ENNReal.ofReal (testerValue x.val M.val)

/-- Singular input marginals are covered by the proved simultaneous realization. -/
theorem compositeBeta_eq_primal (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) (ε : ℝ) : compositeBeta N F ε = primalBeta N F ε := by
  rw [compositeBeta_eq_pure]
  apply le_antisymm
  · apply le_iInf
    intro x
    obtain ⟨ψ,T,h⟩ := exists_uniform_primal_realization (primalOfMem x.val x.property.1)
    refine iInf_le_of_le ⟨(ψ,T), ?_⟩ ?_
    · rw [h]
      exact x.property.2
    · simp only [h]
      rfl
  · apply le_iInf
    intro t
    let P := pureTestPrimal t.val.1 t.val.2
    have hp : (P.omega.matrix,P.Q) ∈ testerSet N ε :=
      ⟨P.mem_primalSet, by
        change 1-ε ≤ P.value N.choi
        dsimp [P]
        rw [pureTestPrimal_acceptance]
        exact t.property⟩
    refine iInf_le_of_le ⟨(P.omega.matrix,P.Q),hp⟩ ?_
    have h : ∀ M : FreeChannel F,
        testerValue (P.omega.matrix,P.Q) M.val.choi =
          t.val.2.probability (pureOutput M.val t.val.1) := by
      intro M
      exact pureTestPrimal_acceptance M.val t.val.1 t.val.2
    simp only [h,le_refl]

theorem singleBeta_eq_primal (N M : KrausChannel a b) (ε : ℝ) :
    singleBeta N M ε = primalSingleBeta N M ε := by
  apply le_antisymm
  · apply le_iInf
    intro x
    obtain ⟨ψ,T,h⟩ := exists_uniform_primal_realization (primalOfMem x.val x.property.1)
    refine iInf_le_of_le ⟨(ψ,T), ?_⟩ ?_
    · rw [h]
      exact x.property.2
    · rw [h]
      rfl
  · apply le_iInf
    intro t
    let P := pureTestPrimal t.val.1 t.val.2
    have hp : (P.omega.matrix,P.Q) ∈ testerSet N ε :=
      ⟨P.mem_primalSet, by
        change 1-ε ≤ P.value N.choi
        dsimp [P]
        rw [pureTestPrimal_acceptance]
        exact t.property⟩
    refine iInf_le_of_le ⟨(P.omega.matrix,P.Q),hp⟩ ?_
    exact le_of_eq (congrArg ENNReal.ofReal (pureTestPrimal_acceptance M t.val.1 t.val.2))

/-- Passing from redundant Kraus witnesses to their Choi image loses no alternatives. -/
theorem primalBeta_eq_choiBeta (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M) (ε : ℝ) :
    primalBeta N F ε = choiBeta N (MatrixMap.choi '' F) ε := by
  apply congrArg iInf
  funext x
  apply le_antisymm
  · apply iSup_le
    intro M
    exact le_iSup_of_le ⟨M.val.choi, M.val.toLinearMap,M.property,rfl⟩ le_rfl
  · apply iSup_le
    intro C
    obtain ⟨M,hM,hC⟩ := C.property
    obtain ⟨K,hK⟩ := (isChannel_iff_kraus M).mp (hF M hM)
    refine le_iSup_of_le ⟨K,hK ▸ hM⟩ ?_
    have hc : K.choi = C.val := by rw [← MatrixMap.choi_toLinearMap,hK,hC]
    rw [hc]

/-- Bounded real suprema commute with the standard probability embedding. -/
theorem ofReal_ciSup {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : BddAbove (Set.range f)) :
    ENNReal.ofReal (⨆ i, f i) = ⨆ i, ENNReal.ofReal (f i) :=
  Monotone.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    (fun _ _ h => ENNReal.ofReal_le_ofReal h) hf

end GeneralizedChannelStein
