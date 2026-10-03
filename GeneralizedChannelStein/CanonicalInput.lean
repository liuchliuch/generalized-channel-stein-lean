import GeneralizedChannelStein.EntropyContinuity
import QuantumChannelStein.DivergenceOptimization

/-! Canonical purification parametrized by the physical input marginal.
The older densityInput uses the transposed marginal; this module proves
and records the required transpose instead of changing that convention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CanonicalInput
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {n m r : ℕ}

def transposeState (ρ : State n) : State n where
  matrix := ρ.matrixᵀ
  positive := ρ.positive.transpose
  trace_one := by rw [Matrix.trace_transpose,ρ.trace_one]

@[simp] theorem transposeState_transpose (ρ : State n) : transposeState (transposeState ρ)=ρ := by
  cases ρ
  rfl

def transposeEquiv : State n ≃ State n where
  toFun := transposeState
  invFun := transposeState
  left_inv := transposeState_transpose
  right_inv := transposeState_transpose

theorem sqrt_transpose (ρ : State n) : CFC.sqrt ρ.matrixᵀ = (CFC.sqrt ρ.matrix)ᵀ := by
  apply (CFC.sqrt_eq_iff _ _ ρ.positive.transpose.nonneg
    (CFC.sqrt_nonneg ρ.matrix).posSemidef.transpose.nonneg).mpr
  rw [← Matrix.transpose_mul,CFC.sqrt_mul_sqrt_self _ ρ.positive.nonneg]

/-- Canonical purification whose physical input marginal is ρ. -/
def input (ρ : State n) : UnitPureInput n n := TestingPrimal.densityInput (transposeState ρ)

/-- In reference-input coordinates its entries are `(sqrt ρ)_(input,reference)`. -/
theorem input_apply (ρ : State n) (i j : Fin n) : (input ρ).val (i,j) = CFC.sqrt ρ.matrix j i := by
  change CFC.sqrt ρ.matrixᵀ i j = _
  rw [sqrt_transpose]
  rfl

def physicalMarginal (ψ : UnitPureInput r n) : Operator n :=
  fun i j => ∑ z : Fin r, pureMatrix ψ.val (z,i) (z,j)

def referenceMarginal (ψ : UnitPureInput r n) : Operator r :=
  fun i j => ∑ z : Fin n, pureMatrix ψ.val (i,z) (j,z)

/-- The input Gram in the reference-recovery infrastructure is transposed
relative to the physical partial trace. -/
theorem physicalMarginal_eq_gram_transpose (ψ : UnitPureInput r n) :
    physicalMarginal ψ = (PureReferenceRecovery.inputDensity ψ).matrixᵀ := by
  ext i j
  simp only [physicalMarginal,PureReferenceRecovery.inputDensity,Matrix.transpose_apply,
    Matrix.mul_apply,pureMatrix,Matrix.vecMulVec_apply,Pi.star_apply,Matrix.conjTranspose_apply,
    PureReferenceRecovery.coefficientMatrix]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem inputDensity_densityInput (ρ : State n) :
    PureReferenceRecovery.inputDensity (TestingPrimal.densityInput ρ)=ρ := by
  apply ChannelEntropy.state_eq_of_matrix_eq
  change (CFC.sqrt ρ.matrix)ᴴ * CFC.sqrt ρ.matrix = ρ.matrix
  rw [(CFC.sqrt_nonneg ρ.matrix).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self _ ρ.positive.nonneg]

/-- Exact physical input marginal, including singular states. -/
@[simp] theorem physicalMarginal_input (ρ : State n) : physicalMarginal (input ρ)=ρ.matrix := by
  rw [physicalMarginal_eq_gram_transpose,input,inputDensity_densityInput]
  rfl

/-- Exact reference marginal in the paper's vectorization convention. -/
@[simp] theorem referenceMarginal_input (ρ : State n) : referenceMarginal (input ρ)=ρ.matrixᵀ := by
  have h : referenceMarginal (input ρ) =
      CFC.sqrt ρ.matrixᵀ * (CFC.sqrt ρ.matrixᵀ)ᴴ := by
    ext i j
    simp [referenceMarginal,input,TestingPrimal.densityInput,TestingPrimal.coefficientVector,
      transposeState,pureMatrix,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [h,(CFC.sqrt_nonneg ρ.matrixᵀ).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self _ ρ.positive.transpose.nonneg]

def output (Φ : KrausChannel n m) (ρ : State n) : State (n*m) := pureOutput Φ (input ρ)
def value (Φ Ψ : KrausChannel n m) (ρ : State n) : EReal := umegaki (output Φ ρ) (output Ψ ρ)

theorem output_matrix (Φ : KrausChannel n m) (ρ : State n) :
    (output Φ ρ).matrix = Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((CFC.sqrt ρ.matrixᵀ ⊗ₖ (1:Operator m)) * Φ.choi *
        (CFC.sqrt ρ.matrixᵀ ⊗ₖ (1:Operator m))ᴴ) :=
  DivergenceOptimization.canonical_output_matrix Φ (transposeState ρ)

theorem value_nonneg (Φ Ψ : KrausChannel n m) (ρ : State n) : 0≤value Φ Ψ ρ := umegaki_nonneg _ _

theorem value_le_channelD (Φ Ψ : KrausChannel n m) (ρ : State n) : value Φ Ψ ρ≤channelD Φ Ψ :=
  le_iSup (fun ψ : UnitPureInput n n => umegaki (pureOutput Φ ψ) (pureOutput Ψ ψ)) (input ρ)

/-- The exact all-pure channel entropy is the supremum over physical input marginals. -/
theorem channelD_eq_sup (Φ Ψ : KrausChannel n m) : channelD Φ Ψ = ⨆ ρ : State n, value Φ Ψ ρ := by
  have h := DivergenceOptimization.channelValue_eq_density_sup
    (fun ρ σ => umegaki ρ σ) (fun Φ ρ σ => umegaki_data_processing Φ ρ σ) Φ Ψ
  change channelD Φ Ψ = _ at h
  rw [h]
  apply le_antisymm
  · apply iSup_le
    intro ρ
    exact le_iSup_of_le (transposeState ρ) (by simp [value,output,input])
  · apply iSup_le
    intro ρ
    exact le_iSup_of_le (transposeState ρ) le_rfl

/-- The literal compact convex domain of physical density matrices. -/
def densitySet (n : ℕ) : Set (Operator n) := {X | X.PosSemidef ∧ X.trace=1}
def ofDensity (ρ : densitySet n) : State n := ⟨ρ.val,ρ.property.1,ρ.property.2⟩

theorem isClosed_densitySet (n : ℕ) : IsClosed (densitySet n) := by
  letI : CStarAlgebra (Operator n) := CStarAlgebra.mk
  have ht : Continuous (fun X : Operator n => X.trace) := by unfold Matrix.trace; fun_prop
  have h : IsClosed {X : Operator n | 0≤X ∧ X.trace=1} :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_eq ht continuous_const)
  simpa only [densitySet,Matrix.nonneg_iff_posSemidef] using h

theorem isCompact_densitySet (n : ℕ) : IsCompact (densitySet n) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_densitySet n)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1,?_⟩
  intro X hX
  exact TestingSDP.state_norm_le_one (ofDensity ⟨X,hX⟩)

theorem convex_densitySet (n : ℕ) : Convex ℝ (densitySet n) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul ha).add (hY.1.smul hb),?_⟩
  rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,hX.2,hY.2]
  simp only [Complex.real_smul,mul_one]
  exact_mod_cast hab

theorem continuous_canonical_root :
    Continuous (fun ρ : densitySet n => CFC.sqrt ρ.valᵀ) := by
  letI : CStarAlgebra (Operator n) := CStarAlgebra.mk
  apply CFC.continuousOn_sqrt.comp_continuous (by fun_prop)
  intro ρ
  exact ρ.property.1.transpose.nonneg

/-- Canonical purification is continuous even at singular physical inputs. -/
theorem continuous_input : Continuous (fun ρ : densitySet n => (input (ofDensity ρ)).val) := by
  have h := continuous_canonical_root (n:=n)
  change Continuous (fun ρ : densitySet n => TestingPrimal.coefficientVector (CFC.sqrt ρ.valᵀ))
  have hc : Continuous (TestingPrimal.coefficientVector : Operator n → EuclideanSpace ℂ (Fin n×Fin n)) := by
    unfold TestingPrimal.coefficientVector
    fun_prop
  exact hc.comp h

/-- The joint Choi/output expression used before imposing channel constraints. -/
def outputFromChoi (ρ : densitySet n) (C : Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ) : Operator (n*m) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((CFC.sqrt ρ.valᵀ ⊗ₖ (1:Operator m))*C*(CFC.sqrt ρ.valᵀ ⊗ₖ (1:Operator m))ᴴ)

theorem continuous_outputFromChoi : Continuous (fun p : densitySet n × Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ =>
    outputFromChoi p.1 p.2) := by
  have hs : Continuous (fun p : densitySet n × Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ => CFC.sqrt p.1.valᵀ) :=
    continuous_canonical_root.comp continuous_fst
  have hkr : Continuous (fun p : densitySet n × Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ =>
      CFC.sqrt p.1.valᵀ ⊗ₖ (1:Operator m)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((continuous_apply _).comp ((continuous_apply _).comp hs)).mul continuous_const
  unfold outputFromChoi
  fun_prop

end GeneralizedChannelStein.CanonicalInput
