import QuantumChannelStein.Choi
import QuantumChannelStein.Testing

/-!
# Concrete feasible matrices and weak duality for channel testing

This file develops the primal and dual matrix constraints of Lemma 4.1 in
arXiv:2609.27196v1. The trace pairing and weak-duality bound are proved for
actual finite matrices. Strong duality and identification with the operational
channel-testing quantity are separate obligations, not assumptions here.
-/

set_option maxHeartbeats 800000
noncomputable section
namespace QuantumChannelStein.TestingSDP
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

abbrev BipartiteOperator (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

/-- Concrete primal variables: a density matrix and a PSD test variable
bounded by its tensor product with the output identity. -/
structure PrimalFeasible (a b : ℕ) where
  omega : State a
  Q : BipartiteOperator a b
  positive : Q.PosSemidef
  dominated : ((omega.matrix ⊗ₖ (1 : Operator b)) - Q).PosSemidef

/-- Concrete dual variable for the Hermitian difference of Choi matrices. -/
structure DualFeasible {a b : ℕ} (Delta : BipartiteOperator a b) where
  Y : BipartiteOperator a b
  positive : Y.PosSemidef
  dominates : (Y - Delta).PosSemidef

/-- The real trace objective of a primal feasible pair. -/
def PrimalFeasible.value {a b : ℕ} (P : PrimalFeasible a b)
    (Delta : BipartiteOperator a b) : ℝ := (Delta * P.Q).trace.re

/-- The dual objective is the Hilbert operator norm of the output partial trace. -/
def DualFeasible.value {a b : ℕ} {Delta : BipartiteOperator a b}
    (D : DualFeasible Delta) : ℝ := ‖KrausChannel.traceOutput D.Y‖

/-- PSD trace pairing for arbitrary finite coordinate types, including products. -/
theorem trace_pairing_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A = Cᴴ * C at hC
  rw [hC, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

/-- The output partial trace is a positive map. -/
theorem traceOutput_positive {a b : ℕ} {Y : BipartiteOperator a b}
    (hY : Y.PosSemidef) : (KrausChannel.traceOutput Y).PosSemidef := by
  have hsum : KrausChannel.traceOutput Y =
      ∑ j : Fin b, Y.submatrix (fun i : Fin a => (i, j)) (fun i : Fin a => (i, j)) := by
    ext i k
    simp [KrausChannel.traceOutput, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro j _
    exact hY.submatrix _

/-- The trace/Kronecker pairing defining the SDP's partial-trace adjoint. -/
theorem traceOutput_pairing {a b : ℕ} (omega : Operator a) (Y : BipartiteOperator a b) :
    (Y * (omega ⊗ₖ (1 : Operator b))).trace =
      (KrausChannel.traceOutput Y * omega).trace := by
  rw [Matrix.trace_mul_comm Y, Matrix.trace_mul_comm (KrausChannel.traceOutput Y)]
  exact (trace_partialTrace_duality omega Y).symm

/-- A density-matrix expectation of a positive operator is at most its
Hilbert operator norm. -/
theorem trace_state_pairing_le_norm {a : ℕ} (omega : State a) {A : Operator a}
    (hA : A.PosSemidef) : (A * omega.matrix).trace.re ≤ ‖A‖ := by
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  have hle : A ≤ ‖A‖ • (1 : Operator a) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hA.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
  have hpos : (‖A‖ • (1 : Operator a) - A).PosSemidef := hle
  have ht := trace_pairing_nonnegative hpos omega.positive
  have hre := (Complex.nonneg_iff.mp ht).1
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, omega.trace_one, Complex.sub_re, Complex.real_smul,
    Complex.ofReal_re, mul_one] at hre
  linarith

/-- Matrix weak duality, before packaging the primal and dual feasible sets. -/
theorem weak_duality_matrices {a b : ℕ} (omega : State a)
    (Delta Q Y : BipartiteOperator a b)
    (hQ : Q.PosSemidef) (hupper : ((omega.matrix ⊗ₖ (1 : Operator b)) - Q).PosSemidef)
    (hY : Y.PosSemidef) (hDelta : (Y - Delta).PosSemidef) :
    (Delta * Q).trace.re ≤ ‖KrausChannel.traceOutput Y‖ := by
  have hfirst := (Complex.nonneg_iff.mp (trace_pairing_nonnegative hDelta hQ)).1
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hfirst
  have hsecond := (Complex.nonneg_iff.mp (trace_pairing_nonnegative hY hupper)).1
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hsecond
  rw [traceOutput_pairing] at hsecond
  have hnorm := trace_state_pairing_le_norm omega (traceOutput_positive hY)
  linarith

/-- Every primal feasible objective is bounded by every dual feasible objective.
No strong-duality hypothesis is used. -/
theorem weak_duality {a b : ℕ} {Delta : BipartiteOperator a b}
    (P : PrimalFeasible a b) (D : DualFeasible Delta) : P.value Delta ≤ D.value :=
  weak_duality_matrices P.omega Delta P.Q D.Y P.positive P.dominated D.positive D.dominates

/-- Each eigenvalue of a positive matrix is at most its trace. -/
theorem eigenvalue_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (i : ι) :
    hA.isHermitian.eigenvalues i ≤ A.trace.re := by
  have htrace : A.trace.re = ∑ j, hA.isHermitian.eigenvalues j := by
    simpa using congrArg Complex.re hA.isHermitian.trace_eq_sum_eigenvalues
  rw [htrace]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- A positive matrix is bounded in Löwner order by its trace times the identity. -/
theorem positive_le_trace_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    A ≤ A.trace.re • (1 : Matrix ι ι ℂ) := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => ((A.trace.re - hA.isHermitian.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (eigenvalue_le_trace hA i), by simp⟩
  have hdiag : Matrix.diagonal (fun i => ((A.trace.re - hA.isHermitian.eigenvalues i : ℝ) : ℂ)) =
      A.trace.re • (1 : Matrix ι ι ℂ) - Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, Complex.real_smul]
    · simp [Matrix.diagonal, hij]
  have hU : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := unitary.coe_mul_star_self U
  have hspec : (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ = A := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem.symm
  have hc := hd.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, hspec] at hc
  exact hc

/-- For a positive matrix, the operator norm is at most the real trace. -/
theorem positive_norm_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : ‖A‖ ≤ A.trace.re := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have htr : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  apply (CStarAlgebra.norm_le_iff_le_algebraMap A htr hA.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using positive_le_trace_smul_one hA

/-- The operator norm of a density matrix is at most one. -/
theorem state_norm_le_one {a : ℕ} (omega : State a) : ‖omega.matrix‖ ≤ 1 := by
  simpa only [omega.trace_one, Complex.one_re] using positive_norm_le_trace omega.positive

/-- A feasible primal test variable has operator norm at most one. -/
theorem PrimalFeasible.norm_Q_le_one {a b : ℕ} (P : PrimalFeasible a b) : ‖P.Q‖ ≤ 1 := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have hle : P.Q ≤ P.omega.matrix ⊗ₖ (1 : Operator b) := P.dominated
  exact (CStarAlgebra.norm_le_norm_of_nonneg_of_le P.positive.nonneg hle).trans
    ((TensorNorm.kronecker_one_opNorm_le P.omega.matrix).trans (state_norm_le_one P.omega))

/-- Tensoring a positive matrix with the identity preserves positivity. -/
theorem kronecker_one_positive {a b : ℕ} {A : Operator a} (hA : A.PosSemidef) :
    (A ⊗ₖ (1 : Operator b)).PosSemidef := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A = Cᴴ * C at hC
  have h : (C ⊗ₖ (1 : Operator b))ᴴ * (C ⊗ₖ (1 : Operator b)) =
      A ⊗ₖ (1 : Operator b) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, ← hC]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The raw primal feasible set in its finite-dimensional ambient vector space. -/
def primalSet (a b : ℕ) : Set (Operator a × BipartiteOperator a b) :=
  {p | p.1.PosSemidef ∧ p.1.trace = 1 ∧ p.2.PosSemidef ∧
    ((p.1 ⊗ₖ (1 : Operator b)) - p.2).PosSemidef}

/-- Package a raw feasible pair as the concrete primal structure. -/
def primalOfMem {a b : ℕ} (p : Operator a × BipartiteOperator a b)
    (hp : p ∈ primalSet a b) : PrimalFeasible a b where
  omega := ⟨p.1, hp.1, hp.2.1⟩
  Q := p.2
  positive := hp.2.2.1
  dominated := hp.2.2.2

/-- Every primal structure determines a point of the raw feasible set. -/
theorem PrimalFeasible.mem_primalSet {a b : ℕ} (P : PrimalFeasible a b) :
    (P.omega.matrix, P.Q) ∈ primalSet a b :=
  ⟨P.omega.positive, P.omega.trace_one, P.positive, P.dominated⟩

/-- The finite-dimensional primal constraints define a closed set. -/
theorem isClosed_primalSet (a b : ℕ) : IsClosed (primalSet a b) := by
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have htrace : Continuous (fun p : Operator a × BipartiteOperator a b => p.1.trace) := by
    unfold Matrix.trace
    fun_prop
  have hkr : Continuous (fun p : Operator a × BipartiteOperator a b => p.1 ⊗ₖ (1 : Operator b)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun p : Operator a × BipartiteOperator a b =>
      p.1 i.1 j.1 * (1 : Operator b) i.2 j.2)
    fun_prop
  have hclosed : IsClosed {p : Operator a × BipartiteOperator a b |
      0 ≤ p.1 ∧ p.1.trace = 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1 ⊗ₖ (1 : Operator b)} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_eq htrace continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd hkr)))
  simpa only [primalSet, Matrix.nonneg_iff_posSemidef, Matrix.le_iff, sub_zero] using hclosed

/-- All primal feasible pairs lie in the ambient unit ball. -/
theorem primalSet_norm_le_one {a b : ℕ} {p : Operator a × BipartiteOperator a b}
    (hp : p ∈ primalSet a b) : ‖p‖ ≤ 1 := by
  let P := primalOfMem p hp
  change max ‖p.1‖ ‖p.2‖ ≤ 1
  exact max_le (state_norm_le_one P.omega) P.norm_Q_le_one

/-- The primal feasible set is compact, using genuine closedness and the
proved uniform operator-norm bounds. -/
theorem isCompact_primalSet (a b : ℕ) : IsCompact (primalSet a b) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_primalSet a b)
  exact isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hp => primalSet_norm_le_one hp⟩

/-- A density matrix provides a feasible zero test, without any restriction on
the output dimension. -/
def zeroPrimal {a : ℕ} (omega : State a) (b : ℕ) : PrimalFeasible a b where
  omega := omega
  Q := 0
  positive := Matrix.PosSemidef.zero
  dominated := by simpa using (kronecker_one_positive (b := b) omega.positive)

/-- The primal maximum is attained whenever the input density-matrix space is
nonempty. This does not identify its value with the dual minimum. -/
theorem exists_primal_maximizer {a b : ℕ} (omega0 : State a)
    (Delta : BipartiteOperator a b) :
    ∃ P : PrimalFeasible a b, ∀ P' : PrimalFeasible a b, P'.value Delta ≤ P.value Delta := by
  have hcont : Continuous (fun p : Operator a × BipartiteOperator a b => (Delta * p.2).trace.re) := by
    unfold Matrix.trace
    fun_prop
  obtain ⟨p, hp, hmax⟩ := (isCompact_primalSet a b).exists_isMaxOn
    ⟨((zeroPrimal omega0 b).omega.matrix, (zeroPrimal omega0 b).Q),
      (zeroPrimal omega0 b).mem_primalSet⟩ hcont.continuousOn
  refine ⟨primalOfMem p hp, ?_⟩
  intro P'
  exact hmax P'.mem_primalSet

/-- The full trace is preserved by the output partial trace. -/
theorem trace_traceOutput {a b : ℕ} (Y : BipartiteOperator a b) :
    (KrausChannel.traceOutput Y).trace = Y.trace := by
  simp [KrausChannel.traceOutput, Matrix.trace, Fintype.sum_prod_type]

/-- The trace of a positive matrix is at most its dimension times its operator norm. -/
theorem positive_trace_le_card_mul_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : A.trace.re ≤ Fintype.card ι * ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have hle : A ≤ ‖A‖ • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hA.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
  have hp : (‖A‖ • (1 : Matrix ι ι ℂ) - A).PosSemidef := hle
  have hre := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Complex.mul_re] at hre
  nlinarith

/-- A positive bipartite matrix has norm controlled by the dual objective,
with only the input dimension as a multiplicative factor. -/
theorem positive_norm_le_input_dim_mul_partial_norm {a b : ℕ}
    {Y : BipartiteOperator a b} (hY : Y.PosSemidef) :
    ‖Y‖ ≤ (a : ℝ) * ‖KrausChannel.traceOutput Y‖ := by
  calc
    ‖Y‖ ≤ Y.trace.re := positive_norm_le_trace hY
    _ = (KrausChannel.traceOutput Y).trace.re := by rw [trace_traceOutput]
    _ ≤ (a : ℝ) * ‖KrausChannel.traceOutput Y‖ := by
      simpa only [Fintype.card_fin] using positive_trace_le_card_mul_norm (traceOutput_positive hY)

/-- Continuity of the concrete output partial-trace map. -/
theorem continuous_traceOutput (a b : ℕ) :
    Continuous (fun Y : BipartiteOperator a b => KrausChannel.traceOutput Y) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun Y : BipartiteOperator a b => ∑ k : Fin b, Y (i, k) (j, k))
  fun_prop

/-- A closed sublevel set of feasible dual matrices. -/
def dualSublevelSet {a b : ℕ} (Delta : BipartiteOperator a b) (c : ℝ) :
    Set (BipartiteOperator a b) :=
  {Y | Y.PosSemidef ∧ (Y - Delta).PosSemidef ∧ ‖KrausChannel.traceOutput Y‖ ≤ c}

/-- Feasible dual sublevels are closed. -/
theorem isClosed_dualSublevelSet {a b : ℕ} (Delta : BipartiteOperator a b) (c : ℝ) :
    IsClosed (dualSublevelSet Delta c) := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have hclosed : IsClosed {Y : BipartiteOperator a b |
      0 ≤ Y ∧ 0 ≤ Y - Delta ∧ ‖KrausChannel.traceOutput Y‖ ≤ c} :=
    (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_const (continuous_id.sub continuous_const)).inter
        (isClosed_le (continuous_traceOutput a b).norm continuous_const))
  simpa only [dualSublevelSet, Matrix.nonneg_iff_posSemidef] using hclosed

/-- Feasible dual sublevels are compact; the positive trace controls the
matrix norm even though the full dual feasible cone is unbounded. -/
theorem isCompact_dualSublevelSet {a b : ℕ} (Delta : BipartiteOperator a b) (c : ℝ) :
    IsCompact (dualSublevelSet Delta c) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_dualSublevelSet Delta c)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(a : ℝ) * c, ?_⟩
  intro Y hY
  exact (positive_norm_le_input_dim_mul_partial_norm hY.1).trans
    (mul_le_mul_of_nonneg_left hY.2.2 (Nat.cast_nonneg a))

/-- A feasible dual witness guarantees attainment of the global dual minimum.
No relation between the primal and dual optimal values is assumed. -/
theorem exists_dual_minimizer {a b : ℕ} {Delta : BipartiteOperator a b}
    (D0 : DualFeasible Delta) :
    ∃ D : DualFeasible Delta, ∀ D' : DualFeasible Delta, D.value ≤ D'.value := by
  have hD0 : D0.Y ∈ dualSublevelSet Delta D0.value := ⟨D0.positive, D0.dominates, le_rfl⟩
  obtain ⟨Y, hY, hmin⟩ := (isCompact_dualSublevelSet Delta D0.value).exists_isMinOn
    ⟨D0.Y, hD0⟩ (continuous_traceOutput a b).norm.continuousOn
  let D : DualFeasible Delta := ⟨Y, hY.1, hY.2.1⟩
  refine ⟨D, ?_⟩
  intro D'
  by_cases hcost : D'.value ≤ D0.value
  · exact hmin ⟨D'.positive, D'.dominates, hcost⟩
  · exact (hmin hD0).trans (le_of_not_ge hcost)

/-- Every Hermitian objective matrix has an explicit feasible dual witness. -/
def normDual {a b : ℕ} (Delta : BipartiteOperator a b) (hDelta : Delta.IsHermitian) :
    DualFeasible Delta := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  refine ⟨‖Delta‖ • 1, Matrix.PosSemidef.one.smul (norm_nonneg Delta), ?_⟩
  change Delta ≤ ‖Delta‖ • (1 : BipartiteOperator a b)
  simpa only [Algebra.algebraMap_eq_smul_one] using hDelta.isSelfAdjoint.le_algebraMap_norm_self

/-- The dual minimum is attained for every Hermitian objective matrix. -/
theorem exists_dual_minimizer_of_hermitian {a b : ℕ}
    (Delta : BipartiteOperator a b) (hDelta : Delta.IsHermitian) :
    ∃ D : DualFeasible Delta, ∀ D' : DualFeasible Delta, D.value ≤ D'.value :=
  exists_dual_minimizer (normDual Delta hDelta)

/-- The PSD cone is self-dual under the real trace pairing, proved using
rank-one positive matrices and the Hermitian quadratic-form criterion. -/
theorem positive_iff_trace_pairing_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ Y : Matrix ι ι ℂ, Y.PosSemidef → 0 ≤ (A * Y).trace.re := by
  constructor
  · intro h Y hY
    exact (Complex.nonneg_iff.mp (trace_pairing_nonnegative h hY)).1
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro x
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hA.im_star_dotProduct_mulVec_self x).symm⟩
    have ht := h (Matrix.vecMulVec x (star x)) (Matrix.posSemidef_vecMulVec_self_star x)
    simpa only [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] using ht

/-- Failure of a Hermitian PSD constraint has an actual positive trace
separator. This is the matrix-cone witness needed for penalty or separation
arguments toward strong duality. -/
theorem exists_positive_negative_trace_of_not_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hnot : ¬ A.PosSemidef) :
    ∃ Y : Matrix ι ι ℂ, Y.PosSemidef ∧ (A * Y).trace.re < 0 := by
  have h : ¬ ∀ Y : Matrix ι ι ℂ, Y.PosSemidef → 0 ≤ (A * Y).trace.re := by
    intro h
    exact hnot ((positive_iff_trace_pairing_nonnegative hA).mpr h)
  push_neg at h
  exact h

/-- The positive matrix cone is convex over the real scalars. -/
theorem convex_positiveCone {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Convex ℝ {Y : Matrix ι ι ℂ | Y.PosSemidef} := by
  intro X hX Y hY r s hr hs _
  exact (hX.smul hr).add (hY.smul hs)

end QuantumChannelStein.TestingSDP
