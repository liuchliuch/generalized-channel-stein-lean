import GeneralizedChannelStein.EntanglementBreaking
import QuantumChannelStein.FaithfulDensity

/-! Normalized bases of the separable cone, with finite convex decompositions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem positive_trace_eq_real {d : ℕ} {X : Operator d} (hX : X.PosSemidef) :
    X.trace = (X.trace.re:ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hX.trace_nonneg).2.symm

/-- Normalize a positive matrix; zero trace uses an irrelevant faithful fallback. -/
def normalizePositive {d : ℕ} (hd : 0<d) (X : Operator d) (hX : X.PosSemidef) : State d := by
  by_cases ht : 0<X.trace.re
  · refine ⟨(X.trace.re)⁻¹ • X,hX.smul (inv_nonneg.mpr ht.le),?_⟩
    rw [Matrix.trace_smul,positive_trace_eq_real hX,Complex.real_smul,←Complex.ofReal_mul,Complex.ofReal_re,
      inv_mul_cancel₀ ht.ne',Complex.ofReal_one]
  · exact FaithfulDensity.maximallyMixed d hd

theorem normalizePositive_recover {d : ℕ} (hd : 0<d) (X : Operator d) (hX : X.PosSemidef) :
    X.trace.re • (normalizePositive hd X hX).matrix = X := by
  by_cases ht : 0<X.trace.re
  · simp only [normalizePositive,dif_pos ht,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  · have ht0 : X.trace.re=0 := le_antisymm (le_of_not_gt ht) (Complex.nonneg_iff.mp hX.trace_nonneg).1
    have hnorm := positive_norm_le_trace hX
    rw [ht0] at hnorm
    have hz : X=0 := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
    rw [ht0,zero_smul,hz]

def productStateMatrices (a b : ℕ) : Set (BipartiteOperator a b) :=
  {C | ∃ ρ : State a, ∃ σ : State b, C=ρ.matrix ⊗ₖ σ.matrix}

def separableStateMatrices (a b : ℕ) : Set (BipartiteOperator a b) :=
  convexHull ℝ (productStateMatrices a b)

theorem convex_separable (a b : ℕ) : Convex ℝ {C : BipartiteOperator a b | Separable C} := by
  intro C hC D hD r s hr hs hrs
  exact (hC.smul hr).add (hD.smul hs)

theorem separable_of_mem_convexHull {C : BipartiteOperator a b}
    (hC : C ∈ separableStateMatrices a b) : Separable C := by
  apply (convexHull_min ?_ (convex_separable a b)) hC
  rintro X ⟨ρ,σ,rfl⟩
  exact Separable.product ρ.positive σ.positive

theorem trace_one_of_mem_separableStateMatrices {C : BipartiteOperator a b}
    (hC : C ∈ separableStateMatrices a b) : C.trace=1 := by
  have hconv : Convex ℝ {C : BipartiteOperator a b | C.trace=1} := by
    intro C hC D hD r s hr hs hrs
    change (r • C+s • D).trace=1
    rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,hC,hD,←add_smul,hrs,one_smul]
  apply (convexHull_min ?_ hconv) hC
  rintro X ⟨ρ,σ,rfl⟩
  simp [Matrix.trace_kronecker,ρ.trace_one,σ.trace_one]

/-- Every trace-one element of the finite separable cone is a finite convex combination of states. -/
theorem mem_convexHull_of_separable_trace_one (ha : 0<a) (hb : 0<b)
    {C : BipartiteOperator a b} (hC : Separable C) (htr : C.trace=1) :
    C ∈ separableStateMatrices a b := by
  obtain ⟨k,A,B,hA,hB,hC⟩ := hC
  let ρ : Fin k → State a := fun i => normalizePositive ha (A i) (hA i)
  let σ : Fin k → State b := fun i => normalizePositive hb (B i) (hB i)
  let w : Fin k → ℝ := fun i => (A i).trace.re*(B i).trace.re
  have hw : ∀ i, 0≤w i := fun i => mul_nonneg
    (Complex.nonneg_iff.mp (hA i).trace_nonneg).1 (Complex.nonneg_iff.mp (hB i).trace_nonneg).1
  have he (i : Fin k) : w i • ((ρ i).matrix ⊗ₖ (σ i).matrix) = A i ⊗ₖ B i := by
    calc
      w i • ((ρ i).matrix ⊗ₖ (σ i).matrix) =
          ((A i).trace.re • (ρ i).matrix) ⊗ₖ ((B i).trace.re • (σ i).matrix) := by
        simp only [Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,w,mul_comm]
      _ = _ := by dsimp [ρ,σ]; rw [normalizePositive_recover,normalizePositive_recover]
  have hsum : ∑ i, w i=1 := by
    have hh := congrArg (fun X : BipartiteOperator a b => X.trace.re) hC
    change C.trace.re = (∑ i, A i ⊗ₖ B i).trace.re at hh
    rw [htr] at hh
    simp only [Complex.one_re,Matrix.trace_sum,Complex.re_sum,Matrix.trace_kronecker] at hh
    have hm (i : Fin k) : ((A i).trace*(B i).trace).re=w i := by
      rw [positive_trace_eq_real (hA i),positive_trace_eq_real (hB i)]
      simp [w]
    simpa only [hm] using hh.symm
  have he' : C=∑ i, w i • ((ρ i).matrix ⊗ₖ (σ i).matrix) := by
    rw [hC]
    apply Finset.sum_congr rfl; intro i hi
    simpa only [Matrix.smul_kronecker] using (he i).symm
  rw [he']
  apply (convex_convexHull ℝ (productStateMatrices a b)).sum_mem
    (fun i hi => hw i) hsum
  intro i hi
  exact subset_convexHull ℝ (productStateMatrices a b) ⟨ρ i,σ i,rfl⟩

/-- Exact equivalence, not a closure-based replacement for finite separability. -/
theorem separable_trace_one_iff (ha : 0<a) (hb : 0<b) (C : BipartiteOperator a b) :
    (Separable C ∧ C.trace=1) ↔ C ∈ separableStateMatrices a b :=
  ⟨fun h => mem_convexHull_of_separable_trace_one ha hb h.1 h.2,
    fun h => ⟨separable_of_mem_convexHull h,trace_one_of_mem_separableStateMatrices h⟩⟩


/-- Density matrices as a genuine compact set of coordinates. -/
def stateMatrixSet (d : ℕ) : Set (Operator d) := {X | X.PosSemidef ∧ X.trace=1}

theorem isCompact_stateMatrixSet (d : ℕ) : IsCompact (stateMatrixSet d) := by
  letI : CStarAlgebra (Operator d) := CStarAlgebra.mk
  have hc : IsClosed (stateMatrixSet d) := by
    have htrace : Continuous (fun X : Operator d => X.trace) := by unfold Matrix.trace; fun_prop
    have h : IsClosed {X : Operator d | 0≤X ∧ X.trace=1} :=
      (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq htrace continuous_const)
    simpa only [stateMatrixSet,Matrix.nonneg_iff_posSemidef] using h
  apply Metric.isCompact_of_isClosed_isBounded hc
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1,fun X hX => ?_⟩
  exact state_norm_le_one ⟨X,hX.1,hX.2⟩

theorem isCompact_productStateMatrices (a b : ℕ) : IsCompact (productStateMatrices a b) := by
  have hcont : Continuous (fun p : Operator a × Operator b => p.1 ⊗ₖ p.2) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    change Continuous (fun p : Operator a × Operator b => p.1 i.1 j.1*p.2 i.2 j.2)
    fun_prop
  have he : productStateMatrices a b = (fun p : Operator a × Operator b => p.1 ⊗ₖ p.2) ''
      (stateMatrixSet a ×ˢ stateMatrixSet b) := by
    ext C
    constructor
    · rintro ⟨ρ,σ,rfl⟩
      exact ⟨(ρ.matrix,σ.matrix),⟨⟨ρ.positive,ρ.trace_one⟩,⟨σ.positive,σ.trace_one⟩⟩,rfl⟩
    · rintro ⟨⟨X,Y⟩,⟨hX,hY⟩,rfl⟩
      exact ⟨⟨X,hX.1,hX.2⟩,⟨Y,hY.1,hY.2⟩,rfl⟩
  rw [he]
  exact ((isCompact_stateMatrixSet a).prod (isCompact_stateMatrixSet b)).image hcont

/-- A fixed positive trace converts the cone criterion into normalized finite separability. -/
theorem separable_fixed_trace_iff (ha : 0<a) (hb : 0<b) {C : BipartiteOperator a b}
    {t : ℝ} (ht : 0<t) (htr : C.trace=(t:ℂ)) :
    Separable C ↔ t⁻¹ • C ∈ separableStateMatrices a b := by
  constructor
  · intro hC
    apply mem_convexHull_of_separable_trace_one ha hb (hC.smul (inv_nonneg.mpr ht.le))
    rw [Matrix.trace_smul,htr,Complex.real_smul,←Complex.ofReal_mul,inv_mul_cancel₀ ht.ne',Complex.ofReal_one]
  · intro hC
    have h := (separable_of_mem_convexHull hC).smul ht.le
    simpa only [smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using h

end GeneralizedChannelStein
