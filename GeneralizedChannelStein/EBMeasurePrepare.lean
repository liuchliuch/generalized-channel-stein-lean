import GeneralizedChannelStein.EntanglementBreakingFamilies

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.EBMeasurePrepare
open QuantumChannelStein Matrix ChannelEntropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b k : ℕ}

/-- Literal finite measurement followed by preparation of normalized states. -/
def preparedMap (E : Fin k → Operator a) (σ : Fin k → State b) : MatrixMap a b where
  toFun X := ∑ i, (E i*X).trace • (σ i).matrix
  map_add' X Y := by simp [Matrix.mul_add,Matrix.trace_add,add_smul,Finset.sum_add_distrib]
  map_smul' z X := by simp [Matrix.trace_smul,smul_smul,Finset.smul_sum]

theorem preparedMap_choi (E : Fin k → Operator a) (σ : Fin k → State b) :
    MatrixMap.choi (preparedMap E σ) = ∑ i, (E i)ᵀ ⊗ₖ (σ i).matrix := by
  ext ⟨u,x⟩ ⟨v,y⟩
  simp [MatrixMap.choi,preparedMap,Matrix.sum_apply,Matrix.trace,Matrix.diag,
    Matrix.mul_apply,Matrix.single,Matrix.kroneckerMap_apply,Matrix.transpose_apply,ite_and]

/-- Every measurement effect is an actual Effect; the POVM is normalized by its sum. -/
def HasMeasurePrepare (Φ : KrausChannel a b) : Prop :=
  ∃ k : ℕ, ∃ E : Fin k → Effect a, ∃ σ : Fin k → State b,
    (∑ i, (E i).matrix)=1 ∧ Φ.toLinearMap=preparedMap (fun i => (E i).matrix) σ

theorem effect_of_positive_partition (E : Fin k → Operator a) (hE : ∀ i, (E i).PosSemidef)
    (hsum : ∑ i, E i=1) (i : Fin k) : (1-E i).PosSemidef := by
  classical
  have hp : (∑ j ∈ Finset.univ.erase i, E j).PosSemidef := by
    apply Finset.sum_induction
    · intro X Y hX hY; exact hX.add hY
    · exact Matrix.PosSemidef.zero
    · intro j _; exact hE j
  have he := Finset.sum_erase_add Finset.univ E (Finset.mem_univ i)
  rw [hsum] at he
  have heq : (1-E i)=(∑ j ∈ Finset.univ.erase i, E j) := (eq_sub_iff_add_eq.mpr he).symm
  rwa [heq]

/-- Zero output factors are normalized using the proved harmless fallback, with zero POVM weight. -/
theorem measurePrepare_of_separable (Φ : KrausChannel a b) (hb : 0<b)
    (hΦ : Separable Φ.choi) : HasMeasurePrepare Φ := by
  obtain ⟨k,A,B,hA,hB,hC⟩ := hΦ
  let σ : Fin k → State b := fun i => normalizePositive hb (B i) (hB i)
  let E : Fin k → Operator a := fun i => (B i).trace.re • (A i)ᵀ
  have hE (i : Fin k) : (E i).PosSemidef :=
    (hA i).transpose.smul (Complex.nonneg_iff.mp (hB i).trace_nonneg).1
  have hchoi : Φ.choi = ∑ i, (E i)ᵀ ⊗ₖ (σ i).matrix := by
    rw [hC]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [E,σ]
    rw [Matrix.transpose_smul,Matrix.transpose_transpose,Matrix.smul_kronecker,
      ← Matrix.kronecker_smul,normalizePositive_recover]
  have hsum : ∑ i, E i=1 := by
    have htrace := Φ.traceOutput_choi
    rw [hchoi] at htrace
    have he : KrausChannel.traceOutput (∑ i, (E i)ᵀ ⊗ₖ (σ i).matrix) = (∑ i, E i)ᵀ := by
      ext u v
      simp only [KrausChannel.traceOutput,Matrix.sum_apply,Matrix.kroneckerMap_apply,
        Matrix.transpose_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      change (∑ i, E i v u*(σ i).matrix.trace) = _
      simp only [(σ _).trace_one,mul_one]
    rw [he] at htrace
    have hh := congrArg Matrix.transpose htrace
    simpa only [Matrix.transpose_transpose,Matrix.transpose_one] using hh
  let effects : Fin k → Effect a := fun i => ⟨E i,hE i,effect_of_positive_partition E hE hsum i⟩
  refine ⟨k,effects,σ,hsum,?_⟩
  apply MatrixMap.choi_injective
  rw [MatrixMap.choi_toLinearMap,preparedMap_choi]
  exact hchoi

theorem separable_of_measurePrepare (Φ : KrausChannel a b) (hΦ : HasMeasurePrepare Φ) :
    Separable Φ.choi := by
  obtain ⟨k,E,σ,hsum,hmap⟩ := hΦ
  rw [← MatrixMap.choi_toLinearMap,hmap,preparedMap_choi]
  exact Separable.sum _ (fun i => Separable.product (E i).positive.transpose (σ i).positive)

theorem separable_choi_iff_measurePrepare (Φ : KrausChannel a b) (hb : 0<b) :
    Separable Φ.choi ↔ HasMeasurePrepare Φ :=
  ⟨measurePrepare_of_separable Φ hb,separable_of_measurePrepare Φ⟩

/-- Operational entanglement breaking is equivalent to a finite normalized POVM/preparation realization. -/
theorem entanglementBreaking_iff_measurePrepare (Φ : KrausChannel a b) (hb : 0<b) :
    IsEntanglementBreaking Φ ↔ HasMeasurePrepare Φ :=
  (entanglementBreaking_iff_separable_choi Φ).trans (separable_choi_iff_measurePrepare Φ hb)


/-- On normalized inputs the coefficients are the literal Born probabilities. -/
theorem preparedMap_state_action (E : Fin k → Effect a) (σ : Fin k → State b) (ρ : State a) :
    preparedMap (fun i => (E i).matrix) σ ρ.matrix =
      ∑ i, (E i).probability ρ • (σ i).matrix := by
  unfold preparedMap
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  have htrace : ((E i).matrix*ρ.matrix).trace = ((E i).probability ρ:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (trace_mul_nonnegative (E i).positive ρ.positive)).2.symm
  rw [htrace]
  rfl

theorem normalized_povm_probabilities (E : Fin k → Effect a) (hsum : ∑ i, (E i).matrix=1)
    (ρ : State a) : (∀ i, 0≤(E i).probability ρ) ∧ ∑ i, (E i).probability ρ=1 := by
  refine ⟨fun i => (E i).probability_nonneg ρ,?_⟩
  unfold Effect.probability
  rw [← Complex.re_sum,← Matrix.trace_sum,← Matrix.sum_mul,hsum,Matrix.one_mul,ρ.trace_one]
  rfl

end GeneralizedChannelStein.EBMeasurePrepare
