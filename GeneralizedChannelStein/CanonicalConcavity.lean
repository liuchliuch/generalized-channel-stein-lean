import GeneralizedChannelStein.EntropyMinimax
import GeneralizedChannelStein.EntropyFlags

/-! Flagged-purification proof of concavity in the physical input marginal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CanonicalConcavity
open QuantumChannelStein Matrix ChannelEntropy PureReferenceRecovery EntropyContinuity CanonicalInput
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {n m : ℕ}

def flagCoefficient (ψ φ : UnitPureInput n n) (p : ℝ) : Matrix (Fin (n+n)) (Fin n) ℂ :=
  fun r i => Sum.elim (fun z => (Real.sqrt p : ℂ)*ψ.val (z,i))
    (fun z => (Real.sqrt (1-p) : ℂ)*φ.val (z,i)) (finSumFinEquiv.symm r)

@[simp] theorem flagCoefficient_left (ψ φ : UnitPureInput n n) (p : ℝ) (r i : Fin n) :
    flagCoefficient ψ φ p (finSumFinEquiv (Sum.inl r)) i = (Real.sqrt p : ℂ)*ψ.val (r,i) := by
  simp only [flagCoefficient,Equiv.symm_apply_apply,Sum.elim_inl]
@[simp] theorem flagCoefficient_right (ψ φ : UnitPureInput n n) (p : ℝ) (r i : Fin n) :
    flagCoefficient ψ φ p (finSumFinEquiv (Sum.inr r)) i = (Real.sqrt (1-p) : ℂ)*φ.val (r,i) := by
  simp only [flagCoefficient,Equiv.symm_apply_apply,Sum.elim_inr]

theorem flagCoefficient_gram (ψ φ : UnitPureInput n n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (flagCoefficient ψ φ p)ᴴ * flagCoefficient ψ φ p =
      p•(inputDensity ψ).matrix+(1-p)•(inputDensity φ).matrix := by
  ext i j
  rw [Matrix.mul_apply]
  have heq := finSumFinEquiv.sum_comp (fun z => (flagCoefficient ψ φ p)ᴴ i z * flagCoefficient ψ φ p z j)
  rw [← heq,Fintype.sum_sum_type]
  simp only [Matrix.conjTranspose_apply,flagCoefficient_left,flagCoefficient_right,map_mul,
    Complex.star_def,Complex.conj_ofReal,Matrix.add_apply,Matrix.smul_apply,inputDensity,
    Matrix.mul_apply,coefficientMatrix,Complex.real_smul,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro z _
  · have hs : (Real.sqrt p : ℂ)*(Real.sqrt p : ℂ)=(p:ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hp
    calc
      _ = ((Real.sqrt p:ℂ)*(Real.sqrt p:ℂ)) * (starRingEnd ℂ (ψ.val (z,i))*ψ.val (z,j)) := by ring
      _ = _ := by rw [hs]
  · have hs : (Real.sqrt (1-p) : ℂ)*(Real.sqrt (1-p) : ℂ)=((1-p:ℝ):ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hp1)
    calc
      _ = ((Real.sqrt (1-p):ℂ)*(Real.sqrt (1-p):ℂ)) * (starRingEnd ℂ (φ.val (z,i))*φ.val (z,j)) := by ring
      _ = _ := by rw [hs]

def rectangularVector {r : ℕ} (S : Matrix (Fin r) (Fin n) ℂ) : EuclideanSpace ℂ (Fin r×Fin n) :=
  WithLp.toLp 2 (fun x => S x.1 x.2)

theorem rectangularVector_norm_sq {r : ℕ} (S : Matrix (Fin r) (Fin n) ℂ) :
    ‖rectangularVector S‖^2=(Sᴴ*S).trace.re := by
  rw [Matrix.trace_mul_comm]
  simp [EuclideanSpace.norm_sq_eq,rectangularVector,Matrix.trace,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,← Complex.normSq_eq_norm_sq,Complex.mul_conj]

/-- The normalized coherent flag is a genuine pure input with enlarged reference. -/
def flagInput (ψ φ : UnitPureInput n n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : UnitPureInput (n+n) n :=
  ⟨rectangularVector (flagCoefficient ψ φ p),by
    have h := rectangularVector_norm_sq (flagCoefficient ψ φ p)
    rw [flagCoefficient_gram ψ φ p hp hp1,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
      (inputDensity ψ).trace_one,(inputDensity φ).trace_one] at h
    simp only [Complex.add_re,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one] at h
    have hn := norm_nonneg (rectangularVector (flagCoefficient ψ φ p))
    nlinarith⟩

theorem inputDensity_flagInput (ψ φ : UnitPureInput n n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    inputDensity (flagInput ψ φ p hp hp1)=mix (inputDensity ψ) (inputDensity φ) p hp hp1 := by
  apply state_eq_of_matrix_eq
  exact flagCoefficient_gram ψ φ p hp hp1

/-- The coherent flag of two canonical purifications has the mixed physical marginal. -/
theorem canonical_flag_density (ρ σ : State n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    inputDensity (flagInput (input ρ) (input σ) p hp hp1)=transposeState (mix ρ σ p hp hp1) := by
  rw [inputDensity_flagInput,input,input,inputDensity_densityInput,inputDensity_densityInput]
  apply state_eq_of_matrix_eq
  ext i j
  rfl

def flagMask (n : ℕ) (left : Bool) (i : Fin (n+n)) : ℂ :=
  match finSumFinEquiv.symm i with
  | Sum.inl _ => if left then 1 else 0
  | Sum.inr _ => if left then 0 else 1

/-- Actual two-Kraus dephasing of the classical flag. -/
def dephase (n : ℕ) : KrausChannel (n+n) (n+n) where
  rank := 2
  kraus := ![Matrix.diagonal (flagMask n true),Matrix.diagonal (flagMask n false)]
  normalized := by
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i=j
    · subst j
      obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
      cases i <;> simp [-finSumFinEquiv_apply_left,-finSumFinEquiv_apply_right,flagMask]
    · simp [Matrix.diagonal_apply_ne _ h,Matrix.one_apply_ne h]

theorem dephase_apply_index (X : Operator (n+n)) (i j : Fin n ⊕ Fin n) :
    (dephase n).apply X (finSumFinEquiv i) (finSumFinEquiv j) =
      match i,j with
      | Sum.inl _, Sum.inl _ => X (finSumFinEquiv i) (finSumFinEquiv j)
      | Sum.inr _, Sum.inr _ => X (finSumFinEquiv i) (finSumFinEquiv j)
      | _,_ => 0 := by
  cases i <;> cases j <;>
    simp [-finSumFinEquiv_apply_left,-finSumFinEquiv_apply_right,dephase,KrausChannel.apply,Fin.sum_univ_two,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul,Matrix.mul_diagonal,flagMask]

def outputRegroup (n m : ℕ) : Fin ((n+n)*m) ≃ Fin (n*m+n*m) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl (Fin m))).trans
      ((Equiv.sumProdDistrib (Fin n) (Fin n) (Fin m)).trans
        ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)))

@[simp] theorem outputRegroup_left (i : Fin n) (u : Fin m) :
    (outputRegroup n m).symm (finSumFinEquiv (Sum.inl (finProdFinEquiv (i,u)))) =
      finProdFinEquiv (finSumFinEquiv (Sum.inl i),u) := by
  simp [-finSumFinEquiv_apply_left,-finSumFinEquiv_apply_right,outputRegroup,Equiv.sumProdDistrib]
@[simp] theorem outputRegroup_right (i : Fin n) (u : Fin m) :
    (outputRegroup n m).symm (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,u)))) =
      finProdFinEquiv (finSumFinEquiv (Sum.inr i),u) := by
  simp [-finSumFinEquiv_apply_left,-finSumFinEquiv_apply_right,outputRegroup,Equiv.sumProdDistrib]

theorem flagInput_pure_left (ψ φ : UnitPureInput n n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (i j : Fin n) :
    (fun u v => pureMatrix (flagInput ψ φ p hp hp1).val
      (finSumFinEquiv (Sum.inl i),u) (finSumFinEquiv (Sum.inl j),v)) =
      (p:ℂ)•(fun u v => pureMatrix ψ.val (i,u) (j,v)) := by
  ext u v
  simp only [pureMatrix,flagInput,rectangularVector,WithLp.ofLp_toLp,Matrix.vecMulVec_apply,Pi.star_apply,flagCoefficient_left,Pi.smul_apply,smul_eq_mul]
  change ((Real.sqrt p:ℂ)*ψ.val (i,u))*star ((Real.sqrt p:ℂ)*ψ.val (j,v)) =
    (p:ℂ)*(ψ.val (i,u)*star (ψ.val (j,v)))
  have hs : (Real.sqrt p:ℂ)*(Real.sqrt p:ℂ)=(p:ℂ) := by exact_mod_cast Real.mul_self_sqrt hp
  simp only [StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt p:ℂ)*(Real.sqrt p:ℂ))*(ψ.val (i,u)*starRingEnd ℂ (ψ.val (j,v))) := by ring
    _ = _ := by rw [hs]

theorem flagInput_pure_right (ψ φ : UnitPureInput n n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (i j : Fin n) :
    (fun u v => pureMatrix (flagInput ψ φ p hp hp1).val
      (finSumFinEquiv (Sum.inr i),u) (finSumFinEquiv (Sum.inr j),v)) =
      ((1-p:ℝ):ℂ)•(fun u v => pureMatrix φ.val (i,u) (j,v)) := by
  ext u v
  simp only [pureMatrix,flagInput,rectangularVector,WithLp.ofLp_toLp,Matrix.vecMulVec_apply,Pi.star_apply,flagCoefficient_right,Pi.smul_apply,smul_eq_mul]
  change ((Real.sqrt (1-p):ℂ)*φ.val (i,u))*star ((Real.sqrt (1-p):ℂ)*φ.val (j,v)) =
    ((1-p:ℝ):ℂ)*(φ.val (i,u)*star (φ.val (j,v)))
  have hs : (Real.sqrt (1-p):ℂ)*(Real.sqrt (1-p):ℂ)=((1-p:ℝ):ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hp1)
  simp only [StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (1-p):ℂ)*(Real.sqrt (1-p):ℂ))*(φ.val (i,u)*starRingEnd ℂ (φ.val (j,v))) := by ring
    _ = _ := by rw [hs]

theorem pureOutput_flag_left (Φ : KrausChannel n m) (ψ φ : UnitPureInput n n)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (i j : Fin n) (u v : Fin m) :
    (pureOutput Φ (flagInput ψ φ p hp hp1)).matrix
      (finProdFinEquiv (finSumFinEquiv (Sum.inl i),u)) (finProdFinEquiv (finSumFinEquiv (Sum.inl j),v)) =
      (p:ℂ)*(pureOutput Φ ψ).matrix (finProdFinEquiv (i,u)) (finProdFinEquiv (j,v)) := by
  simp only [pureOutput_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rw [KrausChannel.amplify_block,flagInput_pure_left,Φ.apply_smul,KrausChannel.amplify_block]
  rfl

theorem pureOutput_flag_right (Φ : KrausChannel n m) (ψ φ : UnitPureInput n n)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (i j : Fin n) (u v : Fin m) :
    (pureOutput Φ (flagInput ψ φ p hp hp1)).matrix
      (finProdFinEquiv (finSumFinEquiv (Sum.inr i),u)) (finProdFinEquiv (finSumFinEquiv (Sum.inr j),v)) =
      ((1-p:ℝ):ℂ)*(pureOutput Φ φ).matrix (finProdFinEquiv (i,u)) (finProdFinEquiv (j,v)) := by
  simp only [pureOutput_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rw [KrausChannel.amplify_block,flagInput_pure_right,Φ.apply_smul,KrausChannel.amplify_block]
  rfl

/-- Dephasing the actual coherent output gives the literal flagged mixture. -/
theorem dephase_output (Φ : KrausChannel n m) (ψ φ : UnitPureInput n n)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (dephase (n*m)).onState ((pureOutput Φ (flagInput ψ φ p hp hp1)).reindex (outputRegroup n m)) =
      EntropyFlags.flagState (pureOutput Φ ψ) (pureOutput Φ φ) p hp hp1 := by
  apply state_eq_of_matrix_eq
  ext i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  change (dephase (n*m)).apply _ (finSumFinEquiv i) (finSumFinEquiv j) = _
  rw [dephase_apply_index]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      obtain ⟨⟨i,u⟩,rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j,v⟩,rfl⟩ := finProdFinEquiv.surjective j
      simp only [State.reindex_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,outputRegroup_left,
        EntropyFlags.flagState,Equiv.symm_apply_apply]
      rw [pureOutput_flag_left]
      rfl
    | inr j =>
      simp only [EntropyFlags.flagState,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
      rfl
  | inr i =>
    cases j with
    | inl j =>
      simp only [EntropyFlags.flagState,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
      rfl
    | inr j =>
      obtain ⟨⟨i,u⟩,rfl⟩ := finProdFinEquiv.surjective i
      obtain ⟨⟨j,v⟩,rfl⟩ := finProdFinEquiv.surjective j
      simp only [State.reindex_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,outputRegroup_right,
        EntropyFlags.flagState,Equiv.symm_apply_apply]
      rw [pureOutput_flag_right]
      rfl

/-- The interior-weight input concavity follows from actual flag dephasing,
the full direct-sum identity, and the constructed reference recovery. -/
theorem value_concave_input_interior (N M : KrausChannel n m) (ρ σ : State n)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (p:EReal)*value N M ρ+((1-p:ℝ):EReal)*value N M σ ≤
      value N M (mix ρ σ p hp.le hp1.le) := by
  let ψ := flagInput (input ρ) (input σ) p hp.le hp1.le
  have hd := RelativeEntropy.umegaki_data_processing (dephase (n*m))
    ((pureOutput N ψ).reindex (outputRegroup n m)) ((pureOutput M ψ).reindex (outputRegroup n m))
  rw [dephase_output,dephase_output,RelativeEntropy.umegaki_reindex,
    EntropyFlags.umegaki_flag _ _ _ _ p hp hp1] at hd
  have hc := DivergenceOptimization.pure_reference_le_canonical
    (fun ρ σ => RelativeEntropy.umegaki ρ σ)
    (fun Φ ρ σ => RelativeEntropy.umegaki_data_processing Φ ρ σ) N M ψ
  rw [canonical_flag_density] at hc
  exact hd.trans hc

theorem mix_zero (ρ σ : State n) : mix ρ σ 0 (by norm_num) (by norm_num)=σ := by
  apply state_eq_of_matrix_eq
  simp [mix]
theorem mix_one (ρ σ : State n) : mix ρ σ 1 (by norm_num) (by norm_num)=ρ := by
  apply state_eq_of_matrix_eq
  simp [mix]

/-- Full canonical-input concavity, allowing singular states, zero mixing
weights, and infinite divergences exactly as in Lemma 32. -/
theorem value_concave_input (N M : KrausChannel n m) (ρ σ : State n)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (p:EReal)*value N M ρ+((1-p:ℝ):EReal)*value N M σ ≤ value N M (mix ρ σ p hp hp1) := by
  by_cases h0 : p=0
  · subst p
    rw [mix_zero]
    simp
  · by_cases h1 : p=1
    · subst p
      rw [mix_one]
      simp
    · exact value_concave_input_interior N M ρ σ p (lt_of_le_of_ne hp (Ne.symm h0)) (lt_of_le_of_ne hp1 h1)

end GeneralizedChannelStein.CanonicalConcavity
