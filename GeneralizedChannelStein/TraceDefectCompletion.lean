import GeneralizedChannelStein.Families
import GeneralizedChannelStein.UniformAuxiliary
import QuantumChannelStein.DiamondPureReduction

/-! # Actual trace-defect completion of CP trace-nonincreasing maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.TraceDefectCompletion
open QuantumChannelStein Matrix ChannelEntropy TestingSDP DiamondNorm
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- The literal Hilbert--Schmidt adjoint applied to the output identity. -/
def adjointIdentity (Q : MatrixMap a b) : Operator a :=
  (KrausChannel.traceOutput (MatrixMap.choi Q))ᵀ

/-- The trace defect I-Q†(I). -/
def defect (Q : MatrixMap a b) : Operator a := 1 - adjointIdentity Q

theorem adjointIdentity_pairing (Q : MatrixMap a b) (X : Operator a) :
    (adjointIdentity Q * X).trace = (Q X).trace := by
  have hX : X = ∑ i : Fin a, ∑ j : Fin a, X i j • Matrix.single i j 1 := by
    ext k l
    simp [Matrix.sum_apply, Matrix.single, ite_and, eq_comm]
  have hQX : Q X = ∑ i : Fin a, ∑ j : Fin a, X i j • Q (Matrix.single i j 1) := by
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul]
  rw [hQX]
  simp only [adjointIdentity, KrausChannel.traceOutput, MatrixMap.choi,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]

theorem adjointIdentity_positive (Q : MatrixMap a b) (hQ : MatrixMap.CompletelyPositive Q) :
    (adjointIdentity Q).PosSemidef :=
  (traceOutput_positive (MatrixMap.choi_positive_of_completelyPositive Q hQ)).transpose

theorem defect_pairing (Q : MatrixMap a b) (X : Operator a) :
    (defect Q * X).trace = X.trace - (Q X).trace := by
  rw [defect, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, adjointIdentity_pairing]

theorem defect_positive (Q : Subchannel a b) : (defect Q.toLinearMap).PosSemidef := by
  apply (positive_iff_trace_pairing_nonnegative
    (Matrix.isHermitian_one.sub (adjointIdentity_positive Q.toLinearMap Q.completelyPositive).isHermitian)).mpr
  intro X hX
  change 0 ≤ (defect Q.toLinearMap * X).trace.re
  rw [defect_pairing, Complex.sub_re]
  exact sub_nonneg.mpr (Q.trace_nonincreasing X hX)

theorem norm_defect_le_one (Q : Subchannel a b) : ‖defect Q.toLinearMap‖ ≤ 1 := by
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (defect_positive Q).nonneg).mpr
  change (1 - defect Q.toLinearMap).PosSemidef
  simpa [defect] using adjointIdentity_positive Q.toLinearMap Q.completelyPositive

/-- A positive effect's unnormalized trace-and-prepare CP map. -/
def weightedReplacer (D : Operator a) (ω : State b) : MatrixMap a b where
  toFun X := (D * X).trace • ω.matrix
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.trace_smul, smul_smul]

theorem choi_weightedReplacer (D : Operator a) (ω : State b) :
    MatrixMap.choi (weightedReplacer D ω) = Dᵀ ⊗ₖ ω.matrix := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [MatrixMap.choi, weightedReplacer, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.single, ite_and]

theorem weightedReplacer_cp (D : Operator a) (hD : D.PosSemidef) (ω : State b) :
    MatrixMap.CompletelyPositive (weightedReplacer D ω) := by
  apply (MatrixMap.completelyPositive_iff_choi_positive _).mpr
  rw [choi_weightedReplacer]
  exact MatrixMap.posSemidef_kronecker hD.transpose ω.positive

theorem weightedReplacer_trace (D : Operator a) (ω : State b) (X : Operator a) :
    ((weightedReplacer D ω) X).trace = (D * X).trace := by
  simp [weightedReplacer, Matrix.trace_smul, ω.trace_one]

theorem weightedReplacer_cpLe (D : Operator a) (hD : D.PosSemidef) (ω : State b) :
    MatrixMap.CPLe (weightedReplacer D ω)
      ((‖D‖ : ℂ) • (ReplacerChannel.channel a ω).toLinearMap) := by
  have hbound : (‖D‖ • (1 : Operator a) - D).PosSemidef := by
    letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
    exact (show D ≤ ‖D‖ • (1 : Operator a) by
      simpa only [Algebra.algebraMap_eq_smul_one] using hD.isHermitian.isSelfAdjoint.le_algebraMap_norm_self)
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul,
    MatrixMap.choi_toLinearMap, ReplacerChannel.channel_choi, choi_weightedReplacer]
  have h := MatrixMap.posSemidef_kronecker hbound.transpose ω.positive
  convert h using 1
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [Matrix.kroneckerMap_apply, Complex.real_smul, sub_mul, mul_assoc]

theorem cp_hermiticityPreserving (Q : MatrixMap a b) (hQ : MatrixMap.CompletelyPositive Q) :
    IsHermiticityPreserving Q := by
  obtain ⟨K,rfl⟩ := MatrixMap.exists_ofKraus_of_choi_positive Q
    (MatrixMap.choi_positive_of_completelyPositive Q hQ)
  intro X hX
  change (∑ k, K k * X * (K k)ᴴ).IsHermitian
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.isHermitian_zero
  · intro k hk
    change (K k * X * (K k)ᴴ)ᴴ = K k * X * (K k)ᴴ
    simp [Matrix.conjTranspose_mul, hX.eq, Matrix.mul_assoc]

/-- The full diamond norm obeys its triangle inequality, including infinity. -/
theorem diamondNorm_add_le (P Q : MatrixMap a b) :
    diamondNorm (P + Q) ≤ diamondNorm P + diamondNorm Q := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  have hmap : MatrixMap.amplify (P + Q) r X.val =
      MatrixMap.amplify P r X.val + MatrixMap.amplify Q r X.val := rfl
  rw [hmap]
  calc
    _ ≤ ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify P r X.val) +
      TraceNorm.traceNorm (MatrixMap.amplify Q r X.val)) :=
      ENNReal.ofReal_le_ofReal (TraceNorm.traceNorm_add_le _ _)
    _ = ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify P r X.val)) +
      ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Q r X.val)) :=
      ENNReal.ofReal_add (TraceNorm.traceNorm_nonneg _) (TraceNorm.traceNorm_nonneg _)
    _ ≤ diamondNorm P + diamondNorm Q := add_le_add
      (le_iSup_of_le r (le_iSup_of_le X le_rfl))
      (le_iSup_of_le r (le_iSup_of_le X le_rfl))

/-- CP domination by c times a channel bounds the full diamond norm by c. -/
theorem diamondNorm_le_of_cp_domination (Q : MatrixMap a b)
    (hQ : MatrixMap.CompletelyPositive Q) (M : KrausChannel a b) (c : ℝ) (_hc : 0 ≤ c)
    (hdom : MatrixMap.CPLe Q ((c : ℂ) • M.toLinearMap)) :
    diamondNorm Q ≤ ENNReal.ofReal c := by
  rw [diamondNorm_eq_pureDiamondNorm Q (cp_hermiticityPreserving Q hQ)]
  apply iSup_le
  intro ψ
  apply ENNReal.ofReal_le_ofReal
  rw [TraceNorm.traceNorm_of_posSemidef _ (hQ a _ (pureMatrix_positive ψ.val))]
  have hp := hdom a (pureMatrix ψ.val) (pureMatrix_positive ψ.val)
  have heq : MatrixMap.amplify ((c : ℂ) • M.toLinearMap - Q) a (pureMatrix ψ.val) =
      (c : ℂ) • M.amplify a (pureMatrix ψ.val) -
        MatrixMap.amplify Q a (pureMatrix ψ.val) := by
    change (c : ℂ) • MatrixMap.amplify M.toLinearMap a (pureMatrix ψ.val) - _ = _
    rw [MatrixMap.amplify_toLinearMap]
    rfl
  rw [heq] at hp
  have h := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simpa [Matrix.trace_sub, Matrix.trace_smul, M.trace_amplify,
    trace_pureMatrix_of_norm_one ψ.val ψ.property] using h

theorem diamondNorm_weightedReplacer_le (D : Operator a) (hD : D.PosSemidef) (ω : State b) :
    diamondNorm (weightedReplacer D ω) ≤ ENNReal.ofReal ‖D‖ :=
  diamondNorm_le_of_cp_domination _ (weightedReplacer_cp D hD ω)
    (ReplacerChannel.channel a ω) ‖D‖ (norm_nonneg _) (weightedReplacer_cpLe D hD ω)

/-- Completing the missing trace gives an actual normalized channel. -/
theorem completion_isChannel (Q : Subchannel a b) (ω : State b) :
    IsChannel (Q.toLinearMap + weightedReplacer (defect Q.toLinearMap) ω) := by
  constructor
  · intro r X hX
    change (MatrixMap.amplify Q.toLinearMap r X +
      MatrixMap.amplify (weightedReplacer (defect Q.toLinearMap) ω) r X).PosSemidef
    exact (Q.completelyPositive r X hX).add
      (weightedReplacer_cp _ (defect_positive Q) ω r X hX)
  · intro X
    change (Q.toLinearMap X + weightedReplacer (defect Q.toLinearMap) ω X).trace = _
    rw [Matrix.trace_add, weightedReplacer_trace, defect_pairing]
    abel

/-- Every ordinary state is a legitimate one-dimensional-reference diamond test. -/
theorem norm_trace_map_state_le_diamond (P : MatrixMap a b) (ρ : State a) :
    ENNReal.ofReal ‖(P ρ.matrix).trace‖ ≤ diamondNorm P := by
  let X : Matrix (Fin 1 × Fin a) (Fin 1 × Fin a) ℂ := ρ.matrix.submatrix Prod.snd Prod.snd
  have hX : TraceNorm.traceNorm X = 1 := by
    rw [TraceNorm.traceNorm_of_posSemidef X (ρ.positive.submatrix Prod.snd)]
    have ht : X.trace = ρ.matrix.trace := by
      simp [X, Matrix.trace, Fintype.sum_prod_type, Matrix.submatrix_apply]
    rw [ht, ρ.trace_one]
    rfl
  have ht : (MatrixMap.amplify P 1 X).trace = (P ρ.matrix).trace := by
    simp [MatrixMap.amplify, X, Matrix.trace, Fintype.sum_prod_type, Matrix.submatrix_apply]
  have hn : ‖(P ρ.matrix).trace‖ ≤ TraceNorm.traceNorm (MatrixMap.amplify P 1 X) := by
    rw [← ht]
    have h := TraceNorm.norm_trace_mul_le (1 : Matrix (Fin 1 × Fin b) (Fin 1 × Fin b) ℂ)
      (MatrixMap.amplify P 1 X)
    rw [Matrix.one_mul] at h
    exact h.trans (mul_le_of_le_one_left (TraceNorm.traceNorm_nonneg _) (by simpa using TraceNorm.unitary_opNorm_le_one (1 : Matrix.unitaryGroup (Fin 1 × Fin b) ℂ)))
  exact (ENNReal.ofReal_le_ofReal hn).trans
    (le_iSup_of_le 1 (le_iSup_of_le ⟨X,hX.le⟩ le_rfl))

/-- The actual missing trace norm is bounded by distance from every channel. -/
theorem defect_le_diamond (Q : Subchannel a b) (N : KrausChannel a b) (ha : 0 < a) :
    ENNReal.ofReal ‖defect Q.toLinearMap‖ ≤ diamondNorm (Q.toLinearMap - N.toLinearMap) := by
  by_cases htop : diamondNorm (Q.toLinearMap - N.toLinearMap) = ⊤
  · rw [htop]
    exact le_top
  let ε := (diamondNorm (Q.toLinearMap - N.toLinearMap)).toReal
  have hn : ‖defect Q.toLinearMap‖ ≤ ε := by
    apply norm_le_of_state_expectations (PureReferenceRecovery.inputDensity
      (ChannelEntropy.unitProductInput ha)) _ (defect_positive Q) ε
    intro ρ
    have ht := norm_trace_map_state_le_diamond (Q.toLinearMap - N.toLinearMap) ρ
    have htr : ((Q.toLinearMap - N.toLinearMap) ρ.matrix).trace =
        -(defect Q.toLinearMap * ρ.matrix).trace := by
      change (Q.toLinearMap ρ.matrix - N.apply ρ.matrix).trace = _
      rw [Matrix.trace_sub, N.trace_apply, defect_pairing]
      abel
    rw [htr, norm_neg] at ht
    have hreal : ‖(defect Q.toLinearMap * ρ.matrix).trace‖ ≤ ε := by
      simpa [ε] using (ENNReal.toReal_mono htop ht)
    exact (Complex.re_le_norm _).trans hreal
  exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal htop)

/-- The completed channel differs from its target by at most twice the
original full diamond error. -/
theorem completion_error_le (Q : Subchannel a b) (N : KrausChannel a b) (ha : 0 < a)
    (ω : State b) :
    diamondNorm (Q.toLinearMap + weightedReplacer (defect Q.toLinearMap) ω - N.toLinearMap) ≤
      2 * diamondNorm (Q.toLinearMap - N.toLinearMap) := by
  rw [show Q.toLinearMap + weightedReplacer (defect Q.toLinearMap) ω - N.toLinearMap =
    (Q.toLinearMap - N.toLinearMap) + weightedReplacer (defect Q.toLinearMap) ω by abel]
  exact (diamondNorm_add_le _ _).trans (by
    rw [two_mul]
    exact add_le_add_right ((diamondNorm_weightedReplacer_le _ (defect_positive Q) ω).trans
      (defect_le_diamond Q N ha)) _)

/-- Convexity of the actual Choi image is convexity of the linear-map set. -/
theorem convex_map_combination_mem (F : Set (MatrixMap a b))
    (hF : Convex ℝ (MatrixMap.choi '' F)) (P Q : MatrixMap a b)
    (hP : P ∈ F) (hQ : Q ∈ F) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1) :
    (x : ℂ) • P + (y : ℂ) • Q ∈ F := by
  have h := hF ⟨P,hP,rfl⟩ ⟨Q,hQ,rfl⟩ hx hy hxy
  obtain ⟨S,hS,heq⟩ := h
  have he : S = (x : ℂ) • P + (y : ℂ) • Q := by
    apply MatrixMap.choi_injective
    rw [MatrixMap.choi_add, MatrixMap.choi_smul, MatrixMap.choi_smul]
    simpa only [Complex.real_smul] using heq
  rwa [← he]

/-- Mixing two normalized channels with real probability weights gives a channel. -/
theorem isChannel_combination (P Q : KrausChannel a b) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1) :
    IsChannel ((x : ℂ) • P.toLinearMap + (y : ℂ) • Q.toLinearMap) := by
  constructor
  · intro r X hX
    have hp := (P.amplify_positive r hX).smul hx
    have hq := (Q.amplify_positive r hX).smul hy
    have heq : MatrixMap.amplify ((x : ℂ) • P.toLinearMap + (y : ℂ) • Q.toLinearMap) r X =
        (x : ℂ) • P.amplify r X + (y : ℂ) • Q.amplify r X := by
      change (x : ℂ) • MatrixMap.amplify P.toLinearMap r X +
        (y : ℂ) • MatrixMap.amplify Q.toLinearMap r X = _
      rw [MatrixMap.amplify_toLinearMap, MatrixMap.amplify_toLinearMap]
    rw [heq]
    simpa only [Complex.real_smul] using hp.add hq
  · intro X
    change ((x : ℂ) • P.apply X + (y : ℂ) • Q.apply X).trace = _
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, P.trace_apply, Q.trace_apply]
    simp only [smul_eq_mul, ← add_mul, ← Complex.ofReal_add, hxy, Complex.ofReal_one, one_mul]

/-- Lemma 7, with actual normalized channel witnesses, exact lam+d cost,
full diamond errors, and only convexity plus membership of the replacer. -/
theorem lemma_7 (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (Q : Subchannel a b) (N M : KrausChannel a b) (ha : 0 < a)
    (ω : State b) (hM : M.toLinearMap ∈ F)
    (hR : (ReplacerChannel.channel a ω).toLinearMap ∈ F)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hdom : MatrixMap.CPLe Q.toLinearMap ((lam : ℂ) • M.toLinearMap)) :
    let d := ‖defect Q.toLinearMap‖
    0 ≤ d ∧ d ≤ 1 ∧ ENNReal.ofReal d ≤ diamondNorm (Q.toLinearMap - N.toLinearMap) ∧
    ∃ L S : KrausChannel a b, S.toLinearMap ∈ F ∧
      MatrixMap.CPLe L.toLinearMap (((lam + d : ℝ) : ℂ) • S.toLinearMap) ∧
      diamondNorm (L.toLinearMap - N.toLinearMap) ≤
        2 * diamondNorm (Q.toLinearMap - N.toLinearMap) := by
  dsimp only
  let d := ‖defect Q.toLinearMap‖
  have hd : 0 ≤ d := norm_nonneg _
  have hc : 0 < lam + d := by linarith
  let x := lam / (lam + d)
  let y := d / (lam + d)
  have hx : 0 ≤ x := div_nonneg (by linarith) hc.le
  have hy : 0 ≤ y := div_nonneg hd hc.le
  have hxy : x + y = 1 := by dsimp [x,y]; field_simp
  let R := ReplacerChannel.channel a ω
  obtain ⟨S,hS⟩ := (isChannel_iff_kraus _).mp (isChannel_combination M R x y hx hy hxy)
  obtain ⟨L,hL⟩ := (isChannel_iff_kraus _).mp (completion_isChannel Q ω)
  refine ⟨hd,norm_defect_le_one Q,defect_le_diamond Q N ha,L,S,?_,?_,?_⟩
  · rw [hS]
    exact convex_map_combination_mem F hF M.toLinearMap R.toLinearMap hM hR x y hx hy hxy
  · rw [hL,hS]
    have hscalar : (((lam + d : ℝ) : ℂ) • ((x : ℂ) • M.toLinearMap + (y : ℂ) • R.toLinearMap)) =
        (lam : ℂ) • M.toLinearMap + (d : ℂ) • R.toLinearMap := by
      rw [smul_add, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> simp only [x,y,Complex.ofReal_div,Complex.ofReal_add] <;>
        field_simp [Complex.ofReal_ne_zero.mpr hc.ne']
    rw [hscalar]
    intro r X hX
    have h1 := hdom r X hX
    have h2 := weightedReplacer_cpLe (defect Q.toLinearMap) (defect_positive Q) ω r X hX
    have heq : MatrixMap.amplify
        ((lam : ℂ) • M.toLinearMap + (d : ℂ) • R.toLinearMap -
          (Q.toLinearMap + weightedReplacer (defect Q.toLinearMap) ω)) r X =
        MatrixMap.amplify ((lam : ℂ) • M.toLinearMap - Q.toLinearMap) r X +
        MatrixMap.amplify ((d : ℂ) • R.toLinearMap - weightedReplacer (defect Q.toLinearMap) ω) r X := by
      ext i j
      simp [MatrixMap.amplify]
      ring
    rw [heq]
    exact h1.add h2
  · rw [hL]
    exact completion_error_le Q N ha ω

/-- The weighted replacement map has diamond norm exactly its effect's
operator norm, including a singular or zero effect. -/
theorem diamondNorm_weightedReplacer (D : Operator a) (hD : D.PosSemidef)
    (ω : State b) (ha : 0 < a) :
    diamondNorm (weightedReplacer D ω) = ENNReal.ofReal ‖D‖ := by
  apply le_antisymm (diamondNorm_weightedReplacer_le D hD ω)
  have htop : diamondNorm (weightedReplacer D ω) ≠ ⊤ :=
    ne_of_lt ((diamondNorm_weightedReplacer_le D hD ω).trans_lt ENNReal.ofReal_lt_top)
  have hn : ‖D‖ ≤ (diamondNorm (weightedReplacer D ω)).toReal := by
    apply norm_le_of_state_expectations (PureReferenceRecovery.inputDensity
      (ChannelEntropy.unitProductInput ha)) D hD
    intro ρ
    have ht := norm_trace_map_state_le_diamond (weightedReplacer D ω) ρ
    rw [weightedReplacer_trace] at ht
    have ht' : ‖(D * ρ.matrix).trace‖ ≤ (diamondNorm (weightedReplacer D ω)).toReal := by
      simpa using ENNReal.toReal_mono htop ht
    exact (Complex.re_le_norm _).trans ht'
  exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal htop)

end GeneralizedChannelStein.TraceDefectCompletion
