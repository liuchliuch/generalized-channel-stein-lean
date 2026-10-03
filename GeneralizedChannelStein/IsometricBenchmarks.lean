import GeneralizedChannelStein.EntanglementBreaking
import GeneralizedChannelStein.Smoothing
import QuantumChannelStein.PinchingGramBound
import QuantumChannelStein.BinaryDataProcessing
import QuantumChannelStein.SharpChannelWeights

/-! Exact isometric benchmarks: concrete isometries, PPT overlap and dephasing dominators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelEntropy PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- A genuine one-Kraus channel associated with a rectangular isometry. -/
def isometryChannel (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) : KrausChannel a b where
  rank := 1
  kraus _ := J
  normalized := by simpa using hJ

@[simp] theorem isometryChannel_apply (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (X : Operator a) : (isometryChannel J hJ).apply X=J*X*Jᴴ := by
  simp [isometryChannel,KrausChannel.apply]

theorem isometryChannel_choi (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (isometryChannel J hJ).choi = Matrix.vecMulVec (fun i => J i.2 i.1) (star (fun i => J i.2 i.1)) := by
  rw [KrausChannel.choi_eq_columns]
  ext i j
  simp [KrausChannel.krausColumns,isometryChannel,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.vecMulVec,Pi.star_apply]

def flipMatrix (a : ℕ) : BipartiteOperator a a :=
  fun i j => if i.1=j.2 ∧ i.2=j.1 then 1 else 0

theorem flipMatrix_selfadjoint (a : ℕ) : (flipMatrix a)ᴴ=flipMatrix a := by
  ext i j
  simp [flipMatrix,Matrix.conjTranspose_apply,eq_comm,and_comm]

theorem flipMatrix_sq (a : ℕ) : flipMatrix a*flipMatrix a=1 := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp [flipMatrix,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,ite_and,Prod.mk.injEq]

theorem one_sub_flip_positive (a : ℕ) : (1-flipMatrix a).PosSemidef := by
  have h := (Matrix.posSemidef_self_mul_conjTranspose (1-flipMatrix a)).smul
    (by norm_num : (0:ℝ)≤1/2)
  have he : (1-flipMatrix a)*(1-flipMatrix a)ᴴ = (2:ℝ) • (1-flipMatrix a) := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,flipMatrix_selfadjoint,
      Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.one_mul,
      Matrix.mul_one,flipMatrix_sq]
    module
  rw [he,smul_smul] at h
  norm_num at h
  exact h

theorem isometry_complement_positive (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (1-J*Jᴴ).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (1-J*Jᴴ)
  have he : (1-J*Jᴴ)*(1-J*Jᴴ)ᴴ=1-J*Jᴴ := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_one]
    have hm : J*Jᴴ*(J*Jᴴ)=J*Jᴴ := by rw [Matrix.mul_assoc,← Matrix.mul_assoc Jᴴ,hJ,Matrix.one_mul]
    rw [hm]
    abel
  rwa [he] at h

def conjugateMatrix (J : Matrix (Fin b) (Fin a) ℂ) : Matrix (Fin b) (Fin a) ℂ :=
  fun i j => star (J i j)

theorem isometry_conjugate_complement (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (1-conjugateMatrix J*(conjugateMatrix J)ᴴ).PosSemidef := by
  have h := (isometry_complement_positive J hJ).transpose
  convert h using 1
  ext i j
  simp [Matrix.transpose_sub,Matrix.transpose_apply,Matrix.mul_apply,conjugateMatrix,
    Matrix.conjTranspose_apply,Matrix.one_apply,mul_comm,eq_comm]

theorem partialTranspose_isometry_choi (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    partialTranspose (isometryChannel J hJ).choi =
      ((1:Operator a) ⊗ₖ conjugateMatrix J)*flipMatrix a*((1:Operator a) ⊗ₖ conjugateMatrix J)ᴴ := by
  rw [isometryChannel_choi]
  ext ⟨i,x⟩ ⟨j,y⟩
  simp [partialTranspose,Matrix.vecMulVec,Pi.star_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,
    conjugateMatrix,flipMatrix,ite_and,Finset.sum_mul,apply_ite]
  ring

/-- The unnormalized maximally entangled isometric Choi projector has PPT bound one. -/
theorem partialTranspose_isometry_le_one (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (1-partialTranspose (isometryChannel J hJ).choi).PosSemidef := by
  let L := (1:Operator a) ⊗ₖ conjugateMatrix J
  have h1 := MatrixMap.posSemidef_kronecker (Matrix.PosSemidef.one (n:=Fin a) (R:=ℂ))
    (isometry_conjugate_complement J hJ)
  have h2 := (one_sub_flip_positive a).mul_mul_conjTranspose_same L
  have he : (1:Operator a) ⊗ₖ (1-conjugateMatrix J*(conjugateMatrix J)ᴴ) = 1-L*Lᴴ := by
    simp only [L,Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,Matrix.one_mul]
    rw [show (1:BipartiteOperator a b) = (1:Operator a) ⊗ₖ (1:Operator b) from Matrix.one_kronecker_one.symm]
    ext i j
    simp [mul_sub,Matrix.one_apply,Prod.ext_iff,ite_and]
    split_ifs <;> rfl
  rw [he] at h1
  have h := h1.add h2
  have he2 : (1-L*Lᴴ)+L*(1-flipMatrix a)*Lᴴ =
      1-partialTranspose (isometryChannel J hJ).choi := by
    rw [partialTranspose_isometry_choi]
    dsimp [L]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one]
    abel
  rwa [he2] at h

/-- Partial transposition is self-adjoint for the bilinear trace pairing. -/
theorem trace_partialTranspose_pair (C D : BipartiteOperator a b) :
    (partialTranspose C*partialTranspose D).trace=(C*D).trace := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,partialTranspose]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  -- The two output summations are exchanged independently of the reference indices.
  simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Fin a)) (t:=Finset.univ (α:=Fin b))]
  exact Finset.sum_comm


/-- Every density matrix is an effect; pure ones give the desired projector. -/
def stateEffect {d : ℕ} (ρ : State d) : Effect d where
  matrix := ρ.matrix
  positive := ρ.positive
  complement_positive := by
    have h := positive_le_trace_smul_one ρ.positive
    rw [ρ.trace_one,Complex.one_re,one_smul] at h
    exact h

theorem isometry_choi_sq (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (isometryChannel J hJ).choi*(isometryChannel J hJ).choi = (a:ℝ) • (isometryChannel J hJ).choi := by
  have htrace := Pseudoinverse.choi_trace (isometryChannel J hJ)
  rw [isometryChannel_choi] at htrace ⊢
  let v : Fin a × Fin b → ℂ := fun i => J i.2 i.1
  change (Matrix.vecMulVec v (star v)).trace=(a:ℂ) at htrace
  have hs : ∑ i, star (v i)*v i = (a:ℂ) := by
    simpa [Matrix.trace,Matrix.diag,Matrix.vecMulVec,Pi.star_apply,mul_comm] using htrace
  ext i j
  change (∑ k, v i * star (v k)*(v k * star (v j))) = (a:ℝ) • (v i * star (v j))
  calc
    (∑ k, v i * star (v k)*(v k * star (v j))) = v i*(∑ k, star (v k)*v k)*star (v j) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k hk; ring
    _ = _ := by rw [hs]; simp [Complex.real_smul]; ring

theorem normalizedChoi_isometry_idempotent (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a) :
    let ρ := normalizedChoiState (isometryChannel J hJ) ha
    ρ.matrix*ρ.matrix=ρ.matrix := by
  dsimp only
  rw [normalizedChoiState_matrix]
  change SharpChannel.flatten ((a:ℝ)⁻¹ • (isometryChannel J hJ).choi) *
    SharpChannel.flatten ((a:ℝ)⁻¹ • (isometryChannel J hJ).choi) =
    SharpChannel.flatten ((a:ℝ)⁻¹ • (isometryChannel J hJ).choi)
  rw [← SharpChannel.flatten_mul]
  congr 1
  rw [Matrix.smul_mul,Matrix.mul_smul,isometry_choi_sq,smul_smul,smul_smul]
  congr 1
  have ha0 : (a:ℝ)≠0 := by exact_mod_cast ha.ne'
  field_simp

def isometryTestEffect (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a) : Effect (a*b) :=
  stateEffect (normalizedChoiState (isometryChannel J hJ) ha)

theorem isometryTestEffect_target (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a) :
    (isometryTestEffect J hJ ha).probability (normalizedChoiState (isometryChannel J hJ) ha)=1 := by
  change (((normalizedChoiState (isometryChannel J hJ) ha).matrix*
    (normalizedChoiState (isometryChannel J hJ) ha).matrix).trace).re=1
  rw [normalizedChoi_isometry_idempotent,(normalizedChoiState _ _).trace_one,Complex.one_re]

theorem trace_mul_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) : 0≤(A*B).trace := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  obtain ⟨C,hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A=Cᴴ*C at hC
  rw [hC,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

theorem isometry_choi_ppt_pair_bound (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (hM : IsPPT M.toLinearMap) :
    (((isometryChannel J hJ).choi*M.choi).trace).re ≤ a := by
  have h := (Complex.nonneg_iff.mp (trace_mul_positive (partialTranspose_isometry_le_one J hJ)
    (show (partialTranspose M.choi).PosSemidef from hM))).1
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re,trace_partialTranspose_pair] at h
  have htr : (partialTranspose M.choi).trace=M.choi.trace := rfl
  rw [htr,Pseudoinverse.choi_trace,Complex.natCast_re] at h
  linarith

/-- A maximally entangled isometric test has acceptance at most 1/a for every PPT alternative. -/
theorem isometryTestEffect_ppt_bound (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (M : KrausChannel a b) (hM : IsPPT M.toLinearMap) :
    (isometryTestEffect J hJ ha).probability (normalizedChoiState M ha) ≤ (a:ℝ)⁻¹ := by
  have h := isometry_choi_ppt_pair_bound J hJ M hM
  change (((normalizedChoiState (isometryChannel J hJ) ha).matrix*(normalizedChoiState M ha).matrix).trace).re ≤ _
  rw [normalizedChoiState_matrix,normalizedChoiState_matrix]
  change ((SharpChannel.flatten ((a:ℝ)⁻¹ • (isometryChannel J hJ).choi) *
    SharpChannel.flatten ((a:ℝ)⁻¹ • M.choi)).trace).re ≤ _
  rw [← SharpChannel.flatten_mul]
  change (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (((a:ℝ)⁻¹ • (isometryChannel J hJ).choi)*((a:ℝ)⁻¹ • M.choi))).trace.re ≤ _
  rw [trace_reindex_equiv,Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,Matrix.trace_smul]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have ha0 : (a:ℝ)>0 := by exact_mod_cast ha
  calc
    (a:ℝ)⁻¹*((a:ℝ)⁻¹*(((isometryChannel J hJ).choi*M.choi).trace).re) ≤
      (a:ℝ)⁻¹*((a:ℝ)⁻¹*(a:ℝ)) := by gcongr
    _ = (a:ℝ)⁻¹ := by rw [inv_mul_cancel₀ ha0.ne',mul_one]


/-- The EB dominator obtained by first completely dephasing the input basis. -/
def pinchedIsometry (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) : KrausChannel a b :=
  (isometryChannel J hJ).compose (SharpDivergence.diagonalChannel a)

def cutColumn (J : Matrix (Fin b) (Fin a) ℂ) (k : Fin a) :
    Matrix (Fin a × Fin b) (Fin 1) ℂ := fun x _ => if x.1=k then J x.2 x.1 else 0

theorem pinchedIsometry_choi (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (pinchedIsometry J hJ).choi = ∑ k, cutColumn J k*(cutColumn J k)ᴴ := by
  ext ⟨i,x⟩ ⟨j,y⟩
  change (pinchedIsometry J hJ).apply (Matrix.single i j 1) x y = _
  simp only [pinchedIsometry,KrausChannel.compose_apply,isometryChannel_apply,SharpDivergence.diagonalChannel_apply]
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.diag,
    Matrix.single,Matrix.sum_apply,cutColumn,ite_and,apply_ite,eq_comm]
  by_cases hij : i=j <;> simp_all

theorem cutColumn_gram_separable (J : Matrix (Fin b) (Fin a) ℂ) (k : Fin a) :
    Separable (cutColumn J k*(cutColumn J k)ᴴ) := by
  let v : Fin a → ℂ := Pi.single k 1
  let w : Fin b → ℂ := fun x => J x k
  have he : cutColumn J k*(cutColumn J k)ᴴ =
      Matrix.vecMulVec v (star v) ⊗ₖ Matrix.vecMulVec w (star w) := by
    ext ⟨i,x⟩ ⟨j,y⟩
    simp [cutColumn,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.vecMulVec,
      Pi.star_apply,v,w,Pi.single_apply]
    split_ifs <;> simp_all
  rw [he]
  exact Separable.product (Matrix.posSemidef_vecMulVec_self_star _) (Matrix.posSemidef_vecMulVec_self_star _)

theorem pinchedIsometry_EB (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    IsEntanglementBreaking (pinchedIsometry J hJ) := by
  apply (entanglementBreaking_iff_separable_choi _).mpr
  rw [pinchedIsometry_choi]
  exact Separable.sum _ (fun k => cutColumn_gram_separable J k)

/-- Exact CP pinching domination, with coefficient equal to input dimension. -/
theorem isometry_cpLe_pinched (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    MatrixMap.CPLe (isometryChannel J hJ).toLinearMap ((a:ℂ) • (pinchedIsometry J hJ).toLinearMap) := by
  apply (MatrixMap.cpLe_iff_choi_difference _ _).mpr
  rw [MatrixMap.choi_smul,MatrixMap.choi_toLinearMap,MatrixMap.choi_toLinearMap,pinchedIsometry_choi]
  have h := SpectralPinching.gram_sum_le_card (cutColumn J)
  have he : (∑ k, cutColumn J k)*(∑ k, cutColumn J k)ᴴ = (isometryChannel J hJ).choi := by
    rw [isometryChannel_choi]
    ext i j
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,cutColumn,
      Matrix.vecMulVec,Pi.star_apply,apply_ite]
  rw [he,Fintype.card_fin] at h
  convert h using 1


open OperationalTesting RelativeEntropy

def scaleEffect {d : ℕ} (T : Effect d) (s : ℝ) (hs : 0≤s) (hs1 : s≤1) : Effect d where
  matrix := s • T.matrix
  positive := T.positive.smul hs
  complement_positive := by
    have h := (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hs1)).add (T.complement_positive.smul hs)
    convert h using 1
    module

theorem scaleEffect_probability {d : ℕ} (T : Effect d) (s : ℝ) (hs : 0≤s) (hs1 : s≤1) (ρ : State d) :
    (scaleEffect T s hs hs1).probability ρ = s*T.probability ρ := by
  simp [Effect.probability,scaleEffect,Matrix.smul_mul,Matrix.trace_smul]

theorem test_acceptance_le_domination (N M : KrausChannel a b) (c : ℝ)
    (hdom : MatrixMap.CPLe N.toLinearMap ((c:ℂ) • M.toLinearMap)) (t : ChannelTest a b) :
    t.acceptance N ≤ c*t.acceptance M := by
  obtain ⟨ψ,T,h⟩ := ParallelTestingReduction.exists_pure_test t
  have hh := DiamondTesting.testValue_le_of_cpLe N.toLinearMap M c hdom ψ T
  rw [DiamondTesting.testValue_channel,h,h] at hh
  exact hh

/-- Exact one-block testing for any family between the EB pinching witness and PPT channels. -/
theorem isometry_compositeBeta_exact (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hfree : (pinchedIsometry J hJ).toLinearMap ∈ F)
    (hPPT : ∀ M : KrausChannel a b, M.toLinearMap ∈ F → IsPPT M.toLinearMap)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    compositeBeta (isometryChannel J hJ) F ε = ENNReal.ofReal ((1-ε)/(a:ℝ)) := by
  apply le_antisymm
  · let T := scaleEffect (isometryTestEffect J hJ ha) (1-ε) (by linarith) (by linarith)
    let t := ofPureTest (maximallyEntangledInput ha) T
    have ht : t.acceptance (isometryChannel J hJ)=1-ε := by
      rw [OperationalTesting.ofPureTest_acceptance]
      change T.probability (normalizedChoiState (isometryChannel J hJ) ha)=_
      rw [scaleEffect_probability,isometryTestEffect_target,mul_one]
    refine iInf_le_of_le ⟨t,ht.ge⟩ ?_
    apply iSup_le
    intro M
    apply ENNReal.ofReal_le_ofReal
    rw [OperationalTesting.ofPureTest_acceptance]
    change T.probability (normalizedChoiState M.val ha)≤_
    rw [scaleEffect_probability]
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (isometryTestEffect_ppt_bound J hJ ha M.val (hPPT M.val M.property))
        (by linarith : 0≤1-ε)
  · apply le_iInf
    intro t
    have hh := test_acceptance_le_domination (isometryChannel J hJ) (pinchedIsometry J hJ)
      (a:ℝ) (isometry_cpLe_pinched J hJ) t.val
    have hq : (1-ε)/(a:ℝ)≤t.val.acceptance (pinchedIsometry J hJ) :=
      (div_le_iff₀ (by exact_mod_cast ha)).mpr (by linarith [t.property])
    exact (ENNReal.ofReal_le_ofReal hq).trans (acceptance_le_worst F t.val _ hfree)

/-- A PPT alternative has at least log₂(a) Umegaki divergence from an isometry. -/
theorem isometry_channelD_ppt_lower (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (M : KrausChannel a b) (hM : IsPPT M.toLinearMap) :
    (Real.logb 2 (a:ℝ):EReal)≤channelD (isometryChannel J hJ) M := by
  by_cases htop : channelD (isometryChannel J hJ) M=⊤
  · rw [htop]; exact le_top
  let ρ := normalizedChoiState (isometryChannel J hJ) ha
  let σ := normalizedChoiState M ha
  let T := isometryTestEffect J hJ ha
  have hfinite : umegaki ρ σ<⊤ := (umegaki_normalizedChoi_le_channelD _ _ ha).trans_lt (lt_top_iff_ne_top.mpr htop)
  obtain ⟨c,hc,hdom⟩ := (umegaki_lt_top_iff_exists_domination ρ σ).mp hfinite
  have hprob := BinaryMeasurement.probability_le_of_domination T ρ σ c hdom
  have hp : T.probability ρ=1 := isometryTestEffect_target J hJ ha
  rw [hp] at hprob
  have hq0 : 0<T.probability σ := by
    by_contra! hn
    have hz : T.probability σ=0 := le_antisymm hn (T.probability_nonneg σ)
    rw [hz,mul_zero] at hprob
    norm_num at hprob
  have hq := isometryTestEffect_ppt_bound J hJ ha M hM
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hq0 hq
  rw [Real.logb_inv] at hlog
  have hd := BinaryMeasurement.binary_measurement_data_processing T ρ σ
  rw [hp,BinaryEntropyBounds.binaryRelativeEntropy_one] at hd
  calc
    (Real.logb 2 (a:ℝ):EReal) ≤ (-Real.logb 2 (T.probability σ):ℝ) := by exact_mod_cast (by linarith : Real.logb 2 (a:ℝ)≤-Real.logb 2 (T.probability σ))
    _ ≤ umegaki ρ σ := hd
    _ ≤ channelD (isometryChannel J hJ) M := umegaki_normalizedChoi_le_channelD _ _ ha

/-- Exact one-block resource entropy under the same concrete EB/PPT sandwich. -/
theorem isometry_familyEntropy_exact (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hfree : (pinchedIsometry J hJ).toLinearMap ∈ F)
    (hPPT : ∀ M : KrausChannel a b, M.toLinearMap ∈ F → IsPPT M.toLinearMap) :
    familyEntropy (isometryChannel J hJ) F = (Real.logb 2 (a:ℝ):EReal) := by
  apply le_antisymm
  · exact (familyEntropy_le _ _ _ hfree).trans
      (channelD_le_log2_of_cpLe _ _ (a:ℝ) (by exact_mod_cast ha) (isometry_cpLe_pinched J hJ))
  · apply le_iInf
    intro M
    exact isometry_channelD_ppt_lower J hJ ha M.val (hPPT M.val M.property)


/-- Tensor-power isometry in exactly the project's channel-power coordinates. -/
def powerIsometry (J : Matrix (Fin b) (Fin a) ℂ) (n : ℕ) : Matrix (Fin (b^n)) (Fin (a^n)) ℂ :=
  Matrix.reindex (ChannelPowerReindex.channelIndexEquiv b n) (ChannelPowerReindex.channelIndexEquiv a n)
    (TensorPower.tensorPower J n)

theorem powerIsometry_isometry (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (n : ℕ) :
    (powerIsometry J n)ᴴ*powerIsometry J n=1 :=
  ChannelDilationPower.reindex_isometry _ _ _ (TensorPower.tensorPower_isometry J hJ n)

theorem isometryChannel_power_map (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (n : ℕ) :
    ((isometryChannel J hJ).tensorPower n).toLinearMap =
      (isometryChannel (powerIsometry J n) (powerIsometry_isometry J hJ n)).toLinearMap := by
  apply MatrixMap.choi_injective
  simp only [MatrixMap.choi_toLinearMap]
  ext ⟨i,x⟩ ⟨j,y⟩
  obtain ⟨i,rfl⟩ := (ChannelPowerReindex.channelIndexEquiv a n).surjective i
  obtain ⟨j,rfl⟩ := (ChannelPowerReindex.channelIndexEquiv a n).surjective j
  obtain ⟨x,rfl⟩ := (ChannelPowerReindex.channelIndexEquiv b n).surjective x
  obtain ⟨y,rfl⟩ := (ChannelPowerReindex.channelIndexEquiv b n).surjective y
  rw [ChannelPowerReindex.choi_tensorPower_apply,isometryChannel_choi]
  simp only [isometryChannel_choi,powerIsometry,Matrix.vecMulVec_apply,Pi.star_apply,
    Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    TensorPower.tensorPower_apply_eq_prod,map_prod,star_prod,Finset.prod_mul_distrib]

theorem familyEntropy_congr_target {N L : KrausChannel a b} (h : N.toLinearMap=L.toLinearMap)
    (F : Set (MatrixMap a b)) : familyEntropy N F=familyEntropy L F := by
  apply iInf_congr
  intro M
  exact channelD_congr _ _ _ _ h rfl

/-- Proposition 22's exact finite-block values, for both full correlated EB and PPT alternatives. -/
theorem proposition_22_benchmarks (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (n : ℕ) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    familyEntropy ((isometryChannel J hJ).tensorPower n) (EBFamily a b n) =
      ((n:ℝ)*Real.logb 2 (a:ℝ):ℝ) ∧
    familyEntropy ((isometryChannel J hJ).tensorPower n) (PPTFamily a b n) =
      ((n:ℝ)*Real.logb 2 (a:ℝ):ℝ) ∧
    compositeBeta ((isometryChannel J hJ).tensorPower n) (EBFamily a b n) ε =
      ENNReal.ofReal ((1-ε)/(a:ℝ)^n) ∧
    compositeBeta ((isometryChannel J hJ).tensorPower n) (PPTFamily a b n) ε =
      ENNReal.ofReal ((1-ε)/(a:ℝ)^n) := by
  let K := powerIsometry J n
  have hK := powerIsometry_isometry J hJ n
  have hN := isometryChannel_power_map J hJ n
  have he : (pinchedIsometry K hK).toLinearMap ∈ EBFamily a b n :=
    (mem_EBFamily_iff n _).mpr (pinchedIsometry_EB K hK)
  have hp : (pinchedIsometry K hK).toLinearMap ∈ PPTFamily a b n := EBFamily_subset_PPTFamily n he
  have hall : ∀ M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ PPTFamily a b n → IsPPT M.toLinearMap :=
    fun M hM => hM.2
  have hallE : ∀ M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ EBFamily a b n → IsPPT M.toLinearMap :=
    fun M hM => (EBFamily_subset_PPTFamily n hM).2
  have e1 := isometry_familyEntropy_exact K hK (pow_pos ha n) _ he hallE
  have e2 := isometry_familyEntropy_exact K hK (pow_pos ha n) _ hp hall
  have b1 := isometry_compositeBeta_exact K hK (pow_pos ha n) _ he hallE ε hε hε1
  have b2 := isometry_compositeBeta_exact K hK (pow_pos ha n) _ hp hall ε hε hε1
  rw [familyEntropy_congr_target hN,familyEntropy_congr_target hN,
    compositeBeta_congr_target hN,compositeBeta_congr_target hN]
  simpa only [Nat.cast_pow,Real.logb_pow] using And.intro e1 (And.intro e2 (And.intro b1 b2))

end GeneralizedChannelStein
