import GeneralizedChannelStein.RoughApproximation
import GeneralizedChannelStein.FreeAmplification

/-! # Lemma 25: an actual CP branch with uniform positive overlap

The shorter proof uses the proved testing-to-auxiliary approximation theorem.
No ellipsoid duality or singular-value test assumption is introduced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.BranchExtraction
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal EnvironmentTensor
  UniformAuxiliary FreeAmplification
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

def adMap (V : Matrix (Fin b) (Fin a) ℂ) : MatrixMap a b :=
  MatrixMap.ofKraus (fun _ : Fin 1 => V)

@[simp] theorem adMap_apply (V : Matrix (Fin b) (Fin a) ℂ) (X : Operator a) :
    adMap V X = V*X*Vᴴ := by simp [adMap,MatrixMap.ofKraus]

def isometryChannel (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) : KrausChannel a b where
  rank := 1
  kraus _ := J
  normalized := by simpa using hJ

theorem isometryChannel_map (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (isometryChannel J hJ).toLinearMap = adMap J := rfl

def lift (J : Matrix (Fin b) (Fin a) ℂ) : Matrix (Fin b × Fin 1) (Fin a) ℂ :=
  Matrix.reindex (Equiv.prodUnique (Fin b) (Fin 1)).symm (Equiv.refl _) J

def flatten (V : Matrix (Fin b × Fin 1) (Fin a) ℂ) : Matrix (Fin b) (Fin a) ℂ :=
  Matrix.reindex (Equiv.prodUnique (Fin b) (Fin 1)) (Equiv.refl _) V

@[simp] theorem lift_flatten (V : Matrix (Fin b × Fin 1) (Fin a) ℂ) : lift (flatten V)=V := by
  ext ⟨i,j⟩ k
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  rfl

@[simp] theorem flatten_lift (J : Matrix (Fin b) (Fin a) ℂ) : flatten (lift J)=J := rfl

@[simp] theorem norm_lift (J : Matrix (Fin b) (Fin a) ℂ) : ‖lift J‖=‖J‖ := TensorPower.norm_reindex _ _ _
@[simp] theorem norm_flatten (V : Matrix (Fin b × Fin 1) (Fin a) ℂ) : ‖flatten V‖=‖V‖ := TensorPower.norm_reindex _ _ _

theorem dilationMap_lift (J : Matrix (Fin b) (Fin a) ℂ) : dilationMap (lift J)=adMap J := by
  ext X i j
  simp [dilationMap,adMap,MatrixMap.ofKraus,lift,Matrix.reindex_apply]

theorem dilationMap_isometry_lift (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    dilationMap (lift J)=(isometryChannel J hJ).toLinearMap := by
  rw [dilationMap_lift,isometryChannel_map]

theorem norm_isometry_le_one (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) : ‖J‖≤1 := by
  have hI : ‖(1 : Operator a)‖≤1 := by
    simpa using TraceNorm.unitary_opNorm_le_one (1 : Matrix.unitaryGroup (Fin a) ℂ)
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self J
  rw [hJ] at hn
  nlinarith [norm_nonneg J]

/-- Hermitian real part, literally (X+X†)/2. -/
def realPart (X : Operator a) : Operator a := (1/2 : ℝ) • (X+Xᴴ)

theorem realPart_isHermitian (X : Operator a) : (realPart X).IsHermitian := by
  change (realPart X)ᴴ=realPart X
  simp [realPart,Matrix.conjTranspose_add,add_comm]

theorem realPart_norm_le (X : Operator a) : ‖realPart X‖≤‖X‖ := by
  rw [realPart,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have h := norm_add_le X Xᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at h
  linarith

/-- Operator-norm proximity to an isometry gives a genuine Loewner overlap bound. -/
theorem overlap_of_close (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (r : ℝ) (hr : 0≤r) (he : ‖J-Z‖≤r) :
    (realPart (Jᴴ*Z)-(1-r) • (1 : Operator a)).PosSemidef := by
  let E := Jᴴ*(Z-J)
  have hEn : ‖realPart E‖≤r := (realPart_norm_le E).trans ((Matrix.l2_opNorm_mul _ _).trans (by
    rw [Matrix.l2_opNorm_conjTranspose,norm_sub_rev]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_isometry_le_one J hJ)).trans he))
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  have hl := (realPart_isHermitian E).isSelfAdjoint.neg_algebraMap_norm_le_self
  have hp : (realPart E+‖realPart E‖ • (1 : Operator a)).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    simpa only [Algebra.algebraMap_eq_smul_one,sub_neg_eq_add] using sub_nonneg.mpr hl
  have hs := (show (1 : Operator a).PosSemidef from Matrix.PosSemidef.one).smul (sub_nonneg.mpr hEn)
  have hh := hp.add hs
  have hid : realPart (Jᴴ*Z)=1+realPart E := by
    dsimp [realPart,E]
    rw [Matrix.mul_sub,hJ,Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
    module
  rw [hid]
  convert hh using 1 <;> module

theorem adMap_real_smul (Z : Matrix (Fin b) (Fin a) ℂ) (s : ℝ) :
    adMap (s • Z) = ((s^2 : ℝ) : ℂ) • adMap Z := by
  ext X i j
  simp [adMap_apply,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,Complex.real_smul,pow_two,mul_assoc]

theorem realPart_real_smul (X : Operator a) (s : ℝ) : realPart (s • X)=s • realPart X := by
  simp only [realPart,Matrix.conjTranspose_smul,star_trivial]
  module

/-- Lemma 25 with any positive certified lower bound on the actual single
alternative testing optimum. Equality is supplied in the final wrapper. -/
theorem branch_of_testing_lower_bound (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (ha : 0<a) (δ β : ℝ) (hδ : 0<δ) (hδ1 : δ<1) (hβ : 0<β)
    (hb : ENNReal.ofReal β ≤ singleBeta (isometryChannel J hJ) M δ) :
    ∃ V : Matrix (Fin b) (Fin a) ℂ, ‖V‖≤1 ∧
      (realPart (Jᴴ*V)-((1-Real.sqrt (1-δ))/(1+Real.sqrt (1-δ))) • (1 : Operator a)).PosSemidef ∧
      MatrixMap.CPLe ((β:ℂ) • adMap V) M.toLinearMap := by
  let r := Real.sqrt (1-δ)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=1-δ := Real.sq_sqrt (by linarith)
  have hr1 : r<1 := by nlinarith
  have hden : 0<1+r := by linarith
  let s := (1+r)⁻¹
  have hs : 0≤s := inv_nonneg.mpr hden.le
  obtain ⟨A,hA,he⟩ := rough_auxiliary_map (isometryChannel J hJ) M ha (lift J) M.stinespring
    (dilationMap_isometry_lift J hJ) (ParallelConverse.dilationMap_stinespring M)
    δ β hδ.le hβ hb
  let Zhat := applyEnvironment M.stinespring A
  let Z := flatten Zhat
  have herr : ‖J-Z‖≤r := by
    have heq : J-Z=flatten (lift J-Zhat) := rfl
    rw [heq,norm_flatten]
    change ‖lift J-Zhat‖^2≤1-δ at he
    nlinarith [norm_nonneg (lift J-Zhat)]
  have hZn : ‖Z‖≤1+r := by
    calc
      ‖Z‖=‖J-(J-Z)‖ := by congr 1; abel
      _ ≤ ‖J‖+‖J-Z‖ := norm_sub_le _ _
      _ ≤ 1+r := add_le_add (norm_isometry_le_one J hJ) herr
  have hDom : MatrixMap.CPLe (adMap Z) (Complex.ofReal (δ/β) • M.toLinearMap) := by
    have h := (lemma_6_converse M.stinespring A).2
    rw [ParallelConverse.dilationMap_stinespring] at h
    have hZmap : dilationMap Zhat = adMap Z := by
      rw [← dilationMap_lift, lift_flatten]
    change MatrixMap.CPLe (dilationMap Zhat) _ at h
    rw [hZmap] at h
    exact cpLe_scalar_mono _ M ((pow_le_pow_left₀ (norm_nonneg A) hA 2).trans_eq
      (Real.sq_sqrt (div_nonneg hδ.le hβ.le))) h
  refine ⟨s • Z,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hZn hs).trans_eq (inv_mul_cancel₀ hden.ne')
  · rw [Matrix.mul_smul,realPart_real_smul]
    have h := (overlap_of_close J Z hJ r hr herr).smul hs
    convert h using 1
    simp only [smul_sub,smul_smul]
    congr 1
    dsimp [s,r]
    ring
  · rw [adMap_real_smul,smul_smul]
    have h := cpLe_smul_real hDom (β*s^2) (mul_nonneg hβ.le (sq_nonneg _))
    have hcoef : β*s^2*(δ/β)≤1 := by
      have heq : β*s^2*(δ/β)=δ/(1+r)^2 := by dsimp [s]; field_simp
      rw [heq]
      apply (div_le_one (sq_pos_of_pos hden)).mpr
      nlinarith
    have h' : MatrixMap.CPLe (((β:ℂ) * ((s^2:ℝ):ℂ)) • adMap Z)
        (Complex.ofReal (β*s^2*(δ/β)) • M.toLinearMap) := by
      simpa only [smul_smul,Complex.ofReal_mul] using h
    simpa only [Complex.ofReal_one,one_smul] using cpLe_scalar_mono _ M hcoef h'

/-- The operational beta is finite because the identity effect is feasible. -/
theorem singleBeta_le_one (N M : KrausChannel a b) (ha : 0<a) (δ : ℝ) (hδ : 0≤δ) :
    singleBeta N M δ ≤ 1 := by
  let ψ := unitProductInput ha
  let T : Effect (a*b) := ⟨1,Matrix.PosSemidef.one,by simpa using (Matrix.PosSemidef.zero : (0 : Operator (a*b)).PosSemidef)⟩
  have hprob (ρ : State (a*b)) : T.probability ρ=1 := by simp [T,Effect.probability,ρ.trace_one]
  have hp : 1-δ≤T.probability (pureOutput N ψ) := by rw [hprob]; linarith
  exact (iInf_le (fun t : {t : UnitPureInput a a × Effect (a*b) //
    1-δ≤t.2.probability (pureOutput N t.1)} =>
    ENNReal.ofReal (t.val.2.probability (pureOutput M t.val.1))) ⟨(ψ,T),hp⟩).trans_eq (by simp [hprob])

/-- Lemma 25, with β literally the positive actual single-channel testing
optimum, and exactly the paper's overlap constant. -/
theorem lemma_25 (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (ha : 0<a) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hβ : 0<singleBeta (isometryChannel J hJ) M δ) :
    ∃ V : Matrix (Fin b) (Fin a) ℂ, ‖V‖≤1 ∧
      (realPart (Jᴴ*V)-((1-Real.sqrt (1-δ))/(1+Real.sqrt (1-δ))) • (1 : Operator a)).PosSemidef ∧
      MatrixMap.CPLe (((singleBeta (isometryChannel J hJ) M δ).toReal : ℂ) • adMap V) M.toLinearMap := by
  have htop : singleBeta (isometryChannel J hJ) M δ ≠ ⊤ :=
    ne_of_lt ((singleBeta_le_one _ M ha δ hδ.le).trans_lt (by simp))
  exact branch_of_testing_lower_bound J hJ M ha δ _ hδ hδ1
    (ENNReal.toReal_pos hβ.ne' htop) (by rw [ENNReal.ofReal_toReal htop])

end GeneralizedChannelStein.BranchExtraction
