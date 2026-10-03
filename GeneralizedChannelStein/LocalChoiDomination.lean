import GeneralizedChannelStein.LocalReplacement
import QuantumChannelStein.PositiveSplitting

/-! # The single-support multiplier bound without Weyl twirling -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace GeneralizedChannelStein.LocalChoiDomination
open QuantumChannelStein Matrix ChannelEntropy BranchExtraction LocalReplacement
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c d : ℕ}

def splitEquiv (a b c d : ℕ) : Fin (a*b) × Fin (c*d) ≃ Fin (a*c) × Fin (b*d) :=
  (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodCongr finProdFinEquiv finProdFinEquiv))

def columns (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ) : Matrix (Fin (a*c)) (Fin (b*d)) ℂ :=
  fun u v => K (finProdFinEquiv ((finProdFinEquiv.symm u).2,(finProdFinEquiv.symm v).2))
    (finProdFinEquiv ((finProdFinEquiv.symm u).1,(finProdFinEquiv.symm v).1))

def splitChoi (P : MatrixMap (a*b) (c*d)) :
    Matrix (Fin (a*c) × Fin (b*d)) (Fin (a*c) × Fin (b*d)) ℂ :=
  Matrix.reindex (splitEquiv a b c d) (splitEquiv a b c d) (MatrixMap.choi P)

theorem choi_adMap_apply {u v : ℕ} (K : Matrix (Fin v) (Fin u) ℂ)
    (i j : Fin u) (x y : Fin v) :
    MatrixMap.choi (adMap K) (i,x) (j,y)=K x i * star (K y j) := by
  simp [MatrixMap.choi,adMap_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.single,ite_and]

theorem splitChoi_adMap (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ) :
    splitChoi (adMap K)=Matrix.vecMulVec (fun x => columns K x.1 x.2)
      (star (fun x => columns K x.1 x.2)) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨u1,u2⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨v1,v2⟩,rfl⟩ := finProdFinEquiv.surjective v
  have hd {p q : ℕ} (x : Fin p) (y : Fin q) : (finProdFinEquiv (x,y)).divNat=x :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x,y))
  have hm {p q : ℕ} (x : Fin p) (y : Fin q) : (finProdFinEquiv (x,y)).modNat=y :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (x,y))
  simp [splitChoi,splitEquiv,Matrix.reindex_apply,choi_adMap_apply,columns,Matrix.vecMulVec_apply,Pi.star_apply,hd,hm]

theorem traceOutput_splitChoi_adMap (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ) :
    KrausChannel.traceOutput (splitChoi (adMap K))=columns K*(columns K)ᴴ := by
  rw [splitChoi_adMap]
  rfl

theorem splitChoi_replaced_identity (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ) :
    splitChoi (replacedMap (adMap K) 1 1)=
      (columns K*(columns K)ᴴ) ⊗ₖ (1 : Operator (b*d)) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨u1,u2⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨v1,v2⟩,rfl⟩ := finProdFinEquiv.surjective v
  have hd {p q : ℕ} (x : Fin p) (y : Fin q) : (finProdFinEquiv (x,y)).divNat=x :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x,y))
  have hm {p q : ℕ} (x : Fin p) (y : Fin q) : (finProdFinEquiv (x,y)).modNat=y :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (x,y))
  simp [splitChoi,splitEquiv,Matrix.reindex_apply,MatrixMap.choi,replacedMap,replaceRight,
    adMap_apply,columns,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    Matrix.single,← finProdFinEquiv.sum_comp,Fintype.sum_prod_type,
    finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,ite_and,hd,hm]
  split_ifs <;> simp_all
  exact Finset.sum_comm

def outputLocal (c : ℕ) (F : Operator d) : Operator (c*d) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv ((1:Operator c) ⊗ₖ F)

theorem norm_outputLocal_le (c : ℕ) (F : Operator d) : ‖outputLocal c F‖≤‖F‖ := by
  rw [outputLocal,TensorPower.norm_reindex]
  exact TensorNorm.one_kronecker_opNorm_le F

theorem columns_outputLocal (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ) (F : Operator d) :
    columns (outputLocal c F*K)=columns K * outputLocal b Fᵀ := by
  ext i u
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨u1,u2⟩,rfl⟩ := finProdFinEquiv.surjective u
  have hd {p q : ℕ} (x : Fin p) (y : Fin q) : (finProdFinEquiv (x,y)).divNat=x :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x,y))
  have hm {p q : ℕ} (x : Fin p) (y : Fin q) : (finProdFinEquiv (x,y)).modNat=y :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (x,y))
  simp [columns,outputLocal,Matrix.reindex_apply,Matrix.mul_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply,← finProdFinEquiv.sum_comp,Fintype.sum_prod_type,hd,hm,mul_comm]

/-- A contraction on the discarded output does not increase the retained Choi marginal. -/
theorem marginal_outputLocal_le (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ)
    (F : Operator d) (hF : ‖F‖≤1) :
    (columns K*(columns K)ᴴ-columns (outputLocal c F*K)*(columns (outputLocal c F*K))ᴴ).PosSemidef := by
  have hn : ‖outputLocal b Fᵀ‖≤1 :=
    (norm_outputLocal_le b Fᵀ).trans (by simpa only [TransposeNorm.opNorm_transpose] using hF)
  have hp := (gram_le_one_of_norm_le_one (outputLocal b Fᵀ) hn).mul_mul_conjTranspose_same (columns K)
  rw [columns_outputLocal]
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.conjTranspose_mul,Matrix.mul_assoc] using hp

/-- Dimension control on the replaced input-output Choi factor gives the
single-support bound with precisely dimension b*d. -/
theorem ad_outputLocal_le_replaced_identity (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ)
    (F : Operator d) (hF : ‖F‖≤1) :
    MatrixMap.CPLe (adMap (outputLocal c F*K))
      (Complex.ofReal (b*d:ℕ) • replacedMap (adMap K) 1 1) := by
  have hpos : (splitChoi (adMap (outputLocal c F*K))).PosSemidef := by
    rw [splitChoi_adMap]
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hdim := DimensionDomination.dimension_order _ hpos
  rw [traceOutput_splitChoi_adMap] at hdim
  have hmar := (MatrixMap.posSemidef_kronecker (marginal_outputLocal_le K F hF)
    (Matrix.PosSemidef.one (n:=Fin (b*d)))).smul (show (0:ℝ)≤(b*d:ℕ) from Nat.cast_nonneg _)
  have hsum := hmar.add hdim
  have hK : (columns K*(columns K)ᴴ-columns (outputLocal c F*K)*(columns (outputLocal c F*K))ᴴ) ⊗ₖ
      (1 : Operator (b*d)) =
      (columns K*(columns K)ᴴ) ⊗ₖ (1 : Operator (b*d)) -
      (columns (outputLocal c F*K)*(columns (outputLocal c F*K))ᴴ) ⊗ₖ (1 : Operator (b*d)) := by
    ext i j
    simp only [Matrix.kroneckerMap_apply,Matrix.sub_apply,sub_mul]
  rw [hK,smul_sub,sub_add_sub_cancel] at hsum
  have hh : (((b*d:ℕ):ℝ) • splitChoi (replacedMap (adMap K) 1 1)-
      splitChoi (adMap (outputLocal c F*K))).PosSemidef := by
    rwa [splitChoi_replaced_identity]
  rw [MatrixMap.cpLe_iff_choi_difference,MatrixMap.choi_smul]
  have hs := hh.submatrix (splitEquiv a b c d)
  convert hs using 1
  ext i j
  change (Complex.ofReal (b*d:ℕ) * MatrixMap.choi (replacedMap (adMap K) 1 1) i j -
    MatrixMap.choi (adMap (outputLocal c F*K)) i j) =
    (((b*d:ℕ):ℝ) • MatrixMap.choi (replacedMap (adMap K) 1 1)
      ((splitEquiv a b c d).symm ((splitEquiv a b c d) i))
      ((splitEquiv a b c d).symm ((splitEquiv a b c d) j)) -
    MatrixMap.choi (adMap (outputLocal c F*K))
      ((splitEquiv a b c d).symm ((splitEquiv a b c d) i))
      ((splitEquiv a b c d).symm ((splitEquiv a b c d) j)))
  simp only [Equiv.symm_apply_apply,Complex.real_smul]

/-- A supported contraction is dominated by actual input/output replacement
at precisely the coefficient tw/(local-input-dimension*local-output-dimension). -/
theorem local_multiplier_cpLe (M : MatrixMap (a*b) (c*d))
    (K : Matrix (Fin (c*d)) (Fin (a*b)) ℂ) (F : Operator d) (hF : ‖F‖≤1)
    (τ : Operator b) (ω : Operator d) (hτ : τ.PosSemidef) (hω : ω.PosSemidef)
    (t w p : ℝ) (ht : 0<t) (hw : 0<w) (hp : 0≤p) (hb : 0<b) (hd : 0<d)
    (htτ : (τ-t • (1:Operator b)).PosSemidef) (hwω : (ω-w • (1:Operator d)).PosSemidef)
    (hdom : MatrixMap.CPLe (Complex.ofReal p • adMap K) M) :
    MatrixMap.CPLe (Complex.ofReal (p*t*w/(b*d:ℕ)) • adMap (outputLocal c F*K))
      (replacedMap M τ ω) := by
  have hn : (b*d:ℝ)≠0 := by positivity
  have h₁ := FreeAmplification.cpLe_smul_real (ad_outputLocal_le_replaced_identity K F hF)
    (t*w/(b*d:ℕ)) (by positivity)
  have hcoef : (t*w/(b*d:ℕ))*(b*d:ℕ)=t*w := by
    apply div_mul_cancel₀
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hb hd)
  simp only [smul_smul,← Complex.ofReal_mul,hcoef] at h₁
  have h₂ := replacedMap_lower (adMap K) (MatrixMap.completelyPositive_ofKraus _)
    τ ω hτ hω t w ht.le hw.le htτ hwω
  have h₃ := FreeAmplification.cpLe_smul_real (MatrixMap.cpLe_trans h₁ h₂) p hp
  have h₄ := replacedMap_cpLe hdom τ ω hτ hω
  rw [replacedMap_smul] at h₄
  have h := MatrixMap.cpLe_trans h₃ h₄
  simpa only [smul_smul,← Complex.ofReal_mul,mul_div_assoc,mul_assoc] using h

end GeneralizedChannelStein.LocalChoiDomination
