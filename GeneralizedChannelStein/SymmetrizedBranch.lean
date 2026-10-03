import GeneralizedChannelStein.FreeMultipliers
import GeneralizedChannelStein.TensorRecovery

/-! Actual finite permutation averaging of dominated rectangular branches. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.SymmetrizedBranch
open QuantumChannelStein Matrix ChannelPowerReindex ChannelTransport
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d n : ℕ}

def permute (π : Equiv.Perm (Fin n)) (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) :=
  Matrix.reindex (sitePermutation d n π) (sitePermutation a n π) V

def weight (n : ℕ) : ℝ := (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹

theorem weight_pos (n : ℕ) : 0<weight n := by unfold weight; positivity

theorem weight_sum (n : ℕ) : ∑ _ : Equiv.Perm (Fin n), weight n=1 := by
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,weight]
  exact mul_inv_cancel₀ (by positivity)

def average (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) :=
  ∑ π : Equiv.Perm (Fin n), weight n • permute π V

theorem norm_average (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (hV : ‖V‖≤1) :
    ‖average V‖≤1 := by
  calc
    _ ≤ ∑ π : Equiv.Perm (Fin n), ‖weight n • permute π V‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Equiv.Perm (Fin n), weight n := by
      apply Finset.sum_le_sum
      intro π _
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (weight_pos n),permute,TensorPower.norm_reindex]
      nlinarith [weight_pos n]
    _ = 1 := weight_sum n

theorem permute_power (J : Matrix (Fin d) (Fin a) ℂ) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    permute π (powerIsometry J n)=powerIsometry J n := by
  ext i j
  obtain ⟨i,rfl⟩ := (channelIndexEquiv d n).surjective i
  obtain ⟨j,rfl⟩ := (channelIndexEquiv a n).surjective j
  have h := TensorPermutation.tensorPower_permutation J n π
  have he := congrFun (congrFun h i) j
  simpa [permute,powerIsometry,sitePermutation,Matrix.reindex_apply] using he

theorem permute_mul (π σ : Equiv.Perm (Fin n)) (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) :
    permute π (permute σ V)=permute (π*σ) V := by
  ext i j
  simp [permute,sitePermutation,Matrix.reindex_apply,TensorPermutation.factorPermutation_mul]
  rfl

theorem average_invariant (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (π : Equiv.Perm (Fin n)) :
    permute π (average V)=average V := by
  change Matrix.reindexLinearEquiv ℂ ℂ (sitePermutation d n π) (sitePermutation a n π)
    (∑ σ,weight n•permute σ V)=_
  rw [map_sum]
  change (∑ σ,weight n•permute π (permute σ V))=_
  simp_rw [permute_mul]
  exact Equiv.sum_comp (Equiv.mulLeft π) (fun σ => weight n•permute σ V)

theorem average_free_dominator (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (hn : 0<n)
    (M : KrausChannel (a^n) (d^n)) (hM : M.toLinearMap∈F n)
    (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (p : ℝ) (hp : 0<p)
    (hdom : MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap V) M.toLinearMap) :
    ∃ M' : KrausChannel (a^n) (d^n), M'.toLinearMap∈F n ∧
      MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap (average V)) M'.toLinearMap := by
  have hmass : WeightedGramMixture.coefficientMass (fun _ : Equiv.Perm (Fin n) => Complex.ofReal (weight n)) (fun _ => 1)=1 := by
    simpa [WeightedGramMixture.coefficientMass,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos n)] using weight_sum n
  obtain ⟨M',hM',hD⟩ := WeightedGramMixture.free_mixture_dominator (F n) (hF.convex n hn)
    (fun _ : Equiv.Perm (Fin n) => Complex.ofReal (weight n)) (fun _ => 1)
    (fun π => permute π V) (fun π => permuteChannel n π M) hp (fun _ => zero_lt_one)
    (by rw [hmass]; norm_num)
    (fun π => hτ.permutation_closed n hn π M hM) (fun π => by
      have h := reindexMap_cpLe (sitePermutation a n π) (sitePermutation d n π) _ _ hdom
      simpa [reindexMap_smul,FreeMultipliers.reindexMap_adMap,← reindexChannel_map,permuteChannel,permute] using h)
  refine ⟨M',hM',?_⟩
  simpa only [hmass,one_pow,div_one,Complex.real_smul,average] using hD


theorem gram_permute (J : Matrix (Fin d) (Fin a) ℂ) (n : ℕ)
    (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (π : Equiv.Perm (Fin n)) :
    (powerIsometry J n)ᴴ*permute π V = permute π ((powerIsometry J n)ᴴ*V) := by
  have h := Matrix.reindexLinearEquiv_mul ℂ ℂ (sitePermutation a n π) (sitePermutation d n π)
    (sitePermutation a n π) (powerIsometry J n)ᴴ V
  change Matrix.reindex (sitePermutation a n π) (sitePermutation d n π) (powerIsometry J n)ᴴ *
    permute π V = permute π ((powerIsometry J n)ᴴ*V) at h
  rw [← Matrix.conjTranspose_reindex] at h
  change (permute π (powerIsometry J n))ᴴ*permute π V=_ at h
  simpa only [permute_power] using h

theorem realPart_permute (X : Operator (a^n)) (π : Equiv.Perm (Fin n)) :
    BranchExtraction.realPart (permute π X)=permute π (BranchExtraction.realPart X) := by
  ext i j
  simp [BranchExtraction.realPart,permute,Matrix.conjTranspose_apply,Matrix.reindex_apply]

theorem realPart_sum {η : Type} [Fintype η] (X : η → Operator a) :
    BranchExtraction.realPart (∑ i,X i)=∑ i,BranchExtraction.realPart (X i) := by
  simp [BranchExtraction.realPart,Matrix.conjTranspose_sum,Finset.sum_add_distrib,Finset.smul_sum]

theorem average_overlap (J : Matrix (Fin d) (Fin a) ℂ) (n : ℕ)
    (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (c : ℝ)
    (hcover : (BranchExtraction.realPart ((powerIsometry J n)ᴴ*V)-c•1).PosSemidef) :
    (BranchExtraction.realPart ((powerIsometry J n)ᴴ*average V)-c•1).PosSemidef := by
  have hsum : (∑ π : Equiv.Perm (Fin n), weight n • permute π
      (BranchExtraction.realPart ((powerIsometry J n)ᴴ*V)-c•1)).PosSemidef := by
    apply Finset.sum_induction
    · intro A B hA hB; exact hA.add hB
    · exact Matrix.PosSemidef.zero
    · intro π _
      exact (hcover.submatrix (sitePermutation a n π).symm).smul (weight_pos n).le
  have heq : BranchExtraction.realPart ((powerIsometry J n)ᴴ*average V)-c•1 =
      ∑ π : Equiv.Perm (Fin n), weight n • permute π
        (BranchExtraction.realPart ((powerIsometry J n)ᴴ*V)-c•1) := by
    simp only [average,Matrix.mul_sum,Matrix.mul_smul,gram_permute,realPart_sum,
      BranchExtraction.realPart_real_smul,realPart_permute]
    have hre (π : Equiv.Perm (Fin n)) (Y : Operator (a^n)) :
        permute π (Y-c•1)=permute π Y-c•1 := by
      ext i j
      simp [permute,Matrix.reindex_apply,Matrix.one_apply]
    simp_rw [hre,smul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_smul,weight_sum,one_smul]
  rw [heq]
  exact hsum

end GeneralizedChannelStein.SymmetrizedBranch
