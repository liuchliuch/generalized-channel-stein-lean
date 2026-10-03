import GeneralizedChannelStein.ImageProjector
import QuantumChannelStein.SpectralDecompositionCFC
import QuantumChannelStein.ChannelEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ImageProjector
open QuantumChannelStein Matrix LocalExpansion ImageProjectorScalars
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {k : ℕ}

/-- The literal matrix tensor product with a possibly different factor at every site. -/
def siteProduct (A : Fin k → Matrix ι ι ℂ) : Block ι k :=
  fun x y => ∏ i, A i (x i) (y i)

theorem siteProduct_mul (A B : Fin k → Matrix ι ι ℂ) :
    siteProduct (fun i => A i * B i) = siteProduct A * siteProduct B := by
  ext x y
  simp only [siteProduct,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

@[simp] theorem siteProduct_one : siteProduct (fun _ : Fin k => (1:Matrix ι ι ℂ)) = 1 := by
  ext x y
  by_cases h : x=y
  · subst y
    simp [siteProduct,Matrix.one_apply]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hz : (∏ j : Fin k, (1:Matrix ι ι ℂ) (x j) (y j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply,hi])
    change (∏ j : Fin k, (1:Matrix ι ι ℂ) (x j) (y j)) = _
    rw [hz]
    simp [Matrix.one_apply,h]

theorem siteProduct_adjoint (A : Fin k → Matrix ι ι ℂ) :
    siteProduct (fun i => (A i)ᴴ) = (siteProduct A)ᴴ := by
  ext x y
  simp [siteProduct,Matrix.conjTranspose_apply,map_prod]

theorem siteProduct_constant (A : Matrix ι ι ℂ) (k : ℕ) :
    siteProduct (fun _ : Fin k => A) = TensorPower.finTensorPower A k := by
  ext x y
  simp [siteProduct]

theorem oneSite_eq_siteProduct (i : Fin k) (A : Matrix ι ι ℂ) :
    oneSite i A = siteProduct (Function.update (fun _ => (1:Matrix ι ι ℂ)) i A) := by
  ext x y
  rw [oneSite,embed_apply]
  simp only [Matrix.reindex_apply,singletonEquiv,Equiv.symm_symm,Equiv.coe_fn_mk]
  change A (x i) (y i) * (if (fun j : {j // j∉({i}:Finset (Fin k))} => x j)=
      (fun j : {j // j∉({i}:Finset (Fin k))} => y j) then 1 else 0) = _
  by_cases hc : (fun j : {j // j∉({i}:Finset (Fin k))} => x j)=
      (fun j : {j // j∉({i}:Finset (Fin k))} => y j)
  · simp only [hc,ite_true,mul_one,siteProduct]
    symm
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      have hxy : x j=y j := congrFun hc ⟨j,by simpa using hji⟩
      simp [Function.update_of_ne hji,hxy]
    · simp
  · simp only [hc,ite_false,mul_zero,siteProduct]
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hc
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j.val)
    have hji : j.val≠i := by simpa using j.property
    simp [Function.update_of_ne hji,Matrix.one_apply,hj]

/-- Tensor powers of local unitaries are actual unitaries on the site strings. -/
def siteUnitary (U : Matrix.unitaryGroup ι ℂ) (k : ℕ) : Matrix.unitaryGroup (Fin k→ι) ℂ :=
  ⟨siteProduct (fun _ => (U : Matrix ι ι ℂ)), by
    rw [Matrix.mem_unitaryGroup_iff]
    change siteProduct (fun _ => (U : Matrix ι ι ℂ)) *
      (siteProduct (fun _ => (U : Matrix ι ι ℂ)))ᴴ = 1
    rw [← siteProduct_adjoint,← siteProduct_mul]
    simp only [show (U : Matrix ι ι ℂ)*(U : Matrix ι ι ℂ)ᴴ=1 from Unitary.mul_star_self_of_mem U.property]
    exact siteProduct_one⟩

/-- Conjugation of a tensor product acts independently on every factor. -/
theorem siteProduct_conjugate (U : Matrix.unitaryGroup ι ℂ) (A : Fin k→Matrix ι ι ℂ) :
    (siteUnitary U k : Block ι k)ᴴ * siteProduct A * (siteUnitary U k : Block ι k) =
      siteProduct (fun i => (U : Matrix ι ι ℂ)ᴴ * A i * (U : Matrix ι ι ℂ)) := by
  change (siteProduct (fun _ => (U : Matrix ι ι ℂ)))ᴴ * siteProduct A *
    siteProduct (fun _ => (U : Matrix ι ι ℂ)) = _
  rw [← siteProduct_adjoint,← siteProduct_mul,← siteProduct_mul]

def basisChange {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) : Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix α α ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix α α ℂ) U).symm

@[simp] theorem basisChange_apply {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    basisChange U A = (U : Matrix α α ℂ)ᴴ * A * (U : Matrix α α ℂ) := rfl

theorem basisChange_real_smul {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) (c : ℝ) :
    basisChange U (c•A) = c•basisChange U A := by
  simp only [basisChange_apply,Matrix.mul_smul,Matrix.smul_mul]

theorem norm_basisChange {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) : ‖basisChange U A‖ = ‖A‖ := by
  change ‖(star U : Matrix.unitaryGroup α ℂ).val * A * (U : Matrix α α ℂ)‖ = _
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

theorem basisChange_oneSite (U : Matrix.unitaryGroup ι ℂ) (i : Fin k) (A : Matrix ι ι ℂ) :
    basisChange (siteUnitary U k) (oneSite i A) = oneSite i (basisChange U A) := by
  rw [basisChange_apply,oneSite_eq_siteProduct,siteProduct_conjugate,oneSite_eq_siteProduct]
  congr 1
  funext j
  by_cases h : j=i
  · subst j; simp [basisChange_apply]
  · simp [Function.update_of_ne h,show (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)=1 from
      Unitary.star_mul_self_of_mem U.property]

theorem siteProduct_diagonal (d : Fin k → ι → ℂ) :
    siteProduct (fun i => Matrix.diagonal (d i)) = Matrix.diagonal (fun x => ∏ i, d i (x i)) := by
  ext x y
  by_cases h : x=y
  · subst y; simp [siteProduct]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hz : (∏ j : Fin k, Matrix.diagonal (d j) (x j) (y j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal_apply_ne _ hi])
    change (∏ j : Fin k, Matrix.diagonal (d j) (x j) (y j)) = _
    rw [hz]
    simp [Matrix.diagonal_apply_ne _ h]

theorem oneSite_diagonal (i : Fin k) (d : ι → ℂ) :
    oneSite i (Matrix.diagonal d) = Matrix.diagonal (fun x : Fin k→ι => d (x i)) := by
  rw [oneSite_eq_siteProduct]
  have heq : Function.update (fun _ : Fin k => (1:Matrix ι ι ℂ)) i (Matrix.diagonal d) =
      fun j => Matrix.diagonal (fun a => if j=i then d a else 1) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [h,Function.update_of_ne h]
  rw [heq,siteProduct_diagonal]
  congr 1
  funext x
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem basisChange_spectral {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    basisChange hP.eigenvectorUnitary P = Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
  let U := hP.eigenvectorUnitary
  have hd : basisChange U P = Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
    rw [basisChange_apply]
    conv_lhs => arg 1; arg 2; rw [hP.spectral_theorem]
    change (U : Matrix ι ι ℂ)ᴴ * ((U : Matrix ι ι ℂ) * _ * (U : Matrix ι ι ℂ)ᴴ) * (U : Matrix ι ι ℂ) = _
    have hu : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)=1 := Unitary.star_mul_self_of_mem U.property
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),hu,Matrix.one_mul]
    rw [Matrix.mul_one]
    rfl
  exact hd

theorem projection_eigenvalues {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) (i : ι) :
    hP.eigenvalues i=0 ∨ hP.eigenvalues i=1 := by
  let U := hP.eigenvectorUnitary
  have hd := basisChange_spectral hP
  have heq := congrArg (basisChange U) hPP
  rw [map_mul,hd,Matrix.diagonal_mul_diagonal] at heq
  have hi := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) heq
  simp only [Matrix.diagonal_apply_eq,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] at hi
  have hs : hP.eigenvalues i * (hP.eigenvalues i-1)=0 := by nlinarith
  rcases mul_eq_zero.mp hs with h|h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem projection_norm_le_one {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) : ‖P‖≤1 := by
  rw [← norm_basisChange hP.eigenvectorUnitary P,basisChange_spectral hP,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rcases projection_eigenvalues hP hPP i with h|h <;> simp [h]

theorem complement_projection_norm_le_one {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) : ‖1-P‖≤1 := by
  apply projection_norm_le_one (Matrix.isHermitian_one.sub hP)
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hPP]
  abel

def outsideCount (p : ι→ℝ) (x : Fin k→ι) : ℕ := (Finset.univ.filter (fun i => p (x i)=0)).card

theorem outsideCount_le (p : ι→ℝ) (x : Fin k→ι) : outsideCount p x ≤ k := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem sum_complement_eq_count (p : ι→ℝ) (hp : ∀ i, p i=0 ∨ p i=1) (x : Fin k→ι) :
    (∑ i, (1-p (x i))) = (outsideCount p x : ℝ) := by
  simp only [outsideCount,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases hp (x i) with h|h <;> simp [h]

theorem prod_eq_count_zero (p : ι→ℝ) (hp : ∀ i, p i=0 ∨ p i=1) (x : Fin k→ι) :
    (∏ i, p (x i)) = if outsideCount p x=0 then 1 else 0 := by
  by_cases hz : outsideCount p x=0
  · rw [if_pos hz]
    apply Finset.prod_eq_one
    intro i _
    rcases hp (x i) with hi|hi
    · have hmem : i∈Finset.univ.filter (fun i => p (x i)=0) := by simp [hi]
      have hpos := Finset.card_pos.mpr ⟨i,hmem⟩
      change 0 < outsideCount p x at hpos
      omega
    · exact hi
  · rw [if_neg hz]
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.mem_filter.mp hi).2

theorem basisChange_complement {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    basisChange hP.eigenvectorUnitary (1-P) =
      Matrix.diagonal (fun i => ((1-hP.eigenvalues i : ℝ):ℂ)) := by
  rw [map_sub,map_one,basisChange_spectral hP]
  ext i j
  by_cases h : i=j
  · subst j; simp
  · simp [Matrix.diagonal_apply_ne _ h,Matrix.one_apply_ne h]

theorem basisChange_count {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) (k : ℕ) :
    basisChange (siteUnitary hP.eigenvectorUnitary k) (∑ i : Fin k, oneSite i (1-P)) =
      Matrix.diagonal (fun x => ((outsideCount hP.eigenvalues x : ℝ):ℂ)) := by
  rw [map_sum]
  simp_rw [basisChange_oneSite,basisChange_complement hP,oneSite_diagonal]
  ext x y
  by_cases h : x=y
  · subst y
    simp only [Matrix.sum_apply,Matrix.diagonal_apply_eq]
    rw [← Complex.ofReal_sum,sum_complement_eq_count _ (projection_eigenvalues hP hPP)]
  · simp [Matrix.sum_apply,Matrix.diagonal_apply_ne _ h]

theorem basisChange_affine {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) (k : ℕ) :
    basisChange (siteUnitary hP.eigenvectorUnitary k) (affineMatrix (1-P) k) =
      Matrix.diagonal (fun x => ((((k:ℝ)+1-2*(outsideCount hP.eigenvalues x : ℝ))/((k:ℝ)-1) : ℝ):ℂ)) := by
  rw [affineMatrix,map_add,basisChange_real_smul,basisChange_real_smul,map_one,basisChange_count hP hPP]
  ext x y
  by_cases h : x=y
  · subst y
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.diagonal_apply_eq,Complex.real_smul]
    push_cast
    ring
  · simp [Matrix.diagonal_apply_ne _ h,Matrix.one_apply_ne h]

theorem basisChange_productProjection {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) (k : ℕ) :
    basisChange (siteUnitary hP.eigenvectorUnitary k) (TensorPower.finTensorPower P k) =
      Matrix.diagonal (fun x : Fin k→ι => if outsideCount hP.eigenvalues x=0 then (1:ℂ) else 0) := by
  rw [← siteProduct_constant,basisChange_apply,siteProduct_conjugate]
  change siteProduct (fun _ => basisChange hP.eigenvectorUnitary P) = _
  rw [basisChange_spectral,siteProduct_diagonal]
  congr 1
  funext x
  rw [← Complex.ofReal_prod,prod_eq_count_zero _ (projection_eigenvalues hP hPP)]
  split_ifs <;> simp

theorem basisChange_chebyshev (U : Matrix.unitaryGroup (Fin k→ι) ℂ) (X : Block ι k) (n : ℕ) :
    basisChange U (chebyshevMatrix X n) = chebyshevMatrix (basisChange U X) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact map_one (basisChange U)
  | one => rfl
  | more n ih0 ih1 => simp only [chebyshevMatrix,map_sub,map_smul,map_mul,ih0,ih1]

theorem chebyshev_diagonal (d : (Fin k→ι)→ℝ) (n : ℕ) :
    chebyshevMatrix (Matrix.diagonal (fun x => (d x : ℂ))) n =
      Matrix.diagonal (fun x => (((Polynomial.Chebyshev.T ℝ (n:ℤ)).eval (d x) : ℝ) : ℂ)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebyshevMatrix]
  | one => simp [chebyshevMatrix]
  | more n ih0 ih1 =>
    rw [chebyshevMatrix,ih0,ih1,Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases h : x=y
    · subst y
      simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,smul_eq_mul,
        Nat.cast_add,Nat.cast_ofNat,Polynomial.Chebyshev.T_add_two,Polynomial.eval_sub,
        Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      push_cast
      ring
    · simp [Matrix.diagonal_apply_ne _ h]

def filterValue (k : ℕ) (ξ z : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (filterDegree k ξ : ℤ)).eval
    (((k:ℝ)+1-2*z)/((k:ℝ)-1)) / denominator k (filterDegree k ξ)

theorem basisChange_filter {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P) (k : ℕ) (ξ : ℝ) :
    basisChange (siteUnitary hP.eigenvectorUnitary k) (filterMatrix P k ξ) =
      Matrix.diagonal (fun x : Fin k→ι => (filterValue k ξ (outsideCount hP.eigenvalues x) : ℂ)) := by
  rw [filterMatrix,basisChange_real_smul,basisChange_chebyshev,basisChange_affine hP hPP,chebyshev_diagonal]
  ext x y
  by_cases h : x=y
  · subst y
    simp only [Matrix.smul_apply,Matrix.diagonal_apply_eq,Complex.real_smul,filterValue]
    push_cast
    ring
  · simp [Matrix.diagonal_apply_ne _ h]

/-- Spectral norm bound for the genuine Chebyshev product-image filter. -/
theorem filter_norm_le_one {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P)
    (hk : 2≤k) {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ≤1) : ‖filterMatrix P k ξ‖≤1 := by
  rw [← norm_basisChange (siteUnitary hP.eigenvectorUnitary k),basisChange_filter hP hPP,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro x
  simp only [Complex.norm_real,Real.norm_eq_abs]
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  by_cases hz : outsideCount hP.eigenvalues x=0
  · simp only [hz,Nat.cast_zero,filterValue]
    rw [filter_at_zero hk']
    norm_num
  · apply (abs_filter_le_error hk' hξ _).trans hξ1
    constructor
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    · exact_mod_cast outsideCount_le hP.eigenvalues x

/-- Spectral error relative to the actual tensor-power projector. -/
theorem filter_error_le {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P)
    (hk : 2≤k) {ξ : ℝ} (hξ : 0<ξ) :
    ‖filterMatrix P k ξ - TensorPower.finTensorPower P k‖≤ξ := by
  rw [← norm_basisChange (siteUnitary hP.eigenvectorUnitary k),map_sub,
    basisChange_filter hP hPP,basisChange_productProjection hP hPP]
  have heq : (Matrix.diagonal (fun x : Fin k→ι => (filterValue k ξ (outsideCount hP.eigenvalues x) : ℂ)) -
      Matrix.diagonal (fun x : Fin k→ι => if outsideCount hP.eigenvalues x=0 then (1:ℂ) else 0)) =
      Matrix.diagonal (fun x : Fin k→ι => (filterValue k ξ (outsideCount hP.eigenvalues x) : ℂ) -
        if outsideCount hP.eigenvalues x=0 then 1 else 0) := by
        ext x y
        by_cases h : x=y <;> simp [Matrix.diagonal,h]
  rw [heq,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hξ.le).mpr
  intro x
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  by_cases hz : outsideCount hP.eigenvalues x=0
  · simp only [hz,Nat.cast_zero,filterValue,ite_true]
    rw [filter_at_zero hk']
    simpa using hξ.le
  · simp only [hz,ite_false,sub_zero,Complex.norm_real,Real.norm_eq_abs]
    apply abs_filter_le_error hk' hξ
    constructor
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    · exact_mod_cast outsideCount_le hP.eigenvalues x

/-- Lemma 29 for every local orthogonal projector. This stronger formulation
also covers a one-dimensional auxiliary register without an exceptional case. -/
theorem product_projector_approximation {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hPP : P*P=P)
    (hk : 2≤k) {ξ : ℝ} (hξ : 0<ξ) (hξupper : ξ≤1/16) :
    ∃ E : Expansion ι k,
      ‖E.value‖≤1 ∧ ‖E.value-TensorPower.finTensorPower P k‖≤ξ ∧
      E.HasSize (min k (filterDegree k ξ)) ∧ E.cost≤(15:ℝ)^(filterDegree k ξ) := by
  let hQ := complement_projection_norm_le_one hP hPP
  refine ⟨filterExpansion P hQ k ξ,?_,?_,filterExpansion_size P hQ k ξ,filterExpansion_cost P hQ hk ξ⟩
  · rw [filterExpansion_value]
    exact filter_norm_le_one hP hPP hk hξ (by linarith)
  · rw [filterExpansion_value]
    exact filter_error_le hP hPP hk hξ

section PaperCoordinates
variable {A C : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype C] [DecidableEq C] [Nonempty C]

/-- Explicitly regroup the site pairs into the input and auxiliary registers. -/
def regroup (A C : Type*) (k : ℕ) : (Fin k→A×C) ≃ (Fin k→A)×(Fin k→C) :=
  Equiv.arrowProdEquivProdArrow (Fin k) (fun _=>A) (fun _=>C)

theorem regroup_tensor (B : Matrix A A ℂ) (D : Matrix C C ℂ) (k : ℕ) :
    Matrix.reindex (regroup A C k) (regroup A C k) (TensorPower.finTensorPower (B⊗ₖD) k) =
      TensorPower.finTensorPower B k ⊗ₖ TensorPower.finTensorPower D k := by
  ext ⟨x,y⟩ ⟨x',y'⟩
  simp [regroup,Matrix.reindex_apply,Equiv.arrowProdEquivProdArrow,TensorPower.finTensorPower_apply,
    Matrix.kroneckerMap_apply,Finset.prod_mul_distrib]

theorem finTensorPower_one (k : ℕ) : TensorPower.finTensorPower (1:Matrix A A ℂ) k = 1 := by
  rw [← siteProduct_constant]
  exact siteProduct_one

theorem pureMatrix_projection (v : EuclideanSpace ℂ C) (hv : ‖v‖=1) :
    pureMatrix v * pureMatrix v = pureMatrix v := by
  have ht := ChannelEntropy.trace_pureMatrix_of_norm_one v hv
  have hdot : star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = 1 := by
    simpa only [pureMatrix,Matrix.trace_vecMulVec,dotProduct_comm] using ht
  rw [pureMatrix,Matrix.vecMulVec_mul_vecMulVec,hdot,one_smul]

/-- The paper's local image projector, with the prescribed auxiliary vector. -/
def localImage (v : EuclideanSpace ℂ C) : Matrix (A×C) (A×C) ℂ :=
  (1:Matrix A A ℂ) ⊗ₖ pureMatrix v

theorem localImage_hermitian (v : EuclideanSpace ℂ C) : (localImage (A:=A) v).IsHermitian :=
  (MatrixMap.posSemidef_kronecker Matrix.PosSemidef.one (ChannelEntropy.pureMatrix_positive v)).isHermitian

theorem localImage_projection (v : EuclideanSpace ℂ C) (hv : ‖v‖=1) :
    localImage (A:=A) v * localImage v = localImage v := by
  rw [localImage,← Matrix.mul_kronecker_mul,Matrix.one_mul,pureMatrix_projection v hv]

/-- Exact tensor-factor permutation identifying the target with the paper's
`I_(A^k) ⊗ (|0><0|)^⊗k`. -/
theorem regroup_product_image (v : EuclideanSpace ℂ C) (k : ℕ) :
    Matrix.reindex (regroup A C k) (regroup A C k)
      (TensorPower.finTensorPower (localImage (A:=A) v) k) =
      (1:Matrix (Fin k→A) (Fin k→A) ℂ) ⊗ₖ TensorPower.finTensorPower (pureMatrix v) k := by
  rw [localImage,regroup_tensor,finTensorPower_one]

/-- Lemma 29 with the paper's literal local space and its fixed unit vector.
The auxiliary register may be one-dimensional. -/
theorem lemma_29 (v : EuclideanSpace ℂ C) (hv : ‖v‖=1) (hk : 2≤k)
    {ξ : ℝ} (hξ : 0<ξ) (hξupper : ξ≤1/16) :
    ∃ E : Expansion (A×C) k,
      ‖E.value‖≤1 ∧
      ‖Matrix.reindex (regroup A C k) (regroup A C k) E.value -
        (1:Matrix (Fin k→A) (Fin k→A) ℂ) ⊗ₖ TensorPower.finTensorPower (pureMatrix v) k‖≤ξ ∧
      E.HasSize (min k (filterDegree k ξ)) ∧ E.cost≤(15:ℝ)^(filterDegree k ξ) := by
  obtain ⟨E,hE,herr,hsize,hcost⟩ := product_projector_approximation
    (localImage_hermitian (A:=A) v) (localImage_projection (A:=A) v hv) hk hξ hξupper
  refine ⟨E,hE,?_,hsize,hcost⟩
  rw [← regroup_product_image v k]
  have heq : Matrix.reindex (regroup A C k) (regroup A C k) E.value -
      Matrix.reindex (regroup A C k) (regroup A C k) (TensorPower.finTensorPower (localImage (A:=A) v) k) =
      Matrix.reindex (regroup A C k) (regroup A C k) (E.value-TensorPower.finTensorPower (localImage (A:=A) v) k) := rfl
  rw [heq,TensorPower.norm_reindex]
  exact herr
end PaperCoordinates

end GeneralizedChannelStein.ImageProjector
