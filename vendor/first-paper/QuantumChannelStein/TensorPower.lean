import QuantumChannelStein.TensorAlgebra

/-!
# Genuine tensor powers and their approximation errors

The index type is a recursively parenthesized finite product. The zeroth
power acts on the one-dimensional space indexed by `PUnit`, and successors
are actual matrix Kronecker products. Every norm is the Hilbert L2 operator
norm. No tensor-norm or tensor-power properties are assumed.
-/

noncomputable section
namespace QuantumChannelStein.TensorPower
open scoped Kronecker Matrix.Norms.L2Operator
open Matrix

universe u v w

/-- Coordinates of the `k`-fold tensor product, including its one-dimensional
zeroth tensor power. -/
def Index (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => ι × Index ι k

instance instUniqueIndexZero {ι : Type u} : Unique (Index ι 0) :=
  inferInstanceAs (Unique PUnit)

instance instFintypeIndex {ι : Type u} [Fintype ι] : (k : ℕ) → Fintype (Index ι k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k + 1 => by
    letI := instFintypeIndex (ι := ι) k
    exact inferInstanceAs (Fintype (ι × Index ι k))

instance instDecidableEqIndex {ι : Type u} [DecidableEq ι] :
    (k : ℕ) → DecidableEq (Index ι k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k + 1 => by
    letI := instDecidableEqIndex (ι := ι) k
    exact inferInstanceAs (DecidableEq (ι × Index ι k))

/-- Actual rectangular matrix tensor powers, with a scalar identity at zero. -/
def tensorPower {m : Type u} {n : Type v} (A : Matrix m n ℂ) :
    (k : ℕ) → Matrix (Index m k) (Index n k) ℂ
  | 0 => fun _ _ => 1
  | k + 1 => A ⊗ₖ tensorPower A k

@[simp] theorem tensorPower_zero {m : Type u} {n : Type v} (A : Matrix m n ℂ) :
    tensorPower A 0 = fun _ _ => 1 := rfl

@[simp] theorem tensorPower_succ {m : Type u} {n : Type v} (A : Matrix m n ℂ) (k : ℕ) :
    tensorPower A (k + 1) = A ⊗ₖ tensorPower A k := rfl

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The zeroth tensor power has norm one even when the original input or
output space is empty. -/
@[simp] theorem norm_tensorPower_zero (A : Matrix m n ℂ) : ‖tensorPower A 0‖ = 1 := by
  have hbound : ‖tensorPower A 0‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖WithLp.toLp 2 ((tensorPower A 0) *ᵥ WithLp.ofLp x)‖ ≤ 1 * ‖x‖
    simp [tensorPower, Index, Matrix.mulVec, dotProduct, EuclideanSpace.norm_eq]
  have h := Matrix.l2_opNorm_mulVec (tensorPower A 0)
    (WithLp.toLp 2 (fun _ : Index n 0 => (1 : ℂ)))
  have hlower : 1 ≤ ‖tensorPower A 0‖ := by
    simpa [tensorPower, Index, Matrix.mulVec, dotProduct, EuclideanSpace.norm_eq] using h
  exact le_antisymm hbound hlower

/-- Submultiplicativity for genuine `k`-fold tensor powers. -/
theorem norm_tensorPower_le (A : Matrix m n ℂ) (k : ℕ) :
    ‖tensorPower A k‖ ≤ ‖A‖ ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using (norm_tensorPower_zero A).le
  | succ k ih =>
    calc
      ‖tensorPower A (k + 1)‖ ≤ ‖A‖ * ‖tensorPower A k‖ :=
        TensorAlgebra.kronecker_opNorm_le _ _
      _ ≤ ‖A‖ * ‖A‖ ^ k := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖A‖ ^ (k + 1) := by rw [pow_succ'];

/-- A tensor power of a contraction is a contraction. -/
theorem norm_tensorPower_le_one (A : Matrix m n ℂ) (hA : ‖A‖ ≤ 1) (k : ℕ) :
    ‖tensorPower A k‖ ≤ 1 :=
  (norm_tensorPower_le A k).trans (pow_le_one₀ (norm_nonneg _) hA)

/-- Tensor powers preserve an operator approximation with the standard
finite-block telescoping error. This is an operator lemma for rectangular
matrices, not a full channel-amplification theorem. -/
theorem norm_tensorPower_sub_le (A B : Matrix m n ℂ) {e : ℝ}
    (herror : ‖A - B‖ ≤ e) (hB : ‖B‖ ≤ 1) (k : ℕ) :
    ‖tensorPower A k - tensorPower B k‖ ≤ (k : ℝ) * e * (1 + e) ^ (k - 1) := by
  have he : 0 ≤ e := (norm_nonneg _).trans herror
  have hq : 1 ≤ 1 + e := by linarith
  have hA : ‖A‖ ≤ 1 + e := by
    calc
      ‖A‖ ≤ ‖B‖ + ‖A - B‖ := norm_le_insert' _ _
      _ ≤ 1 + e := add_le_add hB herror
  have hApow (j : ℕ) : ‖tensorPower A j‖ ≤ (1 + e) ^ j :=
    (norm_tensorPower_le A j).trans (pow_le_pow_left₀ (norm_nonneg _) hA j)
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : (1 + e) ^ (k - 1) ≤ (1 + e) ^ k :=
      pow_le_pow_right₀ hq (Nat.sub_le k 1)
    calc
      ‖tensorPower A (k + 1) - tensorPower B (k + 1)‖ ≤
          ‖A - B‖ * ‖tensorPower A k‖ + ‖B‖ * ‖tensorPower A k - tensorPower B k‖ :=
        TensorAlgebra.kronecker_difference_le _ _ _ _
      _ ≤ e * (1 + e) ^ k + 1 * ((k : ℝ) * e * (1 + e) ^ (k - 1)) := by
        apply add_le_add
        · exact mul_le_mul herror (hApow k) (norm_nonneg _) he
        · exact mul_le_mul hB ih (norm_nonneg _) zero_le_one
      _ ≤ e * (1 + e) ^ k + (k : ℝ) * e * (1 + e) ^ k := by
        simp only [one_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
      _ = ((k + 1 : ℕ) : ℝ) * e * (1 + e) ^ (k + 1 - 1) := by
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Tensor powers respect composition, on the same recursive tensor indices. -/
theorem tensorPower_mul {r : Type w} [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (B : Matrix n r ℂ) (k : ℕ) :
    tensorPower (A * B) k = tensorPower A k * tensorPower B k := by
  induction k with
  | zero =>
    ext i j
    simp [tensorPower, Index, Matrix.mul_apply]
  | succ k ih =>
    simp only [tensorPower_succ, ih, Matrix.mul_kronecker_mul]

omit [Fintype m] in
/-- The tensor power of an identity is the identity on the tensor space. -/
@[simp] theorem tensorPower_one (k : ℕ) :
    tensorPower (1 : Matrix m m ℂ) k = 1 := by
  induction k with
  | zero =>
    ext i j
    simpa [tensorPower, Matrix.one_apply] using (Subsingleton.elim i j)
  | succ k ih =>
    simp only [tensorPower_succ, ih, Matrix.one_kronecker_one]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Tensor powers respect the Hilbert adjoint. -/
@[simp] theorem tensorPower_conjTranspose (A : Matrix m n ℂ) (k : ℕ) :
    tensorPower Aᴴ k = (tensorPower A k)ᴴ := by
  induction k with
  | zero =>
    ext i j
    simp [tensorPower, Matrix.conjTranspose_apply]
  | succ k ih =>
    rw [tensorPower_succ, tensorPower_succ, Matrix.conjTranspose_kronecker, ih]

omit [DecidableEq m] in
/-- Tensor powers preserve isometries, including their zero-fold identity. -/
theorem tensorPower_isometry (A : Matrix m n ℂ) (hA : Aᴴ * A = 1) (k : ℕ) :
    (tensorPower A k)ᴴ * tensorPower A k = 1 := by
  rw [← tensorPower_conjTranspose, ← tensorPower_mul, hA, tensorPower_one]

end QuantumChannelStein.TensorPower

noncomputable section
namespace QuantumChannelStein.TensorPower
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix WithLp

section Reindex
variable {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

/-- Transport a Euclidean vector by a finite coordinate equivalence. -/
def reindexVector (e : a ≃ b) (x : EuclideanSpace ℂ a) : EuclideanSpace ℂ b :=
  toLp 2 (fun i => x (e.symm i))

omit [DecidableEq a] [DecidableEq b] in
@[simp] theorem reindexVector_norm (e : a ≃ b) (x : EuclideanSpace ℂ a) :
    ‖reindexVector e x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, reindexVector, PiLp.toLp_apply]
  exact congrArg Real.sqrt (e.symm.sum_comp (fun i => ‖x i‖ ^ 2))

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
  [DecidableEq c] [DecidableEq d] in
theorem reindex_mulVec (e : a ≃ b) (f : c ≃ d) (A : Matrix a c ℂ)
    (x : EuclideanSpace ℂ d) :
    toLp 2 (Matrix.reindex e f A *ᵥ ofLp x) =
      reindexVector e (toLp 2 (A *ᵥ ofLp (reindexVector f.symm x))) := by
  ext i
  simp only [PiLp.toLp_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    reindexVector, ofLp_toLp, Equiv.symm_symm, Function.comp_apply]
  rfl

omit [DecidableEq a] [DecidableEq b] in
theorem norm_reindex_le (e : a ≃ b) (f : c ≃ d) (A : Matrix a c ℂ) :
    ‖Matrix.reindex e f A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖toLp 2 (Matrix.reindex e f A *ᵥ ofLp x)‖ ≤ ‖A‖ * ‖x‖
  rw [reindex_mulVec, reindexVector_norm]
  have h := Matrix.l2_opNorm_mulVec A (reindexVector f.symm x)
  simpa only [reindexVector_norm] using h

omit [DecidableEq a] [DecidableEq b] in
/-- Arbitrary bijective row and column reindexing preserves the L2 operator norm. -/
theorem norm_reindex (e : a ≃ b) (f : c ≃ d) (A : Matrix a c ℂ) :
    ‖Matrix.reindex e f A‖ = ‖A‖ := by
  apply le_antisymm (norm_reindex_le e f A)
  have h := norm_reindex_le e.symm f.symm (Matrix.reindex e f A)
  have heq : Matrix.reindex e.symm f.symm (Matrix.reindex e f A) = A := by
    ext i j
    simp [Matrix.reindex_apply]
  simpa only [heq] using h
end Reindex

/-- The recursive tensor coordinates are the usual finite strings. -/
def indexEquiv (ι : Type*) : (k : ℕ) → Index ι k ≃ (Fin k → ι)
  | 0 => (Equiv.equivPUnit (Fin 0 → ι)).symm
  | k + 1 => (Equiv.prodCongr (Equiv.refl ι) (indexEquiv ι k)).trans
      (Fin.consEquiv (fun _ => ι))

@[simp] theorem indexEquiv_succ_zero (ι : Type*) (k : ℕ) (i : Index ι (k + 1)) :
    indexEquiv ι (k + 1) i 0 = i.1 := by
  simp only [indexEquiv, Equiv.trans_apply, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero]
  rfl

@[simp] theorem indexEquiv_succ_succ (ι : Type*) (k : ℕ) (i : Index ι (k + 1))
    (j : Fin k) : indexEquiv ι (k + 1) i j.succ = indexEquiv ι k i.2 j := by
  simp only [indexEquiv, Equiv.trans_apply, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_succ]
  rfl

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Every entry is the product of the entries at its tensor coordinates. -/
theorem tensorPower_apply_eq_prod (A : Matrix m n ℂ) (k : ℕ)
    (i : Index m k) (j : Index n k) :
    tensorPower A k i j = ∏ l : Fin k, A (indexEquiv m k i l) (indexEquiv n k j l) := by
  induction k with
  | zero => simp [tensorPower]
  | succ k ih =>
    change A i.1 j.1 * tensorPower A k i.2 j.2 = _
    rw [Fin.prod_univ_succ, ih]
    simp only [indexEquiv_succ_zero, indexEquiv_succ_succ]

/-- Tensor powers in the common finite-string coordinate convention. -/
def finTensorPower (A : Matrix m n ℂ) (k : ℕ) : Matrix (Fin k → m) (Fin k → n) ℂ :=
  Matrix.reindex (indexEquiv m k) (indexEquiv n k) (tensorPower A k)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
@[simp] theorem finTensorPower_apply (A : Matrix m n ℂ) (k : ℕ)
    (i : Fin k → m) (j : Fin k → n) :
    finTensorPower A k i j = ∏ l : Fin k, A (i l) (j l) := by
  simp [finTensorPower, Matrix.reindex_apply, Matrix.submatrix_apply, tensorPower_apply_eq_prod]

omit [DecidableEq m] in
@[simp] theorem norm_finTensorPower (A : Matrix m n ℂ) (k : ℕ) :
    ‖finTensorPower A k‖ = ‖tensorPower A k‖ :=
  norm_reindex _ _ _

theorem norm_finTensorPower_le (A : Matrix m n ℂ) (k : ℕ) :
    ‖finTensorPower A k‖ ≤ ‖A‖ ^ k := by
  rw [norm_finTensorPower]
  exact norm_tensorPower_le A k

theorem norm_finTensorPower_sub_le (A B : Matrix m n ℂ) {e : ℝ}
    (herror : ‖A - B‖ ≤ e) (hB : ‖B‖ ≤ 1) (k : ℕ) :
    ‖finTensorPower A k - finTensorPower B k‖ ≤ (k : ℝ) * e * (1 + e) ^ (k - 1) := by
  have heq : finTensorPower A k - finTensorPower B k =
      Matrix.reindex (indexEquiv m k) (indexEquiv n k) (tensorPower A k - tensorPower B k) := by
    ext i j
    rfl
  rw [heq, norm_reindex]
  exact norm_tensorPower_sub_le A B herror hB k

end QuantumChannelStein.TensorPower

noncomputable section
namespace QuantumChannelStein.TensorPower
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix

/-- The standard regrouping of tensor coordinates pairs all first factors
and all second factors, preserving their original orders. -/
def indexProdEquiv (m n : Type*) (k : ℕ) : Index (m × n) k ≃ Index m k × Index n k :=
  (indexEquiv (m × n) k).trans
    ((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => m) (fun _ => n)).trans
      (Equiv.prodCongr (indexEquiv m k).symm (indexEquiv n k).symm))

@[simp] theorem indexEquiv_indexProdEquiv_symm (m n : Type*) (k : ℕ)
    (i : Index m k) (j : Index n k) (l : Fin k) :
    indexEquiv (m × n) k ((indexProdEquiv m n k).symm (i, j)) l =
      (indexEquiv m k i l, indexEquiv n k j l) := by
  simp [indexProdEquiv, Equiv.arrowProdEquivProdArrow]

/-- Tensor powers commute with Kronecker products after the canonical
coordinate regrouping. This is an equality of actual matrices. -/
theorem tensorPower_kronecker {m n r s : Type*}
    (A : Matrix m n ℂ) (B : Matrix r s ℂ) (k : ℕ) :
    Matrix.reindex (indexProdEquiv m r k) (indexProdEquiv n s k)
        (tensorPower (A ⊗ₖ B) k) = tensorPower A k ⊗ₖ tensorPower B k := by
  ext ⟨i, j⟩ ⟨p, q⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, tensorPower_apply_eq_prod,
    indexEquiv_indexProdEquiv_symm, Matrix.kronecker_apply, Finset.prod_mul_distrib]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Two contractions have the sharper linear tensor-power error bound. -/
theorem norm_tensorPower_sub_le_mul (A B : Matrix m n ℂ) {e : ℝ}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (herror : ‖A - B‖ ≤ e) (k : ℕ) :
    ‖tensorPower A k - tensorPower B k‖ ≤ (k : ℝ) * e := by
  have he : 0 ≤ e := (norm_nonneg _).trans herror
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖tensorPower A (k + 1) - tensorPower B (k + 1)‖ ≤
          ‖A - B‖ * ‖tensorPower A k‖ + ‖B‖ * ‖tensorPower A k - tensorPower B k‖ :=
        TensorAlgebra.kronecker_difference_le _ _ _ _
      _ ≤ e * 1 + 1 * ((k : ℝ) * e) := by
        apply add_le_add
        · exact mul_le_mul herror (norm_tensorPower_le_one A hA k) (norm_nonneg _) he
        · exact mul_le_mul hB ih (norm_nonneg _) zero_le_one
      _ = ((k + 1 : ℕ) : ℝ) * e := by push_cast; ring

end QuantumChannelStein.TensorPower

noncomputable section
namespace QuantumChannelStein.TensorPower
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix

/-- Concatenate two groups of tensor coordinates, retaining their orders. -/
def indexAddEquiv (ι : Type*) (p q : ℕ) :
    Index ι p × Index ι q ≃ Index ι (p + q) :=
  (Equiv.prodCongr (indexEquiv ι p) (indexEquiv ι q)).trans
    ((Equiv.sumArrowEquivProdArrow (Fin p) (Fin q) ι).symm.trans
      ((Equiv.piCongrLeft (fun _ : Fin (p + q) => ι) finSumFinEquiv).trans
        (indexEquiv ι (p + q)).symm))

@[simp] theorem indexEquiv_indexAddEquiv_left (ι : Type*) (p q : ℕ)
    (i : Index ι p) (j : Index ι q) (l : Fin p) :
    indexEquiv ι (p + q) (indexAddEquiv ι p q (i, j)) (Fin.castAdd q l) =
      indexEquiv ι p i l := by
  simp [indexAddEquiv, Equiv.piCongrLeft, Equiv.sumArrowEquivProdArrow]

@[simp] theorem indexEquiv_indexAddEquiv_right (ι : Type*) (p q : ℕ)
    (i : Index ι p) (j : Index ι q) (l : Fin q) :
    indexEquiv ι (p + q) (indexAddEquiv ι p q (i, j)) (Fin.natAdd p l) =
      indexEquiv ι q j l := by
  simp [indexAddEquiv, Equiv.piCongrLeft, Equiv.sumArrowEquivProdArrow]

/-- Actual tensor powers satisfy the addition law after canonical padding. -/
theorem tensorPower_add_reindex {a b : Type*} (A : Matrix a b ℂ) (p q : ℕ) :
    Matrix.reindex (indexAddEquiv a p q) (indexAddEquiv b p q)
      (tensorPower A p ⊗ₖ tensorPower A q) = tensorPower A (p + q) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (indexAddEquiv a p q).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (indexAddEquiv b p q).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kronecker_apply, tensorPower_apply_eq_prod, Fin.prod_univ_add,
    indexEquiv_indexAddEquiv_left, indexEquiv_indexAddEquiv_right]

/-- Block-major coordinates for `m` consecutive blocks of `k` factors. -/
def blockIndexEquiv (k m : ℕ) : Fin m × Fin k ≃ Fin (k * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m k))

/-- Flatten nested tensor coordinates, retaining block-major order. -/
def indexMulEquiv (ι : Type*) (k m : ℕ) :
    Index (Index ι k) m ≃ Index ι (k * m) :=
  (indexEquiv (Index ι k) m).trans
    ((Equiv.piCongrRight (fun _ : Fin m => indexEquiv ι k)).trans
      ((Equiv.curry (Fin m) (Fin k) ι).symm.trans
        ((Equiv.piCongrLeft (fun _ : Fin (k * m) => ι) (blockIndexEquiv k m)).trans
          (indexEquiv ι (k * m)).symm)))

@[simp] theorem indexEquiv_indexMulEquiv (ι : Type*) (k m : ℕ)
    (i : Index (Index ι k) m) (b : Fin m) (l : Fin k) :
    indexEquiv ι (k * m) (indexMulEquiv ι k m i) (blockIndexEquiv k m (b, l)) =
      indexEquiv ι k (indexEquiv (Index ι k) m i b) l := by
  simp [indexMulEquiv, Equiv.piCongrLeft, Equiv.piCongrRight, Equiv.curry]

/-- Nested tensor powers flatten to the product of blocklengths, as an
actual matrix identity after canonical coordinate reindexing. -/
theorem tensorPower_mul_reindex {a b : Type*} (A : Matrix a b ℂ) (k m : ℕ) :
    Matrix.reindex (indexMulEquiv a k m) (indexMulEquiv b k m)
      (tensorPower (tensorPower A k) m) = tensorPower A (k * m) := by
  ext i j
  obtain ⟨i, rfl⟩ := (indexMulEquiv a k m).surjective i
  obtain ⟨j, rfl⟩ := (indexMulEquiv b k m).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    tensorPower_apply_eq_prod]
  rw [← (blockIndexEquiv k m).prod_comp
    (fun l => A (indexEquiv a (k * m) (indexMulEquiv a k m i) l)
      (indexEquiv b (k * m) (indexMulEquiv b k m j) l)), Fintype.prod_prod_type]
  simp only [indexEquiv_indexMulEquiv]

end QuantumChannelStein.TensorPower
