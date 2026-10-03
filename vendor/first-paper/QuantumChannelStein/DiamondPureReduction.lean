import QuantumChannelStein.DiamondHermitianReduction

/-! # Pure-state formula for the genuine diamond norm of HP maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DiamondNorm
open Matrix hiding traceNorm
open ChannelEntropy TraceNorm
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b r : ℕ}

/-- Literal preservation of Hermitian matrices by a complex-linear map. -/
def IsHermiticityPreserving (Φ : MatrixMap a b) : Prop :=
  ∀ X : Operator a, X.IsHermitian → (Φ X).IsHermitian

/-- Complex linearity upgrades Hermitian preservation to preservation of adjoints. -/
theorem map_conjTranspose_of_hermiticityPreserving (Φ : MatrixMap a b)
    (hΦ : IsHermiticityPreserving Φ) (X : Operator a) : Φ Xᴴ = (Φ X)ᴴ := by
  have hR : (X + Xᴴ).IsHermitian := by
    change (X + Xᴴ)ᴴ = X + Xᴴ
    simp [add_comm]
  have hS : (Complex.I • (X - Xᴴ)).IsHermitian := by
    change (Complex.I • (X - Xᴴ))ᴴ = Complex.I • (X - Xᴴ)
    ext i j
    simp [smul_sub]
    ring
  have hr := (hΦ _ hR).eq
  have hs := (hΦ _ hS).eq
  ext i j
  have hr' := congrFun (congrFun hr i) j
  have hs' := congrFun (congrFun hs i) j
  simp only [map_add, Matrix.conjTranspose_add, Matrix.add_apply] at hr'
  simp only [map_smul, map_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.star_def, Complex.conj_I] at hs'
  change Φ Xᴴ i j = (Φ X)ᴴ i j
  linear_combination (norm := ring_nf) (-1/2 : ℂ) * hr' - (Complex.I/2) * hs'
  simp [Complex.I_sq]

/-- The doubled reference is flattened separately from the input coordinate. -/
def referenceDoubleEquiv (r a : ℕ) :
    (Fin r × Fin a) ⊕ (Fin r × Fin a) ≃ Fin (r+r) × Fin a :=
  (Equiv.sumProdDistrib (Fin r) (Fin r) (Fin a)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))

@[simp] theorem referenceDoubleEquiv_symm_apply (u : Fin r ⊕ Fin r) (x : Fin a) :
    (referenceDoubleEquiv r a).symm (finSumFinEquiv u, x) =
      Equiv.sumProdDistrib (Fin r) (Fin r) (Fin a) (u,x) := by
  change Equiv.sumProdDistrib (Fin r) (Fin r) (Fin a)
    (finSumFinEquiv.symm (finSumFinEquiv u), x) = _
  rw [Equiv.symm_apply_apply]

def doubledMatrix (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    Matrix (Fin (r+r) × Fin a) (Fin (r+r) × Fin a) ℂ :=
  Matrix.reindex (referenceDoubleEquiv r a) (referenceDoubleEquiv r a) (hermitianDilation X)

/-- Actual amplification preserves the off-diagonal Hermitian dilation. -/
theorem amplify_doubledMatrix (Φ : MatrixMap a b) (hΦ : IsHermiticityPreserving Φ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify Φ (r+r) (doubledMatrix X) =
      doubledMatrix (MatrixMap.amplify Φ r X) := by
  ext ⟨u,i⟩ ⟨v,j⟩
  obtain ⟨u,rfl⟩ := finSumFinEquiv.surjective u
  obtain ⟨v,rfl⟩ := finSumFinEquiv.surjective v
  rcases u with u | u <;> rcases v with v | v
  all_goals
    simp only [MatrixMap.amplify, doubledMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
      referenceDoubleEquiv_symm_apply, Equiv.sumProdDistrib_apply_left,
      Equiv.sumProdDistrib_apply_right, hermitianDilation,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  all_goals first
    | exact congrFun (congrFun Φ.map_zero i) j
    | exact congrFun (congrFun (map_conjTranspose_of_hermiticityPreserving Φ hΦ
        (fun k l => X (v,k) (u,l))) i) j

/-- A Hermiticity-preserving map's full cb trace norm is controlled by pure
input tests with input-sized reference, via an actual doubled reference. -/
theorem diamondNorm_le_pureDiamondNorm (Φ : MatrixMap a b) (hΦ : IsHermiticityPreserving Φ) :
    diamondNorm Φ ≤ pureDiamondNorm Φ := by
  by_cases htop : pureDiamondNorm Φ = ⊤
  · rw [htop]
    exact le_top
  let M := (pureDiamondNorm Φ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hpure (s : ℕ) (ψ : UnitPureInput s a) :
      traceNorm (MatrixMap.amplify Φ s (pureMatrix ψ.val)) ≤ M := by
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp (pure_traceNorm_le_pureDiamondNorm Φ ψ)
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
  have hH : (doubledMatrix X.val).IsHermitian :=
    (hermitianDilation_isHermitian X.val).submatrix _
  have h := hermitian_traceNorm_bound Φ M (hpure (r+r)) (doubledMatrix X.val) hH
  rw [amplify_doubledMatrix Φ hΦ] at h
  simp only [doubledMatrix, traceNorm_reindex, traceNorm_hermitianDilation] at h
  have hh : traceNorm (MatrixMap.amplify Φ r X.val) ≤ M * traceNorm X.val := by nlinarith
  exact hh.trans (mul_le_of_le_one_right hM X.property)

/-- The literal unhalved pure-input diamond formula stated in Section 5.2.
The reference dimension equals the channel input dimension. -/
theorem diamondNorm_eq_pureDiamondNorm (Φ : MatrixMap a b) (hΦ : IsHermiticityPreserving Φ) :
    diamondNorm Φ = ⨆ ψ : UnitPureInput a a,
      ENNReal.ofReal (traceNorm (MatrixMap.amplify Φ a (pureMatrix ψ.val))) :=
  le_antisymm (diamondNorm_le_pureDiamondNorm Φ hΦ) (pureDiamondNorm_le_diamondNorm Φ)

end QuantumChannelStein.DiamondNorm
