import QuantumChannelStein.GeometricMeanConcavity
import QuantumChannelStein.SupportDomination

/-! # Geometric-mean transformer inequality for actual finite Kraus families -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [DecidableEq J]
local instance geometricMeanKrausCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance geometricMeanKrausCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk

def krausSum (s : Finset J) (K : J → Matrix κ ι ℂ) (A : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  s.sum (fun j => K j * A * (K j)ᴴ)

theorem krausSum_positive (s : Finset J) (K : J → Matrix κ ι ℂ)
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) : (krausSum s K A).PosSemidef := by
  apply Finset.sum_induction
  · intro X Y hX hY; exact hX.add hY
  · exact Matrix.PosSemidef.zero
  · intro j hj; exact hA.mul_mul_conjTranspose_same (K j)

theorem krausSum_support (s : Finset J) (K : J → Matrix κ ι ℂ)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    LinearMap.ker (krausSum s K B).mulVecLin ≤ LinearMap.ker (krausSum s K A).mulVecLin := by
  obtain ⟨c, hc, hdom⟩ := SupportDomination.exists_domination_of_ker_le hA hB hs
  have hm := krausSum_positive s K (c • B - A) hdom
  have heq : krausSum s K (c • B - A) = c • krausSum s K B - krausSum s K A := by
    simp [krausSum, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Finset.sum_sub_distrib, Finset.smul_sum]
  rw [heq] at hm
  exact SupportDomination.ker_le_of_posSemidef_smul_sub (krausSum_positive s K A hA) hm

theorem krausSum_transformer (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (s : Finset J) (K : J → Matrix κ ι ℂ)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    krausSum s K (mean p B hB A) ≤
      mean p (krausSum s K B) (krausSum_positive s K B hB) (krausSum s K A) := by
  induction s using Finset.induction_on with
  | empty =>
    change 0 ≤ mean p 0 _ 0
    exact (mean_positive p 0 _ 0).nonneg
  | @insert j s hjs ih =>
    let hAj := hA.mul_mul_conjTranspose_same (K j)
    let hBj := hB.mul_mul_conjTranspose_same (K j)
    have hsj : LinearMap.ker (K j * B * (K j)ᴴ).mulVecLin ≤
        LinearMap.ker (K j * A * (K j)ᴴ).mulVecLin := by
      simpa [krausSum] using krausSum_support {j} K A B hA hB hs
    have hsum := superadditive p hp (K j * A * (K j)ᴴ) (K j * B * (K j)ᴴ)
      (krausSum s K A) (krausSum s K B) hAj hBj
      (krausSum_positive s K A hA) (krausSum_positive s K B hB) hsj
      (krausSum_support s K A B hA hB hs)
    have hstep := (add_le_add (transformer p hp A B hA hB hs (K j)) ih).trans hsum
    have hright := mean_congr p
      (krausSum_positive (insert j s) K B hB)
      (hBj.add (krausSum_positive s K B hB))
      (show krausSum (insert j s) K B = K j * B * (K j)ᴴ + krausSum s K B by simp [krausSum, hjs])
      (show krausSum (insert j s) K A = K j * A * (K j)ᴴ + krausSum s K A by simp [krausSum, hjs])
    rw [hright]
    simpa only [krausSum, Finset.sum_insert hjs] using hstep

/-- The actual trace-preserving Kraus action obeys the transformer inequality. -/
theorem channel_transformer {n m : ℕ} (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (Φ : KrausChannel n m) (A B : Operator n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    Φ.apply (mean p B hB A) ≤ mean p (Φ.apply B) (Φ.apply_positive hB) (Φ.apply A) :=
  krausSum_transformer p hp Finset.univ Φ.kraus A B hA hB hs

end QuantumChannelStein.SupportedGeometricMean
