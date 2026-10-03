import QuantumChannelStein.SharpDataProcessing
import QuantumChannelStein.GeometricMeanCongruence

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpDivergence
open Matrix SupportedGeometricMean
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n m : ℕ}

def Feasible.transform {p : ℝ} (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    {A B : Operator n} {hB : B.PosSemidef} (X : Feasible p A B hB)
    (F : Matrix (Fin m) (Fin n) ℂ) :
    Feasible p (F * A * Fᴴ) (F * B * Fᴴ) (hB.mul_mul_conjTranspose_same F) where
  matrix := F * X.matrix * Fᴴ
  positive := X.positive.mul_mul_conjTranspose_same F
  supported := by
    simpa [krausSum] using krausSum_support ({()} : Finset Unit) (fun _ => F)
      X.matrix B X.positive hB X.supported
  dominates := by
    have hd := (sub_nonneg.mpr X.dominates).posSemidef.mul_mul_conjTranspose_same F
    have hh : F * A * Fᴴ ≤ F * mean p B hB X.matrix * Fᴴ := by
      apply sub_nonneg.mp
      simpa only [Matrix.mul_sub, Matrix.sub_mul] using hd.nonneg
    exact hh.trans (transformer p hp X.matrix B X.positive hB X.supported F)

def Feasible.cast {p : ℝ} {A B C D : Operator n} {hB : B.PosSemidef}
    (X : Feasible p A B hB) (hD : D.PosSemidef) (hAC : A = C) (hBD : B = D) :
    Feasible p C D hD := by
  subst C
  subst D
  exact X

@[simp] theorem Feasible.cast_matrix {p : ℝ} {A B C D : Operator n} {hB : B.PosSemidef}
    (X : Feasible p A B hB) (hD : D.PosSemidef) (hAC : A = C) (hBD : B = D) :
    (X.cast hD hAC hBD).matrix = X.matrix := by
  subst C
  subst D
  rfl

def Feasible.pullback {p : ℝ} (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B F G : Operator n) (hB : B.PosSemidef) (hGF : G * F = 1)
    (X : Feasible p (F * A * Fᴴ) (F * B * Fᴴ) (hB.mul_mul_conjTranspose_same F)) :
    Feasible p A B hB :=
  (X.transform hp G).cast hB (undo_congruence F G A hGF) (undo_congruence F G B hGF)

theorem Feasible.pullback_recover {p : ℝ} (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B F G : Operator n) (hB : B.PosSemidef) (hGF : G * F = 1) (hFG : F * G = 1)
    (X : Feasible p (F * A * Fᴴ) (F * B * Fᴴ) (hB.mul_mul_conjTranspose_same F)) :
    F * (X.pullback hp A B F G hB hGF).matrix * Fᴴ = X.matrix := by
  simp only [Feasible.pullback, Feasible.cast_matrix, Feasible.transform]
  exact undo_congruence G F X.matrix hFG

end QuantumChannelStein.SharpDivergence
