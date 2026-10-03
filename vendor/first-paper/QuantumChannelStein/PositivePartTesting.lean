import QuantumChannelStein.TestingSDP
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-! # Spectral positive parts and optimal binary effects -/
noncomputable section
namespace QuantumChannelStein.PositivePartTesting
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spectral_positive (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hH.eigenvalues i)) : (hH.cfc f).PosSemidef := by
  apply (Matrix.PosSemidef.diagonal (fun i => ?_)).mul_mul_conjTranspose_same
    (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  simpa only [Pi.zero_apply, Function.comp_apply, RCLike.ofReal_nonneg] using hf i

theorem spectral_mul (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (f g : ℝ → ℝ) :
    hH.cfc f * hH.cfc g = hH.cfc (fun x => f x * g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, Function.comp_def]

theorem spectral_sub (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (f g : ℝ → ℝ) :
    hH.cfc f - hH.cfc g = hH.cfc (fun x => f x - g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_sub]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, Function.comp_def]

theorem spectral_one (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    hH.cfc (fun _ => 1) = 1 := by
  unfold Matrix.IsHermitian.cfc
  simp [Function.comp_def]

def positivePart (H : Matrix ι ι ℂ) (hH : H.IsHermitian) : Matrix ι ι ℂ :=
  hH.cfc (fun x => max x 0)

def positiveProjection (H : Matrix ι ι ℂ) (hH : H.IsHermitian) : Matrix ι ι ℂ :=
  hH.cfc (fun x => if 0 < x then 1 else 0)

theorem positivePart_positive (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (positivePart H hH).PosSemidef := spectral_positive H hH _ (fun _ => le_max_right _ _)

theorem positivePart_dominates (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (positivePart H hH - H).PosSemidef := by
  have hid : hH.cfc id = H := hH.spectral_theorem.symm
  have hh := spectral_positive H hH (fun x => max x 0 - x)
    (fun i => sub_nonneg.mpr (le_max_left _ _))
  have hs := spectral_sub H hH (fun x => max x 0) id
  simp only [id_eq, hid] at hs
  rw [← hs] at hh
  exact hh

theorem positiveProjection_positive (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (positiveProjection H hH).PosSemidef :=
  spectral_positive H hH _ (by intro i; split <;> norm_num)

theorem positiveProjection_complement_positive (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (1 - positiveProjection H hH).PosSemidef := by
  rw [← spectral_one H hH]
  change (hH.cfc (fun _ => 1) - hH.cfc _).PosSemidef
  rw [spectral_sub]
  exact spectral_positive H hH _ (by intro i; split <;> norm_num)

theorem mul_positiveProjection (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    H * positiveProjection H hH = positivePart H hH := by
  have hid : hH.cfc id = H := hH.spectral_theorem.symm
  change H * hH.cfc (fun x => if 0 < x then 1 else 0) = hH.cfc (fun x => max x 0)
  calc
    H * hH.cfc (fun x => if 0 < x then 1 else 0) =
        hH.cfc (fun x => x * (if 0 < x then 1 else 0)) := by
      simpa only [id_eq, hid] using spectral_mul H hH id (fun x => if 0 < x then 1 else 0)
    _ = _ := by
      congr 1
      funext x
      split
      · rename_i hx
        simp [max_eq_left hx.le]
      · rename_i hx
        simp [max_eq_right (le_of_not_gt hx)]

theorem trace_effect_le_positivePart (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (Q : Matrix ι ι ℂ) (hQ : Q.PosSemidef) (hcQ : (1 - Q).PosSemidef) :
    (H * Q).trace.re ≤ (positivePart H hH).trace.re := by
  have h₁ := TestingSDP.trace_pairing_nonnegative (positivePart_dominates H hH) hQ
  have h₂ := TestingSDP.trace_pairing_nonnegative (positivePart_positive H hH) hcQ
  have hr₁ := (Complex.nonneg_iff.mp h₁).1
  have hr₂ := (Complex.nonneg_iff.mp h₂).1
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
    Complex.sub_re] at hr₁ hr₂
  linarith
end QuantumChannelStein.PositivePartTesting
