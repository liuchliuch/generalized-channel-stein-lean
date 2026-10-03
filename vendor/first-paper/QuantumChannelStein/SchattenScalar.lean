import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Scalar root identities used in the genuine Schatten triangle proof -/
noncomputable section
namespace QuantumChannelStein.SchattenScalar

theorem root_product_sq {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q) :
    (a ^ (1 / (2 * p)) * b ^ (1 / (2 * q))) ^ 2 = a ^ (1 / p) * b ^ (1 / q) := by
  rw [mul_pow, ← Real.rpow_mul_natCast ha (1 / (2 * p)) 2,
    ← Real.rpow_mul_natCast hb (1 / (2 * q)) 2]
  simp only [Nat.cast_ofNat]
  have he₁ : (1 / (2 * p)) * (2 : ℝ) = 1 / p := by field_simp
  have he₂ : (1 / (2 * q)) * (2 : ℝ) = 1 / q := by field_simp
  rw [he₁, he₂]

theorem le_root_product_of_sq_le {z a b p q : ℝ} (hz : 0 ≤ z) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q) (h : z ^ 2 ≤ a ^ (1 / p) * b ^ (1 / q)) :
    z ≤ a ^ (1 / (2 * p)) * b ^ (1 / (2 * q)) := by
  apply (sq_le_sq₀ hz (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))).mp
  rwa [root_product_sq ha hb hp hq]

theorem sqrt_split_holder {s p q : ℝ} (hs : 0 < s) (hpq : p.HolderConjugate q) :
    Real.sqrt s = s ^ (1 / (2 * p)) * s ^ (1 / (2 * q)) := by
  have he : 1 / (2 * p) + 1 / (2 * q) = (1 / 2 : ℝ) := by
    calc
      _ = (p⁻¹ + q⁻¹) / 2 := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = _ := by rw [hpq.inv_add_inv_eq_one]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs, he]

theorem root_bound_of_domination {Q t s α : ℝ} (hQ : 0 ≤ Q) (ht : 0 ≤ t)
    (hs : 0 ≤ s) (hα : 0 < α) (h : Q ≤ t ^ (α - 1) * s ^ 2) :
    Q ^ (1 / (2 * α)) ≤ t ^ ((α - 1) / (2 * α)) * s ^ (1 / α) := by
  calc
    Q ^ (1 / (2 * α)) ≤ (t ^ (α - 1) * s ^ 2) ^ (1 / (2 * α)) :=
      Real.rpow_le_rpow hQ h (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg ht _) (sq_nonneg s),
        ← Real.rpow_mul ht, ← Real.rpow_natCast_mul hs 2]
      simp only [Nat.cast_ofNat]
      have he₁ : (α - 1) * (1 / (2 * α)) = (α - 1) / (2 * α) := by ring
      have he₂ : (2 : ℝ) * (1 / (2 * α)) = 1 / α := by field_simp
      rw [he₁, he₂]

end QuantumChannelStein.SchattenScalar
