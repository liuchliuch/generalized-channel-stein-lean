import GeneralizedChannelStein.SingularInputReduction

/-! Input-sized reference stabilization for every complex-linear map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy DiamondNorm TraceNorm
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

def stabilizedDiamondNorm (Φ : MatrixMap a b) : ENNReal :=
  ⨆ X : {X : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ // TraceNorm.traceNorm X≤1},
    ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ a X.val))

theorem cross_traceNorm_le_stabilized (Φ : MatrixMap a b) {r : ℕ} (ψ ζ : UnitPureInput r a) :
    ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ r (crossMatrix ψ.val ζ.val)))≤stabilizedDiamondNorm Φ := by
  obtain ⟨φ,χ,h⟩ := cross_reference_traceNorm_le Φ ψ ζ
  apply (ENNReal.ofReal_le_ofReal h).trans
  exact le_iSup_of_le ⟨crossMatrix φ.val χ.val,(traceNorm_crossMatrix _ _ φ.property χ.property).le⟩ le_rfl

/-- The full cb trace norm needs only reference dimension equal to the input dimension.
No Hermiticity-preserving, positivity, or channel premise is present. -/
theorem diamondNorm_stabilizes (Φ : MatrixMap a b) : diamondNorm Φ=stabilizedDiamondNorm Φ := by
  apply le_antisymm
  · by_cases ht : stabilizedDiamondNorm Φ=⊤
    · rw [ht]; exact le_top
    let M := (stabilizedDiamondNorm Φ).toReal
    have hM : 0≤M := ENNReal.toReal_nonneg
    have hp (r : ℕ) (ψ ζ : UnitPureInput r a) :
        TraceNorm.traceNorm (MatrixMap.amplify Φ r (crossMatrix ψ.val ζ.val))≤M :=
      (ENNReal.ofReal_le_iff_le_toReal ht).mp (cross_traceNorm_le_stabilized Φ ψ ζ)
    apply iSup_le
    intro r
    apply iSup_le
    intro X
    have h := SingularInputReduction.arbitrary_traceNorm_bound Φ M (hp r) X.val
    have hb : TraceNorm.traceNorm (MatrixMap.amplify Φ r X.val)≤M :=
      h.trans (mul_le_of_le_one_right hM X.property)
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_toReal ht)
  · exact le_iSup_of_le a le_rfl

/-- The nonzero-input quotient definition written in the paper. -/
def quotientDiamondNorm (Φ : MatrixMap a b) : ENNReal :=
  ⨆ r : ℕ, ⨆ X : {X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ // X≠0},
    ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ r X.val)/TraceNorm.traceNorm X.val)

theorem diamondNorm_eq_quotient (Φ : MatrixMap a b) : diamondNorm Φ=quotientDiamondNorm Φ := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro X
    by_cases hX : X.val=0
    · have hz : MatrixMap.amplify Φ r X.val=0 := by
        rw [hX]
        exact (amplifyLinear Φ r).map_zero
      simp [hz,TraceNorm.traceNorm_zero]
    · have ht : 0<TraceNorm.traceNorm X.val := lt_of_le_of_ne (TraceNorm.traceNorm_nonneg _)
        (Ne.symm (by intro hz; exact hX ((Matrix.traceNorm_zero_iff X.val).mp hz)))
      have hb : TraceNorm.traceNorm (MatrixMap.amplify Φ r X.val)≤
          TraceNorm.traceNorm (MatrixMap.amplify Φ r X.val)/TraceNorm.traceNorm X.val :=
        (le_div_iff₀ ht).mpr (mul_le_of_le_one_right (TraceNorm.traceNorm_nonneg _) X.property)
      exact (ENNReal.ofReal_le_ofReal hb).trans (le_iSup_of_le r (le_iSup_of_le ⟨X.val,hX⟩ le_rfl))
  · apply iSup_le
    intro r
    apply iSup_le
    intro X
    have ht : 0<TraceNorm.traceNorm X.val := lt_of_le_of_ne (TraceNorm.traceNorm_nonneg _)
      (Ne.symm (by intro hz; exact X.property ((Matrix.traceNorm_zero_iff X.val).mp hz)))
    let Y := Complex.ofReal ((TraceNorm.traceNorm X.val)⁻¹) • X.val
    have hY : TraceNorm.traceNorm Y≤1 := by
      change TraceNorm.traceNorm ((TraceNorm.traceNorm X.val)⁻¹ • X.val)≤1
      rw [TraceNorm.traceNorm_real_smul,abs_of_pos (inv_pos.mpr ht),inv_mul_cancel₀ ht.ne']
    have hy : MatrixMap.amplify Φ r Y=Complex.ofReal ((TraceNorm.traceNorm X.val)⁻¹) • MatrixMap.amplify Φ r X.val :=
      (amplifyLinear Φ r).map_smul _ _
    have hbound : ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ r Y))≤diamondNorm Φ :=
      le_iSup_of_le r (le_iSup_of_le ⟨Y,hY⟩ le_rfl)
    rw [hy,TraceNorm.traceNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)] at hbound
    simpa only [div_eq_mul_inv,mul_comm] using hbound

end GeneralizedChannelStein
