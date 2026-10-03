import GeneralizedChannelStein.GroupedDilation
import GeneralizedChannelStein.PostTesting
import GeneralizedChannelStein.ExtensionComparison

/-! Literal blockwise extension comparison for the locally lifted free family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelPowerReindex ChannelDilationPower UniformApproximation
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b e : ℕ}

def liftedTarget (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (n : ℕ) :
    KrausChannel (a^n) ((b*e)^n) :=
  isometryChannel (powerIsometry (AuxiliaryExtensions.outputIsometry V) n)
    (powerIsometry_isometry _ (AuxiliaryExtensions.outputIsometry_isometry V hV) n)

theorem liftedTarget_map (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (n : ℕ) :
    (liftedTarget V hV n).toLinearMap =
      ((isometryChannel (AuxiliaryExtensions.outputIsometry V)
        (AuxiliaryExtensions.outputIsometry_isometry V hV)).tensorPower n).toLinearMap :=
  (isometryChannel_power_map _ _ n).symm

theorem lifted_beta_lower (N : KrausChannel a b) (ha : 0<a)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap)
    (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ENNReal.ofReal (ExtensionComparison.factor ε)*compositeBeta (N.tensorPower n) (F n) ε ≤
      compositeBeta (liftedTarget V hV n) (liftedFamily F e n) (ExtensionComparison.tolerance ε) := by
  let T := BranchExtraction.isometryChannel (AuxiliaryExtensions.outputIsometry (powerDilation V n))
    (AuxiliaryExtensions.outputIsometry_isometry _ (powerDilation_isometry V hV n))
  have hlow := ExtensionComparison.lower_comparison (N.tensorPower n) (pow_pos ha n)
    (F n) (hF.channels n hn) (hF.compact n hn) (hF.convex n hn) (hF.nonempty n hn)
    (powerDilation V n) (powerDilation_isometry V hV n) (dilationMap_powerDilation N V hVN n)
    ε hε hε1
  have hpost := compositeBeta_postprocess_le T (coordinateChannel (groupedOutputEquiv b e n).symm)
    (AuxiliaryExtensions.extensionFamily (F n)) (liftedFamily F e n)
    (fun L hL => ungroupExtension_mem F n L hL) (ExtensionComparison.tolerance ε)
  have ht : ((coordinateChannel (groupedOutputEquiv b e n).symm).compose T).toLinearMap =
      (liftedTarget V hV n).toLinearMap :=
    (ungroup_isometry_power V hV n).trans (liftedTarget_map V hV n).symm
  exact hlow.trans (hpost.trans_eq (compositeBeta_map_congr _ _ _ ht _))

theorem reduce_liftedTarget (N : KrausChannel a b)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap) (n : ℕ) :
    ((AuxiliaryExtensions.discard b e).tensorPower n).toLinearMap.comp (liftedTarget V hV n).toLinearMap =
      (N.tensorPower n).toLinearMap := by
  rw [liftedTarget_map]
  exact reduce_powerIsometry N V hV hVN n

end GeneralizedChannelStein
