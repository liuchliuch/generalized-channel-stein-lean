import GeneralizedChannelStein.LiftedFamilies
import GeneralizedChannelStein.IsometricBenchmarks
import GeneralizedChannelStein.FreeMultipliers
import QuantumChannelStein.ChannelDilationPower

/-! Exact regrouping of repeated physical outputs and auxiliary environments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TensorPower ChannelPowerReindex ChannelDilationPower UniformApproximation BranchExtraction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b e : ℕ}

def siteEquiv (d n : ℕ) : Fin (d^n) ≃ (Fin n → Fin d) :=
  (channelIndexEquiv d n).symm.trans (indexEquiv (Fin d) n)

def outputPowerEquiv (b e n : ℕ) : Fin ((b*e)^n) ≃ Fin (b^n) × Fin (e^n) :=
  (siteEquiv (b*e) n).trans
    ((Equiv.piCongrRight (fun _ : Fin n => finProdFinEquiv.symm)).trans
      ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin b) (fun _ => Fin e)).trans
        (Equiv.prodCongr (siteEquiv b n).symm (siteEquiv e n).symm)))

theorem outputPowerEquiv_symm_site (n : ℕ) (i : Fin (b^n)) (j : Fin (e^n)) (l : Fin n) :
    siteEquiv (b*e) n ((outputPowerEquiv b e n).symm (i,j)) l =
      finProdFinEquiv (siteEquiv b n i l,siteEquiv e n j l) := by
  simp [outputPowerEquiv,Equiv.arrowProdEquivProdArrow]

def groupedOutputEquiv (b e n : ℕ) : Fin ((b*e)^n) ≃ Fin (b^n*e^n) :=
  (outputPowerEquiv b e n).trans finProdFinEquiv

theorem grouped_powerIsometry (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (n : ℕ) :
    Matrix.reindex (groupedOutputEquiv b e n) (Equiv.refl _)
      (powerIsometry (AuxiliaryExtensions.outputIsometry V) n) =
        AuxiliaryExtensions.outputIsometry (powerDilation V n) := by
  ext i j
  obtain ⟨⟨x,y⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨x,rfl⟩ := (channelIndexEquiv b n).surjective x
  obtain ⟨y,rfl⟩ := (channelIndexEquiv e n).surjective y
  obtain ⟨j,rfl⟩ := (channelIndexEquiv a n).surjective j
  simp only [powerIsometry,Matrix.reindex_apply,Matrix.submatrix_apply,
    AuxiliaryExtensions.outputIsometry,groupedOutputEquiv,Equiv.symm_trans_apply,
    Equiv.symm_apply_apply,Equiv.refl_symm,Equiv.refl_apply,
    tensorPower_apply_eq_prod,powerDilation_apply]
  apply Finset.prod_congr rfl
  intro l _
  have h := outputPowerEquiv_symm_site (b:=b) (e:=e) n
    (channelIndexEquiv b n x) (channelIndexEquiv e n y) l
  simpa only [siteEquiv,Equiv.trans_apply,Equiv.symm_apply_apply] using
    congrArg (fun z => V (finProdFinEquiv.symm z) (indexEquiv (Fin a) n j l)) h

def splitIsometry (b e : ℕ) : Matrix (Fin b × Fin e) (Fin (b*e)) ℂ :=
  Matrix.reindex finProdFinEquiv.symm (Equiv.refl _) (1:Operator (b*e))

theorem output_splitIsometry (b e : ℕ) : AuxiliaryExtensions.outputIsometry (splitIsometry b e)=1 := by
  ext i j
  change (1:Operator (b*e)) (finProdFinEquiv (finProdFinEquiv.symm i)) j=(1:Operator (b*e)) i j
  rw [Equiv.apply_symm_apply]

theorem splitIsometry_dilation (b e : ℕ) :
    dilationMap (splitIsometry b e)=(AuxiliaryExtensions.discard b e).toLinearMap := by
  ext X i j
  have h := AuxiliaryExtensions.discard_adMap (splitIsometry b e) X
  rw [output_splitIsometry,adMap_apply] at h
  simpa using congrFun (congrFun h.symm i) j

def coordinateChannel {b c : ℕ} (f : Fin b ≃ Fin c) : KrausChannel b c :=
  reindexChannel (Equiv.refl _) f (KrausChannel.identity b)

theorem coordinateChannel_apply {b c : ℕ} (f : Fin b≃Fin c) (X : Operator b) :
    (coordinateChannel f).apply X=Matrix.reindex f f X := by
  rw [coordinateChannel,reindexChannel_apply_any,KrausChannel.identity_apply]
  rfl

theorem adMap_coordinate {b c : ℕ} (f : Fin b≃Fin c) :
    adMap (Matrix.reindex f (Equiv.refl _) (1:Operator b))=(coordinateChannel f).toLinearMap := by
  ext X i j
  change adMap _ X i j=(coordinateChannel f).apply X i j
  rw [adMap_apply,coordinateChannel_apply]
  simp [Matrix.reindex_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply]

theorem powerIsometry_one (d n : ℕ) : powerIsometry (1:Operator d) n=1 := by
  rw [powerIsometry,tensorPower_one]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ _

/-- The local environment discard tensor is exactly global discard after the specified regrouping. -/
theorem discardPower_grouped (b e n : ℕ) :
    ((AuxiliaryExtensions.discard b e).tensorPower n).toLinearMap =
      (AuxiliaryExtensions.discard (b^n) (e^n)).toLinearMap.comp
        (coordinateChannel (groupedOutputEquiv b e n)).toLinearMap := by
  have hp := dilationMap_powerDilation (AuxiliaryExtensions.discard b e)
    (splitIsometry b e) (splitIsometry_dilation b e) n
  rw [←hp]
  have hj := grouped_powerIsometry (splitIsometry b e) n
  rw [output_splitIsometry,powerIsometry_one] at hj
  ext X i j
  have h := AuxiliaryExtensions.discard_adMap (powerDilation (splitIsometry b e) n) X
  rw [←hj,adMap_coordinate] at h
  exact congrFun (congrFun h.symm i) j

theorem coordinateChannel_inverse {b c : ℕ} (f : Fin b≃Fin c) (X : Operator c) :
    (coordinateChannel f).apply ((coordinateChannel f.symm).apply X)=X := by
  rw [coordinateChannel_apply,coordinateChannel_apply]
  ext i j
  simp [Matrix.reindex_apply]

theorem discardPower_ungrouped (b e n : ℕ) :
    ((AuxiliaryExtensions.discard b e).tensorPower n).toLinearMap.comp
      (coordinateChannel (groupedOutputEquiv b e n).symm).toLinearMap =
        (AuxiliaryExtensions.discard (b^n) (e^n)).toLinearMap := by
  rw [discardPower_grouped]
  ext X i j
  change (AuxiliaryExtensions.discard (b^n) (e^n)).apply
    ((coordinateChannel (groupedOutputEquiv b e n)).apply
      ((coordinateChannel (groupedOutputEquiv b e n).symm).apply X)) i j = _
  rw [coordinateChannel_inverse]
  rfl

theorem benchmark_isometry_map {a b : ℕ} (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    (isometryChannel J hJ).toLinearMap=adMap J :=
  BranchExtraction.isometryChannel_map J hJ

theorem coordinate_isometry_map {a b c : ℕ} (f : Fin b≃Fin c)
    (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) :
    ((coordinateChannel f).compose (isometryChannel J hJ)).toLinearMap =
      adMap (Matrix.reindex f (Equiv.refl _) J) := by
  rw [compose_map,benchmark_isometry_map]
  have h : (coordinateChannel f).toLinearMap.comp (adMap J) =
      ChannelTransport.reindexMap (Equiv.refl _) f (adMap J) := by
    ext X i j
    change (coordinateChannel f).apply (adMap J X) i j = _
    rw [coordinateChannel_apply]
    rfl
  rw [h,FreeMultipliers.reindexMap_adMap]

theorem ungroup_isometry_power (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (n : ℕ) :
    ((coordinateChannel (groupedOutputEquiv b e n).symm).compose
      (isometryChannel (AuxiliaryExtensions.outputIsometry (powerDilation V n))
        (AuxiliaryExtensions.outputIsometry_isometry _ (powerDilation_isometry V hV n)))).toLinearMap =
      ((isometryChannel (AuxiliaryExtensions.outputIsometry V)
        (AuxiliaryExtensions.outputIsometry_isometry V hV)).tensorPower n).toLinearMap := by
  rw [coordinate_isometry_map,isometryChannel_power_map,benchmark_isometry_map,←grouped_powerIsometry]
  congr 1
  ext i j
  simp [Matrix.reindex_apply]

theorem ungroupExtension_mem (F : AlternativeFamily a b) (n : ℕ)
    (L : KrausChannel (a^n) (b^n*e^n))
    (hL : L.toLinearMap∈AuxiliaryExtensions.extensionFamily (F n)) :
    ((coordinateChannel (groupedOutputEquiv b e n).symm).compose L).toLinearMap∈liftedFamily F e n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change ((AuxiliaryExtensions.discard b e).tensorPower n).toLinearMap.comp
    ((coordinateChannel (groupedOutputEquiv b e n).symm).compose L).toLinearMap∈F n
  rw [compose_map,←LinearMap.comp_assoc,discardPower_ungrouped]
  exact hL.2

theorem reduce_powerIsometry (N : KrausChannel a b)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1)
    (hVN : dilationMap V=N.toLinearMap) (n : ℕ) :
    ((AuxiliaryExtensions.discard b e).tensorPower n).toLinearMap.comp
      ((isometryChannel (AuxiliaryExtensions.outputIsometry V)
        (AuxiliaryExtensions.outputIsometry_isometry V hV)).tensorPower n).toLinearMap =
      (N.tensorPower n).toLinearMap := by
  rw [discardPower_grouped,LinearMap.comp_assoc,isometryChannel_power_map,←compose_map,
    coordinate_isometry_map,grouped_powerIsometry]
  rw [←dilationMap_powerDilation N V hVN n]
  ext X i j
  exact congrFun (congrFun (AuxiliaryExtensions.discard_adMap (powerDilation V n) X) i) j

end GeneralizedChannelStein
