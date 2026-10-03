import GeneralizedChannelStein.CoherentMarginal
import GeneralizedChannelStein.LocalApproximationFinite

/-! F5-preserving block marginal and its exact coherent retained branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.DiscardedBranch
open QuantumChannelStein Matrix ChannelPowerReindex ChannelTransport PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d : ℕ}

theorem powerIsometry_add (J : Matrix (Fin d) (Fin a) ℂ) (k m : ℕ) :
    Matrix.reindex (channelAddEquiv d k m).symm (channelAddEquiv a k m).symm (powerIsometry J (k+m)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (powerIsometry J k ⊗ₖ powerIsometry J m) := by
  ext i j
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  have h := TensorPower.tensorPower_add_reindex J k m
  rw [powerIsometry,h.symm]
  simp [Matrix.reindex_apply,channelAddEquiv,channelConcatEquiv,powerIsometry,Matrix.kroneckerMap_apply]

theorem weighted_finite_eq_map (τ : State a) (k m : ℕ) (W : Operator (a^(k+m))) :
    finiteWeightedExpectation τ k m W=weightedDiscardMap (a^k) (statePower τ m)
      (Matrix.reindex (channelAddEquiv a k m).symm (channelAddEquiv a k m).symm W) := by
  rw [finiteWeightedExpectation,weightedDiscard_eq_map]
  congr 1
  ext i j
  change W ((channelAddEquiv a k m) (finProdFinEquiv (finProdFinEquiv.symm i)))
    ((channelAddEquiv a k m) (finProdFinEquiv (finProdFinEquiv.symm j))) = _
  simp only [Equiv.apply_symm_apply]
  rfl

theorem exists_free_coherent_branch (F : AlternativeFamily a d) (τ : State a)
    (hτ : QuantitativeAt F τ) (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (k m : ℕ) (hk : 0<k) (M : KrausChannel (a^(k+m)) (d^(k+m)))
    (hM : M.toLinearMap∈F (k+m)) (V : Matrix (Fin (d^(k+m))) (Fin (a^(k+m))) ℂ)
    (hV : ‖V‖≤1) (p : ℝ) (hp : 0≤p)
    (hdom : MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap V) M.toLinearMap) :
    ∃ Z : Matrix (Fin (d^k)) (Fin (a^k)) ℂ, ∃ Mk : KrausChannel (a^k) (d^k),
      Mk.toLinearMap∈F k ∧ ‖Z‖≤1 ∧
      MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap Z) Mk.toLinearMap ∧
      (powerIsometry J k)ᴴ*Z=finiteWeightedExpectation τ k m ((powerIsometry J (k+m))ᴴ*V) := by
  let ea := (channelAddEquiv a k m).symm
  let ed := (channelAddEquiv d k m).symm
  let Ms := reindexChannel ea ed M
  let Vs := Matrix.reindex ed ea V
  have hd : MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap Vs) Ms.toLinearMap := by
    have h := reindexMap_cpLe ea ed _ _ hdom
    simpa only [reindexMap_smul,FreeMultipliers.reindexMap_adMap,← reindexChannel_map] using h
  obtain ⟨Z,hZ,hD,hE⟩ := CoherentMarginal.exists_branch (statePower τ m) (powerIsometry J m)
    (powerIsometry_isometry J hJ m) Vs Ms p hp hd
  let Mk := iteratedMarginal k τ m M
  have hMk : Mk.toLinearMap=(BulkMarginal.pairMarginal (statePower τ m) Ms).toLinearMap :=
    BulkMarginal.iteratedMarginal_eq_bulk k m τ M
  refine ⟨Z,Mk,hτ.iterated_marginal_closed k m hk M hM,?_,?_,?_⟩
  · exact hZ.trans ((TensorPower.norm_reindex _ _ _).trans_le hV)
  · rwa [hMk]
  · rw [hE,weighted_finite_eq_map]
    congr 1
    rw [← powerIsometry_add J k m,Matrix.conjTranspose_reindex]
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ ea ed ea _ _

theorem weighted_overlap_lower (τ : State a) (k m : ℕ) (W : Operator (a^(k+m)))
    (c : ℝ) (hW : (BranchExtraction.realPart W-c•1).PosSemidef) :
    (BranchExtraction.realPart (finiteWeightedExpectation τ k m W)-c•1).PosSemidef := by
  rw [weighted_finite_eq_map]
  apply heisenbergMap_realPart_lower
  have h := hW.submatrix (channelAddEquiv a k m)
  convert h using 1
  ext i j
  simp [BranchExtraction.realPart,Matrix.reindex_apply,Matrix.conjTranspose_apply,Matrix.one_apply]

end GeneralizedChannelStein.DiscardedBranch
