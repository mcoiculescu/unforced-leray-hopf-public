import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11

/-!
# `PartIII-b:C/rep/11/2`: `multOpNormBound` reduced to two leaves

Source `the November 2 reference manuscript` 2706-2713, 2775-2777, 3876-3878,
5779-5782.  `multOp = (√π)⁻¹ strIso⁻¹ ∘ (G⁻¹ M_U g) ∘ velIso` with `strIso`, `velIso` isometries, so
`‖multOp‖ ≤ (√π)⁻¹ ‖G⁻¹ M_U g‖_{H→Z}` (proved here).  The two leaves are the existence of the split
multiplier at the levels of the sequence and the gained-multiplier bound, both from
`NearInst.SplitMultBound` (Targets.lean:140) and the flat-train pieces `TrainMultRestr`,
`ThinDiffMult`, `BroadMult` (NearInst/Delta/Lemmas.lean) at the regime of `RepairStanding`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- Leaf 1 (source 2703-2713, 3876-3878): at the levels of the sequence the exact split has a
bounded split multiplier `M_U : H → Z` (`NearInst.IsSplitMult`, `StressMultiplier`). -/
def NearMUExists : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
    NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb

/-- Leaf 2 (source 2706-2713, 2775-2777, 4029-4040): the gained split multiplier is
`P_ν`-bounded, `‖G⁻¹ M_U g‖_{H→Z} ≤ C ν^{-k}` (the pointwise bounds of `SplitMultBound` plus the
gain `g ≥ 1` cancelling pointwise in the age variable). -/
def NearMUGainBound : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    ‖NearInst.gainConjM (gRate D.Pl) (D.level n).ν_pos (nearMU D.Pl D.K (D.level n))‖ ≤
      C * (D.level n).ν⁻¹ ^ k

end SeqData

theorem multOp_norm_le_gainConj (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (w : LVel Pl L) :
    ‖multOp Pl K L w‖ ≤ (Real.sqrt Real.pi)⁻¹ *
      ‖NearInst.gainConjM (gRate Pl) L.ν_pos (nearMU Pl K L)‖ * ‖w‖ := by
  unfold multOp NearInst.NearOps.MG
  rw [smul_apply, norm_smul]
  simp only [ContinuousLinearMap.comp_apply, norm_inv, Real.norm_eq_abs]
  rw [abs_of_pos (Real.sqrt_pos.2 Real.pi_pos), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (le_of_eq ((NearInst.strIso (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν).symm.norm_map
    _)).trans ?_
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (le_of_eq ((NearInst.velIso (cOf L.ν) (gRate Pl) L.ν).norm_map _)) (norm_nonneg _))

namespace SeqData

theorem multOpNormBound_of (D : SeqData) (h2 : D.NearMUGainBound) : D.MultOpNormBound := by
  obtain ⟨C, k, h⟩ := h2
  refine ⟨(Real.sqrt Real.pi)⁻¹ * C, k, ?_⟩
  filter_upwards [h] with n hn w
  have hp : 0 ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
  calc ‖multOp D.Pl D.K (D.level n) w‖
      ≤ (Real.sqrt Real.pi)⁻¹ * ‖NearInst.gainConjM (gRate D.Pl) (D.level n).ν_pos
          (nearMU D.Pl D.K (D.level n))‖ * ‖w‖ := multOp_norm_le_gainConj _ _ _ w
    _ ≤ (Real.sqrt Real.pi)⁻¹ * (C * (D.level n).ν⁻¹ ^ k) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hp) (norm_nonneg _)
    _ = _ := by ring

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
