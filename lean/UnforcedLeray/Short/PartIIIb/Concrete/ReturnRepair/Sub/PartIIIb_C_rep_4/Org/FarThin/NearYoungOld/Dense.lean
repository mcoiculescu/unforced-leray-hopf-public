import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld.Of
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.FarMaskAgree
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level

/-!
# `StrBoxDenseAt` from `boxDenseZ` (source 3905-3912), transported by the gain equivalence

The transport: `Ψ = strIso⁻¹ ∘ gainEquiv⁻¹ : Z → StrG` is a bounded linear map with
`Ψ (gainEquiv (strIso x)) = x`, so `x - Ψ y' = Ψ (y - y')` and `‖x - Ψ y'‖ ≤ ‖Ψ‖ ‖y - y'‖`.
The box property of `Ψ y'` is `strSum_strOfZ_ae`.  The positivity hypotheses `0 ≤ m_Z` and
`0 < C₀` (hence `0 < ρ_b`) are those of `RepairStanding` (`mZ_gt`, `C0_pos`); they are taken as
arguments here, since the target `strBoxDenseAt` carries no standing hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open UnforcedLeray.Short.PartIIIb.NearInst

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem strBoxDenseAt_of {Pl : UnforcedLeray.Blueprint.Planar.PlanarData} {K : ReturnConsts}
    {L : ReturnLevel} (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) : StrBoxDenseAt Pl K L := by
  intro x η hη
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hρ : 0 < L.ρb Pl K := inv_rhoB_pos hC0
  have hν : 0 < L.ν := L.ν_pos
  set Ψ : Zsp (cOf L.ν) K.mZ (L.ρb Pl K) →L[ℝ] StrG (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν :=
    ((strIso (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((gainEquiv (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) hν).symm.toContinuousLinearMap) with hΨ
  set y := gainEquiv (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) hν (strIso (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν x) with hy
  have hxΨ : Ψ y = x := by
    simp [hΨ, hy]
  set η' := η / (‖Ψ‖ + 1) with hη'
  have hη'pos : 0 < η' := by positivity
  obtain ⟨y', ⟨f, hf, hzf⟩, hyy'⟩ :=
    NearInst.Masked.boxDenseZ (cOf L.ν) K.mZ (L.ρb Pl K) hc hmZ hρ y η' hη'pos
  refine ⟨Ψ y', ⟨f, hf, ?_⟩, ?_⟩
  · filter_upwards [NearInst.strSum_strOfZ_ae hρ hν y', hzf] with p a b
    exact a.trans b
  · have hsub : x - Ψ y' = Ψ (y - y') := by rw [map_sub, hxΨ]
    rw [hsub]
    calc ‖Ψ (y - y')‖ ≤ ‖Ψ‖ * ‖y - y'‖ := Ψ.le_opNorm _
      _ ≤ ‖Ψ‖ * η' := mul_le_mul_of_nonneg_left hyy'.le (norm_nonneg _)
      _ < η := by
        rw [hη', ← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg Ψ]

/-- Density for the sequence under the repair standing hypotheses (`m_Z > 3/2`, `C₀ > 0`).  The
unconditional statement over free `ReturnConsts` is not provable (`BoxDenseZ` needs `0 ≤ m_Z`,
`0 < ρ_b`), so the standing hypotheses are supplied. -/
theorem strBoxDenseAt_standing {dm dp : ℝ} (D : SeqData) (hst : D.RepairStanding dm dp) (n : ℕ) :
    StrBoxDenseAt D.Pl D.K (D.level n) :=
  strBoxDenseAt_of (by linarith [hst.mZ_gt]) hst.C0_pos

/-- `nearYoungOldZero_of` with the density hypothesis discharged under `RepairStanding`. -/
theorem nearYoungOldZero_of_box {dm dp : ℝ} (hb : NearYoungOldBox dm dp) :
    NearYoungOldZero dm dp := by
  intro D hst
  filter_upwards [hb D hst] with n hn z hz x
  set A : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n) :=
    (youngMul hst.chiY).comp ((SNop D.Pl D.K (D.level n) (D.mu n z)).comp
      (ftOld D.Pl D.K (D.level n))) with hA
  have h0 : ∀ F, (∃ f : Chart → Ten3, NearInst.IsBoxTensor f ∧
        strSum F =ᵐ[ageμ (cOf (D.level n).ν) (-1 / 2)] f) → A F = 0 := fun F hF => hn z hz F hF
  change A x = 0
  have hle : ∀ η, 0 < η → ‖A x‖ ≤ ‖A‖ * η := by
    intro η hη
    obtain ⟨F, hF, hxF⟩ := strBoxDenseAt_standing D hst n x η hη
    have : A x = A (x - F) := by rw [map_sub, h0 F hF, sub_zero]
    rw [this]
    calc ‖A (x - F)‖ ≤ ‖A‖ * ‖x - F‖ := A.le_opNorm _
      _ ≤ ‖A‖ * η := mul_le_mul_of_nonneg_left hxF.le (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖A x‖ := norm_pos_iff.2 hne
  have hA0 : 0 < ‖A‖ + 1 := by positivity
  have := hle (‖A x‖ / (2 * (‖A‖ + 1))) (by positivity)
  have h2 : ‖A‖ * (‖A x‖ / (2 * (‖A‖ + 1))) < ‖A x‖ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg A]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
