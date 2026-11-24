import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinParts

/-!
# `PartIII-b:C/rep/4/1/org/6`: `χ_yS_Nχ_o = 0` from the box case and density

Source `the November 2 reference manuscript` 5303-5306, 3902-3920, 4163-4166.
The kernel pin `IsFarMaskG` of the far part lives on the dense class of box tensors, so the
statement splits into (1) density of the stresses with box component sum, and (2) the statement
on those stresses (young output `s < 1/ν`, old source `t > 1.2/ν`, `e^δ s < t`, `S = ε^{-b} > 1/ν`
for large `n`, so the far mask equals the full separated kernel there).  Density and continuity of
`x ↦ χ_yS_N(χ_ox)` give the target; (1) and (2) are the two Props below.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Stresses with box component sum are dense** (source 3905-3912, the kernel pin is on the dense
class `NearInst.IsBoxTensor`; transport of `NearInst.Masked.BoxDenseZ` by the gain equivalence and
`zsum_zOfStr`): every stress is within any `η > 0` of `F` with `F₁ + F₂` a.e. a box tensor. -/
def StrBoxDenseAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) : Prop :=
  ∀ (x : LStr Pl K L) (η : ℝ), 0 < η → ∃ F : LStr Pl K L,
    (∃ f : Chart → Ten3, NearInst.IsBoxTensor f ∧ strSum F =ᵐ[ageμ (cOf L.ν) (-1 / 2)] f) ∧
      ‖x - F‖ < η

/-- **`χ_yS_Nχ_o = 0` on box stresses** (source 5303-5306, 3902-3920, 4163-4166): for large `n`,
`z ∈ [-1,1]` and every `F` with box component sum, `χ_y S_N(χ_oF) = 0`.  Proof: `χ_oF` has box
component sum supported at ages `t > 1.2/ν`, `χ_y` kills outputs `s ≥ 1/ν`, `e^δ < 12/11` gives
`e^δ s < t`, and `S = ε^{-b} > 1/ν`, so `IsFarMaskG` of `Sop - SNop` (`SopSubIsFarSeq`) is the full
separated kernel `sep:resolvent` (3611-3621), which `S_μ` has there. -/
def NearYoungOldBox (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, ∀ hst : D.RepairStanding dm dp, ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ F : LStr D.Pl D.K (D.level n),
      (∃ f : Chart → Ten3, NearInst.IsBoxTensor f ∧
        strSum F =ᵐ[ageμ (cOf (D.level n).ν) (-1 / 2)] f) →
      youngMul hst.chiY (SNop D.Pl D.K (D.level n) (D.mu n z) (ftOld D.Pl D.K (D.level n) F)) = 0

/-- **`χ_yS_Nχ_o = 0`** from the box case and density (continuity of the operator). -/
theorem nearYoungOldZero_of {dm dp : ℝ}
    (hd : ∀ D : SeqData, ∀ n, StrBoxDenseAt D.Pl D.K (D.level n)) (hb : NearYoungOldBox dm dp) :
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
    obtain ⟨F, hF, hxF⟩ := hd D n x η hη
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
