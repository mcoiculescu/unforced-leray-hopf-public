import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.MollifierFamily
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.MollifyReal.Smooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.MollifyReal.Deriv
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.MollifyReal.LpConv

/-!
# `MollifyApprox` (step 1 of `HardyApprox`)

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.

`mollifyApprox_of` proves `MollifyApprox` from the three hypotheses `MollifierFamilyExists`,
`MollifySmooth`, `MollifyLp`, with `v n = mollify (ρ n) u`. The unconditional target
`mollifyApprox_holds` discharges those hypotheses by `mollifierFamilyExists_holds`
(`MollifierFamily.lean`), `mollify_contDiff` and `pdir_mollify_eq` (`MollifyReal/Smooth.lean`,
`MollifyReal/Deriv.lean`), and `mollifyLpReal_holds` (`MollifyReal/LpConv.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem mollifyApprox_of (h1 : MollifierFamilyExists) (h2 : MollifySmooth) (h3 : MollifyLp) :
    MollifyApprox := by
  intro u D hu hD hDw
  obtain ⟨ρ, hρ⟩ := h1
  have hsm : ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) :=
    fun n => ⟨(hρ n).1, (hρ n).2.1⟩
  have hS : ∀ n, ContDiff ℝ ∞ (mollify (ρ n) u) ∧
      ∀ j, pdir j (mollify (ρ n) u) = mollify (ρ n) (D j) :=
    fun n => h2 (ρ n) (hsm n).1 (hsm n).2 u D hu hD hDw
  have L6 := h3 ρ hρ 6 (by norm_num) (by norm_num) u hu
  have L2 : ∀ j, (∀ n, MemLp (mollify (ρ n) (D j)) 2 volume) ∧
      Tendsto (fun n => eLpNorm (mollify (ρ n) (D j) - D j) 2 volume) atTop (𝓝 0) :=
    fun j => h3 ρ hρ 2 (by norm_num) (by norm_num) (D j) (hD j)
  refine ⟨fun n => mollify (ρ n) u, fun n => (hS n).1, fun n => L6.1 n, ?_, L6.2, ?_⟩
  · intro n j
    rw [(hS n).2 j]
    exact (L2 j).1 n
  · intro j
    exact (L2 j).2.congr (fun n => by rw [(hS n).2 j])

/-- Step 1 of `HardyApprox`, unconditional: mollification approximates `u ∈ L⁶` with `L²`
weak gradient. -/
theorem mollifyApprox_holds : MollifyApprox :=
  mollifyApprox_of mollifierFamilyExists_holds
    (fun ρ hρ hc u D hu hD hw => ⟨mollify_contDiff hρ hc hu, fun j => pdir_mollify_eq hρ hc hu hD hw j⟩)
    mollifyLpReal_holds

end UnforcedLeray.Short.PartIIIb.Concrete
