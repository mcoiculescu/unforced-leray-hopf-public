import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_3
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.Split
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.NvReal
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.CommRe

/-!
# Part II-b, task `PartII-b:G4/3/3/1` (`InletLapGen`): the off-axis chart identity

Source of record: `the November 2 reference manuscript`, lines 1651-1658, 1919-1921.
Proof: the off-axis branch of `lapPtwise_of` (`Sub/PartII-b_T09_5_5.lean`, lines 134-168), with
`lapSplit`, `lapNvReal`, `lapCommRe` and `hbS := hb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **Leaf `G4/3/3/1`**: the off-axis chart identity `InletLapGen`. -/
theorem inletLapGen : UnforcedLeray.Short.IIb.InletLapGen := by
  intro ε ν b hε hbS t y hy
  have hR0 : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨hre, him, hQs, hEs, hQre, hQim, hEre, hEim⟩ := lapCommRe ε b hbS
  obtain ⟨-, -, -, -, hQre2, hQim2, -, -⟩ := lapCommRe ε (classQ ε b) hQs
  obtain ⟨-, -, -, -, -, -, hEre2, hEim2⟩ := lapCommRe ε (classEta b) hEs
  have eQre : (fun x => reM (classQ ε b x)) = classQg ε (fun x => reM (b x)) := funext hQre
  have eQim : (fun x => imM (classQ ε b x)) = classQg ε (fun x => imM (b x)) := funext hQim
  have eEre : (fun x => reM (classEta b x)) = classEtaG (fun x => reM (b x)) := funext hEre
  have eEim : (fun x => imM (classEta b x)) = classEtaG (fun x => imM (b x)) := funext hEim
  have kre : (fun x => reM (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b)) x)) =
      ν • lapReal ε (fun x => reM (b x)) := by
    rw [lapProf_re]
    funext x
    simp only [lapReal, Pi.smul_apply]
    rw [hQre2 x, hEre2 x, eQre, eEre]
  have kim : (fun x => imM (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b)) x)) =
      ν • lapReal ε (fun x => imM (b x)) := by
    rw [lapProf_im]
    funext x
    simp only [lapReal, Pi.smul_apply]
    rw [hQim2 x, hEim2 x, eQim, eEim]
  have hL : nuLapT ν (NvC ε⁻¹ b) (t, y) = ν • lapT (NvC ε⁻¹ b) (t, y) := rfl
  rw [hL, lapSplit ε⁻¹ b hR0 hbS t y hy, lapNvReal ε⁻¹ _ hR0 hre t y hy,
    lapNvReal ε⁻¹ _ hR0 him t y hy]
  simp only [NvC]
  rw [kre, kim, inv_inv, UnforcedLeray.Axi.Nv_smul, UnforcedLeray.Axi.Nv_smul, realC_real_smul,
    realC_real_smul]
  rw [smul_add, smul_comm (ν : ℝ) Complex.I]
  simp only [Complex.coe_smul]

end UnforcedLeray.Short.IIb
