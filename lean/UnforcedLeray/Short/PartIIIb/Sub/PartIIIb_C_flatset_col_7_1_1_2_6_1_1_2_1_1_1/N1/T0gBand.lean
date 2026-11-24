import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

theorem t0g_planeHeat_zero (θ : ℝ) :
    UnforcedLeray.B0224.planeHeat θ (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by
  by_cases hθ : 0 < θ
  · funext x
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    simp
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

theorem t0gBand_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gBand := by
  unfold T0gBand
  intro c ν t Φ hΦ
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  have hinv : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  refine ⟨s0 * Real.exp (-t), s1 * Real.exp (-t), by positivity, ?_⟩
  intro p hp
  by_contra hmem
  apply hp
  unfold t0gPsi
  have hu : (fun z : ℝ × ℝ => Φ (Real.exp t * p.1, z)) = fun _ => 0 := by
    funext z
    by_contra hz
    apply hmem
    obtain ⟨h1, h2⟩ := (hb _ hz).1
    have hp1 : p.1 = Real.exp (-t) * (Real.exp t * p.1) := by
      rw [← mul_assoc, hinv, one_mul]
    constructor
    · rw [hp1]
      nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]
    · rw [hp1]
      nlinarith [mul_le_mul_of_nonneg_left h2 hpos.le]
  rw [hu, t0g_planeHeat_zero]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
