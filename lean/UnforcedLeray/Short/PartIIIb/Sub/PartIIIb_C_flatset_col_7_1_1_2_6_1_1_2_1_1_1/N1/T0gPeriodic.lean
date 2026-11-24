import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- The planar heat commutes with a shift in the `q`-variable. -/
theorem t0g_planeHeat_shift (θ c : ℝ) (u : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ u (x.1 + c, x.2) =
      UnforcedLeray.B0224.planeHeat θ (fun z => u (z.1 + c, z.2)) x := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
    congr 1
    funext y
    have h : ((x.1 + c, x.2) : ℝ × ℝ) - UnforcedLeray.B0224.planeι y =
        ((x - UnforcedLeray.B0224.planeι y).1 + c, (x - UnforcedLeray.B0224.planeι y).2) := by
      ext <;> simp <;> ring
    rw [h]
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ),
      UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

theorem t0gPeriodic_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gPeriodic := by
  unfold T0gPeriodic
  intro c ν t Φ hΦ
  unfold QPeriodic
  intro p
  unfold t0gPsi
  dsimp only
  have key := t0g_planeHeat_shift (ν * p.1 * (Real.exp t - 1)) c
    (fun z => Φ (Real.exp t * p.1, z)) p.2
  have hfun : (fun z : ℝ × ℝ => Φ (Real.exp t * p.1, (z.1 + c, z.2))) =
      fun z => Φ (Real.exp t * p.1, z) := by
    funext z
    have := hΦ.periodic (Real.exp t * p.1, z.1, z.2)
    simpa using this
  rw [key, hfun]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
