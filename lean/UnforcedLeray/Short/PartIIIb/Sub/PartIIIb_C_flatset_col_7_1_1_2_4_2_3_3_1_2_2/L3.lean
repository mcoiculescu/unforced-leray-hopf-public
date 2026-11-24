import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_2

/-!
# `OfCylSmoothSub` (source 1650-1656, 1684-1689): additivity of `W.ofCylSmooth` for `Vec2`

Route as in `TrainB.ofCylSmooth_sub_eq` (`Lib/TrainB/WeakEmbedding.lean:491`): both sides are
elements of `W`, equal under `W.value_injective`, and `W.value` is linear.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

theorem ofCylSmoothSub_proof : OfCylSmoothSub := by
  intro c hc k f g hf hg hfg
  apply UnforcedLeray.Sob.W.value_injective
  rw [map_sub]
  apply Lp.ext
  filter_upwards [UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
      hc (fun x => f x - g x) hfg,
    UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
      hc f hf,
    UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
      hc g hg,
    Lp.coeFn_sub (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 k 2
      (UnforcedLeray.Sob.W.ofCylSmooth (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2) hc f hf))
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 k 2
      (UnforcedLeray.Sob.W.ofCylSmooth (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2) hc g hg))] with z h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.sub_apply]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
