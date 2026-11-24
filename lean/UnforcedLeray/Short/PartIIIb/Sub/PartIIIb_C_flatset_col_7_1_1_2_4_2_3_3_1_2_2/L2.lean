import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_2

/-!
# `SmoothSeqH` (source 1650-1656, 1684-1689): smooth approximants in `H^k`

Route as in `TrainB.exists_smoothH2_sequence` (`Lib/TrainB/WeakEmbedding.lean:531`):
`Sob.W.exists_seq_cylSmooth` gives smooth representatives, and `W.value_injective` upgrades
the value identity to the equality `W.ofCylSmooth (u n) = y n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

theorem smoothSeqH_proof : SmoothSeqH := by
  intro c hc k y
  obtain ⟨v, hv, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := k) (p := 2) hc (by norm_num) y
  choose u hu hrep using hv
  refine ⟨u, hu, ?_⟩
  have heq : (fun n => UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)) = v := by
    funext n
    apply UnforcedLeray.Sob.W.value_injective
    apply Lp.ext
    have hrepW := (UnforcedLeray.Sob.ae_eq_wμ_iff (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mpr (hrep n)
    filter_upwards [hrepW, UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
      hc (u n) (hu n)] with z hz₁ hz₂
    exact hz₂.trans hz₁.symm
  rw [heq]
  exact hlim

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
