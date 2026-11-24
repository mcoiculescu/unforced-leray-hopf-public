import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth

/-!
# Measurability of the coefficient-change density on the sequence (task `PartIII-b:C/rep/8/2/pres/4/1`)

Source `the November 2 reference manuscript`
1217-1222 (`IsExactProfile` smoothness), 5287-5289.

This file is downstream of `Sub/PartIII-b_C_rep_8_2_pres_4_1.lean`: the raw smoothness
`rawU_contDiffOn_offAxis_of` lives in `_4_1_3`, which imports `_4_1`, so the theorem cannot be
placed in `_4_1` itself without an import cycle.

`V τ y = raw τ y + Σ_i coord z i • inlet i τ y` on an actual level (`IsActualLevel.split`), so
`V` is `C²` off the axis from the raw lift (`rawU_contDiffOn_offAxis_of`, with the stream `C^∞` by
`SeqData.train_stream_smooth`) and the inlet columns (`IIb.inletJointSmooth`, eventually in `n`
since `retNu → 0`).
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1`.** The coefficient-change density is measurable on the
sequence, from the standing hypotheses of the repair. -/
theorem coefChgMeas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : CoefChgMeas D := by
  obtain ⟨ν₀, hν₀, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue D.Pl.mode
    D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  have hInlet : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 2,
      ContDiff ℝ ∞ (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) := by
    filter_upwards [hst.actual, hν] with n hn hνn
    exact fun i => hS ((D.level n).params D.Pl) _ hn.regime hνn.le rfl rfl i
  have hRaw : ∀ᶠ n : ℕ in atTop,
      ContDiffOn ℝ 2 (fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2) offAxis := by
    filter_upwards [hst.actual] with n _hn
    exact rawU_contDiffOn_offAxis_of ((D.level n).params D.Pl) (D.level n).ε_pos
      ((D.level n).train_stream_smooth.of_le (by norm_num))
  have hV : ∀ᶠ n : ℕ in atTop,
      ContDiffOn ℝ 2 (fun x : ℝ × Space => (D.level n).V x.1 x.2) offAxis := by
    filter_upwards [hst.actual, hRaw, hInlet] with n hn hr hi
    obtain ⟨z, -, hVz, -, -⟩ := hn.split.state
    have he : (fun x : ℝ × Space => (D.level n).V x.1 x.2) =
        fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2 +
          ∑ i : Fin 2, ((D.level n).params D.Pl).coord z i •
            ((D.level n).params D.Pl).inlet i x.1 x.2 := by
      funext x
      exact hVz x.1 x.2
    rw [he]
    refine hr.add ?_
    have hi2 : ∀ i : Fin 2, ContDiffOn ℝ 2
        (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) offAxis :=
      fun i => ((hi i).of_le (by norm_num)).contDiffOn
    refine ContDiffOn.sum fun i _ => ?_
    exact (hi2 i).const_smul _
  exact coefChgMeas_of D hst hV

end UnforcedLeray.Short.PartIIIb.Concrete
