import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Bridge
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ

/-!
# `strBoxTrunc` (source 3593-3594, 3905-3912, 2697-2700): box truncation of a stress.

Route (as `boxDenseZ`): the window `A_k = bdWin f f k` for the source `f`; the components of `F`
are cut by `A_k` (indicator in `L²` of each gain measure), `Fn k` is the cut stress. Dominated
convergence (`bd_tendsto_cut`) on each of the two gain measures gives `Fn k → F`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `L²` distance of a cut: `‖u - 1_A u‖ = ‖1_{Aᶜ} u‖`. -/
theorem strBox_norm_cut {μ : Measure Chart} (u : Lp Ten3 2 μ) (A : Set Chart)
    (hind : MemLp (A.indicator (⇑u)) 2 μ) :
    ‖u - hind.toLp _‖ = (eLpNorm (Aᶜ.indicator (⇑u)) 2 μ).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub u (hind.toLp _), hind.coeFn_toLp] with p h1 h2
  rw [h1, Pi.sub_apply, h2]
  by_cases hpA : p ∈ A
  · simp [hpA]
  · simp [hpA]

theorem strBoxTrunc : StrBoxTrunc := by
  intro c mZ ρb γ ν hc hρ hν F f hf hsum
  set g1 : Chart → Ten3 := ⇑(F.fst) with hg1
  set g2 : Chart → Ten3 := ⇑(F.snd) with hg2
  have m1 : Measurable g1 := (Lp.stronglyMeasurable F.fst).measurable
  have m2 : Measurable g2 := (Lp.stronglyMeasurable F.snd).measurable
  have hl1 : MemLp g1 2 (gainZ1Measure c mZ γ ν) := Lp.memLp F.fst
  have hl2 : MemLp g2 2 (gainHTMeasure c ρb γ ν) := Lp.memLp F.snd
  have hfilt1 : ae (gainZ1Measure c mZ γ ν) = ae (ageμ c (-1 / 2)) :=
    (ae_gainZ1Measure c mZ γ ν).trans (ae_z1Measure c mZ)
  have hfilt2 : ae (gainHTMeasure c ρb γ ν) = ae (ageμ c (-1 / 2)) :=
    (ae_gainHTMeasure c ρb γ ν).trans (ae_htRhoMeasure hρ)
  have pos : ∀ᵐ p ∂(ageμ c (-1 / 2)), 0 < p.1 := UnforcedLeray.Short.IIIa.ae_pos_ageμ c _
  have cov1 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ∃ n, p ∈ bdWin f f n := by
    rw [hfilt1]; filter_upwards [pos] with p hp using bdWin_cover f f hp
  have cov2 : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), ∃ n, p ∈ bdWin f f n := by
    rw [hfilt2]; filter_upwards [pos] with p hp using bdWin_cover f f hp
  have T1 := bd_tendsto_cut (μ := gainZ1Measure c mZ γ ν) m1 hl1 (bdWin f f)
    (fun n => bdWin_meas hf hf n) (bdWin_mono f f) cov1
  have T2 := bd_tendsto_cut (μ := gainHTMeasure c ρb γ ν) m2 hl2 (bdWin f f)
    (fun n => bdWin_meas hf hf n) (bdWin_mono f f) cov2
  refine ⟨bdWin f f, fun k => WithLp.toLp 1
    (((hl1.indicator (bdWin_meas hf hf k))).toLp _, ((hl2.indicator (bdWin_meas hf hf k))).toLp _),
    ?_, ?_, ?_⟩
  · intro k
    refine ⟨hf.indicator (bdWin_meas hf hf k), ⟨(k : ℝ), fun p => ?_⟩,
      ⟨1 / ((k : ℝ) + 1), k, k, by positivity, fun p hp => ?_⟩⟩
    · by_cases hpA : p ∈ bdWin f f k
      · rw [Set.indicator_of_mem hpA]
        exact hpA.2.2.2.1
      · rw [Set.indicator_of_notMem hpA, norm_zero]
        positivity
    · by_cases hpA : p ∈ bdWin f f k
      · exact ⟨hpA.1, hpA.2.1, hpA.2.2.1⟩
      · exact absurd (by simp [Set.indicator_of_notMem hpA]) hp
  · intro k
    have e1 : ∀ᵐ p ∂(ageμ c (-1 / 2)),
        ((hl1.indicator (bdWin_meas hf hf k)).toLp _ : Chart → Ten3) p
          = (bdWin f f k).indicator g1 p := by
      rw [← hfilt1]; exact (hl1.indicator (bdWin_meas hf hf k)).coeFn_toLp
    have e2 : ∀ᵐ p ∂(ageμ c (-1 / 2)),
        ((hl2.indicator (bdWin_meas hf hf k)).toLp _ : Chart → Ten3) p
          = (bdWin f f k).indicator g2 p := by
      rw [← hfilt2]; exact (hl2.indicator (bdWin_meas hf hf k)).coeFn_toLp
    filter_upwards [hsum, e1, e2] with p hp h1 h2
    show ((hl1.indicator (bdWin_meas hf hf k)).toLp _ : Chart → Ten3) p
        + ((hl2.indicator (bdWin_meas hf hf k)).toLp _ : Chart → Ten3) p = _
    rw [h1, h2]
    have hp' : g1 p + g2 p = f p := hp
    by_cases hpA : p ∈ bdWin f f k
    · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpA, Set.indicator_of_mem hpA, hp']
    · rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpA,
        add_zero]
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hT := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp T1).add
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp T2)
    rw [ENNReal.toReal_zero, add_zero] at hT
    refine hT.congr fun k => ?_
    have hn : ‖WithLp.toLp 1 ((hl1.indicator (bdWin_meas hf hf k)).toLp _,
        (hl2.indicator (bdWin_meas hf hf k)).toLp _) - F‖
        = ‖(hl1.indicator (bdWin_meas hf hf k)).toLp _ - F.fst‖
          + ‖(hl2.indicator (bdWin_meas hf hf k)).toLp _ - F.snd‖ := by
      rw [WithLp.prod_norm_eq_of_L1]
      rfl
    rw [hn, norm_sub_rev _ F.fst, norm_sub_rev _ F.snd]
    show ENNReal.toReal (eLpNorm ((bdWin f f k)ᶜ.indicator g1) 2 (gainZ1Measure c mZ γ ν))
        + ENNReal.toReal (eLpNorm ((bdWin f f k)ᶜ.indicator g2) 2 (gainHTMeasure c ρb γ ν)) = _
    rw [strBox_norm_cut F.fst _ (hl1.indicator (bdWin_meas hf hf k)),
      strBox_norm_cut F.snd _ (hl2.indicator (bdWin_meas hf hf k))]

end UnforcedLeray.Short.PartIIIb.Concrete
