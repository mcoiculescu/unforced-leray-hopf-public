import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_1

/-!
# `CgiPerLimit`: completeness of `L^r(cylMeas c)` and the periodic modification (SP 1932-1935)

The `L^r(cylMeas c)`-limit `G₀` of the sequence is taken in `Lp`; its representative `G₀m`
is replaced by `G x = G₀m (cgiPer c x)`, where `cgiPer` folds the `q`-coordinate into the cell
`[-c/2, c/2)`. Since `cylMeas c` lives on the cell, `G = G₀` `cylMeas c`-a.e., and `G` is
everywhere `qShift c`-periodic.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- Folds the `q`-coordinate into `[-c/2, c/2)` by subtracting multiples of `c`. -/
def cgiPer (c : ℝ) (x : Coord) : Coord :=
  (x.1, (x.2.1 - c * ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ), x.2.2))

theorem cgiPer_measurable (c : ℝ) : Measurable (cgiPer c) := by
  unfold cgiPer
  fun_prop

theorem cgiPer_qShift (c : ℝ) (hc : 0 < c) (x : Coord) : cgiPer c (qShift c x) = cgiPer c x := by
  have h1 : (x.2.1 + c + c / 2) / c = (x.2.1 + c / 2) / c + 1 := by
    rw [div_add_one hc.ne']; congr 1; ring
  unfold cgiPer
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  show x.2.1 + c - c * ((⌊(x.2.1 + c + c / 2) / c⌋ : ℤ) : ℝ) =
    x.2.1 - c * ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ)
  rw [h1, Int.floor_add_one]
  push_cast
  ring

theorem cgiPer_mem (c : ℝ) (hc : 0 < c) (x : Coord) (hq : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    cgiPer c x = x := by
  have h0 : ⌊(x.2.1 + c / 2) / c⌋ = 0 :=
    Int.floor_eq_zero_iff.2 ⟨div_nonneg (by linarith [hq.1]) hc.le,
      (div_lt_one hc).2 (by linarith [hq.2])⟩
  unfold cgiPer
  simp [h0]

theorem cylMeas_q_mem_ae (c : ℝ) (hc : 0 < c) :
    ∀ᵐ x ∂(cylMeas c), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
  have hcell : MeasurableSet (UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hNull : cylMeas c {x : Coord | ¬ (x.2.1 ∈ Ico (-c / 2) (c / 2))} = 0 := by
    have hset : {x : Coord | ¬ (x.2.1 ∈ Ico (-c / 2) (c / 2))} =
        univ ×ˢ {p : ℝ × ℝ | ¬ (p.1 ∈ Ico (-c / 2) (c / 2))} := by
      ext x; simp
    have h2 : UnforcedLeray.Cyl.avgμ c {p : ℝ × ℝ | ¬ (p.1 ∈ Ico (-c / 2) (c / 2))} = 0 := by
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      rw [Measure.smul_apply, Measure.restrict_apply' hcell]
      have hem : {p : ℝ × ℝ | ¬ (p.1 ∈ Ico (-c / 2) (c / 2))} ∩ UnforcedLeray.Cyl.cell c = ∅ := by
        ext p
        simp [UnforcedLeray.Cyl.cell]
      rw [hem, measure_empty, smul_zero]
    rw [cylMeas, hset, Measure.prod_prod, h2, mul_zero]
  exact ae_iff.2 hNull

theorem cgiPerLimit_proof : UnforcedLeray.Short.IIb.CgiPerLimit := by
  intro r hr c hc g hgc hgfin hper hcau
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨hp⟩
  have hmem : ∀ n, MemLp (g n) (ENNReal.ofReal r) (cylMeas c) :=
    fun n => ⟨(hgc n).aestronglyMeasurable, hgfin n⟩
  have hcauchy : CauchySeq (fun n => (hmem n).toLp (g n)) := by
    refine EMetric.cauchySeq_iff.2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [MeasureTheory.Lp.edist_toLp_toLp (g m) (g n) (hmem m) (hmem n)]
    exact hN n m hn hm
  obtain ⟨G0, hG0⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hae : ∀ n, (⇑((hmem n).toLp (g n)) - ⇑G0 : Coord → ℂ) =ᵐ[cylMeas c]
      (fun x => g n x - G0 x) := fun n => by
    filter_upwards [(hmem n).coeFn_toLp] with x hx
    simp [hx]
  have hconv : Tendsto (fun n => eLpNorm (fun x => g n x - G0 x) (ENNReal.ofReal r) (cylMeas c))
      atTop (𝓝 0) := by
    have h := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hG0
    exact Tendsto.congr (fun n => eLpNorm_congr_ae (hae n)) h
  obtain ⟨G0m, hG0m_sm, hG0m_ae⟩ : ∃ H : Coord → ℂ, StronglyMeasurable H ∧
      (⇑G0) =ᵐ[cylMeas c] H :=
    ⟨(Lp.aestronglyMeasurable G0).mk _, (Lp.aestronglyMeasurable G0).stronglyMeasurable_mk,
      (Lp.aestronglyMeasurable G0).ae_eq_mk⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Coord → ℂ, ∀ x, G x = G0m (cgiPer c x) :=
    ⟨fun x => G0m (cgiPer c x), fun x => rfl⟩
  have hGmeas : Measurable G := by
    have : G = G0m ∘ cgiPer c := funext fun x => hGdef x
    rw [this]
    exact hG0m_sm.measurable.comp (cgiPer_measurable c)
  have hGG0 : (fun x => G x) =ᵐ[cylMeas c] ⇑G0 := by
    filter_upwards [cylMeas_q_mem_ae c hc, hG0m_ae] with x hx hx2
    rw [hGdef, cgiPer_mem c hc x hx, hx2]
  have hsub : ∀ n, (fun x => g n x - G x) =ᵐ[cylMeas c] (fun x => g n x - G0 x) := fun n =>
    hGG0.mono fun x hx => by simp only [hx]
  refine ⟨G, ae_of_all _ fun x => ?_, hGmeas.aestronglyMeasurable, ?_⟩
  · show G (qShift c x) = G x
    rw [hGdef, hGdef, cgiPer_qShift c hc x]
  · exact Tendsto.congr (fun n => (eLpNorm_congr_ae (hsub n)).symm) hconv

end UnforcedLeray.Short.IIb
