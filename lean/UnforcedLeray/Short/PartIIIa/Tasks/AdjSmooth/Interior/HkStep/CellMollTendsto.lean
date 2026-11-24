import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellDenseCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollTendstoCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt

/-!
# `PartIII-a:T21/2/7/2/1/1/5/11`: mollification converges in the periodic `X_{-m,c}`

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.

Proof (`ε/3`): for `f` periodic in `X_{-m,c}` and `e > 0`, `CellDenseCont` gives a continuous,
periodic, band-limited `h` with `‖f - h‖ ≤ e`. Then
`ρ_n ⋆ f - f = ρ_n ⋆ (f - h) + (ρ_n ⋆ h - h) - (f - h)`, where `‖ρ_n ⋆ (f - h)‖ ≤ C e`
(`CellMollBound`), `‖ρ_n ⋆ h - h‖ → 0` (`CellMollTendstoCont`), and `‖f - h‖ ≤ e`.
Hence `‖ρ_n ⋆ f - f‖ ≤ (C + 2) e` eventually, which gives convergence to `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- For a locally integrable `g`, the integrand of the mollification at `x` is integrable
(the mollifier is continuous with compact support). -/
theorem cmt_integrable_mol (n : ℕ) {g : ℝ × ℝ → ℂ} (hg : LocallyIntegrable g volume)
    (x : ℝ × ℝ) :
    Integrable (fun y => molKer n y • g (x - y)) volume := by
  have hK : HasCompactSupport (molKer n) := (molBump n).hasCompactSupport_normed (μ := volume)
  have h : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (molKer n t) (g (x - t))) volume :=
    (hK.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (cmb_molKer_continuous n) hg x)
  simpa [ContinuousLinearMap.lsmul_apply] using h

/-- The mollification is linear: `ρ_n ⋆ (f - h) = ρ_n ⋆ f - ρ_n ⋆ h` for locally integrable `f`
and continuous `h`. -/
theorem cmt_cellMoll_sub (n : ℕ) {f h : ℝ × ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (hh : Continuous h) :
    cellMoll n (f - h) = cellMoll n f - cellMoll n h := by
  funext x
  have hfI := cmt_integrable_mol n hf x
  have hhI := cmt_integrable_mol n hh.locallyIntegrable x
  simp only [cellMoll, cellConv, Pi.sub_apply, smul_sub]
  exact integral_sub hfI hhI

/-- The mollification of a locally integrable field is continuous (hence strongly measurable). -/
theorem cmt_cellMoll_continuous (n : ℕ) {g : ℝ × ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    Continuous (cellMoll n g) := by
  have hK : HasCompactSupport (molKer n) := (molBump n).hasCompactSupport_normed (μ := volume)
  unfold cellMoll
  rw [cellConv_eq_convolution]
  exact hK.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (cmb_molKer_continuous n) hg

/-- **Mollification converges in `X_{-m,c}`** (SP 3060-3061; `ε/3` argument as in the header). -/
theorem cellMollTendsto : UnforcedLeray.Short.IIIa.CellMollTendsto := by
  intro c m f hc hper hf
  obtain ⟨C, hC0, hCb⟩ := cellMollBound c m hc
  have hfLI : LocallyIntegrable f volume := (cellPeriodicLocInt c m f hc hper hf).2
  have hfAE : AEStronglyMeasurable f (B0579.cellMeasure c (-m)) := hf.1
  have key : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      xNorm c (-m) (cellMoll n f - f) ≤ ENNReal.ofReal ((C + 2) * e) := by
    intro e he
    obtain ⟨h, hcont, hperh, hband, hfh⟩ := cellDenseCont c m f hc hper hf e he
    have hhLI : LocallyIntegrable h volume := hcont.locallyIntegrable
    have hfhPer : ∀ x : ℝ × ℝ, (f - h) (x.1 + c, x.2) = (f - h) x := by
      intro x
      simp only [Pi.sub_apply, hper x, hperh x]
    have hfhMem : MemLp (f - h) 2 (B0579.cellMeasure c (-m)) :=
      ⟨hfAE.sub hcont.aestronglyMeasurable, lt_of_le_of_lt hfh ENNReal.ofReal_lt_top⟩
    have hT := cellMollTendstoCont c m h hc hcont hperh hband
    have hTe := ENNReal.tendsto_nhds_zero.1 hT (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he)
    have hpos1 : 0 ≤ C * e := mul_nonneg hC0 he.le
    have hpos2 : 0 ≤ C * e + e := add_nonneg hpos1 he.le
    filter_upwards [hTe] with n hn
    have hsplit : cellMoll n f - f = (cellMoll n (f - h) + (cellMoll n h - h)) - (f - h) := by
      rw [cmt_cellMoll_sub n hfLI hcont]
      abel
    have hA : xNorm c (-m) (cellMoll n (f - h)) ≤ ENNReal.ofReal (C * e) := by
      have h1 := hCb n (f - h) hfhPer hfhMem
      calc xNorm c (-m) (cellMoll n (f - h))
          ≤ ENNReal.ofReal C * xNorm c (-m) (f - h) := h1
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal e := by gcongr
        _ = ENNReal.ofReal (C * e) := (ENNReal.ofReal_mul hC0).symm
    have hAcont : Continuous (cellMoll n (f - h)) :=
      cmt_cellMoll_continuous n (hfLI.sub hhLI)
    have hBcont : Continuous (cellMoll n h - h) :=
      (cmt_cellMoll_continuous n hhLI).sub hcont
    have hABcont : Continuous (cellMoll n (f - h) + (cellMoll n h - h)) :=
      hAcont.add hBcont
    have htri : xNorm c (-m) (cellMoll n f - f)
        ≤ xNorm c (-m) (cellMoll n (f - h)) + xNorm c (-m) (cellMoll n h - h)
          + xNorm c (-m) (f - h) := by
      rw [hsplit]
      unfold xNorm
      have e1 := eLpNorm_add_le
        (hAcont.aestronglyMeasurable (μ := B0579.cellMeasure c (-m)))
        (hBcont.aestronglyMeasurable (μ := B0579.cellMeasure c (-m))) (p := 2) (by norm_num)
      have e2 := eLpNorm_sub_le
        (hABcont.aestronglyMeasurable (μ := B0579.cellMeasure c (-m)))
        hfhMem.1 (p := 2) (by norm_num)
      calc eLpNorm (cellMoll n (f - h) + (cellMoll n h - h) - (f - h)) 2 (B0579.cellMeasure c (-m))
          ≤ eLpNorm (cellMoll n (f - h) + (cellMoll n h - h)) 2 (B0579.cellMeasure c (-m))
            + eLpNorm (f - h) 2 (B0579.cellMeasure c (-m)) := e2
        _ ≤ (eLpNorm (cellMoll n (f - h)) 2 (B0579.cellMeasure c (-m))
            + eLpNorm (cellMoll n h - h) 2 (B0579.cellMeasure c (-m)))
            + eLpNorm (f - h) 2 (B0579.cellMeasure c (-m)) := add_le_add e1 le_rfl
    calc xNorm c (-m) (cellMoll n f - f)
        ≤ xNorm c (-m) (cellMoll n (f - h)) + xNorm c (-m) (cellMoll n h - h)
          + xNorm c (-m) (f - h) := htri
      _ ≤ ENNReal.ofReal (C * e) + ENNReal.ofReal e + ENNReal.ofReal e :=
          add_le_add (add_le_add hA hn) hfh
      _ = ENNReal.ofReal (C * e + e + e) := by
          rw [ENNReal.ofReal_add hpos2 he.le, ENNReal.ofReal_add hpos1 he.le]
      _ ≤ ENNReal.ofReal ((C + 2) * e) := ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  by_cases htop : ε = ⊤
  · refine Filter.Eventually.of_forall (fun n => ?_)
    rw [htop]
    exact le_top
  · obtain ⟨t, ht_eq⟩ : ∃ t : ℝ, ε = ENNReal.ofReal t :=
      ⟨ε.toReal, (ENNReal.ofReal_toReal htop).symm⟩
    have ht : 0 < t := ENNReal.ofReal_pos.1 (ht_eq ▸ hε)
    have hC2 : 0 < C + 2 := by linarith
    have hne : C + 2 ≠ 0 := hC2.ne'
    have hval : (C + 2) * (t / (2 * (C + 2))) = t / 2 := by
      field_simp
    filter_upwards [key (t / (2 * (C + 2))) (div_pos ht (by linarith))] with n hn
    refine hn.trans ?_
    rw [hval, ht_eq]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end UnforcedLeray.Short.IIIa
