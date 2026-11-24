import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2

/-!
# `PartIII-b:C/near/delta/8/2/3/4/org/3`: `FreeEnergyFlatSq` from the scalar leaves of `T18/3/2`

Source `the November 2 reference manuscript`
1686-1689, 3541-3552.  `FreeEnergyFlatSq` is the `γ = 0`, single-`μ`, general-`c` case of
`IIIa.FreeEnergyInequalities`; the proof of `IIIa.freeEnergyInequalities_of`
(`PartIII-a/Sub/PartIII-a_T18_3_2.lean`) is repeated with `γ = 0` (`gainConj 0 ν = id`), so the
scalar leaves `CutoffLimit`, `SliceLoc`, `NormSq`, `AgeSlice`, `YoungSlice`, `GainLocF` (tasks
`PartIII-a:T18/3/2/2..6, 8`) and `WeightedEnergyIdentity` suffice.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution vnorm2 tnorm2 hCalNorm tCalNorm gainConj)

theorem freeEnergyFlatSq_of' (hCL : IIIa.CutoffLimit) (hSL : IIIa.SliceLoc) (hNS : IIIa.NormSq)
    (hAS : IIIa.AgeSlice) (hY : IIIa.YoungSlice) (hGF : IIIa.GainLocF)
    (hW : IIIa.WeightedEnergyIdentity) : FreeEnergyFlatSq := by
  intro c ν μ hc hν hk F hFm hF b G hsol
  have hFm' : ∀ i j, Measurable fun p => F p i j := hFm
  have hbm : ∀ i, Measurable fun p => b p i := hsol.measurable
  have hGm : ∀ i j, Measurable fun p => G p i j := hsol.gradMeasurable
  -- local finiteness
  have hBG : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (G p) ^ 2) < ⊤) := by
    intro s₁ s₂ h1 h2
    have h := hsol.energyLoc s₁ s₂ h1 h2
    have e1 : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ vnorm2 (b p) ^ 2 := fun p => sq_nonneg _
    have e2 : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ tnorm2 (G p) ^ 2 := fun p => sq_nonneg _
    constructor
    · refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) h
      linarith [e2 p]
    · refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) h
      linarith [e1 p]
  have hFl := hGF c ν 0 hc le_rfl hν F hFm' (by simpa [fsf_gainConj_zero] using hF)
  simp only [fsf_gainConj_zero] at hFl
  set gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (b p) ^ 2 with hgV
  set gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (G p) ^ 2 with hgN
  set gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (F p) ^ 2 with hgQ
  have hgVm : Measurable gV := IIIa.measurable_vnorm2_sq hbm
  have hgNm : Measurable gN := (IIIa.measurable_tnorm2 hGm).pow_const 2
  have hgQm : Measurable gQ := (IIIa.measurable_tnorm2 hFm').pow_const 2
  have hgV0 : ∀ p, 0 ≤ gV p := fun p => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun p => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun p => sq_nonneg _
  obtain ⟨hVm, hVi, -⟩ := hSL c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨hNm, hNi, -⟩ := hSL c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨hQm, hQi, -⟩ := hSL c gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2
  have hWEI := hW c ν 0 μ hc hν le_rfl F b G (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).1) hFm' hsol
  simp only [fsf_gainConj_zero] at hWEI
  have hZ : ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * IIIa.sliceSq c gV s) < ⊤ := by
    obtain ⟨δ, hδ, hfin⟩ := hsol.zeroEntrance
    refine ⟨δ, hδ, ?_⟩
    obtain ⟨-, h2⟩ := hAS c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
    have := h2 δ
    rw [this] at hfin
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by simpa using inv_pos.2 hc
    rcases ENNReal.mul_lt_top_iff.1 hfin with h | h | h
    · exact h.2
    · exact absurd h hc'
    · simp [h]
  have hbase := fun (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ 2 * ν) =>
    hCL (μ.re + 1 / 4) ν (1 / 2 + 2 * μ.re) θ (IIIa.sliceSq c gV) (IIIa.sliceSq c gN)
      (IIIa.sliceSq c (fun p => tnorm2 (F p) * tnorm2 (G p)))
      (IIIa.sliceSq c gQ) hk hν hθ hθ2 (by linarith)
      (fun s => ⟨IIIa.sliceSq_nonneg hgV0 s, IIIa.sliceSq_nonneg hgN0 s,
        IIIa.sliceSq_nonneg (fun p => mul_nonneg (by unfold tnorm2; positivity)
          (by unfold tnorm2; positivity)) s, IIIa.sliceSq_nonneg hgQ0 s⟩)
      hVm hNm hQm
      (fun s₁ s₂ h1 h2 => ⟨hVi s₁ s₂ h1 h2, hNi s₁ s₂ h1 h2, hQi s₁ s₂ h1 h2⟩)
      (hY c F G hc hFm' hGm (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2)
        (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) θ hθ)
      hZ hWEI
  have eH : hCalNorm c b ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * IIIa.sliceSq c gV s) := by
    rw [hNS.1]
    exact (hAS c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1).1
  have eN : tCalNorm c G ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * IIIa.sliceSq c gN s) := by
    rw [hNS.2]
    exact (hAS c (-1 / 2) gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2).1
  have eQ : tCalNorm c F ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * IIIa.sliceSq c gQ s) := by
    rw [hNS.2]
    exact (hAS c (-1 / 2) gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2).1
  rw [eH, eN, eQ]
  have hk2 : 2 * (μ.re + 1 / 4) = 1 / 2 + 2 * μ.re := by ring
  constructor
  · have h := hbase ν hν (by linarith)
    have h' : 2 * ν - ν = ν := by ring
    rw [h'] at h
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal c⁻¹)) h
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> ring
  · have h := hbase (2 * ν) (by linarith) le_rfl
    simp only [sub_self, ENNReal.ofReal_zero, zero_mul, add_zero] at h
    have h2 := mul_le_mul' (le_refl (ENNReal.ofReal c⁻¹)) h
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
