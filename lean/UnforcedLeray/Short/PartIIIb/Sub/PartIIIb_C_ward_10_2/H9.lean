import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H8

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (9): the young `L²` bound of the primitive field

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3713,
4180-4186, 2683-2689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **The vertical field `|Ψ_{X₀}| e_z` on the annulus region has young chart reading in `L²`**
(source 3687-3713, 4180-4186, 2683-2689). -/
theorem w2_psiBd {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (r2 : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g →
      WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R (w2Phi ν μ R c r2 g)) K := by
  obtain ⟨C, hC, hDom⟩ := w2_psi_dom hν hR hc hμ r2
  obtain ⟨B, hB, hLt⟩ := w2_ltau hν hR hc hμ r2
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro g hg
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  set T := oldCutSrc R c r0 g with hT
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set N : ℝ → Space → ℝ := w2N ν μ R c r2 g with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := w2N_measurable r2 hg.measurable
  have hN0 : ∀ τ y, 0 ≤ N τ y := w2N_nonneg ν μ R c r2 g
  have hNper : ∀ τ y, N (τ + 2 * c / R) y = N τ y := by
    intro τ y
    simp only [hN, w2N]
    simp only [outPrim, w2_X0_periodic hν hR hc hg]
  have hFm : Measurable (fun x : ℝ × Space => w2Phi ν μ R c r2 g x.1 x.2) :=
    hNm.smul_const _
  refine ⟨(w10_read_meas hFm).aestronglyMeasurable, ?_⟩
  have hDom' : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤ ENNReal.ofReal C *
        w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T) τ y := by
    intro τ y hy
    rw [hN, w2N_meridPt]
    unfold w2N
    split_ifs with h
    · exact hDom g hg τ y hy h
    · simp
  have hTr := chartYoungTransport R c ν hR hc hν (w10Fn R ν N) (w10Fn_measurable R ν hNm)
    (w10Fn_axi R ν N) (w10Fn_periodic R ν _ hNper)
  have hI : ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
        (ENNReal.ofReal C * (ENNReal.ofReal B *
          IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T))) ^ (2 : ℝ) := by
    refine hTr.trans ?_
    gcongr
    have hpt : ∀ τ y, (if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
        ‖w10Fn R ν N τ y‖ₑ else 0) ≤ ENNReal.ofReal C *
          w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T) τ y := by
      intro τ y
      by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
      · rw [if_pos h]
        have h' : R * Real.sqrt ν ≤ ϱ y := h
        rw [w10Fn_enorm hN0 τ h']
        exact hDom' τ y h'
      · rw [if_neg h]
        exact zero_le
    calc IIIa.ltauLq (2 * c / R) 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
            then ‖w10Fn R ν N τ y‖ₑ else 0)
        ≤ IIIa.ltauLq (2 * c / R) 2 (fun τ y => ENNReal.ofReal C *
            w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T) τ y) :=
          IIIa.ltauLq_mono _ _ (by norm_num) hpt
      _ = ENNReal.ofReal C * IIIa.ltauLq (2 * c / R) 2
            (w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T)) :=
          IIIa.ltauLq_const_mul _ _ (by norm_num) _ ENNReal.ofReal_ne_top _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hLt g hg) zero_le
  have hF : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖w2Phi ν μ R c r2 g τ y‖ ≤ N τ y :=
    fun τ y _ => le_of_eq (w2Phi_norm ν μ R c r2 g τ y)
  exact w10_final hν hR hc g hg.measurable r0 hN0 hF C B hC hB hI

end UnforcedLeray.Short.PartIIIb.Concrete
end
