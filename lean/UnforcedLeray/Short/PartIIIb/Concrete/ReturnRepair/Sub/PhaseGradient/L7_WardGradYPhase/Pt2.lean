import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Pt

/-!
# `PartIII-b:C/rep/2/7`, proof of `WGYPointwise`

Source 4192-4200, 4203-4214, 5212-5223.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wgyPointwise : WGYPointwise := by
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨C1, hC1, hcut⟩ := wgyCutPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨C2, hC2, hcomm⟩ := wgy_comm_fderiv_bound hχ
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hL : 0 < L := by rw [hLdef]; positivity
  have hLsq : ν * R ^ 2 = L ^ 2 := by
    rw [hLdef, mul_pow, Real.sq_sqrt hν.le]; ring
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hrL : R * Real.sqrt (5 * ν / 6) < L := by
    rw [hLdef]
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hQ2L : R * Real.sqrt (5 * ν / 4) ≤ 2 * L := by
    rw [hLdef]
    have : Real.sqrt (5 * ν / 4) ≤ 2 * Real.sqrt ν := by
      rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc R * Real.sqrt (5 * ν / 4) ≤ R * (2 * Real.sqrt ν) := by gcongr
      _ = 2 * (R * Real.sqrt ν) := by ring
  have hpos : ∀ᶠ z in 𝓝 y, 0 < ϱ z := (continuous_ϱ.continuousAt).eventually (lt_mem_nhds hy)
  have hYev : sepWY ν μ R χy T τ =ᶠ[𝓝 y]
      fun z => wardStreamCut ν R χy (sepWre ν μ T) τ z + tcComm ν R χy (sepX0 ν μ T) τ z := by
    filter_upwards [hpos] with z hz
    exact wgy_Y_eq hχ hσ hν hν1 hR1 hP0 hμ hT hSM hAx τ hz
  obtain ⟨hdc, hbc⟩ := hcut ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy
  have hcutfun : wardStreamCut ν R χy (sepWre ν μ T) τ = fun z => wardStreamCut ν R χy (sepWre ν μ T) τ z := rfl
  -- the commutator
  have hcommstep : ∃ D : Space →L[ℝ] Space, DifferentiableAt ℝ (tcComm ν R χy (sepX0 ν μ T) τ) y ∧
      fderiv ℝ (tcComm ν R χy (sepX0 ν μ T) τ) y = D ∧
      ENNReal.ofReal ‖D‖ ≤ ENNReal.ofReal C2 *
              (ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y +
                wgxJet 1 ν μ L T τ y +
                ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y +
                ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y +
                ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) := by
    by_cases hmem : y ∈ streamAnn ν R
    · obtain ⟨hL1, hb'⟩ := hmem
      have hyoung : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrL hL1
      have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
      have hZc : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) :=
        wgx_sepX0_contDiffOn hν hμ' hr0 hP0 hT hSM τ
      have hZat : ContDiffAt ℝ 2 (sepX0 ν μ T τ) y := hZc.contDiffAt (hopen.mem_nhds hyoung)
      have hdr := fun r z (hr : R * Real.sqrt (5 * ν / 6) < r) =>
        wgx_sepX0_partials hν hR hμ' hP0 hT hSM hAx τ r z hr
      have hΨ := wgx_outPrim_hasFDerivAt hν hR hZc hdr hyoung
      obtain ⟨hfr, hnorm⟩ := wgx_sepX0_axi hν hμ' hr0 hP0 hT hSM hAx τ y hyoung
      have hρ0 : 0 < ϱ y := lt_of_lt_of_le hL hL1
      have hΨb : ‖(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2) • ϱD y +
          (-(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0)) •
            (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 2 * ϱ y * ‖sepX0 ν μ T τ y‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        have hn' : ‖sepX0 ν μ T τ !₂[ϱ y, 0, y 2]‖ = ‖sepX0 ν μ T τ y‖ := hnorm
        have h2 : |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2| ≤ ‖sepX0 ν μ T τ y‖ :=
          (wgx_abs_apply_le _ 2).trans hn'.le
        have h0 : |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0| ≤ ‖sepX0 ν μ T τ y‖ :=
          (wgx_abs_apply_le _ 0).trans hn'.le
        have hv := wgx_ϱD_le hρ0 v
        have hv2 := wgx_abs_apply_le v 2
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          EuclideanSpace.coe_proj, Real.norm_eq_abs]
        calc |ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2 * ϱD y v +
              -(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0) * v 2|
            ≤ |ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2 * ϱD y v| +
              |-(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0) * v 2| := abs_add_le _ _
          _ = ϱ y * |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2| * |ϱD y v| +
              ϱ y * |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0| * |v 2| := by
              simp only [abs_mul, abs_neg, abs_of_pos hρ0]
          _ ≤ ϱ y * ‖sepX0 ν μ T τ y‖ * ‖v‖ + ϱ y * ‖sepX0 ν μ T τ y‖ * ‖v‖ := by
              gcongr
          _ = 2 * ϱ y * ‖sepX0 ν μ T τ y‖ * ‖v‖ := by ring
      have hϱ2 : ϱ y ≤ 2 * L := hb'.trans hQ2L
      have hΨn : ‖(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2) • ϱD y +
          (-(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0)) •
            (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 4 * L * ‖sepX0 ν μ T τ y‖ := by
        refine hΨb.trans ?_
        have := mul_le_mul_of_nonneg_right hϱ2 (norm_nonneg (sepX0 ν μ T τ y))
        nlinarith
      obtain ⟨hdiff, hbd⟩ := hcomm ν R hν hν1 hR1 (sepX0 ν μ T) τ y _ ⟨hL1, hb'⟩ hZat hΨ hΨn
      refine ⟨_, hdiff, rfl, ?_⟩
      set Zn := ‖sepX0 ν μ T τ y‖ with hZn
      set Zdn := ‖fderiv ℝ (sepX0 ν μ T τ) y‖ with hZdn
      set Zddn := ‖fderiv ℝ (fderiv ℝ (sepX0 ν μ T τ)) y‖ with hZddn
      set Pn := |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)| with hPn
      have hj0 : wgxJet 0 ν μ L T τ y = ENNReal.ofReal Zn := by
        unfold wgxJet
        rw [if_pos hL1, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_zero]
      have hj1 : wgxJet 1 ν μ L T τ y = ENNReal.ofReal Zdn := by
        unfold wgxJet
        rw [if_pos hL1, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_one]
      have hj2 : wgxJet 2 ν μ L T τ y = ENNReal.ofReal Zddn := by
        unfold wgxJet
        rw [if_pos hL1, ← ofReal_norm_eq_enorm]
        congr 1
        rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
      have hψ : wgxPsi ν μ R T τ y = ENNReal.ofReal Pn := by
        unfold wgxPsi
        rw [Set.indicator_of_mem (show y ∈ streamAnn ν R from ⟨hL1, hb'⟩)]
      rw [hj0, hj1, hj2, hψ, ← wgy_ofReal5 C2 L⁻¹ Zn Zdn Zddn 0 Pn hC2 (inv_nonneg.2 hL.le)
        (norm_nonneg _) (norm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hbd
    · have hout := (Sub8_1_1_2_3.tcOut_iff_not_mem hν hR hy).2 hmem
      have hz := Sub8_1_1_2_3.tcComm_eventually_zero hχ (sepX0 ν μ T) τ hy hout
      refine ⟨0, (differentiableAt_const (0 : Space)).congr_of_eventuallyEq hz, ?_, ?_⟩
      · rw [hz.fderiv_eq]; simp
      · simp
  obtain ⟨D, hdD, hfD, hbD⟩ := hcommstep
  have hfy : fderiv ℝ (sepWY ν μ R χy T τ) y =
      fderiv ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y + D := by
    rw [hYev.fderiv_eq]
    exact (fderiv_add hdc hdD).trans (by rw [hfD])
  rw [hfy]
  refine (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans ?_
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact add_le_add hbc hbD

end UnforcedLeray.Short.PartIIIb.Concrete

end
