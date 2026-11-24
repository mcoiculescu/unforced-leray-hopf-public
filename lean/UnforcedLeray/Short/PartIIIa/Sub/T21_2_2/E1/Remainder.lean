import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_9

/-!
# `PartIII-a:T21/2/2/3/9`: the bound of the `E_1` rate

Source: `the November 2 reference manuscript`, lines 3062-3071 ("the diffusion-weight
errors have coefficient `C_m β` and the transport and compact terms have coefficient `C_b`"),
3044-3051. The diffusion and transport integrations by parts are the hypotheses `hD`, `hTr`; the
one-direction bound is `tk_gen` (`Sub/PartIIIa_T21_2_2_3_9.lean`), summed over `k` here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem e1RemainderBound (m : ℝ) (hm : 8 < m)
    (hW : UnforcedLeray.Short.IIIa.PeriodicWeightLogBounds)
    (hD : UnforcedLeray.Short.IIIa.AdjE1.E1DiffusionIBP m)
    (hTr : UnforcedLeray.Short.IIIa.AdjE1.E1TransportIBP m) :
    UnforcedLeray.Short.IIIa.AdjE1.E1RemainderBound m := by
  obtain ⟨CW, hCW0, hWB⟩ := wb_of_hW hW m
  intro CV Kχ
  have hCVm := le_max_right CV 0
  have hKm := le_max_right Kχ 0
  refine ⟨CW + 2 * CW ^ 2 + 3 + 2 * max CV 0 * CW + 6 * max CV 0 + max Kχ 0, ?_, ?_⟩
  · nlinarith [sq_nonneg CW, mul_nonneg hCVm hCW0, hKm]
  intro d β V Φ χ hd hβ hβ1 hVc hVp hVb hlo hhi hχ hχi hχb
  have hCV : 0 ≤ CV := CV_nonneg hVb
  rw [max_eq_left hCV]
  have hwb := hWB d β hd hβ hβ1
  have hk := fun k : Fin 2 =>
    tk_gen d β CW CV (periodicWeight (-m) d) (dtW m d β) V Φ χ k hβ hβ1 hCW0 hCV
      ((pw_contDiff _ _).of_le (by exact_mod_cast le_top)) (fun y => (pw_pos _ _ y).le)
      hwb.grad hwb.dil hwb.dt hwb.dtc hVc hVb hlo.smooth hχ hlo.int1
      (fun l => hhi.int2 l k) (hχi k) (hD d Φ hd hlo hhi k)
      (hTr d CV V Φ hd hVc hVp hVb hlo hhi k)
  have hE2 : adjE2 d m Φ = ∑ k : Fin 2, ∑ l : Fin 2,
      ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx l (pdCx k Φ) y‖ ^ 2 := by
    unfold adjE2
    exact Finset.sum_comm
  have hN0 : 0 ≤ ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx 0 Φ y‖ ^ 2 :=
    setIntegral_nonneg (B0579.measurableSet_cell d) fun y _ =>
      mul_nonneg (pw_pos _ _ y).le (sq_nonneg _)
  have hN1 : 0 ≤ ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx 1 Φ y‖ ^ 2 :=
    setIntegral_nonneg (B0579.measurableSet_cell d) fun y _ =>
      mul_nonneg (pw_pos _ _ y).le (sq_nonneg _)
  have hE0 : 0 ≤ adjE0 d m Φ := adjE0_nonneg d m Φ
  have h0 := hk 0
  have h1 := hk 1
  rw [hE2]
  unfold e1Rate adjE1
  simp only [Fin.sum_univ_two] at hχb h0 h1 ⊢
  have hKle : Kχ ≤ CW + 2 * CW ^ 2 + 3 + 2 * CV * CW + 6 * CV + max Kχ 0 := by
    nlinarith [le_max_left Kχ 0, sq_nonneg CW, mul_nonneg hCV hCW0]
  have hB := mul_le_mul_of_nonneg_right hKle hE0
  have hA := mul_nonneg hKm (add_nonneg hN0 hN1)
  linarith [hA, hB, hχb, h0, h1, hN0, hN1, hE0]

end UnforcedLeray.Short.IIIa.AdjE1
