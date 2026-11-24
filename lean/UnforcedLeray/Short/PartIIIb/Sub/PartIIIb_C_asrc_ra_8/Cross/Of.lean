import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L2

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : `RCrossBound` from the double-sum, cell-norm and continuity leaves

Source `the November 2 reference manuscript`
5029-5031 (cross-center cell norms `≤ C δ_base M(A) s^{5/2}`), 4371 (`δ_base`), 4955-4962
(`M(A)`).  With `B = A^y(s)`: `|B| ≤ s^{5/2} M(A)` on `0 < s ≤ 1.1/ν` (`fac_frob_Ay_le`,
`aySumBdd_inst11`); `RcCrossPointwise` and `RcCellGaussL2` give the cell norm
`≤ K₂ K₁ |B| e^{-c²/135}`, and `e^{-c²/135} = δ_base` at `C_Σ = 0`, `b_Σ = 1/135`, `P_ν = 1`
(`k = 0`, `ν₀ = 1`).  `RcCrossContinuous` gives the `AEMeasurable` conjunct.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rc_toMer_continuous : Continuous toMer := by
  unfold toMer
  fun_prop

theorem rCrossBound_of (as : ℝ) (χf : ℝ → ℝ) (h1 : RcCrossPointwise) (h2 : RcCellGaussL2)
    (h3 : RcCrossContinuous) : RCrossBound as χf := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨K1, hK1, hP⟩ := h1
  obtain ⟨K2, hK2, hL⟩ := h2
  refine ⟨0, 1 / 135, K2 * K1, 0, 1, by norm_num, one_pos, ?_⟩
  intro p d hreg hν μ hμ A hA s hs hs'
  have hνp : 0 < p.ν := p.ν_pos
  have hbdd := aySumBdd_inst11 as χf hχ p.ν hνp A hA
  have hk := fac_frob_Ay_le p.ν χf A hbdd s hs hs'
  have hB : frob (Ay p.ν χf A s) ≤ s ^ (5 / 2 : ℝ) * affM p.ν χf A := by
    linarith [fac_frob_nonneg (s • deriv (Ay p.ν χf A) s)]
  have hcont := h3 p.ν s (Ay p.ν χf A s) hνp hν hs hs'
  rw [rCross_eq_rcCross]
  refine ⟨?_, ?_⟩
  · exact (ENNReal.continuous_ofReal.comp
      ((continuous_norm.comp (rc_toMer_continuous.comp hcont)).pow 2)).measurable.aemeasurable
  · set E := Real.exp (-(cOf p.ν ^ 2) / 135) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hF0 : 0 ≤ frob (Ay p.ν χf A s) := fac_frob_nonneg _
    have hD0 : 0 ≤ K1 * frob (Ay p.ν χf A s) * E := by positivity
    have hbound := hL p.c (K1 * frob (Ay p.ν χf A s) * E) (rcCross p.ν s (Ay p.ν χf A s))
      p.c_pos hD0 (fun x => hP p.ν s (Ay p.ν χf A s) x hνp hν hs hs')
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hdb : deltaBase 0 (1 / 135) p.ν = E := by
      rw [hE]
      unfold deltaBase
      congr 1
      ring
    rw [hdb, pow_zero, mul_one]
    have hM0 : 0 ≤ affM p.ν χf A := affM_nonneg p.ν χf A
    have hs5 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    apply pow_le_pow_left₀ (by positivity)
    have hKK : 0 ≤ K2 * K1 * E := by positivity
    have := mul_le_mul_of_nonneg_left hB hKK
    calc K2 * (K1 * frob (Ay p.ν χf A s) * E) = K2 * K1 * E * frob (Ay p.ν χf A s) := by ring
      _ ≤ K2 * K1 * E * (s ^ (5 / 2 : ℝ) * affM p.ν χf A) := this
      _ = K2 * K1 * E * affM p.ν χf A * s ^ (5 / 2 : ℝ) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
