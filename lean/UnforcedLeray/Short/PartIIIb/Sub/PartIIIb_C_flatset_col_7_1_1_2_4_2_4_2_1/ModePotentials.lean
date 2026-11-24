import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CoefSmoothBand
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve

/-!
# `ModePotentials` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/10`)

Source of record `the November 2 reference manuscript`
lines 1713-1716: the one-mode potentials `φ_n = G_{k_n} * (i k_n a_n + ∂_η b_n)` and
`ψ_n = G_{k_n} * (i k_n b_n - ∂_η a_n)` are `NzDecay2` and solve the one-mode flat Hodge equations.
The construction is the one of `nzModeSolve_of` (`PartII-a/Sub/N02_4_5/Cond.lean`), applied with
the smooth band data `a_n = coefR c f n`, `b_n = coefZ c f n` from `CoefSmoothBand`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- The two flat Hodge equations for the Green convolutions of `h₁`, `h₂` (the bullets of the proof
of `nzModeSolve_of`, with the data `a`, `b` kept as variables). -/
theorem modePot_modeEq_aux {k s0 s1 L : ℝ} (hk : k ≠ 0) {a b : ℝ × ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hBa : NzBandJ s0 s1 L a) (hBb : NzBandJ s0 s1 L b) :
    NzModeEq k a b (nzConv k (nzmsH1 k a b)) (nzConv k (nzmsH2 k a b)) := by
  have hh1 : ContDiff ℝ ∞ (nzmsH1 k a b) := nzmsH1_smooth ha hb
  have hh2 : ContDiff ℝ ∞ (nzmsH2 k a b) := nzmsH2_smooth ha hb
  have hB1 := nzmsH1_band (k := k) hBa hBb
  have hB2 := nzmsH2_band (k := k) hBa hBb
  have hcs1 := hB1.hasCompactSupport
  have hcs2 := hB2.hasCompactSupport
  have hcsa := hBa.hasCompactSupport
  have hcsb := hBb.hasCompactSupport
  have hK := nzGreenKey2D_of nzGreenKey1D_proof
  have hF := nzConvFderiv_of nzConvGenHyp_proof
  have hI := nzConvIntegrable_proof
  intro x
  constructor
  · -- first equation
    have e1 := hF k hk _ hh2 hcs2 x
    have e2 := nzConv_const_mul k (Complex.I * (k : ℂ)) (nzmsH1 k a b) x
    have hc1 : Continuous fun q => Complex.I * (k : ℂ) * nzmsH1 k a b q :=
      (contDiff_const.mul hh1).continuous
    have hcs1' : HasCompactSupport fun q => Complex.I * (k : ℂ) * nzmsH1 k a b q :=
      (hB1.const_mul _).hasCompactSupport
    have hc2 : Continuous fun q => fderiv ℝ (nzmsH2 k a b) q (0, 1) :=
      (nzms_dEta_smooth hh2).continuous
    have hcs2' : HasCompactSupport fun q => fderiv ℝ (nzmsH2 k a b) q (0, 1) :=
      hB2.dEta.hasCompactSupport
    have esub := nzConv_sub hI hk hc1 hcs1' hc2 hcs2' x
    have hfun : (fun q => Complex.I * (k : ℂ) * nzmsH1 k a b q - fderiv ℝ (nzmsH2 k a b) q (0, 1))
        = fun q => fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q (0, 1) - (k : ℂ) ^ 2 * a q := by
      funext q
      rw [nzmsH2_dEta ha hb q]
      simp only [nzmsH1]
      have hz : Complex.I * (k : ℂ) * (Complex.I * (k : ℂ)) = -(k : ℂ) ^ 2 := by
        have := Complex.I_mul_I
        linear_combination ((k : ℂ) ^ 2) * this
      linear_combination (a q) * hz
    rw [e1, ← e2, ← esub, hfun]
    exact hK k hk a ha hcsa x
  · -- second equation
    have e1 := hF k hk _ hh1 hcs1 x
    have e2 := nzConv_const_mul k (Complex.I * (k : ℂ)) (nzmsH2 k a b) x
    have hc1 : Continuous fun q => fderiv ℝ (nzmsH1 k a b) q (0, 1) :=
      (nzms_dEta_smooth hh1).continuous
    have hcs1' : HasCompactSupport fun q => fderiv ℝ (nzmsH1 k a b) q (0, 1) :=
      hB1.dEta.hasCompactSupport
    have hc2 : Continuous fun q => Complex.I * (k : ℂ) * nzmsH2 k a b q :=
      (contDiff_const.mul hh2).continuous
    have hcs2' : HasCompactSupport fun q => Complex.I * (k : ℂ) * nzmsH2 k a b q :=
      (hB2.const_mul _).hasCompactSupport
    have eadd := nzConv_add hI hk hc1 hcs1' hc2 hcs2' x
    have hfun : (fun q => fderiv ℝ (nzmsH1 k a b) q (0, 1) +
          Complex.I * (k : ℂ) * nzmsH2 k a b q)
        = fun q => fderiv ℝ (fun y => fderiv ℝ b y (0, 1)) q (0, 1) - (k : ℂ) ^ 2 * b q := by
      funext q
      rw [nzmsH1_dEta ha hb q]
      simp only [nzmsH2]
      have hz : Complex.I * (k : ℂ) * (Complex.I * (k : ℂ)) = -(k : ℂ) ^ 2 := by
        have := Complex.I_mul_I
        linear_combination ((k : ℂ) ^ 2) * this
      linear_combination (b q) * hz
    rw [e1, ← e2, ← eadd, hfun]
    exact hK k hk b hb hcsb x

theorem modePotentials : ModePotentials := by
  intro c hc f hf n hn
  obtain ⟨s0, s1, L, hs0, hb⟩ := coefSmoothBand c hc f hf
  obtain ⟨ha, hb', hBa, hBb⟩ := hb n
  have hk : nzk c n ≠ 0 := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn') hc.ne'
  have hS := nzConvSmooth_of nzConvGenHyp_proof
  have hD := nzConvDecay_of nzConvGenHyp_proof
  exact ⟨nzms_decay2 hS hD hk hs0 (nzmsH1_smooth ha hb') (nzmsH1_band hBa hBb),
    nzms_decay2 hS hD hk hs0 (nzmsH2_smooth ha hb') (nzmsH2_band hBa hBb),
    modePot_modeEq_aux hk ha hb' hBa hBb⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
