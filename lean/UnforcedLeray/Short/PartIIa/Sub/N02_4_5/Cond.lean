import UnforcedLeray.Short.PartIIa.Sub.N02_4_5

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzModeSolve`): the conditional theorem `nzModeSolve_of`


`NzConvIntegrable`, `NzConvDecay` (see `Sub/N02_4_5.lean`), the potentials
`φ = conv h₁`, `ψ = conv h₂` with `h₁ = i k a + ∂_η b`, `h₂ = i k b - ∂_η a` solve
`i k φ - ∂_η ψ = a`, `∂_η φ + i k ψ = b`; both are smooth, `s`-band supported and decay like
`e^{-|k||η|}` together with their derivatives of order `≤ 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- `h₁ = i k a + ∂_η b`. -/
def nzmsH1 (k : ℝ) (a b : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun q =>
  Complex.I * (k : ℂ) * a q + fderiv ℝ b q (0, 1)

/-- `h₂ = i k b - ∂_η a`. -/
def nzmsH2 (k : ℝ) (a b : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun q =>
  Complex.I * (k : ℂ) * b q - fderiv ℝ a q (0, 1)

theorem nzmsH1_smooth {k : ℝ} {a b : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (nzmsH1 k a b) :=
  (contDiff_const.mul ha).add (nzms_dEta_smooth hb)

theorem nzmsH2_smooth {k : ℝ} {a b : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (nzmsH2 k a b) :=
  (contDiff_const.mul hb).sub (nzms_dEta_smooth ha)

theorem nzmsH1_band {k : ℝ} {a b : ℝ × ℝ → ℂ} {s0 s1 L : ℝ} (ha : NzBandJ s0 s1 L a)
    (hb : NzBandJ s0 s1 L b) : NzBandJ s0 s1 L (nzmsH1 k a b) :=
  (ha.const_mul _).add hb.dEta

theorem nzmsH2_band {k : ℝ} {a b : ℝ × ℝ → ℂ} {s0 s1 L : ℝ} (ha : NzBandJ s0 s1 L a)
    (hb : NzBandJ s0 s1 L b) : NzBandJ s0 s1 L (nzmsH2 k a b) :=
  (hb.const_mul _).sub ha.dEta

theorem nzmsH1_dEta {k : ℝ} {a b : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (q : ℝ × ℝ) :
    fderiv ℝ (nzmsH1 k a b) q (0, 1) =
      Complex.I * (k : ℂ) * fderiv ℝ a q (0, 1) +
        fderiv ℝ (fun y => fderiv ℝ b y (0, 1)) q (0, 1) := by
  have h1 : DifferentiableAt ℝ (fun y => Complex.I * (k : ℂ) * a y) q :=
    ((contDiff_const.mul ha).differentiable (by simp)) q
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ b y (0, 1)) q :=
    ((nzms_dEta_smooth hb).differentiable (by simp)) q
  have hd : DifferentiableAt ℝ a q := (ha.differentiable (by simp)) q
  have e : fderiv ℝ (nzmsH1 k a b) q = fderiv ℝ (fun y => Complex.I * (k : ℂ) * a y) q +
      fderiv ℝ (fun y => fderiv ℝ b y (0, 1)) q := fderiv_add h1 h2
  rw [e, fderiv_const_mul hd]
  simp

theorem nzmsH2_dEta {k : ℝ} {a b : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (q : ℝ × ℝ) :
    fderiv ℝ (nzmsH2 k a b) q (0, 1) =
      Complex.I * (k : ℂ) * fderiv ℝ b q (0, 1) -
        fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q (0, 1) := by
  have h1 : DifferentiableAt ℝ (fun y => Complex.I * (k : ℂ) * b y) q :=
    ((contDiff_const.mul hb).differentiable (by simp)) q
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ a y (0, 1)) q :=
    ((nzms_dEta_smooth ha).differentiable (by simp)) q
  have hd : DifferentiableAt ℝ b q := (hb.differentiable (by simp)) q
  have e : fderiv ℝ (nzmsH2 k a b) q = fderiv ℝ (fun y => Complex.I * (k : ℂ) * b y) q -
      fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q := fderiv_sub h1 h2
  rw [e, fderiv_const_mul hd]
  simp

/-- Smoothness, `s`-support and exponential decay of a Green convolution. -/
theorem nzms_decay2 (hS : NzConvSmooth) (hD : NzConvDecay) {k : ℝ} (hk : k ≠ 0)
    {h : ℝ × ℝ → ℂ} {s0 s1 L : ℝ} (hs0 : 0 < s0) (hh : ContDiff ℝ ∞ h)
    (hB : NzBandJ s0 s1 L h) : NzDecay2 (nzConv k h) := by
  have hcs := hB.hasCompactSupport
  obtain ⟨C0, h0⟩ := hD k hk h hh hcs 0
  obtain ⟨C1, h1⟩ := hD k hk h hh hcs 1
  obtain ⟨C2, h2⟩ := hD k hk h hh hcs 2
  refine ⟨hS k hk h hh hcs, ⟨s0, s1, hs0, fun x hx => ?_⟩, |k|, max C0 (max C1 C2),
    abs_pos.2 hk, fun x m hm => ?_⟩
  · by_contra hxs
    exact hx (nzConv_eq_zero (fun y hy => (hB y hy).1) hxs)
  · have he : 0 ≤ Real.exp (-|k| * |x.2|) := (Real.exp_pos _).le
    interval_cases m
    · exact (h0 x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
    · exact (h1 x).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) he)
    · exact (h2 x).trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) he)

/-- **`NzModeSolve` from the five leaves (proved).** -/
theorem nzModeSolve_of (hK : NzGreenKey2D) (hS : NzConvSmooth) (hF : NzConvFderiv)
    (hI : NzConvIntegrable) (hD : NzConvDecay) : NzModeSolve := by
  intro k hk a b ha hb ⟨sa0, sa1, La, hsa0, hba⟩ ⟨sb0, sb1, Lb, hsb0, hbb⟩
  have hs0 : 0 < min sa0 sb0 := lt_min hsa0 hsb0
  have hBa : NzBandJ (min sa0 sb0) (max sa1 sb1) (max La Lb) a :=
    (show NzBandJ sa0 sa1 La a from hba).mono (min_le_left _ _) (le_max_left _ _)
      (le_max_left _ _)
  have hBb : NzBandJ (min sa0 sb0) (max sa1 sb1) (max La Lb) b :=
    (show NzBandJ sb0 sb1 Lb b from hbb).mono (min_le_right _ _) (le_max_right _ _)
      (le_max_right _ _)
  have hcsa := hBa.hasCompactSupport
  have hcsb := hBb.hasCompactSupport
  have hh1 : ContDiff ℝ ∞ (nzmsH1 k a b) := nzmsH1_smooth ha hb
  have hh2 : ContDiff ℝ ∞ (nzmsH2 k a b) := nzmsH2_smooth ha hb
  have hB1 := nzmsH1_band (k := k) hBa hBb
  have hB2 := nzmsH2_band (k := k) hBa hBb
  have hcs1 := hB1.hasCompactSupport
  have hcs2 := hB2.hasCompactSupport
  refine ⟨nzConv k (nzmsH1 k a b), nzConv k (nzmsH2 k a b),
    nzms_decay2 hS hD hk hs0 hh1 hB1, nzms_decay2 hS hD hk hs0 hh2 hB2, fun x => ⟨?_, ?_⟩⟩
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

end UnforcedLeray.Short.PartIIa
