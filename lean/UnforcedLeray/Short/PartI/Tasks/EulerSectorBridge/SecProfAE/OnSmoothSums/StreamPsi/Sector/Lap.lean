import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2
import UnforcedLeray.Short.PartI.Sub.PartI_S05_1_1
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi.Sector.Smooth

/-!
# Polar Laplacian of the order-`m` sector function (`SecSectorLap`)

Source lines 841-889 of `the November 2 reference manuscript`.  General-order
port of `polarLaplacianCore_proof` (`PartI_S05_1_1.lean`): the line derivative of
`U^m * Q` is `U^m (m (w'/w - R'/R) Q + Q')`, and `m (1/w - Re w/|w|²) = -m i Im w/|w|²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- Line derivative of `(w/R)^m * Q`. -/
theorem lineZpow_Gm {w : ℝ → ℂ} {R : ℝ → ℝ} {Q : ℝ → ℂ} {dw dQ : ℂ} {dR : ℝ} (m : ℤ)
    (hw : HasDerivAt w dw 0) (hR : HasDerivAt R dR 0) (hQ : HasDerivAt Q dQ 0)
    (hw0 : w 0 ≠ 0) (hρ : R 0 ≠ 0) :
    HasDerivAt (fun t : ℝ => (w t / ((R t : ℝ) : ℂ)) ^ m * Q t)
      ((w 0 / ((R 0 : ℝ) : ℂ)) ^ m *
        ((m : ℂ) * (dw / w 0 - (dR : ℂ) / ((R 0 : ℝ) : ℂ)) * Q 0 + dQ)) 0 := by
  have hρC : ((R 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hRc : HasDerivAt (fun t : ℝ => ((R t : ℝ) : ℂ)) (dR : ℂ) 0 := hR.ofReal_comp
  have hU := hw.div hRc hρC
  have hU0 : w 0 / ((R 0 : ℝ) : ℂ) ≠ 0 := div_ne_zero hw0 hρC
  have hz := hasDerivAt_zpow m (w 0 / ((R 0 : ℝ) : ℂ)) (Or.inl hU0)
  have hP := hz.comp (0 : ℝ) hU
  have hG := hP.mul hQ
  refine hG.congr_deriv ?_
  simp only [Function.comp_apply, Pi.div_apply]
  rw [zpow_sub_one₀ hU0]
  field_simp

/-- The algebraic relations `1/Y - (A/ρ)/ρ = -J B/ρ²` and `J/Y - (B/ρ)/ρ = J A/ρ²`. -/
theorem invRel_Gm (Y J : ℂ) (A B ρ : ℝ) (hY0 : Y ≠ 0) (hY : Y = (A : ℂ) + (B : ℂ) * J)
    (hJ : J ^ 2 + 1 = 0) (hρ : ρ ^ 2 = A ^ 2 + B ^ 2) (hρ0 : ρ ≠ 0) :
    (1 : ℂ) / Y - ((A / ρ : ℝ) : ℂ) / (ρ : ℂ) = -J * (B : ℂ) / (ρ : ℂ) ^ 2 ∧
    J / Y - ((B / ρ : ℝ) : ℂ) / (ρ : ℂ) = J * (A : ℂ) / (ρ : ℂ) ^ 2 := by
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  have hρ2 : (ρ : ℂ) ^ 2 = (A : ℂ) ^ 2 + (B : ℂ) ^ 2 := by exact_mod_cast hρ
  have hρ2ne : (ρ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hρC
  have hinv : (1 : ℂ) / Y = ((A : ℂ) - (B : ℂ) * J) / (ρ : ℂ) ^ 2 := by
    rw [div_eq_div_iff hY0 hρ2ne]
    rw [hY]
    linear_combination hρ2 + (B : ℂ) ^ 2 * hJ
  have hinvJ : J / Y = J * ((A : ℂ) - (B : ℂ) * J) / (ρ : ℂ) ^ 2 := by
    rw [div_eq_div_iff hY0 hρ2ne]
    rw [hY]
    linear_combination J * hρ2 + J * (B : ℂ) ^ 2 * hJ
  constructor
  · rw [hinv]
    push_cast
    field_simp
    ring
  · rw [hinvJ]
    push_cast
    field_simp
    linear_combination (-(B : ℂ)) * hJ

/-- Derivative of `t ↦ (w t/R t)^m * (ψ'(R) A/R + κ ψ(R) B/R²)` along a line. -/
theorem lineDeriv_gen_m {ψ : ℝ → ℂ} {w : ℝ → ℂ} {R A B : ℝ → ℝ} {dw κ : ℂ} {dR dA dB : ℝ}
    (m : ℤ)
    (hψ0 : HasDerivAt ψ (deriv ψ (R 0)) (R 0))
    (hψ1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) (R 0)) (R 0))
    (hw : HasDerivAt w dw 0) (hR : HasDerivAt R dR 0) (hA : HasDerivAt A dA 0)
    (hB : HasDerivAt B dB 0) (hρ : R 0 ≠ 0) (hw0 : w 0 ≠ 0) :
    HasDerivAt (fun t : ℝ => (w t / ((R t : ℝ) : ℂ)) ^ m *
        (deriv ψ (R t) * ((A t / R t : ℝ) : ℂ) +
          κ * ψ (R t) * ((B t / (R t) ^ 2 : ℝ) : ℂ)))
      ((w 0 / ((R 0 : ℝ) : ℂ)) ^ m *
        ((m : ℂ) * (dw / w 0 - (dR : ℂ) / ((R 0 : ℝ) : ℂ)) *
            (deriv ψ (R 0) * ((A 0 / R 0 : ℝ) : ℂ) +
              κ * ψ (R 0) * ((B 0 / (R 0) ^ 2 : ℝ) : ℂ)) +
          (deriv (deriv ψ) (R 0) * (dR : ℂ) * ((A 0 / R 0 : ℝ) : ℂ) +
            deriv ψ (R 0) * ((dA / R 0 - A 0 * dR / (R 0) ^ 2 : ℝ) : ℂ) +
            κ * (deriv ψ (R 0) * (dR : ℂ) * ((B 0 / (R 0) ^ 2 : ℝ) : ℂ) +
              ψ (R 0) * ((dB / (R 0) ^ 2 - 2 * B 0 * dR / (R 0) ^ 3 : ℝ) : ℂ))))) 0 := by
  have hψR : HasDerivAt (fun t => ψ (R t)) (dR • deriv ψ (R 0)) 0 := hψ0.scomp 0 hR
  have hψ'R : HasDerivAt (fun t => deriv ψ (R t)) (dR • deriv (deriv ψ) (R 0)) 0 :=
    hψ1.scomp 0 hR
  have hAR := (hA.div hR hρ).ofReal_comp
  have hBR := (hB.div (hR.pow 2) (pow_ne_zero 2 hρ)).ofReal_comp
  have hQ := (hψ'R.mul hAR).add ((hψR.const_mul κ).mul hBR)
  have hL := lineZpow_Gm (w := w) (R := R) m hw hR hQ hw0 hρ
  refine hL.congr_deriv ?_
  simp only [Complex.real_smul, Pi.mul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply]
  push_cast
  field_simp

/-- First partial in direction `1`. -/
theorem fderivGm_one {m : ℤ} {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {w : ℂ} (hw : w ≠ 0) :
    fderiv ℝ (Ang.ofProfile m ψ) w 1 =
      (w / (‖w‖ : ℂ)) ^ m * (deriv ψ ‖w‖ * ((w.re / ‖w‖ : ℝ) : ℂ) +
        (-(m : ℂ) * Complex.I) * ψ ‖w‖ * ((w.im / ‖w‖ ^ 2 : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hP : DifferentiableAt ℝ (Ang.ofProfile m ψ) w :=
    ((secSectorSmooth_proof m ψ hψ w hw).differentiableAt (by simp))
  have hl : HasDerivAt (fun t : ℝ => w + (t : ℂ)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_add w)
  have hX : HasDerivAt (fun t : ℝ => Ang.ofProfile m ψ (w + (t : ℂ)))
      (fderiv ℝ (Ang.ofProfile m ψ) w 1) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hP.hasFDerivAt hl (by simp)
  have hψ0 : HasDerivAt ψ (deriv ψ ‖w + ((0 : ℝ) : ℂ)‖) ‖w + ((0 : ℝ) : ℂ)‖ := by
    simpa using hasDerivAt_of_contDiffOn hψ hpos
  have hR := hasDerivAt_norm_one hw
  have hQ : HasDerivAt (fun t : ℝ => ψ ‖w + (t : ℂ)‖)
      ((w.re / ‖w‖) • deriv ψ ‖w + ((0 : ℝ) : ℂ)‖) 0 := hψ0.scomp 0 hR
  have hL := lineZpow_Gm (w := fun t : ℝ => w + (t : ℂ)) (R := fun t : ℝ => ‖w + (t : ℂ)‖)
    m hl hR hQ (by simpa using hw) (by simpa using hpos.ne')
  have key := hX.unique (hL.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simp only [Ang.ofProfile, Ang.angPhase]
    ring))
  rw [key]
  obtain ⟨h1, -⟩ := invRel_Gm w Complex.I w.re w.im ‖w‖ hw (Complex.re_add_im w).symm
    (by simp [Complex.I_sq]) (by
      rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]) hpos.ne'
  simp only [Complex.ofReal_zero, add_zero, Complex.real_smul]
  congr 1
  rw [h1]
  push_cast
  ring

/-- First partial in direction `I`. -/
theorem fderivGm_I {m : ℤ} {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {w : ℂ} (hw : w ≠ 0) :
    fderiv ℝ (Ang.ofProfile m ψ) w Complex.I =
      (w / (‖w‖ : ℂ)) ^ m * (deriv ψ ‖w‖ * ((w.im / ‖w‖ : ℝ) : ℂ) +
        ((m : ℂ) * Complex.I) * ψ ‖w‖ * ((w.re / ‖w‖ ^ 2 : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hP : DifferentiableAt ℝ (Ang.ofProfile m ψ) w :=
    ((secSectorSmooth_proof m ψ hψ w hw).differentiableAt (by simp))
  have hl : HasDerivAt (fun t : ℝ => w + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add w
  have hX : HasDerivAt (fun t : ℝ => Ang.ofProfile m ψ (w + (t : ℂ) * Complex.I))
      (fderiv ℝ (Ang.ofProfile m ψ) w Complex.I) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hP.hasFDerivAt hl (by simp)
  have hψ0 : HasDerivAt ψ (deriv ψ ‖w + ((0 : ℝ) : ℂ) * Complex.I‖)
      ‖w + ((0 : ℝ) : ℂ) * Complex.I‖ := by
    simpa using hasDerivAt_of_contDiffOn hψ hpos
  have hR := hasDerivAt_norm_I hw
  have hQ : HasDerivAt (fun t : ℝ => ψ ‖w + (t : ℂ) * Complex.I‖)
      ((w.im / ‖w‖) • deriv ψ ‖w + ((0 : ℝ) : ℂ) * Complex.I‖) 0 := hψ0.scomp 0 hR
  have hL := lineZpow_Gm (w := fun t : ℝ => w + (t : ℂ) * Complex.I)
    (R := fun t : ℝ => ‖w + (t : ℂ) * Complex.I‖)
    m hl hR hQ (by simpa using hw) (by simpa using hpos.ne')
  have key := hX.unique (hL.congr_of_eventuallyEq (Eventually.of_forall fun t => by
    simp only [Ang.ofProfile, Ang.angPhase]
    ring))
  rw [key]
  obtain ⟨-, h2⟩ := invRel_Gm w Complex.I w.re w.im ‖w‖ hw (Complex.re_add_im w).symm
    (by simp [Complex.I_sq]) (by
      rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]) hpos.ne'
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.real_smul]
  congr 1
  rw [h2]
  push_cast
  ring

/-- The explicit second-derivative value along a line. -/
def polarEm (m : ℤ) (w0 dw : ℂ) (ρ A0 B0 dR dA dB : ℝ) (κ p0 p1 p2 : ℂ) : ℂ :=
  (w0 / (ρ : ℂ)) ^ m *
    ((m : ℂ) * (dw / w0 - (dR : ℂ) / (ρ : ℂ)) *
        (p1 * ((A0 / ρ : ℝ) : ℂ) + κ * p0 * ((B0 / ρ ^ 2 : ℝ) : ℂ)) +
      (p2 * (dR : ℂ) * ((A0 / ρ : ℝ) : ℂ) + p1 * ((dA / ρ - A0 * dR / ρ ^ 2 : ℝ) : ℂ) +
        κ * (p1 * (dR : ℂ) * ((B0 / ρ ^ 2 : ℝ) : ℂ) +
          p0 * ((dB / ρ ^ 2 - 2 * B0 * dR / ρ ^ 3 : ℝ) : ℂ))))

/-- The two line contributions add up to `(p2 + p1/ρ - m² p0/ρ²)(Y/ρ)^m`. -/
theorem polar_alg_gen (m : ℤ) (Y J : ℂ) (A B ρ : ℝ) (p0 p1 p2 : ℂ) (hY0 : Y ≠ 0)
    (hY : Y = (A : ℂ) + (B : ℂ) * J) (hJ : J ^ 2 + 1 = 0) (hρ : ρ ^ 2 = A ^ 2 + B ^ 2)
    (hρ0 : ρ ≠ 0) :
    polarEm m Y 1 ρ A B (A / ρ) 1 0 (-(m : ℂ) * J) p0 p1 p2 +
        polarEm m Y J ρ B A (B / ρ) 1 0 ((m : ℂ) * J) p0 p1 p2 =
      (p2 + p1 / (ρ : ℂ) - (m : ℂ) ^ 2 * p0 / (ρ : ℂ) ^ 2) * (Y / (ρ : ℂ)) ^ m := by
  obtain ⟨h1, h2⟩ := invRel_Gm Y J A B ρ hY0 hY hJ hρ hρ0
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  have hρ2 : (ρ : ℂ) ^ 2 = (A : ℂ) ^ 2 + (B : ℂ) ^ 2 := by exact_mod_cast hρ
  unfold polarEm
  rw [h1, h2, ← mul_add, mul_comm]
  congr 1
  linear_combination (norm := skip)
    (-((p2 / (ρ : ℂ) ^ 2 - p1 / (ρ : ℂ) ^ 3 - (m : ℂ) ^ 2 * p0 / (ρ : ℂ) ^ 4))) * hρ2 +
    ((m : ℂ) ^ 2 * p0 * ((A : ℂ) ^ 2 + (B : ℂ) ^ 2) / (ρ : ℂ) ^ 4) * hJ
  push_cast
  field_simp
  ring

/-- Laplacian as the sum of the two iterated derivatives, in terms of the first partials. -/
theorem lap_iterated_eq {Ψ : ℂ → ℂ} {y : ℂ} (hP : ContDiffAt ℝ 2 Ψ y) :
    iteratedFDeriv ℝ 2 Ψ y ![1, 1] + iteratedFDeriv ℝ 2 Ψ y ![Complex.I, Complex.I] =
      fderiv ℝ (fun w => fderiv ℝ Ψ w 1) y 1 +
        fderiv ℝ (fun w => fderiv ℝ Ψ w Complex.I) y Complex.I := by
  have h3 : Laplacian.laplacian Ψ y =
      iteratedFDeriv ℝ 2 Ψ y ![1, 1] + iteratedFDeriv ℝ 2 Ψ y ![Complex.I, Complex.I] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane Ψ) y
  rw [← h3]
  exact laplacian_eq_fderiv hP

/-- **Target.** The polar identity of order `m`. -/
theorem secSectorLap_proof : UnforcedLeray.Short.PartI.SecSectorLap := by
  intro m ψ hψ y hy
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hP : ContDiffAt ℝ 2 (Ang.ofProfile m ψ) y :=
    (secSectorSmooth_proof m ψ hψ y hy).of_le (by first | simp | exact le_top | (norm_cast; exact le_top))
  rw [lap_iterated_eq hP]
  have hl1 : HasDerivAt (fun t : ℝ => y + (t : ℂ)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_add y)
  have hlI : HasDerivAt (fun t : ℝ => y + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add y
  have hne1 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), y + (t : ℂ) ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => y + (t : ℂ)) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hy)
  have hneI : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), y + (t : ℂ) * Complex.I ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => y + (t : ℂ) * Complex.I) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hy)
  have hD : DifferentiableAt ℝ (fderiv ℝ (Ang.ofProfile m ψ)) y :=
    (hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF1 : DifferentiableAt ℝ (fun w => fderiv ℝ (Ang.ofProfile m ψ) w 1) y :=
    hD.clm_apply (differentiableAt_const _)
  have hFI : DifferentiableAt ℝ (fun w => fderiv ℝ (Ang.ofProfile m ψ) w Complex.I) y :=
    hD.clm_apply (differentiableAt_const _)
  have hX1 : HasDerivAt (fun t : ℝ => fderiv ℝ (Ang.ofProfile m ψ) (y + (t : ℂ)) 1)
      (fderiv ℝ (fun w => fderiv ℝ (Ang.ofProfile m ψ) w 1) y 1) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hF1.hasFDerivAt hl1 (by simp)
  have hXI : HasDerivAt
      (fun t : ℝ => fderiv ℝ (Ang.ofProfile m ψ) (y + (t : ℂ) * Complex.I) Complex.I)
      (fderiv ℝ (fun w => fderiv ℝ (Ang.ofProfile m ψ) w Complex.I) y Complex.I) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hFI.hasFDerivAt hlI (by simp)
  have hψ0 : HasDerivAt ψ (deriv ψ ‖y + ((0 : ℝ) : ℂ)‖) ‖y + ((0 : ℝ) : ℂ)‖ := by
    simpa using hasDerivAt_of_contDiffOn hψ hpos
  have hψ1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) ‖y + ((0 : ℝ) : ℂ)‖)
      ‖y + ((0 : ℝ) : ℂ)‖ := by
    simpa using hasDerivAt_deriv_of_contDiffOn hψ hpos
  have hρ0 : (fun t : ℝ => ‖y + (t : ℂ)‖) 0 ≠ 0 := by simpa using hpos.ne'
  have hρI0 : (fun t : ℝ => ‖y + (t : ℂ) * Complex.I‖) 0 ≠ 0 := by simpa using hpos.ne'
  have hA1 : HasDerivAt (fun t : ℝ => (y + (t : ℂ)).re) 1 0 := by
    have e : (fun t : ℝ => (y + (t : ℂ)).re) = fun t : ℝ => y.re + t := by
      funext t
      simp
    rw [e]
    exact (hasDerivAt_id (0 : ℝ)).const_add y.re
  have hB1 : HasDerivAt (fun t : ℝ => (y + (t : ℂ)).im) 0 0 := by
    have e : (fun t : ℝ => (y + (t : ℂ)).im) = fun _ : ℝ => y.im := by
      funext t
      simp
    rw [e]
    exact hasDerivAt_const 0 y.im
  have hAI1 : HasDerivAt (fun t : ℝ => (y + (t : ℂ) * Complex.I).im) 1 0 := by
    have e : (fun t : ℝ => (y + (t : ℂ) * Complex.I).im) = fun t : ℝ => y.im + t := by
      funext t
      simp
    rw [e]
    exact (hasDerivAt_id (0 : ℝ)).const_add y.im
  have hBI1 : HasDerivAt (fun t : ℝ => (y + (t : ℂ) * Complex.I).re) 0 0 := by
    have e : (fun t : ℝ => (y + (t : ℂ) * Complex.I).re) = fun _ : ℝ => y.re := by
      funext t
      simp
    rw [e]
    exact hasDerivAt_const 0 y.re
  have hG1 := lineDeriv_gen_m (ψ := ψ) (w := fun t : ℝ => y + (t : ℂ))
    (R := fun t : ℝ => ‖y + (t : ℂ)‖) (A := fun t : ℝ => (y + (t : ℂ)).re)
    (B := fun t : ℝ => (y + (t : ℂ)).im) (dw := 1) (κ := -(m : ℂ) * Complex.I)
    (dR := y.re / ‖y‖) (dA := 1) (dB := 0) m hψ0 hψ1 hl1 (hasDerivAt_norm_one hy) hA1 hB1
    hρ0 (by simpa using hy)
  simp only [Complex.ofReal_zero, add_zero] at hG1
  have hG1' : HasDerivAt (fun t : ℝ => fderiv ℝ (Ang.ofProfile m ψ) (y + (t : ℂ)) 1)
      (polarEm m y 1 ‖y‖ y.re y.im (y.re / ‖y‖) 1 0 (-(m : ℂ) * Complex.I) (ψ ‖y‖)
        (deriv ψ ‖y‖) (deriv (deriv ψ) ‖y‖)) 0 := by
    refine hG1.congr_of_eventuallyEq ?_
    filter_upwards [hne1] with t ht
    rw [fderivGm_one hψ ht]
  have hψ0I : HasDerivAt ψ (deriv ψ ‖y + ((0 : ℝ) : ℂ) * Complex.I‖)
      ‖y + ((0 : ℝ) : ℂ) * Complex.I‖ := by
    simpa using hasDerivAt_of_contDiffOn hψ hpos
  have hψ1I : HasDerivAt (deriv ψ) (deriv (deriv ψ) ‖y + ((0 : ℝ) : ℂ) * Complex.I‖)
      ‖y + ((0 : ℝ) : ℂ) * Complex.I‖ := by
    simpa using hasDerivAt_deriv_of_contDiffOn hψ hpos
  have hG2 := lineDeriv_gen_m (ψ := ψ) (w := fun t : ℝ => y + (t : ℂ) * Complex.I)
    (R := fun t : ℝ => ‖y + (t : ℂ) * Complex.I‖)
    (A := fun t : ℝ => (y + (t : ℂ) * Complex.I).im)
    (B := fun t : ℝ => (y + (t : ℂ) * Complex.I).re) (dw := Complex.I)
    (κ := (m : ℂ) * Complex.I) (dR := y.im / ‖y‖) (dA := 1) (dB := 0) m hψ0I hψ1I hlI
    (hasDerivAt_norm_I hy) hAI1 hBI1 hρI0 (by simpa using hy)
  simp only [Complex.ofReal_zero, add_zero, zero_mul] at hG2
  have hGI' : HasDerivAt
      (fun t : ℝ => fderiv ℝ (Ang.ofProfile m ψ) (y + (t : ℂ) * Complex.I) Complex.I)
      (polarEm m y Complex.I ‖y‖ y.im y.re (y.im / ‖y‖) 1 0 ((m : ℂ) * Complex.I) (ψ ‖y‖)
        (deriv ψ ‖y‖) (deriv (deriv ψ) ‖y‖)) 0 := by
    refine hG2.congr_of_eventuallyEq ?_
    filter_upwards [hneI] with t ht
    rw [fderivGm_I hψ ht]
  rw [hX1.unique hG1', hXI.unique hGI']
  have hY : y = ((y.re : ℝ) : ℂ) + ((y.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im y).symm
  have hJ : Complex.I ^ 2 + 1 = 0 := by simp [Complex.I_sq]
  have hρsq : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  have hmain := polar_alg_gen m y Complex.I y.re y.im ‖y‖ (ψ ‖y‖) (deriv ψ ‖y‖)
    (deriv (deriv ψ) ‖y‖) hy hY hJ hρsq hpos.ne'
  simp only [Ang.ofProfile, Ang.angPhase]
  exact hmain

end UnforcedLeray.Short.PartI

end
