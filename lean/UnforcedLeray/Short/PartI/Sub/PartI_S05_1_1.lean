import UnforcedLeray.Short.PartI.Sub.PartI_S05_1

/-!
# Part I, task `PartI:S05/1/1`: the polar planar Laplacian (`PolarLaplacianCore`)

Target: `polarLaplacianCore_proof : PolarLaplacianCore`, the polar identity used by
`gaussianModeLaplacian_of_core` in `PartI_S05_1.lean`. Source lines 788-803 of
`the November 2 reference manuscript`.

Method: for `y ≠ 0`, the Laplacian of `Ψ = ψ(|z|)(z/|z|)²` is `∂₁²Ψ + ∂₂²Ψ` at `y`
(Mathlib's complex-plane formula, `fderiv (fderiv Ψ)`). The first partials are the
explicit formulas of `fderiv_ofProfile_two_one/_I`. Each second partial is the derivative
along a real line through `y`, computed by `lineDeriv_gen`. The two contributions add up
to `(ψ'' + ψ'/r - 4ψ/r²)(y/r)²` (`polar_alg`, a rational identity modulo `y = a + bi`
and `r² = a² + b²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The angular-two profile is `C²` off the origin. -/
theorem contDiffAt_ofProfile_two {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {y : ℂ}
    (hy : y ≠ 0) : ContDiffAt ℝ 2 (Planar.NUE.Ang.ofProfile 2 ψ) y := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hψa : ContDiffAt ℝ ∞ ψ ‖y‖ := hψ.contDiffAt (Ioi_mem_nhds hpos)
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) y := contDiffAt_norm ℝ hy
  have hψc : ContDiffAt ℝ ∞ (fun z : ℂ => ψ ‖z‖) y := hψa.comp y hn
  have hnC : ContDiffAt ℝ ∞ (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y hn
  have hinv : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖⁻¹) y := hn.inv hpos.ne'
  have hinvC : ContDiffAt ℝ ∞ (fun z : ℂ => ((‖z‖⁻¹ : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y hinv
  have hid : ContDiffAt ℝ ∞ (fun z : ℂ => z) y := contDiffAt_id
  have hq : ContDiffAt ℝ ∞ (fun z : ℂ => z * ((‖z‖⁻¹ : ℝ) : ℂ)) y := hid.mul hinvC
  have hfun : Planar.NUE.Ang.ofProfile 2 ψ =
      fun z : ℂ => ψ ‖z‖ * (z * ((‖z‖⁻¹ : ℝ) : ℂ)) ^ 2 := by
    funext z
    rw [Planar.NUE.Ang.ofProfile, Planar.angPhase_two_eq, Complex.ofReal_inv, div_eq_mul_inv]
  rw [hfun]
  exact (hψc.mul (hq.pow 2)).of_le (by first | simp | exact_mod_cast le_top)

/-- Derivative of the profile at a positive point. -/
theorem hasDerivAt_of_contDiffOn {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {s : ℝ}
    (hs : 0 < s) : HasDerivAt ψ (deriv ψ s) s :=
  ((hψ.contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by simp)).hasDerivAt

/-- Derivative of the first derivative of the profile at a positive point. -/
theorem hasDerivAt_deriv_of_contDiffOn {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {s : ℝ}
    (hs : 0 < s) : HasDerivAt (deriv ψ) (deriv (deriv ψ) s) s := by
  have h1 : ContDiffOn ℝ 1 (deriv ψ) (Ioi 0) :=
    hψ.deriv_of_isOpen isOpen_Ioi (m := 1) (by first | simp | exact le_top)
  exact ((h1.contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by simp)).hasDerivAt

/-- The first Cartesian partial of `Ψ = ψ(|z|) e^{2iθ}` off the origin. -/
theorem fderiv_one_explicit {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {w : ℂ} (hw : w ≠ 0) :
    fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) w 1 =
      (w / (‖w‖ : ℂ)) ^ 2 * (deriv ψ ‖w‖ * ((w.re / ‖w‖ : ℝ) : ℂ) -
        2 * Complex.I * ψ ‖w‖ / (‖w‖ : ℂ) * ((w.im / ‖w‖ : ℝ) : ℂ)) := by
  rw [Planar.fderiv_ofProfile_two_one hw (hasDerivAt_of_contDiffOn hψ (norm_pos_iff.2 hw)),
    Planar.angPhase_two_eq]

/-- The second Cartesian partial direction `I` off the origin. -/
theorem fderiv_I_explicit {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ∞ ψ (Ioi 0)) {w : ℂ} (hw : w ≠ 0) :
    fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) w Complex.I =
      (w / (‖w‖ : ℂ)) ^ 2 * (deriv ψ ‖w‖ * ((w.im / ‖w‖ : ℝ) : ℂ) +
        2 * Complex.I * ψ ‖w‖ / (‖w‖ : ℂ) * ((w.re / ‖w‖ : ℝ) : ℂ)) := by
  rw [Planar.fderiv_ofProfile_two_I hw (hasDerivAt_of_contDiffOn hψ (norm_pos_iff.2 hw)),
    Planar.angPhase_two_eq]

/-- Complex-plane Laplacian as the sum of the two second partials of the gradient. -/
theorem laplacian_eq_fderiv {Ψ : ℂ → ℂ} {y : ℂ} (hP : ContDiffAt ℝ 2 Ψ y) :
    Laplacian.laplacian Ψ y =
      fderiv ℝ (fun w => fderiv ℝ Ψ w 1) y 1 +
        fderiv ℝ (fun w => fderiv ℝ Ψ w Complex.I) y Complex.I := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Ψ) y :=
    (hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun w => fderiv ℝ Ψ w 1) y 1 = fderiv ℝ (fderiv ℝ Ψ) y 1 1 := by
    rw [fderiv_clm_apply hD (differentiableAt_const (1 : ℂ))]
    simp
  have h2 : fderiv ℝ (fun w => fderiv ℝ Ψ w Complex.I) y Complex.I =
      fderiv ℝ (fderiv ℝ Ψ) y Complex.I Complex.I := by
    rw [fderiv_clm_apply hD (differentiableAt_const Complex.I)]
    simp
  have h3 : Laplacian.laplacian Ψ y =
      iteratedFDeriv ℝ 2 Ψ y ![1, 1] + iteratedFDeriv ℝ 2 Ψ y ![Complex.I, Complex.I] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane Ψ) y
  rw [h3, h1, h2, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp

/-- `d/dt ‖y + t‖ = Re y / |y|` at `t = 0`. -/
theorem hasDerivAt_norm_one {y : ℂ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖y + (t : ℂ)‖) (y.re / ‖y‖) 0 := by
  have hn : ‖y‖ = √(y.re ^ 2 + y.im ^ 2) := Complex.norm_eq_sqrt_sq_add_sq y
  have hfun : (fun t : ℝ => ‖y + (t : ℂ)‖) = fun t : ℝ => √((y.re + t) ^ 2 + y.im ^ 2) := by
    funext t
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp
  have h1 : HasDerivAt (fun t : ℝ => y.re + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add y.re
  have h2 : HasDerivAt (fun t : ℝ => (y.re + t) ^ 2 + y.im ^ 2) (2 * y.re) 0 :=
    ((h1.pow 2).add_const (y.im ^ 2)).congr_deriv (by norm_num)
  have hval : (y.re + 0) ^ 2 + y.im ^ 2 ≠ 0 := by
    intro h0
    rw [add_zero] at h0
    have h00 : ‖y‖ = 0 := by rw [hn, h0, Real.sqrt_zero]
    exact hy (norm_eq_zero.1 h00)
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hs := h2.sqrt hval
  rw [hfun]
  refine hs.congr_deriv ?_
  rw [add_zero, ← hn]
  field_simp

/-- `d/dt ‖y + t i‖ = Im y / |y|` at `t = 0`. -/
theorem hasDerivAt_norm_I {y : ℂ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖y + (t : ℂ) * Complex.I‖) (y.im / ‖y‖) 0 := by
  have hn : ‖y‖ = √(y.re ^ 2 + y.im ^ 2) := Complex.norm_eq_sqrt_sq_add_sq y
  have hfun : (fun t : ℝ => ‖y + (t : ℂ) * Complex.I‖) =
      fun t : ℝ => √(y.re ^ 2 + (y.im + t) ^ 2) := by
    funext t
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp
  have h1 : HasDerivAt (fun t : ℝ => y.im + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add y.im
  have h2 : HasDerivAt (fun t : ℝ => y.re ^ 2 + (y.im + t) ^ 2) (2 * y.im) 0 :=
    ((h1.pow 2).const_add (y.re ^ 2)).congr_deriv (by norm_num)
  have hval : y.re ^ 2 + (y.im + 0) ^ 2 ≠ 0 := by
    intro h0
    rw [add_zero] at h0
    have h00 : ‖y‖ = 0 := by rw [hn, h0, Real.sqrt_zero]
    exact hy (norm_eq_zero.1 h00)
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hs := h2.sqrt hval
  rw [hfun]
  refine hs.congr_deriv ?_
  rw [add_zero, ← hn]
  field_simp

/-- The explicit derivative value used for the line computation. -/
def polarE (w0 dw : ℂ) (ρ A0 B0 dR dA dB : ℝ) (κ p0 p1 p2 : ℂ) : ℂ :=
  (2 * w0 * dw / (ρ : ℂ) ^ 2 - 2 * w0 ^ 2 * (dR : ℂ) / (ρ : ℂ) ^ 3) *
      (p1 * ((A0 / ρ : ℝ) : ℂ) + κ * p0 * ((B0 / ρ ^ 2 : ℝ) : ℂ)) +
    (w0 / (ρ : ℂ)) ^ 2 *
      (p2 * (dR : ℂ) * ((A0 / ρ : ℝ) : ℂ) +
        p1 * ((dA / ρ - A0 * dR / ρ ^ 2 : ℝ) : ℂ) +
        κ * (p1 * (dR : ℂ) * ((B0 / ρ ^ 2 : ℝ) : ℂ) +
          p0 * ((dB / ρ ^ 2 - 2 * B0 * dR / ρ ^ 3 : ℝ) : ℂ)))

/-- Derivative along a line of `(w/R)² (ψ'(R) A/R + κ ψ(R) B/R²)`, with `R = R(t)` real. -/
theorem lineDeriv_gen {ψ : ℝ → ℂ} {w : ℝ → ℂ} {R A B : ℝ → ℝ} {dw κ : ℂ} {dR dA dB : ℝ}
    (hψ0 : HasDerivAt ψ (deriv ψ (R 0)) (R 0))
    (hψ1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) (R 0)) (R 0))
    (hw : HasDerivAt w dw 0) (hR : HasDerivAt R dR 0) (hA : HasDerivAt A dA 0)
    (hB : HasDerivAt B dB 0) (hρ : R 0 ≠ 0) :
    HasDerivAt (fun t : ℝ => (w t / ((R t : ℝ) : ℂ)) ^ 2 *
        (deriv ψ (R t) * ((A t / R t : ℝ) : ℂ) +
          κ * ψ (R t) * ((B t / (R t) ^ 2 : ℝ) : ℂ)))
      (polarE (w 0) dw (R 0) (A 0) (B 0) dR dA dB κ (ψ (R 0)) (deriv ψ (R 0))
        (deriv (deriv ψ) (R 0))) 0 := by
  have hρC : ((R 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ
  have hRc : HasDerivAt (fun t : ℝ => ((R t : ℝ) : ℂ)) (dR : ℂ) 0 := hR.ofReal_comp
  have hP : HasDerivAt (fun t : ℝ => w t / ((R t : ℝ) : ℂ)) _ 0 := hw.div hRc hρC
  have hPow := hP.pow 2
  have hψR : HasDerivAt (fun t => ψ (R t)) (dR • deriv ψ (R 0)) 0 := hψ0.scomp 0 hR
  have hψ'R : HasDerivAt (fun t => deriv ψ (R t)) (dR • deriv (deriv ψ) (R 0)) 0 :=
    hψ1.scomp 0 hR
  have hAR := (hA.div hR hρ).ofReal_comp
  have hBR := (hB.div (hR.pow 2) (pow_ne_zero 2 hρ)).ofReal_comp
  have hQ := (hψ'R.mul hAR).add ((hψR.const_mul κ).mul hBR)
  have hG := hPow.mul hQ
  refine hG.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply, Complex.real_smul]
  unfold polarE
  push_cast
  field_simp

/-- Numerator (first cofactor) of the algebraic identity. -/
def polarN1 (A B ρ J p0 p1 p2 : ℂ) : ℂ :=
  A ^ 2 * B ^ 2 * ρ * p2 - 3 * A ^ 2 * B ^ 2 * p1 + 4 * A ^ 2 * ρ * p0 + 4 * A * B * J * ρ * p0 +
    B ^ 4 * ρ * p2 - 3 * B ^ 4 * p1 - B ^ 2 * ρ ^ 3 * p2 + 3 * B ^ 2 * ρ ^ 2 * p1

/-- Numerator (second cofactor) of the algebraic identity. -/
def polarN2 (A B ρ J p0 p1 p2 : ℂ) : ℂ :=
  -A ^ 2 * ρ * p2 + 3 * A ^ 2 * p1 - 2 * A * B * J * ρ * p2 + 6 * A * B * J * p1 +
    B ^ 2 * ρ * p2 - 3 * B ^ 2 * p1

/-- Algebraic identity: the two line contributions add up to `(ψ'' + ψ'/r - 4ψ/r²)(y/r)²`. -/
theorem polar_alg (Y : ℂ) (A B ρ : ℝ) (J p0 p1 p2 : ℂ) (hY : Y = (A : ℂ) + (B : ℂ) * J)
    (hJ : J ^ 2 + 1 = 0) (hρ : ρ ^ 2 = A ^ 2 + B ^ 2) (hρ0 : ρ ≠ 0) :
    polarE Y 1 ρ A B (A / ρ) 1 0 (-2 * J) p0 p1 p2 +
        polarE Y J ρ B A (B / ρ) 1 0 (2 * J) p0 p1 p2 =
      (p2 + p1 / (ρ : ℂ) - 4 * p0 / (ρ : ℂ) ^ 2) * (Y / (ρ : ℂ)) ^ 2 := by
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  have hρ2 : (ρ : ℂ) ^ 2 - (A : ℂ) ^ 2 - (B : ℂ) ^ 2 = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hρ
    push_cast at h
    linear_combination h
  have key : polarE Y 1 ρ A B (A / ρ) 1 0 (-2 * J) p0 p1 p2 +
        polarE Y J ρ B A (B / ρ) 1 0 (2 * J) p0 p1 p2 -
      (p2 + p1 / (ρ : ℂ) - 4 * p0 / (ρ : ℂ) ^ 2) * (Y / (ρ : ℂ)) ^ 2 =
      (polarN1 (A : ℂ) (B : ℂ) (ρ : ℂ) J p0 p1 p2 * (J ^ 2 + 1) +
        polarN2 (A : ℂ) (B : ℂ) (ρ : ℂ) J p0 p1 p2 * ((ρ : ℂ) ^ 2 - (A : ℂ) ^ 2 - (B : ℂ) ^ 2)) /
        (ρ : ℂ) ^ 5 := by
    subst hY
    unfold polarE polarN1 polarN2
    push_cast
    field_simp
    ring
  simp only [hJ, hρ2, mul_zero, add_zero, zero_div] at key
  linear_combination key

/-- **Target.** The polar identity `ΔΨ = (ψ'' + ψ'/r - 4ψ/r²)` on the angular-two sector. -/
theorem polarLaplacianCore_proof : PolarLaplacianCore := by
  intro ψ hψ y hy
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hP : ContDiffAt ℝ 2 (Planar.NUE.Ang.ofProfile 2 ψ) y := contDiffAt_ofProfile_two hψ hy
  rw [laplacian_eq_fderiv hP]
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
  have hD : DifferentiableAt ℝ (fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ)) y :=
    (hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF1 : DifferentiableAt ℝ (fun w => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) w 1) y :=
    hD.clm_apply (differentiableAt_const _)
  have hFI : DifferentiableAt ℝ
      (fun w => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) w Complex.I) y :=
    hD.clm_apply (differentiableAt_const _)
  have hX1 : HasDerivAt (fun t : ℝ => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) (y + (t : ℂ)) 1)
      (fderiv ℝ (fun w => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) w 1) y 1) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hF1.hasFDerivAt hl1 (by simp)
  have hXI : HasDerivAt
      (fun t : ℝ => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) (y + (t : ℂ) * Complex.I) Complex.I)
      (fderiv ℝ (fun w => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) w Complex.I) y Complex.I) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hFI.hasFDerivAt hlI (by simp)
  -- the values of ψ and its derivatives at the base point
  have hψ0 : HasDerivAt ψ (deriv ψ ‖y + ((0 : ℝ) : ℂ)‖) ‖y + ((0 : ℝ) : ℂ)‖ := by
    simpa using hasDerivAt_of_contDiffOn hψ hpos
  have hψ1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) ‖y + ((0 : ℝ) : ℂ)‖) ‖y + ((0 : ℝ) : ℂ)‖ := by
    simpa using hasDerivAt_deriv_of_contDiffOn hψ hpos
  have hρ0 : (fun t : ℝ => ‖y + (t : ℂ)‖) 0 ≠ 0 := by simpa using hpos.ne'
  have hρI0 : (fun t : ℝ => ‖y + (t : ℂ) * Complex.I‖) 0 ≠ 0 := by simpa using hpos.ne'
  -- the line derivative in the real direction
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
  -- real direction: value and eventual identity with the explicit partial
  have hG1 := lineDeriv_gen (ψ := ψ) (w := fun t : ℝ => y + (t : ℂ))
    (R := fun t : ℝ => ‖y + (t : ℂ)‖) (A := fun t : ℝ => (y + (t : ℂ)).re)
    (B := fun t : ℝ => (y + (t : ℂ)).im) (dw := 1) (κ := -2 * Complex.I)
    (dR := y.re / ‖y‖) (dA := 1) (dB := 0) hψ0 hψ1 hl1 (hasDerivAt_norm_one hy) hA1 hB1 hρ0
  simp only [Complex.ofReal_zero, add_zero] at hG1
  have hG1' : HasDerivAt (fun t : ℝ => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) (y + (t : ℂ)) 1)
      (polarE y 1 ‖y‖ y.re y.im (y.re / ‖y‖) 1 0 (-2 * Complex.I) (ψ ‖y‖) (deriv ψ ‖y‖)
        (deriv (deriv ψ) ‖y‖)) 0 := by
    refine hG1.congr_of_eventuallyEq ?_
    filter_upwards [hne1] with t ht
    rw [fderiv_one_explicit hψ ht]
    push_cast
    ring
  -- imaginary direction
  have hψ0I : HasDerivAt ψ (deriv ψ ‖y + ((0 : ℝ) : ℂ) * Complex.I‖)
      ‖y + ((0 : ℝ) : ℂ) * Complex.I‖ := by
    simpa using hasDerivAt_of_contDiffOn hψ hpos
  have hψ1I : HasDerivAt (deriv ψ) (deriv (deriv ψ) ‖y + ((0 : ℝ) : ℂ) * Complex.I‖)
      ‖y + ((0 : ℝ) : ℂ) * Complex.I‖ := by
    simpa using hasDerivAt_deriv_of_contDiffOn hψ hpos
  have hG2 := lineDeriv_gen (ψ := ψ) (w := fun t : ℝ => y + (t : ℂ) * Complex.I)
    (R := fun t : ℝ => ‖y + (t : ℂ) * Complex.I‖) (A := fun t : ℝ => (y + (t : ℂ) * Complex.I).im)
    (B := fun t : ℝ => (y + (t : ℂ) * Complex.I).re) (dw := Complex.I) (κ := 2 * Complex.I)
    (dR := y.im / ‖y‖) (dA := 1) (dB := 0) hψ0I hψ1I hlI (hasDerivAt_norm_I hy) hAI1 hBI1 hρI0
  simp only [Complex.ofReal_zero, add_zero, zero_mul] at hG2
  have hGI' : HasDerivAt
      (fun t : ℝ => fderiv ℝ (Planar.NUE.Ang.ofProfile 2 ψ) (y + (t : ℂ) * Complex.I) Complex.I)
      (polarE y Complex.I ‖y‖ y.im y.re (y.im / ‖y‖) 1 0 (2 * Complex.I) (ψ ‖y‖) (deriv ψ ‖y‖)
        (deriv (deriv ψ) ‖y‖)) 0 := by
    refine hG2.congr_of_eventuallyEq ?_
    filter_upwards [hneI] with t ht
    rw [fderiv_I_explicit hψ ht]
    push_cast
    ring
  rw [hX1.unique hG1', hXI.unique hGI']
  have hY : y = ((y.re : ℝ) : ℂ) + ((y.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im y).symm
  have hJ : Complex.I ^ 2 + 1 = 0 := by simp [Complex.I_sq]
  have hρsq : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  have hmain := polar_alg y y.re y.im ‖y‖ Complex.I (ψ ‖y‖) (deriv ψ ‖y‖) (deriv (deriv ψ) ‖y‖)
    hY hJ hρsq hpos.ne'
  simp only [Planar.NUE.Ang.ofProfile, B0034.radialDelta2, Planar.angPhase_two_eq]
  linear_combination hmain

end UnforcedLeray.Short.PartI

end
