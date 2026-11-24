import UnforcedLeray.Cons.C01ReferenceChoice.Adjoint
import UnforcedLeray.Lib.PlanarSectorsB.Transfer
import UnforcedLeray.Lib.PlanarSpectralB.Eigenfunctional
import UnforcedLeray.Lib.PlanarSpectralB.XGSpectrum

/-!
# Step C1, part G3a: the direct–adjoint pairing `J_q` is nonzero

`paper/main.tex` line 1518 (blueprint unit B0096: "Algebraic simplicity implies
`⟨q,h_X⟩ ≠ 0`") and `eq:st18-t00108` (lines 1949–1960, unit B0127):
`J_q = ∫₀^∞ h²/k r dr = ⟨q, h_X⟩_{X_G}` "is nonzero by algebraic simplicity and the closed-range
argument".

The proof here follows the compiled bypass B2(c) of the scoping note (the index lemma) instead
of the closed-range argument. The eigenvorticity `h` of the whole-line mode is an eigenvector of
the sector generator on `L²_2` (`L²((0,∞), 2πr(1+r²)²dr)`, which contains `X_G`:
`Planar.profileMeasure_two_le`). Its transfer `f = √W J ψ(e^t)/(Ω - c)` (`Planar.transfer`,
`eq:st18-t00061`) is a phase-speed eigenvector, `C₂f = cf` (`Planar.phaseSpeedOp_transfer`), and
the index lemma gives `∫ f (1 - N₂)f dt ≠ 0` (`Planar.inner_star_B_ne_zero_of_eq_two`). Since
`C₂ = a_* + J(1 - N₂)`, `J(1 - N₂)f = (c - a_*)f`, so
`f(1 - N₂)f = (c - a_*)WJψ²/(Ω - c)² = -(c - a_*)e^{2t}k(e^t)φ(e^t)²/(Ω - c)²`
(`W J = -e^{2t}k(e^t)`, `Planar.Wlog_mul_J`), and the substitution `r = e^t` turns its integral
into `-(c - a_*)J_q`.

Main declarations (namespace `UnforcedLeray.Cons.C01`): `memLp_xG_of_memXG`,
`memLp_profile_two_of_memXG`, **`directAdjointPairing_ne_zero`**.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Cons.C01

open UnforcedLeray.ComplexODEC

variable {c : ℂ} {F : ℝ → ℂ}

theorem radialGaussianWeight_inv_eq (r : ℝ) :
    (B0010.radialGaussianWeight r)⁻¹ = Blueprint.Planar.gaussianWeightInv r := by
  unfold B0010.radialGaussianWeight GaussianVortex.radialOmega Blueprint.Planar.gaussianWeightInv
  rw [mul_inv, inv_inv, ← Real.exp_neg, neg_neg]

/-- The blueprint's `X_G` membership is membership in the compiled `B0010.XG`. -/
theorem memLp_xG_of_memXG {f : Blueprint.Planar.Profile} (hf : Blueprint.Planar.MemXG f) :
    MemLp f 2 B0010.xGMeasure := by
  rw [B0010.memLp_iff_integrableOn hf.measurable]
  refine IntegrableOn.congr_fun hf.integrable (fun r _ => ?_) measurableSet_Ioi
  rw [radialGaussianWeight_inv_eq]
  ring

/-- `X_G ⊂ L²_2` (`Planar.profileMeasure_two_le`). -/
theorem memLp_profile_two_of_memXG {f : Blueprint.Planar.Profile}
    (hf : Blueprint.Planar.MemXG f) : MemLp f 2 (Planar.profileMeasure 2) :=
  (memLp_xG_of_memXG hf).of_measure_le_smul (by simp) Planar.profileMeasure_two_le

/-- **`J_q ≠ 0`** (line 1518, unit B0096; `eq:st18-t00108`, unit B0127) for the eigenvorticity
of every whole-line growing mode, by the index lemma for the transferred phase-speed
eigenvector. -/
theorem directAdjointPairing_ne_zero (hF : WholeLineData c F) : directAdjointPairing c F ≠ 0 := by
  have hc : c.im ≠ 0 := hF.im_ne_zero
  have hM : (1 : ℝ) < 2 := by norm_num
  have hn : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  have hmem := memLp_profile_two_of_memXG (memXG_modeVort hF)
  set w : Planar.ProfL2 2 := hmem.toLp _ with hw
  have hw_ae : (w : ℝ → ℂ) =ᵐ[Planar.profileMeasure 2] modeVort c F := hmem.coeFn_toLp
  have hw_vol : (w : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] modeVort c F :=
    (Planar.ac_profileMeasure 2).ae_le hw_ae
  have hG : ∀ r, Planar.greenN 2 w r = Planar.greenN 2 (modeVort c F) r := by
    intro r
    unfold Planar.greenN
    congr 1
    refine integral_congr_ae (hw_vol.mono fun ρ hρ => ?_)
    simp only [hρ]
  have heig : ∀ᵐ r ∂Planar.profileMeasure 2,
      (GaussianVortex.radialOmega r : ℂ) * w r -
        (GaussianVortex.radialK r : ℂ) * Planar.greenN 2 w r = c * w r := by
    filter_upwards [hw_ae, Planar.ae_profile_pos 2] with r h1 h2
    rw [h1, hG, ← mode_eq_green hF r h2]
    have hne := ofReal_sub_ne_zero hc (GaussianVortex.radialOmega r)
    rw [modeVort_eq]
    field_simp
    ring
  set f := Planar.transfer hM 2 hc w with hf_def
  have hf : Sturm.phaseSpeedOp hn f = c • f := Planar.phaseSpeedOp_transfer hM hn hc heig
  have hf0 : f ≠ 0 := by
    intro h0
    have hw0 := Planar.eq_zero_of_transfer_eq_zero hM hc heig h0
    apply modeVort_not_ae_zero hF
    have h1 : (w : ℝ → ℂ) =ᵐ[Planar.profileMeasure 2] 0 := by
      rw [hw0]
      exact Lp.coeFn_zero _ _ _
    exact (Planar.ac_profileMeasure 2).ae_le (hw_ae.symm.trans h1)
  have hB := Planar.inner_star_B_ne_zero_of_eq_two (by norm_num : ((2 : ℕ) : ℝ) = 2) hn hc hf0 hf
  rw [← Sturm.integral_mul_eq_inner_star] at hB
  set g := (1 - Sturm.birmanSchwingerOperator hn) f with hg
  have hJg : Sturm.JOp g = c • f - (Sturm.aStar : ℂ) • f := by
    have h := hf
    rw [Sturm.phaseSpeedOp_eq] at h
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at h
    rw [← h]
    abel
  have hJg_ae : ∀ᵐ t : ℝ, ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) * g t =
      (c - Sturm.aStar) * f t := by
    filter_upwards [Sturm.coeFn_JOp g, Lp.coeFn_sub (c • f) ((Sturm.aStar : ℂ) • f),
      Lp.coeFn_smul c f, Lp.coeFn_smul (Sturm.aStar : ℂ) f] with t h1 h2 h3 h4
    rw [← h1, hJg, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  have hft := Planar.coeFn_transfer hM 2 hc w
  set G : ℝ → ℂ := fun ρ => modeVort c F ρ * adjointKernel c F ρ * ρ with hGdef
  have hpt : ∀ᵐ t : ℝ, f t * g t = -(c - Sturm.aStar) * (Real.exp t • G (Real.exp t)) := by
    filter_upwards [hJg_ae, hft] with t h1 h2
    have he := Real.exp_pos t
    have hψ : Planar.greenN 2 w (Real.exp t) = modeRadial F (Real.exp t) := by
      rw [hG, mode_eq_green hF _ he]
    have hD : (Sturm.neutralOmega t : ℂ) = (GaussianVortex.radialOmega (Real.exp t) : ℂ) := by
      rw [GaussianVortex.radialOmega_exp]
    have hne := ofReal_sub_ne_zero hc (GaussianVortex.radialOmega (Real.exp t))
    have hWJ : ((Sturm.sqrtPotential t : ℝ) : ℂ) ^ 2 *
        ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) =
        ((-(Real.exp (2 * t) * GaussianVortex.radialK (Real.exp t)) : ℝ) : ℂ) := by
      rw [← Planar.Wlog_mul_J, ← Planar.sqrtPotential_sq]
      push_cast
      ring
    have h2' : f t = ((Sturm.sqrtPotential t : ℝ) : ℂ) *
        ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) * modeRadial F (Real.exp t) /
          ((GaussianVortex.radialOmega (Real.exp t) : ℂ) - c) := by
      rw [h2, Planar.transferFun, hψ, hD]
    have hexp : Real.exp (2 * t) = Real.exp t * Real.exp t := by
      rw [← Real.exp_add]
      ring_nf
    calc f t * g t
        = ((Sturm.sqrtPotential t : ℝ) : ℂ) * modeRadial F (Real.exp t) /
            ((GaussianVortex.radialOmega (Real.exp t) : ℂ) - c) *
          (((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) * g t) := by
          rw [h2']
          ring
      _ = ((Sturm.sqrtPotential t : ℝ) : ℂ) * modeRadial F (Real.exp t) /
            ((GaussianVortex.radialOmega (Real.exp t) : ℂ) - c) *
          ((c - Sturm.aStar) * f t) := by rw [h1]
      _ = (c - Sturm.aStar) * (((Sturm.sqrtPotential t : ℝ) : ℂ) ^ 2 *
            ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ)) * modeRadial F (Real.exp t) ^ 2 /
            ((GaussianVortex.radialOmega (Real.exp t) : ℂ) - c) ^ 2 := by
          rw [h2']
          field_simp
      _ = -(c - Sturm.aStar) * (Real.exp t • G (Real.exp t)) := by
          rw [hWJ, hGdef]
          simp only [Complex.real_smul]
          rw [modeVort_eq, adjointKernel, hexp]
          push_cast
          field_simp
  have hint : ∫ t, f t * g t = -(c - Sturm.aStar) * directAdjointPairing c F := by
    rw [integral_congr_ae hpt, integral_const_mul, Planar.integral_comp_exp_univ]
    rfl
  intro hJ0
  apply hB
  rw [hint, hJ0, mul_zero]

end UnforcedLeray.Cons.C01
