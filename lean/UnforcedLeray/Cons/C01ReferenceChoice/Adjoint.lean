import UnforcedLeray.Cons.C01ReferenceChoice.Eigenpair
import UnforcedLeray.Cons.C01ReferenceChoice.Quadrupole

/-!
# Step C1, part G3a/G4: the explicit adjoint eigenvector and the nonzero input `ℓ(H)`

`paper/main.tex`:
* the explicit unnormalized adjoint `h_X = G ψ̄_r/(Ω - c̄) e^{2iϑ}`, `L₀^*h_X = λ̄h_X`
  (`eq:st18-t00066`, lines 1479–1490, blueprint unit B0092): "The Rayleigh equation gives
  `R(kh_u) = ψ̄_r` ... Thus `(Ω - Rk)h_u = c̄h_u`, which is precisely the unweighted radial
  adjoint equation. Multiplication by `G` transfers it to `X_G`";
* the normalization `ℓ(f) = ⟨f,q†⟩_{X_G}`, `ℓ(q) = 1` (`eq:st18-t00012`, G3a, unit B0099),
  possible because `J_q = ⟨q,h_X⟩ ≠ 0` (line 1518, unit B0096; `eq:st18-t00108`);
* the explicit eigenfunctional `ℓ(f) = J_q⁻¹∫ h f₂/k r dr` and `ℓ(H) = M_q/J_q ≠ 0`
  (`eq:st18-t00109`, lines 1949–1968, unit B0127; G4, unit B0134).

With `φ = Rh` the radial streamfunction of the whole-line mode, `u = φ/(Ω - c)` (so that
`h = ku` and `φ = (Ω - c)u`), this file defines `q† = G ū / J̄` with `G = 1/gaussianWeightInv`
and `J = J_q = ∫ h u r dr`, so that `⟨f, q†⟩_{X_G} = J⁻¹∫ f u r dr`. It proves, assuming only
`J ≠ 0`:
* `isAdjointEigenvector_adjointMode`: `q†` is an `X_G`-adjoint eigenvector of `L₀` with
  `⟨q,q†⟩ = 1`. The left-eigen identity is the symmetry of the Green operator
  (`Planar.integral_greenN_mul_symm`) with `R(ku) = Rh = φ` (O9, `mode_eq_green`):
  `∫ (L₀f) u r = -2i∫Ωfur + 2i∫(Rf)hr = -2i∫Ωfur + 2i∫fφr = -2ic∫fur`;
* `strainCoupling_adjointMode`: `ℓ(H) = M_q/J` with `M_q = 𝔐(h) ≠ 0` (O11), so `ℓ(H) ≠ 0`.

Main declarations (namespace `UnforcedLeray.Cons.C01`): `adjointKernel`,
`directAdjointPairing` (`J_q`), `adjointMode` (`q†`), `wprof_of_memXG`,
`gaussianPairing_adjointMode`, `memXG_adjointMode`, **`isAdjointEigenvector_adjointMode`**,
**`strainCoupling_adjointMode_ne_zero`**.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Cons.C01

open UnforcedLeray.ComplexODEC Blueprint.Planar

variable {c : ℂ} {F : ℝ → ℂ}

/-- The unweighted adjoint kernel `u = φ/(Ω - c)` (the profile `h_u` of line 1487 before
conjugation). -/
def adjointKernel (c : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  modeRadial F r / ((GaussianVortex.radialOmega r : ℂ) - c)

/-- The direct–adjoint pairing `J_q = ∫₀^∞ h²/k r dr = ∫₀^∞ h u r dr` (`eq:st18-t00108`;
`h/k = ψ/(Ω - c) = u`, line 1957). -/
def directAdjointPairing (c : ℂ) (F : ℝ → ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), modeVort c F r * adjointKernel c F r * r

/-- The normalized `X_G`-adjoint eigenvector `q† = h_X/J̄`, `h_X = Gū` (`eq:st18-t00066`,
`eq:st18-t00012`). -/
def adjointMode (c : ℂ) (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  conj (adjointKernel c F r) / (gaussianWeightInv r : ℂ) / conj (directAdjointPairing c F)

theorem radialOmega_le_one (r : ℝ) : GaussianVortex.radialOmega r ≤ 1 := by
  unfold GaussianVortex.radialOmega
  rw [Real.exp_le_one_iff]
  have := sq_nonneg r
  linarith

theorem radialOmega_nonneg (r : ℝ) : 0 ≤ GaussianVortex.radialOmega r :=
  (Real.exp_pos _).le

/-- `‖u‖ ≤ M/|Im c|` when `‖F‖ ≤ M` (`|Ω - c| ≥ |Im c|`). -/
theorem norm_adjointKernel_le (hc : c.im ≠ 0) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t, ‖F t‖ ≤ M)
    (r : ℝ) : ‖adjointKernel c F r‖ ≤ M / |c.im| := by
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  rw [adjointKernel, norm_div]
  exact div_le_div₀ hM0 (hM _) hpos (abs_im_le_norm_ofReal_sub c _)

theorem continuousOn_adjointKernel (hF : WholeLineData c F) :
    ContinuousOn (adjointKernel c F) (Ioi 0) := by
  have h1 := continuousOn_modeRadial hF
  have h2 : Continuous fun r : ℝ => (GaussianVortex.radialOmega r : ℂ) - c := by
    unfold GaussianVortex.radialOmega
    fun_prop
  exact h1.div h2.continuousOn fun r _ => ofReal_sub_ne_zero hF.im_ne_zero _

/-- `h = ku`. -/
theorem modeVort_eq_mul (c : ℂ) (F : ℝ → ℂ) (r : ℝ) :
    modeVort c F r = (GaussianVortex.radialK r : ℂ) * adjointKernel c F r := by
  rw [modeVort_eq, adjointKernel, mul_div_assoc]

/-- `φ = (Ω - c)u`. -/
theorem modeRadial_eq_mul (hc : c.im ≠ 0) (F : ℝ → ℂ) (r : ℝ) :
    modeRadial F r = ((GaussianVortex.radialOmega r : ℂ) - c) * adjointKernel c F r := by
  rw [adjointKernel, mul_div_assoc', mul_comm, mul_div_assoc, div_self (ofReal_sub_ne_zero hc (GaussianVortex.radialOmega r)),
    mul_one]

/-! ## `X_G ⊂ WProf` and the sup bound of the Green inverse -/

/-- `r/G⁻¹(r) = r G(r)` is integrable on `(0, ∞)`. -/
theorem integrableOn_id_div_weight :
    IntegrableOn (fun r : ℝ => r / gaussianWeightInv r) (Ioi 0) := by
  refine IntegrableOn.congr_fun
    ((integrableOn_pow_mul_gauss_quarter 1).const_mul (4 * Real.pi)⁻¹)
    (fun r _ => ?_) measurableSet_Ioi
  simp only [gaussianWeightInv, pow_one]
  rw [Real.exp_neg]
  field_simp

/-- `X_G` profiles are admissible Green data: `r f ∈ L¹(0, ∞)`. -/
theorem wprof_of_memXG {f : Profile} (hf : MemXG f) : B0011.WProf f := by
  refine ⟨hf.measurable, ?_⟩
  have hb : IntegrableOn (fun r : ℝ => 1 / 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) +
      1 / (2 * 1) * (r / gaussianWeightInv r)) (Ioi 0) :=
    (hf.integrable.const_mul _).add (integrableOn_id_div_weight.const_mul _)
  refine hb.mono' ?_ ?_
  · exact continuous_id.aestronglyMeasurable.mul hf.measurable.norm
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hw := gaussianWeightInv_pos r
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine le_of_sq_eq_mul (by positivity) (by positivity) (by positivity) ?_ one_pos
    field_simp

/-- `|R f(r)| ≤ ¼∫ ρ|f|` for `r > 0`. -/
theorem norm_greenN_two_le {f : Profile} (hf : B0011.WProf f) (r : ℝ) (hr : 0 < r) :
    ‖Planar.greenN 2 f r‖ ≤ 1 / 4 * ∫ ρ in Ioi (0 : ℝ), ρ * ‖f ρ‖ := by
  unfold Planar.greenN
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have h4 : |((2 * ((2 : ℕ) : ℝ))⁻¹ : ℝ)| = 1 / 4 := by norm_num
  rw [h4]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hpt : ∀ ρ : ℝ, 0 < ρ →
      ‖(((min r ρ / max r ρ) ^ 2 : ℝ) : ℂ) * f ρ * (ρ : ℂ)‖ ≤ ρ * ‖f ρ‖ := by
    intro ρ hρ0
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg hρ0.le]
    have := Planar.norm_minmax_pow_le (n := 2) hr hρ0
    calc ‖(((min r ρ / max r ρ) ^ 2 : ℝ) : ℂ)‖ * ‖f ρ‖ * ρ ≤ 1 * ‖f ρ‖ * ρ := by gcongr
      _ = ρ * ‖f ρ‖ := by ring
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ?_ hf.int measurableSet_Ioi fun ρ hρ => hpt ρ hρ
  refine hf.int.mono' ?_ ?_
  · exact ((((Planar.measurable_minmax_pow 2).comp (measurable_const.prodMk measurable_id)
      ).aestronglyMeasurable.mul hf.meas).mul
      (Complex.continuous_ofReal.aestronglyMeasurable)).norm
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => ?_
    rw [norm_norm]
    exact hpt ρ hρ

theorem continuousOn_greenN_two {f : Profile} (hf : B0011.WProf f) :
    ContinuousOn (Planar.greenN 2 f) (Ioi 0) := by
  obtain ⟨ψ', hd, -, -⟩ := Planar.isRadialPoissonSol_greenN (n := 2) (by norm_num) hf
  exact fun r hr => (hd r hr).continuousAt.continuousWithinAt

/-! ## The pairing with `q†` -/

/-- `⟨f, q†⟩_{X_G} = J⁻¹∫₀^∞ f u r dr` (no convergence needed). -/
theorem gaussianPairing_adjointMode (hJ : directAdjointPairing c F ≠ 0) (f : Profile) :
    gaussianPairing f (adjointMode c F) =
      (directAdjointPairing c F)⁻¹ * ∫ r in Ioi (0 : ℝ), f r * adjointKernel c F r * r := by
  unfold gaussianPairing adjointMode
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  have hw := (gaussianWeightInv_pos r).ne'
  have hw' : (gaussianWeightInv r : ℂ) ≠ 0 := by exact_mod_cast hw
  have hJ' : conj (directAdjointPairing c F) ≠ 0 := (map_ne_zero _).mpr hJ
  simp only [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  field_simp

/-- `q† ∈ X_G`: `|q†|²G⁻¹r = |u|²G r/|J|²`. -/
theorem memXG_adjointMode (hF : WholeLineData c F) : MemXG (adjointMode c F) := by
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  have hc := hF.im_ne_zero
  set K : ℝ := M / |c.im|
  set J := directAdjointPairing c F
  have hcont : ContinuousOn (adjointMode c F) (Ioi 0) := by
    have h1 : ContinuousOn (fun r => conj (adjointKernel c F r)) (Ioi 0) :=
      Complex.continuous_conj.comp_continuousOn (continuousOn_adjointKernel hF)
    have h2 : Continuous fun r : ℝ => (gaussianWeightInv r : ℂ) :=
      Complex.continuous_ofReal.comp continuous_gaussianWeightInv'
    exact (h1.div h2.continuousOn fun r _ => by
      exact_mod_cast (gaussianWeightInv_pos r).ne').div_const _
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  refine (integrableOn_id_div_weight.const_mul ((K / ‖J‖) ^ 2)).mono' ?_ ?_
  · exact ((((hcont.norm.pow 2).mul continuous_gaussianWeightInv'.continuousOn).mul
      continuousOn_id)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hw := gaussianWeightInv_pos r
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hu := norm_adjointKernel_le hc hM0 hM r
    have hn : ‖adjointMode c F r‖ = ‖adjointKernel c F r‖ / gaussianWeightInv r / ‖J‖ := by
      rw [adjointMode, norm_div, norm_div, Complex.norm_conj, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hw]
    rw [hn]
    by_cases hJ : ‖J‖ = 0
    · rw [hJ, div_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, div_zero]
      positivity
    · have hJp : 0 < ‖J‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hJ)
      have hu' : ‖adjointKernel c F r‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      calc (‖adjointKernel c F r‖ / gaussianWeightInv r / ‖J‖) ^ 2 * gaussianWeightInv r * r
          = ‖adjointKernel c F r‖ ^ 2 / ‖J‖ ^ 2 * (r / gaussianWeightInv r) := by
            field_simp
        _ ≤ K ^ 2 / ‖J‖ ^ 2 * (r / gaussianWeightInv r) := by gcongr
        _ = (K / ‖J‖) ^ 2 * (r / gaussianWeightInv r) := by ring

/-- The normalization `⟨q, q†⟩ = 1`. -/
theorem gaussianPairing_modeVort_adjointMode (hJ : directAdjointPairing c F ≠ 0) :
    gaussianPairing (modeVort c F) (adjointMode c F) = 1 := by
  rw [gaussianPairing_adjointMode hJ]
  exact inv_mul_cancel₀ hJ

/-! ## The left-eigen identity -/

/-- **The adjoint eigen-equation** `∫ (L₀f) u r = λ∫ f u r`, `λ = -2ic`, for `f ∈ X_G`
(`eq:st18-t00066`, lines 1484–1490). -/
theorem integral_generatorL0_mul_adjointKernel (hF : WholeLineData c F) {f : Profile}
    (hf : MemXG f) :
    ∫ r in Ioi (0 : ℝ), generatorL0 f r * adjointKernel c F r * r =
      (-2 * Complex.I * c) * ∫ r in Ioi (0 : ℝ), f r * adjointKernel c F r * r := by
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  have hc := hF.im_ne_zero
  set K : ℝ := M / |c.im|
  have hWf := wprof_of_memXG hf
  have hWh := wprof_modeVort hF
  set u := adjointKernel c F with hu
  have hucont := continuousOn_adjointKernel hF
  have hub : ∀ r, ‖u r‖ ≤ K := norm_adjointKernel_le hc hM0 hM
  have hcR : Continuous fun r : ℝ => ((r : ℝ) : ℂ) := Complex.continuous_ofReal
  have hΩc : Continuous fun r : ℝ => (GaussianVortex.radialOmega r : ℂ) := by
    unfold GaussianVortex.radialOmega; fun_prop
  -- integrability of the three pieces
  have I1 : IntegrableOn (fun r : ℝ => f r * u r * r) (Ioi 0) := by
    refine (hWf.int.const_mul K).mono' ?_ ?_
    · exact (hf.measurable.mul (hucont.aestronglyMeasurable measurableSet_Ioi)).mul
        hcR.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
      have hr0 : (0 : ℝ) < r := hr
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      calc ‖f r‖ * ‖u r‖ * r ≤ ‖f r‖ * K * r := by gcongr; exact hub r
        _ = K * (r * ‖f r‖) := by ring
  have I2 : IntegrableOn (fun r : ℝ => (GaussianVortex.radialOmega r : ℂ) * f r * u r * r)
      (Ioi 0) := by
    refine (hWf.int.const_mul K).mono' ?_ ?_
    · exact (((hΩc.aestronglyMeasurable.mul hf.measurable).mul
        (hucont.aestronglyMeasurable measurableSet_Ioi)).mul hcR.aestronglyMeasurable)
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
      have hr0 : (0 : ℝ) < r := hr
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hr0, abs_of_nonneg (radialOmega_nonneg r)]
      have h1 := radialOmega_le_one r
      calc GaussianVortex.radialOmega r * ‖f r‖ * ‖u r‖ * r ≤ 1 * ‖f r‖ * K * r := by
            gcongr; exact hub r
        _ = K * (r * ‖f r‖) := by ring
  set Cf : ℝ := 1 / 4 * ∫ ρ in Ioi (0 : ℝ), ρ * ‖f ρ‖
  have I3 : IntegrableOn (fun r : ℝ => Planar.greenN 2 f r * modeVort c F r * r) (Ioi 0) := by
    refine (hWh.int.const_mul Cf).mono' ?_ ?_
    · exact (((continuousOn_greenN_two hWf).aestronglyMeasurable measurableSet_Ioi).mul
        hWh.meas).mul hcR.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
      have hr0 : (0 : ℝ) < r := hr
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      have := norm_greenN_two_le hWf r hr0
      calc ‖Planar.greenN 2 f r‖ * ‖modeVort c F r‖ * r ≤ Cf * ‖modeVort c F r‖ * r := by
            gcongr
        _ = Cf * (r * ‖modeVort c F r‖) := by ring
  -- the pointwise form of `L₀f`
  have hL : ∫ r in Ioi (0 : ℝ), generatorL0 f r * u r * r =
      ∫ r in Ioi (0 : ℝ), (-2 * Complex.I * ((GaussianVortex.radialOmega r : ℂ) * f r * u r * r) +
        2 * Complex.I * (Planar.greenN 2 f r * modeVort c F r * r)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hG : greenInverse f r = Planar.greenN 2 f r := by
      rw [greenInverse_eq_R, Planar.greenN_two_eq_R hWf hr0]
    simp only [generatorL0]
    rw [hG, vortexOmega_eq, strainK_eq, modeVort_eq_mul]
    ring
  -- the Green symmetry and `Rh = φ`
  have hS : ∫ r in Ioi (0 : ℝ), Planar.greenN 2 f r * modeVort c F r * r =
      ∫ r in Ioi (0 : ℝ), ((GaussianVortex.radialOmega r : ℂ) * f r * u r * r -
        c * (f r * u r * r)) := by
    rw [Planar.integral_greenN_mul_symm 2 hWf hWh]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    rw [← mode_eq_green hF r hr0, modeRadial_eq_mul hc F r]
    ring
  rw [hL, integral_add (I2.const_mul _) (I3.const_mul _), integral_const_mul, integral_const_mul,
    hS, integral_sub I2 (I1.const_mul c), integral_const_mul]
  ring

/-- **G3a for the explicit adjoint** (`eq:st18-t00066`, `eq:st18-t00012`, units B0092, B0099):
when `J_q ≠ 0`, `q† = h_X/J̄` is a normalized `X_G`-adjoint eigenvector of `L₀` for `λ = -2ic`. -/
theorem isAdjointEigenvector_adjointMode (hF : WholeLineData c F)
    (hJ : directAdjointPairing c F ≠ 0) :
    IsAdjointEigenvector (-2 * Complex.I * c) (modeVort c F) (adjointMode c F) where
  memXG := memXG_adjointMode hF
  left_eigen := fun f hf => by
    rw [gaussianPairing_adjointMode hJ, gaussianPairing_adjointMode hJ,
      integral_generatorL0_mul_adjointKernel hF hf]
    ring
  normalized := gaussianPairing_modeVort_adjointMode hJ

/-- `ℓ(H) = M_q/J_q` (`eq:st18-t00109`, unit B0127). -/
theorem strainCoupling_adjointMode (hJ : directAdjointPairing c F ≠ 0) :
    gaussianPairing strainProfile (adjointMode c F) =
      (directAdjointPairing c F)⁻¹ * quadrupole (modeVort c F) := by
  rw [gaussianPairing_adjointMode hJ]
  congr 1
  unfold quadrupole
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [show strainProfile r = ((r ^ 2 * strainK r : ℝ) : ℂ) from rfl, modeVort_eq_mul, strainK_eq]
  push_cast
  ring

/-- **`ℓ(H) ≠ 0`** (G4, `eq:st18-t00109`, units B0127, B0134), from `J_q ≠ 0` and the nonzero
quadrupole `M_q = 𝔐(h) ≠ 0` (O11, `eq:st18-t00047`). -/
theorem strainCoupling_adjointMode_ne_zero (hF : WholeLineData c F)
    (hJ : directAdjointPairing c F ≠ 0) :
    gaussianPairing strainProfile (adjointMode c F) ≠ 0 := by
  rw [strainCoupling_adjointMode hJ]
  exact mul_ne_zero (inv_ne_zero hJ) (modeQuadrupole_ne_zero hF)

end UnforcedLeray.Cons.C01
