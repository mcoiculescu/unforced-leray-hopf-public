import UnforcedLeray.Blueprint.Construction.Planar
import UnforcedLeray.Lib.ComplexODEB
import UnforcedLeray.Lib.ComplexODEC.Quadrupole
import UnforcedLeray.Lib.PlanarSectors

/-!
# Step C1, part G1: the Gaussian growing eigenpair in the blueprint's encoding

`paper/main.tex`, Theorem G1 (`thm:ref-planar-pair`, lines 691–706, `eq:st18-t00008`), in the
angular sector `2`, read through the Gaussian space `X_G` and the generator
`L₀ = -2iΩ + 2ikR` of lines 672–689 (`eq:st18-t00005`–`t00007`). Blueprint units B0085
(reference choice), B0010–B0012 (`X_G`, `R`, `L₀`), B0034 (the annular mode at `n = 2`),
B0042–B0057 (the whole-line mode, its Green representation and its nonzero quadrupole,
lines 1022–1192).

This file proves the clause `IsGrowingEigenpair` of `Blueprint.Planar.IsPlanarReference`
(`Blueprint/Construction/Planar.lean`), with `-2 < ω < 0`, for the eigenpair built by the
compiled drafts:
* `Rayleigh.Evans.exists_wholeLine_growing_mode` (O8, `Lib/ComplexODEB.lean`, through
  B0034): a whole-line Rayleigh mode `F` at a speed `c` with `Im c > 0`, `0 < Re c < 1`;
* `ComplexODEC.mode_eq_green` (O9): `φ = R h` for `φ(r) = F(log r)` and the vorticity
  `h = kφ/(Ω - c)` (`ComplexODEC.modeVort`, tex eq. `st18-t00046`);
* `ComplexODEC.modeQuadrupole_ne_zero` (O11): `𝔐(h) ≠ 0` (tex eq. `st18-t00047`).

Then `L₀h = -2iΩh + 2ikφ = -2iΩh + 2i(Ω - c)h = λh` with `λ = -2ic = γ + iω`, `γ = 2 Im c > 0`
and `ω = -2 Re c ∈ (-2, 0)` (tex lines 1120–1127, eq. `st18-t00042`).

Main declarations (namespace `UnforcedLeray.Cons.C01`):
* `greenInverse_eq_R`: the blueprint's `R` is the compiled `B0011.R` (definitionally);
* `memXG_modeVort`, `modeVort_not_ae_zero`, `contDiffOn_modeVort`, `generatorL0_modeVort`;
* `isGrowingEigenpair_modeVort`: G1 for `(-2ic, h)`;
* **`exists_growingEigenpair`**: `∃ λ q, IsGrowingEigenpair λ q ∧ -2 < Im λ < 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Cons.C01

open UnforcedLeray.ComplexODEC

/-- `Ω` of the blueprint (`Blueprint.Planar.vortexOmega`) is the compiled
`GaussianVortex.radialOmega` (tex line 639). -/
theorem vortexOmega_eq (r : ℝ) :
    Blueprint.Planar.vortexOmega r = GaussianVortex.radialOmega r := by
  simp only [Blueprint.Planar.vortexOmega, GaussianVortex.radialOmega, neg_div]

/-- `k` of the blueprint (`Blueprint.Planar.strainK`) is the compiled `GaussianVortex.radialK`
(`eq:st18-t00002`). -/
theorem strainK_eq (r : ℝ) : Blueprint.Planar.strainK r = GaussianVortex.radialK r := by
  rw [GaussianVortex.radialK, ← vortexOmega_eq]
  rfl

/-- The blueprint's Green inverse `R` (`eq:st18-t00007`) is literally the compiled
`B0011.R`. -/
theorem greenInverse_eq_R (f : ℝ → ℂ) (r : ℝ) :
    Blueprint.Planar.greenInverse f r = B0011.R f r := rfl

/-- The output of O8 in the bundled form `WholeLineData` used by O9–O11, with
`Im c > 0` and `0 < Re c < 1` (tex lines 1022–1127). -/
theorem exists_wholeLineData : ∃ c : ℂ, 0 < c.im ∧ 0 < c.re ∧ c.re < 1 ∧
    ∃ F : ℝ → ℂ, WholeLineData c F := by
  obtain ⟨c, hci, hre0, hre1, -, F, hF, -, hsm, h1, h2, h3, h4⟩ :=
    Rayleigh.Evans.exists_wholeLine_growing_mode
  exact ⟨c, hci, hre0, hre1, F, ⟨hF, hsm, h1, h2, h3, h4⟩⟩

variable {c : ℂ} {F : ℝ → ℂ}

/-- `x^k e^{-x²/4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_gauss' (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2 / 4))) (Ioi 0) :=
  integrableOn_pow_mul_gauss k

theorem continuous_gaussianWeightInv : Continuous Blueprint.Planar.gaussianWeightInv := by
  unfold Blueprint.Planar.gaussianWeightInv
  fun_prop

/-- The eigenvorticity `h = kφ/(Ω - c)` lies in `X_G` (`eq:st18-t00005`): it is bounded by
`C(r²/4 + 2)e^{-r²/4}`, so `|h|²G⁻¹r ≤ C'(r²/4 + 2)² r e^{-r²/4}`. -/
theorem memXG_modeVort (hF : WholeLineData c F) :
    Blueprint.Planar.MemXG (modeVort c F) := by
  obtain ⟨M, hM0, hM⟩ := hF.exists_bound
  have hc := hF.im_ne_zero
  set K : ℝ := M / |c.im| with hK
  refine ⟨(continuousOn_modeVort hF).aestronglyMeasurable measurableSet_Ioi, ?_⟩
  have hint : IntegrableOn (fun r : ℝ => 4 * Real.pi * K ^ 2 *
      (1 / 16 * (r ^ 5 * Real.exp (-(r ^ 2 / 4))) + r ^ 3 * Real.exp (-(r ^ 2 / 4)) +
        4 * (r ^ 1 * Real.exp (-(r ^ 2 / 4))))) (Ioi 0) :=
    ((((integrableOn_pow_mul_gauss' 5).const_mul (1 / 16)).add
      (integrableOn_pow_mul_gauss' 3)).add
        ((integrableOn_pow_mul_gauss' 1).const_mul 4)).const_mul (4 * Real.pi * K ^ 2)
  refine hint.mono' ?_ ?_
  · have hcont : ContinuousOn (fun r : ℝ => ‖modeVort c F r‖ ^ 2 *
        Blueprint.Planar.gaussianWeightInv r * r) (Ioi 0) :=
      (((continuousOn_modeVort hF).norm.pow 2).mul
        continuous_gaussianWeightInv.continuousOn).mul continuousOn_id
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hw : 0 ≤ Blueprint.Planar.gaussianWeightInv r := by
      unfold Blueprint.Planar.gaussianWeightInv; positivity
    have hnn : 0 ≤ ‖modeVort c F r‖ ^ 2 * Blueprint.Planar.gaussianWeightInv r * r := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hb := norm_modeVort_le hc hM0 hM r
    have hb2 : ‖modeVort c F r‖ ^ 2 ≤ (K * ((r ^ 2 / 4 + 2) * Real.exp (-(r ^ 2 / 4)))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have he : Real.exp (-(r ^ 2 / 4)) ^ 2 * Real.exp (r ^ 2 / 4) = Real.exp (-(r ^ 2 / 4)) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    calc ‖modeVort c F r‖ ^ 2 * Blueprint.Planar.gaussianWeightInv r * r
        ≤ (K * ((r ^ 2 / 4 + 2) * Real.exp (-(r ^ 2 / 4)))) ^ 2 *
            Blueprint.Planar.gaussianWeightInv r * r := by
          gcongr
      _ = 4 * Real.pi * K ^ 2 * ((r ^ 2 / 4 + 2) ^ 2 * r) *
            (Real.exp (-(r ^ 2 / 4)) ^ 2 * Real.exp (r ^ 2 / 4)) := by
          unfold Blueprint.Planar.gaussianWeightInv
          ring
      _ = 4 * Real.pi * K ^ 2 *
            (1 / 16 * (r ^ 5 * Real.exp (-(r ^ 2 / 4))) + r ^ 3 * Real.exp (-(r ^ 2 / 4)) +
              4 * (r ^ 1 * Real.exp (-(r ^ 2 / 4)))) := by
          rw [he]
          ring

/-- `h ≢ 0` on `(0, ∞)`: its quadrupole `𝔐(h) = ∫ r³h` is nonzero (O11,
`modeQuadrupole_ne_zero`, tex eq. `st18-t00047`). -/
theorem modeVort_not_ae_zero (hF : WholeLineData c F) :
    ¬ modeVort c F =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  intro h0
  apply modeQuadrupole_ne_zero hF
  have h1 : (fun r : ℝ => (r : ℂ) ^ 3 * modeVort c F r) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    h0.mono fun r hr => by simp [hr]
  rw [modeQuadrupole, integral_congr_ae h1]
  simp

/-- `h` is smooth on `(0, ∞)`: `h(r) = κ_c(r²)F(log r)` with `κ_c` and `F` smooth. -/
theorem contDiffOn_modeVort (hF : WholeLineData c F) :
    ContDiffOn ℝ ∞ (modeVort c F) (Ioi 0) := by
  have hk : ContDiff ℝ ∞ fun r : ℝ => kappa c (r ^ 2) :=
    (contDiff_kappa hF.im_ne_zero).comp (contDiff_id.pow 2)
  have hl : ContDiffOn ℝ ∞ (fun r : ℝ => F (Real.log r)) (Ioi 0) :=
    hF.smooth.comp_contDiffOn (Real.contDiffOn_log.mono fun r hr => ne_of_gt hr)
  exact hk.contDiffOn.mul hl

/-- **The eigen-equation** `L₀h = λh`, `λ = -2ic`, at every `r > 0` (tex lines 1120–1127 and
1181–1183): `Rh = φ` by O9, and `kφ = (Ω - c)h`. -/
theorem generatorL0_modeVort (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    Blueprint.Planar.generatorL0 (modeVort c F) r = (-2 * Complex.I * c) * modeVort c F r := by
  have hR : Blueprint.Planar.greenInverse (modeVort c F) r = modeRadial F r := by
    rw [greenInverse_eq_R, ← Planar.greenN_two_eq_R (wprof_modeVort hF) hr,
      ← mode_eq_green hF r hr]
  have hne : (GaussianVortex.radialOmega r : ℂ) - c ≠ 0 :=
    ofReal_sub_ne_zero hF.im_ne_zero _
  have hkφ : (GaussianVortex.radialK r : ℂ) * modeRadial F r =
      ((GaussianVortex.radialOmega r : ℂ) - c) * modeVort c F r := by
    rw [modeVort_eq]
    field_simp
  unfold Blueprint.Planar.generatorL0
  rw [hR, vortexOmega_eq, strainK_eq]
  linear_combination (2 * Complex.I) * hkφ

/-- **G1** in the blueprint's encoding (`thm:ref-planar-pair`, lines 691–706): `(-2ic, h)` is a
growing eigenpair of `L₀` on `X_G`. -/
theorem isGrowingEigenpair_modeVort (hF : WholeLineData c F) :
    Blueprint.Planar.IsGrowingEigenpair (-2 * Complex.I * c) (modeVort c F) where
  re_pos := by
    have h := hF.mode.upper_half_plane
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  memXG := memXG_modeVort hF
  nonzero := modeVort_not_ae_zero hF
  smooth := contDiffOn_modeVort hF
  eigen := fun _ hr => generatorL0_modeVort hF hr

/-- **G1 with the frequency bound** (`thm:ref-planar-pair`, `eq:st18-t00008`, lines 691–706;
blueprint B0085 with B0034, B0042–B0057): there is a growing eigenpair `(λ, q)` of `L₀` on
`X_G` in sector `2` with `-2 < Im λ < 0`. Proved from the compiled O8–O11, with no
hypothesis. -/
theorem exists_growingEigenpair : ∃ (eigenvalue : ℂ) (q : Blueprint.Planar.Profile),
    Blueprint.Planar.IsGrowingEigenpair eigenvalue q ∧ eigenvalue.im ∈ Ioo (-2 : ℝ) 0 := by
  obtain ⟨c, hci, hre0, hre1, F, hF⟩ := exists_wholeLineData
  refine ⟨-2 * Complex.I * c, modeVort c F, isGrowingEigenpair_modeVort hF, ?_⟩
  have h := (Rayleigh.Evans.growthRate_bounds hci hre0 hre1).2
  exact ⟨h.1, h.2⟩

end UnforcedLeray.Cons.C01
