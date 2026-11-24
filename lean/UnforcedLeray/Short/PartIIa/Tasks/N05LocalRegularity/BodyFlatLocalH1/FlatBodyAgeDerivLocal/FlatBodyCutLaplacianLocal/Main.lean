import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Reduction

/-!
# `PartII-a:N05/2/2/1`: `FlatBodyCutLaplacianLocal` from the cylinder heat estimate

Source: `the November 2 reference manuscript`, lines 1794-1799.
`flatBodyCutLaplacianLocal_of` proves `FlatBodyCutLaplacianLocal` from `CylHeatMaxRegL` (the
cylinder heat estimate `IIb.CylHeatMaxReg`, copied verbatim in `CylDefs.lean`), with
`k_L = 6` and `C_L = 4 C (8 + 6 M₀)` (`C` the cylinder constant for `r = 2`,
`M₀ = sup |smoothTransition'|`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell periodize QPeriodic
  periodize_of_mem)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta IsNearCutoff IsLargerCutoff Gamma
  GammaBox cNorm8 cNorm8_nonneg T0flat PepsC dsFromS cellL2Norm FlatBodyCutLaplacianLocal
  flatStressCutRep)
open UnforcedLeray.Short.PartIIa.N05_2_2Aux (flatCutAgeDriftTerm flatCutAgeForceTerm)
open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

theorem eLpNorm_component_le {μ : Measure Profile} (f : Profile → MeridC) (i : Fin 2) :
    eLpNorm (fun p => f p i) 2 μ ≤ eLpNorm f 2 μ :=
  eLpNorm_mono fun p => PiLp.norm_apply_le (f p) i

theorem eLpNorm_lin3_le {μm : Measure Profile} {A B C : Profile → ℂ}
    (hA : AEStronglyMeasurable A μm) (hB : AEStronglyMeasurable B μm)
    (hC : AEStronglyMeasurable C μm) (z : ℂ) :
    eLpNorm (fun p => A p - z * B p + C p) 2 μm ≤
      eLpNorm A 2 μm + ‖z‖ₑ * eLpNorm B 2 μm + eLpNorm C 2 μm := by
  calc eLpNorm (fun p => A p - z * B p + C p) 2 μm
      ≤ eLpNorm (fun p => A p - z * B p) 2 μm + eLpNorm C 2 μm :=
        eLpNorm_add_le (hA.sub (hB.const_mul z)) hC (by norm_num)
    _ ≤ eLpNorm A 2 μm + eLpNorm (fun p => z * B p) 2 μm + eLpNorm C 2 μm := by
        gcongr
        exact eLpNorm_sub_le hA (hB.const_mul z) (by norm_num)
    _ = eLpNorm A 2 μm + ‖z‖ₑ * eLpNorm B 2 μm + eLpNorm C 2 μm := by
        rw [show (fun p => z * B p) = z • B from rfl, eLpNorm_const_smul]

theorem fCut_ae_eq {c σ H1 : ℝ} (hc : 0 < c) (μ : ℂ) (V G : Profile → MeridC) (i : Fin 2) :
    fCut c σ H1 μ V G i =ᵐ[cellMeasure c]
      fun p => ((timeCut σ H1 p.1 * p.1⁻¹) • G p) i -
        μ * ((timeCut σ H1 p.1 * p.1⁻¹) • V p) i + (deriv (timeCut σ H1) p.1 • V p) i := by
  filter_upwards [ae_mem_cell c] with x hx
  simp only [fCut, periodize_of_mem hc _ hx, smul_apply_real]
  push_cast
  ring

theorem eLpNorm_ksmul_comp_le {c b K : ℝ} (hK0 : 0 ≤ K) (hb : 0 ≤ b) (V : HSpace c MeridC)
    {k : ℝ → ℝ} (hK : ∀ s, |k s| ≤ K) (hk0 : ∀ s, b < s → k s = 0) (i : Fin 2) :
    eLpNorm (fun p : Profile => (k p.1 • (V : Profile → MeridC) p) i) 2 (cellMeasure c) ≤
      ENNReal.ofReal (K * (1 + b) * ‖V‖) :=
  (eLpNorm_component_le (fun p : Profile => k p.1 • (V : Profile → MeridC) p) i).trans
    (eLpNorm_ksmul_le hK0 hb V hK hk0)

theorem aesm_ksmul_comp {c : ℝ} (V : HSpace c MeridC) {k : ℝ → ℝ} (hk : Measurable k)
    (i : Fin 2) :
    AEStronglyMeasurable (fun p : Profile => (k p.1 • (V : Profile → MeridC) p) i)
      (cellMeasure c) :=
  ((measurable_comp_apply ((hk.comp measurable_fst).smul
    (Lp.stronglyMeasurable V).measurable) i)).aestronglyMeasurable

/-- `‖f_i‖_{cell} ≤ (2/σ)(1+2H₁)‖g‖ + |μ|(2/σ)(1+2H₁)‖w‖ + (3M₀/σ)(1+2H₁)‖w‖`. -/
theorem eLpNorm_fCut_le {c σ H1 M0 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (hM0n : 0 ≤ M0) (hM0 : ∀ t, |deriv Real.smoothTransition t| ≤ M0) (μ : ℂ)
    (V G : HSpace c MeridC) (i : Fin 2) :
    eLpNorm (fCut c σ H1 μ (V : Profile → MeridC) (G : Profile → MeridC) i) 2 (cellMeasure c) ≤
      ENNReal.ofReal (2 / σ * (1 + 2 * H1) * ‖G‖ + ‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖V‖) +
        3 * M0 / σ * (1 + 2 * H1) * ‖V‖) := by
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hk1m : Measurable fun s : ℝ => timeCut σ H1 s * s⁻¹ :=
    (measurable_timeCut σ H1).mul measurable_inv
  have hk2m : Measurable (deriv (timeCut σ H1)) := (continuous_deriv_timeCut σ H1).measurable
  have h2σ : (0 : ℝ) ≤ 2 / σ := by positivity
  have h3σ : (0 : ℝ) ≤ 3 * M0 / σ := by positivity
  have hb : (0 : ℝ) ≤ 2 * H1 := by linarith
  have hA := eLpNorm_ksmul_comp_le (c := c) h2σ hb G (abs_timeCut_div_le hσ hH)
    (fun s hs => timeCut_div_zero hH hs) i
  have hB := eLpNorm_ksmul_comp_le (c := c) h2σ hb V (abs_timeCut_div_le hσ hH)
    (fun s hs => timeCut_div_zero hH hs) i
  have hC := eLpNorm_ksmul_comp_le (c := c) h3σ hb V (abs_deriv_timeCut_le hM0 hσ hσH)
    (fun s hs => deriv_timeCut_zero_of_gt hH hs) i
  rw [eLpNorm_congr_ae (fCut_ae_eq hc μ _ _ i)]
  refine (eLpNorm_lin3_le (aesm_ksmul_comp G hk1m i) (aesm_ksmul_comp V hk1m i)
    (aesm_ksmul_comp V hk2m i) μ).trans ?_
  have hB' : ‖μ‖ₑ * eLpNorm (fun p : Profile => ((timeCut σ H1 p.1 * p.1⁻¹) •
      (V : Profile → MeridC) p) i) 2 (cellMeasure c) ≤
      ENNReal.ofReal (‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖V‖)) := by
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    gcongr
  have hsplit : ENNReal.ofReal (2 / σ * (1 + 2 * H1) * ‖G‖ + ‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖V‖) +
      3 * M0 / σ * (1 + 2 * H1) * ‖V‖) = ENNReal.ofReal (2 / σ * (1 + 2 * H1) * ‖G‖) +
        ENNReal.ofReal (‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖V‖)) +
          ENNReal.ofReal (3 * M0 / σ * (1 + 2 * H1) * ‖V‖) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hsplit]
  exact add_le_add (add_le_add hA hB') hC

end UnforcedLeray.Short.PartIIa.FBCLL
