import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffShellVector
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialPathSmooth
import UnforcedLeray.Lib.CZL2.Decay

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Filter Set
open Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.RieszLp
open NavierStokesR3.ComparisonCutoffs

local instance dual_ge_one_shellLp : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

/-- The actual cutoff-shell field tends to zero in the dual exponent on one period cell. -/
theorem tendsto_projectedNewtonCorrectionCutoffShell_eLpNorm_cell
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      Tendsto (fun n : ℕ => eLpNorm
        (projectedPotentialNewtonCorrectionCutoffShellField (R₀ + (n : ℝ)) Φ)
        (conjExp q0E) (volume.restrict (phaseCell P))) atTop (𝓝 0) := by
  obtain ⟨R₀, K, hR₀, hK, hbound⟩ :=
    exists_uniform_projectedNewtonCorrectionCutoffShell_powWeight_bound hΦ
  refine ⟨R₀, hR₀, ?_⟩
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let p : ℝ≥0∞ := conjExp q0E
  let B : SpaceTime → ℝ := fun z => K * powWeight 3 z.2
  let D : ℕ → SpaceTime → CVec3 := fun n z =>
    projectedPotentialNewtonCorrectionCutoffShellField (R₀ + (n : ℝ)) Φ z
  have hp1 : 1 < p := by dsimp [p]; exact one_lt_of_holderConjugate q0E_ne_top
  have hptop : p ≠ ⊤ := by dsimp [p]; exact conjExp_ne_top one_lt_q0E
  have hp0 : p ≠ 0 := by
    have hpge : (1 : ℝ≥0∞) ≤ p := Fact.out
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hpge)
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hprod : (volume : Measure SpaceTime).restrict (phaseCell P) =
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := by
    simpa only [phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  have hweight : MemLp (fun z : SpaceTime => powWeight 3 z.2) p μ := by
    have hspace : MemLp (powWeight 3) p (volume : Measure Space) :=
      memLp_powWeight_three hp1
    have hprodWeight := hspace.comp_snd ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
    rw [← hprod] at hprodWeight
    exact hprodWeight
  have hB : MemLp B p μ := by
    have h := hweight.const_mul K
    simpa [B, p, μ] using h
  have hDmeas : ∀ n : ℕ, AEStronglyMeasurable (D n) μ := by
    intro n
    have hRe := contDiff_projectedPotentialRePath hΦ
    have hIm := contDiff_projectedPotentialImPath hΦ
    have hcut : ContDiff ℝ ∞ (cutoff (R₀ + (n : ℝ))) := cutoff_smooth _
    have hgrad : Continuous (gradField (cutoff (R₀ + (n : ℝ)))) := continuous_gradField hcut
    have hcont : Continuous (fun z : SpaceTime => D n z) := by
      change Continuous (fun z =>
        ofReV (projectedPotentialRePath Φ z •
          gradField (cutoff (R₀ + (n : ℝ))) z.2) +
        ofImV (projectedPotentialImPath Φ z •
          gradField (cutoff (R₀ + (n : ℝ))) z.2))
      exact (ofReV.continuous.comp (hRe.continuous.smul (hgrad.comp continuous_snd))).add
        (ofImV.continuous.comp (hIm.continuous.smul (hgrad.comp continuous_snd)))
    exact hcont.aestronglyMeasurable.restrict
  have hboundD : ∀ n z, z ∈ phaseCell P → ‖D n z‖ ≤ B z := by
    intro n z hz
    have hphase : z.1 ∈ Icc (0 : ℝ) P := ⟨le_of_lt hz.1.1, hz.1.2⟩
    exact hbound (R₀ + (n : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg _)) z.1 hphase z.2
  have hboundAE (n : ℕ) : ∀ᵐ z ∂μ, ‖D n z‖ ≤ B z := by
    exact ae_restrict_of_forall_mem (measurableSet_Ioc.prod MeasurableSet.univ)
      (hboundD n)
  have hDlim : ∀ z : SpaceTime, Tendsto (fun n : ℕ => ‖D n z‖) atTop (𝓝 0) := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z.2‖
    have hev : ∀ᶠ n : ℕ in atTop, ‖z.2‖ < R₀ + (n : ℝ) := by
      filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
      have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hN' : ‖z.2‖ < (N : ℝ) := by exact_mod_cast hN
      linarith [hR₀]
    have hzero : ∀ᶠ n : ℕ in atTop, D n z = 0 := by
      filter_upwards [hev] with n hn
      have hgradzero : gradField (cutoff (R₀ + (n : ℝ))) z.2 = 0 := by
        ext i
        simp [gradField, spatialTestDerivative_cutoff_of_lt (by positivity) hn]
      simp [D, projectedPotentialNewtonCorrectionCutoffShellField, hgradzero]
    exact tendsto_const_nhds.congr' (hzero.mono fun n hn => by simp [hn])
  have hDm : ∀ n : ℕ, MemLp (D n) p μ := fun n =>
    hB.of_le (hDmeas n) ((hboundAE n).mono fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (powWeight_nonneg 3 z.2))]
      exact hz)
  have heq (n : ℕ) : eLpNorm (D n) p μ =
      ENNReal.ofReal ((∫ z, ‖D n z‖ ^ p.toReal ∂μ) ^ (p.toReal)⁻¹) := by
    simpa [p] using (hDm n).eLpNorm_eq_integral_rpow_norm hp0 hptop
  have hpowInt : Integrable (fun z => ‖B z‖ ^ p.toReal) μ := by
    simpa using hB.integrable_norm_rpow hp0 hptop
  have hint : Tendsto (fun n : ℕ => ∫ z, ‖D n z‖ ^ p.toReal ∂μ)
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := fun n z => ‖D n z‖ ^ p.toReal) (f := fun _ => (0 : ℝ))
      (fun z => ‖B z‖ ^ p.toReal)
      (eventually_atTop.2 ⟨0, fun n _ =>
        ((hDmeas n).norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable⟩)
      (eventually_atTop.2 ⟨0, fun n _ => (hboundAE n).mono fun z hz => by
        have hB0 : 0 ≤ B z := by dsimp [B]; exact mul_nonneg hK (powWeight_nonneg 3 z.2)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        rw [Real.norm_of_nonneg hB0]
        exact Real.rpow_le_rpow (norm_nonneg _) hz hpReal.le⟩)
      hpowInt
      (Eventually.of_forall fun z => by
        have hc := ((Real.continuous_rpow_const (q := p.toReal) hpReal.le).tendsto 0).comp
          (hDlim z)
        simpa [Function.comp_def, Real.zero_rpow hpReal.ne'] using hc)
    simpa using h
  have hroot : Tendsto (fun x : ℝ => ENNReal.ofReal (x ^ (p.toReal)⁻¹))
      (𝓝 0) (𝓝 0) := by
    have hpos : 0 < (p.toReal)⁻¹ := inv_pos.mpr hpReal
    have hc := (ENNReal.continuous_ofReal.comp
      (Real.continuous_rpow_const (q := (p.toReal)⁻¹) hpos.le)).tendsto 0
    simpa [Function.comp_def, Real.zero_rpow hpos.ne'] using hc
  rw [show (fun n : ℕ => eLpNorm (D n) p μ) =
      fun n => ENNReal.ofReal ((∫ z, ‖D n z‖ ^ p.toReal ∂μ) ^ (p.toReal)⁻¹) by
        funext n
        exact heq n]
  exact hroot.comp hint

#print axioms tendsto_projectedNewtonCorrectionCutoffShell_eLpNorm_cell

end UnforcedLeray.Cons.C03.Concrete

end
