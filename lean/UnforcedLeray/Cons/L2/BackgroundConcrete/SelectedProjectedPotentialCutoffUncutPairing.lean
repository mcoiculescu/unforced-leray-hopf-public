import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffMainOffset
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffShellLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffCancellation
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairingLimit

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Filter Set
open Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412
open NavierStokesR3.ComparisonCutoffs

local instance dual_ge_one_uncut : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

local instance holder_uncut : ENNReal.HolderTriple (conjExp q0E) q0E 1 :=
  UnforcedLeray.Sob.holderTriple_conjExp q0E

/-- The uncut actual complex Newton-gradient correction annihilates every phase-solenoidal
`L^(11/4)` field. This is obtained by passing the finite-radius main/shell identity to the
period-cell limit; the pressure/projection correction itself is the genuine Re/Im Newton path. -/
theorem pairF_projectedNewtonCorrection_eq_zero_of_phaseSolenoidal
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w) :
    pairF P (projectedPotentialNewtonCorrectionField Φ)
      (fun z => rep w z.1 z.2) = 0 := by
  obtain ⟨R₀, hR₀, hShellLim⟩ :=
    tendsto_projectedNewtonCorrectionCutoffShell_eLpNorm_cell hΦ
  obtain ⟨Rtail, K, hRtail, hK, hbound⟩ :=
    exists_uniform_projectedNewtonCorrectionCutoffShell_powWeight_bound hΦ
  obtain ⟨N, hN⟩ := exists_nat_ge (Rtail - R₀)
  have hshift : Rtail ≤ R₀ + (N : ℝ) := by linarith
  let R : ℝ := R₀ + (N : ℝ)
  have hR : 0 < R := by dsimp [R]; linarith [hR₀]
  have hShellShift : Tendsto (fun n : ℕ => eLpNorm
      (projectedPotentialNewtonCorrectionCutoffShellField (R + (n : ℝ)) Φ)
      (conjExp q0E) (volume.restrict (phaseCell P))) atTop (𝓝 0) := by
    have hshiftSeq := hShellLim.comp (tendsto_add_atTop_nat N)
    change Tendsto (fun n : ℕ => eLpNorm
      (projectedPotentialNewtonCorrectionCutoffShellField
        (R₀ + ((n + N : ℕ) : ℝ)) Φ)
      (conjExp q0E) (volume.restrict (phaseCell P))) atTop (𝓝 0) at hshiftSeq
    apply hshiftSeq.congr'
    filter_upwards [] with n
    congr 1
    dsimp [R]
    push_cast
    ring_nf
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let C : SpaceTime → CVec3 := projectedPotentialNewtonCorrectionField Φ
  let M : ℕ → SpaceTime → CVec3 := fun n =>
    projectedPotentialNewtonCorrectionCutoffMainField (R + (n : ℝ)) Φ
  let S : ℕ → SpaceTime → CVec3 := fun n =>
    projectedPotentialNewtonCorrectionCutoffShellField (R + (n : ℝ)) Φ
  let W : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  have hC : MemLp C (conjExp q0E) μ := by
    change MemLp (projectedPotentialNewtonCorrectionField Φ)
      (conjExp q0E) (volume.restrict (phaseCell P))
    exact memLp_projectedNewtonCorrection_cell hΦ
  have hW : MemLp W q0E μ := by
    change MemLp (fun z : SpaceTime => rep w z.1 z.2) q0E
      (volume.restrict (phaseCell P))
    simpa [phaseCell] using memLp_rep_periodCell q0E_ne_top w
  have hMrepr (n : ℕ) : M n = fun z =>
      ((cutoff (R + (n : ℝ)) z.2 : ℝ) : ℂ) • C z := by
    funext z
    ext i
    simp [M, C, projectedPotentialNewtonCorrectionCutoffMainField,
      projectedPotentialNewtonCorrectionField, map_smul, Complex.real_smul]
  have hMmeas (n : ℕ) : AEStronglyMeasurable (M n) μ := by
    have hcut : Continuous (fun z : SpaceTime =>
        ((cutoff (R + (n : ℝ)) z.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((cutoff_smooth (R + (n : ℝ))).continuous.comp continuous_snd)
    rw [hMrepr n]
    exact hcut.aestronglyMeasurable.smul hC.aestronglyMeasurable
  have hMbound (n : ℕ) : ∀ᵐ z ∂μ, ‖M n z‖ ≤ ‖C z‖ := by
    filter_upwards [] with z
    rw [hMrepr n, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hχ := cutoff_mem_Icc (R + (n : ℝ)) z.2
    rw [abs_of_nonneg hχ.1]
    calc
      cutoff (R + (n : ℝ)) z.2 * ‖C z‖ ≤ 1 * ‖C z‖ :=
        mul_le_mul_of_nonneg_right hχ.2 (norm_nonneg (C z))
      _ = ‖C z‖ := one_mul _
  have hM (n : ℕ) : MemLp (M n) (conjExp q0E) μ :=
    hC.of_le (hMmeas n) (hMbound n)
  have hp1 : 1 < conjExp q0E := one_lt_of_holderConjugate q0E_ne_top
  have hprod : (volume : Measure SpaceTime).restrict (phaseCell P) =
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := by
    simpa only [phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  have hweight : MemLp (fun z : SpaceTime => powWeight 3 z.2)
      (conjExp q0E) μ := by
    have hspace : MemLp (powWeight 3) (conjExp q0E) (volume : Measure Space) :=
      memLp_powWeight_three hp1
    have hprodWeight := hspace.comp_snd ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
    rw [← hprod] at hprodWeight
    exact hprodWeight
  let B : SpaceTime → ℝ := fun z => K * powWeight 3 z.2
  have hB : MemLp B (conjExp q0E) μ := by
    have h := hweight.const_mul K
    simpa [B] using h
  have hSmeas (n : ℕ) : AEStronglyMeasurable (S n) μ := by
    have hRe := contDiff_projectedPotentialRePath hΦ
    have hIm := contDiff_projectedPotentialImPath hΦ
    have hcut : ContDiff ℝ ∞ (cutoff (R + (n : ℝ))) := cutoff_smooth _
    have hgrad : Continuous (gradField (cutoff (R + (n : ℝ)))) := continuous_gradField hcut
    have hcont : Continuous (S n) := by
      change Continuous (fun z =>
        ofReV (projectedPotentialRePath Φ z • gradField (cutoff (R + (n : ℝ))) z.2) +
        ofImV (projectedPotentialImPath Φ z • gradField (cutoff (R + (n : ℝ))) z.2))
      exact (ofReV.continuous.comp (hRe.continuous.smul (hgrad.comp continuous_snd))).add
        (ofImV.continuous.comp (hIm.continuous.smul (hgrad.comp continuous_snd)))
    exact hcont.aestronglyMeasurable.restrict
  have hSbound (n : ℕ) : ∀ᵐ z ∂μ, ‖S n z‖ ≤ B z := by
    apply ae_restrict_of_forall_mem (measurableSet_Ioc.prod MeasurableSet.univ)
    intro z hz
    have hphase : z.1 ∈ Icc (0 : ℝ) P := ⟨le_of_lt hz.1.1, hz.1.2⟩
    have hRad : Rtail ≤ R + (n : ℝ) := by
      dsimp [R]
      exact le_trans hshift (le_add_of_nonneg_right (Nat.cast_nonneg _))
    exact hbound (R + (n : ℝ)) hRad z.1 hphase z.2
  have hS (n : ℕ) : MemLp (S n) (conjExp q0E) μ := by
    apply hB.of_le (hSmeas n) ((hSbound n).mono fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (powWeight_nonneg 3 z.2))]
    exact hz
  have hMconv : Tendsto
      (fun n : ℕ => eLpNorm (M n - C) (conjExp q0E) μ) atTop (𝓝 0) := by
    change Tendsto
      (fun n : ℕ => eLpNorm
        (fun z : SpaceTime => projectedPotentialNewtonCorrectionCutoffMainField
          (R + (n : ℝ)) Φ z - projectedPotentialNewtonCorrectionField Φ z)
        (conjExp q0E) (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))))
      atTop (𝓝 0)
    exact tendsto_projectedNewtonCorrectionCutoffMain_eLpNorm_cell_of_offset hR hΦ
  have hSconv : Tendsto (fun n : ℕ => eLpNorm (S n) (conjExp q0E) μ)
      atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => eLpNorm
      (projectedPotentialNewtonCorrectionCutoffShellField (R + (n : ℝ)) Φ)
      (conjExp q0E) (volume.restrict (phaseCell P))) atTop (𝓝 0)
    exact hShellShift
  have hMint : Tendsto (fun n : ℕ => ∫ z, dotL (M n z) (W z) ∂μ)
      atTop (𝓝 (∫ z, dotL (C z) (W z) ∂μ)) :=
    tendsto_integral_dotL_of_eLpNorm hC hW hM hMconv
  have hSint : Tendsto (fun n : ℕ => ∫ z, dotL (S n z) (W z) ∂μ)
      atTop (𝓝 (0 : ℂ)) := by
    have hconvArg : Tendsto
        (fun n : ℕ => eLpNorm (S n - (fun _ : SpaceTime => (0 : CVec3)))
          (conjExp q0E) μ) atTop (𝓝 0) := by
      convert hSconv using 1
      funext n
      congr 1
      funext z
      simp
    have hconv := tendsto_integral_dotL_of_eLpNorm
      (F := fun _ : SpaceTime => (0 : CVec3)) (G := W) (Fseq := S)
      (p := conjExp q0E) (q := q0E)
      (by simpa using (memLp_const (c := (0 : CVec3)) (μ := μ))) hW hS hconvArg
    simpa using hconv
  have hmainPairInt (n : ℕ) : Integrable (fun z => dotL (M n z) (W z)) μ :=
    integrable_dotL_of_memLp_holder (hM n) hW
  have hshellPairInt (n : ℕ) : Integrable (fun z => dotL (S n z) (W z)) μ :=
    integrable_dotL_of_memLp_holder (hS n) hW
  have hsumPairZero (n : ℕ) : pairF P (M n) W + pairF P (S n) W = 0 := by
    have hcan := pairF_projectedNewtonCorrectionCutoff_main_eq_neg_shell
      (P := P) (R := R + (n : ℝ)) hΦ (by positivity) hw
    change pairF P (M n) W = -pairF P (S n) W at hcan
    linear_combination hcan
  have hCint : Integrable (fun z => dotL (C z) (W z)) μ :=
    integrable_dotL_of_memLp_holder hC hW
  have hPairMainBase := hMint.const_smul (P⁻¹ : ℝ)
  have hPairMain : Tendsto (fun n : ℕ => pairF P (M n) W)
      atTop (𝓝 (pairF P C W)) := by
    have hPairMain' := hPairMainBase.congr' (Eventually.of_forall fun n =>
      (pairF_eq_restrictedProductIntegral (hmainPairInt n)).symm)
    rw [pairF_eq_restrictedProductIntegral hCint]
    exact hPairMain'
  have hPairShellBase := hSint.const_smul (P⁻¹ : ℝ)
  have hPairShell : Tendsto (fun n : ℕ => pairF P (S n) W)
      atTop (𝓝 (0 : ℂ)) := by
    have hPairShell' := hPairShellBase.congr' (Eventually.of_forall fun n =>
      (pairF_eq_restrictedProductIntegral (hshellPairInt n)).symm)
    simpa using hPairShell'
  have hPairSum := hPairMain.add hPairShell
  have hPairZeroSeq : Tendsto (fun n : ℕ => pairF P (M n) W + pairF P (S n) W)
      atTop (𝓝 (0 : ℂ)) := by
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hsumPairZero n).symm)
  have hlimitEq := tendsto_nhds_unique hPairSum hPairZeroSeq
  simpa using hlimitEq

#print axioms pairF_projectedNewtonCorrection_eq_zero_of_phaseSolenoidal

end UnforcedLeray.Cons.C03.Concrete

end
