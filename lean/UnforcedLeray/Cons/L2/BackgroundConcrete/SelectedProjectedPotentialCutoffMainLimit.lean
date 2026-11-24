import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSourceFamilyL1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCellLp
import UnforcedLeray.Lib.Semigroups.Multiplication
import NavierStokes.R3.ComparisonCutoffs

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Filter
open Set
open Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412
open NavierStokesR3.ComparisonCutoffs

local instance cutoff_dual_ge_one : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

/-- The actual complex Newton-gradient correction field defined by the two real source paths. -/
def projectedPotentialNewtonCorrectionField (Φ : SpaceTime → CVec3) : SpaceTime → CVec3 :=
  fun z => ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
    ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)

/-- The main spatial-cutoff part of the actual complex Newton-gradient correction. -/
def projectedPotentialNewtonCorrectionCutoffMainField (R : ℝ)
    (Φ : SpaceTime → CVec3) : SpaceTime → CVec3 :=
  fun z => ofReV (cutoff R z.2 •
      gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
    ofImV (cutoff R z.2 •
      gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)

/-- The actual full Newton correction is the L^(11/7) limit of its spatially cutoff main term
on a period cell. -/
theorem tendsto_projectedNewtonCorrectionCutoffMain_eLpNorm_cell
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : SpaceTime => projectedPotentialNewtonCorrectionCutoffMainField
        ((n : ℝ) + 1) Φ z - projectedPotentialNewtonCorrectionField Φ z)
      (conjExp q0E) (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))))
      atTop (𝓝 0) := by
  let μ := volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))
  let C : SpaceTime → CVec3 := fun z =>
    ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
      ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)
  let M : ℕ → SpaceTime → CVec3 := fun n =>
    projectedPotentialNewtonCorrectionCutoffMainField ((n : ℝ) + 1) Φ
  let g : ℕ → SpaceTime → ℂ := fun n z =>
    ((cutoff ((n : ℝ) + 1) z.2 - 1 : ℝ) : ℂ)
  have hCraw := memLp_projectedNewtonCorrection_cell hΦ
  have hC : MemLp C (conjExp q0E) μ := by
    change MemLp (fun z : SpaceTime =>
      ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (conjExp q0E) μ
    exact hCraw
  have hg : ∀ n, AEStronglyMeasurable (g n) μ := by
    intro n
    have hcont : Continuous (g n) := by
      change Continuous (fun z : SpaceTime =>
        ((cutoff ((n : ℝ) + 1) z.2 - 1 : ℝ) : ℂ))
      exact Complex.continuous_ofReal.comp
        (((cutoff_smooth ((n : ℝ) + 1)).continuous.comp continuous_snd).sub continuous_const)
    exact hcont.aestronglyMeasurable
  have hgeventual : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (g n) μ :=
    eventually_atTop.2 ⟨0, fun n _ => hg n⟩
  have hB : ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂μ, ‖g n z‖ ≤ (1 : ℝ) := by
    filter_upwards [] with n
    filter_upwards [] with z
    have h01 := cutoff_mem_Icc ((n : ℝ) + 1) z.2
    change ‖((cutoff ((n : ℝ) + 1) z.2 - 1 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h01.1, h01.2]
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ => g n z) atTop (𝓝 0) := by
    filter_upwards [] with z
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z.2‖
    have hnat : ∀ᶠ n : ℕ in atTop, N ≤ n :=
      eventually_atTop.2 ⟨N, fun n hn => hn⟩
    have hev : ∀ᶠ n : ℕ in atTop, cutoff ((n : ℝ) + 1) z.2 = 1 := by
      filter_upwards [hnat] with n hn
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hncut : cutoff ((n : ℝ) + 1) z.2 = 1 :=
        cutoff_eq_one (by positivity) (hN.trans (by linarith))
      exact hncut
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => by simp [g, hn])
  have hmul := UnforcedLeray.Infra.Mult.tendsto_eLpNorm_smul_of_dominated
    (p := conjExp q0E) (μ := μ) (l := atTop)
    (conjExp_ne_top one_lt_q0E) hgeventual hB hlim hC
  have heq (n : ℕ) :
      (fun z : SpaceTime => M n z - C z) = fun z => g n z • C z := by
    funext z
    ext i
    simp [M, C, g, projectedPotentialNewtonCorrectionCutoffMainField,
      projectedPotentialNewtonCorrectionField, map_smul, Complex.real_smul, smul_eq_mul]
    ring
  have hnorm (n : ℕ) : eLpNorm (fun z : SpaceTime => M n z - C z)
      (conjExp q0E) μ = eLpNorm (fun z => g n z • C z) (conjExp q0E) μ := by
    rw [heq]
  have hfinal := hmul.congr' (Eventually.of_forall fun n => (hnorm n).symm)
  simpa only [μ, M, C, projectedPotentialNewtonCorrectionField] using hfinal

#print axioms tendsto_projectedNewtonCorrectionCutoffMain_eLpNorm_cell

end UnforcedLeray.Cons.C03.Concrete

end
