import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffMainLimit

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

local instance cutoff_dual_ge_one_offset : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

theorem tendsto_projectedNewtonCorrectionCutoffMain_eLpNorm_cell_of_offset
    {P R₀ : ℝ} [Fact (0 < P)] (hR₀ : 0 < R₀)
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : SpaceTime => projectedPotentialNewtonCorrectionCutoffMainField
        (R₀ + (n : ℝ)) Φ z - projectedPotentialNewtonCorrectionField Φ z)
      (conjExp q0E) (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))))
      atTop (𝓝 0) := by
  let μ := volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))
  let C : SpaceTime → CVec3 := fun z =>
    ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
      ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)
  let M : ℕ → SpaceTime → CVec3 := fun n =>
    projectedPotentialNewtonCorrectionCutoffMainField (R₀ + (n : ℝ)) Φ
  let g : ℕ → SpaceTime → ℂ := fun n z =>
    ((cutoff (R₀ + (n : ℝ)) z.2 - 1 : ℝ) : ℂ)
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
        ((cutoff (R₀ + (n : ℝ)) z.2 - 1 : ℝ) : ℂ))
      exact Complex.continuous_ofReal.comp
        (((cutoff_smooth (R₀ + (n : ℝ))).continuous.comp continuous_snd).sub continuous_const)
    exact hcont.aestronglyMeasurable
  have hgeventual : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (g n) μ :=
    eventually_atTop.2 ⟨0, fun n _ => hg n⟩
  have hB : ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂μ, ‖g n z‖ ≤ (1 : ℝ) := by
    filter_upwards [] with n
    filter_upwards [] with z
    have h01 := cutoff_mem_Icc (R₀ + (n : ℝ)) z.2
    change ‖((cutoff (R₀ + (n : ℝ)) z.2 - 1 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h01.1, h01.2]
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ => g n z) atTop (𝓝 0) := by
    filter_upwards [] with z
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z.2‖
    have hnat : ∀ᶠ n : ℕ in atTop, N ≤ n :=
      eventually_atTop.2 ⟨N, fun n hn => hn⟩
    have hev : ∀ᶠ n : ℕ in atTop, cutoff (R₀ + (n : ℝ)) z.2 = 1 := by
      filter_upwards [hnat] with n hn
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hncut : cutoff (R₀ + (n : ℝ)) z.2 = 1 :=
        cutoff_eq_one (by positivity) (hN.trans (by linarith [hR₀]))
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


#print axioms tendsto_projectedNewtonCorrectionCutoffMain_eLpNorm_cell_of_offset

end UnforcedLeray.Cons.C03.Concrete

end
