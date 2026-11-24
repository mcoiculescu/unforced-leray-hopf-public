import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialParamIntegral
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductBounds

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Kernels
open UnforcedLeray.PressureAnalysis

/-- Derivatives of the translated-source Newton integrand fall entirely on the smooth source. -/
theorem iteratedFDeriv_newtonSourceIntegrand {D : SpaceTime → ℝ}
    (hD : ContDiff ℝ ∞ D) (x : Space) (n : ℕ) (p : SpaceTime) :
    iteratedFDeriv ℝ n (fun z : SpaceTime => newtonPotential x * D (z - (0, x))) p =
      newtonPotential x • iteratedFDeriv ℝ n D (p - (0, x)) := by
  have hshift : ContDiff ℝ ∞ (fun z : SpaceTime => D (z - (0, x))) :=
    hD.comp (by fun_prop)
  change iteratedFDeriv ℝ n
      (fun z : SpaceTime => newtonPotential x • D (z - (0, x))) p = _
  rw [iteratedFDeriv_const_smul_apply'
      (hshift.contDiffAt.of_le (by exact_mod_cast le_top)), iteratedFDeriv_comp_sub']

/-- A smooth source with a fixed compact spatial support radius has all derivative supports in
that same spatial cylinder. -/
theorem tsupport_newtonSource_spatialCylinder {D : SpaceTime → ℝ}
    (R : ℝ) (hR : ∀ τ y, R < ‖y‖ → D (τ, y) = 0) :
    tsupport D ⊆ {z : SpaceTime | ‖z.2‖ ≤ max R 0} := by
  have hsupport : support D ⊆ {z : SpaceTime | ‖z.2‖ ≤ max R 0} := by
    intro z hz
    by_contra hnot
    have hgt : R < ‖z.2‖ := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hnot)
    exact (Function.mem_support.mp hz) (hR z.1 z.2 hgt)
  have hclosed : IsClosed {z : SpaceTime | ‖z.2‖ ≤ max R 0} :=
    isClosed_le (continuous_norm.comp continuous_snd) continuous_const
  rw [tsupport]
  exact closure_minimal hsupport hclosed

theorem tsupport_iteratedFDeriv_spatialCylinder {D : SpaceTime → ℝ}
    (R : ℝ)
    (hR : ∀ τ y, R < ‖y‖ → D (τ, y) = 0) (n : ℕ) :
    tsupport (iteratedFDeriv ℝ n D) ⊆ {z : SpaceTime | ‖z.2‖ ≤ max R 0} := by
  intro z hz
  exact tsupport_newtonSource_spatialCylinder R hR
    (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) n hz)

/-- An iterated source derivative vanishes outside the support cylinder. -/
theorem iteratedFDeriv_newtonSource_zero {D : SpaceTime → ℝ}
    (R : ℝ)
    (hR : ∀ τ y, R < ‖y‖ → D (τ, y) = 0) (n : ℕ) (z : SpaceTime)
    (hz : max R 0 < ‖z.2‖) : iteratedFDeriv ℝ n D z = 0 := by
  have hnotTS : z ∉ tsupport D := by
    intro hmem
    have hbound := tsupport_newtonSource_spatialCylinder R hR hmem
    exact (not_lt_of_ge hbound) hz
  have hnotSupport : z ∉ support (iteratedFDeriv ℝ n D) := by
    intro hmem
    exact hnotTS (support_iteratedFDeriv_subset (𝕜 := ℝ) n hmem)
  exact Function.notMem_support.mp hnotSupport

/-- The actual Newton parameter integral of a smooth source with uniformly compact spatial support
is jointly smooth in its phase and spatial output variables. The Newton singularity stays in the
integration variable, and all output derivatives fall on the source. -/
theorem contDiff_newtonSourceParamIntegral {P : ℝ} {D : SpaceTime → ℝ}
    (hD : IsPhaseTest P D) :
    ContDiff ℝ ∞ (fun p : SpaceTime =>
      ∫ x, newtonPotential x * D (p - (0, x))) := by
  let F : Space → SpaceTime → ℝ := fun x p => newtonPotential x * D (p - (0, x))
  have hsmooth : ∀ᵐ x ∂(volume : Measure Space), ContDiff ℝ ∞ (F x) := by
    filter_upwards [] with x
    exact contDiff_const.mul (hD.smooth.comp (by fun_prop))
  have hmeas : ∀ (n : ℕ) (p : SpaceTime),
      AEStronglyMeasurable (fun x => iteratedFDeriv ℝ n (F x) p) volume := by
    intro n p
    have hcont : Continuous (fun x : Space =>
        iteratedFDeriv ℝ n D (p - (0, x))) :=
      (hD.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp (by fun_prop)
    have hmul := aestronglyMeasurable_newtonPotential.smul hcont.aestronglyMeasurable
    refine hmul.congr (Eventually.of_forall fun x => ?_)
    simpa [F, smul_eq_mul] using
      (iteratedFDeriv_newtonSourceIntegrand hD.smooth x n p).symm
  have hdom : LocDominated volume F univ := by
    intro n p hp
    obtain ⟨R, hR⟩ := hD.bounded_support
    let R₀ := max R 0
    let K := R₀ + ‖p.2‖ + 1
    let sourceSet : Set SpaceTime := Set.Icc (p.1 - 1) (p.1 + 1) ×ˢ closedBall 0 R₀
    have hsourceCompact : IsCompact sourceSet :=
      isCompact_Icc.prod (isCompact_closedBall (0 : Space) R₀)
    obtain ⟨B, hB0, hB⟩ := exists_norm_bound_on_compact
      (fun z => iteratedFDeriv ℝ n D z)
      (hD.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)) hsourceCompact
    let b : Space → ℝ := fun x => B * (closedBall 0 K).indicator (fun x => |newtonPotential x|) x
    refine ⟨ball p 1, ball_mem_nhds p (by norm_num), b, ?_, Eventually.of_forall fun x q hq => ?_⟩
    · have hN := integrable_newtonPotential_abs_on_closedBall K
      have hb := hN.mul_const B
      exact hb.congr (Eventually.of_forall fun x => by simpa [b, mul_comm])
    · rw [iteratedFDeriv_newtonSourceIntegrand hD.smooth x n q]
      by_cases hx : x ∈ closedBall 0 K
      · have hqnorm : ‖q - p‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hq
        have hfst : |q.1 - p.1| ≤ ‖q - p‖ := by
          have := norm_fst_le (q - p)
          simpa [Real.norm_eq_abs] using this
        have hphase : q.1 ∈ Set.Icc (p.1 - 1) (p.1 + 1) := by
          rw [Set.mem_Icc]
          have habs := abs_lt.mp (lt_of_le_of_lt hfst hqnorm)
          constructor <;> linarith
        have hsource : ‖iteratedFDeriv ℝ n D (q - (0, x))‖ ≤ B := by
          by_cases hy : ‖(q - (0, x)).2‖ ≤ R₀
          · exact hB _ ⟨by simpa using hphase, by simpa using hy⟩
          · rw [iteratedFDeriv_newtonSource_zero R hR n
              (q - (0, x)) (lt_of_not_ge hy)]
            simpa using hB0
        rw [norm_smul, Real.norm_eq_abs]
        calc
          |newtonPotential x| * ‖iteratedFDeriv ℝ n D (q - (0, x))‖ ≤
              |newtonPotential x| * B := mul_le_mul_of_nonneg_left hsource (abs_nonneg _)
          _ = b x := by simp [b, hx, mul_comm]
      · have hxgt : K < ‖x‖ := by
          simpa [K, mem_closedBall, dist_zero_right, not_le] using hx
        have hqnorm : ‖q - p‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hq
        have hysub : ‖q.2 - p.2‖ ≤ ‖q - p‖ := norm_snd_le (q - p)
        have hsourceNorm : R₀ < ‖(q - (0, x)).2‖ := by
          by_contra h
          have hy : ‖q.2 - x‖ ≤ R₀ := le_of_not_gt h
          have hxle : ‖x‖ ≤ ‖q.2‖ + ‖q.2 - x‖ := by
            calc
              ‖x‖ = ‖q.2 - (q.2 - x)‖ := by congr 1; abel
              _ ≤ ‖q.2‖ + ‖q.2 - x‖ := norm_sub_le _ _
          have hqsp : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
            calc
              ‖q.2‖ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := by
                calc ‖q.2‖ = ‖p.2 + (q.2 - p.2)‖ := by congr 1; abel
                  _ ≤ _ := norm_add_le _ _
              _ ≤ ‖p.2‖ + 1 := by nlinarith [hysub, hqnorm]
          linarith [hxle]
        have hzero : iteratedFDeriv ℝ n D (q - (0, x)) = 0 := by
          exact iteratedFDeriv_newtonSource_zero R hR n
            (q - (0, x)) hsourceNorm
        simp [hzero, b, hx]
  have hcontOn : ContDiffOn ℝ ∞ (fun p => ∫ x, F x p) univ :=
    Kernels.contDiffOn_integral isOpen_univ hsmooth hmeas hdom
  simpa only [F] using contDiffOn_univ.mp hcontOn

#print axioms iteratedFDeriv_newtonSourceIntegrand
#print axioms tsupport_newtonSource_spatialCylinder
#print axioms tsupport_iteratedFDeriv_spatialCylinder
#print axioms iteratedFDeriv_newtonSource_zero
#print axioms contDiff_newtonSourceParamIntegral

end UnforcedLeray.Cons.C03.Concrete

end
