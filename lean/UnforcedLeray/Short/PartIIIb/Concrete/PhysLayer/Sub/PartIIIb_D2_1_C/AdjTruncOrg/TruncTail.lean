import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `truncTail`: the tail `(1 - χₙ) g → 0` in `Y_2`

Source: `the November 2 reference manuscript` lines 1334-1337, 1351-1362,
1470-1480.  Dominated convergence on the phase measure `muP P = (Lebesgue on (0,P]) ⊗ Lebesgue`:
`0 ≤ χₙ ≤ 1` gives `|χₙ - 1| ≤ 1` and `χₙ - 1 → 0` pointwise (`goodMult_cutχ_sub_one`), and
`∫⁻ ‖g‖ₑ^2 < ∞` (finite `Y_2` norm, `lint_lt_top_of_phaseLpNorm`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem truncTail : TruncTail := by
  unfold TruncTail
  intro P hP g hg
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x : ℝ × Space => (cutχ n x.2 - 1) • g x) volume := fun n =>
    (((contDiff_cutχ n).continuous.comp continuous_snd).sub continuous_const).aestronglyMeasurable.smul
      hg.meas
  -- pointwise limit of the integrand
  have hpt : ∀ z : ℝ × Space, Tendsto (fun n : ℕ => ‖(cutχ n z.2 - 1) • g z‖ₑ ^ (2 : ℝ))
      atTop (𝓝 0) := by
    intro z
    have hlim : Tendsto (fun n : ℕ => cutχ n z.2 - 1) atTop (𝓝 0) :=
      goodMult_cutχ_sub_one.lim z.2
    have h3 : Tendsto (fun n : ℕ => |cutχ n z.2 - 1|) atTop (𝓝 0) := by
      simpa using hlim.norm
    have h4 : Tendsto (fun n : ℕ => ENNReal.ofReal |cutχ n z.2 - 1|) atTop (𝓝 0) := by
      have h4' := (ENNReal.continuous_ofReal.tendsto 0).comp h3
      rw [ENNReal.ofReal_zero] at h4'
      exact h4'
    have h5 : Tendsto (fun n : ℕ => ‖(cutχ n z.2 - 1) • g z‖ₑ) atTop (𝓝 0) := by
      have h5' := ENNReal.Tendsto.mul_const h4 (Or.inr enorm_ne_top) (b := ‖g z‖ₑ)
      rw [zero_mul] at h5'
      refine h5'.congr (fun n => ?_)
      rw [enorm_smul, Real.enorm_eq_ofReal_abs]
    have h6 := ((ENNReal.continuous_rpow_const (y := 2)).tendsto 0).comp h5
    have h7 : (0 : ℝ≥0∞) ^ (2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [h7] at h6
    exact h6
  -- the squared-norm integral tends to zero by dominated convergence
  have hJ : Tendsto (fun n : ℕ => ∫⁻ z, ‖(cutχ n z.2 - 1) • g z‖ₑ ^ (2 : ℝ) ∂(muP P))
      atTop (𝓝 0) := by
    have hfin := lint_lt_top_of_phaseLpNorm hP hg.meas hg.finite
    have hdom : ∀ n : ℕ, ∀ z : ℝ × Space, ‖(cutχ n z.2 - 1) • g z‖ₑ ^ (2 : ℝ) ≤
        ‖g z‖ₑ ^ (2 : ℝ) := by
      intro n z
      have hc0 : 0 ≤ cutχ n z.2 := by unfold cutχ; exact unitBump.nonneg
      have hc1 : cutχ n z.2 ≤ 1 := by unfold cutχ; exact unitBump.le_one
      have habs : |cutχ n z.2 - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have hle : ‖(cutχ n z.2 - 1) • g z‖ₑ ≤ ‖g z‖ₑ := by
        rw [enorm_smul, Real.enorm_eq_ofReal_abs]
        have h1 : ENNReal.ofReal |cutχ n z.2 - 1| ≤ 1 := ENNReal.ofReal_le_one.2 habs
        exact mul_le_of_le_one_left (by positivity) h1
      exact ENNReal.rpow_le_rpow hle (by norm_num)
    have key := tendsto_lintegral_of_dominated_convergence'
      (μ := muP P)
      (F := fun n z => ‖(cutχ n z.2 - 1) • g z‖ₑ ^ (2 : ℝ))
      (f := fun _ => (0 : ℝ≥0∞))
      (fun z => ‖g z‖ₑ ^ (2 : ℝ))
      (fun n => ((aesm_muP (hmeas n)).enorm).pow_const 2)
      (fun n => Filter.Eventually.of_forall (fun z => hdom n z))
      hfin.ne
      (Filter.Eventually.of_forall (fun z => hpt z))
    simpa using key
  have hfun : (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2
      (fun x => (cutχ n x.2 - 1) • g x)) = fun n : ℕ =>
        (ENNReal.ofReal P⁻¹ * ∫⁻ z, ‖(cutχ n z.2 - 1) • g z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) :=
    funext fun n => phaseLpNorm_eq P _ (hmeas n)
  rw [hfun]
  have h8 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal P⁻¹) hJ (Or.inr ENNReal.ofReal_ne_top)
  have h9 := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto (ENNReal.ofReal P⁻¹ * 0)).comp h8
  have h10 : (ENNReal.ofReal P⁻¹ * 0) ^ (1 / 2 : ℝ) = 0 := by
    rw [mul_zero]
    exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h10] at h9
  exact h9
