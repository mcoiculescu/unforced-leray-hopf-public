import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Unit B0079, helper: Cauchy–Schwarz with the weight `⟨s⟩^{2M} s ds`

Blueprint unit `B0079` (`eq:st18-t00060`), `paper/main.tex` lines 1374–1378: "Cauchy–Schwarz
with weight `⟨s⟩^{2M} s ds`". For a profile `w` on `(0,∞)` with
`∫₀^∞ |w|² (1+s²)^M s ds < ∞` (here `⟨s⟩^{2M} = (1+s²)^M`), a measurable set `A ⊆ (0,∞)`, and a
nonnegative factor `p` with `p(s)² ≤ q(s) (1+s²)^M s` on `A` for an integrable `q ≥ 0`,
`setIntegral_mul_norm_le` gives `p ‖w‖ ∈ L¹(A)` and
`∫_A p ‖w‖ ≤ (∫_A q)^{1/2} (∫₀^∞ |w|² (1+s²)^M s)^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.B0079

/-- Weighted Cauchy–Schwarz on a subset `A ⊆ (0,∞)`: if `p ≥ 0` and `p² ≤ q (1+s²)^M s` on
`A` with `q ≥ 0` integrable on `A`, then `p ‖w‖` is integrable on `A` and
`∫_A p ‖w‖ ≤ √(∫_A q) · √(∫₀^∞ ‖w‖² (1+s²)^M s)` (`paper/main.tex` lines 1374–1375). -/
theorem setIntegral_mul_norm_le {M : ℝ} {w : ℝ → ℂ}
    (hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)))
    (hwi : Integrable (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (volume.restrict (Ioi 0)))
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ioi 0)
    {p q : ℝ → ℝ} (hp : AEStronglyMeasurable p (volume.restrict A)) (hp0 : ∀ s ∈ A, 0 ≤ p s)
    (hq : IntegrableOn q A) (hq0 : ∀ s ∈ A, 0 ≤ q s)
    (hpq : ∀ s ∈ A, p s ^ 2 ≤ q s * ((1 + s ^ 2) ^ M * s)) :
    IntegrableOn (fun s => p s * ‖w s‖) A ∧
      ∫ s in A, p s * ‖w s‖ ≤
        √(∫ s in A, q s) * √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by
  set ω : ℝ → ℝ := fun s => (1 + s ^ 2) ^ M * s with hω
  have hω0 : ∀ s ∈ A, 0 ≤ ω s := fun s hs =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_of_lt (hA0 hs))
  set f : ℝ → ℝ := fun s => √(q s) with hf
  set g : ℝ → ℝ := fun s => ‖w s‖ * √(ω s) with hg
  have hwA : AEStronglyMeasurable w (volume.restrict A) :=
    hwm.mono_measure (Measure.restrict_mono hA0 le_rfl)
  have hwiA : IntegrableOn (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) A :=
    hwi.mono_measure (Measure.restrict_mono hA0 le_rfl)
  have hωc : Continuous ω := by
    refine Continuous.mul ?_ continuous_id
    exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun s => Or.inl (show (1 : ℝ) + s ^ 2 ≠ 0 by positivity)
  have hfm : AEStronglyMeasurable f (volume.restrict A) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hq.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g (volume.restrict A) :=
    hwA.norm.mul (Real.continuous_sqrt.comp hωc).aestronglyMeasurable
  have hf2 : ∀ s ∈ A, f s ^ 2 = q s := fun s hs => Real.sq_sqrt (hq0 s hs)
  have hg2 : ∀ s ∈ A, g s ^ 2 = ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s := fun s hs => by
    show (‖w s‖ * √(ω s)) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (hω0 s hs)]
    simp only [hω]
    ring
  have hf2i : IntegrableOn (fun s => f s ^ 2) A :=
    hq.congr_fun (fun s hs => (hf2 s hs).symm) hA
  have hg2i : IntegrableOn (fun s => g s ^ 2) A :=
    hwiA.congr_fun (fun s hs => (hg2 s hs).symm) hA
  -- pointwise comparison `p ‖w‖ ≤ f g`
  have hpfg : ∀ s ∈ A, p s * ‖w s‖ ≤ f s * g s := fun s hs => by
    have h1 : p s ≤ √(q s) * √(ω s) := by
      rw [← Real.sqrt_mul (hq0 s hs)]
      calc p s = √(p s ^ 2) := (Real.sqrt_sq (hp0 s hs)).symm
        _ ≤ √(q s * ω s) := Real.sqrt_le_sqrt (hpq s hs)
    calc p s * ‖w s‖ ≤ (√(q s) * √(ω s)) * ‖w s‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = f s * g s := by simp only [hf, hg]; ring
  have hfg0 : ∀ s ∈ A, 0 ≤ f s * g s := fun s _ =>
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  -- integrability of `f g`
  have hfgi : IntegrableOn (fun s => f s * g s) A := by
    refine Integrable.mono' ((hf2i.add hg2i).div_const 2) (hfm.mul hgm) ?_
    refine ae_restrict_of_forall_mem hA fun s hs => ?_
    rw [Real.norm_of_nonneg (hfg0 s hs)]
    have := two_mul_le_add_sq (f s) (g s)
    simp only [Pi.add_apply]
    linarith
  have hpwi : IntegrableOn (fun s => p s * ‖w s‖) A := by
    refine Integrable.mono' hfgi (hp.mul hwA.norm) ?_
    refine ae_restrict_of_forall_mem hA fun s hs => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hp0 s hs) (norm_nonneg _))]
    exact hpfg s hs
  refine ⟨hpwi, ?_⟩
  -- Hölder with exponents `2, 2`
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hfL : MemLp f (ENNReal.ofReal 2) (volume.restrict A) := by
    rw [h2]; exact (memLp_two_iff_integrable_sq hfm).2 hf2i
  have hgL : MemLp g (ENNReal.ofReal 2) (volume.restrict A) := by
    rw [h2]; exact (memLp_two_iff_integrable_sq hgm).2 hg2i
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_restrict_of_forall_mem hA fun s _ => Real.sqrt_nonneg (q s))
    (ae_restrict_of_forall_mem hA fun s _ =>
      mul_nonneg (norm_nonneg (w s)) (Real.sqrt_nonneg (ω s))) hfL hgL
  have hfq : ∫ s in A, f s ^ (2 : ℝ) = ∫ s in A, q s :=
    setIntegral_congr_fun hA fun s hs => by rw [Real.rpow_two, hf2 s hs]
  have hgq : ∫ s in A, g s ^ (2 : ℝ) = ∫ s in A, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s :=
    setIntegral_congr_fun hA fun s hs => by rw [Real.rpow_two, hg2 s hs]
  rw [hfq, hgq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  have hmono : ∫ s in A, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s ≤
      ∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s := by
    refine setIntegral_mono_set hwi ?_ (Filter.Eventually.of_forall hA0)
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
      (le_of_lt hs)
  calc ∫ s in A, p s * ‖w s‖ ≤ ∫ s in A, f s * g s :=
        setIntegral_mono_on hpwi hfgi hA hpfg
    _ ≤ √(∫ s in A, q s) * √(∫ s in A, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := hH
    _ ≤ √(∫ s in A, q s) * √(∫ s in Ioi 0, ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)

end UnforcedLeray.B0079
