import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Algebra.Ring.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Shift invariance of the lower integral of a periodic function over one period. -/
theorem sepPhaseMink_shift (P : ℝ) (hP : 0 < P) (f : ℝ → ℝ≥0∞)
    (hper : ∀ τ, f (τ + P) = f τ) (c : ℝ) :
    ∫⁻ τ in Ioc (0 : ℝ) P, f (τ + c) = ∫⁻ τ in Ioc (0 : ℝ) P, f τ := by
  have : Fact (0 < P) := ⟨hP⟩
  have hp : Function.Periodic f P := hper
  set F : AddCircle P → ℝ≥0∞ := hp.lift with hF
  have hFc : ∀ a : ℝ, F (a : AddCircle P) = f a := fun a => hp.lift_coe a
  have hA := AddCircle.lintegral_preimage P 0 F
  have hB := AddCircle.lintegral_preimage P 0 (fun b => F (b + (c : AddCircle P)))
  rw [zero_add] at hA hB
  have h1 : ∫⁻ τ in Ioc (0 : ℝ) P, f τ = ∫⁻ b : AddCircle P, F b := by
    rw [← hA]
    exact setLIntegral_congr_fun measurableSet_Ioc fun τ _ => (hFc τ).symm
  have h2 : ∫⁻ τ in Ioc (0 : ℝ) P, f (τ + c) = ∫⁻ b : AddCircle P, F (b + (c : AddCircle P)) := by
    rw [← hB]
    refine setLIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
    rw [← AddCircle.coe_add, hFc]
  rw [h1, h2]
  exact lintegral_add_right_eq_self F (c : AddCircle P)

/-- **Minkowski in `λ` and phase invariance** (SP 3637-3646). -/
theorem sepPhaseMink : UnforcedLeray.Short.IIIa.SepPhaseMink := by
  intro P hP W n hW hn hper
  have hFm : Measurable (Function.uncurry fun (τ l : ℝ) => W l * n (τ + 2 * Real.log l)) :=
    (hW.comp measurable_snd).mul
      (hn.comp (measurable_fst.add (measurable_const.mul (Real.measurable_log.comp measurable_snd))))
  have hmink := NonUniqueEuler.Conv.lintegral_lintegral_rpow_le
    (μ := volume.restrict (Ioc (0 : ℝ) P)) (ν := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun τ l => W l * n (τ + 2 * Real.log l)) hFm.aemeasurable (p := (2 : ℝ)) (by norm_num)
  have hWW : ∀ x : ℝ≥0∞, (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  -- Per-`l` identity: the `L²(0,P]` norm of `τ ↦ W l * n(τ + 2 log l)` is `W l` times that of `n`.
  have hslice : ∀ l : ℝ, (∫⁻ τ in Ioc (0 : ℝ) P, (W l * n (τ + 2 * Real.log l)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      = W l * (∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro l
    have hnm : Measurable fun τ : ℝ => n (τ + 2 * Real.log l) ^ (2 : ℝ) :=
      (hn.comp (measurable_id.add_const _)).pow_const _
    have hsh : ∫⁻ τ in Ioc (0 : ℝ) P, n (τ + 2 * Real.log l) ^ (2 : ℝ) =
        ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ) :=
      sepPhaseMink_shift P hP (fun τ => n τ ^ (2 : ℝ)) (fun τ => by simp only [hper]) _
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [lintegral_const_mul _ hnm, hsh, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hWW]
  calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
          (∫⁻ l in Ioo (0 : ℝ) 1, W l * n (τ + 2 * Real.log l)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) * (∫⁻ τ in Ioc (0 : ℝ) P,
          (∫⁻ l in Ioo (0 : ℝ) 1, W l * n (τ + 2 * Real.log l)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) * ∫⁻ l in Ioo (0 : ℝ) 1,
          (∫⁻ τ in Ioc (0 : ℝ) P, (W l * n (τ + 2 * Real.log l)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        by gcongr
    _ = ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) * ∫⁻ l in Ioo (0 : ℝ) 1,
          W l * (∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        congrArg _ (setLIntegral_congr_fun measurableSet_Ioo fun l _ => hslice l)
    _ = ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) * ((∫⁻ l in Ioo (0 : ℝ) 1, W l) *
          (∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) := by
        rw [lintegral_mul_const _ hW]
    _ = (∫⁻ l in Ioo (0 : ℝ) 1, W l) * ((ENNReal.ofReal P)⁻¹ *
          ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        ring

end UnforcedLeray.Short.IIIa

end
