import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-b:C/rep/2/1/1` : Minkowski in `λ` (SP 3636-3640)

`SepDomMinkowski` from the one-variable Minkowski integral inequality
`NonUniqueEuler.Conv.eLpNorm_lintegral_le`, after rewriting the `L^q` slice norm `lqNorm`
as an `eLpNorm` and pulling the constant `ofReal (l^a)` out of each slice.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepMink_lqNorm_eq_eLpNorm {q : ℝ} (hq : 1 ≤ q) (f : Space → ℝ≥0∞) :
    lqNorm q f = eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hneT : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hneT, ENNReal.toReal_ofReal hq0.le]
  simp only [lqNorm, enorm_eq_self]

theorem sepDomMinkowski_proved : UnforcedLeray.Short.PartIIIb.Concrete.SepDomMinkowski := by
  intro a j D q hq g hgm τ
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hq
  have hpne : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hsk : Measurable (fun x : Space => IIIa.sepKd j D x) := by
    unfold IIIa.sepKd
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) measurable_const
  have hH : Measurable fun p : (Space × ℝ) × Space =>
      IIIa.sepKd j D (p.1.1 - p.1.2 • p.2) * g (τ + 2 * Real.log p.1.2) p.2 := by
    have h1 : Measurable fun p : (Space × ℝ) × Space => IIIa.sepKd j D (p.1.1 - p.1.2 • p.2) :=
      hsk.comp (measurable_fst.fst.sub (measurable_fst.snd.smul measurable_snd))
    have h2 : Measurable fun p : (Space × ℝ) × Space => g (τ + 2 * Real.log p.1.2) p.2 :=
      hgm.comp ((measurable_const.add (measurable_const.mul
        (Real.measurable_log.comp measurable_fst.snd))).prodMk measurable_snd)
    exact h1.mul h2
  have hA : Measurable fun p : Space × ℝ => ENNReal.ofReal (p.2 ^ a) :=
    ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)
  have hI : Measurable fun p : Space × ℝ =>
      ∫⁻ z : Space, IIIa.sepKd j D (p.1 - p.2 • z) * g (τ + 2 * Real.log p.2) z :=
    hH.lintegral_prod_right'
  have hMeas : Measurable (Function.uncurry fun (x : Space) (l : ℝ) =>
      ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, IIIa.sepKd j D (x - l • z) * g (τ + 2 * Real.log l) z) :=
    hA.mul hI
  have key : ∀ l : ℝ, eLpNorm (fun y => ENNReal.ofReal (l ^ a) *
      ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) (ENNReal.ofReal q) volume
      = ENNReal.ofReal (l ^ a) * lqNorm q
        (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) := by
    intro l
    rw [← sepMink_lqNorm_eq_eLpNorm hq]
    exact lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top _
  calc lqNorm q (IIIa.sepDom a j D g τ)
      = eLpNorm (fun y => ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
          ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z)
          (ENNReal.ofReal q) volume := by
        rw [sepMink_lqNorm_eq_eLpNorm hq]
        rfl
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, eLpNorm (fun y => ENNReal.ofReal (l ^ a) *
          ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z)
          (ENNReal.ofReal q) volume :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hMeas.aemeasurable hp1 hpne
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * lqNorm q
          (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) :=
        lintegral_congr key

end UnforcedLeray.Short.PartIIIb.Concrete
