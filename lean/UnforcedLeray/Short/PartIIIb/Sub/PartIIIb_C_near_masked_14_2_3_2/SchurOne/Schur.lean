import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Real.ConjExponents

/-!
# Abstract weighted Schur test (lintegral form)

Helper for `PartIII-b:C/near/masked/14/2/3/2` (`SchurOne`, source 3996-4011).
Pure measure theory: for a nonnegative kernel `K` and a positive finite weight `w` with
`∫ K(y,·) w ≤ A w(y)` and `∫ K(·,z) w ≤ B w(z)`, the operator `g ↦ ∫ K g` has
`L²`-norm squared at most `A B`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.SchurOneHelp

variable {X : Type*} [MeasurableSpace X]

/-- Pointwise Cauchy-Schwarz: `(∫ k g)² ≤ (∫ k w)(∫ k g² / w)`. -/
lemma cs_step (μ : Measure X) (k w g : X → ℝ≥0∞)
    (hk : AEMeasurable k μ) (hw : AEMeasurable w μ) (hg : AEMeasurable g μ)
    (hw0 : ∀ x, w x ≠ 0) (hwt : ∀ x, w x ≠ ⊤) :
    (∫⁻ x, k x * g x ∂μ) ^ 2 ≤ (∫⁻ x, k x * w x ∂μ) * ∫⁻ x, k x * (g x ^ 2 * (w x)⁻¹) ∂μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hsq : ∀ P : ℝ≥0∞, (P ^ (1 / 2 : ℝ)) ^ 2 = P := by
    intro P
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq2 : ∀ P : ℝ≥0∞, (P ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = P := by
    intro P
    rw [← ENNReal.rpow_mul]
    norm_num
  set f : X → ℝ≥0∞ := fun x => (k x * w x) ^ (1 / 2 : ℝ) with hf
  set h : X → ℝ≥0∞ := fun x => (k x * (g x ^ 2 * (w x)⁻¹)) ^ (1 / 2 : ℝ) with hh
  have hfh : ∀ x, (f * h) x = k x * g x := by
    intro x
    simp only [Pi.mul_apply, hf, hh]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have e : k x * w x * (k x * (g x ^ 2 * (w x)⁻¹)) = (k x * g x) ^ 2 * (w x * (w x)⁻¹) := by
      ring
    rw [e, ENNReal.mul_inv_cancel (hw0 x) (hwt x), mul_one]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hfm : AEMeasurable f μ := by
    simp only [hf]
    exact ((hk.mul hw).pow_const _)
  have hhm : AEMeasurable h μ := by
    simp only [hh]
    exact (hk.mul ((hg.pow_const 2).mul (hw.inv))).pow_const _
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hfm hhm
  have e1 : ∫⁻ x, (f * h) x ∂μ = ∫⁻ x, k x * g x ∂μ := lintegral_congr fun x => hfh x
  have e2 : ∫⁻ x, f x ^ (2 : ℝ) ∂μ = ∫⁻ x, k x * w x ∂μ :=
    lintegral_congr fun x => hsq2 _
  have e3 : ∫⁻ x, h x ^ (2 : ℝ) ∂μ = ∫⁻ x, k x * (g x ^ 2 * (w x)⁻¹) ∂μ :=
    lintegral_congr fun x => hsq2 _
  rw [e1, e2, e3] at hH
  calc (∫⁻ x, k x * g x ∂μ) ^ 2
      ≤ ((∫⁻ x, k x * w x ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, k x * (g x ^ 2 * (w x)⁻¹) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ zero_le hH 2
    _ = (∫⁻ x, k x * w x ∂μ) * ∫⁻ x, k x * (g x ^ 2 * (w x)⁻¹) ∂μ := by
        rw [mul_pow, hsq, hsq]

/-- **Abstract Schur test** (lintegral form). If `∫ K(y,z) w(z) dz ≤ A w(y)` and
`∫ K(y,z) w(y) dy ≤ B w(z)` with `0 < w < ∞`, then `∫ (∫ K(y,z) g(z) dz)² dy ≤ A B ∫ g²`. -/
theorem schur_test (μ : Measure X) [SFinite μ] (K : X → X → ℝ≥0∞) (w : X → ℝ≥0∞)
    (A B : ℝ≥0∞)
    (hK : Measurable (fun p : X × X => K p.1 p.2)) (hw : Measurable w)
    (hw0 : ∀ x, w x ≠ 0) (hwt : ∀ x, w x ≠ ⊤)
    (h1 : ∀ y, ∫⁻ z, K y z * w z ∂μ ≤ A * w y)
    (h2 : ∀ z, ∫⁻ y, K y z * w y ∂μ ≤ B * w z)
    (g : X → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, (∫⁻ z, K y z * g z ∂μ) ^ 2 ∂μ ≤ A * B * ∫⁻ z, g z ^ 2 ∂μ := by
  have hKy : ∀ y, Measurable (K y) := fun y => hK.comp measurable_prodMk_left
  have hKz : ∀ z, Measurable (fun y => K y z) := fun z => hK.comp measurable_prodMk_right
  have hwi : Measurable (fun x => (w x)⁻¹) := hw.inv
  have hpt : ∀ y, (∫⁻ z, K y z * g z ∂μ) ^ 2 ≤
      A * w y * ∫⁻ z, K y z * (g z ^ 2 * (w z)⁻¹) ∂μ := by
    intro y
    calc (∫⁻ z, K y z * g z ∂μ) ^ 2
        ≤ (∫⁻ z, K y z * w z ∂μ) * ∫⁻ z, K y z * (g z ^ 2 * (w z)⁻¹) ∂μ :=
          cs_step μ (K y) w g (hKy y).aemeasurable hw.aemeasurable hg.aemeasurable hw0 hwt
      _ ≤ (A * w y) * ∫⁻ z, K y z * (g z ^ 2 * (w z)⁻¹) ∂μ := by
          gcongr
          exact h1 y
      _ = A * w y * ∫⁻ z, K y z * (g z ^ 2 * (w z)⁻¹) ∂μ := rfl
  -- joint measurability of the swapped integrand
  have hjoint : Measurable (fun p : X × X => w p.1 * (K p.1 p.2 * (g p.2 ^ 2 * (w p.2)⁻¹))) := by
    apply Measurable.mul (hw.comp measurable_fst)
    exact hK.mul ((hg.comp measurable_snd |>.pow_const 2).mul ((hw.comp measurable_snd).inv))
  calc ∫⁻ y, (∫⁻ z, K y z * g z ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ y, A * w y * ∫⁻ z, K y z * (g z ^ 2 * (w z)⁻¹) ∂μ ∂μ := lintegral_mono hpt
    _ = ∫⁻ y, A * ∫⁻ z, w y * (K y z * (g z ^ 2 * (w z)⁻¹)) ∂μ ∂μ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ (hwt y)]
        ring
    _ = A * ∫⁻ y, ∫⁻ z, w y * (K y z * (g z ^ 2 * (w z)⁻¹)) ∂μ ∂μ := by
        exact lintegral_const_mul _ (hjoint.lintegral_prod_right' (ν := μ))
    _ = A * ∫⁻ z, ∫⁻ y, w y * (K y z * (g z ^ 2 * (w z)⁻¹)) ∂μ ∂μ := by
        congr 1
        exact lintegral_lintegral_swap (hjoint.aemeasurable)
    _ ≤ A * ∫⁻ z, B * g z ^ 2 ∂μ := by
        gcongr with z
        have inner : ∫⁻ y, w y * (K y z * (g z ^ 2 * (w z)⁻¹)) ∂μ
            = (∫⁻ y, K y z * w y ∂μ) * (g z ^ 2 * (w z)⁻¹) := by
          rw [← lintegral_mul_const]
          · exact lintegral_congr fun y => by ring
          · exact (hKz z).mul hw
        rw [inner]
        calc (∫⁻ y, K y z * w y ∂μ) * (g z ^ 2 * (w z)⁻¹)
            ≤ (B * w z) * (g z ^ 2 * (w z)⁻¹) := by
              gcongr
              exact h2 z
          _ = B * g z ^ 2 := by
              have e : w z * (g z ^ 2 * (w z)⁻¹) = g z ^ 2 := by
                calc w z * (g z ^ 2 * (w z)⁻¹) = g z ^ 2 * (w z * (w z)⁻¹) := by ring
                  _ = g z ^ 2 := by rw [ENNReal.mul_inv_cancel (hw0 z) (hwt z), mul_one]
              calc (B * w z) * (g z ^ 2 * (w z)⁻¹) = B * (w z * (g z ^ 2 * (w z)⁻¹)) := by ring
                _ = B * g z ^ 2 := by rw [e]
    _ = A * B * ∫⁻ z, g z ^ 2 ∂μ := by
        rw [lintegral_const_mul _ (hg.pow_const 2), mul_assoc]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.SchurOneHelp
