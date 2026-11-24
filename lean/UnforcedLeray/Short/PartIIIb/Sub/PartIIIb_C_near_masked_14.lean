import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# Decomposition of `farKernelL2_of` (source 3996-4011, 3604-3621, 2683)

Source: `the November 2 reference manuscript`.

The far kernel `farOut` is dominated pointwise by the positive Hardy-type operator `farMaj`
(`sep:kernel` 3604-3610: `|∇K_t(x)| ≤ C|x|^{-4}`, applied to the dilation integral of
`sep:resolvent` 3611-3621), and `farMaj` is bounded `L²(ageμ c (-1/2)) → L²(ageμ c (-3/2))`
(separation of radii on the far region, `∫_{|x|≥d}|x|^{-4} = 4π/d`, Young, `λ^{2μ+1/2}` integrable
for `μ > -3/4`, normalized-phase Minkowski, lifts multiply both norms by `√πR`, 2683).
Measurability of `farOut` is the third piece.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The positive majorant of the masked dilation integral (source 3996-4011): with
`y = chartY R x`, `τ = chartTau R x`,
`∫_0^1 λ^{2μ+2} ∫ |y - λz|^{-4} |𝒩_T f(z, τ + 2 log λ)| 1_{e^δ s < R²/|z'|²} dz dλ`. -/
def farMaj (R c μ δ : ℝ) (f : Chart → Ten3) (x : Chart) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
    ∫⁻ z : Space,
      (if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
        ENNReal.ofReal (‖chartY R x - l • z‖ ^ (-4 : ℝ) *
          UnforcedLeray.Short.IIIa.tensorNorm
            (cartLift R c f (chartTau R x + 2 * Real.log l) z)) else 0)

/-- The output-side majorant `1_{s<S} s^{-1/2} farMaj`. -/
def farMajOut (R c μ δ S : ℝ) (f : Chart → Ten3) (x : Chart) : ℝ≥0∞ :=
  if x.1 < S then ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMaj R c μ δ f x else 0

/-- **Pointwise positive majorant** (source 3604-3610, 3996-4011): from `sep:kernel`,
`‖farOut f x‖ ≤ C · farMajOut f x` for every box tensor, with `C` uniform. -/
def FarOutMajorant : Prop :=
  UnforcedLeray.Short.IIIa.SepKernelBounds →
  ∀ (R c ν δ S μ : ℝ), 0 < R → 0 < c → 0 < ν → 0 < δ → 0 < S → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Chart → Ten3, IsBoxTensor f → ∀ x : Chart,
      ENNReal.ofReal ‖farOut R c ν μ δ S f x‖ ≤ ENNReal.ofReal C * farMajOut R c μ δ S f x

/-- **`L²` bound of the positive Hardy operator** (source 3996-4011, 2683): `farMajOut` is bounded
from `L²(ageμ c (-1/2))` to `L²(ageμ c (-3/2))` on box tensors (squared form). -/
def FarMajL2 : Prop :=
  ∀ (R c δ S μ : ℝ), 0 < R → 0 < c → 0 < δ → 0 < S → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Chart → Ten3, IsBoxTensor f →
      ∫⁻ x, (farMajOut R c μ δ S f x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal C ^ (2 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))

/-- **Measurability of the far kernel output** on box tensors (joint measurability of the masked
dilation integrand, as for `SepPhiMeasurable`). -/
def FarOutMeasurable : Prop :=
  ∀ (R c ν δ S μ : ℝ), 0 < R → 0 < c → 0 < ν → 0 < δ → 0 < S → -(1 / 4) < μ →
    ∀ f : Chart → Ten3, IsBoxTensor f →
      AEStronglyMeasurable (farOut R c ν μ δ S f) (ageμ c (-3 / 2))

theorem farKernelL2_of_parts (h1 : FarOutMajorant) (h2 : FarMajL2) (h3 : FarOutMeasurable)
    (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) : FarKernelL2 := by
  intro R c ν δ S μ hR hc hν hδ hS hμ
  obtain ⟨C1, hC1, hm⟩ := h1 hK R c ν δ S μ hR hc hν hδ hS hμ
  obtain ⟨C2, hC2, hl⟩ := h2 R c δ S μ hR hc hδ hS hμ
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun f hf => ⟨h3 R c ν δ S μ hR hc hν hδ hS hμ f hf, ?_⟩⟩
  have hp : (0 : ℝ) < 2 := by norm_num
  have key : ∫⁻ x, ‖farOut R c ν μ δ S f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
      (ENNReal.ofReal C1 * ENNReal.ofReal C2) ^ (2 : ℝ) *
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
    calc ∫⁻ x, ‖farOut R c ν μ δ S f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        ≤ ∫⁻ x, (ENNReal.ofReal C1) ^ (2 : ℝ) * (farMajOut R c μ δ S f x) ^ (2 : ℝ)
            ∂(ageμ c (-3 / 2)) := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_norm, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          exact ENNReal.rpow_le_rpow (hm f hf x) hp.le
      _ = (ENNReal.ofReal C1) ^ (2 : ℝ) *
            ∫⁻ x, (farMajOut R c μ δ S f x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      _ ≤ (ENNReal.ofReal C1) ^ (2 : ℝ) *
            (ENNReal.ofReal C2 ^ (2 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) :=
          by gcongr; exact hl f hf
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, mul_assoc]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ x, ‖farOut R c ν μ δ S f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / (2 : ℝ))
      ≤ ((ENNReal.ofReal C1 * ENNReal.ofReal C2) ^ (2 : ℝ) *
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
        rw [ENNReal.ofReal_mul hC1]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
