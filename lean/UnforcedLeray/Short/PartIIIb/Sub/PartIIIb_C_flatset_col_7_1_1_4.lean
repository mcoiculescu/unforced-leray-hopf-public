import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_of

/-!
# `HspNormLintegral` (L4): the `Hsp c` norm is the `ageμ c (-3/2)` `L²` norm

Source of record `the November 2 reference manuscript` (norm identity, the `Hsp c`
norm is the `L²(ageμ c (-3/2))` norm of the complexified field).

Proof outline:
* `key`: for real meridional fields `f g`, `vnorm2 (velC f p - velC g p) = ‖f p - g p‖`.
* `Lp` almost everywhere subtraction `Lp.coeFn_sub` transports the pointwise identity.
* `sq_norm_eq_lintegral`: for `f : Lp E 2 μ`, `ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ ofReal (‖f p‖ ^ 2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- Pointwise: the Euclidean norm of the complexified difference is the norm of the real
difference. -/
theorem vnorm2_velC_sub (f g : Chart → Merid) (p : Chart) :
    vnorm2 (NearInst.velC f p - NearInst.velC g p) = ‖f p - g p‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold vnorm2 NearInst.velC
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show ‖((f p).ofLp i : ℂ) - ((g p).ofLp i : ℂ)‖ ^ 2 = ‖(f p - g p).ofLp i‖ ^ 2
  rw [← Complex.ofReal_sub, Complex.norm_real]
  simp

/-- For an `L²` function, the squared norm is the lintegral of the squared pointwise norm. -/
theorem ofReal_sq_norm_eq_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : Lp E 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂μ := by
  have hfin : eLpNorm f 2 μ ≠ ⊤ := (MeasureTheory.Lp.eLpNorm_lt_top f).ne
  have hpow : eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
    simpa using this
  have hI : ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂μ = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ := by
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm, ENNReal.rpow_two]
  rw [hI, ← hpow]
  rw [Lp.norm_def]
  set E2 : ℝ≥0∞ := eLpNorm f 2 μ with hE2
  have hE2sq : E2 ^ (2 : ℝ) = E2 ^ 2 := by
    rw [ENNReal.rpow_two]
  rw [hE2sq]
  have hsq : E2 ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hfin
  rw [← ENNReal.ofReal_toReal hsq]
  congr 1
  rw [ENNReal.toReal_pow]

theorem hspNormLintegral : HspNormLintegral := by
  intro c u v
  have hae : ∀ᵐ p ∂(ageμ c (-3 / 2)),
      ENNReal.ofReal (vnorm2 (NearInst.velC u p - NearInst.velC v p) ^ 2) =
        ENNReal.ofReal (‖(u - v) p‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub u v] with p hp
    rw [vnorm2_velC_sub, hp, Pi.sub_apply]
  rw [lintegral_congr_ae hae]
  exact (ofReal_sq_norm_eq_lintegral (u - v)).symm
