import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# `PartIII-b:C/rep/8/2/3`: the weighted train bounds, decomposed

Source: `the November 2 reference manuscript` 5464-5465, 5477-5482 (weighted train
coefficients), young train 5484-5495, train IVP 2045-2051.

`TrainMomentAt` has three parts; here they are three source facts, and `trainMoment_of` assembles
`SeqData.TrainMoment` from them (only the order of choice of the constants is handled here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(a) Measurability of the weight** (source 5464-5465): `iteratedFDeriv` of order `≥ 1` is
measurable for any function (`measurable_fderiv`, `iteratedFDeriv_succ_eq_comp_left`); order `0`
needs `trainFv`, `trainFp` continuous (`smooth_v`, `smooth_p`) and `trainFpsi` measurable
(`ψ(s,q,η) = -lim_M ∫_η^M ∂_ηψ` with `∂_ηψ` from `stream`, using `stream_decay`; source 2045-2051). -/
def TMMeas : Prop := ∀ L : ReturnLevel, Measurable (trainWeight 4 L)

/-- **(b) The weight is polynomially bounded on the young range** (source 5477-5482, 5484-5495:
Gaussian train separation `c = ν⁻²`, `a = 1+νs ≤ 2.1`, fixed-order derivatives of the Gaussians and
their `(1+|η|)^4`-weighted decay; `P_ν = Cν^{-k}`). -/
def TMPt (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ p : Chart,
    0 < p.1 → p.1 ≤ 1 / (D.level n).ν → trainWeight 4 (D.level n) p ≤ C * (D.level n).ν⁻¹ ^ k

/-- **(c) `L²` bound of `s^{5/2}𝔴_4`** (source 5464-5465, 5477-5482): `srcMeasure = π•ageμ c (-3/2)`
(`lintegral_ageμ`, `Lib/AxisymmetricB/Lift.lean:62`), the square is `π∫_0^{1/ν} s^{7/2}∫_cell 𝔴_4² dq/c dη ds`
and the cell integral is bounded uniformly in `s ≤ 1/ν` by Gaussian moments of fixed order
(the young-train Gaussian envelope of the actual train, source 5484-5495). -/
def TML2 (D : SeqData) (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    eLpNorm (youngWeight (D.level n)) 2 (srcMeasure (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k)

/-- Assembly of `SeqData.TrainMoment` from (a), (b), (c): the two families of constants are
merged using `ν_n ≤ 1` eventually. -/
theorem trainMoment_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : TMMeas) (h2 : TMPt D dm dp) (h3 : TML2 D dm dp) : D.TrainMoment := by
  obtain ⟨C1, k1, e1⟩ := h2 hst
  obtain ⟨C2, k2, e2⟩ := h3 hst
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨max (max C1 C2) 0, max k1 k2, ?_⟩
  filter_upwards [e1, e2, hle] with n a b c
  have hx : (1 : ℝ) ≤ ((D.level n).ν)⁻¹ := by
    have : (D.level n).ν ≤ 1 := c.1
    exact one_le_inv₀ (D.level n).ν_pos |>.2 this
  have hC0 : 0 ≤ max (max C1 C2) 0 := le_max_right _ _
  have m1 : ∀ C k, C ≤ max (max C1 C2) 0 → k ≤ max k1 k2 →
      C * ((D.level n).ν)⁻¹ ^ k ≤ max (max C1 C2) 0 * ((D.level n).ν)⁻¹ ^ max k1 k2 := by
    intro C k hC hk
    calc C * ((D.level n).ν)⁻¹ ^ k ≤ max (max C1 C2) 0 * ((D.level n).ν)⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hk) hC0
  refine ⟨h1 _, fun p hp hq => (a p hp hq).trans (m1 _ _ ?_ (le_max_left _ _)), ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact b.trans (ENNReal.ofReal_le_ofReal (m1 _ _ ((le_max_right _ _).trans (le_max_left _ _))
      (le_max_right _ _)))

end UnforcedLeray.Short.PartIIIb.Concrete
