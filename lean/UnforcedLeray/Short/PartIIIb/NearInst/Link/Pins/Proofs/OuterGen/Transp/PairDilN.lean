import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2

/-!
# `OuterPairDilN` (task `PartIII-b:C/near/pins/3/4/2/3/2/2`)

Source `the November 2 reference manuscript` lines 3350-3352.
Transposition of the normalized dilation `dilN a` under the bilinear pairing `outerPair`:
`dilN a F(z) = a^{3/2} F(a z.1, z.2)` a.e., and the scaling `(x, τ) ↦ (a x, τ)` pushes
Lebesgue measure to the constant multiple `a^3 • volume`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0223 UnforcedLeray.PhaseSpace

/-- Scaling of the first factor, `y ↦ (a⁻¹ • y.1, y.2)`, changes variables in a Lebesgue
integral with Jacobian `a^3` (from `map_dil`). -/
theorem pairDilN_integral_scale {P : ℝ} [Fact (0 < P)] {a : ℝ} (ha : 0 < a)
    (K : PSpace P → ℂ) (hK : AEStronglyMeasurable K volume) :
    ∫ y : PSpace P, K (a⁻¹ • y.1, y.2) = a ^ 3 • ∫ z, K z := by
  have hn : Measurable (fun y : PSpace P => (a⁻¹ • y.1, y.2)) :=
    (measurable_fst.const_smul a⁻¹).prodMk measurable_snd
  have hmap : (volume : Measure (PSpace P)).map (fun y : PSpace P => (a⁻¹ • y.1, y.2)) =
      ENNReal.ofReal (a ^ 3) • volume := by
    rw [map_dil (P := P) (inv_pos.2 ha),
      show |((a⁻¹) ^ 3)⁻¹| = a ^ 3 by rw [inv_pow, inv_inv, abs_of_pos (pow_pos ha 3)]]
  have hK' : AEStronglyMeasurable K ((volume : Measure (PSpace P)).map
      (fun y : PSpace P => (a⁻¹ • y.1, y.2))) := by
    rw [hmap]
    exact hK.smul_measure _
  have h1 := integral_map hn.aemeasurable hK'
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg ha.le 3)] at h1
  exact h1.symm

/-- The integrand of the bilinear pairing after the dilation: `z ↦ ⟨Ψ z, w (a z.1, z.2)⟩`. -/
def pairDilK {P : ℝ} [Fact (0 < P)] (a : ℝ) (Ψ w : XC P) (z : PSpace P) : ℂ :=
  dotL (Ψ z) (w (a • z.1, z.2))

theorem outerPairDilN : OuterPairDilN := by
  intro P _ a ha Ψ w
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  have hK : AEStronglyMeasurable (pairDilK a Ψ w) volume := by
    have hg : AEStronglyMeasurable (fun z => dotL (Ψ z) ((dilN a) w z)) volume :=
      dotL.aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable Ψ)
        (Lp.aestronglyMeasurable (dilN a w))
    refine (hg.const_smul ((a ^ (3 / 2 : ℝ))⁻¹)).congr ?_
    filter_upwards [coeFn_dilN ha w] with z hz
    dsimp only [Pi.smul_apply]
    unfold pairDilK
    rw [hz, ContinuousLinearMap.map_smul_of_tower, smul_smul, inv_mul_cancel₀ (by positivity),
      one_smul]
  have hL : outerPair Ψ (dilN a w) = a ^ (3 / 2 : ℝ) • ∫ z, pairDilK a Ψ w z := by
    rw [← integral_smul]
    unfold outerPair
    refine integral_congr_ae ?_
    filter_upwards [coeFn_dilN ha w] with z hz
    unfold pairDilK
    rw [hz, ContinuousLinearMap.map_smul_of_tower]
  have hK1n := pairDilN_integral_scale ha (pairDilK a Ψ w) hK
  have hmn : ∀ y : PSpace P, (a • (a⁻¹ • y.1), y.2) = y := by
    intro y
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hR' : ∫ y : PSpace P, pairDilK a Ψ w (a⁻¹ • y.1, y.2) = ∫ y : PSpace P, dotL (Ψ (a⁻¹ • y.1, y.2)) (w y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [pairDilK]
    rw [hmn y]
  have hK1I : ∫ z, pairDilK a Ψ w z = (a ^ 3)⁻¹ • ∫ y : PSpace P, dotL (Ψ (a⁻¹ • y.1, y.2)) (w y) := by
    have h2 : (a ^ 3)⁻¹ • ∫ y : PSpace P, pairDilK a Ψ w (a⁻¹ • y.1, y.2) = ∫ z, pairDilK a Ψ w z := by
      rw [hK1n, smul_smul, inv_mul_cancel₀ ha3.ne', one_smul]
    rw [← h2, hR']
  have hRHS : outerPair (dilN a⁻¹ Ψ) w =
      (a⁻¹ ^ (3 / 2 : ℝ)) • ∫ y : PSpace P, dotL (Ψ (a⁻¹ • y.1, y.2)) (w y) := by
    rw [← integral_smul]
    unfold outerPair
    refine integral_congr_ae ?_
    filter_upwards [coeFn_dilN (inv_pos.2 ha) Ψ] with z hz
    rw [hz, ContinuousLinearMap.map_smul_of_tower, smul_apply]
  have hs : a ^ (3 / 2 : ℝ) * (a ^ 3)⁻¹ = (a⁻¹) ^ (3 / 2 : ℝ) := by
    have hr : (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      norm_num
    rw [Real.inv_rpow ha.le, ← hr]
    have hne : a ^ (3 / 2 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hL, hRHS, hK1I, smul_smul, hs]

end UnforcedLeray.Short.PartIIIb.NearInst
