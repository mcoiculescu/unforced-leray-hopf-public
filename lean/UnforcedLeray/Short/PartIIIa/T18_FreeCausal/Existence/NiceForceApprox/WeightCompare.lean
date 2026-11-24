import UnforcedLeray.Short.PartIIIa.Sub.T18_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_Gain

/-!
# Part III-a, task `PartIII-a:T18/2/3/2`: comparison of the weighted `𝒯` norm with `L²(Lebesgue)`

Proves `NiceWeightCompare` (`Sub/T18_2_3.lean`). Source of record:
`the November 2 reference manuscript`, lines 3427-3440 ("the weights `s^{-1/2}`
and `g^{-2}` are bounded above and below on compact subintervals of `(0,∞)`").

Proof: `Axi.lintegral_ageμ` writes `‖g⁻¹H‖_𝒯²` as an integral over `(0,∞) × cell` with density
`c⁻¹ s^{-1/2}`. On the strip `α ≤ s ≤ β` the factor `g⁻¹` lies between `exp(-|γ|/ν)` and
`exp(|γ|/ν)` (`gainG_bounds`) and `s^{-1/2}` between `β^{-1/2}` and `α^{-1/2}`. Off the strip `H`
vanishes on the cell. The square root is handled in `ℝ≥0∞` by `ENNReal.rpow_le_rpow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Elementary facts -/

theorem nwc_rpow_neg_half {s : ℝ} (hs : 0 < s) : s ^ (-1 / 2 : ℝ) = (Real.sqrt s)⁻¹ := by
  rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hs.le]

theorem nwc_cell_eq (c : ℝ) : qCell c = B0579.cell c := by
  unfold qCell B0579.cell
  rw [neg_div]

theorem nwc_tnorm2_nonneg (T : Fin 2 → Fin 2 → ℂ) : 0 ≤ tnorm2 T := by
  unfold tnorm2
  exact Real.sqrt_nonneg _

theorem nwc_tnorm2_zero : tnorm2 (0 : Fin 2 → Fin 2 → ℂ) = 0 := by
  unfold tnorm2
  simp

theorem nwc_tnorm2_smul {r : ℝ} (hr : 0 ≤ r) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (r • T) = r * tnorm2 T := by
  unfold tnorm2
  have h : ∀ i j, ‖(r • T) i j‖ ^ 2 = r ^ 2 * ‖T i j‖ ^ 2 := by
    intro i j
    rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hr, mul_pow]
  simp only [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

theorem nwc_measurable_tnorm2 {H : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hH : ∀ i j, Measurable fun p => H p i j) : Measurable fun p => tnorm2 (H p) := by
  unfold tnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((hH i j).norm).pow_const 2

theorem nwc_gainG_pos (γ ν s : ℝ) : 0 < gainG γ ν s :=
  Real.exp_pos _

theorem nwc_tnorm2_gainConj (γ ν : ℝ) (H : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν H p) = (gainG γ ν p.1)⁻¹ * tnorm2 (H p) := by
  have e : gainConj γ ν H p = (gainG γ ν p.1)⁻¹ • H p := rfl
  rw [e]
  exact nwc_tnorm2_smul (inv_nonneg.2 (nwc_gainG_pos γ ν p.1).le) (H p)

theorem nwc_measurable_gainG (γ ν : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 := by
  have hdiv : Measurable fun p : ℝ × (ℝ × ℝ) => γ * p.1 / (1 + ν * p.1) := by
    simp only [div_eq_mul_inv]
    exact (measurable_const.mul measurable_fst).mul
      (measurable_const.add (measurable_const.mul measurable_fst)).inv
  unfold gainG
  exact Real.continuous_exp.measurable.comp hdiv

/-- `∫⁻ ‖G‖ₑ² dageμ` as an integral over the cell (uses `Axi.lintegral_ageμ`). -/
theorem nwc_lintegral_eq {c : ℝ} (hc : 0 < c) {G : ℝ × (ℝ × ℝ) → ℝ} (hG : Measurable G) :
    ∫⁻ p, ‖G p‖ₑ ^ 2 ∂ageμ c (-1 / 2) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * ‖G p‖ₑ ^ 2 := by
  rw [lintegral_ageμ hc (-1 / 2) (f := fun p => ‖G p‖ₑ ^ 2) (hG.enorm.pow_const 2),
    nwc_cell_eq]

theorem nwc_eLpNorm_two {X : Type*} [MeasurableSpace X] (f : X → ℝ) (μ : Measure X) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

theorem nwc_sqrt_bound {X Y : ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K) (h : X ≤ ENNReal.ofReal K * Y) :
    X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K ^ (1 / 2 : ℝ)) * Y ^ (1 / 2 : ℝ) := by
  calc X ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal K * Y) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal K ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal (K ^ (1 / 2 : ℝ)) * Y ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hK (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-! ## Pointwise lemmas in `ℝ≥0∞` -/

theorem nwc_ennreal_A {w k a b : ℝ} (hw : 0 ≤ w) (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : w * a ^ 2 ≤ k * b ^ 2) :
    ENNReal.ofReal w * ‖a‖ₑ ^ 2 ≤ ENNReal.ofReal k * ‖b‖ₑ ^ 2 := by
  rw [Real.enorm_eq_ofReal ha, Real.enorm_eq_ofReal hb, ← ENNReal.ofReal_pow ha,
    ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hk]
  exact ENNReal.ofReal_le_ofReal h

theorem nwc_ennreal_B {w k a b : ℝ} (hw : 0 ≤ w) (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b ^ 2 ≤ k * (w * a ^ 2)) :
    ‖b‖ₑ ^ 2 ≤ ENNReal.ofReal k * (ENNReal.ofReal w * ‖a‖ₑ ^ 2) := by
  rw [Real.enorm_eq_ofReal ha, Real.enorm_eq_ofReal hb, ← ENNReal.ofReal_pow ha,
    ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hk]
  exact ENNReal.ofReal_le_ofReal h

/-! ## Real inequalities on the strip -/

theorem nwc_gain_inv_le {γ ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    (gainG γ ν s)⁻¹ ≤ Real.exp (|γ| / ν) := by
  obtain ⟨h1, _⟩ := gainG_bounds (γ := γ) hν hs
  calc (gainG γ ν s)⁻¹ ≤ (Real.exp (-(|γ| / ν)))⁻¹ := inv_anti₀ (Real.exp_pos _) h1
    _ = Real.exp (|γ| / ν) := by rw [Real.exp_neg, inv_inv]

theorem nwc_gain_inv_ge {γ ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    Real.exp (-(|γ| / ν)) ≤ (gainG γ ν s)⁻¹ := by
  obtain ⟨_, h2⟩ := gainG_bounds (γ := γ) hν hs
  rw [Real.exp_neg]
  exact inv_anti₀ (nwc_gainG_pos γ ν s) h2

theorem nwc_real_A {c ν γ α s F : ℝ} (hc : 0 < c) (hν : 0 < ν) (hα : 0 < α) (hs : 0 < s)
    (hsa : α ≤ s) :
    c⁻¹ * s ^ (-1 / 2 : ℝ) * ((gainG γ ν s)⁻¹ * F) ^ 2 ≤
      c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2 * F ^ 2 := by
  have hw : (Real.sqrt s)⁻¹ ≤ (Real.sqrt α)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hα) (Real.sqrt_le_sqrt hsa)
  rw [nwc_rpow_neg_half hs]
  have hg0 : 0 ≤ (gainG γ ν s)⁻¹ := inv_nonneg.2 (nwc_gainG_pos γ ν s).le
  have hsq : ((gainG γ ν s)⁻¹ * F) ^ 2 ≤ Real.exp (|γ| / ν) ^ 2 * F ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hg0 (nwc_gain_inv_le (γ := γ) hν hs.le) 2) (sq_nonneg F)
  calc c⁻¹ * (Real.sqrt s)⁻¹ * ((gainG γ ν s)⁻¹ * F) ^ 2
      ≤ c⁻¹ * (Real.sqrt α)⁻¹ * (Real.exp (|γ| / ν) ^ 2 * F ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw (inv_nonneg.2 hc.le)) hsq (sq_nonneg _)
          (by positivity)
    _ = c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2 * F ^ 2 := by ring

theorem nwc_real_B {c ν γ β s F : ℝ} (hc : 0 < c) (hν : 0 < ν) (hs : 0 < s) (hsb : s ≤ β)
    (hF : 0 ≤ F) :
    F ^ 2 ≤ c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 *
      (c⁻¹ * s ^ (-1 / 2 : ℝ) * ((gainG γ ν s)⁻¹ * F) ^ 2) := by
  have hβ : 0 < β := lt_of_lt_of_le hs hsb
  have hsqβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hE : 0 < Real.exp (|γ| / ν) := Real.exp_pos _
  have hc0 : c ≠ 0 := hc.ne'
  have hsqβ0 : Real.sqrt β ≠ 0 := hsqβ.ne'
  have hE0 : Real.exp (|γ| / ν) ≠ 0 := hE.ne'
  have hw : (Real.sqrt β)⁻¹ ≤ (Real.sqrt s)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hs) (Real.sqrt_le_sqrt hsb)
  rw [nwc_rpow_neg_half hs]
  have hK : 0 ≤ c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 := by positivity
  have hlow : (Real.exp (|γ| / ν))⁻¹ ≤ (gainG γ ν s)⁻¹ := by
    have h := nwc_gain_inv_ge (γ := γ) hν hs.le
    rwa [Real.exp_neg] at h
  have hsq : ((Real.exp (|γ| / ν))⁻¹ * F) ^ 2 ≤ ((gainG γ ν s)⁻¹ * F) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (inv_nonneg.2 hE.le) hF)
      (mul_le_mul_of_nonneg_right hlow hF) 2
  have hid : c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 * (c⁻¹ * (Real.sqrt β)⁻¹) *
      ((Real.exp (|γ| / ν))⁻¹ * F) ^ 2 = F ^ 2 := by
    have e : c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 * (c⁻¹ * (Real.sqrt β)⁻¹) *
        ((Real.exp (|γ| / ν))⁻¹ * F) ^ 2 =
        (c * c⁻¹) * (Real.sqrt β * (Real.sqrt β)⁻¹) *
          (Real.exp (|γ| / ν) ^ 2 * ((Real.exp (|γ| / ν))⁻¹) ^ 2) * F ^ 2 := by ring
    rw [e, mul_inv_cancel₀ hc0, mul_inv_cancel₀ hsqβ0, ← mul_pow, mul_inv_cancel₀ hE0,
      one_pow]
    ring
  calc F ^ 2 = c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 * (c⁻¹ * (Real.sqrt β)⁻¹) *
      ((Real.exp (|γ| / ν))⁻¹ * F) ^ 2 := hid.symm
    _ ≤ c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 * (c⁻¹ * (Real.sqrt s)⁻¹) *
        ((gainG γ ν s)⁻¹ * F) ^ 2 :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (inv_nonneg.2 hc.le)) hK)
          hsq (sq_nonneg _) (by positivity)
    _ = c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 *
        (c⁻¹ * (Real.sqrt s)⁻¹ * ((gainG γ ν s)⁻¹ * F) ^ 2) := by ring

/-! ## The comparison -/

theorem niceWeightCompare : NiceWeightCompare := by
  intro c ν γ α β hc hν hα
  have hK1 : 0 ≤ c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2 := by positivity
  have hK2 : 0 ≤ c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2 := by positivity
  obtain ⟨C, hC1, hC2, hC0⟩ : ∃ C : ℝ,
      (c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) ^ (1 / 2 : ℝ) ≤ C ∧
      (c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) ^ (1 / 2 : ℝ) ≤ C ∧ 0 ≤ C :=
    ⟨max ((c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) ^ (1 / 2 : ℝ))
        ((c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) ^ (1 / 2 : ℝ)),
      le_max_left _ _, le_max_right _ _,
      le_max_of_le_left (Real.rpow_nonneg hK1 _)⟩
  refine ⟨C, hC0, ?_⟩
  intro H hmeas hvan
  -- `H` vanishes on the cell outside the strip, so does `tnorm2 (H p)`
  have hzero : ∀ p : ℝ × (ℝ × ℝ), p.2 ∈ B0579.cell c → (p.1 < α ∨ β < p.1) →
      tnorm2 (H p) = 0 := by
    intro p hx hcase
    have hH0 : H p = 0 := by
      funext i j
      exact hvan p.1 p.2 i j hx hcase
    rw [hH0, nwc_tnorm2_zero]
  have hFm : Measurable fun p => tnorm2 (H p) := nwc_measurable_tnorm2 hmeas
  have hgm : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ :=
    (nwc_measurable_gainG γ ν).inv
  have hGeq : ∀ p : ℝ × (ℝ × ℝ),
      tnorm2 (gainConj γ ν H p) = (gainG γ ν p.1)⁻¹ * tnorm2 (H p) :=
    nwc_tnorm2_gainConj γ ν H
  have hGm : Measurable fun p => tnorm2 (gainConj γ ν H p) := by
    have e : (fun p => tnorm2 (gainConj γ ν H p)) =
        fun p => (gainG γ ν p.1)⁻¹ * tnorm2 (H p) := funext hGeq
    rw [e]
    exact hgm.mul hFm
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hX := nwc_lintegral_eq hc hGm
  -- forward pointwise bound on the strip
  have ptA : ∀ p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 ≤
        ENNReal.ofReal (c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) *
          ‖tnorm2 (H p)‖ₑ ^ 2 := by
    intro p hp
    have hs : 0 < p.1 := hp.1
    rw [hGeq p]
    by_cases hin : α ≤ p.1 ∧ p.1 ≤ β
    · exact nwc_ennreal_A (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs.le _)) hK1
        (mul_nonneg (inv_nonneg.2 (nwc_gainG_pos γ ν p.1).le) (nwc_tnorm2_nonneg (H p)))
        (nwc_tnorm2_nonneg (H p))
        (nwc_real_A hc hν hα hs hin.1)
    · have hout : p.1 < α ∨ β < p.1 := by
        simpa only [not_and_or, not_le] using hin
      rw [hzero p hp.2 hout]
      simp
  -- reverse pointwise bound on the strip
  have ptB : ∀ p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c,
      ‖tnorm2 (H p)‖ₑ ^ 2 ≤
        ENNReal.ofReal (c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) *
          (ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2) := by
    intro p hp
    have hs : 0 < p.1 := hp.1
    rw [hGeq p]
    by_cases hin : α ≤ p.1 ∧ p.1 ≤ β
    · exact nwc_ennreal_B (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs.le _)) hK2
        (mul_nonneg (inv_nonneg.2 (nwc_gainG_pos γ ν p.1).le) (nwc_tnorm2_nonneg (H p)))
        (nwc_tnorm2_nonneg (H p))
        (nwc_real_B hc hν hs hin.2 (nwc_tnorm2_nonneg (H p)))
    · have hout : p.1 < α ∨ β < p.1 := by
        simpa only [not_and_or, not_le] using hin
      rw [hzero p hp.2 hout]
      simp
  have hA : ∫⁻ p, ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 ∂ageμ c (-1 / 2) ≤
      ENNReal.ofReal (c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2 := by
    rw [hX]
    calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2
        ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
            ENNReal.ofReal (c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) *
              ‖tnorm2 (H p)‖ₑ ^ 2 :=
          setLIntegral_mono' hS ptA
      _ = ENNReal.ofReal (c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) *
            ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hB : ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2 ≤
      ENNReal.ofReal (c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) *
        ∫⁻ p, ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 ∂ageμ c (-1 / 2) := by
    rw [hX]
    calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2
        ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
            ENNReal.ofReal (c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) *
              (ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
                ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2) :=
          setLIntegral_mono' hS ptB
      _ = ENNReal.ofReal (c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) *
            ∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
              ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  constructor
  · calc tCalNorm c (gainConj γ ν H)
        = (∫⁻ p, ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ) := by
          unfold tCalNorm
          exact nwc_eLpNorm_two _ _
      _ ≤ ENNReal.ofReal ((c⁻¹ * (Real.sqrt α)⁻¹ * Real.exp (|γ| / ν) ^ 2) ^ (1 / 2 : ℝ)) *
            (∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          nwc_sqrt_bound hK1 hA
      _ ≤ ENNReal.ofReal C *
            (∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hC1) zero_le
      _ = ENNReal.ofReal C *
            eLpNorm (fun p => tnorm2 (H p)) 2
              (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) := by
          rw [nwc_eLpNorm_two]
  · calc eLpNorm (fun p => tnorm2 (H p)) 2 (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c))
        = (∫⁻ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ‖tnorm2 (H p)‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          nwc_eLpNorm_two _ _
      _ ≤ ENNReal.ofReal ((c * Real.sqrt β * Real.exp (|γ| / ν) ^ 2) ^ (1 / 2 : ℝ)) *
            (∫⁻ p, ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ) :=
          nwc_sqrt_bound hK2 hB
      _ ≤ ENNReal.ofReal C *
            (∫⁻ p, ‖tnorm2 (gainConj γ ν H p)‖ₑ ^ 2 ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hC2) zero_le
      _ = ENNReal.ofReal C * tCalNorm c (gainConj γ ν H) := by
          unfold tCalNorm
          rw [nwc_eLpNorm_two]

end UnforcedLeray.Short.IIIa
