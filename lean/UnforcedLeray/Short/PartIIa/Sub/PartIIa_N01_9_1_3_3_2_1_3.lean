import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1

/-!
# `PartII-a:N01/9/1/3/3/2/1/3` (decomposition): `HardyGradKernel`

Source `the November 2 reference manuscript`
lines 1684-1689, 3541-3552.  Substitute `σ = t s`, Minkowski in `L²(s^{-3/2}ds)`, Beta integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

/-- **(H1)** Beta integral finite iff `a > -1/4` (tex 3541-3552):
`∫₀¹ t^{a-1}(1-t)^{-1/2} t^{1/4} dt < ∞`. -/
def HardyBetaFinite : Prop :=
  ∀ a : ℝ, -(1 / 4 : ℝ) < a →
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) *
      ENNReal.ofReal (t ^ (1 / 4 : ℝ)) < ∞

/-- **(H2)** Substitution `σ = t s` (tex 1684-1689): for `s > 0`,
`∫₀^s k(s,σ)Φ(σ)dσ = ν^{-1/2}s^{-1/2} ∫₀¹ t^{a-1}(1-t)^{-1/2} Φ(ts) dt`. -/
def HardySubst : Prop :=
  ∀ (a ν s : ℝ), 0 < ν → 0 < s → ∀ Φ : ℝ → ℝ≥0∞, Measurable Φ →
    ∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel a ν s σ) * Φ σ =
      ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) *
        ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)

/-- **(H3)** Minkowski's integral inequality in `L²(s^{-3/2}ds)` with the dilation
`‖Φ(t·)‖ = t^{1/4}‖Φ‖` (tex 3541-3552). -/
def HardyMinkowski : Prop :=
  ∀ (w : ℝ → ℝ≥0∞), Measurable w → ∀ Φ : ℝ → ℝ≥0∞, Measurable Φ →
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (∫⁻ t in Ioo (0 : ℝ) 1, w t * Φ (t * s)) ^ 2 ≤
      (∫⁻ t in Ioo (0 : ℝ) 1, w t * ENNReal.ofReal (t ^ (1 / 4 : ℝ))) ^ 2 *
        ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2

theorem hardyGradKernel_of (h1 : HardyBetaFinite) (h2 : HardySubst) (h3 : HardyMinkowski) :
    HardyGradKernel := by
  intro a ν ha hν
  set I : ℝ≥0∞ := ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) *
      ENNReal.ofReal (t ^ (1 / 4 : ℝ)) with hI
  have hIfin : I < ∞ := h1 a ha
  refine ⟨ν⁻¹ * I.toReal ^ 2, ?_⟩
  intro Φ hΦ
  have hwm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) := by
    fun_prop
  have h3' := h3 _ hwm Φ hΦ
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel a ν s σ) * Φ σ) ^ 2 =
      ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)) ^ 2) := by
    intro s hs
    have hs' : 0 < s := hs
    rw [h2 a ν s hν hs' Φ hΦ, mul_pow]
    have key : s ^ (-(1 / 2 : ℝ)) * (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ^ 2 =
        ν⁻¹ * s ^ (-(3 / 2 : ℝ)) := by
      have e1 : (ν ^ (-(1 / 2 : ℝ))) ^ 2 = ν⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hν.le]; norm_num [Real.rpow_neg_one]
      have e2 : s ^ (-(1 / 2 : ℝ)) * (s ^ (-(1 / 2 : ℝ))) ^ 2 = s ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs'.le, ← Real.rpow_add hs']; norm_num
      calc _ = (ν ^ (-(1 / 2 : ℝ))) ^ 2 * (s ^ (-(1 / 2 : ℝ)) * (s ^ (-(1 / 2 : ℝ))) ^ 2) := by ring
        _ = _ := by rw [e1, e2]
    have hm : ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ^ 2 =
        ENNReal.ofReal ν⁻¹ * ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), key]
    calc _ = (ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ^ 2) *
          (∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)) ^ 2 := by ring
      _ = _ := by rw [hm]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hIr : I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hIfin.ne).symm
  calc _ ≤ ENNReal.ofReal ν⁻¹ * (I ^ 2 * ∫⁻ σ in Ioi (0 : ℝ),
          ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2) := by gcongr
    _ = _ := by
        conv_lhs => rw [hIr]
        rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]

end UnforcedLeray.Short.PartIIa.N01
