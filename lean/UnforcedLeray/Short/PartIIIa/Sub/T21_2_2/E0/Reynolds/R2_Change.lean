import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# `PartIII-a:T21/2/2/2/2/2`: the change of variables to the fixed cell (SP 3036-3037)

`E_0(ζ) = adjE0 d m (movingPhi ν φ r)` with `d = c/√a`, `a = a(r)`, `r = revAge ν s ζ`. The
substitution `x = √a y` (`integral_moving_weight`, `norm_movingPhi_sq`, `wtF0_eq_periodicWeight`)
gives `a⁻³ ∫_{C_c} p_d⁻¹(x/√a)|φ(r, x)|² dx`, the integrand of `reyIntegrand`, for every `ζ > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- `1 - ν z > 0` at reverse moving time `ζ > 0`. -/
theorem chgD_pos {ν s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    0 < 1 - ν * (movingZ ν s - ζ) := by
  have hνs : 0 ≤ ν * s := mul_nonneg hν.le hs
  have h1 : 0 < 1 + ν * s := by linarith
  have hM : ν * (s / (1 + ν * s)) < 1 := by
    rw [← mul_div_assoc, div_lt_one h1]
    linarith
  have e : 1 - ν * (movingZ ν s - ζ) = (1 - ν * (s / (1 + ν * s))) + ν * ζ := by
    unfold movingZ clockA
    ring
  have hp : 0 < ν * ζ := mul_pos hν hζ
  rw [e]
  linarith

/-- `a(r) = 1/(1 - ν z)` at reverse moving time `ζ > 0`. -/
theorem chgClockA_eq {ν s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    clockA ν (revAge ν s ζ) = (1 - ν * (movingZ ν s - ζ))⁻¹ := by
  have hD := (chgD_pos hν hs hζ).ne'
  unfold revAge ageOfZ clockA
  field_simp
  ring

/-- `a(r) > 0` at reverse moving time `ζ > 0`. -/
theorem chgClockA_pos {ν s ζ : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hζ : 0 < ζ) :
    0 < clockA ν (revAge ν s ζ) := by
  rw [chgClockA_eq hν hs hζ]
  exact inv_pos.mpr (chgD_pos hν hs hζ)

/-- **R2: change of variables to the fixed cell** (SP 3036-3037): `y = x/√a`, `dy = dx/a`,
`Φ = a⁻¹φ(r, √a ·)`, `d = c/√a`. -/
theorem reyChange (m : ℝ) : ReyChange m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ
  have hs : 0 ≤ s := by linarith
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  refine Filter.eventually_of_mem (Ioi_mem_nhds hζ.1) ?_
  intro ζ' hζ'
  have hζ'0 : 0 < ζ' := hζ'
  have ha : 0 < clockA ν (revAge ν s ζ') := chgClockA_pos hν hs hζ'0
  have hnorm : ∀ y : ℝ × ℝ, ‖movingPhi ν φ (revAge ν s ζ') y‖ ^ 2 =
      (clockA ν (revAge ν s ζ'))⁻¹ ^ 2 *
        ‖φ (revAge ν s ζ') (Real.sqrt (clockA ν (revAge ν s ζ')) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ')) * y.2)‖ ^ 2 :=
    fun y => norm_movingPhi_sq ha y
  show revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ' =
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x
  unfold revE0 adjE0
  simp only [hnorm]
  have h := integral_moving_weight (ν ^ (-2 : ℝ)) m (clockA ν (revAge ν s ζ')) hc ha
    (fun x => (clockA ν (revAge ν s ζ'))⁻¹ ^ 2 * ‖φ (revAge ν s ζ') x‖ ^ 2)
  rw [h, ← integral_const_mul]
  congr 1
  funext x
  rw [wtF0_eq_periodicWeight _ m _ hc ha]
  unfold reyIntegrand
  ring

end UnforcedLeray.Short.IIIa.E0
