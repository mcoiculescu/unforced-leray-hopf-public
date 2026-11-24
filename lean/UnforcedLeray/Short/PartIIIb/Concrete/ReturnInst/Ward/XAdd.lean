import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XAdd.Prim
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Reg

/-!
# `WardXAdd`: additivity of the Ward displacement on old `L²` data
(source 4171-4191, 3603-3629)

Source of record: `the November 2 reference manuscript` (73 pages).

* Receivers with `ϱ² ≤ νR²` (`ν·age ≥ 1`): `χ_y` and `χ_y'` vanish, so the three sides vanish
  (`wardX_eq_zero_of_sq_le`).
* Receivers with `ϱ² > νR²`: `ϱ > R√(5ν/6)`, so `X₀` is additive at the receiver and at every
  point `(ρ, 0, z)`, `ρ > ϱ y`, of the outward primitive (`xa_wardX0_add`: `sepW` is one integral
  whose integrand is integrable for old `L²` data), and the primitive's integrand is integrable
  on `(ϱ y, ∞)` (`xa_outPrim_integrable`), so `integral_add` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xa_outPrim_add {c ν μ R : ℝ} (hc : 0 < c) (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ)
    {g g' : Chart → Ten3} (hg : IsOldL2 c ν g) (hg' : IsOldL2 c ν g') (τ z r : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    outPrim (wardX0 ν μ R c (g + g')) τ r z =
      outPrim (wardX0 ν μ R c g) τ r z + outPrim (wardX0 ν μ R c g') τ r z := by
  unfold outPrim
  have hpt : ∀ ρ ∈ Ioi r, ρ * wardX0 ν μ R c (g + g') τ (!₂[ρ, 0, z] : Space) 2 =
      ρ * wardX0 ν μ R c g τ (!₂[ρ, 0, z] : Space) 2 +
        ρ * wardX0 ν μ R c g' τ (!₂[ρ, 0, z] : Space) 2 := by
    intro ρ hρ
    have hρ' : r < ρ := hρ
    have hρ0 : 0 ≤ ρ := by
      have : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
      linarith
    have hy : R * Real.sqrt (5 * ν / 6) < ϱ (!₂[ρ, 0, z] : Space) := by
      rw [wardFar_varrho ρ z hρ0]; linarith
    rw [xa_wardX0_add hc hν hR hμ hg hg' τ _ hy]
    simp only [PiLp.add_apply]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add (xa_outPrim_integrable hc hν hR hμ hg τ z r hr)
      (xa_outPrim_integrable hc hν hR hμ hg' τ z r hr)]
  ring

theorem wardXAdd_proved : WardXAdd := by
  intro ν μ R c χy hχy hν hR hc hμ g g' hg hg' τ y hy
  by_cases hcase : ϱ y ^ 2 ≤ ν * R ^ 2
  · rw [wardX_eq_zero_of_sq_le hχy (g + g') τ hy hcase, wardX_eq_zero_of_sq_le hχy g τ hy hcase,
      wardX_eq_zero_of_sq_le hχy g' τ hy hcase, add_zero]
  · have hlt : ν * R ^ 2 < ϱ y ^ 2 := not_le.1 hcase
    have hϱ0 : 0 < ϱ y := ϱ_pos hy
    have hr0 : R * Real.sqrt (5 * ν / 6) < ϱ y := by
      by_contra hcon
      have hle : ϱ y ≤ R * Real.sqrt (5 * ν / 6) := not_lt.1 hcon
      have h2 : ϱ y ^ 2 ≤ (R * Real.sqrt (5 * ν / 6)) ^ 2 := pow_le_pow_left₀ hϱ0.le hle 2
      have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith [mul_pos hν (pow_pos hR 2)]
    unfold wardX wardStreamCut
    rw [xa_wardX0_add hc hν hR hμ hg hg' τ y hr0, xa_outPrim_add hc hν hR hμ hg hg' τ (y 2) _ hr0]
    rw [smul_add, mul_add, add_smul, add_add_add_comm]

end UnforcedLeray.Short.PartIIIb.Concrete
