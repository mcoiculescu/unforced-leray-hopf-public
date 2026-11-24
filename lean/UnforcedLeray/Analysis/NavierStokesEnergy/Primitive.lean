import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Energy equality from a positive-time differential identity

A velocity path continuous in genuine L² up to time zero inherits the energy
identity at zero once its squared norm has the differential identity at positive
times and its dissipation is nonnegative. Integrability of the dissipation at
zero is a conclusion. Applying this to an actual Navier--Stokes solution still
requires proving the positive-time identity from its equation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Topology

namespace UnforcedLeray.NavierStokesEnergy

def primitive (U : ℝ → L2Space) (t : ℝ) : ℝ := -(‖U t‖ ^ 2) / 2

private theorem primitive_continuousOn {T : ℝ} {U : ℝ → L2Space}
    (hU : ContinuousOn U (Icc (0 : ℝ) T)) :
    ContinuousOn (primitive U) (Icc (0 : ℝ) T) := by
  exact ((hU.norm.pow 2).neg.div_const 2)

private theorem primitive_hasDerivAt {t : ℝ} {U : ℝ → L2Space} {D : ℝ → ℝ}
    (hD : HasDerivAt (fun s => ‖U s‖ ^ 2) (-2 * D t) t) :
    HasDerivAt (primitive U) (D t) t := by
  change HasDerivAt (fun s : ℝ => -(‖U s‖ ^ 2) / 2) (D t) t
  exact (hD.neg.div_const (2 : ℝ)).congr_deriv (by ring)

/-- On every time interval inside `[0,T]`, the positive-time identity itself
forces integrability of the dissipation, including when the left endpoint is
zero. No energy bound or endpoint integrability is assumed. -/
theorem dissipation_integrableOn_Ioc {T : ℝ} {U : ℝ → L2Space} {D : ℝ → ℝ}
    (hU : ContinuousOn U (Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s => ‖U s‖ ^ 2) (-2 * D t) t)
    (hnonneg : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ D t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IntegrableOn D (Ioc a b) := by
  have hcont : ContinuousOn (primitive U) (Icc a b) :=
    (primitive_continuousOn hU).mono (fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)
  have hinside (t : ℝ) (ht : t ∈ Ioo a b) : t ∈ Ioo (0 : ℝ) T :=
    ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  exact intervalIntegral.integrableOn_deriv_of_nonneg hcont
    (fun t ht => primitive_hasDerivAt (hderiv t (hinside t ht)))
    (fun t ht => hnonneg t (hinside t ht))

/-- Full energy equality at any two times, including the initial time. -/
theorem energy_equality {T : ℝ} {U : ℝ → L2Space} {D : ℝ → ℝ}
    (hU : ContinuousOn U (Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s => ‖U s‖ ^ 2) (-2 * D t) t)
    (hnonneg : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ D t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (1 / 2 : ℝ) * ‖U b‖ ^ 2 + (∫ t in Ioo a b, D t) =
      (1 / 2 : ℝ) * ‖U a‖ ^ 2 := by
  have hcont : ContinuousOn (primitive U) (Icc a b) :=
    (primitive_continuousOn hU).mono (fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)
  have hinside (t : ℝ) (ht : t ∈ Ioo a b) : t ∈ Ioo (0 : ℝ) T :=
    ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  have hint : IntervalIntegrable D volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (dissipation_integrableOn_Ioc hU hderiv hnonneg ha hab hb)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun t ht => primitive_hasDerivAt (hderiv t (hinside t ht))) hint
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hFTC
  unfold primitive at hFTC
  linarith

end UnforcedLeray.NavierStokesEnergy
