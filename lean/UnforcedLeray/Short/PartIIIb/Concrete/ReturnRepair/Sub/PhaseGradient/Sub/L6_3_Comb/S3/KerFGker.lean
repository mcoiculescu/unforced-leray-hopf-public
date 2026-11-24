import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_1_HRep

/-!
# `kerFGker` (`PartIII-b:C/rep/2/6/3/3/1`, source 3603-3626, 3800-3807, 4171-4200, 5223)

Pointwise identity `kerF T τ i (Gker ν m) (h,z) y = -(l/2) · sepPhi ν m T τ i (l,z) y` with
`l = exp(-h/2)`: `l² = e^{-h}`, `l^{2m+2}·l = e^{-(m+3/2)h}`, `τ + 2 log l = τ - h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Summand factorisation: a constant factor pulls through a double finite sum. -/
theorem sum_jk_const_mul_aux (c : ℂ) (f g : Fin 3 → Fin 3 → ℂ) :
    ∑ j : Fin 3, ∑ k : Fin 3, c * f j k * g j k = c * ∑ j : Fin 3, ∑ k : Fin 3, f j k * g j k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **(L1)** `h`-form of the `sepPhi` integrand. -/
theorem kerFGker : KerFGker := by
  intro ν m T τ i p y
  have hsq : Real.exp (-p.1 / 2) ^ 2 = Real.exp (-p.1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hlog : Real.log (Real.exp (-p.1 / 2)) = -p.1 / 2 := Real.log_exp _
  have hτ : τ + 2 * (-p.1 / 2) = τ - p.1 := by ring
  have hL : ((Real.exp (-p.1 / 2) : ℝ) : ℂ) ^ (2 * m + 2) = Complex.exp (-(m + 1) * (p.1 : ℂ)) := by
    rw [cpow_exp_real_h]
    congr 1
    push_cast
    ring
  have hE : ((Real.exp (-p.1 / 2) : ℝ) : ℂ) * Complex.exp (-(m + 1) * (p.1 : ℂ)) =
      Complex.exp (-(m + 3 / 2) * (p.1 : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [kerF, Gker, sepPhi, hsq, hlog, hτ, hL]
  rw [← hE, sum_jk_const_mul_aux]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
