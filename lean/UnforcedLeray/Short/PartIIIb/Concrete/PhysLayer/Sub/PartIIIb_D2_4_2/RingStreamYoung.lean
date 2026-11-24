import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.HhatYoungPointwise

/-!
# `RingStreamYoung`: the ring stream vanishes near the axis (source 4953-4956, 4996)

With `ρ₀ = R √(10ν/11)`, every `0 < ρ < ρ₀` has `ν R²/ρ² > 11/10`, where `ψ^p_A` vanishes
(`hhatY_psipA_zero`), so the ring stream `ρ ψ^p_A(R²/ρ², …)` is zero there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringStreamYoung_proof (ν : ℝ) (χf : ℝ → ℝ) : RingStreamYoung ν χf := by
  intro hχ hν R hR A τ
  have hνpos : 0 < 10 * ν / 11 := div_pos (mul_pos (by norm_num) hν) (by norm_num)
  refine ⟨R * Real.sqrt (10 * ν / 11), mul_pos hR (Real.sqrt_pos.mpr hνpos), ?_⟩
  intro p hp hpρ
  have ha : Real.sqrt (10 * ν / 11) ^ 2 = 10 * ν / 11 := Real.sq_sqrt hνpos.le
  have hsq : p.1 ^ 2 < (R * Real.sqrt (10 * ν / 11)) ^ 2 :=
    pow_lt_pow_left₀ hpρ hp.le two_ne_zero
  rw [mul_pow, ha] at hsq
  have hpos2 : 0 < p.1 ^ 2 := pow_pos hp 2
  have ht : (11 / 10 : ℝ) < ν * (R ^ 2 / p.1 ^ 2) := by
    rw [← mul_div_assoc, lt_div_iff₀ hpos2]
    linarith
  show p.1 * psiRing ν χf A (merChart R τ p) = 0
  unfold psiRing
  show p.1 * psipA ν χf A (R ^ 2 / p.1 ^ 2) (merChart R τ p).2 = 0
  rw [hhatY_psipA_zero hχ A _ ht, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
