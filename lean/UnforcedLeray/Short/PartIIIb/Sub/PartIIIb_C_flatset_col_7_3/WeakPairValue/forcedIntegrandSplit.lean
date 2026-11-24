import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_6

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem forcedIntegrandSplit : ForcedIntegrandSplit := by
  intro c ν μ Φ hΦ f h vR p hp hvel hres
  have hs : (0:ℝ) < p.1 := hp
  have hR0 : (0:ℝ) < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  -- `s^{-3/2} = s^{-1} (√s)^{-1}`
  have ht : p.1 ^ (-(3 / 2 : ℝ)) = p.1⁻¹ * (Real.sqrt p.1)⁻¹ := by
    have h1 : p.1 ^ (-(3 / 2 : ℝ)) * Real.sqrt p.1 = p.1⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
      norm_num [Real.rpow_neg_one]
    calc p.1 ^ (-(3 / 2 : ℝ))
        = p.1 ^ (-(3 / 2 : ℝ)) * Real.sqrt p.1 * (Real.sqrt p.1)⁻¹ :=
          (mul_inv_cancel_right₀ hR0.ne' _).symm
      _ = p.1⁻¹ * (Real.sqrt p.1)⁻¹ := by rw [h1]
  have hh : ∀ i, ((h p i : ℝ) : ℂ) = (p.1 : ℂ) * f p i := fun i => hvel i
  have hsC : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hRC : ((Real.sqrt p.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
  rw [hres]
  simp only [forcedIntegrand, UnforcedLeray.Short.IIIa.flatIntegrand, NearInst.velC, NearInst.merC, zetaPhi,
    PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, Complex.conj_ofReal,
    Complex.real_smul, PiLp.toLp_apply, WithLp.ofLp_toLp, Pi.zero_apply, Complex.ofReal_zero,
    mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add, Finset.sum_const_zero, ht]
  simp only [hh]
  push_cast
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
