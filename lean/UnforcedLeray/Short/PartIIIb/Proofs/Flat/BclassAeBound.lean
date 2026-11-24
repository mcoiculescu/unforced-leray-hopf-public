import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flat_1

/-!
# Proof of `bclassAeBound` (source: `the November 2 reference manuscript`,
lines 4589-4592)

`‖B‖_a = ess sup_{s>0} e^{-as} s^{-3/2} |B(s)|` (`bNorm`), so for almost every `t > 0`,
`matNorm (B t) ≤ ‖B‖_a e^{at} t^{3/2}`. The essential supremum bounds the integrand almost
everywhere (`ae_le_essSup`), and the finiteness hypothesis converts the bound to reals.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.ConcreteYF

theorem bclassAeBound : FlatAmp.BclassAeBound := by
  unfold FlatAmp.BclassAeBound
  intro a ν B hB
  obtain ⟨-, -, -, -, hfin⟩ := hB
  have hae := (ae_le_essSup (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun s => ENNReal.ofReal (Real.exp (-a * s) * s ^ (-(3 / 2 : ℝ)) * matNorm (B s))))
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with t hFt ht
  have ht0 : 0 < t := ht
  have hr : Real.exp (-a * t) * t ^ (-(3 / 2 : ℝ)) * matNorm (B t)
      ≤ bNorm a B := by
    have h := (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 hFt
    exact h
  have hP : 0 ≤ Real.exp (a * t) * t ^ (3 / 2 : ℝ) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
  have h1 : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
    rw [← Real.exp_add, show a * t + -a * t = 0 by ring, Real.exp_zero]
  have h2 : t ^ (3 / 2 : ℝ) * t ^ (-(3 / 2 : ℝ)) = 1 := by
    rw [Real.rpow_neg ht0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos ht0 _).ne']
  have key : Real.exp (a * t) * t ^ (3 / 2 : ℝ) *
      (Real.exp (-a * t) * t ^ (-(3 / 2 : ℝ)) * matNorm (B t)) = matNorm (B t) := by
    linear_combination (matNorm (B t)) * (t ^ (3 / 2 : ℝ) * t ^ (-(3 / 2 : ℝ))) * h1
      + (matNorm (B t)) * h2
  calc matNorm (B t)
      = Real.exp (a * t) * t ^ (3 / 2 : ℝ) *
          (Real.exp (-a * t) * t ^ (-(3 / 2 : ℝ)) * matNorm (B t)) := key.symm
    _ ≤ Real.exp (a * t) * t ^ (3 / 2 : ℝ) * bNorm a B :=
        mul_le_mul_of_nonneg_left hr hP
    _ = bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) := mul_comm _ _

end UnforcedLeray.Short.PartIIIb.ConcreteYF
