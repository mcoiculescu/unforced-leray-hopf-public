import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg

/-!
# `Z1TailGained` (source 5571-5584, 5601)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {c mZ ρb γ ν : ℝ}

theorem zgl_one_le (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) :
    1 ≤ Real.exp (γ / ν) * ginv γ ν p := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  rw [← Real.exp_neg, ← Real.exp_add]
  apply Real.one_le_exp
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  have h1 : 0 < 1 + ν * max p.1 0 := by positivity
  have : γ * max p.1 0 / (1 + ν * max p.1 0) ≤ γ / ν := by
    rw [div_le_div_iff₀ h1 hν]
    nlinarith [mul_nonneg hγ hs]
  linarith

theorem zgl_meas (γ ν : ℝ) : Measurable (fun p : Chart => ginv γ ν p) := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  fun_prop

theorem zgl_tail_le (hγ : 0 ≤ γ) (hν : 0 < ν) (a : ℝ) (x : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) :
    z1Tail c mZ a (x : Chart → Ten3) ≤ ENNReal.ofReal (Real.exp (γ / ν)) * ‖x‖ₑ := by
  have hdens : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((zgl_meas γ ν).pow_const 2)
  have hm : AEMeasurable (fun p : Chart => ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) (gainZ1Measure c mZ γ ν) :=
    ((Lp.aestronglyMeasurable x).enorm).pow_const _
  have hI : ∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)
      = ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
    unfold gainZ1Measure
    exact lintegral_withDensity_eq_lintegral_mul₀' hdens.aemeasurable hm
  have hnorm : ‖x‖ₑ = (∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  set E := ENNReal.ofReal (Real.exp (γ / ν)) with hE
  have hpt : ∀ p : Chart, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
      ≤ E ^ (2 : ℝ) * (ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) := by
    intro p
    have h1 : (1 : ℝ≥0∞) ≤ E ^ (2 : ℝ) * ENNReal.ofReal (ginv γ ν p ^ 2) := by
      have := zgl_one_le hγ hν p
      have h2 : 1 ≤ (Real.exp (γ / ν) * ginv γ ν p) ^ 2 := one_le_pow₀ this
      have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((Real.exp (γ / ν) * ginv γ ν p) ^ 2) := by
        simpa using ENNReal.ofReal_le_ofReal h2
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Real.exp_pos _).le] at h3
      rw [hE, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      exact h3
    calc ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
        = 1 * ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) := (one_mul _).symm
      _ ≤ (E ^ (2 : ℝ) * ENNReal.ofReal (ginv γ ν p ^ 2)) * ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) :=
          mul_le_mul_left h1 _
      _ = _ := by ring
  have hle : ∫⁻ p in {p : Chart | a ≤ p.1}, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)
      ≤ E ^ (2 : ℝ) * ∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν) := by
    rw [hI, ← lintegral_const_mul' _ _ (by simp [hE])]
    calc _ ≤ ∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) :=
          setLIntegral_le_lintegral _ _
      _ ≤ _ := lintegral_mono hpt
  unfold z1Tail z1Part
  calc _ ≤ (E ^ (2 : ℝ) * ∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = E * ‖x‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hnorm, ← ENNReal.rpow_mul]
        norm_num

theorem z1TailGained : Z1TailGained := by
  intro c mZ ρb γ ν hγ hν T a
  refine (zgl_tail_le hγ hν a (thinPart T).fst).trans ?_
  gcongr
  have e : (thinPart T).fst = T.fst := rfl
  rw [e, ← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  have := norm_nonneg T.snd
  simp only [ENNReal.toReal_one, div_one, Real.rpow_one]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
