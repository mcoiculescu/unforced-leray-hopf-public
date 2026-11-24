import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin

/-!
# `EarlyZ1Gained` (source 4163-4166, 5594-5599)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

variable {c mZ ρb γ ν : ℝ}

theorem zge_meas (γ ν : ℝ) : Measurable (fun p : Chart => ginv γ ν p) := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  fun_prop

theorem zge_tail_le (K : ℝ) (hK : 0 ≤ K) (a : ℝ) (x : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (hx : ∀ᵐ p ∂(z1Measure c mZ), (x : Chart → Ten3) p = 0 ∨ 1 ≤ K * ginv γ ν p) :
    z1Tail c mZ a (x : Chart → Ten3) ≤ ENNReal.ofReal K * ‖x‖ₑ := by
  have hdens : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((zge_meas γ ν).pow_const 2)
  have hm : AEMeasurable (fun p : Chart => ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) (gainZ1Measure c mZ γ ν) :=
    ((Lp.aestronglyMeasurable x).enorm).pow_const _
  have hI : ∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)
      = ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
    unfold gainZ1Measure
    exact lintegral_withDensity_eq_lintegral_mul₀' hdens.aemeasurable hm
  have hnorm : ‖x‖ₑ = (∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  set E := ENNReal.ofReal K with hE
  have hpt : ∀ᵐ p ∂(z1Measure c mZ), ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
      ≤ E ^ (2 : ℝ) * (ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [hx] with p hp
    rcases hp with h0 | hp
    · rw [h0]; simp
    have h1 : (1 : ℝ≥0∞) ≤ E ^ (2 : ℝ) * ENNReal.ofReal (ginv γ ν p ^ 2) := by
      have h2 : 1 ≤ (K * ginv γ ν p) ^ 2 := one_le_pow₀ hp
      have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((K * ginv γ ν p) ^ 2) := by
        simpa using ENNReal.ofReal_le_ofReal h2
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hK] at h3
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
      _ ≤ _ := lintegral_mono_ae hpt
  unfold z1Tail z1Part
  calc _ ≤ (E ^ (2 : ℝ) * ∫⁻ p, ‖(x : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = E * ‖x‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hnorm, ← ENNReal.rpow_mul]
        norm_num


theorem earlyZ1Gained : EarlyZ1Gained := by
  intro c mZ ρb γ ν χ hχ hγ hν T a
  set F := (thinPart T - chiOStr c mZ ρb γ ν hχ (thinPart T)).fst with hFdef
  have hFA : (F : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      fun p => (1 - cutFun χ ν p) • (T.fst : Chart → Ten3) p := by
    have hc : F = T.fst - NearInst.mulBdd (E := Ten3) (μ := gainZ1Measure c mZ γ ν) (cutFun χ ν)
        (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) T.fst := rfl
    have h1 := Lp.coeFn_sub T.fst (NearInst.mulBdd (E := Ten3) (μ := gainZ1Measure c mZ γ ν)
        (cutFun χ ν) (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) T.fst)
    have h2 := NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainZ1Measure c mZ γ ν) (cutFun χ ν)
        (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) T.fst
    rw [hc]
    filter_upwards [h1, h2] with p e1 e2
    rw [e1]
    simp only [Pi.sub_apply]
    rw [e2]
    simp [sub_smul]
  have hdens : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((zge_meas γ ν).pow_const 2)
  have hac : z1Measure c mZ ≪ gainZ1Measure c mZ γ ν := by
    unfold gainZ1Measure
    apply withDensity_absolutelyContinuous' hdens.aemeasurable
    refine Filter.Eventually.of_forall fun p => ?_
    have : 0 < ginv γ ν p := by
      unfold ginv; exact inv_pos.2 (gainG_pos' _ _ _)
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hFA' := hac.ae_le hFA
  set G := UnforcedLeray.Short.IIIa.gainG γ ν (3 / (2 * ν)) with hG
  have hGpos : 0 < G := gainG_pos' _ _ _
  have hx : ∀ᵐ p ∂(z1Measure c mZ), (F : Chart → Ten3) p = 0 ∨ 1 ≤ G * ginv γ ν p := by
    filter_upwards [hFA'] with p hp
    by_cases h : 3 / (2 * ν) ≤ p.1
    · left
      rw [hp]
      have : χ (ν * p.1) = 1 := hχ.one _ (by
        rw [div_le_iff₀ (by positivity)] at h
        linarith)
      simp [cutFun, this]
    · right
      rw [not_le] at h
      have hm : max p.1 0 ≤ 3 / (2 * ν) := max_le h.le (by positivity)
      have := gainG_mono hγ hν (le_max_right p.1 0) hm
      unfold ginv
      rw [← div_eq_mul_inv, le_div_iff₀ (gainG_pos' _ _ _)]
      simpa using this
  refine (zge_tail_le G hGpos.le a F hx).trans ?_
  gcongr
  have hn : ‖F‖ₑ ≤ ‖T.fst‖ₑ := by
    rw [Lp.enorm_def, Lp.enorm_def]
    apply eLpNorm_mono_ae
    filter_upwards [hFA] with p hp
    rw [hp, norm_smul]
    have h0 := (hχ.range (ν * p.1)).1
    have h1 := (hχ.range (ν * p.1)).2
    have : ‖1 - cutFun χ ν p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      unfold cutFun; constructor <;> linarith
    calc ‖1 - cutFun χ ν p‖ * ‖(T.fst : Chart → Ten3) p‖ ≤ 1 * ‖(T.fst : Chart → Ten3) p‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  refine hn.trans ?_
  rw [← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  have := norm_nonneg T.snd
  simp only [ENNReal.toReal_one, div_one, Real.rpow_one]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
