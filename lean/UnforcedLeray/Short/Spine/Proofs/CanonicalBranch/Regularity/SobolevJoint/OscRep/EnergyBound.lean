import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.Cutoff
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.Caccioppoli

/-!


Source of record: `the November 2 reference manuscript`, lines 1134-1140
(local Sobolev/elliptic estimate). The Prop `OscEnergyBound` is proved exactly as stated in
`Short/Spine/Sub/SP_CAN4_4_1.lean`, from `oscCutoff_proof` (Cutoff.lean) and
`oscCaccioppoli_proof` (Caccioppoli.lean).

Argument. Let `a' = a/2`, `b' = b+1`, and let `χ` be the cutoff from `oscCutoff_proof a b a' b'`.
`L := |C|` bounds `(χ')²` on `[a', b']` (compactness). Then:
* `∫ χ² w |φ|² ≤ 1` and `∫ χ'² w |φ|² ≤ L` on `[a', b']`;
* Caccioppoli gives `∫ χ² w |φ'|² ≤ 2(n+2) + 4L` on `[a', b']`;
* `w ≥ 4π a` on `[a, b]`, `χ = 1` on `[a, b]`, and integrands are nonnegative, so
  `4π a ∫_a^b |φ'|² ≤ 2(n+2) + 4L` and `4π a ∫_a^b |φ|² ≤ 1`.
Take `K := (5 + 4L) / (4π a)`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

theorem energyBound_weight_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ oscWeight r := by
  unfold oscWeight
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hr.le

theorem energyBound_weight_ge {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    4 * Real.pi * a ≤ oscWeight r := by
  unfold oscWeight
  have h1 : (1 : ℝ) ≤ Real.exp (r ^ 2 / 4) := Real.one_le_exp (by positivity)
  have hpi : 0 < 4 * Real.pi := by positivity
  calc 4 * Real.pi * a = (4 * Real.pi * 1) * a := by ring
    _ ≤ (4 * Real.pi * Real.exp (r ^ 2 / 4)) * r := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hpi.le) har ha.le
      positivity

theorem oscEnergyBound_proof : UnforcedLeray.Short.Spine.OscEnergyBound := by
  intro a b ha hab
  have ha2 : 0 < a / 2 := by linarith
  have haa2 : a / 2 < a := by linarith
  have hbb : b < b + 1 := by linarith
  have hc : 0 < 4 * Real.pi * a := mul_pos (by positivity) ha
  obtain ⟨χ, hχ, hχ1, hχa, hχb, hχ01⟩ := oscCutoff_proof a b (a / 2) (b + 1) haa2 hab.le hbb
  have hχc : Continuous χ := hχ.continuous
  have hdχc : ContinuousOn (deriv χ) (Icc (a / 2) (b + 1)) :=
    (hχ.continuous_deriv (by simp)).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hdχc.pow 2 : ContinuousOn (fun x => deriv χ x ^ 2) (Icc (a / 2) (b + 1)))
  have hC' : ∀ x ∈ Icc (a / 2) (b + 1), deriv χ x ^ 2 ≤ |C| := by
    intro x hx
    have h : ‖deriv χ x ^ 2‖ ≤ C := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    exact h.trans (le_abs_self C)
  have hwc : Continuous oscWeight := by
    unfold oscWeight
    fun_prop
  have hw_S : ContinuousOn oscWeight (Icc (a / 2) (b + 1)) := hwc.continuousOn
  have hχS : ContinuousOn χ (Icc (a / 2) (b + 1)) := hχc.continuousOn
  have IIc : ∀ (f : ℝ → ℝ) (x y : ℝ), ContinuousOn f (Icc (a / 2) (b + 1)) →
      a / 2 ≤ x → x ≤ y → y ≤ b + 1 → IntervalIntegrable f volume x y := by
    intro f x y hf h1 h2 h3
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h2]
    exact hf.mono (Icc_subset_Icc h1 h3)
  have IIfull : ∀ f : ℝ → ℝ, ContinuousOn f (Icc (a / 2) (b + 1)) →
      IntervalIntegrable f volume (a / 2) (b + 1) :=
    fun f hf => IIc f (a / 2) (b + 1) hf le_rfl (by linarith) le_rfl
  have IIab : ∀ f : ℝ → ℝ, ContinuousOn f (Icc (a / 2) (b + 1)) →
      IntervalIntegrable f volume a b :=
    fun f hf => IIc f a b hf (by linarith) hab.le (by linarith)
  refine ⟨(5 + 4 * |C|) / (4 * Real.pi * a), ?_⟩
  intro n φ hφ hH
  have hφc : ContinuousOn φ (Icc (a / 2) (b + 1)) :=
    hφ.1.continuousOn.mono (fun r hr => lt_of_lt_of_le ha2 hr.1)
  have hdφc : ContinuousOn (deriv φ) (Icc (a / 2) (b + 1)) :=
    (hφ.1.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono
      (fun r hr => lt_of_lt_of_le ha2 hr.1)
  have hn2 : ContinuousOn (fun r => ‖φ r‖ ^ 2) (Icc (a / 2) (b + 1)) := hφc.norm.pow 2
  have hdn2 : ContinuousOn (fun r => ‖deriv φ r‖ ^ 2) (Icc (a / 2) (b + 1)) :=
    hdφc.norm.pow 2
  have hS1 : ContinuousOn (fun r => ‖φ r‖ ^ 2 * oscWeight r) (Icc (a / 2) (b + 1)) :=
    hn2.mul hw_S
  have hS2 : ContinuousOn (fun r => χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2)
      (Icc (a / 2) (b + 1)) :=
    ((hχS.pow 2).mul hw_S).mul hdn2
  have hS3 : ContinuousOn (fun r => χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2)
      (Icc (a / 2) (b + 1)) :=
    ((hχS.pow 2).mul hw_S).mul hn2
  have hS4 : ContinuousOn (fun r => deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2)
      (Icc (a / 2) (b + 1)) :=
    ((hdχc.pow 2).mul hw_S).mul hn2
  have hS5 : ContinuousOn (fun r => oscWeight r * ‖deriv φ r‖ ^ 2) (Icc (a / 2) (b + 1)) :=
    hw_S.mul hdn2
  have hS6 : ContinuousOn (fun r => |C| * (‖φ r‖ ^ 2 * oscWeight r)) (Icc (a / 2) (b + 1)) :=
    continuousOn_const.mul hS1
  have hS7 : ContinuousOn (fun r => 4 * Real.pi * a * ‖deriv φ r‖ ^ 2) (Icc (a / 2) (b + 1)) :=
    continuousOn_const.mul hdn2
  have hS8 : ContinuousOn (fun r => 4 * Real.pi * a * ‖φ r‖ ^ 2) (Icc (a / 2) (b + 1)) :=
    continuousOn_const.mul hn2
  -- non-negativity of the integrands on `(a/2, b+1]`
  have hnn1 : 0 ≤ᵐ[volume.restrict (Ioc (a / 2) (b + 1))]
      (fun r => ‖φ r‖ ^ 2 * oscWeight r) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => ?_)
    show (0 : ℝ) ≤ ‖φ r‖ ^ 2 * oscWeight r
    exact mul_nonneg (sq_nonneg _) (energyBound_weight_nonneg (lt_trans ha2 hr.1))
  have hnn2 : 0 ≤ᵐ[volume.restrict (Ioc (a / 2) (b + 1))]
      (fun r => χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => ?_)
    show (0 : ℝ) ≤ χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (energyBound_weight_nonneg (lt_trans ha2 hr.1)))
      (sq_nonneg _)
  -- (U) the cut-off `L²(w)` bound
  have hU : ∫ r in (a / 2)..(b + 1), χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2 ≤ 1 := by
    calc ∫ r in (a / 2)..(b + 1), χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2
        ≤ ∫ r in (a / 2)..(b + 1), ‖φ r‖ ^ 2 * oscWeight r := by
          apply intervalIntegral.integral_mono_on (by linarith) (IIfull _ hS3) (IIfull _ hS1)
          intro r hr
          show χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2 ≤ ‖φ r‖ ^ 2 * oscWeight r
          have hr0 : 0 < r := lt_of_lt_of_le ha2 hr.1
          have h01 := hχ01 r
          have hχ2 : χ r ^ 2 ≤ 1 := by nlinarith [h01.1, h01.2]
          have hX : 0 ≤ oscWeight r * ‖φ r‖ ^ 2 :=
            mul_nonneg (energyBound_weight_nonneg hr0) (sq_nonneg _)
          have e : χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2 = χ r ^ 2 * (oscWeight r * ‖φ r‖ ^ 2) := by
            ring
          have e' : ‖φ r‖ ^ 2 * oscWeight r = 1 * (oscWeight r * ‖φ r‖ ^ 2) := by ring
          rw [e, e']
          exact mul_le_mul_of_nonneg_right hχ2 hX
      _ ≤ 1 := hH
  -- (V) the cut-off derivative bound
  have hV : ∫ r in (a / 2)..(b + 1), deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2 ≤ |C| := by
    calc ∫ r in (a / 2)..(b + 1), deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2
        ≤ ∫ r in (a / 2)..(b + 1), |C| * (‖φ r‖ ^ 2 * oscWeight r) := by
          apply intervalIntegral.integral_mono_on (by linarith) (IIfull _ hS4) (IIfull _ hS6)
          intro r hr
          show deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2 ≤ |C| * (‖φ r‖ ^ 2 * oscWeight r)
          have h1 := hC' r hr
          have hX : 0 ≤ ‖φ r‖ ^ 2 * oscWeight r :=
            mul_nonneg (sq_nonneg _) (energyBound_weight_nonneg (lt_of_lt_of_le ha2 hr.1))
          have e : deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2
              = deriv χ r ^ 2 * (‖φ r‖ ^ 2 * oscWeight r) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right h1 hX
      _ = |C| * ∫ r in (a / 2)..(b + 1), ‖φ r‖ ^ 2 * oscWeight r :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hH (abs_nonneg C)
      _ = |C| := mul_one _
  -- (J) Caccioppoli on `[a/2, b+1]`
  have hCac := oscCaccioppoli_proof n φ χ (a / 2) (b + 1) ha2 (by linarith) hφ hχ
    (hχa (a / 2) le_rfl) (hχb (b + 1) le_rfl)
  have hJ : ∫ r in (a / 2)..(b + 1), χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2
      ≤ 2 * ((n : ℝ) + 2) + 4 * |C| := by
    have h2 : 2 * ((n : ℝ) + 2) * (∫ r in (a / 2)..(b + 1), χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2)
        ≤ 2 * ((n : ℝ) + 2) * 1 :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    linarith [hCac, h2, hV]
  -- (L) passing to `[a, b]`, where `χ = 1`
  have hEq : ∫ r in a..b, χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2
      = ∫ r in a..b, oscWeight r * ‖deriv φ r‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le hab.le] at hr
    show χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 = oscWeight r * ‖deriv φ r‖ ^ 2
    rw [hχ1 r hr]
    ring
  have hLow : ∫ r in a..b, oscWeight r * ‖deriv φ r‖ ^ 2
      ≤ 2 * ((n : ℝ) + 2) + 4 * |C| := by
    rw [← hEq]
    refine le_trans ?_ hJ
    exact intervalIntegral.integral_mono_interval (by linarith) hab.le (by linarith) hnn2
      (IIfull _ hS2)
  have hLowY : (4 * Real.pi * a) * ∫ r in a..b, ‖deriv φ r‖ ^ 2
      ≤ 2 * ((n : ℝ) + 2) + 4 * |C| := by
    have e : (4 * Real.pi * a) * ∫ r in a..b, ‖deriv φ r‖ ^ 2
        = ∫ r in a..b, 4 * Real.pi * a * ‖deriv φ r‖ ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    have hm : ∫ r in a..b, 4 * Real.pi * a * ‖deriv φ r‖ ^ 2
        ≤ ∫ r in a..b, oscWeight r * ‖deriv φ r‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hab.le (IIab _ hS7) (IIab _ hS5)
      intro r hr
      show 4 * Real.pi * a * ‖deriv φ r‖ ^ 2 ≤ oscWeight r * ‖deriv φ r‖ ^ 2
      exact mul_le_mul_of_nonneg_right (energyBound_weight_ge ha hr.1) (sq_nonneg _)
    linarith [hm, hLow, e]
  have hkey : (4 * Real.pi * a) * ∫ r in a..b, ‖deriv φ r‖ ^ 2
      ≤ (5 + 4 * |C|) * (1 + (n : ℝ)) := by
    nlinarith [hLowY, abs_nonneg C, (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      mul_nonneg (abs_nonneg C) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- (X) the `L²` bound on `[a, b]`
  have hX : (4 * Real.pi * a) * ∫ r in a..b, ‖φ r‖ ^ 2 ≤ 1 := by
    have e : (4 * Real.pi * a) * ∫ r in a..b, ‖φ r‖ ^ 2
        = ∫ r in a..b, 4 * Real.pi * a * ‖φ r‖ ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    have hm : ∫ r in a..b, 4 * Real.pi * a * ‖φ r‖ ^ 2
        ≤ ∫ r in a..b, ‖φ r‖ ^ 2 * oscWeight r := by
      apply intervalIntegral.integral_mono_on hab.le (IIab _ hS8) (IIab _ hS1)
      intro r hr
      show 4 * Real.pi * a * ‖φ r‖ ^ 2 ≤ ‖φ r‖ ^ 2 * oscWeight r
      have := mul_le_mul_of_nonneg_left (energyBound_weight_ge ha hr.1) (sq_nonneg ‖φ r‖)
      linarith
    have hm2 : ∫ r in a..b, ‖φ r‖ ^ 2 * oscWeight r
        ≤ ∫ r in (a / 2)..(b + 1), ‖φ r‖ ^ 2 * oscWeight r :=
      intervalIntegral.integral_mono_interval (by linarith) hab.le (by linarith) hnn1
        (IIfull _ hS1)
    linarith [e, hm, hm2, hH]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hc]
    linarith [hX, abs_nonneg C]
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith [hkey]

end UnforcedLeray.Short.Spine

end
