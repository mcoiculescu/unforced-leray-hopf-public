import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.A
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Int
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.QuotGInt
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds

/-!


Fixed cutoff `c = max s (τ-η)`. For `r ∈ (s, c]` we have `τ - r ≥ η`, so the pointwise limit of the
difference quotient is the chain rule for `b ↦ heatSG b (F r) x` at `b = ν(τ-r) > 0` (`convTD_A`).
Domination for `|t-τ| < η/2`: the mean value theorem on the segment between `ν(t-r)` and `ν(τ-r)`
(both `≥ νη/2`) with the derivative bound from `HeatWBounds`; the resulting bound is `ν · M₀`,
constant in `r` and `t`. Source: `the November 2 reference manuscript`, lines
2074-2093, 2103-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CTDIn

lemma mvt_bd {φ φ' : ℝ → ℝ} {M : ℝ} :
    ∀ {u v : ℝ}, (∀ ξ ∈ uIcc u v, HasDerivAt φ (φ' ξ) ξ) → (∀ ξ ∈ uIcc u v, |φ' ξ| ≤ M) →
      |φ v - φ u| ≤ M * |v - u| := by
  have key : ∀ a b : ℝ, a ≤ b → (∀ ξ ∈ Icc a b, HasDerivAt φ (φ' ξ) ξ) →
      (∀ ξ ∈ Icc a b, |φ' ξ| ≤ M) → |φ b - φ a| ≤ M * |b - a| := by
    intro a b hab hd hbd
    rcases eq_or_lt_of_le hab with h | h
    · subst h
      simp
    · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope φ φ' h
        (fun ξ hξ => (hd ξ hξ).continuousAt.continuousWithinAt)
        (fun ξ hξ => hd ξ (Ioo_subset_Icc_self hξ))
      have hne : b - a ≠ 0 := sub_ne_zero.2 (ne_of_gt h)
      have e : φ b - φ a = φ' c * (b - a) := by
        rw [hceq, div_mul_cancel₀ _ hne]
      rw [e, abs_mul, abs_of_nonneg (sub_nonneg.2 hab)]
      exact mul_le_mul_of_nonneg_right (hbd c (Ioo_subset_Icc_self hc)) (sub_nonneg.2 hab)
  intro u v hd hbd
  rcases le_total u v with h | h
  · rw [uIcc_of_le h] at hd hbd
    exact key u v h hd hbd
  · rw [uIcc_of_ge h] at hd hbd
    have := key v u h hd hbd
    calc |φ v - φ u| = |φ u - φ v| := abs_sub_comm _ _
      _ ≤ M * |u - v| := this
      _ = M * |v - u| := by rw [abs_sub_comm]

lemma mono_prod {A A' P P' B : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hP : 0 ≤ P) (hPP : P ≤ P')
    (hB : 0 ≤ B) : 2 * A * P * B ≤ 2 * A' * P' * B := by
  have h1 : 2 * A * P ≤ 2 * A' * P' :=
    mul_le_mul (mul_le_mul_of_nonneg_left hAA (by norm_num)) hPP hP (by linarith)
  exact mul_le_mul_of_nonneg_right h1 hB

end CTDIn

open CTDIn in
/-- **`PartII-b:T22/1/11/4/2`** The inner part of the difference quotient converges. -/
theorem convTD_Quot_inner : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Quot_Inner := by
  intro ν s T hν hsT B F hF hb τ hτ x η hη
  have hb0 : ∀ r ∈ Icc s T, WB B (F r) := fun r hr => (hb r hr).1
  have hs0 : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  have hB0 : 0 ≤ B := by
    have h0 := (hb s hs0).1 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  have hsc : s ≤ max s (τ - η) := le_max_left _ _
  have hcτ : max s (τ - η) ≤ τ := max_le hτ.1 (by linarith)
  have hcT : max s (τ - η) ≤ T := hcτ.trans hτ.2
  have hrη : ∀ r ∈ Ioc s (max s (τ - η)), r ≤ τ - η := by
    intro r hr
    rcases le_max_iff.1 hr.2 with h | h
    · linarith [hr.1]
    · exact h
  have hm : 0 < ν * (η / 2) := mul_pos hν (half_pos hη)
  -- uniform derivative bound on the segment
  have hDbd : ∀ r ∈ Icc s T, ∀ ξ : ℝ, ν * (η / 2) ≤ ξ → ξ ≤ ν * (T - s) →
      |∑ i : Fin 2, heatSGd i ξ (B0579.pd i (F r)) x| ≤
        4 * Real.exp (ν * (T - s)) * (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B := by
    intro r hr ξ h1 h2
    have hξ : 0 < ξ := lt_of_lt_of_le hm h1
    have hpow : ξ ^ (-(1 / 2 : ℝ)) ≤ (ν * (η / 2)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hm h1 (by norm_num)
    have hpow0 : 0 ≤ ξ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hξ.le _
    have hE : Real.exp ξ ≤ Real.exp (ν * (T - s)) := Real.exp_le_exp.2 h2
    have hc : 1 ≤ Real.cosh x.2 := Real.one_le_cosh _
    have hbi : ∀ i : Fin 2, |heatSGd i ξ (B0579.pd i (F r)) x| ≤
        2 * Real.exp (ν * (T - s)) * (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B := by
      intro i
      have h := (heatWBounds B (B0579.pd i (F r)) ((hb r hr).2 i)).2 ξ hξ i x
      have habs : |heatSGd i ξ (B0579.pd i (F r)) x| ≤
          |heatSGd i ξ (B0579.pd i (F r)) x| * Real.cosh x.2 :=
        le_mul_of_one_le_right (abs_nonneg _) hc
      have hmono := mono_prod (A := Real.exp ξ) (A' := Real.exp (ν * (T - s)))
        (P := 1 + ξ ^ (-(1 / 2 : ℝ))) (P' := 1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ)))
        (B := B) (Real.exp_pos ξ).le hE (by linarith) (by linarith) hB0
      linarith
    rw [Fin.sum_univ_two]
    calc |heatSGd 0 ξ (B0579.pd 0 (F r)) x + heatSGd 1 ξ (B0579.pd 1 (F r)) x|
        ≤ |heatSGd 0 ξ (B0579.pd 0 (F r)) x| + |heatSGd 1 ξ (B0579.pd 1 (F r)) x| :=
          abs_add_le _ _
      _ ≤ _ := by linarith [hbi 0, hbi 1]
  -- pointwise limit
  have hlim_pt : ∀ r ∈ Ioc s (max s (τ - η)),
      Tendsto (fun t : ℝ => (t - τ)⁻¹ * (heatSG (ν * (t - r)) (F r) x -
        heatSG (ν * (τ - r)) (F r) x)) (𝓝[Icc s T \ {τ}] τ)
        (𝓝 (ν * ∑ i : Fin 2, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x)) := by
    intro r hr
    have hrτ : r < τ := lt_of_le_of_lt (hrη r hr) (by linarith)
    have hrI : r ∈ Icc s T := ⟨hr.1.le, hr.2.trans hcT⟩
    have hφ := convTD_A B (F r) (hF.c1 r hrI) (hb r hrI).1 (hb r hrI).2 (ν * (τ - r))
      (mul_pos hν (by linarith)) x
    have hlin : HasDerivAt (fun t : ℝ => ν * (t - r)) ν τ := by
      simpa using ((hasDerivAt_id τ).sub_const r).const_mul ν
    have hcomp := hφ.comp τ hlin
    have hs := (hasDerivAt_iff_tendsto_slope.1 hcomp).mono_left
      (nhdsWithin_mono τ (show Icc s T \ {τ} ⊆ {τ}ᶜ from fun t ht => ht.2))
    have hval : ν * ∑ i : Fin 2, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x =
        (∑ i : Fin 2, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x) * ν := mul_comm _ _
    rw [hval]
    refine Tendsto.congr (fun t => ?_) hs
    simp only [slope_def_field, Function.comp_apply, div_eq_inv_mul]
  -- integrability of the limit integrands on [s, c]
  have hgi : ∀ i : Fin 2, IntervalIntegrable
      (fun r : ℝ => heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x) volume s (max s (τ - η)) := by
    intro i
    exact (convTD_Quot_gint ν s T hν hsT B F hF hb τ hτ x i).mono_set
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc_of_le hsc hcτ))
  -- domination
  have hbdd : ∀ᶠ t in 𝓝[Icc s T \ {τ}] τ, ∀ᵐ r ∂volume,
      r ∈ uIoc s (max s (τ - η)) → ‖(t - τ)⁻¹ * (heatSG (ν * (t - r)) (F r) x -
        heatSG (ν * (τ - r)) (F r) x)‖ ≤ ν * (4 * Real.exp (ν * (T - s)) *
          (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B) := by
    have hball : ∀ᶠ t in 𝓝 τ, t ∈ Metric.ball τ (η / 2) :=
      Metric.ball_mem_nhds τ (half_pos hη)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with t ht htb
    refine ae_of_all _ fun r hr => ?_
    rw [Set.uIoc_of_le hsc] at hr
    have htne : t - τ ≠ 0 := sub_ne_zero.2 ht.2
    have hab0 : |t - τ| ≠ 0 := abs_ne_zero.2 htne
    have hdist : |t - τ| < η / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using htb
    have hdist' := abs_lt.1 hdist
    have hrI : r ∈ Icc s T := ⟨hr.1.le, hr.2.trans hcT⟩
    have htI : t ∈ Icc s T := ht.1
    have hrη' := hrη r hr
    have hu : ν * (η / 2) ≤ ν * (t - r) :=
      mul_le_mul_of_nonneg_left (by linarith [hdist'.1]) hν.le
    have hv : ν * (η / 2) ≤ ν * (τ - r) :=
      mul_le_mul_of_nonneg_left (by linarith) hν.le
    have hu' : ν * (t - r) ≤ ν * (T - s) :=
      mul_le_mul_of_nonneg_left (by linarith [htI.2, hrI.1]) hν.le
    have hv' : ν * (τ - r) ≤ ν * (T - s) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ.2, hrI.1]) hν.le
    have hdiff : ∀ ξ ∈ uIcc (ν * (t - r)) (ν * (τ - r)),
        ν * (η / 2) ≤ ξ ∧ ξ ≤ ν * (T - s) := by
      intro ξ hξ
      rcases Set.mem_uIcc.1 hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    have hd : ∀ ξ ∈ uIcc (ν * (t - r)) (ν * (τ - r)),
        HasDerivAt (fun b => heatSG b (F r) x) (∑ i : Fin 2, heatSGd i ξ (B0579.pd i (F r)) x) ξ := by
      intro ξ hξ
      exact convTD_A B (F r) (hF.c1 r hrI) (hb r hrI).1 (hb r hrI).2 ξ
        (lt_of_lt_of_le hm (hdiff ξ hξ).1) x
    have hbd := mvt_bd (φ := fun b => heatSG b (F r) x)
      (φ' := fun ξ => ∑ i : Fin 2, heatSGd i ξ (B0579.pd i (F r)) x)
      (M := 4 * Real.exp (ν * (T - s)) * (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B)
      (u := ν * (t - r)) (v := ν * (τ - r)) hd
      (fun ξ hξ => hDbd r hrI ξ (hdiff ξ hξ).1 (hdiff ξ hξ).2)
    have habs : |ν * (τ - r) - ν * (t - r)| = ν * |t - τ| := by
      rw [show ν * (τ - r) - ν * (t - r) = -(ν * (t - τ)) by ring, abs_neg, abs_mul,
        abs_of_pos hν]
    rw [habs] at hbd
    have h1 : |heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x| ≤
        (4 * Real.exp (ν * (T - s)) * (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B) *
          (ν * |t - τ|) := by
      rw [abs_sub_comm]
      exact hbd
    show ‖(t - τ)⁻¹ * (heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_inv]
    calc |t - τ|⁻¹ * |heatSG (ν * (t - r)) (F r) x - heatSG (ν * (τ - r)) (F r) x|
        ≤ |t - τ|⁻¹ * ((4 * Real.exp (ν * (T - s)) * (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B) *
          (ν * |t - τ|)) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (abs_nonneg _))
      _ = ν * (4 * Real.exp (ν * (T - s)) * (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B) := by
        field_simp
  -- measurability
  have hmeas : ∀ᶠ t in 𝓝[Icc s T \ {τ}] τ,
      AEStronglyMeasurable (fun r : ℝ => (t - τ)⁻¹ * (heatSG (ν * (t - r)) (F r) x -
        heatSG (ν * (τ - r)) (F r) x)) (volume.restrict (uIoc s (max s (τ - η)))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hsubT : uIcc s (max s (τ - η)) ⊆ uIcc s T :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc_of_le hsc hcT)
    have hI1 := convTD_Int ν s T hν hsT B F hF hb0 t ht.1 x
    have hI2 := convTD_Int ν s T hν hsT B F hF hb0 τ hτ x
    rw [Set.uIoc_of_le hsc]
    exact (((hI1.mono_set hsubT).1.sub (hI2.mono_set hsubT).1).const_mul _).aestronglyMeasurable
  have hlimpt : ∀ᵐ r ∂volume, r ∈ uIoc s (max s (τ - η)) →
      Tendsto (fun t : ℝ => (t - τ)⁻¹ * (heatSG (ν * (t - r)) (F r) x -
        heatSG (ν * (τ - r)) (F r) x)) (𝓝[Icc s T \ {τ}] τ)
        (𝓝 (ν * ∑ i : Fin 2, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x)) := by
    refine ae_of_all _ fun r hr => ?_
    rw [Set.uIoc_of_le hsc] at hr
    exact hlim_pt r hr
  have hT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => ν * (4 * Real.exp (ν * (T - s)) *
      (1 + (ν * (η / 2)) ^ (-(1 / 2 : ℝ))) * B))
    hmeas hbdd (intervalIntegrable_const) hlimpt
  have e2 : ∫ r in s..max s (τ - η), ν * ∑ i : Fin 2, heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x
      = ν * ∑ i : Fin 2, ∫ r in s..max s (τ - η), heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun i _ => hgi i)]
  rw [← e2]
  refine Tendsto.congr (fun t => ?_) hT
  rw [intervalIntegral.integral_const_mul]

end UnforcedLeray.Short.IIb.CylPDE
