import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L1_Smooth

/-!
# `PartIII-a:T16/1/1/2` : `HeatLerayKJointMeas` (joint measurability of the kernel derivatives)

Source `the November 2 reference manuscript` lines 3597-3610.
On `t > 0`, `K_t(x) = t^{-3/2} K_1(x/√t)` (parabolic scaling of `G_t` and of `∫_t^∞ G_a`),
so `D^m_x K_t(x) = (t^{-3/2} (√t)^{-m}) · (D^m K_1)((√t)^{-1} x)` is a continuous function of
`(t, x)` on `t > 0` times a measurable scalar.  The smoothness input is `heatLerayKSmoothAll`
(L1), which gives `K_1 ∈ C^∞`, hence `D^m K_1` is continuous for every `m`.

The scaling lemmas are copies (prefix `l2_`) of the `PartIII-b` leaves
`heatG_mul_scale_L1`, `mul_rpow_three_halves_L1`, `heatTail_mul_scale_L1`, `heatGTailScale_L1`,
`heatLerayScale_of` and `heatLerayJointMeas_of`, with the restriction `m ≤ 3` removed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Scaling of the heat kernel: `G_{tu}(x) = t^{-3/2} G_u(x/√t)` for `t, u > 0`. -/
theorem l2_heatG_mul_scale (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (x : Space) :
    heatG (t * u) x = t ^ (-(3 / 2 : ℝ)) * heatG u ((Real.sqrt t)⁻¹ • x) := by
  unfold heatG
  have hsn : ‖(Real.sqrt t)⁻¹‖ = (Real.sqrt t)⁻¹ := by
    rw [norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
  have hs : ‖(Real.sqrt t)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / t := by
    rw [norm_smul, hsn, mul_pow, inv_pow, Real.sq_sqrt ht.le, div_eq_inv_mul]
  rw [hs]
  have hpos : 0 ≤ 4 * Real.pi * u := by positivity
  have hmul : 4 * Real.pi * (t * u) = t * (4 * Real.pi * u) := by ring
  rw [hmul, Real.mul_rpow ht.le hpos]
  have hexp : -‖x‖ ^ 2 / (4 * (t * u)) = -(‖x‖ ^ 2 / t) / (4 * u) := by
    field_simp
  rw [hexp, show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, mul_assoc]

/-- `t * t^{-3/2} = t^{-1/2}` for `t > 0`. -/
theorem l2_mul_rpow_three_halves (t : ℝ) (ht : 0 < t) :
    t * t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
  nth_rewrite 1 [← Real.rpow_one t]
  rw [← Real.rpow_add ht]
  congr 1
  norm_num

/-- Scaling of the heat tail: `∫_t^∞ G_a(x) da = t^{-1/2} (∫_1^∞ G_a)(x/√t)`. -/
theorem l2_heatTail_mul_scale (t : ℝ) (ht : 0 < t) (x : Space) :
    heatTail t x = t ^ (-(1 / 2 : ℝ)) * heatTail 1 ((Real.sqrt t)⁻¹ • x) := by
  unfold heatTail
  have h1 := integral_comp_mul_left_Ioi' (fun a => heatG a x) 1 ht
  simp only [mul_one] at h1
  have h2 : ∫ a in Ioi t, heatG a x
      = t * ∫ u in Ioi (1 : ℝ), heatG (t * u) x := by
    rw [← h1, smul_eq_mul]
  have h3 : ∫ u in Ioi (1 : ℝ), heatG (t * u) x
      = ∫ u in Ioi (1 : ℝ), t ^ (-(3 / 2 : ℝ)) * heatG u ((Real.sqrt t)⁻¹ • x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu' : (0 : ℝ) < u := by
      have : (1 : ℝ) < u := hu
      linarith
    exact l2_heatG_mul_scale t u ht hu' x
  rw [h2, h3, integral_const_mul]
  rw [← mul_assoc, l2_mul_rpow_three_halves t ht]

/-- Parabolic scaling of the heat kernel and of its tail (`t > 0`). -/
theorem l2_heatGTailScale (t : ℝ) (ht : 0 < t) (x : Space) :
    heatG t x = t ^ (-(3 / 2 : ℝ)) * heatG 1 ((Real.sqrt t)⁻¹ • x) ∧
    heatTail t x = t ^ (-(1 / 2 : ℝ)) * heatTail 1 ((Real.sqrt t)⁻¹ • x) := by
  constructor
  · have h := l2_heatG_mul_scale t 1 ht one_pos x
    rw [mul_one] at h
    exact h
  · exact l2_heatTail_mul_scale t ht x

/-- Scaling of the heat-Leray kernel: `K_t(x) = t^{-3/2} K_1(x/√t)` for `t > 0`. -/
theorem l2_heatLerayScale (t : ℝ) (ht : 0 < t) (i j : Fin 3) (x : Space) :
    heatLerayK t i j x = t ^ (-(3 / 2 : ℝ)) * heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x) := by
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hc : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 hsq
  have hcc : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = t⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ht.le]
  have hpow : t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) * t⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) + -1 by norm_num, Real.rpow_add ht, Real.rpow_neg_one]
  have hA : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have hT : ∀ y, heatTail t y
      = t ^ (-(1 / 2 : ℝ)) * heatTail 1 ((Real.sqrt t)⁻¹ • y) := fun y => (l2_heatGTailScale t ht y).2
  have hG : ∀ y, heatG t y
      = t ^ (-(3 / 2 : ℝ)) * heatG 1 ((Real.sqrt t)⁻¹ • y) := fun y => (l2_heatGTailScale t ht y).1
  set c : ℝ := (Real.sqrt t)⁻¹ with hc_def
  set A : ℝ := t ^ (-(1 / 2 : ℝ)) with hA_def
  have : Invertible (A * c) := invertibleOfNonzero (mul_pos hA hc).ne'
  have : Invertible A := invertibleOfNonzero hA.ne'
  -- derivative of the scaled tail
  have hfd : ∀ y v, fderiv ℝ (heatTail t) y v
      = (A * c) * fderiv ℝ (heatTail 1) (c • y) v := by
    intro y v
    have e1 : heatTail t = A • (fun z => heatTail 1 (c • z)) :=
      funext fun z => hT z
    have e2 : fderiv ℝ (heatTail t) y
        = A • fderiv ℝ (fun z => heatTail 1 (c • z)) y := by
      rw [e1]
      exact fderiv_const_smul_of_invertible A
    have e3 : fderiv ℝ (fun z => heatTail 1 (c • z)) y
        = c • fderiv ℝ (heatTail 1) (c • y) :=
      fderiv_comp_smul c
    rw [e2, e3]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- second partial of the scaled tail
  have hpart2 : part2 (heatTail t) i j x
      = (A * c) * c * part2 (heatTail 1) i j (c • x) := by
    unfold part2
    have e4 : (fun y => fderiv ℝ (heatTail t) y (coordinateVector j))
        = (A * c) • (fun y => fderiv ℝ (heatTail 1) (c • y) (coordinateVector j)) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hfd y _
    have e5 : fderiv ℝ (fun y => fderiv ℝ (heatTail 1) (c • y) (coordinateVector j)) x
        = c • fderiv ℝ (fun w => fderiv ℝ (heatTail 1) w (coordinateVector j)) (c • x) :=
      fderiv_comp_smul (f := fun w => fderiv ℝ (heatTail 1) w (coordinateVector j)) c
    rw [e4, fderiv_const_smul_of_invertible (A * c), e5]
    simp only [smul_apply, smul_eq_mul]
    ring
  have hite : (if i = j then heatG t x else 0)
      = t ^ (-(3 / 2 : ℝ)) * (if i = j then heatG 1 (c • x) else 0) := by
    split_ifs
    · exact hG x
    · simp
  have hcoef : t ^ (-(3 / 2 : ℝ)) = (A * c) * c := by
    rw [hpow, ← hcc]
    ring
  unfold heatLerayK
  rw [hite, hpart2, hcoef]
  ring

/-- The derivative of order `m` of `K_t` on `t > 0`, written through the scaling identity. -/
theorem l2_iteratedFDeriv_scale (i j : Fin 3) (m : ℕ) (t : ℝ) (ht : 0 < t) (y : Space)
    (hK1 : ContDiff ℝ m (fun x => heatLerayK 1 i j x)) :
    iteratedFDeriv ℝ m (fun x => heatLerayK t i j x) y
      = (t ^ (-(3 / 2 : ℝ)) * ((Real.sqrt t)⁻¹) ^ m) •
        iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j x) ((Real.sqrt t)⁻¹ • y) := by
  have hfun : (fun x => heatLerayK t i j x)
      = fun x => t ^ (-(3 / 2 : ℝ)) * heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x) :=
    funext fun x => l2_heatLerayScale t ht i j x
  rw [hfun]
  have hcomp : ContDiff ℝ m (fun x => heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)) :=
    hK1.comp (contDiff_const_smul _)
  have key : iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)) y
      = ((Real.sqrt t)⁻¹) ^ m • iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j x)
          ((Real.sqrt t)⁻¹ • y) :=
    congrFun (iteratedFDeriv_comp_const_smul ((Real.sqrt t)⁻¹) hK1) y
  have hsc : (fun x => t ^ (-(3 / 2 : ℝ)) * heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x))
      = t ^ (-(3 / 2 : ℝ)) • (fun x => heatLerayK 1 i j ((Real.sqrt t)⁻¹ • x)) := rfl
  rw [hsc, iteratedFDeriv_const_smul_apply hcomp.contDiffAt, key, smul_smul]

/-- **`PartIII-a:T16/1/1/2`**: joint strong measurability in `(t, x)` of all `x`-derivatives of
`K_t` (extended by `0` for `t ≤ 0`). -/
theorem heatLerayKJointMeas : HeatLerayKJointMeas := by
  intro i j m
  have hK1 : ContDiff ℝ ∞ (fun x => heatLerayK 1 i j x) := heatLerayKSmoothAll 1 one_pos i j
  have hK1m : ContDiff ℝ m (fun x => heatLerayK 1 i j x) :=
    hK1.of_le (by exact_mod_cast le_top)
  -- continuity of the `m`-th derivative of `K_1`
  have hG : Continuous (fun y => iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j x) y) :=
    ContDiff.continuous_iteratedFDeriv le_rfl hK1m
  -- measurability of the global candidate
  have hs : Measurable (fun q : ℝ × Space => (Real.sqrt q.1)⁻¹ • q.2) :=
    ((Real.continuous_sqrt.measurable.comp measurable_fst).inv).smul measurable_snd
  have hcomp2 : StronglyMeasurable
      (fun q : ℝ × Space => iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j x)
        ((Real.sqrt q.1)⁻¹ • q.2)) :=
    hG.comp_stronglyMeasurable hs.stronglyMeasurable
  have hsc2 : StronglyMeasurable
      (fun q : ℝ × Space => q.1 ^ (-(3 / 2 : ℝ)) * ((Real.sqrt q.1)⁻¹) ^ m) :=
    ((measurable_fst.pow_const _).mul
      (((Real.continuous_sqrt.measurable.comp measurable_fst).inv).pow_const m)).stronglyMeasurable
  have hPsi : StronglyMeasurable
      (fun q : ℝ × Space => (q.1 ^ (-(3 / 2 : ℝ)) * ((Real.sqrt q.1)⁻¹) ^ m) •
        iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j x) ((Real.sqrt q.1)⁻¹ • q.2)) :=
    hsc2.smul hcomp2
  have hS : MeasurableSet {q : ℝ × Space | 0 < q.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hF : (fun q : ℝ × Space =>
      if 0 < q.1 then iteratedFDeriv ℝ m (fun x => heatLerayK q.1 i j x) q.2 else 0)
      = {q : ℝ × Space | 0 < q.1}.indicator (fun q : ℝ × Space =>
          (q.1 ^ (-(3 / 2 : ℝ)) * ((Real.sqrt q.1)⁻¹) ^ m) •
            iteratedFDeriv ℝ m (fun x => heatLerayK 1 i j x) ((Real.sqrt q.1)⁻¹ • q.2)) := by
    funext q
    by_cases hq : 0 < q.1
    · have hmem : q ∈ {q : ℝ × Space | 0 < q.1} := hq
      rw [if_pos hq, Set.indicator_of_mem hmem, l2_iteratedFDeriv_scale i j m q.1 hq q.2 hK1m]
    · have hnmem : q ∉ {q : ℝ × Space | 0 < q.1} := hq
      rw [if_neg hq, Set.indicator_of_notMem hnmem]
  rw [hF]
  exact hPsi.indicator hS

end UnforcedLeray.Short.IIIa

end
