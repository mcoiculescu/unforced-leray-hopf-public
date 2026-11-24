import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!
# Leaf B5 (`OscSobolev1D`): the one-dimensional Sobolev inequality

Source of record: `the November 2 reference manuscript`, lines 1134-1140.
The Prop `OscSobolev1D` is proved exactly as stated in `Short/Spine/Sub/SP_CAN4_4_1.lean`.

Proof. Write `A = ∫_a^b ‖g‖²`, `B = ∫_a^b ‖g'‖²`, `S = A + B`.
For `x, y ∈ [a, b]`, the fundamental theorem of calculus applied to `‖g‖²`
(`HasDerivAt.norm_sq`) gives `‖g x‖² - ‖g y‖² = ∫_y^x 2⟪g, g'⟫`, and
`|2⟪g, g'⟫| ≤ ‖g‖² + ‖g'‖²`, so `‖g x‖² ≤ ‖g y‖² + S`. Integrating in `y` over `[a, b]`
gives `(b - a) ‖g x‖² ≤ A + (b - a) S`; dividing by `b - a > 0` gives the claim.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

theorem oscSobolev1D_proof : UnforcedLeray.Short.Spine.OscSobolev1D := by
  unfold OscSobolev1D
  intro g a b ha hab hg x hx
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le ha ht.1
  have ha_mem : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb_mem : b ∈ Icc a b := right_mem_Icc.2 hab.le
  -- regularity of `g` and `g'` on `[a, b] ⊆ (0, ∞)`
  have hgc : ContinuousOn g (Icc a b) := hg.continuousOn.mono hsub
  have hdgc : ContinuousOn (deriv g) (Icc a b) :=
    (hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub
  have hdiff : ∀ t ∈ Icc a b, HasDerivAt g (deriv g t) t := fun t ht =>
    ((hg.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds (lt_of_lt_of_le ha ht.1))).hasDerivAt
  -- continuity of the integrands on `[a, b]`
  have hNc : ContinuousOn (fun t => ‖g t‖ ^ 2) (Icc a b) := hgc.norm.pow 2
  have hN'c : ContinuousOn (fun t => ‖deriv g t‖ ^ 2) (Icc a b) := hdgc.norm.pow 2
  have hDc : ContinuousOn (fun t => 2 * ⟪g t, deriv g t⟫_ℝ) (Icc a b) :=
    continuousOn_const.mul (hgc.inner hdgc)
  have hkc : ContinuousOn (fun t => ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) (Icc a b) :=
    hNc.add hN'c
  -- interval integrability on any `[[u, v]] ⊆ [a, b]`
  have hII : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc a b) → ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      IntervalIntegrable f volume u v := fun hf u hu v hv =>
    (hf.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  -- pointwise bound `|2⟪g, g'⟫| ≤ ‖g‖² + ‖g'‖²`
  have hDbd : ∀ t, ‖2 * ⟪g t, deriv g t⟫_ℝ‖ ≤ ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    have h1 := abs_real_inner_le_norm (g t) (deriv g t)
    nlinarith [sq_nonneg (‖g t‖ - ‖deriv g t‖), norm_nonneg (g t), norm_nonneg (deriv g t)]
  -- fundamental theorem of calculus for `‖g‖²`
  have hFTC : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      ∫ t in u..v, 2 * ⟪g t, deriv g t⟫_ℝ = ‖g v‖ ^ 2 - ‖g u‖ ^ 2 := by
    intro u hu v hv
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => ‖g t‖ ^ 2) (f' := fun t => 2 * ⟪g t, deriv g t⟫_ℝ)
      (fun t ht => HasDerivAt.norm_sq (hdiff t (uIcc_subset_Icc hu hv ht)))
      (hII hDc u hu v hv)
  -- energy bound on any ordered subinterval
  have hcore : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      ‖∫ t in u..v, 2 * ⟪g t, deriv g t⟫_ℝ‖ ≤
        ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) := by
    intro u hu v hv huv
    calc ‖∫ t in u..v, 2 * ⟪g t, deriv g t⟫_ℝ‖
        ≤ ∫ t in u..v, ‖2 * ⟪g t, deriv g t⟫_ℝ‖ :=
          intervalIntegral.norm_integral_le_integral_norm huv
      _ ≤ ∫ t in u..v, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) :=
          intervalIntegral.integral_mono_on huv (hII hDc.norm u hu v hv)
            (hII hkc u hu v hv) (fun t _ => hDbd t)
      _ ≤ ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) :=
          intervalIntegral.integral_mono_interval hu.1 huv hv.2
            (ae_of_all _ fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
            (hII hkc a ha_mem b hb_mem)
  -- Step 1: `‖g x‖² ≤ ‖g y‖² + S` for `x, y ∈ [a, b]`
  have hstep : ∀ y ∈ Icc a b,
      ‖g x‖ ^ 2 ≤ ‖g y‖ ^ 2 + ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) := by
    intro y hy
    rcases le_total y x with hyx | hxy
    · have h1 := hcore y hy x hx hyx
      rw [hFTC y hy x hx, Real.norm_eq_abs] at h1
      linarith [(abs_le.mp h1).2]
    · have h1 := hcore x hx y hy hxy
      rw [hFTC x hx y hy, Real.norm_eq_abs] at h1
      linarith [(abs_le.mp h1).1]
  -- Step 2: integrate the pointwise bound over `y ∈ [a, b]`
  have hS : ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) =
      (∫ t in a..b, ‖g t‖ ^ 2) + ∫ t in a..b, ‖deriv g t‖ ^ 2 :=
    intervalIntegral.integral_add (hII hNc a ha_mem b hb_mem) (hII hN'c a ha_mem b hb_mem)
  have hint1 : IntervalIntegrable (fun _ : ℝ => ‖g x‖ ^ 2) volume a b :=
    continuousOn_const.intervalIntegrable_of_Icc hab.le
  have hint2 : IntervalIntegrable
      (fun y => ‖g y‖ ^ 2 + ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2)) volume a b :=
    (hNc.add continuousOn_const).intervalIntegrable_of_Icc hab.le
  have hmono : ∫ y in a..b, ‖g x‖ ^ 2 ≤
      ∫ y in a..b, (‖g y‖ ^ 2 + ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2)) :=
    intervalIntegral.integral_mono_on hab.le hint1 hint2 (fun y hy => hstep y hy)
  have e1 : ∫ y in a..b, ‖g x‖ ^ 2 = (b - a) * ‖g x‖ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hmono' : (b - a) * ‖g x‖ ^ 2 ≤
      (∫ t in a..b, ‖g t‖ ^ 2) + (b - a) * ((∫ t in a..b, ‖g t‖ ^ 2) +
        ∫ t in a..b, ‖deriv g t‖ ^ 2) := by
    calc (b - a) * ‖g x‖ ^ 2 = ∫ y in a..b, ‖g x‖ ^ 2 := e1.symm
      _ ≤ ∫ y in a..b, (‖g y‖ ^ 2 + ∫ t in a..b, (‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2)) := hmono
      _ = (∫ t in a..b, ‖g t‖ ^ 2) + (b - a) * ((∫ t in a..b, ‖g t‖ ^ 2) +
            ∫ t in a..b, ‖deriv g t‖ ^ 2) := by
          rw [intervalIntegral.integral_add (hII hNc a ha_mem b hb_mem)
            (continuousOn_const.intervalIntegrable_of_Icc hab.le),
            intervalIntegral.integral_const, smul_eq_mul, hS]
  -- Step 3: divide by `b - a > 0`
  have hba : 0 < b - a := sub_pos.mpr hab
  have hinv : (b - a) * (1 / (b - a)) = 1 := mul_one_div_cancel hba.ne'
  have hmain : (b - a) * ‖g x‖ ^ 2 ≤
      (b - a) * ((1 / (b - a) + 1) * (∫ t in a..b, ‖g t‖ ^ 2) +
        ∫ t in a..b, ‖deriv g t‖ ^ 2) := by
    have e3 : (b - a) * ((1 / (b - a) + 1) * (∫ t in a..b, ‖g t‖ ^ 2) +
        ∫ t in a..b, ‖deriv g t‖ ^ 2) =
        (∫ t in a..b, ‖g t‖ ^ 2) + (b - a) * ((∫ t in a..b, ‖g t‖ ^ 2) +
          ∫ t in a..b, ‖deriv g t‖ ^ 2) := by
      linear_combination (∫ t in a..b, ‖g t‖ ^ 2) * hinv
    rw [e3]
    exact hmono'
  exact le_of_mul_le_mul_left hmain hba

end UnforcedLeray.Short.Spine
