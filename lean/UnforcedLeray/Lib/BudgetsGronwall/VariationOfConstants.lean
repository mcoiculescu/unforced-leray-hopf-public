import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gronwall inequalities in variation-of-constants and integral form (INF30, T30.1, T30.5)


§5, Level 5, targets T30.1a, T30.1b/c and T30.5; bypass B13 (§4).

* `le_voc_of_deriv_le` (T30.1a): the **time-ordered** (variation-of-constants) Gronwall inequality
  for a continuous function `y` on `[s, T]` with right derivative `y' ≤ β y + γ`, where `β` and `γ`
  are continuous of any sign:
  `y t ≤ e^{∫_s^t β} y s + ∫_s^t e^{∫_r^t β} γ r dr`.
  This is the form used at B0149 (`eq:st18-t00147`, tex 2244–2261: "Time-ordered Gronwall ...
  replacing the integrating factor by `e^{C/ν}` before its integration would discard this
  estimate"), B0161 (tex 2425–2433), B0338 (tex 6396–6406) and B0360 (tex 6728–6742).
  The coarse form `e^{∫β}(y_s + ∫γ)` is *not* used: the integrating factor stays inside the
  `r`-integral (scoping §6, risk 1).
* `le_exp_of_integral_le`, `le_voc_of_integral_le` (T30.1b/c): integral forms with `β ≥ 0`
  (B0245 tex 4200–4214, B0257 tex 4413–4435, B0667 tex 4824–4834, B0937 tex 14362–14381).
* `le_exp_mul_of_deriv_le`: the constant-coefficient case `y' ≤ K y + γ`.
* `eq_zero_of_energy_le` (T30.5): a nonnegative energy with `y' ≤ β y` and `y s = 0` vanishes
  (B1010, tex 313–319: forward uniqueness of graph solutions from the energy estimate).

Conventions. Derivatives are right derivatives `HasDerivWithinAt _ _ (Ici t) t` at every
`t ∈ [s, T)`, and continuity is on the closed interval `[s, T]`; this is weaker than `C¹` and
covers the energies of smooth data (bypass B13: no a.e.-derivative Gronwall is needed).
All interval integrals are of functions continuous on the interval of integration, so they are
genuine Riemann/Lebesgue integrals (no junk value of a non-integrable integrand occurs).
-/

set_option autoImplicit false

open Set Filter Topology intervalIntegral

namespace UnforcedLeray.Gronwall

/-- Continuous extension of a function continuous on `[s, T]`: compose with the projection
onto `[s, T]`. -/
noncomputable def clampExt {s T : ℝ} (hsT : s ≤ T) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (projIcc s T hsT x : ℝ)

theorem clampExt_eq {s T : ℝ} (hsT : s ≤ T) (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc s T) :
    clampExt hsT f x = f x := by
  simp [clampExt, projIcc_of_mem hsT hx]

theorem continuous_clampExt {s T : ℝ} (hsT : s ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc s T)) : Continuous (clampExt hsT f) :=
  hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun x => (projIcc s T hsT x).2)

/-- Interval integrals over `[a, b] ⊆ [s, T]` do not see the extension. -/
theorem integral_clampExt {s T : ℝ} (hsT : s ≤ T) (f : ℝ → ℝ) {a b : ℝ}
    (ha : a ∈ Icc s T) (hb : b ∈ Icc s T) :
    ∫ u in a..b, clampExt hsT f u = ∫ u in a..b, f u := by
  refine integral_congr fun u hu => clampExt_eq hsT f ?_
  have hsub : uIcc a b ⊆ Icc s T := uIcc_subset_Icc ha hb
  exact hsub hu

/-- **Sharp variation-of-constants Gronwall inequality** (T30.1a; B0149, B0161, B0338, B0360).
Let `y`, `β`, `γ` be continuous on `[s, T]`, and let `y` have at every `t ∈ [s, T)` a right
derivative `y'` with `y' ≤ β t y t + γ t`. Then for `t ∈ [s, T]`
`y t ≤ e^{∫_s^t β} y s + ∫_s^t e^{∫_r^t β} γ r dr`.
No sign condition on `β` or `γ` is needed. -/
theorem le_voc_of_deriv_le {y β γ : ℝ → ℝ} {s T : ℝ}
    (hy : ContinuousOn y (Icc s T)) (hβ : ContinuousOn β (Icc s T))
    (hγ : ContinuousOn γ (Icc s T))
    (hd : ∀ t ∈ Ico s T, ∃ y', HasDerivWithinAt y y' (Ici t) t ∧ y' ≤ β t * y t + γ t) :
    ∀ t ∈ Icc s T, y t ≤ Real.exp (∫ u in s..t, β u) * y s +
      ∫ r in s..t, Real.exp (∫ u in r..t, β u) * γ r := by
  intro t ht
  have hsT : s ≤ T := ht.1.trans ht.2
  have hs : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  set β' := clampExt hsT β with hβ'def
  set γ' := clampExt hsT γ with hγ'def
  have hβ'c : Continuous β' := continuous_clampExt hsT hβ
  have hγ'c : Continuous γ' := continuous_clampExt hsT hγ
  set B : ℝ → ℝ := fun x => ∫ u in s..x, β' u with hBdef
  have hB : ∀ x, HasDerivAt B (β' x) x := fun x =>
    (hβ'c.integral_hasStrictDerivAt s x).hasDerivAt
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun x => (hB x).continuousAt
  set g : ℝ → ℝ := fun r => Real.exp (-B r) * γ' r with hgdef
  have hgc : Continuous g := (Real.continuous_exp.comp hBc.neg).mul hγ'c
  set G : ℝ → ℝ := fun x => ∫ r in s..x, g r with hGdef
  have hG : ∀ x, HasDerivAt G (g x) x := fun x => (hgc.integral_hasStrictDerivAt s x).hasDerivAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  set z : ℝ → ℝ := fun x => Real.exp (-B x) * y x - G x with hzdef
  have hzc : ContinuousOn z (Icc s T) :=
    ((Real.continuous_exp.comp hBc.neg).continuousOn.mul hy).sub hGc.continuousOn
  choose! y' hy' hy'le using hd
  have hz' : ∀ x ∈ Ico s T, HasDerivWithinAt z
      (Real.exp (-B x) * -β' x * y x + Real.exp (-B x) * y' x - g x) (Ici x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => Real.exp (-B x)) (Real.exp (-B x) * -β' x) x :=
      (hB x).neg.exp
    exact (h1.hasDerivWithinAt.mul (hy' x hx)).sub (hG x).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico s T,
      Real.exp (-B x) * -β' x * y x + Real.exp (-B x) * y' x - g x ≤ 0 := by
    intro x hx
    have hxI : x ∈ Icc s T := Ico_subset_Icc_self hx
    have e1 : β' x = β x := clampExt_eq hsT β hxI
    have e2 : γ' x = γ x := clampExt_eq hsT γ hxI
    have hrw : Real.exp (-B x) * -β' x * y x + Real.exp (-B x) * y' x - g x =
        Real.exp (-B x) * (y' x - (β x * y x + γ x)) := by
      simp only [hgdef, e1, e2]; ring
    rw [hrw]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hy'le x hx])
  have hzle : z t ≤ z s :=
    image_le_of_deriv_right_le_deriv_boundary hzc hz' (B := fun _ => z s) (B' := fun _ => 0)
      le_rfl continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) hbound ht
  have hBs : B s = 0 := integral_same
  have hGs : G s = 0 := integral_same
  have hzs : z s = y s := by simp [hzdef, hBs, hGs]
  rw [hzs] at hzle
  -- unfold `z t ≤ y s` into the claimed bound
  have hmul : y t ≤ Real.exp (B t) * y s + Real.exp (B t) * G t := by
    have hz : Real.exp (-B t) * y t ≤ y s + G t := by simp only [hzdef] at hzle; linarith
    have hE : Real.exp (B t) * Real.exp (-B t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc y t = Real.exp (B t) * (Real.exp (-B t) * y t) := by
          rw [← mul_assoc, hE, one_mul]
      _ ≤ Real.exp (B t) * (y s + G t) :=
          mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
      _ = Real.exp (B t) * y s + Real.exp (B t) * G t := by ring
  have hBt : B t = ∫ u in s..t, β u := integral_clampExt hsT β hs ht
  have hGt : Real.exp (B t) * G t = ∫ r in s..t, Real.exp (∫ u in r..t, β u) * γ r := by
    rw [hGdef, ← integral_const_mul]
    refine integral_congr fun r hr => ?_
    have hr' : r ∈ Icc s t := by rwa [uIcc_of_le ht.1] at hr
    have hrI : r ∈ Icc s T := ⟨hr'.1, hr'.2.trans ht.2⟩
    have hsub : B t - B r = ∫ u in r..t, β u := by
      rw [hBdef]
      simp only
      rw [integral_interval_sub_left (hβ'c.intervalIntegrable _ _)
        (hβ'c.intervalIntegrable _ _)]
      exact integral_clampExt hsT β hrI ht
    have hγr : γ' r = γ r := clampExt_eq hsT γ hrI
    simp only [hgdef]
    rw [← hsub, hγr, ← mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  rw [hGt] at hmul
  rw [hBt] at hmul
  exact hmul

/-- Constant-coefficient case: `y' ≤ K y + γ` gives
`y t ≤ e^{K (t - s)} y s + ∫_s^t e^{K (t - r)} γ r dr` (B0245, B0257). -/
theorem le_exp_mul_of_deriv_le {y γ : ℝ → ℝ} {K s T : ℝ}
    (hy : ContinuousOn y (Icc s T)) (hγ : ContinuousOn γ (Icc s T))
    (hd : ∀ t ∈ Ico s T, ∃ y', HasDerivWithinAt y y' (Ici t) t ∧ y' ≤ K * y t + γ t) :
    ∀ t ∈ Icc s T, y t ≤ Real.exp (K * (t - s)) * y s +
      ∫ r in s..t, Real.exp (K * (t - r)) * γ r := by
  intro t ht
  have h := le_voc_of_deriv_le (β := fun _ => K) hy continuousOn_const hγ hd t ht
  simp only [integral_const, smul_eq_mul] at h
  have e : ∀ a, (t - a) * K = K * (t - a) := fun a => mul_comm _ _
  simp only [e] at h
  exact h

/-- **Integral Gronwall, coarse form** (T30.1b; B0245, B0257, B0667, B0937).
If `y` and `β ≥ 0` are continuous on `[s, T]` and `y t ≤ A + ∫_s^t β y` there, then
`y t ≤ A e^{∫_s^t β}`. The constant `A` may have any sign. -/
theorem le_exp_of_integral_le {y β : ℝ → ℝ} {A s T : ℝ} (hy : ContinuousOn y (Icc s T))
    (hβ : ContinuousOn β (Icc s T)) (hβ0 : ∀ r ∈ Icc s T, 0 ≤ β r)
    (h : ∀ t ∈ Icc s T, y t ≤ A + ∫ r in s..t, β r * y r) :
    ∀ t ∈ Icc s T, y t ≤ A * Real.exp (∫ r in s..t, β r) := by
  intro t ht
  have hsT : s ≤ T := ht.1.trans ht.2
  have hs : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  set f : ℝ → ℝ := clampExt hsT (fun r => β r * y r) with hfdef
  have hfc : Continuous f := continuous_clampExt hsT (hβ.mul hy)
  set w : ℝ → ℝ := fun x => A + ∫ r in s..x, f r with hwdef
  have hw : ∀ x, HasDerivAt w (f x) x := fun x =>
    ((hfc.integral_hasStrictDerivAt s x).hasDerivAt).const_add A
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun x => (hw x).continuousAt
  have hwy : ∀ x ∈ Icc s T, y x ≤ w x := by
    intro x hx
    have := h x hx
    simp only [hwdef]
    rwa [integral_clampExt hsT _ hs hx]
  have hd : ∀ x ∈ Ico s T, ∃ w', HasDerivWithinAt w w' (Ici x) x ∧ w' ≤ β x * w x + 0 := by
    intro x hx
    have hxI : x ∈ Icc s T := Ico_subset_Icc_self hx
    refine ⟨f x, (hw x).hasDerivWithinAt, ?_⟩
    rw [hfdef, clampExt_eq hsT _ hxI, add_zero]
    exact mul_le_mul_of_nonneg_left (hwy x hxI) (hβ0 x hxI)
  have hmain := le_voc_of_deriv_le (γ := fun _ => 0) hwc.continuousOn hβ continuousOn_const hd
    t ht
  have hws : w s = A := by simp [hwdef]
  simp only [mul_zero, integral_zero, add_zero, hws] at hmain
  rw [mul_comm]
  exact (hwy t ht).trans hmain

/-- **Integral Gronwall, sharp form** (T30.1c; B0946, B0947). If `y`, `β ≥ 0` and `γ` are
continuous on `[s, T]` and `y t ≤ y s + ∫_s^t (β y + γ)`, then
`y t ≤ e^{∫_s^t β} y s + ∫_s^t e^{∫_r^t β} γ r dr`. -/
theorem le_voc_of_integral_le {y β γ : ℝ → ℝ} {s T : ℝ} (hy : ContinuousOn y (Icc s T))
    (hβ : ContinuousOn β (Icc s T)) (hγ : ContinuousOn γ (Icc s T))
    (hβ0 : ∀ r ∈ Icc s T, 0 ≤ β r)
    (h : ∀ t ∈ Icc s T, y t ≤ y s + ∫ r in s..t, (β r * y r + γ r)) :
    ∀ t ∈ Icc s T, y t ≤ Real.exp (∫ u in s..t, β u) * y s +
      ∫ r in s..t, Real.exp (∫ u in r..t, β u) * γ r := by
  intro t ht
  have hsT : s ≤ T := ht.1.trans ht.2
  have hs : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  set f : ℝ → ℝ := clampExt hsT (fun r => β r * y r + γ r) with hfdef
  have hfc : Continuous f := continuous_clampExt hsT ((hβ.mul hy).add hγ)
  set w : ℝ → ℝ := fun x => y s + ∫ r in s..x, f r with hwdef
  have hw : ∀ x, HasDerivAt w (f x) x := fun x =>
    ((hfc.integral_hasStrictDerivAt s x).hasDerivAt).const_add (y s)
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun x => (hw x).continuousAt
  have hwy : ∀ x ∈ Icc s T, y x ≤ w x := by
    intro x hx
    have := h x hx
    simp only [hwdef]
    rwa [integral_clampExt hsT _ hs hx]
  have hd : ∀ x ∈ Ico s T, ∃ w', HasDerivWithinAt w w' (Ici x) x ∧ w' ≤ β x * w x + γ x := by
    intro x hx
    have hxI : x ∈ Icc s T := Ico_subset_Icc_self hx
    refine ⟨f x, (hw x).hasDerivWithinAt, ?_⟩
    rw [hfdef, clampExt_eq hsT _ hxI]
    have := mul_le_mul_of_nonneg_left (hwy x hxI) (hβ0 x hxI)
    linarith
  have hmain := le_voc_of_deriv_le hwc.continuousOn hβ hγ hd t ht
  have hws : w s = y s := by simp [hwdef]
  rw [hws] at hmain
  exact (hwy t ht).trans hmain

/-- **Zero-datum uniqueness** (T30.5; B1010, tex 313–319). If a continuous nonnegative energy
`y` on `[s, T]` has right derivative `y' ≤ β y` with `β` continuous, and `y s = 0`, then
`y = 0` on `[s, T]`. -/
theorem eq_zero_of_energy_le {y β : ℝ → ℝ} {s T : ℝ} (hy : ContinuousOn y (Icc s T))
    (hβ : ContinuousOn β (Icc s T))
    (hd : ∀ t ∈ Ico s T, ∃ y', HasDerivWithinAt y y' (Ici t) t ∧ y' ≤ β t * y t)
    (h0 : y s = 0) (hnn : ∀ t ∈ Icc s T, 0 ≤ y t) : ∀ t ∈ Icc s T, y t = 0 := by
  intro t ht
  have hd' : ∀ t ∈ Ico s T, ∃ y', HasDerivWithinAt y y' (Ici t) t ∧ y' ≤ β t * y t + 0 := by
    intro t ht
    obtain ⟨y', h1, h2⟩ := hd t ht
    exact ⟨y', h1, by rwa [add_zero]⟩
  have h := le_voc_of_deriv_le (γ := fun _ => 0) hy hβ continuousOn_const hd' t ht
  simp only [h0, mul_zero, integral_zero, add_zero] at h
  exact le_antisymm h (hnn t ht)

/-- Zero-datum uniqueness with a constant coefficient: `y' ≤ C y`, `y s = 0`, `y ≥ 0`. -/
theorem eq_zero_of_energy_le_const {y : ℝ → ℝ} {C s T : ℝ} (hy : ContinuousOn y (Icc s T))
    (hd : ∀ t ∈ Ico s T, ∃ y', HasDerivWithinAt y y' (Ici t) t ∧ y' ≤ C * y t)
    (h0 : y s = 0) (hnn : ∀ t ∈ Icc s T, 0 ≤ y t) : ∀ t ∈ Icc s T, y t = 0 :=
  eq_zero_of_energy_le (β := fun _ => C) hy continuousOn_const hd h0 hnn

end UnforcedLeray.Gronwall
