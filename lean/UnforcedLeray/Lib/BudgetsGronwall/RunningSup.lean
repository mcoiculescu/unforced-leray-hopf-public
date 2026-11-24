import UnforcedLeray.Lib.BudgetsGronwall.VariationOfConstants

/-!
# The running maximum and Gronwall on it (INF30, target T30.2)


§5, Level 5, target T30.2; bypass B13(c).

The units B0116 (`eq:st18-t00093`, tex 1768–1790), B0117 (`eq:st18-t00094`, tex 1792–1803) and
B0351 (`eq:st18-t00357`, tex 6600–6645) apply Gronwall to the running maximum
`M(t) = sup_{s ≤ u ≤ t} |A(u)|`. This file proves:

* `continuousOn_runningSup`: for `A` continuous on `[s, T]`, `t ↦ sup A([s, t])` is continuous on
  `[s, T]` (it is the supremum over the fixed compact `[0, 1]` of the jointly continuous
  `(t, r) ↦ A(s + r (t - s))`);
* `le_runningSup`, `runningSup_mono`: the running maximum dominates `A` and is nondecreasing;
* `runningSup_le_exp_of_le_integral`: if `0 ≤ A t ≤ a + ∫_s^t β M` with `β ≥ 0` continuous,
  then `M t ≤ a e^{∫_s^t β}` (the Gronwall step of B0116, B0351).

`sSup` is the real conditional supremum; it is only evaluated on images of nonempty compact
intervals under continuous maps, which are nonempty and bounded, so no junk value occurs.
-/

set_option autoImplicit false

open Set Filter Topology intervalIntegral

namespace UnforcedLeray.Gronwall

/-- The running maximum `M(t) = sup_{u ∈ [s, t]} A u`. -/
noncomputable def runningSup (A : ℝ → ℝ) (s t : ℝ) : ℝ := sSup (A '' Icc s t)

/-- The affine reparametrization of `[s, t]` by `[0, 1]`. -/
theorem image_affine_Icc {s t : ℝ} (hst : s ≤ t) :
    (fun r : ℝ => s + r * (t - s)) '' Icc 0 1 = Icc s t := by
  ext u
  constructor
  · rintro ⟨r, ⟨hr0, hr1⟩, rfl⟩
    have h0 : 0 ≤ t - s := by linarith
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hu1, hu2⟩
    rcases eq_or_lt_of_le hst with h | h
    · subst h
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp; linarith⟩
    · have hpos : 0 < t - s := by linarith
      refine ⟨(u - s) / (t - s), ⟨div_nonneg (by linarith) hpos.le, ?_⟩, ?_⟩
      · rw [div_le_one hpos]; linarith
      · simp only
        field_simp
        ring

/-- **The running maximum is continuous** (T30.2; B0116, B0117, B0351). -/
theorem continuousOn_runningSup {A : ℝ → ℝ} {s T : ℝ} (hA : ContinuousOn A (Icc s T)) :
    ContinuousOn (fun t => runningSup A s t) (Icc s T) := by
  rcases lt_or_ge T s with hTs | hsT
  · rw [Icc_eq_empty (not_le.2 hTs)]
    exact continuousOn_empty _
  set A' := clampExt hsT A
  have hA' : Continuous A' := continuous_clampExt hsT hA
  set f : ℝ → ℝ → ℝ := fun t r => A' (s + r * (t - s))
  have hf : Continuous (Function.uncurry f) := by
    refine hA'.comp ?_
    exact continuous_const.add (continuous_snd.mul (continuous_fst.sub continuous_const))
  have hc := IsCompact.continuous_sSup (f := f) (K := Icc (0 : ℝ) 1) isCompact_Icc hf
  refine hc.continuousOn.congr fun t ht => ?_
  simp only [runningSup]
  congr 1
  rw [← image_affine_Icc ht.1, image_image]
  refine image_congr fun r hr => ?_
  simp only [f, A']
  have hmem : s + r * (t - s) ∈ Icc s t := by
    rw [← image_affine_Icc ht.1]; exact ⟨r, hr, rfl⟩
  have hmem' : s + r * (t - s) ∈ Icc s T := ⟨hmem.1, hmem.2.trans ht.2⟩
  exact (clampExt_eq hsT A hmem').symm

theorem bddAbove_image_Icc {A : ℝ → ℝ} {s T t : ℝ} (hA : ContinuousOn A (Icc s T))
    (ht : t ≤ T) : BddAbove (A '' Icc s t) :=
  (isCompact_Icc.image_of_continuousOn (hA.mono (Icc_subset_Icc le_rfl ht))).bddAbove

/-- The running maximum dominates the function. -/
theorem le_runningSup {A : ℝ → ℝ} {s T : ℝ} (hA : ContinuousOn A (Icc s T)) {u t : ℝ}
    (hu : u ∈ Icc s t) (ht : t ≤ T) : A u ≤ runningSup A s t :=
  le_csSup (bddAbove_image_Icc hA ht) ⟨u, hu, rfl⟩

/-- The running maximum is nondecreasing. -/
theorem runningSup_mono {A : ℝ → ℝ} {s T : ℝ} (hA : ContinuousOn A (Icc s T)) {t t' : ℝ}
    (hs : s ≤ t) (htt' : t ≤ t') (ht' : t' ≤ T) : runningSup A s t ≤ runningSup A s t' :=
  csSup_le_csSup (bddAbove_image_Icc hA ht') ⟨A s, s, ⟨le_rfl, hs⟩, rfl⟩
    (image_mono (Icc_subset_Icc le_rfl htt'))

/-- The running maximum is attained: it is a value of `A` on `[s, t]`. -/
theorem exists_eq_runningSup {A : ℝ → ℝ} {s T t : ℝ} (hA : ContinuousOn A (Icc s T))
    (hs : s ≤ t) (ht : t ≤ T) : ∃ u ∈ Icc s t, A u = runningSup A s t := by
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hs)
    (hA.mono (Icc_subset_Icc le_rfl ht))
  refine ⟨u, hu, le_antisymm (le_runningSup hA hu ht) (csSup_le ⟨A s, s, ⟨le_rfl, hs⟩, rfl⟩ ?_)⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hmax hv

/-- **Gronwall on the running maximum** (B0116 tex 1768–1790, B0351 tex 6600–6645).
If `A` is continuous and nonnegative on `[s, T]`, `β ≥ 0` is continuous there and
`A t ≤ a + ∫_s^t β r M(r) dr` with `M` the running maximum, then `M t ≤ a e^{∫_s^t β}`. -/
theorem runningSup_le_exp_of_le_integral {A β : ℝ → ℝ} {a s T : ℝ}
    (hA : ContinuousOn A (Icc s T)) (hA0 : ∀ r ∈ Icc s T, 0 ≤ A r)
    (hβ : ContinuousOn β (Icc s T)) (hβ0 : ∀ r ∈ Icc s T, 0 ≤ β r)
    (h : ∀ t ∈ Icc s T, A t ≤ a + ∫ r in s..t, β r * runningSup A s r) :
    ∀ t ∈ Icc s T, runningSup A s t ≤ a * Real.exp (∫ r in s..t, β r) := by
  have hM : ContinuousOn (fun t => runningSup A s t) (Icc s T) := continuousOn_runningSup hA
  have hM0 : ∀ r ∈ Icc s T, 0 ≤ runningSup A s r := fun r hr =>
    (hA0 s ⟨le_rfl, hr.1.trans hr.2⟩).trans (le_runningSup hA ⟨le_rfl, hr.1⟩ hr.2)
  have hstep : ∀ t ∈ Icc s T, runningSup A s t ≤ a + ∫ r in s..t, β r * runningSup A s r := by
    intro t ht
    refine csSup_le ⟨A s, s, ⟨le_rfl, ht.1⟩, rfl⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    have huT : u ∈ Icc s T := ⟨hu.1, hu.2.trans ht.2⟩
    refine (h u huT).trans ?_
    have hint : IntervalIntegrable (fun r => β r * runningSup A s r) MeasureTheory.volume s t :=
      ((hβ.mul hM).mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hmono : ∫ r in s..u, β r * runningSup A s r ≤ ∫ r in s..t, β r * runningSup A s r := by
      refine integral_mono_interval le_rfl hu.1 hu.2 ?_ hint
      refine (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono fun r hr => ?_
      have hrI : r ∈ Icc s T := ⟨hr.1.le, hr.2.trans ht.2⟩
      exact mul_nonneg (hβ0 r hrI) (hM0 r hrI)
    linarith
  exact le_exp_of_integral_le hM hβ hβ0 hstep

end UnforcedLeray.Gronwall
