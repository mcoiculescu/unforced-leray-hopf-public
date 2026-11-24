import UnforcedLeray.Short.PartI.Sub.C09

/-!
# Part I, task `PartI:C09`, Step 1a: the radial Green identity for `Δ₂`

Source of record: `the November 2 reference manuscript`, lines 1139-1140
("the radial Green formula for `Δ₂⁻¹`"). This file proves `radialGreenIdentity : RadialGreenIdentity`,
i.e. for locally integrable `f` on `(0, ∞)` and `ψ` with `B0011.IsDelta2Sol f ψ`, the integrated
form `RadialWeakEq ψ f` holds.

Proof sketch. Fix `Φ` supported in `[a, b] ⊂ (0, ∞)` and take `[a, b]` strictly inside the support
window. With `v(r) = r Φ'(r)` the integrand is `ψ v' - 4ψΦ/r`. Integration by parts for the `C¹`
function `ψ` gives `∫ ψ v' = -∫ ψ' v`. For the absolutely continuous `ψ'`, `ψ'(s) - ψ'(a) = ∫_a^s g`
with `g = f - ψ'/r + 4ψ/r²`; a Fubini identity on the triangle (`radial_primitive_mul_eq`) applied
twice gives `∫ ψ' v = -∫ (r g + ψ') Φ = -∫ (r f + 4ψ/r) Φ`. Combining, the `4ψΦ/r` terms cancel and
`∫ r f Φ` remains.

Helpers: `radialFubKernel`, `radial_primitive_mul_eq` (triangle Fubini for `∫_a^b (∫_a^s h) w'(s) ds`).
-/
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

/-- The triangular kernel `(s, t) ↦ 1_{t ≤ s} h(t) w'(s)` used in the Fubini step. -/
def radialFubKernel (h w' : ℝ → ℂ) (s t : ℝ) : ℂ := (Set.Iic s).indicator h t * w' s

theorem radial_primitive_mul_eq {a b : ℝ} (hab : a ≤ b) (h w w' : ℝ → ℂ)
    (hh : IntervalIntegrable h volume a b)
    (hw : ∀ s ∈ Icc a b, HasDerivAt w (w' s) s) (hw' : ContinuousOn w' (Icc a b)) :
    ∫ s in a..b, (∫ t in a..s, h t) * w' s =
      (∫ t in a..b, h t) * w b - ∫ t in a..b, h t * w t := by
  have hA : ∀ s ∈ Icc a b, ∫ t in a..b, radialFubKernel h w' s t = (∫ t in a..s, h t) * w' s := by
    intro s hs
    have has : a ≤ s := hs.1
    have hsb : s ≤ b := hs.2
    unfold radialFubKernel
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le has, setIntegral_indicator measurableSet_Iic,
      Set.Ioc_inter_Iic, inf_eq_right.2 hsb]
  have hB : ∀ t ∈ Icc a b, ∫ s in a..b, radialFubKernel h w' s t = h t * (w b - w t) := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have key : ∀ s, radialFubKernel h w' s t = h t * (Ici t).indicator w' s := by
      intro s
      unfold radialFubKernel
      by_cases hts : t ≤ s
      · simp [hts]
      · simp [hts]
    have hset : (Ioc a b ∩ Ici t : Set ℝ) =ᵐ[volume] (Ioc t b : Set ℝ) := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [Measure.ae_ne volume t] with x hx
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨lt_of_le_of_ne h3 (Ne.symm hx), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨lt_of_le_of_lt hat h1, h2⟩, h1.le⟩
    have hderiv : ∀ x ∈ uIcc t b, HasDerivAt w (w' x) x := by
      intro x hx
      rw [uIcc_of_le htb] at hx
      exact hw x ⟨le_trans hat hx.1, hx.2⟩
    have hint : IntervalIntegrable w' volume t b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le htb]
      exact hw'.mono (Icc_subset_Icc hat le_rfl)
    simp only [key]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab,
      setIntegral_indicator measurableSet_Ici, setIntegral_congr_set hset,
      ← intervalIntegral.integral_of_le htb, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hmeas_h : AEStronglyMeasurable h (volume.restrict (Ioc a b)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hh).aestronglyMeasurable
  have hmeas_w : AEStronglyMeasurable w' (volume.restrict (Ioc a b)) :=
    (hw'.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw'
  have hfin : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hnorm : Integrable (fun t => ‖h t‖) (volume.restrict (Ioc a b)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hh).norm
  have hbound : Integrable (fun p : ℝ × ℝ => C * ‖h p.2‖)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
    (integrable_const C).mul_prod hnorm
  have hint : IntegrableOn (Function.uncurry (radialFubKernel h w')) (uIoc a b ×ˢ uIoc a b) volume := by
    show Integrable (Function.uncurry (radialFubKernel h w')) ((volume : Measure (ℝ × ℝ)).restrict
      (uIoc a b ×ˢ uIoc a b))
    rw [uIoc_of_le hab, Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine Integrable.mono' hbound ?_ ?_
    · have heq : Function.uncurry (radialFubKernel h w') = fun p : ℝ × ℝ =>
          ({q : ℝ × ℝ | q.2 ≤ q.1}).indicator (fun q => h q.2 * w' q.1) p := by
        funext p
        by_cases hp : p.2 ≤ p.1
        · simp [Function.uncurry, radialFubKernel, hp]
        · simp [Function.uncurry, radialFubKernel, hp]
      rw [heq]
      exact ((hmeas_h.comp_snd).mul hmeas_w.comp_fst).indicator
        (measurableSet_le measurable_snd measurable_fst)
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
      rintro ⟨s, t⟩ ⟨hs, ht⟩
      show ‖radialFubKernel h w' s t‖ ≤ C * ‖h t‖
      unfold radialFubKernel
      rw [norm_mul, mul_comm C]
      exact mul_le_mul (norm_indicator_le_norm_self _ _) (hC s (Ioc_subset_Icc_self hs))
        (norm_nonneg _) (norm_nonneg _)
  have hswap := intervalIntegral_intervalIntegral_swap (F := radialFubKernel h w') (a := a)
    (b := b) (c := a) (d := b) hint
  have L1 : ∫ s in a..b, (∫ t in a..s, h t) * w' s =
      ∫ s in a..b, ∫ t in a..b, radialFubKernel h w' s t := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hab] at hs
    exact (hA s hs).symm
  have L2 : ∫ t in a..b, ∫ s in a..b, radialFubKernel h w' s t =
      ∫ t in a..b, h t * (w b - w t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hab] at ht
    exact hB t ht
  have hwc : ContinuousOn w (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro x hx
    exact (hw x hx).continuousAt.continuousWithinAt
  rw [L1, hswap, L2]
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub (hh.mul_const (w b)) (hh.mul_continuousOn hwc),
    intervalIntegral.integral_mul_const]

theorem radialGreenIdentity : RadialGreenIdentity := by
  unfold RadialGreenIdentity RadialWeakEq
  intro f ψ hf hψ Φ hΦ hsupp
  obtain ⟨a₀, b₀, ha₀, hzero⟩ := hsupp
  obtain ⟨ψ', hψd, hψc, hψi⟩ := hψ
  -- Regularity of `Φ`.
  have hΦd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Φ (deriv Φ x) x := fun x hx =>
    ((hΦ.differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have hΦ1 : ContDiffOn ℝ ∞ (deriv Φ) (Ioi 0) := hΦ.deriv_of_isOpen isOpen_Ioi (by simp)
  have hΦdd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x := fun x hx =>
    ((hΦ1.differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have hΦ2 : ContDiffOn ℝ ∞ (deriv (deriv Φ)) (Ioi 0) := hΦ1.deriv_of_isOpen isOpen_Ioi (by simp)
  have hΦc : ContinuousOn Φ (Ioi 0) := hΦ.continuousOn
  have hΦ1c : ContinuousOn (deriv Φ) (Ioi 0) := hΦ1.continuousOn
  have hΦ2c : ContinuousOn (deriv (deriv Φ)) (Ioi 0) := hΦ2.continuousOn
  -- The compact interval `[a, b]`.
  obtain ⟨a, ha0, haa⟩ : ∃ a : ℝ, 0 < a ∧ a < a₀ := ⟨a₀ / 2, half_pos ha₀, by linarith⟩
  obtain ⟨b, hb₀, hab⟩ : ∃ b : ℝ, b₀ < b ∧ a ≤ b :=
    ⟨|b₀| + a₀ + 1, by linarith [le_abs_self b₀, abs_nonneg b₀], by linarith [abs_nonneg b₀]⟩
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  -- Vanishing of `Φ` and its derivatives off the support.
  have hEv : ∀ x : ℝ, 0 < x → (x < a₀ ∨ b₀ < x) → ∀ᶠ y in 𝓝 x, Φ y = 0 := by
    intro x hx hxo
    rcases hxo with h | h
    · filter_upwards [Ioo_mem_nhds hx h] with y hy
      exact hzero y hy.1 (Or.inl hy.2)
    · filter_upwards [Ioi_mem_nhds (max_lt h hx)] with y hy
      have hy' : max b₀ 0 < y := hy
      exact hzero y (lt_of_le_of_lt (le_max_right _ _) hy')
        (Or.inr (lt_of_le_of_lt (le_max_left _ _) hy'))
  have hdz : ∀ y : ℝ, 0 < y → (y < a₀ ∨ b₀ < y) → deriv Φ y = 0 := by
    intro y hy hyo
    have h1 : Φ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := hEv y hy hyo
    simpa using h1.deriv_eq
  have hEvd : ∀ y : ℝ, 0 < y → (y < a₀ ∨ b₀ < y) → deriv Φ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    intro y hy hyo
    rcases hyo with h | h
    · filter_upwards [Ioo_mem_nhds hy h] with z hz
      exact hdz z hz.1 (Or.inl hz.2)
    · filter_upwards [Ioi_mem_nhds (max_lt h hy)] with z hz
      have hz' : max b₀ 0 < z := hz
      exact hdz z (lt_of_le_of_lt (le_max_right _ _) hz')
        (Or.inr (lt_of_le_of_lt (le_max_left _ _) hz'))
  have hdzz : ∀ y : ℝ, 0 < y → (y < a₀ ∨ b₀ < y) → deriv (deriv Φ) y = 0 := by
    intro y hy hyo
    simpa using (hEvd y hy hyo).deriv_eq
  have hΦa : Φ a = 0 := hzero a ha0 (Or.inl haa)
  have hda : deriv Φ a = 0 := hdz a ha0 (Or.inl haa)
  have hΦb : Φ b = 0 := hzero b hb0 (Or.inr hb₀)
  have hdb : deriv Φ b = 0 := hdz b hb0 (Or.inr hb₀)
  have hvan : ∀ x : ℝ, 0 < x → (x < a ∨ b < x) →
      Φ x = 0 ∧ deriv Φ x = 0 ∧ deriv (deriv Φ) x = 0 := by
    intro x hx hxo
    have hxo' : x < a₀ ∨ b₀ < x := by
      rcases hxo with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact ⟨hzero x hx hxo', hdz x hx hxo', hdzz x hx hxo'⟩
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hsub : Icc a b ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le ha0 hs.1
  have hne : ∀ x ∈ Icc a b, (x : ℂ) ≠ 0 := fun x hx =>
    Complex.ofReal_ne_zero.2 (lt_of_lt_of_le ha0 hx.1).ne'
  -- Reduction of the integrals over `(0, ∞)` to `[a, b]`.
  have hred : ∀ F : ℝ → ℂ, (∀ x : ℝ, 0 < x → (x < a ∨ b < x) → F x = 0) →
      ∫ x in Ioi (0 : ℝ), F x = ∫ x in a..b, F x := by
    intro F hF
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub ?_
    intro x hx
    apply hF x hx.1
    rcases lt_or_ge x a with h | h
    · exact Or.inl h
    · exact Or.inr (not_le.1 fun h' => hx.2 ⟨h, h'⟩)
  have hpt1 : ∀ x : ℝ, 0 < x → (x < a ∨ b < x) →
      ψ x * (deriv (deriv Φ) x + deriv Φ x / (x : ℂ) - 4 * Φ x / (x : ℂ) ^ 2) * (x : ℂ) = 0 := by
    intro x hx hxo
    obtain ⟨h1, h2, h3⟩ := hvan x hx hxo
    rw [h1, h2, h3]
    simp
  have hpt2 : ∀ x : ℝ, 0 < x → (x < a ∨ b < x) → f x * Φ x * (x : ℂ) = 0 := by
    intro x hx hxo
    rw [(hvan x hx hxo).1]
    simp
  rw [hred _ hpt1, hred _ hpt2]
  -- Auxiliary functions.
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun r => f r - ψ' r / (r : ℂ) + 4 * ψ r / (r : ℂ) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨vv, hvv⟩ : ∃ vv : ℝ → ℂ, vv = fun s : ℝ => (s : ℂ) * deriv Φ s := ⟨_, rfl⟩
  obtain ⟨vd, hvd⟩ : ∃ vd : ℝ → ℂ, vd = fun s : ℝ => deriv Φ s + (s : ℂ) * deriv (deriv Φ) s :=
    ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ → ℂ, W = fun u : ℝ => ∫ x in a..u, Φ x := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1 : ℝ → ℂ, w1 = fun s : ℝ => (s : ℂ) * Φ s - W s := ⟨_, rfl⟩
  have hψg : ∀ s : ℝ, 0 < s → ψ' s - ψ' a = ∫ r in a..s, g r := by
    intro s hs
    rw [hg]
    exact hψi a s ha0 hs
  have hψu : ∀ x ∈ uIcc a b, HasDerivAt ψ (ψ' x) x := by
    intro x hx
    rw [hIcc] at hx
    exact hψd x (lt_of_lt_of_le ha0 hx.1)
  have hcΦ : ContinuousOn Φ (Icc a b) := hΦc.mono hsub
  have hcΦ1 : ContinuousOn (deriv Φ) (Icc a b) := hΦ1c.mono hsub
  have hcΦ2 : ContinuousOn (deriv (deriv Φ)) (Icc a b) := hΦ2c.mono hsub
  have hcψ : ContinuousOn ψ (Icc a b) := fun x hx =>
    (hψd x (lt_of_lt_of_le ha0 hx.1)).continuousAt.continuousWithinAt
  have hcψ' : ContinuousOn ψ' (Icc a b) := hψc.mono hsub
  have hII : ∀ F : ℝ → ℂ, ContinuousOn F (Icc a b) → IntervalIntegrable F volume a b :=
    fun F hF => ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hF)
  have hfI : IntervalIntegrable f volume a b := by
    refine IntegrableOn.intervalIntegrable ?_
    rw [hIcc]
    exact (hf.mono_set hsub).integrableOn_isCompact isCompact_Icc
  have hgI : IntervalIntegrable g volume a b := by
    have hc1 : ContinuousOn (fun r : ℝ => ψ' r / (r : ℂ)) (Icc a b) :=
      hcψ'.div Complex.continuous_ofReal.continuousOn (fun x hx => hne x hx)
    have hc2 : ContinuousOn (fun r : ℝ => 4 * ψ r / (r : ℂ) ^ 2) (Icc a b) :=
      (continuousOn_const.mul hcψ).div (Complex.continuous_ofReal.continuousOn.pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx))
    rw [hg]
    exact (hfI.sub (hII _ hc1)).add (hII _ hc2)
  have hWd : ∀ s ∈ Icc a b, HasDerivAt W (Φ s) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
    have hint : IntervalIntegrable Φ volume a s := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.1]
      exact hcΦ.mono (Icc_subset_Icc le_rfl hs.2)
    rw [hW]
    exact intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hΦc s hs0)
      (hΦc.continuousAt (Ioi_mem_nhds hs0))
  have hcW : ContinuousOn W (Icc a b) := fun s hs => (hWd s hs).continuousAt.continuousWithinAt
  have hw1d : ∀ s ∈ Icc a b, HasDerivAt w1 (vv s) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 s := by
      simpa using (hasDerivAt_id' s).ofReal_comp
    have h2 := (h0.mul (hΦd s hs0)).sub (hWd s hs)
    rw [hw1]
    refine h2.congr_deriv ?_
    simp only [hvv]
    ring
  have hvvd : ∀ s ∈ Icc a b, HasDerivAt vv (vd s) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 s := by
      simpa using (hasDerivAt_id' s).ofReal_comp
    have h1 := h0.mul (hΦdd s hs0)
    rw [hvv]
    refine h1.congr_deriv ?_
    simp only [hvd]
    ring
  have hcvv : ContinuousOn vv (Icc a b) := by
    rw [hvv]
    exact Complex.continuous_ofReal.continuousOn.mul hcΦ1
  have hcvd : ContinuousOn vd (Icc a b) := by
    rw [hvd]
    exact hcΦ1.add (Complex.continuous_ofReal.continuousOn.mul hcΦ2)
  have hvvI : IntervalIntegrable vv volume a b := hII _ hcvv
  have hvdI : IntervalIntegrable vd volume a b := hII _ hcvd
  have hψ'I : IntervalIntegrable ψ' volume a b := hII _ hcψ'
  have hvva : vv a = 0 := by
    rw [hvv]
    simp [hda]
  have hvvb : vv b = 0 := by
    rw [hvv]
    simp [hdb]
  have hw1a : w1 a = 0 := by
    rw [hw1]
    simp [hΦa, hW]
  have hw1b : w1 b = -W b := by
    rw [hw1]
    simp [hΦb]
  have hWb : W b = ∫ x in a..b, Φ x := by rw [hW]
  have hE7 : w1 b + W b = 0 := by
    rw [hw1b]
    ring
  -- Step (ii): the Fubini-type identity for `∫ ψ' · vv`.
  have E3 : ∫ x in a..b, (ψ' x - ψ' a) * vv x =
      (∫ t in a..b, g t) * w1 b - ∫ t in a..b, g t * w1 t := by
    have h1 : ∫ x in a..b, (ψ' x - ψ' a) * vv x = ∫ s in a..b, (∫ t in a..s, g t) * vv s := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [hIcc] at hx
      show (ψ' x - ψ' a) * vv x = (∫ t in a..x, g t) * vv x
      rw [hψg x (lt_of_lt_of_le ha0 hx.1)]
    rw [h1]
    exact radial_primitive_mul_eq hab g w1 vv hgI (fun s hs => hw1d s hs) hcvv
  have E2 : ∫ x in a..b, vv x = w1 b := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hw1d x (by rwa [hIcc] at hx)) hvvI
    rw [h, hw1a, sub_zero]
  have E1 : ∫ x in a..b, ψ' x * vv x =
      (∫ x in a..b, (ψ' x - ψ' a) * vv x) + ψ' a * ∫ x in a..b, vv x := by
    have h1 : ∀ x, ψ' x * vv x = (ψ' x - ψ' a) * vv x + ψ' a * vv x := fun x => by ring
    have hI1 : IntervalIntegrable (fun x => (ψ' x - ψ' a) * vv x) volume a b :=
      hII _ ((hcψ'.sub continuousOn_const).mul hcvv)
    have hI2 : IntervalIntegrable (fun x => ψ' a * vv x) volume a b :=
      hII _ (continuousOn_const.mul hcvv)
    simp_rw [h1]
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul]
  have hgt : IntervalIntegrable (fun x => g x * ((x : ℂ) * Φ x)) volume a b :=
    hgI.mul_continuousOn (by rw [hIcc]; exact Complex.continuous_ofReal.continuousOn.mul hcΦ)
  have hgW : IntervalIntegrable (fun x => g x * W x) volume a b :=
    hgI.mul_continuousOn (by rw [hIcc]; exact hcW)
  have E4 : ∫ t in a..b, g t * w1 t =
      (∫ t in a..b, g t * ((t : ℂ) * Φ t)) - ∫ t in a..b, g t * W t := by
    rw [← intervalIntegral.integral_sub hgt hgW]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [hw1]
    ring
  have E5 : ∫ x in a..b, (ψ' x - ψ' a) * Φ x =
      (∫ t in a..b, g t) * W b - ∫ t in a..b, g t * W t := by
    have h1 : ∫ x in a..b, (ψ' x - ψ' a) * Φ x = ∫ s in a..b, (∫ t in a..s, g t) * Φ s := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [hIcc] at hx
      show (ψ' x - ψ' a) * Φ x = (∫ t in a..x, g t) * Φ x
      rw [hψg x (lt_of_lt_of_le ha0 hx.1)]
    rw [h1]
    exact radial_primitive_mul_eq hab g W Φ hgI hWd hcΦ
  have E6 : ∫ x in a..b, (ψ' x - ψ' a) * Φ x = (∫ x in a..b, ψ' x * Φ x) - ψ' a * W b := by
    have h1 : ∀ x, (ψ' x - ψ' a) * Φ x = ψ' x * Φ x - ψ' a * Φ x := fun x => by ring
    have hI1 : IntervalIntegrable (fun x => ψ' x * Φ x) volume a b := hII _ (hcψ'.mul hcΦ)
    have hI2 : IntervalIntegrable (fun x => ψ' a * Φ x) volume a b :=
      hII (fun x => ψ' a * Φ x) (continuousOn_const.mul hcΦ)
    simp_rw [h1]
    rw [intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_const_mul, ← hWb]
  have hQeq : ∀ x : ℝ, ((x : ℂ) * g x + ψ' x) * Φ x = g x * ((x : ℂ) * Φ x) + ψ' x * Φ x :=
    fun x => by ring
  have hQ : IntervalIntegrable (fun x => ((x : ℂ) * g x + ψ' x) * Φ x) volume a b := by
    simp_rw [hQeq]
    exact hgt.add (hII _ (hcψ'.mul hcΦ))
  have E8 : ∫ x in a..b, ((x : ℂ) * g x + ψ' x) * Φ x =
      (∫ x in a..b, g x * ((x : ℂ) * Φ x)) + ∫ x in a..b, ψ' x * Φ x := by
    have hI2 : IntervalIntegrable (fun x => ψ' x * Φ x) volume a b := hII _ (hcψ'.mul hcΦ)
    simp_rw [hQeq]
    exact intervalIntegral.integral_add hgt hI2
  have hK3 : ∫ x in a..b, ψ' x * vv x = -∫ x in a..b, ((x : ℂ) * g x + ψ' x) * Φ x := by
    linear_combination E1 + E3 + ψ' a * E2 - E4 + E5 - E6 + E8
      + ((∫ t in a..b, g t) + ψ' a) * hE7
  -- Step (i): integration by parts for `ψ`.
  have hK2 : ∫ x in a..b, ψ x * vd x = -∫ x in a..b, ψ' x * vv x := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
      (u := ψ) (v := vv) (u' := ψ') (v' := vd)
      (fun x hx => hψu x hx) (fun x hx => hvvd x (by rwa [hIcc] at hx)) hψ'I hvdI
    rw [h, hvva, hvvb]
    ring
  -- Pointwise identities on `[a, b]`.
  have hpt3 : ∀ x ∈ uIcc a b,
      ψ x * (deriv (deriv Φ) x + deriv Φ x / (x : ℂ) - 4 * Φ x / (x : ℂ) ^ 2) * (x : ℂ)
        = ψ x * vd x - 4 * ψ x * Φ x / (x : ℂ) := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : (x : ℂ) ≠ 0 := hne x hx
    simp only [hvd]
    field_simp
    ring
  have hpt4 : ∀ x ∈ uIcc a b, f x * Φ x * (x : ℂ) =
      ((x : ℂ) * g x + ψ' x) * Φ x - 4 * ψ x * Φ x / (x : ℂ) := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : (x : ℂ) ≠ 0 := hne x hx
    simp only [hg]
    field_simp
    ring
  have hI : ∫ x in a..b, ψ x * (deriv (deriv Φ) x + deriv Φ x / (x : ℂ) - 4 * Φ x / (x : ℂ) ^ 2)
      * (x : ℂ) = ∫ x in a..b, (ψ x * vd x - 4 * ψ x * Φ x / (x : ℂ)) :=
    intervalIntegral.integral_congr hpt3
  have hR : ∫ x in a..b, f x * Φ x * (x : ℂ) =
      ∫ x in a..b, (((x : ℂ) * g x + ψ' x) * Φ x - 4 * ψ x * Φ x / (x : ℂ)) :=
    intervalIntegral.integral_congr hpt4
  have hψvd : IntervalIntegrable (fun x => ψ x * vd x) volume a b :=
    hII _ (hcψ.mul hcvd)
  have hψΦ : IntervalIntegrable (fun x => 4 * ψ x * Φ x / (x : ℂ)) volume a b :=
    hII _ (((continuousOn_const.mul hcψ).mul hcΦ).div
      Complex.continuous_ofReal.continuousOn hne)
  rw [hI, hR, intervalIntegral.integral_sub hψvd hψΦ,
    intervalIntegral.integral_sub hQ hψΦ, hK2, hK3]
  ring

end UnforcedLeray.Short.PartI
end
