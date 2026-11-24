import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUOneWeight` (item `PartIII-b:C/near/delta/9/1/5`)

One weight of the energy inequality (source 3541-3545): for a smooth cutoff `w` with `w = 1` on
`[2δ, t₁]`, `0 ≤ w ≤ 1`, `w' ≤ (K/δ) 1_{[δ,2δ]}` and `κ ∫ (w/s) E ≤ ∫ w' E`, one gets
`(κ/t₁) ∫_ε^{t₁} E ≤ (K/δ) ∫_δ^{2δ} E`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- A locally integrable factor against a continuous function that vanishes off `[a,b]` is
integrable on `(0,∞)`. -/
private lemma fu1_int_helper (E h : ℝ → ℝ) (a b : ℝ) (hE : IntegrableOn E (Icc a b))
    (hh : ContinuousOn h (Icc a b)) (h0 : ∀ s, s ∉ Icc a b → h s = 0) :
    IntegrableOn (fun s => h s * E s) (Ioi 0) := by
  have h1 : IntegrableOn (fun s => h s * E s) (Icc a b) := by
    have := hE.mul_continuousOn hh isCompact_Icc
    convert this using 1
    funext s
    ring
  refine IntegrableOn.of_forall_sdiff_eq_zero h1 measurableSet_Ioi ?_
  intro x hx
  simp [h0 x hx.2]

theorem fuOneWeight : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUOneWeight := by
  intro κ K δ ε t₁ t₂ E w hκ hδ hε2 hεt₁ ht₁t₂ hE0 hEint hw hsupp hw01 hw1 hder hineq
  have hε : 0 < ε := by linarith
  have hEint' : IntegrableOn E (Icc δ t₂) := hEint δ t₂ hδ (by linarith)
  have hw0 : ∀ s, s ∉ Icc δ t₂ → w s = 0 := by
    intro s hs
    by_contra h
    exact hs (hsupp (subset_tsupport w h))
  have hwc : ContinuousOn (fun s => w s / s) (Icc δ t₂) := by
    refine ContinuousOn.div hw.continuous.continuousOn continuousOn_id ?_
    intro s hs
    exact ne_of_gt (lt_of_lt_of_le hδ hs.1)
  have hfI : IntegrableOn (fun s => w s / s * E s) (Ioi 0) :=
    fu1_int_helper E (fun s => w s / s) δ t₂ hEint' hwc (fun s hs => by simp [hw0 s hs])
  have hw'I : IntegrableOn (fun s => deriv w s * E s) (Ioi 0) := by
    refine fu1_int_helper E (deriv w) δ t₂ hEint'
      (hw.continuous_deriv (by norm_num)).continuousOn ?_
    intro s hs
    by_contra h
    exact hs (hsupp (support_deriv_subset h))
  have hE_Icc : IntegrableOn E (Icc ε t₁) := hEint ε t₁ hε (by linarith)
  have hsub1 : Icc ε t₁ ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hε hx.1
  have hsub2 : Icc δ (2 * δ) ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hδ hx.1
  -- lower bound on the left by the interval integral of `E / t₁`
  have hA : ∫ s in Icc ε t₁, 1 / t₁ * E s ≤ ∫ s in Ioi (0 : ℝ), w s / s * E s := by
    have h1 : ∫ s in Icc ε t₁, 1 / t₁ * E s ≤ ∫ s in Icc ε t₁, w s / s * E s := by
      apply setIntegral_mono_on (hE_Icc.const_mul (1 / t₁)) (hfI.mono_set hsub1) measurableSet_Icc
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
      have hwx : w x = 1 := hw1 x ⟨by linarith [hx.1], hx.2⟩
      rw [hwx]
      apply mul_le_mul_of_nonneg_right _ (hE0 x)
      exact one_div_le_one_div_of_le hx0 hx.2
    have h2 : ∫ s in Icc ε t₁, w s / s * E s ≤ ∫ s in Ioi (0 : ℝ), w s / s * E s := by
      apply setIntegral_mono_set hfI
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
        exact mul_nonneg (div_nonneg (hw01 x).1 (le_of_lt (Set.mem_Ioi.mp hx))) (hE0 x)
      · exact Eventually.of_forall fun x hx => hsub1 hx
    exact h1.trans h2
  have hA' : 1 / t₁ * ∫ s in Icc ε t₁, E s ≤ ∫ s in Ioi (0 : ℝ), w s / s * E s := by
    rw [← integral_const_mul]
    exact hA
  -- upper bound on the right by the interval integral on `[δ, 2δ]`
  have hfeq : (fun s => K / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s * E s) =
      (Icc δ (2 * δ)).indicator (fun s => K / δ * E s) := by
    funext s
    by_cases hs : s ∈ Icc δ (2 * δ)
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hgI : IntegrableOn (fun s => K / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s * E s)
      (Ioi 0) := by
    rw [hfeq]
    exact (IntegrableOn.integrable_indicator (Integrable.const_mul (hEint δ (2 * δ) hδ (by linarith))
      (K / δ)) measurableSet_Icc).integrableOn
  have hC : ∫ s in Ioi (0 : ℝ), deriv w s * E s ≤ K / δ * ∫ s in Icc δ (2 * δ), E s := by
    have hmono : ∫ s in Ioi (0 : ℝ), deriv w s * E s ≤
        ∫ s in Ioi (0 : ℝ), K / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s * E s := by
      apply setIntegral_mono hw'I hgI
      intro s
      exact mul_le_mul_of_nonneg_right (hder s) (hE0 s)
    have heval : ∫ s in Ioi (0 : ℝ), K / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s * E s
        = K / δ * ∫ s in Icc δ (2 * δ), E s := by
      rw [hfeq, setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.2 hsub2,
        integral_const_mul]
    exact hmono.trans_eq heval
  have hmain : κ * (1 / t₁ * ∫ s in Icc ε t₁, E s) ≤ K / δ * ∫ s in Icc δ (2 * δ), E s :=
    calc κ * (1 / t₁ * ∫ s in Icc ε t₁, E s)
        ≤ κ * ∫ s in Ioi (0 : ℝ), w s / s * E s := mul_le_mul_of_nonneg_left hA' hκ.le
      _ ≤ ∫ s in Ioi (0 : ℝ), deriv w s * E s := hineq
      _ ≤ K / δ * ∫ s in Icc δ (2 * δ), E s := hC
  have hrw : κ / t₁ * ∫ s in Icc ε t₁, E s = κ * (1 / t₁ * ∫ s in Icc ε t₁, E s) := by ring
  rw [hrw]
  exact hmain

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
