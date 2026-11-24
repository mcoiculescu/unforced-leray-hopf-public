import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUCoreWindow` (item `PartIII-b:C/near/delta/9/1/2`)

The weighted energy identity as an inequality (source 3541-3545): with `R = 0` a.e. on `(0,T)`,
`N ≥ 0`, `ν ≥ 0`, `w ≥ 0` smooth and compactly supported in `(0,T)`, the identity
`∫ w' E = ∫ w (κ E/s + 2νN + 2R)` gives `κ ∫ (w/s) E ≤ ∫ w' E`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- A compact set inside `(0,T)` lies in some `[a,b]` with `0 < a < b`. -/
private lemma fu2_compact_Icc (w : ℝ → ℝ) (T : ℝ) (hts : tsupport w ⊆ Ioo 0 T)
    (hc : HasCompactSupport w) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport w ⊆ Icc a b := by
  rcases (tsupport w).eq_empty_or_nonempty with h | hne
  · exact ⟨1, 2, one_pos, by norm_num, by rw [h]; exact empty_subset _⟩
  · have hK : IsCompact (tsupport w) := hc.isCompact
    have h1 : sInf (tsupport w) ∈ tsupport w := hK.sInf_mem hne
    have h2 : sSup (tsupport w) ∈ tsupport w := hK.sSup_mem hne
    have h12 : sInf (tsupport w) ≤ sSup (tsupport w) := csInf_le hK.bddBelow h2
    exact ⟨sInf (tsupport w), sSup (tsupport w) + 1, (hts h1).1, by linarith,
      fun x hx => ⟨csInf_le hK.bddBelow hx, by linarith [le_csSup hK.bddAbove hx]⟩⟩

/-- A locally integrable factor against a continuous function that vanishes off `[a,b]` is
integrable on `(0,∞)`. -/
private lemma fu2_int_helper (E h : ℝ → ℝ) (a b : ℝ) (hE : IntegrableOn E (Icc a b))
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

theorem fuCoreWindow : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUCoreWindow := by
  intro κ ν T E N R hν hE0 hN0 hint hR w hw hcs hts hw0 hsum
  obtain ⟨a, b, ha, hab, hsub⟩ := fu2_compact_Icc w T hts hcs
  have hw_out : ∀ s, s ∉ Icc a b → w s = 0 := fun s hs => by
    by_contra h
    exact hs (hsub (subset_tsupport w h))
  have hwc : Continuous w := hw.continuous
  obtain ⟨hEi, hNi, hRi⟩ := hint a b ha hab
  have hwdiv : ContinuousOn (fun s => w s / s) (Icc a b) := by
    refine ContinuousOn.div hwc.continuousOn continuousOn_id ?_
    intro s hs
    exact ne_of_gt (lt_of_lt_of_le ha hs.1)
  have hI1 : IntegrableOn (fun s => w s / s * E s) (Ioi 0) :=
    fu2_int_helper E (fun s => w s / s) a b hEi hwdiv (fun s hs => by simp [hw_out s hs])
  have hI2 : IntegrableOn (fun s => w s * N s) (Ioi 0) :=
    fu2_int_helper N w a b hNi hwc.continuousOn (fun s hs => hw_out s hs)
  have hI3 : IntegrableOn (fun s => w s * R s) (Ioi 0) :=
    fu2_int_helper R w a b hRi hwc.continuousOn (fun s hs => hw_out s hs)
  -- the cross term `∫ w R` vanishes: `R = 0` a.e. on `(0,T)` and `w = 0` off `(0,T)`
  have hwR : ∫ s in Ioi (0 : ℝ), w s * R s = 0 := by
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_ae
    have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo (0 : ℝ) T → R s = 0 :=
      (ae_restrict_iff' measurableSet_Ioo).1 hR
    filter_upwards [h1] with s hs
    by_cases hsI : s ∈ Ioo (0 : ℝ) T
    · simp [hs hsI]
    · have hws : w s = 0 := by
        by_contra h
        exact hsI (hts (subset_tsupport w h))
      simp [hws]
  have hsplit : ∀ s, w s * (κ / s * E s + 2 * ν * N s + 2 * R s) =
      κ * (w s / s * E s) + 2 * ν * (w s * N s) + 2 * (w s * R s) := fun s => by ring
  have hsum' : ∫ s in Ioi (0 : ℝ), deriv w s * E s =
      ∫ s in Ioi (0 : ℝ), (κ * (w s / s * E s) + 2 * ν * (w s * N s) + 2 * (w s * R s)) :=
    hsum.trans (integral_congr_ae (Eventually.of_forall hsplit))
  have J1 : IntegrableOn (fun s => κ * (w s / s * E s)) (Ioi 0) := Integrable.const_mul hI1 κ
  have J2 : IntegrableOn (fun s => 2 * ν * (w s * N s)) (Ioi 0) :=
    Integrable.const_mul hI2 (2 * ν)
  have J3 : IntegrableOn (fun s => 2 * (w s * R s)) (Ioi 0) := Integrable.const_mul hI3 2
  have J12 : IntegrableOn (fun s => κ * (w s / s * E s) + 2 * ν * (w s * N s)) (Ioi 0) :=
    Integrable.add J1 J2
  rw [integral_add J12 J3, integral_add J1 J2, integral_const_mul κ,
    integral_const_mul (2 * ν), integral_const_mul 2] at hsum'
  have hnn : 0 ≤ 2 * ν * ∫ s in Ioi (0 : ℝ), w s * N s :=
    mul_nonneg (by linarith) (integral_nonneg fun s => mul_nonneg (hw0 s) (hN0 s))
  linarith [hsum', hwR, hnn]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
