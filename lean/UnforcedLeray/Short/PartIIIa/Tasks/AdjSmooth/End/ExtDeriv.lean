import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2`, task `endExtDeriv`: the derivative of the extension to the end age

Proves `EndExtDeriv` (the calculus leaf of `Sub/PartIII-a_T21_2_7_2_1_2.lean`, SP 3060-3071): if a
field `h` is differentiable on `(t, s) × ℝ²` and both `h` and `fderiv h` extend continuously to
`[t, s) × ℝ²` by `endExt`, then the extension of `h` has, within `[t, s) × ℝ²`, the derivative given
by the extension of `fderiv h`. Off the end age `endExt` is `h` near the point. At the end age the
convex open set `(t, m) × ℝ²`, `m = (t + s)/2`, has closure inside `[t, s) × ℝ²`, and
`hasFDerivWithinAt_closure_of_tendsto_fderiv` gives the derivative on that closure, which is then
restricted to a neighbourhood of the end age.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Off the end age `r = t`, the extension agrees with the field itself near every point. -/
theorem endExt_eventuallyEq_off {F : Type*} [NormedAddCommGroup F] (t : ℝ) (h : ℝ × (ℝ × ℝ) → F)
    {y : ℝ × (ℝ × ℝ)} (hy : y.1 ≠ t) : endExt t h =ᶠ[𝓝 y] h := by
  have hopen : IsOpen {q : ℝ × (ℝ × ℝ) | q.1 ≠ t} := isOpen_ne_fun continuous_fst continuous_const
  filter_upwards [hopen.mem_nhds hy] with q hq
  have hq' : q.1 ≠ t := hq
  unfold endExt
  rw [if_neg hq']

theorem endExtDeriv : UnforcedLeray.Short.IIIa.EndExtDeriv := by
  intro F _ _ t s hts h hd hc hc' p hp
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  by_cases hpt : p.1 = t
  · obtain ⟨m, htm, hms⟩ : ∃ m : ℝ, t < m ∧ m < s := ⟨(t + s) / 2, by linarith, by linarith⟩
    have hVU : Ioo t m ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
      fun y hy => ⟨⟨hy.1.1, lt_trans hy.1.2 hms⟩, mem_univ _⟩
    have hVS : Ioo t m ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) :=
      fun y hy => ⟨⟨hy.1.1.le, lt_trans hy.1.2 hms⟩, mem_univ _⟩
    have hVconv : Convex ℝ (Ioo t m ×ˢ (univ : Set (ℝ × ℝ))) :=
      (convex_Ioo t m).prod convex_univ
    have hV_ne : ∀ y ∈ Ioo t m ×ˢ (univ : Set (ℝ × ℝ)), y.1 ≠ t := fun y hy => hy.1.1.ne'
    -- the extension is differentiable on `V`, with derivative the extension of `fderiv h`
    have hdiffV : DifferentiableOn ℝ (endExt t h) (Ioo t m ×ˢ (univ : Set (ℝ × ℝ))) := by
      intro y hy
      exact ((hd.differentiableAt (hU.mem_nhds (hVU hy))).congr_of_eventuallyEq
        (endExt_eventuallyEq_off t h (hV_ne y hy))).differentiableWithinAt
    have hfd : ∀ y ∈ Ioo t m ×ˢ (univ : Set (ℝ × ℝ)),
        fderiv ℝ (endExt t h) y = endExt t (fderiv ℝ h) y := by
      intro y hy
      rw [(endExt_eventuallyEq_off t h (hV_ne y hy)).fderiv_eq]
      unfold endExt
      rw [if_neg (hV_ne y hy)]
    have hc0 : Tendsto (endExt t (fderiv ℝ h)) (𝓝[Ico t s ×ˢ (univ : Set (ℝ × ℝ))] p)
        (𝓝 (endExt t (fderiv ℝ h) p)) := hc' p hp
    have hlim : Tendsto (fun y => fderiv ℝ (endExt t h) y)
        (𝓝[Ioo t m ×ˢ (univ : Set (ℝ × ℝ))] p) (𝓝 (endExt t (fderiv ℝ h) p)) := by
      refine Tendsto.congr' ?_ (hc0.mono_left (nhdsWithin_mono p hVS))
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hfd y hy).symm
    have hcl : closure (Ioo t m ×ˢ (univ : Set (ℝ × ℝ))) ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := by
      rw [closure_prod_eq, closure_Ioo htm.ne, closure_univ]
      exact fun y hy => ⟨⟨hy.1.1, lt_of_le_of_lt hy.1.2 hms⟩, mem_univ _⟩
    have hbase : HasFDerivWithinAt (endExt t h) (endExt t (fderiv ℝ h) p)
        (closure (Ioo t m ×ˢ (univ : Set (ℝ × ℝ)))) p :=
      hasFDerivWithinAt_closure_of_tendsto_fderiv hdiffV hVconv
        (isOpen_Ioo.prod isOpen_univ)
        (fun y hy => (hc y (hcl hy)).mono hVS) hlim
    -- restrict from the closure to `[t, s) × ℝ²` near the end age
    have hW : Iio m ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 p :=
      (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨show p.1 < m by rw [hpt]; exact htm, mem_univ _⟩
    have hsub : (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) ∩ (Iio m ×ˢ (univ : Set (ℝ × ℝ))) ⊆
        closure (Ioo t m ×ˢ (univ : Set (ℝ × ℝ))) := by
      intro y hy
      rw [closure_prod_eq, closure_Ioo htm.ne, closure_univ]
      exact ⟨⟨hy.1.1.1, le_of_lt hy.2.1⟩, mem_univ _⟩
    have hW' := hbase.mono hsub
    exact (hasFDerivWithinAt_inter hW).1 hW'
  · have hpU : p ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
      ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hpt), hp.1.2⟩, mem_univ _⟩
    have hdiff : HasFDerivAt h (fderiv ℝ h p) p :=
      (hd.differentiableAt (hU.mem_nhds hpU)).hasFDerivAt
    have h1 : HasFDerivAt (endExt t h) (fderiv ℝ h p) p :=
      hdiff.congr_of_eventuallyEq (endExt_eventuallyEq_off t h hpt)
    have h2 : endExt t (fderiv ℝ h) p = fderiv ℝ h p := by
      unfold endExt
      rw [if_neg hpt]
    rw [h2]
    exact h1.hasFDerivWithinAt

end UnforcedLeray.Short.IIIa
