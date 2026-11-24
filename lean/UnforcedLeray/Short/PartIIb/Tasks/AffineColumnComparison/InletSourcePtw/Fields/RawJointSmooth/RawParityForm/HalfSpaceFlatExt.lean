import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The closed zero region `w ≤ 0` of the half space flat extension. -/
def hsfeZr : Set (ℝ × (ℝ × ℝ)) := {x | x.2.1 ≤ 0}

theorem hsfeIsClosed_Zr : IsClosed hsfeZr :=
  isClosed_le (continuous_fst.comp continuous_snd) continuous_const

theorem hsfeMem_compl_Zr {y : ℝ × (ℝ × ℝ)} : y ∈ (hsfeZr)ᶜ ↔ 0 < y.2.1 := by
  simp [hsfeZr]

/-- The segment from a point of `w > 0` to a boundary point `w = 0` stays in `w > 0` before its end. -/
theorem hsfeSeg_mem_compl {y y₀ : ℝ × (ℝ × ℝ)} (hy : y ∈ (hsfeZr)ᶜ) (hy₀ : y₀.2.1 = 0) {t : ℝ}
    (_ht0 : 0 ≤ t) (ht : t < 1) : y + t • (y₀ - y) ∈ (hsfeZr)ᶜ := by
  rw [hsfeMem_compl_Zr] at hy ⊢
  have e : (y + t • (y₀ - y)).2.1 = (1 - t) * y.2.1 := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.snd_sub, Prod.fst_sub,
      Prod.smul_fst, smul_eq_mul, hy₀]
    ring
  rw [e]
  exact mul_pos (by linarith) hy

theorem hsfeNhdsWithin_parPos_eq_bot {y₀ : ℝ × (ℝ × ℝ)} (hneg : y₀.2.1 < 0) :
    𝓝[(hsfeZr)ᶜ] y₀ = ⊥ := by
  rw [← Filter.eventually_false_iff_eq_bot]
  have hc : Continuous fun y : ℝ × (ℝ × ℝ) => y.2.1 := continuous_fst.comp continuous_snd
  have h1 : ∀ᶠ y in 𝓝 y₀, y.2.1 < 0 := hc.continuousAt.eventually_lt continuousAt_const hneg
  have h2 : ∀ᶠ y in 𝓝[(hsfeZr)ᶜ] y₀, y.2.1 < 0 := eventually_nhdsWithin_of_eventually_nhds h1
  have h3 : ∀ᶠ y in 𝓝[(hsfeZr)ᶜ] y₀, y ∈ (hsfeZr)ᶜ := eventually_mem_nhdsWithin
  filter_upwards [h2, h3] with y hy2 hy3
  rw [hsfeMem_compl_Zr] at hy3
  exact lt_asymm hy2 hy3

section General

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuity across the zero region. -/
theorem hsfeContinuous_of_tendsto_bd {g : ℝ × (ℝ × ℝ) → F} (h0 : ∀ y ∈ hsfeZr, g y = 0)
    (hc : ContinuousOn g (hsfeZr)ᶜ) (ht : ∀ y₀ ∈ hsfeZr, Tendsto g (𝓝[(hsfeZr)ᶜ] y₀) (𝓝 0)) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ hsfeZr
  · rw [ContinuousAt, h0 y hy]
    have h1 : Tendsto g (𝓝[hsfeZr] y) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => (h0 z hz).symm)
    have h2 := h1.sup (ht y hy)
    rwa [← nhdsWithin_union, union_compl_self, nhdsWithin_univ] at h2
  · exact hc.continuousAt (hsfeIsClosed_Zr.isOpen_compl.mem_nhds hy)

/-- The derivative on the boundary `w = 0` vanishes when the derivative tends to `0` there
(mean value inequality along the segment from the boundary point). -/
theorem hsfeHasFDerivAt_zero_of_tendsto_bd {g : ℝ × (ℝ × ℝ) → F} (hcont : Continuous g)
    (h0 : ∀ y ∈ hsfeZr, g y = 0) (hd : DifferentiableOn ℝ g (hsfeZr)ᶜ) {y₀ : ℝ × (ℝ × ℝ)}
    (ht : Tendsto (fun y => ‖fderiv ℝ g y‖) (𝓝[(hsfeZr)ᶜ] y₀) (𝓝 0)) (hy₀ : y₀.2.1 = 0) :
    HasFDerivAt g (0 : (ℝ × (ℝ × ℝ)) →L[ℝ] F) y₀ := by
  have hy₀Z : y₀ ∈ hsfeZr := le_of_eq hy₀
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hev : ∀ᶠ z in 𝓝[(hsfeZr)ᶜ] y₀, ‖fderiv ℝ g z‖ ≤ ε :=
    ((tendsto_order.1 ht).2 ε hε).mono fun z hz => hz.le
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun y hy => ?_⟩
  simp only [h0 y₀ hy₀Z, sub_zero, zero_apply]
  by_cases hya : y ∈ hsfeZr
  · rw [h0 y hya, norm_zero]
    positivity
  · have hyc : y ∈ (hsfeZr)ᶜ := hya
    set φ : ℝ → F := fun t => g (y + t • (y₀ - y)) with hφ
    have hline : Continuous fun t : ℝ => y + t • (y₀ - y) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hφc : ContinuousOn φ (Icc 0 1) := (hcont.comp hline).continuousOn
    have hφd : ∀ t ∈ Ico (0 : ℝ) 1,
        HasDerivWithinAt φ (fderiv ℝ g (y + t • (y₀ - y)) (y₀ - y)) (Ici t) t := by
      intro t ht
      have hz : y + t • (y₀ - y) ∈ (hsfeZr)ᶜ := hsfeSeg_mem_compl hyc hy₀ ht.1 ht.2
      have hgd : HasFDerivAt g (fderiv ℝ g (y + t • (y₀ - y))) (y + t • (y₀ - y)) :=
        (hd.differentiableAt (hsfeIsClosed_Zr.isOpen_compl.mem_nhds hz)).hasFDerivAt
      have hl : HasDerivAt (fun t : ℝ => y + t • (y₀ - y)) (y₀ - y) t := by
        simpa using ((hasDerivAt_id t).smul_const (y₀ - y)).const_add y
      exact (hgd.comp_hasDerivAt t hl).hasDerivWithinAt
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
        ‖fderiv ℝ g (y + t • (y₀ - y)) (y₀ - y)‖ ≤ ε * ‖y - y₀‖ := by
      intro t ht
      have hz : y + t • (y₀ - y) ∈ (hsfeZr)ᶜ := hsfeSeg_mem_compl hyc hy₀ ht.1 ht.2
      have hdist : dist (y + t • (y₀ - y)) y₀ < δ := by
        rw [dist_eq_norm]
        have e : y + t • (y₀ - y) - y₀ = (1 - t) • (y - y₀) := by
          rw [sub_smul, one_smul, smul_sub, smul_sub]
          abel
        rw [e, norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
        calc (1 - t) * ‖y - y₀‖ ≤ 1 * ‖y - y₀‖ :=
              mul_le_mul_of_nonneg_right (by linarith [ht.1]) (norm_nonneg _)
          _ = dist y y₀ := by rw [one_mul, dist_eq_norm]
          _ < δ := hy
      calc ‖fderiv ℝ g (y + t • (y₀ - y)) (y₀ - y)‖
          ≤ ‖fderiv ℝ g (y + t • (y₀ - y))‖ * ‖y₀ - y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * ‖y - y₀‖ := by
          rw [norm_sub_rev y₀ y]
          exact mul_le_mul_of_nonneg_right (hball hdist hz) (norm_nonneg _)
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd hbound 1
      ⟨zero_le_one, le_rfl⟩
    have e1 : φ 1 = 0 := by
      simp only [hφ, one_smul, add_sub_cancel]
      exact h0 y₀ hy₀Z
    have e0 : φ 0 = g y := by simp only [hφ, zero_smul, add_zero]
    rw [e1, e0, zero_sub, norm_neg, sub_zero, mul_one] at hmvt
    exact hmvt

/-- **Smoothness across the zero region** (induction on `k`, as `contDiff_of_tendsto_axis`). -/
theorem hsfeContDiff_of_tendsto_bd : ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ × (ℝ × ℝ) → F}, (∀ y ∈ hsfeZr, g y = 0) → ContDiffOn ℝ k g (hsfeZr)ᶜ →
    (∀ n ≤ k, ∀ y₀ ∈ hsfeZr,
      Tendsto (fun y => ‖iteratedFDeriv ℝ n g y‖) (𝓝[(hsfeZr)ᶜ] y₀) (𝓝 0)) →
    ContDiff ℝ k g := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g h0 hc ht
    rw [Nat.cast_zero, contDiff_zero]
    refine hsfeContinuous_of_tendsto_bd h0 (hc.continuousOn) fun y₀ hy₀ => ?_
    have := ht 0 le_rfl y₀ hy₀
    simp only [norm_iteratedFDeriv_zero] at this
    exact tendsto_zero_iff_norm_tendsto_zero.2 this
  | succ k ih =>
    intro F _ _ g h0 hc ht
    have hcont : Continuous g := by
      refine hsfeContinuous_of_tendsto_bd h0 hc.continuousOn fun y₀ hy₀ => ?_
      have := ht 0 (Nat.zero_le _) y₀ hy₀
      simp only [norm_iteratedFDeriv_zero] at this
      exact tendsto_zero_iff_norm_tendsto_zero.2 this
    have hdiff : DifferentiableOn ℝ g (hsfeZr)ᶜ := hc.differentiableOn (by simp)
    have hfd0 : ∀ y₀ ∈ hsfeZr, HasFDerivAt g (0 : (ℝ × (ℝ × ℝ)) →L[ℝ] F) y₀ := by
      intro y₀ hy₀
      have hy₀' : y₀.2.1 ≤ 0 := hy₀
      rcases lt_or_eq_of_le hy₀' with hneg | heq
      · have hev : ∀ᶠ y in 𝓝 y₀, y.2.1 < 0 :=
          (continuous_fst.comp continuous_snd).continuousAt.eventually_lt
            continuousAt_const hneg
        refine (hasFDerivAt_const (0 : F) y₀).congr_of_eventuallyEq ?_
        filter_upwards [hev] with y hy
        exact h0 y (le_of_lt hy)
      · refine hsfeHasFDerivAt_zero_of_tendsto_bd hcont h0 hdiff ?_ heq
        have := ht 1 (by omega) y₀ hy₀
        simpa only [norm_iteratedFDeriv_one] using this
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fderiv ℝ g, ?_, fun x => ?_⟩
    · refine ih (g := fderiv ℝ g) (fun y hy => (hfd0 y hy).fderiv) ?_ ?_
      · exact hc.fderiv_of_isOpen hsfeIsClosed_Zr.isOpen_compl (by rw [hcast])
      · intro n hn y₀ hy₀
        have := ht (n + 1) (by omega) y₀ hy₀
        simpa only [norm_iteratedFDeriv_fderiv] using this
    · by_cases hx : x ∈ hsfeZr
      · rw [(hfd0 x hx).fderiv]
        exact hfd0 x hx
      · exact (hdiff.differentiableAt (hsfeIsClosed_Zr.isOpen_compl.mem_nhds hx)).hasFDerivAt

end General

/-- **Half-space flat extension** (`HalfSpaceFlatExt`): the zero extension across `w = 0` of a
function that is `C^k` on `w > 0` with derivatives of order `≤ k` that are `O(w)` locally
uniformly in `z` is `C^k`. The zero region is `w ≤ 0`; the boundary `w = 0` is handled by
`hsfeHasFDerivAt_zero_of_tendsto_bd`, the rest of the region is locally zero. -/
theorem halfSpaceFlatExt : UnforcedLeray.Short.IIb.HalfSpaceFlatExt := by
  intro k F _ _ f hf hbd
  have hZc : (hsfeZr)ᶜ = parPos := by
    ext y
    simp [hsfeZr, parPos]
  have hopen : IsOpen parPos := isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  apply hsfeContDiff_of_tendsto_bd k (g := zeroExtW f)
  · intro y hy
    have hy' : y.2.1 ≤ 0 := hy
    simp [zeroExtW, not_lt.2 hy']
  · rw [hZc]
    refine hf.congr (fun y hy => ?_)
    have hy' : (0 : ℝ) < y.2.1 := hy
    simp [zeroExtW, hy']
  · intro n hn y₀ hy₀
    have hy₀' : y₀.2.1 ≤ 0 := hy₀
    rcases lt_or_eq_of_le hy₀' with hneg | heq
    · rw [hsfeNhdsWithin_parPos_eq_bot hneg]
      exact tendsto_bot
    · obtain ⟨C, hC⟩ := hbd n hn (|y₀.2.2| + 1)
      have hcw : Continuous fun y : ℝ × (ℝ × ℝ) => y.2.1 := continuous_fst.comp continuous_snd
      have hw : Tendsto (fun y : ℝ × (ℝ × ℝ) => y.2.1) (𝓝[(hsfeZr)ᶜ] y₀) (𝓝 0) := by
        have h := (hcw.tendsto y₀).mono_left (nhdsWithin_le_nhds (s := (hsfeZr)ᶜ))
        rw [heq] at h
        exact h
      have hev1 : ∀ᶠ y in 𝓝[(hsfeZr)ᶜ] y₀, y.2.1 < 1 := by
        have h := hw.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
        exact h
      have hcabs : Continuous fun y : ℝ × (ℝ × ℝ) => |y.2.2| := by fun_prop
      have hev2 : ∀ᶠ y in 𝓝[(hsfeZr)ᶜ] y₀, |y.2.2| < |y₀.2.2| + 1 := by
        have hh : ∀ᶠ y in 𝓝 y₀, |y.2.2| < |y₀.2.2| + 1 :=
          hcabs.continuousAt.eventually_lt continuousAt_const (by linarith)
        exact eventually_nhdsWithin_of_eventually_nhds hh
      have hlim : Tendsto (fun y : ℝ × (ℝ × ℝ) => C * y.2.1) (𝓝[(hsfeZr)ᶜ] y₀) (𝓝 0) := by
        simpa using hw.const_mul C
      refine squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ hlim
      have hEq : ∀ y ∈ parPos,
          iteratedFDeriv ℝ n (zeroExtW f) y = iteratedFDeriv ℝ n f y := by
        intro y hy
        have hy' : (0 : ℝ) < y.2.1 := hy
        have hEv : zeroExtW f =ᶠ[𝓝 y] f :=
          Filter.eventually_of_mem (hopen.mem_nhds hy) fun z hz => by
            have hz' : (0 : ℝ) < z.2.1 := hz
            simp [zeroExtW, hz']
        exact (hEv.iteratedFDeriv ℝ n).eq_of_nhds
      filter_upwards [self_mem_nhdsWithin, hev1, hev2] with y hy h1 h2
      have hyP : y ∈ parPos := by
        rw [hZc] at hy
        exact hy
      rw [hEq y hyP]
      exact hC y hyP h1.le h2.le

end UnforcedLeray.Short.IIb
