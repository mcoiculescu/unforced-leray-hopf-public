import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.TriangleFubini.Meas

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb
namespace TriFubiniAux
open PartIIbF4Aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem gridPt_nonneg' {s : ℝ} (hs : 0 ≤ s) (n k : ℕ) : 0 ≤ gridPt s n k := by
  unfold gridPt
  positivity

theorem gridPt_le' {s : ℝ} (hs : 0 ≤ s) (n k : ℕ) (hk : k ≤ n + 1) : gridPt s n k ≤ s := by
  unfold gridPt
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hn1]
  have : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hk
  nlinarith

theorem tendsto_U_apply {H M_U : ℝ} {U : ℝ → ℝ → (X →L[ℝ] X)} {r t : ℝ} (y : X)
    (hr : r ≤ H) (ht : t ∈ Icc 0 H)
    (hU_id : ∀ r ∈ Icc 0 H, U r r = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ H → (U c b).comp (U b a) = U c a)
    (hU_cont : ∀ a ∈ Icc 0 H, ∀ g : X, ContinuousOn (fun b => U b a g) (Icc a H))
    (hU_bd : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → ‖U b a‖ ≤ M_U)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 t)) (hge : ∀ n, t ≤ τ n)
    (hle : ∀ᶠ n in atTop, τ n ≤ r) :
    Tendsto (fun n => U r (τ n) y) atTop (𝓝 (U r t y)) := by
  have hrH : ∀ᶠ n in atTop, τ n ≤ H := hle.mono fun n hn => hn.trans hr
  have hnh : Tendsto τ atTop (𝓝[Icc t H] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ
      (hrH.mono fun n hn => ⟨hge n, hn⟩)
  have hcont_t := (hU_cont t ht y) t ⟨le_rfl, ht.2⟩
  have hU_rn_t : Tendsto (fun n : ℕ => U (τ n) t y) atTop (𝓝 y) := by
    have h := hcont_t.tendsto.comp hnh
    rwa [hU_id t ht, ContinuousLinearMap.id_apply] at h
  have hnorm_zero : Tendsto (fun n : ℕ => ‖y - U (τ n) t y‖) atTop (𝓝 0) := by
    simpa [sub_self] using ((tendsto_const_nhds (x := y)).sub hU_rn_t).norm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hnorm_zero.const_mul M_U)
  filter_upwards [hle] with n hn
  have hcoc := hU_coc t (τ n) r ht.1 (hge n) hn hr
  have hsub : U r (τ n) y - U r t y = U r (τ n) (y - U (τ n) t y) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply, hcoc]
  rw [hsub]
  calc ‖U r (τ n) (y - U (τ n) t y)‖
      ≤ ‖U r (τ n)‖ * ‖y - U (τ n) t y‖ := (U r (τ n)).le_opNorm _
    _ ≤ M_U * ‖y - U (τ n) t y‖ :=
      mul_le_mul_of_nonneg_right (hU_bd (τ n) r (ht.1.trans (hge n)) hn hr) (norm_nonneg _)

theorem aesm_triangle {H M_U : ℝ} (U : ℝ → ℝ → (X →L[ℝ] X)) (L : ℝ → (X →L[ℝ] ℝ)) (s : ℝ)
    (hs : 0 ≤ s) (hsH : s ≤ H)
    (hU_id : ∀ r ∈ Icc 0 H, U r r = ContinuousLinearMap.id ℝ X)
    (hU_coc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ H → (U c b).comp (U b a) = U c a)
    (hU_cont : ∀ a ∈ Icc 0 H, ∀ g : X, ContinuousOn (fun b => U b a g) (Icc a H))
    (hU_bd : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → ‖U b a‖ ≤ M_U)
    (hmeas : ∀ a : ℝ, 0 ≤ a → a ≤ s → ∀ x : X,
      AEStronglyMeasurable (fun r => L r (U r a x)) (volume.restrict (Ioc a s)))
    (f : ℝ → X) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 s))) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ => (Ioi q.2).indicator (fun r => L r (U r q.2 (f q.2))) q.1)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))) := by
  set A : ℕ → ℝ × ℝ → ℝ := fun n q =>
    ∑ k ∈ Finset.range (n + 1),
      (Ico (gridPt s n k) (gridPt s n (k + 1))).indicator (fun _ => (1 : ℝ)) q.2 *
        (Ioi (gridPt s n (k + 1))).indicator
          (fun r => L r (U r (gridPt s n (k + 1)) (f q.2))) q.1 with hA
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := A) (fun n => ?_) ?_
  · refine Finset.aestronglyMeasurable_fun_sum _ fun k hk => ?_
    have hk' : k + 1 ≤ n + 1 := by have := Finset.mem_range.1 hk; omega
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (measurable_const.indicator measurableSet_Ico).comp measurable_snd |>.aestronglyMeasurable
    · exact aesm_ae U L s _ (hmeas _ (gridPt_nonneg' hs n _) (gridPt_le' hs n _ hk')) f hf
  · have hr1 : ∀ᵐ q ∂((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))),
        q.1 ∈ Ioc 0 s :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hr2 : ∀ᵐ q ∂((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))),
        q.2 ∈ Ioc 0 s :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hr1, hr2] with q hq1 hq2
    obtain ⟨r, t⟩ := q
    simp only at hq1 hq2
    rcases eq_or_lt_of_le hq2.2 with hts | hts
    · -- t = s
      subst hts
      have hK : (Ioi t).indicator (fun r => L r (U r t (f t))) r = 0 :=
        Set.indicator_of_notMem (by simpa using hq1.2) _
      simp only [hK]
      have : ∀ n, A n (r, t) = 0 := by
        intro n
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk' : k + 1 ≤ n + 1 := by have := Finset.mem_range.1 hk; omega
        have : t ∉ Ico (gridPt t n k) (gridPt t n (k + 1)) := by
          intro h
          have := gridPt_le' hs n (k + 1) hk'
          linarith [h.2]
        simp [Set.indicator_of_notMem this]
      simp only [this]
      exact tendsto_const_nhds
    · have ht : t ∈ Ioo 0 s := ⟨hq2.1, hts⟩
      set τ : ℕ → ℝ := fun n => gridPt s n (⌊t * ((n + 1 : ℕ) : ℝ) / s⌋₊ + 1) with hτdef
      have hbd : ∀ n : ℕ, t < τ n ∧ τ n ≤ s ∧ τ n - t ≤ s / ((n + 1 : ℕ) : ℝ) := by
        intro n
        obtain ⟨_, ht_mem, hr_le_s, hdiff, _⟩ := gridPt_Properties ht n
        exact ⟨ht_mem.2, hr_le_s, hdiff⟩
      have hτ : Tendsto τ atTop (𝓝 t) := by
        have h0 : Tendsto (fun n : ℕ => τ n - t) atTop (𝓝 0) := by
          refine squeeze_zero (fun n => sub_nonneg.2 (hbd n).1.le) (fun n => (hbd n).2.2) ?_
          have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
          exact tendsto_const_nhds.div_atTop hnat
        simpa using h0.add_const t
      have hAeq : ∀ n, A n (r, t) =
          (Ioi (τ n)).indicator (fun r => L r (U r (τ n) (f t))) r := by
        intro n
        obtain ⟨hk_mem, ht_mem, _, _, hdisj⟩ := gridPt_Properties ht n
        simp only [hA]
        rw [Finset.sum_eq_single (⌊t * ((n + 1 : ℕ) : ℝ) / s⌋₊)]
        · rw [Set.indicator_of_mem ht_mem, one_mul]
        · intro j hj hjk
          simp [Set.indicator_of_notMem (hdisj j hj hjk)]
        · intro hnot; exact absurd hk_mem hnot
      simp only [hAeq]
      by_cases hrt : t < r
      · have hK : (Ioi t).indicator (fun r => L r (U r t (f t))) r = L r (U r t (f t)) :=
          Set.indicator_of_mem (by simpa using hrt) _
        simp only [hK]
        have hev : ∀ᶠ n in atTop, τ n < r := hτ.eventually (gt_mem_nhds hrt)
        have hlim := tendsto_U_apply (H := H) (M_U := M_U) (U := U) (f t)
          (hq1.2.trans hsH) ⟨ht.1.le, ht.2.le.trans hsH⟩ hU_id hU_coc hU_cont hU_bd hτ
          (fun n => (hbd n).1.le) (hev.mono fun n hn => hn.le)
        have hlim' := ((L r).continuous.tendsto _).comp hlim
        refine hlim'.congr' ?_
        filter_upwards [hev] with n hn
        simp [Set.indicator_of_mem (show r ∈ Ioi (τ n) from hn)]
      · have hK : (Ioi t).indicator (fun r => L r (U r t (f t))) r = 0 :=
          Set.indicator_of_notMem (by simpa using hrt) _
        simp only [hK]
        have : ∀ n, (Ioi (τ n)).indicator (fun r => L r (U r (τ n) (f t))) r = 0 := by
          intro n
          refine Set.indicator_of_notMem ?_ _
          simp only [mem_Ioi, not_lt]
          exact (not_lt.1 hrt).trans (hbd n).1.le
        simp only [this]
        exact tendsto_const_nhds

end TriFubiniAux
end UnforcedLeray.Short.IIb
