import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.WeakAndSlices
import UnforcedLeray.Lib.BochnerTime.JointRep
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel

/-!
# `DuhamelRegularity.WindowGlue`: Countable good-age coverings, continuous `Lp` path gluing,
`JointRep` + `wrapPlane` periodic realization, and global `D²` weak-derivative assembly

Helper module for `PartII-b:F8/1/org/3` (`MeridionalDuhamelRegularity`, SP 2301–2305).
All declarations are inside `UnforcedLeray.Short.IIb.F8Duh` (R6).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.F8Duh

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Cell-to-volume equality on arbitrary positive open intervals `Ioo a b` -/

lemma ae_vol_eq_on_Ioo_of_ae_cell_periodic {c a b : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    {u₁ u₂ : CProf}
    (hsm₁ : StronglyMeasurable u₁) (hsm₂ : StronglyMeasurable u₂)
    (hper₁ : QPeriodic c u₁) (hper₂ : QPeriodic c u₂)
    (hcell : ∀ᵐ s ∂volume, s ∈ Ioo a b →
      (fun y => u₁ (s, y)) =ᵐ[volume.restrict (B0579.cell c)] (fun y => u₂ (s, y))) :
    u₁ =ᵐ[volume.restrict (Ioo a b ×ˢ univ)] u₂ := by
  let S_gt : Set Coord := {x : Coord | a < x.1}
  have hS_meas : MeasurableSet S_gt := measurableSet_lt measurable_const measurable_fst
  let u₁' : CProf := S_gt.indicator u₁
  let u₂' : CProf := S_gt.indicator u₂
  have hsm₁' : StronglyMeasurable u₁' := hsm₁.indicator hS_meas
  have hsm₂' : StronglyMeasurable u₂' := hsm₂.indicator hS_meas
  have hper₁' : QPeriodic c u₁' := by
    refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp hper₁] with x hx hp
    by_cases hxa : x ∈ S_gt
    · have hxa' : qShift c x ∈ S_gt := hxa
      dsimp only [u₁']
      rw [indicator_of_mem hxa', indicator_of_mem hxa, hx hp]
    · have hxa' : qShift c x ∉ S_gt := hxa
      dsimp only [u₁']
      rw [indicator_of_notMem hxa', indicator_of_notMem hxa]
  have hper₂' : QPeriodic c u₂' := by
    refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp hper₂] with x hx hp
    by_cases hxa : x ∈ S_gt
    · have hxa' : qShift c x ∈ S_gt := hxa
      dsimp only [u₂']
      rw [indicator_of_mem hxa', indicator_of_mem hxa, hx hp]
    · have hxa' : qShift c x ∉ S_gt := hxa
      dsimp only [u₂']
      rw [indicator_of_notMem hxa', indicator_of_notMem hxa]
  have hcell' : ∀ᵐ s ∂volume, s ∈ Ioo 0 b →
      (fun y => u₁' (s, y)) =ᵐ[volume.restrict (B0579.cell c)] (fun y => u₂' (s, y)) := by
    filter_upwards [hcell] with s hs hs0b
    by_cases hsa : a < s
    · have heq₁ : (fun y => u₁' (s, y)) = fun y => u₁ (s, y) := by
        funext y; exact indicator_of_mem (show (s, y) ∈ S_gt from hsa) u₁
      have heq₂ : (fun y => u₂' (s, y)) = fun y => u₂ (s, y) := by
        funext y; exact indicator_of_mem (show (s, y) ∈ S_gt from hsa) u₂
      rw [heq₁, heq₂]
      exact hs ⟨hsa, hs0b.2⟩
    · have heq₁ : (fun y => u₁' (s, y)) = 0 := by
        funext y; exact indicator_of_notMem (show (s, y) ∉ S_gt from hsa) u₁
      have heq₂ : (fun y => u₂' (s, y)) = 0 := by
        funext y; exact indicator_of_notMem (show (s, y) ∉ S_gt from hsa) u₂
      rw [heq₁, heq₂]
  have hvol := ContBodySourceAux.ae_vol_eq_of_ae_cell_periodic hc hsm₁' hsm₂' hper₁' hper₂' hcell'
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)]
  filter_upwards [hvol] with x hx hx_mem
  have hx0b : x.1 ∈ Ioo 0 b := ⟨lt_of_le_of_lt ha hx_mem.1.1, hx_mem.1.2⟩
  have hxa : x ∈ S_gt := hx_mem.1.1
  have h := hx hx0b
  dsimp only [u₁', u₂'] at h
  rwa [indicator_of_mem hxa, indicator_of_mem hxa] at h

/-! ## 2. Continuous `Lp`-path helpers and pointwise agreement on open overlaps -/

lemma eqOn_Ioo_of_continuousOn_ae {X : Type*} [MetricSpace X] {a b : ℝ}
    {f₁ f₂ : ℝ → X}
    (hc₁ : ContinuousOn f₁ (Ioo a b)) (hc₂ : ContinuousOn f₂ (Ioo a b))
    (hae : ∀ᵐ t ∂volume, t ∈ Ioo a b → f₁ t = f₂ t) :
    ∀ t ∈ Ioo a b, f₁ t = f₂ t := by
  intro t₀ ht₀
  by_contra hne
  have hpos : 0 < dist (f₁ t₀) (f₂ t₀) := dist_pos.2 hne
  have hcont_dist : ContinuousAt (fun t => dist (f₁ t) (f₂ t)) t₀ :=
    (hc₁.continuousAt (isOpen_Ioo.mem_nhds ht₀)).dist
      (hc₂.continuousAt (isOpen_Ioo.mem_nhds ht₀))
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ Ioo a b ∧ 0 < dist (f₁ t) (f₂ t) :=
    Filter.Eventually.and (isOpen_Ioo.mem_nhds ht₀)
      (hcont_dist.eventually (lt_mem_nhds hpos))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hsub : Ioo (t₀ - δ) (t₀ + δ) ⊆ {t : ℝ | ¬ (t ∈ Ioo a b → f₁ t = f₂ t)} := by
    intro t ht h_imp
    have hdist_lt : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨ht_in, hd_pos⟩ := hball hdist_lt
    exact (dist_pos.1 hd_pos) (h_imp ht_in)
  have hnull : volume {t : ℝ | ¬ (t ∈ Ioo a b → f₁ t = f₂ t)} = 0 := mem_ae_iff.1 hae
  have hvol_zero : volume (Ioo (t₀ - δ) (t₀ + δ)) = 0 := measure_mono_null hsub hnull
  rw [Real.volume_Ioo] at hvol_zero
  have : (0 : ℝ) < (t₀ + δ) - (t₀ - δ) := by linarith
  exact (ENNReal.ofReal_pos.2 this).ne' hvol_zero

lemma continuousOn_toPathLq_of_cellL2 {c a b : ℝ} {w : CProf}
    (hmem : ∀ t ∈ Ioo a b, MemLp (F8U.slice w t) 2 (volume.restrict (B0579.cell c)))
    (hcont : ∀ t ∈ Ioo a b,
      Tendsto (fun t' => F8U.cellL2 c (fun y => w (t', y) - w (t, y))) (𝓝 t) (𝓝 0)) :
    ContinuousOn (UnforcedLeray.BochnerTime.toPathLq 2 (volume.restrict (B0579.cell c)) w)
      (Ioo a b) := by
  let μc := volume.restrict (B0579.cell c)
  intro t ht
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h_real : Tendsto (fun t' => (F8U.cellL2 c (fun y => w (t', y) - w (t, y))).toReal)
      (𝓝 t) (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
  filter_upwards [isOpen_Ioo.mem_nhds ht, h_real.eventually (gt_mem_nhds hε)] with t' ht' hlt
  have hmt : MemLp (fun y => w (t, y)) 2 μc := hmem t ht
  have hmt' : MemLp (fun y => w (t', y)) 2 μc := hmem t' ht'
  rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hmt',
    UnforcedLeray.BochnerTime.toPathLq_of_memLp hmt,
    dist_edist, Lp.edist_def]
  have hae : (⇑(hmt'.toLp _) - ⇑(hmt.toLp _)) =ᵐ[μc] fun y => w (t', y) - w (t, y) := by
    filter_upwards [MemLp.coeFn_toLp hmt', MemLp.coeFn_toLp hmt] with y hy' hy
    simp only [Pi.sub_apply, hy', hy]
  rwa [eLpNorm_congr_ae hae]

/-! ## 3. Countable good-age sequences covering `(0, ∞)` and dense in `(0, ∞)` -/

lemma exists_good_in_Ioo {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ)
    (α β : ℝ) (hα : 0 ≤ α) (hαβ : α < β) :
    ∃ σ ∈ Ioo α β, Good σ := by
  by_contra hnone
  have hsub : Ioo α β ⊆ {σ : ℝ | ¬ (0 < σ → Good σ)} := by
    intro σ hσ h_imp
    exact hnone ⟨σ, hσ, h_imp (lt_of_le_of_lt hα hσ.1)⟩
  have hnull : volume {σ : ℝ | ¬ (0 < σ → Good σ)} = 0 := mem_ae_iff.1 hGood
  have hvol_zero : volume (Ioo α β) = 0 := measure_mono_null hsub hnull
  rw [Real.volume_Ioo] at hvol_zero
  exact (ENNReal.ofReal_pos.2 (sub_pos.2 hαβ)).ne' hvol_zero

/-- Sequence of good ages `aSeq n ∈ (0, 1/(n+2))` converging to `0⁺`. -/
def aSeq {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (n : ℕ) : ℝ :=
  Classical.choose (exists_good_in_Ioo hGood 0 (1 / ((n : ℝ) + 2)) le_rfl (by positivity))

lemma aSeq_spec {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (n : ℕ) :
    aSeq hGood n ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 2)) ∧ Good (aSeq hGood n) :=
  Classical.choose_spec (exists_good_in_Ioo hGood 0 (1 / ((n : ℝ) + 2)) le_rfl (by positivity))

lemma tendsto_aSeq {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) :
    Tendsto (aSeq hGood) atTop (𝓝 0) := by
  have h_inv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def, add_assoc, one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_inv
    (fun n => (aSeq_spec hGood n).1.1.le) (fun n => (aSeq_spec hGood n).1.2.le)

/-- Sequence of good ages `bSeq k ∈ ((k+1)/2, (k+1)/2 + 1/4)` covering `[3/4, ∞)` with overlap `≥ 1/4`. -/
def bSeq {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (k : ℕ) : ℝ :=
  Classical.choose (exists_good_in_Ioo hGood (((k : ℝ) + 1) / 2) (((k : ℝ) + 1) / 2 + 1 / 4)
    (by positivity) (by linarith))

lemma bSeq_spec {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (k : ℕ) :
    bSeq hGood k ∈ Ioo (((k : ℝ) + 1) / 2) (((k : ℝ) + 1) / 2 + 1 / 4) ∧ Good (bSeq hGood k) :=
  Classical.choose_spec (exists_good_in_Ioo hGood (((k : ℝ) + 1) / 2) (((k : ℝ) + 1) / 2 + 1 / 4)
    (by positivity) (by linarith))

/-- Interleaved covering sequence `winSeq` of good ages covering all of `(0, ∞)`. -/
def winSeq {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (m : ℕ) : ℝ :=
  if m % 2 = 0 then aSeq hGood (m / 2) else bSeq hGood (m / 2)

lemma winSeq_pos_and_good {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (m : ℕ) :
    0 < winSeq hGood m ∧ Good (winSeq hGood m) := by
  unfold winSeq
  split_ifs with hm
  · exact ⟨(aSeq_spec hGood (m / 2)).1.1, (aSeq_spec hGood (m / 2)).2⟩
  · have hb := bSeq_spec hGood (m / 2)
    exact ⟨lt_trans (by positivity) hb.1.1, hb.2⟩

lemma exists_mem_winSeq {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ)
    {s : ℝ} (hs : 0 < s) :
    ∃ m : ℕ, s ∈ Ioo (winSeq hGood m) (winSeq hGood m + 1) := by
  by_cases hs1 : s < 1
  · obtain ⟨n, hn⟩ := exists_nat_gt (1 / s)
    have hdiv : 1 / ((n : ℝ) + 2) < s := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 < (n : ℝ) * s := (div_lt_iff₀ hs).1 hn
      nlinarith
    have ha := (aSeq_spec hGood n).1
    refine ⟨2 * n, ?_⟩
    have hmod : (2 * n) % 2 = 0 := Nat.mul_mod_right 2 n
    have hq : (2 * n) / 2 = n := Nat.mul_div_right n two_pos
    simp only [winSeq, hmod, ↓reduceIte, hq, mem_Ioo]
    exact ⟨lt_trans ha.2 hdiv, by linarith [ha.1]⟩
  · replace hs1 : 1 ≤ s := le_of_not_gt hs1
    let k : ℕ := ⌊2 * s - 3 / 2⌋₊
    have hk_le : (k : ℝ) ≤ 2 * s - 3 / 2 := Nat.floor_le (by linarith)
    have hk_lt : 2 * s - 3 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hb := (bSeq_spec hGood k).1
    refine ⟨2 * k + 1, ?_⟩
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    have hq : (2 * k + 1) / 2 = k := by omega
    simp only [winSeq, hmod, one_ne_zero, ↓reduceIte, hq, mem_Ioo]
    exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

/-- Countable sequence of good ages dense in `(0, ∞)` (indexed via `Nat.unpair`). -/
def denseGoodSeq {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (m : ℕ) : ℝ :=
  Classical.choose (exists_good_in_Ioo hGood
    ((m.unpair.1 : ℝ) / ((m.unpair.2 : ℝ) + 1))
    (((m.unpair.1 : ℝ) + 1) / ((m.unpair.2 : ℝ) + 1))
    (by positivity)
    (div_lt_div_of_pos_right (by linarith) (by positivity)))

lemma denseGoodSeq_spec {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ) (m : ℕ) :
    denseGoodSeq hGood m ∈ Ioo
      ((m.unpair.1 : ℝ) / ((m.unpair.2 : ℝ) + 1))
      (((m.unpair.1 : ℝ) + 1) / ((m.unpair.2 : ℝ) + 1)) ∧
    Good (denseGoodSeq hGood m) :=
  Classical.choose_spec (exists_good_in_Ioo hGood
    ((m.unpair.1 : ℝ) / ((m.unpair.2 : ℝ) + 1))
    (((m.unpair.1 : ℝ) + 1) / ((m.unpair.2 : ℝ) + 1))
    (by positivity)
    (div_lt_div_of_pos_right (by linarith) (by positivity)))

lemma exists_denseGoodSeq_in_Ioo {Good : ℝ → Prop} (hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ m : ℕ, denseGoodSeq hGood m ∈ Ioo α β := by
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / (β - α))
  set N : ℝ := (j : ℝ) + 1
  have hN_pos : 0 < N := by positivity
  have hgap : 2 < N * (β - α) := by
    have hj' : 2 / (β - α) < N := lt_trans hj (by dsimp [N]; linarith)
    exact (div_lt_iff₀ (sub_pos.2 hαβ)).1 hj'
  let i : ℕ := ⌊N * α⌋₊ + 1
  have hi_gt : N * α < (i : ℝ) := by
    dsimp [i]; push_cast; exact Nat.lt_floor_add_one (N * α)
  have hi_le : (i : ℝ) + 1 ≤ N * α + 2 := by
    dsimp [i]; push_cast
    have := Nat.floor_le (mul_nonneg hN_pos.le hα.le)
    linarith
  let m : ℕ := Nat.pair i j
  refine ⟨m, ?_⟩
  have hunp : m.unpair = (i, j) := Nat.unpair_pair i j
  have hspec := (denseGoodSeq_spec hGood m).1
  rw [hunp] at hspec
  have hleft : α < (i : ℝ) / N := (lt_div_iff₀ hN_pos).2 (by linarith)
  have hright : ((i : ℝ) + 1) / N < β := (div_lt_iff₀ hN_pos).2 (by nlinarith)
  exact ⟨lt_trans hleft hspec.1, lt_trans hspec.2 hright⟩

/-! ## 4. Periodic extension of a `JointRep` and piecewise `StronglyMeasurable` `D²` gluing -/

/-- Periodic `CProf` built from a `JointRep` `U : ℝ → Plane → CMerid` via `wrapPlane c`. -/
def perJointProf (c : ℝ) (U : ℝ → B0579.Plane → CMerid) : CProf :=
  fun x => if 0 < x.1 then U x.1 (wrapPlane c x.2) else 0

lemma stronglyMeasurable_perJointProf {c : ℝ} {U : ℝ → B0579.Plane → CMerid}
    (hU : StronglyMeasurable (Function.uncurry U)) :
    StronglyMeasurable (perJointProf c U) := by
  have hcomp : StronglyMeasurable (fun x : Coord => U x.1 (wrapPlane c x.2)) :=
    hU.comp_measurable (measurable_fst.prodMk ((measurable_wrapPlane c).comp measurable_snd))
  have hM : MeasurableSet {x : Coord | 0 < x.1} := measurableSet_lt measurable_const measurable_fst
  have heq : perJointProf c U = {x : Coord | 0 < x.1}.indicator
      (fun x => U x.1 (wrapPlane c x.2)) := by
    funext x
    by_cases hp : 0 < x.1
    · simp [perJointProf, hp]
    · simp [perJointProf, hp]
  rw [heq]
  exact hcomp.indicator hM

lemma qPeriodic_perJointProf {c : ℝ} (hc : 0 < c) (U : ℝ → B0579.Plane → CMerid) :
    QPeriodic c (perJointProf c U) := by
  refine QPerHalf.of_ae_imp (Eventually.of_forall fun x hx => ?_)
  simp only [perJointProf, hx, ↓reduceIte, qShift]
  rw [isPeriodic_wrapPlane hc x.2]

lemma slice_perJointProf_ae_cell {c : ℝ} (hc : 0 < c)
    {u : ℝ → Lp CMerid 2 (volume.restrict (B0579.cell c))}
    {U : ℝ → B0579.Plane → CMerid}
    (hUu : ∀ s ∈ Ioi (0 : ℝ), U s =ᵐ[volume.restrict (B0579.cell c)] u s)
    {s : ℝ} (hs : 0 < s) :
    F8U.slice (perJointProf c U) s =ᵐ[volume.restrict (B0579.cell c)] u s := by
  have heq_on : F8U.slice (perJointProf c U) s =ᵐ[volume.restrict (B0579.cell c)] U s := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell c)]
    exact Eventually.of_forall fun y hy => by
      simp [F8U.slice, perJointProf, hs, wrapPlane_of_mem_cell hc hy]
  exact heq_on.trans (hUu s hs)

lemma tendsto_cellL2_perJointProf {c : ℝ} (hc : 0 < c)
    {u : ℝ → Lp CMerid 2 (volume.restrict (B0579.cell c))}
    (hu_cont : ContinuousOn u (Ioi 0))
    {U : ℝ → B0579.Plane → CMerid}
    (hUu : ∀ s ∈ Ioi (0 : ℝ), U s =ᵐ[volume.restrict (B0579.cell c)] u s)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun s' => F8U.cellL2 c
      (fun y => perJointProf c U (s', y) - perJointProf c U (s, y))) (𝓝 s) (𝓝 0) := by
  have hcont_at : ContinuousAt u s := hu_cont.continuousAt (isOpen_Ioi.mem_nhds hs)
  have hnorm : Tendsto (fun s' => ENNReal.ofReal ‖u s' - u s‖) (𝓝 s) (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_iff_norm_sub_tendsto_zero.1 hcont_at)
  refine hnorm.congr' ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with s' hs'
  have hae_s := slice_perJointProf_ae_cell hc hUu hs
  have hae_s' := slice_perJointProf_ae_cell hc hUu hs'
  have hae_sub : (fun y => perJointProf c U (s', y) - perJointProf c U (s, y)) =ᵐ[volume.restrict (B0579.cell c)]
      ⇑(u s' - u s) := by
    filter_upwards [hae_s', hae_s, Lp.coeFn_sub (u s') (u s)] with y hy' hy hsub
    change F8U.slice (perJointProf c U) s' y - F8U.slice (perJointProf c U) s y = _
    rw [hy', hy, hsub]
    rfl
  unfold F8U.cellL2
  rw [eLpNorm_congr_ae hae_sub, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- Disjointified first-window piecewise gluing of a sequence of `StronglyMeasurable` profiles
on `Ioo (σ m) (σ m + 1)`. -/
def glueWindowProf (σ : ℕ → ℝ) (hcov : ∀ s : ℝ, 0 < s → ∃ m : ℕ, s ∈ Ioo (σ m) (σ m + 1))
    (F : ℕ → CProf) : CProf :=
  fun x => if h : 0 < x.1 then F (Nat.find (hcov x.1 h)) x else 0

private def glueWindowProfAux (σ : ℕ → ℝ) (F : ℕ → CProf) : ℕ → CProf
  | 0 => 0
  | N + 1 =>
      {x : Coord | x.1 ∈ Ioo (σ N) (σ N + 1) ∧ ∀ j < N, x.1 ∉ Ioo (σ j) (σ j + 1)}.piecewise
        (F N) (glueWindowProfAux σ F N)

private lemma glueWindowProfAux_eq_of_find {σ : ℕ → ℝ}
    {hcov : ∀ s : ℝ, 0 < s → ∃ m : ℕ, s ∈ Ioo (σ m) (σ m + 1)}
    {F : ℕ → CProf} {x : Coord} (hx : 0 < x.1) :
    ∀ N : ℕ, Nat.find (hcov x.1 hx) < N →
      glueWindowProfAux σ F N x = F (Nat.find (hcov x.1 hx)) x := by
  set m := Nat.find (hcov x.1 hx)
  have hm_mem : x.1 ∈ Ioo (σ m) (σ m + 1) := Nat.find_spec (hcov x.1 hx)
  have hm_min : ∀ j < m, x.1 ∉ Ioo (σ j) (σ j + 1) := fun j hj => Nat.find_min (hcov x.1 hx) hj
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hN with hlt | rfl
    · have hnot : x ∉ {y : Coord | y.1 ∈ Ioo (σ N) (σ N + 1) ∧
          ∀ j < N, y.1 ∉ Ioo (σ j) (σ j + 1)} := fun h => h.2 m hlt hm_mem
      simp only [glueWindowProfAux, piecewise_eq_of_notMem _ _ _ hnot]
      exact ih hlt
    · have hin : x ∈ {y : Coord | y.1 ∈ Ioo (σ m) (σ m + 1) ∧
          ∀ j < m, y.1 ∉ Ioo (σ j) (σ j + 1)} := ⟨hm_mem, hm_min⟩
      simp only [glueWindowProfAux, piecewise_eq_of_mem _ _ _ hin]

lemma stronglyMeasurable_glueWindowProf {σ : ℕ → ℝ} (hσ_pos : ∀ m, 0 < σ m)
    (hcov : ∀ s : ℝ, 0 < s → ∃ m : ℕ, s ∈ Ioo (σ m) (σ m + 1))
    {F : ℕ → CProf} (hF : ∀ m, StronglyMeasurable (F m)) :
    StronglyMeasurable (glueWindowProf σ hcov F) := by
  have haux_sm : ∀ N : ℕ, StronglyMeasurable (glueWindowProfAux σ F N) := by
    intro N
    induction N with
    | zero => exact stronglyMeasurable_const
    | succ N ih =>
      have hM : MeasurableSet {x : Coord | x.1 ∈ Ioo (σ N) (σ N + 1) ∧
          ∀ j < N, x.1 ∉ Ioo (σ j) (σ j + 1)} := by
        have hM1 : MeasurableSet {x : Coord | x.1 ∈ Ioo (σ N) (σ N + 1)} :=
          measurableSet_Ioo.preimage measurable_fst
        have hM2 : MeasurableSet {x : Coord | ∀ j < N, x.1 ∉ Ioo (σ j) (σ j + 1)} := by
          have hfin : {x : Coord | ∀ j < N, x.1 ∉ Ioo (σ j) (σ j + 1)} =
              ⋂ j ∈ Finset.range N, (Prod.fst ⁻¹' Ioo (σ j) (σ j + 1))ᶜ := by
            ext x; simp
          rw [hfin]
          exact Finset.measurableSet_biInter _ fun j _ =>
            (measurableSet_Ioo.preimage measurable_fst).compl
        exact hM1.inter hM2
      exact (hF N).piecewise hM ih
  refine stronglyMeasurable_of_tendsto atTop haux_sm (tendsto_pi_nhds.2 fun x => ?_)
  by_cases hx : 0 < x.1
  · simp only [glueWindowProf, hx, ↓reduceDIte]
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.find (hcov x.1 hx) + 1) fun N hN => ?_
    exact glueWindowProfAux_eq_of_find hx N hN
  · simp only [glueWindowProf, hx, ↓reduceDIte]
    have h0 : ∀ N : ℕ, glueWindowProfAux σ F N x = 0 := by
      intro N
      induction N with
      | zero => rfl
      | succ N ih =>
        have hnot : x ∉ {y : Coord | y.1 ∈ Ioo (σ N) (σ N + 1) ∧
            ∀ j < N, y.1 ∉ Ioo (σ j) (σ j + 1)} :=
          fun h => hx (lt_trans (hσ_pos N) h.1.1)
        simp only [glueWindowProfAux, piecewise_eq_of_notMem _ _ _ hnot, ih]
    exact tendsto_atTop_of_eventually_const (i₀ := 0) fun N _ => h0 N

lemma glueWindowProf_ae_eq_on_Ioo {σ : ℕ → ℝ}
    (hcov : ∀ s : ℝ, 0 < s → ∃ m : ℕ, s ∈ Ioo (σ m) (σ m + 1))
    {F : ℕ → CProf} {τ : ℝ} (hτ : 0 ≤ τ) {G : CProf}
    (hcompat : ∀ m : ℕ,
      F m =ᵐ[volume.restrict (Ioo (max (σ m) τ) (min (σ m + 1) (τ + 1)) ×ˢ univ)] G) :
    glueWindowProf σ hcov F =ᵐ[volume.restrict (Ioo τ (τ + 1) ×ˢ univ)] G := by
  have hm_ae : ∀ m : ℕ, ∀ᵐ x : Coord,
      x.1 ∈ Ioo (max (σ m) τ) (min (σ m + 1) (τ + 1)) → F m x = G x := by
    intro m
    have h := hcompat m
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)] at h
    filter_upwards [h] with x hx hx_mem
    exact hx ⟨hx_mem, trivial⟩
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)]
  filter_upwards [ae_all_iff.2 hm_ae] with x hx hx_mem
  have hx_pos : 0 < x.1 := lt_of_le_of_lt hτ hx_mem.1.1
  set m := Nat.find (hcov x.1 hx_pos)
  have hm_in : x.1 ∈ Ioo (σ m) (σ m + 1) := Nat.find_spec (hcov x.1 hx_pos)
  simp only [glueWindowProf, hx_pos, ↓reduceDIte]
  exact hx m ⟨max_lt hm_in.1 hx_mem.1.1, lt_min hm_in.2 hx_mem.1.2⟩

end UnforcedLeray.Short.IIb.F8Duh
