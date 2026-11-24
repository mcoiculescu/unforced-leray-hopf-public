import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.LeibCellJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerAdjXBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerAdjSubAE
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerAdjWeakDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerAdjPeriodic
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.WeightedMulL12

/-!
# `PartIII-a:T21/2/7/2/1/1/6/19`: the kernel term preserves `C(I; H^infty_{-m,c})`

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3058
(the localized source `K_c^T(G f)`, bounded from `L^1 ∩ L^2` into `X_{-m,c}`) and 2866-2870
(the weighted coefficient jets `∂_r^i∇E`). The cell jets are `leibCellJet` and `KerAdjWeakDeriv`;
the continuity in `r` is the telescoping of the Leibniz fields, each term bounded in `L^1 + L^2`
of the cell by `WeightedMulL12`, and then `KerAdjSubAE` and `KerAdjXBound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace KMAux

/-- The `L¹ + L²` size of a field on the cell (the left side of `WeightedMulL12`). -/
def KS (c : ℝ) (F : ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  eLpNorm F 1 (volume.restrict (B0579.cell c)) + eLpNorm F 2 (volume.restrict (B0579.cell c))

/-- Subadditivity of `KS`. -/
theorem KS_add {c : ℝ} {F G : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (B0579.cell c)))
    (hG : AEStronglyMeasurable G (volume.restrict (B0579.cell c))) :
    KS c (F + G) ≤ KS c F + KS c G := by
  unfold KS
  have h1 := eLpNorm_add_le hF hG (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have h2 := eLpNorm_add_le hF hG (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- Pointwise difference of two finite sums is the sum of the termwise differences. -/
theorem sum_map_sub {ι : Type} (L : List ι) (f g : ι → ℂ) :
    (L.map f).sum - (L.map g).sum = (L.map fun p => f p - g p).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

/-- A finite sum of integrable functions is integrable. -/
theorem list_integrable {ι : Type} {s : Set (ℝ × ℝ)} (L : List ι) (F : ι → ℝ × ℝ → ℂ)
    (h : ∀ p ∈ L, IntegrableOn (F p) s) :
    IntegrableOn (fun x => (L.map fun p => F p x).sum) s := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact integrableOn_zero
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h p (by simp)).add (ih fun q hq => h q (by simp [hq]))

/-- Finite sums of functions with `KS` tending to `0` have `KS` tending to `0`. -/
theorem tendsto_list_KS {ι : Type} {c : ℝ} {l : Filter ℝ} (L : List ι) (G : ι → ℝ → ℝ × ℝ → ℂ)
    (hm : ∀ p ∈ L, ∀ᶠ r' in l, AEStronglyMeasurable (G p r') (volume.restrict (B0579.cell c)))
    (h : ∀ p ∈ L, Tendsto (fun r' => KS c (G p r')) l (𝓝 0)) :
    Tendsto (fun r' => KS c (fun x => (L.map fun p => G p r' x).sum)) l (𝓝 0) ∧
      ∀ᶠ r' in l, AEStronglyMeasurable (fun x => (L.map fun p => G p r' x).sum)
        (volume.restrict (B0579.cell c)) := by
  induction L with
  | nil =>
    refine ⟨?_, Eventually.of_forall fun _ => ?_⟩
    · have e : (fun r' => KS c (fun x => (([] : List ι).map fun p => G p r' x).sum)) =
          fun _ => 0 := by
        funext r'
        simp [KS]
      rw [e]
      exact tendsto_const_nhds
    · simp only [List.map_nil, List.sum_nil]
      exact aestronglyMeasurable_const
  | cons p L ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun q hq => hm q (by simp [hq])) (fun q hq => h q (by simp [hq]))
    have hmp := hm p (by simp)
    have hp := h p (by simp)
    refine ⟨?_, ?_⟩
    · have hsum := hp.add ih1
      rw [add_zero] at hsum
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [hmp, ih2] with r' h1 h2
      simp only [List.map_cons, List.sum_cons]
      exact KS_add h1 h2
    · filter_upwards [hmp, ih2] with r' h1 h2
      simp only [List.map_cons, List.sum_cons]
      exact h1.add h2

/-- `1 ≤ ⟨x₂⟩^{m+1}` for `m > 1`. -/
theorem ejWeight_one_le {m : ℝ} (hm : 1 < m) (x : ℝ × ℝ) : 1 ≤ ejWeight m x := by
  unfold ejWeight
  exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)

/-- A small multiple of a finite quantity is small. -/
theorem enn_small_KS {K : ℝ≥0∞} (hK : K ≠ ⊤) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε * K < δ := by
  have hc : Tendsto (fun ε : ℝ => ENNReal.ofReal ε * K) (𝓝 0) (𝓝 (ENNReal.ofReal 0 * K)) :=
    ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hK)
  rw [ENNReal.ofReal_zero, zero_mul] at hc
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ENNReal.ofReal ε * K < δ := hc.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal ε * K < δ := nhdsWithin_le_nhds h1
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε2, hε1⟩ := (h2.and h3).exists
  exact ⟨ε, hε1, hε2⟩

theorem term_tendsto_KS {c m : ℝ} {I : Set ℝ} {r : ℝ} (hc : 0 < c) (hW : WeightedMulL12)
    (hr : r ∈ I)
    (q : ℝ → ℝ × ℝ → ℝ) (g : ℝ → ℝ × ℝ → ℂ)
    (hqc : ∀ r' ∈ I, Continuous (q r'))
    (hqd : ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[I] r, ∀ x, ejWeight m x * |q r' x - q r x| ≤ ε)
    (hqb : ∃ C : ℝ, ∀ x, ejWeight m x * |q r x| ≤ C)
    (hgm : ∀ r' ∈ I, MemLp (g r') 2 (B0579.cellMeasure c (-m)))
    (hgE : Tendsto (fun r' => xNorm c (-m) (g r' - g r)) (𝓝[I] r) (𝓝 0)) :
    (∀ᶠ r' in 𝓝[I] r, AEStronglyMeasurable
        (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x)
        (volume.restrict (B0579.cell c))) ∧
      Tendsto (fun r' => KS c (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x))
        (𝓝[I] r) (𝓝 0) := by
  obtain ⟨K, hK0, hWM⟩ := hW c m hc
  obtain ⟨C, hC⟩ := hqb
  set l := 𝓝[I] r with hl
  have hIev : ∀ᶠ r' in l, r' ∈ I := self_mem_nhdsWithin
  have hgr : MemLp (g r) 2 (B0579.cellMeasure c (-m)) := hgm r hr
  have hsplit : ∀ r' : ℝ, (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x) =
      (fun x => ((q r' x - q r x : ℝ) : ℂ) * g r' x) +
        (fun x => ((q r x : ℝ) : ℂ) * (g r' x - g r x)) := by
    intro r'
    funext x
    simp only [Pi.add_apply]
    push_cast
    ring
  have hmeas : ∀ᶠ r' in l, AEStronglyMeasurable
      (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x)
      (volume.restrict (B0579.cell c)) := by
    filter_upwards [hIev, hqd 1 one_pos] with r' h' hd
    have h1 := hWM (fun x => q r' x - q r x) (g r') 1
      ((hqc r' h').sub (hqc r hr)).aestronglyMeasurable (hgm r' h') (fun x _ => hd x)
    have h2 := hWM (fun x => q r x) (fun x => g r' x - g r x) C
      (hqc r hr).aestronglyMeasurable ((hgm r' h').sub hgr) (fun x _ => hC x)
    rw [hsplit r']
    exact h1.2.1.aestronglyMeasurable.add h2.2.1.aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  have hEb : ∀ᶠ r' in l, eLpNorm (g r') 2 (B0579.cellMeasure c (-m)) ≤
      eLpNorm (g r) 2 (B0579.cellMeasure c (-m)) + 1 := by
    filter_upwards [hgE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1)), hIev]
      with r' h1 h'
    have hsub : AEStronglyMeasurable (g r' - g r) (B0579.cellMeasure c (-m)) :=
      ((hgm r' h').sub hgr).aestronglyMeasurable
    have h3 := eLpNorm_add_le hsub hgr.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simp only [sub_add_cancel] at h3
    exact h3.trans ((add_le_add h1.le le_rfl).trans (le_of_eq (add_comm _ _)))
  have hK : ENNReal.ofReal K * (eLpNorm (g r) 2 (B0579.cellMeasure c (-m)) + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨hgr.eLpNorm_lt_top.ne, ENNReal.one_ne_top⟩)
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨ε, hε, hεX⟩ := enn_small_KS hK hδ2
  have hu : Tendsto (fun r' => ENNReal.ofReal (K * C) *
      eLpNorm (g r' - g r) 2 (B0579.cellMeasure c (-m))) l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (K * C)) hgE
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at this
    exact this
  have hsmall := hu.eventually (gt_mem_nhds hδ2)
  filter_upwards [hEb, hqd ε hε, hsmall, hIev] with r' hE hd1 hsm h'
  have h1 := hWM (fun x => q r' x - q r x) (g r') ε
    ((hqc r' h').sub (hqc r hr)).aestronglyMeasurable (hgm r' h') (fun x _ => hd1 x)
  have h2 := hWM (fun x => q r x) (fun x => g r' x - g r x) C
    (hqc r hr).aestronglyMeasurable ((hgm r' h').sub hgr) (fun x _ => hC x)
  have h1' : KS c (fun x => ((q r' x - q r x : ℝ) : ℂ) * g r' x) ≤
      ENNReal.ofReal (K * ε) * eLpNorm (g r') 2 (B0579.cellMeasure c (-m)) := h1.2.2
  have h2' : KS c (fun x => ((q r x : ℝ) : ℂ) * (g r' x - g r x)) ≤
      ENNReal.ofReal (K * C) * eLpNorm (g r' - g r) 2 (B0579.cellMeasure c (-m)) := h2.2.2
  have e1 : ENNReal.ofReal (K * ε) * eLpNorm (g r') 2 (B0579.cellMeasure c (-m)) ≤
      ENNReal.ofReal ε * (ENNReal.ofReal K *
        (eLpNorm (g r) 2 (B0579.cellMeasure c (-m)) + 1)) := by
    rw [ENNReal.ofReal_mul hK0]
    calc ENNReal.ofReal K * ENNReal.ofReal ε * eLpNorm (g r') 2 (B0579.cellMeasure c (-m))
        ≤ ENNReal.ofReal K * ENNReal.ofReal ε *
            (eLpNorm (g r) 2 (B0579.cellMeasure c (-m)) + 1) := by gcongr
      _ = _ := by ring
  rw [hsplit r']
  refine (KS_add h1.2.1.aestronglyMeasurable h2.2.1.aestronglyMeasurable).trans
    ((add_le_add h1' h2').trans ?_)
  exact (add_le_add (e1.trans hεX.le) hsm.le).trans (ENNReal.add_halves δ).le

end KMAux

open KMAux

/-- **(19) The kernel term preserves `C(I; H^∞_{-m,c})`** (SP 3052-3058, `m > 1`). -/
theorem adjHkAllKerMul (m : ℝ) (hm : 1 < m) : AdjHkAllKerMul m := by
  intro c I G f D hc1 hG hf
  have hc : 0 < c := lt_of_lt_of_le one_pos hc1
  obtain ⟨C₀, hC₀, hX⟩ := kerAdjXBound m hm
  obtain ⟨K, hK0, hWM⟩ := weightedMulL12 c m hc
  -- the Leibniz terms are `L¹ ∩ L²` and `X_{-m,c}`-valued
  have lk_mem : ∀ r' ∈ I, ∀ (w' : List (Fin 2)) (l : Fin 2),
      IntegrableOn (leib (G r' l) (D r') w') (B0579.cell c) ∧
        MemLp (leib (G r' l) (D r') w') 2 (volume.restrict (B0579.cell c)) := by
    intro r' hr' w' l
    have hterm : ∀ p ∈ wordSplits w',
        IntegrableOn (fun x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x)
          (B0579.cell c) ∧
        MemLp (fun x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x) 2
          (volume.restrict (B0579.cell c)) := by
      intro p _
      obtain ⟨C, hC⟩ := (hG.2 p.1 l r' hr').1
      have hh := hWM (fun x => rSpatial p.1 (G r' l) x) (D r' p.2) C
        ((ll_rs_smooth_per (hG.1 r' hr' l).1 (hG.1 r' hr' l).2 p.1).1.continuous).aestronglyMeasurable
        ((hf.1 r' hr' p.2.length).memX p.2 le_rfl) (fun x _ => hC x)
      exact ⟨hh.1, hh.2.1⟩
    exact ⟨list_integrable (wordSplits w') (fun p x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) *
        D r' p.2 x) (fun p hp => (hterm p hp).1),
      ll_memLp_sum (wordSplits w') (fun p x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x)
        (fun p hp => (hterm p hp).2)⟩
  refine ⟨fun r hr k => ?_, fun w r hr => ?_⟩
  · -- the cell jets of the kernel term
    refine ⟨?_, ?_, ?_, ?_⟩
    · show kerAdj c (fun l => leib (G r l) (D r) []) = kerAdj c (fun l y => (G r l y : ℂ) * f r y)
      congr 1
      funext l y
      simp [leib, wordSplits, rSpatial, (hf.1 r hr k).base]
    · intro w' _ x
      exact kerAdjPeriodic c hc1 _ x
    · intro w' _
      exact (hX c hc1 (fun l => leib (G r l) (D r) w') (fun l => lk_mem r hr w' l)).1
    · intro j w' _
      refine kerAdjWeakDeriv c hc1 j (fun l => leib (G r l) (D r) w')
        (fun l => leib (G r l) (D r) (j :: w')) (fun l => ⟨(lk_mem r hr w' l).1,
          (lk_mem r hr (j :: w') l).1, ?_⟩)
      exact ((leibCellJet c m (G r l) (f r) (D r) hc (hG.1 r hr l).1 (hG.1 r hr l).2
        (fun w'' => by
          obtain ⟨C, hC⟩ := (hG.2 w'' l r hr).1
          exact ⟨C, fun x => (le_mul_of_one_le_left (abs_nonneg _)
            (ejWeight_one_le hm x)).trans (hC x)⟩)
        (fun k' => hf.1 r hr k') (w'.length + 1)).deriv j w' (by omega))
  · -- continuity of the kernel term
    show Tendsto (fun r' => xNorm c (-m)
      (kerAdj c (fun l => leib (G r' l) (D r') w) - kerAdj c (fun l => leib (G r l) (D r) w)))
      (𝓝[I] r) (𝓝 0)
    have hL : ∀ l : Fin 2, Tendsto (fun r' => KS c (fun y => (1 : ℂ) *
        leib (G r' l) (D r') w y + (-1 : ℂ) * leib (G r l) (D r) w y)) (𝓝[I] r) (𝓝 0) := by
      intro l
      have hterm : ∀ p ∈ wordSplits w,
          (∀ᶠ r' in 𝓝[I] r, AEStronglyMeasurable
            (fun x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x -
              ((rSpatial p.1 (G r l) x : ℝ) : ℂ) * D r p.2 x) (volume.restrict (B0579.cell c))) ∧
          Tendsto (fun r' => KS c (fun x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x -
              ((rSpatial p.1 (G r l) x : ℝ) : ℂ) * D r p.2 x)) (𝓝[I] r) (𝓝 0) := by
        intro p _
        exact term_tendsto_KS hc weightedMulL12 hr (fun r' x => rSpatial p.1 (G r' l) x) (fun r' => D r' p.2)
          (fun r' h' => (ll_rs_smooth_per (hG.1 r' h' l).1 (hG.1 r' h' l).2 p.1).1.continuous)
          (fun ε hε => (hG.2 p.1 l r hr).2 ε hε) (hG.2 p.1 l r hr).1
          (fun r' h' => (hf.1 r' h' p.2.length).memX p.2 le_rfl) (hf.2 p.2 r hr)
      have hall := tendsto_list_KS (c := c) (wordSplits w)
        (fun p r' x => ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x -
          ((rSpatial p.1 (G r l) x : ℝ) : ℂ) * D r p.2 x)
        (fun p hp => (hterm p hp).1) (fun p hp => (hterm p hp).2)
      have hH : ∀ r' : ℝ, (fun y => (1 : ℂ) * leib (G r' l) (D r') w y +
            (-1 : ℂ) * leib (G r l) (D r) w y) =
          fun x => ((wordSplits w).map fun p =>
            ((rSpatial p.1 (G r' l) x : ℝ) : ℂ) * D r' p.2 x -
              ((rSpatial p.1 (G r l) x : ℝ) : ℂ) * D r p.2 x).sum := by
        intro r'
        funext y
        simp only [leib, one_mul, neg_one_mul]
        rw [← sub_eq_add_neg]
        exact sum_map_sub _ _ _
      exact (tendsto_congr fun r' => congrArg (KS c) (hH r')).2 hall.1
    have hsum : Tendsto (fun r' => ∑ l : Fin 2, KS c (fun y => (1 : ℂ) *
        leib (G r' l) (D r') w y + (-1 : ℂ) * leib (G r l) (D r) w y)) (𝓝[I] r) (𝓝 0) := by
      have := tendsto_finset_sum Finset.univ (fun l (_ : l ∈ Finset.univ) => hL l)
      simpa only [Finset.sum_const_zero] using this
    have hΦ : Tendsto (fun r' => ENNReal.ofReal C₀ * ∑ l : Fin 2, KS c (fun y => (1 : ℂ) *
        leib (G r' l) (D r') w y + (-1 : ℂ) * leib (G r l) (D r) w y)) (𝓝[I] r) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C₀) hsum
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hΦ
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    have hmemH : ∀ l : Fin 2, IntegrableOn (fun y => (1 : ℂ) * leib (G r' l) (D r') w y +
          (-1 : ℂ) * leib (G r l) (D r) w y) (B0579.cell c) ∧
        MemLp (fun y => (1 : ℂ) * leib (G r' l) (D r') w y +
          (-1 : ℂ) * leib (G r l) (D r) w y) 2 (volume.restrict (B0579.cell c)) := fun l =>
      ⟨(Integrable.const_mul (lk_mem r' hr' w l).1 1).add
          (Integrable.const_mul (lk_mem r hr w l).1 (-1)),
        (MemLp.const_mul (lk_mem r' hr' w l).2 1).add (MemLp.const_mul (lk_mem r hr w l).2 (-1))⟩
    have hbound := (hX c hc1 (fun l y => (1 : ℂ) * leib (G r' l) (D r') w y +
      (-1 : ℂ) * leib (G r l) (D r) w y) hmemH).2
    have hAE := kerAdjSubAE c hc1 (fun l => leib (G r' l) (D r') w)
      (fun l => leib (G r l) (D r) w) (fun l => lk_mem r' hr' w l) (fun l => lk_mem r hr w l)
      1 (-1)
    have h1 : (kerAdj c (fun l => leib (G r' l) (D r') w) -
        kerAdj c (fun l => leib (G r l) (D r) w)) =ᵐ[B0579.cellMeasure c (-m)]
        (fun y => (1 : ℂ) * kerAdj c (fun l => leib (G r' l) (D r') w) y +
          (-1 : ℂ) * kerAdj c (fun l => leib (G r l) (D r) w) y) :=
      Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring
    have hAEc := h1.trans ((B0579.cellMeasure_ac c (-m)).ae_le hAE)
    have e : xNorm c (-m) (kerAdj c (fun l => leib (G r' l) (D r') w) -
        kerAdj c (fun l => leib (G r l) (D r) w)) =
        xNorm c (-m) (kerAdj c (fun l y => (1 : ℂ) * leib (G r' l) (D r') w y +
          (-1 : ℂ) * leib (G r l) (D r) w y)) :=
      eLpNorm_congr_ae hAEc
    exact (le_of_eq e).trans hbound

end UnforcedLeray.Short.IIIa
