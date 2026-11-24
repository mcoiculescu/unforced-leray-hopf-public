import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.LeibCellJet

/-!
# `PartIII-a:T21/2/7/2/1/1/6/10`: products with a smooth coefficient family preserve `C(I; H^infty)`

Source of record: `the November 2 reference manuscript` (SP), line 3060 and
270-288. The pointwise jets are `leibCellJet`; the continuity in `r` is the telescoping identity
`b' g' - b g = (b' - b) g' + b (g' - g)` applied to every Leibniz term, with the finite sum handled
by induction on the word splittings.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CMAux

/-- A bounded complex coefficient multiplies the `L²` norm by at most its bound. -/
theorem coeff_bound (μ : Measure (ℝ × ℝ)) (b : ℝ × ℝ → ℂ) {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hb : ∀ x, ‖b x‖ ≤ B0) (g : ℝ × ℝ → ℂ) :
    eLpNorm (fun x => b x * g x) 2 μ ≤ ENNReal.ofReal B0 * eLpNorm g 2 μ := by
  calc eLpNorm (fun x => b x * g x) 2 μ ≤ eLpNorm (fun x => (B0 : ℂ) * g x) 2 μ := by
        refine eLpNorm_mono fun x => ?_
        show ‖b x * g x‖ ≤ ‖(B0 : ℂ) * g x‖
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hB0]
        exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = ‖(B0 : ℂ)‖ₑ * eLpNorm g 2 μ := by
        rw [← eLpNorm_const_smul (B0 : ℂ) g 2 μ]
        rfl
    _ = ENNReal.ofReal B0 * eLpNorm g 2 μ := by
        rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hB0]

/-- A small multiple of a finite quantity is small. -/
theorem enn_small {K : ℝ≥0∞} (hK : K ≠ ⊤) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε * K < δ := by
  have hc : Tendsto (fun ε : ℝ => ENNReal.ofReal ε * K) (𝓝 0) (𝓝 (ENNReal.ofReal 0 * K)) :=
    ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hK)
  rw [ENNReal.ofReal_zero, zero_mul] at hc
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ENNReal.ofReal ε * K < δ := hc.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal ε * K < δ := nhdsWithin_le_nhds h1
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε2, hε1⟩ := (h2.and h3).exists
  exact ⟨ε, hε1, hε2⟩

/-- Pointwise difference of two finite sums is the sum of the termwise differences. -/
theorem sum_map_sub {ι : Type} (L : List ι) (f g : ι → ℂ) :
    (L.map f).sum - (L.map g).sum = (L.map fun p => f p - g p).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

/-- A finite sum of a.e.-strongly measurable functions is a.e.-strongly measurable. -/
theorem list_sum_aesm {ι : Type} {μ : Measure (ℝ × ℝ)} (L : List ι) (G : ι → ℝ × ℝ → ℂ)
    (h : ∀ p ∈ L, AEStronglyMeasurable (G p) μ) :
    AEStronglyMeasurable (fun x => (L.map fun p => G p x).sum) μ := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact aestronglyMeasurable_const
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h p (by simp)).add (ih fun q hq => h q (by simp [hq]))

/-- Finite sums of functions tending to `0` in `L²` tend to `0`. -/
theorem tendsto_list_sum {ι : Type} {μ : Measure (ℝ × ℝ)} {l : Filter ℝ} (L : List ι)
    (G : ι → ℝ → ℝ × ℝ → ℂ)
    (hm : ∀ p ∈ L, ∀ᶠ r' in l, AEStronglyMeasurable (G p r') μ)
    (h : ∀ p ∈ L, Tendsto (fun r' => eLpNorm (G p r') 2 μ) l (𝓝 0)) :
    Tendsto (fun r' => eLpNorm (fun x => (L.map fun p => G p r' x).sum) 2 μ) l (𝓝 0) ∧
      ∀ᶠ r' in l, AEStronglyMeasurable (fun x => (L.map fun p => G p r' x).sum) μ := by
  induction L with
  | nil =>
    refine ⟨?_, Eventually.of_forall fun _ => ?_⟩
    · have e : (fun r' => eLpNorm (fun x => (([] : List ι).map fun p => G p r' x).sum) 2 μ) =
          fun _ => 0 := by
        funext r'
        simp
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
      exact eLpNorm_add_le h1 h2 (by norm_num)
    · filter_upwards [hmp, ih2] with r' h1 h2
      simp only [List.map_cons, List.sum_cons]
      exact h1.add h2

end CMAux

open CMAux

/-- **One Leibniz term**: if `b_{r'} → b_r` uniformly with `b_r` bounded, `g_{r'} → g_r` in
`L²`, and `g` is `L²` on `I`, then `b_{r'} g_{r'} - b_r g_r → 0` in `L²` as `r' → r` in `I`. -/
theorem term_tendsto {μ : Measure (ℝ × ℝ)} {I : Set ℝ} {r : ℝ} (hr : r ∈ I)
    (q : ℝ → ℝ × ℝ → ℝ) (g : ℝ → ℝ × ℝ → ℂ)
    (hqc : ∀ r' ∈ I, Continuous (q r'))
    (hqd : ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[I] r, ∀ x, |q r' x - q r x| ≤ ε)
    (hqb : ∃ C : ℝ, ∀ x, |q r x| ≤ C)
    (hgm : ∀ r' ∈ I, MemLp (g r') 2 μ)
    (hgE : Tendsto (fun r' => eLpNorm (g r' - g r) 2 μ) (𝓝[I] r) (𝓝 0)) :
    (∀ᶠ r' in 𝓝[I] r, AEStronglyMeasurable
        (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x) μ) ∧
      Tendsto (fun r' => eLpNorm (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x)
        2 μ) (𝓝[I] r) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hqb
  set l := 𝓝[I] r with hl
  have hIev : ∀ᶠ r' in l, r' ∈ I := self_mem_nhdsWithin
  have hgmeas : ∀ᶠ r' in l, AEStronglyMeasurable (g r') μ :=
    hIev.mono fun r' h' => (hgm r' h').aestronglyMeasurable
  have hgr : MemLp (g r) 2 μ := hgm r hr
  have hmeas : ∀ᶠ r' in l, AEStronglyMeasurable
      (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x) μ := by
    filter_upwards [hIev, hgmeas] with r' h' hg'
    exact ((Complex.continuous_ofReal.comp (hqc r' h')).aestronglyMeasurable.mul hg').sub
      ((Complex.continuous_ofReal.comp (hqc r hr)).aestronglyMeasurable.mul
        hgr.aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  -- uniform bound of the difference quotient `g r'` near `r`
  have hEb : ∀ᶠ r' in l, eLpNorm (g r') 2 μ ≤ eLpNorm (g r) 2 μ + 1 := by
    filter_upwards [hgE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1)), hgmeas]
      with r' h1 h2
    have hsub : AEStronglyMeasurable (g r' - g r) μ := h2.sub hgr.aestronglyMeasurable
    have h3 := eLpNorm_add_le hsub hgr.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simp only [sub_add_cancel] at h3
    exact h3.trans ((add_le_add h1.le le_rfl).trans (le_of_eq (add_comm _ _)))
  have hK : eLpNorm (g r) 2 μ + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hgr.eLpNorm_lt_top.ne, ENNReal.one_ne_top⟩
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨ε, hε, hεK⟩ := enn_small hK hδ2
  have hu : Tendsto (fun r' => ENNReal.ofReal (max C 0) * eLpNorm (g r' - g r) 2 μ) l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (max C 0)) hgE
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at this
    exact this
  have hsmall := hu.eventually (gt_mem_nhds hδ2)
  have hqε := hqd ε hε
  filter_upwards [hEb, hqε, hsmall, hIev] with r' hE hd1 hsm hr'I
  have hfun : (fun x => ((q r' x : ℝ) : ℂ) * g r' x - ((q r x : ℝ) : ℂ) * g r x) =
      (fun x => (((q r' x - q r x : ℝ)) : ℂ) * g r' x) +
        (fun x => ((q r x : ℝ) : ℂ) * (g r' x - g r x)) := by
    funext x
    simp only [Pi.add_apply]
    push_cast
    ring
  have hm1 : AEStronglyMeasurable (fun x => (((q r' x - q r x : ℝ)) : ℂ) * g r' x) μ :=
    ((Complex.continuous_ofReal.comp ((hqc r' hr'I).sub (hqc r hr))).aestronglyMeasurable).mul
      (hgm r' hr'I).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => ((q r x : ℝ) : ℂ) * (g r' x - g r x)) μ :=
    (Complex.continuous_ofReal.comp (hqc r hr)).aestronglyMeasurable.mul
      ((hgm r' hr'I).aestronglyMeasurable.sub hgr.aestronglyMeasurable)
  rw [hfun]
  refine (eLpNorm_add_le hm1 hm2 (by norm_num)).trans ?_
  have b1 := CMAux.coeff_bound μ (fun x => (((q r' x - q r x : ℝ)) : ℂ)) hε.le
    (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hd1 x) (g r')
  have b2 := CMAux.coeff_bound μ (fun x => ((q r x : ℝ) : ℂ)) (le_max_right C 0)
    (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hC x).trans (le_max_left _ _))
    (fun x => g r' x - g r x)
  have b1' : ENNReal.ofReal ε * eLpNorm (g r') 2 μ ≤
      ENNReal.ofReal ε * (eLpNorm (g r) 2 μ + 1) := by gcongr
  exact (add_le_add (b1.trans b1') b2).trans
    ((add_le_add hεK.le hsm.le).trans (ENNReal.add_halves δ).le)

/-- **(10) Products with a smooth coefficient family preserve `C(I; H^∞_{-m,c})`** (SP 3060,
270-288): the jets are `leibCellJet`; continuity in `r` by the termwise telescoping of
`leib`. -/
theorem adjHkAllCoeffMul : AdjHkAllCoeffMul := by
  intro c m I a f D hc hA hf
  refine ⟨fun r hr k => ?_, fun w r hr => ?_⟩
  · exact leibCellJet c m (a r) (f r) (D r) hc (hA.1 r hr).1 (hA.1 r hr).2
      (fun w' => (hA.2 w' r hr).1) (fun k' => hf.1 r hr k') k
  · have hsplit : ∀ r' : ℝ, leib (a r') (D r') w - leib (a r) (D r) w =
        fun x => ((wordSplits w).map fun p =>
          (((rSpatial p.1 (a r') x : ℝ) : ℂ) * D r' p.2 x -
            ((rSpatial p.1 (a r) x : ℝ) : ℂ) * D r p.2 x)).sum := by
      intro r'
      funext x
      simp only [Pi.sub_apply]
      unfold leib
      exact CMAux.sum_map_sub _ _ _
    have hterm : ∀ p ∈ wordSplits w, (∀ᶠ r' in 𝓝[I] r, AEStronglyMeasurable
          (fun x => (((rSpatial p.1 (a r') x : ℝ) : ℂ) * D r' p.2 x -
            ((rSpatial p.1 (a r) x : ℝ) : ℂ) * D r p.2 x)) (B0579.cellMeasure c (-m))) ∧
        Tendsto (fun r' => eLpNorm (fun x => (((rSpatial p.1 (a r') x : ℝ) : ℂ) * D r' p.2 x -
            ((rSpatial p.1 (a r) x : ℝ) : ℂ) * D r p.2 x)) 2 (B0579.cellMeasure c (-m)))
          (𝓝[I] r) (𝓝 0) := by
      intro p _
      refine term_tendsto (μ := B0579.cellMeasure c (-m)) hr (fun r' x => rSpatial p.1 (a r') x)
        (fun r' => D r' p.2)
        (fun r' hr' => ?_) (fun ε hε => (hA.2 p.1 r hr).2 ε hε) ?_
        (fun r' hr' => (hf.1 r' hr' p.2.length).memX p.2 le_rfl)
        (hf.2 p.2 r hr)
      · exact ((ll_rs_smooth_per (hA.1 r' hr').1 (hA.1 r' hr').2 p.1).1.continuous)
      · exact (hA.2 p.1 r hr).1
    have hall := tendsto_list_sum (μ := B0579.cellMeasure c (-m)) (wordSplits w)
      (fun p r' x => (((rSpatial p.1 (a r') x : ℝ) : ℂ) * D r' p.2 x -
            ((rSpatial p.1 (a r) x : ℝ) : ℂ) * D r p.2 x))
      (fun p hp => (hterm p hp).1) (fun p hp => (hterm p hp).2)
    show Tendsto (fun r' => eLpNorm (leib (a r') (D r') w - leib (a r) (D r) w) 2
      (B0579.cellMeasure c (-m))) (𝓝[I] r) (𝓝 0)
    exact (tendsto_congr fun r' => by rw [hsplit r']).2 hall.1

end UnforcedLeray.Short.IIIa
