import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.WindowUpper

/-!
# Part II-b, task `PartII-b:T13/1/4/2/5` (`ChmCommBound`): commutator bound

Source `the November 2 reference manuscript` lines 1933-1935 and 1377-1424.
The commutator `ν(2 ζ' ∂_q w + ζ'' w)` vanishes off the two cells `[-c, 0]` and `[N c, (N+1) c]`
(`ζ = 1` on `[0, N c]`, `ζ = 0` outside `[-c, (N+1) c]`, so `ζ'` and `ζ''` vanish on the open
sets `(0, N c)`, `(-∞, -c)`, `((N+1) c, ∞)`). Splitting the two cells with indicators, each piece is
a bounded profile in `q` supported in one cell times `∂_q w` or `w`, and `chmWindowUpper` (`m = 1`)
bounds each piece by `b c^{1/r} ‖·‖_{L^r(cylMeas c)}`, with constants independent of `N` and `ζ`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- A function that is eventually constant near `t` has vanishing first and second derivatives
at `t`. -/
lemma chm_deriv_eventually_const (f : ℝ → ℝ) (t c0 : ℝ) (h : f =ᶠ[𝓝 t] fun _ => c0) :
    deriv f t = 0 ∧ deriv (deriv f) t = 0 := by
  refine ⟨?_, ?_⟩
  · rw [h.deriv_eq, deriv_const]
  · rw [h.deriv.deriv_eq, deriv_const', deriv_const]

/-- Indicators of two disjoint sets add up to `f` when `f` vanishes off their union. -/
lemma chm_indicator_split (W1 W2 : Set ℝ) (hd : Disjoint W1 W2) (f : ℝ → ℝ)
    (hf : ∀ t, t ∉ W1 → t ∉ W2 → f t = 0) (t : ℝ) :
    W1.indicator f t + W2.indicator f t = f t := by
  by_cases h1 : t ∈ W1
  · have h2 : t ∉ W2 := Set.disjoint_left.1 hd h1
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
  · by_cases h2 : t ∈ W2
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
      exact (hf t h1 h2).symm

/-- A bounded-by-`B` function has bounded indicator. -/
lemma chm_abs_indicator_le (W : Set ℝ) (f : ℝ → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t, |f t| ≤ B) (t : ℝ) : |W.indicator f t| ≤ B := by
  by_cases h : t ∈ W
  · rw [Set.indicator_of_mem h]; exact hB t
  · rw [Set.indicator_of_notMem h, abs_zero]; exact hB0

/-- The cut-off derivatives vanish off the two cells `[-c, 0]` and `[N c, (N+1) c]`. -/
lemma chm_outside (K c : ℝ) (N : ℕ) (ζ : ℝ → ℝ) (hζ : IsChmCut K c N ζ) (t : ℝ)
    (h1 : t ∉ Icc (-c) 0) (h2 : t ∉ Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c)) :
    deriv ζ t = 0 ∧ deriv (deriv ζ) t = 0 := by
  obtain ⟨-, -, hζ1, hζ0, -, -⟩ := hζ
  simp only [Set.mem_Icc, not_and_or, not_le] at h1 h2
  rcases h1 with h1 | h1
  · exact chm_deriv_eventually_const ζ t 0 (by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact hζ0 s (Or.inl hs))
  · rcases h2 with h2 | h2
    · exact chm_deriv_eventually_const ζ t 1 (by
        filter_upwards [Ioo_mem_nhds h1 h2] with s hs
        exact hζ1 s ⟨hs.1.le, hs.2.le⟩)
    · exact chm_deriv_eventually_const ζ t 0 (by
        filter_upwards [Ioi_mem_nhds h2] with s hs
        exact hζ0 s (Or.inr hs))

/-- The one-cell window bound, from `chmWindowUpper` with `m = 1`. -/
lemma chm_win (r : ℝ) (hr : 1 < r) (c : ℝ) (hc : 0 < c) (g : Coord → ℂ)
    (hg : AEStronglyMeasurable g volume) (hper : QPeriodicS c g) (h : ℝ → ℝ) (hh : Measurable h)
    (b a : ℝ) (hb : ∀ t, |h t| ≤ b) (hs : ∀ t, (t < a ∨ a + c < t) → h t = 0) :
    eLpNorm (fun x : Coord => (h x.2.1 : ℂ) * g x) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (b * c ^ (1 / r)) * cylNorm c r g := by
  have := chmWindowUpper r hr c hc g hg hper h b a 1 hh hb
    (fun t ht => hs t (by simpa using ht))
  simpa using this

lemma chm_meas_term (h : ℝ → ℝ) (hh : Measurable h) (g : Coord → ℂ) (hg : Measurable g) :
    Measurable (fun x : Coord => (h x.2.1 : ℂ) * g x) :=
  (Complex.measurable_ofReal.comp (hh.comp (measurable_fst.comp measurable_snd))).mul hg

theorem chmCommBound : UnforcedLeray.Short.IIb.ChmCommBound := by
  intro r hr c ν K hc hν w hw
  have hwm : AEStronglyMeasurable w volume := hw.smooth.continuous.aestronglyMeasurable
  have hwmeas : Measurable w := hw.smooth.continuous.measurable
  have hwp : QPeriodicS c w := Filter.Eventually.of_forall hw.periodic
  have hdp : QPeriodicS c (cdv 1 w) :=
    Filter.Eventually.of_forall (chm_cdv_periodic c w hw.periodic 1)
  have hdmeas : Measurable (cdv 1 w) := chm_measurable_cdv 1 w
  have hdm : AEStronglyMeasurable (cdv 1 w) volume := hdmeas.aestronglyMeasurable
  have hX1 : cylNorm c r (cdv 1 w) < ⊤ := hw.mem1 1
  have hX0 : cylNorm c r w < ⊤ := hw.mem0
  obtain ⟨A1, hA1⟩ : ∃ A : ℝ≥0∞, A = ENNReal.ofReal (2 * ν * (K / c) * c ^ (1 / r)) :=
    ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A : ℝ≥0∞, A = ENNReal.ofReal (ν * (K / c ^ 2) * c ^ (1 / r)) :=
    ⟨_, rfl⟩
  have hA1t : A1 < ⊤ := by rw [hA1]; exact ENNReal.ofReal_lt_top
  have hA0t : A0 < ⊤ := by rw [hA0]; exact ENNReal.ofReal_lt_top
  refine ⟨A1 * cylNorm c r (cdv 1 w) + A1 * cylNorm c r (cdv 1 w) +
    (A0 * cylNorm c r w + A0 * cylNorm c r w), ?_, fun N hN ζ hζ => ?_⟩
  · exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hA1t hX1,
      ENNReal.mul_lt_top hA1t hX1⟩, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hA0t hX0,
      ENNReal.mul_lt_top hA0t hX0⟩⟩
  -- geometry of the two cells
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNc : 0 < (N : ℝ) * c := mul_pos (by linarith) hc
  have hd : Disjoint (Icc (-c) 0) (Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c)) := by
    refine Set.disjoint_left.2 ?_
    intro t ht1 ht2
    simp only [Set.mem_Icc] at ht1 ht2
    linarith [ht1.2, ht2.1]
  obtain ⟨hζs, hζ01, hζ1, hζ0, hζd1, hζd2⟩ := id hζ
  have hB1 : 0 ≤ K / c := (abs_nonneg _).trans (hζd1 0)
  have hB2 : 0 ≤ K / c ^ 2 := (abs_nonneg _).trans (hζd2 0)
  -- the four bounded profiles, obtained from the splitting of `ζ'`, `ζ''`
  obtain ⟨h1, hh1⟩ : ∃ h : ℝ → ℝ, ∀ t, h t = 2 * ν * (Icc (-c) 0).indicator (deriv ζ) t :=
    ⟨_, fun t => rfl⟩
  obtain ⟨h2, hh2⟩ : ∃ h : ℝ → ℝ, ∀ t,
      h t = 2 * ν * (Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c)).indicator (deriv ζ) t :=
    ⟨_, fun t => rfl⟩
  obtain ⟨h3, hh3⟩ : ∃ h : ℝ → ℝ, ∀ t,
      h t = ν * (Icc (-c) 0).indicator (deriv (deriv ζ)) t := ⟨_, fun t => rfl⟩
  obtain ⟨h4, hh4⟩ : ∃ h : ℝ → ℝ, ∀ t,
      h t = ν * (Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c)).indicator (deriv (deriv ζ)) t :=
    ⟨_, fun t => rfl⟩
  have hsa : ∀ t, h1 t + h2 t = 2 * ν * deriv ζ t := by
    intro t
    rw [hh1, hh2, ← mul_add,
      chm_indicator_split _ _ hd (deriv ζ)
        (fun s a b => (chm_outside K c N ζ hζ s a b).1) t]
  have hsb : ∀ t, h3 t + h4 t = ν * deriv (deriv ζ) t := by
    intro t
    rw [hh3, hh4, ← mul_add,
      chm_indicator_split _ _ hd (deriv (deriv ζ))
        (fun s a b => (chm_outside K c N ζ hζ s a b).2) t]
  -- measurability
  have hmd : Measurable (deriv ζ) := measurable_deriv ζ
  have hmdd : Measurable (deriv (deriv ζ)) := measurable_deriv (deriv ζ)
  have hm1 : Measurable h1 := by
    have e : h1 = fun t => 2 * ν * (Icc (-c) 0).indicator (deriv ζ) t := funext hh1
    rw [e]; exact (hmd.indicator measurableSet_Icc).const_mul _
  have hm2 : Measurable h2 := by
    have e : h2 = fun t => 2 * ν *
        (Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c)).indicator (deriv ζ) t := funext hh2
    rw [e]; exact (hmd.indicator measurableSet_Icc).const_mul _
  have hm3 : Measurable h3 := by
    have e : h3 = fun t => ν * (Icc (-c) 0).indicator (deriv (deriv ζ)) t := funext hh3
    rw [e]; exact (hmdd.indicator measurableSet_Icc).const_mul _
  have hm4 : Measurable h4 := by
    have e : h4 = fun t => ν * (Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c)).indicator
        (deriv (deriv ζ)) t := funext hh4
    rw [e]; exact (hmdd.indicator measurableSet_Icc).const_mul _
  -- bounds
  have hb1 : ∀ t, |h1 t| ≤ 2 * ν * (K / c) := by
    intro t
    rw [hh1, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * ν)]
    exact mul_le_mul_of_nonneg_left
      (chm_abs_indicator_le (Icc (-c) 0) (deriv ζ) (K / c) hB1 hζd1 t) (by linarith)
  have hb2 : ∀ t, |h2 t| ≤ 2 * ν * (K / c) := by
    intro t
    rw [hh2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * ν)]
    exact mul_le_mul_of_nonneg_left
      (chm_abs_indicator_le _ (deriv ζ) (K / c) hB1 hζd1 t) (by linarith)
  have hb3 : ∀ t, |h3 t| ≤ ν * (K / c ^ 2) := by
    intro t
    rw [hh3, abs_mul, abs_of_pos hν]
    exact mul_le_mul_of_nonneg_left
      (chm_abs_indicator_le (Icc (-c) 0) (deriv (deriv ζ)) (K / c ^ 2) hB2 hζd2 t) hν.le
  have hb4 : ∀ t, |h4 t| ≤ ν * (K / c ^ 2) := by
    intro t
    rw [hh4, abs_mul, abs_of_pos hν]
    exact mul_le_mul_of_nonneg_left
      (chm_abs_indicator_le _ (deriv (deriv ζ)) (K / c ^ 2) hB2 hζd2 t) hν.le
  -- supports
  have hs1 : ∀ t, (t < -c ∨ -c + c < t) → h1 t = 0 := by
    intro t ht
    have hnot : t ∉ Icc (-c) 0 := by
      intro hm
      rw [Set.mem_Icc] at hm
      rcases ht with h | h <;> linarith [hm.1, hm.2]
    rw [hh1, Set.indicator_of_notMem hnot, mul_zero]
  have hs2 : ∀ t, (t < (N : ℝ) * c ∨ (N : ℝ) * c + c < t) → h2 t = 0 := by
    intro t ht
    have e : ((N : ℝ) + 1) * c = (N : ℝ) * c + c := by ring
    have hnot : t ∉ Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c) := by
      intro hm
      rw [Set.mem_Icc] at hm
      rcases ht with h | h <;> linarith [hm.1, hm.2, e]
    rw [hh2, Set.indicator_of_notMem hnot, mul_zero]
  have hs3 : ∀ t, (t < -c ∨ -c + c < t) → h3 t = 0 := by
    intro t ht
    have hnot : t ∉ Icc (-c) 0 := by
      intro hm
      rw [Set.mem_Icc] at hm
      rcases ht with h | h <;> linarith [hm.1, hm.2]
    rw [hh3, Set.indicator_of_notMem hnot, mul_zero]
  have hs4 : ∀ t, (t < (N : ℝ) * c ∨ (N : ℝ) * c + c < t) → h4 t = 0 := by
    intro t ht
    have e : ((N : ℝ) + 1) * c = (N : ℝ) * c + c := by ring
    have hnot : t ∉ Icc ((N : ℝ) * c) (((N : ℝ) + 1) * c) := by
      intro hm
      rw [Set.mem_Icc] at hm
      rcases ht with h | h <;> linarith [hm.1, hm.2, e]
    rw [hh4, Set.indicator_of_notMem hnot, mul_zero]
  -- the four window bounds
  have e1 := chm_win r hr c hc (cdv 1 w) hdm hdp h1 hm1 (2 * ν * (K / c)) (-c) hb1 hs1
  have e2 := chm_win r hr c hc (cdv 1 w) hdm hdp h2 hm2 (2 * ν * (K / c)) ((N : ℝ) * c) hb2 hs2
  have e3 := chm_win r hr c hc w hwm hwp h3 hm3 (ν * (K / c ^ 2)) (-c) hb3 hs3
  have e4 := chm_win r hr c hc w hwm hwp h4 hm4 (ν * (K / c ^ 2)) ((N : ℝ) * c) hb4 hs4
  rw [← hA1] at e1 e2
  rw [← hA0] at e3 e4
  -- pointwise decomposition of the commutator
  have hdec : ∀ x : Coord, chmComm ν ζ w x =
      (h1 x.2.1 : ℂ) * cdv 1 w x + (h2 x.2.1 : ℂ) * cdv 1 w x +
        ((h3 x.2.1 : ℂ) * w x + (h4 x.2.1 : ℂ) * w x) := by
    intro x
    have ea := congrArg (fun s : ℝ => (s : ℂ)) (hsa x.2.1)
    have eb := congrArg (fun s : ℝ => (s : ℂ)) (hsb x.2.1)
    push_cast at ea eb
    unfold chmComm
    linear_combination (-(cdv 1 w x)) * ea + (-(w x)) * eb
  have hfun : chmComm ν ζ w = ((fun x : Coord => (h1 x.2.1 : ℂ) * cdv 1 w x) +
      (fun x : Coord => (h2 x.2.1 : ℂ) * cdv 1 w x)) +
      ((fun x : Coord => (h3 x.2.1 : ℂ) * w x) + (fun x : Coord => (h4 x.2.1 : ℂ) * w x)) := by
    funext x
    simp only [Pi.add_apply]
    exact hdec x
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have mF1 := chm_meas_term h1 hm1 (cdv 1 w) hdmeas
  have mF2 := chm_meas_term h2 hm2 (cdv 1 w) hdmeas
  have mF3 := chm_meas_term h3 hm3 w hwmeas
  have mF4 := chm_meas_term h4 hm4 w hwmeas
  have s12 := eLpNorm_add_le (μ := volume) (p := ENNReal.ofReal r)
    (f := fun x : Coord => (h1 x.2.1 : ℂ) * cdv 1 w x)
    (g := fun x : Coord => (h2 x.2.1 : ℂ) * cdv 1 w x)
    mF1.aestronglyMeasurable mF2.aestronglyMeasurable hp
  have s34 := eLpNorm_add_le (μ := volume) (p := ENNReal.ofReal r)
    (f := fun x : Coord => (h3 x.2.1 : ℂ) * w x)
    (g := fun x : Coord => (h4 x.2.1 : ℂ) * w x)
    mF3.aestronglyMeasurable mF4.aestronglyMeasurable hp
  have s := eLpNorm_add_le (μ := volume) (p := ENNReal.ofReal r)
    (f := (fun x : Coord => (h1 x.2.1 : ℂ) * cdv 1 w x) +
      (fun x : Coord => (h2 x.2.1 : ℂ) * cdv 1 w x))
    (g := (fun x : Coord => (h3 x.2.1 : ℂ) * w x) + (fun x : Coord => (h4 x.2.1 : ℂ) * w x))
    (mF1.aestronglyMeasurable.add mF2.aestronglyMeasurable)
    (mF3.aestronglyMeasurable.add mF4.aestronglyMeasurable) hp
  rw [hfun]
  refine le_trans s ?_
  exact le_trans (add_le_add s12 s34) (add_le_add (add_le_add e1 e2) (add_le_add e3 e4))

end UnforcedLeray.Short.IIb
