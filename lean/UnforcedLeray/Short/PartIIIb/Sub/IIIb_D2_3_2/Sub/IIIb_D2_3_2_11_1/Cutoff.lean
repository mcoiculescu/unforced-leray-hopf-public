import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1

/-!
# Smooth cutoff exhaustion of `chartDom c` (`PartIII-b:IIIb-D2/3/2/11/1`, source 4284-4286, 2666-2700)

A product of three one-dimensional smooth bumps, built from `ContDiffBump`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- One-dimensional smooth bump: equal to `1` on `[a,b]`, vanishing off `[l,u]`, values in `[0,1]`. -/
theorem cutoff1d_exists (a b l u : ℝ) (h1 : l < a) (h2 : a < b) (h3 : b < u) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ Icc a b, f x = 1) ∧ (∀ x, x ∉ Icc l u → f x = 0) := by
  set d : ℝ := min (a - l) (u - b) with hd_def
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hda : d ≤ a - l := min_le_left _ _
  have hdb : d ≤ u - b := min_le_right _ _
  let F : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2, (b - a) / 2 + d, by linarith, by linarith⟩
  refine ⟨F, F.contDiff, fun x => ⟨F.nonneg, F.le_one⟩, ?_, ?_⟩
  · intro x hx
    apply F.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |x - (a + b) / 2| ≤ (b - a) / 2
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_le]
    constructor <;> linarith
  · intro x hx
    apply F.zero_of_le_dist
    show (b - a) / 2 + d ≤ dist x ((a + b) / 2)
    rw [Real.dist_eq]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl (by linarith))

theorem smoothCutoffExhaustion (c : ℝ) (hc : 0 < c) :
    ∃ ψ : ℕ → Chart → ℝ, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n)) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧ (∀ n, tsupport (ψ n) ⊆ chartDom c) ∧
      (∀ n x, 0 ≤ ψ n x ∧ ψ n x ≤ 1) ∧
      ∀ x ∈ chartDom c, Filter.Tendsto (fun n => ψ n x) Filter.atTop (nhds 1) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ n, e n = 1 / ((n : ℝ) + 2) :=
    ⟨fun n => 1 / ((n : ℝ) + 2), fun n => rfl⟩
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ n := fun n => Nat.cast_nonneg n
  have he_pos : ∀ n, 0 < e n := fun n => by rw [he]; positivity
  have he_le : ∀ n, e n ≤ 1 / 2 := fun n => by
    rw [he]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [hn0 n])
  have hE : Tendsto e atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      Tendsto.div_atTop (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) h2
    exact Tendsto.congr (fun n => (he n).symm) h3
  -- s-factor
  have hs : ∀ n : ℕ, ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ Icc (e n) ((n : ℝ) + 1), f x = 1) ∧
      (∀ x, x ∉ Icc (e n / 2) ((n : ℝ) + 1 + e n / 2) → f x = 0) := by
    intro n
    refine cutoff1d_exists _ _ _ _ ?_ ?_ ?_
    · linarith [he_pos n]
    · linarith [he_le n, hn0 n]
    · linarith [he_pos n]
  -- q-factor
  have hq : ∀ n : ℕ, ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ Icc (-(c / 2 * (1 - e n))) (c / 2 * (1 - e n)), f x = 1) ∧
      (∀ x, x ∉ Icc (-(c / 2 * (1 - e n / 2))) (c / 2 * (1 - e n / 2)) → f x = 0) := by
    intro n
    refine cutoff1d_exists _ _ _ _ ?_ ?_ ?_
    · nlinarith [mul_pos hc (he_pos n)]
    · have h1e : 0 < 1 - e n := by linarith [he_le n]
      nlinarith [mul_pos hc h1e]
    · nlinarith [mul_pos hc (he_pos n)]
  -- η-factor
  have hη : ∀ n : ℕ, ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), f x = 1) ∧
      (∀ x, x ∉ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2) → f x = 0) := by
    intro n
    refine cutoff1d_exists _ _ _ _ ?_ ?_ ?_
    · linarith [hn0 n]
    · linarith [hn0 n]
    · linarith [hn0 n]
  choose fs hfs using hs
  choose fq hfq using hq
  choose fη hfη using hη
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → Set Chart, ∀ n, K n =
      (Icc (e n / 2) ((n : ℝ) + 1 + e n / 2) ×ˢ
        (Icc (-(c / 2 * (1 - e n / 2))) (c / 2 * (1 - e n / 2)) ×ˢ
          Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2))) :=
    ⟨fun n => (Icc (e n / 2) ((n : ℝ) + 1 + e n / 2) ×ˢ
        (Icc (-(c / 2 * (1 - e n / 2))) (c / 2 * (1 - e n / 2)) ×ˢ
          Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2))), fun n => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → Chart → ℝ, ∀ n p, ψ n p = fs n p.1 * (fq n p.2.1 * fη n p.2.2) :=
    ⟨fun n p => fs n p.1 * (fq n p.2.1 * fη n p.2.2), fun n p => rfl⟩
  have hKc : ∀ n, IsCompact (K n) := fun n => by
    rw [hKdef]; exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : ∀ n, K n ⊆ chartDom c := fun n => by
    intro p hp
    rw [hKdef] at hp
    obtain ⟨⟨hs1, _⟩, ⟨hq1, hq2⟩, _⟩ := hp
    show 0 < p.1 ∧ |p.2.1| < c / 2
    refine ⟨by linarith [he_pos n], ?_⟩
    rw [abs_lt]
    constructor <;> nlinarith [mul_pos hc (he_pos n)]
  have hzero : ∀ n p, p ∉ K n → ψ n p = 0 := by
    intro n p hp
    rw [hψ]
    rw [hKdef] at hp
    have key : fs n p.1 = 0 ∨ fq n p.2.1 = 0 ∨ fη n p.2.2 = 0 := by
      by_contra hcon
      push_neg at hcon
      apply hp
      refine ⟨?_, ?_, ?_⟩
      · by_contra h
        exact hcon.1 ((hfs n).2.2.2 p.1 h)
      · by_contra h
        exact hcon.2.1 ((hfq n).2.2.2 p.2.1 h)
      · by_contra h
        exact hcon.2.2 ((hfη n).2.2.2 p.2.2 h)
    rcases key with h | h | h <;> simp [h]
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hfun : ψ n = fun p => fs n p.1 * (fq n p.2.1 * fη n p.2.2) := funext (hψ n)
    rw [hfun]
    exact ((hfs n).1.comp contDiff_fst).mul
      (((hfq n).1.comp (contDiff_fst.comp contDiff_snd)).mul
        ((hfη n).1.comp (contDiff_snd.comp contDiff_snd)))
  · intro n
    exact HasCompactSupport.intro (hKc n) (fun p hp => hzero n p hp)
  · intro n
    have hsupp : Function.support (ψ n) ⊆ K n := fun p hp => by
      by_contra h
      exact hp (hzero n p h)
    exact (closure_minimal hsupp (hKc n).isClosed).trans (hKsub n)
  · intro n p
    rw [hψ]
    obtain ⟨a1, a2⟩ := (hfs n).2.1 p.1
    obtain ⟨b1, b2⟩ := (hfq n).2.1 p.2.1
    obtain ⟨c1, c2⟩ := (hfη n).2.1 p.2.2
    constructor
    · exact mul_nonneg a1 (mul_nonneg b1 c1)
    · exact mul_le_one₀ a2 (mul_nonneg b1 c1) (mul_le_one₀ b2 c1 c2)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have ev1 : ∀ᶠ n in atTop, e n < x.1 := hE.eventually (gt_mem_nhds hx1)
    have ev2 : ∀ᶠ n : ℕ in atTop, x.1 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop x.1
    have hQ : Tendsto (fun n => c / 2 * (1 - e n)) atTop (𝓝 (c / 2)) := by
      have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c / 2) atTop (𝓝 (c / 2))).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hE)
      simpa using this
    have ev3 : ∀ᶠ n in atTop, |x.2.1| < c / 2 * (1 - e n) := hQ.eventually (lt_mem_nhds hx2)
    have ev4 : ∀ᶠ n : ℕ in atTop, |x.2.2| ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop |x.2.2|
    have hev : ∀ᶠ n in atTop, ψ n x = 1 := by
      filter_upwards [ev1, ev2, ev3, ev4] with n h1 h2 h3 h4
      have ha : fs n x.1 = 1 := (hfs n).2.2.1 x.1 ⟨h1.le, by linarith⟩
      have hb : fq n x.2.1 = 1 := (hfq n).2.2.1 x.2.1 (abs_le.mp h3.le)
      have hc' : fη n x.2.2 = 1 := (hfη n).2.2.1 x.2.2 (abs_le.mp (by linarith))
      rw [hψ, ha, hb, hc']
      norm_num
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

end UnforcedLeray.Short.PartIIIb.Concrete
