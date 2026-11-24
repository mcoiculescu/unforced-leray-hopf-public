import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `frechetLscBound`

A finite lower semicontinuous seminorm on the band tests is bounded by finitely many `C^k`
seminorms.  Baire-type nested construction (no Baire theorem): if no bound holds, build band tests
`x_n` and neighbourhoods `{ψ : C^{K_n}-distance to x_n ≤ ε_n}` on which `p > n - 1`
(lower semicontinuity), with `x_{n+1} - x_n` small; the series limit `x∞` (completeness via
`contDiff_tsum_of_eventually`) lies in every neighbourhood, so `p x∞ > n - 1` for all `n`.
Source: `the November 2 reference manuscript` around line 4610.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace FrechetLscAux

lemma ckSmall_mono {K K' : ℕ} {M M' : ℝ} {φ : ℝ × ℝ → ℝ} (h : CkSmall K M φ) (hK : K' ≤ K)
    (hM : M ≤ M') : CkSmall K' M' φ :=
  fun j hj x => (h j (hj.trans hK) x).trans hM

lemma bandTest_smul {c R : ℝ} {φ : ℝ × ℝ → ℝ} (h : BandTest c R φ) (a : ℝ) :
    BandTest c R (a • φ) := by
  refine ⟨⟨h.1.smooth.const_smul a, fun x => ?_, ⟨R, fun x hx => ?_⟩⟩, fun x hx => ?_⟩
  · simp [h.1.periodic x]
  · simp [h.2 x hx]
  · simp [h.2 x hx]

lemma bandTest_add {c R : ℝ} {φ ψ : ℝ × ℝ → ℝ} (h : BandTest c R φ) (h' : BandTest c R ψ) :
    BandTest c R (φ + ψ) := by
  refine ⟨⟨h.1.smooth.add h'.1.smooth, fun x => ?_, ⟨R, fun x hx => ?_⟩⟩, fun x hx => ?_⟩
  · simp [h.1.periodic x, h'.1.periodic x]
  · simp [h.2 x hx, h'.2 x hx]
  · simp [h.2 x hx, h'.2 x hx]

lemma bandTest_zero (c R : ℝ) : BandTest c R 0 :=
  ⟨⟨contDiff_const, fun _ => rfl, ⟨R, fun _ _ => rfl⟩⟩, fun _ _ => rfl⟩

/-- Step A: failure of every bound gives test functions small in `C^k` with `p` arbitrarily large. -/
lemma unbounded (c R : ℝ) (p : (ℝ × ℝ → ℝ) → ℝ)
    (hsm : ∀ (a : ℝ) φ, BandTest c R φ → p (a • φ) = |a| * p φ)
    (hneg : ¬ ∃ (k : ℕ) (C : ℝ), ∀ φ, BandTest c R φ → ∀ M : ℝ, CkSmall k M φ → p φ ≤ C * M)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (N : ℝ) :
    ∃ ψ, BandTest c R ψ ∧ CkSmall k ε ψ ∧ N < p ψ := by
  by_contra hcon
  push Not at hcon
  apply hneg
  refine ⟨k, N / ε, fun φ hφ M hM => ?_⟩
  have hM0 : 0 ≤ M := by
    have := hM 0 (Nat.zero_le _) 0
    exact (norm_nonneg _).trans this
  rcases hM0.eq_or_lt with h0 | hpos
  · have hφ0 : φ = (0 : ℝ) • φ := by
      funext x
      have := hM 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero, ← h0] at this
      have : φ x = 0 := norm_le_zero_iff.mp this
      simp [this]
    have : p φ = 0 := by
      have h := hsm 0 φ hφ
      rw [← hφ0] at h
      simpa using h
    rw [this, ← h0]; simp
  · have hψ : BandTest c R ((ε / M) • φ) := bandTest_smul hφ _
    have hsmall : CkSmall k ε ((ε / M) • φ) := by
      intro j hj x
      have hc : ContDiffAt ℝ (j : ℕ∞) φ x :=
        (hφ.1.smooth.of_le (by exact_mod_cast le_top)).contDiffAt
      have h2 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := ε / M) hc
      rw [h2, norm_smul, Real.norm_of_nonneg (div_pos hε hpos).le]
      calc ε / M * ‖iteratedFDeriv ℝ j φ x‖ ≤ ε / M * M :=
            mul_le_mul_of_nonneg_left (hM j hj x) (div_pos hε hpos).le
        _ = ε := by field_simp
    have h1 := hcon _ hψ hsmall
    rw [hsm _ _ hφ, abs_of_pos (div_pos hε hpos)] at h1
    calc p φ = (M / ε) * ((ε / M) * p φ) := by field_simp
      _ ≤ (M / ε) * N := mul_le_mul_of_nonneg_left h1 (div_pos hpos hε).le
      _ = N / ε * M := by ring

/-- Step B: lower semicontinuity gives a `C^K`-neighbourhood on which `p > b`. -/
lemma nbhd (c R : ℝ) (p : (ℝ × ℝ → ℝ) → ℝ)
    (hlsc : ∀ (φn : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ), (∀ n, BandTest c R (φn n)) → BandTest c R φ →
        CkConv φn φ → ∀ t : ℝ, (∀ᶠ n in atTop, p (φn n) ≤ t) → p φ ≤ t)
    (x : ℝ × ℝ → ℝ) (hx : BandTest c R x) (b : ℝ) (hb : b < p x) :
    ∃ (K : ℕ) (ε : ℝ), 0 < ε ∧ ∀ ψ, BandTest c R ψ → CkSmall K ε (ψ - x) → b < p ψ := by
  by_contra hcon
  push Not at hcon
  choose ψ hψ1 hψ2 hψ3 using fun m : ℕ => hcon m (1 / ((m : ℝ) + 1)) (by positivity)
  have key : CkConv ψ x := by
    intro j ε hε
    obtain ⟨m0, hm0⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop (max j m0)] with m hm y
    have hjm : j ≤ m := (le_max_left _ _).trans hm
    have hm0m : m0 ≤ m := (le_max_right _ _).trans hm
    refine (hψ2 m j hjm y).trans ?_
    have h1 : 1 / ε < (m : ℝ) := hm0.trans_le (by exact_mod_cast hm0m)
    have h2 : 1 < (m : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := hlsc ψ x hψ1 hx key b (Filter.Eventually.of_forall hψ3)
  linarith

/-- Completeness: series of `C^∞` functions with `C^{K_i}`-summable bounds. -/
lemma series_bound (Z : ℕ → ℝ × ℝ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) (hK : ∀ i, CkSmall (K i) (δ i) (Z i)) (hδ : Summable δ)
    (hKinf : ∀ j : ℕ, ∀ᶠ i in atTop, j ≤ K i) :
    ContDiff ℝ ∞ (fun y => ∑' i, Z i y) ∧
      ∀ j : ℕ, (∀ i, j ≤ K i) → ∀ y,
        ‖iteratedFDeriv ℝ j (fun y => ∑' i, Z i y) y‖ ≤ ∑' i, δ i := by
  constructor
  · refine contDiff_tsum_of_eventually (N := ⊤) (v := fun _ => δ) hZ (fun _ _ => hδ) ?_
    intro k _
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hKinf k] with i hi y
    exact hK i k hi y
  · intro j hj y
    have hZj : ∀ i, ContDiff ℝ ((j : ℕ∞) : WithTop ℕ∞) (Z i) :=
      fun i => (hZ i).of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_tsum_apply (N := (j : ℕ∞)) (v := fun _ => δ) hZj (fun _ _ => hδ)
      (fun k i x hk => hK i k ((Nat.cast_le.mp hk).trans (hj i)) x) le_rfl y]
    exact tsum_of_norm_bounded hδ.hasSum (fun i => hK i j (hj i) y)

/-- Invariant of the nested construction. -/
def Inv (c R : ℝ) (p : (ℝ × ℝ → ℝ) → ℝ) (n : ℕ) (s : (ℝ × ℝ → ℝ) × ℕ × ℝ) : Prop :=
  BandTest c R s.1 ∧ 0 < s.2.2 ∧
    ∀ ψ, BandTest c R ψ → CkSmall s.2.1 s.2.2 (ψ - s.1) → (n : ℝ) - 1 < p ψ

lemma step (c R : ℝ) (p : (ℝ × ℝ → ℝ) → ℝ)
    (hsub : ∀ φ ψ, BandTest c R φ → BandTest c R ψ → p (φ + ψ) ≤ p φ + p ψ)
    (hsm : ∀ (a : ℝ) φ, BandTest c R φ → p (a • φ) = |a| * p φ)
    (hlsc : ∀ (φn : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ), (∀ n, BandTest c R (φn n)) → BandTest c R φ →
        CkConv φn φ → ∀ t : ℝ, (∀ᶠ n in atTop, p (φn n) ≤ t) → p φ ≤ t)
    (hneg : ¬ ∃ (k : ℕ) (C : ℝ), ∀ φ, BandTest c R φ → ∀ M : ℝ, CkSmall k M φ → p φ ≤ C * M)
    (n : ℕ) (s : (ℝ × ℝ → ℝ) × ℕ × ℝ) :
    ∃ s' : (ℝ × ℝ → ℝ) × ℕ × ℝ, Inv c R p n s →
      (Inv c R p (n + 1) s' ∧ s.2.1 + 1 ≤ s'.2.1 ∧ s'.2.2 ≤ s.2.2 / 2 ∧
        CkSmall s.2.1 (s.2.2 / 2) (s'.1 - s.1)) := by
  by_cases h : Inv c R p n s
  swap
  · exact ⟨s, fun h' => absurd h' h⟩
  obtain ⟨hx, hε, hψ⟩ := h
  obtain ⟨y, hy, hyS, hyp⟩ := unbounded c R p hsm hneg s.2.1 (s.2.2 / 2) (by positivity)
    ((n : ℝ) + p s.1)
  have hx' : BandTest c R (s.1 + y) := bandTest_add hx hy
  have hpx' : (n : ℝ) < p (s.1 + y) := by
    have hyeq : y = (s.1 + y) + (-1 : ℝ) • s.1 := by funext z; simp
    have h1 := hsub (s.1 + y) ((-1 : ℝ) • s.1) hx' (bandTest_smul hx _)
    have h2 := hsm (-1) s.1 hx
    rw [← hyeq] at h1
    simp only [abs_neg, abs_one, one_mul] at h2
    linarith
  obtain ⟨K0, ε0, hε0, hK0⟩ := nbhd c R p hlsc _ hx' n hpx'
  refine ⟨(s.1 + y, max K0 (s.2.1 + 1), min ε0 (s.2.2 / 2)), fun _ => ?_⟩
  refine ⟨⟨hx', lt_min hε0 (by positivity), fun ψ hψb hψc => ?_⟩, le_max_right _ _,
    min_le_right _ _, ?_⟩
  · have := hK0 ψ hψb (ckSmall_mono hψc (le_max_left _ _) (min_le_left _ _))
    push_cast
    linarith
  · simpa using hyS

lemma series_main (c R : ℝ) (p : (ℝ × ℝ → ℝ) → ℝ)
    (hp0 : ∀ φ, BandTest c R φ → 0 ≤ p φ)
    (hsub : ∀ φ ψ, BandTest c R φ → BandTest c R ψ → p (φ + ψ) ≤ p φ + p ψ)
    (hsm : ∀ (a : ℝ) φ, BandTest c R φ → p (a • φ) = |a| * p φ)
    (hlsc : ∀ (φn : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ), (∀ n, BandTest c R (φn n)) → BandTest c R φ →
        CkConv φn φ → ∀ t : ℝ, (∀ᶠ n in atTop, p (φn n) ≤ t) → p φ ≤ t)
    (hneg : ¬ ∃ (k : ℕ) (C : ℝ), ∀ φ, BandTest c R φ → ∀ M : ℝ, CkSmall k M φ → p φ ≤ C * M) :
    False := by
  choose F hF using step c R p hsub hsm hlsc hneg
  let u : ℕ → (ℝ × ℝ → ℝ) × ℕ × ℝ := fun n => Nat.rec (0, 0, 1) (fun m s => F m s) n
  have hu0 : u 0 = (0, 0, 1) := rfl
  have hus : ∀ n, u (n + 1) = F n (u n) := fun n => rfl
  have hInv : ∀ n, Inv c R p n (u n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨bandTest_zero c R, one_pos, fun ψ hψ _ => ?_⟩
      have := hp0 ψ hψ
      show ((0 : ℕ) : ℝ) - 1 < p ψ
      simp
      linarith
    | succ n ih => rw [hus]; exact (hF n (u n) ih).1
  have hK : ∀ n, (u n).2.1 + 1 ≤ (u (n + 1)).2.1 := fun n => by
    rw [hus]; exact (hF n (u n) (hInv n)).2.1
  have hε : ∀ n, (u (n + 1)).2.2 ≤ (u n).2.2 / 2 := fun n => by
    rw [hus]; exact (hF n (u n) (hInv n)).2.2.1
  have hy : ∀ n, CkSmall (u n).2.1 ((u n).2.2 / 2) ((u (n + 1)).1 - (u n).1) := fun n => by
    rw [hus]; exact (hF n (u n) (hInv n)).2.2.2
  have Kge : ∀ n, n ≤ (u n).2.1 := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact (Nat.succ_le_succ ih).trans (hK n)
  have Kmono : ∀ m i, (u m).2.1 ≤ (u (i + m)).2.1 := by
    intro m i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hK (i + m)
      rw [show i + 1 + m = (i + m) + 1 by ring]
      omega
  have εle : ∀ m i, (u (i + m)).2.2 ≤ (u m).2.2 * (1 / 2) ^ i := by
    intro m i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hε (i + m)
      rw [show i + 1 + m = (i + m) + 1 by ring, pow_succ]
      nlinarith
  set Y : ℕ → ℝ × ℝ → ℝ := fun n => (u (n + 1)).1 - (u n).1 with hYdef
  have hYsmooth : ∀ n, ContDiff ℝ ∞ (Y n) := fun n =>
    (hInv (n + 1)).1.1.smooth.sub (hInv n).1.1.smooth
  have hYsum : ∀ z, Summable fun i => Y i z := by
    intro z
    refine Summable.of_norm_bounded (g := fun i => (1 / 2 : ℝ) ^ i) summable_geometric_two
      (fun i => ?_)
    have h0 := hy i 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero] at h0
    have h1 := εle 0 i
    have h2 : (u 0).2.2 = 1 := rfl
    simp only [Nat.add_zero] at h1
    rw [h2] at h1
    have h3 : (u i).2.2 / 2 ≤ (1 / 2 : ℝ) ^ i := by
      have : (0:ℝ) ≤ (1 / 2) ^ i := by positivity
      nlinarith [(hInv i).2.1]
    exact h0.trans h3
  let xinf : ℝ × ℝ → ℝ := fun z => ∑' i, Y i z
  have hdec : ∀ m z, xinf z = (u m).1 z + ∑' i, Y (i + m) z := by
    intro m z
    have h := (hYsum z).sum_add_tsum_nat_add m
    have htel : ∑ i ∈ Finset.range m, Y i z = (u m).1 z := by
      have := Finset.sum_range_sub (fun n => (u n).1 z) m
      simp only [Y, Pi.sub_apply]
      rw [this]
      simp [hu0]
    rw [← htel]
    exact h.symm
  have hser : ∀ m, ContDiff ℝ ∞ (fun z => ∑' i, Y (i + m) z) ∧
      ∀ j : ℕ, j ≤ (u m).2.1 → ∀ y, ‖iteratedFDeriv ℝ j (fun z => ∑' i, Y (i + m) z) y‖ ≤
        (u m).2.2 := by
    intro m
    have hδ : Summable fun i => (u (i + m)).2.2 / 2 := by
      refine Summable.of_nonneg_of_le (fun i => by have := (hInv (i + m)).2.1; positivity)
        (fun i => ?_) ((summable_geometric_two.mul_left ((u m).2.2 / 2)))
      have := εle m i
      nlinarith
    obtain ⟨h1, h2⟩ := series_bound (fun i => Y (i + m)) (fun i => (u (i + m)).2.1)
      (fun i => (u (i + m)).2.2 / 2) (fun i => hYsmooth _) (fun i => hy (i + m)) hδ
      (fun j => by
        filter_upwards [eventually_ge_atTop j] with i hi
        exact hi.trans ((Nat.le_add_right i m).trans (Kge (i + m))))
    refine ⟨h1, fun j hj y => (h2 j (fun i => hj.trans (Kmono m i)) y).trans ?_⟩
    calc ∑' i, (u (i + m)).2.2 / 2 ≤ ∑' i : ℕ, (u m).2.2 / 2 * (1 / 2 : ℝ) ^ i := by
          refine Summable.tsum_le_tsum (fun i => ?_) hδ
            (summable_geometric_two.mul_left ((u m).2.2 / 2))
          have := εle m i
          nlinarith
      _ = (u m).2.2 := by rw [tsum_mul_left, tsum_geometric_two]; ring
  have hxb : BandTest c R xinf := by
    refine ⟨⟨?_, fun z => ?_, ⟨R, fun z hz => ?_⟩⟩, fun z hz => ?_⟩
    · have := (hser 0).1
      have e : xinf = fun z => ∑' i, Y (i + 0) z := rfl
      exact e ▸ this
    · refine tsum_congr (fun i => ?_)
      simp only [Y, Pi.sub_apply, (hInv i).1.1.periodic z, (hInv (i + 1)).1.1.periodic z]
    · refine (tsum_congr (fun i => ?_)).trans tsum_zero
      simp only [Y, Pi.sub_apply, (hInv i).1.2 z hz, (hInv (i + 1)).1.2 z hz, sub_zero]
    · refine (tsum_congr (fun i => ?_)).trans tsum_zero
      simp only [Y, Pi.sub_apply, (hInv i).1.2 z hz, (hInv (i + 1)).1.2 z hz, sub_zero]
  have hbig : ∀ n : ℕ, (n : ℝ) - 1 < p xinf := by
    intro n
    refine (hInv n).2.2 xinf hxb (fun j hj y => ?_)
    have e : xinf - (u n).1 = fun z => ∑' i, Y (i + n) z := by
      funext z
      simp only [Pi.sub_apply, hdec n z]
      ring
    rw [e]
    exact (hser n).2 j hj y
  obtain ⟨n, hn⟩ := exists_nat_gt (p xinf + 1)
  have := hbig n
  linarith

end FrechetLscAux

theorem frechetLscBound : FrechetLscBound := by
  intro c R p hp0 hsub hsm hlsc
  by_contra hneg
  exact FrechetLscAux.series_main c R p hp0 hsub hsm hlsc hneg

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
