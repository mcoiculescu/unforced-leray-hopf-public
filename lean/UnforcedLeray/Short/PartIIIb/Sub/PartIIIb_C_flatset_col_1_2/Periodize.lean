import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Reduce
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Smoothness of the `c`-periodization of a Schwartz function on the plane

Proves `PeriodizeSchwartzSmooth` (`Reduce.lean`).  Route: for a Schwartz function `g` with values
in a normed space `V`, the periodization `per c g x = ∑' j, g (x.1 - j c, x.2)` has the derivative
`per c (fderivCLM g)` at every point (`hasFDerivAt_tsum_of_isPreconnected` on a ball, with the
summable majorant `K / (1 + j^2)`); induction on the order of smoothness, using
`contDiff_succ_iff_hasFDerivAt`, gives `C^n` for every `n` and every `V`-valued `g`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace PeriodizeAux

/-- The `c`-periodization in the first variable. -/
def per {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ)
    (g : SchwartzMap (ℝ × ℝ) V) (x : ℝ × ℝ) : V :=
  ∑' j : ℤ, g (x.1 - j * c, x.2)

theorem summable_inv_one_add_sq :
    Summable (fun j : ℤ => 1 / (1 + (j : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually (g := fun j : ℤ => 1 / (j : ℝ) ^ 2)
    (Real.summable_one_div_int_pow.2 one_lt_two) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj
  have ha : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast ha
      simpa [Int.cast_abs] using this
    nlinarith [sq_abs (j : ℝ)]
  show ‖1 / (1 + (j : ℝ) ^ 2)‖ ≤ 1 / (j : ℝ) ^ 2
  rw [Real.norm_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem schwartz_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SchwartzMap (ℝ × ℝ) V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ × ℝ, (1 + ‖y‖ ^ 2) * ‖g y‖ ≤ K := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ 2 0 g,
    add_nonneg (apply_nonneg _ _) (apply_nonneg _ _), fun y => ?_⟩
  have h0 := SchwartzMap.norm_le_seminorm ℝ g y
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ g 2 y
  have e : (1 + ‖y‖ ^ 2) * ‖g y‖ = ‖g y‖ + ‖y‖ ^ 2 * ‖g y‖ := by ring
  rw [e]
  linarith

theorem decay_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SchwartzMap (ℝ × ℝ) V) {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (x : ℝ × ℝ), ‖x‖ ≤ R →
      ‖g (x.1 - j * c, x.2)‖ ≤ K * (1 / (1 + (j : ℝ) ^ 2)) := by
  obtain ⟨K0, hK0, hb⟩ := schwartz_bound g
  have hp : 0 < c ^ 2 := by positivity
  refine ⟨K0 * (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2), by positivity, ?_⟩
  intro j x hx
  set y : ℝ × ℝ := (x.1 - j * c, x.2) with hy
  have hyb := hb y
  have hgn : 0 ≤ ‖g y‖ := norm_nonneg _
  have hx1 : |x.1| ≤ R := by
    have := norm_fst_le x
    rw [Real.norm_eq_abs] at this
    linarith
  have hy1 : |y.1| ≤ ‖y‖ := by
    have := norm_fst_le y
    rw [Real.norm_eq_abs] at this
    exact this
  have hjc : (j : ℝ) * c = x.1 - y.1 := by
    simp only [hy]; ring
  have htri : |(j : ℝ)| * c ≤ |x.1| + |y.1| := by
    have h1 : |(j : ℝ) * c| = |(j : ℝ)| * c := by
      rw [abs_mul, abs_of_pos hc]
    rw [← h1, hjc]
    exact abs_sub _ _
  have hyn : |(j : ℝ)| * c - R ≤ ‖y‖ := by linarith
  have hj2 : (j : ℝ) ^ 2 = |(j : ℝ)| ^ 2 := (sq_abs _).symm
  rcases lt_or_ge (|(j : ℝ)| * c) (2 * R) with hA | hB
  · -- small `j`: the bound `‖g y‖ ≤ K0` suffices
    have hsmall : ‖g y‖ ≤ K0 := by
      have : ‖g y‖ ≤ (1 + ‖y‖ ^ 2) * ‖g y‖ := by nlinarith [sq_nonneg ‖y‖]
      linarith
    have hj2le : (j : ℝ) ^ 2 ≤ 4 * R ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ hp]
      have h0 : 0 ≤ |(j : ℝ)| * c := by positivity
      have : (|(j : ℝ)| * c) ^ 2 ≤ (2 * R) ^ 2 := by
        exact pow_le_pow_left₀ h0 hA.le 2
      nlinarith [sq_abs (j : ℝ)]
    have hD : 1 ≤ (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) / (1 + (j : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ 8 / c ^ 2 := by positivity
      linarith
    calc ‖g y‖ ≤ K0 := hsmall
      _ ≤ K0 * ((1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) / (1 + (j : ℝ) ^ 2)) :=
          le_mul_of_one_le_right hK0 hD
      _ = K0 * (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) * (1 / (1 + (j : ℝ) ^ 2)) := by ring
  · -- large `j`: `‖y‖ ≥ |j| c / 2`
    have hjne : (j : ℝ) ≠ 0 := by
      intro h
      have : |(j : ℝ)| = 0 := by simp [h]
      have hpos : 0 < |(j : ℝ)| * c := by linarith
      rw [this] at hpos
      simp at hpos
    have hjz : j ≠ 0 := fun h => hjne (by simp [h])
    have hj1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
      have ha : (1 : ℤ) ≤ |j| := Int.one_le_abs hjz
      have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have : ((1 : ℤ) : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast ha
        simpa [Int.cast_abs] using this
      nlinarith [sq_abs (j : ℝ)]
    have hs : |(j : ℝ)| * c / 2 ≤ ‖y‖ := by linarith
    have hs0 : 0 ≤ |(j : ℝ)| * c / 2 := by positivity
    have hs2 : (|(j : ℝ)| * c / 2) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hs0 hs 2
    have hq : (|(j : ℝ)| * c / 2) ^ 2 = (j : ℝ) ^ 2 * c ^ 2 / 4 := by
      rw [div_pow, mul_pow, sq_abs]; ring
    have key1 : ‖g y‖ * ((j : ℝ) ^ 2 * c ^ 2) ≤ 4 * K0 := by
      have h1 : ‖g y‖ * ((j : ℝ) ^ 2 * c ^ 2 / 4) ≤ (1 + ‖y‖ ^ 2) * ‖g y‖ := by
        have : (j : ℝ) ^ 2 * c ^ 2 / 4 ≤ 1 + ‖y‖ ^ 2 := by
          rw [← hq]; nlinarith
        nlinarith [norm_nonneg (g y)]
      have h2 : ‖g y‖ * ((j : ℝ) ^ 2 * c ^ 2) = 4 * (‖g y‖ * ((j : ℝ) ^ 2 * c ^ 2 / 4)) := by
        ring
      rw [h2]
      linarith
    have hq1 : (1 : ℝ) + (j : ℝ) ^ 2 ≤ 2 * (j : ℝ) ^ 2 := by linarith
    have key2 : ‖g y‖ * (1 + (j : ℝ) ^ 2) ≤ 8 * K0 / c ^ 2 := by
      have hpc : 0 < (j : ℝ) ^ 2 * c ^ 2 := by positivity
      rw [le_div_iff₀ hp]
      have hgq : ‖g y‖ * (1 + (j : ℝ) ^ 2) * c ^ 2 ≤ 2 * (‖g y‖ * ((j : ℝ) ^ 2 * c ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hq1 (mul_nonneg hgn hp.le)
        nlinarith [this]
      linarith
    have hfin : ‖g y‖ * (1 + (j : ℝ) ^ 2) ≤ K0 * (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) := by
      have hK : 8 * K0 / c ^ 2 ≤ K0 * (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) := by
        have e1 : K0 * (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) = K0 + K0 * (4 * R ^ 2 / c ^ 2) + K0 * (8 / c ^ 2) := by ring
        have h1 : 0 ≤ K0 * (4 * R ^ 2 / c ^ 2) := by positivity
        have h2 : 8 * K0 / c ^ 2 = K0 * (8 / c ^ 2) := by ring
        rw [e1, h2]
        linarith
      linarith
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc ‖g y‖ * (1 + (j : ℝ) ^ 2) ≤ K0 * (1 + 4 * R ^ 2 / c ^ 2 + 8 / c ^ 2) := hfin
      _ = _ := by ring

theorem hasFDerivAt_per {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {c : ℝ}
    (hc : 0 < c) (g : SchwartzMap (ℝ × ℝ) V) (x : ℝ × ℝ) :
    HasFDerivAt (per c g) (per c (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) V g) x) x := by
  set R : ℝ := ‖x‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  have hsopen : IsOpen (ball (0 : ℝ × ℝ) R) := isOpen_ball
  have hspre : IsPreconnected (ball (0 : ℝ × ℝ) R) := (convex_ball _ _).isPreconnected
  have hxs : x ∈ ball (0 : ℝ × ℝ) R := by
    rw [mem_ball_zero_iff]
    linarith
  have hA : ∀ (a : ℝ) (y : ℝ × ℝ),
      HasFDerivAt (fun z : ℝ × ℝ => (z.1 - a, z.2)) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) y := by
    intro a y
    have h1 : HasFDerivAt (fun z : ℝ × ℝ => z.1 - a) (ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
      (hasFDerivAt_fst).sub_const a
    have h2 := h1.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := y))
    have hid : (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) =
        ContinuousLinearMap.id ℝ (ℝ × ℝ) := ContinuousLinearMap.ext fun v => rfl
    rw [hid] at h2
    exact h2
  have hterm : ∀ (n : ℤ) (y : ℝ × ℝ),
      HasFDerivAt (fun z : ℝ × ℝ => g (z.1 - (n : ℝ) * c, z.2))
        (fderiv ℝ g (y.1 - (n : ℝ) * c, y.2)) y := by
    intro n y
    have h := (g.hasFDerivAt (y.1 - (n : ℝ) * c, y.2)).comp y (hA ((n : ℝ) * c) y)
    rwa [ContinuousLinearMap.comp_id] at h
  obtain ⟨K, hK, hbd⟩ := decay_sum (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) V g) hc hR
  obtain ⟨K0, hK0, hbd0⟩ := decay_sum g hc hR
  have hu : Summable (fun n : ℤ => K * (1 / (1 + (n : ℝ) ^ 2))) :=
    summable_inv_one_add_sq.mul_left K
  have hsum := hasFDerivAt_tsum_of_isPreconnected
    (f := fun (n : ℤ) (z : ℝ × ℝ) => g (z.1 - (n : ℝ) * c, z.2))
    (f' := fun (n : ℤ) (y : ℝ × ℝ) => fderiv ℝ g (y.1 - (n : ℝ) * c, y.2))
    (u := fun n : ℤ => K * (1 / (1 + (n : ℝ) ^ 2)))
    hu hsopen hspre (fun n y _ => hterm n y)
    (fun n y hy => by
      have h := hbd n y (le_of_lt (mem_ball_zero_iff.1 hy))
      exact h)
    (mem_ball_self hR)
    (Summable.of_norm_bounded_eventually (summable_inv_one_add_sq.mul_left K0)
      (Filter.Eventually.of_forall fun n => by
        have h := hbd0 n 0 (by rw [norm_zero]; exact hR.le)
        exact h))
    hxs
  exact hsum

theorem contDiff_per (c : ℝ) (hc : 0 < c) :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (g : SchwartzMap (ℝ × ℝ) V), ContDiff ℝ n (per c g) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ g
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x => (hasFDerivAt_per hc g x).continuousAt
  | succ n ih =>
    intro V _ _ _ g
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨fun x => per c (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) V g) x,
      ih _ (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) V g), fun x => hasFDerivAt_per hc g x⟩

end PeriodizeAux

open PeriodizeAux in
/-- **Leaf 2** (source 4988): the `c`-periodization in `q` of a Schwartz function on the plane is
`C^∞`. -/
theorem periodizeSchwartzSmooth : PeriodizeSchwartzSmooth := by
  intro c hc f
  exact contDiff_infty.2 fun n => contDiff_per c hc n ℝ f

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
