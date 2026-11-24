import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# `PartIII-b:C/rep/8/2/3/2/11`: derivatives of the theta sums `tt`

Source `the November 2 reference manuscript` 4963-4968.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace TtJetAux

/-- Base bound. -/
lemma tt_base (j : ℕ) : ∃ A : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ x : ℝ × ℝ, 1 / 5 ≤ x.1 → x.1 ≤ 1 →
    ‖UnforcedLeray.Short.IIb.tt c j x‖ ≤ A := by
  obtain ⟨C, hC, h⟩ := UnforcedLeray.Short.IIb.gauss_poly_le j (m := 1 / 10) (by norm_num)
  refine ⟨10 * C, fun c hc x hx1 hx2 => ?_⟩
  have ha : (0 : ℝ) < 5 / 2 := by norm_num
  have hac : (5 / 2 : ℝ) ≤ c ^ 2 := by nlinarith
  have hs := UnforcedLeray.Gaussian.summable_gauss_shift ha hac x.2
  have hb := UnforcedLeray.Gaussian.tsum_gauss_shift_le ha hac x.2
  have hterm : ∀ n : ℤ, ‖UnforcedLeray.Short.IIb.ttTerm c j n x‖ ≤
      C * Real.exp (-(x.2 - n * c) ^ 2 / (4 * (5 / 2))) := by
    intro n
    rw [UnforcedLeray.Short.IIb.norm_ttTerm]
    set t := x.2 - n * c with ht
    have h1 := h t
    have h2 : (1 + |t|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    have h3 : Real.exp (-x.1 * t ^ 2) ≤ Real.exp (-(1 / 5) * t ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg t])
    have e : Real.exp (-(1 / 5) * t ^ 2) =
        Real.exp (-(1 / 10 * t ^ 2)) * Real.exp (-t ^ 2 / (4 * (5 / 2))) := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 : |t| ^ j * Real.exp (-(1 / 10 * t ^ 2)) ≤ C := by
      calc _ ≤ C * (1 + |t|) ^ (-2 : ℝ) := h1
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 hC.le
        _ = C := mul_one C
    calc |t| ^ j * Real.exp (-x.1 * t ^ 2) ≤ |t| ^ j * Real.exp (-(1 / 5) * t ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (|t| ^ j * Real.exp (-(1 / 10 * t ^ 2))) * Real.exp (-t ^ 2 / (4 * (5 / 2))) := by
          rw [e]; ring
      _ ≤ C * Real.exp (-t ^ 2 / (4 * (5 / 2))) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
  have hm : Summable fun n : ℤ => C * Real.exp (-(x.2 - n * c) ^ 2 / (4 * (5 / 2))) :=
    hs.mul_left C
  have hn : Summable fun n : ℤ => ‖UnforcedLeray.Short.IIb.ttTerm c j n x‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hm
  unfold UnforcedLeray.Short.IIb.tt
  refine (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hterm hm).trans ?_)
  rw [tsum_mul_left]
  nlinarith [hb]

/-- fst is smooth with small derivatives. -/
lemma fst_iter (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ × ℝ, |x.1| ≤ 1 →
    ‖iteratedFDeriv ℝ k (fun y : ℝ × ℝ => y.1) x‖ ≤ M := by
  have hd : fderiv ℝ (fun y : ℝ × ℝ => y.1) = fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ := by
    funext y; exact (ContinuousLinearMap.fst ℝ ℝ ℝ).fderiv
  match k with
  | 0 => exact ⟨1, by norm_num, fun x hx => by simpa [norm_iteratedFDeriv_zero] using hx⟩
  | 1 =>
    refine ⟨1, by norm_num, fun x _ => ?_⟩
    have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y : ℝ × ℝ => y.1) (x := x) (n := 0))
    rw [hd] at this
    simp only [norm_iteratedFDeriv_zero] at this
    rw [← this]; exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  | k + 2 =>
    refine ⟨0, le_rfl, fun x _ => ?_⟩
    have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y : ℝ × ℝ => y.1) (x := x) (n := k + 1))
    rw [hd, iteratedFDeriv_const_of_ne (by omega)] at this
    rw [← this]; simp

/-- Derivative of `g • L`. -/
lemma norm_iter_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → ℝ) (L : Y) {x : X} {i : ℕ}
    (hg : ContDiffAt ℝ i g x) :
    ‖iteratedFDeriv ℝ i (fun y => g y • L) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i g x‖ := by
  set L' : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight L
  have h := L'.norm_iteratedFDeriv_comp_left hg (le_refl (i : WithTop ℕ∞))
  have hn : ‖L'‖ ≤ ‖L‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun r => ?_
    simp [L', norm_smul, mul_comm]
  have e : (fun y => g y • L) = L' ∘ g := by funext y; simp [L']
  rw [e]
  exact h.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

lemma norm_iter_cmul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (a : ℝ) (h : X → ℝ)
    {x : X} {i : ℕ} (hg : ContDiffAt ℝ i h x) :
    ‖iteratedFDeriv ℝ i (fun y => a * h y) x‖ ≤ |a| * ‖iteratedFDeriv ℝ i h x‖ := by
  have := norm_iter_smul h (1 : ℝ) hg
  set L : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
  have h1 := L.norm_iteratedFDeriv_comp_left hg (le_refl (i : WithTop ℕ∞))
  have hn : ‖L‖ ≤ |a| := by
    refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun r => ?_
    simp [L, norm_smul, mul_comm]
  have e : (fun y => a * h y) = L ∘ h := by funext y; simp [L]
  rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

open UnforcedLeray.Short.IIb in
lemma leib {c : ℝ} (hc : c ≠ 0) (j i : ℕ) {x : ℝ × ℝ} (hx : 0 < x.1) :
    ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => y.1 * tt c j y) x‖ ≤
      ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * ‖iteratedFDeriv ℝ m (fun y : ℝ × ℝ => y.1) x‖ *
        ‖iteratedFDeriv ℝ (i - m) (tt c j) x‖ := by
  have hU : IsOpen {x : ℝ × ℝ | 0 < x.1} := isOpen_lt continuous_const continuous_fst
  have h := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := fun y : ℝ × ℝ => y.1) (g := tt c j)
    (s := {x : ℝ × ℝ | 0 < x.1}) (N := (i : WithTop ℕ∞))
    contDiff_fst.contDiffOn (contDiffOn_tt hc i j) hU.uniqueDiffOn hx (le_refl _)
  have e : ∀ n (f : ℝ × ℝ → ℝ), iteratedFDerivWithin ℝ n f {x : ℝ × ℝ | 0 < x.1} x =
      iteratedFDeriv ℝ n f x := fun n f => iteratedFDerivWithin_of_isOpen n hU hx
  simp only [e] at h
  exact h

end TtJetAux

open TtJetAux UnforcedLeray.Short.IIb in
theorem ttJetBound : TtJetBound := by
  intro i j
  have key : ∀ i : ℕ, ∀ k ≤ i, ∀ j : ℕ, ∃ K : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ x : ℝ × ℝ, 1 / 5 ≤ x.1 →
      x.1 ≤ 1 → ‖iteratedFDeriv ℝ k (tt c j) x‖ ≤ K := by
    intro i
    induction i with
    | zero =>
      intro k hk j
      obtain rfl : k = 0 := by omega
      obtain ⟨A, hA⟩ := tt_base j
      exact ⟨A, fun c hc x h1 h2 => by simpa [norm_iteratedFDeriv_zero] using hA c hc x h1 h2⟩
    | succ i ih =>
      intro k hk j
      rcases Nat.lt_or_ge k (i + 1) with hlt | hge
      · exact ih k (by omega) j
      obtain rfl : k = i + 1 := by omega
      choose! Kf hKf using ih
      choose! M hM0 hM using fst_iter
      refine ⟨Kf i (j + 2) + |(j : ℝ)| * Kf i (j - 1) + 2 *
        ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * M m * Kf (i - m) (j + 1), ?_⟩
      intro c hc x hx1 hx2
      have hc0 : c ≠ 0 := by intro h; rw [h] at hc; norm_num at hc
      have hU : IsOpen {x : ℝ × ℝ | 0 < x.1} := isOpen_lt continuous_const continuous_fst
      have hx0 : 0 < x.1 := by linarith
      have hxm : x ∈ {x : ℝ × ℝ | 0 < x.1} := hx0
      have hCD : ∀ (k j' : ℕ), ContDiffAt ℝ (k : WithTop ℕ∞) (tt c j') x := fun k j' =>
        (contDiffOn_tt hc0 k j').contDiffAt (hU.mem_nhds hxm)
      have heq : fderiv ℝ (tt c j) =ᶠ[𝓝 x] fun y : ℝ × ℝ =>
          (-(tt c (j + 2) y)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
            ((j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) •
              ContinuousLinearMap.snd ℝ ℝ ℝ := by
        filter_upwards [hU.mem_nhds hxm] with y hy using fderiv_tt hc0 j hy
      rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ i).self_of_nhds]
      have hg1 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => -(tt c (j + 2) y)) x := (hCD i _).neg
      have hg2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ =>
          (j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) x := by
        have := (hCD i (j - 1)).const_smul (j : ℝ)
        have h2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => 2 * y.1) x := by fun_prop
        exact (contDiffAt_const.mul (hCD i (j - 1))).sub (h2.mul (hCD i (j + 1)))
      have hadd := iteratedFDeriv_add_apply (i := i) (f := fun y : ℝ × ℝ =>
          (-(tt c (j + 2) y)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (g := fun y : ℝ × ℝ => ((j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) •
              ContinuousLinearMap.snd ℝ ℝ ℝ)
        (x := x) (hg1.smul_const _ |>.of_le (by exact_mod_cast le_refl _))
        (hg2.smul_const _ |>.of_le (by exact_mod_cast le_refl _))
      have hKt : ∀ k ≤ i, ∀ j', ‖iteratedFDeriv ℝ k (tt c j') x‖ ≤ Kf k j' :=
        fun k hk j' => hKf k hk j' c hc x hx1 hx2
      have n1 : ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => -(tt c (j + 2) y)) x‖ ≤ Kf i (j + 2) := by
        have := iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := i) (f := tt c (j + 2)) (x := x)
        have e : (fun y : ℝ × ℝ => -(tt c (j + 2) y)) = -tt c (j + 2) := rfl
        rw [e, this, norm_neg]; exact hKt i le_rfl _
      have hA : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => (j : ℝ) * tt c (j - 1) y) x :=
        contDiffAt_const.mul (hCD i _)
      have hP : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => y.1 * tt c (j + 1) y) x :=
        (by fun_prop : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => y.1) x).mul (hCD i _)
      have hB : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => 2 * (y.1 * tt c (j + 1) y)) x :=
        contDiffAt_const.mul hP
      have hx' : |x.1| ≤ 1 := abs_le.2 ⟨by linarith, hx2⟩
      have nP : ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => y.1 * tt c (j + 1) y) x‖ ≤
          ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * M m * Kf (i - m) (j + 1) := by
        refine (leib hc0 (j + 1) i hx0).trans (Finset.sum_le_sum fun m hm => ?_)
        have hm' : m ≤ i := by simpa [Nat.lt_succ_iff] using hm
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hM m x hx') (Nat.cast_nonneg _))
          (hKt (i - m) (by omega) _) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hM0 m))
      have n2 : ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ =>
          (j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) x‖ ≤
          |(j : ℝ)| * Kf i (j - 1) +
            2 * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * M m * Kf (i - m) (j + 1) := by
        have e2 : (fun y : ℝ × ℝ => (j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) =
            (fun y : ℝ × ℝ => (j : ℝ) * tt c (j - 1) y) -
              (fun y : ℝ × ℝ => 2 * (y.1 * tt c (j + 1) y)) := by funext y; simp; ring
        rw [e2, iteratedFDeriv_sub_apply hA hB]
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_iter_cmul _ _ (hCD i _)).trans
            (mul_le_mul_of_nonneg_left (hKt i le_rfl _) (abs_nonneg _))
        · refine (norm_iter_cmul _ _ hP).trans ?_
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left nP (by norm_num)
      change ‖iteratedFDeriv ℝ i ((fun y : ℝ × ℝ => (-(tt c (j + 2) y)) • ContinuousLinearMap.fst ℝ ℝ ℝ) + fun y : ℝ × ℝ => ((j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) • ContinuousLinearMap.snd ℝ ℝ ℝ) x‖ ≤ _
      rw [hadd]
      refine (norm_add_le _ _).trans ?_
      have s1 := norm_iter_smul _ (ContinuousLinearMap.fst ℝ ℝ ℝ) hg1
      have s2 := norm_iter_smul _ (ContinuousLinearMap.snd ℝ ℝ ℝ) hg2
      have f1 : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
      have f2 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
      have t1 : ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => (-(tt c (j + 2) y)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ) x‖ ≤ Kf i (j + 2) := by
        refine s1.trans ?_
        calc _ ≤ 1 * ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => -(tt c (j + 2) y)) x‖ :=
              mul_le_mul_of_nonneg_right f1 (norm_nonneg _)
          _ ≤ _ := by linarith
      have t2 : ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => ((j : ℝ) * tt c (j - 1) y -
          2 * y.1 * tt c (j + 1) y) • ContinuousLinearMap.snd ℝ ℝ ℝ) x‖ ≤
          |(j : ℝ)| * Kf i (j - 1) +
            2 * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * M m * Kf (i - m) (j + 1) := by
        refine s2.trans ?_
        calc _ ≤ 1 * ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ => (j : ℝ) * tt c (j - 1) y -
              2 * y.1 * tt c (j + 1) y) x‖ :=
              mul_le_mul_of_nonneg_right f2 (norm_nonneg _)
          _ ≤ _ := by linarith
      linarith
  exact key i i le_rfl j

end UnforcedLeray.Short.PartIIIb.Concrete
