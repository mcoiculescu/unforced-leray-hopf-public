import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.PcEnv_Aux

/-!
# Composed theta-sum jet bound for `PartI:T25/3/1`

Source of record: `the November 2 reference manuscript`, lines 468–478, 543–551,
4963–4968.

Adapts `TtJet.lean` and `TtComp.lean` to arbitrary slow-age horizon `0 < s ≤ Sg / ν` (`Sg > 0`,
`0 < ν ≤ 1`) and period condition `0 < c`, `1 + Sg ≤ c ^ 2`, where
`u = (2 * (1 + ν * s))⁻¹ ∈ [(2 * (1 + Sg))⁻¹, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.VelAgeJetAux.PcTwoMulMAux
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartI.VelAgeJetAux

open UnforcedLeray.Cyl (Plane)

/-! ### 1. Derivatives of `IIb.tt c j` on `(2 * (1 + Sg))⁻¹ ≤ x.1 ≤ 1` when `1 + Sg ≤ c ^ 2` -/

/-- Base (`i = 0`) uniform bound for `IIb.tt c j x` on `(2 * (1 + Sg))⁻¹ ≤ x.1 ≤ 1` when `1 + Sg ≤ c ^ 2`. -/
lemma tt_base_sg (Sg : ℝ) (hSg : 0 < Sg) (j : ℕ) :
    ∃ A : ℝ, ∀ c : ℝ, 0 < c → 1 + Sg ≤ c ^ 2 →
      ∀ x : ℝ × ℝ, (2 * (1 + Sg))⁻¹ ≤ x.1 → x.1 ≤ 1 →
        ‖UnforcedLeray.Short.IIb.tt c j x‖ ≤ A := by
  have ha : 0 < 1 + Sg := by positivity
  obtain ⟨C, hC, h⟩ :=
    UnforcedLeray.Short.IIb.gauss_poly_le j (m := (4 * (1 + Sg))⁻¹) (by positivity)
  refine ⟨10 * C, fun c _hc hac x hx1 _hx2 => ?_⟩
  have hs := UnforcedLeray.Gaussian.summable_gauss_shift ha hac x.2
  have hb := UnforcedLeray.Gaussian.tsum_gauss_shift_le ha hac x.2
  have hterm : ∀ n : ℤ, ‖UnforcedLeray.Short.IIb.ttTerm c j n x‖ ≤
      C * Real.exp (-(x.2 - n * c) ^ 2 / (4 * (1 + Sg))) := by
    intro n
    rw [UnforcedLeray.Short.IIb.norm_ttTerm]
    set t := x.2 - n * c
    have h1 := h t
    have h2 : (1 + |t|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    have h3 : Real.exp (-x.1 * t ^ 2) ≤ Real.exp (-(2 * (1 + Sg))⁻¹ * t ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg t])
    have e : Real.exp (-(2 * (1 + Sg))⁻¹ * t ^ 2) =
        Real.exp (-((4 * (1 + Sg))⁻¹ * t ^ 2)) * Real.exp (-t ^ 2 / (4 * (1 + Sg))) := by
      rw [← Real.exp_add]; congr 1
      have ha_ne : 1 + Sg ≠ 0 := ha.ne'
      field_simp
      ring
    have h4 : |t| ^ j * Real.exp (-((4 * (1 + Sg))⁻¹ * t ^ 2)) ≤ C := by
      calc _ ≤ C * (1 + |t|) ^ (-2 : ℝ) := h1
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 hC.le
        _ = C := mul_one C
    calc |t| ^ j * Real.exp (-x.1 * t ^ 2) ≤ |t| ^ j * Real.exp (-(2 * (1 + Sg))⁻¹ * t ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (|t| ^ j * Real.exp (-((4 * (1 + Sg))⁻¹ * t ^ 2))) *
            Real.exp (-t ^ 2 / (4 * (1 + Sg))) := by
          rw [e]; ring
      _ ≤ C * Real.exp (-t ^ 2 / (4 * (1 + Sg))) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
  have hm : Summable fun n : ℤ => C * Real.exp (-(x.2 - n * c) ^ 2 / (4 * (1 + Sg))) :=
    hs.mul_left C
  have hn : Summable fun n : ℤ => ‖UnforcedLeray.Short.IIb.ttTerm c j n x‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hm
  unfold UnforcedLeray.Short.IIb.tt
  refine (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hterm hm).trans ?_)
  rw [tsum_mul_left]
  nlinarith [hb]

/-- `fst` is smooth with bounded derivatives on `|x.1| ≤ 1`. -/
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
      ∑ m ∈ Finset.range (i + 1),
        (i.choose m : ℝ) * ‖iteratedFDeriv ℝ m (fun y : ℝ × ℝ => y.1) x‖ *
          ‖iteratedFDeriv ℝ (i - m) (tt c j) x‖ := by
  have hU : IsOpen {x : ℝ × ℝ | 0 < x.1} := isOpen_lt continuous_const continuous_fst
  have h := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := fun y : ℝ × ℝ => y.1) (g := tt c j)
    (s := {x : ℝ × ℝ | 0 < x.1}) (N := (i : WithTop ℕ∞))
    contDiff_fst.contDiffOn (contDiffOn_tt hc i j) hU.uniqueDiffOn hx (le_refl _)
  have e : ∀ n (f : ℝ × ℝ → ℝ), iteratedFDerivWithin ℝ n f {x : ℝ × ℝ | 0 < x.1} x =
      iteratedFDeriv ℝ n f x := fun n f => iteratedFDerivWithin_of_isOpen n hU hx
  simp only [e] at h
  exact h

open UnforcedLeray.Short.IIb in
/-- Uniform derivative bound for `IIb.tt c j` on `(2 * (1 + Sg))⁻¹ ≤ x.1 ≤ 1` when `0 < c` and
`1 + Sg ≤ c ^ 2`. -/
theorem ttJetBoundSg (Sg : ℝ) (hSg : 0 < Sg) (i j : ℕ) :
    ∃ K : ℝ, ∀ c : ℝ, 0 < c → 1 + Sg ≤ c ^ 2 →
      ∀ x : ℝ × ℝ, (2 * (1 + Sg))⁻¹ ≤ x.1 → x.1 ≤ 1 →
        ‖iteratedFDeriv ℝ i (tt c j) x‖ ≤ K := by
  have hlow_pos : 0 < (2 * (1 + Sg))⁻¹ := by positivity
  have key : ∀ i : ℕ, ∀ k ≤ i, ∀ j : ℕ, ∃ K : ℝ, ∀ c : ℝ, 0 < c → 1 + Sg ≤ c ^ 2 →
      ∀ x : ℝ × ℝ, (2 * (1 + Sg))⁻¹ ≤ x.1 → x.1 ≤ 1 →
        ‖iteratedFDeriv ℝ k (tt c j) x‖ ≤ K := by
    intro i
    induction i with
    | zero =>
      intro k hk j
      obtain rfl : k = 0 := by omega
      obtain ⟨A, hA⟩ := tt_base_sg Sg hSg j
      exact ⟨A, fun c hc hac x h1 h2 =>
        by simpa [norm_iteratedFDeriv_zero] using hA c hc hac x h1 h2⟩
    | succ i ih =>
      intro k hk j
      rcases Nat.lt_or_ge k (i + 1) with hlt | hge
      · exact ih k (by omega) j
      obtain rfl : k = i + 1 := by omega
      choose! Kf hKf using ih
      choose! M hM0 hM using fst_iter
      refine ⟨Kf i (j + 2) + |(j : ℝ)| * Kf i (j - 1) + 2 *
        ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * M m * Kf (i - m) (j + 1), ?_⟩
      intro c hc hac x hx1 hx2
      have hc0 : c ≠ 0 := hc.ne'
      have hU : IsOpen {x : ℝ × ℝ | 0 < x.1} := isOpen_lt continuous_const continuous_fst
      have hx0 : 0 < x.1 := hlow_pos.trans_le hx1
      have hxm : x ∈ {x : ℝ × ℝ | 0 < x.1} := hx0
      have hCD : ∀ (k j' : ℕ), ContDiffAt ℝ (k : WithTop ℕ∞) (tt c j') x := fun k j' =>
        (contDiffOn_tt hc0 k j').contDiffAt (hU.mem_nhds hxm)
      have heq : fderiv ℝ (tt c j) =ᶠ[𝓝 x] fun y : ℝ × ℝ =>
          (-(tt c (j + 2) y)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
            ((j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) •
              ContinuousLinearMap.snd ℝ ℝ ℝ := by
        filter_upwards [hU.mem_nhds hxm] with y hy using fderiv_tt hc0 j hy
      rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ i).self_of_nhds]
      have hg1 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => -(tt c (j + 2) y)) x :=
        (hCD i _).neg
      have hg2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ =>
          (j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) x := by
        have h2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y : ℝ × ℝ => 2 * y.1) x := by fun_prop
        exact (contDiffAt_const.mul (hCD i (j - 1))).sub (h2.mul (hCD i (j + 1)))
      have hadd := iteratedFDeriv_add_apply (i := i) (f := fun y : ℝ × ℝ =>
          (-(tt c (j + 2) y)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (g := fun y : ℝ × ℝ => ((j : ℝ) * tt c (j - 1) y - 2 * y.1 * tt c (j + 1) y) •
              ContinuousLinearMap.snd ℝ ℝ ℝ)
        (x := x) (hg1.smul_const _ |>.of_le (by exact_mod_cast le_refl _))
        (hg2.smul_const _ |>.of_le (by exact_mod_cast le_refl _))
      have hKt : ∀ k ≤ i, ∀ j', ‖iteratedFDeriv ℝ k (tt c j') x‖ ≤ Kf k j' :=
        fun k hk j' => hKf k hk j' c hc hac x hx1 hx2
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
      change ‖iteratedFDeriv ℝ i ((fun y : ℝ × ℝ => (-(tt c (j + 2) y)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ) + fun y : ℝ × ℝ => ((j : ℝ) * tt c (j - 1) y -
        2 * y.1 * tt c (j + 1) y) • ContinuousLinearMap.snd ℝ ℝ ℝ) x‖ ≤ _
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

/-! ### 2. Composed theta jet bound on `0 < s ≤ Sg / ν` -/

/-- Norm of the `i`-th derivative (`i ≥ 1`) of a continuous linear functional is at most its norm. -/
lemma ttcClmIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (i : ℕ)
    (hi : 1 ≤ i) (x : E) : ‖iteratedFDeriv ℝ i L x‖ ≤ ‖L‖ := by
  rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | h2
  · rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ L = fun _ => L := funext fun y => ContinuousLinearMap.fderiv L
    rw [hfd, iteratedFDeriv_succ_const]
    simp

/-- The inner map `x ↦ (2(1+νx.1))⁻¹` is smooth on `pcUfst`. -/
lemma ttcInnerCDO (ν : ℝ) (hν0 : 0 ≤ ν) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) pcUfst := by
  have hfun : (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) =
      fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹ := by
    funext x
    rw [pow_one, mul_inv]
    ring
  rw [hfun]
  exact pcAffCDO ν hν0 (1 / 2) 1

/-- The inner first component: `i`-th derivative bound. -/
lemma ttcInnerBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n i : ℕ) (hi : i ≤ n)
    (y : ℝ × Plane) (hy : y ∈ pcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) pcUfst y‖
      ≤ ((n : ℝ) + 1) ^ i := by
  have hfun : (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) =
      fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹ := by
    funext x
    rw [pow_one, mul_inv]
    ring
  rw [hfun]
  simpa using pcAffJetBound ν hν0 hν1 (1 / 2) (by norm_num) 1 n i hi y hy

/-- The second component `x ↦ x.2.1`: derivative bound by `1`. -/
lemma ttcSndBound (i : ℕ) (hi : 1 ≤ i) (y : ℝ × Plane) (hy : y ∈ pcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => x.2.1) pcUfst y‖ ≤ 1 := by
  set L : ℝ × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)
  have hL : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
    have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ Plane
    have h3 : (0 : ℝ) ≤ ‖(ContinuousLinearMap.snd ℝ ℝ Plane : ℝ × Plane →L[ℝ] Plane)‖ :=
      norm_nonneg _
    nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ ℝ : Plane →L[ℝ] ℝ)]
  show ‖iteratedFDerivWithin ℝ i (⇑L) pcUfst y‖ ≤ 1
  rw [(iteratedFDerivWithin_of_isOpen i pcIsOpenUfst) hy]
  exact (ttcClmIter L i hi y).trans hL

/-- The pair map `φ(x) = ((2(1+νx.1))⁻¹, x.2.1)`: derivative bound by `(n+1)^i`. -/
lemma ttcPairBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ n)
    (y : ℝ × Plane) (hy : y ∈ pcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) pcUfst y‖
      ≤ ((n : ℝ) + 1) ^ i := by
  have hc1 : ContDiffWithinAt ℝ ∞ (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) pcUfst y :=
    (ttcInnerCDO ν hν0).contDiffWithinAt hy
  have hc2 : ContDiffWithinAt ℝ ∞ (fun x : ℝ × Plane => x.2.1) pcUfst y :=
    (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => x.2.1)).contDiffWithinAt
  have hsplit : iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      pcUfst y
      = (iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) pcUfst y).prod
        (iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => x.2.1) pcUfst y) :=
    iteratedFDerivWithin_prodMk hc1 hc2 pcIsOpenUfst.uniqueDiffOn hy
      (show (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
  rw [hsplit, ContinuousMultilinearMap.opNorm_prod]
  have hP := ttcInnerBound ν hν0 hν1 n i hi y hy
  have hQ := ttcSndBound i hi1 y hy
  have hone : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ i :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact max_le hP (hQ.trans hone)

/-- **Composed theta jet bound on `0 < s ≤ Sg / ν`**: the joint derivatives of
`(s, q, η) ↦ IIb.tt c 0 ((2(1+νs))⁻¹, q)` on `0 < s ≤ Sg / ν` are bounded uniformly in
`0 < ν ≤ 1` and `0 < c` with `1 + Sg ≤ c ^ 2`. -/
theorem ttCompJetSg (Sg : ℝ) (hSg : 0 < Sg) (n : ℕ) :
    ∃ KT : ℝ, 0 ≤ KT ∧
      ∀ ν c : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 1 + Sg ≤ c ^ 2 →
        ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ Sg / ν →
          ‖iteratedFDeriv ℝ n
            (fun x : ℝ × Plane =>
              UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) y‖ ≤ KT := by
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ c : ℝ, 0 < c → 1 + Sg ≤ c ^ 2 →
      ∀ x : ℝ × ℝ, (2 * (1 + Sg))⁻¹ ≤ x.1 → x.1 ≤ 1 →
        ‖iteratedFDeriv ℝ i (UnforcedLeray.Short.IIb.tt c 0) x‖ ≤ K :=
    fun i => ttJetBoundSg Sg hSg i 0
  choose K hK using hK
  refine ⟨(n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), |K i|) * ((n : ℝ) + 1) ^ n,
    by positivity, ?_⟩
  intro ν c hν0 hν1 hc hac y hy0 hy1
  have hν0' : (0 : ℝ) ≤ ν := hν0.le
  have hy : y ∈ pcUfst := hy0
  set C : ℝ := ∑ i ∈ Finset.range (n + 1), |K i|
  have hTopen : IsOpen {x : ℝ × ℝ | 0 < x.1} :=
    isOpen_lt continuous_const continuous_fst
  have hG : ContDiffOn ℝ ∞ (UnforcedLeray.Short.IIb.tt c 0) {x : ℝ × ℝ | 0 < x.1} :=
    UnforcedLeray.Short.IIb.contDiffOn_tt_infty hc.ne' 0
  have hφC : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) pcUfst :=
    (ttcInnerCDO ν hν0').prodMk
      (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => x.2.1)).contDiffOn
  have hMaps : Set.MapsTo (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) pcUfst
      {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx
    have hx' : (0 : ℝ) < x.1 := hx
    show (0 : ℝ) < (2 * (1 + ν * x.1))⁻¹
    have := mul_nonneg hν0' hx'.le
    exact inv_pos.mpr (by linarith)
  have hνy : ν * y.1 ≤ Sg := by
    have := (le_div_iff₀ hν0).mp hy1
    linarith
  have hφy1 : (2 * (1 + Sg))⁻¹ ≤ ((2 * (1 + ν * y.1))⁻¹ : ℝ) := by
    have hpos : (0 : ℝ) < 2 * (1 + ν * y.1) := by
      have := mul_nonneg hν0' hy0.le
      linarith
    exact inv_anti₀ hpos (by linarith)
  have hφy2 : ((2 * (1 + ν * y.1))⁻¹ : ℝ) ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have := mul_nonneg hν0' hy0.le
    linarith
  have hφy : (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) y ∈ {x : ℝ × ℝ | 0 < x.1} :=
    hMaps hy
  have hCi : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i (UnforcedLeray.Short.IIb.tt c 0)
      {x : ℝ × ℝ | 0 < x.1} ((fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) y)‖ ≤ C := by
    intro i _hi
    rw [(iteratedFDerivWithin_of_isOpen i hTopen) hφy]
    have hb := hK i c hc hac ((2 * (1 + ν * y.1))⁻¹, y.2.1) hφy1 hφy2
    have hsum : |K i| ≤ C :=
      Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have := le_abs_self (K i)
    linarith
  have hout := norm_iteratedFDerivWithin_comp_le (N := ∞) (n := n) (C := C)
    (D := (n : ℝ) + 1) hG hφC
    (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
    hTopen.uniqueDiffOn pcIsOpenUfst.uniqueDiffOn hMaps hy hCi
    (fun i hi1 hi => ttcPairBound ν hν0' hν1 n i hi1 hi y hy)
  rw [← (iteratedFDerivWithin_of_isOpen n pcIsOpenUfst) hy]
  exact hout

end UnforcedLeray.Short.PartI.VelAgeJetAux.PcTwoMulMAux

end
