import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Gop

/-!
# Jet sums and the one-step estimate (`PartIII-b:C/rep/8/2/1/3/b`, helper 2)

`J n F z = Σ_{k ≤ n} ‖D^k F z‖`; `J n (Gop … F) z ≤ (|a|+|b|+|c|+|d|(|η|+n)+|e|) J (n+1) F z`
(Leibniz for the coordinate `η`, whose derivatives of order `≥ 2` vanish).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jet sum `Σ_{k ≤ n} ‖D^k F z‖`. -/
def J (n : ℕ) (F : Zc → E) (z : Zc) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k F z‖

theorem J_nonneg (n : ℕ) (F : Zc → E) (z : Zc) : 0 ≤ J n F z :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_le_J (n : ℕ) (F : Zc → E) (z : Zc) : ‖F z‖ ≤ J n F z := by
  unfold J
  have h := Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k F z‖)
    (fun k _ => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos n))
  simpa [norm_iteratedFDeriv_zero] using h

theorem norm_iter_le_J {n k : ℕ} (hk : k ≤ n) (F : Zc → E) (z : Zc) :
    ‖iteratedFDeriv ℝ k F z‖ ≤ J n F z := by
  unfold J
  exact Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k F z‖)
    (fun k _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

theorem J_mono {n m : ℕ} (h : n ≤ m) (F : Zc → E) (z : Zc) : J n F z ≤ J m F z := by
  unfold J
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (Nat.succ_le_succ h)) (fun _ _ _ => norm_nonneg _)

theorem J_add_le (n : ℕ) {F G : Zc → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (z : Zc) :
    J n (fun z => F z + G z) z ≤ J n F z + J n G z := by
  unfold J
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [fun_iteratedFDeriv_add_apply (hF.contDiffAt.of_le (by simp)) (hG.contDiffAt.of_le (by simp))]
  exact norm_add_le _ _

theorem J_smul (n : ℕ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (c : ℝ) (z : Zc) :
    J n (fun z => c • F z) z = |c| * J n F z := by
  unfold J
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_const_smul_apply' (hF.contDiffAt.of_le (by simp)), norm_smul, Real.norm_eq_abs]

theorem J_dir (n : ℕ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (d : Zc) (z : Zc) :
    J n (fun z => fderiv ℝ F z d) z ≤ ‖d‖ * J (n + 1) F z := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hk : ∀ k : ℕ, ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ F z d) z‖ ≤
      ‖d‖ * ‖iteratedFDeriv ℝ (k + 1) F z‖ := by
    intro k
    refine (norm_iteratedFDeriv_clm_apply_const (c := d) (N := ∞) h1.contDiffAt (by simp)).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
  unfold J
  calc ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ F z d) z‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖d‖ * ‖iteratedFDeriv ℝ (k + 1) F z‖ :=
        Finset.sum_le_sum fun k _ => hk k
    _ = ‖d‖ * ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ (k + 1) F z‖ := by
        rw [Finset.mul_sum]
    _ ≤ ‖d‖ * ∑ k ∈ Finset.range (n + 1 + 1), ‖iteratedFDeriv ℝ k F z‖ := by
        gcongr
        rw [Finset.sum_range_succ' (fun k => ‖iteratedFDeriv ℝ k F z‖) (n + 1)]
        exact le_add_of_nonneg_right (norm_nonneg _)

end

/-! ### Derivatives of the coordinate `η` -/

theorem norm_iter_eta_zero (z : Zc) : ‖iteratedFDeriv ℝ 0 (fun z : Zc => z.2.2) z‖ = |z.2.2| := by
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]

theorem norm_iter_eta_one (z : Zc) : ‖iteratedFDeriv ℝ 1 (fun z : Zc => z.2.2) z‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one]
  have hL : HasFDerivAt (fun z : Zc => z.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) z :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  rw [hL.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  have h2 : ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  nlinarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ ℝ),
    norm_nonneg (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]

theorem norm_iter_eta_two (m : ℕ) (z : Zc) :
    ‖iteratedFDeriv ℝ (m + 2) (fun z : Zc => z.2.2) z‖ = 0 := by
  have hL : ∀ z : Zc, HasFDerivAt (fun z : Zc => z.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) z := fun z =>
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hf : fderiv ℝ (fun z : Zc => z.2.2) = fun _ =>
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) :=
    funext fun z => (hL z).fderiv
  rw [← norm_iteratedFDeriv_fderiv (n := m + 1), hf, iteratedFDeriv_const_of_ne (by omega)]
  simp

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iter_eta_smul_le {F : Zc → E} (hF : ContDiff ℝ ∞ F) (k : ℕ) (z : Zc) :
    ‖iteratedFDeriv ℝ k (fun z => z.2.2 • F z) z‖ ≤
      |z.2.2| * ‖iteratedFDeriv ℝ k F z‖ + (k : ℝ) * ‖iteratedFDeriv ℝ (k - 1) F z‖ := by
  have hη : ContDiff ℝ ∞ (fun z : Zc => z.2.2) := contDiff_snd.comp contDiff_snd
  have h := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := ∞) hη hF z (n := k) (by simp)
  refine h.trans ?_
  cases k with
  | zero =>
    simp [norm_iter_eta_zero]
  | succ m =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1 + 1) : ℝ) *
        ‖iteratedFDeriv ℝ (i + 1 + 1) (fun z : Zc => z.2.2) z‖ *
          ‖iteratedFDeriv ℝ (m + 1 - (i + 1 + 1)) F z‖ = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have := norm_iter_eta_two i z
      rw [show i + 1 + 1 = i + 2 from rfl, this]
      simp
    rw [hz, zero_add]
    have h1 := norm_iter_eta_one z
    have h0 := norm_iter_eta_zero z
    have e1 : ((m + 1).choose (0 + 1) : ℝ) = (m : ℝ) + 1 := by simp
    have e0 : ((m + 1).choose 0 : ℝ) = 1 := by simp
    have e2 : m + 1 - (0 + 1) = m := by omega
    rw [e1, e0, e2, h0, Nat.sub_zero]
    have hn : 0 ≤ ‖iteratedFDeriv ℝ m F z‖ := norm_nonneg _
    have : ((m : ℝ) + 1) * ‖iteratedFDeriv ℝ (0 + 1) (fun z : Zc => z.2.2) z‖ ≤ ((m : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right this hn]

theorem J_eta_smul (n : ℕ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    J n (fun z => z.2.2 • F z) z ≤ (|z.2.2| + n) * J n F z := by
  unfold J
  have h1 : ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (fun z => z.2.2 • F z) z‖ ≤
      ∑ k ∈ Finset.range (n + 1), (|z.2.2| * ‖iteratedFDeriv ℝ k F z‖ +
        (k : ℝ) * ‖iteratedFDeriv ℝ (k - 1) F z‖) :=
    Finset.sum_le_sum fun k _ => norm_iter_eta_smul_le hF k z
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_mul]
  refine add_le_add le_rfl ?_
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  calc ∑ k ∈ Finset.range n, ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ k F z‖
      ≤ ∑ k ∈ Finset.range n, (n : ℝ) * ‖iteratedFDeriv ℝ k F z‖ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have : (k : ℝ) + 1 ≤ n := by
          have := Finset.mem_range.1 hk
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = (n : ℝ) * ∑ k ∈ Finset.range n, ‖iteratedFDeriv ℝ k F z‖ := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) * ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k F z‖ := by
        gcongr
        exact Nat.le_succ n

theorem norm_dir_one (a b c : ℝ) (h : (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 1)) : ‖((a, (b, c)) : Zc)‖ = 1 := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [Prod.norm_def]

theorem J_add5 (n : ℕ) {f1 f2 f3 f4 f5 : Zc → E} (h1 : ContDiff ℝ ∞ f1) (h2 : ContDiff ℝ ∞ f2)
    (h3 : ContDiff ℝ ∞ f3) (h4 : ContDiff ℝ ∞ f4) (h5 : ContDiff ℝ ∞ f5) (z : Zc) :
    J n (fun z => f1 z + f2 z + f3 z + f4 z + f5 z) z ≤
      J n f1 z + J n f2 z + J n f3 z + J n f4 z + J n f5 z := by
  have h12 : ContDiff ℝ ∞ (fun z => f1 z + f2 z) := h1.add h2
  have h123 : ContDiff ℝ ∞ (fun z => f1 z + f2 z + f3 z) := h12.add h3
  have h1234 : ContDiff ℝ ∞ (fun z => f1 z + f2 z + f3 z + f4 z) := h123.add h4
  have e1 := J_add_le n h1234 h5 z
  have e2 := J_add_le n h123 h4 z
  have e3 := J_add_le n h12 h3 z
  have e4 := J_add_le n h1 h2 z
  linarith

/-- **One-step jet estimate.** -/
theorem J_Gop (a b c d e : ℝ) (n : ℕ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    J n (Gop a b c d e F) z ≤
      (|a| + |b| + |c| + |d| * (|z.2.2| + n) + |e|) * J (n + 1) F z := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hq : ContDiff ℝ ∞ (fun z => fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) :=
    h1.clm_apply contDiff_const
  have hs : ContDiff ℝ ∞ (fun z => fderiv ℝ F z ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) :=
    h1.clm_apply contDiff_const
  have he : ContDiff ℝ ∞ (fun z => fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) :=
    h1.clm_apply contDiff_const
  have hη : ContDiff ℝ ∞ (fun z : Zc => z.2.2) := contDiff_snd.comp contDiff_snd
  have hJq := J_dir n hF ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) z
  have hJs := J_dir n hF ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) z
  have hJe := J_dir n hF ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) z
  rw [norm_dir_one _ _ _ (by simp)] at hJq hJs hJe
  have hJF := J_mono (Nat.le_succ n) F z
  have hnn := J_nonneg (n + 1) F z
  have hη' : ContDiff ℝ ∞ (fun z : Zc => z.2.2 • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) :=
    hη.smul he
  have hEq : Gop a b c d e F = fun z =>
      a • fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) + b • fderiv ℝ F z ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
        c • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) +
        d • (z.2.2 • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) + e • F z := by
    funext z
    simp only [Gop]
    module
  rw [hEq]
  have ca : ContDiff ℝ ∞ (fun z : Zc => a • fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) :=
    contDiff_const.smul hq
  have cb : ContDiff ℝ ∞ (fun z : Zc => b • fderiv ℝ F z ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) :=
    contDiff_const.smul hs
  have cc : ContDiff ℝ ∞ (fun z : Zc => c • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) :=
    contDiff_const.smul he
  have cd : ContDiff ℝ ∞ (fun z : Zc =>
      d • (z.2.2 • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) := contDiff_const.smul hη'
  have ce : ContDiff ℝ ∞ (fun z : Zc => e • F z) := contDiff_const.smul hF
  have hS := J_add5 n ca cb cc cd ce z
  have hA := J_smul n hq a z
  have hB := J_smul n hs b z
  have hC := J_smul n he c z
  have hD := J_smul n hη' d z
  have hD2 := J_eta_smul n he z
  have hE := J_smul n hF e z
  have hJeF : J n (fun z => fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) z ≤ J (n + 1) F z := by
    simpa using hJe
  have hJqF : J n (fun z => fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) z ≤ J (n + 1) F z := by
    simpa using hJq
  have hJsF : J n (fun z => fderiv ℝ F z ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) z ≤ J (n + 1) F z := by
    simpa using hJs
  have hJηe : J n (fun z => z.2.2 • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) z ≤
      (|z.2.2| + n) * J (n + 1) F z :=
    hD2.trans (mul_le_mul_of_nonneg_left hJeF (by positivity))
  have t1 : |a| * J n (fun z => fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) z ≤ |a| * J (n + 1) F z :=
    mul_le_mul_of_nonneg_left hJqF (abs_nonneg _)
  have t2 : |b| * J n (fun z => fderiv ℝ F z ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) z ≤ |b| * J (n + 1) F z :=
    mul_le_mul_of_nonneg_left hJsF (abs_nonneg _)
  have t3 : |c| * J n (fun z => fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) z ≤ |c| * J (n + 1) F z :=
    mul_le_mul_of_nonneg_left hJeF (abs_nonneg _)
  have t4 : |d| * J n (fun z => z.2.2 • fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) z ≤
      |d| * ((|z.2.2| + n) * J (n + 1) F z) :=
    mul_le_mul_of_nonneg_left hJηe (abs_nonneg _)
  have t5 : |e| * J n F z ≤ |e| * J (n + 1) F z :=
    mul_le_mul_of_nonneg_left hJF (abs_nonneg _)
  nlinarith [hA, hB, hC, hD, hE, hS]

end

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
