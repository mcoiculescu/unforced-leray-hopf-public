import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2

/-!
# Part II-b, task `PartII-b:T13/1/4/2/1` (`ChmCutoffExists`)

Source `the November 2 reference manuscript` lines 1933-1935. The cutoff is
`ζ(q) = ψ(-q/c) ψ(q/c - N)` with `ψ = 1 - Real.smoothTransition`, so `ζ = 1` on `[0, N c]` and
`ζ = 0` outside `(-c, (N+1) c)`; derivative bounds scale with `1/c` and `1/c²`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace ChmCutoff

/-- `1` on `(-∞, 0]`, `0` on `[1, ∞)`. -/
def cutPsi (t : ℝ) : ℝ := 1 - Real.smoothTransition t

lemma cutPsi_contDiff : ContDiff ℝ ∞ cutPsi := contDiff_const.sub Real.smoothTransition.contDiff

lemma cutPsi_eq_one {t : ℝ} (h : t ≤ 0) : cutPsi t = 1 := by
  unfold cutPsi; rw [Real.smoothTransition.zero_of_nonpos h]; ring

lemma cutPsi_eq_zero {t : ℝ} (h : 1 ≤ t) : cutPsi t = 0 := by
  unfold cutPsi; rw [Real.smoothTransition.one_of_one_le h]; ring

lemma cutPsi_mem (t : ℝ) : 0 ≤ cutPsi t ∧ cutPsi t ≤ 1 := by
  unfold cutPsi
  constructor
  · linarith [Real.smoothTransition.le_one t]
  · linarith [Real.smoothTransition.nonneg t]

lemma cutPsi_diff : Differentiable ℝ cutPsi := (contDiff_infty_iff_deriv.1 cutPsi_contDiff).1

lemma dcutPsi_contDiff : ContDiff ℝ ∞ (deriv cutPsi) := (contDiff_infty_iff_deriv.1 cutPsi_contDiff).2

lemma dcutPsi_diff : Differentiable ℝ (deriv cutPsi) := (contDiff_infty_iff_deriv.1 dcutPsi_contDiff).1

lemma dcutPsi_cont : Continuous (deriv cutPsi) := dcutPsi_contDiff.continuous

lemma ddcutPsi_cont : Continuous (deriv (deriv cutPsi)) :=
  (contDiff_infty_iff_deriv.1 dcutPsi_contDiff).2.continuous

lemma dcutPsi_zero_of_not_mem {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : deriv cutPsi t = 0 := by
  by_cases h0 : t < 0
  · have hev : cutPsi =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h0] with y hy
      exact cutPsi_eq_one (le_of_lt hy)
    rw [hev.deriv_eq, deriv_const]
  · have h1 : 1 < t := by
      by_contra hc
      exact ht ⟨not_lt.1 h0, not_lt.1 hc⟩
    have hev : cutPsi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact cutPsi_eq_zero (le_of_lt hy)
    rw [hev.deriv_eq, deriv_const]

lemma dcutPsi_hcs : HasCompactSupport (deriv cutPsi) :=
  HasCompactSupport.intro isCompact_Icc (fun _ ht => dcutPsi_zero_of_not_mem ht)

lemma ddcutPsi_zero_of_not_mem {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : deriv (deriv cutPsi) t = 0 := by
  have hev : deriv cutPsi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with y hy
    exact dcutPsi_zero_of_not_mem hy
  rw [hev.deriv_eq, deriv_const]

lemma ddcutPsi_hcs : HasCompactSupport (deriv (deriv cutPsi)) :=
  HasCompactSupport.intro isCompact_Icc (fun _ ht => ddcutPsi_zero_of_not_mem ht)

lemma cutPsi_bounds : ∃ M : ℝ, 1 ≤ M ∧ (∀ t, |deriv cutPsi t| ≤ M) ∧
    (∀ t, |deriv (deriv cutPsi) t| ≤ M) := by
  obtain ⟨A, hA⟩ := dcutPsi_cont.bounded_above_of_compact_support dcutPsi_hcs
  obtain ⟨B, hB⟩ := ddcutPsi_cont.bounded_above_of_compact_support ddcutPsi_hcs
  refine ⟨|A| + |B| + 1, by linarith [abs_nonneg A, abs_nonneg B], fun t => ?_, fun t => ?_⟩
  · have := hA t
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self A, abs_nonneg B]
  · have := hB t
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self B, abs_nonneg A]

lemma contDiff_cutPsi_affine (a p : ℝ) : ContDiff ℝ ∞ (fun y : ℝ => cutPsi (a * y + p)) :=
  cutPsi_contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

lemma hasDerivAt_cutPsi (a p x : ℝ) :
    HasDerivAt (fun y => cutPsi (a * y + p)) (deriv cutPsi (a * x + p) * a) x := by
  have h1 : HasDerivAt (fun y => a * y + p) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const p
  have h2 : HasDerivAt cutPsi (deriv cutPsi (a * x + p)) (a * x + p) :=
    (cutPsi_diff (a * x + p)).hasDerivAt
  have h3 := h2.comp x h1
  exact h3

lemma hasDerivAt_dcutPsi (a p x : ℝ) :
    HasDerivAt (fun y => deriv cutPsi (a * y + p)) (deriv (deriv cutPsi) (a * x + p) * a) x := by
  have h1 : HasDerivAt (fun y => a * y + p) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const p
  have h2 : HasDerivAt (deriv cutPsi) (deriv (deriv cutPsi) (a * x + p)) (a * x + p) :=
    (dcutPsi_diff (a * x + p)).hasDerivAt
  have h3 := h2.comp x h1
  exact h3

lemma cut_hasDerivAt1 (a b p q x : ℝ) :
    HasDerivAt (fun y => cutPsi (a * y + p) * cutPsi (b * y + q))
      (deriv cutPsi (a * x + p) * a * cutPsi (b * x + q) +
        cutPsi (a * x + p) * (deriv cutPsi (b * x + q) * b)) x :=
  (hasDerivAt_cutPsi a p x).mul (hasDerivAt_cutPsi b q x)

lemma cut_hasDerivAt2 (a b p q x : ℝ) :
    HasDerivAt
      (fun y => deriv cutPsi (a * y + p) * a * cutPsi (b * y + q) +
        cutPsi (a * y + p) * (deriv cutPsi (b * y + q) * b))
      (deriv (deriv cutPsi) (a * x + p) * a * a * cutPsi (b * x + q) +
        deriv cutPsi (a * x + p) * a * (deriv cutPsi (b * x + q) * b) +
        (deriv cutPsi (a * x + p) * a * (deriv cutPsi (b * x + q) * b) +
          cutPsi (a * x + p) * (deriv (deriv cutPsi) (b * x + q) * b * b))) x := by
  have t1 : HasDerivAt (fun y => deriv cutPsi (a * y + p) * a * cutPsi (b * y + q))
      (deriv (deriv cutPsi) (a * x + p) * a * a * cutPsi (b * x + q) +
        deriv cutPsi (a * x + p) * a * (deriv cutPsi (b * x + q) * b)) x :=
    ((hasDerivAt_dcutPsi a p x).mul_const a).mul (hasDerivAt_cutPsi b q x)
  have t2 : HasDerivAt (fun y => cutPsi (a * y + p) * (deriv cutPsi (b * y + q) * b))
      (deriv cutPsi (a * x + p) * a * (deriv cutPsi (b * x + q) * b) +
        cutPsi (a * x + p) * (deriv (deriv cutPsi) (b * x + q) * b * b)) x :=
    (hasDerivAt_cutPsi a p x).mul ((hasDerivAt_dcutPsi b q x).mul_const b)
  exact t1.add t2

lemma abs_mul_le' {x y B C : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ C) (hB : 0 ≤ B) :
    |x * y| ≤ B * C := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hB

lemma abs_cutPsi_le (t : ℝ) : |cutPsi t| ≤ 1 := by
  rw [abs_of_nonneg (cutPsi_mem t).1]; exact (cutPsi_mem t).2

lemma cut_bound (c : ℝ) (hc : 0 < c) (N : ℕ) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ t, |deriv cutPsi t| ≤ M) (hM2 : ∀ t, |deriv (deriv cutPsi) t| ≤ M) :
    IsChmCut (2 * M + 2 * M * M) c N
      (fun x => cutPsi (-(1 / c) * x + 0) * cutPsi ((1 / c) * x + -(N : ℝ))) := by
  have hu : (0 : ℝ) < 1 / c := by positivity
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hau : |-(1 / c)| ≤ 1 / c := (abs_neg _).le.trans (le_of_eq (abs_of_pos hu))
  have hbu : |1 / c| ≤ 1 / c := le_of_eq (abs_of_pos hu)
  have hu0 : (0 : ℝ) ≤ 1 / c := hu.le
  refine ⟨(contDiff_cutPsi_affine _ _).mul (contDiff_cutPsi_affine _ _), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u0, u1⟩ := cutPsi_mem (-(1 / c) * x + 0)
    obtain ⟨v0, v1⟩ := cutPsi_mem ((1 / c) * x + -(N : ℝ))
    constructor
    · exact mul_nonneg u0 v0
    · nlinarith
  · intro x hx
    have h1 : cutPsi (-(1 / c) * x + 0) = 1 := by
      apply cutPsi_eq_one
      have : 0 ≤ (1 / c) * x := mul_nonneg hu0 hx.1
      linarith
    have h2 : cutPsi ((1 / c) * x + -(N : ℝ)) = 1 := by
      apply cutPsi_eq_one
      have hle : (1 / c) * x ≤ (1 / c) * ((N : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hx.2 hu0
      have e : (1 / c) * ((N : ℝ) * c) = (N : ℝ) := by field_simp
      linarith
    simp only [h1, h2, mul_one]
  · intro x hx
    rcases hx with hx | hx
    · dsimp only
      have hpos : 1 < -(1 / c) * x + 0 := by
        have h1 : (1 / c) * x < (1 / c) * (-c) := mul_lt_mul_of_pos_left hx hu
        have e : (1 / c) * (-c) = -1 := by field_simp
        linarith
      rw [cutPsi_eq_zero hpos.le, zero_mul]
    · dsimp only
      have hpos : 1 < (1 / c) * x + -(N : ℝ) := by
        have h1 : (1 / c) * (((N : ℝ) + 1) * c) < (1 / c) * x :=
          mul_lt_mul_of_pos_left hx hu
        have e : (1 / c) * (((N : ℝ) + 1) * c) = (N : ℝ) + 1 := by field_simp
        linarith
      rw [cutPsi_eq_zero hpos.le, mul_zero]
  · intro x
    have hd1 : deriv (fun x => cutPsi (-(1 / c) * x + 0) * cutPsi ((1 / c) * x + -(N : ℝ))) =
        fun x => deriv cutPsi (-(1 / c) * x + 0) * (-(1 / c)) * cutPsi ((1 / c) * x + -(N : ℝ)) +
          cutPsi (-(1 / c) * x + 0) * (deriv cutPsi ((1 / c) * x + -(N : ℝ)) * (1 / c)) :=
      funext fun y => (cut_hasDerivAt1 _ _ _ _ y).deriv
    rw [hd1]
    dsimp only
    have e1 : |deriv cutPsi (-(1 / c) * x + 0) * (-(1 / c)) * cutPsi ((1 / c) * x + -(N : ℝ))|
        ≤ M * (1 / c) * 1 :=
      abs_mul_le' (abs_mul_le' (hM _) hau hM0) (abs_cutPsi_le _)
        (mul_nonneg hM0 hu0)
    have e2 : |cutPsi (-(1 / c) * x + 0) * (deriv cutPsi ((1 / c) * x + -(N : ℝ)) * (1 / c))|
        ≤ 1 * (M * (1 / c)) := by
      exact abs_mul_le' (abs_cutPsi_le _) (abs_mul_le' (hM _) hbu hM0) (by norm_num)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ M * (1 / c) * 1 + 1 * (M * (1 / c)) := add_le_add e1 e2
      _ = 2 * M / c := by ring
      _ ≤ (2 * M + 2 * M * M) / c := by
          apply div_le_div_of_nonneg_right _ hc.le
          nlinarith
  · intro x
    have hd1 : deriv (fun x => cutPsi (-(1 / c) * x + 0) * cutPsi ((1 / c) * x + -(N : ℝ))) =
        fun x => deriv cutPsi (-(1 / c) * x + 0) * (-(1 / c)) * cutPsi ((1 / c) * x + -(N : ℝ)) +
          cutPsi (-(1 / c) * x + 0) * (deriv cutPsi ((1 / c) * x + -(N : ℝ)) * (1 / c)) :=
      funext fun y => (cut_hasDerivAt1 _ _ _ _ y).deriv
    have hd2 : deriv (deriv (fun x => cutPsi (-(1 / c) * x + 0) *
        cutPsi ((1 / c) * x + -(N : ℝ)))) =
        fun x => deriv (deriv cutPsi) (-(1 / c) * x + 0) * (-(1 / c)) * (-(1 / c)) *
            cutPsi ((1 / c) * x + -(N : ℝ)) +
          deriv cutPsi (-(1 / c) * x + 0) * (-(1 / c)) *
            (deriv cutPsi ((1 / c) * x + -(N : ℝ)) * (1 / c)) +
          (deriv cutPsi (-(1 / c) * x + 0) * (-(1 / c)) *
            (deriv cutPsi ((1 / c) * x + -(N : ℝ)) * (1 / c)) +
            cutPsi (-(1 / c) * x + 0) * (deriv (deriv cutPsi) ((1 / c) * x + -(N : ℝ)) *
              (1 / c) * (1 / c))) := by
      rw [hd1]
      funext y
      exact (cut_hasDerivAt2 _ _ _ _ y).deriv
    rw [hd2]
    dsimp only
    have hMu : (0 : ℝ) ≤ M * (1 / c) := mul_nonneg hM0 hu0
    have bA : |deriv (deriv cutPsi) (-(1 / c) * x + 0) * (-(1 / c)) * (-(1 / c)) *
        cutPsi ((1 / c) * x + -(N : ℝ))| ≤ M * (1 / c) * (1 / c) * 1 :=
      abs_mul_le' (abs_mul_le' (abs_mul_le' (hM2 _) hau hM0) hau hMu) (abs_cutPsi_le _)
        (mul_nonneg hMu hu0)
    have bB : |deriv cutPsi (-(1 / c) * x + 0) * (-(1 / c)) *
        (deriv cutPsi ((1 / c) * x + -(N : ℝ)) * (1 / c))| ≤ M * (1 / c) * (M * (1 / c)) :=
      abs_mul_le' (abs_mul_le' (hM _) hau hM0) (abs_mul_le' (hM _) hbu hM0) hMu
    have bD : |cutPsi (-(1 / c) * x + 0) *
        (deriv (deriv cutPsi) ((1 / c) * x + -(N : ℝ)) * (1 / c) * (1 / c))| ≤
        1 * (M * (1 / c) * (1 / c)) :=
      abs_mul_le' (abs_cutPsi_le _) (abs_mul_le' (abs_mul_le' (hM2 _) hbu hM0) hbu hMu)
        (by norm_num)
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (abs_add_le _ _))) ?_
    refine le_trans (add_le_add (add_le_add bA bB) (add_le_add bB bD)) (le_of_eq ?_)
    field_simp
    ring

end ChmCutoff

/-- **Lemma 1 (cutoff, SP 1933-1935)** as stated in `Sub/PartII-b_T13_1_4_2.lean`. -/
theorem chmCutoffExists : UnforcedLeray.Short.IIb.ChmCutoffExists := by
  obtain ⟨M, hM1, hM, hM2⟩ := ChmCutoff.cutPsi_bounds
  refine ⟨2 * M + 2 * M * M, by nlinarith, fun c hc N _ => ?_⟩
  exact ⟨_, ChmCutoff.cut_bound c hc N M hM1 hM hM2⟩

end UnforcedLeray.Short.IIb
