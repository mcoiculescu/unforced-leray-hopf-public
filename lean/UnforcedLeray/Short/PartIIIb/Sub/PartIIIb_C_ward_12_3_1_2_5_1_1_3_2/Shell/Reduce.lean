import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Smooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.NearOrg

/-!
# `NvShellJets` from the calculus leaves

Source `the November 2 reference manuscript`
lines 2545-2549, 1206-1222.  On the shell `ρ₀ ≤ ϱ ≤ R₀` (open neighbourhood `axisᶜ`):

* `shellChartJets_of`: `‖D^i chart‖ ≤ C (1+|y₃|)` for `1 ≤ i ≤ n` (componentwise, `opNorm_prod`);
* `shellLiftJets_of`: Leibniz for `frameFac R y (b (chart R τ y))`
  (`norm_iteratedFDerivWithin_clm_apply`), Faà di Bruno for `b ∘ chart`
  (`norm_iteratedFDerivWithin_comp_le` with `D = C (1+|y₃|) ≥ 1`), `e^{-κ|η|} ≤ e^{-a|y₃|}`
  with `a = κR/R₁` since `|η| = R|y₃|/ϱ ≥ R|y₃|/R₁`, and `ShellAbsorb`;
* `nvShellJets_of`: orders `≤ 3` from `shellLiftJets_of` at `n = 3`; the `∂_τ` part is
  `realC ∘ Nv R ((R/2)∂_ξ b)` near `y` (`ShellDτ`), whose jets of order `≤ 1` are bounded by
  `shellLiftJets_of` at `n = 1` (jets of `∂_ξ b` of order `l` are jets of `b` of order `l+1 ≤ 2`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Nat

namespace UnforcedLeray.Short.PartIIIb.Concrete.Shell

open UnforcedLeray.Axi

theorem one_le_one_add_abs (t : ℝ) : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]

/-- The chart jets of order `1..n` grow at most linearly in `|y₃|` on the shell. -/
theorem shellChartJets_of (hA : ShellAgeJets) (hP : ShellPhaseJets) (hT : ShellTransJets)
    {R ρ0 R0 : ℝ} (n : ℕ) (hR : 0 < R) (hρ0 : 0 < ρ0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), ρ0 ≤ ϱ y → ϱ y ≤ R0 →
      ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (chart R τ) y‖ ≤ C * (1 + |y 2|) := by
  obtain ⟨Ca, ha⟩ := hA R ρ0 R0 n hR hρ0
  obtain ⟨Cp, hp⟩ := hP R ρ0 R0 n hR hρ0
  obtain ⟨Ct, ht⟩ := hT R ρ0 R0 n hR hρ0
  refine ⟨max 1 (max Ca (max Cp Ct)), le_max_left _ _, fun τ y hy1 hy2 i hi1 hin => ?_⟩
  have hax : y ∉ axis := notMem_axis_of_le hρ0 hy1
  have hnhds : axisᶜ ∈ nhds y := isOpen_compl_axis.mem_nhds hax
  have hle : ((i : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcA : ContDiffAt ℝ i (age R) y := ((contDiffOn_age R).contDiffAt hnhds).of_le hle
  have hcP : ContDiffAt ℝ i (phase R τ) y :=
    ((contDiffOn_phase hR.ne' τ).contDiffAt hnhds).of_le hle
  have hcT : ContDiffAt ℝ i (Axi.trans R) y := ((contDiffOn_trans R).contDiffAt hnhds).of_le hle
  have hchart : chart R τ = fun x => (age R x, (phase R τ x, Axi.trans R x)) := rfl
  rw [hchart, iteratedFDeriv_prodMk hcA (hcP.prodMk hcT) le_rfl,
    ContinuousMultilinearMap.opNorm_prod, iteratedFDeriv_prodMk hcP hcT le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  set K := max 1 (max Ca (max Cp Ct)) with hK
  have h1 := one_le_one_add_abs (y 2)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKK : K ≤ K * (1 + |y 2|) := le_mul_of_one_le_right (by linarith) h1
  have hCa : Ca ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hCp : Cp ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCt : Ct ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine max_le ((ha y hy1 hy2 i hin).trans (hCa.trans hKK)) (max_le ?_ ?_)
  · exact (hp τ y hy1 hy2 i hi1 hin).trans (hCp.trans hKK)
  · exact (ht y hy1 hy2 i hin).trans (mul_le_mul_of_nonneg_right hCt (by linarith))

theorem norm_cplxV_le : ‖Axi.cplxV‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [norm_cplxV, one_mul]

theorem realC_comp_eq (f : UnforcedLeray.Space → UnforcedLeray.Space) :
    (fun x => UnforcedLeray.B0412.realC (f x)) = Axi.cplxV ∘ f := by
  funext x
  ext i
  simp [UnforcedLeray.B0412.realC_apply, Axi.cplxV_apply]

/-- **Shell jets of the ring lift, any order.**  Jets of order `≤ n` of `realC (Nv R b τ ·)` on
the shell are `≤ C (1+|y₃|)^{-N}` when the jets of `b` of order `≤ n` are `≤ M e^{-κ|η|}`. -/
theorem shellLiftJets_of (hF : ShellFrameJets) (hA : ShellAgeJets) (hP : ShellPhaseJets)
    (hT : ShellTransJets) (hX : ShellAbsorb)
    {R ρ0 R0 κ M : ℝ} (hR : 0 < R) (hρ0 : 0 < ρ0) (hκ : 0 < κ) (hM : 0 ≤ M) (n : ℕ)
    {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiff ℝ ∞ b)
    (hj : ∀ l : ℕ, l ≤ n → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l b m‖ ≤ M * Real.exp (-(κ * |m.2.2|))) (N : ℕ) :
    ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space), ρ0 ≤ ϱ y → ϱ y ≤ R0 →
      ∀ k : ℕ, k ≤ n →
        ‖iteratedFDeriv ℝ k (fun x => UnforcedLeray.B0412.realC (Nv R b τ x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ)) := by
  obtain ⟨CA, hCA⟩ := hF R ρ0 R0 n hR hρ0
  obtain ⟨Cc, hCc1, hCc⟩ := shellChartJets_of (R0 := R0) hA hP hT n hR hρ0
  have hR1pos : 0 < max R0 ρ0 := lt_of_lt_of_le hρ0 (le_max_right _ _)
  have hapos : 0 < κ * R / max R0 ρ0 := by positivity
  obtain ⟨CX, hCX⟩ := hX (κ * R / max R0 ρ0) hapos n N
  set CA' := max CA 0 with hCA'
  have hCA'0 : 0 ≤ CA' := le_max_right _ _
  set K : ℝ := (n + 1) * 2 ^ n * CA' * n ! * M * Cc ^ n with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * CX, fun τ y hy1 hy2 k hk => ?_⟩
  have hax : y ∉ axis := notMem_axis_of_le hρ0 hy1
  have hs : IsOpen (axisᶜ : Set UnforcedLeray.Space) := isOpen_compl_axis
  have hus : UniqueDiffOn ℝ (axisᶜ : Set UnforcedLeray.Space) := hs.uniqueDiffOn
  have hys : y ∈ (axisᶜ : Set UnforcedLeray.Space) := hax
  have hnhds : axisᶜ ∈ nhds y := hs.mem_nhds hax
  have hFs := contDiffOn_frameFac hR.ne'
  have hcs := contDiffOn_chart hR.ne' τ
  have hGs : ContDiffOn ℝ ∞ (b ∘ chart R τ) axisᶜ := hb.comp_contDiffOn hcs
  have hNv : ContDiffOn ℝ ∞ (Nv R b τ) axisᶜ := contDiffOn_Nv hR.ne' hb τ
  -- complexification
  have step1 : ‖iteratedFDeriv ℝ k (fun x => UnforcedLeray.B0412.realC (Nv R b τ x)) y‖ ≤
      ‖iteratedFDeriv ℝ k (Nv R b τ) y‖ := by
    rw [realC_comp_eq]
    refine (Axi.cplxV.norm_iteratedFDeriv_comp_left (hNv.contDiffAt hnhds) (n := k)
      (by exact_mod_cast le_top)).trans ?_
    calc ‖Axi.cplxV‖ * ‖iteratedFDeriv ℝ k (Nv R b τ) y‖
        ≤ 1 * ‖iteratedFDeriv ℝ k (Nv R b τ) y‖ :=
          mul_le_mul_of_nonneg_right norm_cplxV_le (norm_nonneg _)
      _ = _ := one_mul _
  -- Leibniz
  have hNvEq : Nv R b τ = fun x => (frameFac R x) ((b ∘ chart R τ) x) := rfl
  have leib := norm_iteratedFDerivWithin_clm_apply hFs hGs hus hys (n := k)
    (by exact_mod_cast le_top)
  rw [← hNvEq] at leib
  rw [← iteratedFDerivWithin_of_isOpen (f := Nv R b τ) k hs hys] at step1
  -- the pieces
  set D : ℝ := Cc * (1 + |y 2|) with hD
  have h1y := one_le_one_add_abs (y 2)
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le hCc1 h1y
  set Cb : ℝ := M * Real.exp (-(κ * |(chart R τ y).2.2|)) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hfaa : ∀ j : ℕ, j ≤ n →
      ‖iteratedFDerivWithin ℝ j (b ∘ chart R τ) axisᶜ y‖ ≤ j ! * Cb * D ^ j := by
    intro j hj'
    refine norm_iteratedFDerivWithin_comp_le hb.contDiffOn hcs (by exact_mod_cast le_top)
      uniqueDiffOn_univ hus (mapsTo_univ _ _) hys ?_ ?_
    · intro i hi
      rw [iteratedFDerivWithin_univ]
      exact hj i (hi.trans hj') _
    · intro i hi1 hij
      rw [iteratedFDerivWithin_of_isOpen i hs hys]
      exact (hCc τ y hy1 hy2 i hi1 (hij.trans hj')).trans (le_self_pow₀ hD1 (by omega))
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (frameFac R) axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (b ∘ chart R τ) axisᶜ y‖ ≤
        2 ^ n * CA' * (n ! * Cb * D ^ n) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hch : (k.choose i : ℝ) ≤ 2 ^ n := by
      have : k.choose i ≤ 2 ^ n := (Nat.choose_le_two_pow k i).trans
        (Nat.pow_le_pow_right (by norm_num) hk)
      exact_mod_cast this
    have hA' : ‖iteratedFDerivWithin ℝ i (frameFac R) axisᶜ y‖ ≤ CA' := by
      rw [iteratedFDerivWithin_of_isOpen i hs hys]
      exact (hCA y hy1 hy2 i (hik.trans hk)).trans (le_max_left _ _)
    have hG' : ‖iteratedFDerivWithin ℝ (k - i) (b ∘ chart R τ) axisᶜ y‖ ≤ n ! * Cb * D ^ n := by
      refine (hfaa (k - i) (by omega)).trans ?_
      have hf : ((k - i) ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le (by omega)
      have hp : D ^ (k - i) ≤ D ^ n := pow_le_pow_right₀ hD1 (by omega)
      have hD0 : 0 ≤ D := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_right hf hCb0) hp (pow_nonneg hD0 _)
        (by positivity)
    have hD0 : 0 ≤ D := by linarith
    exact mul_le_mul (mul_le_mul hch hA' (norm_nonneg _) (by positivity)) hG' (norm_nonneg _)
      (by positivity)
  have hsum : ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (frameFac R) axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (b ∘ chart R τ) axisᶜ y‖ ≤
        (n + 1) * (2 ^ n * CA' * (n ! * Cb * D ^ n)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hB : 0 ≤ 2 ^ n * CA' * (n ! * Cb * D ^ n) := by
      have hD0 : 0 ≤ D := by linarith
      positivity
    have hkn : ((k + 1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hk
    exact mul_le_mul_of_nonneg_right hkn hB
  -- exponential comparison
  have hϱpos : 0 < ϱ y := lt_of_lt_of_le hρ0 hy1
  have hη : (chart R τ y).2.2 = R * y 2 / ϱ y := rfl
  have hexp : Real.exp (-(κ * |(chart R τ y).2.2|)) ≤
      Real.exp (-(κ * R / max R0 ρ0 * |y 2|)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff, hη, abs_div, abs_mul, abs_of_pos hR,
      abs_of_pos hϱpos]
    have h2 : R * |y 2| / max R0 ρ0 ≤ R * |y 2| / ϱ y :=
      div_le_div_of_nonneg_left (by positivity) hϱpos (hy2.trans (le_max_left _ _))
    calc κ * R / max R0 ρ0 * |y 2| = κ * (R * |y 2| / max R0 ρ0) := by ring
      _ ≤ κ * (R * |y 2| / ϱ y) := mul_le_mul_of_nonneg_left h2 hκ.le
  have habs := hCX (y 2)
  calc ‖iteratedFDeriv ℝ k (fun x => UnforcedLeray.B0412.realC (Nv R b τ x)) y‖
      ≤ (n + 1) * (2 ^ n * CA' * (n ! * Cb * D ^ n)) := step1.trans (leib.trans hsum)
    _ = K * ((1 + |y 2|) ^ n * Real.exp (-(κ * |(chart R τ y).2.2|))) := by
        rw [hK, hCb, hD, mul_pow]; ring
    _ ≤ K * ((1 + |y 2|) ^ n * Real.exp (-(κ * R / max R0 ρ0 * |y 2|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) hK0
    _ ≤ K * (CX * (1 + |y 2|) ^ (-(N : ℝ))) := mul_le_mul_of_nonneg_left habs hK0
    _ = K * CX * (1 + |y 2|) ^ (-(N : ℝ)) := (mul_assoc _ _ _).symm

/-- **`NvShellJets` from the calculus leaves.** -/
theorem nvShellJets_of (hF : ShellFrameJets) (hA : ShellAgeJets) (hP : ShellPhaseJets)
    (hT : ShellTransJets) (hX : ShellAbsorb) (hD : ShellDτ) : NvShellJets := by
  intro R ρ0 R0 κ M hR hρ0 hκ hM b hb hj N
  obtain ⟨C1, hC1⟩ := shellLiftJets_of hF hA hP hT hX hR hρ0 hκ hM 3 hb hj N
  have hb's : ContDiff ℝ ∞ (fun m => (R / 2) • dQ b m) :=
    (contDiff_dQ hb).const_smul (R / 2)
  have hj' : ∀ l : ℕ, l ≤ 1 → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l (fun m => (R / 2) • dQ b m) m‖ ≤
        (R / 2 * M) * Real.exp (-(κ * |m.2.2|)) := by
    intro l hl m
    have h1 : iteratedFDeriv ℝ l (fun m => (R / 2) • dQ b m) m =
        (R / 2) • iteratedFDeriv ℝ l (dQ b) m :=
      iteratedFDeriv_const_smul_apply'
        ((contDiff_dQ hb).contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h1, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((norm_iteratedFDeriv_dQ_le hb l m).trans (hj (l + 1) (by omega) m)) (by positivity)
  obtain ⟨C2, hC2⟩ := shellLiftJets_of hF hA hP hT hX hR hρ0 hκ (by positivity) 1 hb's hj' N
  refine ⟨max C1 C2, fun τ y hy1 hy2 => ⟨fun k hk => ?_, fun k hk => ?_⟩⟩
  · have hp : 0 ≤ (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    exact (hC1 τ y hy1 hy2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hp : 0 ≤ (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    have hax := notMem_axis_of_le hρ0 hy1
    have hev : (fun x : UnforcedLeray.Space => UnforcedLeray.PhaseSpace.dτ
          (fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2))
            (τ, x)) =ᶠ[nhds y]
        (fun x => UnforcedLeray.B0412.realC (Nv R (fun m => (R / 2) • dQ b m) τ x)) := by
      filter_upwards [isOpen_compl_axis.mem_nhds hax] with x hx
      exact hD R b hR hb τ x hx
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hC2 τ y hy1 hy2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

end UnforcedLeray.Short.PartIIIb.Concrete.Shell
