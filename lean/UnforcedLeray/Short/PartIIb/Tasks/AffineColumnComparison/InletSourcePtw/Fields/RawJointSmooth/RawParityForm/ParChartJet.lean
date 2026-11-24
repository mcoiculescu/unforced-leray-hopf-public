import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.ParWeightJet
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Jets of the parity chart (`parChartJet`)

Source: `the November 2 reference manuscript` lines 1287-1291. The three components
of `parChart R` are `R²/w`, `Rτ/2 - (R/2) log(R²/w)`, `z · (R/√w)`; each is bounded in iterated
derivatives of order `1 ≤ i ≤ n` by `E (w^(i+1))⁻¹` on `0 < w ≤ 1`, `|z| ≤ M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `z` coordinate `x ↦ x.2.2` as a continuous linear map. -/
def pcZProj : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The `τ` coordinate `x ↦ x.1` as a continuous linear map. -/
def pcTProj : ℝ × (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

theorem norm_pcZProj_le : ‖pcZProj‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  have h2 : ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem norm_pcTProj_le : ‖pcTProj‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)

theorem pc_norm_iter_clm_ge_one (L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (k : ℕ) (hk : 1 ≤ k)
    (y : ℝ × (ℝ × ℝ)) : ‖iteratedFDeriv ℝ k (fun z => L z) y‖ ≤ 1 := by
  rcases k with _ | _ | m
  · omega
  · rw [norm_iteratedFDeriv_one]
    have h2 : fderiv ℝ (fun z => L z) y = L := L.fderiv
    rw [h2]
    exact hL
  · have h1 : ‖iteratedFDeriv ℝ (m + 1 + 1) (fun z => L z) y‖ =
        ‖iteratedFDeriv ℝ (m + 1) (fderiv ℝ (fun z => L z)) y‖ :=
      (norm_iteratedFDeriv_fderiv).symm
    have h2 : fderiv ℝ (fun z => L z) = fun _ => L := funext fun z => L.fderiv
    rw [h1, h2, iteratedFDeriv_succ_const]
    simp

theorem pc_norm_iter_clm_le (L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (k : ℕ)
    (y : ℝ × (ℝ × ℝ)) : ‖iteratedFDeriv ℝ k (fun z => L z) y‖ ≤ 1 + ‖L y‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero]
    linarith [norm_nonneg (L y)]
  · linarith [pc_norm_iter_clm_ge_one L hL k hk y, norm_nonneg (L y)]

theorem pc_norm_iter_mul_le {f F : ℝ × (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f parPos) (hF : ContDiffOn ℝ ∞ F parPos)
    {y : ℝ × (ℝ × ℝ)} (hy : y ∈ parPos) (i : ℕ) {a B : ℝ}
    (ha : ∀ k, ‖iteratedFDeriv ℝ k f y‖ ≤ a) (hB : ∀ k ≤ i, ‖iteratedFDeriv ℝ k F y‖ ≤ B)
    (ha0 : 0 ≤ a) (hB0 : 0 ≤ B) :
    ‖iteratedFDeriv ℝ i (fun z => f z * F z) y‖ ≤ (((i : ℝ) + 1) * 2 ^ i) * a * B := by
  have hn : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hu : UniqueDiffOn ℝ parPos := isOpen_parPos.uniqueDiffOn
  have hw : ∀ (k : ℕ) (g : ℝ × (ℝ × ℝ) → ℝ),
      iteratedFDerivWithin ℝ k g parPos y = iteratedFDeriv ℝ k g y :=
    fun k g => iteratedFDerivWithin_of_isOpen k isOpen_parPos hy
  have hL := norm_iteratedFDerivWithin_mul_le hf hF hu hy hn
  simp only [hw] at hL
  refine hL.trans ?_
  have hsum : ∑ k ∈ Finset.range (i + 1),
      (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k f y‖ * ‖iteratedFDeriv ℝ (i - k) F y‖ ≤
      ∑ k ∈ Finset.range (i + 1), (2 : ℝ) ^ i * a * B := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ i := by
      rw [Finset.mem_range] at hk
      omega
    have hch : (i.choose k : ℝ) ≤ 2 ^ i := by exact_mod_cast Nat.choose_le_two_pow i k
    have hA : (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k f y‖ ≤ 2 ^ i * a :=
      mul_le_mul hch (ha k) (norm_nonneg _) (by positivity)
    exact mul_le_mul hA (hB (i - k) (by omega)) (norm_nonneg _) (by positivity)
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem pc_norm_iter_sub_le {f g : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (i : ℕ)
    (hf : ContDiffAt ℝ i f y) (hg : ContDiffAt ℝ i g y) :
    ‖iteratedFDeriv ℝ i (fun z => f z - g z) y‖ ≤
      ‖iteratedFDeriv ℝ i f y‖ + ‖iteratedFDeriv ℝ i g y‖ := by
  have h : iteratedFDeriv ℝ i (fun z => f z - g z) y =
      iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i g y :=
    iteratedFDeriv_sub_apply hf hg
  rw [h]
  exact norm_sub_le _ _

theorem pc_norm_iter_const_mul_le (c : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (i : ℕ)
    (hf : ContDiffAt ℝ i f y) :
    ‖iteratedFDeriv ℝ i (fun z => c * f z) y‖ ≤ |c| * ‖iteratedFDeriv ℝ i f y‖ := by
  have hfun : (fun z => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  have h : iteratedFDeriv ℝ i (fun z => c * f z) y = c • iteratedFDeriv ℝ i f y := by
    rw [hfun]
    exact iteratedFDeriv_const_smul_apply hf
  rw [h, norm_smul, Real.norm_eq_abs]

/-- `w^(-1-i) = (w^(i+1))⁻¹`. -/
theorem pc_rpow_form {w : ℝ} (hw : 0 < w) (i : ℕ) :
    w ^ (-(1 : ℝ) - (i : ℝ)) = (w ^ (i + 1))⁻¹ := by
  have : -(1 : ℝ) - (i : ℝ) = -(((i + 1 : ℕ)) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg hw.le, Real.rpow_natCast]

/-- Power comparison on `0 < w ≤ 1`. -/
theorem pc_inv_pow_mono {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (w ^ a)⁻¹ ≤ (w ^ b)⁻¹ :=
  inv_anti₀ (pow_pos hw b) (pow_le_pow_of_le_one hw.le hw1 hab)

/-- The log part: `‖D^{m+1} log(R²/w)‖ ≤ m! (w^{m+1})⁻¹`. -/
theorem pc_norm_iter_log_le (R : ℝ) (hR : 0 < R) (m : ℕ) (x : ℝ × (ℝ × ℝ)) (hx : 0 < x.2.1) :
    ‖iteratedFDeriv ℝ (m + 1) (fun y : ℝ × (ℝ × ℝ) => Real.log (R ^ 2 / y.2.1)) x‖ ≤
      (m.factorial : ℝ) * (x.2.1 ^ (m + 1))⁻¹ := by
  have hG : ContDiffOn ℝ ∞ (fun t : ℝ => Real.log (R ^ 2 / t)) (Ioi 0) := by
    refine ContDiffOn.log (contDiffOn_const.div contDiffOn_id (fun t ht => ne_of_gt ht)) ?_
    intro t ht
    exact (div_pos (pow_pos hR 2) ht).ne'
  have hE : EqOn (fun t : ℝ => Real.log (R ^ 2 / t))
      (fun t : ℝ => Real.log (R ^ 2) - Real.log t) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    show Real.log (R ^ 2 / t) = Real.log (R ^ 2) - Real.log t
    exact Real.log_div (pow_pos hR 2).ne' ht'.ne'
  refine (norm_iteratedFDeriv_comp_w_le _ _ hG hE (m + 1) x hx).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ']
  have hd : deriv (fun t : ℝ => Real.log (R ^ 2) - Real.log t) = -(Inv.inv : ℝ → ℝ) := by
    funext t
    rw [deriv_const_sub, Real.deriv_log]
    rfl
  rw [hd, iteratedDeriv_neg, iteratedDeriv_eq_iterate, iter_deriv_inv, norm_neg, norm_mul,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  have hz : x.2.1 ^ (-1 - (m : ℤ)) = (x.2.1 ^ (m + 1))⁻¹ := by
    have : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast]
  rw [hz, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos hx _))]

/-- Smoothness of an outer function of `w`. -/
theorem pc_contDiffOn_comp_w {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => G y.2.1) parPos :=
  hG.comp wProj.contDiff.contDiffOn (fun x hx => hx)

theorem pc_contDiffOn_pcz : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => y.2.2) parPos :=
  pcZProj.contDiff.contDiffOn

theorem pc_contDiffOn_pct : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => y.1) parPos :=
  pcTProj.contDiff.contDiffOn

theorem pc_contDiffOn_inv (c : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => c / y.2.1) parPos :=
  pc_contDiffOn_comp_w (G := fun t => c / t)
    (contDiffOn_const.div contDiffOn_id (fun t ht => ne_of_gt ht))

theorem pc_contDiffOn_invsqrt (c : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => c / Real.sqrt y.2.1) parPos :=
  pc_contDiffOn_comp_w (G := fun t => c / Real.sqrt t)
    (contDiffOn_const.div
      (fun t ht => (Real.contDiffAt_sqrt (n := ∞) (ne_of_gt ht)).contDiffWithinAt)
      (fun t ht => (Real.sqrt_pos.2 ht).ne'))

theorem pc_contDiffOn_log (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => Real.log (R ^ 2 / y.2.1)) parPos := by
  refine pc_contDiffOn_comp_w (G := fun t => Real.log (R ^ 2 / t)) ?_
  refine ContDiffOn.log (contDiffOn_const.div contDiffOn_id (fun t ht => ne_of_gt ht)) ?_
  intro t ht
  exact (div_pos (pow_pos hR 2) ht).ne'

theorem pc_comp3 (R : ℝ) :
    parChart R = fun x => (R ^ 2 / x.2.1,
      (R / 2 * x.1 - R / 2 * Real.log (R ^ 2 / x.2.1), x.2.2 * (R / Real.sqrt x.2.1))) := by
  funext x
  simp only [parChart]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show R * x.1 / 2 - R / 2 * Real.log (R ^ 2 / x.2.1) = _
    ring
  · show R * x.2.2 / Real.sqrt x.2.1 = _
    ring

theorem pc_contDiffOn_two (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) =>
      R / 2 * y.1 - R / 2 * Real.log (R ^ 2 / y.2.1)) parPos :=
  (contDiffOn_const.mul pc_contDiffOn_pct).sub (contDiffOn_const.mul (pc_contDiffOn_log R hR))

theorem pc_smooth (R : ℝ) (hR : 0 < R) : ContDiffOn ℝ ∞ (parChart R) parPos := by
  rw [pc_comp3]
  exact (pc_contDiffOn_inv (R ^ 2)).prodMk
    ((pc_contDiffOn_two R hR).prodMk
      (pc_contDiffOn_pcz.mul (pc_contDiffOn_invsqrt R)))

/-- Uniform bound of the three components. -/
theorem pc_bounds (R : ℝ) (hR : 0 < R) (n : ℕ) (M : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x ∈ parPos, x.2.1 ≤ 1 → |x.2.2| ≤ M → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (parChart R) x‖ ≤ E * (x.2.1 ^ (i + 1))⁻¹ := by
  obtain ⟨C1, hC1⟩ := (parWeightJet (R ^ 2)).2.2 n
  obtain ⟨C3, hC3⟩ := (parWeightJet R).2.2 n
  refine ⟨|C1| + |R / 2| * (1 + (n.factorial : ℝ)) +
    ((n : ℝ) + 1) * 2 ^ n * (1 + |M|) * |C3|, by positivity, ?_⟩
  intro x hx hx1 hzM i hi1 hin
  have hw : 0 < x.2.1 := hx
  set w := x.2.1 with hwdef
  set W := (w ^ (i + 1))⁻¹ with hW
  have hW1 : 1 ≤ W := by
    rw [hW]
    exact (one_le_inv₀ (pow_pos hw _)).2 (pow_le_one₀ hw.le hx1)
  have hW0 : 0 ≤ W := by linarith
  have hat : ∀ f : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ f parPos → ContDiffAt ℝ i f x := by
    intro f hf
    exact (hf.contDiffAt (isOpen_parPos.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  have hi : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) * 2 ^ n * (1 + |M|) * |C3| := by positivity
  have hfa : (0 : ℝ) ≤ |R / 2| * (1 + (n.factorial : ℝ)) := by positivity
  -- component 1
  have b1 : ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => R ^ 2 / y.2.1) x‖ ≤
      (|C1| + |R / 2| * (1 + (n.factorial : ℝ)) +
        ((n : ℝ) + 1) * 2 ^ n * (1 + |M|) * |C3|) * W := by
    have h := (hC1 x hx hx1 i hin).1
    rw [pc_rpow_form hw] at h
    calc _ ≤ C1 * W := h
      _ ≤ |C1| * W := mul_le_mul_of_nonneg_right (le_abs_self _) hW0
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hW0
        linarith
  -- component 3
  have b3 : ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => y.2.2 * (R / Real.sqrt y.2.1)) x‖ ≤
      (|C1| + |R / 2| * (1 + (n.factorial : ℝ)) +
        ((n : ℝ) + 1) * 2 ^ n * (1 + |M|) * |C3|) * W := by
    have hzb : ∀ k, ‖iteratedFDeriv ℝ k (fun y : ℝ × (ℝ × ℝ) => y.2.2) x‖ ≤ 1 + |M| := by
      intro k
      have h := pc_norm_iter_clm_le pcZProj norm_pcZProj_le k x
      have h2 : ‖pcZProj x‖ = |x.2.2| := Real.norm_eq_abs _
      have h3 : |x.2.2| ≤ |M| := hzM.trans (le_abs_self M)
      exact h.trans (by rw [h2]; linarith)
    have hB : ∀ k ≤ i, ‖iteratedFDeriv ℝ k (fun y : ℝ × (ℝ × ℝ) => R / Real.sqrt y.2.1) x‖ ≤
        |C3| * W := by
      intro k hk
      have h := (hC3 x hx hx1 k (hk.trans hin)).2
      have hp : w ^ (-(1 / 2 : ℝ) - (k : ℝ)) ≤ w ^ (-(1 : ℝ) - (i : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hw hx1 (by
          have : (k : ℝ) ≤ i := by exact_mod_cast hk
          linarith)
      rw [pc_rpow_form hw] at hp
      calc _ ≤ C3 * w ^ (-(1 / 2 : ℝ) - (k : ℝ)) := h
        _ ≤ |C3| * w ^ (-(1 / 2 : ℝ) - (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hw.le _)
        _ ≤ |C3| * W := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    have h := pc_norm_iter_mul_le (f := fun y : ℝ × (ℝ × ℝ) => y.2.2)
      (F := fun y : ℝ × (ℝ × ℝ) => R / Real.sqrt y.2.1) pc_contDiffOn_pcz
      (pc_contDiffOn_invsqrt R) hx i hzb hB (by positivity) (by positivity)
    refine h.trans ?_
    have hc : (((i : ℝ) + 1) * 2 ^ i) ≤ ((n : ℝ) + 1) * 2 ^ n := by
      have h1 : (i : ℝ) ≤ n := by exact_mod_cast hin
      have h2 : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hin
      exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have hpos : 0 ≤ (1 + |M|) * (|C3| * W) := by positivity
    calc ((i : ℝ) + 1) * 2 ^ i * (1 + |M|) * (|C3| * W)
        = (((i : ℝ) + 1) * 2 ^ i) * ((1 + |M|) * (|C3| * W)) := by ring
      _ ≤ (((n : ℝ) + 1) * 2 ^ n) * ((1 + |M|) * (|C3| * W)) :=
          mul_le_mul_of_nonneg_right hc hpos
      _ = ((n : ℝ) + 1) * 2 ^ n * (1 + |M|) * |C3| * W := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hW0
        linarith [abs_nonneg C1, hfa]
  -- component 2
  have b2 : ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) =>
      R / 2 * y.1 - R / 2 * Real.log (R ^ 2 / y.2.1)) x‖ ≤
      (|C1| + |R / 2| * (1 + (n.factorial : ℝ)) +
        ((n : ℝ) + 1) * 2 ^ n * (1 + |M|) * |C3|) * W := by
    have hlog := hat _ (pc_contDiffOn_log R hR)
    have hT := hat _ pc_contDiffOn_pct
    refine (pc_norm_iter_sub_le i (hat _ (contDiffOn_const.mul pc_contDiffOn_pct))
      (hat _ (contDiffOn_const.mul (pc_contDiffOn_log R hR)))).trans ?_
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have e1 := pc_norm_iter_const_mul_le (R / 2) (f := fun y : ℝ × (ℝ × ℝ) => y.1) (y := x)
      (m + 1) hT
    have e2 := pc_norm_iter_const_mul_le (R / 2)
      (f := fun y : ℝ × (ℝ × ℝ) => Real.log (R ^ 2 / y.2.1)) (y := x) (m + 1) hlog
    have f1 := pc_norm_iter_clm_ge_one pcTProj norm_pcTProj_le (m + 1) (by omega) x
    have f2 := pc_norm_iter_log_le R hR m x hw
    have hmf : (m.factorial : ℝ) ≤ n.factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hWm : (w ^ (m + 1))⁻¹ ≤ W := pc_inv_pow_mono hw hx1 (by omega)
    have hA : ‖iteratedFDeriv ℝ (m + 1) (fun y : ℝ × (ℝ × ℝ) => y.1) x‖ ≤ 1 := f1
    have hB : ‖iteratedFDeriv ℝ (m + 1) (fun y : ℝ × (ℝ × ℝ) =>
        Real.log (R ^ 2 / y.2.1)) x‖ ≤ (n.factorial : ℝ) * W :=
      f2.trans (mul_le_mul hmf hWm (by positivity) (by positivity))
    have hRn : 0 ≤ |R / 2| := abs_nonneg _
    calc _ ≤ |R / 2| * ‖iteratedFDeriv ℝ (m + 1) (fun y : ℝ × (ℝ × ℝ) => y.1) x‖ +
          |R / 2| * ‖iteratedFDeriv ℝ (m + 1) (fun y : ℝ × (ℝ × ℝ) =>
            Real.log (R ^ 2 / y.2.1)) x‖ := add_le_add e1 e2
      _ ≤ |R / 2| * 1 + |R / 2| * ((n.factorial : ℝ) * W) :=
          add_le_add (mul_le_mul_of_nonneg_left hA hRn) (mul_le_mul_of_nonneg_left hB hRn)
      _ ≤ |R / 2| * (1 + (n.factorial : ℝ)) * W := by
          have : |R / 2| * 1 ≤ |R / 2| * W := mul_le_mul_of_nonneg_left hW1 hRn
          nlinarith [this]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hW0
          linarith [abs_nonneg C1, hnn]
  -- assemble
  have hch : iteratedFDeriv ℝ i (parChart R) x =
      iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => (R ^ 2 / y.2.1,
        (R / 2 * y.1 - R / 2 * Real.log (R ^ 2 / y.2.1),
          y.2.2 * (R / Real.sqrt y.2.1)))) x := by rw [pc_comp3]
  rw [hch]
  have c1 := hat _ (pc_contDiffOn_inv (R ^ 2))
  have c2 := hat _ (pc_contDiffOn_two R hR)
  have c3 := hat _ (pc_contDiffOn_pcz.mul (pc_contDiffOn_invsqrt R))
  have hp2 := iteratedFDeriv_prodMk (𝕜 := ℝ) (x := x) (i := i) (n := (i : WithTop ℕ∞)) c2 c3
    le_rfl
  have hp1 := iteratedFDeriv_prodMk (𝕜 := ℝ) (x := x) (i := i) (n := (i : WithTop ℕ∞)) c1
    (c2.prodMk c3) le_rfl
  rw [hp1, ContinuousMultilinearMap.opNorm_prod]
  have hp2' : ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) =>
      (R / 2 * y.1 - R / 2 * Real.log (R ^ 2 / y.2.1), y.2.2 * (R / Real.sqrt y.2.1))) x‖ =
      max ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) =>
        R / 2 * y.1 - R / 2 * Real.log (R ^ 2 / y.2.1)) x‖
        ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => y.2.2 * (R / Real.sqrt y.2.1)) x‖ := by
    rw [hp2, ContinuousMultilinearMap.opNorm_prod]
  rw [hp2']
  exact max_le b1 (max_le b2 b3)

/-- **Jets of the parity chart** (SP 1287-1291). -/
theorem parChartJet : UnforcedLeray.Short.IIb.ParChartJet := by
  intro R hR
  refine ⟨pc_smooth R hR, ?_⟩
  intro n M
  obtain ⟨E, hE0, hE⟩ := pc_bounds R hR n M
  refine ⟨max 1 E, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro x hx hx1 hzM i hi1 hin
  have hw : 0 < x.2.1 := hx
  refine (hE x hx hx1 hzM i hi1 hin).trans ?_
  have hD1 : 1 ≤ max 1 E := le_max_left _ _
  have hED : E ≤ max 1 E := le_max_right _ _
  have hDi : max 1 E ≤ (max 1 E) ^ i := le_self_pow₀ hD1 (by omega)
  have hW : (x.2.1 ^ (i + 1))⁻¹ ≤ (x.2.1 ^ (2 * i))⁻¹ :=
    pc_inv_pow_mono hw hx1 (by omega)
  have hdiv : ((max 1 E) / x.2.1 ^ 2) ^ i = (max 1 E) ^ i * (x.2.1 ^ (2 * i))⁻¹ := by
    rw [div_pow, ← pow_mul, div_eq_mul_inv]
  rw [hdiv]
  have hp : 0 ≤ (x.2.1 ^ (i + 1))⁻¹ := inv_nonneg.2 (pow_pos hw _).le
  calc E * (x.2.1 ^ (i + 1))⁻¹ ≤ max 1 E * (x.2.1 ^ (i + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right hED hp
    _ ≤ max 1 E * (x.2.1 ^ (2 * i))⁻¹ :=
        mul_le_mul_of_nonneg_left hW (le_trans zero_le_one hD1)
    _ ≤ (max 1 E) ^ i * (x.2.1 ^ (2 * i))⁻¹ :=
        mul_le_mul_of_nonneg_right hDi (inv_nonneg.2 (pow_pos hw _).le)

end UnforcedLeray.Short.IIb
