import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Field.Basic

/-!
# Gaussian derivative bound `exp(-|x|^2/(4a))` on `s0 ≤ s`

Task `ra_9_1_2_5_4_3`: every iterated derivative of `p ↦ exp(-|p.2|^2/(4 a(p.1)))` is bounded by a
polynomial times `exp(-κ |p.2|^2)` on `s0 ≤ s ≤ s1`.

Strategy: replace `a` by the globally smooth `1 + ν·ageSmoothT s0 s` (equal to `a` for `s ≥ s0/2`),
then induct on the order with the Leibniz rule for `exp ∘ Q` written as `exp(Q) • fderiv Q`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The exponent with `a` replaced by its globally smooth truncation. -/
def eqQ (ν s0 : ℝ) (p : Chart) : ℝ := -(sq2 p.2) / (4 * (1 + ν * ageSmoothT s0 p.1))

lemma eqQ_eq_mul (ν s0 : ℝ) :
    eqQ ν s0 = fun p : Chart =>
      (-(1 / 4 : ℝ) * (p.2.1 ^ 2 + p.2.2 ^ 2)) * (1 + ν * ageSmoothT s0 p.1)⁻¹ := by
  funext p
  unfold eqQ sq2
  rw [div_eq_mul_inv, mul_inv]
  ring

lemma eqd_f1_smooth :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => -(1 / 4 : ℝ) * (p.2.1 ^ 2 + p.2.2 ^ 2)) := by
  fun_prop

lemma eqd_A_pos (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) (t : ℝ) :
    0 < 1 + ν * ageSmoothT s0 t := by
  have := mul_nonneg hν.le (ageSmoothT_nonneg s0 hs0 t)
  linarith

lemma eqd_g_smooth (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹) := by
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => 1 + ν * ageSmoothT s0 p.1) :=
    contDiff_const.add (contDiff_const.mul ((ageSmoothT_contDiff s0).comp contDiff_fst))
  exact hA.inv (fun p => (eqd_A_pos ν hν s0 hs0 p.1).ne')

lemma eqd_f1_bd (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Chart,
    ‖iteratedFDeriv ℝ k (fun p : Chart => -(1 / 4 : ℝ) * (p.2.1 ^ 2 + p.2.2 ^ 2)) z‖
      ≤ K * (1 + ‖z.2‖) ^ 2 := by
  obtain ⟨C, hC⟩ := coordPoly_iteratedFDeriv_bound k
  refine ⟨‖(-(1 / 4 : ℝ))‖ * |C|, by positivity, fun z => ?_⟩
  have hpoly : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => p.2.1 ^ 2 + p.2.2 ^ 2) := by
    fun_prop
  have hsmooth : ContDiffAt ℝ k (fun p : Chart => p.2.1 ^ 2 + p.2.2 ^ 2) z :=
    (hpoly.of_le (by exact_mod_cast le_top)).contDiffAt
  have hfun : (fun p : Chart => -(1 / 4 : ℝ) * (p.2.1 ^ 2 + p.2.2 ^ 2))
      = fun p : Chart => (-(1 / 4 : ℝ)) • (p.2.1 ^ 2 + p.2.2 ^ 2) := by
    funext p
    simp [smul_eq_mul]
  rw [hfun, iteratedFDeriv_const_smul_apply' hsmooth, norm_smul]
  have h1 := (hC z).1
  calc ‖(-(1 / 4 : ℝ))‖ * ‖iteratedFDeriv ℝ k (fun p : Chart => p.2.1 ^ 2 + p.2.2 ^ 2) z‖
      ≤ ‖(-(1 / 4 : ℝ))‖ * (C * (1 + ‖z.2‖) ^ 2) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖(-(1 / 4 : ℝ))‖ * (|C| * (1 + ‖z.2‖) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (norm_nonneg _)
    _ = ‖(-(1 / 4 : ℝ))‖ * |C| * (1 + ‖z.2‖) ^ 2 := by ring

lemma eqd_g_bd (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) (k : ℕ) : ∃ B : ℝ, ∀ z : Chart,
    s0 ≤ z.1 → ‖iteratedFDeriv ℝ k (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹) z‖ ≤ B := by
  obtain ⟨B, hB⟩ := ageInvPow_iteratedFDeriv_bound ν hν s0 hs0 1 k
  refine ⟨B, fun z hz => ?_⟩
  have hW : {p : Chart | s0 / 2 < p.1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (show s0 / 2 < z.1 by linarith)
  have hev : (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹) =ᶠ[𝓝 z]
      (fun p : Chart => ((ageA ν p.1) ^ 1)⁻¹) := by
    filter_upwards [hW] with p hp
    have hp' : s0 / 2 ≤ p.1 := (show s0 / 2 < p.1 from hp).le
    rw [ageSmoothT_eq s0 hs0 p.1 hp']
    simp [ageA]
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hB z hz

lemma eqd_Q_bd (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ z : Chart, s0 ≤ z.1 → ‖iteratedFDeriv ℝ k (eqQ ν s0) z‖ ≤ K * (1 + ‖z.2‖) ^ 2 := by
  choose Kf hKf0 hKf using eqd_f1_bd
  choose Bg hBg using eqd_g_bd ν hν s0 hs0
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |Kf i| * |Bg (k - i)|, ?_, fun z hz => ?_⟩
  · positivity
  rw [eqQ_eq_mul]
  have hk : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hX : (0 : ℝ) ≤ (1 + ‖z.2‖) ^ 2 := by positivity
  refine (norm_iteratedFDeriv_mul_le (eqd_f1_smooth) (eqd_g_smooth ν hν s0 hs0) z hk).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hF : ‖iteratedFDeriv ℝ i (fun p : Chart => -(1 / 4 : ℝ) * (p.2.1 ^ 2 + p.2.2 ^ 2)) z‖
      ≤ |Kf i| * (1 + ‖z.2‖) ^ 2 :=
    (hKf i z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX)
  have hG : ‖iteratedFDeriv ℝ (k - i) (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹) z‖
      ≤ |Bg (k - i)| :=
    (hBg (k - i) z hz).trans (le_abs_self _)
  have hch : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hF hch) hG (norm_nonneg _)
    (mul_nonneg hch (mul_nonneg (abs_nonneg _) hX))
  exact h1.trans (le_of_eq (by ring))

lemma eqd_exp_bd (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) (n : ℕ) : ∃ C : ℝ,
    ∀ z : Chart, s0 ≤ z.1 →
      ‖iteratedFDeriv ℝ n (fun p : Chart => Real.exp (eqQ ν s0 p)) z‖
        ≤ C * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (eqQ ν s0 z) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero =>
    refine ⟨1, fun z _ => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp
  | succ m =>
    have hc : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (i ≤ m → ∀ z : Chart, s0 ≤ z.1 →
        ‖iteratedFDeriv ℝ i (fun p : Chart => Real.exp (eqQ ν s0 p)) z‖
          ≤ C * (1 + ‖z.2‖) ^ (2 * i) * Real.exp (eqQ ν s0 z)) := by
      intro i
      by_cases hi : i ≤ m
      · obtain ⟨C0, hC0⟩ := ih i (by omega)
        refine ⟨|C0|, abs_nonneg _, fun _ z hz => (hC0 z hz).trans ?_⟩
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity)) (Real.exp_pos _).le
      · exact ⟨0, le_rfl, fun h => absurd h hi⟩
    choose Ci hCi0 hCi using hc
    choose Kq hKq0 hKq using eqd_Q_bd ν hν s0 hs0
    have hQs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eqQ ν s0) := by
      rw [eqQ_eq_mul]
      exact eqd_f1_smooth.mul (eqd_g_smooth ν hν s0 hs0)
    have hQd : ∀ p : Chart, DifferentiableAt ℝ (eqQ ν s0) p := fun p =>
      (hQs.differentiable (by simp)) p
    have hfd : fderiv ℝ (fun p : Chart => Real.exp (eqQ ν s0 p))
        = fun p : Chart => Real.exp (eqQ ν s0 p) • fderiv ℝ (eqQ ν s0) p := by
      funext p
      exact ((hQd p).hasFDerivAt).exp.fderiv
    have hgd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (eqQ ν s0)) :=
      hQs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Chart => Real.exp (eqQ ν s0 p)) :=
      hQs.exp
    have hn : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun i => by
      exact_mod_cast le_top
    refine ⟨∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * Ci i * Kq (m - i + 1)), fun z hz => ?_⟩
    have hX1 : 1 ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
    have hX0 : 0 ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
    have hE : 0 ≤ Real.exp (eqQ ν s0 z) := (Real.exp_pos _).le
    have key : ‖iteratedFDeriv ℝ (m + 1) (fun p : Chart => Real.exp (eqQ ν s0 p)) z‖
        = ‖iteratedFDeriv ℝ m
            (fun y : Chart => Real.exp (eqQ ν s0 y) • fderiv ℝ (eqQ ν s0) y) z‖ := by
      rw [← hfd, norm_iteratedFDeriv_fderiv]
    rw [key]
    refine (norm_iteratedFDeriv_smul_le hfs hgd z (hn m)).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have hA := hCi i hi' z hz
    have hB : ‖iteratedFDeriv ℝ (m - i) (fderiv ℝ (eqQ ν s0)) z‖
        ≤ Kq (m - i + 1) * (1 + ‖z.2‖) ^ 2 := by
      rw [norm_iteratedFDeriv_fderiv]
      exact hKq (m - i + 1) z hz
    have hch : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    have hpow : (1 + ‖z.2‖) ^ (2 * i + 2) ≤ (1 + ‖z.2‖) ^ (2 * (m + 1)) :=
      pow_le_pow_right₀ hX1 (by omega)
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hA hch) hB (norm_nonneg _)
      (mul_nonneg hch (mul_nonneg (mul_nonneg (hCi0 i) (pow_nonneg hX0 _)) hE))
    refine h1.trans ?_
    have hCK : 0 ≤ (m.choose i : ℝ) * Ci i * Kq (m - i + 1) :=
      mul_nonneg (mul_nonneg hch (hCi0 i)) (hKq0 _)
    calc (m.choose i : ℝ) * (Ci i * (1 + ‖z.2‖) ^ (2 * i) * Real.exp (eqQ ν s0 z))
          * (Kq (m - i + 1) * (1 + ‖z.2‖) ^ 2)
        = (m.choose i : ℝ) * Ci i * Kq (m - i + 1) * (1 + ‖z.2‖) ^ (2 * i + 2)
          * Real.exp (eqQ ν s0 z) := by ring
      _ ≤ (m.choose i : ℝ) * Ci i * Kq (m - i + 1) * (1 + ‖z.2‖) ^ (2 * (m + 1))
          * Real.exp (eqQ ν s0 z) := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact mul_le_mul_of_nonneg_left hpow hCK

/-- The statement: `k`-th derivatives of `exp(-|x|^2/(4a))` on `s0 ≤ s ≤ s1` are polynomial times
a Gaussian in `x`, with `κ = 1/(4(1+ν max(s1,s0)))`, `P = 2n`, `C = |C_n|`. -/
theorem expQuad_iteratedFDeriv_bound (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0) (n : ℕ) :
    ∃ (C κ : ℝ) (P : ℕ), 0 < κ ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 →
      ‖iteratedFDeriv ℝ n (fun p : Chart => Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) z‖
        ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2) := by
  obtain ⟨C, hC⟩ := eqd_exp_bd ν hν s0 hs0 n
  have hmax : s0 ≤ max s1 s0 := le_max_right _ _
  have hνs : 0 < ν * max s1 s0 := mul_pos hν (lt_of_lt_of_le hs0 hmax)
  have ha1pos : 0 < 1 + ν * max s1 s0 := by linarith
  refine ⟨|C|, 1 / (4 * (1 + ν * max s1 s0)), 2 * n, div_pos one_pos (by linarith),
    fun z hz1 hz2 => ?_⟩
  have hloc : (fun p : Chart => Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)))
      =ᶠ[𝓝 z] (fun p : Chart => Real.exp (eqQ ν s0 p)) := by
    have hW : {p : Chart | s0 / 2 < p.1} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds (show s0 / 2 < z.1 by linarith)
    filter_upwards [hW] with p hp
    have hp' : s0 / 2 ≤ p.1 := (show s0 / 2 < p.1 from hp).le
    simp only [eqQ, ageSmoothT_eq s0 hs0 p.1 hp', ageA]
  rw [(hloc.iteratedFDeriv ℝ n).eq_of_nhds]
  have hsq : ‖z.2‖ ^ 2 ≤ sq2 z.2 := by
    have hn : ‖z.2‖ = max |z.2.1| |z.2.2| := by
      rw [Prod.norm_def]
      simp [Real.norm_eq_abs]
    rw [hn]
    unfold sq2
    rcases max_cases |z.2.1| |z.2.2| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_abs z.2.1, sq_abs z.2.2, sq_nonneg z.2.1, sq_nonneg z.2.2]
  have hAeq : ageSmoothT s0 z.1 = z.1 := ageSmoothT_eq s0 hs0 z.1 (by linarith)
  have hA0 : 0 < 1 + ν * z.1 := by
    have : 0 < ν * z.1 := mul_pos hν (by linarith)
    linarith
  have hAa : 1 + ν * z.1 ≤ 1 + ν * max s1 s0 := by
    have : ν * z.1 ≤ ν * max s1 s0 :=
      mul_le_mul_of_nonneg_left (hz2.trans (le_max_left _ _)) hν.le
    linarith
  have hS0 : 0 ≤ sq2 z.2 := by
    unfold sq2
    positivity
  have hQle : eqQ ν s0 z ≤ -(1 / (4 * (1 + ν * max s1 s0))) * ‖z.2‖ ^ 2 := by
    unfold eqQ
    rw [hAeq]
    have key : ‖z.2‖ ^ 2 / (4 * (1 + ν * max s1 s0)) ≤ sq2 z.2 / (4 * (1 + ν * z.1)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have h1 : ‖z.2‖ ^ 2 * (4 * (1 + ν * z.1)) ≤ sq2 z.2 * (4 * (1 + ν * z.1)) :=
        mul_le_mul_of_nonneg_right hsq (by linarith)
      have h2 : sq2 z.2 * (4 * (1 + ν * z.1)) ≤ sq2 z.2 * (4 * (1 + ν * max s1 s0)) :=
        mul_le_mul_of_nonneg_left (by linarith) hS0
      linarith
    have e : -(1 / (4 * (1 + ν * max s1 s0))) * ‖z.2‖ ^ 2
        = -(‖z.2‖ ^ 2 / (4 * (1 + ν * max s1 s0))) := by ring
    rw [neg_div, e]
    exact neg_le_neg key
  calc ‖iteratedFDeriv ℝ n (fun p : Chart => Real.exp (eqQ ν s0 p)) z‖
      ≤ C * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (eqQ ν s0 z) := hC z hz1
    _ ≤ |C| * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (eqQ ν s0 z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (Real.exp_pos _).le
    _ ≤ |C| * (1 + ‖z.2‖) ^ (2 * n) * Real.exp (-(1 / (4 * (1 + ν * max s1 s0))) * ‖z.2‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hQle) (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete
