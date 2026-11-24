import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Derivatives of `a^{-m}` with `a = 1 + ν s` on `s ≥ s0 > 0`

Task `ra_9_1_2_5_4_1`: for each order `k`, the `k`-th derivatives of `((ageA ν s)^m)⁻¹` on the
chart are bounded on `{s0 ≤ s}`, with a bound depending only on `ν, m, k`.

The explicit formula `iteratedDeriv k (fun t ↦ c * ((1 + ν t)^j)⁻¹) t
  = c * (-ν)^k * (∏ i < k, (j + i)) * ((1 + ν t)^(j + k))⁻¹` holds on the open set `0 < 1 + ν t`.
Since `t ↦ ((1 + ν t)^m)⁻¹` is not smooth globally, the chart function is compared with a globally
smooth function that agrees with it on `s0/2 < s`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Derivative of `c * ((1 + ν t)^j)⁻¹` on the open set `0 < 1 + ν t`. -/
lemma ageInvPow_hasDerivAt (ν : ℝ) (j : ℕ) (c t : ℝ) (ht : 0 < 1 + ν * t) :
    HasDerivAt (fun t => c * ((1 + ν * t) ^ j)⁻¹)
      (c * (-(j : ℝ) * ν) * ((1 + ν * t) ^ (j + 1))⁻¹) t := by
  have hx : (1 + ν * t) ≠ 0 := ht.ne'
  have hlin : HasDerivAt (fun t => 1 + ν * t) ν t := by
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  have hp := hlin.pow j
  have hi := hp.inv (pow_ne_zero j hx)
  have hc := hi.const_mul c
  have key : c * (-(j : ℝ) * ν) * ((1 + ν * t) ^ (j + 1))⁻¹
      = c * (-((j : ℝ) * (1 + ν * t) ^ (j - 1) * ν) / ((1 + ν * t) ^ j) ^ 2) := by
    rcases j with _ | m
    · simp
    · rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  exact hc.congr_deriv key.symm

/-- Explicit iterated derivatives of `c * ((1 + ν t)^j)⁻¹` on `0 < 1 + ν t`. -/
lemma ageInvPow_iter (ν : ℝ) (k : ℕ) :
    ∀ (j : ℕ) (c t : ℝ), 0 < 1 + ν * t →
      iteratedDeriv k (fun t => c * ((1 + ν * t) ^ j)⁻¹) t
        = c * (-ν) ^ k * (∏ i ∈ Finset.range k, ((j : ℝ) + i)) * ((1 + ν * t) ^ (j + k))⁻¹ := by
  induction k with
  | zero =>
    intro j c t ht
    simp
  | succ k ih =>
    intro j c t ht
    have hopen : {s : ℝ | 0 < 1 + ν * s} ∈ 𝓝 t :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds ht
    have hderiv : deriv (fun t => c * ((1 + ν * t) ^ j)⁻¹)
        =ᶠ[𝓝 t] fun s => (c * (-(j : ℝ) * ν)) * ((1 + ν * s) ^ (j + 1))⁻¹ := by
      filter_upwards [hopen] with s hs
      exact (ageInvPow_hasDerivAt ν j c s hs).deriv
    rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq k, ih (j + 1) (c * (-(j : ℝ) * ν)) t ht]
    have hprod : (∏ i ∈ Finset.range (k + 1), ((j : ℝ) + i))
        = (j : ℝ) * ∏ i ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) + i) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
    rw [hprod, show j + 1 + k = j + (k + 1) by omega]
    ring

/-- Bound for the derivatives of `((1 + ν t)^m)⁻¹` on `0 ≤ t`. -/
lemma ageInvPow_iter_bound (ν : ℝ) (hν : 0 ≤ ν) (m k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖iteratedDeriv k (fun t => ((1 + ν * t) ^ m)⁻¹) t‖
      ≤ ν ^ k * |∏ i ∈ Finset.range k, ((m : ℝ) + i)| := by
  have hpos : 0 < 1 + ν * t := by
    have := mul_nonneg hν ht
    linarith
  have h := ageInvPow_iter ν k m 1 t hpos
  simp only [one_mul] at h
  rw [h]
  have hY0 : 0 < ((1 + ν * t) ^ (m + k))⁻¹ := inv_pos.mpr (pow_pos hpos _)
  have hY1 : ((1 + ν * t) ^ (m + k))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    apply one_le_pow₀
    have := mul_nonneg hν ht
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos hY0, abs_of_nonneg hν]
  calc ν ^ k * |∏ i ∈ Finset.range k, ((m : ℝ) + i)| * ((1 + ν * t) ^ (m + k))⁻¹
      ≤ ν ^ k * |∏ i ∈ Finset.range k, ((m : ℝ) + i)| * 1 :=
        mul_le_mul_of_nonneg_left hY1 (mul_nonneg (pow_nonneg hν k) (abs_nonneg _))
    _ = ν ^ k * |∏ i ∈ Finset.range k, ((m : ℝ) + i)| := mul_one _

/-- A globally smooth truncation of `s ↦ s`: equal to `s` for `s0/2 ≤ s`, nonnegative. -/
def ageSmoothT (s0 : ℝ) (t : ℝ) : ℝ := Real.smoothTransition (4 * t / s0 - 1) * t

lemma ageSmoothT_contDiff (s0 : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ageSmoothT s0) := by
  unfold ageSmoothT
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 4 * t / s0 - 1) :=
    ((contDiff_const.mul contDiff_id).div_const s0).sub contDiff_const
  exact (Real.smoothTransition.contDiff.comp h1).mul contDiff_id

lemma ageSmoothT_eq (s0 : ℝ) (hs0 : 0 < s0) (t : ℝ) (ht : s0 / 2 ≤ t) :
    ageSmoothT s0 t = t := by
  unfold ageSmoothT
  have h1 : 1 ≤ 4 * t / s0 - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hs0]
    linarith
  rw [Real.smoothTransition.one_of_one_le h1, one_mul]

lemma ageSmoothT_nonneg (s0 : ℝ) (hs0 : 0 < s0) (t : ℝ) : 0 ≤ ageSmoothT s0 t := by
  unfold ageSmoothT
  rcases le_total t 0 with ht | ht
  · have h1 : 4 * t / s0 - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ hs0]
      linarith
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) ht

/-- The statement of the bound: `k`-th derivatives of `((ageA ν s)^m)⁻¹` on `s0 ≤ s` are uniformly
bounded. -/
theorem ageInvPow_iteratedFDeriv_bound (ν : ℝ) (hν : 0 < ν) (s0 : ℝ) (hs0 : 0 < s0) (m k : ℕ) : ∃ B : ℝ, ∀ z : Chart, s0 ≤ z.1 → ‖iteratedFDeriv ℝ k (fun p : Chart => ((ageA ν p.1) ^ m)⁻¹) z‖ ≤ B := by
  refine ⟨ν ^ k * |∏ i ∈ Finset.range k, ((m : ℝ) + i)|, fun z hz => ?_⟩
  -- the globally smooth replacement
  have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ((1 + ν * ageSmoothT s0 t) ^ m)⁻¹) := by
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 1 + ν * ageSmoothT s0 t) :=
      contDiff_const.add (contDiff_const.mul (ageSmoothT_contDiff s0))
    exact ContDiff.inv (hA.pow m) (fun t => pow_ne_zero m (by
      have := mul_nonneg hν.le (ageSmoothT_nonneg s0 hs0 t)
      linarith))
  -- agreement of the chart function with the replacement near `z`
  have hW : {p : Chart | s0 / 2 < p.1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (show s0 / 2 < z.1 by linarith)
  have hev : (fun p : Chart => ((ageA ν p.1) ^ m)⁻¹)
      =ᶠ[𝓝 z] (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ m)⁻¹) := by
    filter_upwards [hW] with p hp
    have hp' : s0 / 2 ≤ p.1 := (show s0 / 2 < p.1 from hp).le
    rw [ageSmoothT_eq s0 hs0 p.1 hp']
    rfl
  have hval : iteratedFDeriv ℝ k (fun p : Chart => ((ageA ν p.1) ^ m)⁻¹) z
      = iteratedFDeriv ℝ k (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ m)⁻¹) z :=
    (hev.iteratedFDeriv ℝ k).eq_of_nhds
  rw [hval]
  -- composition with the first projection
  have hcomp : (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ m)⁻¹)
      = (fun t : ℝ => ((1 + ν * ageSmoothT s0 t) ^ m)⁻¹)
          ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : Chart → ℝ) := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hGc z
    (show (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)]
  have hn := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k (fun t : ℝ => ((1 + ν * ageSmoothT s0 t) ^ m)⁻¹)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) z))
    (fun _ : Fin k => (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : Chart →L[ℝ] ℝ))
  have hprod : ∏ _i : Fin k, ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : Chart →L[ℝ] ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ))
  have hfst : (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : Chart →L[ℝ] ℝ) z = z.1 := rfl
  -- germ at `z.1` of the replacement and the explicit function
  have hgerm : (fun t : ℝ => ((1 + ν * ageSmoothT s0 t) ^ m)⁻¹)
      =ᶠ[𝓝 z.1] (fun t : ℝ => ((1 + ν * t) ^ m)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds
      (show s0 / 2 < z.1 by linarith)] with t ht
    have ht' : s0 / 2 ≤ t := (show s0 / 2 < t from ht).le
    rw [ageSmoothT_eq s0 hs0 t ht']
  have hb := ageInvPow_iter_bound ν hν.le m k z.1 (by linarith)
  have hG : ‖iteratedFDeriv ℝ k (fun t : ℝ => ((1 + ν * ageSmoothT s0 t) ^ m)⁻¹)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) z)‖
      = ‖iteratedDeriv k (fun t : ℝ => ((1 + ν * t) ^ m)⁻¹) z.1‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfst, hgerm.iteratedDeriv_eq k]
  refine hn.trans ?_
  calc _ ≤ ‖iteratedFDeriv ℝ k (fun t : ℝ => ((1 + ν * ageSmoothT s0 t) ^ m)⁻¹)
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedDeriv k (fun t : ℝ => ((1 + ν * t) ^ m)⁻¹) z.1‖ := by rw [mul_one, hG]
    _ ≤ ν ^ k * |∏ i ∈ Finset.range k, ((m : ℝ) + i)| := hb

end UnforcedLeray.Short.PartIIIb.Concrete
