import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `PartIII-b:C/rep/8/2/3/2/12`: the Gaussian envelope jet bound `PcEnvJet`

Source of record: `the November 2 reference manuscript` 4963-4968, 5484-5495.
On `U = {x : ℝ × Plane | 0 < x.1}`, the envelope
`E(x) = -((1 + ν x.1)^3)⁻¹ * exp(-x.2.2² / (2(1 + ν x.1)))` factors as `A(x) * exp(g(x))`
with `A(x) = -((1 + ν x.1)^3)⁻¹` and `g(x) = (-x.2.2²) * (2(1 + ν x.1))⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Derivative of `c * ((1 + ν t)^j)⁻¹` on `0 < 1 + ν t`. -/
lemma pcAffHasDeriv (ν : ℝ) (j : ℕ) (c t : ℝ) (ht : 0 < 1 + ν * t) :
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
lemma pcAffIter (ν : ℝ) (k : ℕ) :
    ∀ (j : ℕ) (c t : ℝ), 0 < 1 + ν * t →
      iteratedDeriv k (fun t => c * ((1 + ν * t) ^ j)⁻¹) t
        = c * (-ν) ^ k * (∏ i ∈ Finset.range k, ((j : ℝ) + i)) * ((1 + ν * t) ^ (j + k))⁻¹ := by
  induction k with
  | zero =>
    intro j c t _ht
    simp
  | succ k ih =>
    intro j c t ht
    have hopen : {s : ℝ | 0 < 1 + ν * s} ∈ 𝓝 t :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds ht
    have hderiv : deriv (fun t => c * ((1 + ν * t) ^ j)⁻¹)
        =ᶠ[𝓝 t] fun s => (c * (-(j : ℝ) * ν)) * ((1 + ν * s) ^ (j + 1))⁻¹ := by
      filter_upwards [hopen] with s hs
      exact (pcAffHasDeriv ν j c s hs).deriv
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

/-- Bound for the `i`-th derivative of `t ↦ c * ((1 + ν t)^j)⁻¹` on `0 ≤ t` when `|c| ≤ 1`. -/
lemma pcAffIterBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (c : ℝ) (hc : |c| ≤ 1)
    (j n i : ℕ) (hi : i ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ‖iteratedDeriv i (fun t : ℝ => c * ((1 + ν * t) ^ j)⁻¹) t‖ ≤ ((n : ℝ) + j) ^ i := by
  have hpos : 0 < 1 + ν * t := by
    have := mul_nonneg hν0 ht
    linarith
  rw [pcAffIter ν i j c t hpos]
  have hY0 : 0 < ((1 + ν * t) ^ (j + i))⁻¹ := inv_pos.mpr (pow_pos hpos _)
  have hY1 : ((1 + ν * t) ^ (j + i))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    apply one_le_pow₀
    linarith [mul_nonneg hν0 ht]
  have hP0 : 0 ≤ ∏ k ∈ Finset.range i, ((j : ℝ) + k) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hP1 : ∏ k ∈ Finset.range i, ((j : ℝ) + k) ≤ ((n : ℝ) + j) ^ i := by
    have h := Finset.prod_le_prod (s := Finset.range i)
      (f := fun k : ℕ => ((j : ℝ) + k)) (g := fun _ : ℕ => (n : ℝ) + j)
      (fun k _ => by positivity) (fun k hk => by
        have h1 : (k : ℝ) < i := by exact_mod_cast Finset.mem_range.mp hk
        have h2 : (i : ℝ) ≤ n := by exact_mod_cast hi
        linarith)
    simpa [Finset.prod_const, Finset.card_range] using h
  have hnu : ν ^ i ≤ 1 := pow_le_one₀ hν0 hν1
  have hνi : 0 ≤ ν ^ i := pow_nonneg hν0 i
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hν0,
    abs_of_nonneg hP0, abs_of_pos hY0]
  have hA : |c| * ν ^ i * ((1 + ν * t) ^ (j + i))⁻¹ ≤ 1 := by
    have h1 : |c| * ν ^ i ≤ 1 * 1 := mul_le_mul hc hnu hνi (by norm_num)
    have h2 : |c| * ν ^ i * ((1 + ν * t) ^ (j + i))⁻¹ ≤ 1 * 1 :=
      mul_le_mul (by linarith) hY1 hY0.le (by norm_num)
    linarith
  have hfin := mul_le_mul_of_nonneg_right hA hP0
  have e : |c| * ν ^ i * (∏ k ∈ Finset.range i, ((j : ℝ) + k)) * ((1 + ν * t) ^ (j + i))⁻¹
      = (|c| * ν ^ i * ((1 + ν * t) ^ (j + i))⁻¹) * (∏ k ∈ Finset.range i, ((j : ℝ) + k)) := by
    ring
  rw [e]
  exact hfin.trans (by linarith)

/-- The open set `{x : ℝ × Plane | 0 < x.1}`. -/
def pcUfst : Set (ℝ × Plane) := (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) ⁻¹' Ioi 0

lemma pcIsOpenUfst : IsOpen pcUfst :=
  isOpen_Ioi.preimage (ContinuousLinearMap.fst ℝ ℝ Plane).continuous

/-- Smoothness of `x ↦ c * ((1 + ν x.1)^j)⁻¹` on `pcUfst`. -/
lemma pcAffCDO (ν : ℝ) (hν0 : 0 ≤ ν) (c : ℝ) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => c * ((1 + ν * x.1) ^ j)⁻¹) pcUfst := by
  have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => (1 + ν * t) ^ j) (Ioi 0) :=
    (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (1 + ν * t) ^ j)).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => c * ((1 + ν * t) ^ j)⁻¹) (Ioi 0) :=
    contDiffOn_const.mul (h1.inv (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have := mul_nonneg hν0 ht'.le
      exact pow_ne_zero j (ne_of_gt (by linarith))))
  have hfst : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) x) pcUfst :=
    (ContinuousLinearMap.fst ℝ ℝ Plane).contDiff.contDiffOn
  exact h2.comp hfst (fun _ hx => hx)

/-- Derivative bound for `x ↦ c * ((1 + ν x.1)^j)⁻¹` on `pcUfst`. -/
lemma pcAffJetBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (c : ℝ) (hc : |c| ≤ 1)
    (j n i : ℕ) (hi : i ≤ n) (y : ℝ × Plane) (hy : y ∈ pcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => c * ((1 + ν * x.1) ^ j)⁻¹) pcUfst y‖
      ≤ ((n : ℝ) + j) ^ i := by
  have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => (1 + ν * t) ^ j) (Ioi 0) :=
    (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (1 + ν * t) ^ j)).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => c * ((1 + ν * t) ^ j)⁻¹) (Ioi 0) :=
    contDiffOn_const.mul (h1.inv (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have := mul_nonneg hν0 ht'.le
      exact pow_ne_zero j (ne_of_gt (by linarith))))
  have hy' : (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y ∈ Ioi (0 : ℝ) := hy
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) h2 isOpen_Ioi.uniqueDiffOn
    pcIsOpenUfst.uniqueDiffOn hy' (i := i)
    (show (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
  have key : iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => c * ((1 + ν * x.1) ^ j)⁻¹) pcUfst y
      = (iteratedFDerivWithin ℝ i (fun t : ℝ => c * ((1 + ν * t) ^ j)⁻¹) (Ioi 0)
          ((ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y)).compContinuousLinearMap
          (fun _ => (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ)) := hcomp
  rw [key]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _k : Fin i, ‖(ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ Plane)
  have hG : ‖iteratedFDerivWithin ℝ i (fun t : ℝ => c * ((1 + ν * t) ^ j)⁻¹) (Ioi 0)
      ((ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y)‖ ≤ ((n : ℝ) + j) ^ i := by
    rw [(iteratedFDerivWithin_of_isOpen i isOpen_Ioi) hy', norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact pcAffIterBound ν hν0 hν1 c hc j n i hi y.1 (le_of_lt hy)
  calc _ ≤ ((n : ℝ) + j) ^ i * 1 := mul_le_mul hG hprod (by positivity) (by positivity)
    _ = ((n : ℝ) + j) ^ i := mul_one _

/-- Iterated derivative of the zero function is zero. -/
lemma pcIterZero (m : ℕ) (η : ℝ) : iteratedDeriv m (fun _ : ℝ => (0 : ℝ)) η = 0 := by
  induction m generalizing η with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => (0 : ℝ) :=
      funext fun t => deriv_const t (0 : ℝ)
    rw [hd, ih]

/-- 1D derivatives of `t ↦ -t^2` are bounded by `2 * (1 + t^2)`. -/
lemma pcNegSq1DBound (k : ℕ) (η : ℝ) :
    ‖iteratedDeriv k (fun t : ℝ => -t ^ 2) η‖ ≤ 2 * (1 + η ^ 2) := by
  have hd1 : deriv (fun t : ℝ => -t ^ 2) = fun t : ℝ => -(2 * t) := by
    funext t
    simp
  have hd2 : deriv (fun t : ℝ => -(2 * t)) = fun _ : ℝ => (-2 : ℝ) := by
    funext t
    simp
  have hd3 : deriv (fun _ : ℝ => (-2 : ℝ)) = fun _ : ℝ => (0 : ℝ) :=
    funext fun t => deriv_const t (-2 : ℝ)
  match k with
  | 0 =>
    rw [iteratedDeriv_zero, Real.norm_eq_abs, abs_neg, abs_sq]
    nlinarith [sq_nonneg η]
  | 1 =>
    rw [iteratedDeriv_one, hd1, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos two_pos]
    have hsq : 0 ≤ (1 - |η|) ^ 2 := sq_nonneg (1 - |η|)
    have habs : |η| ^ 2 = η ^ 2 := sq_abs η
    nlinarith
  | 2 =>
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', hd1, iteratedDeriv_one, hd2,
      Real.norm_eq_abs]
    norm_num
    nlinarith [sq_nonneg η]
  | k + 3 =>
    rw [show k + 3 = (k + 2) + 1 from rfl, iteratedDeriv_succ', hd1,
      show k + 2 = (k + 1) + 1 from rfl, iteratedDeriv_succ', hd2,
      iteratedDeriv_succ', hd3, pcIterZero k η, norm_zero]
    positivity

/-- Joint derivatives of `x ↦ -x.2.2^2` on `pcUfst` are bounded by `2 * (1 + y.2.2^2)`. -/
lemma pcNegSqJetBound (k : ℕ) (y : ℝ × Plane) (hy : y ∈ pcUfst) :
    ‖iteratedFDerivWithin ℝ k (fun x : ℝ × Plane => -x.2.2 ^ 2) pcUfst y‖ ≤ 2 * (1 + y.2.2 ^ 2) := by
  rw [(iteratedFDerivWithin_of_isOpen k pcIsOpenUfst) hy]
  set L : ℝ × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane) with hLdef
  have hL : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ Plane
    nlinarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ ℝ : Plane →L[ℝ] ℝ),
      norm_nonneg (ContinuousLinearMap.snd ℝ ℝ Plane : ℝ × Plane →L[ℝ] Plane)]
  have e : (fun x : ℝ × Plane => -x.2.2 ^ 2) = (fun t : ℝ => -t ^ 2) ∘ L := rfl
  have hcd : ContDiff ℝ ∞ (fun t : ℝ => -t ^ 2) := by fun_prop
  have hk : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [e, L.iteratedFDeriv_comp_right hcd y hk]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin k, ‖L‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  have h1D : ‖iteratedFDeriv ℝ k (fun t : ℝ => -t ^ 2) (L y)‖ ≤ 2 * (1 + y.2.2 ^ 2) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact pcNegSq1DBound k y.2.2
  calc _ ≤ (2 * (1 + y.2.2 ^ 2)) * 1 := mul_le_mul h1D hprod (by positivity) (by positivity)
    _ = 2 * (1 + y.2.2 ^ 2) := mul_one _

/-- Derivative bound for the exponent `g(x) = -x.2.2^2 / (2(1 + ν x.1))` for `1 ≤ i ≤ m`. -/
lemma pcExponentJetBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (m i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ m)
    (y : ℝ × Plane) (hy : y ∈ pcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => -x.2.2 ^ 2 / (2 * (1 + ν * x.1))) pcUfst y‖
      ≤ (4 * ((m : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ i := by
  have hfun : (fun x : ℝ × Plane => -x.2.2 ^ 2 / (2 * (1 + ν * x.1)))
      = fun x : ℝ × Plane => (-x.2.2 ^ 2) * ((1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) := by
    funext x
    rw [pow_one, div_eq_mul_inv, mul_inv]
    ring
  rw [hfun]
  have hq : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => -x.2.2 ^ 2) pcUfst :=
    (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => -x.2.2 ^ 2)).contDiffOn
  have hh : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst :=
    pcAffCDO ν hν0 (1 / 2) 1
  have hleib := norm_iteratedFDerivWithin_mul_le hq hh pcIsOpenUfst.uniqueDiffOn hy
    (n := i) (by exact_mod_cast le_top)
  refine hleib.trans ?_
  have hterm : ∀ k ∈ Finset.range (i + 1),
      (i.choose k : ℝ) * ‖iteratedFDerivWithin ℝ k (fun x : ℝ × Plane => -x.2.2 ^ 2) pcUfst y‖ *
        ‖iteratedFDerivWithin ℝ (i - k)
          (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst y‖
      ≤ (i.choose k : ℝ) * ((2 * (1 + y.2.2 ^ 2)) * ((m : ℝ) + 1) ^ i) := by
    intro k hk
    have hk' : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have ha := pcNegSqJetBound k y hy
    have hb1 : ‖iteratedFDerivWithin ℝ (i - k)
        (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst y‖
        ≤ ((m : ℝ) + 1) ^ (i - k) := by
      simpa using pcAffJetBound ν hν0 hν1 (1 / 2) (by norm_num) 1 m (i - k) (by omega) y hy
    have hb : ‖iteratedFDerivWithin ℝ (i - k)
        (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst y‖ ≤ ((m : ℝ) + 1) ^ i :=
      hb1.trans (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (by omega))
    have hc0 : (0 : ℝ) ≤ (i.choose k : ℝ) := Nat.cast_nonneg _
    have hab : ‖iteratedFDerivWithin ℝ k (fun x : ℝ × Plane => -x.2.2 ^ 2) pcUfst y‖ *
        ‖iteratedFDerivWithin ℝ (i - k)
          (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst y‖
        ≤ (2 * (1 + y.2.2 ^ 2)) * ((m : ℝ) + 1) ^ i :=
      mul_le_mul ha hb (norm_nonneg _) (by positivity)
    calc (i.choose k : ℝ) * ‖iteratedFDerivWithin ℝ k (fun x : ℝ × Plane => -x.2.2 ^ 2) pcUfst y‖ *
          ‖iteratedFDerivWithin ℝ (i - k)
            (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst y‖
        = (i.choose k : ℝ) * (‖iteratedFDerivWithin ℝ k (fun x : ℝ × Plane => -x.2.2 ^ 2) pcUfst y‖ *
          ‖iteratedFDerivWithin ℝ (i - k)
            (fun x : ℝ × Plane => (1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) pcUfst y‖) := by ring
      _ ≤ (i.choose k : ℝ) * ((2 * (1 + y.2.2 ^ 2)) * ((m : ℝ) + 1) ^ i) :=
          mul_le_mul_of_nonneg_left hab hc0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hchoose : (∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)) = (2 : ℝ) ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  rw [hchoose]
  have hpow : 2 * (1 + y.2.2 ^ 2) ≤ (2 * (1 + y.2.2 ^ 2)) ^ i :=
    le_self_pow₀ (by nlinarith [sq_nonneg y.2.2]) (by omega)
  calc (2 : ℝ) ^ i * (2 * (1 + y.2.2 ^ 2) * ((m : ℝ) + 1) ^ i)
      = (2 : ℝ) ^ i * ((m : ℝ) + 1) ^ i * (2 * (1 + y.2.2 ^ 2)) := by ring
    _ ≤ (2 : ℝ) ^ i * ((m : ℝ) + 1) ^ i * (2 * (1 + y.2.2 ^ 2)) ^ i :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (4 * ((m : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ i := by
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring

/-- Absorption of `(1 + η^2)^m` by `exp(-η^2 / 4)`. -/
lemma pcWeightAbsorb (m : ℕ) (η : ℝ) :
    (1 + η ^ 2) ^ m * Real.exp (-η ^ 2 / 4) ≤ 4 ^ m * Real.exp 1 * (m.factorial : ℝ) := by
  set t := η ^ 2 / 4 with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 : 1 + η ^ 2 ≤ 4 * (1 + t) := by rw [ht]; linarith
  have h2 : (1 + η ^ 2) ^ m ≤ 4 ^ m * (1 + t) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 m
  have h3 := UnforcedLeray.Gaussian.pow_mul_exp_neg_le_factorial m (s := 1 + t) (by linarith)
  have he : Real.exp (-η ^ 2 / 4) = Real.exp 1 * Real.exp (-(1 + t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht]
    ring
  calc (1 + η ^ 2) ^ m * Real.exp (-η ^ 2 / 4)
      ≤ (4 ^ m * (1 + t) ^ m) * Real.exp (-η ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 4 ^ m * Real.exp 1 * ((1 + t) ^ m * Real.exp (-(1 + t))) := by rw [he]; ring
    _ ≤ 4 ^ m * Real.exp 1 * (m.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Constant bounding the `m`-th derivative of the Gaussian factor. -/
def pcKexp (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (4 * ((m : ℝ) + 1)) ^ m * (4 ^ m * Real.exp 1 * (m.factorial : ℝ))

/-- Uniform jet bound for the Gaussian factor `exp(-x.2.2^2 / (2(1 + ν x.1)))` on `0 < y.1 ≤ 1/ν`. -/
lemma pcExpJetBound (m : ℕ) (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (y : ℝ × Plane) (hy0 : 0 < y.1) (hy1 : y.1 ≤ 1 / ν) :
    ‖iteratedFDerivWithin ℝ m
        (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) pcUfst y‖
      ≤ pcKexp m := by
  have hy : y ∈ pcUfst := hy0
  have hν0' : 0 ≤ ν := hν0.le
  set f : ℝ × Plane → ℝ := fun x => -x.2.2 ^ 2 / (2 * (1 + ν * x.1)) with hfdef
  have hfC : ContDiffOn ℝ ∞ f pcUfst := by
    have hfun : f = fun x : ℝ × Plane => (-x.2.2 ^ 2) * ((1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) := by
      funext x
      simp only [hfdef, pow_one, div_eq_mul_inv, mul_inv]
      ring
    rw [hfun]
    exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => -x.2.2 ^ 2)).contDiffOn.mul
      (pcAffCDO ν hν0' (1 / 2) 1)
  have hνy : ν * y.1 ≤ 1 := by
    have := (le_div_iff₀ hν0).mp hy1
    linarith
  have hfy : f y ≤ -y.2.2 ^ 2 / 4 := by
    simp only [hfdef]
    have hden : 0 < 2 * (1 + ν * y.1) := by linarith [mul_nonneg hν0' hy0.le]
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith [sq_nonneg y.2.2]
  have hCi : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i Real.exp (univ : Set ℝ) (f y)‖ ≤ Real.exp (-y.2.2 ^ 2 / 4) := by
    intro i _hi
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hfy
  have hout := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := f)
    (t := (univ : Set ℝ)) (s := pcUfst) (N := ∞) (n := m)
    (C := Real.exp (-y.2.2 ^ 2 / 4)) (D := 4 * ((m : ℝ) + 1) * (1 + y.2.2 ^ 2))
    Real.contDiff_exp.contDiffOn hfC
    (show (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
    uniqueDiffOn_univ pcIsOpenUfst.uniqueDiffOn (mapsTo_univ _ _) hy hCi
    (fun i hi1 hi => pcExponentJetBound ν hν0' hν1 m i hi1 hi y hy)
  change ‖iteratedFDerivWithin ℝ m (Real.exp ∘ f) pcUfst y‖ ≤ pcKexp m
  refine hout.trans ?_
  unfold pcKexp
  have hpow : (4 * ((m : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ m
      = (4 * ((m : ℝ) + 1)) ^ m * (1 + y.2.2 ^ 2) ^ m := mul_pow _ _ _
  have habs := pcWeightAbsorb m y.2.2
  calc (m.factorial : ℝ) * Real.exp (-y.2.2 ^ 2 / 4) * (4 * ((m : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ m
      = (m.factorial : ℝ) * (4 * ((m : ℝ) + 1)) ^ m *
          ((1 + y.2.2 ^ 2) ^ m * Real.exp (-y.2.2 ^ 2 / 4)) := by rw [hpow]; ring
    _ ≤ (m.factorial : ℝ) * (4 * ((m : ℝ) + 1)) ^ m * (4 ^ m * Real.exp 1 * (m.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left habs (by positivity)

/-- **The Gaussian envelope** `-a⁻³e^{-η²/(2a)}`, `a = 1+νs`: bounded joint derivatives of each
order on `0 < s ≤ 1/ν`, uniformly in `ν ≤ 1`. -/
theorem pcEnvJet : PcEnvJet := by
  unfold PcEnvJet
  intro n
  refine ⟨∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ((n : ℝ) + 3) ^ i * pcKexp (n - i), ?_⟩
  intro ν hν0 hν1 y hy0 hy1
  have hy : y ∈ pcUfst := hy0
  have hν0' : 0 ≤ ν := hν0.le
  rw [← (iteratedFDerivWithin_of_isOpen n pcIsOpenUfst) hy]
  have hfun : (fun x : ℝ × Plane =>
      -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1))))
      = fun x : ℝ × Plane =>
        ((-1 : ℝ) * ((1 + ν * x.1) ^ 3)⁻¹) * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1))) := by
    funext x
    ring
  rw [hfun]
  have hA : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (-1 : ℝ) * ((1 + ν * x.1) ^ 3)⁻¹) pcUfst :=
    pcAffCDO ν hν0' (-1) 3
  have hE : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) pcUfst := by
    have hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => -x.2.2 ^ 2 / (2 * (1 + ν * x.1))) pcUfst := by
      have hfeq : (fun x : ℝ × Plane => -x.2.2 ^ 2 / (2 * (1 + ν * x.1)))
          = fun x : ℝ × Plane => (-x.2.2 ^ 2) * ((1 / 2 : ℝ) * ((1 + ν * x.1) ^ 1)⁻¹) := by
        funext x
        rw [pow_one, div_eq_mul_inv, mul_inv]
        ring
      rw [hfeq]
      exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => -x.2.2 ^ 2)).contDiffOn.mul
        (pcAffCDO ν hν0' (1 / 2) 1)
    exact hf.exp
  have hL := norm_iteratedFDerivWithin_mul_le hA hE pcIsOpenUfst.uniqueDiffOn hy
    (n := n) (by exact_mod_cast le_top)
  refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have ha := pcAffJetBound ν hν0' hν1 (-1) (by norm_num) 3 n i hi' y hy
  have hb := pcExpJetBound (n - i) ν hν0 hν1 y hy0 hy1
  have hc0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  have ha' : ‖iteratedFDerivWithin ℝ i
      (fun x : ℝ × Plane => (-1 : ℝ) * ((1 + ν * x.1) ^ 3)⁻¹) pcUfst y‖ ≤ ((n : ℝ) + (3 : ℕ)) ^ i :=
    ha
  push_cast at ha'
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha' hc0) hb (norm_nonneg _) (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete

end
