import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `PartIII-b:C/rep/8/2/3/2/13`: the jet bound `TtCompJet` for the composed theta factor

Source of record: `the November 2 reference manuscript` 4963-4968, 5484-5495.
`φ(x) = ((2(1+νx.1))⁻¹, x.2.1)`, `G = IIb.tt (cOf ν) 0` on `{u | 0 < u.1}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Derivative of `c * ((1 + ν t)^j)⁻¹` on `0 < 1 + ν t`. -/
lemma ttcAffHasDeriv (ν : ℝ) (j : ℕ) (c t : ℝ) (ht : 0 < 1 + ν * t) :
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
lemma ttcAffIter (ν : ℝ) (k : ℕ) :
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
      exact (ttcAffHasDeriv ν j c s hs).deriv
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

/-- Bound for `k`-th derivatives of `t ↦ (2(1+νt))⁻¹` on `0 ≤ t`, by `(n+1)^k` for `k ≤ n`, `0 ≤ ν ≤ 1`. -/
lemma ttcAffIterBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n i : ℕ) (hi : i ≤ n) (t : ℝ)
    (ht : 0 ≤ t) :
    ‖iteratedDeriv i (fun t : ℝ => (2 * (1 + ν * t))⁻¹) t‖ ≤ ((n : ℝ) + 1) ^ i := by
  have hfun : (fun t : ℝ => (2 * (1 + ν * t))⁻¹) = fun t : ℝ => (1 / 2 : ℝ) * ((1 + ν * t) ^ 1)⁻¹ := by
    funext s
    rw [pow_one, mul_inv]
    ring
  have hpos : 0 < 1 + ν * t := by
    have := mul_nonneg hν0 ht
    linarith
  rw [hfun, ttcAffIter ν i 1 (1 / 2) t hpos]
  have hY0 : 0 < ((1 + ν * t) ^ (1 + i))⁻¹ := inv_pos.mpr (pow_pos hpos _)
  have hY1 : ((1 + ν * t) ^ (1 + i))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    apply one_le_pow₀
    linarith [mul_nonneg hν0 ht]
  have hP0 : 0 ≤ ∏ k ∈ Finset.range i, (((1 : ℕ) : ℝ) + k) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hP1 : ∏ k ∈ Finset.range i, (((1 : ℕ) : ℝ) + k) ≤ ((n : ℝ) + 1) ^ i := by
    have h := Finset.prod_le_prod (s := Finset.range i)
      (f := fun k : ℕ => (((1 : ℕ) : ℝ) + k)) (g := fun _ : ℕ => (n : ℝ) + 1)
      (fun k _ => by positivity) (fun k hk => by
        have h1 : (k : ℝ) < i := by exact_mod_cast Finset.mem_range.mp hk
        have h2 : (i : ℝ) ≤ n := by exact_mod_cast hi
        push_cast
        linarith)
    simpa [Finset.prod_const, Finset.card_range] using h
  have hnu : ν ^ i ≤ 1 := pow_le_one₀ hν0 hν1
  have hνi : 0 ≤ ν ^ i := pow_nonneg hν0 i
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hν0,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hP0, abs_of_pos hY0]
  have hA : 1 / 2 * ν ^ i * ((1 + ν * t) ^ (1 + i))⁻¹ ≤ 1 := by
    have h1 : 1 / 2 * ν ^ i ≤ 1 := by linarith
    have h2 : 1 / 2 * ν ^ i * ((1 + ν * t) ^ (1 + i))⁻¹ ≤ 1 * 1 :=
      mul_le_mul h1 hY1 hY0.le (by norm_num)
    linarith
  have hfin := mul_le_mul_of_nonneg_right hA hP0
  have hPn : 1 * (∏ k ∈ Finset.range i, (((1 : ℕ) : ℝ) + k)) ≤ ((n : ℝ) + 1) ^ i := by
    rw [one_mul]; exact hP1
  have e : 1 / 2 * ν ^ i * (∏ k ∈ Finset.range i, (((1 : ℕ) : ℝ) + k)) * ((1 + ν * t) ^ (1 + i))⁻¹
      = (1 / 2 * ν ^ i * ((1 + ν * t) ^ (1 + i))⁻¹) * (∏ k ∈ Finset.range i, (((1 : ℕ) : ℝ) + k)) := by
    ring
  rw [e]
  exact hfin.trans hPn

/-- The open set `{x : ℝ × Plane | 0 < x.1}`. -/
def ttcUfst : Set (ℝ × Plane) := (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) ⁻¹' Ioi 0

lemma ttcIsOpenUfst : IsOpen ttcUfst :=
  isOpen_Ioi.preimage (ContinuousLinearMap.fst ℝ ℝ Plane).continuous

lemma ttcMemUfst {x : ℝ × Plane} : x ∈ ttcUfst ↔ 0 < x.1 := Iff.rfl

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

/-- The inner map `x ↦ (2(1+νx.1))⁻¹` is smooth on `ttcUfst`. -/
lemma ttcInnerCDO (ν : ℝ) (hν0 : 0 ≤ ν) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) ttcUfst := by
  have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => 2 * (1 + ν * t)) (Ioi 0) :=
    (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => 2 * (1 + ν * t))).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => (2 * (1 + ν * t))⁻¹) (Ioi 0) :=
    h1.inv (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have := mul_nonneg hν0 ht'.le
      exact ne_of_gt (by linarith))
  have hfst : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) x) ttcUfst :=
    (ContinuousLinearMap.fst ℝ ℝ Plane).contDiff.contDiffOn
  exact h2.comp hfst (fun x hx => hx)

/-- The inner first component: `i`-th derivative bound. -/
lemma ttcInnerBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n i : ℕ) (hi : i ≤ n)
    (y : ℝ × Plane) (hy : y ∈ ttcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) ttcUfst y‖
      ≤ ((n : ℝ) + 1) ^ i := by
  have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => 2 * (1 + ν * t)) (Ioi 0) :=
    (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => 2 * (1 + ν * t))).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun t : ℝ => (2 * (1 + ν * t))⁻¹) (Ioi 0) :=
    h1.inv (fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have := mul_nonneg hν0 ht'.le
      exact ne_of_gt (by linarith))
  have hy' : (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y ∈ Ioi (0 : ℝ) := hy
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) h2 isOpen_Ioi.uniqueDiffOn
    ttcIsOpenUfst.uniqueDiffOn hy' (i := i)
    (show (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
  have key : iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) ttcUfst y
      = (iteratedFDerivWithin ℝ i (fun t : ℝ => (2 * (1 + ν * t))⁻¹) (Ioi 0)
          ((ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y)).compContinuousLinearMap
          (fun _ => (ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ)) := hcomp
  rw [key]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin i, ‖(ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ Plane)
  have hG : ‖iteratedFDerivWithin ℝ i (fun t : ℝ => (2 * (1 + ν * t))⁻¹) (Ioi 0)
      ((ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y)‖ ≤ ((n : ℝ) + 1) ^ i := by
    rw [(iteratedFDerivWithin_of_isOpen i isOpen_Ioi) hy', norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact ttcAffIterBound ν hν0 hν1 n i hi y.1 (le_of_lt hy)
  calc _ ≤ ‖iteratedFDerivWithin ℝ i (fun t : ℝ => (2 * (1 + ν * t))⁻¹) (Ioi 0)
          ((ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ) y)‖ *
            ∏ _j : Fin i, ‖(ContinuousLinearMap.fst ℝ ℝ Plane : ℝ × Plane →L[ℝ] ℝ)‖ :=
        le_rfl
    _ ≤ ((n : ℝ) + 1) ^ i * 1 := mul_le_mul hG hprod (by positivity) (by positivity)
    _ = ((n : ℝ) + 1) ^ i := mul_one _

/-- The second component `x ↦ x.2.1`: derivative bound by `1`. -/
lemma ttcSndBound (i : ℕ) (hi : 1 ≤ i) (y : ℝ × Plane) (hy : y ∈ ttcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => x.2.1) ttcUfst y‖ ≤ 1 := by
  set L : ℝ × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane) with hLdef
  have hL : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
    have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ Plane
    have h3 : (0 : ℝ) ≤ ‖(ContinuousLinearMap.snd ℝ ℝ Plane : ℝ × Plane →L[ℝ] Plane)‖ :=
      norm_nonneg _
    nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ ℝ : Plane →L[ℝ] ℝ)]
  show ‖iteratedFDerivWithin ℝ i (⇑L) ttcUfst y‖ ≤ 1
  rw [(iteratedFDerivWithin_of_isOpen i ttcIsOpenUfst) hy]
  exact (ttcClmIter L i hi y).trans hL

/-- The pair map `φ(x) = ((2(1+νx.1))⁻¹, x.2.1)`: derivative bound by `(n+1)^i`. -/
lemma ttcPairBound (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ n)
    (y : ℝ × Plane) (hy : y ∈ ttcUfst) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) ttcUfst y‖
      ≤ ((n : ℝ) + 1) ^ i := by
  have hc1 : ContDiffWithinAt ℝ ∞ (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) ttcUfst y :=
    (ttcInnerCDO ν hν0).contDiffWithinAt hy
  have hc2 : ContDiffWithinAt ℝ ∞ (fun x : ℝ × Plane => x.2.1) ttcUfst y :=
    (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => x.2.1)).contDiffWithinAt
  have hsplit : iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1))
      ttcUfst y
      = (iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => (2 * (1 + ν * x.1))⁻¹) ttcUfst y).prod
        (iteratedFDerivWithin ℝ i (fun x : ℝ × Plane => x.2.1) ttcUfst y) :=
    iteratedFDerivWithin_prodMk hc1 hc2 ttcIsOpenUfst.uniqueDiffOn hy
      (show (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
  rw [hsplit, ContinuousMultilinearMap.opNorm_prod]
  have hP := ttcInnerBound ν hν0 hν1 n i hi y hy
  have hQ := ttcSndBound i hi1 y hy
  have hone : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ i := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact max_le hP (hQ.trans hone)

/-- **Composed theta jet** (source 4963-4968, 5484-5495): the joint derivatives of
`(s,q,η) ↦ IIb.tt (cOf ν) 0 ((2(1+νs))⁻¹, q)` on `0 < s ≤ 1/ν` are bounded uniformly in `ν ≤ 1/2`. -/
theorem ttCompJet_of (h : TtJetBound) : TtCompJet := by
  have h' := h
  unfold TtJetBound at h'
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ x : ℝ × ℝ, 1 / 5 ≤ x.1 → x.1 ≤ 1 →
      ‖iteratedFDeriv ℝ i (UnforcedLeray.Short.IIb.tt c 0) x‖ ≤ K :=
    fun i => h' i 0
  choose K hK using hK
  unfold TtCompJet
  intro n
  refine ⟨(n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), |K i|) * ((n : ℝ) + 1) ^ n, ?_⟩
  intro ν hν0 hν1 y hy0 hy1
  have hν0' : (0 : ℝ) ≤ ν := hν0.le
  have hν1' : ν ≤ 1 := by linarith
  have hy : y ∈ ttcUfst := hy0
  set C : ℝ := ∑ i ∈ Finset.range (n + 1), |K i| with hCdef
  have hTopen : IsOpen {x : ℝ × ℝ | 0 < x.1} :=
    isOpen_lt continuous_const continuous_fst
  have hG : ContDiffOn ℝ ∞ (UnforcedLeray.Short.IIb.tt (cOf ν) 0) {x : ℝ × ℝ | 0 < x.1} :=
    UnforcedLeray.Short.IIb.contDiffOn_tt_infty (inv_pos.mpr (pow_pos hν0 2)).ne' 0
  have hφC : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) ttcUfst :=
    (ttcInnerCDO ν hν0').prodMk
      (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ × Plane => x.2.1)).contDiffOn
  have hMaps : Set.MapsTo (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) ttcUfst
      {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx
    have hx' : (0 : ℝ) < x.1 := hx
    show (0 : ℝ) < (2 * (1 + ν * x.1))⁻¹
    have := mul_nonneg hν0' hx'.le
    exact inv_pos.mpr (by linarith)
  -- the point `φ y` lies in `[1/5, 1]` in its first coordinate
  have hνy : ν * y.1 ≤ 1 := by
    have := (le_div_iff₀ hν0).mp hy1
    linarith
  have hφy1 : 1 / 5 ≤ ((2 * (1 + ν * y.1))⁻¹ : ℝ) := by
    have hpos : (0 : ℝ) < 2 * (1 + ν * y.1) := by
      have := mul_nonneg hν0' hy0.le
      linarith
    calc (1 : ℝ) / 5 = (5 : ℝ)⁻¹ := by norm_num
      _ ≤ (2 * (1 + ν * y.1))⁻¹ := inv_anti₀ hpos (by nlinarith)
  have hφy2 : ((2 * (1 + ν * y.1))⁻¹ : ℝ) ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have := mul_nonneg hν0' hy0.le
    linarith
  have hc2 : (2 : ℝ) ≤ cOf ν := by
    unfold cOf
    have hp : (0 : ℝ) < ν ^ 2 := pow_pos hν0 2
    have hle : ν ^ 2 ≤ 1 / 4 := by nlinarith
    have := inv_anti₀ hp hle
    norm_num at this
    linarith
  have hφy : (fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) y ∈ {x : ℝ × ℝ | 0 < x.1} :=
    hMaps hy
  have hCi : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i (UnforcedLeray.Short.IIb.tt (cOf ν) 0)
      {x : ℝ × ℝ | 0 < x.1} ((fun x : ℝ × Plane => ((2 * (1 + ν * x.1))⁻¹, x.2.1)) y)‖ ≤ C := by
    intro i hi
    rw [(iteratedFDerivWithin_of_isOpen i hTopen) hφy]
    have hb := hK i (cOf ν) hc2 ((2 * (1 + ν * y.1))⁻¹, y.2.1) hφy1 hφy2
    have hsum : |K i| ≤ C :=
      Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have := le_abs_self (K i)
    linarith
  have hout := norm_iteratedFDerivWithin_comp_le (N := ∞) (n := n) (C := C)
    (D := (n : ℝ) + 1) hG hφC
    (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
    hTopen.uniqueDiffOn ttcIsOpenUfst.uniqueDiffOn hMaps hy hCi
    (fun i hi1 hi => ttcPairBound ν hν0' hν1' n i hi1 hi y hy)
  rw [← (iteratedFDerivWithin_of_isOpen n ttcIsOpenUfst) hy]
  exact hout

end UnforcedLeray.Short.PartIIIb.Concrete
