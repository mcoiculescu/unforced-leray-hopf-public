import UnforcedLeray.Short.PartI.Sub.PartI_T25_3
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Envelope jet bound and age-jet-to-joint-jet domination for `PartI:T25/3/1`

Source of record: `the November 2 reference manuscript`, lines 468–478, 543–551,
4963–4968.

Adapts the Gaussian pressure envelope jet bound (`PcEnv.lean`) and age-to-joint derivative bound
(`AgeJetJoint.lean`) to arbitrary slow-age horizon `0 < s ≤ Sg / ν` (`Sg > 0`, `0 < ν ≤ 1`) and
transverse polynomial weight `(1 + η ^ 2) ^ w`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.PcTwoMulMAux

open UnforcedLeray.Cyl (Plane)

/-! ### 1. Age-jet domination by joint spacetime Fréchet derivative -/

/-- The spatial jet at fixed age is bounded by the joint jet at the same point. -/
theorem alj_slice_le {G : ℝ × Plane → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    (m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖iteratedFDeriv ℝ m (fun z' : Plane => G (s, z')) z‖ ≤ ‖iteratedFDeriv ℝ m G (s, z)‖ := by
  set a : ℝ × Plane := (s, (0, 0)) with ha
  set V : Set (ℝ × Plane) := (fun y : ℝ × Plane => y + a) ⁻¹' (Ioi (0 : ℝ) ×ˢ (univ : Set Plane))
    with hV
  set f2 : ℝ × Plane → ℝ := fun y => G (y + a) with hf2
  have hVo : IsOpen V :=
    IsOpen.preimage (continuous_id.add continuous_const) (isOpen_Ioi.prod isOpen_univ)
  have hf2C : ContDiffOn ℝ ∞ f2 V :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun y hy => hy)
  set g : Plane →L[ℝ] (ℝ × Plane) := ContinuousLinearMap.inr ℝ ℝ Plane with hg
  have hmem : ∀ z' : Plane, g z' ∈ V := fun z' => by
    refine ⟨?_, mem_univ _⟩
    show (0 : ℝ) < 0 + s
    rw [zero_add]
    exact hs
  have hcomp : (fun z' : Plane => G (s, z')) = f2 ∘ g := by
    funext z'
    show G (s, z') = G (((0 : ℝ), z') + a)
    congr 1
    rw [ha]
    exact Prod.ext (zero_add s).symm (add_zero z').symm
  have hgV : g ⁻¹' V = univ := Set.eq_univ_of_forall hmem
  have hz : g z ∈ V := hmem z
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right g hf2C hVo.uniqueDiffOn
    (by rw [hgV]; exact uniqueDiffOn_univ) hz (i := m) (by exact_mod_cast le_top)
  rw [hgV, iteratedFDerivWithin_univ,
    iteratedFDerivWithin_of_isOpen m hVo hz] at key
  have hg1 : ‖g‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ Plane
  have hpt : g z + a = (s, z) := by
    show ((0 : ℝ), z) + a = (s, z)
    rw [ha]
    exact Prod.ext (zero_add s) (add_zero z)
  have hshift : iteratedFDeriv ℝ m f2 (g z) = iteratedFDeriv ℝ m G (s, z) := by
    rw [hf2, iteratedFDeriv_comp_add_right, hpt]
  rw [hcomp, key, ← hshift]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin m, ‖g‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hg1)
  calc ‖iteratedFDeriv ℝ m f2 (g z)‖ * ∏ _i : Fin m, ‖g‖
      ≤ ‖iteratedFDeriv ℝ m f2 (g z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ m f2 (g z)‖ := mul_one _

/-- The age derivative of `G` is the first-coordinate Fréchet derivative. -/
theorem alj_deriv_eq {G : ℝ × Plane → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    {x : ℝ × Plane} (hx : 0 < x.1) :
    deriv (fun r : ℝ => G (r, x.2)) x.1 = fderiv ℝ G x ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hxU : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hx, mem_univ _⟩
  have hd : DifferentiableAt ℝ G x :=
    (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hl : HasDerivAt (fun r : ℝ => (r, x.2)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) x.1 :=
    (hasDerivAt_id' x.1).prodMk (hasDerivAt_const x.1 x.2)
  exact (hd.hasFDerivAt.comp_hasDerivAt x.1 hl).deriv

/-- One derivative from the joint `fderiv` costs one order of the joint derivative. -/
theorem alj_fderiv_le {G : ℝ × Plane → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    (n : ℕ) {y : ℝ × Plane} (hy : 0 < y.1) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => fderiv ℝ G x ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) y‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) G y‖ := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hyU : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hy, mem_univ _⟩
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ G) y :=
    ((hG.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hyU))
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
    (n := n) hfd (by exact_mod_cast le_top)
  have h2 : ‖iteratedFDeriv ℝ n (fderiv ℝ G) y‖ = ‖iteratedFDeriv ℝ (n + 1) G y‖ :=
    norm_iteratedFDeriv_fderiv
  have hc : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
    simp [Prod.norm_def]
  calc ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => fderiv ℝ G x ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) y‖
      ≤ ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ G) y‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ G) y‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) G y‖ := by rw [one_mul, h2]

/-- The age jets of a jointly smooth field are bounded by the joint jet (induction on `ℓ`). -/
theorem alj_main : ∀ (ℓ : ℕ) (F : ℝ → Plane → ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) →
    ∀ (m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane),
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m F s z‖ ≤
        ‖iteratedFDeriv ℝ (ℓ + m) (fun x : ℝ × Plane => F x.1 x.2) (s, z)‖ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro F hF m s hs z
    rw [zero_add]
    have h0 : (fun z' : Plane => iteratedDeriv 0 (fun r => F r z') s) = fun z' => F s z' := by
      funext z'
      rw [iteratedDeriv_zero]
    show ‖iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv 0 (fun r => F r z') s) z‖ ≤ _
    rw [h0]
    exact alj_slice_le (G := fun x : ℝ × Plane => F x.1 x.2) hF m hs z
  | succ ℓ ih =>
    intro F hF m s hs z
    have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
    have hyU : (s, z) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hs, mem_univ _⟩
    have hKC : ContDiffOn ℝ ∞
        (fun x : ℝ × Plane => fderiv ℝ (fun x : ℝ × Plane => F x.1 x.2) x
          ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    have hF'C : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (fun r z' => deriv (fun r' => F r' z') r) x.1 x.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      hKC.congr (fun x hx => alj_deriv_eq hF hx.1)
    have ihF := ih (fun r z' => deriv (fun r' => F r' z') r) hF'C m hs z
    have hAJ : UnforcedLeray.Short.PartI.ageJet (ℓ + 1) m F s z =
        UnforcedLeray.Short.PartI.ageJet ℓ m (fun r z' => deriv (fun r' => F r' z') r) s z := by
      have hfun : (fun z' : Plane => iteratedDeriv (ℓ + 1) (fun r => F r z') s) =
          (fun z' : Plane => iteratedDeriv ℓ (fun r => deriv (fun r' => F r' z') r) s) := by
        funext z'
        rw [iteratedDeriv_succ']
      show iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv (ℓ + 1) (fun r => F r z') s) z =
        iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv ℓ (fun r => deriv (fun r' => F r' z') r) s) z
      rw [hfun]
    rw [hAJ]
    refine ihF.trans ?_
    have heq : (fun x : ℝ × Plane => (fun r z' => deriv (fun r' => F r' z') r) x.1 x.2) =ᶠ[𝓝 (s, z)]
        (fun x : ℝ × Plane => fderiv ℝ (fun x : ℝ × Plane => F x.1 x.2) x
          ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hyU) (fun x hx => alj_deriv_eq hF hx.1)
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) heq (ℓ + m)).self_of_nhds]
    have hstep := alj_fderiv_le (G := fun x : ℝ × Plane => F x.1 x.2) hF (ℓ + m) (y := (s, z)) hs
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    exact hstep

/-! ### 2. Weighted Gaussian envelope jet bound on `0 < s ≤ Sg / ν` -/

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

/-- Absorption of `(1 + η^2)^M` by `exp(-η^2 / (2(1 + Sg)))`. -/
lemma pcWeightAbsorbSg (Sg : ℝ) (hSg : 0 < Sg) (M : ℕ) (η : ℝ) :
    (1 + η ^ 2) ^ M * Real.exp (-η ^ 2 / (2 * (1 + Sg))) ≤
      (2 * (1 + Sg)) ^ M * Real.exp 1 * (M.factorial : ℝ) := by
  set B : ℝ := 2 * (1 + Sg) with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hB0 : 0 < B := by linarith
  set t := η ^ 2 / B with ht
  have ht0 : 0 ≤ t := by positivity
  have hBt : B * t = η ^ 2 := mul_div_cancel₀ _ hB0.ne'
  have h1 : 1 + η ^ 2 ≤ B * (1 + t) := by nlinarith
  have h2 : (1 + η ^ 2) ^ M ≤ B ^ M * (1 + t) ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 M
  have h3 := UnforcedLeray.Gaussian.pow_mul_exp_neg_le_factorial M (s := 1 + t) (by linarith)
  have he : Real.exp (-η ^ 2 / B) = Real.exp 1 * Real.exp (-(1 + t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht]
    ring
  calc (1 + η ^ 2) ^ M * Real.exp (-η ^ 2 / B)
      ≤ (B ^ M * (1 + t) ^ M) * Real.exp (-η ^ 2 / B) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = B ^ M * Real.exp 1 * ((1 + t) ^ M * Real.exp (-(1 + t))) := by rw [he]; ring
    _ ≤ B ^ M * Real.exp 1 * (M.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Constant bounding `(1 + η^2)^w` times the `r`-th derivative of the Gaussian factor on
`0 < s ≤ Sg / ν`. -/
def pcKexpSg (Sg : ℝ) (w r : ℕ) : ℝ :=
  (r.factorial : ℝ) * (4 * ((r : ℝ) + 1)) ^ r *
    ((2 * (1 + Sg)) ^ (w + r) * Real.exp 1 * ((w + r).factorial : ℝ))

lemma pcKexpSg_nonneg {Sg : ℝ} (hSg : 0 < Sg) (w r : ℕ) : 0 ≤ pcKexpSg Sg w r := by
  unfold pcKexpSg
  positivity

/-- Uniform weighted jet bound for the Gaussian factor `exp(-x.2.2^2 / (2(1 + ν x.1)))` on
`0 < y.1 ≤ Sg / ν`. -/
lemma pcExpJetBoundSg (Sg : ℝ) (hSg : 0 < Sg) (w r : ℕ) (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (y : ℝ × Plane) (hy0 : 0 < y.1) (hy1 : y.1 ≤ Sg / ν) :
    (1 + y.2.2 ^ 2) ^ w *
      ‖iteratedFDerivWithin ℝ r
        (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) pcUfst y‖
      ≤ pcKexpSg Sg w r := by
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
  have hνy : ν * y.1 ≤ Sg := by
    have := (le_div_iff₀ hν0).mp hy1
    linarith
  have hfy : f y ≤ -y.2.2 ^ 2 / (2 * (1 + Sg)) := by
    simp only [hfdef]
    have hden : 0 < 2 * (1 + ν * y.1) := by linarith [mul_nonneg hν0' hy0.le]
    have hden2 : 0 < 2 * (1 + Sg) := by positivity
    rw [div_le_div_iff₀ hden hden2]
    nlinarith [sq_nonneg y.2.2]
  have hCi : ∀ i, i ≤ r →
      ‖iteratedFDerivWithin ℝ i Real.exp (univ : Set ℝ) (f y)‖ ≤
        Real.exp (-y.2.2 ^ 2 / (2 * (1 + Sg))) := by
    intro i _hi
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hfy
  have hout := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := f)
    (t := (univ : Set ℝ)) (s := pcUfst) (N := ∞) (n := r)
    (C := Real.exp (-y.2.2 ^ 2 / (2 * (1 + Sg)))) (D := 4 * ((r : ℝ) + 1) * (1 + y.2.2 ^ 2))
    Real.contDiff_exp.contDiffOn hfC
    (show (r : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
    uniqueDiffOn_univ pcIsOpenUfst.uniqueDiffOn (mapsTo_univ _ _) hy hCi
    (fun i hi1 hi => pcExponentJetBound ν hν0' hν1 r i hi1 hi y hy)
  have hout_w : (1 + y.2.2 ^ 2) ^ w *
      ‖iteratedFDerivWithin ℝ r (Real.exp ∘ f) pcUfst y‖ ≤
      (1 + y.2.2 ^ 2) ^ w *
        ((r.factorial : ℝ) * Real.exp (-y.2.2 ^ 2 / (2 * (1 + Sg))) *
          (4 * ((r : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ r) :=
    mul_le_mul_of_nonneg_left hout (by positivity)
  change (1 + y.2.2 ^ 2) ^ w * ‖iteratedFDerivWithin ℝ r (Real.exp ∘ f) pcUfst y‖ ≤ pcKexpSg Sg w r
  refine hout_w.trans ?_
  unfold pcKexpSg
  have hpow : (4 * ((r : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ r
      = (4 * ((r : ℝ) + 1)) ^ r * (1 + y.2.2 ^ 2) ^ r := mul_pow _ _ _
  have habs := pcWeightAbsorbSg Sg hSg (w + r) y.2.2
  calc (1 + y.2.2 ^ 2) ^ w *
        ((r.factorial : ℝ) * Real.exp (-y.2.2 ^ 2 / (2 * (1 + Sg))) *
          (4 * ((r : ℝ) + 1) * (1 + y.2.2 ^ 2)) ^ r)
      = (r.factorial : ℝ) * (4 * ((r : ℝ) + 1)) ^ r *
          ((1 + y.2.2 ^ 2) ^ (w + r) * Real.exp (-y.2.2 ^ 2 / (2 * (1 + Sg)))) := by
        rw [hpow, pow_add]; ring
    _ ≤ (r.factorial : ℝ) * (4 * ((r : ℝ) + 1)) ^ r *
          ((2 * (1 + Sg)) ^ (w + r) * Real.exp 1 * ((w + r).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left habs (by positivity)

/-- **Weighted Gaussian envelope jet bound**: on `0 < s ≤ Sg / ν` (`0 < ν ≤ 1`),
`(1 + η²)^w` times the `n`-th joint derivative of `-a⁻³ e^{-η²/(2a)}` (`a = 1 + νs`) is bounded
uniformly in `ν, s, q, η`. -/
theorem pcEnvJetSg (Sg : ℝ) (hSg : 0 < Sg) (w n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ Sg / ν →
        (1 + y.2.2 ^ 2) ^ w *
          ‖iteratedFDeriv ℝ n
            (fun x : ℝ × Plane =>
              -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) y‖ ≤ K := by
  refine ⟨∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ((n : ℝ) + 3) ^ i * pcKexpSg Sg w (n - i),
    Finset.sum_nonneg fun i _ => by
      have := pcKexpSg_nonneg hSg w (n - i)
      positivity, ?_⟩
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
  have hLw := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (1 + y.2.2 ^ 2) ^ w)
  rw [Finset.mul_sum] at hLw
  refine hLw.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have ha := pcAffJetBound ν hν0' hν1 (-1) (by norm_num) 3 n i hi' y hy
  have hb := pcExpJetBoundSg Sg hSg w (n - i) ν hν0 hν1 y hy0 hy1
  have hc0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  have ha' : ‖iteratedFDerivWithin ℝ i
      (fun x : ℝ × Plane => (-1 : ℝ) * ((1 + ν * x.1) ^ 3)⁻¹) pcUfst y‖ ≤ ((n : ℝ) + (3 : ℕ)) ^ i :=
    ha
  push_cast at ha'
  calc (1 + y.2.2 ^ 2) ^ w *
        ((n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i
            (fun x : ℝ × Plane => (-1 : ℝ) * ((1 + ν * x.1) ^ 3)⁻¹) pcUfst y‖ *
          ‖iteratedFDerivWithin ℝ (n - i)
            (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) pcUfst y‖)
      = ((n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i
            (fun x : ℝ × Plane => (-1 : ℝ) * ((1 + ν * x.1) ^ 3)⁻¹) pcUfst y‖) *
        ((1 + y.2.2 ^ 2) ^ w *
          ‖iteratedFDerivWithin ℝ (n - i)
            (fun x : ℝ × Plane => Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) pcUfst y‖) := by ring
    _ ≤ ((n.choose i : ℝ) * ((n : ℝ) + 3) ^ i) * pcKexpSg Sg w (n - i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha' hc0) hb (by positivity) (by positivity)

end UnforcedLeray.Short.PartI.PcTwoMulMAux

end
