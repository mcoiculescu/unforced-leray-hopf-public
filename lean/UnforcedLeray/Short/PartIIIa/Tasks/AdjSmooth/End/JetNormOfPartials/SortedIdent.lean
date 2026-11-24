import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_4

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`, task `sortedIdent`: the sorted word is the mixed partial

Proves `SortedIdent` (defined in `Sub/PartIII-a_T21_2_7_2_1_2_1_4.lean`, SP 3060-3073, calculus only).
Peeling off the first argument of `D^n F(p)` (`iteratedFDeriv_succ_apply_left`) gives the outer
derivative in the direction `stDir (k + 1) = (0, dir k)` for a spatial letter `k`, which is the outer
`pdCx k` of `adjSpatial`; for the age letters the one-dimensional derivative along `stDir 0` is used.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem siStDirSucc (k : Fin 2) : stDir k.succ = (0, B0579.dir k) := by
  fin_cases k <;> rfl

theorem siSortedCons (k : Fin 2) (w : List (Fin 2)) (m : ℕ) :
    sortedVec (k :: w) (m + 1) = Fin.cons (stDir k.succ) (sortedVec w m) := by
  funext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp [sortedVec]
  · simp [sortedVec]

theorem siSortedNil (n : ℕ) : sortedVec [] n = fun _ => stDir 0 := by
  funext k
  simp [sortedVec]

theorem siDiff (F : ℝ × (ℝ × ℝ) → ℂ) (U : Set (ℝ × (ℝ × ℝ))) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (m : ℕ) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ U) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ m F) p :=
  (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv (by exact_mod_cast
    (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m)))

/-- Base case: the derivative along the age direction `stDir 0` is the age derivative of the slice. -/
theorem siBase : ∀ (j : ℕ) (F : ℝ × (ℝ × ℝ) → ℂ) (U : Set (ℝ × (ℝ × ℝ))), IsOpen U →
    ContDiffOn ℝ ∞ F U → ∀ p ∈ U,
      iteratedFDeriv ℝ j F p (fun _ => stDir 0) = iteratedDeriv j (fun r' => F (r', p.2)) p.1
  | 0, F, U, _, _, p, _ => by
    rw [iteratedFDeriv_zero_apply, iteratedDeriv_zero]
  | j + 1, F, U, hU, hF, p, hp => by
    have hdj := siDiff F U hU hF j p hp
    have hG : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ j F q (fun _ => stDir 0)) p :=
      (hdj.hasFDerivAt.continuousMultilinear_apply_const _).differentiableAt
    have hL : iteratedFDeriv ℝ (j + 1) F p (fun _ => stDir 0) =
        fderiv ℝ (fun q => iteratedFDeriv ℝ j F q (fun _ => stDir 0)) p (stDir 0) := by
      rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply hdj]
      rfl
    have hev : iteratedDeriv j (fun r' => F (r', p.2)) =ᶠ[nhds p.1]
        fun r => iteratedFDeriv ℝ j F (r, p.2) (fun _ => stDir 0) := by
      have hV : {r : ℝ | (r, p.2) ∈ U} ∈ nhds p.1 :=
        (hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp
      filter_upwards [hV] with r hr
      exact (siBase j F U hU hF (r, p.2) hr).symm
    have hdr : HasDerivAt (fun r : ℝ => (r, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id' (x := p.1)).prodMk (hasDerivAt_const p.1 p.2)
    have hD := (hG.hasFDerivAt.comp_hasDerivAt p.1 hdr)
    rw [iteratedDeriv_succ, hev.deriv_eq, hL]
    have hstd : ((1 : ℝ), (0 : ℝ × ℝ)) = stDir 0 := by
      rfl
    rw [← hstd]
    exact hD.deriv.symm

theorem siMain : ∀ (w : List (Fin 2)) (j n : ℕ), w.length + j = n →
    ∀ (F : ℝ × (ℝ × ℝ) → ℂ) (U : Set (ℝ × (ℝ × ℝ))), IsOpen U → ContDiffOn ℝ ∞ F U →
    ∀ p ∈ U, iteratedFDeriv ℝ n F p (sortedVec w n) =
      adjSpatial w (fun y => iteratedDeriv j (fun r' => F (r', y)) p.1) p.2
  | [], j, n, h, F, U, hU, hF, p, hp => by
    have hn : n = j := by simpa using h.symm
    subst hn
    rw [siSortedNil]
    exact siBase n F U hU hF p hp
  | k :: w, j, n, h, F, U, hU, hF, p, hp => by
    have hn : n = w.length + j + 1 := by
      simp only [List.length_cons] at h
      omega
    subst hn
    rw [siSortedCons]
    have hdm := siDiff F U hU hF (w.length + j) p hp
    have hIH := siMain w j (w.length + j) rfl F U hU hF
    set vs := sortedVec w (w.length + j) with hvs
    set A : ℝ × (ℝ × ℝ) → ℂ := fun q => iteratedFDeriv ℝ (w.length + j) F q vs with hA
    have hAd : DifferentiableAt ℝ A p :=
      (hdm.hasFDerivAt.continuousMultilinear_apply_const vs).differentiableAt
    have he : HasFDerivAt (fun y : ℝ × ℝ => (p.1, y))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    have hcomp := hAd.hasFDerivAt.comp p.2 he
    have hd : fderiv ℝ (fun y => A (p.1, y)) p.2 (B0579.dir k) =
        fderiv ℝ A p (0, B0579.dir k) := by
      rw [show (fun y => A (p.1, y)) = A ∘ (fun y : ℝ × ℝ => (p.1, y)) from rfl, hcomp.fderiv]
      simp
    have hV : {y : ℝ × ℝ | (p.1, y) ∈ U} ∈ nhds p.2 :=
      (hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
    have hev : (fun y => A (p.1, y)) =ᶠ[nhds p.2]
        adjSpatial w (fun y => iteratedDeriv j (fun r' => F (r', y)) p.1) := by
      filter_upwards [hV] with y hy
      exact hIH (p.1, y) hy
    have hcongr : fderiv ℝ (fun y => A (p.1, y)) p.2 =
        fderiv ℝ (adjSpatial w (fun y => iteratedDeriv j (fun r' => F (r', y)) p.1)) p.2 :=
      hev.fderiv_eq
    have hL : iteratedFDeriv ℝ (w.length + j + 1) F p (Fin.cons (stDir k.succ) vs) =
        fderiv ℝ A p (stDir k.succ) := by
      rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons,
        ← fderiv_continuousMultilinear_apply_const_apply hdm]
    rw [hL, siStDirSucc]
    simp only [adjSpatial, pdCx]
    rw [← hd, hcongr]

theorem sortedIdent : UnforcedLeray.Short.IIIa.SortedIdent := by
  intro φ' U hU hsm p hp j w n h
  exact siMain w j n h (fun p => φ' p.1 p.2) U hU hsm p hp

end UnforcedLeray.Short.IIIa
