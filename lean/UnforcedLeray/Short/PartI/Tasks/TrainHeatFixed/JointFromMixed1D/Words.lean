import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic

/-!
# Part I, task `PartI:HF/7`: helper lemmas (word derivatives on the plane)

Generic calculus for `Short/PartI/Sub/PartI_TrainHeatFixed.lean` (`JointFromMixed1D`). For a
function `g` that is `C^∞` on `U = Ioi 0 ×ˢ univ`, `dW l g` is the derivative of `g` along the
list `l` of plane directions (head outermost). Symmetry of the second derivative gives
invariance under permutation of the list (`dW_perm`); the word `replicate a (0,1) ++
replicate b (1,0)` is the mixed derivative `∂_η^a ∂_s^b` (`dW_replicate_ee_es`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI.MixedDeriv

/-- Directional derivatives of `g` along the list `l` of plane directions; the head is outermost. -/
def dW : List (ℝ × ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], g => g
  | v :: l, g => fun x => fderiv ℝ (dW l g) x v

theorem isOpen_halfPlane : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
  isOpen_Ioi.prod isOpen_univ

theorem dW_cons (v : ℝ × ℝ) (l : List (ℝ × ℝ)) (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    dW (v :: l) g x = fderiv ℝ (dW l g) x v := rfl

theorem dW_contDiffOn {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) : ∀ l : List (ℝ × ℝ), ContDiffOn ℝ ∞ (dW l g) U := by
  intro l
  induction l with
  | nil => exact hg
  | cons v l ih =>
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (dW l g)) U := ih.fderiv_of_isOpen hU (by simp)
    show ContDiffOn ℝ ∞ (fun x => fderiv ℝ (dW l g) x v) U
    exact h1.clm_apply contDiffOn_const

theorem fderiv_fst_line {G : ℝ × ℝ → ℝ} {r η : ℝ} (hG : DifferentiableAt ℝ G (r, η)) :
    fderiv ℝ G (r, η) (1, 0) = deriv (fun t => G (t, η)) r := by
  have hl : HasDerivAt (fun t : ℝ => (t, η)) ((1 : ℝ), (0 : ℝ)) r :=
    (hasDerivAt_id' r).prodMk (hasDerivAt_const r η)
  exact ((hG.hasFDerivAt).comp_hasDerivAt r hl).deriv.symm

theorem fderiv_snd_line {G : ℝ × ℝ → ℝ} {r η : ℝ} (hG : DifferentiableAt ℝ G (r, η)) :
    fderiv ℝ G (r, η) (0, 1) = deriv (fun t => G (r, t)) η := by
  have hl : HasDerivAt (fun t : ℝ => (r, t)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η r).prodMk (hasDerivAt_id' η)
  exact ((hG.hasFDerivAt).comp_hasDerivAt η hl).deriv.symm

theorem dW_swap {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (l : List (ℝ × ℝ)) (v w : ℝ × ℝ) {x : ℝ × ℝ} (hx : x ∈ U) :
    dW (v :: w :: l) g x = dW (w :: v :: l) g x := by
  have hC : ContDiffAt ℝ ∞ (dW l g) x := (dW_contDiffOn hU hg l).contDiffAt (hU.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (dW l g)) x :=
    ((dW_contDiffOn hU hg l).fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ (dW l g) x := hC.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (dW l g)) x := hD.differentiableAt (by simp)
  have key : ∀ a b : ℝ × ℝ,
      fderiv ℝ (fun y => fderiv ℝ (dW l g) y b) x a = fderiv ℝ (fderiv ℝ (dW l g)) x a b := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ (dW l g) y w) x v =
    fderiv ℝ (fun y => fderiv ℝ (dW l g) y v) x w
  rw [key, key]
  exact hsymm v w

theorem dW_perm {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g : ℝ × ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    {l₁ l₂ : List (ℝ × ℝ)} (hp : l₁.Perm l₂) : ∀ x ∈ U, dW l₁ g x = dW l₂ g x := by
  induction hp with
  | nil => intro x _; rfl
  | @cons v l₁ l₂ p ih =>
    intro x hx
    have hev : dW l₁ g =ᶠ[𝓝 x] dW l₂ g :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    rw [dW_cons, dW_cons, hev.fderiv_eq]
  | @swap x y l =>
    intro z hz
    exact dW_swap hU hg l y x hz
  | @trans l₁ l₂ l₃ p₁ p₂ ih₁ ih₂ =>
    intro x hx
    exact (ih₁ x hx).trans (ih₂ x hx)

theorem dW_ofFn_eq {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) :
    ∀ (n : ℕ) (m : Fin n → ℝ × ℝ) (x : ℝ × ℝ), x ∈ U →
      dW (List.ofFn m) g x = iteratedFDeriv ℝ n g x m := by
  intro n
  induction n with
  | zero => intro m x _; simp [dW, iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x hx
    have hev : dW (List.ofFn fun i : Fin n => m i.succ) g =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ n g y (Fin.tail m) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih (fun i => m i.succ) y hy)
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top n)
    rw [List.ofFn_succ, dW_cons, hev.fderiv_eq, hdiff.iteratedFDeriv_succ_apply_left']

theorem dW_replicate_es {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0 ×ˢ (univ : Set ℝ))) :
    ∀ (b : ℕ) (η r : ℝ), 0 < r →
      dW (List.replicate b (1, 0)) g (r, η) = iteratedDeriv b (fun t => g (t, η)) r := by
  intro b
  induction b with
  | zero => intro η r _; simp [dW]
  | succ b ih =>
    intro η r hr
    have hmem : ((r, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
    have hGd : DifferentiableAt ℝ (dW (List.replicate b (1, 0)) g) (r, η) :=
      ((dW_contDiffOn isOpen_halfPlane hg _).contDiffAt
        (isOpen_halfPlane.mem_nhds hmem)).differentiableAt (by simp)
    rw [List.replicate_succ, dW_cons, fderiv_fst_line hGd, iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact ih η t ht

theorem dW_replicate_ee_es {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0 ×ˢ (univ : Set ℝ))) :
    ∀ (a b : ℕ) (r η : ℝ), 0 < r →
      dW (List.replicate a (0, 1) ++ List.replicate b (1, 0)) g (r, η) =
        iteratedDeriv a (fun e => iteratedDeriv b (fun t => g (t, e)) r) η := by
  intro a
  induction a with
  | zero =>
    intro b r η hr
    simp only [List.replicate_zero, List.nil_append, iteratedDeriv_zero]
    exact dW_replicate_es hg b η r hr
  | succ a ih =>
    intro b r η hr
    have hmem : ((r, η) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
    have hGd : DifferentiableAt ℝ (dW (List.replicate a (0, 1) ++ List.replicate b (1, 0)) g)
        (r, η) :=
      ((dW_contDiffOn isOpen_halfPlane hg _).contDiffAt
        (isOpen_halfPlane.mem_nhds hmem)).differentiableAt (by simp)
    have hfun : (fun e => dW (List.replicate a (0, 1) ++ List.replicate b (1, 0)) g (r, e)) =
        (fun e => iteratedDeriv a (fun e' => iteratedDeriv b (fun t => g (t, e')) r) e) :=
      funext (fun e => ih b r e hr)
    rw [List.replicate_succ, List.cons_append, dW_cons, fderiv_snd_line hGd, iteratedDeriv_succ,
      hfun]

/-- The coordinate direction: `true ↦ (1,0)` (the `s` direction), `false ↦ (0,1)` (the `η`
direction). -/
def bas (b : Bool) : ℝ × ℝ := if b then (1, 0) else (0, 1)

theorem bas_decomp (x : ℝ × ℝ) : x = ∑ b : Bool, (if b then x.1 else x.2) • bas b := by
  rw [Fintype.sum_bool]
  ext <;> simp [bas]

/-- The norm of a bilinear-type map is bounded by the sum of its values on coordinate words. -/
theorem norm_iteratedFDeriv_le_sum (g : ℝ × ℝ → ℝ) (n : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n g x‖ ≤
      ∑ r : Fin n → Bool, |iteratedFDeriv ℝ n g x (fun k => bas (r k))| := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun r _ => abs_nonneg _)) ?_
  intro m
  have hexp : iteratedFDeriv ℝ n g x m =
      ∑ r : Fin n → Bool, (∏ i, (if r i then (m i).1 else (m i).2)) *
        iteratedFDeriv ℝ n g x (fun i => bas (r i)) := by
    have h1 : iteratedFDeriv ℝ n g x m =
        iteratedFDeriv ℝ n g x (fun i => ∑ b : Bool, (if b then (m i).1 else (m i).2) • bas b) := by
      congr 1
      funext i
      exact bas_decomp (m i)
    rw [h1, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    show iteratedFDeriv ℝ n g x (fun i => (if r i then (m i).1 else (m i).2) • bas (r i)) = _
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hbound : ∀ r : Fin n → Bool, |∏ i, (if r i then (m i).1 else (m i).2)| ≤ ∏ i, ‖m i‖ := by
    intro r
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
    split_ifs
    · rw [← Real.norm_eq_abs]
      exact norm_fst_le (m i)
    · rw [← Real.norm_eq_abs]
      exact norm_snd_le (m i)
  rw [hexp, Real.norm_eq_abs]
  calc |∑ r : Fin n → Bool, (∏ i, (if r i then (m i).1 else (m i).2)) *
          iteratedFDeriv ℝ n g x (fun i => bas (r i))|
      ≤ ∑ r : Fin n → Bool, |(∏ i, (if r i then (m i).1 else (m i).2)) *
          iteratedFDeriv ℝ n g x (fun i => bas (r i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin n → Bool, (∏ i, ‖m i‖) * |iteratedFDeriv ℝ n g x (fun i => bas (r i))| := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound r) (abs_nonneg _)
    _ = (∑ r : Fin n → Bool, |iteratedFDeriv ℝ n g x (fun i => bas (r i))|) * ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring

end UnforcedLeray.Short.PartI.MixedDeriv
