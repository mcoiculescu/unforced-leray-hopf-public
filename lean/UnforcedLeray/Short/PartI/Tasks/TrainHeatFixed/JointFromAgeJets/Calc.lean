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
# Part I, task `PartI:HF/3`: helper lemmas (word derivatives on `ℝ × (ℝ × ℝ)`)

Generic calculus for `Short/PartI/Sub/PartI_TrainHeatFixed.lean` (`JointFromAgeJets`). The space
`ℝ × (ℝ × ℝ)` is `(s, z)` with `z` the plane. For `G` smooth on `s > 0`, `dW l G` is the
directional derivative along the list `l` of directions (head outermost). Words over the three
directions `s, q, η` are reordered (`dW_perm`, from symmetry of second derivatives) so that the
`s`-directions are innermost. The plane part then equals the `j`-th Fréchet derivative of
`z ↦ ∂_s^ℓ G(s, z)`, which is `ageJet ℓ j`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI.AgeDeriv

section Generic

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Directional derivatives of `g` along the list `l` of directions; the head is outermost. -/
def dW : List X → (X → ℝ) → X → ℝ
  | [], g => g
  | v :: l, g => fun x => fderiv ℝ (dW l g) x v

theorem dW_cons (v : X) (l : List X) (g : X → ℝ) (x : X) :
    dW (v :: l) g x = fderiv ℝ (dW l g) x v := rfl

theorem dW_contDiffOn {U : Set X} (hU : IsOpen U) {g : X → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) : ∀ l : List X, ContDiffOn ℝ ∞ (dW l g) U := by
  intro l
  induction l with
  | nil => exact hg
  | cons v l ih =>
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (dW l g)) U := ih.fderiv_of_isOpen hU (by simp)
    show ContDiffOn ℝ ∞ (fun x => fderiv ℝ (dW l g) x v) U
    exact h1.clm_apply contDiffOn_const

theorem dW_swap {U : Set X} (hU : IsOpen U) {g : X → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (l : List X) (v w : X) {x : X} (hx : x ∈ U) :
    dW (v :: w :: l) g x = dW (w :: v :: l) g x := by
  have hC : ContDiffAt ℝ ∞ (dW l g) x := (dW_contDiffOn hU hg l).contDiffAt (hU.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (dW l g)) x :=
    ((dW_contDiffOn hU hg l).fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ (dW l g) x := hC.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (dW l g)) x := hD.differentiableAt (by simp)
  have key : ∀ a b : X,
      fderiv ℝ (fun y => fderiv ℝ (dW l g) y b) x a = fderiv ℝ (fderiv ℝ (dW l g)) x a b := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ (dW l g) y w) x v =
    fderiv ℝ (fun y => fderiv ℝ (dW l g) y v) x w
  rw [key, key]
  exact hsymm v w

theorem dW_perm {U : Set X} (hU : IsOpen U) {g : X → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    {l₁ l₂ : List X} (hp : l₁.Perm l₂) : ∀ x ∈ U, dW l₁ g x = dW l₂ g x := by
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

theorem dW_ofFn_eq {U : Set X} (hU : IsOpen U) {g : X → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) :
    ∀ (n : ℕ) (m : Fin n → X) (x : X), x ∈ U →
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

theorem dW_append (g : X → ℝ) : ∀ (p q : List X), dW (p ++ q) g = dW p (dW q g)
  | [], q => by simp [dW]
  | v :: p, q => by
    funext x
    show fderiv ℝ (dW (p ++ q) g) x v = fderiv ℝ (dW p (dW q g)) x v
    rw [dW_append g p q]

end Generic

/-! ### The three coordinate directions on `ℝ × (ℝ × ℝ)` -/

/-- The directions `s = (1,0,0)`, `q = (0,1,0)`, `η = (0,0,1)`. -/
def LL : Fin 3 → ℝ × (ℝ × ℝ) := ![(1, (0, 0)), (0, (1, 0)), (0, (0, 1))]

/-- The coordinates `(s, q, η)` of a point. -/
def cd : Fin 3 → ℝ × (ℝ × ℝ) → ℝ := fun c x => ![x.1, x.2.1, x.2.2] c

theorem cd_abs_le (c : Fin 3) (x : ℝ × (ℝ × ℝ)) : |cd c x| ≤ ‖x‖ := by
  fin_cases c
  · simp only [cd]
    rw [← Real.norm_eq_abs]
    exact norm_fst_le x
  · simp only [cd]
    rw [← Real.norm_eq_abs]
    exact (norm_fst_le x.2).trans (norm_snd_le x)
  · simp only [cd]
    rw [← Real.norm_eq_abs]
    exact (norm_snd_le x.2).trans (norm_snd_le x)

theorem LL_decomp (x : ℝ × (ℝ × ℝ)) : x = ∑ c : Fin 3, cd c x • LL c := by
  rcases x with ⟨a, b, c⟩
  simp [Fin.sum_univ_three, cd, LL]

/-- The norm of the `i`-th derivative is bounded by the sum of its values on the coordinate
words. -/
theorem norm_iteratedFDeriv_le_sum3 (G : ℝ × (ℝ × ℝ) → ℝ) (n : ℕ) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ n G x‖ ≤
      ∑ r : Fin n → Fin 3, |iteratedFDeriv ℝ n G x (fun k => LL (r k))| := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun r _ => abs_nonneg _)) ?_
  intro m
  have hexp : iteratedFDeriv ℝ n G x m =
      ∑ r : Fin n → Fin 3, (∏ i, cd (r i) (m i)) * iteratedFDeriv ℝ n G x (fun i => LL (r i)) := by
    have h1 : iteratedFDeriv ℝ n G x m =
        iteratedFDeriv ℝ n G x (fun i => ∑ c : Fin 3, cd c (m i) • LL c) := by
      congr 1
      funext i
      exact LL_decomp (m i)
    rw [h1, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    show iteratedFDeriv ℝ n G x (fun i => cd (r i) (m i) • LL (r i)) = _
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hbound : ∀ r : Fin n → Fin 3, |∏ i, cd (r i) (m i)| ≤ ∏ i, ‖m i‖ := by
    intro r
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => cd_abs_le _ _)
  rw [hexp, Real.norm_eq_abs]
  calc |∑ r : Fin n → Fin 3, (∏ i, cd (r i) (m i)) * iteratedFDeriv ℝ n G x (fun i => LL (r i))|
      ≤ ∑ r : Fin n → Fin 3, |(∏ i, cd (r i) (m i)) *
          iteratedFDeriv ℝ n G x (fun i => LL (r i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin n → Fin 3, (∏ i, ‖m i‖) * |iteratedFDeriv ℝ n G x (fun i => LL (r i))| := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound r) (abs_nonneg _)
    _ = (∑ r : Fin n → Fin 3, |iteratedFDeriv ℝ n G x (fun i => LL (r i))|) * ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring

/-! ### Specific derivative identities -/

theorem isOpen_halfPlane3 : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

theorem fderiv_fst_line3 {G : ℝ × (ℝ × ℝ) → ℝ} {r : ℝ} {z : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G (r, z)) :
    fderiv ℝ G (r, z) (LL 0) = deriv (fun t => G (t, z)) r := by
  show fderiv ℝ G (r, z) (1, (0, 0)) = _
  have hl : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) r :=
    (hasDerivAt_id' r).prodMk (hasDerivAt_const r z)
  exact ((hG.hasFDerivAt).comp_hasDerivAt r hl).deriv.symm

/-- The `s`-direction iterated: `∂_s^ℓ` along the line, for `s > 0`. -/
theorem dW_rep_s {G : ℝ × (ℝ × ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)))) :
    ∀ (ℓ : ℕ) (z : ℝ × ℝ) (s : ℝ), 0 < s →
      dW (List.replicate ℓ (LL 0)) G (s, z) = iteratedDeriv ℓ (fun t => G (t, z)) s := by
  intro ℓ
  induction ℓ with
  | zero => intro z s _; simp [dW]
  | succ ℓ ih =>
    intro z s hs
    have hmem : ((s, z) : ℝ × (ℝ × ℝ)) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hs, mem_univ _⟩
    have hGd : DifferentiableAt ℝ (dW (List.replicate ℓ (LL 0)) G) (s, z) :=
      ((dW_contDiffOn isOpen_halfPlane3 hG _).contDiffAt
        (isOpen_halfPlane3.mem_nhds hmem)).differentiableAt (by simp)
    rw [List.replicate_succ, dW_cons, fderiv_fst_line3 hGd, iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact ih z t ht

/-- Plane words after the `s`-words: the plane part is the derivative of the slice `z ↦ K(s,z)`. -/
theorem dW_plane_word {K : ℝ × (ℝ × ℝ) → ℝ}
    (hK : ContDiffOn ℝ ∞ K (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ)))) :
    ∀ (w : List (ℝ × ℝ)) (s : ℝ), 0 < s → ∀ z : ℝ × ℝ,
      dW (w.map (fun v => ((0 : ℝ), v))) K (s, z) = dW w (fun z' => K (s, z')) z := by
  intro w
  induction w with
  | nil => intro s hs z; simp [dW]
  | cons v w ih =>
    intro s hs z
    have hmem : ((s, z) : ℝ × (ℝ × ℝ)) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
      ⟨hs, mem_univ _⟩
    have hΦ : ContDiffOn ℝ ∞ (dW (w.map (fun v => ((0 : ℝ), v))) K)
        (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) := dW_contDiffOn isOpen_halfPlane3 hK _
    have hΦd : DifferentiableAt ℝ (dW (w.map (fun v => ((0 : ℝ), v))) K) (s, z) :=
      (hΦ.contDiffAt (isOpen_halfPlane3.mem_nhds hmem)).differentiableAt (by simp)
    have hfun : dW w (fun z' => K (s, z')) =
        (dW (w.map (fun v => ((0 : ℝ), v))) K) ∘ (fun z' => (s, z')) := by
      funext z'
      exact (ih s hs z').symm
    have hι : HasFDerivAt (fun z' : ℝ × ℝ => ((s : ℝ), z'))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
      (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
    have hcomp := hΦd.hasFDerivAt.comp z hι
    rw [List.map_cons, dW_cons, dW_cons, hfun, hcomp.fderiv]
    rfl

/-- A plane word of length `j` is bounded by the `j`-th derivative of the slice function. -/
theorem dW_plane_bound {H : ℝ × ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H Set.univ) :
    ∀ (j : ℕ) (w : List (ℝ × ℝ)) (z : ℝ × ℝ), w.length = j → (∀ v ∈ w, ‖v‖ ≤ 1) →
      |dW w H z| ≤ ‖iteratedFDeriv ℝ j H z‖ := by
  intro j w z hj hw
  subst hj
  have h1 := dW_ofFn_eq isOpen_univ hH w.length w.get z (mem_univ _)
  rw [List.ofFn_get] at h1
  rw [h1]
  have h2 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ w.length H z) w.get
  have h3 : ∏ k, ‖w.get k‖ ≤ 1 :=
    Finset.prod_le_one (fun k _ => norm_nonneg _) (fun k _ => hw _ (List.get_mem w k))
  calc |iteratedFDeriv ℝ w.length H z w.get|
      = ‖iteratedFDeriv ℝ w.length H z w.get‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ w.length H z‖ * ∏ k, ‖w.get k‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ w.length H z‖ * 1 := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ w.length H z‖ := mul_one _

end UnforcedLeray.Short.PartI.AgeDeriv
