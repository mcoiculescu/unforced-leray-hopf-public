import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# `PartIII-b:C/grad/3/5/1`: `HpAC1` from termwise `C^1` and locally uniform summable majorants

Source `the November 2 reference manuscript`
4973-4980, 4991, 5063-5079, 4741-4745.  `h^p_A` is the lattice sum of `C^1` terms; on every
convex ball with closure in `{s>0}` the first derivatives of the terms are bounded by
summable (Gaussian in `j`) majorants.  Proved: `hpAC1_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Lattice-sum smoothness: finite-order termwise-bounded `tsum` of `C^n` functions on a convex
open set is `C^n` (generalises `perDeriv_contDiffOn_aux`). -/
def TsumContDiffOnBounds : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (U : Set E), IsOpen U → Convex ℝ U → ∀ (n : ℕ)
    (f : ℤ → E → F) (v : ℕ → ℤ → ℝ), (∀ i, ContDiffOn ℝ n (f i) U) →
    (∀ k ≤ n, Summable (v k)) →
    (∀ k ≤ n, ∀ i (x : E), x ∈ U → ‖iteratedFDerivWithin ℝ k (f i) U x‖ ≤ v k i) →
    ContDiffOn ℝ n (fun y => ∑' i, f i y) U

/-- The `j`-th term of `h^p_A` as a function of `(s,x)`. -/
def hpATm (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (p : Chart) : ℝ × ℝ :=
  merApply (Ay ν χ A p.1) (Vj ν p.1 j p.2)
    - fderiv ℝ (Vj ν p.1 j) p.2 (merApply (Ay ν χ A p.1) (xj ν j p.2))

/-- Each term is `C^1` on `{s>0}` (source 4973-4980; `A^y` is `C^6` on `(0,∞)`, `V_j` smooth
there). -/
def HpATermC1 (as : ℝ) : Prop :=
  ∀ (χ : ℝ → ℝ), IsSourceCutoffC χ → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ j : ℤ, ContDiffOn ℝ 1 (hpATm ν χ A j) {p : Chart | 0 < p.1}

/-- Locally uniform Gaussian majorants for the terms and their first derivatives
(source 4991, 5063-5079). -/
def HpALocUnif (as : ℝ) : Prop :=
  ∀ (χ : ℝ → ℝ), IsSourceCutoffC χ → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ U : Set Chart, IsOpen U → Convex ℝ U → closure U ⊆ {p : Chart | 0 < p.1} →
      Bornology.IsBounded (closure U) →
      ∃ v : ℕ → ℤ → ℝ, (∀ k ≤ 1, Summable (v k)) ∧
        ∀ k ≤ 1, ∀ j : ℤ, ∀ p ∈ U, ‖iteratedFDerivWithin ℝ k (hpATm ν χ A j) U p‖ ≤ v k j

theorem hpAC1_of (as : ℝ) (χf : ℝ → ℝ) (h1 : TsumContDiffOnBounds) (h2 : HpATermC1 as)
    (h3 : HpALocUnif as) : HpAC1 as χf := by
  intro hχ ν hν A hA
  refine contDiffOn_of_locally_contDiffOn ?_
  intro p0 hp0
  have hp0' : 0 < p0.1 := hp0
  set r : ℝ := p0.1 / 2 with hr
  have hrpos : 0 < r := by positivity
  have hcl : closure (ball p0 r) ⊆ {p : Chart | 0 < p.1} := by
    intro p hp
    have hp' : p ∈ closedBall p0 r := closure_ball_subset_closedBall hp
    have : dist p.1 p0.1 ≤ r := by
      have := mem_closedBall.mp hp'
      rw [Prod.dist_eq] at this
      exact le_trans (le_max_left _ _) this
    have h := abs_le.mp (by simpa [Real.dist_eq] using this)
    show 0 < p.1
    linarith [h.1]
  have hbd : Bornology.IsBounded (closure (ball p0 r)) := isBounded_ball.closure
  obtain ⟨v, hv1, hv2⟩ := h3 χf hχ ν hν A hA (ball p0 r) isOpen_ball (convex_ball p0 r) hcl hbd
  refine ⟨ball p0 r, isOpen_ball, mem_ball_self hrpos, ?_⟩
  have key := h1 (ball p0 r) isOpen_ball (convex_ball p0 r) 1 (hpATm ν χf A) v
    (fun j => (h2 χf hχ ν hν A hA j).mono (fun p hp => hcl (subset_closure hp))) hv1 
    (fun k hk j p hp => hv2 k hk j p hp)
  exact key.mono inter_subset_right

end UnforcedLeray.Short.PartIIIb.Concrete
