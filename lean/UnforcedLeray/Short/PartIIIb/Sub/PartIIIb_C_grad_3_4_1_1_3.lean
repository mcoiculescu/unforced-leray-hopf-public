import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Module.Convex

/-!
# `PartIII-b:C/grad/3/4/1/1/3`: termwise differentiation of the lattice sums

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

`tsumOps_of` (proved): for a family `f j (s, x)` with `U = Σ_j f j`, a local summable majorant of
`‖∂_x f_j‖` on a ball in `x` and of `|∂_s f_j|` on an interval in `s` gives
`HasSum` of `f, ∂_q f, ∂_η f, 𝒦 f` to `U, ∂_q U, ∂_η U, 𝒦 U`.
The remaining content is the local majorants for the concrete terms `gradHpTm`, `gradPsiTm`
(`HpXData`, `HpSData`, ...), which need the `V_j`, `ψ_j` bounds on a neighbourhood of
`s₀ = (11/10)/ν`, i.e. for `ν s ≤ 23/20`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- x-local majorant data for a term family at `(s, x)`. -/
def TsumXData (f : ℤ → ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ g : ℤ → ℝ, Summable g ∧ Summable (fun j => f j s x) ∧
    ∀ (j : ℤ) (y : ℝ × ℝ), y ∈ ball x r →
      DifferentiableAt ℝ (f j s) y ∧ ‖fderiv ℝ (f j s) y‖ ≤ g j

/-- s-local majorant data for a term family at `(s, x)`. -/
def TsumSData (f : ℤ → ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ g : ℤ → ℝ, Summable g ∧
    ∀ (j : ℤ) (t : ℝ), t ∈ ball s r →
      DifferentiableAt ℝ (fun t' => f j t' x) t ∧ ‖deriv (fun t' => f j t' x) t‖ ≤ g j

/-- A family with x-local majorant data is summable on a neighbourhood of `x`. -/
theorem TsumXData.summable_nhds {f : ℤ → ℝ → ℝ × ℝ → ℝ} {s : ℝ} {x : ℝ × ℝ}
    (hX : TsumXData f s x) : ∀ᶠ y in nhds x, Summable (fun j => f j s y) := by
  obtain ⟨r, hr, g, hg, hsum, hd⟩ := hX
  filter_upwards [ball_mem_nhds x hr] with y hy
  exact summable_of_summable_hasFDerivAt_of_isPreconnected (f' := fun j y => fderiv ℝ (f j s) y)
    hg isOpen_ball (convex_ball x r).isPreconnected (fun j y hy => (hd j y hy).1.hasFDerivAt)
    (fun j y hy => (hd j y hy).2) (mem_ball_self hr) hsum hy

/-- A family with s-local majorant data and summable at `(s, x)` is summable for `t` near `s`. -/
theorem TsumSData.summable_nhds {f : ℤ → ℝ → ℝ × ℝ → ℝ} {s : ℝ} {x : ℝ × ℝ}
    (hS : TsumSData f s x) (h0 : Summable (fun j => f j s x)) :
    ∀ᶠ t in nhds s, Summable (fun j => f j t x) := by
  obtain ⟨r, hr, g, hg, hd⟩ := hS
  filter_upwards [ball_mem_nhds s hr] with t ht
  exact summable_of_summable_hasDerivAt_of_isPreconnected (g := fun j t => f j t x)
    (g' := fun j t => deriv (fun t' => f j t' x) t) hg isOpen_ball
    (convex_ball s r).isPreconnected (fun j t ht => (hd j t ht).1.hasDerivAt)
    (fun j t ht => (hd j t ht).2) (mem_ball_self hr) h0 ht

theorem tsumOps_of {f : ℤ → ℝ → ℝ × ℝ → ℝ} {U : ℝ → ℝ × ℝ → ℝ} {s : ℝ} {x : ℝ × ℝ}
    (hUx : ∀ᶠ y in nhds x, U s y = ∑' j, f j s y)
    (hUs : ∀ᶠ t in nhds s, U t x = ∑' j, f j t x)
    (hX : TsumXData f s x) (hS : TsumSData f s x) :
    HasSum (fun j => f j s x) (U s x) ∧
    HasSum (fun j => dQ (f j) s x) (dQ U s x) ∧
    HasSum (fun j => dEta (f j) s x) (dEta U s x) ∧
    HasSum (fun j => Kop (f j) s x) (Kop U s x) := by
  obtain ⟨r, hr, g, hg, hsum, hd⟩ := hX
  have hF : HasFDerivAt (fun y => ∑' j, f j s y) (∑' j, fderiv ℝ (f j s) x) x :=
    hasFDerivAt_tsum_of_isPreconnected (f' := fun j y => fderiv ℝ (f j s) y) hg isOpen_ball
      (convex_ball x r).isPreconnected (fun j y hy => (hd j y hy).1.hasFDerivAt)
      (fun j y hy => (hd j y hy).2) (mem_ball_self hr) hsum (mem_ball_self hr)
  have hsF : Summable (fun j => fderiv ℝ (f j s) x) :=
    Summable.of_norm_bounded hg (fun j => (hd j x (mem_ball_self hr)).2)
  have hfd : fderiv ℝ (U s) x = ∑' j, fderiv ℝ (f j s) x :=
    (hF.congr_of_eventuallyEq hUx).fderiv
  have hdir : ∀ v : ℝ × ℝ,
      HasSum (fun j => fderiv ℝ (f j s) x v) (fderiv ℝ (U s) x v) := fun v => by
    rw [hfd]; exact hsF.hasSum.mapL (ContinuousLinearMap.apply ℝ ℝ v)
  obtain ⟨r2, hr2, g2, hg2, hd2⟩ := hS
  have hD : HasDerivAt (fun t => ∑' j, f j t x) (∑' j, deriv (fun t' => f j t' x) s) s :=
    hasDerivAt_tsum_of_isPreconnected (g := fun j t => f j t x)
      (g' := fun j t => deriv (fun t' => f j t' x) t) hg2 isOpen_ball
      (convex_ball s r2).isPreconnected (fun j t ht => (hd2 j t ht).1.hasDerivAt)
      (fun j t ht => (hd2 j t ht).2) (mem_ball_self hr2)
      (by simpa using hsum) (mem_ball_self hr2)
  have hsD : Summable (fun j => deriv (fun t' => f j t' x) s) :=
    Summable.of_norm_bounded hg2 (fun j => (hd2 j s (mem_ball_self hr2)).2)
  have hdv : deriv (fun t => U t x) s = ∑' j, deriv (fun t' => f j t' x) s :=
    (hD.congr_of_eventuallyEq hUs).deriv
  refine ⟨?_, hdir (ei 0), hdir (ei 1), ?_⟩
  · rw [hUx.self_of_nhds]; exact hsum.hasSum
  · have h1 : HasSum (fun j => x.2 * fderiv ℝ (f j s) x (ei 1))
        (x.2 * fderiv ℝ (U s) x (ei 1)) := (hdir (ei 1)).mul_left x.2
    have h2 : HasSum (fun j => 2 * s * deriv (fun t' => f j t' x) s)
        (2 * s * deriv (fun t => U t x) s) := by
      rw [hdv]; exact hsD.hasSum.mul_left (2 * s)
    exact h1.add h2

/-- x-local majorants (value summability and `‖∂_x‖` bound on a ball) for the lattice terms of
`h^p_A` (source 5063-5079).  Task `.../2`. -/
def HpXData : Prop :=
  ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2), TsumXData (gradHpTm i ν χf A) s x

/-- s-local majorants (`|∂_s|` bound on an interval around `s`, including the endpoint
`s = (11/10)/ν`) for the lattice terms of `h^p_A`.  Task `.../6`. -/
def HpSData : Prop :=
  ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ (x : ℝ × ℝ) (i : Fin 2), TsumSData (gradHpTm i ν χf A) s x

theorem gradHpTsum_of (hX : HpXData) (hS : HpSData) : GradHpTsum := by
  intro ν s χf A hd x i
  have hX0 := hX ν s χf A hd x 0
  have hX1 := hX ν s χf A hd x 1
  have hS0 := hS ν s χf A hd x 0
  have hS1 := hS ν s χf A hd x 1
  have hv0 : Summable (fun j => gradHpTm 0 ν χf A j s x) := by
    obtain ⟨_, _, _, _, h, _⟩ := hX0; exact h
  have hv1 : Summable (fun j => gradHpTm 1 ν χf A j s x) := by
    obtain ⟨_, _, _, _, h, _⟩ := hX1; exact h
  have key : ∀ (s' : ℝ) (y : ℝ × ℝ),
      Summable (fun j => gradHpTm 0 ν χf A j s' y) → Summable (fun j => gradHpTm 1 ν χf A j s' y) →
      hpA ν χf A s' y = (∑' j, gradHpTm 0 ν χf A j s' y, ∑' j, gradHpTm 1 ν χf A j s' y) := by
    intro s' y h0 h1
    have h := h0.hasSum.prodMk h1.hasSum
    rw [hpA_eq]
    have e : (fun j => hpATerm ν χf A s' y j) = fun j => (gradHpTm 0 ν χf A j s' y,
        gradHpTm 1 ν χf A j s' y) := by
      funext j; simp [gradHpTm]
    rw [e]; exact h.tsum_eq
  have hcomp : ∀ (s' : ℝ) (y : ℝ × ℝ),
      Summable (fun j => gradHpTm 0 ν χf A j s' y) → Summable (fun j => gradHpTm 1 ν χf A j s' y) →
      gradHpU i ν χf A s' y = ∑' j, gradHpTm i ν χf A j s' y := by
    intro s' y h0 h1
    have := key s' y h0 h1
    fin_cases i
    · simp [gradHpU, hpR, this, gradHpTm]
    · simp [gradHpU, hpZ, this, gradHpTm]
  have hUx : ∀ᶠ y in nhds x, gradHpU i ν χf A s y = ∑' j, gradHpTm i ν χf A j s y := by
    filter_upwards [hX0.summable_nhds, hX1.summable_nhds] with y h0 h1
    exact hcomp s y h0 h1
  have hUs : ∀ᶠ t in nhds s, gradHpU i ν χf A t x = ∑' j, gradHpTm i ν χf A j t x := by
    filter_upwards [hS0.summable_nhds hv0, hS1.summable_nhds hv1] with t h0 h1
    exact hcomp t x h0 h1
  exact tsumOps_of hUx hUs (hX ν s χf A hd x i) (hS ν s χf A hd x i)

end UnforcedLeray.Short.PartIIIb.Concrete
