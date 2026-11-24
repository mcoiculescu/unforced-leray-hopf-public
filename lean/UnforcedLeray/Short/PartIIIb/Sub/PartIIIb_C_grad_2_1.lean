import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# `PartIII-b:C/grad/2/1`: `HpADiffX` from the `C²` smoothness of `V_j` and a derivative majorant

Source `the November 2 reference manuscript` 4973-4980, 4741-4745, 5081-5084.
`h^p_A = Σ_j [V_j, A^y_mer x_j]`; each lattice term is `C¹` because `V_j` is `C²`, and its
`x`-derivative has a summable Gaussian majorant on unit balls (source 4978: "the sums and their
required derivatives converge by Gaussian decay").
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf (source 4963-4968): `V_j = a⁻² e^{-|x_j|²/(4a)} J x_j` is `C²`. -/
def VjContDiff2 : Prop := ∀ (ν s : ℝ) (j : ℤ), ContDiff ℝ 2 (Vj ν s j)

/-- Leaf (source 4973, 4978): the `x`-derivative of the `j`-th lattice term of `h^p_A`,
`w ↦ M V_j(w) - DV_j(w)(M x_j(w))` (`M = A^y_mer`), is bounded on every unit ball by a summable
sequence (Gaussian decay: `(1+|y|)^4 e^{-|y|²/(4a)}` at `y = x_j`, comparison on the ball as in
`ball_geom`, `Concrete/ReturnInst/PsipADiff/XPart.lean`). -/
def HpTermMajorant : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (s : ℝ), 0 < s → ∀ (M : Mat3) (x : ℝ × ℝ),
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 →
      ‖fderiv ℝ (fun w => merApply M (Vj ν s j w) -
        fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w))) z‖ ≤ u j

theorem vjContDiff2 : VjContDiff2 := by
  intro ν s j
  unfold Vj Jrot xj sq2
  simp only
  have h1 : ContDiff ℝ 2 (fun x : ℝ × ℝ =>
      (ageA ν s ^ 2)⁻¹ * Real.exp (-((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / (4 * ageA ν s))) := by
    apply ContDiff.mul contDiff_const
    apply Real.contDiff_exp.comp
    apply ContDiff.div_const
    apply ContDiff.neg
    fun_prop
  have h2 : ContDiff ℝ 2 (fun x : ℝ × ℝ => (-x.2, x.1 - j * cOf ν)) :=
    (contDiff_snd.neg).prodMk (contDiff_fst.sub contDiff_const)
  exact h1.smul h2

theorem hpADiffX_of (as : ℝ) (χf : ℝ → ℝ) (hmaj : HpTermMajorant)
    (hsum : HpPsiTermSummable) : HpADiffX as χf := by
  have hC2 := vjContDiff2
  intro ν hν A _ s hs x
  obtain ⟨u, hu, hb⟩ := hmaj ν hν s hs (Ay ν χf A s) x
  set M := Ay ν χf A s with hM
  have hd : ∀ j : ℤ, Differentiable ℝ (fun w => merApply M (Vj ν s j w) -
      fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w))) := by
    intro j
    have hV : Differentiable ℝ (Vj ν s j) := (hC2 ν s j).differentiable (by norm_num)
    have hDV : Differentiable ℝ (fderiv ℝ (Vj ν s j)) :=
      ((hC2 ν s j).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have h1 : Differentiable ℝ (fun w => merApply M (Vj ν s j w)) := by
      unfold merApply
      have h1 := hV.fst
      have h2 := hV.snd
      fun_prop
    have h2 : Differentiable ℝ (fun w : ℝ × ℝ => merApply M (xj ν j w)) := by
      unfold merApply xj
      fun_prop
    exact h1.sub (hDV.clm_apply h2)
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun (j : ℤ) (w : ℝ × ℝ) => merApply M (Vj ν s j w) -
      fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w)))
    (f' := fun j z => fderiv ℝ (fun w => merApply M (Vj ν s j w) -
      fderiv ℝ (Vj ν s j) w (merApply M (xj ν j w))) z)
    (u := u) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected
    (fun j z _ => (hd j z).hasFDerivAt)
    (fun j z hz => hb j z (mem_ball_iff_norm.mp hz))
    (Metric.mem_ball_self one_pos) (hsum ν χf A s x hν hs).1 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete
