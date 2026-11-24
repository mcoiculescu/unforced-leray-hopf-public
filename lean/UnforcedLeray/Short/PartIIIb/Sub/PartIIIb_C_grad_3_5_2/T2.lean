import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `PartIII-b:C/grad/3/5/2` task T2: `PsipATermC2` for every term of `psi^p_A`

Source 4974-4980, 4741-4745.  Each term `(s,x) ↦ (tr A^y_mer) ψ_j - (A^y_mer x_j)·∇ψ_j` is `C^2`
on `{s>0}`: `ψ_j` is `C^3` jointly on `{s>0}` (since `a = 1 + νs > 0`), `A^y` is `C^6` on `(0,∞)`,
and the `x`-derivative of a jointly `C^3` function is jointly `C^2`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma psc2_isOpen_pos : IsOpen {p : Chart | 0 < p.1} :=
  isOpen_lt continuous_const continuous_fst

lemma psc2_ageA_ne (ν : ℝ) (hν : 0 < ν) (p : Chart) (hp : 0 < p.1) : ageA ν p.1 ≠ 0 := by
  have h : 0 < 1 + ν * p.1 := by
    have := mul_pos hν hp
    linarith
  exact h.ne'

/-- `Ay` is `C^6` on `(0,∞)`. -/
lemma psc2_Ay_contDiffOn (ν : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (A : ℝ → Mat3)
    (hA : ContDiffOn ℝ 6 A (Ioi 0)) : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := by
  have hc : ContDiff ℝ 6 (fun s : ℝ => χ (ν * s)) :=
    (hχ.smooth.comp (contDiff_const.mul contDiff_id)).of_le
      (by norm_num)
  exact hc.contDiffOn.smul hA

/-- Entrywise restriction of a `C^n` matrix field. -/
lemma psc2_entry_contDiffOn {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}
    {n : WithTop ℕ∞} (f : X → Mat3) (hf : ContDiffOn ℝ n f s) (i j : Fin 3) :
    ContDiffOn ℝ n (fun x => f x i j) s :=
  contDiffOn_pi.1 (contDiffOn_pi.1 hf i) j

/-- `(A, x) ↦ A_mer x` is `C^n` when both arguments are. -/
lemma psc2_merApply_contDiffOn {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}
    {n : WithTop ℕ∞} (f : X → Mat3) (g : X → ℝ × ℝ) (hf : ContDiffOn ℝ n f s)
    (hg : ContDiffOn ℝ n g s) : ContDiffOn ℝ n (fun x => merApply (f x) (g x)) s := by
  unfold merApply
  have g1 : ContDiffOn ℝ n (fun x => (g x).1) s := contDiff_fst.comp_contDiffOn hg
  have g2 : ContDiffOn ℝ n (fun x => (g x).2) s := contDiff_snd.comp_contDiffOn hg
  exact ContDiffOn.prodMk
    (((psc2_entry_contDiffOn f hf 0 0).mul g1).add ((psc2_entry_contDiffOn f hf 0 2).mul g2))
    (((psc2_entry_contDiffOn f hf 2 0).mul g1).add ((psc2_entry_contDiffOn f hf 2 2).mul g2))

/-- The `x`-partial of a function on the chart is the restriction of the joint derivative. -/
lemma psc2_fderiv_x {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Chart → F)
    (hG : ContDiffOn ℝ 1 G {p : Chart | 0 < p.1}) (p : Chart) (hp : 0 < p.1) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => G (p.1, y)) p.2 v = fderiv ℝ G p (0, v) := by
  have hd : DifferentiableAt ℝ G p :=
    (hG.differentiableOn one_ne_zero).differentiableAt (psc2_isOpen_pos.mem_nhds hp)
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => (p.1, y))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h2 : HasFDerivAt G (fderiv ℝ G p) (p.1, p.2) := hd.hasFDerivAt
  have := (h2.comp p.2 h1).fderiv
  have e : (fun y : ℝ × ℝ => G (p.1, y)) = G ∘ (fun y : ℝ × ℝ => (p.1, y)) := rfl
  rw [e, this]
  simp

/-- `(s,x) ↦ ψ_j(s,x)` is jointly `C^3` on `{s>0}`. -/
lemma psc2_psij_contDiffOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContDiffOn ℝ 3 (fun p : Chart => psij ν p.1 j p.2) {p : Chart | 0 < p.1} := by
  have ha : ContDiff ℝ 3 (fun p : Chart => ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hden : ContDiff ℝ 3 (fun p : Chart => 4 * ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hg : ContDiff ℝ 3 (fun p : Chart => -(sq2 (xj ν j p.2))) := by
    unfold sq2 xj
    fun_prop
  have hinv : ContDiffOn ℝ 3 (fun p : Chart => (ageA ν p.1)⁻¹) {p : Chart | 0 < p.1} :=
    ContDiffOn.inv ha.contDiffOn (fun p hp => psc2_ageA_ne ν hν p hp)
  have hdiv : ContDiffOn ℝ 3 (fun p : Chart => -(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))
      {p : Chart | 0 < p.1} :=
    ContDiffOn.div hg.contDiffOn hden.contDiffOn
      (fun p hp => mul_ne_zero (by norm_num) (psc2_ageA_ne ν hν p hp))
  have hexp : ContDiffOn ℝ 3 (fun p : Chart => Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)))
      {p : Chart | 0 < p.1} :=
    Real.contDiff_exp.comp_contDiffOn hdiv
  exact ((contDiffOn_const (c := (-2 : ℝ))).mul hinv).mul hexp

/-- Each term of `ψ^p_A` is `C^2` on `{s>0}`. -/
theorem psipATermC2 (as : ℝ) : PsipATermC2 as := by
  intro χ hχ ν hν A hA j
  have hA6 : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := psc2_Ay_contDiffOn ν χ hχ A hA.smooth
  have hAy2 : ContDiffOn ℝ 2 (fun p : Chart => Ay ν χ A p.1) {p : Chart | 0 < p.1} :=
    (hA6.of_le (by norm_num)).comp contDiff_fst.contDiffOn (fun p hp => hp)
  have hxj2 : ContDiffOn ℝ 2 (fun p : Chart => xj ν j p.2) {p : Chart | 0 < p.1} := by
    have : ContDiff ℝ 2 (fun p : Chart => xj ν j p.2) := by
      unfold xj
      fun_prop
    exact this.contDiffOn
  have hW : ContDiffOn ℝ 2 (fun p : Chart => merApply (Ay ν χ A p.1) (xj ν j p.2))
      {p : Chart | 0 < p.1} :=
    psc2_merApply_contDiffOn (fun p : Chart => Ay ν χ A p.1) (fun p : Chart => xj ν j p.2)
      hAy2 hxj2
  have hG3 := psc2_psij_contDiffOn ν hν j
  have hG1 : ContDiffOn ℝ 1 (fun p : Chart => psij ν p.1 j p.2) {p : Chart | 0 < p.1} :=
    hG3.of_le (by norm_num)
  have hPsi2 : ContDiffOn ℝ 2 (fun p : Chart => psij ν p.1 j p.2) {p : Chart | 0 < p.1} :=
    hG3.of_le (by norm_num)
  have hFd : ContDiffOn ℝ 2 (fderiv ℝ (fun p : Chart => psij ν p.1 j p.2))
      {p : Chart | 0 < p.1} :=
    hG3.fderiv_of_isOpen psc2_isOpen_pos (by norm_num)
  have hM : ContDiffOn ℝ 2
      (fun p : Chart => fderiv ℝ (fun q : Chart => psij ν q.1 j q.2) p
        ((0 : ℝ), merApply (Ay ν χ A p.1) (xj ν j p.2))) {p : Chart | 0 < p.1} :=
    hFd.clm_apply (contDiffOn_const.prodMk hW)
  have hT2 : ContDiffOn ℝ 2
      (fun p : Chart => fderiv ℝ (psij ν p.1 j) p.2 (merApply (Ay ν χ A p.1) (xj ν j p.2)))
      {p : Chart | 0 < p.1} :=
    hM.congr (fun p hp => psc2_fderiv_x (fun q : Chart => psij ν q.1 j q.2) hG1 p hp _)
  have hT : ContDiffOn ℝ 2 (fun p : Chart => merTrace (Ay ν χ A p.1)) {p : Chart | 0 < p.1} := by
    unfold merTrace
    exact (psc2_entry_contDiffOn (fun p : Chart => Ay ν χ A p.1) hAy2 0 0).add
      (psc2_entry_contDiffOn (fun p : Chart => Ay ν χ A p.1) hAy2 2 2)
  have key : ContDiffOn ℝ 2
      (fun p : Chart => merTrace (Ay ν χ A p.1) * psij ν p.1 j p.2
        - fderiv ℝ (psij ν p.1 j) p.2 (merApply (Ay ν χ A p.1) (xj ν j p.2)))
      {p : Chart | 0 < p.1} :=
    (hT.mul hPsi2).sub hT2
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
