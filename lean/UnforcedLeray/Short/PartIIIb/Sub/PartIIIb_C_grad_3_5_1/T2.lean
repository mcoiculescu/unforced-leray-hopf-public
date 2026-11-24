import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `PartIII-b:C/grad/3/5/1` task T2: `HpATermC1` for every term of `h^p_A`

Source 4973-4980, 4741-4745.  Each term `(s,x) ↦ [V_j, A^y_mer x_j]` is `C^1` on `{s>0}`:
`A^y = χ(ν s) A(s)` is `C^6` on `(0,∞)`, `V_j` is jointly `C^∞` on `{s>0}` (since `1 + νs > 0`),
and the `x`-derivative of a jointly `C^2` function is jointly `C^1` (`fderiv` in the `x` slot is
the restriction of the joint derivative).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma t2_isOpen_pos : IsOpen {p : Chart | 0 < p.1} :=
  isOpen_lt continuous_const continuous_fst

lemma t2_ageA_ne (ν : ℝ) (hν : 0 < ν) (p : Chart) (hp : 0 < p.1) : ageA ν p.1 ≠ 0 := by
  have h : 0 < 1 + ν * p.1 := by
    have := mul_pos hν hp
    linarith
  exact h.ne'

/-- `Ay` is `C^6` on `(0,∞)`. -/
lemma t2_Ay_contDiffOn (ν : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (A : ℝ → Mat3)
    (hA : ContDiffOn ℝ 6 A (Ioi 0)) : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := by
  have hc : ContDiff ℝ 6 (fun s : ℝ => χ (ν * s)) :=
    (hχ.smooth.comp (contDiff_const.mul contDiff_id)).of_le
      (by norm_num)
  exact hc.contDiffOn.smul hA

/-- Entrywise restriction of a `C^n` matrix field. -/
lemma t2_entry_contDiffOn {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}
    {n : WithTop ℕ∞} (f : X → Mat3) (hf : ContDiffOn ℝ n f s) (i j : Fin 3) :
    ContDiffOn ℝ n (fun x => f x i j) s :=
  contDiffOn_pi.1 (contDiffOn_pi.1 hf i) j

/-- `(A, x) ↦ A_mer x` is `C^n` when both arguments are. -/
lemma t2_merApply_contDiffOn {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}
    {n : WithTop ℕ∞} (f : X → Mat3) (g : X → ℝ × ℝ) (hf : ContDiffOn ℝ n f s)
    (hg : ContDiffOn ℝ n g s) : ContDiffOn ℝ n (fun x => merApply (f x) (g x)) s := by
  unfold merApply
  have g1 : ContDiffOn ℝ n (fun x => (g x).1) s := contDiff_fst.comp_contDiffOn hg
  have g2 : ContDiffOn ℝ n (fun x => (g x).2) s := contDiff_snd.comp_contDiffOn hg
  exact ContDiffOn.prodMk
    (((t2_entry_contDiffOn f hf 0 0).mul g1).add ((t2_entry_contDiffOn f hf 0 2).mul g2))
    (((t2_entry_contDiffOn f hf 2 0).mul g1).add ((t2_entry_contDiffOn f hf 2 2).mul g2))

/-- The `x`-partial of a function on the chart is the restriction of the joint derivative. -/
lemma t2_fderiv_x {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Chart → F)
    (hG : ContDiffOn ℝ 1 G {p : Chart | 0 < p.1}) (p : Chart) (hp : 0 < p.1) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => G (p.1, y)) p.2 v = fderiv ℝ G p (0, v) := by
  have hd : DifferentiableAt ℝ G p :=
    (hG.differentiableOn one_ne_zero).differentiableAt (t2_isOpen_pos.mem_nhds hp)
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => (p.1, y))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h2 : HasFDerivAt G (fderiv ℝ G p) (p.1, p.2) := hd.hasFDerivAt
  have := (h2.comp p.2 h1).fderiv
  have e : (fun y : ℝ × ℝ => G (p.1, y)) = G ∘ (fun y : ℝ × ℝ => (p.1, y)) := rfl
  rw [e, this]
  simp

/-- The joint `C^2` regularity of `(s,x) ↦ V_j(s,x)` on `{s>0}`. -/
lemma t2_V_contDiffOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContDiffOn ℝ 2 (fun p : Chart => Vj ν p.1 j p.2) {p : Chart | 0 < p.1} := by
  have ha : ContDiff ℝ 2 (fun p : Chart => ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hden : ContDiff ℝ 2 (fun p : Chart => 4 * ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hg : ContDiff ℝ 2 (fun p : Chart => -(sq2 (xj ν j p.2))) := by
    unfold sq2 xj
    fun_prop
  have hJ : ContDiff ℝ 2 (fun p : Chart => Jrot (xj ν j p.2)) := by
    unfold Jrot xj
    fun_prop
  have hinv : ContDiffOn ℝ 2 (fun p : Chart => (ageA ν p.1 ^ 2)⁻¹) {p : Chart | 0 < p.1} :=
    ContDiffOn.inv (ha.pow 2).contDiffOn (fun p hp => pow_ne_zero 2 (t2_ageA_ne ν hν p hp))
  have hdiv : ContDiffOn ℝ 2 (fun p : Chart => -(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))
      {p : Chart | 0 < p.1} :=
    ContDiffOn.div hg.contDiffOn hden.contDiffOn
      (fun p hp => mul_ne_zero (by norm_num) (t2_ageA_ne ν hν p hp))
  have hexp : ContDiffOn ℝ 2 (fun p : Chart => Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)))
      {p : Chart | 0 < p.1} :=
    Real.contDiff_exp.comp_contDiffOn hdiv
  have hc : ContDiffOn ℝ 2
      (fun p : Chart => (ageA ν p.1 ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)))
      {p : Chart | 0 < p.1} :=
    hinv.mul hexp
  exact hc.smul hJ.contDiffOn

/-- Each term of `h^p_A` is `C^1` on `{s>0}`. -/
theorem hpATermC1 (as : ℝ) : HpATermC1 as := by
  intro χ hχ ν hν A hA j
  have hA6 : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := t2_Ay_contDiffOn ν χ hχ A hA.smooth
  have hAy1 : ContDiffOn ℝ 1 (fun p : Chart => Ay ν χ A p.1) {p : Chart | 0 < p.1} :=
    (hA6.of_le (by norm_num)).comp contDiff_fst.contDiffOn (fun p hp => hp)
  have hV2 := t2_V_contDiffOn ν hν j
  have hV1 : ContDiffOn ℝ 1 (fun p : Chart => Vj ν p.1 j p.2) {p : Chart | 0 < p.1} :=
    hV2.of_le (by norm_num)
  have hxj : ContDiffOn ℝ 1 (fun p : Chart => xj ν j p.2) {p : Chart | 0 < p.1} := by
    have : ContDiff ℝ 1 (fun p : Chart => xj ν j p.2) := by
      unfold xj
      fun_prop
    exact this.contDiffOn
  have hw : ContDiffOn ℝ 1 (fun p : Chart => merApply (Ay ν χ A p.1) (xj ν j p.2))
      {p : Chart | 0 < p.1} :=
    t2_merApply_contDiffOn (fun p : Chart => Ay ν χ A p.1) (fun p : Chart => xj ν j p.2)
      hAy1 hxj
  have hT1 : ContDiffOn ℝ 1 (fun p : Chart => merApply (Ay ν χ A p.1) (Vj ν p.1 j p.2))
      {p : Chart | 0 < p.1} :=
    t2_merApply_contDiffOn (fun p : Chart => Ay ν χ A p.1) (fun p : Chart => Vj ν p.1 j p.2)
      hAy1 hV1
  have hFd : ContDiffOn ℝ 1 (fderiv ℝ (fun p : Chart => Vj ν p.1 j p.2))
      {p : Chart | 0 < p.1} :=
    hV2.fderiv_of_isOpen t2_isOpen_pos (by norm_num)
  have hM : ContDiffOn ℝ 1
      (fun p : Chart => fderiv ℝ (fun q : Chart => Vj ν q.1 j q.2) p
        ((0 : ℝ), merApply (Ay ν χ A p.1) (xj ν j p.2))) {p : Chart | 0 < p.1} :=
    hFd.clm_apply (contDiffOn_const.prodMk hw)
  have hT2 : ContDiffOn ℝ 1
      (fun p : Chart => fderiv ℝ (Vj ν p.1 j) p.2 (merApply (Ay ν χ A p.1) (xj ν j p.2)))
      {p : Chart | 0 < p.1} :=
    hM.congr (fun p hp => t2_fderiv_x (fun q : Chart => Vj ν q.1 j q.2) hV1 p hp _)
  exact (hT1.sub hT2)

end UnforcedLeray.Short.PartIIIb.Concrete
