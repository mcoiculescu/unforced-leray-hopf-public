import UnforcedLeray.Short.PartIIb.Sub.T12_1
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville

/-!
# Part II-b, task `PartII-b:T12/1/2` (`CylDivCurlFreeZero`): the Liouville core of the
uniqueness

Source of record: `the November 2 reference manuscript`, line 1670 and the
zero-frequency remark at lines 1727-1731. The target is `CylDivCurlFreeZero` of `Sub/T12_1.lean`.

## Proof

Let `Φ z = (z.re, z.im)` and `F z = u (Φ z) - i v (Φ z)` (complex valued, `z = q + iη`).

* `F` is complex differentiable: it is real differentiable (`u, v` are `C^∞`), and its real
  derivative `D` satisfies `D I = I • D 1` by the two div-curl equations (the Cauchy-Riemann
  equations of `F`). This uses `differentiableAt_complex_iff_differentiableAt_real`.
* `F` is bounded on all of `ℂ`, since `|u| ≤ M` and `|v| ≤ M` globally.
* Liouville (`Differentiable.apply_eq_apply_of_bounded`) makes `F` constant, so `u` and `v`
  are constants `u (0,0)` and `v (0,0)`.
* A nonzero constant is not in `L^r(Cyl.avgμ c)`, because `Cyl.avgμ c univ = ∞`
  (`Cyl.avgμ_univ_prod`, `Real.volume_univ`) and `memLp_const_iff` applies.

No periodicity and no logarithm are needed: boundedness is assumed globally.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cylDivCurlFreeZero : CylDivCurlFreeZero := by
  intro c r u v hc hr hu hv _hperu _hperv hbdd hLu hLv hdiv hcurl
  obtain ⟨M, hM⟩ := hbdd
  -- the real-linear map `z ↦ (re z, im z)`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ →L[ℝ] ℝ × ℝ, ∀ w : ℂ, Φ w = (w.re, w.im) :=
    ⟨Complex.reCLM.prod Complex.imCLM, fun w => by simp⟩
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hdv : Differentiable ℝ v := hv.differentiable (by simp)
  have hI : Φ I = (0, 1) := by rw [hΦ]; simp
  have hone : Φ 1 = (1, 0) := by rw [hΦ]; simp
  -- the complex function `F = u - i v`
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ,
      F = fun z => Complex.ofRealCLM (u (Φ z)) - I * Complex.ofRealCLM (v (Φ z)) :=
    ⟨_, rfl⟩
  have hFd : ∀ z : ℂ, HasFDerivAt F
      (Complex.ofRealCLM.comp ((fderiv ℝ u (Φ z)).comp Φ) -
        I • Complex.ofRealCLM.comp ((fderiv ℝ v (Φ z)).comp Φ)) z := by
    intro z
    rw [hFdef]
    have hu' := HasFDerivAt.comp z (hdu (Φ z)).hasFDerivAt Φ.hasFDerivAt
    have hv' := HasFDerivAt.comp z (hdv (Φ z)).hasFDerivAt Φ.hasFDerivAt
    exact (HasFDerivAt.comp z Complex.ofRealCLM.hasFDerivAt hu').sub
      ((HasFDerivAt.comp z Complex.ofRealCLM.hasFDerivAt hv').const_mul I)
  -- the Cauchy-Riemann equation of `F`
  have hCR : ∀ z : ℂ, fderiv ℝ F z I = I • fderiv ℝ F z 1 := by
    intro z
    rw [(hFd z).fderiv]
    have h1 := hdiv (Φ z)
    have h2 := hcurl (Φ z)
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, hI, hone, smul_eq_mul]
    apply Complex.ext <;> simp <;> linarith
  have hdiffC : Differentiable ℂ F := fun z =>
    differentiableAt_complex_iff_differentiableAt_real.2 ⟨(hFd z).differentiableAt, hCR z⟩
  -- boundedness of `F` on the whole plane
  have hbdF : Bornology.IsBounded (Set.range F) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨2 * M, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : F z = Complex.ofRealCLM (u (Φ z)) - I * Complex.ofRealCLM (v (Φ z)) := by
      rw [hFdef]
    have h1 : ‖Complex.ofRealCLM (u (Φ z))‖ ≤ M := by
      rw [Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs]
      exact (hM _).1
    have h2 : ‖I * Complex.ofRealCLM (v (Φ z))‖ ≤ M := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.ofRealCLM_apply, Complex.norm_real,
        Real.norm_eq_abs]
      exact (hM _).2
    rw [hz]
    calc ‖Complex.ofRealCLM (u (Φ z)) - I * Complex.ofRealCLM (v (Φ z))‖
        ≤ ‖Complex.ofRealCLM (u (Φ z))‖ + ‖I * Complex.ofRealCLM (v (Φ z))‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add h1 h2
      _ = 2 * M := by ring
  -- Liouville: `F` is constant
  have hconst : ∀ z : ℂ, F z = F 0 := fun z => hdiffC.apply_eq_apply_of_bounded hbdF z 0
  have h0 : Φ 0 = (0, 0) := by rw [hΦ]; simp
  have hu_const : ∀ p : ℝ × ℝ, u p = u (0, 0) ∧ v p = v (0, 0) := by
    intro p
    have hΦp : Φ ⟨p.1, p.2⟩ = p := by simp [hΦ]
    have h := hconst ⟨p.1, p.2⟩
    rw [hFdef] at h
    simp only [hΦp, h0] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    constructor <;> linarith
  -- a nonzero constant is not in `L^r(avgμ c)`
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hptop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have htop : UnforcedLeray.Cyl.avgμ c Set.univ = ⊤ := by
    have h := UnforcedLeray.Cyl.avgμ_univ_prod hc Set.univ
    rw [Set.univ_prod_univ, Real.volume_univ] at h
    exact h
  have hua : u (0, 0) = 0 := by
    have hLu' : MemLp (fun _ : ℝ × ℝ => u (0, 0)) (ENNReal.ofReal r)
        (UnforcedLeray.Cyl.avgμ c) := by
      rw [show (fun _ : ℝ × ℝ => u (0, 0)) = u from funext fun p => (hu_const p).1.symm]
      exact hLu
    rcases (memLp_const_iff hp0 hptop).1 hLu' with h | h
    · exact h
    · rw [htop] at h
      exact absurd h (lt_irrefl _)
  have hvb : v (0, 0) = 0 := by
    have hLv' : MemLp (fun _ : ℝ × ℝ => v (0, 0)) (ENNReal.ofReal r)
        (UnforcedLeray.Cyl.avgμ c) := by
      rw [show (fun _ : ℝ × ℝ => v (0, 0)) = v from funext fun p => (hu_const p).2.symm]
      exact hLv
    rcases (memLp_const_iff hp0 hptop).1 hLv' with h | h
    · exact h
    · rw [htop] at h
      exact absurd h (lt_irrefl _)
  intro z
  exact ⟨by rw [(hu_const z).1, hua], by rw [(hu_const z).2, hvb]⟩

end UnforcedLeray.Short.IIb
