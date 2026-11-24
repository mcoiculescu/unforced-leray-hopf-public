import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6

/-!
# `StreamCutDiv`: divergence of the outward stream cutoff (task `PartIII-b:C/srcL/7/15`)

Source of record: `the November 2 reference manuscript`, lines 4182-4186
(`𝒞_y Z = χ_y Z + (χ_y'/r) Ψ_Z e_z`).  With `r = cylR y`, `χ = chiYr ν ε χy`, the gradient of
`cylR` is `(y₁,y₂)/r` in the first two slots and `0` in the third; the product and chain rules
then give the stated identity componentwise.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem streamCutDiv : StreamCutDiv := by
  intro ν ε χy hχ hε Z y hr hZd hΨd
  have hχs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chiYr ν ε χy) (Ioi 0) :=
    chiYr_contDiffOn hχ hε
  have hχ' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (chiYr ν ε χy)) (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hχs).2
  have hχd1 : DifferentiableAt ℝ (chiYr ν ε χy) (cylR y) :=
    (hχs.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)
  have hχd2 : DifferentiableAt ℝ (deriv (chiYr ν ε χy)) (cylR y) :=
    (hχ'.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)
  have hne : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    rw [← cylR_sq_sum]; exact (pow_pos hr 2).ne'
  have hq0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) y
  have hq1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) y
  have hsq := ((hq0.pow 2).add (hq1.pow 2)).sqrt hne
  set Lc : Vec3 →L[ℝ] ℝ :=
    (y 0 / cylR y) • ContinuousLinearMap.proj 0 + (y 1 / cylR y) • ContinuousLinearMap.proj 1
    with hLc
  have hcylF : HasFDerivAt cylR Lc y := by
    refine HasFDerivAt.congr_fderiv hsq ?_
    ext v
    simp only [hLc, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul, Pi.add_apply]
    rw [show cylR y = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) from rfl]
    have hpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by unfold cylR at hr; exact hr
    field_simp
    ring
  have hcylD : DifferentiableAt ℝ cylR y := hcylF.differentiableAt
  have hcylFd : fderiv ℝ cylR y = Lc := hcylF.fderiv
  have hfd : ∀ v : Vec3, fderiv ℝ cylR y v = (y 0 * v 0 + y 1 * v 1) / cylR y := by
    intro v
    rw [hcylFd, hLc]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  have hfe : fderiv ℝ cylR y (Pi.single 2 1) = 0 := by
    rw [hfd]; simp
  have hχc : DifferentiableAt ℝ (fun z => chiYr ν ε χy (cylR z)) y := hχd1.comp y hcylD
  have hcD : fderiv ℝ (fun z => chiYr ν ε χy (cylR z)) y =
      deriv (chiYr ν ε χy) (cylR y) • fderiv ℝ cylR y := by
    rw [hcylFd]
    exact (hχd1.hasDerivAt.comp_hasFDerivAt y hcylF).fderiv
  have hh : DifferentiableAt ℝ (fun t => deriv (chiYr ν ε χy) t / t) (cylR y) :=
    hχd2.div differentiableAt_id hr.ne'
  have hfn : DifferentiableAt ℝ (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z) y :=
    hh.comp y hcylD
  have hfe2 : fderiv ℝ (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z) y (Pi.single 2 1) = 0 := by
    have hc' : fderiv ℝ (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z) y =
        deriv (fun t => deriv (chiYr ν ε χy) t / t) (cylR y) • fderiv ℝ cylR y := by
      rw [hcylFd]
      exact (hh.hasDerivAt.comp_hasFDerivAt y hcylF).fderiv
    rw [hc', ContinuousLinearMap.smul_apply, hfe, smul_zero]
  have hA : DifferentiableAt ℝ (fun z => chiYr ν ε χy (cylR z) • Z z) y := hχc.smul hZd
  have hBc : DifferentiableAt ℝ
      (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) y := hfn.mul hΨd
  have hB : DifferentiableAt ℝ
      (fun z => (deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) • (![0, 0, 1] : Vec3)) y :=
    hBc.smul_const _
  have hAd : fderiv ℝ (fun z => chiYr ν ε χy (cylR z) • Z z) y =
      chiYr ν ε χy (cylR y) • fderiv ℝ Z y +
        (fderiv ℝ (fun z => chiYr ν ε χy (cylR z)) y).smulRight (Z y) :=
    fderiv_smul hχc hZd
  have hBd : fderiv ℝ
      (fun z => (deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) • (![0, 0, 1] : Vec3)) y =
      (fderiv ℝ (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) y).smulRight
        (![0, 0, 1] : Vec3) :=
    fderiv_smul_const hBc _
  have hgd : fderiv ℝ (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) y =
      (deriv (chiYr ν ε χy) (cylR y) / cylR y) • fderiv ℝ (streamPsi Z) y +
        (streamPsi Z y) • fderiv ℝ (fun z => deriv (chiYr ν ε χy) (cylR z) / cylR z) y :=
    fderiv_mul hfn hΨd
  have hsc : streamCut ν ε χy Z = fun z => chiYr ν ε χy (cylR z) • Z z +
      (deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) • (![0, 0, 1] : Vec3) := rfl
  have hfsum : fderiv ℝ (fun z => chiYr ν ε χy (cylR z) • Z z +
      (deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) • (![0, 0, 1] : Vec3)) y =
      fderiv ℝ (fun z => chiYr ν ε χy (cylR z) • Z z) y +
        fderiv ℝ (fun z => (deriv (chiYr ν ε χy) (cylR z) / cylR z * streamPsi Z z) • (![0, 0, 1] : Vec3)) y :=
    fderiv_add hA hB
  rw [hsc]
  simp only [hfsum]
  simp only [ContinuousLinearMap.add_apply, hAd, hBd, hgd, hcD, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hfd,
    hfe2, Fin.sum_univ_three]
  simp [Pi.single_apply]
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
