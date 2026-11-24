import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntCong
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `WardX0FactsOldL2` parts (a) and (b) (`PartIII-b:C/ward/6/2`, L2a)

Source of record: `the November 2 reference manuscript` 4155-4186, 3611-3621,
3604-3610.  The old `L²` datum `g` replaces the `StrG` element: the separated source is the
output `oldL2SepReg_proved` (`L1.lean`), and every other argument of the conditional Sub theorems
(`wardX0Smooth_of`, `wardX0Structure_of`) is used verbatim with `oldPhys R c g` in place of
`oldPhys ε⁻¹ c (g₁ + g₂)`, `R` in place of `ε⁻¹`, and the periodicity conjunct dropped.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace WardL2a

/-- (a) Smoothness of `X₀` on the young region (port of `wardX0Smooth_of`, `Sub/IIIb-D2_3_1_1.lean`
66-83). -/
theorem smooth (ν μ R c : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4 : ℝ) < μ) (hg : IsOldL2 c ν g) (τ : ℝ) :
    ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R) := by
  obtain ⟨P, T', hP, hS, hM, hEq, -⟩ := oldL2SepReg_proved ν R c g hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hA := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) _ P T' hν (by simpa using hμ) hr hP hS
    hM τ
  have hB := sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) _ P T' hν (by simp; linarith) hr
    hP hS hM τ
  unfold wardX0
  refine contDiffOn_piLp' 2 fun i => ?_
  have hd : ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T' y τ i -
      IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i) (youngOpen ν R) :=
    (hA i).sub (hB i)
  have := Complex.reCLM.contDiff.comp_contDiffOn hd
  refine this.congr fun y _ => ?_
  simp [hEq]

/-- (b1) Divergence free part of `X₀` on the young region (port of `wardX0Structure_of`,
`Sub/IIIb-D2_3_1_2.lean` 79-134, the first conjunct). -/
theorem divFree (ν μ R c : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4 : ℝ) < μ) (hg : IsOldL2 c ν g) (τ : ℝ) (y : Space)
    (hy : y ∈ youngOpen ν R) :
    ∑ j : Fin 3, physPd (wardX0 ν μ R c g τ) j y j = 0 := by
  obtain ⟨P, T', hPp, hS, hM, hEq, -⟩ := oldL2SepReg_proved ν R c g hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hopen : IsOpen {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hy' : y ∈ {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} := hy
  have hA' := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) _ P T' hν (by simpa using hμ) hr hPp
    hS hM τ
  have hB' := sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) _ P T' hν (by simp; linarith)
    hr hPp hS hM τ
  have dA : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T' y' τ i) y := fun i =>
    ((hA' i).contDiffAt (hopen.mem_nhds hy')).differentiableAt (by norm_num)
  have dB : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ i) y := fun i =>
    ((hB' i).contDiffAt (hopen.mem_nhds hy')).differentiableAt (by norm_num)
  have hfun : wardX0 ν μ R c g τ = fun y' => (WithLp.toLp 2 fun i =>
      (IIIa.sepW ν (μ : ℂ) T' y' τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ i).re : Space) := by
    funext y'
    unfold wardX0
    simp [hEq]
  have hdiff : DifferentiableAt ℝ (wardX0 ν μ R c g τ) y := by
    rw [hfun]
    refine (differentiableAt_piLp 2).2 fun i => ?_
    exact Complex.reCLM.differentiableAt.comp y ((dA i).sub (dB i))
  unfold physPd
  have hcd : ∀ j : Fin 3, fderiv ℝ (wardX0 ν μ R c g τ) y (coordinateVector j) j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T' y' τ j) y (coordinateVector j) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ j) y (coordinateVector j)).re := by
    intro j
    rw [fderiv_apply_coord _ _ _ _ hdiff, hfun]
    simp only
    have hh : HasFDerivAt (fun y' => (IIIa.sepW ν (μ : ℂ) T' y' τ j -
        IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ j).re)
        (Complex.reCLM.comp ((fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T' y' τ j) y) -
          (fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ j) y))) y :=
      Complex.reCLM.hasFDerivAt.comp y (((dA j).hasFDerivAt).sub ((dB j).hasFDerivAt))
    rw [hh.fderiv]
    simp
  simp only [hcd]
  have e1 := sepWDivFree_all ν (μ : ℂ) _ P T' hν (by simpa using hμ) hr hPp hS hM τ y hy
  have e2 := sepWDivFree_all ν ((μ : ℂ) + 1) _ P T' hν (by simp; linarith) hr hPp hS hM τ y hy
  rw [← Complex.re_sum, Finset.sum_sub_distrib, e1, e2]
  simp

/-- (b2) Axisymmetric swirl-free part of `X₀` on the young region (port of `wardX0Structure_of`,
the third conjunct, through `wardX0Axi_all`, `sepIntegrableOfSource_all`, `sepIntegrableCongrAE`). -/
theorem axi (ν μ R c : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4 : ℝ) < μ) (hg : IsOldL2 c ν g) :
    AxiNoSwirlOn (youngOpen ν R) (wardX0 ν μ R c g) := by
  obtain ⟨P, T', hPp, hS, hM, hEq, hae⟩ := oldL2SepReg_proved ν R c g hν hR hc hg
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  intro τ y hy' hy
  exact wardX0Axi_all ν μ R c g τ y hy
    (sepIntegrableCongrAE ν _ _ T' hae _ τ
      (sepIntegrableOfSource_all ν _ _ P T' hν (by simpa using hμ) hr0 hPp hS hM τ _
        (by rw [varrho_meridPt]; exact hy')))
    (sepIntegrableCongrAE ν _ _ T' hae _ τ
      (sepIntegrableOfSource_all ν _ _ P T' hν (by simp; linarith) hr0 hPp hS hM τ _
        (by rw [varrho_meridPt]; exact hy')))

end WardL2a

end UnforcedLeray.Short.PartIIIb.Concrete
