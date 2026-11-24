import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_1_2
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftOffAxis.Rep

/-!
# Part II-b, helper for `PartII-b:T09/1/2/2`: chart divergence of the ring lift

Source: `the November 2 reference manuscript` 1639-1668, 1912-1916.
Off the axis, for `R > 0`, a differentiable profile `b`, with `c = chart R τ y`, `s = age`, `η = trans`:
`div_y N_v b = s (∂_q b₀ - R⁻¹ (2 s ∂_s b₀ + η ∂_η b₀) + ∂_η b₁)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.DivOff

open UnforcedLeray UnforcedLeray.Short.IIb.DriftOff

theorem coord_sum (y : Space) : ∑ j : Fin 3, y j • coordinateVector j = y := by
  ext i
  fin_cases i <;> simp [coordinateVector, Fin.sum_univ_three, PiLp.single_apply]

theorem sum_coord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F)
    (v : Space) : ∑ j : Fin 3, v j • L (coordinateVector j) = L v := by
  conv_rhs => rw [← coord_sum v]
  rw [map_sum]
  simp only [map_smul]

theorem div_eRD {y : Space} (hy : y ∉ Axi.axis) :
    ∑ j : Fin 3, Axi.eRD y (coordinateVector j) j = (Axi.ϱ y)⁻¹ := by
  have hac := Axi.eR_sq_sum hy
  have hρ := Axi.ϱ_ne_zero hy
  simp only [Fin.sum_univ_three, Axi.eRD_apply_coord, Axi.ϱD_apply, Axi.hor_apply_zero,
    Axi.hor_apply_one, Axi.hor_apply_two, Axi.eR_apply_zero, Axi.eR_apply_one,
    Axi.eR_apply_two, Axi.coordinateVector_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  field_simp
  linear_combination Axi.ϱ_sq y

theorem div_core {R : ℝ} (hR : 0 < R) {b : CProf} (hbd : Differentiable ℝ b) (τ : ℝ)
    {y : Space} (hy : y ∉ Axi.axis) :
    ∑ j : Fin 3, fderiv ℝ (fun y' : Space => NvC R b (τ, y')) y (coordinateVector j) j =
      (Axi.age R y : ℂ) *
        ((Axi.dQ b (Axi.chart R τ y) -
          R⁻¹ • ((2 * Axi.age R y) • Axi.dS b (Axi.chart R τ y) +
            Axi.trans R y • Axi.dEta b (Axi.chart R τ y))) 0 +
          Axi.dEta b (Axi.chart R τ y) 1) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hρ := Axi.ϱ_pos hy
  have hs : √(Axi.age R y) = R / Axi.ϱ y := Axi.sqrt_age hR hy
  have hBd : HasFDerivAt (fun x : Space => b (Axi.chart R τ x))
      ((fderiv ℝ b (Axi.chart R τ y)).comp (Axi.chartD R y)) y :=
    (hbd _).hasFDerivAt.comp y (Axi.hasFDerivAt_chart hR0 τ hy)
  have hB0 := ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Short.IIb.CMerid →L[ℂ] ℂ).restrictScalars
    ℝ).hasFDerivAt.comp y hBd
  have hB1 := ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Short.IIb.CMerid →L[ℂ] ℂ).restrictScalars
    ℝ).hasFDerivAt.comp y hBd
  have hE : HasFDerivAt (fun x : Space => realCL (Axi.eR x)) (realCL.comp (Axi.eRD y)) y :=
    realCL.hasFDerivAt.comp y (Axi.hasFDerivAt_eR hy)
  have hA : HasFDerivAt (fun x : Space => √(Axi.age R x))
      ((1 / (2 * √(Axi.age R y))) • Axi.ageD R y) y :=
    (Axi.hasFDerivAt_age R hy).sqrt (Axi.age_pos hR0 hy).ne'
  have hG := hA.fun_smul ((hB0.fun_smul hE).add (hB1.fun_smul (hasFDerivAt_const (realCL Axi.e3) y)))
  have hNv : (fun y' : Space => NvC R b (τ, y')) = fun x : Space =>
      √(Axi.age R x) • ((b (Axi.chart R τ x)) 0 • realCL (Axi.eR x) +
        (b (Axi.chart R τ x)) 1 • realCL Axi.e3) :=
    funext fun x => nvC_rep R b (τ, x)
  have hG' : HasFDerivAt (fun x : Space =>
      √(Axi.age R x) • ((b (Axi.chart R τ x)) 0 • realCL (Axi.eR x) +
        (b (Axi.chart R τ x)) 1 • realCL Axi.e3)) _ y := hG
  rw [hNv, hG'.fderiv]
  -- the three linear facts
  have hr2 : Axi.eR y 2 = 0 := Axi.eR_apply_two y
  have hLB : ∀ v : Space, ((fderiv ℝ b (Axi.chart R τ y)).comp (Axi.chartD R y)) v =
      fderiv ℝ b (Axi.chart R τ y) (Axi.chartD R y v) := fun v => rfl
  have hU : ∀ k : Fin 2, ∑ j : Fin 3, Axi.eR y j •
      (fderiv ℝ b (Axi.chart R τ y) (Axi.chartD R y (coordinateVector j))).ofLp k =
        (fderiv ℝ b (Axi.chart R τ y) (Axi.chartD R y (Axi.eR y))).ofLp k := by
    intro k
    have := sum_coord (((EuclideanSpace.proj k : UnforcedLeray.Short.IIb.CMerid →L[ℂ] ℂ).restrictScalars
      ℝ).comp ((fderiv ℝ b (Axi.chart R τ y)).comp (Axi.chartD R y))) (Axi.eR y)
    simpa using this
  have hAg : ∑ j : Fin 3, Axi.eR y j • Axi.ageD R y (coordinateVector j) =
      Axi.ageD R y (Axi.eR y) := sum_coord (Axi.ageD R y) (Axi.eR y)
  have hrad := Axi.radial_chain hR hy (hbd (Axi.chart R τ y))
  have hax := Axi.axial_chain hR hy (hbd (Axi.chart R τ y))
  rw [Axi.fderiv_comp_chart_apply hR0 hy (hbd (Axi.chart R τ y))] at hrad hax
  have hDiv := div_eRD hy
  simp only [Fin.sum_univ_three] at hU hAg hDiv
  have hU0 := hU 0
  have hage_e3 : Axi.ageD R y (coordinateVector 2) = 0 := by
    have := Axi.ϱD_e3 y
    simp [Axi.ageD, this]
  have hage_eR : Axi.ageD R y (Axi.eR y) = -(2 * R ^ 2 / Axi.ϱ y ^ 3) := by
    simp [Axi.ageD, Axi.ϱD_eR hy]
  have hrad0 := congrArg (fun v : UnforcedLeray.Short.IIb.CMerid => v.ofLp 0) hrad
  have hax1 := congrArg (fun v : UnforcedLeray.Short.IIb.CMerid => v.ofLp 1) hax
  simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, Complex.real_smul] at hrad0 hax1
  have hDivC : (((Axi.eRD y (coordinateVector 0)).ofLp 0 : ℝ) : ℂ) +
      ((Axi.eRD y (coordinateVector 1)).ofLp 1 : ℝ) + ((Axi.eRD y (coordinateVector 2)).ofLp 2 : ℝ)
      = (((Axi.ϱ y)⁻¹ : ℝ) : ℂ) := by
    have := congrArg Complex.ofReal hDiv
    push_cast at this ⊢
    exact this
  have hAgC : (((Axi.eR y).ofLp 0 : ℝ) : ℂ) * ((Axi.ageD R y (coordinateVector 0) : ℝ) : ℂ) +
      (((Axi.eR y).ofLp 1 : ℝ) : ℂ) * ((Axi.ageD R y (coordinateVector 1) : ℝ) : ℂ) =
      ((-(2 * R ^ 2 / Axi.ϱ y ^ 3) : ℝ) : ℂ) := by
    have := congrArg Complex.ofReal hAg
    rw [hage_eR, hage_e3, hr2] at this
    push_cast at this ⊢
    simpa using this
  have hAx2 : ((fderiv ℝ b (Axi.chart R τ y)) ((Axi.chartD R y) (coordinateVector 2))).ofLp 1 =
      ((√(Axi.age R y) : ℝ) : ℂ) * (Axi.dEta b (Axi.chart R τ y)).ofLp 1 := hax1
  have hρC : ((Axi.ϱ y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hRC : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR0
  have hsc : ((√(Axi.age R y) : ℝ) : ℂ) = (R : ℂ) / (Axi.ϱ y : ℂ) := by
    rw [hs]; push_cast; rfl
  have hageC : ((Axi.age R y : ℝ) : ℂ) = (R : ℂ) ^ 2 / (Axi.ϱ y : ℂ) ^ 2 := by
    simp [Axi.age]
  have hsA : ((√(Axi.age R y) : ℝ) : ℂ) ≠ 0 := by rw [hsc]; exact div_ne_zero hRC hρC
  simp only [Fin.sum_univ_three]
  simp [realCL_apply, UnforcedLeray.B0412.realC_apply, Axi.e3_apply, hage_e3]
  simp [Complex.real_smul] at hU0 hAgC
  push_cast at hrad0 hAgC
  rw [hAx2]
  push_cast at hDivC
  have hfin : ((√(Axi.age R y) : ℝ) : ℂ) * ((b (Axi.chart R τ y)).ofLp 0 * (Axi.ϱ y : ℂ)⁻¹) +
      ((√(Axi.age R y) : ℝ) : ℂ) * (((√(Axi.age R y) : ℝ) : ℂ) *
        ((Axi.dQ b (Axi.chart R τ y)).ofLp 0 - (R : ℂ)⁻¹ * (2 * ((Axi.age R y : ℝ) : ℂ) *
          (Axi.dS b (Axi.chart R τ y)).ofLp 0 + ((Axi.trans R y : ℝ) : ℂ) *
            (Axi.dEta b (Axi.chart R τ y)).ofLp 0))) +
      ((√(Axi.age R y) : ℝ) : ℂ) * (((√(Axi.age R y) : ℝ) : ℂ) *
        (Axi.dEta b (Axi.chart R τ y)).ofLp 1) +
      (((√(Axi.age R y) : ℝ) : ℂ))⁻¹ * 2⁻¹ * (-(2 * (R : ℂ) ^ 2 / (Axi.ϱ y : ℂ) ^ 3)) *
        (b (Axi.chart R τ y)).ofLp 0 =
      ((Axi.age R y : ℝ) : ℂ) *
      ((Axi.dQ b (Axi.chart R τ y)).ofLp 0 -
          ((R : ℂ)⁻¹ * (2 * ((Axi.age R y : ℝ) : ℂ) * (Axi.dS b (Axi.chart R τ y)).ofLp 0) +
            (R : ℂ)⁻¹ * (((Axi.trans R y : ℝ) : ℂ) * (Axi.dEta b (Axi.chart R τ y)).ofLp 0)) +
        (Axi.dEta b (Axi.chart R τ y)).ofLp 1) := by
    rw [hsc, hageC]
    field_simp
    ring
  refine Eq.trans ?_ hfin
  linear_combination (((√(Axi.age R y) : ℝ) : ℂ) * (b (Axi.chart R τ y)).ofLp 0) * hDivC +
    ((√(Axi.age R y) : ℝ) : ℂ) * hU0 + ((√(Axi.age R y) : ℝ) : ℂ) * hrad0 +
    ((((√(Axi.age R y) : ℝ) : ℂ))⁻¹ * 2⁻¹ * (b (Axi.chart R τ y)).ofLp 0) * hAgC

end UnforcedLeray.Short.IIb.DivOff
