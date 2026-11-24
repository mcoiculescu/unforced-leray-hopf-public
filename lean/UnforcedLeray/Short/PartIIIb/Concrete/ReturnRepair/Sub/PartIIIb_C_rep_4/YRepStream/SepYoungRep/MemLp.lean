import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.MemLp.SrcMom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.MemLp.Axi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.GainYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Transport
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.WreL2

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/6`: `sepRepYoungMemLp` (finiteness of the young cut field)

Source `the November 2 reference manuscript` 4187-4194, 5169-5176.

Assembly: `sepRepSrcMom` gives the separated representative `T` (with `IsSepSource`, `SepMoment`,
`IsAxiSource` and the `L²_τL^{22/19}` bound); `sepRepYoungAEMeas` gives measurability;
`sepYoungCut` (the young cut of `sepWre`) is `AxiNoSwirl` and `2εc/R`-periodic, so
`chartYoungTransport` converts the chart `L²` mass to the young `L²_τL²` norm of the cut, which
`sepWreYoungL2` bounds by the `L²_τL^{22/19}` norm of `T`; `bodyMeasure_young_le` gives the
body density bound.

Interface note: the target's `hRS : RepairSourceAt Pl K L μ C k` has an arity defect
(`RepairSourceAt` takes no `μ`, see `Estimates.lean:278`); it is stated as `RepairSourceAt Pl K L C k`,
as in `sepRepSrcFinite`.  Everything else is as written.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The chart coefficient of the young cut equals that of `sepWre` on the young region
`ν s ≤ 1` (there `R/√s ≥ R√ν`, so the cut is inactive at the chart's receivers). -/
theorem coefOf_sepYoungCut (R ν μ : ℝ) (hR : 0 < R) (hν : 0 < ν)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (p : Chart) (hp : ν * p.1 ≤ 1) :
    coefOf R (sepYoungCut R ν μ T) p = coefOf R (sepWre ν μ T) p := by
  rcases le_or_gt p.1 0 with hs | hs
  · have h0 : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 hs
    simp [coefOf, h0]
  · have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
    have hY0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
    have hY1 : (NearInst.chartY R p) 1 = 0 := by simp [NearInst.chartY]
    have hcond : R * Real.sqrt ν ≤ Real.sqrt ((NearInst.chartY R p) 0 ^ 2 + (NearInst.chartY R p) 1 ^ 2) := by
      rw [hY0, hY1]
      have hpos : 0 ≤ R / Real.sqrt p.1 := by positivity
      rw [show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring,
        Real.sqrt_sq hpos]
      rw [le_div_iff₀ hsq]
      have h1 : Real.sqrt ν * Real.sqrt p.1 ≤ 1 := by
        rw [← Real.sqrt_mul hν.le]
        exact Real.sqrt_le_one.2 hp
      nlinarith
    unfold coefOf
    congr 1
    ext i
    fin_cases i <;> simp [sepYoungCut, hcond]

/-- Pointwise: the young cut field has the same body coefficient as `sepWre`. -/
theorem sepRepYoungMemLp (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) (k : ℕ)
    (hRS : RepairSourceAt Pl K L C k) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hμ : -(1/4) < μ)
    (hper : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹) : SepRepYoungMemLpAt Pl K L μ := by
  intro w g₁ g₂ hg
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hP : 0 < 2 * L.ε * cOf L.ν := by positivity
  obtain ⟨T, hS, hMom, hAx, hT, hlt⟩ := sepRepSrcMom Pl K L μ C k hRS hC0 hmZ w hg
  have hmeas : AEStronglyMeasurable (youngWCoef Pl K L μ (g₁ + g₂))
      (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) :=
    sepRepYoungAEMeas Pl K L μ (g₁ + g₂) T hT hS
  have hW : wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) = sepWre L.ν μ T :=
    funext fun τ => funext fun y => hT τ y
  -- the `L²_τ` bound of the young cut (`sepWreYoungL2`)
  obtain ⟨C', -, hY⟩ := sepWreYoungL2 μ μ hμ
  have hcut := hY L.ν L.ε⁻¹ (2 * L.ε * cOf L.ν) hν hR hP μ (Set.left_mem_Icc.2 le_rfl) T hS
  have hZ : IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) < ⊤ := hlt
  -- the cut field, its axisymmetry, measurability and periodicity
  have hGm := sepYoungCut_measurable L.ε⁻¹ L.ν μ hν T (fun i j => hS.measurable i j)
  have hGax := sepYoungCut_axi L.ε⁻¹ L.ν μ (2 * L.ε * cOf L.ν) hR hν hμ T hP hS hMom
    sepWEquivariance hAx
  have hGper : ∀ τ y, sepYoungCut L.ε⁻¹ L.ν μ T (τ + 2 * cOf L.ν / L.ε⁻¹) y =
      sepYoungCut L.ε⁻¹ L.ν μ T τ y := fun τ y => by
    rw [← hper]
    exact sepYoungCut_periodic _ _ _ _ T hS.periodic τ y
  have hYT := chartYoungTransport L.ε⁻¹ (cOf L.ν) L.ν hR hc hν (sepYoungCut L.ε⁻¹ L.ν μ T)
    hGm hGax hGper
  rw [← hper] at hYT
  have hcutG : (fun τ y => if L.ε⁻¹ * Real.sqrt L.ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖sepYoungCut L.ε⁻¹ L.ν μ T τ y‖ₑ else 0) =
      (fun τ y => if L.ε⁻¹ * Real.sqrt L.ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖sepWre L.ν μ T τ y‖ₑ else 0) := by
    funext τ y
    by_cases h : L.ε⁻¹ * Real.sqrt L.ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    · simp only [sepYoungCut, if_pos h]
    · simp only [if_neg h]
  rw [hcutG] at hYT
  -- the young region: the cut coefficient is the coefficient of `sepWre`
  have hYm : MeasurableSet {p : Chart | L.ν * p.1 ≤ 1} :=
    measurableSet_le (measurable_const.mul measurable_fst) measurable_const
  have hYT' : ∫⁻ p in {p : Chart | L.ν * p.1 ≤ 1}, ‖coefOf L.ε⁻¹ (sepWre L.ν μ T) p‖ₑ ^ (2 : ℝ)
      ∂(ageμ (cOf L.ν) (-3 / 2)) ≤ ENNReal.ofReal (1 / (Real.pi * L.ε⁻¹ ^ 2)) *
        IIIa.ltauLq (2 * L.ε * cOf L.ν) 2
          (fun τ y => if L.ε⁻¹ * Real.sqrt L.ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
            ‖sepWre L.ν μ T τ y‖ₑ else 0) ^ (2 : ℝ) := by
    have hcongr : ∫⁻ p in {p : Chart | L.ν * p.1 ≤ 1}, ‖coefOf L.ε⁻¹ (sepYoungCut L.ε⁻¹ L.ν μ T) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ (cOf L.ν) (-3 / 2)) = ∫⁻ p in {p : Chart | L.ν * p.1 ≤ 1},
          ‖coefOf L.ε⁻¹ (sepWre L.ν μ T) p‖ₑ ^ (2 : ℝ) ∂(ageμ (cOf L.ν) (-3 / 2)) := by
      refine setLIntegral_congr_fun hYm fun p hp => ?_
      rw [coefOf_sepYoungCut L.ε⁻¹ L.ν μ hR hν T p hp]
    rw [← hcongr]
    exact hYT
  have hX : IIIa.ltauLq (2 * L.ε * cOf L.ν) 2
      (fun τ y => if L.ε⁻¹ * Real.sqrt L.ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
        ‖sepWre L.ν μ T τ y‖ₑ else 0) < ⊤ :=
    lt_of_le_of_lt hcut (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZ)
  have hXr : (IIIa.ltauLq (2 * L.ε * cOf L.ν) 2
      (fun τ y => if L.ε⁻¹ * Real.sqrt L.ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
        ‖sepWre L.ν μ T τ y‖ₑ else 0)) ^ (2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hX.ne
  have hbody := bodyMeasure_young_le (cOf L.ν) (gRate Pl) L.ν hν
    (fun p => ‖coefOf L.ε⁻¹ (sepWre L.ν μ T) p‖ₑ ^ (2 : ℝ))
  have hfin := hbody.trans (mul_le_mul_of_nonneg_left hYT' zero_le')
  have hpt : ∀ p : Chart, ‖youngWCoef Pl K L μ (g₁ + g₂) p‖ₑ ^ (2 : ℝ) =
      {p : Chart | L.ν * p.1 ≤ 1}.indicator
        (fun p => ‖coefOf L.ε⁻¹ (sepWre L.ν μ T) p‖ₑ ^ (2 : ℝ)) p := by
    intro p
    by_cases h : L.ν * p.1 ≤ 1
    · simp [youngWCoef, hW, h, Set.indicator_apply]
    · simp [youngWCoef, hW, h, Set.indicator_apply, ENNReal.zero_rpow_of_pos]
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  rw [h2, lintegral_congr hpt, lintegral_indicator hYm]
  exact lt_of_le_of_lt hfin
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hXr))

end UnforcedLeray.Short.PartIIIb.Concrete
end
