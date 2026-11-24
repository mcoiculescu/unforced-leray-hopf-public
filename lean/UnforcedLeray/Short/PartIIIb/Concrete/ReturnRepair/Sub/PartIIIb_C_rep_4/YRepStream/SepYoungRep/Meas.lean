import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L2_JointMeas

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/1`: measurability of the young cut field

Source `the November 2 reference manuscript` 3611-3621.

The separated response `sepWre` is jointly measurable in `(τ, y)`: its `λ`-integral and
`z`-integral are parametric Bochner integrals of a jointly measurable integrand.  The heat-Leray
derivative is jointly measurable on `t > 0` by `IIIa.heatLerayKJointMeas`.  Composing with the
measurable chart maps `chartTau`, `chartY` and the age measure gives `youngWCoef` measurable.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `z`-integrand of `IIIa.sepW` at the phase `τ`, receiver `y` and `λ = l`, with the kernel
indicator `0 < ν(1-l²)` made explicit (it holds for `l ∈ (0,1)`). -/
def sepZInt (ν : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (τ : ℝ) (y : Space)
    (l : ℝ) : ℂ :=
  ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
    ((if 0 < ν * (1 - l ^ 2) then
        fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
          (coordinateVector k) else 0 : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)

/-- Joint measurability of `(t, x) ↦ ∂_{e_k} K_t(x)` on `t > 0`, from `heatLerayKJointMeas`. -/
theorem heatDeriv_stronglyMeasurable (i j k : Fin 3) :
    StronglyMeasurable (fun q : ℝ × Space =>
      if 0 < q.1 then fderiv ℝ (fun x => IIIa.heatLerayK q.1 i j x) q.2 (coordinateVector k)
      else 0) := by
  have h := UnforcedLeray.Short.IIIa.heatLerayKJointMeas i j 1
  have hc : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Space) ℝ =>
      A (fun _ => coordinateVector k)) := continuous_eval_const _
  have h2 := hc.comp_stronglyMeasurable h
  convert h2 using 1
  funext q
  by_cases hq : 0 < q.1
  · simp only [hq, ite_true, iteratedFDeriv_one_apply]
  · simp [hq]

/-- Measurability of the kernel factor, as a complex function of `((τ,y),l),z`. -/
theorem sepKern_measurable (ν : ℝ) (i j k : Fin 3) :
    Measurable (fun p : ((ℝ × Space) × ℝ) × Space =>
      ((if 0 < ν * (1 - p.1.2 ^ 2) then
          fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1.2 ^ 2)) i j x)
            (p.1.1.2 - p.1.2 • p.2) (coordinateVector k) else 0 : ℝ) : ℂ)) := by
  have hmap : Measurable (fun p : ((ℝ × Space) × ℝ) × Space =>
      ((ν * (1 - p.1.2 ^ 2), p.1.1.2 - p.1.2 • p.2) : ℝ × Space)) := by
    fun_prop
  have h := (heatDeriv_stronglyMeasurable i j k).comp_measurable hmap
  have h' : Measurable (fun p : ((ℝ × Space) × ℝ) × Space =>
      (if 0 < ν * (1 - p.1.2 ^ 2) then
          fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1.2 ^ 2)) i j x)
            (p.1.1.2 - p.1.2 • p.2) (coordinateVector k) else 0 : ℝ)) := h.measurable
  exact Complex.measurable_ofReal.comp h'

/-- Measurability of the full `λ`-integrand's `z`-summand in `((τ,y),l),z`. -/
theorem sepSummand_measurable (ν : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) (i : Fin 3) :
    Measurable (fun p : ((ℝ × Space) × ℝ) × Space =>
      ∑ j : Fin 3, ∑ k : Fin 3,
        ((if 0 < ν * (1 - p.1.2 ^ 2) then
            fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1.2 ^ 2)) i j x)
              (p.1.1.2 - p.1.2 • p.2) (coordinateVector k) else 0 : ℝ) : ℂ) *
          ((T (p.1.1.1 + 2 * Real.log p.1.2) p.2 j k : ℝ) : ℂ)) := by
  have hφ : Measurable (fun p : ((ℝ × Space) × ℝ) × Space =>
      (p.1.1.1 + 2 * Real.log p.1.2, p.2)) := by
    fun_prop
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  exact (sepKern_measurable ν i j k).mul (Complex.measurable_ofReal.comp ((hT j k).comp hφ))

/-- The `z`-integral `sepZInt` is jointly measurable in `((τ,y),l)`. -/
theorem sepZInt_measurable (ν : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) (i : Fin 3) :
    StronglyMeasurable (fun x : (ℝ × Space) × ℝ => sepZInt ν T i x.1.1 x.1.2 x.2) := by
  have h := (sepSummand_measurable ν T hT i).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure Space))
  exact h

/-- The `λ`-integral in `sepW`, jointly measurable in `(τ,y)`. -/
theorem sepL_stronglyMeasurable (ν : ℝ) (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) (i : Fin 3) :
    StronglyMeasurable (fun q : ℝ × Space =>
      ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * sepZInt ν T i q.1 q.2 l) := by
  have hpow : Measurable (fun x : (ℝ × Space) × ℝ => (x.2 : ℂ) ^ (2 * (μ : ℂ) + 2)) :=
    (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  have hf : StronglyMeasurable (fun x : (ℝ × Space) × ℝ =>
      (x.2 : ℂ) ^ (2 * (μ : ℂ) + 2) * sepZInt ν T i x.1.1 x.1.2 x.2) :=
    hpow.stronglyMeasurable.mul (sepZInt_measurable ν T hT i)
  exact hf.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))

/-- `IIIa.sepW` rewritten through `sepZInt` (the kernel indicator is true on `(0,1)` when `ν > 0`). -/
theorem sepW_eq_sepZInt (ν : ℝ) (hν : 0 < ν) (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) (p : ℝ × Space) :
    IIIa.sepW ν (μ : ℂ) T p.2 p.1 i =
      -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * sepZInt ν T i p.1 p.2 l := by
  simp only [IIIa.sepW, sepZInt]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo ?_
  intro l hl
  have hpos : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  simp only [hpos, ite_true]

/-- `sepWre` is jointly measurable in `(τ, y)`. -/
theorem sepWre_measurable (ν μ : ℝ) (hν : 0 < ν) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) :
    Measurable (fun q : ℝ × Space => sepWre ν μ T q.1 q.2) := by
  have hc : ∀ i : Fin 3, Measurable (fun q : ℝ × Space => (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i).re) := by
    intro i
    have h : Measurable (fun q : ℝ × Space =>
        -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * sepZInt ν T i q.1 q.2 l) :=
      (sepL_stronglyMeasurable ν μ T hT i).measurable.const_mul _
    have h2 : Measurable (fun q : ℝ × Space => IIIa.sepW ν (μ : ℂ) T q.2 q.1 i) := by
      have heq : (fun q : ℝ × Space => IIIa.sepW ν (μ : ℂ) T q.2 q.1 i) =
          (fun q : ℝ × Space =>
            -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * sepZInt ν T i q.1 q.2 l) := by
        funext q
        exact sepW_eq_sepZInt ν hν μ T i q
      rw [heq]
      exact h
    exact Complex.measurable_re.comp h2
  have hv : Measurable (fun q : ℝ × Space => fun i : Fin 3 => (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i).re) :=
    measurable_pi_lambda _ fun i => hc i
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hv

/-- `coefOf` is measurable on the chart when the field is jointly measurable. -/
theorem coefOf_measurable_of (R : ℝ) (F : ℝ → Space → Space)
    (hF : Measurable (fun q : ℝ × Space => F q.1 q.2)) : Measurable (coefOf R F) := by
  have hτ : Measurable (NearInst.chartTau R) := by
    unfold NearInst.chartTau
    fun_prop
  have hy : Measurable (NearInst.chartY R) := by
    unfold NearInst.chartY
    have : Measurable fun p : Chart => (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
      refine measurable_pi_lambda _ fun i => ?_
      fin_cases i <;> simp <;> fun_prop
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this
  have hq : Measurable (fun p : Chart => ((NearInst.chartTau R p, NearInst.chartY R p) : ℝ × Space)) :=
    hτ.prodMk hy
  have hG : Measurable (fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p)) :=
    hF.comp hq
  have hc0 : Measurable (fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p) 0) :=
    (EuclideanSpace.proj (0 : Fin 3)).continuous.measurable.comp hG
  have hc2 : Measurable (fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p) 2) :=
    (EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp hG
  have hv : Measurable (fun p : Chart =>
      (![F (NearInst.chartTau R p) (NearInst.chartY R p) 0,
        F (NearInst.chartTau R p) (NearInst.chartY R p) 2] : Fin 2 → ℝ)) :=
    measurable_pi_lambda _ fun i => by fin_cases i <;> simp <;> assumption
  have hvec : Measurable (fun p : Chart =>
      (!₂[F (NearInst.chartTau R p) (NearInst.chartY R p) 0,
        F (NearInst.chartTau R p) (NearInst.chartY R p) 2] : Merid)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp hv
  have hs : Measurable (fun p : Chart => (Real.sqrt p.1)⁻¹) :=
    (Real.continuous_sqrt.measurable.comp measurable_fst).inv
  unfold coefOf
  exact hs.smul hvec

/-- **`PartIII-b:C/rep/4/4/1/org/1/1/1`**: the young cut field `-W_μ` is a.e. strongly
measurable on the chart body measure. -/
theorem sepRepYoungAEMeas (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (g : Chart → Ten3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ y, wardW L.ν μ L.ε⁻¹ (cOf L.ν) g τ y = sepWre L.ν μ T τ y)
    (hS : IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T) :
    AEStronglyMeasurable (youngWCoef Pl K L μ g) (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) := by
  have hfun : wardW L.ν μ L.ε⁻¹ (cOf L.ν) g = sepWre L.ν μ T :=
    funext fun τ => funext fun y => hT τ y
  have hyw : youngWCoef Pl K L μ g = fun p : Chart =>
      if L.ν * p.1 ≤ 1 then -coefOf L.ε⁻¹ (sepWre L.ν μ T) p else 0 := by
    funext p
    simp only [youngWCoef, hfun]
  rw [hyw]
  apply Measurable.aestronglyMeasurable
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (measurable_const.mul measurable_fst) measurable_const
  · exact (coefOf_measurable_of L.ε⁻¹ (sepWre L.ν μ T)
      (sepWre_measurable L.ν μ L.ν_pos T fun i j => (hS.measurable i j))).neg

end UnforcedLeray.Short.PartIIIb.Concrete
end
