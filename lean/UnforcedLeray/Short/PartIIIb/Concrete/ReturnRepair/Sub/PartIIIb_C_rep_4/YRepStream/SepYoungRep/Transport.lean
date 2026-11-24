import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T7

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/2`: the change of variables `ChartYoungTransport`

Source `the November 2 reference manuscript` 2666-2668, 2683, 5143.

The proof is the ring-chart change of variables already proved in `Lib/AxisymmetricB/Lift.lean`
(`lintegral_Nv_rpow`, exponent `q = 2` gives the chart exponent `q/2 - 5/2 = -3/2` of `ageμ`),
applied to the young cut `b = 1_{ν s ≤ 1} coefOf R F`.  Off the axis, the physical lift of
`coefOf R F` is `F` (`velPhysCoefOf_of`), and the young condition `ν age ≤ 1` is the condition
`R√ν ≤ ϱ` on the physical point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Measurability of the chart coefficient of a jointly measurable field. -/
theorem coefOf_measurable_tr (R : ℝ) (F : ℝ → Space → Space)
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

/-- A `c`-periodic-in-`ξ` profile is its own periodic extension. -/
theorem perExt_eq_self_of {c : ℝ} (hc : 0 < c) {b : ℝ × (ℝ × ℝ) → Merid}
    (hb : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) : perExt c b = b := by
  funext p
  obtain ⟨s, ξ, η⟩ := p
  have hP : Function.Periodic (fun x => b (s, (x, η))) c := fun x => hb s x η
  have hk := hP.int_mul (-⌊(ξ + c / 2) / c⌋)
  have hcell : cellRep c ξ = ξ + ((-⌊(ξ + c / 2) / c⌋ : ℤ) : ℝ) * c := by
    unfold cellRep
    push_cast
    ring
  show b (s, (cellRep c ξ, η)) = b (s, (ξ, η))
  rw [hcell]
  exact hk ξ

/-- The chart coefficient of a `2c/R`-periodic field is `c`-periodic in `ξ`. -/
theorem coefOf_periodic_xi {R c : ℝ} (hR : 0 < R) (F : ℝ → Space → Space)
    (hper : ∀ τ y, F (τ + 2 * c / R) y = F τ y) (s ξ η : ℝ) :
    coefOf R F (s, (ξ + c, η)) = coefOf R F (s, (ξ, η)) := by
  have hτ : NearInst.chartTau R (s, (ξ + c, η)) = NearInst.chartTau R (s, (ξ, η)) + 2 * c / R := by
    unfold NearInst.chartTau
    field_simp
    ring
  have hY : NearInst.chartY R (s, (ξ + c, η)) = NearInst.chartY R (s, (ξ, η)) := rfl
  unfold coefOf
  rw [hτ, hY, hper]

/-- The young condition `ν · age ≤ 1` in physical variables: `R√ν ≤ ϱ`. -/
theorem young_iff_phys {R ν : ℝ} (hR : 0 < R) (hν : 0 < ν) {y : Space} (hy : y ∉ axis) :
    ν * age R y ≤ 1 ↔ R * Real.sqrt ν ≤ ϱ y := by
  have hϱ : 0 < ϱ y := ϱ_pos hy
  have hsq : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have hs0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
  have hage : ν * age R y = ν * R ^ 2 / ϱ y ^ 2 := by
    unfold age
    ring
  rw [hage, div_le_one (by positivity)]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have h1 : ϱ y ^ 2 < (R * Real.sqrt ν) ^ 2 := by
      have := mul_lt_mul'' hcon hcon hϱ.le hϱ.le
      nlinarith
    nlinarith
  · intro h
    have h1 : (R * Real.sqrt ν) ^ 2 ≤ ϱ y ^ 2 := by
      have := mul_le_mul h h (by positivity) hϱ.le
      nlinarith
    nlinarith

/-- Off the axis the physical lift of `coefOf R F` is `F` (`velPhysCoefOf_of`). -/
theorem Nv_coefOf_eq {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (F : ℝ → Space → Space)
    (hF : AxiNoSwirl F) (hper : ∀ τ y, F (τ + 2 * c / R) y = F τ y) (τ : ℝ) {y : Space}
    (hy : y ∉ axis) : Nv R (coefOf R F) τ y = F τ y := by
  have h := velPhysCoefOf_of R c hR hc F hF hper (τ, y) hy
  have hb : ∀ s ξ η, coefOf R F (s, (ξ + c, η)) = coefOf R F (s, (ξ, η)) :=
    fun s ξ η => coefOf_periodic_xi hR F hper s ξ η
  unfold velPhys at h
  simp only at h
  rw [perExt_eq_self_of hc hb] at h
  ext i
  have := congrArg (fun v => v i) h
  simp only [B0412.realC_apply] at this
  exact Complex.ofReal_injective this

/-- Pointwise off-axis identity for the young cut. -/
theorem Nv_young_eq {R c ν : ℝ} (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (F : ℝ → Space → Space)
    (hF : AxiNoSwirl F) (hper : ∀ τ y, F (τ + 2 * c / R) y = F τ y) (τ : ℝ) {y : Space}
    (hy : y ∉ axis) :
    ‖Nv R (fun p : ℝ × (ℝ × ℝ) => if ν * p.1 ≤ 1 then coefOf R F p else 0) τ y‖ₑ =
      if R * Real.sqrt ν ≤ ϱ y then ‖F τ y‖ₑ else 0 := by
  have hNv : Nv R (fun p : ℝ × (ℝ × ℝ) => if ν * p.1 ≤ 1 then coefOf R F p else 0) τ y =
      if R * Real.sqrt ν ≤ ϱ y then F τ y else 0 := by
    unfold Nv
    have hc' : (chart R τ y).1 = age R y := rfl
    by_cases h : R * Real.sqrt ν ≤ ϱ y
    · have hc2 : ν * age R y ≤ 1 := (young_iff_phys hR hν hy).2 h
      simp only [h, if_true, hc', if_pos hc2]
      rw [← Nv_coefOf_eq hR hc F hF hper τ hy]
      rfl
    · have hc2 : ¬ ν * age R y ≤ 1 := fun h' => h ((young_iff_phys hR hν hy).1 h')
      have hc3 : ¬ ν * (chart R τ y).1 ≤ 1 := by rw [hc']; exact hc2
      simp only [h, if_false, if_neg hc3, map_zero, smul_zero]
  rw [hNv]
  split_ifs <;> simp

/-- **`ChartYoungTransport`** (source 2666-2668, 2683, 5143): the change of variables. -/
theorem chartYoungTransport (R c ν : ℝ) (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) :
    ChartYoungTransport R c ν := by
  intro F hFm hax hper
  set b : Chart → Merid := fun p => if ν * p.1 ≤ 1 then coefOf R F p else 0 with hbdef
  have hcm : Measurable (coefOf R F) := coefOf_measurable_tr R F hFm
  have hbm : Measurable b :=
    Measurable.ite (measurableSet_le (measurable_const.mul measurable_fst) measurable_const)
      hcm measurable_const
  have hbper : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η)) := by
    intro s ξ η
    simp only [hbdef]
    rw [coefOf_periodic_xi hR F hper s ξ η]
  have hS : MeasurableSet {p : Chart | ν * p.1 ≤ 1} :=
    measurableSet_le (measurable_const.mul measurable_fst) measurable_const
  have hL : ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R F p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
      = ∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) := by
    rw [← lintegral_indicator hS]
    congr 1
    funext p
    by_cases h : ν * p.1 ≤ 1
    · simp [hbdef, h, Set.indicator]
    · simp [hbdef, h, Set.indicator]
  have hLN := lintegral_Nv_rpow (R := R) (c := c) (P := 2 * c / R) (q := 2) hR hc rfl
    (by norm_num) hbm hbper
  have e : (2 : ℝ) / 2 - 5 / 2 = -3 / 2 := by norm_num
  rw [e] at hLN
  -- inner integrals agree with the young-region integrand
  have hin : ∀ τ : ℝ, ∫⁻ y, ‖Nv R b τ y‖ₑ ^ (2 : ℝ) =
      ∫⁻ y, (if R * Real.sqrt ν ≤ ϱ y then ‖F τ y‖ₑ else 0) ^ (2 : ℝ) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_not_mem_axis] with y hy
    rw [Nv_young_eq hR hc hν F hax hper τ hy]
  have hpos : (ENNReal.ofReal (Real.pi * R ^ 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have htop : (ENNReal.ofReal (Real.pi * R ^ 2)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hI : ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ y, ‖Nv R b τ y‖ₑ ^ (2 : ℝ) =
      ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ y, (if R * Real.sqrt ν ≤ ϱ y then ‖F τ y‖ₑ else 0) ^ (2 : ℝ) :=
    setLIntegral_congr_fun measurableSet_Ioc fun τ _ => hin τ
  rw [hI] at hLN
  have hLN' : ∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) =
      (ENNReal.ofReal (Real.pi * R ^ 2))⁻¹ * ((ENNReal.ofReal (2 * c / R))⁻¹ *
        ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ y, (if R * Real.sqrt ν ≤ ϱ y then ‖F τ y‖ₑ else 0) ^ (2 : ℝ)) := by
    calc ∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        = (ENNReal.ofReal (Real.pi * R ^ 2))⁻¹ *
            (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
      _ = _ := by rw [← hLN]
  -- the right-hand side
  have hR' : ∀ f : ℝ → Space → ℝ≥0∞, (IIIa.ltauLq (2 * c / R) 2 f) ^ (2 : ℝ) =
      (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ y, f τ y ^ (2 : ℝ) := by
    intro f
    unfold IIIa.ltauLq
    rw [← ENNReal.rpow_mul]
    norm_num
  change _ ≤ ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * (IIIa.ltauLq (2 * c / R) 2
    (fun τ y => if R * Real.sqrt ν ≤ ϱ y then ‖F τ y‖ₑ else 0)) ^ (2 : ℝ)
  rw [hL, hR', hLN', one_div, ENNReal.ofReal_inv_of_pos (by positivity)]

end UnforcedLeray.Short.PartIIIb.Concrete
end
