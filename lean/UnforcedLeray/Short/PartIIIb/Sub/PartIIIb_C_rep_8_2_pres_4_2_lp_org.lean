import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2

/-!
# Decomposition of `CoefChgLp` (organizer task `PartIII-b:C/rep/8/2/pres/4/2/lp/org`)

Source `the November 2 reference manuscript`
5287-5289, 2669, 2681-2688, 2697-2713, 5134-5139.  `U - V = r_b` (the exact split,
2664-2713; the entrance part `V - U_raw` is not in `Y_{11/4}`, 2346-2347, and is handled by `EntJetAt`); the `Y_{11/4}` norm of the change density is read in the ring chart
(`ChartPhaseLIntegral`, `phaseAvg_ringChart`), and bounded by the repair part (`RepairDerivBound`,
`ExactSplitII.energy`).

`coefChgLp_of` assembles the four source pieces below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- The entrance field `E_εα = Σᵢ αᵢ Eᵢ` of the inlet columns of `p` (source 2664-2672). -/
def entrOf (p : Params) (α : Fin 2 → ℝ) (τ : ℝ) : UnforcedLeray.SpatialField :=
  fun y => ∑ i : Fin 2, α i • p.inlet i τ y

/-- A scalar density `F(τ, y)` is read faithfully in the ring chart at ring parameter `R` and
phase width `c`: its chart reading is a.e.-measurable for the chart measure
`s^{-5/2} ds dq/c dη` (which lives on `s > 0`, off the axis), and `F(τ, y) = F(chartOf R c y τ)`
almost everywhere (axisymmetry about the axis, `NearInst.chartOf`, source 2670-2674, 2681-2688). -/
def AxiChartForm (R c : ℝ) (F : ℝ → Space → ℝ) : Prop :=
  AEMeasurable (ringRead R F) (ageμ c (-5 / 2)) ∧
    ∀ᵐ x : ℝ × Space ∂volume, F x.1 x.2 = ringRead R F (NearInst.chartOf R c x.2 x.1)

/-- **Piece 1 (ring-chart form of the phase norm; source 2681-2688, `ChartPhaseLIntegral`)**:
for a density read faithfully in the chart, the chart `L^{11/4}` norm over `ringPhysμ` equals the
phase-normalized norm `phaseLr` over `(0, 2εc] × ℝ³`. -/
def ChartFormPhaseLr : Prop :=
  ∀ (ε c : ℝ), 0 < ε → 0 < c → ∀ F : ℝ → Space → ℝ, AxiChartForm ε⁻¹ c F →
    eLpNorm (ringRead ε⁻¹ F) (11 / 4) (ringPhysμ ε⁻¹ c) = phaseLr (2 * ε * c) (11 / 4) (fun x => F x.1 x.2)

/-- **Piece 2**: the density of `r_b` and its two derivatives is read faithfully in the chart
(`r_b = corr z` is axisymmetric without swirl, smooth off the axis). -/
def RbChartForm (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, AxiChartForm (D.level n).ε⁻¹ (cOf (D.level n).ν)
    fun τ y => coefChgDens (D.rb n τ) 0 y

/-- **Piece 4 (the repair part; source 5134-5139, `RepairDerivBound`, `ExactSplitII.energy`)**:
`Y_{11/4}` bound of `r_b` and its two derivatives by `C ν⁻ᵏ ρ`, `ρ = ε^{3/11}e^{m₀/ν}`. -/
def RbYBound (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    phaseLr (2 * (D.level n).ε * cOf (D.level n).ν) (11 / 4)
        (fun x => coefChgDens (D.rb n x.1) 0 x.2) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n))

/-- **Piece 6 (the pointwise identification, source 5287-5289)**: `U = V + r_b` (`ReturnLevel.U`),
so at chart points, where all fields are smooth (off the axis), the change density of `(U, V)` is
that of `r_b`: `U - V = r_b` and the first and second derivatives are linear. -/
def CoefChgPointwise (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ p : Chart, 0 < p.1 →
      coefChgDens ((D.level n).U (NearInst.chartTau (D.level n).ε⁻¹ p))
          ((D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ p))
          (NearInst.chartY (D.level n).ε⁻¹ p) ≤
        coefChgDens (D.rb n (NearInst.chartTau (D.level n).ε⁻¹ p)) 0
            (NearInst.chartY (D.level n).ε⁻¹ p)

theorem coefChgLp_of (D : SeqData)
    (h1 : ChartFormPhaseLr) (h2 : RbChartForm D) (h4 : RbYBound D)
    (h6 : CoefChgPointwise D) : CoefChgLp D := by
  obtain ⟨C4, k4, hA⟩ := h4
  refine ⟨C4, k4, ?_⟩
  filter_upwards [h2, hA, h6] with n hF2 hA hP
  set L := D.level n with hL
  have hεpos : 0 < L.ε := L.ε_pos
  have hcpos : 0 < cOf L.ν := cOf_pos L.ν_pos
  set dRb : ℝ → Space → ℝ := fun τ y => coefChgDens (D.rb n τ) 0 y with hdRb
  set dU : ℝ → Space → ℝ := fun τ y => coefChgDens (L.U τ) (L.V τ) y with hdU
  have e1 : eLpNorm (ringRead L.ε⁻¹ dRb) (11 / 4) (ringPhysμ L.ε⁻¹ (cOf L.ν)) =
      phaseLr (2 * L.ε * cOf L.ν) (11 / 4) (fun x => dRb x.1 x.2) :=
    h1 L.ε (cOf L.ν) hεpos hcpos dRb hF2
  have hae : ∀ᵐ p ∂(ringPhysμ L.ε⁻¹ (cOf L.ν)), ‖ringRead L.ε⁻¹ dU p‖ₑ ≤
      ‖ringRead L.ε⁻¹ dRb p‖ₑ := by
    unfold ringPhysμ
    refine Measure.ae_smul_measure ?_ _
    have hpos : ∀ᵐ p ∂(ageμ (cOf L.ν) (-5 / 2)), 0 < p.1 := by
      have h0 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
          fun s => ENNReal.ofReal (s ^ (-5 / 2 : ℝ))), 0 < s :=
        (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
      exact Measure.quasiMeasurePreserving_fst.ae h0
    filter_upwards [hpos] with p hp
    have h0 : 0 ≤ coefChgDens (L.U (NearInst.chartTau L.ε⁻¹ p)) (L.V (NearInst.chartTau L.ε⁻¹ p))
        (NearInst.chartY L.ε⁻¹ p) := coefChgDens_nonneg _ _ _
    have h1' := coefChgDens_nonneg (D.rb n (NearInst.chartTau L.ε⁻¹ p)) 0 (NearInst.chartY L.ε⁻¹ p)
    simp only [ringRead, hdU, hdRb, Real.enorm_eq_ofReal h0, Real.enorm_eq_ofReal h1']
    exact ENNReal.ofReal_le_ofReal (hP p hp)
  calc eLpNorm (ringRead L.ε⁻¹ dU) (11 / 4) (ringPhysμ L.ε⁻¹ (cOf L.ν))
      ≤ eLpNorm (ringRead L.ε⁻¹ dRb) (11 / 4) (ringPhysμ L.ε⁻¹ (cOf L.ν)) :=
        eLpNorm_mono_enorm_ae (p := (11 / 4 : ℝ≥0∞)) hae
    _ = phaseLr (2 * L.ε * cOf L.ν) (11 / 4) (fun x => dRb x.1 x.2) := e1
    _ ≤ _ := hA

end UnforcedLeray.Short.PartIIIb.Concrete
