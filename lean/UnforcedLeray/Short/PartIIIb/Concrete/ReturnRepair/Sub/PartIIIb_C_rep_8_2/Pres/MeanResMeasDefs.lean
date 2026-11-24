import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.VelYH

/-!
# Decomposition of `meanResMeas` (task `PartIII-b:C/rep/8/2/pres/6`)

Source `the November 2 reference manuscript`
lines 1205-1225, 4139-4141 (the fields are smooth), 5272-5289 (measurability implicit).

`meanE - meanERaw = coefOf ε⁻¹ (wardEXY(U,p) - wardEXY(raw,lift))`; the chart points are off the
axis, so only the off-axis (axis-zeroed) Ward difference needs to be jointly measurable on
`ℝ × Space`; measurability of `coefOf` of a jointly measurable field is `vyh_measurable_coefOf`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- Joint measurability of the (axis-zeroed) Ward difference on `ℝ × Space`: the fields `L.U`,
`L.pres` are `C^∞` (`IsExactProfile`), `rawU`, `liftP` are smooth off the axis (1205-1225, source
`Params.raw`, `train.p`), `Xmt`/`Ymt` are phase independent and measurable. -/
def WardDiffMeasAt : Prop :=
  ∀ T : LStr Pl K L,
    Measurable (fun x : ℝ × Space =>
      if x.2 ∈ axis then (0 : Space) else
        wardEXY L.ν μ L.ε⁻¹ L.U L.pres
          (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) x.1 x.2
        - wardEXY L.ν μ L.ε⁻¹ (rawU Pl L) (liftP L)
          (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) x.1 x.2)

theorem coefOf_axis_zero (R : ℝ) (hR : R ≠ 0) (F : ℝ → Space → Space) :
    coefOf R F = coefOf R (fun τ y => if y ∈ axis then 0 else F τ y) := by
  funext p
  by_cases hp : 0 < p.1
  · have hy : NearInst.chartY R p ∉ axis := by
      intro h
      have h0 : (NearInst.chartY R p) 0 = 0 := h.1
      simp [NearInst.chartY] at h0
      rcases h0 with h0 | h0
      · exact hR h0
      · exact absurd h0 (Real.sqrt_pos.2 hp).ne'
    simp [coefOf, hy]
  · have : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero_of_nonpos (not_lt.1 hp)
    simp [coefOf, this]

/-- **Reduction**: measurability of the mean-residual difference from `WardDiffMeasAt`. -/
theorem meanResMeasAt_of (h : WardDiffMeasAt Pl K L μ) : MeanResMeasAt Pl K L μ := by
  intro T
  have hR : L.ε⁻¹ ≠ 0 := (inv_pos.2 L.ε_pos).ne'
  have e : meanE Pl K L μ T - meanERaw Pl K L μ T = coefOf L.ε⁻¹ (fun τ y =>
      if y ∈ axis then (0 : Space) else
        wardEXY L.ν μ L.ε⁻¹ L.U L.pres
          (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) τ y
        - wardEXY L.ν μ L.ε⁻¹ (rawU Pl L) (liftP L)
          (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) τ y) := by
    unfold meanE meanERaw
    rw [coefOf_sub_eq, coefOf_axis_zero L.ε⁻¹ hR]
  rw [e]
  exact (vyh_measurable_coefOf L.ε⁻¹ (h T)).aestronglyMeasurable

/-- Measurability of the Newton field `X^mt` of a stress `T` (source 4776-4791, 5380-5382): `newtonV`
is an integral of the smooth kernel `∂³N` against `σ_M`, and the null set where the representative
`thinRep T` differs from a measurable one does not depend on the parameter `x`, so `Xmt` agrees
everywhere with the same expression for a measurable representative; `streamCut` adds the
measurable `chiYr`, its derivative and the ray integral `streamPsi`. -/
def XmtMeasAt : Prop :=
  IsStreamCutoff K.χy → ∀ T : LStr Pl K L,
    Measurable (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))

/-- Regularity of the raw coefficient and the lifted pressure (source 1205-1225, 5272-5282):
jointly measurable on `ℝ × Space` and `C²` in `y` off the axis. -/
def RawLiftRegularAt : Prop :=
  Measurable (fun x : ℝ × Space => rawU Pl L x.1 x.2) ∧
  Measurable (fun x : ℝ × Space => liftP L x.1 x.2) ∧
  (∀ τ (y : Space), y ∉ axis → ContDiffAt ℝ 2 (rawU Pl L τ) y ∧ ContDiffAt ℝ 2 (liftP L τ) y) ∧
  (∀ τ (y : Space), y ∉ axis → ∀ j : Fin 3, ContDiffAt ℝ 1 (fun y' => physPd (rawU Pl L τ) j y') y ∧
    ContDiffAt ℝ 1 (fun y' => fderiv ℝ (liftP L τ) y' (coordinateVector j)) y)

end Regime

/-- Along the sequence. -/
theorem meanResMeas_of (D : SeqData)
    (h : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, WardDiffMeasAt D.Pl D.K (D.level n) (D.mu n z)) :
    D.MeanResMeas :=
  h.mono fun _ hn z hz => meanResMeasAt_of _ _ _ _ (hn z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
