import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_1.Generic

/-!
# `PartIII-b:IIIb-D2/3/2/12/3` (`StrPairCont`): decomposition

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

`StrPairCont` is the continuity on `StrG` of `T ↦ ⟨𝒩_T(T₁+T₂), ∇Φ⟩` (phase test `Φ`).  Facts used:

* `stressPairAE` (proved, `NearInst/Link/Pins/Proofs/StressPairAE.lean`): the pairing sees only the
  `ageμ c (-1/2)`-class of the chart tensor.
* Weights.  For `mZ < 0` the weight `W = ⟨η/√(1+s)⟩^{mZ}` is *not* bounded below on the chart, but on the
  support of `∇Φ` (`|y| ≤ R₀`) one has `|η|/√(1+s) = R|y₃|/√(ϱ²+R²) ≤ |y₃| ≤ R₀`, so `W ≥ (1+R₀²)^{mZ/2}`
  there (`StrRegion`).  The gain `g⁻¹ ≥ e^{-|γ|/ν}` is bounded below everywhere.
* `ρb ≤ 0`: `htRhoMeasure c ρb = 0`, the second factor of `StrG` is the zero space, and the coercion of
  its zero element is a *fixed junk function* `j₀`; the statement is then still true (the value is
  constant `0` if the integrand of `j₀` is not integrable, otherwise it is affine), see
  `StrPairContNonpos`.  It cannot be handled by a bound `‖val T‖ ≤ C‖T‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- The value `T ↦ ⟨𝒩_T(T₁+T₂), ∇Φ⟩` of `StrPairCont`. -/
def strPairVal (c mZ ρb γ ν ε : ℝ) (Φ : ℝ × Space → CVec3) (T : StrG c mZ ρb γ ν) : ℂ :=
  stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum T)) Φ

/-- The chart region `{|η| ≤ Y √(1+s)}` containing the chart image of `{|y₃| ≤ Y}` (source 2696:
there `W = ⟨η/√(1+s)⟩^{m_Z}` is bounded above and below). -/
def StrRegion (Y : ℝ) : Set Chart := {p | |p.2.2| ≤ Y * Real.sqrt (1 + p.1)}

/-- **`.../12/3/1`** (source 2683, 2698-2700, 4284-4286): the stress lift against a phase test is
bounded by the `L²(s^{-1/2}dς)`-norm of the chart tensor on the region `StrRegion Y` (change of
variables `Axi.phaseAvg_ringChart` with `G = 1_{StrRegion Y}·s²‖nsSym g‖²`, `s² · s^{-5/2} = s^{-1/2}`,
Cauchy-Schwarz on the bounded support of `∇Φ`, `|cylFrame| ≤ 1`). -/
def StrChartBound : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
    ∃ Y K : ℝ, 0 ≤ K ∧ ∀ g : Chart → Ten3, Measurable g →
      (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) < ⊤ →
      Integrable (fun x : ℝ × Space => ∑ i : Fin 3, ∑ j : Fin 3,
          ((strPhys ε⁻¹ c g x i j : ℝ) : ℂ) * dy j Φ x i) (volume.restrict (phaseCell (2 * ε * c))) ∧
      ‖stressPair (2 * ε * c) (strPhys ε⁻¹ c g) Φ‖ ≤
        K * ((∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ)).toReal

/-- **`.../12/3/2`** (source 2696-2700, 5117): comparison of the gain-weighted stress measures with
`ageμ c (-1/2)`: `ageμ ≪ g⁻²W² ageμ` (positive densities); on `StrRegion Y`,
`g⁻²W² ≥ e^{-2|γ|/ν}·min(1, (1+Y²)^{mZ/2})² > 0`; for `ρb > 0` the density `g⁻²ρb⁻¹ ≥ ρb⁻¹ e^{-2|γ|/ν}`
(`ageμ_le_body` in `Generic.lean` is the analogue for the body measure). -/
def StrMeasureCmp : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < ν → 0 < ρb → ∀ Y : ℝ, ∃ K : ℝ≥0∞, K ≠ ∞ ∧ K ≠ 0 ∧
    (ageμ c (-1 / 2)).restrict (StrRegion Y) ≤ K • (gainZ1Measure c mZ γ ν).restrict (StrRegion Y) ∧
    ageμ c (-1 / 2) ≤ K • gainHTMeasure c ρb γ ν ∧
    ageμ c (-1 / 2) ≪ gainZ1Measure c mZ γ ν

/-- **`.../12/3/3`**: the value is real-linear in `T ∈ StrG` (`ρb > 0`).  From `stressPairAE`
(a.e. classes), `Lp.coeFn_add/smul`, `ageμ ≪ gain measures` (`StrMeasureCmp`), pointwise linearity of
`cartLift`/`nsSym`, and integrability of the stress integrand (`StrChartBound`, finite region norm from
`StrMeasureCmp`) to split the phase integral (`pairF_add_right_of_integrable`). -/
def StrPairLin : Prop :=
  ∀ (c mZ ρb γ ν ε : ℝ), 0 < c → 0 < ν → 0 < ε → 0 < ρb →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      (∀ T T' : StrG c mZ ρb γ ν,
        strPairVal c mZ ρb γ ν ε Φ (T + T') =
          strPairVal c mZ ρb γ ν ε Φ T + strPairVal c mZ ρb γ ν ε Φ T') ∧
      ∀ (a : ℝ) (T : StrG c mZ ρb γ ν),
        strPairVal c mZ ρb γ ν ε Φ (a • T) = a • strPairVal c mZ ρb γ ν ε Φ T

/-- **`.../12/3/4`**: the value is bounded by `C ‖T‖` (`ρb > 0`), from `StrChartBound`,
`StrMeasureCmp` (`eLpNorm_le_of_measure_le_smul`), Minkowski on the restricted measure for
`strSum T = T₁ + T₂`, and `‖T‖ = ‖T₁‖ + ‖T₂‖` in `WithLp 1`. -/
def StrPairBd : Prop :=
  ∀ (c mZ ρb γ ν ε : ℝ), 0 < c → 0 < ν → 0 < ε → 0 < ρb →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      ∃ C : ℝ, ∀ T : StrG c mZ ρb γ ν, ‖strPairVal c mZ ρb γ ν ε Φ T‖ ≤ C * ‖T‖

/-- **`.../12/3/5`** (junk-representative case): for `ρb ≤ 0` the measure `htRhoMeasure c ρb` is zero, so
`T.snd = 0` and `strSum T = coeFn T.fst + j₀`, `j₀ = ⇑(0 : Lp _ 2 (gainHTMeasure ..))` a fixed function.
Either the integrand of `strPhys j₀ · ∇Φ` is integrable on the phase cell (then the value is the
affine map `T₁ ↦ val(T₁) + val(j₀)` by `StrChartBound`, `stressPairAE`, hence continuous by the `Z₁` bound
of `StrMeasureCmp`-type), or it is not and the integrand of the sum is not integrable either, so the
value is the constant `0` (Bochner integral of a non-integrable function). -/
def StrPairContNonpos : Prop :=
  ∀ (c mZ ρb γ ν ε : ℝ), ρb ≤ 0 → StrPairCont c mZ ρb γ ν ε

/-- **`StrPairCont` from the five facts.** -/
theorem strPairCont_of (h1 : StrPairLin) (h2 : StrPairBd) (h3 : StrPairContNonpos)
    (c mZ ρb γ ν ε : ℝ) : StrPairCont c mZ ρb γ ν ε := by
  by_cases hρ : ρb ≤ 0
  · exact h3 c mZ ρb γ ν ε hρ
  · push_neg at hρ
    intro hc hν hε Φ hΦ
    obtain ⟨hadd, hsmul⟩ := h1 c mZ ρb γ ν ε hc hν hε hρ Φ hΦ
    obtain ⟨C, hC⟩ := h2 c mZ ρb γ ν ε hc hν hε hρ Φ hΦ
    let L : StrG c mZ ρb γ ν →ₗ[ℝ] ℂ :=
      { toFun := strPairVal c mZ ρb γ ν ε Φ
        map_add' := hadd
        map_smul' := fun a T => by
          rw [RingHom.id_apply]
          exact hsmul a T }
    have hbd : ∀ T, ‖L T‖ ≤ max C 0 * ‖T‖ := fun T =>
      (hC T).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    exact (LinearMap.mkContinuous L (max C 0) hbd).continuous

end UnforcedLeray.Short.PartIIIb.Concrete
