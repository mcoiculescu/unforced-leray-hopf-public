import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg

/-!
# The entrance coefficient change against the mean jet (organizer task
`PartIII-b:C/rep/8/2/pres/4/org2`)

Source `the November 2 reference manuscript`
2346-2347, 2353-2356, 2389-2390, 2519-2520, 5285-5289, 5402-5404, 5440-5446, 5470-5476.

`V - U_raw = E_εα_bg` is *not* in `Y_{11/4}` (its nonzero inlet is not in `Y_p`), so the entrance
coefficient change cannot be bounded in `Y_{11/4}` as the repair change `U - V = r_b` is.  The
source bounds it pointwise in `W^{2,∞}` with the exponential transverse decay of the inlet stream
(`EntWPt`) and pairs it in `L²` with the mean jet (`MeanJetKernelPt`, `YoungJetDecayInt`): this
gives `EntJetAt` of `PresCoef.lean`.

Leaves defined here:
* `EntWPt` : `|E_εα|_{W^{2}}(chart point) ≤ P_ν e^{m₀/ν} ε e^{-m₁ν²|η|}` (rate `2π/c`, `c = ν⁻²`);
* `YoungJetDecayInt` : `‖e^{-m₁ν²|η|}·youngJetWeight‖_{L²(ringPhysμ)} ≤ P_ν ε²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The entrance coefficient change, pointwise** (source 2347-2356, 2389-2390, 2519-2520:
`‖E_εα‖_{W^{j,∞}} ≤ P_{ν,j}|α|`, `|α| = ε^{8/11}|A| ≤ P_ν e^{m₀/ν}ε`, and the actual periodized
inlet stream with every fixed derivative has exponential transverse decay with polynomial `c`
costs).  The transverse rate is the period rate: the periodized harmonic part is
`(π/c)²csc²(π(q+iη)/c)`, which decays like `e^{-2π|η|/c}`, and `c = ν⁻²`, so the rate is
`m₁ν²` for a fixed `m₁ > 0` (a fixed rate independent of `ν` is false).  Statement: for some
`m₁ > 0`, eventually in `n`, at every chart point `(s, (q, η))`, `s > 0`,
`|V - U_raw| + |D(V - U_raw)| + |D²(V - U_raw)| ≤ C ν^{-k} e^{m₀/ν} ε e^{-m₁ν²|η|}`. -/
def EntWPt (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (m₁ : ℝ), 0 < m₁ ∧ ∀ᶠ n : ℕ in atTop, ∀ p : Chart, 0 < p.1 →
    coefChgDens ((D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ p))
        (rawU D.Pl (D.level n) (NearInst.chartTau (D.level n).ε⁻¹ p))
        (NearInst.chartY (D.level n).ε⁻¹ p) ≤
      C * (D.level n).ν⁻¹ ^ k * (Real.exp (D.K.m0 / (D.level n).ν) * (D.level n).ε) *
        Real.exp (-(m₁ * (D.level n).ν ^ 2) * |p.2.2|)

/-- **The `(s, η)` integration of the young weight against the transverse decay** (source
5470-5476, density `πR²s^{-5/2}ds dq/c dη`, `R = ε⁻¹`; `youngJetWeight` is supported in
`s ≤ 1/ν` and is `≤ ε³s^{5/2}`, so `∫ ε⁶ s^{5}·πε⁻²s^{-5/2} ds ≤ Cν^{-9/2}ε⁴`, the `q`-cell has
mass `c = ν⁻²`, and `∫e^{-m₁ν²|η|}dη = 2/(m₁ν²)` costs a further power of `ν`): for every
`m₁ > 0` there are `C, k` with
`‖e^{-m₁ν²|η|}·youngJetWeight ν ε‖_{L²(ringPhysμ ε⁻¹ c)} ≤ C ν^{-k} ε²`, `c = ν⁻²`. -/
def YoungJetDecayInt : Prop :=
  ∀ m₁ : ℝ, 0 < m₁ → ∃ (C : ℝ) (k : ℕ), ∀ (ν ε : ℝ), 0 < ν → ν ≤ 1 → 0 < ε →
    eLpNorm (fun p : Chart => Real.exp (-(m₁ * ν ^ 2) * |p.2.2|) * youngJetWeight ν ε p) 2
        (ringPhysμ ε⁻¹ (cOf ν)) ≤
      ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ 2)

end UnforcedLeray.Short.PartIIIb.Concrete
