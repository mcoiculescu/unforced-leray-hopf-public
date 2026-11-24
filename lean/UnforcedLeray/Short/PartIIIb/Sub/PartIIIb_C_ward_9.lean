import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound.Young
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# `PartIII-b:C/ward/9` (decomposition): the young `Y₂` bound of `Y = D_{μ+1}X`

Source of record `the November 2 reference manuscript`
(73 pages).  `WardYYoungL2` (`Ward/HBound/Young.lean`) splits, by `wardY_split`
(`Org/YThinTrans.lean`, source 4203-4214, valid once `ShiftedResolventYoung`), as
`Y = χ_yW_μ + transField` (`transField = (𝒞_y - χ_y)W_μ + [D_{μ+1}, 𝒞_y]X₀`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Lemma 1** (`ward:shifted-resolvent`, source 4196-4201): `D_{μ+1}X₀ = W_μ` on the young region
`ϱ > 0`, `νs ≤ 1`, separated from the old source (supported in `s ≥ 1.2/ν`, 4163-4168). -/
def WardYShiftedRes : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    IsOldL2 c ν g → ShiftedResolventYoung ν μ R c g

/-- **Lemma 2** (`sep:young` 3633-3648 with `p = q = 2`, `b = 1`, `j = 0`, lift identity
2683-2689): the young chart reading of the scalar-cutoff part `χ_yW_μ` is `≤ C‖g‖`. -/
def WardYWYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      YoungL2Le c ν R C (wardYoungW ν μ R c χy g) g

/-- **Lemma 3** (source 3687-3713, 4202-4216): the young chart reading of
`transField = (𝒞_y - χ_y)W_μ + [D_{μ+1}, 𝒞_y]X₀` is `≤ C‖g‖`; both terms live on the annulus
`R√ν ≤ ϱ ≤ R√(1.25ν)` (`χ_y'` supported there), carry only derivatives of `χ_y`, `Bχ = -ϱχ'/2`
bounded, and the stream primitive `Ψ` has the translation-invariant majorant of 3687-3697. -/
def WardYTransYoungL2 : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      YoungL2Le c ν R C (transField ν μ R c χy g) g

/-- **Lemma 4** (measurability): the young chart reading of `Y` is a.e. strongly measurable for
`ageμ c (-3/2)` (the integrand `τ ↦ outPrim`, `fderiv`, `sepW` are jointly measurable for
measurable `g`; cf. `wardX0_measurable_of_measurable`, `sepWre_measurable`). -/
def WardYYoungMeas : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∀ g : Chart → Ten3, IsOldL2 c ν g →
      AEStronglyMeasurable (wardYoungRead ν R (wardY ν μ R c χy g)) (ageμ c (-3 / 2))

end UnforcedLeray.Short.PartIIIb.Concrete
