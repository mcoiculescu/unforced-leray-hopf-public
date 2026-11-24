import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1

/-!
# `PartIII-b:C/rep/8/1/1/1` (`geomX`): the pieces of the `X` part of the geometric comparison

Source `the November 2 reference manuscript`
lines 5400-5427 (separated kernels, one phase primitive with dilation-one boundary term, finite
transverse width, heat-to-Newton error by Taylor's formula), 5439-5443 (strict radial gap along
every Taylor segment), 4171-4186 and 4783-4791 (`X = 𝒞_y X₀`, `X^mt = 𝒞_y(W^mt_μ - W^mt_{μ+1})`).

## Decomposition

Both `X₁ = actX` and `X^mt = mnX` are the outward stream cutoff `𝒞_y` of an unscaled field:
`actX = 𝒞_y zAct` with `zAct = X₀ = W_μ - W_{μ+1}` (the finite-width, phase-dependent response,
`wardX0`), and `mnX = 𝒞_y zMt` with `zMt = W^mt_μ - W^mt_{μ+1}` (zero width, phase mean, Newton).
Between them sits the response `zMid` of the **phase-mean chart tensor** (finite transverse width
retained, the phase `q` averaged away).  Then

* `zAct → zMid`: **phase primitive** (`PhasePrimitiveAt`): the oscillating part of the tensor has
  zero `q`-mean, so one primitive in the dilation variable (boundary term at dilation one kept)
  converts it into one power of `ε` (5415-5427);
* `zMid → zMt`: **finite width and heat-to-Newton** (`TaylorWidthAt`): both fields are phase free,
  and the difference is the transverse Taylor remainder (first transverse moment `N`) plus the
  heat-to-Newton kernel error with the strict radial gap along each Taylor segment (5439-5443);
* `ZRegularAt`: regularity and decay of the three fields on the region clear of the old source, so
  that `𝒞_y` may be differentiated, the outward primitive `Ψ` converges, and `D𝒞_y` of the
  difference is controlled by the ray integrals of `|DΔ|` (assembly, organizer item `.../asm`).

Each bound is at **every young chart point** `s ∈ (0, 1/ν]`, hence at every point of the outward
ray through a young receiver (ages decrease outward), uniformly in `η`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- The phase (`q`) mean of a chart tensor over the cell: `ḡ(s,(q,η)) = c⁻¹∫_cell g(s,(q',η))dq'`
(source 3753-3757 `phaseMean`, 4764-4770; the transverse variables `(s, η)` are kept, so the
finite transverse width is retained). -/
def meanQ (c : ℝ) (g : Chart → Ten3) : Chart → Ten3 :=
  fun p => c⁻¹ • ∫ q in Ico (-c / 2) (c / 2), g (p.1, (q, p.2.2))

/-- The point of the outward ray through `y`: same azimuth and height, horizontal radius `t`
(`rayPt`, source 4180-4182). -/
def outRay (y : Space) (t : ℝ) : Space :=
  WithLp.toLp 2 ![t * (y 0 / ϱ y), t * (y 1 / ϱ y), y 2]

/-- The region clear of the old source: `(εϱ)² > ν/1.1` (the old source lives at `(εϱ)² ≤ ν/1.2`,
ratio of radii at most `1/√1.2`, source 5404-5406; the young receivers have `(εϱ)² ≥ ν`).  Open,
contains every outward ray from a young receiver. -/
def clearSet (ε ν : ℝ) : Set Space := {y | 0 < ϱ y} ∩ {y | ν / (11 / 10) < (ε * ϱ y) ^ 2}

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `X₀ = W_μ - W_{μ+1}` for the old thin source (source 4171, 5377-5379). -/
def zAct (T : LStr Pl K L) : ℝ → Space → Space :=
  wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (thinG Pl K L T)

/-- `X₀` with the phase-mean chart tensor `ḡ` in place of `g` (finite width, no phase). -/
def zMid (T : LStr Pl K L) : ℝ → Space → Space :=
  wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T))

/-- `W^mt_μ - W^mt_{μ+1}` (source 4783-4791), phase free, as a field on `Space`:
`mnX = 𝒞_y zMt`. -/
def zMt (T : LStr Pl K L) : ℝ → Space → Space :=
  fun _ y => WithLp.toLp 2
    (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) (WithLp.ofLp y) -
      youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T) (WithLp.ofLp y))

/-- `|D_y zAct - D_y zMid|` (the phase part). -/
def dPhase (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (zAct Pl K L μ T τ) y - fderiv ℝ (zMid Pl K L μ T τ) y‖

/-- `|D_y zMid - D_y zMt|` (the width and heat-to-Newton part). -/
def dWidth (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (zMid Pl K L μ T τ) y - fderiv ℝ (zMt Pl K L μ T τ) y‖

/-- **Phase primitive** (source 5415-5427: "one phase primitive in the dilation variable, with its
dilation-one boundary term retained"): at every young chart point
`‖D_y zAct - D_y zMid‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`. -/
def PhasePrimitiveAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => dPhase Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (dPhase Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Finite width and heat-to-Newton** (source 5415-5427, 5439-5443: Taylor's formula costs the
first transverse moment, the strict radial gap holds along every Taylor segment; the age power
`s³` is bounded by `P_ν s^{5/2}` on the young interval): both fields are phase free, so the bound
is pointwise in the phase: `|D_y zMid - D_y zMt| ≤ P_ν ε⁴ s^{5/2} N` at every young chart point
and every phase `q`, for swirl-free thin stresses (`ThinAziZero`: source 5376, 5141-5142, 4772-4774;
`zMid` keeps a hoop entry `T(1,1)` through `NearInst.nsSym`, `zMt` drops it through `phaseMean`,
so for a hoop stress the difference is of order `ε³ s^{5/2} N`). -/
def TaylorWidthAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T → ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η q : ℝ,
    ENNReal.ofReal (dWidth Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Regularity and decay off the old source** (source 4178-4186, 5400-5406: the separated
kernels are smooth away from the source, the outward primitive `Ψ` converges): for every `T` and
phase, the three fields are `C¹` on `clearSet` and tend to zero along every outward ray. -/
def ZRegularAt : Prop :=
  ∀ T : LStr Pl K L, ∀ τ : ℝ,
    (∀ Z ∈ ({zAct Pl K L μ T, zMid Pl K L μ T, zMt Pl K L μ T} :
        Set (ℝ → Space → Space)), ContDiffOn ℝ 1 (Z τ) (clearSet L.ε L.ν)) ∧
    (∀ Z ∈ ({zAct Pl K L μ T, zMid Pl K L μ T, zMt Pl K L μ T} :
        Set (ℝ → Space → Space)), ∀ y ∈ clearSet L.ε L.ν,
      Tendsto (fun t : ℝ => Z τ (outRay y t)) atTop (𝓝 0))

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `PhasePrimitiveAt`. -/
def PhasePrimitive : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    PhasePrimitiveAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `TaylorWidthAt`. -/
def TaylorWidth : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    TaylorWidthAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `ZRegularAt`. -/
def ZRegular : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ZRegularAt D.Pl D.K (D.level n) (D.mu n z)

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
