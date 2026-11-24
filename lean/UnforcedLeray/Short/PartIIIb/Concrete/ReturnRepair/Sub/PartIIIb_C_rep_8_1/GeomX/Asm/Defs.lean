import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Pieces

/-!
# `PartIII-b:C/rep/8/1/1/1/asm`: the stream-cut assembly of `GeomX` — statements

Source `the November 2 reference manuscript`
lines 4178-4186 (outward primitive `Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,z) dρ`, stream cutoff
`𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z`; "the separated-kernel estimates prove convergence of this
primitive and its differentiated versions"), 5415-5427 (the geometric comparison in the normalized
phase `L²`), 2666-2668 (the chart `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`).

## The mathematics

`actX = 𝒞_y zAct` (definitionally) and `mnX = 𝒞_y zMt` off the axis (`StreamCutEq`, the target of
`PartIII-b:C/rep/8/1/1/1/1`).  At a young receiver `y = (r, 0, z)` (`ν R²/r² ≤ 1`), with
`Z = zAct - zMt` and `g = |DzAct - DzMt|` on the outward ray `ρ ≥ r`:

* (`StreamCutAlgStmt`) differentiating `𝒞_y`:
  `|D𝒞_yZ₁ - D𝒞_yZ₂| ≤ C₀(|DZ(y)| + r⁻¹|Z(y)| + r⁻³|Ψ_{Z₁} - Ψ_{Z₂}| + r⁻²|∂_zΨ_{Z₁} - ∂_zΨ_{Z₂}|)`,
  `C₀` depending on `χ̂_y` only (`|∇χ_y| ≤ 2‖χ̂_y'‖/r`, `|χ_y'/r| ≤ 2‖χ̂_y'‖/r²`,
  `|∇(χ_y'/r)| ≤ (8‖χ̂_y'‖ + 4‖χ̂_y''‖)/r³` because `ν R²/r² ≤ 1`, and `∂_rΨ = r Z_z`);
* (`RayFTCStmt`) along the ray: `|Z(y)| ≤ ∫_r^∞ g` (value `= -∫` of the outward derivative, the
  field tends to zero), `|ΔΨ| ≤ ∫_r^∞ ρ|Z| ≤ ∫_r^∞ σ² g(σ) dσ`, `|Δ∂_zΨ| ≤ ∫_r^∞ ρ g`;
* the ray point at radius `ρ` is the chart point `(s', (q', η'))`, `s' = R²/ρ²`, `η' = zR/ρ`,
  `q' = q + (R/2) log(s/s')`, so `ρ^j (R/ρ)^5` integrates to `≤ r^{j+1} s^{5/2}` (`j ≤ 2`), the
  `L²_τ` bound of `dPhase` transfers by `c`-periodicity in `q` (the phase period `2c/R`), and
  Minkowski's integral inequality gives the `L²_τ` bound of the ray integrals; `dWidth` is bounded
  pointwise.

The two new source facts beyond `Pieces.lean` are `ZPrimRegularAt` (convergence and
differentiability of the outward primitive, source 4182-4184: `ZRegularAt` gives `C¹` and decay of
the fields but not the primitive) and `DPhaseMeasAt` (joint measurability of `dPhase` on the clear
region, needed for Tonelli/Minkowski in `(q, ρ)`; it follows from `ZRegular` and the joint
measurability of `wardX0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomXAsm

/-- The point `(ρ, 0, z)` of the half plane `φ = 0` (where `outPrim` reads its field). -/
def hpt (ρ z : ℝ) : Space := WithLp.toLp 2 ![ρ, 0, z]

/-- `|D Z₁(x) - D Z₂(x)|` at phase `τ`. -/
def dDiff (Z₁ Z₂ : ℝ → Space → Space) (τ : ℝ) (x : Space) : ℝ :=
  ‖fderiv ℝ (Z₁ τ) x - fderiv ℝ (Z₂ τ) x‖

/-- The ray integral `∫_r^∞ ρ^j g(ρ, 0, z) dρ` (extended real; `∞` allowed). -/
def rayW (j : ℕ) (g : Space → ℝ) (r z : ℝ) : ℝ≥0∞ :=
  ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * g (hpt ρ z))

/-- The pointwise bound of the stream-cut derivative difference at `y = (r, 0, z)`:
`g(y) + r⁻¹∫_r^∞ g + r⁻²∫_r^∞ ρ g + r⁻³∫_r^∞ ρ² g`. -/
def rayBound (g : Space → ℝ) (r z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (g (hpt r z)) + ENNReal.ofReal r⁻¹ * rayW 0 g r z +
    ENNReal.ofReal (r⁻¹ ^ 2) * rayW 1 g r z + ENNReal.ofReal (r⁻¹ ^ 3) * rayW 2 g r z

/-- The differentiated outward primitive `∫_r^∞ ρ ∂_z Z_z(ρ, 0, z) dρ` (so that
`∂_zΨ_Z = -primDz`). -/
def primDz (Z : ℝ → Space → Space) (τ r z : ℝ) : ℝ :=
  ∫ ρ in Ioi r, ρ * fderiv ℝ (Z τ) (hpt ρ z) (coordinateVector 2) 2

/-- **Convergence and differentiability of the outward primitive** at `(r, z)` (source 4182-4184):
`ρ Z_z` and `ρ ∂_zZ_z` are integrable on the ray `(r, ∞)`, and `Ψ_Z = outPrim Z τ` is
differentiable at `(r, z)` with `∂_rΨ_Z = r Z_z(r, 0, z)` and `∂_zΨ_Z = -∫_r^∞ ρ ∂_zZ_z dρ`. -/
def PrimData (Z : ℝ → Space → Space) (τ r z : ℝ) : Prop :=
  IntegrableOn (fun ρ => ρ * Z τ (hpt ρ z) 2) (Ioi r) ∧
  IntegrableOn (fun ρ => ρ * fderiv ℝ (Z τ) (hpt ρ z) (coordinateVector 2) 2) (Ioi r) ∧
  HasFDerivAt (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
    ((r * Z τ (hpt r z) 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (-primDz Z τ r z) • ContinuousLinearMap.snd ℝ ℝ ℝ) (r, z)

theorem hpt_eq (ρ z : ℝ) : hpt ρ z = !₂[ρ, 0, z] := rfl

theorem chartY_eq_hpt (R s q η : ℝ) :
    NearInst.chartY R (s, (q, η)) = hpt (R / Real.sqrt s) (η / Real.sqrt s) := rfl

end GeomXAsm

open GeomXAsm

/-- The bound of `StreamCutAlgStmt` with a given constant `C₀`. -/
def StreamCutAlgWith (χ : ℝ → ℝ) (C₀ : ℝ) : Prop :=
  ∀ (ν R r z τ : ℝ) (Z₁ Z₂ : ℝ → Space → Space), 0 < ν → 0 < R → 0 < r →
    ν * (R ^ 2 / r ^ 2) ≤ 1 →
    DifferentiableAt ℝ (Z₁ τ) (hpt r z) → DifferentiableAt ℝ (Z₂ τ) (hpt r z) →
    PrimData Z₁ τ r z → PrimData Z₂ τ r z →
    ‖fderiv ℝ (wardStreamCut ν R χ Z₁ τ) (hpt r z) -
        fderiv ℝ (wardStreamCut ν R χ Z₂ τ) (hpt r z)‖ ≤
      C₀ * (dDiff Z₁ Z₂ τ (hpt r z) + r⁻¹ * ‖Z₁ τ (hpt r z) - Z₂ τ (hpt r z)‖ +
        r⁻¹ ^ 3 * |outPrim Z₁ τ r z - outPrim Z₂ τ r z| +
        r⁻¹ ^ 2 * |primDz Z₁ τ r z - primDz Z₂ τ r z|)

/-- **(a1) The derivative of the stream cutoff** (source 4178-4186): for a stream cutoff profile
`χ` there is `C₀` (depending on `χ` only) such that at every young point `y = (r, 0, z)`
(`ν R²/r² ≤ 1`) where `Z₁, Z₂` are differentiable and have convergent, differentiable outward
primitives,
`|D𝒞Z₁(y) - D𝒞Z₂(y)| ≤ C₀(|DZ₁(y) - DZ₂(y)| + r⁻¹|Z₁(y) - Z₂(y)| + r⁻³|Ψ₁ - Ψ₂| + r⁻²|∂_zΨ₁ - ∂_zΨ₂|)`
with `𝒞 = wardStreamCut ν R χ`, `Ψᵢ = outPrim Zᵢ τ r z`. -/
def StreamCutAlgStmt : Prop :=
  ∀ χ : ℝ → ℝ, IsStreamCutoff χ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ StreamCutAlgWith χ C₀

/-- **(a2) The ray bounds** (source 4178-4184: the value is minus the integral of the outward
derivative since the fields decay; Tonelli for the primitive): with `g = dDiff Z₁ Z₂ τ` along the
ray `ρ ≥ r` through `(r, 0, z)`,
`|Z₁ - Z₂|(r,0,z) ≤ ∫_r^∞ g`, `|Ψ₁ - Ψ₂| ≤ ∫_r^∞ ρ² g`, `|∂_zΨ₁ - ∂_zΨ₂| ≤ ∫_r^∞ ρ g`. -/
def RayFTCStmt : Prop :=
  ∀ (r z τ : ℝ) (Z₁ Z₂ : ℝ → Space → Space), 0 < r →
    (∀ ρ : ℝ, r ≤ ρ → DifferentiableAt ℝ (Z₁ τ) (hpt ρ z) ∧ DifferentiableAt ℝ (Z₂ τ) (hpt ρ z)) →
    Tendsto (fun t : ℝ => Z₁ τ (hpt t z) - Z₂ τ (hpt t z)) atTop (𝓝 0) →
    PrimData Z₁ τ r z → PrimData Z₂ τ r z →
    ENNReal.ofReal ‖Z₁ τ (hpt r z) - Z₂ τ (hpt r z)‖ ≤ rayW 0 (dDiff Z₁ Z₂ τ) r z ∧
    ENNReal.ofReal |outPrim Z₁ τ r z - outPrim Z₂ τ r z| ≤ rayW 2 (dDiff Z₁ Z₂ τ) r z ∧
    ENNReal.ofReal |primDz Z₁ τ r z - primDz Z₂ τ r z| ≤ rayW 1 (dDiff Z₁ Z₂ τ) r z

/-- The exact statement of `mnX_eq_wardStreamCut` (task `PartIII-b:C/rep/8/1/1/1/1`, source
4178-4186, 4783-4791): off the axis `X^mt` is the Ward stream cutoff of `zMt`. -/
def StreamCutEq : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (T : LStr Pl K L) (τ : ℝ)
    (y : Space), 0 < ϱ y →
    mnX Pl K L μ T τ y = wardStreamCut L.ν L.ε⁻¹ K.χy (zMt Pl K L μ T) τ y

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Outward primitive of the old-source fields** (source 4182-4184: "The separated-kernel
estimates prove convergence of this primitive and its differentiated versions"; 5400-5406: the
receivers in the clear region `(εr)² > ν/1.1` are radially separated from the old source
`(εr)² ≤ ν/1.2`): for every `T`, every phase and every point `(r, 0, z)` of the clear region, the
actual field `zAct = X₀` and the mean field `zMt` have `PrimData`. -/
def ZPrimRegularAt : Prop :=
  ∀ T : LStr Pl K L, ∀ τ : ℝ,
    ∀ Z ∈ ({zAct Pl K L μ T, zMt Pl K L μ T} : Set (ℝ → Space → Space)),
      ∀ r z : ℝ, 0 < r → L.ν / (11 / 10) < (L.ε * r) ^ 2 → PrimData Z τ r z

/-- **Joint measurability of the phase part on the clear region**: `(τ, y) ↦ 1_clear(y) dPhase(τ, y)`
is measurable (from the joint measurability of `wardX0` for measurable chart tensors and the
differentiability of `zAct, zMid` on the open clear region, `ZRegularAt`). -/
def DPhaseMeasAt : Prop :=
  ∀ T : LStr Pl K L, Measurable fun p : ℝ × Space =>
    (clearSet L.ε L.ν).indicator (fun y => dPhase Pl K L μ T p.1 y) p.2

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `ZPrimRegularAt`. -/
def ZPrimRegular : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ZPrimRegularAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence form of `DPhaseMeasAt`. -/
def DPhaseMeas : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, DPhaseMeasAt D.Pl D.K (D.level n) (D.mu n z)

/-- The measurability conjunct of `GeomXAt` (the statement of `xcmp_aemeasurable_cell`, task
`PartIII-b:C/rep/8/1/1/1/5`, restricted to the young chart points `0 < s ≤ 1/ν`). -/
def XcmpCellMeas : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
    ∀ s ∈ Ioc (0 : ℝ) (1 / (D.level n).ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => xcmp D.Pl D.K (D.level n) (D.mu n z) T
        (NearInst.chartTau (D.level n).ε⁻¹ (s, (q, η)))
        (NearInst.chartY (D.level n).ε⁻¹ (s, (q, η))))
      (volume.restrict (Ico (-cOf (D.level n).ν / 2) (cOf (D.level n).ν / 2)))

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
