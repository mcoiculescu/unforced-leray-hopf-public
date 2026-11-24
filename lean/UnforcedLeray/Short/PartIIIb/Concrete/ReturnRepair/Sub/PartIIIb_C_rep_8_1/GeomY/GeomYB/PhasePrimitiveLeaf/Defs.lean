import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitive.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeaf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11

/-!
# Definitions and proved reductions for `PartIII-b:C/rep/8/1/1/2/5/1/1` (`YBPhase.SepCommOscFar`)

Source `the November 2 reference manuscript`
lines 5427-5432 ("For `Y` use the exact formula `Y = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`.
Apply the spatial kernel comparison to these terms separately"), 4195-4215 (`ward:shifted-resolvent`,
`ward:cutoff-source` `Y = 𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀`, `Ψ_{AZ} = AΨ_Z + Ψ_Z`,
`Ψ_{ΔZ} = (∂_r² - r⁻¹∂_r + ∂_z²)Ψ_Z`), 5400-5427 (one phase primitive in the dilation variable with
its dilation-one boundary term retained; separated kernels of degree `-5`; outward stream primitive
of the same degree), 3700-3712 (`𝒬 = [B, 𝒞_χ] - ν[Δ, 𝒞_χ]`).

## Decomposition into transition-annulus sub-leaves and quantifier-order fix

1. **Support reduction to the transition annulus (`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`)**:
   Outside `xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (i.e. for `5 * ν / 4 < xo 0 ^ 2 + xo 1 ^ 2`),
   `fderiv ℝ (comm ν μ ε⁻¹ χy Z τ) (ε⁻¹ • xo) = 0` by `YBWidth.fderiv_comm_eq_zero_of_gt`
   (`TaylorWidth/SepComm/Defs.lean:84`), so `B := fun _ => 0` is a measurable periodic majorant
   with `ltauAt (2 * ε * c) B = 0`.
2. **Quantifier order of `χy`**:
   Because `IsStreamCutoff χy` (`Concrete/SourceL.lean:55`) constrains only `0 ≤ χy ≤ 1`,
   `χy = 1` on `(-∞, 4/5]`, and `χy = 0` on `[1, ∞)` without bounding `deriv^[m] χy` (`1 ≤ m ≤ 3`)
   on `(4/5, 1)`, the constant `C` must depend on `χy` (`∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C ...`,
   matching `YBWidth.SepCommMeanFar` in `TaylorWidth/Of.lean:62` and `TCCoeff` in
   `PartIII-b_C_rep_5_2_2_11.lean:163`).
3. **The five transition-annulus sub-leaves**:
   * `CommDerivSplit`: Leibniz derivative inequality for `comm = commMain + commPsi` on the
     transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`;
   * `SepX0OscFar0`: order-`0` phase-primitive oscillation bound for `ε|xo'|⁻¹(Z₁ - Z₂)`;
   * `SepX0OscFar1`: order-`1` phase-primitive oscillation bound for `D_y(Z₁ - Z₂)` (**proved here**
     from `sepOscFar`, `GeomX/PhasePrimitive/FarLeaf.lean`);
   * `SepX0OscFar2`: order-`2` (Hessian) phase-primitive oscillation bound for
     `ν ε|xo'|⁻¹ D²_y(Z₁ - Z₂)`;
   * `SepPsiOscFar`: outward stream-primitive phase-primitive oscillation bound for
     `D_y(commPsi Z₁ - commPsi Z₂)`.
4. **Conditional assembly (`sepCommOscFarFixed_of`)**:
   Assembles `SepCommOscFarFixed` from `CommDerivSplit`, `SepX0OscFar0`, `SepX0OscFar2`, and
   `SepPsiOscFar` (with `SepX0OscFar1` discharged by `sepX0OscFar1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Short.IIIa

namespace YBPhase

open YBComm PhasePrim

/-! ## 1. Decomposition of the stream cutoff and commutator -/

/-- The scalar cutoff part `tcC0(ϱ y) • Z τ y` of `wardStreamCut`. -/
def cutMain (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcC0 ν R χy (ϱ y) • Z τ y

/-- The outward stream-primitive part `tcF0(ϱ y) • psiFld Z τ y` of `wardStreamCut`. -/
def cutPsi (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcF0 ν R χy (ϱ y) • psiFld Z τ y

/-- The `[D_{μ+1}, cutMain]` part of the commutator (source 3700-3712, 4203-4214):
`tcA1(ϱ y) • Z τ y + tcA2(ϱ y) • fderiv ℝ (Z τ) y (radialUnit y)`. -/
def commMain (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  tcA1 ν R χy (ϱ y) • Z τ y + tcA2 ν R χy (ϱ y) • fderiv ℝ (Z τ) y (radialUnit y)

/-- The `[D_{μ+1}, cutPsi]` outward stream-primitive part of the commutator (source 4195-4215). -/
def commPsi (ν μ R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y - cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y

/-- `wardStreamCut = cutMain + cutPsi` identically. -/
theorem wardStreamCut_eq_cutMain_add_cutPsi (ν R : ℝ) (χy : ℝ → ℝ)
    (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    wardStreamCut ν R χy Z τ y = cutMain ν R χy Z τ y + cutPsi ν R χy Z τ y := by
  unfold wardStreamCut cutMain cutPsi psiFld tcC0 tcF0 age
  rw [mul_smul]

/-! ## 2. The transition-annulus sub-leaves -/

/-- **Sub-leaf 1 (`CommDerivSplit`, task `PartIII-b:C/rep/8/1/1/2/5/1/1/1`)**:
Leibniz derivative inequality for `comm = [D_{μ+1}, 𝒞_y]` at a young receiver `y = ε⁻¹ • xo` on the
transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (source 4195-4215, 3700-3712, 5427-5432).
Near `y`, `comm Z = commMain Z + commPsi Z`; differentiating `commMain` and bounding the smooth
cutoff factors on `4/5 ≤ ν / |xo'|² ≤ 1` (`|∇(tcA1 ∘ ϱ)| ≤ C₀ ε |xo'|⁻¹`,
`|tcA1| + |∇(tcA2 ∘ ϱ)| + |tcA2| ‖D(radialUnit)‖ ≤ C₀`, `|tcA2| ≤ C₀ ν ε |xo'|⁻¹`) bounds
`‖D_y(comm Z₁ - comm Z₂)(y)‖` by the weighted order-`0,1,2` differences of `Z₁ - Z₂` plus
`‖D_y(commPsi Z₁ - commPsi Z₂)(y)‖`. -/
def CommDerivSplit : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 → ∀ τ : ℝ,
          let Z₁ := srcX0 ν μ (IIIa.thinSource ε F)
          let Z₂ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))
          let y := ε⁻¹ • xo
          let r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
          ‖fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y‖ₑ ≤
            ENNReal.ofReal C₀ *
              (ENNReal.ofReal (ε * r⁻¹) * ‖Z₁ τ y - Z₂ τ y‖ₑ +
                ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖ₑ +
                ENNReal.ofReal (ν * ε * r⁻¹) *
                  ‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖ₑ +
                ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y -
                  fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖ₑ)

/-- **Sub-leaf 2 (`SepX0OscFar0`, task `PartIII-b:C/rep/8/1/1/2/5/1/1/2`)**:
order-`0` phase-primitive oscillation bound for `X₀` on the transition annulus (source 5400-5427,
SP 3768-3790 at derivative order `0`): `∇K` has degree `-4`, so one phase primitive in the dilation
variable gives `‖X₀(F) - X₀(F̄)‖_{L²_τ} ≲ ε³ |xo'|⁻⁴ N₁(F)`, and multiplying by the cutoff-gradient
weight `ε |xo'|⁻¹` gives `ε⁴ |xo'|⁻⁵ N₁(F)`. -/
def SepX0OscFar0 : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ENNReal.ofReal (ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹) *
                ‖srcX0 ν μ (IIIa.thinSource ε F) τ (ε⁻¹ • xo) -
                  srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ
                    (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-- **Sub-leaf 3 (`SepX0OscFar1`)**: order-`1` phase-primitive oscillation bound for `D_y X₀` on the
transition annulus (source 5400-5427, SP 3768-3790 at derivative order `1`). Proved below from
`sepOscFar`. -/
def SepX0OscFar1 : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ‖fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε F) τ) (ε⁻¹ • xo) -
                fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ)
                  (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-- **Sub-leaf 4 (`SepX0OscFar2`, task `PartIII-b:C/rep/8/1/1/2/5/1/1/3`)**:
order-`2` (Hessian) phase-primitive oscillation bound for `D²_y X₀` on the transition annulus
(source 5400-5427, SP 3768-3790 at derivative order `2`): `D²∇K` has degree `-6`, so one phase
primitive in the dilation variable gives `‖D²_y X₀(F) - D²_y X₀(F̄)‖_{L²_τ} ≲ ε⁵ |xo'|⁻⁶ N₁(F)`,
and multiplying by the Laplacian cutoff weight `ν ε |xo'|⁻¹` (`ν |xo'|⁻² ≤ 1`, `ε ≤ 1`) gives
`ε⁴ |xo'|⁻⁵ N₁(F)`. -/
def SepX0OscFar2 : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ENNReal.ofReal (ν * ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹) *
                ‖fderiv ℝ (fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε F) τ)) (ε⁻¹ • xo) -
                  fderiv ℝ (fderiv ℝ (srcX0 ν μ
                    (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ))
                    (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-- **Sub-leaf 5 (`SepPsiOscFar`, task `PartIII-b:C/rep/8/1/1/2/5/1/1/4`)**:
outward stream-primitive phase-primitive oscillation bound for `commPsi` on the transition annulus
(source 4178-4215, 5400-5432): the outward stream primitive `Ψ_{X₀}` has the same degree `-5` after
its cutoff factors `tcF0(ϱ)` and `∂_r Ψ_Z = r Z_z`, `∂_z^m Ψ_Z = -∫_r^∞ ρ ∂_z^m Z_z dρ` are
included, so `D_y(commPsi Z₁ - commPsi Z₂)` at `y = ε⁻¹ • xo` has a measurable periodic phase
majorant with `‖B‖_{L²_τ} ≤ C (1 + ν⁻¹ + c)^k ε⁴ |xo'|⁻⁵ N₁(F)`. -/
def SepPsiOscFar : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε F)) τ) (ε⁻¹ • xo) -
                fderiv ℝ (commPsi ν μ ε⁻¹ χy
                  (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))) τ)
                  (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-! ## 3. Proof of Sub-leaf 3 (`SepX0OscFar1`) from `sepOscFar` -/

private theorem fderiv_srcX0 (ν μ : ℝ) (src : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y)
    (hB : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) :
    fderiv ℝ (srcX0 ν μ src τ) y =
      PhasePrim.reMap.comp (fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y -
        fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) := by
  have hw : srcX0 ν μ src τ = fun y => PhasePrim.reMap
      ((fun y => IIIa.sepW ν (μ : ℂ) src y τ) y -
        (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y) := rfl
  rw [hw]
  exact (PhasePrim.reMap.hasFDerivAt.comp y (hA.hasFDerivAt.sub hB.hasFDerivAt)).fderiv

private theorem dSrcX0_le (ν μ : ℝ) (src src' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y)
    (hB : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y)
    (hA' : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) src' y τ) y)
    (hB' : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src' y τ) y) :
    ‖fderiv ℝ (srcX0 ν μ src τ) y - fderiv ℝ (srcX0 ν μ src' τ) y‖ ≤
      2 * (‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y -
            fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) src' y τ) y‖ +
          ‖fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y -
            fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src' y τ) y‖) := by
  rw [fderiv_srcX0 ν μ src τ y hA hB, fderiv_srcX0 ν μ src' τ y hA' hB',
    ← ContinuousLinearMap.comp_sub]
  set a := fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) src y τ) y
  set b := fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src y τ) y
  set a' := fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) src' y τ) y
  set b' := fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) src' y τ) y
  have e : a - b - (a' - b') = (a - a') - (b - b') := by abel
  rw [e]
  calc ‖PhasePrim.reMap.comp ((a - a') - (b - b'))‖
      ≤ ‖PhasePrim.reMap‖ * ‖(a - a') - (b - b')‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (‖a - a'‖ + ‖b - b'‖) :=
        mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)

private theorem poly_le_13 (ν c : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) :
    1 + ν⁻¹ + c + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 13 * (1 + ν⁻¹ + c) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := PhasePrim.gap_le ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  linarith

private theorem sepW_thin_diffAt {ν c ε ρo ρi : ℝ} {μc : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi)
    (hμ : -(1 / 4) < μc.re) {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hth : FarLeafOrg.ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    {xo : Space} (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    DifferentiableAt ℝ (fun y => IIIa.sepW ν μc (IIIa.thinSource ε F) y τ) (ε⁻¹ • xo) := by
  set y0 : Space := ε⁻¹ • xo
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ FarLeafOrg.hor (ε⁻¹ • xo)
    rw [FarLeafOrg.hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  exact (FarLeafOrg.fderiv_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (FarLeafOrg.thin_isSep hε hth) τ y0 hy0
    (FarLeafOrg.sepDom_thin_lt_top hε hc hρ hμ hth hN τ y0)).2.differentiableAt

/-- **`SepX0OscFar1` from `SepOscFar`** (source 5400-5427). -/
theorem sepX0OscFar1_of (hOsc : SepOscFar) : SepX0OscFar1 := by
  obtain ⟨C₀, k₀, hC₀, hlf⟩ := hOsc PhasePrim.Kmu PhasePrim.Kmu_compact PhasePrim.Kmu_re
  refine ⟨4 * C₀ * 13 ^ k₀, k₀, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx _
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi_xo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := Real.sqrt_le_sqrt hνx
  have hμK : ((μ : ℝ) : ℂ) ∈ PhasePrim.Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ PhasePrim.Kmu :=
    ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  obtain ⟨B₁, hB₁m, hB₁p, hB₁ae, hB₁le⟩ := hlf ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ
    (μ : ℂ) hμK F hFm hFp hFs hFfin xo hρi_xo
  obtain ⟨B₂, hB₂m, hB₂p, hB₂ae, hB₂le⟩ := hlf ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ
    ((μ : ℂ) + 1) hμ1K F hFm hFp hFs hFfin xo hρi_xo
  have hth : FarLeafOrg.ThinHyp c ρo F := ⟨hFm, hFp, hFs⟩
  obtain ⟨hm1, _⟩ := IIIa.sepMomentSplit c hc F hFm
  have hN1 : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfin hm1
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hFm
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hFs x' Y _ h]
  have hth1 : FarLeafOrg.ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  refine ⟨fun τ => 2 * (B₁ τ + B₂ τ), (hB₁m.add hB₂m).const_mul 2,
    fun τ => by simp only [hB₁p τ, hB₂p τ], ?_, ?_⟩
  · filter_upwards [hB₁ae, hB₂ae] with τ h1 h2
    have hd := dSrcX0_le ν μ (IIIa.thinSource ε F)
      (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ (ε⁻¹ • xo)
      (sepW_thin_diffAt hν hc hε hρo hρ hreμ hth hFfin hρi_xo τ)
      (sepW_thin_diffAt hν hc hε hρo hρ hreμ1 hth hFfin hρi_xo τ)
      (sepW_thin_diffAt hν hc hε hρo hρ hreμ hth1 hN1 hρi_xo τ)
      (sepW_thin_diffAt hν hc hε hρo hρ hreμ1 hth1 hN1 hρi_xo τ)
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε F) τ) (ε⁻¹ • xo) -
          fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ)
            (ε⁻¹ • xo)‖
        ≤ ENNReal.ofReal (2 * (‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) y τ)
              (ε⁻¹ • xo) - fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) y τ) (ε⁻¹ • xo)‖ +
            ‖fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) y τ)
              (ε⁻¹ • xo) - fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1)
              (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) y τ) (ε⁻¹ • xo)‖)) :=
          ENNReal.ofReal_le_ofReal hd
      _ = 2 * (‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) y τ)
              (ε⁻¹ • xo) - fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ)
              (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) y τ) (ε⁻¹ • xo)‖ₑ +
            ‖fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) y τ)
              (ε⁻¹ • xo) - fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1)
              (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) y τ) (ε⁻¹ • xo)‖ₑ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
            ofReal_norm, ofReal_norm]
          norm_num
      _ ≤ 2 * (B₁ τ + B₂ τ) := by gcongr
  · set b := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    set M := 1 + ν⁻¹ + c
    set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
    have hr0 : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hρi_xo
    have hb0 : 0 ≤ b := by
      have : 0 < ρi - ρo := sub_pos.2 hρ
      have : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
      positivity
    have hM0 : 0 ≤ M := by positivity
    have hble : b ^ k₀ ≤ 13 ^ k₀ * M ^ k₀ := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hb0 (poly_le_13 ν c hν hν1 hc) k₀
    set a := C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)
    have ha0 : 0 ≤ a := by positivity
    have ha_le : 4 * a ≤ 4 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by
      have hr5 : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr0.le _
      calc 4 * a = 4 * C₀ * b ^ k₀ * (ε ^ 4 * r ^ (-5 : ℝ)) := by unfold a; ring
        _ ≤ 4 * C₀ * (13 ^ k₀ * M ^ k₀) * (ε ^ 4 * r ^ (-5 : ℝ)) := by gcongr
        _ = 4 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by ring
    calc IIIa.ltauAt (2 * ε * c) (fun τ => 2 * (B₁ τ + B₂ τ))
        ≤ 2 * (IIIa.ltauAt (2 * ε * c) B₁ + IIIa.ltauAt (2 * ε * c) B₂) :=
          PhasePrim.ltauAt_two_mul _ hB₁m hB₂m
      _ ≤ 2 * (ENNReal.ofReal a * IIIa.thinMoment c F +
            ENNReal.ofReal a * IIIa.thinMoment c F) := by
          gcongr
      _ = ENNReal.ofReal (4 * a) * IIIa.thinMoment c F := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc]
          have h2 : (2 : ℝ≥0∞) * 2 = ENNReal.ofReal 4 := by norm_num
          rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal (4 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) *
            IIIa.thinMoment c F := by
          gcongr

/-- **Sub-leaf 3 (`SepX0OscFar1`) holds unconditionally**, from `sepOscFar`. -/
theorem sepX0OscFar1 : SepX0OscFar1 :=
  sepX0OscFar1_of sepOscFar

/-! ## 4. Quantifier-corrected commutator leaf and assembly from the sub-leaves -/

/-- **Transition-annulus commutator oscillation bound** (`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`,
with `∀ χy : ℝ → ℝ, IsStreamCutoff χy →` preceding `∃ (C : ℝ) (k : ℕ)`). -/
def SepCommOscAnnulusBoundFixed : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε F)) τ) (ε⁻¹ • xo) -
                fderiv ℝ (comm ν μ ε⁻¹ χy
                  (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))) τ)
                  (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-- **Quantifier-corrected `SepCommOscFar`** (source 5427-5432, 4195-4215, 5400-5427): places
`∀ χy : ℝ → ℝ, IsStreamCutoff χy →` before `∃ (C : ℝ) (k : ℕ)` (matching `YBWidth.SepCommMeanFar`
in `TaylorWidth/Of.lean:62` and `TCCoeff`). -/
def SepCommOscFarFixed : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ xo : Space, ν ≤ xo 0 ^ 2 + xo 1 ^ 2 →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧ Function.Periodic B (2 * ε * c) ∧
            (∀ᵐ τ ∂(volume : Measure ℝ),
              ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε F)) τ) (ε⁻¹ • xo) -
                fderiv ℝ (comm ν μ ε⁻¹ χy
                  (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))) τ)
                  (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            IIIa.ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
                Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c F

/-- Reduction of `SepCommOscFarFixed` to the transition annulus `SepCommOscAnnulusBoundFixed`. -/
theorem sepCommOscFarFixed_of_annulus (hAnn : SepCommOscAnnulusBoundFixed) :
    SepCommOscFarFixed := by
  intro χy hχ
  obtain ⟨C, k, hC, hB⟩ := hAnn χy hχ
  refine ⟨C, k, hC, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx
  by_cases hgt : 5 * ν / 4 < xo 0 ^ 2 + xo 1 ^ 2
  · refine ⟨fun _ => 0, measurable_const, fun _ => rfl, ?_, ?_⟩
    · refine Eventually.of_forall fun τ => ?_
      rw [YBWidth.fderiv_comm_eq_zero_of_gt hχ hν hε _ τ hgt,
        YBWidth.fderiv_comm_eq_zero_of_gt hχ hν hε _ τ hgt, sub_self, ← ofReal_norm,
        norm_zero, ENNReal.ofReal_zero]
    · have hP : 0 < 2 * ε * c := by positivity
      rw [IIIa.ltauAt_const (2 * ε * c) hP 0]
      exact zero_le
  · exact hB ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx (le_of_not_gt hgt)

private theorem ltauAt_sum4_le (P : ℝ) {B₀ B₁ B₂ B₃ : ℝ → ℝ≥0∞}
    (h0 : Measurable B₀) (h1 : Measurable B₁) (h2 : Measurable B₂) (h3 : Measurable B₃) :
    IIIa.ltauAt P (fun τ => B₀ τ + B₁ τ + B₂ τ + B₃ τ) ≤
      IIIa.ltauAt P B₀ + IIIa.ltauAt P B₁ + IIIa.ltauAt P B₂ + IIIa.ltauAt P B₃ := by
  refine (IIIa.ltauAt_add_le P ((h0.add h1).add h2) h3).trans ?_
  gcongr
  refine (IIIa.ltauAt_add_le P (h0.add h1) h2).trans ?_
  gcongr
  exact IIIa.ltauAt_add_le P h0 h1

/-- **`SepCommOscAnnulusBoundFixed` from all five transition-annulus sub-leaves**
(source 5427-5432, 4195-4215, 5400-5427). -/
theorem sepCommOscAnnulusBoundFixed_of_subleaves (hSplit : CommDerivSplit) (h0 : SepX0OscFar0)
    (h1 : SepX0OscFar1) (h2 : SepX0OscFar2) (hPsi : SepPsiOscFar) :
    SepCommOscAnnulusBoundFixed := by
  intro χy hχ
  obtain ⟨Cs, hCs, hsp⟩ := hSplit χy hχ
  obtain ⟨C₀, k₀, hC₀, hlf0⟩ := h0
  obtain ⟨C₁, k₁, hC₁, hlf1⟩ := h1
  obtain ⟨C₂, k₂, hC₂, hlf2⟩ := h2
  obtain ⟨C₃, k₃, hC₃, hlf3⟩ := hPsi χy hχ
  set K := max (max k₀ k₁) (max k₂ k₃)
  refine ⟨Cs * (C₀ + C₁ + C₂ + C₃), K, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx hle
  obtain ⟨B₀, hB₀m, hB₀p, hB₀ae, hB₀le⟩ :=
    hlf0 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx hle
  obtain ⟨B₁, hB₁m, hB₁p, hB₁ae, hB₁le⟩ :=
    hlf1 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx hle
  obtain ⟨B₂, hB₂m, hB₂p, hB₂ae, hB₂le⟩ :=
    hlf2 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx hle
  obtain ⟨B₃, hB₃m, hB₃p, hB₃ae, hB₃le⟩ :=
    hlf3 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx hle
  set B : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal Cs * (B₀ τ + B₁ τ + B₂ τ + B₃ τ)
  have hBm : Measurable B := (((hB₀m.add hB₁m).add hB₂m).add hB₃m).const_mul _
  have hBp : Function.Periodic B (2 * ε * c) := fun τ => by
    simp only [B, hB₀p τ, hB₁p τ, hB₂p τ, hB₃p τ]
  refine ⟨B, hBm, hBp, ?_, ?_⟩
  · filter_upwards [hB₀ae, hB₁ae, hB₂ae, hB₃ae] with τ ha0 ha1 ha2 ha3
    have hpt := hsp ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx hle τ
    refine hpt.trans ?_
    simp only [B]
    gcongr
  · set M := 1 + ν⁻¹ + c
    have hM1 : 1 ≤ M := by
      have : 0 < ν⁻¹ := inv_pos.2 hν
      linarith
    have hk0 : k₀ ≤ K := le_trans (le_max_left k₀ k₁) (le_max_left _ _)
    have hk1 : k₁ ≤ K := le_trans (le_max_right k₀ k₁) (le_max_left _ _)
    have hk2 : k₂ ≤ K := le_trans (le_max_left k₂ k₃) (le_max_right _ _)
    have hk3 : k₃ ≤ K := le_trans (le_max_right k₂ k₃) (le_max_right _ _)
    set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
    have hr0 : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) (Real.sqrt_le_sqrt hνx)
    have hr5 : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr0.le _
    have hp0 : C₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) ≤ C₀ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by
      have := pow_le_pow_right₀ hM1 hk0; gcongr
    have hp1 : C₁ * M ^ k₁ * ε ^ 4 * r ^ (-5 : ℝ) ≤ C₁ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by
      have := pow_le_pow_right₀ hM1 hk1; gcongr
    have hp2 : C₂ * M ^ k₂ * ε ^ 4 * r ^ (-5 : ℝ) ≤ C₂ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by
      have := pow_le_pow_right₀ hM1 hk2; gcongr
    have hp3 : C₃ * M ^ k₃ * ε ^ 4 * r ^ (-5 : ℝ) ≤ C₃ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by
      have := pow_le_pow_right₀ hM1 hk3; gcongr
    have hL0 : IIIa.ltauAt (2 * ε * c) B₀ ≤
        ENNReal.ofReal (C₀ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F :=
      hB₀le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hp0) _)
    have hL1 : IIIa.ltauAt (2 * ε * c) B₁ ≤
        ENNReal.ofReal (C₁ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F :=
      hB₁le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hp1) _)
    have hL2 : IIIa.ltauAt (2 * ε * c) B₂ ≤
        ENNReal.ofReal (C₂ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F :=
      hB₂le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hp2) _)
    have hL3 : IIIa.ltauAt (2 * ε * c) B₃ ≤
        ENNReal.ofReal (C₃ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F :=
      hB₃le.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hp3) _)
    calc IIIa.ltauAt (2 * ε * c) B
        = ENNReal.ofReal Cs *
            IIIa.ltauAt (2 * ε * c) (fun τ => B₀ τ + B₁ τ + B₂ τ + B₃ τ) :=
          IIIa.ltauAt_const_mul _ _ ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal Cs *
            (IIIa.ltauAt (2 * ε * c) B₀ + IIIa.ltauAt (2 * ε * c) B₁ +
              IIIa.ltauAt (2 * ε * c) B₂ + IIIa.ltauAt (2 * ε * c) B₃) := by
          gcongr
          exact ltauAt_sum4_le _ hB₀m hB₁m hB₂m hB₃m
      _ ≤ ENNReal.ofReal Cs *
            (ENNReal.ofReal (C₀ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F +
              ENNReal.ofReal (C₁ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F +
              ENNReal.ofReal (C₂ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F +
              ENNReal.ofReal (C₃ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F) := by
          gcongr
      _ = ENNReal.ofReal (Cs * (C₀ + C₁ + C₂ + C₃) * M ^ K * ε ^ 4 * r ^ (-5 : ℝ)) *
            IIIa.thinMoment c F := by
          have ha0 : 0 ≤ C₀ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          have ha1 : 0 ≤ C₁ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          have ha2 : 0 ≤ C₂ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          have ha3 : 0 ≤ C₃ * M ^ K * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          rw [← add_mul, ← add_mul, ← add_mul, ← mul_assoc,
            ← ENNReal.ofReal_add ha0 ha1, ← ENNReal.ofReal_add (by positivity) ha2,
            ← ENNReal.ofReal_add (by positivity) ha3, ← ENNReal.ofReal_mul hCs]
          congr 2
          ring

/-- **Conditional assembly of `SepCommOscFarFixed`** from `CommDerivSplit`, `SepX0OscFar0`,
`SepX0OscFar2`, and `SepPsiOscFar` (with `SepX0OscFar1` discharged by `sepX0OscFar1`). -/
theorem sepCommOscFarFixed_of (hSplit : CommDerivSplit) (h0 : SepX0OscFar0)
    (h2 : SepX0OscFar2) (hPsi : SepPsiOscFar) : SepCommOscFarFixed :=
  sepCommOscFarFixed_of_annulus
    (sepCommOscAnnulusBoundFixed_of_subleaves hSplit h0 sepX0OscFar1 h2 hPsi)

end YBPhase

end UnforcedLeray.Short.PartIIIb.Concrete
