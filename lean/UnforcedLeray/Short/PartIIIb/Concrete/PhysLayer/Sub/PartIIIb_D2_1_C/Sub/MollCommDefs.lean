import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PhaseLpTri2

/-!
# `MollCommutatorLimitFull`: concrete definitions and Haiku-sized ingredients

Source `the November 2 reference manuscript` lines 1351-1362 (adjoint graph at
`r = 2`) and 1556-1583 (mollified differences converge strongly).

Mathematics.  Write `ρ` for the normalised bump `ρ.normed volume` on `ℝ × ℝ³`, and
`L₀ᵗ = -∂_τ + ½ y·∇ - νΔ + 1` (`driftT - νΔ - ½`).  For `Φ ∈ Y_2` with the full equation
`⟪(μ + L₀)Ψ, Φ⟫ = ⟪Ψ, g⟫` against all phase tests, test with the periodised translate
`Ψ(w) = ∑ₖ ρ(x - w + (kP, 0)) e`.  Unfolding the pairing gives, with `z = x - w`,
`(μ + L₀ᵗ)(ρ ⋆ Φ)(x) - ρ ⋆ g (x) = ∫ ½ (3 ρ(z) + z·∇_yρ(z)) Φ(x - z) dz = commK ρ Φ x`,
the Friedrichs commutator `½ [y·∇, ρ ⋆] Φ` (kernel `½ div_y(z ρ)`, mean zero, `L¹`-norm bounded
independently of the shape of `ρ` by the layer-cake decomposition of the monotone profile into
cube averages).  It is bounded on `Y_2` by an absolute constant, tends to `0` on smooth tests, and
`Y_2` is approximated by tests.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## Kernels (all real scalar functions on `ℝ × ℝ³`, built from `ρ.normed volume`) -/

/-- `∂_τ κ`. -/
def kerDτ (κ : ℝ × Space → ℝ) (z : ℝ × Space) : ℝ := fderiv ℝ κ z (1, 0)

/-- `v·∇_y κ` for a spatial vector `v`. -/
def kerDv (κ : ℝ × Space → ℝ) (v : Space) (z : ℝ × Space) : ℝ := fderiv ℝ κ z (0, v)

/-- `Δ_y κ = ∑ⱼ ∂ⱼ∂ⱼ κ`. -/
def kerLap (κ : ℝ × Space → ℝ) (z : ℝ × Space) : ℝ :=
  ∑ j : Fin 3, fderiv ℝ (fun z' => fderiv ℝ κ z' (0, coordinateVector j)) z (0, coordinateVector j)

/-- The commutator kernel `kap ρ = div_y(z ρ) = 3 ρ + z·∇_y ρ` (mean zero). -/
def kap (ρ : ContDiffBump (0 : ℝ × Space)) (z : ℝ × Space) : ℝ :=
  3 * ρ.normed volume z + kerDv (ρ.normed volume) z.2 z

/-- The Friedrichs commutator `½ [y·∇, ρ ⋆] Φ (x) = ∫ ½ kap ρ z • Φ(x - z) dz`
(source 1556-1583; here `y·∇` is the transpose drift, `ρ ⋆` commutes with `∂_τ` and `Δ`). -/
def commK (ρ : ContDiffBump (0 : ℝ × Space)) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ z, ((1 / 2 : ℝ) * kap ρ z) • Φ (x - z)

/-- Kernel of `(μ + L₀ᵗ)(ρ ⋆ Φ)(x) = ∫ adjKer ρ ν μ x z • Φ(x - z) dz`:
`(μ + 1) ρ - ∂_τ ρ + ½ x·∇_y ρ - νΔ_y ρ`, evaluated at `z`. -/
def adjKer (ν μ : ℝ) (ρ : ContDiffBump (0 : ℝ × Space)) (x z : ℝ × Space) : ℝ :=
  (μ + 1) * ρ.normed volume z - kerDτ (ρ.normed volume) z +
    (1 / 2 : ℝ) * kerDv (ρ.normed volume) x.2 z - ν * kerLap (ρ.normed volume) z

/-- Kernel of the pairing `⟪(μ + L₀)Ψ, Φ⟫` for `Ψ(w) = ρ(x - w) e`, evaluated at `z = x - w`:
`(μ - ½) ρ - ∂_τ ρ + ½ (x - z)·∇_y ρ - νΔ_y ρ` (the transpose of `L₀ = ∂_τ - ½ y·∇ - νΔ - ½`). -/
def testKer (ν μ : ℝ) (ρ : ContDiffBump (0 : ℝ × Space)) (x z : ℝ × Space) : ℝ :=
  (μ - 1 / 2) * ρ.normed volume z - kerDτ (ρ.normed volume) z +
    (1 / 2 : ℝ) * kerDv (ρ.normed volume) (x.2 - z.2) z - ν * kerLap (ρ.normed volume) z

/-- The `P`-periodised translate `w ↦ ∑ₖ κ(x - w + (kP, 0)) e` of a kernel `κ` (a finite sum
for compactly supported `κ`). -/
def shiftKer (P : ℝ) (κ : ℝ × Space → ℝ) (x : ℝ × Space) (e : CVec3) : ℝ × Space → CVec3 :=
  fun w => (∑' k : ℤ, κ (x - w + ((k : ℝ) * P, 0))) • e

/-- The `P`-periodised translate of `ρ` (a phase test). -/
def shiftTest (P : ℝ) (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (e : CVec3) :
    ℝ × Space → CVec3 :=
  shiftKer P (ρ.normed volume) x e

/-- The periodised kernel of `⟪(μ + L₀)Ψ, ·⟫`: `(μ + L₀)(shiftTest ρ x e) = shiftKer testKer`, where
the `w`-dependence of `testKer` enters only through `x - z`, `z = x - w + (kP, 0)`. -/
def shiftTestOp (P ν μ : ℝ) (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (e : CVec3) :
    ℝ × Space → CVec3 :=
  fun w => (∑' k : ℤ, testKer ν μ ρ x (x - w + ((k : ℝ) * P, 0))) • e

/-! ## The ingredients (each a `Prop`; hypotheses `0 < P`, `P ≤ 1`, `0 < ν` as needed) -/

/-- (A) Differentiation under the integral (source 1556-1583): `ρ ⋆ Φ` is smooth and
`(μ + L₀ᵗ)(ρ ⋆ Φ)(x) = ∫ adjKer ρ ν μ x z • Φ(x - z) dz` for `Φ ∈ Y_2` (locally integrable,
the kernels have compact support); this includes that `ρ ⋆` commutes with `∂_τ` and `Δ`. -/
def MollKernelAdj : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space),
      L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x = ∫ z, adjKer ν μ ρ x z • Φ (x - z)

/-- (B1) The periodised translate of `ρ` is a phase test (smooth, `P`-periodic, `y`-compact). -/
def ShiftTestPhase : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (e : CVec3),
    IsPhaseTest P (shiftTest P ρ x e)

/-- (B2) Unfolding of the pairing for a periodised kernel (`Φ` is `P`-periodic, so the sum over
translates unfolds the `τ`-cell `(0, P]` to `ℝ`): for a smooth compactly supported kernel `κ`,
`⟪shiftKer κ x e, F⟫ = P⁻¹ e · ∫ κ(z) F(x - z) dz` for every `F ∈ Y_2` (`P⁻¹` from the
normalised cell average in `phaseInt`). -/
def ShiftPairUnfold : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ κ : ℝ × Space → ℝ, ContDiff ℝ ∞ κ → HasCompactSupport κ →
    ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      ∀ (x : ℝ × Space) (e : CVec3),
        pairF P (shiftKer P κ x e) F = (P⁻¹ : ℂ) * dotL e (∫ z, κ z • F (x - z))

/-- (B3) The operator on the periodised translate (a computation with the definitions of `L₀`,
`T₀`, `radialT`, `lapT`: `∂_τ`, `Δ` commute with the periodisation and the shift `w ↦ x - w` flips
the sign of derivatives; `y·∇` acts on `w.2 = x.2 - z.2`):
`(μ + L₀)(shiftTest ρ x e) = shiftTestOp ρ ν μ x e`. -/
def ShiftTestOpEq : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (e : CVec3),
    (fun w => L0 ν (shiftTest P ρ x e) w + (μ : ℂ) • shiftTest P ρ x e w) =
      shiftTestOp P ν μ ρ x e

/-- (B4) `testKer` is smooth with compact support (as `ρ.normed volume` is), so (B2) applies. -/
def TestKerSmooth : Prop :=
  ∀ (ν μ : ℝ) (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space),
    ContDiff ℝ ∞ (testKer ν μ ρ x) ∧ HasCompactSupport (testKer ν μ ρ x)

/-- (E) Pointwise kernel identity `adjKer - testKer = ½ kap` (`(3/2) ρ + ½ z·∇_y ρ`). -/
def KernelIdentity : Prop :=
  ∀ (ν μ : ℝ) (ρ : ContDiffBump (0 : ℝ × Space)) (x z : ℝ × Space),
    adjKer ν μ ρ x z - testKer ν μ ρ x z = (1 / 2 : ℝ) * kap ρ z

/-- (F) Splitting of the integrals: for `F ∈ Y_2` the three integrals `∫ adjKer F`, `∫ testKer F`,
`∫ ½ kap F` (all compactly supported smooth kernels against a locally integrable field) exist, so
`∫ testKer • F(x - z) = ∫ adjKer • F(x - z) - commK ρ F x`. -/
def MollIntegralSplit : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
    ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space),
      ∫ z, testKer ν μ ρ x z • F (x - z) =
        (∫ z, adjKer ν μ ρ x z • F (x - z)) - commK ρ F x

/-- (G) `ρ ⋆ g` for the pairing with the periodised bump: unfolding is (B2) with `κ = ρ.normed`
(smoothness and compact support of `ρ.normed volume`), recorded as a separate fact. -/
def NormedBumpSmooth : Prop :=
  ∀ ρ : ContDiffBump (0 : ℝ × Space),
    ContDiff ℝ ∞ (ρ.normed volume) ∧ HasCompactSupport (ρ.normed volume)

/-- (c) Friedrichs bound (source 1556-1583): the commutator is bounded on `Y_2` by an absolute
constant, independent of `ρ` (kernel `½ div_y(zρ)` has `L¹` norm `≤ C`: layer-cake decomposition
of the monotone profile into normalised cube indicators, each with total variation of
`div_y(z 1_Q)/|Q|` at most `C`; Young's inequality in `y`, `τ`, using `Φ` `P`-periodic). -/
def FriedrichsBound : Prop :=
  ∀ (P : ℝ), 0 < P → P ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ContDiffBump (0 : ℝ × Space)),
    ρ.rOut = 2 * ρ.rIn → ∀
    (F : ℝ × Space → CVec3), UnforcedLeray.Short.IIb.IsInYr P 2 F →
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (commK ρ F) ≤
        ENNReal.ofReal C * UnforcedLeray.Short.IIb.phaseLpNorm P 2 F

/-- (d) Vanishing on tests: for a phase test `Ψ`, `‖commK ρ Ψ‖_{Y_2} → 0` as `rOut → 0`
(`∫ ½ kap(z)(Ψ(x - z) - Ψ(x)) dz = -½ ∫ ρ z·∇_yΨ(x - z) dz`, bounded by `rOut ‖∇Ψ‖_∞` on the
compact `y`-support). -/
def CommTestLimit : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest P Ψ →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ContDiffBump (0 : ℝ × Space), ρ.rOut < δ →
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (commK ρ Ψ) < ENNReal.ofReal ε

/-- (e) Density: every `Φ ∈ Y_2` is a `Y_2`-limit of phase tests (the difference is in `Y_2`). -/
def PhaseTestDense : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    ∀ η : ℝ, 0 < η → ∃ Ψ : ℝ × Space → CVec3, IsPhaseTest P Ψ ∧
      UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => Φ x - Ψ x) ∧
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => Φ x - Ψ x) < ENNReal.ofReal η

/-- (f) Linearity of `commK` against a `Y_2` field and a test (both locally integrable, kernel
bounded with compact support). -/
def CommSub : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ Ψ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
    IsPhaseTest P Ψ → ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space),
      commK ρ Φ x = commK ρ (fun w => Φ w - Ψ w) x + commK ρ Ψ x

/-- (g) Measurability of the commutator of a `Y_2` field or of a test. -/
def CommMeas : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (F : ℝ × Space → CVec3),
    (UnforcedLeray.Short.IIb.IsInYr P 2 F ∨ IsPhaseTest P F) →
      AEStronglyMeasurable (commK ρ F) volume

end UnforcedLeray.Short.PartIIIb.Concrete
