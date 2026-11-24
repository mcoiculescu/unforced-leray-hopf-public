import UnforcedLeray.Units.B0418
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.Bridge
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.Laplace

/-!
# Part II-a, task `PartII-a:F02`: the body resolvent solves `(μ + L₀)R_μ f = f` (conditional)

Source of record: `the November 2 reference manuscript`, lines 1363-1370
("The heat-dilation formula gives a distributional inverse
`S(t)h(y) = e^{t/2}[e^{ν(e^t-1)Δ}h](e^{t/2}y)`, `R_μ f(τ) = ∫₀^∞ e^{-μt}S(t)f(τ-t) dt`").

## What is proved in this file

`bodyResolvent_solves_of_sub`: the target, conditional on the single Prop `FreeTestGenAll`,
the generator of the free similarity semigroup `S_ν` on phase tests, by duality:
`s⁻¹(⟪Φ, S_ν(s)x⟫ - ⟪Φ, x⟫) → ⟪A^tΦ, x⟫` with `A^t = νΔ - ½ y·∇ - 1`. The reduction uses the
repaired Laplace-transform argument `F02.hasPhaseOp_laplace`
(`Tasks/F02BodyResolventEquation/Laplace.lean`) and the packaging of `𝒯` as an exponentially
bounded semigroup (`Tasks/F02BodyResolventEquation/Bridge.lean`).

## The chain of leaf Props below `FreeTestGenAll` (proved by the tasks `PartII-a:F02/1`-`F02/11`)

The semigroup acts on tests by the explicit adjoint
`S'_ν(s)u(y) = e^{-s}[e^{ν(1-e^{-s})Δ}u](e^{-s/2}y)` (`adjFree`), because
`⟪u, S_ν(s)h⟫ = ⟪S'_ν(s)u, h⟫` (heat self-adjoint, plus the change of variables `z = e^{s/2}y` and
`D_b H_t = H_{b²t} D_b`).

```
FreeTestGenAll
  <= PhaseAdjointTaylor                       (task F02/11)
       <= ComplexAdjointOp                    (task F02/8)   <= AdjointFormula       (task F02/3)
       <= SliceTaylor                         (task F02/9)   <= AdjointTaylor        (task F02/7)
  AdjointFormula  <= HeatSymmetricLp (F02/1), DilationDual (F02/2)
  AdjointTaylor   <= HeatTaylor2 (F02/4), DilationTaylor1 (F02/5), DilationTaylor2 (F02/6)
```
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-! ### The real adjoint of the free similarity semigroup -/

/-- The adjoint `S'_ν(s)` of `S_ν(s)` on real spatial fields (tex line 1366, transposed):
`S'_ν(s)u(y) = e^{-s} [e^{ν(1-e^{-s})Δ}u](e^{-s/2} y)`. -/
def adjFree (ν s : ℝ) (u : SpatialField) : SpatialField :=
  SpatialScaling.spatialScale (Real.exp (-s)) (Real.exp (-s / 2))
    (Heat.flow u (ν * (1 - Real.exp (-s))))

/-- The transposed generator `A^t u = νΔu - ½ y·∇u - u` on real spatial fields
(the real-field form of `genT`). -/
def adjGen (ν : ℝ) (u : SpatialField) : SpatialField :=
  fun y => ν • B0418.vecLaplacian u y - (1 / 2 : ℝ) • fderiv ℝ u y y - u y

/-- The complexification of `adjFree` to `ℂ³`-valued fields, acting on real and imaginary parts
(the same convention as `B0421.coeFn_freeC`). -/
def adjC (ν s : ℝ) (v : Space → CVec3) : Space → CVec3 := fun y =>
  ofReV (adjFree ν s (fun z => reV (v z)) y) + ofImV (adjFree ν s (fun z => imV (v z)) y)

/-! ### Leaf Props of the spatial analysis -/

/-- **Heat flow is symmetric on `L^p × L^{p'}`** (task `PartII-a:F02/1`): the Gaussian is even, so
`∫ ⟪u, e^{tΔ}h⟫ = ∫ ⟪e^{tΔ}u, h⟫` (Fubini and the substitution `w ↦ -w`), `t ≥ 0`. -/
def HeatSymmetricLp : Prop :=
  ∀ (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q], p ≠ ⊤ → q ≠ ⊤ → ∀ t : ℝ, 0 ≤ t →
    ∀ u h : SpatialField, MemLp u p volume → MemLp h q volume →
      ∫ y, inner ℝ (u y) (Heat.flow h t y) = ∫ y, inner ℝ (Heat.flow u t y) (h y)

/-- **Dilations under the pairing** (task `PartII-a:F02/2`): for `b > 0`,
`∫ ⟪u(y), a h(b y)⟫ dy = a b⁻³ ∫ ⟪u(b⁻¹ z), h(z)⟫ dz` (the substitution `z = b y`; no
integrability is needed, `Measure.integral_comp_smul`). -/
def DilationDual : Prop :=
  ∀ (a b : ℝ), 0 < b → ∀ u h : SpatialField,
    ∫ y, inner ℝ (u y) (SpatialScaling.spatialScale a b h y) =
      a * (b ^ 3)⁻¹ * ∫ z, inner ℝ (u (b⁻¹ • z)) (h z)

/-- **The adjoint formula** (task `PartII-a:F02/3`): `⟪u, S_ν(r)h⟫ = ⟪S'_ν(r)u, h⟫` for
`u ∈ L^p`, `h ∈ L^q`, `1/p + 1/q = 1`, `1 < q < ∞`, `ν, r ≥ 0`, where
`S_ν(r) = AncientLocalization.freeEvolution ν r` (tex line 1366). -/
def AdjointFormula : Prop :=
  ∀ (ν r : ℝ), 0 ≤ ν → 0 ≤ r → ∀ (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q], p ≠ ⊤ → q ≠ ⊤ →
    ∀ u h : SpatialField, MemLp u p volume → MemLp h q volume →
      ∫ y, inner ℝ (u y) (AncientLocalization.freeEvolution ν r h y) =
        ∫ y, inner ℝ (adjFree ν r u y) (h y)

/-- **Second-order Taylor bound for the heat flow of a `C_c^∞` field** (task `PartII-a:F02/4`):
`‖e^{σΔ}w - w - σΔw‖_p ≤ (σ²/2) ‖Δ²w‖_p`. Proof: `e^{σΔ}w - w - σΔw
= ∫₀^σ ∫₀^s e^{s'Δ}Δ²w ds' ds` (`B0418.flow_sub_eq_integral` twice), then Minkowski's integral
inequality and the `L^p`-contraction `B0418.eLpNorm_flow_le`. -/
def HeatTaylor2 : Prop :=
  ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∀ w : SpatialField, ContDiff ℝ ∞ w → HasCompactSupport w →
    ∀ σ : ℝ, 0 ≤ σ →
      eLpNorm (fun y => Heat.flow w σ y - w y - σ • B0418.vecLaplacian w y) p volume ≤
        ENNReal.ofReal (σ ^ 2 / 2) *
          eLpNorm (B0418.vecLaplacian (B0418.vecLaplacian w)) p volume

/-- **First-order dilation bound** (task `PartII-a:F02/5`): for `w ∈ C^∞` supported in
`‖y‖ ≤ R` with `‖∇w‖ ≤ M` and `b ∈ [1/2, 1]`, `‖w(b·) - w‖_p ≤ C M (1-b)` with `C` depending only
on `R, p`. -/
def DilationTaylor1 : Prop :=
  ∀ (R : ℝ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : ℝ) (w : SpatialField), ContDiff ℝ ∞ w → (∀ y, R < ‖y‖ → w y = 0) →
      (∀ y, ‖fderiv ℝ w y‖ ≤ M) → ∀ b : ℝ, 1 / 2 ≤ b → b ≤ 1 →
        eLpNorm (fun y => w (b • y) - w y) p volume ≤ ENNReal.ofReal (C * M * (1 - b))

/-- **Second-order dilation bound** (task `PartII-a:F02/6`): for `w ∈ C^∞` supported in
`‖y‖ ≤ R` with `‖∇²w‖ ≤ M` and `b ∈ [1/2, 1]`,
`‖w(b·) - w - (b-1) y·∇w‖_p ≤ C M (1-b)²` with `C` depending only on `R, p`. -/
def DilationTaylor2 : Prop :=
  ∀ (R : ℝ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : ℝ) (w : SpatialField), ContDiff ℝ ∞ w → (∀ y, R < ‖y‖ → w y = 0) →
      (∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ M) → ∀ b : ℝ, 1 / 2 ≤ b → b ≤ 1 →
        eLpNorm (fun y => w (b • y) - w y - (b - 1) • fderiv ℝ w y y) p volume ≤
          ENNReal.ofReal (C * M * (1 - b) ^ 2)

/-- **Quantitative second-order generator bound for the adjoint** (task `PartII-a:F02/7`): for
a smooth real field `u` supported in `‖y‖ ≤ R` whose derivatives (the six quantities below) are
bounded by `M`, and `0 < r ≤ 1`,
`‖S'_ν(r)u - u - r A^t u‖_p ≤ C M r²`, with `C` depending only on `ν, R, p`. -/
def AdjointTaylor : Prop :=
  ∀ (ν R : ℝ) (p : ℝ≥0∞), 0 < ν → 1 ≤ p → p ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : ℝ) (u : SpatialField), ContDiff ℝ ∞ u → (∀ y, R < ‖y‖ → u y = 0) →
      (∀ y, ‖u y‖ ≤ M ∧ ‖fderiv ℝ u y‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ M ∧
        ‖B0418.vecLaplacian u y‖ ≤ M ∧ ‖fderiv ℝ (B0418.vecLaplacian u) y‖ ≤ M ∧
        ‖B0418.vecLaplacian (B0418.vecLaplacian u) y‖ ≤ M) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        eLpNorm (fun y => adjFree ν r u y - u y - r • adjGen ν u y) p volume ≤
          ENNReal.ofReal (C * M * r ^ 2)

/-! ### Leaf Props of the lift to complex fields and to the phase space -/

/-- **The complex adjoint as a bounded operator** (task `PartII-a:F02/8`): for `1 < q < ∞`,
`ν, s ≥ 0`, there is a bounded `ℂ`-linear operator `A` on `L^{q'}(ℝ³; ℂ³)` which represents
`adjC ν s` on every representative and satisfies `⟪A g, h⟫ = ⟪g, S_ν(s) h⟫` for the complexified
semigroup `B0421.freeC` (`A = B0421.cx (adjSemigroupLp)`, `adjSemigroupLp` the real operator
built from `adjFree` exactly as `B0418.freeSemigroupLp` is built from `freeEvolution`). -/
def ComplexAdjointOp : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤), 1 < q → ∀ ν s : ℝ, 0 ≤ ν → 0 ≤ s →
    ∃ A : Lp CVec3 (conjExp q) (volume : Measure Space) →L[ℂ]
        Lp CVec3 (conjExp q) (volume : Measure Space),
      (∀ (g : Lp CVec3 (conjExp q) (volume : Measure Space))
          (h : Lp CVec3 q (volume : Measure Space)),
        innerPair q (A g) h = innerPair q g (B0421.freeC hq ν s h)) ∧
      (∀ (g : Lp CVec3 (conjExp q) (volume : Measure Space)) (v : Space → CVec3),
        (g : Space → CVec3) =ᵐ[volume] v → (A g : Space → CVec3) =ᵐ[volume] adjC ν s v)

/-- **Uniform second-order bound on the slices of a phase test** (task `PartII-a:F02/9`): for a
phase test `Φ`, `ν > 0` and `1 ≤ p < ∞` there is `C` with
`‖adjC ν s (Φ(t,·)) - Φ(t,·) - s (genT ν Φ)(t,·)‖_p ≤ C s²` for all phases `t ∈ ℝ` and
`0 < s ≤ 1`. -/
def SliceTaylor : Prop :=
  ∀ (ν : ℝ) (p : ℝ≥0∞) (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3), 0 < ν → 1 ≤ p → p ≠ ⊤ →
    IsPhaseTest P Φ → ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, 0 < s → s ≤ 1 →
      eLpNorm (fun y => adjC ν s (fun z => Φ (t, z)) y - Φ (t, y) -
        (s : ℂ) • F02.genT ν Φ (t, y)) p volume ≤ ENNReal.ofReal (C * s ^ 2)

/-- **The adjoint of the phase semigroup on a phase test** (task `PartII-a:F02/10`): for each
phase test `Φ` and `0 < s ≤ 1` there is `ψ_s ∈ Y_{r'}` representing
`x ↦ ⟪Φ, S_ν(s)x⟫` on `Y_r`, and `‖ψ_s - Φ - s A^tΦ‖_{Y_{r'}} ≤ C s²`. -/
def PhaseAdjointTaylor : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (_ : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (nu : ℝ),
    0 < nu → ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ ψs : Yq P (conjExp r),
        (∀ x : Yq P r, phasePair P r Φ ((B0421.freeC (ne_top_of_lt h3) nu s).compLpL r
            AddCircle.haarAddCircle x) = phasePairing P r ψs x) ∧
        ‖ψs - testElem P (conjExp r) Φ - (s : ℂ) • testElem P (conjExp r) (F02.genT nu Φ)‖ ≤
          C * s ^ 2

/-! ### The generator of the free semigroup on phase tests -/

/-- **The generator identity of `S_ν` on phase tests, by duality** (task `PartII-a:F02/11`):
`F02.FreeTestGenerator` (`s⁻¹(⟪Φ, S_ν(s)x⟫ - ⟪Φ, x⟫) → ⟪A^tΦ, x⟫`, `A^t = νΔ - ½ y·∇ - 1`) for
`1 < r < 3`, `ν > 0`, every period `P > 0`. -/
def FreeTestGenAll : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (_ : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (nu : ℝ),
    0 < nu → F02.FreeTestGenerator P r (ne_top_of_lt h3) nu

/-- **`PartII-a:F02`, conditional on the generator identity on phase tests**: the Laplace
integral `Rm f = ∫₀^∞ e^{-μt} 𝒯(t) f dt` (the same hypotheses as `PartII-a:F01`) satisfies
`(μ + L₀)Rm f = f` in distributions (source lines 1363-1370). -/
theorem bodyResolvent_solves_of_sub (hG : FreeTestGenAll) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (h1 : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (nu : ℝ) (hnu : 0 < nu) (mu : ℂ)
    (hmu : 0 < mu.re + gammaR r) (Rm : Yq P r →L[ℂ] Yq P r)
    (hRm : ∀ f, Rm f = ∫ t in Set.Ioi (0:ℝ),
      Complex.exp (-(mu * t)) • B0421.phaseT (ne_top_of_lt h3) nu t f)
    (f : Yq P r) :
    HasPhaseOp (fun Phi => mu • Phi + B0411.L0T nu Phi) (Rm f) f :=
  bodyResolvent_solves_of_laplace r h3 P nu hnu mu hmu
    (fun _ hμ h => F02.hasPhaseOp_laplace (ne_top_of_lt h3) hnu.le (hG r h1 h3 P nu hnu)
      (bodySemigroup r h3 P nu hnu.le) (fun t => bodySemigroup_T r h3 P nu hnu.le t) hμ h)
    Rm hRm f

end UnforcedLeray.Short.PartIIa
