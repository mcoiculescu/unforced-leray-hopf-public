import UnforcedLeray.Cons.L2.CanonicalBranch
import UnforcedLeray.Units.B0122
import UnforcedLeray.Units.B0123

/-!
# Spine: `Cons.G3b.ClassicalRegularityHyp` (task `Spine:SP-CAN/4`, blueprint B0124)

Source of record: `the November 2 reference manuscript`, line 1086 ("It is bounded in
`X_G` as `θ ↓ 0` and smooth for positive `θ`") and lines 1134-1145 (the `X_{G,j}` spaces: graph norm
equivalence, `L : X_{G,j} → X_{G,j}` bounded, one-derivative heat gain
`‖e^{aD}‖_{X_{G,j}→X_{G,j+1}} ≤ C_j a^{-1/2}`), together with the old manuscript `paper/main.tex`
lines 1856-1888 (`eq:st18-t00100`-`t00102`: "The local argument gives smoothness for positive `θ`").

`Cons.G3b.ClassicalRegularityHyp` (`Cons/L2/CanonicalBranch.lean:314`) says: every mild solution
`V(θ) = S(θ, θ')V(θ')` (`0 < θ ≤ θ'`) of the concrete backward evolution has a representative `W`
that is jointly `C^∞` on `(0, ∞)²` and solves `-∂_θ W = L₀ W + θ⁻¹ D W` pointwise, with the classical
`generatorL0` and `oscillatorD`. The proof has five independent steps, each stated below as a
precise `Prop` (a true source fact):

1. `MildSpatialSmoothing` (smoothing). A mild `V` takes values in every `X_{G,j}` for `θ > 0` and is
   continuous into each `X_{G,j}`. Route: the Dyson series of `S(θ, θ')` over the free family
   `e^{log(θ'/θ) D}` converges in `X_{G,j}`, because `L₀` is bounded on `X_{G,j}`
   (`B0122.L0_mem_XGj_norm`, under `GreenEllipticRegularity j`), and `e^{aD} : X_{G,j} → X_{G,j+1}`
   with norm `≤ C_j a^{-1/2}` (`B0123.expD_smoothing`); iterate `j` times on subintervals of
   `[θ, θ']`, starting from `V θ' ∈ X_G`, using `V θ = S θ θ'' (V θ'')` at a smaller time
   (`S_comp`).
2. `MildIsStrong` (strong equation). A mild `V` satisfies `V θ ∈ 𝒟(D)` and
   `-V' = L₀ V + θ⁻¹ D V` in `X_G` for `θ > 0` (differentiate the Duhamel identity of `S_mild`,
   using step 1 with `j = 2`, `X_{G,2} = 𝒟(D)`: `B0123.XGj_two`).
3. `StrongBootstrap` (time regularity). Continuity into all `X_{G,j}` plus the strong equation
   give `C^∞` into all `X_{G,j}`: `V' = -(L₀ + θ⁻¹D)V` and `D : X_{G,j+2} → X_{G,j}`,
   `L₀ : X_{G,j} → X_{G,j}` are bounded, so each derivative gains one order in time.
4. `SobolevJointSmooth` (Sobolev embedding, INF08). A curve that is `C^∞` into every `X_{G,j}` has
   a jointly `C^∞` representative on `(0, ∞)²` (`X_{G,j}` is the Gaussian-weighted Sobolev space,
   `B0121.mem_XGj_iff_weakDerivs`; Sobolev embedding in the planar variable, with the parameter).
5. `SmoothRepresentativeEquation` (pointwise form). For a jointly smooth representative the
   `X_G` equation is the classical pointwise equation: the `X_G`-derivative of `V` is a.e. the
   pointwise `θ`-derivative of `W`, `L₀` acts by `generatorL0`
   (`Cons.G3b.generatorL0_eq_L0Fun`), and `D` acts on a `C²` representative by `oscillatorD`
   (as in `PlanarSpectral.exists_modeVort_Ddomain_action`); a.e. equality of two functions
   continuous on `(0, ∞)` is equality.

`classicalRegularityHyp_of` assembles them. The elliptic regularity input
`GreenAll` (`B0122.GreenEllipticRegularity j` for all `j`, task `PartI:C09`) is carried as an
explicit hypothesis of steps 1-3 so that those lemmas are provable independently of `PartI:C09`; the
unconditional `classicalRegularityHyp` (`Short/Spine/Proofs/CanonicalBranch/Regularity.lean`)
supplies it from `Short.PartI.greenEllipticRegularity`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- Global elliptic regularity of the Green inverse, of every order `j`
(`B0122.GreenEllipticRegularity j`; old manuscript line 1869; task `PartI:C09`). It makes `L₀`
bounded on every `X_{G,j}` (`B0122.L0_mem_XGj_norm`). -/
def GreenAll : Prop := ∀ j : ℕ, B0122.GreenEllipticRegularity j

/-- `V` is a mild solution on `(0, ∞)`: `V(θ) = S(θ, θ')V(θ')` for `0 < θ ≤ θ'`. This is exactly the
hypothesis of `ClassicalRegularityHyp`. -/
def IsMildOnPos (V : ℝ → XG) : Prop :=
  ∀ θ θ' : ℝ, 0 < θ → θ ≤ θ' → V θ = S θ θ' (V θ')

/-- `V(θ) ∈ X_{G,j}` for all `θ > 0` and every `j`, and `θ ↦ (I - D)^{j/2} V(θ)` is continuous on
`(0, ∞)` into `X_G`. Together with the continuity of `V` itself (`j = 0`), this is continuity of `V`
into each `X_{G,j}` for its graph norm `‖f‖² + ‖(I - D)^{j/2} f‖²`. `U` records the curve
`(I - D)^{j/2} V(θ)` as a total function. -/
def IsXGjContinuous (V : ℝ → XG) : Prop :=
  ∀ j : ℕ, ∃ U : ℝ → XG,
    (∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j, B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ) ∧
    ContinuousOn U (Ioi 0)

/-- `V` is a `C^∞` curve into every `X_{G,j}` on `(0, ∞)`: as `IsXGjContinuous`, with
`U = (I - D)^{j/2} V` of class `C^∞` into `X_G` (the case `j = 0` says `V` itself is `C^∞`
into `X_G`). The graph norm of `X_{G,j}` is `‖f‖ + ‖(I - D)^{j/2} f‖` up to constants, so this is
`C^∞` into `X_{G,j}` for each `j`. -/
def IsSmoothAllXGj (V : ℝ → XG) : Prop :=
  ∀ j : ℕ, ∃ U : ℝ → XG,
    (∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0123.XGj j, B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ = U θ) ∧
    ContDiffOn ℝ ∞ U (Ioi 0)

/-- `V` is a strong solution of `-V' = L₀ V + θ⁻¹ D V` in `X_G` on `(0, ∞)`: `V(θ) ∈ 𝒟(D)` and `V`
is differentiable into `X_G` with derivative `-(L₀ V(θ) + θ⁻¹ D V(θ))`. -/
def IsStrongOnPos (V : ℝ → XG) : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ h : V θ ∈ B0094.D.domain,
    HasDerivAt V (-(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩)) θ

/-- **Step 1, smoothing** (shorter proof lines 1134-1145; old manuscript 1867-1888, B0122-B0124):
a mild solution takes values in every `X_{G,j}` for `θ > 0` and is continuous into each. -/
def MildSpatialSmoothing : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsMildOnPos V → IsXGjContinuous V

/-- **Step 2, strong equation** (shorter proof line 1086; old manuscript lines 1879-1888): a mild
solution is a strong solution of `-V' = L₀V + θ⁻¹DV` on `(0, ∞)`. -/
def MildIsStrong : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsMildOnPos V → IsStrongOnPos V

/-- **Step 3, time regularity** (old manuscript lines 1879-1888): a strong solution that is
continuous into every `X_{G,j}` is `C^∞` into every `X_{G,j}` (differentiate the equation:
`V' = -(L₀ + θ⁻¹D)V` with `L₀` bounded on `X_{G,j}` and `D : X_{G,j+2} → X_{G,j}` bounded). -/
def StrongBootstrap : Prop :=
  GreenAll → ∀ V : ℝ → XG, IsXGjContinuous V → IsStrongOnPos V → IsSmoothAllXGj V

/-- **Step 4, Sobolev embedding** (INF08; `X_{G,j}` is the Gaussian-weighted Sobolev space of
order `j`, `B0121.mem_XGj_iff_weakDerivs`): a curve that is `C^∞` into every `X_{G,j}` has a
representative `W` (`W θ = V θ` a.e. for every `θ > 0`) that is jointly `C^∞` in `(θ, r)` on
`(0, ∞)²`. -/
def SobolevJointSmooth : Prop :=
  ∀ V : ℝ → XG, IsSmoothAllXGj V →
    ∃ W : ℝ → Profile, (∀ θ : ℝ, 0 < θ → W θ =ᵐ[xGMeasure] (V θ : ℝ → ℂ)) ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0)

/-- **Step 5, pointwise equation** (identification of `D` and `L₀` with their classical formulas,
`generatorL0_eq_L0Fun`; `D = Δ + ½ y·∇ + 2` acts on a `C²` representative of an element of `𝒟(D)`
by `oscillatorD`): for a strong solution that is `C^∞` into every `X_{G,j}`, every jointly smooth
representative `W` solves `-∂_θ W = L₀ W + θ⁻¹ D W` pointwise on `(0, ∞)²`. -/
def SmoothRepresentativeEquation : Prop :=
  ∀ V : ℝ → XG, IsStrongOnPos V → IsSmoothAllXGj V →
    ∀ W : ℝ → Profile, (∀ θ : ℝ, 0 < θ → W θ =ᵐ[xGMeasure] (V θ : ℝ → ℂ)) →
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0) →
      ∀ θ : ℝ, 0 < θ → ∀ r : ℝ, 0 < r →
        -deriv (fun t => W t r) θ = generatorL0 (W θ) r + (θ : ℂ)⁻¹ * oscillatorD (W θ) r

/-- **`ClassicalRegularityHyp` from the five regularity steps and global elliptic regularity.**
Mildness gives continuity into all `X_{G,j}` (step 1) and the strong equation (step 2); the
bootstrap (step 3) gives `C^∞` into all `X_{G,j}`; Sobolev embedding (step 4) gives the jointly
smooth representative, and step 5 identifies the equation. -/
theorem classicalRegularityHyp_of (hE : GreenAll) (h1 : MildSpatialSmoothing)
    (h2 : MildIsStrong) (h3 : StrongBootstrap) (h4 : SobolevJointSmooth)
    (h5 : SmoothRepresentativeEquation) : ClassicalRegularityHyp := by
  intro V hV
  have hc : IsXGjContinuous V := h1 hE V hV
  have hs : IsStrongOnPos V := h2 hE V hV
  have hsm : IsSmoothAllXGj V := h3 hE V hc hs
  obtain ⟨W, hWV, hWs⟩ := h4 V hsm
  exact ⟨W, hWV, hWs, h5 V hs hsm W hWV hWs⟩

end UnforcedLeray.Short.Spine
