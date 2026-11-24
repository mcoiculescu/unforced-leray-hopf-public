import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4
import UnforcedLeray.Lib.CylinderB.Leray

/-!
# Part III-a, task `PartIII-a:T18/2/4/2`: Leray projection of the slices (conditional)

Target (`Sub/T18_2_4.lean`): `LerayProjectSlices`. For `c > 0` and a globally smooth, `c`-periodic
`u` with locally uniform Gaussian decay in `η` there is a jointly measurable `(b, G)` with the
clauses of `IsLerayProjection`: `b(s) = 𝒫₀ u(s)` (on real and imaginary parts), `G(s)_{ij} =
(𝒫₀ ∂_j u(s))_i`.
Source of record: `the November 2 reference manuscript`, lines 3427-3440 ("start
from zero at `s = δ`, let `δ ↓ 0`"; the free instance of the energy argument, with the
Leray projection `𝒫₀` of the cylinder).



Seven independent facts are missing from the library (the translation commutation of `𝒫₀` exists
in `Lib/TrainB/P0Horizontal.lean`, `Lib/TrainB/P0Translation.lean`, `Lib/HeatCylinder/P0PlaneShift.lean`;
the header of `Lib/CylinderB/Leray.lean` is stale on that point). They are stated below as `Prop`s
about *explicit* objects: `toL2v` (the `L²(cell; ℝ²)` class of a real vector field, `0` if it is not
in `L²`), `P0re f`, `P0im f` (the classes of `𝒫₀` applied to the real and the imaginary part of
`f`), `P0C f` (the `ℂ²`-valued function with these two parts), `uSl u s` (the slice `u(s, ·)`) and
`duSl u s j` (the slice of `∂_j u`).

## Decomposition

1. (*Joint measurable representative*, `JointRepVecC`) two `L²`-valued paths continuous on
   `(0, ∞)` have a jointly measurable `ℂ²`-valued representative that represents the pair at
   **every** age `t > 0` (`Infra/JointMeasurableRep.lean`).
2. (*Continuity of the projected slices*, `LerayClassCont`) `s ↦ 𝒫₀ u(s)`, `s ↦ 𝒫₀ ∂_j u(s)` are
   continuous into `L²` (Gaussian dominated convergence; `𝒫₀` is a bounded operator).
3. (*Local energy bound*, `LerayClassEnergy`) `‖𝒫₀ u(s)‖² + ‖𝒫₀ ∇u(s)‖²` is bounded uniformly for
   `s ≤ s₂` (`‖𝒫₀‖ ≤ 1` and the Gaussian bound).
4. (*Divergence free*, `P0DivFreeC`) `𝒫₀ f ∈ divFree` against `B0579.IsCylTest` tests.
5. (*Orthogonality*, `P0OrthC`) `𝒫₀ f - f` is orthogonal to every smooth divergence-free test field.
6. (*Commutation with weak derivatives*, `P0CommWeakC`) `∂_j 𝒫₀ f = 𝒫₀ ∂_j f` weakly.
7. (*Slice integrability*, `GaussianSliceMemLp`) the slices of `u` and `∂_j u` are in `L²(cell)`.
8. (*Classical to weak*, `SmoothSliceWeak`) the classical derivative of a slice is its weak
   derivative on the cylinder.

Proved here: `lerayProjectSlices_of` (the wiring): apply `JointRepVecC` to the continuous paths of
item 2, set `b = 0`, `G = 0` on the closed set `Z` of ages with `u(s) ≡ 0` (this gives the `zero`
clause with no projection argument), transfer the slice clauses of items 4-8 along the a.e.
identification, and obtain `energyLoc` by Tonelli from item 3.
The unconditional leaves are queued as tasks `PartIII-a:T18/2/4/2/1 ... /8`; two more tasks
provide facts used inside leaves: `/9` (`TestBridge`, used by `/4`, `/5`, `/10`) and `/10`
(`P0CommWeakL2`, the real `H¹` form of item 6, used by `/6`; it is built on the existing
`TrainB.hasWeakDeriv_P0_q_of_vecH1`, `TrainB.hasWeakDeriv_P0_eta_of_vecH1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Definitions -/

/-- The hypotheses of `LerayProjectSlices` on the family `u`: every component is jointly smooth,
`c`-periodic in `q`, with locally uniform Gaussian decay in `η`. -/
structure NiceSlices (c : ℝ) (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => u p i
  periodic : ∀ s x i, u (s, (x.1 + c, x.2)) i = u (s, x) i
  decay : GaussianDecayLoc u

open scoped Classical in
/-- The class in `L²(cell; ℝ²)` of a real vector field on the plane (`0` if it is not in `L²`). -/
def toL2v (c : ℝ) (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) : UnforcedLeray.Cyl.L2v c :=
  if h : MemLp f 2 (UnforcedLeray.Cyl.cellμ c) then h.toLp f else 0

/-- The real part `(Re f₀, Re f₁)` of a `ℂ²`-valued field, as a field with values in `ℝ²`. -/
def reVec (f : ℝ × ℝ → Fin 2 → ℂ) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2 :=
  fun x => UnforcedLeray.Cyl.vec (f x 0).re (f x 1).re

/-- The imaginary part `(Im f₀, Im f₁)` of a `ℂ²`-valued field, as a field with values in `ℝ²`. -/
def imVec (f : ℝ × ℝ → Fin 2 → ℂ) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2 :=
  fun x => UnforcedLeray.Cyl.vec (f x 0).im (f x 1).im

/-- The slice `u(s, ·)` of a family of `ℂ²`-valued fields. -/
def uSl (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (s : ℝ) : ℝ × ℝ → Fin 2 → ℂ :=
  fun x => u (s, x)

/-- The slice of the classical derivative `∂_j u`, `(∂_j u)_i = pdC j (u_i(s, ·))`. -/
def duSl (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (s : ℝ) (j : Fin 2) : ℝ × ℝ → Fin 2 → ℂ :=
  fun x i => pdC j (fun y => u (s, y) i) x

/-- The `ℂ²`-valued function `a + i b` built from two classes `a, b ∈ L²(cell; ℝ²)` (through the
chosen `Lp` representatives). -/
def cplxOf (c : ℝ) (a b : UnforcedLeray.Cyl.L2v c) : ℝ × ℝ → Fin 2 → ℂ :=
  fun x i => ((a x i : ℝ) : ℂ) + Complex.I * ((b x i : ℝ) : ℂ)

/-- The class of `𝒫₀` applied to the real part of `f`. -/
def P0re (c : ℝ) (f : ℝ × ℝ → Fin 2 → ℂ) : UnforcedLeray.Cyl.L2v c :=
  UnforcedLeray.Cyl.P0 c (toL2v c (reVec f))

/-- The class of `𝒫₀` applied to the imaginary part of `f`. -/
def P0im (c : ℝ) (f : ℝ × ℝ → Fin 2 → ℂ) : UnforcedLeray.Cyl.L2v c :=
  UnforcedLeray.Cyl.P0 c (toL2v c (imVec f))

/-- `𝒫₀ f = 𝒫₀ (Re f) + i 𝒫₀ (Im f)` as a `ℂ²`-valued function (a chosen representative). -/
def P0C (c : ℝ) (f : ℝ × ℝ → Fin 2 → ℂ) : ℝ × ℝ → Fin 2 → ℂ :=
  cplxOf c (P0re c f) (P0im c f)

/-! ## The leaf statements -/

/-- **Joint measurable representative** (`PartIII-a:T18/2/4/2/1`; SP 3427-3440; pure measure
theory). Two paths `γ₁, γ₂ : ℝ → L²(cell; ℝ²)` continuous on `(0, ∞)` have a jointly measurable
`ℂ²`-valued function `F` such that, for **every** `t > 0`, `F(t, ·) = γ₁(t) + i γ₂(t)` almost
everywhere on the cell.
Proof idea: `Infra/JointMeasurableRep.lean`, `exists_stronglyMeasurable_rep_of_continuousOn` with
`s = Ioi 0` for each of `γ₁, γ₂` (the `Lp` space is over `cellμ c = volume.restrict (cell c)`),
then take components and combine `F = F₁ + i F₂`. -/
def JointRepVecC : Prop :=
  ∀ c : ℝ, 0 < c → ∀ γ₁ γ₂ : ℝ → UnforcedLeray.Cyl.L2v c,
    ContinuousOn γ₁ (Ioi (0 : ℝ)) → ContinuousOn γ₂ (Ioi (0 : ℝ)) →
      ∃ F : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => F p i) ∧
        ∀ t : ℝ, 0 < t → ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
          ∀ i, F (t, x) i = cplxOf c (γ₁ t) (γ₂ t) x i

/-- **Continuity of the projected slices** (`PartIII-a:T18/2/4/2/2`; SP 3427-3440). For a nice
family `u`, the classes `s ↦ 𝒫₀ Re u(s)`, `𝒫₀ Im u(s)` and `s ↦ 𝒫₀ Re ∂_j u(s)`, `𝒫₀ Im ∂_j u(s)`
are continuous on `(0, ∞)` into `L²(cell; ℝ²)`.
Proof idea: `P0 c` is a continuous linear map, so it suffices that `s ↦ toL2v c (reVec (uSl u s))`
(and the three analogues) is continuous. `u` and `∂_j u` are jointly continuous (`C^∞`), bounded on
`s ≤ s₂` by `C e^{-κ η²}` (`GaussianDecayLoc`, `‖pdC j g x‖ ≤ ‖fderiv ℝ g x‖` because
`‖B0579.dir j‖ = 1` in the sup norm), and `|Re z|, |Im z| ≤ ‖z‖`; dominated convergence on the cell
(dominator `C e^{-κ η²}` is in `L²(cell)`) gives `L²` convergence of the slices as `s' → s`; use
`MemLp` (`GaussianSliceMemLp`) and the `Lp` norm formula to convert. -/
def LerayClassCont : Prop :=
  ∀ c : ℝ, 0 < c → ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, NiceSlices c u →
    ContinuousOn (fun s => P0re c (uSl u s)) (Ioi (0 : ℝ)) ∧
    ContinuousOn (fun s => P0im c (uSl u s)) (Ioi (0 : ℝ)) ∧
    ∀ j : Fin 2, ContinuousOn (fun s => P0re c (duSl u s j)) (Ioi (0 : ℝ)) ∧
      ContinuousOn (fun s => P0im c (duSl u s j)) (Ioi (0 : ℝ))

/-- **Local energy bound** (`PartIII-a:T18/2/4/2/3`; SP 3427-3440). For a nice family `u` and
every `s₂` there is `M` with `∫_cell (|𝒫₀ u(s)|² + |𝒫₀ ∇u(s)|²) ≤ M` for all `0 < s ≤ s₂`
(`vnorm2` and `tnorm2` are the Euclidean and Frobenius norms).
Proof idea: `‖P0 c‖ ≤ 1` (`Cyl.norm_P0_le`) gives `∫ |P0 g|² = ‖P0 (toL2v g)‖² ≤ ‖toL2v g‖² =
∫ |g|²` for `g ∈ L²` (the `Lp` norm formula, e.g. `MeasureTheory.L2` / `eLpNorm_eq_lintegral_rpow_enorm`)
applied to `Re u(s)`, `Im u(s)`, `Re ∂_j u(s)`, `Im ∂_j u(s)`; then `|u|² + |∇u|² ≤ 4 C² e^{-2κ η²}`
pointwise for `s ≤ s₂` and `∫_cell e^{-2κ η²} = c √(π/(2κ)) < ∞`. -/
def LerayClassEnergy : Prop :=
  ∀ c : ℝ, 0 < c → ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, NiceSlices c u → ∀ s₂ : ℝ,
    ∃ M : ℝ, ∀ s : ℝ, 0 < s → s ≤ s₂ →
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (P0C c (uSl u s) x) ^ 2 +
        tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2) ≤ ENNReal.ofReal M

/-- **`𝒫₀ f` is divergence free** (`PartIII-a:T18/2/4/2/4`; SP 3427-3440; `Cyl.P0_mem`). For every
`ℂ²`-valued field `f` (no hypothesis: `toL2v` is `0` outside `L²`) and every test `ψ`,
`∫_cell 𝒫₀f · ∇ψ = 0`.
Proof idea: `Cyl.P0_mem` and `Cyl.mem_divFree` give `⟪gradL ψ, P0 g⟫ = 0` for `Sob.IsCylTest`
tests; the bridge `B0579.IsCylTest c ψ ↔ Sob.IsCylTest c ψ` holds (the periodicity forms
`ψ (x.1 + c, x.2) = ψ x` and `ψ (x + (c, 0)) = ψ x` agree; also `B0579.pd j ψ` is the `gradT`
component `partialQ`/`partialEta`, `Cyl.partialQ_eq_fderiv`); the real pairing is the `L²` inner
product with `gradL ψ` (`Cyl.inner_toLp_left`); split the complex integral into the real and the
imaginary parts, each being such a pairing (note `B0579.cell c = Cyl.cell c`, `neg_div`). -/
def P0DivFreeC : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ × ℝ → Fin 2 → ℂ, ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c,
      (P0C c f x 0 * (B0579.pd 0 ψ x : ℂ) + P0C c f x 1 * (B0579.pd 1 ψ x : ℂ)) = 0

/-- **`𝒫₀ f - f` is orthogonal to divergence-free test fields** (`PartIII-a:T18/2/4/2/5`; SP
3427-3440; `Cyl.P0_eq_self`, `Cyl.inner_P0_comm`). For `f` with real and imaginary parts in
`L²(cell)` and a smooth, `c`-periodic, `η`-compact, pointwise divergence-free real field `Ψ`,
`∫_cell Σ_i (𝒫₀f_i - f_i) Ψ_i = 0`.
Proof idea: `Ψ` as an element of `L²v c` (it is continuous and vanishes for large `|η|`,
`Cyl.memLp_of_vanishes`) lies in `divFree c`: for a test `φ`, `∫ Ψ · ∇φ = -∫ (div Ψ) φ = 0`
(`B0579.integral_mul_pd`, `B0579.integral_pd_eq_zero`, `Units/B0579.lean` 756-812, after the bridge
`B0579.IsCylTest ↔ Sob.IsCylTest`). Hence `P0 Ψ = Ψ` and `⟪P0 g, Ψ⟫ = ⟪g, P0 Ψ⟫ = ⟪g, Ψ⟫` for
`g = toL2v (reVec f)` and `g = toL2v (imVec f)`; the complex integral is the real pairing for the
real part plus `i` times the one for the imaginary part (`toL2v g` has the representative `g`
a.e., `MemLp.coeFn_toLp`). -/
def P0OrthC : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ × ℝ → Fin 2 → ℂ,
    MemLp (reVec f) 2 (UnforcedLeray.Cyl.cellμ c) → MemLp (imVec f) 2 (UnforcedLeray.Cyl.cellμ c) →
      ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, IsDivFreeTestField c Ψ →
        ∫ x in B0579.cell c, ∑ i : Fin 2, (P0C c f x i - f x i) * (Ψ x i : ℂ) = 0

/-- **`𝒫₀` commutes with weak derivatives** (`PartIII-a:T18/2/4/2/6`; SP 3427-3440; the
`P0_comm_weakPartial` listed as not built in `Lib/CylinderB/Leray.lean`). If `f` and `g_j` are
`ℂ²`-valued fields with real and imaginary parts in `L²(cell)` and `g_j,i` is the weak `j`-derivative
of `f_i` on the cylinder (`HasWeakCellDerivC`), then `(𝒫₀ g_j)_i` is the weak `j`-derivative of
`(𝒫₀ f)_i`.
Proof idea: `𝒫₀` commutes with the unitary translations in `q` and `η`
(`TrainB.qShiftL2_P0_comm` in `Lib/TrainB/P0Horizontal.lean`, `TrainB.etaShiftL2_P0_comm` in
`Lib/TrainB/P0Translation.lean`; these are already built). The difference quotients
`D_h f = (f(· + h e_j) - f)/h` of the real and imaginary parts satisfy `D_h P0 f = P0 D_h f`, and
`D_h f ⇀ g_j` weakly in `L²` (tested against `ψ ∈ IsCylTest`, whose translates are `IsCylTest`),
hence `P0 D_h f ⇀ P0 g_j` weakly since `P0` is bounded and self-adjoint (`Cyl.inner_P0_comm`);
passing to the limit in `∫ D_h P0f · ψ = -∫ P0f · D_{-h} ψ` gives the weak derivative identity.
The integrability clauses of `HasWeakCellDerivC` come from `L²` times a bounded compactly
`η`-supported test. -/
def P0CommWeakC : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (f : ℝ × ℝ → Fin 2 → ℂ) (g : Fin 2 → ℝ × ℝ → Fin 2 → ℂ),
    MemLp (reVec f) 2 (UnforcedLeray.Cyl.cellμ c) → MemLp (imVec f) 2 (UnforcedLeray.Cyl.cellμ c) →
    (∀ j, MemLp (reVec (g j)) 2 (UnforcedLeray.Cyl.cellμ c)) →
    (∀ j, MemLp (imVec (g j)) 2 (UnforcedLeray.Cyl.cellμ c)) →
    (∀ i j, HasWeakCellDerivC c j (fun x => f x i) (fun x => g j x i)) →
      ∀ i j, HasWeakCellDerivC c j (fun x => P0C c f x i) (fun x => P0C c (g j) x i)

/-- **Slices of a nice family are in `L²`** (`PartIII-a:T18/2/4/2/7`; SP 3427-3440). For a nice
family `u` and every age `s`, the real and imaginary parts of the slice `u(s, ·)` and of the slices
of `∂_j u` (`duSl`) lie in `L²(cell; ℝ²)`.
Proof idea: the fields are continuous (`u` is `C^∞`; `fderiv` of a `C^∞` function is continuous),
hence strongly measurable; `‖u(s,x)_i‖ + ‖fderiv ℝ (y ↦ u(s,y) i) x‖ ≤ C e^{-κ η²}` for `s ≤ s`
(`GaussianDecayLoc` at `s₂ = s`), `‖pdC j g x‖ ≤ ‖fderiv ℝ g x‖` (`‖B0579.dir j‖ = 1`) and
`|Re z|, |Im z| ≤ ‖z‖`, so the Euclidean norm is `≤ 2 C e^{-κ η²}`; `x ↦ e^{-κ η²}` is in
`L²(cell)` (`cellμ c` is finite on `[-c/2, c/2) × [-R, R]`; use `MemLp.of_le`/`MemLp.mono` with a
dominator whose square `e^{-2κ η²}` is integrable: `integrable_exp_neg_mul_sq`). -/
def GaussianSliceMemLp : Prop :=
  ∀ c : ℝ, 0 < c → ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, NiceSlices c u → ∀ s : ℝ,
    MemLp (reVec (uSl u s)) 2 (UnforcedLeray.Cyl.cellμ c) ∧
      MemLp (imVec (uSl u s)) 2 (UnforcedLeray.Cyl.cellμ c) ∧
      ∀ j : Fin 2, MemLp (reVec (duSl u s j)) 2 (UnforcedLeray.Cyl.cellμ c) ∧
        MemLp (imVec (duSl u s j)) 2 (UnforcedLeray.Cyl.cellμ c)

/-- **Classical derivative of a slice is its weak derivative** (`PartIII-a:T18/2/4/2/8`; SP
3427-3440). For a nice family `u`, every age `s`, and `i, j`, the classical derivative
`pdC j (u_i(s, ·))` is the weak `j`-derivative of `u_i(s, ·)` on the cylinder.
Proof idea: integrability on the cell of `u_i(s,·) ∂_jψ` and `pdC j u_i · ψ`: continuous times a
test (`ψ`, `∂_jψ` bounded and vanishing for `|η| > R`) on the finite-measure set
`[-c/2, c/2) × [-R, R]` (outside it the integrand vanishes). Identity: split `u_i` into real and
imaginary parts (both are `C^∞`, `c`-periodic in `q`, and `∂_j` commutes with `Re`/`Im`), and use
`B0579.integral_mul_pd` (`Units/B0579.lean` 803): `∫_cell φ ∂_jψ = -∫_cell ∂_jφ ψ` for a smooth
`c`-periodic `φ` and a test `ψ` (the `q`-boundary terms cancel by periodicity, the `η`-boundary terms
vanish since `ψ` has compact `η`-support; for `φ` merely Gaussian-bounded no decay is needed since
`ψ` is compactly supported in `η`). -/
def SmoothSliceWeak : Prop :=
  ∀ c : ℝ, 0 < c → ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, NiceSlices c u → ∀ s : ℝ, ∀ i j : Fin 2,
    HasWeakCellDerivC c j (fun x => u (s, x) i) (fun x => pdC j (fun y => u (s, y) i) x)

/-! ## Sub-leaves used inside the leaves (not hypotheses of the wiring) -/

/-- **Test-class bridge** (`PartIII-a:T18/2/4/2/9`; used by `/4`, `/5`, `/10`). The test class
`B0579.IsCylTest` of `Units/B0579.lean` is the test class `Sob.IsCylTest` of
`Lib/Sobolev/Cylinder.lean` (the periodicity forms `φ (x.1 + c, x.2) = φ x` and
`φ (x + (c, 0)) = φ x` agree), and for a test the classical derivatives `B0579.pd 0`, `B0579.pd 1`
(`fderiv ℝ φ x (dir j)`) are `Cyl.partialQ`, `Cyl.partialEta` (`Cyl.partialQ_eq_fderiv`,
`Cyl.partialEta_eq_fderiv` in `Lib/Cylinder/IBP.lean`, for differentiable `φ`). -/
def TestBridge : Prop :=
  ∀ (c : ℝ) (φ : ℝ × ℝ → ℝ), (B0579.IsCylTest c φ ↔ UnforcedLeray.Sob.IsCylTest c φ) ∧
    (B0579.IsCylTest c φ → ∀ x : ℝ × ℝ, B0579.pd 0 φ x = UnforcedLeray.Cyl.partialQ φ x ∧
      B0579.pd 1 φ x = UnforcedLeray.Cyl.partialEta φ x)

/-- **`𝒫₀` commutes with weak derivatives, real `L²` form** (`PartIII-a:T18/2/4/2/10`; used by
`/6`; the `H¹` case of `P0_comm_weakPartial`). If `f, w₀, w₁ ∈ L²(cell; ℝ²)` and `w_j` is the weak
`j`-derivative of `f` componentwise (tested against `B0579.IsCylTest` and the unweighted cell
pairing), then `P0 w_j` is the weak `j`-derivative of `P0 f`.
Proof idea: this is `TrainB.hasWeakDeriv_P0_q_of_vecH1` and `TrainB.hasWeakDeriv_P0_eta_of_vecH1`
(`Lib/TrainB/P0WeakProjection.lean`, already built; `VecH1 c = Cyl.H ℝ Vec2 c 0 1`,
`Lib/TrainB/P0W1.lean`) once `(f, w₀, w₁)` is packaged as an element `x : VecH1 c` (an element of
`Sob.W (Sob.cylinder c) (ρwW c ^ 0) ℝ Vec2 1 2` is a tuple of `L²` classes with `Sob.HasWeakDeriv`
relations; the order-zero measure of `VecH1 c` is `cellμ c`, `TrainB.vecH1_measure_eq_cell`), and
`Sob.HasWeakDeriv` (`Lib/Sobolev/WeakDeriv.lean`) is converted to and from the displayed pairing
identities (test class `Sob.IsCylTest`, `TestBridge`). -/
def P0CommWeakL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (f : UnforcedLeray.Cyl.L2v c) (w : Fin 2 → UnforcedLeray.Cyl.L2v c),
    (∀ (j i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c, (w j : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x) →
    ∀ (j i : Fin 2) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c,
          (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * B0579.pd j ψ x =
        -∫ x in B0579.cell c,
          (UnforcedLeray.Cyl.P0 c (w j) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i * ψ x

/-! ## Small helpers for the wiring -/

theorem cellμ_eq (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell B0579.cell
  rw [neg_div]

/-- The weak-derivative relation only depends on the almost-everywhere class of both functions. -/
theorem HasWeakCellDerivC.congr_ae {c : ℝ} {j : Fin 2} {φ φ' g g' : ℝ × ℝ → ℂ}
    (hφ : φ =ᵐ[volume.restrict (B0579.cell c)] φ')
    (hg : g =ᵐ[volume.restrict (B0579.cell c)] g')
    (h : HasWeakCellDerivC c j φ' g') : HasWeakCellDerivC c j φ g := by
  obtain ⟨hint, heq⟩ := h
  refine ⟨fun ψ hψ => ⟨(hint ψ hψ).1.congr_fun_ae ?_, (hint ψ hψ).2.congr_fun_ae ?_⟩, fun ψ hψ => ?_⟩
  · filter_upwards [hφ] with x hx using by rw [hx]
  · filter_upwards [hg] with x hx using by rw [hx]
  · have e1 : ∫ x in B0579.cell c, φ x * (B0579.pd j ψ x : ℂ) =
        ∫ x in B0579.cell c, φ' x * (B0579.pd j ψ x : ℂ) :=
      integral_congr_ae (by filter_upwards [hφ] with x hx; rw [hx])
    have e2 : ∫ x in B0579.cell c, g x * (ψ x : ℂ) = ∫ x in B0579.cell c, g' x * (ψ x : ℂ) :=
      integral_congr_ae (by filter_upwards [hg] with x hx; rw [hx])
    rw [e1, e2]
    exact heq ψ hψ

/-- The zero function has the zero weak derivative. -/
theorem HasWeakCellDerivC.zero (c : ℝ) (j : Fin 2) :
    HasWeakCellDerivC c j (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · simp
  · simp
  · simp

/-! ## The assembly -/

/-- The set of ages at which the slice of `u` vanishes identically is closed. -/
theorem isClosed_zeroAges {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hu : ∀ i, Continuous fun p : ℝ × (ℝ × ℝ) => u p i) :
    IsClosed {s : ℝ | ∀ x i, u (s, x) i = 0} := by
  have h : {s : ℝ | ∀ x i, u (s, x) i = 0} =
      ⋂ x : ℝ × ℝ, ⋂ i : Fin 2, {s : ℝ | u (s, x) i = 0} := by
    ext s; simp
  rw [h]
  refine isClosed_iInter fun x => isClosed_iInter fun i => ?_
  exact isClosed_eq ((hu i).comp (by fun_prop : Continuous fun s : ℝ => (s, x)))
    continuous_const

/-- **Leray projection of the slices from the eight leaves** (assembly; SP 3427-3440). The
joint representatives of the continuous paths `s ↦ 𝒫₀ u(s)`, `s ↦ 𝒫₀ ∂_j u(s)` (`hJ`, `hC`),
redefined to be `0` on the closed set of ages with `u(s) ≡ 0`, satisfy the clauses of
`IsLerayProjection`: the slice clauses transfer along the a.e. identification from `hD`, `hO`,
`hW` (with `hM`, `hS`), and `energyLoc` follows from `hE` by Tonelli. -/
theorem lerayProjectSlices_of (hJ : JointRepVecC) (hC : LerayClassCont) (hE : LerayClassEnergy)
    (hD : P0DivFreeC) (hO : P0OrthC) (hW : P0CommWeakC) (hM : GaussianSliceMemLp)
    (hS : SmoothSliceWeak) : LerayProjectSlices := by
  classical
  intro c hc u hus hup hdec
  have hN : NiceSlices c u := ⟨hus, hup, hdec⟩
  obtain ⟨hc1, hc2, hc3⟩ := hC c hc u hN
  obtain ⟨Fb, hFbm, hFb⟩ := hJ c hc _ _ hc1 hc2
  have hG : ∀ j : Fin 2, ∃ Fj : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => Fj p i) ∧
      ∀ t : ℝ, 0 < t → ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        ∀ i, Fj (t, x) i = P0C c (duSl u t j) x i := fun j =>
    hJ c hc _ _ (hc3 j).1 (hc3 j).2
  choose Fg hFgm hFg using hG
  have hFb' : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ∀ i, Fb (t, x) i = P0C c (uSl u t) x i := fun t ht => hFb t ht
  set Z : Set ℝ := {s : ℝ | ∀ x i, u (s, x) i = 0} with hZdef
  have hZ : MeasurableSet Z := (isClosed_zeroAges (fun i => (hus i).continuous)).measurableSet
  obtain ⟨b', hbZ, hbN, hbm⟩ : ∃ b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ,
      (∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Z → ∀ i, b' p i = 0) ∧
      (∀ p : ℝ × (ℝ × ℝ), p.1 ∉ Z → ∀ i, b' p i = Fb p i) ∧
      (∀ i, Measurable fun p => b' p i) :=
    ⟨fun p i => if p.1 ∈ Z then 0 else Fb p i, fun p hp i => by simp [hp],
      fun p hp i => by simp [hp],
      fun i => Measurable.ite (measurable_fst hZ) measurable_const (hFbm i)⟩
  obtain ⟨G', hGZ, hGN, hGm⟩ : ∃ G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Z → ∀ i j, G' p i j = 0) ∧
      (∀ p : ℝ × (ℝ × ℝ), p.1 ∉ Z → ∀ i j, G' p i j = Fg j p i) ∧
      (∀ i j, Measurable fun p => G' p i j) :=
    ⟨fun p i j => if p.1 ∈ Z then 0 else Fg j p i, fun p hp i j => by simp [hp],
      fun p hp i j => by simp [hp],
      fun i j => Measurable.ite (measurable_fst hZ) measurable_const (hFgm j i)⟩
  refine ⟨b', G', ?_⟩
  refine
    { measurable := hbm
      gradMeasurable := hGm
      energyLoc := ?_
      divFree := ?_
      weakGrad := ?_
      orth := ?_
      zero := fun s hs x i => hbZ (s, x) hs i }
  · -- energyLoc
    intro s₁ s₂ hs₁ hs₁₂
    obtain ⟨M, hMb⟩ := hE c hc u hN s₂
    have hmeas : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) := by
      refine ENNReal.measurable_ofReal.comp
        (Measurable.add (Measurable.pow_const ?_ 2) (Measurable.pow_const ?_ 2))
      · unfold vnorm2
        exact Real.continuous_sqrt.measurable.comp
          (Finset.measurable_sum _ fun i _ => (hbm i).norm.pow_const 2)
      · unfold tnorm2
        exact Real.continuous_sqrt.measurable.comp
          (Finset.measurable_sum _ fun i _ =>
            Finset.measurable_sum _ fun j _ => (hGm i j).norm.pow_const 2)
    have hprod : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) =
        ∫⁻ s in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (b' (s, x)) ^ 2 + tnorm2 (G' (s, x)) ^ 2) := by
      rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
        lintegral_prod _ hmeas.aemeasurable]
    rw [hprod]
    calc ∫⁻ s in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (b' (s, x)) ^ 2 + tnorm2 (G' (s, x)) ^ 2)
        ≤ ∫⁻ s in Icc s₁ s₂, ENNReal.ofReal M := by
          refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
          have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
          by_cases hsZ : s ∈ Z
          · have h0 : ∀ x : ℝ × ℝ, ENNReal.ofReal
                (vnorm2 (b' (s, x)) ^ 2 + tnorm2 (G' (s, x)) ^ 2) = 0 := by
              intro x
              have hb0 : b' (s, x) = fun _ => 0 := funext fun i => hbZ (s, x) hsZ i
              have hG0 : G' (s, x) = fun _ _ => 0 :=
                funext fun i => funext fun j => hGZ (s, x) hsZ i j
              rw [hb0, hG0]
              simp [vnorm2, tnorm2]
            simp [h0]
          · have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
                ENNReal.ofReal (vnorm2 (b' (s, x)) ^ 2 + tnorm2 (G' (s, x)) ^ 2) =
                  ENNReal.ofReal (vnorm2 (P0C c (uSl u s) x) ^ 2 +
                    tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2) := by
              filter_upwards [hFb' s hs0, hFg 0 s hs0, hFg 1 s hs0] with x h1 h2 h3
              have hb : b' (s, x) = P0C c (uSl u s) x :=
                funext fun i => (hbN (s, x) hsZ i).trans (h1 i)
              have hG : G' (s, x) = fun i j => P0C c (duSl u s j) x i := by
                funext i j
                rw [hGN (s, x) hsZ i j]
                fin_cases j
                · exact h2 i
                · exact h3 i
              rw [hb, hG]
            rw [lintegral_congr_ae hae]
            exact hMb s hs0 hs.2
      _ = ENNReal.ofReal M * volume (Icc s₁ s₂) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  · -- divFree
    intro s hs ψ hψ
    by_cases hsZ : s ∈ Z
    · have h0 : ∀ x : ℝ × ℝ, b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
          b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ) = 0 := by
        intro x
        rw [hbZ (s, x) hsZ 0, hbZ (s, x) hsZ 1]
        simp
      simp [h0]
    · refine (integral_congr_ae ?_).trans (hD c hc (uSl u s) ψ hψ)
      filter_upwards [hFb' s hs] with x hx
      rw [hbN (s, x) hsZ 0, hbN (s, x) hsZ 1, hx 0, hx 1]
  · -- weakGrad
    intro s hs i j
    by_cases hsZ : s ∈ Z
    · have hb0 : (fun x => b' (s, x) i) = fun _ => 0 :=
        funext fun x => hbZ (s, x) hsZ i
      have hG0 : (fun x => G' (s, x) i j) = fun _ => 0 :=
        funext fun x => hGZ (s, x) hsZ i j
      rw [hb0, hG0]
      exact HasWeakCellDerivC.zero c j
    · have hmem := hM c hc u hN s
      have hweak := hW c hc (uSl u s) (fun j => duSl u s j) hmem.1 hmem.2.1
        (fun j => (hmem.2.2 j).1) (fun j => (hmem.2.2 j).2)
        (fun i j => hS c hc u hN s i j) i j
      refine HasWeakCellDerivC.congr_ae ?_ ?_ hweak
      · filter_upwards [hFb' s hs] with x hx
        rw [hbN (s, x) hsZ i, hx i]
      · filter_upwards [hFg j s hs] with x hx
        rw [hGN (s, x) hsZ i j, hx i]
  · -- orth
    intro s hs Ψ hΨ
    by_cases hsZ : s ∈ Z
    · have h0 : ∀ x : ℝ × ℝ, ∑ i : Fin 2, (b' (s, x) i - u (s, x) i) * (Ψ x i : ℂ) = 0 := by
        intro x
        simp [hbZ (s, x) hsZ, hsZ x]
      simp [h0]
    · have hmem := hM c hc u hN s
      refine (integral_congr_ae ?_).trans (hO c hc (uSl u s) hmem.1 hmem.2.1 Ψ hΨ)
      filter_upwards [hFb' s hs] with x hx
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbN (s, x) hsZ i, hx i]
      rfl

end UnforcedLeray.Short.IIIa
