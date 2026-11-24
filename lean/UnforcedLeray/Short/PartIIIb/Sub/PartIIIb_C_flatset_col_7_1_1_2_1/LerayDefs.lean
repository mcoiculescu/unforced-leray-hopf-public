import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel
import Mathlib.Data.Real.Sign

/-!
# Design of `LerayDriving` (`PartIII-b:C/flatset/col/7/1/1/2/1/org2/leray`)

Source of record `the November 2 reference manuscript` 1650-1656, 1676-1677:
`P₀` is "the ordinary planar cylinder projection" and `T₀ = (μ - A₀)⁻¹ P₀`.  The weight `s^{-3/2}`
of `H` depends only on `s` and the tests `cgrad 0 Φ = (∂_qΦ, ∂_ηΦ)` differentiate only in
`(q, η)`, so `P₀` acts slice by slice in `s` as the Leray projection of the cylinder
`ℝ/cℤ × ℝ_η`; `s` is only a parameter below.

## Route (closed-form cylinder Green function, no Fourier series)

The Fourier route (modes `e^{ikq}`, 1D kernels `e^{-|k||η|}/2|k|`, `contDiff_tsum`, Fourier
inversion) was judged longer in Lean than the following.  On the cylinder the Green function of
`Δ_{q,η}` is closed form: `Γ(q, η) = (4π)⁻¹ log (cosh aη - cos aq)`, `a = 2π/c`
(`= (2π)⁻¹ log |2 sinh(a(η + iq)/2)|`, so `Γ ~ (2π)⁻¹ log |y|` at `0` and `ΔΓ = δ` on the cylinder).
Its gradient `K = ∇Γ` (`cylKer`),
`K₀ = a sin(aq) / (4π D)`, `K₁ = a sinh(aη) / (4π D)`, `D = cosh aη - cos aq` (`cylDen`),
is `O(1/|y|)` at `0` (`D ≥ (2a²/π²)|y|²` on the centred cell) and bounded at infinity, with
`K₀ → 0` and `K₁ → ±a/4π` exponentially.

* `lerayPot c F = Σ_i K_i ⊛ F_i` (`= Γ ⊛ div F` after one integration by parts), the integral over
  the centred cell `cellC c` of `y ↦ K_i(y) F_i(s, x - y)`: an absolutely convergent integral whose
  derivatives fall on `F` (`LerayPotSmooth`), so `u` is smooth with all derivatives bounded and
  `∂_v u = lerayPot c (∂_v F)`; `Δu = div F` (`LerayPotPoisson`, from `CylKerGreen`);
  `∇u` decays like `e^{-a|η|}` (`LerayPotDecay`, from `CylKerAsym` and `∫_cell ∂_j F_1 = 0`).
* `lerayField c F = F - ∇u` is `P₀ F`: smooth, periodic, band supported in `s`, all derivatives
  bounded, divergence free (`LerayFieldProps`), hence `H`-orthogonal to every `cgrad 0 Φ` by
  integration by parts on the cell (`SmoothSolenoidal`); `∇u` is the `H`-limit of
  `cgrad 0 (χ(η/R) u)` (`u` bounded, `∇u ∈ H`), so lies in `(solenoidalHC 0 c)ᗮ`
  (`SmoothGradPerp`).  `P₀(W + ∇u) = W` (`pepsC_eq_of_decomp`), and `G = W/s` (`DrivingOfSmooth`).
* The fundamental-solution identity `∫_cell K_i Δh = -∂_i h(0)` (`CylKerGreen`) goes through the
  smooth regularisation `Γ_ε = (4π)⁻¹ log (D + ε)` (`cylGreenReg`):
  `∂_iΓ_ε = K_i^ε` (`cylKerReg`), `ΔΓ_ε = ρ_ε = a²ε(cosh aη + cos aq)/(4π(D + ε)²)` (`cylRho`),
  a positive approximate identity of mass one on the cell; `|K_i^ε| ≤ |K_i|`, `K_i^ε → K_i`.

All statements are `Prop` definitions here; the conditional assemblies are in `LerayOf.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ## The cylinder kernels on the `(q, η)` plane -/

/-- The frequency `a = 2π/c` of the period `c`. -/
def cylFreq (c : ℝ) : ℝ := 2 * Real.pi / c

/-- `D(q, η) = cosh(aη) - cos(aq)` (`y = (q, η)`); `D ≥ 0`, `D = 0` only on the lattice `cℤ × {0}`. -/
def cylDen (c : ℝ) (y : ℝ × ℝ) : ℝ := Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)

/-- The numerators `(sin(aq), sinh(aη)) = a⁻¹ ∇D`. -/
def cylNum (c : ℝ) (i : Fin 2) (y : ℝ × ℝ) : ℝ :=
  ![Real.sin (cylFreq c * y.1), Real.sinh (cylFreq c * y.2)] i

/-- The gradient `K = ∇Γ` of the cylinder Green function `Γ = (4π)⁻¹ log D` (source 1676,
"planar cylinder projection"): `K_i = a (sin aq, sinh aη)_i / (4π D)`.  The value at the lattice
points (division by `0`) is the junk value `0`, a null set. -/
def cylKer (c : ℝ) (i : Fin 2) (y : ℝ × ℝ) : ℝ :=
  cylFreq c / (4 * Real.pi) * cylNum c i y / cylDen c y

/-- The regularised Green function `Γ_ε = (4π)⁻¹ log (D + ε)`, smooth for `ε > 0`. -/
def cylGreenReg (c ε : ℝ) (y : ℝ × ℝ) : ℝ := (4 * Real.pi)⁻¹ * Real.log (cylDen c y + ε)

/-- `K^ε = ∇Γ_ε = a (sin aq, sinh aη) / (4π (D + ε))`. -/
def cylKerReg (c ε : ℝ) (i : Fin 2) (y : ℝ × ℝ) : ℝ :=
  cylFreq c / (4 * Real.pi) * cylNum c i y / (cylDen c y + ε)

/-- `ρ_ε = ΔΓ_ε = a² ε (cosh aη + cos aq) / (4π (D + ε)²)`: positive, mass one on a cell. -/
def cylRho (c ε : ℝ) (y : ℝ × ℝ) : ℝ :=
  cylFreq c ^ 2 * ε / (4 * Real.pi) *
    (Real.cosh (cylFreq c * y.2) + Real.cos (cylFreq c * y.1)) / (cylDen c y + ε) ^ 2

/-- The centred period cell `(-c/2, c/2] × ℝ` of the `(q, η)` cylinder. -/
def cellC (c : ℝ) : Set (ℝ × ℝ) := Ioc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)

/-- The coordinate directions `e_q = (1, 0)`, `e_η = (0, 1)` of the `(q, η)` plane. -/
def dir2 (i : Fin 2) : ℝ × ℝ := ![((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] i

/-- `∂_q` (`i = 0`), `∂_η` (`i = 1`) on the `(q, η)` plane. -/
def pd2 (i : Fin 2) (h : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ := fderiv ℝ h y (dir2 i)

/-- `Δ_{q,η} h = ∂_q² h + ∂_η² h`. -/
def lap2 (h : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ := pd2 0 (pd2 0 h) y + pd2 1 (pd2 1 h) y

/-- A test function of the cylinder in the `(q, η)` variables: smooth, `c`-periodic in `q`,
vanishing for `|η|` large. -/
def IsCylTest2 (c : ℝ) (h : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧ (∀ y : ℝ × ℝ, h (y.1 + c, y.2) = h y) ∧
    ∃ L : ℝ, ∀ y : ℝ × ℝ, L < |y.2| → h y = 0

/-! ## Chart objects: the potential and the Leray field -/

/-- The flat gradient `(∂_q u, ∂_η u)` of a chart function (`Axi.dQ`, `Axi.dEta`, the components of
`cgrad 0`). -/
def flatGrad (u : Chart → ℝ) (p : Chart) : Fin 2 → ℝ :=
  ![UnforcedLeray.Axi.dQ u p, UnforcedLeray.Axi.dEta u p]

/-- The flat divergence `∂_q F₀ + ∂_η F₁` (source 1653, `div(√s b) = s[(∂_q - εK)b_r + ∂_η b_z]` at
`ε = 0`). -/
def flatDiv (F : Chart → Fin 2 → ℝ) (p : Chart) : ℝ :=
  UnforcedLeray.Axi.dQ (fun p => F p 0) p + UnforcedLeray.Axi.dEta (fun p => F p 1) p

/-- A real meridional vector, complexified (`B0223.MeridC`). -/
def cvec (v : Fin 2 → ℝ) : UnforcedLeray.B0223.MeridC := WithLp.toLp 2 fun i => ((v i : ℝ) : ℂ)

/-- The pointwise part of `IsSmoothForce` (`PartIII-b_C_flatset_col_7_1_1_of.lean:34`, source
1684-1689): smooth, `c`-periodic in `q`, supported in `s ∈ [s₀, s₁]`, `|η| ≤ L`, `s₀ > 0`. -/
def IsForceField (c : ℝ) (F : Chart → Fin 2 → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ fun p => F p i) ∧ (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) ∧
    ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L

/-- The flat potential `u = Γ ⊛ div F = Σ_i K_i ⊛ F_i`, slice by slice in `s` (source 1676: `P₀`
is the planar cylinder projection, `P₀F = F - ∇Δ⁻¹ div F`). -/
def lerayPot (c : ℝ) (F : Chart → Fin 2 → ℝ) (p : Chart) : ℝ :=
  ∑ i : Fin 2, ∫ y in cellC c, cylKer c i y * F (p.1, p.2 - y) i

/-- The Leray field `W = F - ∇u = P₀ F` (source 1655-1656, 1676). -/
def lerayField (c : ℝ) (F : Chart → Fin 2 → ℝ) (p : Chart) : Fin 2 → ℝ :=
  fun i => F p i - flatGrad (lerayPot c F) p i

/-! ## Kernel leaves -/

/-- **Integration by parts on a period cell** (generic): for `C¹` functions, `c`-periodic in `q`,
the second vanishing for `|η|` large, `∫_{(t,t+c]×ℝ} A ∂_i B = -∫_{(t,t+c]×ℝ} ∂_i A B`
(periodic boundary terms cancel in `q`, compact support in `η`). -/
def CellIBP : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (t : ℝ) (A B : ℝ × ℝ → ℝ), ContDiff ℝ 1 A → ContDiff ℝ 1 B →
    (∀ y : ℝ × ℝ, A (y.1 + c, y.2) = A y) → (∀ y : ℝ × ℝ, B (y.1 + c, y.2) = B y) →
    (∃ L : ℝ, ∀ y : ℝ × ℝ, L < |y.2| → B y = 0) → ∀ i : Fin 2,
      ∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), A y * pd2 i B y =
        -∫ y in Ioc t (t + c) ×ˢ (univ : Set ℝ), pd2 i A y * B y

/-- **Calculus of `Γ_ε`**: smooth, `c`-periodic, `∂_iΓ_ε = K_i^ε`, `ΔΓ_ε = ρ_ε` (direct
differentiation; `sin² + sinh² = (cosh - cos)(cosh + cos)`). -/
def RegKerCalc : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε →
    ContDiff ℝ ∞ (cylGreenReg c ε) ∧
      (∀ y : ℝ × ℝ, cylGreenReg c ε (y.1 + c, y.2) = cylGreenReg c ε y) ∧
      (∀ (i : Fin 2) (y : ℝ × ℝ), pd2 i (cylGreenReg c ε) y = cylKerReg c ε i y) ∧
      ∀ y : ℝ × ℝ, lap2 (cylGreenReg c ε) y = cylRho c ε y

/-- **Regularised Green identity**: `∫_cell K_i^ε Δh = -∫_cell ρ_ε ∂_i h` for a cylinder test `h`
(`K_i^ε = ∂_iΓ_ε`; integrate by parts once in `i` and twice in each direction, `CellIBP`). -/
def RegKerIBP : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ h : ℝ × ℝ → ℝ, IsCylTest2 c h → ∀ i : Fin 2,
    ∫ y in cellC c, cylKerReg c ε i y * lap2 h y = -∫ y in cellC c, cylRho c ε y * pd2 i h y

/-- **Mass of `ρ_ε`**: `ρ_ε ≥ 0`, integrable on the cell, `∫_cell ρ_ε = 1`
(`∫_ℝ ∂_η² Γ_ε dη = [a sinh/(4π(D+ε))]_{-∞}^{∞} = a/2π = 1/c`, `∫_cell ∂_q² Γ_ε = 0`). -/
def RhoMass : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε →
    (∀ y : ℝ × ℝ, 0 ≤ cylRho c ε y) ∧ IntegrableOn (cylRho c ε) (cellC c) ∧
      ∫ y in cellC c, cylRho c ε y = 1

/-- **Tail of `ρ_ε`**: away from the lattice point `0` of the cell, `∫ ρ_ε = O(ε)`
(`D ≥ m_δ > 0` there and `(cosh aη + 1)/D²` is integrable). -/
def RhoTail : Prop :=
  ∀ (c δ : ℝ), 0 < c → 0 < δ → ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
    ∫ y in cellC c ∩ {y : ℝ × ℝ | δ ≤ ‖y‖}, cylRho c ε y ≤ C * ε

/-- **Approximate identity**: `∫_cell ρ_ε ∂_i h → ∂_i h(0)` as `ε → 0⁺` (from `RhoMass`,
`RhoTail` and continuity of `∂_i h` at `0`). -/
def RegApproxId : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ h : ℝ × ℝ → ℝ, IsCylTest2 c h → ∀ i : Fin 2,
    Tendsto (fun ε => ∫ y in cellC c, cylRho c ε y * pd2 i h y) (𝓝[>] 0) (𝓝 (pd2 i h 0))

/-- **Window integrability of `K`**: `|K_i(y)| ≤ C₀ + C₁/|y|` on the centred cell, so `K_i` is
integrable on every window `(-c/2, c/2] × [t - L, t + L]` with a bound uniform in `t`. -/
def CylKerWindow : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ L : ℝ, ∃ C : ℝ, ∀ (i : Fin 2) (t : ℝ),
    IntegrableOn (cylKer c i) (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (t - L) (t + L)) ∧
      ∫ y in Ioc (-(c / 2)) (c / 2) ×ˢ Icc (t - L) (t + L), |cylKer c i y| ≤ C

/-- **Removal of the regularisation**: `∫_cell K_i^ε Δh → ∫_cell K_i Δh` (dominated convergence,
`|K_i^ε| ≤ |K_i|`, `K_i^ε → K_i` off `y = 0`). -/
def RegKerLimit : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ h : ℝ × ℝ → ℝ, IsCylTest2 c h → ∀ i : Fin 2,
    Tendsto (fun ε => ∫ y in cellC c, cylKerReg c ε i y * lap2 h y) (𝓝[>] 0)
      (𝓝 (∫ y in cellC c, cylKer c i y * lap2 h y))

/-- **Fundamental solution of the cylinder** (source 1676): `∫_cell ∇Γ · Δh e_i = -∂_i h(0)`,
i.e. `ΔΓ = δ` on `ℝ/cℤ × ℝ`. -/
def CylKerGreen : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ h : ℝ × ℝ → ℝ, IsCylTest2 c h → ∀ i : Fin 2,
    ∫ y in cellC c, cylKer c i y * lap2 h y = -pd2 i h 0

/-- **Asymptotics of `K`** for `|η| ≥ 1`: `K₀ = O(e^{-a|η|})`, `K₁ = (a/4π) sign η + O(e^{-a|η|})`. -/
def CylKerAsym : Prop :=
  ∀ (c : ℝ), 0 < c → ∃ C : ℝ, ∀ y : ℝ × ℝ, 1 ≤ |y.2| →
    |cylKer c 0 y| ≤ C * Real.exp (-(cylFreq c * |y.2|)) ∧
      |cylKer c 1 y - cylFreq c / (4 * Real.pi) * Real.sign y.2| ≤
        C * Real.exp (-(cylFreq c * |y.2|))

/-! ## Potential and field leaves -/

/-- **Bounded derivatives** (generic): a smooth chart function, `c`-periodic in `q`, supported in a
compact `(s, η)` band, has all iterated derivatives bounded. -/
def BoundedDerivBand : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Chart → ℝ, ContDiff ℝ ∞ f →
    (∀ s q η, f (s, (q + c, η)) = f (s, (q, η))) →
    (∃ s0 s1 L : ℝ, ∀ p, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    ∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n f p‖ ≤ C

/-- **Derivatives of a force field are force fields** (generic): `∂_v F` is smooth, `c`-periodic and
supported in the same closed band. -/
def ForceFieldDeriv : Prop :=
  ∀ (c : ℝ) (F : Chart → Fin 2 → ℝ), IsForceField c F → ∀ v : Chart,
    IsForceField c (fun p i => fderiv ℝ (fun p' => F p' i) p v)

/-- **Smoothness of the potential**: `u = lerayPot c F` is `C^∞`, all its derivatives are bounded,
and derivatives fall on `F`: `∂_v u = lerayPot c (∂_v F)` (differentiation under the integral,
`Lib/Kernels/ParamIntegral.lean`, dominated by `|K_i| · sup |D^n F_i|` on a window). -/
def LerayPotSmooth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, IsForceField c F →
    ContDiff ℝ ∞ (lerayPot c F) ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (lerayPot c F) p‖ ≤ C) ∧
      ∀ p v : Chart, fderiv ℝ (lerayPot c F) p v =
        lerayPot c (fun p' i => fderiv ℝ (fun p'' => F p'' i) p' v) p

/-- **Poisson equation** `Δ_{q,η} u = div F` (from `CylKerGreen` applied to `h(y) = F_i(s, x - y)`). -/
def LerayPotPoisson : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, IsForceField c F → ∀ p : Chart,
    UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (lerayPot c F)) p +
        UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (lerayPot c F)) p = flatDiv F p

/-- **Decay of `∇u`** in `η` (`CylKerAsym`; the constant part `±a/4π` of `K₁` integrates
`∂_j F₁` over a cell to `0`). -/
def LerayPotDecay : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, IsForceField c F →
    ∃ C κ : ℝ, 0 < κ ∧ ∀ p : Chart,
      |UnforcedLeray.Axi.dQ (lerayPot c F) p| + |UnforcedLeray.Axi.dEta (lerayPot c F) p| ≤
        C * Real.exp (-(κ * |p.2.2|))

/-- **The Leray field** `W = F - ∇u`: smooth, periodic, band supported in `s`, all derivatives
bounded, exponentially decaying in `η`, divergence free. -/
def LerayFieldProps : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, IsForceField c F →
    (∀ i, ContDiff ℝ ∞ fun p => lerayField c F p i) ∧
      (∀ s q η, lerayField c F (s, (q + c, η)) = lerayField c F (s, (q, η))) ∧
      (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p, lerayField c F p ≠ 0 → p.1 ∈ Icc s0 s1) ∧
      (∀ (i : Fin 2) (n : ℕ), ∃ C : ℝ, ∀ p,
        ‖iteratedFDeriv ℝ n (fun p : Chart => lerayField c F p i) p‖ ≤ C) ∧
      (∃ C κ : ℝ, 0 < κ ∧ ∀ p i, |lerayField c F p i| ≤ C * Real.exp (-(κ * |p.2.2|))) ∧
      ∀ p, flatDiv (lerayField c F) p = 0

/-! ## `H`-level leaves -/

/-- **Driving class of `W/s`** (`IsDriving`, source 1650-1656): smooth, periodic, band supported
(`s₀ > 0`) with bounded derivatives `W` gives the `H_g`-density `G = W/s`. -/
def DrivingOfSmooth : Prop :=
  ∀ (c : ℝ) (W : Chart → Fin 2 → ℝ), (∀ i, ContDiff ℝ ∞ fun p => W p i) →
    (∀ s q η, W (s, (q + c, η)) = W (s, (q, η))) →
    (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p, W p ≠ 0 → p.1 ∈ Icc s0 s1) →
    (∀ (i : Fin 2) (n : ℕ), ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (fun p : Chart => W p i) p‖ ≤ C) →
    IsDriving c (fun p i => W p i / p.1)

/-- **Smooth divergence-free fields are solenoidal** (weak form, `solenoidalHC 0 c`,
`PartII-a/StatementsNear.lean:102`): `∫ s^{-3/2} (W₀ ∂_qΦ + W₁ ∂_ηΦ) = 0` for every profile test
`Φ`, by `CellIBP` on each `s`-slice. -/
def SmoothSolenoidal : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ W : Chart → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => W p i) →
    (∀ s q η, W (s, (q + c, η)) = W (s, (q, η))) → (∀ p, flatDiv W p = 0) →
    ∀ hW : MemLp (fun p => cvec (W p)) 2 (UnforcedLeray.B0220.measureH c),
      hW.toLp _ ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c

/-- **Gradients are orthogonal to the solenoidal space**: for `u` smooth, periodic, band supported in
`s`, bounded, with exponentially decaying `∇u`, `∇u = lim_R cgrad 0 (χ(η/R) u)` in `H`, so
`∇u ∈ (solenoidalHC 0 c)ᗮ`. -/
def SmoothGradPerp : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u : Chart → ℝ, ContDiff ℝ ∞ u →
    (∀ s q η, u (s, (q + c, η)) = u (s, (q, η))) →
    (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p, u p ≠ 0 → p.1 ∈ Icc s0 s1) →
    (∃ C : ℝ, ∀ p, |u p| ≤ C) →
    (∃ C κ : ℝ, 0 < κ ∧ ∀ p : Chart,
      |UnforcedLeray.Axi.dQ u p| + |UnforcedLeray.Axi.dEta u p| ≤ C * Real.exp (-(κ * |p.2.2|))) →
    ∀ hV : MemLp (fun p => cvec (flatGrad u p)) 2 (UnforcedLeray.B0220.measureH c),
      hV.toLp _ ∈ (UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)ᗮ

/-- **`L²` membership** of a continuous field supported in an `s`-band away from `0` with
exponential decay in `η` (weight `s^{-3/2}` integrable on `[s₀, s₁]`). -/
def MemLpOfDecay : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ v : Chart → Fin 2 → ℝ, (∀ i, Continuous fun p => v p i) →
    (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p, v p ≠ 0 → p.1 ∈ Icc s0 s1) →
    (∃ C κ : ℝ, 0 < κ ∧ ∀ p i, |v p i| ≤ C * Real.exp (-(κ * |p.2.2|))) →
    MemLp (fun p => cvec (v p)) 2 (UnforcedLeray.B0220.measureH c)

/-- **Representative of a smooth force in `H`**: the recentred complexified `g` is a.e. the
periodic field `F` (`CellMap.map_cellPt_measureH`: `cellPt` pushes `measureH c` to
`c • ageμ c (-3/2)`; `F ∘ cellPt = F` by periodicity). -/
def SmoothForceRep : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Hsp c) (F : Chart → Fin 2 → ℝ),
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c (-3 / 2)), ∀ i, NearInst.velC g p i = ((F p i : ℝ) : ℂ)) →
    (fun p => NearInst.merC (g (NearInst.cellPt c p))) =ᵐ[UnforcedLeray.B0220.measureH c]
      fun p => cvec (F p)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
