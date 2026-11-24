import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjDensityOf
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PhaseLpTri2
import UnforcedLeray.Lib.PhaseSpace.Cutoff
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc

/-!
# Design for `fwuAdjTrunc`: stream-potential truncation of the adjoint domain

Source: `the November 2 reference manuscript` lines 1334-1337 (`Y_r` is the plain
`L^r` of `(ℝ/Pℤ) × ℝ³`), 1351-1362 (the adjoint at `r = 2` has the maximal graph) and 1470-1480
("radial cutoffs approximate it in this graph, since their drift commutator is bounded on an
escaping annulus and their diffusion commutators tend to zero").

Mathematics (`M = μ + L₀ᵗ = μ + 1 - ∂_τ + ½ y·∇ - νΔ`).  Let `Φ ∈ Y_2` be weakly solenoidal,
`Φ = curl ψ` (Coulomb gauge Biot-Savart potential, `∇ψ ∈ Y_2`, Hardy `ψ/|y| ∈ Y_2`) and
`MΦ = g` weakly.  Put `Φₙ = curl(χₙ ψ) = χₙ Φ + ∇χₙ × ψ`, `χₙ = cutχ n` (equal to `1` on
`|y| ≤ n+1`, `0` on `|y| ≥ 2(n+1)`).  With `w = (μ + ½ - ∂_τ + ½ y·∇ - νΔ) ψ` (again a Coulomb
Biot-Savart potential, of `g`: `curl w = g`, because `curl` intertwines `M` and this operator) one
computes
`MΦₙ = χₙ g + ∇χₙ × w + ½ ∇(y·∇χₙ) × ψ - ν ∇Δχₙ × ψ`
`      + (½ y·∇χₙ - νΔχₙ) Φ - 2ν ∑ₖ ∂ₖχₙ ∂ₖΦ - 2ν ∑ₖ ∇∂ₖχₙ × ∂ₖψ`.
All commutator coefficients live on the annulus `n+1 ≤ |y| ≤ 2(n+1)`; the first three are
`O(1/|y|)` (so they tend to `0` in `Y_2` by Hardy and dominated convergence), the rest are bounded
(dominated convergence, `Φ, ∂ₖΦ, ∂ₖψ ∈ Y_2`).  `∂ₖΦ ∈ Y_2` because `Φ, ΔΦ ∈ Y_2`.

This file fixes the concrete definitions, states each analytic ingredient as a `Prop`, and proves
`fwuAdjTrunc_of` (assembly from the ingredients).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## Definitions -/

/-- The cross product `a × b` of complex 3-vectors (bilinear, not sesquilinear). -/
def crossC (a b : CVec3) : CVec3 :=
  WithLp.toLp 2 ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The curl `∑ⱼ eⱼ × ∂ⱼ Θ` of a (smooth) phase field, derivatives in `y` only. -/
def curlT (Θ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ)) (dy j Θ x)

/-- The gradient `∇a` of a scalar function of `y`, as a complex 3-vector. -/
def gradC (a : Space → ℝ) (y : Space) : CVec3 :=
  WithLp.toLp 2 fun j => ((sd j a y : ℝ) : ℂ)

/-- The transpose of `w ↦ (μ + ½ - ∂_τ + ½ y·∇ - νΔ) w`, namely
`Θ ↦ L₀ Θ + μ Θ - ½ Θ` (compare `(μ + L₀) Θ`: the drift constant is `3/2 - 1 = 1/2` smaller
because `curl (y·∇ψ) = y·∇ curl ψ + curl ψ`). -/
def wOpT (ν μ : ℝ) (Θ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => L0 ν Θ x + (μ : ℂ) • Θ x - (1 / 2 : ℝ) • Θ x

/-- `ψ` is a (Coulomb gauge, decaying) stream potential of `Φ`, with weak `y`-gradient `Dψ`
(source 1351-1362: the potential used for the solenoidal radial cutoff): periodic, measurable,
`curl ψ = Φ`, `div ψ = 0`, `∂ⱼψ = Dψ j ∈ Y_2` weakly, and the Hardy bound `ψ/|y| ∈ Y_2`
(`ψ` itself is only in homogeneous `H¹` in `y`, since `Y_2` is unweighted). -/
structure StreamPot (P : ℝ) (Φ ψ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3) : Prop where
  meas : AEStronglyMeasurable ψ volume
  periodic : ∀ᵐ x : ℝ × Space, ψ (x.1 + P, x.2) = ψ x
  curl : UnforcedLeray.Short.IIb.HasPtwOp P curlT ψ Φ
  sol : IsWeakSolenoidal P ψ
  grad : ∀ j : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (Dψ j) ∧
    UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) ψ (Dψ j)
  hardy : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • ψ x)

/-- The data of the truncation argument: `Φ` and `g` (`MΦ = g`), the potential `ψ` of `Φ` with
gradient `Dψ`, the potential `w` of `g` with gradient `Dw`, and the weak `y`-gradient `DΦ` of `Φ`. -/
structure TruncData where
  Φ : ℝ × Space → CVec3
  g : ℝ × Space → CVec3
  ψ : ℝ × Space → CVec3
  Dψ : Fin 3 → ℝ × Space → CVec3
  w : ℝ × Space → CVec3
  Dw : Fin 3 → ℝ × Space → CVec3
  DΦ : Fin 3 → ℝ × Space → CVec3

/-- The standing hypotheses on the data: `Φ ∈ FWUAdjDom` with `MΦ = g`, `ψ, w` stream potentials of
`Φ, g`, `w = (μ + ½ - ∂_τ + ½ y·∇ - νΔ) ψ` weakly, and `DΦ = ∇Φ ∈ Y_2` weakly. -/
structure TruncHyp (P ν μ : ℝ) (D : TruncData) : Prop where
  dom : FWUAdjDom P ν μ D.Φ D.g
  spΦ : StreamPot P D.Φ D.ψ D.Dψ
  spg : StreamPot P D.g D.w D.Dw
  inter : UnforcedLeray.Short.IIb.HasPtwOp P (wOpT ν μ) D.ψ D.w
  dΦ : ∀ j : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ j) ∧
    UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) D.Φ (D.DΦ j)

/-- The truncated field `Φₙ = curl(χₙ ψ) = χₙ Φ + ∇χₙ × ψ`. -/
def truncPhi (n : ℕ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • D.Φ x + crossC (gradC (cutχ n) x.2) (D.ψ x)

/-- The commutator part with `1/|y|`-size coefficients (Hardy):
`∇χₙ × w + ½ ∇(y·∇χₙ) × ψ - ν ∇Δχₙ × ψ`. -/
def EHardy (n : ℕ) (ν : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => crossC (gradC (cutχ n) x.2) (D.w x)
    + (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)
    - ν • crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)

/-- The commutator part with bounded coefficients:
`(½ y·∇χₙ - νΔχₙ) Φ - 2ν ∑ₖ ∂ₖχₙ ∂ₖΦ - 2ν ∑ₖ ∇∂ₖχₙ × ∂ₖψ`. -/
def EBdd (n : ℕ) (ν : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => ((1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) • D.Φ x
    - (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x
    - (2 * ν) • ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)

/-- The new right-hand side `gₙ = (μ + L₀ᵗ) Φₙ = χₙ g + EHardy + EBdd`. -/
def truncG (n : ℕ) (ν : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • D.g x + EHardy n ν D x + EBdd n ν D x

/-! ## The analytic ingredients -/

/-- **Scaling bounds of the cutoff** (source 1470-1480, "bounded on an escaping annulus"):
`χₙ = ψ(y/(n+1))`; all derivatives of `χₙ` vanish off the annulus `n+1 ≤ |y| ≤ 2(n+1)`, and
(`n+1 ≥ 1`, so `(n+1)⁻ᵏ ≤ (n+1)⁻¹`) `∇χₙ, ∇(y·∇χₙ), ∇Δχₙ = O(1/(n+1))`, while
`y·∇χₙ, Δχₙ, ∂ₖχₙ, ∇∂ₖχₙ = O(1)`, with one constant `C` independent of `n, y`. -/
def CutBounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : Space),
    ((‖y‖ < (n : ℝ) + 1 ∨ 2 * ((n : ℝ) + 1) < ‖y‖) →
      gradC (cutχ n) y = 0 ∧ gradC (radS (cutχ n)) y = 0 ∧ gradC (lapS (cutχ n)) y = 0 ∧
        radS (cutχ n) y = 0 ∧ lapS (cutχ n) y = 0 ∧
        ∀ k : Fin 3, sd k (cutχ n) y = 0 ∧ gradC (sd k (cutχ n)) y = 0) ∧
    ‖gradC (cutχ n) y‖ ≤ C / ((n : ℝ) + 1) ∧
    ‖gradC (radS (cutχ n)) y‖ ≤ C / ((n : ℝ) + 1) ∧
    ‖gradC (lapS (cutχ n)) y‖ ≤ C / ((n : ℝ) + 1) ∧
    |radS (cutχ n) y| ≤ C ∧ |lapS (cutχ n) y| ≤ C ∧
    ∀ k : Fin 3, |sd k (cutχ n) y| ≤ C ∧ ‖gradC (sd k (cutχ n)) y‖ ≤ C

/-- **Biot-Savart** (source 1351-1362; Fourier inversion `ψ̂ = iξ × Φ̂ / |ξ|²` in `y`, phase by
phase, plus Sobolev `ψ ∈ L⁶`, `∇ψ ∈ L²` and Hardy `‖ψ/|y|‖₂ ≤ 2‖∇ψ‖₂` on `ℝ³`): every weakly
solenoidal `Φ ∈ Y_2` has a Coulomb-gauge stream potential. -/
def StreamPotExists : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Φ : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → IsWeakSolenoidal P Φ →
      ∃ (ψ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3), StreamPot P Φ ψ Dψ

/-- **Intertwining** (source 1351-1362): if `Φ ∈ FWUAdjDom` with `(μ + L₀ᵗ) Φ = g` and `ψ, w` are
the Coulomb stream potentials of `Φ, g`, then `w = (μ + ½ - ∂_τ + ½ y·∇ - νΔ) ψ` weakly.  (The
difference is a decaying, divergence-free, curl-free tempered field, hence `0`; equivalently the
degree `-1` homogeneous multiplier `iξ ×/|ξ|²` commutes with `ξ·∇_ξ`, `∂_τ`, `|ξ|²` up to the
shift of the drift constant.) -/
def StreamPotIntertwine : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g ψ w : ℝ × Space → CVec3) (Dψ Dw : Fin 3 → ℝ × Space → CVec3),
      FWUAdjDom P ν μ Φ g → StreamPot P Φ ψ Dψ → StreamPot P g w Dw →
        UnforcedLeray.Short.IIb.HasPtwOp P (wOpT ν μ) ψ w

/-- **`H¹` regularity in `y`** (source 1351-1362): an element of `FWUAdjDom` has weak spatial
gradient in `Y_2` (`‖∇Φ(τ)‖² ≤ ‖Φ(τ)‖ ‖ΔΦ(τ)‖` for a.e. phase `τ`, as `Φ, νΔΦ ∈ Y_2`). -/
def AdjDomGrad : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g →
      ∃ DΦ : Fin 3 → ℝ × Space → CVec3, ∀ j : Fin 3,
        UnforcedLeray.Short.IIb.IsInYr P 2 (DΦ j) ∧
          UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) Φ (DΦ j)

/-- `Φₙ` has `y`-compact support (from `cutχ_eq_zero` and the support part of `CutBounds`). -/
def TruncYCompact : Prop :=
  CutBounds → ∀ (n : ℕ) (D : TruncData), YCompactSupp (truncPhi n D)

/-- **Tail of the cutoff** (dominated convergence, bounded multiplier `1 - χₙ → 0` pointwise):
`‖(1 - χₙ) g‖_{Y_2} → 0` for `g ∈ Y_2`. -/
def TruncTail : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
    Tendsto (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2
      (fun x => (cutχ n x.2 - 1) • g x)) atTop (𝓝 0)

/-- **Hardy commutators vanish** (source 1470-1480; coefficients `O(1/(n+1)) ≤ 2/|y|` on the
annulus, `ψ/|y|, w/|y| ∈ Y_2`, dominated convergence): `EHardy` is measurable and `→ 0` in `Y_2`. -/
def TruncHardyTendsto : Prop :=
  CutBounds → ∀ (P ν : ℝ), 0 < P → ∀ D : TruncData,
    StreamPot P D.Φ D.ψ D.Dψ → StreamPot P D.g D.w D.Dw →
      (∀ n : ℕ, AEStronglyMeasurable (EHardy n ν D) volume) ∧
        Tendsto (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (EHardy n ν D))
          atTop (𝓝 0)

/-- **Bounded commutators vanish** (source 1470-1480; bounded coefficients on an escaping annulus,
`Φ, ∂ₖΦ, ∂ₖψ ∈ Y_2`, dominated convergence): `EBdd` is measurable and `→ 0` in `Y_2`. -/
def TruncBddTendsto : Prop :=
  CutBounds → ∀ (P ν : ℝ), 0 < P → ∀ D : TruncData,
    UnforcedLeray.Short.IIb.IsInYr P 2 D.Φ →
    (∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ j)) →
    (∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (D.Dψ j)) →
      (∀ n : ℕ, AEStronglyMeasurable (EBdd n ν D) volume) ∧
        Tendsto (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (EBdd n ν D))
          atTop (𝓝 0)

/-- `Φₙ, gₙ ∈ Y_2` (finite norms: bounded coefficients on the annulus plus Hardy; periodicity and
measurability from the data). -/
def TruncMemY : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ,
      UnforcedLeray.Short.IIb.IsInYr P 2 (truncPhi n D) ∧
        UnforcedLeray.Short.IIb.IsInYr P 2 (truncG n ν D)

/-- `Φₙ` and `gₙ` are weakly solenoidal (`Φₙ = curl(χₙ ψ)`; `gₙ = curl` of the corresponding
combination of `χₙ w` and `ψ`-commutators; test with `∇φ` and move derivatives by weak `curl`). -/
def TruncSol : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ,
      IsWeakSolenoidal P (truncPhi n D) ∧ IsWeakSolenoidal P (truncG n ν D)

/-- `νΔΦₙ ∈ Y_2` weakly: `Δ(χₙΦ) = χₙ ΔΦ + 2 ∇χₙ·∇Φ + ΔχₙΦ` (with `ΔΦ` from `dom.lapl`) and
`Δ(∇χₙ × ψ) = Δ∇χₙ × ψ + 2 ∂ₖ∇χₙ × ∂ₖψ - ∇χₙ × curl Φ` (`Δψ = -curl Φ`, `curl Φ = ∑ eₖ × ∂ₖΦ`). -/
def TruncLapl : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ,
      ∃ a, UnforcedLeray.Short.IIb.IsInYr P 2 a ∧
        UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (truncPhi n D) a

/-- `𝒯Φₙ ∈ Y_2` weakly (drift commutator `½ (y·∇χₙ) Φ + ½ ∇(y·∇χₙ) × ψ`, bounded by Hardy). -/
def TruncDrift : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ,
      ∃ b, UnforcedLeray.Short.IIb.IsInYr P 2 b ∧
        UnforcedLeray.Short.IIb.HasPtwOp P driftT (truncPhi n D) b

/-- The equation `⟪(μ + L₀)Ψ, Φₙ⟫ = ⟪Ψ, gₙ⟫` for every solenoidal phase test `Ψ` (integration by
parts against the smooth compactly supported `Ψ`, using `dom.equation` with the solenoidal test
`curl(χₙ ·)` built by `Cons.C03.Concrete.isSolTest_projectedPotentialCurlCutoff`-type facts, the
weak `curl` of `ψ`, `inter` and the weak gradients). -/
def TruncEq : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ Ψ, IsSolTest P Ψ →
      pairF P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) (truncPhi n D) = pairF P Ψ (truncG n ν D)

/-! ## Assembly -/

/-- From the existence, intertwining and gradient ingredients, every `FWUAdjDom` pair has data
satisfying `TruncHyp`. -/
theorem truncHyp_exists (h1 : StreamPotExists) (h2 : StreamPotIntertwine) (h3 : AdjDomGrad)
    {P ν μ : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) (hν : 0 < ν) (hμ : 0 < μ + 1 / 4)
    {Φ g : ℝ × Space → CVec3} (hΦ : FWUAdjDom P ν μ Φ g) :
    ∃ D : TruncData, D.Φ = Φ ∧ D.g = g ∧ TruncHyp P ν μ D := by
  obtain ⟨ψ, Dψ, hψ⟩ := h1 P hP Φ hΦ.mem hΦ.sol
  obtain ⟨w, Dw, hw⟩ := h1 P hP g hΦ.mem_g hΦ.sol_g
  obtain ⟨DΦ, hD⟩ := h3 P ν μ hP hP1 hν hμ Φ g hΦ
  exact ⟨⟨Φ, g, ψ, Dψ, w, Dw, DΦ⟩, rfl, rfl,
    ⟨hΦ, hψ, hw, h2 P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hΦ hψ hw, hD⟩⟩

/-- Minkowski for a sum of two measurable fields, from `PhaseLpTri2`. -/
theorem phaseLpNorm_add_le (P : ℝ) (hP : 0 < P) (u v : ℝ × Space → CVec3)
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => u x + v x) ≤
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 u + UnforcedLeray.Short.IIb.phaseLpNorm P 2 v := by
  have h := phaseLpTri2 P (fun x => u x + v x) u (fun _ => 0) hP (hu.add hv) hu
    aestronglyMeasurable_const
  have e1 : (fun x => (u x + v x) - (fun _ : ℝ × Space => (0 : CVec3)) x) = fun x => u x + v x := by
    funext x; simp
  have e2 : (fun x => (u x + v x) - u x) = v := by funext x; simp
  have e3 : (fun x => u x - (fun _ : ℝ × Space => (0 : CVec3)) x) = u := by funext x; simp
  rw [e1, e2, e3] at h
  rw [add_comm] at h
  exact h

/-- **Assembly**: `fwuAdjTrunc` from the analytic ingredients. -/
theorem fwuAdjTrunc_of (hCut : CutBounds) (h1 : StreamPotExists) (h2 : StreamPotIntertwine)
    (h3 : AdjDomGrad) (hY : TruncYCompact) (hT : TruncTail) (hH : TruncHardyTendsto)
    (hB : TruncBddTendsto) (hM : TruncMemY) (hS : TruncSol) (hL : TruncLapl)
    (hD : TruncDrift) (hE : TruncEq) : FWUAdjTrunc := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ ε hε
  obtain ⟨D, rfl, rfl, hD0⟩ := truncHyp_exists h1 h2 h3 hP hP1 hν hμ hΦ
  have hHt := hH hCut P ν hP D hD0.spΦ hD0.spg
  have hBt := hB hCut P ν hP D hΦ.mem (fun j => (hD0.dΦ j).1) (fun j => (hD0.spΦ.grad j).1)
  have hTt := hT P hP D.g hΦ.mem_g
  -- the three norms tend to 0, hence their sum does
  have hsum : Tendsto (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2
        (fun x => (cutχ n x.2 - 1) • D.g x) +
      (UnforcedLeray.Short.IIb.phaseLpNorm P 2 (EHardy n ν D) +
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (EBdd n ν D))) atTop (𝓝 0) := by
    simpa using hTt.add (hHt.2.add hBt.2)
  have hev := (hsum.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  obtain ⟨n, hn⟩ := hev
  refine ⟨truncPhi n D, truncG n ν D, ?_, hY hCut n D, ?_⟩
  · exact
      { mem := (hM hCut P ν μ hP hP1 hν hμ D hD0 n).1
        mem_g := (hM hCut P ν μ hP hP1 hν hμ D hD0 n).2
        sol := (hS hCut P ν μ hP hP1 hν hμ D hD0 n).1
        sol_g := (hS hCut P ν μ hP hP1 hν hμ D hD0 n).2
        lapl := hL hCut P ν μ hP hP1 hν hμ D hD0 n
        drift := hD hCut P ν μ hP hP1 hν hμ D hD0 n
        equation := hE hCut P ν μ hP hP1 hν hμ D hD0 n }
  · have hu : AEStronglyMeasurable (fun x : ℝ × Space => (cutχ n x.2 - 1) • D.g x) volume :=
      (((contDiff_cutχ n).continuous.comp continuous_snd).sub
        continuous_const).aestronglyMeasurable.smul hΦ.mem_g.meas
    have hv : AEStronglyMeasurable (fun x => EHardy n ν D x + EBdd n ν D x) volume :=
      (hHt.1 n).add (hBt.1 n)
    have heq : (fun x => truncG n ν D x - D.g x) =
        fun x => (cutχ n x.2 - 1) • D.g x + (EHardy n ν D x + EBdd n ν D x) := by
      funext x
      simp only [truncG, sub_smul, one_smul]
      abel
    rw [heq]
    refine lt_of_le_of_lt (phaseLpNorm_add_le P hP _ _ hu hv) (lt_of_le_of_lt ?_ hn)
    gcongr
    exact phaseLpNorm_add_le P hP _ _ (hHt.1 n) (hBt.1 n)

end UnforcedLeray.Short.PartIIIb.Concrete
