import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# Decomposition of `truncDrift` (weak drift of the truncated field `Φₙ = χₙ Φ + ∇χₙ × ψ`)

Source: `the November 2 reference manuscript`
lines 1334-1337, 1351-1362, 1470-1480.

Mathematics.  For a phase test `Θ` write `c = χₙ`, `g = ∇c`, `rg = (y·∇∂ⱼ c)ⱼ = ∇(y·∇c) - ∇c`.

* `driftT (cΘ) = c driftT Θ + ½ (y·∇c) Θ` and `driftT (g × Θ) = g × driftT Θ + ½ rg × Θ`.
* `driftT = -wOpT - νΔ + μ + ½` (`driftT_eq_wOpT_pointwise`; `w = (μ + ½ - ∂_τ + ½ y·∇ - νΔ) ψ`,
  source 1470-1480), so with `inter` and `Δψ = -curl Φ`
  (weak, from `spΦ.curl`, `spΦ.sol`, `dΦ`):
  `⟪driftT Θ, ψ⟫ = ⟪Θ, (μ+½)ψ - w + ν curl Φ⟫`.
* triple product `A·(g×ψ) = -ψ·(g×A)`, `⟪g×Θ,u⟫ = -⟪Θ,g×u⟫`.

Together `⟪driftT Θ, Φₙ⟫ = ⟪Θ, driftB⟫` with
`driftB = c b_Φ - ½ (y·∇c) Φ + crossB`,
`crossB = -g×w + ν g×curlΦ + (μ+½) g×ψ - ½ (∇(y·∇c) - ∇c)×ψ`
(all coefficients of `crossB` are supported on the annulus and bounded by `C/(n+1) ≤ 2C/|y|`, so
`crossB ∈ Y_2` by Hardy for `ψ/|y|, w/|y|` and boundedness for `curlΦ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The curl `∑ₖ eₖ × ∂ₖΦ` of `Φ`, from the weak gradients `DΦ k` (source 1351-1362). -/
def curlD (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x)

/-- The part of the weak drift of `Φₙ` coming from `∇χₙ × ψ`:
`-g×w + ν g×curlΦ + (μ+½) g×ψ - ½ (∇(y·∇χₙ) - ∇χₙ)×ψ`, `g = ∇χₙ`. -/
def crossB (n : ℕ) (ν μ : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => -crossC (gradC (cutχ n) x.2) (D.w x)
    + ν • crossC (gradC (cutχ n) x.2) (curlD D x)
    + (μ + 1 / 2 : ℝ) • crossC (gradC (cutχ n) x.2) (D.ψ x)
    - (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)

/-- The weak drift `b` of `Φₙ`, given the weak drift `bΦ` of `Φ`:
`χₙ bΦ - ½ (y·∇χₙ) Φ + crossB`. -/
def driftB (n : ℕ) (ν μ : ℝ) (D : TruncData) (bΦ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • bΦ x - ((1 / 2 : ℝ) * radS (cutχ n) x.2) • D.Φ x + crossB n ν μ D x

/-- **Calculus** (product rule): for smooth `c` and smooth `Θ`,
`driftT (∇c × Θ) = ∇c × driftT Θ + ½ (∇(y·∇c) - ∇c) × Θ` (uses `∂_j (y·∇c) = ∂_j c + y·∇ ∂_j c`
and symmetry of second derivatives; compare `driftT_mulT_apply` in `Lib/PhaseSpace/CutoffCalc`). -/
def CrossDriftCalc : Prop :=
  ∀ (c : Space → ℝ), ContDiff ℝ ∞ c → ∀ (Θ : ℝ × Space → CVec3), ContDiff ℝ ∞ Θ →
    ∀ p : ℝ × Space,
      driftT (fun q => crossC (gradC c q.2) (Θ q)) p =
        crossC (gradC c p.2) (driftT Θ p) +
          (1 / 2 : ℝ) • crossC (gradC (radS c) p.2 - gradC c p.2) (Θ p)

/-- `c Θ` and `∇c × Θ` are phase tests for a smooth `c` and a phase test `Θ`. -/
def CrossPhaseTest : Prop :=
  ∀ (P : ℝ) (c : Space → ℝ), ContDiff ℝ ∞ c → ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
    IsPhaseTest P (fun q => crossC (gradC c q.2) (Θ q)) ∧
      IsPhaseTest P (fun q => c q.2 • Θ q)

/-- **Weak Laplacian of the stream potential** (`Δψ = -curl Φ`, source 1351-1362): for a phase test
`Θ`, `⟪ΔΘ, ψ⟫ = -⟪Θ, curl Φ⟫`.  (From `spΦ.curl : ⟪curlT Θ', ψ⟫ = ⟪Θ', Φ⟫`, `spΦ.sol` and
`dΦ`: `ΔΘ = ∇ div Θ - curl curl Θ`, weak curl of `Φ` via the weak gradients.) -/
def LapPsi : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
      pairF P (lapT Θ) D.ψ = - pairF P Θ (curlD D)

/-- **Weak drift of the stream potential** (from `inter`, the identity
`driftT Θ = μ Θ - νΔΘ - wOpT Θ` and `LapPsi`):
`⟪driftT Θ, ψ⟫ = ⟪Θ, (μ+½)ψ - w + ν curl Φ⟫`. -/
def DriftPsi : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
      pairF P (driftT Θ) D.ψ = pairF P Θ (fun x => (μ + 1 / 2 : ℝ) • D.ψ x - D.w x + ν • curlD D x)

/-- **The `χₙ Φ` part**: `⟪driftT Θ, χₙ Φ⟫ = ⟪Θ, χₙ bΦ - ½ (y·∇χₙ) Φ⟫` (product rule for
`driftT (χₙ Θ)` and `dom.drift`). -/
def PhiDriftPair : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ (n : ℕ) (bΦ : ℝ × Space → CVec3),
      UnforcedLeray.Short.IIb.IsInYr P 2 bΦ →
      UnforcedLeray.Short.IIb.HasPtwOp P driftT D.Φ bΦ →
      ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
        pairF P (driftT Θ) (fun x => cutχ n x.2 • D.Φ x) =
          pairF P Θ (fun x => cutχ n x.2 • bΦ x - ((1 / 2 : ℝ) * radS (cutχ n) x.2) • D.Φ x)

/-- **The `∇χₙ × ψ` part**: `⟪driftT Θ, ∇χₙ × ψ⟫ = ⟪Θ, crossB⟫` (from `CrossDriftCalc`,
`CrossPhaseTest`, `DriftPsi` applied to `∇χₙ × Θ`, and the triple-product identities). -/
def CrossDriftPair : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ (n : ℕ) (Θ : ℝ × Space → CVec3), IsPhaseTest P Θ →
      pairF P (driftT Θ) (fun x => crossC (gradC (cutχ n) x.2) (D.ψ x)) =
        pairF P Θ (crossB n ν μ D)

/-- **Pairing identity**: `⟪driftT Θ, Φₙ⟫ = ⟪Θ, driftB⟫` for phase tests (sum of `PhiDriftPair` and
`CrossDriftPair`; needs integrability of each summand against the compactly supported `Θ`, from
`Φ ∈ Y_2` and `ψ/|y| ∈ Y_2`). -/
def DriftPairIdent : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ (n : ℕ) (bΦ : ℝ × Space → CVec3),
      UnforcedLeray.Short.IIb.IsInYr P 2 bΦ →
      UnforcedLeray.Short.IIb.HasPtwOp P driftT D.Φ bΦ →
      ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
        pairF P (driftT Θ) (truncPhi n D) = pairF P Θ (driftB n ν μ D bΦ)

/-- **Membership**: `driftB ∈ Y_2` (coefficients of `crossB` supported on the annulus and
`O(1/(n+1))`; Hardy for `ψ/|y|, w/|y|`, boundedness against `curlΦ ∈ Y_2` and `Φ, bΦ ∈ Y_2`;
helpers `isInYr_cross_hardy`, `isInYr_cross_bdd`, `isInYr_smul_of_bdd`, `isInYr_add2` in
`AdjTruncOrg/TruncMemY.lean`). -/
def DriftBMem : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ (n : ℕ) (bΦ : ℝ × Space → CVec3),
      UnforcedLeray.Short.IIb.IsInYr P 2 bΦ →
        UnforcedLeray.Short.IIb.IsInYr P 2 (driftB n ν μ D bΦ)

/-- `truncDrift` from the pairing identity and the membership. -/
theorem truncDrift_of (hPair : DriftPairIdent) (hMem : DriftBMem) : TruncDrift := by
  intro hCut P ν μ hP hP1 hν hμ D hD n
  obtain ⟨bΦ, hb, hbd⟩ := hD.dom.drift
  exact ⟨driftB n ν μ D bΦ, hMem hCut P ν μ hP hP1 hν hμ D hD n bΦ hb,
    fun Θ hΘ => hPair P ν μ hP hP1 hν hμ D hD n bΦ hb hbd Θ hΘ⟩

end UnforcedLeray.Short.PartIIIb.Concrete
