import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg
import UnforcedLeray.Short.PartIIb.Bridge.Adjoint

/-!
# `truncEq`: decomposition into the curl route

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Route: `Φₙ = curl(χₙ ψ)` weakly, `curl` intertwines `L₀ + μ` with `wOpT`, `inter`
(`⟪wOpT Θ, ψ⟫ = ⟪Θ, w⟫`), the commutator `[wOpT, χₙ]`, and `spg` (`⟪curl Θ, w⟫ = ⟪Θ, g⟫`).
Each step is a `Prop` below; `truncEq_of` assembles them into `TruncEq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- (a) Pointwise: `curl` intertwines `L₀ + μ` with `wOpT` on smooth phase tests
(`curl (y·∇Ψ) = y·∇ curl Ψ + curl Ψ`, symmetry of second derivatives; source 1351-1362). -/
def TruncCurlIntertwine : Prop :=
  ∀ (P ν μ : ℝ) (Ψ : ℝ × Space → CVec3), IsPhaseTest P Ψ →
    curlT (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) = wOpT ν μ (curlT Ψ)

/-- (b) `χₙ • curl Ψ` is a phase test for a phase test `Ψ` (smooth, periodic, `y`-compact). -/
def TruncCutCurlTest : Prop :=
  ∀ (P : ℝ) (n : ℕ) (Ψ : ℝ × Space → CVec3), IsPhaseTest P Ψ →
    IsPhaseTest P (fun x => cutχ n x.2 • curlT Ψ x)

/-- (c) Weak curl move: `⟪Θ, curl(χₙ ψ)⟫ = ⟪χₙ curl Θ, ψ⟫` for phase tests `Θ`
(`spΦ.curl` applied to the phase test `χₙ Θ`, product rule `curl(χΘ) = χ curl Θ + ∇χ × Θ`, and the
triple product identity `Θ·(∇χ × ψ) = -(∇χ × Θ)·ψ`). -/
def TruncCurlMove : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
      pairF P Θ (truncPhi n D) = pairF P (fun x => cutχ n x.2 • curlT Θ x) D.ψ

/-- (d) Commutator of `wOpT` with `χₙ` against the stream potential `ψ`, for `Z = curl Ψ`:
`⟪χ wOpT Z, ψ⟫ = ⟪wOpT(χ Z), ψ⟫ + ⟪Ψ, (EHardy - ∇χ × w) + EBdd⟫` (pointwise
`χ wOpT Z - wOpT(χ Z) = 2ν ∑ₖ ∂ₖχ ∂ₖZ + νΔχ Z - ½ (y·∇χ) Z`, then weak integration by parts with
`spΦ.grad`, the weak `curl` of `Dψ`, `dΦ`; the pieces are exactly those of `EHardy`, `EBdd`). -/
def TruncCommutator : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest P Ψ →
      pairF P (fun x => cutχ n x.2 • wOpT ν μ (curlT Ψ) x) D.ψ =
        pairF P (wOpT ν μ (fun x => cutχ n x.2 • curlT Ψ x)) D.ψ +
        pairF P Ψ (fun x => (EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) + EBdd n ν D x)

/-- (e) `spg` step: `⟪χₙ curl Ψ, w⟫ = ⟪Ψ, χₙ g + ∇χₙ × w⟫` for phase tests `Ψ`
(`spg.curl` with the phase test `χₙ Ψ`, product rule and triple product). -/
def TruncSpgStep : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest P Ψ →
      pairF P (fun x => cutχ n x.2 • curlT Ψ x) D.w =
        pairF P Ψ (fun x => cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x))

/-- (f) Additivity of the pairing against a phase test for the two fields of the splitting of
`gₙ` (all locally `L²` on the `y`-compact support of the test: `g ∈ Y_2`, `w/|y|, ψ/|y| ∈ Y_2`,
`Φ, DΦ, Dψ ∈ Y_2`, bounded cutoff coefficients). -/
def TruncSplit : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ Ψ : ℝ × Space → CVec3, IsPhaseTest P Ψ →
      pairF P Ψ (fun x =>
        (cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x)) +
        ((EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) + EBdd n ν D x)) =
      pairF P Ψ (fun x => cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x)) +
      pairF P Ψ (fun x => (EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) + EBdd n ν D x)

/-- **Assembly**: `TruncEq` from the six ingredients. -/
theorem truncEq_of (ha : TruncCurlIntertwine) (hb : TruncCutCurlTest) (hc : TruncCurlMove)
    (hd : TruncCommutator) (he : TruncSpgStep) (hf : TruncSplit) : TruncEq := by
  intro hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨ
  have hΨp : IsPhaseTest P Ψ := hΨ.1
  have hΨ' : IsPhaseTest P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) := by
    have h := (UnforcedLeray.Short.IIb.isPhaseTest_L0 hΨp ν).add (hΨp.const_smul (μ : ℂ))
    exact h
  have hcurl := ha P ν μ Ψ hΨp
  have hG : truncG n ν D = fun x =>
      (cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x)) +
        ((EHardy n ν D x - crossC (gradC (cutχ n) x.2) (D.w x)) + EBdd n ν D x) := by
    funext x
    simp only [truncG]
    abel
  rw [hc hCut P ν μ hP hP1 hν hμ D hD n _ hΨ', hcurl,
    hd hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨp,
    hD.inter _ (hb P n Ψ hΨp), he hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨp, hG,
    hf hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨp]

end UnforcedLeray.Short.PartIIIb.Concrete
