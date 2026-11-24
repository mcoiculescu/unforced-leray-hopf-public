import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `truncSol`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`Φₙ = curl(χₙ ψ)` and `gₙ = curl hₙ` weakly, with
`hₙ = χₙ w + (½ y·∇χₙ - νΔχₙ) ψ - 2ν ∑ₖ ∂ₖχₙ ∂ₖψ`
(using `curl ∂ₖψ = ∂ₖΦ`, `curl w = g`); a weak curl is weakly solenoidal since `curl ∇φ = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- `f` is locally `L²` in the sense needed to pair with compactly supported phase tests:
`f ∈ Y_2` or the Hardy quotient `f/|y| ∈ Y_2`. -/
def LocL2 (P : ℝ) (f : ℝ × Space → CVec3) : Prop :=
  UnforcedLeray.Short.IIb.IsInYr P 2 f ∨
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • f x)

/-- A weak curl is weakly solenoidal (`curl ∇φ = 0`, `∇φ` a phase test). -/
def WeakSolOfCurl : Prop :=
  ∀ (P : ℝ) (u v : ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.HasPtwOp P curlT u v → IsWeakSolenoidal P v

/-- Weak product rule for the curl: `curl(c u) = c v + ∇c × u` if `curl u = v` weakly, for a smooth
`c = c(y)` (phase tests are stable under multiplication by `c`; all pairings are against compactly
supported tests, so only local `L²` of `u, v` is used). -/
def WeakCurlMul : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (c : Space → ℝ), ContDiff ℝ ∞ c →
    ∀ u v : ℝ × Space → CVec3, LocL2 P u → LocL2 P v →
      UnforcedLeray.Short.IIb.HasPtwOp P curlT u v →
        UnforcedLeray.Short.IIb.HasPtwOp P curlT (fun x => c x.2 • u x)
          (fun x => c x.2 • v x + crossC (gradC c x.2) (u x))

/-- The weak curl commutes with the weak `y`-derivative: `curl ∂ₖψ = ∂ₖΦ` weakly (twice
integrating by parts, `curlT (dy k Θ) = dy k (curlT Θ)`). -/
def WeakCurlDeriv : Prop :=
  ∀ (P ν μ : ℝ) (D : TruncData), TruncHyp P ν μ D → ∀ j : Fin 3,
    UnforcedLeray.Short.IIb.HasPtwOp P curlT (D.Dψ j) (D.DΦ j)

/-- Linearity of the weak curl relation, for locally `L²` fields (needs integrability of the
pairings to split sums). -/
def WeakCurlLin : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ u1 u2 v1 v2 : ℝ × Space → CVec3,
    LocL2 P u1 → LocL2 P u2 → LocL2 P v1 → LocL2 P v2 →
      UnforcedLeray.Short.IIb.HasPtwOp P curlT u1 v1 →
      UnforcedLeray.Short.IIb.HasPtwOp P curlT u2 v2 →
        UnforcedLeray.Short.IIb.HasPtwOp P curlT (fun x => u1 x + u2 x) (fun x => v1 x + v2 x) ∧
        ∀ s : ℝ, UnforcedLeray.Short.IIb.HasPtwOp P curlT (fun x => s • u1 x) (fun x => s • v1 x)

/-- The potential `hₙ` of `gₙ`: `χₙ w + (½ y·∇χₙ - νΔχₙ) ψ - 2ν ∑ₖ ∂ₖχₙ ∂ₖψ`. -/
def truncH (n : ℕ) (ν : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • D.w x
    + ((1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) • D.ψ x
    - (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.Dψ k x

/-- `gₙ = curl hₙ` weakly (from `WeakCurlMul` for `c = χₙ, ½ y·∇χₙ - νΔχₙ, ∂ₖχₙ` applied to
`(w,g), (ψ,Φ), (∂ₖψ,∂ₖΦ)`, `WeakCurlDeriv`, `WeakCurlLin`, and linearity of `∇` in `c`; compare
the formula of `gₙ` in `AdjTruncOrg.lean`). -/
def TruncGCurl : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ,
      UnforcedLeray.Short.IIb.HasPtwOp P curlT (truncH n ν D) (truncG n ν D)

/-- Assembly of `TruncSol`. -/
theorem truncSol_of (h1 : WeakSolOfCurl) (h2 : WeakCurlMul) (h3 : TruncGCurl) : TruncSol := by
  intro _hCut P ν μ hP hP1 hν hμ D hD n
  have hΦcurl : UnforcedLeray.Short.IIb.HasPtwOp P curlT (fun x => cutχ n x.2 • D.ψ x)
      (truncPhi n D) :=
    h2 P hP (cutχ n) (contDiff_cutχ n) D.ψ D.Φ (Or.inr hD.spΦ.hardy) (Or.inl hD.dom.mem)
      hD.spΦ.curl
  exact ⟨h1 P _ _ hΦcurl, h1 P _ _ (h3 P ν μ hP hP1 hν hμ D hD n)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
