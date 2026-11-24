import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10

/-!
# `truncLapl`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
With `aΦ = νΔΦ` (from `dom.lapl`), `Δ(χΦ) = χΔΦ + 2∇χ·∇Φ + ΔχΦ` and
`Δ(∇χ × ψ) = Δ∇χ × ψ + 2 ∑ₖ ∂ₖ∇χ × ∂ₖψ + ∇χ × Δψ` with `Δψ = -curl Φ = -∑ₖ eₖ × ∂ₖΦ`
(`div ψ = 0`), so `νΔΦₙ = lapA n ν D aΦ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The cross-product part of `νΔΦₙ`:
`ν ∇Δχ × ψ + 2ν ∑ₖ ∇∂ₖχ × ∂ₖψ - ν ∇χ × curl Φ`, `curl Φ = ∑ₖ eₖ × ∂ₖΦ`. -/
def lapCross (n : ℕ) (ν : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => ν • crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)
    + (2 * ν) • ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)
    - ν • crossC (gradC (cutχ n) x.2)
        (∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))

/-- The candidate `νΔΦₙ`: `χ aΦ + 2ν ∑ₖ ∂ₖχ ∂ₖΦ + νΔχ Φ +` `lapCross`. -/
def lapA (n : ℕ) (ν : ℝ) (D : TruncData) (aΦ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • aΦ x + (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x
    + (ν * lapS (cutχ n) x.2) • D.Φ x + lapCross n ν D x

/-- `lapA ∈ Y_2` (bounded coefficients on `Φ, ∂ₖΦ, aΦ`, `∂ₖψ`; Hardy-size coefficient `∇Δχ` on
`ψ/|y|`; helpers `isInYr_smul_of_bdd`, `isInYr_cross_hardy`, `isInYr_cross_bdd`,
`isInYr_add2` of `AdjTruncOrg/TruncMemY.lean`). -/
def LaplMem : Prop :=
  CutBounds → ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ aΦ : ℝ × Space → CVec3,
      UnforcedLeray.Short.IIb.IsInYr P 2 aΦ → UnforcedLeray.Short.IIb.IsInYr P 2 (lapA n ν D aΦ)

/-- `νΔΦₙ = lapA` weakly. -/
def LaplPair : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ D : TruncData, TruncHyp P ν μ D → ∀ n : ℕ, ∀ aΦ : ℝ × Space → CVec3,
      UnforcedLeray.Short.IIb.IsInYr P 2 aΦ →
      UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) D.Φ aΦ →
        UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (truncPhi n D) (lapA n ν D aΦ)

/-- Weak product rule for `νΔ`: if `νΔu = a` and `∂ₖu = du k` weakly (`HasPtwOp (-dy k) u (du k)`),
then `νΔ(c u) = c a + 2ν ∑ₖ ∂ₖc du k + νΔc u` for smooth `c = c(y)` (from `lapT_mulT_apply`,
phase tests stable under `c`, and one integration by parts for `∂ₖ(∂ₖc Θ)`); `u, a, du k` locally
`L²`. -/
def WeakLapMul : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ (c : Space → ℝ), ContDiff ℝ ∞ c →
    ∀ (u a : ℝ × Space → CVec3) (du : Fin 3 → ℝ × Space → CVec3),
      LocL2 P u → LocL2 P a → (∀ k, LocL2 P (du k)) →
      UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) u a →
      (∀ k, UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy k Θ) u (du k)) →
        UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (fun x => c x.2 • u x)
          (fun x => c x.2 • a x + (2 * ν) • ∑ k : Fin 3, sd k c x.2 • du k x
            + (ν * lapS c x.2) • u x)

/-- `Δψ = -curl Φ` weakly for a Coulomb potential: `νΔψ = -ν ∑ₖ eₖ × ∂ₖΦ`
(`ΔΘ = ∇ div Θ - curl curl Θ`, `StreamPot.sol`, `StreamPot.curl` twice, and the weak gradient of
`Φ`). -/
def WeakLapPsi : Prop :=
  ∀ (P ν μ : ℝ) (D : TruncData), TruncHyp P ν μ D →
    UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) D.ψ
      (fun x => -ν • ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))

/-- Linearity of the relation `HasPtwOp (nuLapT ν)` for locally `L²` fields (sums, real scalar
multiples, finite sums over `Fin 3`, and `u ↦ e × u` for a fixed `e : CVec3`, with `a ↦ e × a`:
`e × ΔΘ = Δ(e × Θ)` and `(e × Θ)·u = -Θ·(e × u)`). -/
def WeakLapLin : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ u1 u2 a1 a2 : ℝ × Space → CVec3,
    LocL2 P u1 → LocL2 P u2 → LocL2 P a1 → LocL2 P a2 →
      UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) u1 a1 →
      UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) u2 a2 →
        UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (fun x => u1 x + u2 x) (fun x => a1 x + a2 x) ∧
        (∀ s : ℝ, UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (fun x => s • u1 x) (fun x => s • a1 x)) ∧
        (∀ e : CVec3, UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (fun x => crossC e (u1 x))
          (fun x => crossC e (a1 x)))

/-- Assembly of `TruncLapl`. -/
theorem truncLapl_of (h1 : LaplMem) (h2 : LaplPair) : TruncLapl := by
  intro hCut P ν μ hP hP1 hν hμ D hD n
  obtain ⟨aΦ, haΦ, hpair⟩ := hD.dom.lapl
  exact ⟨lapA n ν D aΦ, h1 hCut P ν μ hP hP1 hν hμ D hD n aΦ haΦ,
    h2 P ν μ hP hP1 hν hμ D hD n aΦ haΦ hpair⟩

end UnforcedLeray.Short.PartIIIb.Concrete
