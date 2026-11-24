import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4
import UnforcedLeray.Lib.AxisymmetricB.Stream

/-!
# `HhatChartSolenoidal`: definitions and sub-statements (source 4991-4997, 5036-5039)

Source of record: `the November 2 reference manuscript`.

The physical stream function of `ĥ_A` is `ρ ψ^p_A(s, q, η)` (`Axi.ringStream`, `ρ = R/√s`,
`R = ε⁻¹`; source 4991-4997), and `ĥ_A` is `Axi.Nv` of its chart profile `Axi.ringStreamProfile`
`= (-ψ_η, ψ_q + ε(ψ - 2sψ_s - ηψ_η))` (source 5036-5039: `∂_r = √s(∂_q - ε𝒦)`,
`∂_z = √s ∂_η`, `h^p = J∇ψ^p`).  No measurable representative is needed: `phaseInt` is an
iterated integral, so for each phase `τ` the spatial integral is shown to vanish, the axis being
null.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The chart function `(s, (q, η)) ↦ ψ^p_A(s, (q, η))` (source 4991, 4996). -/
def psiRing (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → ℝ :=
  fun p => psipA ν χf A p.1 p.2

/-- (S1) `ψ^p_A` is `C²` jointly in `(s, q, η)` on `s > 0` (source 4991: "the sums and their
required derivatives converge by Gaussian decay"; `A ∈ 𝒜` is `C⁶` on `(0,∞)`, `A^y = χ_f A`). -/
def PsiRingSmooth (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 2 (psiRing ν χf A) (Ioi 0 ×ˢ univ)

/-- (S2) `ĥ_A` is invariant under the lattice translations `q ↦ q + n c`, `c = ν⁻²`
(the sums of source 4963-4985 run over `j ∈ ℤ`). -/
def HhatAPeriodic (ν ε : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (n : ℤ),
    hhatA ν ε χf A s (x.1 + n * cOf ν, x.2) = hhatA ν ε χf A s x

/-- (S3) Ring-chart identity (source 4993-4996, 5036-5039): for `s > 0`, the chart coefficient
`s^{-1/2} ĥ_A` is `(-ψ_η, ψ_q + ε(ψ - 2sψ_s - ηψ_η))` (`h^p = J∇ψ^p` and the `(r,z)` rules). -/
def HhatRingProfile (ν ε : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ A : ℝ → Mat3, HpIsJGrad ν χf A → ∀ p : Chart, 0 < p.1 →
    DifferentiableAt ℝ (psiRing ν χf A) p →
      hhatChart ν ε χf A p = ringStreamProfile ε⁻¹ (psiRing ν χf A) p

/-- (S4) Off the axis, the physical field of `ĥ_A` is the stream lift of `ρ ψ^p_A`
(`ringStreamLift_components`, `perExt` removed by (S2)). -/
def HhatNvStream (ν ε c : ℝ) (χf : ℝ → ℝ) : Prop :=
  c = cOf ν → HhatAPeriodic ν ε χf → HhatRingProfile ν ε χf → ∀ A : ℝ → Mat3,
    HpIsJGrad ν χf A → ∀ (τ : ℝ) (y : Space), y ∉ axis →
      DifferentiableAt ℝ (psiRing ν χf A) (chart ε⁻¹ τ y) →
        Nv ε⁻¹ (perExt c (hhatChart ν ε χf A)) τ y = streamLift (ringStream ε⁻¹ τ (psiRing ν χf A)) y

/-- (S5) `ρ ↦ ρ ψ(R²/ρ², …)` is `C²` on `ρ > 0` when `ψ` is `C²` on `s > 0`. -/
def RingStreamSmooth : Prop :=
  ∀ (R τ : ℝ) (φ : Chart → ℝ), R ≠ 0 → ContDiffOn ℝ 2 φ (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ 2 (ringStream R τ φ) (Ioi 0 ×ˢ univ)

/-- (S6) Young support (source 4953-4956, 4996; `HhatYoungPointwise`): `ψ^p_A = 0` for
`s ≥ 1.1/ν`, so the ring stream vanishes for `0 < ρ < ρ₀ = R√(ν/1.1)`. -/
def RingStreamYoung (ν : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → 0 < ν → ∀ (R : ℝ), 0 < R → ∀ (A : ℝ → Mat3) (τ : ℝ),
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ p : ℝ × ℝ, 0 < p.1 → p.1 < ρ0 → ringStream R τ (psiRing ν χf A) p = 0

/-- (S7) Weak integration by parts (source 4997): a stream of class `C²` on `ρ > 0` vanishing
near the axis lifts to a field `F` with `div F = 0` (`div_streamLift_eq_zero`), `C¹` on `ℝ³` after
setting it `0` on the (null) axis; so `∫ ∇φ·F = -∫ φ div F = 0` for a phase test `φ` at
every phase `τ` (bounded spatial support). -/
def StreamLiftIbp : Prop :=
  ∀ (P : ℝ) (Ψ : ℝ × ℝ → ℝ), ContDiffOn ℝ 2 Ψ (Ioi 0 ×ˢ univ) →
    ∀ ρ0 : ℝ, 0 < ρ0 → (∀ p : ℝ × ℝ, 0 < p.1 → p.1 < ρ0 → Ψ p = 0) →
      ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → ∀ τ : ℝ,
        ∫ y, dotL (gradT φ (τ, y)) (B0412.realC (streamLift Ψ y)) = 0

end UnforcedLeray.Short.PartIIIb.Concrete
