import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The chart coefficient `s^{-1/2} ĥ_A` in the `(r, z)` order (source 4980, 4991-4997):
the representative of `B.hA A` fixed by `IsAffinePinned`. -/
def hhatChart (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  fun p => merOf ((Real.sqrt p.1)⁻¹ • hhatA ν ε χf A p.1 p.2)

/-- **Sub-lemma T** (a.e. transfer, source 4991-4997 with `IsAffinePinned`): the pairing of a
gradient of a phase test with the lift of `B.hA A` equals that with the lift of the explicit
chart representative `hhatChart`.  Proof: `IsAffinePinned` gives equality of the two chart
coefficients a.e. on the body measure; `liftFun_congr_ae` (`Lib/AxisymmetricB/Jv.lean:213`,
`P = 2εc = 2c/R`) turns it into a.e. equality on `phaseμ P` of the lifts, hence of the
integrands of `pairF`, hence of the pairings (`phaseInt` is the integral against the
restricted volume on the phase cell; both fields are in `L²`, so the integrals exist). -/
def HhatTransfer {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (ι : Aff →ₗ[ℝ] (ℝ → Mat3))
    (χf : ℝ → ℝ) (ε : ℝ) : Prop :=
  ∀ (A : Aff) (φ : ℝ × Space → ℂ), IsPhaseTest (2 * ε * c) φ →
    pairF (2 * ε * c) (gradT φ) (velPhys ε⁻¹ c (B.hA A)) =
      pairF (2 * ε * c) (gradT φ) (velPhys ε⁻¹ c (hhatChart ν ε χf (ι A)))

/-- **Sub-lemma S** (source 4991-4997): the physical field of `ĥ_A` is solenoidal: the
cylindrical stream function of `ĥ_A` is `rψ^p_A` (`h^p_A = J∇ψ^p_A`, `MerJIdentity` 4993,
`HpIsJGrad`; ring-chart rules 5036-5039 `∂_r = √s(∂_q - ε𝒦)`, `∂_z = √s∂_η`), `ĥ_A`
vanishes for `s ≥ 1.1/ν` (`HhatYoungPointwise`), so `⟨∇φ, ĥ⟩ = -⟨φ, div ĥ⟩ = 0` by integration
by parts against the phase test (Gaussian decay: `Concrete/SummableProof.lean`). -/
def HhatChartSolenoidal (ν ε c : ℝ) {Aff : Type} [AddCommMonoid Aff] [Module ℝ Aff] (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) (χf : ℝ → ℝ) :
    Prop :=
  ∀ A : Aff, IsWeakSolenoidal (2 * ε * c) (velPhys ε⁻¹ c (hhatChart ν ε χf (ι A)))

theorem hhatSolenoidal_core {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ} {ε : ℝ}
    (hT : HhatTransfer B ι χf ε) (hS : HhatChartSolenoidal ν ε c ι χf) :
    HhatSolenoidal B ε := by
  intro A φ hφ
  rw [hT A φ hφ]
  exact hS A φ hφ

end UnforcedLeray.Short.PartIIIb.Concrete
