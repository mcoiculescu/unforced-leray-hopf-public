import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF

/-!
# Decomposition of `FWUSub` (source 1580-1583, 2666-2700)

Source: `the November 2 reference manuscript`.
`FWUSub` follows from the a.e. linearity of the lift (`FWUSubAE`), the integrability of the
pairings of lifts of `VelG` against the test fields (`FWUSubInt`), and linearity of `pairF`
(proved here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_eq_restrictedProductIntegral)

/-- A.e. linearity of the lift along `VelG` differences (source 1580-1583, 2666-2700): the
`VelG`-difference is the a.e. difference on the body measure `ageμ.withDensity (π g⁻²)`, whose null
sets pull back to `volume`-null sets under the lift (`velPhys = realC ∘ ((√π R)•liftFun R c ·)`,
`liftFun_sub`, `liftFun_congr_ae` of `Lib/AxisymmetricB/Jv.lean`, `Lp.coeFn_sub`, `realC` additive,
density positive: `ginv_pos`/`gainG` positivity). -/
def FWUSubAE (c γ ν ε : ℝ) : Prop :=
  0 < c → 0 < ν → 0 < ε →
    ∀ b b' : VelG c γ ν,
      velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) =ᵐ[volume]
        fun x => velPhys ε⁻¹ c b x - velPhys ε⁻¹ c b' x

/-- Integrability of pairings (source 2666-2700, 1341-1344): for `b : VelG`, the lift `velPhys b`
is in `L²_loc` of the phase cell (`memLp_liftFun`, density comparison on the compact support),
tests are compactly supported in space (`gradT φ` of a phase test, and
`L0T ν Φ + μ Φ` of a solenoidal test: support-propagation for `L0T`, which is a differential
operator), so `dotL (H x) (velPhys b x)` is integrable over `phaseCell (2εc)`
(`integrable_dotL_of_memLp_compactFirst`, `SpatialProductCellQuadraticGuard.lean:175`). -/
def FWUSubInt (c γ ν ε μ : ℝ) : Prop :=
  0 < c → 0 < ν → 0 < ε →
    ∀ b : VelG c γ ν, ∀ H : ℝ × Space → CVec3,
      ((∃ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ ∧ H = gradT φ) ∨
        (∃ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ ∧
          H = fun x => L0T ν Φ x + (μ : ℂ) • Φ x)) →
      Integrable (fun x => dotL (H x) (velPhys ε⁻¹ c b x)) (volume.restrict (phaseCell (2 * ε * c)))

theorem fwuSub_of {c γ ν ε μ : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hA : FWUSubAE c γ ν ε) (hI : FWUSubInt c γ ν ε μ) : FWUSub c γ ν ε μ := by
  intro b b' rhs rhs' h1 h2
  have : Fact (0 < 2 * ε * c) := ⟨by positivity⟩
  have hae := hA hc hν hε b b'
  -- pairing of the difference
  have key : ∀ H : ℝ × Space → CVec3,
      ((∃ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ ∧ H = gradT φ) ∨
        (∃ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ ∧
          H = fun x => L0T ν Φ x + (μ : ℂ) • Φ x)) →
      pairF (2 * ε * c) H (velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid)) =
        pairF (2 * ε * c) H (velPhys ε⁻¹ c b) - pairF (2 * ε * c) H (velPhys ε⁻¹ c b') := by
    intro H hH
    have i1 := hI hc hν hε b H hH
    have i2 := hI hc hν hε b' H hH
    have hpt : ∀ x, dotL (H x) (velPhys ε⁻¹ c b x - velPhys ε⁻¹ c b' x) =
        dotL (H x) (velPhys ε⁻¹ c b x) - dotL (H x) (velPhys ε⁻¹ c b' x) := by
      intro x; simp [map_sub]
    have i3 : Integrable (fun x => dotL (H x) (velPhys ε⁻¹ c b x - velPhys ε⁻¹ c b' x))
        (volume.restrict (phaseCell (2 * ε * c))) := by
      have := i1.sub i2
      refine this.congr (ae_of_all _ fun x => (hpt x).symm)
    have hae' : ∀ᵐ x ∂(volume.restrict (phaseCell (2 * ε * c))),
        velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x =
          velPhys ε⁻¹ c b x - velPhys ε⁻¹ c b' x := ae_restrict_of_ae hae
    have i4 : Integrable (fun x => dotL (H x)
        (velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x))
        (volume.restrict (phaseCell (2 * ε * c))) :=
      i3.congr (hae'.mono fun x hx => by simp only [hx])
    rw [pairF_eq_restrictedProductIntegral i4, pairF_eq_restrictedProductIntegral i1,
      pairF_eq_restrictedProductIntegral i2]
    have e1 : ∫ z, dotL (H z) (velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) z)
        ∂(volume.restrict (phaseCell (2 * ε * c))) =
        ∫ z, (dotL (H z) (velPhys ε⁻¹ c b z) - dotL (H z) (velPhys ε⁻¹ c b' z))
        ∂(volume.restrict (phaseCell (2 * ε * c))) :=
      integral_congr_ae (hae'.mono fun x hx => by simp only [hx, hpt])
    rw [e1, integral_sub i1 i2]
    simp [smul_sub]
  refine ⟨?_, ?_⟩
  · intro φ hφ
    rw [key _ (Or.inl ⟨φ, hφ, rfl⟩), h1.solenoidal φ hφ, h2.solenoidal φ hφ, sub_zero]
  · intro Φ hΦ
    rw [key _ (Or.inr ⟨Φ, hΦ, rfl⟩), h1.equation Φ hΦ, h2.equation Φ hΦ]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
