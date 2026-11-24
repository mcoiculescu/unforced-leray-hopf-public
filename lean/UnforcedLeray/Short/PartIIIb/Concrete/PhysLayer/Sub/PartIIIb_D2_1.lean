import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- **Sub-lemma A** (source 1580-1583, subtracting two solutions): the weak formulation is
subtractive along the lift of `VelG`: `velPhys (b - b') = velPhys b - velPhys b'` a.e. on
`ℝ × ℝ³` (the lift is pointwise linear; the `VelG`-difference is the a.e. difference on the
body measure, whose null sets pull back to null sets, as for `WeakDmuAdd`), and `pairF` is
additive in the field slot because lifts of `VelG` are in `Y_2` (sub-lemma B), so
`pairF P Φ (w - w') = pairF P Φ w - pairF P Φ w'` for the compactly supported tests. -/
def FWUSub (c γ ν ε μ : ℝ) : Prop :=
  ∀ (b b' : VelG c γ ν) (rhs rhs' : (ℝ × Space → CVec3) → ℂ),
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c b) rhs →
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c b') rhs' →
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid))
      (rhs - rhs')

/-- **Sub-lemma B** (source 2666-2700, 1341-1344): lifts of `VelG` lie in `Y_2` of period
`P = 2εc`: periodic by `perExt`, measurable, and `‖lift b‖_{Y_2} ≲ √π R ‖b‖_{L²(g⁻²π s^{-3/2})}`
finite, since `g, g⁻¹ ≤ e^{|γ|/ν}` (`NearInst.gainInvFun_le`, `one_le_gainFun`) and
`eLpNorm_liftFun` of `Lib/AxisymmetricB/Jv.lean`. -/
def FWULiftYr (c γ ν ε : ℝ) : Prop :=
  ∀ b : VelG c γ ν, UnforcedLeray.Short.IIb.IsInYr (2 * ε * c) 2 (velPhys ε⁻¹ c b)

/-- **Sub-lemma C** (homogeneous uniqueness, source 1580-1583 via `bg:common-body-graph` 1351-1362,
`r = 2`, `γ_2 = 1/4`, `P ≤ 1`): a field `w ∈ Y_2` that is weakly solenoidal and satisfies
`⟨L₀ᵗΦ + μΦ, w⟩ = 0` for all solenoidal phase tests vanishes a.e.  Proof: transport `w` into
`Yq P 2`; for arbitrary phase tests `Φ` apply the equation to the Leray projection of `Φ`
(`lerayY`, `Lib/LerayC/Phase.lean`) to get `(μ + L) w = 𝐏·0 + ∇q`-free, hence
`HasPhaseOp (μ + L0T) w 0` up to the gradient part killed by weak solenoidality; then
`CommonBodyMaximalDomain` puts `w ∈ D_2` and `CommonBodyBijective` gives `w = 0`. -/
def FWUHomog : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ w : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 w →
      IsWeakDmu ν μ P w (fun _ => 0) → w =ᵐ[volume] 0

/-- **Sub-lemma D** (source 2666-2700): the lift is injective: `velPhys ε⁻¹ c d = 0` a.e. on
`ℝ × ℝ³` forces `d = 0` in `VelG` (`eLpNorm_liftFun`: `‖lift d‖_{L²(phase cell)} = √π R ‖d‖`
against the density `π g⁻² s^{-3/2}`, which is positive, so `‖d‖ = 0`). -/
def FWULiftInj (c γ ν ε : ℝ) : Prop :=
  ∀ d : VelG c γ ν, velPhys ε⁻¹ c d =ᵐ[volume] 0 → d = 0

theorem freeWeakUniqueness_of {c γ ν ε μ : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hP : 2 * ε * c ≤ 1) (hμ : 0 < μ + 1 / 4)
    (hA : FWUSub c γ ν ε μ) (hB : FWULiftYr c γ ν ε) (hC : FWUHomog)
    (hD : FWULiftInj c γ ν ε) : FreeWeakUniqueness c γ ν ε μ := by
  intro b b' rhs h1 h2
  have h3 := hA b b' rhs rhs h1 h2
  rw [sub_self] at h3
  have hP0 : 0 < 2 * ε * c := by positivity
  have h4 : velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) =ᵐ[volume] 0 :=
    hC _ ν μ hP0 hP hν hμ _ (hB (b - b')) h3
  have h5 := hD (b - b') h4
  exact sub_eq_zero.1 h5

end UnforcedLeray.Short.PartIIIb.Concrete
