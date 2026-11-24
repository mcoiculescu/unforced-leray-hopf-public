import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3

/-!
# `PairFunctional` decomposed (task `PartIII-b:C/near/pins/3/3/1`)

Source `the November 2 reference manuscript`:
2666-2668, 2683-2689 (the lift `𝒩_v` and the physical pairing), 1640-1641 (change of variables
`(τ, y) ↦ (s, q, η)`), 1675-1677.

Route.  The pairing `f ↦ ⟨Φ, 𝒩_v f⟩` is a bounded **real**-linear functional of the real chart field
`f ∈ L²(ageμ c (-3/2), ℝ²)` (`RealPairFunctional`, from `PairBound`, `PairLinear`).  The `H`-class `g`
has a real part `T g` in that space (`ChartTransport`), and the complexification
`ℓ g = L (T g) + i L (T (-i g))` is the bounded `ℂ`-linear functional (proved below,
`pairFunctional_of`); on a class with real chart form `f` it equals `L f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **Leaf A (real part of an `H`-class)**: there is a bounded real-linear map `T` from the `H`
space to `L²(ageμ c (-3/2), ℝ²)` (`T g = merReL ∘ g ∘ cellPtInv`, with `‖T g‖² ≤ ‖g‖²/c` by
`Body.norm_sq_cellPt`, `merReL` norm-nonincreasing), which on a class `g` with real chart form
`f` returns `f` and kills `-i g`. -/
def ChartTransport : Prop :=
  ∀ c : ℝ, 0 < c → ∃ T : HSpace c MeridC →L[ℝ] Lp Merid 2 (ageμ c (-3 / 2)),
    ∀ (g : HSpace c MeridC) (f : Chart → Merid), ChartRep c g f →
      ((T g : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] f) ∧ T ((-Complex.I) • g) = 0

/-- **Leaf B (bound)** (2683-2689, 1640-1641): for a solenoidal phase test `Φ` the pairing with
the physical velocity of a measurable `L²` chart field is integrable over the phase cell
`(0, 2εc] × ℝ³` and bounded by `C ‖f‖_{L²(ageμ c (-3/2))}` (Cauchy-Schwarz on the phase cell,
`Axi.eLpNorm_liftFun`, `wda_velPhys_eq`, `fwuB_norm_velPhys`). -/
def PairBound : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
    ∃ C : ℝ, ∀ f : Chart → Merid, Measurable f → MemLp f 2 (ageμ c (-3 / 2)) →
      Integrable (fun x : ℝ × Space => dotL (Φ x) (velPhys ε⁻¹ c f x))
        (volume.restrict (Ioc (0 : ℝ) (2 * ε * c) ×ˢ (univ : Set Space))) ∧
      ‖pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)‖ ≤ C * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal

/-- **Leaf C (linearity and well-definedness)**: the pairing is additive and real-homogeneous in
`L²` chart fields (`wda_velPhys_eq`, `liftFun` linearity, with `PairBound` integrability), and
depends only on the `ageμ c (-3/2)`-class of `f`, even for a non-measurable representative `f`
(`wda_velPhys_congr` for measurable ones; a null set of chart points has null preimage in the
phase cell). -/
def PairLinear : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
    (∀ f f' : Chart → Merid, Measurable f → Measurable f' →
      MemLp f 2 (ageμ c (-3 / 2)) → MemLp f' 2 (ageμ c (-3 / 2)) →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (f + f')) =
        pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f) + pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f')) ∧
    (∀ (a : ℝ) (f : Chart → Merid), Measurable f → MemLp f 2 (ageμ c (-3 / 2)) →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (a • f)) =
        a • pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)) ∧
    (∀ f f' : Chart → Merid, Measurable f' → f =ᵐ[ageμ c (-3 / 2)] f' →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f) = pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f'))

/-- **Leaf D (bounded real functional on `L²`)**: `PairBound` and `PairLinear` give a bounded
real-linear functional `L` on `Lp Merid 2 (ageμ c (-3/2))` (take a strongly measurable
representative of each class, `LinearMap.mkContinuous`), computing the pairing of every
representative. -/
def RealPairFunctional : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
    ∃ L : Lp Merid 2 (ageμ c (-3 / 2)) →L[ℝ] ℂ,
      ∀ (b : Lp Merid 2 (ageμ c (-3 / 2))) (f : Chart → Merid),
        f =ᵐ[ageμ c (-3 / 2)] (b : Chart → Merid) →
          L b = pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)

theorem pairFunctional_of (h1 : RealPairFunctional) (h2 : ChartTransport) : PairFunctional := by
  intro c ε hc hε Φ hΦ
  obtain ⟨L, hL⟩ := h1 c ε hc hε Φ hΦ
  obtain ⟨T, hT⟩ := h2 c hc
  let M : HSpace c MeridC →L[ℝ] HSpace c MeridC :=
    ((-Complex.I) • ContinuousLinearMap.id ℂ (HSpace c MeridC)).restrictScalars ℝ
  have hM : ∀ g, M g = (-Complex.I) • g := fun g => rfl
  let ℓ0 : HSpace c MeridC →L[ℝ] ℂ := L.comp T + Complex.I • (L.comp (T.comp M))
  have h0 : ∀ g, ℓ0 g = L (T g) + Complex.I * L (T (M g)) := fun g => rfl
  have hI : ∀ g, ℓ0 (Complex.I • g) = Complex.I * ℓ0 g := by
    intro g
    have e1 : M (Complex.I • g) = g := by
      rw [hM, smul_smul]; simp
    have e2 : Complex.I • g = -(M g) := by
      rw [hM, neg_smul, neg_neg]
    rw [h0, h0, e1, e2, map_neg, map_neg]
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(L (T (M g)))) * this
  let ℓ : HSpace c MeridC →L[ℂ] ℂ :=
    { toFun := ℓ0
      map_add' := ℓ0.map_add
      map_smul' := by
        intro a g
        have ha : a • g = a.re • g + a.im • (Complex.I • g) := by
          conv_lhs => rw [← Complex.re_add_im a]
          rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
          rfl
        have : ℓ0 (a • g) = a.re • ℓ0 g + a.im • ℓ0 (Complex.I • g) := by
          rw [ha, map_add, map_smul, map_smul]
        rw [this, hI]
        simp only [Complex.real_smul, RingHom.id_apply, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im a]
        ring
      cont := ℓ0.continuous }
  refine ⟨ℓ, fun g f hf => ?_⟩
  obtain ⟨h3, h4⟩ := hT g f hf
  show ℓ0 g = _
  rw [h0, hM, h4, map_zero, mul_zero, add_zero]
  exact hL _ f h3.symm

end UnforcedLeray.Short.PartIIIb.NearInst
