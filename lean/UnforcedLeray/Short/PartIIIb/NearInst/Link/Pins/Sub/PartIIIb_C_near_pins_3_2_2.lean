import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2
import UnforcedLeray.Units.B0226

/-!
# `PairWithLift` decomposed (task `PartIII-b:C/near/pins/3/2/2`)

Source `the November 2 reference manuscript` 1339-1362, 4139-4146, 2666-2668, 2683
(`𝒩_v b = √s b`).

The physical point `(τ, y)` of `velPhys` (chart `s = R²/ρ²`, `R = ε⁻¹`) corresponds to the point
`(x, τ)`, `x = ε y`, of `B0220` (chart `s = 1/|x_h|²`): the two charts agree on `(s, q, η)` after
the dilation `x = ε y`, which is absorbed into the real phase tests `φ₁, φ₂` (so there is no
chart mismatch to correct: `PairWithLift` is true as stated).
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

/-- **Pointwise dictionary** (source 2666-2668, 2683, 3309-3311): with `b = wk ∘ cellPt` a.e., the
physical lift `𝒩_v` of the periodic extension of `wk` at the dilated point `(ε⁻¹x, τ)` equals
`√(2π) ε · J_ε b (x, τ)` for a.e. `(x, τ)` of one period.  (Chart comparison: `Axi.chart ε⁻¹ τ
(ε⁻¹x) = (s, ξ, η)` with `s = B0220.ageS x`, `ξ = B0220.cellQ ε x τ` up to the period
reduction, `η = B0220.etaCoord ε x`; `Axi.age ε⁻¹ (ε⁻¹x) = s`; the frames `Axi.frameL` and
`B0220.frame` agree at `ε⁻¹ x` and `x`; `B0220.coeFn_J`, `B0223.coeFn_liftVec`,
`Axi.liftFun_congr_ae`.) -/
def VelPhysDict : Prop :=
  ∀ (p : Params) (wk : Chart → Merid) (b : HSpace p.c Merid),
    (b : Profile → Merid) =ᵐ[measureH p.c] (fun q => wk (cellPt p.c q)) →
      ∀ᵐ y ∂(UnforcedLeray.B0220.physMeasure p.ε p.c),
        Nv p.ε⁻¹ (perExt p.c wk) y.2 (p.ε⁻¹ • y.1) =
          (√(2 * Real.pi) * p.ε) • (UnforcedLeray.B0220.J p.ε_pos p.c_pos b) y

/-- **Test transport** (dilation `x = ε y`; source 4139-4146): for a complex phase test `φ`
there are real physical tests `φ₁(x, τ) = Re φ(τ, ε⁻¹x)`, `φ₂ = Im φ(τ, ε⁻¹x)` (smooth,
`2εc`-periodic, bounded support) with `(∇φ)(τ, ε⁻¹x) = ε (∇ₓφ₁ + i ∇ₓφ₂)(x, τ)`. -/
def PhaseTestSplit : Prop :=
  ∀ (p : Params) (φ : ℝ × Space → ℂ), IsPhaseTest (2 * p.ε * p.c) φ →
    ∃ φ₁ φ₂ : UnforcedLeray.B0226.PhysTest p.ε p.c, ∀ (y : Space × ℝ) (i : Fin 3),
      gradT φ (y.2, p.ε⁻¹ • y.1) i =
        (p.ε : ℂ) * ((((UnforcedLeray.B0226.gradX φ₁.1 y) i : ℝ) : ℂ) +
          Complex.I * (((UnforcedLeray.B0226.gradX φ₂.1 y) i : ℝ) : ℂ))

/-- **Change of variables in the phase integral** (`∫ F(t,y) dy = ε⁻³ ∫ F(t, ε⁻¹x) dx`, and
Fubini over `ℝ³ × Ioc 0 P`): if `(x, τ) ↦ F(τ, ε⁻¹x)` is integrable over one period then
`phaseInt (2εc) F = (2εc)⁻¹ ε⁻³ ∫ F(τ, ε⁻¹x) d(physMeasure)`. -/
def PhaseIntScale : Prop :=
  ∀ (p : Params) (F : ℝ × Space → ℂ),
    Integrable (fun y : Space × ℝ => F (y.2, p.ε⁻¹ • y.1)) (UnforcedLeray.B0220.physMeasure p.ε p.c) →
      phaseInt (2 * p.ε * p.c) F =
        (((2 * p.ε * p.c)⁻¹ * (p.ε ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ y, F (y.2, p.ε⁻¹ • y.1) ∂(UnforcedLeray.B0220.physMeasure p.ε p.c)

theorem pairWithLift_of (h1 : VelPhysDict) (h2 : PhaseTestSplit) (h3 : PhaseIntScale) :
    PairWithLift := by
  intro p wk b hb
  have hd := h1 p wk b hb
  refine ⟨(((2 * p.ε * p.c)⁻¹ * (p.ε ^ 3)⁻¹ : ℝ) : ℂ) *
    (((p.ε ^ 2 * √(2 * Real.pi) : ℝ)) : ℂ), fun φ hφ => ?_⟩
  obtain ⟨φ₁, φ₂, hs⟩ := h2 p φ hφ
  set J := UnforcedLeray.B0220.J p.ε_pos p.c_pos b with hJ
  set G1 : Space × ℝ → ℝ := fun y => inner ℝ (J y) (UnforcedLeray.B0226.gradX φ₁.1 y) with hG1
  set G2 : Space × ℝ → ℝ := fun y => inner ℝ (J y) (UnforcedLeray.B0226.gradX φ₂.1 y) with hG2
  have hI1 : Integrable G1 (UnforcedLeray.B0220.physMeasure p.ε p.c) := by
    have := (L2.integrable_inner (𝕜 := ℝ) J (UnforcedLeray.B0226.physGrad p.ε p.c φ₁))
    refine this.congr ?_
    filter_upwards [UnforcedLeray.B0226.coeFn_physGrad p.ε p.c φ₁] with y hy
    rw [hy]
  have hI2 : Integrable G2 (UnforcedLeray.B0220.physMeasure p.ε p.c) := by
    have := (L2.integrable_inner (𝕜 := ℝ) J (UnforcedLeray.B0226.physGrad p.ε p.c φ₂))
    refine this.congr ?_
    filter_upwards [UnforcedLeray.B0226.coeFn_physGrad p.ε p.c φ₂] with y hy
    rw [hy]
  set F : ℝ × Space → ℂ := fun x => dotL (gradT φ x) (velPhys p.ε⁻¹ p.c wk x) with hF
  have hae : (fun y : Space × ℝ => F (y.2, p.ε⁻¹ • y.1)) =ᵐ[UnforcedLeray.B0220.physMeasure p.ε p.c]
      fun y => (((p.ε ^ 2 * √(2 * Real.pi) : ℝ)) : ℂ) * ((G1 y : ℂ) + Complex.I * (G2 y : ℂ)) := by
    filter_upwards [hd] with y hy
    simp only [hF, dotL_apply, velPhys, hs y, UnforcedLeray.B0412.realC_apply, hy]
    simp only [hG1, hG2, PiLp.inner_apply, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      PiLp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  have hint : Integrable (fun y : Space × ℝ => F (y.2, p.ε⁻¹ • y.1))
      (UnforcedLeray.B0220.physMeasure p.ε p.c) := by
    refine Integrable.congr ?_ hae.symm
    exact (((hI1.ofReal (𝕜 := ℂ)).add ((hI2.ofReal (𝕜 := ℂ)).const_mul Complex.I))).const_mul _
  refine ⟨φ₁, φ₂, ?_⟩
  show phaseInt (2 * p.ε * p.c) F = _
  have h12 : ∫ y, ((G1 y : ℂ) + Complex.I * (G2 y : ℂ)) ∂(UnforcedLeray.B0220.physMeasure p.ε p.c) =
      ((∫ y, G1 y ∂(UnforcedLeray.B0220.physMeasure p.ε p.c) : ℝ) : ℂ) +
        Complex.I * ((∫ y, G2 y ∂(UnforcedLeray.B0220.physMeasure p.ε p.c) : ℝ) : ℂ) := by
    rw [integral_add (f := fun y => (G1 y : ℂ)) (g := fun y => Complex.I * (G2 y : ℂ))
      (hI1.ofReal (𝕜 := ℂ)) ((hI2.ofReal (𝕜 := ℂ)).const_mul Complex.I),
      integral_const_mul]
    exact congrArg₂ (· + ·) (integral_ofReal (𝕜 := ℂ) (f := G1))
      (congrArg (Complex.I * ·) (integral_ofReal (𝕜 := ℂ) (f := G2)))
  rw [h3 p F hint, integral_congr_ae hae, integral_const_mul, h12]
  have e1 := UnforcedLeray.B0226.inner_physGrad J φ₁
  have e2 := UnforcedLeray.B0226.inner_physGrad J φ₂
  rw [show (inner ℝ J (UnforcedLeray.B0226.physGrad p.ε p.c φ₁) : ℝ) = ∫ y, G1 y ∂_ from e1,
    show (inner ℝ J (UnforcedLeray.B0226.physGrad p.ε p.c φ₂) : ℝ) = ∫ y, G2 y ∂_ from e2]
  ring

end UnforcedLeray.Short.PartIIIb.NearInst
