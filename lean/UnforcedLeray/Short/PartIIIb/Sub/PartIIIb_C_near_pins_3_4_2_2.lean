import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2

/-!
# `OuterDict` decomposed (task `PartIII-b:C/near/pins/3/4/2/2`)

Source `the November 2 reference manuscript`
lines 2671-2689: the cylinder chart `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`, the space
`H = L²(s^{-3/2} dς)`, the lift `𝒩_v b = √s b` and the change of variables of the normalized
phase/spatial integral (the Lean lift `B0223.liftVec` carries the normalization
`jConst ε = (√(2π) ε)⁻¹`).

Three leaves (the constant `κ = jConst ε · ε³ · K · P` is assembled in `outerDict_of`):
* `OuterScaled`: the scaled test `Ψ(x,τ) = Φ(τ, x/ε)` lies in `X` (bounded, compact support);
* `OuterPairIter`: `⟪Ψ, J u⟫` as an iterated cell integral (`coeFn_liftVec`, `mp_toCell`, Fubini);
* `OuterVelJoint`: `a · frame(periodize u(chart)) = K · velPhys(τ, x/ε)` for a.e. `(x, τ)` of one
  period, jointly in `(x, τ)` (task `PartIII-b:C/near/pins/3/4/2/2/3/org`: a single `τ`-slice is
  charted onto a `measureH`-null surface, so no per-`τ` statement follows from `ChartRep`).
  `outerDict_of` slices it by Fubini (`ae_slice_of_ae_joint`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **Ph1** (source 2671-2689): for a smooth periodic compactly supported phase test `Φ`, the
scaled field `Ψ(x,τ) = Φ(τ, x/ε)` is the (a.e.) representative of an element of `X`
(bounded with compact spatial support, `B0223.mp_toCell` for measurability/period). -/
def OuterScaled : Prop :=
  ∀ (p : Params) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    ∃ Ψ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period, OuterRep p Φ Ψ

/-- **Ph2-Ph4a** (source 2671-2689): for the scaled test `Ψ` of `Φ` and every
`u ∈ H`, `⟪Ψ, J_ε u⟫ = (√(2π)ε)⁻¹ ∫_{(0,P]} ∫_{ℝ³} Φ(τ, x/ε) · a(x) e(x) u(chart(x,τ)) dx dτ`.
(`B0223.coeFn_liftVec`, `OuterRep`, `B0223.mp_toCell`, Fubini; all integrands bounded with
compact support.) -/
def OuterPairIter : Prop :=
  ∀ (p : Params) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    ∀ Ψ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period, OuterRep p Φ Ψ →
    ∀ u : HSpace p.c MeridC,
      outerPair Ψ (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl u) =
        (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          ∫ τ in Ioc (0 : ℝ) p.period, ∫ x : Space,
            dotL (Φ (τ, p.ε⁻¹ • x))
              (UnforcedLeray.B0220.liftA x •
                UnforcedLeray.B0223.frameC x
                  (UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
                    (UnforcedLeray.B0220.chart p.ε (x, τ))))

/-- **Ph2-Ph3, joint form** (source 2671-2689: the chart `(s, q, η)`, `𝒩_v b = √s b`, and the
change of variables, whose Jacobian `πR²s^{-5/2} ds dη · dq/c` makes the chart image of
`dx dτ` absolutely continuous with respect to `s^{-3/2} ds dq dη`; `Axi.Nv`, `Axi.perExt`,
`age R y = (R/ϱ(y))²`): there is a real `K ≠ 0` depending on `p` only (`K = 1`) such that for every
`u ∈ H` of real chart form `f`, at a.e. point `z = (x, τ)` of one period `ℝ³ × (0, P]`
(Lebesgue `dx dτ`): `a(x) e(x) u(chart(x,τ)) = K · velPhys ε⁻¹ c f (τ, x/ε)`.

The statement is joint in `(x, τ)`: `ChartRep` fixes `u` only `measureH`-a.e., and for a fixed `τ`
the map `x ↦ chart ε (x, τ)` has a two-dimensional image, a `measureH`-null set. -/
def OuterVelJoint : Prop :=
  ∀ p : Params, ∃ K : ℝ, K ≠ 0 ∧
    ∀ (u : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c u f →
      ∀ᵐ z ∂((volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc (0 : ℝ) p.period)),
        UnforcedLeray.B0220.liftA z.1 •
            UnforcedLeray.B0223.frameC z.1
              (UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
                (UnforcedLeray.B0220.chart p.ε z)) =
          K • velPhys p.ε⁻¹ p.c f (z.2, p.ε⁻¹ • z.1)

/-- Fubini for almost-everywhere statements on one period: an a.e. property of `(x, τ)` in
`ℝ³ × (0, P]` holds, for a.e. `τ ∈ (0, P]`, at a.e. `x ∈ ℝ³`. -/
theorem ae_slice_of_ae_joint {P : ℝ} {Q : Space × ℝ → Prop}
    (h : ∀ᵐ z ∂((volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc (0 : ℝ) P)), Q z) :
    ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ᵐ x : Space, Q (x, τ) := by
  have e : (volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc (0 : ℝ) P) =
      (volume : Measure Space).prod (volume.restrict (Ioc (0 : ℝ) P)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [e] at h
  have h' := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) P))
    (ν := (volume : Measure Space))).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h'

theorem outerDict_of (h1 : OuterScaled) (h2 : OuterPairIter) (h3 : OuterVelJoint) :
    OuterDict := by
  intro p
  obtain ⟨K, hK, hjoint⟩ := h3 p
  have hP : 0 < p.period := p.period_pos
  have hε := p.ε_pos
  refine ⟨(UnforcedLeray.B0220.jConst p.ε : ℂ) * ((p.ε ^ 3 : ℝ) : ℂ) * (K : ℂ) * (p.period : ℂ),
    ?_, ?_⟩
  · have : UnforcedLeray.B0220.jConst p.ε ≠ 0 := by
      unfold UnforcedLeray.B0220.jConst; positivity
    simp [this, hε.ne', hK, hP.ne']
  · intro Φ hΦ
    obtain ⟨Ψ, hΨ⟩ := h1 p Φ hΦ
    refine ⟨Ψ, hΨ, fun u f hf => ?_⟩
    rw [h2 p Φ hΦ Ψ hΨ u]
    have hslice : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) p.period)), ∀ᵐ x : Space,
        UnforcedLeray.B0220.liftA x •
            UnforcedLeray.B0223.frameC x
              (UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
                (UnforcedLeray.B0220.chart p.ε (x, τ))) =
          K • velPhys p.ε⁻¹ p.c f (τ, p.ε⁻¹ • x) :=
      ae_slice_of_ae_joint (hjoint u f hf)
    have hin : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) p.period)),
        (∫ x : Space, dotL (Φ (τ, p.ε⁻¹ • x))
          (UnforcedLeray.B0220.liftA x •
            UnforcedLeray.B0223.frameC x
              (UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
                (UnforcedLeray.B0220.chart p.ε (x, τ))))) =
        ((K * p.ε ^ 3 : ℝ) : ℂ) *
          ∫ y : Space, dotL (Φ (τ, y)) (velPhys p.ε⁻¹ p.c f (τ, y)) := by
      filter_upwards [hslice] with τ hτ
      have e1 : (∫ x : Space, dotL (Φ (τ, p.ε⁻¹ • x))
          (UnforcedLeray.B0220.liftA x •
            UnforcedLeray.B0223.frameC x
              (UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
                (UnforcedLeray.B0220.chart p.ε (x, τ))))) =
          ∫ x : Space, (K : ℂ) * dotL (Φ (τ, p.ε⁻¹ • x)) (velPhys p.ε⁻¹ p.c f (τ, p.ε⁻¹ • x)) := by
        refine integral_congr_ae ?_
        filter_upwards [hτ] with x hx
        rw [hx, ← Complex.coe_smul, map_smul, smul_eq_mul]
      rw [e1, integral_const_mul]
      have e2 := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure Space))
        (fun y : Space => dotL (Φ (τ, y)) (velPhys p.ε⁻¹ p.c f (τ, y))) p.ε⁻¹
      rw [e2]
      have hr : |((p.ε⁻¹) ^ Module.finrank ℝ Space)⁻¹| = p.ε ^ 3 := by
        rw [abs_of_nonneg (by positivity)]
        simp [Space, finrank_euclideanSpace]
      rw [hr, Complex.real_smul]
      push_cast; ring
    rw [integral_congr_ae hin, integral_const_mul]
    unfold pairF phaseInt
    rw [Complex.real_smul]
    have hPne : (p.period : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    push_cast
    field_simp

end UnforcedLeray.Short.PartIIIb.NearInst
