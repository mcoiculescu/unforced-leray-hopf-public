import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_2

/-!
# `OuterPairIter` (task `PartIII-b:C/near/pins/3/4/2/2/2`)

Source `shorter-proof-2026-11-02.tex` lines 3289-3311. The pairing `⟪Ψ, J_ε u⟫` with the scaled
test `Ψ(x,τ) = Φ(τ, x/ε)` is the iterated cell integral
`(√(2π) ε)⁻¹ ∫_{(0,P]} ∫_{ℝ³} Φ(τ,x/ε) · a(x) e(x) u(chart(x,τ)) dx dτ`.

Route: `OuterRep` and `coeFn_liftVec` rewrite the integrand a.e. as `jConst ε * H(toCell z)`;
the measurable embedding `toCell` (`toCell_measurableEmbedding`) and `mp_toCell` move the integral
to the cell `Space × Ioc 0 P`; Fubini (`integral_prod_symm`) gives the iterated integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The cell map `PSpace P → Space × ℝ` is a measurable embedding (it is the product of the identity
with the measurable equivalence `AddCircle P ≃ᵐ Ioc 0 P` followed by the subtype inclusion). -/
theorem toCell_measurableEmbedding (P : ℝ) [Fact (0 < P)] :
    MeasurableEmbedding (UnforcedLeray.B0223.toCell P) := by
  have he : MeasurableEmbedding
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Space)
        (AddCircle.measurableEquivIoc P 0)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Space)
        (AddCircle.measurableEquivIoc P 0)).measurableEmbedding
  have h1 : MeasurableEmbedding
      (Prod.map (id : Space → Space)
        (Subtype.val : Ioc (0 : ℝ) (0 + P) → ℝ)) :=
    MeasurableEmbedding.prodMap MeasurableEmbedding.id
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc)
  have h2 := h1.comp he
  have hfun : UnforcedLeray.B0223.toCell P =
      Prod.map (id : Space → Space)
        (Subtype.val : Ioc (0 : ℝ) (0 + P) → ℝ) ∘
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Space)
        (AddCircle.measurableEquivIoc P 0)) := rfl
  rw [hfun]
  exact h2

/-- The real scalar pulls out of the bilinear pairing. -/
theorem outerDotRealSmul (a v : CVec3) (r : ℝ) : dotL a (r • v) = (r : ℂ) * dotL a v := by
  rw [← Complex.coe_smul, map_smul, smul_eq_mul]

/-- The integrand of `OuterPairIter` as a function of the cell point `w = (x, τ)`. -/
def outerPairIntegrand (p : Params) (Φ : ℝ × Space → CVec3) (u : HSpace p.c MeridC)
    (w : Space × ℝ) : ℂ :=
  dotL (Φ (w.2, p.ε⁻¹ • w.1))
    (UnforcedLeray.B0220.liftA w.1 • UnforcedLeray.B0223.frameC w.1
      (UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
        (UnforcedLeray.B0220.chart p.ε w)))

theorem outerPairIter : OuterPairIter := by
  intro p Φ hΦ Ψ hΨ u
  have hΨ' := hΨ
  unfold OuterRep at hΨ'
  -- the a.e. identity of the integrand on the periodic space
  have hkey : ∀ᵐ z ∂(volume : Measure (UnforcedLeray.B0223.PSpace p.period)),
      dotL (Ψ z) (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl u z) =
        (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          outerPairIntegrand p Φ u (UnforcedLeray.B0223.toCell p.period z) := by
    filter_upwards [hΨ', UnforcedLeray.B0223.coeFn_liftVec (P := p.period) p.ε_pos p.c_pos rfl u]
      with z h1 h2
    rw [h1, h2]
    unfold outerPairIntegrand
    dsimp only [UnforcedLeray.B0223.toCell]
    rw [outerDotRealSmul]
    congr 1
  have hj : (UnforcedLeray.B0220.jConst p.ε : ℂ) ≠ 0 := by
    have : UnforcedLeray.B0220.jConst p.ε ≠ 0 := by
      unfold UnforcedLeray.B0220.jConst; have := p.ε_pos; positivity
    exact_mod_cast this
  -- integrability of the cell integrand on the periodic space
  have hint : Integrable (fun z => dotL (Ψ z)
      (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl u z)) :=
    outerPair_integrable Ψ _
  have hHint : Integrable (fun z => outerPairIntegrand p Φ u
      (UnforcedLeray.B0223.toCell p.period z)) (volume : Measure (UnforcedLeray.B0223.PSpace p.period)) := by
    have h3 := (hint.congr hkey).const_mul ((UnforcedLeray.B0220.jConst p.ε : ℂ))⁻¹
    refine h3.congr ?_
    filter_upwards with z
    rw [← mul_assoc, inv_mul_cancel₀ hj, one_mul]
  -- transfer to the cell `Space × Ioc 0 P`
  have hI : Integrable (outerPairIntegrand p Φ u)
      ((volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 p.period)) := by
    rw [← (UnforcedLeray.B0223.mp_toCell (P := p.period)).map_eq]
    exact (toCell_measurableEmbedding p.period).integrable_map_iff.mpr hHint
  have hm : (volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 p.period) =
      (volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioc 0 p.period)) := by
    rw [show (volume : Measure (Space × ℝ)) = (volume : Measure Space).prod volume from rfl,
      ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm] at hI
  unfold outerPair
  calc ∫ z, dotL (Ψ z) (UnforcedLeray.B0223.liftVec (P := p.period) p.ε_pos p.c_pos rfl u z)
      = ∫ z, (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          outerPairIntegrand p Φ u (UnforcedLeray.B0223.toCell p.period z) :=
        integral_congr_ae hkey
    _ = (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          ∫ z, outerPairIntegrand p Φ u (UnforcedLeray.B0223.toCell p.period z) :=
        integral_const_mul _ _
    _ = (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          ∫ w, outerPairIntegrand p Φ u w
            ∂((volume : Measure (UnforcedLeray.B0223.PSpace p.period)).map
              (UnforcedLeray.B0223.toCell p.period)) := by
        rw [(toCell_measurableEmbedding p.period).integral_map]
    _ = (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          ∫ w, outerPairIntegrand p Φ u w
            ∂((volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 p.period)) := by
        rw [(UnforcedLeray.B0223.mp_toCell (P := p.period)).map_eq]
    _ = (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          ∫ w, outerPairIntegrand p Φ u w
            ∂((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioc 0 p.period))) := by
        rw [hm]
    _ = (UnforcedLeray.B0220.jConst p.ε : ℂ) *
          ∫ τ in Ioc (0 : ℝ) p.period, ∫ x : Space, outerPairIntegrand p Φ u (x, τ) := by
        rw [integral_prod_symm _ hI]
    _ = _ := rfl

end UnforcedLeray.Short.PartIIIb.NearInst
