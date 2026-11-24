import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.PairLinear

/-!
# `RealPairFunctional` (task `PartIII-b:C/near/pins/3/3/1/4`)

Source `the November 2 reference manuscript` 2666-2668, 2683-2689, 1640-1641.
Assembles the bounded real-linear functional `L` on `Lp Merid 2 (ageμ c (-3/2))` from `PairBound`
(bound) and `PairLinear` (additivity, homogeneity, a.e.-invariance).  A strongly measurable
representative `rep b` of each class is chosen; `L b` is the pairing of `rep b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem realPairFunctional : UnforcedLeray.Short.PartIIIb.NearInst.RealPairFunctional := by
  intro c ε hc hε Φ hΦ
  obtain ⟨C, hC⟩ := pairBound c ε hc hε Φ hΦ
  obtain ⟨hadd, hsmul, hcong⟩ := pairLinear c ε hc hε Φ hΦ
  have key : ∀ b : Lp Merid 2 (ageμ c (-3 / 2)),
      ∃ f : Chart → Merid, Measurable f ∧ MemLp f 2 (ageμ c (-3 / 2)) ∧
        f =ᵐ[ageμ c (-3 / 2)] (b : Chart → Merid) := by
    intro b
    exact ⟨(Lp.aestronglyMeasurable b).mk (b : Chart → Merid),
      (Lp.aestronglyMeasurable b).stronglyMeasurable_mk.measurable,
      MemLp.ae_eq (Lp.aestronglyMeasurable b).ae_eq_mk (Lp.memLp b),
      (Lp.aestronglyMeasurable b).ae_eq_mk.symm⟩
  choose rep hrepm hrepL hrepe using key
  let L0 : Lp Merid 2 (ageμ c (-3 / 2)) →ₗ[ℝ] ℂ :=
    { toFun := fun b => pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (rep b))
      map_add' := by
        intro b b'
        have hae : rep (b + b') =ᵐ[ageμ c (-3 / 2)] rep b + rep b' := by
          filter_upwards [hrepe (b + b'), Lp.coeFn_add b b', hrepe b, hrepe b'] with x h1 h2 h3 h4
          rw [h1, h2, Pi.add_apply, Pi.add_apply, h3, h4]
        have e1 := hcong (rep (b + b')) (rep b + rep b') ((hrepm b).add (hrepm b')) hae
        exact e1.trans (hadd (rep b) (rep b') (hrepm b) (hrepm b') (hrepL b) (hrepL b'))
      map_smul' := by
        intro a b
        have hae : rep (a • b) =ᵐ[ageμ c (-3 / 2)] a • rep b := by
          filter_upwards [hrepe (a • b), Lp.coeFn_smul a b, hrepe b] with x h1 h2 h3
          simp [h1, h2, h3]
        have e1 := hcong (rep (a • b)) (a • rep b) ((hrepm b).const_smul a) hae
        have e2 := hsmul a (rep b) (hrepm b) (hrepL b)
        exact e1.trans e2 }
  have hbound : ∀ b : Lp Merid 2 (ageμ c (-3 / 2)), ‖L0 b‖ ≤ C * ‖b‖ := by
    intro b
    have hn : (eLpNorm (rep b) 2 (ageμ c (-3 / 2))).toReal = ‖b‖ := by
      rw [Lp.norm_def, eLpNorm_congr_ae (hrepe b)]
    have h := (hC (rep b) (hrepm b) (hrepL b)).2
    rw [hn] at h
    exact h
  refine ⟨L0.mkContinuous C hbound, fun b f hf => ?_⟩
  change L0 b = _
  exact (hcong f (rep b) (hrepm b) (hf.trans (hrepe b).symm)).symm

end UnforcedLeray.Short.PartIIIb.NearInst
