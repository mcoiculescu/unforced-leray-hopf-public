import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/5/6` (`IntegrableTestPair`)

Source of record: `the November 2 reference manuscript`, lines 1901-1903 (`H_r`) and
1923-1926 (`P_0` at each age). Target: `LerayLiftSub.IntegrableTestPair` (`Sub/T12_2_5.lean`).

Proof: the component `G x i` is integrable on the compact `tsupport φ` (a continuous linear image of
an integrable function). Multiplying by a continuous factor on the compact set gives integrability
there, and the product vanishes off `tsupport φ`, so `integrableOn_iff_integrable_of_support_subset`
upgrades it to integrability on the whole chart.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem integrableTestPair_proof : UnforcedLeray.Short.IIb.LerayLiftSub.IntegrableTestPair := by
  intro G φ hφ hG
  have hK : IsCompact (tsupport φ) := hφ.compact.isCompact
  have hcont : Continuous φ := hφ.smooth.continuous
  have hφ0 : ∀ x : Coord, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hD0 : ∀ j : Fin 3, ∀ x : Coord, x ∉ tsupport φ → cpd j φ x = 0 := by
    intro j x hx
    unfold cpd
    have h0 : fderiv ℝ φ x = 0 := by
      by_contra hne
      exact hx (support_fderiv_subset (𝕜 := ℝ) (f := φ) (Function.mem_support.2 hne))
    simp [h0]
  have hcpd : ∀ j : Fin 3, Continuous (cpd j φ) := by
    intro j
    unfold cpd
    exact (hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGi : ∀ i : Fin 2, IntegrableOn (fun x => G x i) (tsupport φ) := fun i =>
    (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).integrable_comp hG
  have hprod : ∀ (g : Coord → ℂ), IntegrableOn g (tsupport φ) →
      ∀ h : Coord → ℂ, Continuous h → (∀ x : Coord, x ∉ tsupport φ → h x = 0) →
        Integrable (fun x => g x * h x) := by
    intro g hg h hh hz
    have h1 : IntegrableOn (fun x => g x * h x) (tsupport φ) :=
      hg.mul_continuousOn hh.continuousOn hK
    have hs : Function.support (fun x => g x * h x) ⊆ tsupport φ := by
      intro x hx
      by_contra hn
      exact hx (by simp [hz x hn])
    exact (integrableOn_iff_integrable_of_support_subset hs).1 h1
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · exact hprod (fun x => G x i) (hGi i) (fun x => (φ x : ℂ))
      (Complex.continuous_ofReal.comp hcont) (fun x hx => by simp [hφ0 x hx])
  · exact hprod (fun x => G x i) (hGi i) (fun x => (cpd j φ x : ℂ))
      (Complex.continuous_ofReal.comp (hcpd j)) (fun x hx => by simp [hD0 j x hx])

end UnforcedLeray.Short.IIb
