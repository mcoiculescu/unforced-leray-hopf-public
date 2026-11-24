import UnforcedLeray.Short.PartIIb.Sub.T12_2_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.IntegrableOnCompact
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.IntegrableTestPair
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePlanarSolZero

/-!
# Part II-b, task `PartII-b:T12/2/5` (`SliceWeakSolenoidal`): weak solenoidality from cell identities

Source of record: `the November 2 reference manuscript` (SP 1901-1903, 1923-1926).
Proves the Prop `SliceWeakSolenoidal` of `Sub/T12_2.lean`. A compact planar test `φ` is integrable
against `G` on `tsupport φ` (`integrableOnCompact_proof`, `integrableTestPair_proof`); Fubini in
the age `s` (`integral_prod`, `Integrable.prod_right_ae`) reduces the planar integral to the slice
integrals, each of which vanishes for `s > 0` by `slicePlanarSolZero_proof` and for `s ≤ 0` because
the integrand vanishes there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem sliceWeakSolenoidal_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SliceWeakSolenoidal := by
  intro c r G hc hr hGs hGper hGH hslice
  unfold WeakSolenoidal
  intro φ hφ
  have hG1 : IntegrableOn G (tsupport φ) :=
    UnforcedLeray.Short.IIb.LerayLiftSub.integrableOnCompact_proof c r G hc hr hGs hGper hGH.finite
      (tsupport φ) hφ.compact.isCompact hφ.supp
  have hGφ := UnforcedLeray.Short.IIb.integrableTestPair_proof G φ hφ hG1
  have hf1 : Integrable (fun x : Coord => G x 0 * (cpd 1 φ x : ℂ)) := hGφ.2 0 1
  have hf2 : Integrable (fun x : Coord => G x 1 * (cpd 2 φ x : ℂ)) := hGφ.2 1 2
  have hint : Integrable (fun x : Coord => G x 0 * (cpd 1 φ x : ℂ) + G x 1 * (cpd 2 φ x : ℂ)) :=
    hf1.add hf2
  refine ⟨hint, ?_⟩
  have hvol : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  have hintP : Integrable (fun x : Coord => G x 0 * (cpd 1 φ x : ℂ) + G x 1 * (cpd 2 φ x : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rw [← hvol]; exact hint
  have hf1P : Integrable (fun x : Coord => G x 0 * (cpd 1 φ x : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rw [← hvol]; exact hf1
  have hf2P : Integrable (fun x : Coord => G x 1 * (cpd 2 φ x : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rw [← hvol]; exact hf2
  -- vanishing of the test and its derivatives off `s > 0`
  have hcpd0 : ∀ j : Fin 3, ∀ x : Coord, x ∉ tsupport φ → cpd j φ x = 0 := by
    intro j x hx
    unfold cpd
    have h0 : fderiv ℝ φ x = 0 := by
      by_contra hne
      exact hx (support_fderiv_subset (𝕜 := ℝ) (f := φ) (Function.mem_support.2 hne))
    simp [h0]
  rw [hvol, integral_prod _ hintP]
  apply integral_eq_zero_of_ae
  have hA1 : ∀ᵐ s ∂(volume : Measure ℝ),
      Integrable (fun z : ℝ × ℝ => G (s, z) 0 * (cpd 1 φ (s, z) : ℂ)) := hf1P.prod_right_ae
  have hA2 : ∀ᵐ s ∂(volume : Measure ℝ),
      Integrable (fun z : ℝ × ℝ => G (s, z) 1 * (cpd 2 φ (s, z) : ℂ)) := hf2P.prod_right_ae
  have hsl : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi (0 : ℝ) →
      ∀ Φ : ℝ × ℝ → ℝ, CylTest c Φ →
        Integrable (fun z => G (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) +
            G (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ)) (UnforcedLeray.Cyl.avgμ c) ∧
          ∫ z, (G (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) + G (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ))
            ∂(UnforcedLeray.Cyl.avgμ c) = 0 :=
    (ae_restrict_iff' measurableSet_Ioi).1 hslice
  filter_upwards [hA1, hA2, hsl] with s hs1 hs2 hsl_s
  by_cases hs : 0 < s
  · have hΦ := hsl_s hs
    exact UnforcedLeray.Short.IIb.LerayLiftSub.slicePlanarSolZero_proof c (fun z => G (s, z)) hc
      (hGs.comp_measurable measurable_prodMk_left) (fun z => hGper s z) hΦ φ s hφ hs1 hs2
  · have hz : ∀ z : ℝ × ℝ, G (s, z) 0 * (cpd 1 φ (s, z) : ℂ) +
        G (s, z) 1 * (cpd 2 φ (s, z) : ℂ) = 0 := by
      intro z
      have hnot : (s, z) ∉ tsupport φ := fun h => hs (hφ.supp h).1
      rw [hcpd0 1 _ hnot, hcpd0 2 _ hnot]
      simp
    simp only [hz, integral_zero, Pi.zero_apply]

end UnforcedLeray.Short.IIb
