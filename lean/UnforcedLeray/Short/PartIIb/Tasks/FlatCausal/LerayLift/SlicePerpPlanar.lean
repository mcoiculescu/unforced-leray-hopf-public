import UnforcedLeray.Short.PartIIb.Sub.T12_2_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.IntegrableOnCompact
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.IntegrableTestPair
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.HrAeTransfer
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePlanarPerpZero

/-!
# Part II-b, task `PartII-b:T12/2/6` (`SlicePerpPlanar`): orthogonality to planar solenoidal tests

Source of record: `the November 2 reference manuscript` (SP 1901-1903, 1923-1926).
Proves the Prop `SlicePerpPlanar` of `Sub/T12_2.lean`. `F = F'` a.e. on `s > 0` and `hrAeTransfer_proof`
give `H_r`-finiteness of `F'`; `integrableOnCompact_proof` and `integrableTestPair_proof` make
`(F' - G)·Ψ` integrable on `Coord`; Fubini in `s` (`integral_prod`) reduces the claim to the slice
identity `slicePlanarPerpZero_proof` for `s > 0`, while for `s ≤ 0` the integrand vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem slicePerpPlanar_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SlicePerpPlanar := by
  intro c r F F' G hc hr hF hF'p hF'per hFa hGH hGs hGper hslice
  unfold PerpPlanarSol
  intro Ψ hΨ
  have hvol : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  have hN' : hNorm c r F' < ⊤ := by
    rw [UnforcedLeray.Short.IIb.hrAeTransfer_proof c r F F' hc hFa]
    exact hF.finite
  have hNG : hNorm c r G < ⊤ := hGH.finite
  -- integrability of the componentwise pairings with `Ψ`
  have hFint : ∀ k : Fin 2, Integrable (fun x : Coord => F' x k * ((Ψ x k : ℝ) : ℂ)) := by
    intro k
    have hK : IntegrableOn F' (tsupport (fun x => Ψ x k)) :=
      UnforcedLeray.Short.IIb.LerayLiftSub.integrableOnCompact_proof c r F' hc hr hF'p hF'per hN' _
        (hΨ.smooth k).compact.isCompact (hΨ.smooth k).supp
    exact (UnforcedLeray.Short.IIb.integrableTestPair_proof F' (fun x => Ψ x k) (hΨ.smooth k) hK).1 k
  have hGint : ∀ k : Fin 2, Integrable (fun x : Coord => G x k * ((Ψ x k : ℝ) : ℂ)) := by
    intro k
    have hK : IntegrableOn G (tsupport (fun x => Ψ x k)) :=
      UnforcedLeray.Short.IIb.LerayLiftSub.integrableOnCompact_proof c r G hc hr hGs hGper hNG _
        (hΨ.smooth k).compact.isCompact (hΨ.smooth k).supp
    exact (UnforcedLeray.Short.IIb.integrableTestPair_proof G (fun x => Ψ x k) (hΨ.smooth k) hK).1 k
  have hD : ∀ k : Fin 2, Integrable (fun x : Coord => (F' x k - G x k) * ((Ψ x k : ℝ) : ℂ)) := by
    intro k
    refine ((hFint k).sub (hGint k)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hh : Integrable (fun x : Coord => ∑ i : Fin 2, (F' x i - G x i) * ((Ψ x i : ℝ) : ℂ)) :=
    integrable_finsetSum Finset.univ (fun i _ => hD i)
  have hhP : Integrable (fun x : Coord => ∑ i : Fin 2, (F' x i - G x i) * ((Ψ x i : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rw [← hvol]; exact hh
  -- pointwise identification of the integrand with `(F' - G)·Ψ`
  have hae : (fun x : Coord => cdot (F - G) Ψ x) =ᵐ[volume]
      (fun x : Coord => ∑ i : Fin 2, (F' x i - G x i) * ((Ψ x i : ℝ) : ℂ)) := by
    filter_upwards [hFa] with x hx
    by_cases hx0 : 0 < x.1
    · have hFx := hx hx0
      simp only [cdot, Pi.sub_apply, PiLp.sub_apply, hFx]
    · have hz : ∀ i : Fin 2, Ψ x i = 0 := by
        intro i
        have hnot : x ∉ tsupport (fun y => Ψ y i) := fun h => hx0 ((hΨ.smooth i).supp h).1
        have h0 := image_eq_zero_of_notMem_tsupport hnot
        exact h0
      simp [cdot, hz]
  refine ⟨hh.congr hae.symm, ?_⟩
  have hI : ∫ x : Coord, cdot (F - G) Ψ x = ∫ x : Coord, ∑ i : Fin 2, (F' x i - G x i) * ((Ψ x i : ℝ) : ℂ) :=
    integral_congr_ae hae
  rw [hI, hvol, integral_prod _ hhP]
  apply integral_eq_zero_of_ae
  have hDP : ∀ k : Fin 2, Integrable (fun x : Coord => (F' x k - G x k) * ((Ψ x k : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    intro k
    rw [← hvol]; exact hD k
  have hA : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k : Fin 2,
      Integrable (fun z : ℝ × ℝ => (F' (s, z) k - G (s, z) k) * ((Ψ (s, z) k : ℝ) : ℂ)) := by
    rw [ae_all_iff]
    intro k
    exact (hDP k).prod_right_ae
  have hsl := (ae_restrict_iff' measurableSet_Ioi).1 hslice
  filter_upwards [hA, hsl] with s hsA hsl_s
  by_cases hs : 0 < s
  · have hΦ := hsl_s hs
    exact UnforcedLeray.Short.IIb.LerayLiftSub.slicePlanarPerpZero_proof c (fun z => F' (s, z))
      (fun z => G (s, z)) hc (hF'p.comp_measurable measurable_prodMk_left)
      (hGs.comp_measurable measurable_prodMk_left) (fun z => hF'per s z) (fun z => hGper s z)
      hΦ Ψ s hΨ hsA
  · have hz : ∀ z : ℝ × ℝ, ∑ i : Fin 2, (F' (s, z) i - G (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) = 0 := by
      intro z
      apply Finset.sum_eq_zero
      intro i _
      have hnot : (s, z) ∉ tsupport (fun y => Ψ y i) := fun h => hs ((hΨ.smooth i).supp h).1
      have h0 := image_eq_zero_of_notMem_tsupport hnot
      have h1 : Ψ (s, z) i = 0 := h0
      rw [h1]
      simp
    simp only [hz, integral_zero, Pi.zero_apply]

end UnforcedLeray.Short.IIb
