import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeFieldAE
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellFullConvection
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0412

/-- The compact-test convection pairing of the actual scheme field equals that of its selected
raw-plus-state representative. The only field identification is the established product-a.e.
identity; all nine affine terms supply the guarded integrability needed for the pairing. -/
theorem Params.schemeField_convectionPair_eq_rawAddState (p : Params) (B : Budget)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) (z : p.Z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period
      (advT (fun x => realC (((p.scheme B).field z x.1) x.2)) Φ)
      (fun x => realC (((p.scheme B).field z x.1) x.2)) =
    pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
      (fun x => p.Ufun x + p.uOf z x) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let U : SpaceTime → CVec3 := fun x => realC (((p.scheme B).field z x.1) x.2)
  let V : SpaceTime → CVec3 := fun x => p.Ufun x + p.uOf z x
  have hfield : U =ᵐ[volume.prod volume] V := by
    simpa only [U, V] using Params.schemeField_eq_rawAddState_ae p B z
  have hfieldCell : U =ᵐ[μ] V := by
    have hfieldEv : ∀ᵐ x ∂(volume.prod volume), U x = V x := hfield
    have hfieldVol : ∀ᵐ x ∂(volume : Measure SpaceTime), U x = V x := by
      rw [Measure.volume_eq_prod ℝ Space]
      exact hfieldEv
    exact MeasureTheory.ae_restrict_of_ae hfieldVol
  let T : Fin 3 → SpaceTime → CVec3 := selectedFullConvectionTerm p z
  let D : Fin 3 → Fin 3 → SpaceTime → ℂ := fun i j x =>
    dotL (advT (T i) Φ x) (T j x)
  have hD (i j : Fin 3) : Integrable (D i j) μ := by
    simpa [D, μ, T] using
      selectedFullBackground_quadraticTerms_integrable (B := B) hRaw hInlet hΦ i j
  have hInner (i : Fin 3) : Integrable (fun x : SpaceTime => ∑ j : Fin 3, D i j x) μ := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hD i j
  have hSum : Integrable
      (fun x : SpaceTime => ∑ i : Fin 3, ∑ j : Fin 3, D i j x) μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hInner i
  have hPoint (x : SpaceTime) :
      dotL (advT V Φ x) (V x) = ∑ i : Fin 3, ∑ j : Fin 3, D i j x := by
    have hV : V = fun y => ∑ i : Fin 3, T i y := by
      funext y
      dsimp [V, T, selectedFullConvectionTerm, Params.uOf]
      simp [Fin.sum_univ_succ]
    rw [hV]
    change dotL (advT (fun y => ∑ i : Fin 3, T i y) Φ x) (∑ j : Fin 3, T j x) = _
    let A : Fin 3 → CVec3 := fun i => advT (T i) Φ x
    let C : Fin 3 → CVec3 := fun j => T j x
    have hAdv : advT (fun y => ∑ i : Fin 3, T i y) Φ x = ∑ i : Fin 3, A i := by
      change (∑ k : Fin 3, (∑ i : Fin 3, T i x k) • dy k Φ x) =
        ∑ i : Fin 3, ∑ k : Fin 3, T i x k • dy k Φ x
      calc
        (∑ k : Fin 3, (∑ i : Fin 3, T i x k) • dy k Φ x) =
            ∑ k : Fin 3, ∑ i : Fin 3, T i x k • dy k Φ x := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_smul]
        _ = ∑ i : Fin 3, ∑ k : Fin 3, T i x k • dy k Φ x := by rw [Finset.sum_comm]
        _ = ∑ i : Fin 3, A i := rfl
    rw [hAdv]
    change dotL (∑ i : Fin 3, A i) (∑ j : Fin 3, C j) = _
    have hfirst : dotL (∑ i : Fin 3, A i) = ∑ i : Fin 3, dotL (A i) := by rw [map_sum]
    rw [hfirst, sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change dotL (A i) (∑ j : Fin 3, C j) = ∑ j : Fin 3, dotL (A i) (C j)
    exact map_sum (dotL (A i)) C Finset.univ
  have hVInt : Integrable (fun x : SpaceTime => dotL (advT V Φ x) (V x)) μ :=
    Integrable.congr hSum (ae_of_all _ fun x => (hPoint x).symm)
  have hUAE : (fun x : SpaceTime => dotL (advT U Φ x) (U x)) =ᵐ[μ]
      fun x => dotL (advT V Φ x) (V x) := by
    filter_upwards [hfieldCell] with x hx
    have hAdv : advT U Φ x = advT V Φ x := by
      simp [advT, hx]
    rw [hAdv, hx]
  have hUInt : Integrable (fun x : SpaceTime => dotL (advT U Φ x) (U x)) μ :=
    Integrable.congr hVInt hUAE.symm
  rw [pairF_eq_restrictedProductIntegral hUInt, pairF_eq_restrictedProductIntegral hVInt]
  rw [integral_congr_ae hUAE]

#print axioms Params.schemeField_convectionPair_eq_rawAddState

end UnforcedLeray.Cons.C03.Concrete
