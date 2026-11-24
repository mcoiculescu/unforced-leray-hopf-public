import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY

/-!
# Part II-a, task `PartII-a:F06/1/5`: the field-to-`Y_r` step with representative (`LaplacianFieldToYRep`)

Copy of the proof of `laplacianFieldToY_of` (`Sub/PartIIa_F04_2.lean`), keeping the `IsRep a Λ`
obtained from `PeriodicFieldToYq` in its first step, and supplying the five leaves of
`Tasks/F04bFieldToY/` exactly as `laplacianFieldToY` does.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

theorem laplacianFieldToYRep : LaplacianFieldToYRep := by
  intro r _ hr P hP ν w W hW Λ hm hwin hper hfin
  obtain ⟨a, ha⟩ := periodicFieldToYq_proof r hr P Λ hm hper hfin
  refine ⟨a, ha, ?_⟩
  intro Φ hΦ
  obtain ⟨n, c, η, hpart⟩ := periodPartition_proof P hP.out
  have hΨ : IsPhaseTest P (nuLapT ν Φ) := isPhaseTest_nuLapT hΦ ν
  rw [phasePair_eq_periodIntegral hΨ w, phasePair_eq_periodIntegral hΦ a, zero_add]
  congr 1
  have unfold : ∀ (Ψ' : ℝ × Space → CVec3), IsPhaseTest P Ψ' → ∀ v : Yq P r,
      ∫ t in Ioc (0 : ℝ) P, ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) =
        ∑ j, ∫ t, (η j t : ℂ) *
          ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) := by
    intro Ψ' hΨ' v
    refine periodUnfold_proof P hP.out n c η hpart _ ?_ (phasePairSliceIntegrable_proof r P v Ψ' hΨ')
    intro t
    have e : (((t + P : ℝ)) : AddCircle P) = (t : AddCircle P) := AddCircle.coe_add_period P t
    simp only [e, hΨ'.periodic]
  have conv : ∀ (Ψ' : ℝ × Space → CVec3) (v : Yq P r) (V : ℝ × Space → CVec3), IsRep v V →
      ∀ j, ∫ t, (η j t : ℂ) * ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) =
        ∫ t, (η j t : ℂ) * ∫ y, dotL (Ψ' (t, y)) (V (t, y)) := by
    intro Ψ' v V hV j
    refine integral_congr_ae ?_
    filter_upwards [hV.slice] with t ht
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  rw [unfold _ hΨ w, unfold _ hΦ a]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conv _ w W hW j, conv _ a Λ ha j]
  exact windowTestIdentity_proof P ν (c j) W Λ (hwin (c j)) (η j) (hpart.1 j).1 (hpart.1 j).2.1
    (hpart.1 j).2.2 Φ hΦ

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.laplacianFieldToYRep
