import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldPer
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq

/-!
# `GELinFieldYq`: the linear-term field is a phase element (source 2525-2533, 1478-1480)

Task `PartIII-b:C/ward/12/3/1/2/6/11`.  Source of record
`the November 2 reference manuscript`.

Proof.  The field `GELinField p z g h j` is strongly measurable (`gELinFieldMeas`), a.e.
slice-periodic (pointwise periodicity, `gELinFieldPer`) and has finite `L^{q₀}` period integral
(`gELinFieldLp`).  `PeriodicFieldToYq` (`periodicFieldToYq_proof`) gives `F : Yq` with
`IsRep F Λ`.  For a phase test `Φ`, `phasePair_eq_pairF_rep` turns the pairing into `pairF` on the
representative, and the slice identities `rep_slice` and `IsRep.slice` identify the representative
with `Λ` for a.e. phase, so the period integrals agree.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (rep rep_slice phasePair_eq_pairF_rep)

theorem gELinFieldYq : GELinFieldYq := by
  intro p z g h j hraw
  have hΛm : StronglyMeasurable (GELinField p z g h j) := gELinFieldMeas p z g h j hraw.1
  have hper : ∀ᵐ τ : ℝ, (fun y => GELinField p z g h j (τ + p.period, y)) =ᵐ[volume]
      (fun y => GELinField p z g h j (τ, y)) :=
    ae_of_all _ (fun τ => ae_of_all _ (fun y => gELinFieldPer p z g h j hraw.1 τ y))
  have hfin := gELinFieldLp p z g h j hraw
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    UnforcedLeray.B0412.q0E UnforcedLeray.B0412.q0E_ne_top p.period
    (GELinField p z g h j) hΛm hper hfin
  refine ⟨F, fun Φ hΦ => ?_⟩
  have hae : ∀ᵐ τ : ℝ, (fun y => GELinField p z g h j (τ, y)) =ᵐ[volume]
      (fun y => rep F τ y) := by
    filter_upwards [hF.slice] with τ hτ
    exact hτ.trans (rep_slice F τ).symm
  have hint : ∀ᵐ τ : ℝ, ∫ y, dotL (Φ (τ, y)) (rep F τ y) =
      ∫ y, dotL (Φ (τ, y)) (GELinField p z g h j (τ, y)) := by
    filter_upwards [hae] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ] with y hy
    exact congrArg (dotL (Φ (τ, y))) hy.symm
  rw [phasePair_eq_pairF_rep hΦ F]
  unfold UnforcedLeray.Cons.C03.Concrete.pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [hint] with τ hτ _
  exact hτ

end UnforcedLeray.Short.PartIIIb.Concrete
