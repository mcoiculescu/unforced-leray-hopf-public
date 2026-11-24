import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb
namespace TriFubiniAux
open PartIIbF4Aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem aesm_simple (U : ℝ → ℝ → (X →L[ℝ] X)) (L : ℝ → (X →L[ℝ] ℝ)) (s a : ℝ)
    (hmeas : ∀ x : X, AEStronglyMeasurable (fun r => L r (U r a x)) (volume.restrict (Ioc a s)))
    (σ : SimpleFunc ℝ X) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ => (Ioi a).indicator (fun r => L r (U r a (σ q.2))) q.1)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))) := by
  have hterm : ∀ x : X, AEStronglyMeasurable
      (fun r => (Ioi a).indicator (fun r => L r (U r a x)) r) (volume.restrict (Ioc 0 s)) := by
    intro x
    refine (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2 ?_
    rw [Measure.restrict_restrict measurableSet_Ioi]
    refine (hmeas x).mono_measure (Measure.restrict_mono ?_ le_rfl)
    intro r hr
    exact ⟨hr.1, hr.2.2⟩
  have hdec : ∀ q : ℝ × ℝ,
      (Ioi a).indicator (fun r => L r (U r a (σ q.2))) q.1 =
        ∑ x ∈ σ.range, (σ ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) q.2 *
          (Ioi a).indicator (fun r => L r (U r a x)) q.1 := by
    intro q
    rw [Finset.sum_eq_single (σ q.2)]
    · simp
    · intro x _ hx
      have : q.2 ∉ σ ⁻¹' {x} := fun h => hx (by simpa using h.symm)
      simp [Set.indicator_of_notMem this]
    · intro h; exact absurd (SimpleFunc.mem_range_self σ q.2) h
  simp_rw [hdec]
  refine Finset.aestronglyMeasurable_fun_sum _ fun x _ => ?_
  refine AEStronglyMeasurable.mul ?_ ((hterm x).comp_fst)
  refine Measurable.aestronglyMeasurable ?_
  exact (measurable_const.indicator (σ.measurableSet_preimage {x})).comp measurable_snd

theorem aesm_ae (U : ℝ → ℝ → (X →L[ℝ] X)) (L : ℝ → (X →L[ℝ] ℝ)) (s a : ℝ)
    (hmeas : ∀ x : X, AEStronglyMeasurable (fun r => L r (U r a x)) (volume.restrict (Ioc a s)))
    (G : ℝ → X) (hG : AEStronglyMeasurable G (volume.restrict (Ioc 0 s))) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ => (Ioi a).indicator (fun r => L r (U r a (G q.2))) q.1)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))) := by
  have hmk := hG.stronglyMeasurable_mk
  have hae : (fun q : ℝ × ℝ => G q.2) =ᵐ[(volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))]
      (fun q : ℝ × ℝ => hG.mk G q.2) :=
    (Measure.quasiMeasurePreserving_snd).ae_eq_comp hG.ae_eq_mk
  have h1 : AEStronglyMeasurable
      (fun q : ℝ × ℝ => (Ioi a).indicator (fun r => L r (U r a (hG.mk G q.2))) q.1)
      ((volume.restrict (Ioc 0 s)).prod (volume.restrict (Ioc 0 s))) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (j : ℕ) (q : ℝ × ℝ) =>
        (Ioi a).indicator (fun r => L r (U r a ((hmk.approx j) q.2))) q.1)
      (fun j => aesm_simple U L s a hmeas (hmk.approx j)) ?_
    refine Eventually.of_forall fun q => ?_
    by_cases hq : q.1 ∈ Ioi a
    · simp only [Set.indicator_of_mem hq]
      have hc : Continuous fun y : X => L q.1 (U q.1 a y) :=
        ((L q.1).continuous).comp (U q.1 a).continuous
      exact (hc.tendsto _).comp (hmk.tendsto_approx q.2)
    · simp only [Set.indicator_of_notMem hq]
      exact tendsto_const_nhds
  refine h1.congr ?_
  filter_upwards [hae] with q hq
  simp only [hq]

end TriFubiniAux
end UnforcedLeray.Short.IIb
