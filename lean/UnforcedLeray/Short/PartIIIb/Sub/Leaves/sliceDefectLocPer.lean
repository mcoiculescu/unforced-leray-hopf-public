import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `sliceProdPairing`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Test the phase pairing identity with the product test `Θ(t,y) = φ(t) θ(y)`:
`lapT Θ = φ ⊗ lapS θ`, both pairings reduce to `∫_{(0,P]} φ(t) (ν ∫Φ·Δθ - ∫a·θ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Integrability of the slice integrals `t ↦ ∫_y Φ(t,y)·g(y)` on `(0,P]`, from local
integrability of `Φ ∈ Y_2` and boundedness/compact support of `g`. -/
theorem sliceInt_integrableOn_Icc {P a b : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) {g : Space → CVec3} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    IntegrableOn (fun t : ℝ => ∫ y : Space, ∑ i : Fin 3, Φ (t, y) i * g y i) (Icc a b) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Space)
  set K : Set (ℝ × Space) := Icc a b ×ˢ Metric.closedBall (0 : Space) R with hKdef
  set S : Set (ℝ × Space) := Icc a b ×ˢ (univ : Set Space) with hSdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hloc : LocallyIntegrable Φ volume := locInt_of_isInYr hP hΦ
  have hΦK : IntegrableOn Φ K volume := hloc.integrableOn_isCompact hK
  set h : ℝ × Space → ℂ := fun x => ∑ i : Fin 3, Φ x i * g x.2 i with hhdef
  have hdot : h = fun x => UnforcedLeray.PhaseSpace.dotL (Φ x) (g x.2) := by
    funext x
    simp only [hhdef, UnforcedLeray.PhaseSpace.dotL_apply]
  have hh_meas : AEStronglyMeasurable h volume := by
    rw [hdot]
    exact ContinuousLinearMap.aestronglyMeasurable_comp₂ UnforcedLeray.PhaseSpace.dotL
      hΦ.meas ((hg.comp continuous_snd).aestronglyMeasurable)
  have hbound : ∀ x, ‖h x‖ ≤ (‖UnforcedLeray.PhaseSpace.dotL‖ * C) * ‖Φ x‖ := by
    intro x
    rw [hdot]
    have h1 := UnforcedLeray.PhaseSpace.dotL.le_opNorm₂ (Φ x) (g x.2)
    have h2 := hC x.2
    calc ‖UnforcedLeray.PhaseSpace.dotL (Φ x) (g x.2)‖
        ≤ ‖UnforcedLeray.PhaseSpace.dotL‖ * ‖Φ x‖ * ‖g x.2‖ := h1
      _ ≤ ‖UnforcedLeray.PhaseSpace.dotL‖ * ‖Φ x‖ * C := by gcongr
      _ = (‖UnforcedLeray.PhaseSpace.dotL‖ * C) * ‖Φ x‖ := by ring
  have hIntK : IntegrableOn h K volume :=
    Integrable.mono' ((Integrable.norm hΦK).const_mul (‖UnforcedLeray.PhaseSpace.dotL‖ * C))
      hh_meas.restrict (ae_of_all _ fun x => hbound x)
  have hIntS : IntegrableOn h S volume := by
    refine IntegrableOn.of_forall_sdiff_eq_zero hIntK ?_ ?_
    · exact (measurableSet_Icc).prod MeasurableSet.univ
    · intro x hx
      have hy : x.2 ∉ Metric.closedBall (0 : Space) R := fun hc =>
        hx.2 (mk_mem_prod hx.1.1 hc)
      have hnot : x.2 ∉ tsupport g := fun ht => hy (hR ht)
      have hg0 : g x.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
      show ∑ i : Fin 3, Φ x i * g x.2 i = 0
      simp [hg0]
  have e : (volume.restrict (Icc a b)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict S := by
    conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure Space))]
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hprod : Integrable h ((volume.restrict (Icc a b)).prod (volume : Measure Space)) := by
    rw [e]
    exact hIntS
  exact hprod.integral_prod_left


theorem lapS_props {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    ContDiff ℝ ∞ (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) ∧
      HasCompactSupport (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) := by
  have hfj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const
  have hDj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (contDiff_infty_iff_fderiv.mp (hfj j)).2.clm_apply contDiff_const
  have hcj : ∀ j : Fin 3, HasCompactSupport (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => HasCompactSupport.fderiv_apply ℝ hc (EuclideanSpace.single j (1 : ℝ))
  have hsum_eq : UnforcedLeray.Short.PartIIIb.Concrete.lapS θ
      = fun y : Space => ∑ j : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)) := by
    funext y
    rfl
  have hcs : HasCompactSupport (∑ j : Fin 3, (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)))) :=
    HasCompactSupport.finset_sum fun j _ => HasCompactSupport.fderiv_apply ℝ (hcj j) (EuclideanSpace.single j (1 : ℝ))
  rw [hsum_eq]
  refine ⟨ContDiff.sum fun j _ => hDj j, ?_⟩
  convert hcs using 1
  funext y
  simp [Finset.sum_apply]


theorem sliceDefectLocPer : SliceDefectLocPer := by
  intro P ν hP Φ a hΦ ha θ hθ hc
  obtain ⟨hLs, hLc⟩ := lapS_props hθ hc
  have hLI : LocallyIntegrable (sliceDefect ν Φ a θ) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    have hsub : K ⊆ Icc (-M) M := by
      intro x hx
      have h := hM hx
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
      exact abs_le.mp h
    have h1 : IntegrableOn (fun t : ℝ => ∫ y : Space, ∑ i : Fin 3,
        Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i) (Icc (-M) M) :=
      sliceInt_integrableOn_Icc hP hΦ hLs.continuous hLc
    have h2 : IntegrableOn (fun t : ℝ => ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i)
        (Icc (-M) M) :=
      sliceInt_integrableOn_Icc hP ha hθ.continuous hc
    have h3 : IntegrableOn (fun t : ℝ => (ν : ℂ) * (∫ y : Space, ∑ i : Fin 3,
        Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
          - ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i) (Icc (-M) M) :=
      (Integrable.const_mul h1 (ν : ℂ)).sub h2
    exact IntegrableOn.mono_set h3 hsub
  refine ⟨hLI, ?_⟩
  have hpA : ∀ᵐ t : ℝ, ∀ᵐ y : Space, Φ (t + P, y) = Φ (t, y) := by
    have h := hΦ.periodic
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  have hpB : ∀ᵐ t : ℝ, ∀ᵐ y : Space, a (t + P, y) = a (t, y) := by
    have h := ha.periodic
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  have hI1 : ∀ᵐ t : ℝ, (∫ y : Space, ∑ i : Fin 3,
      Φ (t + P, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i)
        = ∫ y : Space, ∑ i : Fin 3, Φ (t, y) i * UnforcedLeray.Short.PartIIIb.Concrete.lapS θ y i := by
    filter_upwards [hpA] with t ht
    apply integral_congr_ae
    filter_upwards [ht] with y hy
    simp only [hy]
  have hI2 : ∀ᵐ t : ℝ, (∫ y : Space, ∑ i : Fin 3, a (t + P, y) i * θ y i)
        = ∫ y : Space, ∑ i : Fin 3, a (t, y) i * θ y i := by
    filter_upwards [hpB] with t ht
    apply integral_congr_ae
    filter_upwards [ht] with y hy
    simp only [hy]
  filter_upwards [hI1, hI2] with t h1 h2
  simp only [sliceDefect]
  rw [h1, h2]

end UnforcedLeray.Short.PartIIIb.Concrete
