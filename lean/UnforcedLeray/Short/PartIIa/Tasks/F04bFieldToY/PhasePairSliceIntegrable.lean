import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1470-1480.

Proof. Let `Ψ` be a phase test and `w ∈ Y_r`. Since `Ψ` is a phase test, its slices form a
periodic continuous map `circleSlice hs : C(AddCircle P, L^{r'})`. For each `t`, the spatial
integral `∫ Ψ(t, y) · w(t)(y) dy` equals `innerPair r' (circleSlice hs t) (w t)` (pointwise, by
`MemLp.coeFn_toLp`). The circle function `τ ↦ innerPair (circleSlice hs τ) (w τ)` is
integrable for Haar measure: it is continuous-bilinear in `(circleSlice hs τ, w τ)`, hence
strongly measurable, and it is dominated by `‖innerPair‖ · ‖circleSlice hs‖ · ‖w τ‖`, which is
integrable because `w` is in `L^r` of a finite measure with `r ≥ 1`. Lebesgue measure on a period
is the pushforward of the Haar measure (`AddCircle.measurePreserving_mk`,
`AddCircle.volume_eq_smul_haarAddCircle`), which transfers integrability to `Ioc 0 P`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

theorem phasePairSliceIntegrable_proof : UnforcedLeray.Short.PartIIa.PhasePairSliceIntegrable := by
  intro r hr P hP w Ψ hΨ
  have hs := hΨ.isSliceTest (conjExp r)
  -- Step 1: integrability on the circle, for Haar measure.
  have hG : Integrable (fun τ : AddCircle P => innerPair r (circleSlice hs τ) (w τ))
      AddCircle.haarAddCircle := by
    refine Integrable.mono' (g := fun τ : AddCircle P => ‖innerPair r‖ * ‖circleSlice hs‖ * ‖w τ‖)
      ?_ ?_ ?_
    · exact ((MemLp.integrable hr.out (Lp.memLp w)).norm).const_mul _
    · have hmeas : AEStronglyMeasurable
          (fun τ : AddCircle P => (circleSlice hs τ, w τ)) AddCircle.haarAddCircle :=
        AEStronglyMeasurable.prodMk (circleSlice hs).continuous.aestronglyMeasurable
          (Lp.aestronglyMeasurable w)
      have hcont : Continuous (fun p : Lp CVec3 (conjExp r) (volume : Measure Space) ×
          Lp CVec3 r (volume : Measure Space) => innerPair r p.1 p.2) :=
        ContinuousLinearMap.continuous₂ (innerPair r)
      exact Continuous.comp_aestronglyMeasurable
        (f := fun τ : AddCircle P => (circleSlice hs τ, w τ)) hcont hmeas
    · refine Filter.Eventually.of_forall fun τ => ?_
      have h1 := (innerPair r).le_opNorm₂ (circleSlice hs τ) (w τ)
      have h2 : ‖circleSlice hs τ‖ ≤ ‖circleSlice hs‖ := ContinuousMap.norm_coe_le_norm (circleSlice hs) τ
      exact h1.trans (by gcongr)
  -- Step 2: transfer to the volume (Lebesgue) measure on the circle.
  have hcirc : Integrable (fun τ : AddCircle P => innerPair r (circleSlice hs τ) (w τ))
      (volume : Measure (AddCircle P)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact (integrable_smul_measure (ENNReal.ofReal_pos.mpr hP.out).ne' ENNReal.ofReal_ne_top).mpr hG
  -- Step 3: pull back along the covering map `ℝ → AddCircle P` on `Ioc 0 P`.
  have hmp : MeasurePreserving ((↑) : ℝ → AddCircle P) (volume.restrict (Ioc 0 P)) volume := by
    have h := AddCircle.measurePreserving_mk (T := P) 0
    rw [zero_add] at h
    exact h
  have key : IntegrableOn (fun t : ℝ => innerPair r (circleSlice hs (t : AddCircle P))
      (w (t : AddCircle P))) (Ioc 0 P) :=
    hmp.integrable_comp_of_integrable hcirc
  -- Step 4: identify the integrand pointwise with the circle function.
  refine key.congr_fun (fun t _ => ?_) measurableSet_Ioc
  dsimp only
  rw [circleSlice_coe, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
  simp only [sliceMap]
  rw [hy]

end UnforcedLeray.Short.PartIIa
