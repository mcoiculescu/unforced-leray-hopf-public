import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalResidual
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorSupport
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellFullConvection

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412

/-- A smooth compact-spatial phase test belongs to every finite Lp space on one phase cell. -/
theorem memLp_phaseTest_cell {P : ℝ} {r : ℝ≥0∞} {T : SpaceTime → CVec3}
    [Fact (0 < P)] [Fact (1 ≤ r)] (hr : r ≠ ⊤)
    (hT : IsPhaseTest (P : ℝ) T) :
    MemLp T r (volume.restrict (phaseCell P)) := by
  obtain ⟨R, hR⟩ := hT.bounded_support
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC0, hC⟩ := exists_norm_bound_on_compact T hT.smooth.continuous (by simpa [K] using hK)
  apply memLp_vector_on_phaseCell_of_spatialSupport hr
    hT.smooth.continuous.aestronglyMeasurable
  · exact ⟨C, fun z hz => hC z (by simpa [K] using hz)⟩
  · intro τ hτ y hy
    exact hR τ y hy

#print axioms memLp_phaseTest_cell

/-- Pairing a compact smooth phase test with a bounded real background is integrable on its
phase cell. The test’s actual support localizes the background; no global Lp or time regularity is
used. -/
theorem integrable_phaseTest_boundedBackground_cell {P : ℝ} [Fact (0 < P)]
    {T : SpaceTime → CVec3} (hT : IsPhaseTest P T)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V) :
    Integrable (fun x : SpaceTime => dotL (T x) (realC (V x.1 x.2)))
      (volume.restrict (phaseCell P)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  obtain ⟨R, hR⟩ := hT.bounded_support
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hKm : MeasurableSet K := (isCompact_Icc.prod (isCompact_closedBall _ _)).measurableSet
  have hTmem : MemLp T (conjExp q0E) μ := by
    simpa [μ] using
      (memLp_phaseTest_cell (P := P) (r := conjExp q0E) (T := T)
        (conjExp_ne_top one_lt_q0E) hT)
  have hVmem : MemLp (K.indicator (fun x : SpaceTime => realC (V x.1 x.2))) q0E μ := by
    simpa [μ] using memLp_boundedBackground_cut_cell (P := P) (R := R) hV
  have hcut : Integrable
      (fun x : SpaceTime => dotL (T x)
        (K.indicator (fun x => realC (V x.1 x.2)) x)) μ :=
    integrable_dotL_of_memLp_holder hTmem hVmem
  have hae : (fun x : SpaceTime => dotL (T x) (realC (V x.1 x.2))) =ᵐ[μ]
      (fun x => dotL (T x) (K.indicator (fun x => realC (V x.1 x.2)) x)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with x hx
    by_cases hy : ‖x.2‖ ≤ R
    · have hxK : x ∈ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        exact ⟨⟨le_of_lt hx.1.1, hx.1.2⟩, hy⟩
      simp [Set.indicator_of_mem hxK]
    · have hz : T x = 0 := hR x.1 x.2 (lt_of_not_ge hy)
      simp [Set.indicator_of_notMem, hz, K, Metric.mem_closedBall, dist_zero_right, hy]
  exact hcut.congr hae.symm

#print axioms integrable_phaseTest_boundedBackground_cell

/-- The selected affine raw-plus-state field pairs with the actual L0 transpose as the sum of its
raw, graph, and coordinate-weighted inlet pairings. Every term has an explicit cell integrability
proof from the source backgrounds and the selected Yq state. -/
theorem selectedState_l0T_pairF_sum {p : Params} (hRaw : p.RawLiftRegular)
    (hInlet : p.InletRegular) {z : p.Z}
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest p.period Φ)
    [Fact (1 ≤ conjExp q0E)] [ENNReal.HolderTriple (conjExp q0E) q0E 1] :
    pairF p.period (L0T p.ν Φ) (fun x => p.Ufun x + p.uOf z x) =
      pairF p.period (L0T p.ν Φ) p.Ufun +
        (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
          ∑ i : Fin 2, (p.coord z i : ℂ) *
            pairF p.period (L0T p.ν Φ) (p.Efun i)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let T : SpaceTime → CVec3 := L0T p.ν Φ
  let V : ℝ → SpatialField := fun τ y =>
    ∑ i : Fin 2, (p.coord z i) • p.inlet i τ y
  have hT : IsPhaseTest p.period T := by
    exact isPhaseTest_L0T hΦ p.ν
  have hraw : Integrable (fun x => dotL (T x) (p.Ufun x)) μ := by
    change Integrable (fun x => dotL (T x) (realC (p.raw x.1 x.2))) μ
    exact integrable_phaseTest_boundedBackground_cell hT hRaw.1
  have hV : IsBoundedBackground V := isBoundedBackground_affineInlet hInlet (p.coord z)
  have hE : Integrable (fun x => dotL (T x) (p.eFun (p.coord z) x)) μ := by
    change Integrable
      (fun x => dotL (T x) (realC (V x.1 x.2))) (volume.restrict (phaseCell p.period))
    exact integrable_phaseTest_boundedBackground_cell hT hV
  have hWmem : MemLp (fun x : SpaceTime => rep (p.wOf z) x.1 x.2) q0E μ := by
    simpa [μ, phaseCell] using memLp_rep_periodCell q0E_ne_top (p.wOf z)
  have hW : Integrable
      (fun x => dotL (T x) (rep (p.wOf z) x.1 x.2)) μ := by
    exact integrable_dotL_of_memLp_holder
      (memLp_phaseTest_cell (P := p.period) (r := conjExp q0E) (T := T)
        (conjExp_ne_top one_lt_q0E) hT) hWmem
  have hstate : Integrable (fun x => dotL (T x) (p.uOf z x)) μ := by
    apply Integrable.congr (hE.add hW)
    filter_upwards [] with x
    simp [Params.uOf, dotL_apply, Finset.sum_add_distrib, mul_add]
  have htotal : Integrable
      (fun x => dotL (T x) (p.Ufun x + p.uOf z x)) μ := by
    apply Integrable.congr (hraw.add hstate)
    filter_upwards [] with x
    simp [dotL_apply, Finset.sum_add_distrib, mul_add]
  have hterms (i : Fin 2) : Integrable (fun x => dotL (T x) (p.Efun i x)) μ := by
    change Integrable (fun x => dotL (T x) (realC (p.inlet i x.1 x.2))) μ
    exact integrable_phaseTest_boundedBackground_cell hT (hInlet i).1
  have hweighted := pairF_affineInlet_right_eq_weighted (p := p) z hterms hE
  rw [pairF_add_right_of_integrable hraw hstate htotal]
  change pairF p.period T p.Ufun +
      pairF p.period T (fun x => p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2) = _
  rw [pairF_add_right_of_integrable hE hW (by simpa [Params.uOf] using hstate)]
  rw [hweighted]
  simp [T, add_assoc, add_comm, add_left_comm]

#print axioms selectedState_l0T_pairF_sum

end UnforcedLeray.Cons.C03.Concrete
