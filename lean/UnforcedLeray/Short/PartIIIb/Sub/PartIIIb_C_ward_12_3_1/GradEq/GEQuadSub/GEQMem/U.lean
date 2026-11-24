import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu

/-!
# `GEQMem`, first clause: `u ∈ L^{2q₀}_loc` (source 1515-1531, 2385-2387, 2531)

`u = p.uOf z = e + rep(w)`.  The affine inlet `e = p.eFun (p.coord z)` is `C^∞` jointly in
`(τ,y)` (`inlet_contDiff_joint`, `ν ≤ 1`), hence bounded on `[0,P] × B(0,R)`.  The correction
`w = p.wOf z` has an a.e. bounded joint representative (`geSupBound`, supremum embedding
1515-1531), hence is in `L^∞` of the phase measure and so in `L^{2q₀}` on every finite-measure
piece `(0,P] × B(0,R)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params rep)

/-- Finite measure of the local phase piece `(0,P] × B(0,R)`. -/
theorem finite_phaseLoc (P : ℝ) (R : ℝ) :
    IsFiniteMeasure ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P)) := by
    refine ⟨?_⟩; simp
  have : IsFiniteMeasure
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
    refine ⟨?_⟩
    simpa using (measure_closedBall_lt_top (x := (0 : UnforcedLeray.Space)) (r := R))
  infer_instance

/-- A strongly measurable phase-vector field with a.e. bound `M` on the phase measure is in
`L^q` of every local piece `(0,P] × B(0,R)`. -/
theorem memLp_phaseLoc_of_bound (P : ℝ) (R : ℝ)
    {f : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hf : StronglyMeasurable f) (M : ℝ) (hb : ∀ᵐ x ∂(phaseμ P), ‖f x‖ ≤ M) (q : ENNReal) :
    MemLp f q ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) := by
  have := finite_phaseLoc P R
  have hle : ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤ phaseμ P :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  refine MemLp.of_bound hf.aestronglyMeasurable M ?_
  exact Filter.Eventually.filter_mono (ae_mono hle) hb

theorem gEQMem_u : GERegime fun p z g => ∀ h, GEQHyp p z g h →
    ∀ i : Fin 3, MemLpLoc p.period (fun x => p.uOf z x i) (2 * UnforcedLeray.B0412.q0E) := by
  intro lam q hq dm dp hdm
  obtain ⟨n, hn, Hs⟩ := geSupBound lam q hq dm dp hdm
  refine ⟨min 1 n, lt_min one_pos hn, ?_⟩
  intro p d hreg hν hmode z g hd h _hh i R
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have hνn : p.ν ≤ n := hν.trans (min_le_right _ _)
  obtain ⟨M, -, hM⟩ := Hs p d hreg hνn hmode z g hd
  have hsm : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν1 hmode l).const_smul _
  have hcont : Continuous (fun x : ℝ × UnforcedLeray.Space => p.eFun (p.coord z) x i) :=
    (EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.comp
      hsm.continuous
  have hA := memLp_ddu_loc p.period R (f := fun x => p.eFun (p.coord z) x i) hcont
    (2 * UnforcedLeray.B0412.q0E)
  have hB : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (p.wOf z) x.1 x.2)
      (2 * UnforcedLeray.B0412.q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
    memLp_phaseLoc_of_bound p.period R (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf z)) M hM _
  have hBi : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (p.wOf z) x.1 x.2 i)
      (2 * UnforcedLeray.B0412.q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
    ((EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp
      (by simp) hB : _)
  have hfun : (fun x : ℝ × UnforcedLeray.Space => p.uOf z x i) =
      fun x => p.eFun (p.coord z) x i + rep (p.wOf z) x.1 x.2 i := by
    funext x
    simp [Params.uOf]
  rw [hfun]
  exact hA.add hBi

end UnforcedLeray.Short.PartIIIb.Concrete
