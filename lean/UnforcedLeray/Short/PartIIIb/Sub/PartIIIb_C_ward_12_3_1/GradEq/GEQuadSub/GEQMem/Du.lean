import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu

/-!
# `GEQMem`, second clause: `D u ∈ L^{2q₀}_loc` (source 2385-2387, 2531)

`GEQDu = dy e + rep(g j)`.  The inlet derivative `dy j e` is `C^∞` jointly in `(τ,y)`
(`inlet_contDiff_joint`, `ν ≤ 1`), hence bounded on `[0,P] × B(0,R)`, so in `L^{2q₀}` there
(`memLp_ddu_loc`).  The representative of `g j` is in `L^{2q₀}` of the whole phase cell by the
standing hypothesis `GEQHyp` (second conjunct), and restricts to the local piece by
`MemLp.mono_measure`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params rep)

theorem gEQMem_du : GERegime fun p z g => ∀ h, GEQHyp p z g h →
    ∀ j i : Fin 3, MemLpLoc p.period (fun x => GEQDu p z g j x i) (2 * UnforcedLeray.B0412.q0E) := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hmode z g hd h hh j i R
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hsm : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  have hcd : ContDiff ℝ ∞ (dy j (p.eFun (p.coord z))) := contDiff_dyT hsm j
  have hcont : Continuous (fun x : ℝ × UnforcedLeray.Space => dy j (p.eFun (p.coord z)) x i) :=
    (EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.comp hcd.continuous
  have hA := memLp_ddu_loc p.period R (f := fun x => dy j (p.eFun (p.coord z)) x i) hcont
    (2 * UnforcedLeray.B0412.q0E)
  have hle : ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤
      (volume.restrict (Ioc (0 : ℝ) p.period)).prod volume :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hB0 : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
      (2 * UnforcedLeray.B0412.q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
    MemLp.mono_measure hle (hh.2 j)
  have hB : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2 i)
      (2 * UnforcedLeray.B0412.q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
    ((EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp
      (by simp) hB0 : _)
  have hfun : (fun x : ℝ × UnforcedLeray.Space => GEQDu p z g j x i) =
      fun x => dy j (p.eFun (p.coord z)) x i + rep (g j) x.1 x.2 i := by
    funext x
    simp [GEQDu]
  rw [hfun]
  exact hA.add hB

end UnforcedLeray.Short.PartIIIb.Concrete
