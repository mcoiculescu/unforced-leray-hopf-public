import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp

/-!
# `GEQMem`, third clause: `D²u ∈ L^{q₀}_loc` (source 2385-2387, 2531)

`D_jD_k u = ∂_j∂_k e + rep(h j k)`.  The affine inlet `e` is `C^∞` jointly in `(τ,y)`
(the proof of `inletJointSmooth`, which needs only `ν ≤ 1`, not the slow datum `ageCut`), so
`∂_j∂_k e` is continuous, hence bounded on `[0,P] × B(0,R)`, hence in `L^{q₀}` there.  The
representative of `h j k` is in `L^{q₀}` on the cell (`memLp_rep_periodCell`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params rep)
open UnforcedLeray.Short.IIb (BgRegime inletCD_ringStreamProfile inletCD_frozenStream)

/-- Joint smoothness of the inlet for every `ν ≤ 1` (slow datum `ageCut` arbitrary). -/
theorem inlet_contDiff_joint (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.inlet i x.1 x.2) := by
  obtain ⟨C, κ, N, -, -, hper⟩ := UnforcedLeray.Short.IIb.frozenStreamBounds lam q hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((Cons.C03.Concrete.contDiff_ageCutoff p.H).comp contDiff_fst).mul
      ((hfro i).comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  have hvan : ∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0 := by
    intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [Cons.C03.Concrete.ageCutoff_eq_zero hH hx.le]
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
        (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [Cons.C03.Concrete.ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]
      simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by
      unfold Axi.dS
      rw [hfd]
      simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
      unfold Axi.dQ
      rw [hfd]
      simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by
      unfold Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  exact UnforcedLeray.Short.IIb.NicePT.contDiff_Nv p.R_pos hB (s1 := p.H / 2) hvan

theorem contDiff_realC : ContDiff ℝ ∞ UnforcedLeray.B0412.realC := by
  unfold UnforcedLeray.B0412.realC
  refine ContDiff.sum fun i _ => ?_
  refine ContDiff.smul (𝕜 := ℝ) (𝕜' := ℂ) ?_ (contDiff_const (c := (EuclideanSpace.single i (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)))
  have h1 : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => x i) :=
    (EuclideanSpace.proj i : UnforcedLeray.Space →L[ℝ] ℝ).contDiff
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  exact h2.comp h1

theorem contDiff_dyT {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × UnforcedLeray.Space → F} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem memLp_ddu_loc (P : ℝ) [Fact (0 < P)] (R : ℝ)
    {f : ℝ × UnforcedLeray.Space → ℂ} (hf : Continuous f)
    (q : ENNReal) :
    MemLp f q ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) := by
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hfin : IsFiniteMeasure ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) := by
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P)) := by
      refine ⟨?_⟩; simp
    have : IsFiniteMeasure
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
      refine ⟨?_⟩
      simpa using (measure_closedBall_lt_top (x := (0 : UnforcedLeray.Space)) (r := R))
    infer_instance
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  have h1 : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), τ ∈ Icc (0 : ℝ) P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact ⟨hτ.1.le, hτ.2⟩
  have h2 : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)),
      y ∈ Metric.closedBall (0 : UnforcedLeray.Space) R :=
    ae_restrict_mem Metric.isClosed_closedBall.measurableSet
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards [h1] with τ hτ
    filter_upwards [h2] with y hy
    exact hC (τ, y) ⟨hτ, hy⟩
  · exact measurableSet_le hf.norm.measurable measurable_const

theorem gEQMem_ddu : GERegime fun p z g => ∀ h, GEQHyp p z g h →
    ∀ j k i : Fin 3, MemLpLoc p.period (fun x => GEQDdu p z g h j k x i)
      UnforcedLeray.B0412.q0E := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hmode z g hd h hh j k i R
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hsm : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  have hcont : Continuous (dy j (dy k (p.eFun (p.coord z)))) :=
    (contDiff_dyT (contDiff_dyT hsm k) j).continuous
  have hA := memLp_ddu_loc p.period R
    (f := fun x => dy j (dy k (p.eFun (p.coord z))) x i)
    ((EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.comp hcont)
    UnforcedLeray.B0412.q0E
  have hrep := UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell
    (q := UnforcedLeray.B0412.q0E) (by simp [UnforcedLeray.B0412.q0E]) (h j k)
  have hB : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (h j k) x.1 x.2 i)
      UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) := by
    have hle : ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤
        (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
          (Ioc (0 : ℝ) p.period ×ˢ (univ : Set UnforcedLeray.Space)) := by
      have : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
          (Ioc (0 : ℝ) p.period ×ˢ (univ : Set UnforcedLeray.Space)) =
          (volume.restrict (Ioc (0 : ℝ) p.period)).prod volume := by
        simpa only [Measure.volume_eq_prod] using
          (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
            (ν := (volume : Measure UnforcedLeray.Space)) (Ioc 0 p.period)).symm
      rw [this]
      exact Measure.prod_mono le_rfl Measure.restrict_le_self
    have h1 := (hrep.mono_measure hle)
    exact ((EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp
      (by simp) h1 : _)
  exact hA.add hB

end UnforcedLeray.Short.PartIIIb.Concrete
