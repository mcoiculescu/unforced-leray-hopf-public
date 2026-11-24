import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Flux
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxBound
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeat
import UnforcedLeray.Lib.HeatCylinder.PeriodicLift
import UnforcedLeray.Lib.HeatCylinder.OrbitMeasurable

/-!
# Periodic representatives of the actual train flux columns

The physical flux is constructed as two genuine weighted `X c m` classes. This leaf chooses
strongly measurable representatives on the centered cell, extends them periodically, and feeds
those concrete representatives to the signed Gaussian heat-divergence cancellation in
`WeightedHeat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579

/-- The actual `X_m` flux column, represented strongly measurably and extended periodically from
the centered cell. -/
def trainPhysicalFluxPeriodicRep {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (i : Fin 2) : Plane → ℝ := by
  let f : X c m := trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound i
  let hsm : AEStronglyMeasurable (f : Plane → ℝ) (cellMeasure c m) := Lp.aestronglyMeasurable f
  exact UnforcedLeray.HeatCylinder.centeredPerLift (Fact.out : 0 < c) (hsm.mk f)

theorem stronglyMeasurable_trainPhysicalFluxPeriodicRep {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (i : Fin 2) : StronglyMeasurable
      (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound i) := by
  let f : X c m := trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound i
  let hsm : AEStronglyMeasurable (f : Plane → ℝ) (cellMeasure c m) := Lp.aestronglyMeasurable f
  exact (UnforcedLeray.HeatCylinder.measurable_centeredPerLift (Fact.out : 0 < c)
    hsm.stronglyMeasurable_mk.measurable).stronglyMeasurable

theorem periodic_trainPhysicalFluxPeriodicRep {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (i : Fin 2) : UnforcedLeray.Cyl.IsPeriodic c
      (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound i) :=
  UnforcedLeray.HeatCylinder.centeredPerLift_periodic (Fact.out : 0 < c) _

/-- The periodic representative agrees with the actual weighted `X_m` flux column a.e. on the
centered physical cell. -/
theorem trainPhysicalFluxPeriodicRep_ae_eq {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (i : Fin 2) :
    trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound i =ᵐ[Cyl.cellμ c]
      (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound i : Plane → ℝ) := by
  let f : X c m := trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound i
  let hsm : AEStronglyMeasurable (f : Plane → ℝ) (cellMeasure c m) := Lp.aestronglyMeasurable f
  have hbase : (f : Plane → ℝ) =ᵐ[cellMeasure c 0] hsm.mk f := by
    filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le hsm.ae_eq_mk] with x hx
    exact hx
  have hleft : -(c / 2) = -c / 2 := by ring
  have hcell : (f : Plane → ℝ) =ᵐ[Cyl.cellμ c] hsm.mk f := by
    simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol, B0579.cell, Cyl.cell,
      Cyl.cellμ, hleft] using hbase
  filter_upwards [hcell, ae_restrict_mem (Cyl.measurableSet_cell c)] with x hx hxc
  change UnforcedLeray.HeatCylinder.centeredPerLift (Fact.out : 0 < c) (hsm.mk f) x = f x
  rw [UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell (Fact.out : 0 < c) _ hxc]
  exact hx.symm

/-- The cell L1 supplier follows from the actual `X_m` flux class, with `m≥1`. -/
theorem integrable_trainPhysicalFluxPeriodicRep {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (i : Fin 2) : Integrable
      (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound i)
      (Cyl.cellμ c) := by
  have hactual := UnforcedLeray.B0583.integrable_of_X hm
    (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound i)
  have hactual' : Integrable
      (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound i : Plane → ℝ)
      (Cyl.cellμ c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simpa [UnforcedLeray.B0581.cellVol, B0579.cell, Cyl.cellμ, Cyl.cell, hleft] using hactual
  have hae := trainPhysicalFluxPeriodicRep_ae_eq tr hs hm w hcirc hCv hCE hvBound hEBound i
  exact hactual'.congr hae.symm

/-- Embed the two actual periodic flux columns as the first coordinate of the physical tensor
input to B0296's heat-divergence operator. -/
def trainPhysicalFluxPeriodicTensor {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    Plane → Plane × Plane :=
  scalarFluxTensor
    (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0)
    (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1)

theorem periodic_trainPhysicalFluxPeriodicTensor {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    Cyl.IsPeriodic c (trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound) := by
  intro z
  simp only [trainPhysicalFluxPeriodicTensor, scalarFluxTensor, Prod.mk.injEq, and_true]
  exact ⟨periodic_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0 z,
    periodic_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1 z⟩

theorem measurable_trainPhysicalFluxPeriodicTensor {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    Measurable (trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound) := by
  have h0 := stronglyMeasurable_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0
  have h1 := stronglyMeasurable_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1
  exact (h0.measurable.prodMk measurable_const).prodMk
    (h1.measurable.prodMk measurable_const)

/-- The physical flux tensor has the same radial `L²` integrability as its two `X_m` columns.
This is the concrete input hypothesis needed by the radial heat-divergence estimate. -/
theorem memLp_trainPhysicalFluxPeriodicTensor_radial {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    MemLp (fun z => bracket z ^ m •
      trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound z) 2
      (Cyl.cellμ c) := by
  have h0ae := trainPhysicalFluxPeriodicRep_ae_eq tr hs hm w hcirc hCv hCE hvBound hEBound 0
  have h1ae := trainPhysicalFluxPeriodicRep_ae_eq tr hs hm w hcirc hCv hCE hvBound hEBound 1
  have hleft : -(c / 2) = -c / 2 := by ring
  have h0w : trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0 =ᵐ[
      cellMeasure c m] (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 0 : Plane → ℝ) := by
    apply (cellMeasure_ac c m).ae_le
    have h0ae' : trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0 =ᵐ[
        volume.restrict (B0579.cell c)]
        (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 0 : Plane → ℝ) := by
      simpa [Cyl.cellμ, Cyl.cell, B0579.cell, hleft] using h0ae
    exact h0ae'
  have h1w : trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1 =ᵐ[
      cellMeasure c m] (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 : Plane → ℝ) := by
    apply (cellMeasure_ac c m).ae_le
    have h1ae' : trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1 =ᵐ[
        volume.restrict (B0579.cell c)]
        (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1 : Plane → ℝ) := by
      simpa [Cyl.cellμ, Cyl.cell, B0579.cell, hleft] using h1ae
    exact h1ae'
  have h0 : MemLp (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0)
      2 (cellMeasure c m) := by
    exact (memLp_congr_ae h0w).mpr
      (Lp.memLp (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 0))
  have h1 : MemLp (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1)
      2 (cellMeasure c m) := by
    exact (memLp_congr_ae h1w).mpr
      (Lp.memLp (trainPhysicalFluxX tr hs hm w hcirc hCv hCE hvBound hEBound 1))
  have h0rad : MemLp (fun z => bracket z ^ m *
      trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0 z) 2
      (Cyl.cellμ c) := by
    have hcell : Cyl.cell c = B0579.cell c := by
      simp only [Cyl.cell, B0579.cell]
      congr 1
      ring
    simpa [Cyl.cellμ, hcell] using (memLp_cellMeasure_iff c m).1 h0
  have h1rad : MemLp (fun z => bracket z ^ m *
      trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1 z) 2
      (Cyl.cellμ c) := by
    have hcell : Cyl.cell c = B0579.cell c := by
      simp only [Cyl.cell, B0579.cell]
      congr 1
      ring
    simpa [Cyl.cellμ, hcell] using (memLp_cellMeasure_iff c m).1 h1
  simp only [trainPhysicalFluxPeriodicTensor, scalarFluxTensor, Prod.smul_mk,
    smul_eq_mul, mul_zero]
  rw [memLp_prod_iff]
  constructor
  · rw [memLp_prod_iff]
    exact ⟨h0rad, (MemLp.zero : MemLp (0 : Plane → ℝ) 2 (Cyl.cellμ c))⟩
  · rw [memLp_prod_iff]
    exact ⟨h1rad, (MemLp.zero : MemLp (0 : Plane → ℝ) 2 (Cyl.cellμ c))⟩

/-- A radially weighted periodic train-flux tensor is also in unweighted centered-cell `L²`.
This is the normalization input for the actual cylinder heat orbit. -/
theorem memLp_trainPhysicalFluxPeriodicTensor_unweighted {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    MemLp (trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound) 2
      (Cyl.cellμ c) := by
  let T := trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound
  have hRad := memLp_trainPhysicalFluxPeriodicTensor_radial tr hs hm w hcirc hCv hCE hvBound hEBound
  have hmeas := measurable_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound
  have hTsm : AEStronglyMeasurable T (Cyl.cellμ c) :=
    hmeas.aestronglyMeasurable.mono_ac Measure.absolutelyContinuous_restrict
  have hbound : ∀ᵐ z ∂(Cyl.cellμ c), ‖T z‖ ≤
      ‖bracket z ^ m • T z‖ := by
    filter_upwards [] with z
    have hbase : 1 ≤ jb z := by
      dsimp [jb]
      nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    have hb : 1 ≤ bracket z := by
      dsimp [bracket]
      exact (Real.one_le_sqrt).2 hbase
    have hw : 1 ≤ bracket z ^ m := by
      rw [bracket_rpow]
      exact Real.one_le_rpow hbase (by linarith)
    have hw0 : 0 ≤ bracket z ^ m := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
    calc
      ‖T z‖ = 1 * ‖T z‖ := by simp
      _ ≤ bracket z ^ m * ‖T z‖ := by
        exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)

  have hmem : MemLp T 2 (Cyl.cellμ c) := hRad.of_le hTsm hbound
  simpa [T] using hmem

/-- The actual periodic train-flux tensor belongs to the normalized-cell `L²` carrier used by
the concrete B0296 cylinder heat orbit. -/
theorem memLp_trainPhysicalFluxPeriodicTensor_normalized {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    MemLp (trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
  exact UnforcedLeray.HeatCylinder.memLp_cellMeasure_of_memLp_cyl (Fact.out : 0 < c)
    (measurable_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)
    (by
      intro z
      simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
        periodic_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound z)
    (memLp_trainPhysicalFluxPeriodicTensor_unweighted tr hs hm w hcirc hCv hCE hvBound hEBound)

/-- The actual positive-age heat-divergence orbit of the train flux is AE strongly measurable
as a normalized-cell `L²` path; this is the concrete B0296 quotient orbit. -/
theorem aestronglyMeasurable_trainPhysicalFlux_heatDivL2Orbit {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    AEStronglyMeasurable
      (fun θ => UnforcedLeray.HeatCylinder.heatDivL2Orbit (Fact.out : 0 < c)
        (by
          intro z
          simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
            periodic_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound z)
        (measurable_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)
        (memLp_trainPhysicalFluxPeriodicTensor_normalized tr hs hm w hcirc hCv hCE hvBound hEBound)
        θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  exact UnforcedLeray.HeatCylinder.aestronglyMeasurable_heatDivL2Orbit
    (Fact.out : 0 < c)
    (by
      intro z
      simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
        periodic_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound z)
    (measurable_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)
    (memLp_trainPhysicalFluxPeriodicTensor_normalized tr hs hm w hcirc hCv hCE hvBound hEBound)

/-- Zero circulation of the signed Gaussian response to the periodic extension of the two actual
train flux columns. The extension agrees with those columns a.e. on the centered cell, and the
`m≥1` pivot supplies the required cell L1 integrability. -/
theorem trainPhysicalFlux_negativeHeatDiv_zero_circulation {ν c m θ : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (hθ : 0 < θ) :
    ∫ z in Cyl.cell c,
      (negativeHeatDiv θ (scalarFluxTensor
        (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0)
        (trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1)) z).1 = 0 := by
  exact integral_negativeHeatDiv_scalarFlux_eq_zero_of_cell_L1 (Fact.out : 0 < c) hθ
    (periodic_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0)
    (periodic_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1)
    (stronglyMeasurable_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0)
    (stronglyMeasurable_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1)
    (integrable_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 0)
    (integrable_trainPhysicalFluxPeriodicRep tr hs hm w hcirc hCv hCE hvBound hEBound 1)

/-- For every positive age parameter `θ≤1`, the actual sign-corrected Gaussian response to the
periodic extension of the train flux belongs to the radial weighted vorticity space `X_m`. -/
theorem memLp_trainPhysicalFlux_negativeHeatDiv_fst_X {ν c m θ : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    MemLp (fun z => (negativeHeatDiv θ
      (trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound) z).1) 2
      (cellMeasure c m) := by
  exact memLp_negativeHeatDiv_fst_X_of_radialInput (Fact.out : 0 < c) hθ hθ1
    (by linarith : 0 ≤ m)
    (periodic_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)
    (measurable_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)
    (memLp_trainPhysicalFluxPeriodicTensor_radial tr hs hm w hcirc hCv hCE hvBound hEBound)

/-- The actual signed heat response obeys the fixed-cylinder radial Gaussian moment bound, with
the input being the real train-flux tensor built above. Its explicit period factor is retained;
this estimate alone does not give the later uniform-in-`c` propagator rate. -/
theorem eLpNorm_trainPhysicalFlux_negativeHeatDiv_fst_sq_le {ν c m θ : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : X c m) (hcirc : ∫ x in cell c, w x = 0)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (eLpNorm (fun z => bracket z ^ m * (negativeHeatDiv θ
      (trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound) z).1)
      2 (Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ x : Plane, gradKernelAxialMomentDensity 1 m x)) ^ 2 *
      (eLpNorm (fun z => bracket z ^ m •
        trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound z)
        2 (Cyl.cellμ c)) ^ 2 := by
  exact eLpNorm_negativeHeatDiv_fst_sq_le_radialInput (Fact.out : 0 < c) hθ hθ1
    (by linarith : 0 ≤ m)
    (periodic_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)
    (measurable_trainPhysicalFluxPeriodicTensor tr hs hm w hcirc hCv hCE hvBound hEBound)

#print axioms trainPhysicalFluxPeriodicRep_ae_eq
#print axioms integrable_trainPhysicalFluxPeriodicRep
#print axioms memLp_trainPhysicalFluxPeriodicTensor_radial
#print axioms memLp_trainPhysicalFluxPeriodicTensor_normalized
#print axioms aestronglyMeasurable_trainPhysicalFlux_heatDivL2Orbit
#print axioms memLp_trainPhysicalFlux_negativeHeatDiv_fst_X
#print axioms eLpNorm_trainPhysicalFlux_negativeHeatDiv_fst_sq_le
#print axioms trainPhysicalFlux_negativeHeatDiv_zero_circulation

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
