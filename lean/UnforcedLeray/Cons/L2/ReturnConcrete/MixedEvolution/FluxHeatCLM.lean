import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxPeriodic
import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit

/-!
# Signed heat response of arbitrary weighted flux columns

This leaf generalizes the actual-train representative results to every pair of weighted
`X c m` columns. It supplies the domain needed for a state-independent signed heat-divergence
operator in the fixed-cylinder Volterra construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579

/-- Strongly measurable periodic extension of an arbitrary weighted flux column. -/
def xColumnPeriodicRep {c m : ℝ} (hc : 0 < c) (f : X c m) : Plane → ℝ := by
  let hsm : AEStronglyMeasurable (f : Plane → ℝ) (cellMeasure c m) := Lp.aestronglyMeasurable f
  exact UnforcedLeray.HeatCylinder.centeredPerLift hc (hsm.mk f)

theorem stronglyMeasurable_xColumnPeriodicRep {c m : ℝ} (hc : 0 < c) (f : X c m) :
    StronglyMeasurable (xColumnPeriodicRep hc f) := by
  let hsm : AEStronglyMeasurable (f : Plane → ℝ) (cellMeasure c m) := Lp.aestronglyMeasurable f
  exact (UnforcedLeray.HeatCylinder.measurable_centeredPerLift hc
    hsm.stronglyMeasurable_mk.measurable).stronglyMeasurable

theorem periodic_xColumnPeriodicRep {c m : ℝ} (hc : 0 < c) (f : X c m) :
    Cyl.IsPeriodic c (xColumnPeriodicRep hc f) :=
  UnforcedLeray.HeatCylinder.centeredPerLift_periodic hc _

theorem xColumnPeriodicRep_ae_eq {c m : ℝ} (hc : 0 < c) (f : X c m) :
    xColumnPeriodicRep hc f =ᵐ[Cyl.cellμ c] (f : Plane → ℝ) := by
  let hsm : AEStronglyMeasurable (f : Plane → ℝ) (cellMeasure c m) := Lp.aestronglyMeasurable f
  have hbase : (f : Plane → ℝ) =ᵐ[cellMeasure c 0] hsm.mk f := by
    filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le hsm.ae_eq_mk] with z hz
    exact hz
  have hleft : -(c / 2) = -c / 2 := by ring
  have hcell : (f : Plane → ℝ) =ᵐ[Cyl.cellμ c] hsm.mk f := by
    simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
      B0579.cell, Cyl.cell, Cyl.cellμ, hleft] using hbase
  filter_upwards [hcell, ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz hzc
  change UnforcedLeray.HeatCylinder.centeredPerLift hc (hsm.mk f) z = f z
  rw [UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell hc _ hzc]
  exact hz.symm

theorem integrable_xColumnPeriodicRep {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (f : X c m) :
    Integrable (xColumnPeriodicRep hc f) (Cyl.cellμ c) := by
  have hactual := UnforcedLeray.B0583.integrable_of_X hm f
  have hactual' : Integrable (f : Plane → ℝ) (Cyl.cellμ c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simpa [UnforcedLeray.B0581.cellVol, B0579.cell, Cyl.cellμ, Cyl.cell, hleft] using hactual
  exact hactual'.congr (xColumnPeriodicRep_ae_eq hc f).symm

/-- Periodic tensor formed from an arbitrary pair of actual `X_m` flux columns. -/
def xFluxPeriodicTensor {c m : ℝ} (hc : 0 < c) (F : Fin 2 → X c m) :
    Plane → Plane × Plane :=
  scalarFluxTensor (xColumnPeriodicRep hc (F 0)) (xColumnPeriodicRep hc (F 1))

/-- The raw centered-cell tensor of an arbitrary pair of weighted flux columns. -/
def xFluxRawTensor {c m : ℝ} (F : Fin 2 → X c m) : Plane → Plane × Plane :=
  scalarFluxTensor (F 0) (F 1)

theorem xFluxPeriodicTensor_ae_eq_raw {c m : ℝ} (hc : 0 < c) (F : Fin 2 → X c m) :
    xFluxPeriodicTensor hc F =ᵐ[Cyl.cellμ c] xFluxRawTensor F := by
  filter_upwards [xColumnPeriodicRep_ae_eq hc (F 0), xColumnPeriodicRep_ae_eq hc (F 1)]
    with z h0 h1
  simp [xFluxPeriodicTensor, xFluxRawTensor, scalarFluxTensor, h0, h1]

theorem xFluxRawTensor_add_ae {c m : ℝ} (F G : Fin 2 → X c m) :
    xFluxRawTensor (F + G) =ᵐ[Cyl.cellμ c]
      (fun z => xFluxRawTensor F z + xFluxRawTensor G z) := by
  have hleft : -(c / 2) = -c / 2 := by ring
  have h0 : (F 0 + G 0 : X c m) =ᵐ[Cyl.cellμ c]
      fun z => F 0 z + G 0 z := by
    have h := Lp.coeFn_add (F 0) (G 0)
    have hc0 : (cellMeasure c 0) = Cyl.cellμ c := by
      simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
        B0579.cell, Cyl.cellμ, Cyl.cell, hleft]
    have h0c : (F 0 + G 0 : X c m) =ᵐ[cellMeasure c 0]
        fun z => F 0 z + G 0 z := by
      filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le h] with z hz
      exact hz
    simpa only [hc0] using h0c
  have h1 : (F 1 + G 1 : X c m) =ᵐ[Cyl.cellμ c]
      fun z => F 1 z + G 1 z := by
    have h := Lp.coeFn_add (F 1) (G 1)
    have hc0 : (cellMeasure c 0) = Cyl.cellμ c := by
      simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
        B0579.cell, Cyl.cellμ, Cyl.cell, hleft]
    have h1c : (F 1 + G 1 : X c m) =ᵐ[cellMeasure c 0]
        fun z => F 1 z + G 1 z := by
      filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le h] with z hz
      exact hz
    simpa only [hc0] using h1c
  filter_upwards [h0, h1] with z hz0 hz1
  change ((↑((F 0 + G 0 : X c m) z), (0 : ℝ)),
      (↑((F 1 + G 1 : X c m) z), (0 : ℝ))) =
    (((F 0 z, (0 : ℝ)), (F 1 z, (0 : ℝ))) +
      ((G 0 z, (0 : ℝ)), (G 1 z, (0 : ℝ))))
  rw [hz0, hz1]
  simp

theorem periodic_xFluxPeriodicTensor {c m : ℝ} (hc : 0 < c) (F : Fin 2 → X c m) :
    Cyl.IsPeriodic c (xFluxPeriodicTensor hc F) := by
  intro z
  simp only [xFluxPeriodicTensor, scalarFluxTensor, Prod.mk.injEq, and_true]
  exact ⟨periodic_xColumnPeriodicRep hc (F 0) z, periodic_xColumnPeriodicRep hc (F 1) z⟩

theorem measurable_xFluxPeriodicTensor {c m : ℝ} (hc : 0 < c) (F : Fin 2 → X c m) :
    Measurable (xFluxPeriodicTensor hc F) := by
  have h0 := (stronglyMeasurable_xColumnPeriodicRep hc (F 0)).measurable
  have h1 := (stronglyMeasurable_xColumnPeriodicRep hc (F 1)).measurable
  exact (h0.prodMk measurable_const).prodMk (h1.prodMk measurable_const)

/-- Every pair of arbitrary `X_m` columns gives a radial weighted tensor in B0296's heat-input
space. The proof is componentwise and keeps the correct centered radial weight. -/
theorem memLp_xFluxPeriodicTensor_radial {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F : Fin 2 → X c m) :
    MemLp (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z) 2 (Cyl.cellμ c) := by
  have hleft : -(c / 2) = -c / 2 := by ring
  have h0ae := xColumnPeriodicRep_ae_eq hc (F 0)
  have h1ae := xColumnPeriodicRep_ae_eq hc (F 1)
  have h0w : xColumnPeriodicRep hc (F 0) =ᵐ[cellMeasure c m] (F 0 : Plane → ℝ) := by
    apply (cellMeasure_ac c m).ae_le
    have hae : xColumnPeriodicRep hc (F 0) =ᵐ[volume.restrict (B0579.cell c)]
        (F 0 : Plane → ℝ) := by
      simpa [Cyl.cellμ, Cyl.cell, B0579.cell, hleft] using h0ae
    exact hae
  have h1w : xColumnPeriodicRep hc (F 1) =ᵐ[cellMeasure c m] (F 1 : Plane → ℝ) := by
    apply (cellMeasure_ac c m).ae_le
    have hae : xColumnPeriodicRep hc (F 1) =ᵐ[volume.restrict (B0579.cell c)]
        (F 1 : Plane → ℝ) := by
      simpa [Cyl.cellμ, Cyl.cell, B0579.cell, hleft] using h1ae
    exact hae
  have h0 : MemLp (xColumnPeriodicRep hc (F 0)) 2 (cellMeasure c m) :=
    (memLp_congr_ae h0w).mpr (Lp.memLp (F 0))
  have h1 : MemLp (xColumnPeriodicRep hc (F 1)) 2 (cellMeasure c m) :=
    (memLp_congr_ae h1w).mpr (Lp.memLp (F 1))
  have hcell : Cyl.cell c = B0579.cell c := by
    simp only [Cyl.cell, B0579.cell]
    congr 1
    ring
  have h0rad : MemLp (fun z => bracket z ^ m * xColumnPeriodicRep hc (F 0) z) 2
      (Cyl.cellμ c) := by
    simpa [Cyl.cellμ, hcell] using (memLp_cellMeasure_iff c m).1 h0
  have h1rad : MemLp (fun z => bracket z ^ m * xColumnPeriodicRep hc (F 1) z) 2
      (Cyl.cellμ c) := by
    simpa [Cyl.cellμ, hcell] using (memLp_cellMeasure_iff c m).1 h1
  simp only [xFluxPeriodicTensor, scalarFluxTensor, Prod.smul_mk, smul_eq_mul, mul_zero]
  rw [memLp_prod_iff]
  constructor
  · rw [memLp_prod_iff]
    exact ⟨h0rad, (MemLp.zero : MemLp (0 : Plane → ℝ) 2 (Cyl.cellμ c))⟩
  · rw [memLp_prod_iff]
    exact ⟨h1rad, (MemLp.zero : MemLp (0 : Plane → ℝ) 2 (Cyl.cellμ c))⟩

theorem memLp_xFluxPeriodicTensor_unweighted {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F : Fin 2 → X c m) : MemLp (xFluxPeriodicTensor hc F) 2 (Cyl.cellμ c) := by
  let T := xFluxPeriodicTensor hc F
  have hRad := memLp_xFluxPeriodicTensor_radial hc hm F
  have hTsm : AEStronglyMeasurable T (Cyl.cellμ c) :=
    (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable.mono_ac
      Measure.absolutelyContinuous_restrict
  have hbound : ∀ᵐ z ∂(Cyl.cellμ c), ‖T z‖ ≤ ‖bracket z ^ m • T z‖ := by
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
    calc ‖T z‖ = 1 * ‖T z‖ := by simp
      _ ≤ bracket z ^ m * ‖T z‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  have hmem : MemLp T 2 (Cyl.cellμ c) := hRad.of_le hTsm hbound
  simpa [T] using hmem

theorem memLp_xFluxPeriodicTensor_normalized {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F : Fin 2 → X c m) :
    MemLp (xFluxPeriodicTensor hc F) 2 (UnforcedLeray.B0284.cellMeasure c) := by
  exact UnforcedLeray.HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    (measurable_xFluxPeriodicTensor hc F)
    (by
      intro z
      simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
        periodic_xFluxPeriodicTensor hc F z)
    (memLp_xFluxPeriodicTensor_unweighted hc hm F)

/-- The actual normalized tensor class associated with two `X_m` flux columns. -/
def xFluxPeriodicTensorInput {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F : Fin 2 → X c m) : Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (memLp_xFluxPeriodicTensor_normalized hc hm F).toLp (xFluxPeriodicTensor hc F)

theorem xFluxPeriodicTensorInput_add {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F G : Fin 2 → X c m) :
    xFluxPeriodicTensorInput hc hm (F + G) =
      xFluxPeriodicTensorInput hc hm F + xFluxPeriodicTensorInput hc hm G := by
  have hcenter : xFluxPeriodicTensor hc (F + G) =ᵐ[Cyl.cellμ c]
      (fun z => xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z) := by
    have hFG := xFluxPeriodicTensor_ae_eq_raw hc (F + G)
    have hF := xFluxPeriodicTensor_ae_eq_raw hc F
    have hG := xFluxPeriodicTensor_ae_eq_raw hc G
    have hraw := xFluxRawTensor_add_ae F G
    filter_upwards [hFG, hF, hG, hraw] with z hfg hf hg hsum
    rw [hfg, hf, hg, hsum]
  have hper : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z) := by
    intro z
    change xFluxPeriodicTensor hc F (z.1 + c, z.2) +
      xFluxPeriodicTensor hc G (z.1 + c, z.2) = _
    rw [(periodic_xFluxPeriodicTensor hc F) z, (periodic_xFluxPeriodicTensor hc G) z]
  have hnorm := UnforcedLeray.HeatCylinder.ae_eq_of_ae_centered_periodic hc
    (periodic_xFluxPeriodicTensor hc (F + G)) hper hcenter
  apply Lp.ext
  have hclassFG : (xFluxPeriodicTensorInput hc hm (F + G) : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] xFluxPeriodicTensor hc (F + G) := by
    simpa [xFluxPeriodicTensorInput] using
      (memLp_xFluxPeriodicTensor_normalized hc hm (F + G)).coeFn_toLp
  have hclassF : (xFluxPeriodicTensorInput hc hm F : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] xFluxPeriodicTensor hc F := by
    simpa [xFluxPeriodicTensorInput] using
      (memLp_xFluxPeriodicTensor_normalized hc hm F).coeFn_toLp
  have hclassG : (xFluxPeriodicTensorInput hc hm G : Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] xFluxPeriodicTensor hc G := by
    simpa [xFluxPeriodicTensorInput] using
      (memLp_xFluxPeriodicTensor_normalized hc hm G).coeFn_toLp
  filter_upwards [hclassFG, hclassF, hclassG, hnorm,
    Lp.coeFn_add (xFluxPeriodicTensorInput hc hm F) (xFluxPeriodicTensorInput hc hm G)]
      with z hfg hf hg hperiod hsum
  change (↑(xFluxPeriodicTensorInput hc hm (F + G)) : Plane → Plane × Plane) z = _
  calc
    _ = xFluxPeriodicTensor hc (F + G) z := hfg
    _ = xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z := hperiod
    _ = ((xFluxPeriodicTensorInput hc hm F : Plane → Plane × Plane) +
        (xFluxPeriodicTensorInput hc hm G : Plane → Plane × Plane)) z := by
      rw [← hf, ← hg]
      simp only [Pi.add_apply]
    _ = (↑(xFluxPeriodicTensorInput hc hm F + xFluxPeriodicTensorInput hc hm G) :
        Plane → Plane × Plane) z := by
      change ((↑(xFluxPeriodicTensorInput hc hm F) : Plane → Plane × Plane) +
        (↑(xFluxPeriodicTensorInput hc hm G) : Plane → Plane × Plane)) z = _
      exact hsum.symm

theorem xFluxPeriodicTensorInput_smul {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (r : ℝ) (F : Fin 2 → X c m) :
    xFluxPeriodicTensorInput hc hm (r • F) = r • xFluxPeriodicTensorInput hc hm F := by
  have hleft : -(c / 2) = -c / 2 := by ring
  have h0 : (r • F 0 : X c m) =ᵐ[Cyl.cellμ c] fun z => r • F 0 z := by
    have h := Lp.coeFn_smul r (F 0)
    have hc0 : cellMeasure c 0 = Cyl.cellμ c := by
      simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
        B0579.cell, Cyl.cellμ, Cyl.cell, hleft]
    have h0c : (r • F 0 : X c m) =ᵐ[cellMeasure c 0] fun z => r • F 0 z := by
      filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le h] with z hz
      exact hz
    simpa only [hc0] using h0c
  have h1 : (r • F 1 : X c m) =ᵐ[Cyl.cellμ c] fun z => r • F 1 z := by
    have h := Lp.coeFn_smul r (F 1)
    have hc0 : cellMeasure c 0 = Cyl.cellμ c := by
      simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
        B0579.cell, Cyl.cellμ, Cyl.cell, hleft]
    have h1c : (r • F 1 : X c m) =ᵐ[cellMeasure c 0] fun z => r • F 1 z := by
      filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le h] with z hz
      exact hz
    simpa only [hc0] using h1c
  have hraw : xFluxRawTensor (r • F) =ᵐ[Cyl.cellμ c]
      (fun z => r • xFluxRawTensor F z) := by
    filter_upwards [h0, h1] with z hz0 hz1
    simp [xFluxRawTensor, scalarFluxTensor, hz0, hz1]
  have hrep := xFluxPeriodicTensor_ae_eq_raw hc (r • F)
  have hrepF := xFluxPeriodicTensor_ae_eq_raw hc F
  have hcenter : xFluxPeriodicTensor hc (r • F) =ᵐ[Cyl.cellμ c]
      (fun z => r • xFluxPeriodicTensor hc F z) := by
    filter_upwards [hrep, hrepF, hraw] with z hr hf hsum
    rw [hr, hf, hsum]
  have hper : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => r • xFluxPeriodicTensor hc F z) := by
    intro z
    change r • xFluxPeriodicTensor hc F (z.1 + c, z.2) = _
    rw [(periodic_xFluxPeriodicTensor hc F) z]
  have hnorm := UnforcedLeray.HeatCylinder.ae_eq_of_ae_centered_periodic hc
    (periodic_xFluxPeriodicTensor hc (r • F)) hper hcenter
  apply Lp.ext
  have hclass := (memLp_xFluxPeriodicTensor_normalized hc hm (r • F)).coeFn_toLp
  have hclassF := (memLp_xFluxPeriodicTensor_normalized hc hm F).coeFn_toLp
  have hclassSmul : (↑(r • xFluxPeriodicTensorInput hc hm F) :
      Plane → Plane × Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] (fun z => r • xFluxPeriodicTensor hc F z) := by
    filter_upwards [Lp.coeFn_smul r (xFluxPeriodicTensorInput hc hm F), hclassF] with z hs hf
    calc
      _ = r • (xFluxPeriodicTensorInput hc hm F : Plane → Plane × Plane) z := hs
      _ = r • xFluxPeriodicTensor hc F z :=
        congrArg (fun v : Plane × Plane => r • v) hf
  filter_upwards [hclass, hnorm, hclassSmul] with z hf hnorm hsm
  exact hf.trans (hnorm.trans hsm.symm)

/-- Linear normalized-cell realization of arbitrary `X_m` flux columns. -/
def xFluxPeriodicTensorInputLinear {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) :
    (Fin 2 → X c m) →ₗ[ℝ] Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) where
  toFun := xFluxPeriodicTensorInput hc hm
  map_add' := xFluxPeriodicTensorInput_add hc hm
  map_smul' := xFluxPeriodicTensorInput_smul hc hm

/-- The normalized periodic tensor realization costs exactly the expected `c⁻¹ᐟ²` cell factor;
the two scalar columns are bounded by the sum of their weighted norms. -/
theorem norm_xFluxPeriodicTensorInput_le {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F : Fin 2 → X c m) :
    ‖xFluxPeriodicTensorInput hc hm F‖ ≤ Real.sqrt (c⁻¹) * (‖F 0‖ + ‖F 1‖) := by
  let T := xFluxPeriodicTensor hc F
  have hTmeas : Measurable T := measurable_xFluxPeriodicTensor hc F
  have hTper : UnforcedLeray.B0284.IsQPeriodic c T := by
    intro z
    simpa [T, UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
      periodic_xFluxPeriodicTensor hc F z
  have hTmem : MemLp T 2 (Cyl.cellμ c) := memLp_xFluxPeriodicTensor_unweighted hc hm F
  have hcenter : (eLpNorm T 2 (Cyl.cellμ c)).toReal ≤ ‖F 0‖ + ‖F 1‖ := by
    have hpoint : ∀ᵐ z ∂(Cyl.cellμ c), ‖T z‖ ≤ ‖F 0 z‖ + ‖F 1 z‖ := by
      filter_upwards [xFluxPeriodicTensor_ae_eq_raw hc F] with z hz
      change ‖xFluxPeriodicTensor hc F z‖ ≤ _
      rw [hz]
      simp only [xFluxRawTensor, scalarFluxTensor]
      have hsplit : ((F 0 z, (0 : ℝ)), (F 1 z, (0 : ℝ))) =
          ((F 0 z, (0 : ℝ)), 0) + (0, (F 1 z, (0 : ℝ))) := by
        ext <;> simp
      rw [hsplit]
      calc
        ‖((F 0 z, (0 : ℝ)), 0) + (0, (F 1 z, (0 : ℝ)))‖ ≤
            ‖((F 0 z, (0 : ℝ)), 0)‖ + ‖((0 : Plane), (F 1 z, (0 : ℝ)))‖ :=
              norm_add_le _ _
        _ = ‖(F 0 z, (0 : ℝ))‖ + ‖(F 1 z, (0 : ℝ))‖ := by simp
        _ = ‖F 0 z‖ + ‖F 1 z‖ := by simp [Real.norm_eq_abs]
    have hmajor : eLpNorm T 2 (Cyl.cellμ c) ≤
        eLpNorm (fun z => ‖F 0 z‖ + ‖F 1 z‖) 2 (Cyl.cellμ c) :=
      eLpNorm_mono_ae_real hpoint
    have hμ : Cyl.cellμ c = UnforcedLeray.B0581.cellVol c := by
      have hleft : -(c / 2) = -c / 2 := by ring
      simp [Cyl.cellμ, UnforcedLeray.B0581.cellVol, B0579.cell, Cyl.cell, hleft]
    have hac : Cyl.cellμ c ≪ cellMeasure c m := by
      rw [hμ, ← cellMeasure_zero_eq_cellVol]
      exact cellMeasure_ac_cellMeasure c 0 m
    have hsum : eLpNorm (fun z => ‖F 0 z‖ + ‖F 1 z‖) 2 (Cyl.cellμ c) ≤
        eLpNorm (fun z => ‖F 0 z‖) 2 (Cyl.cellμ c) +
          eLpNorm (fun z => ‖F 1 z‖) 2 (Cyl.cellμ c) := by
      exact eLpNorm_add_le ((Lp.aestronglyMeasurable (F 0)).mono_ac hac).norm
        ((Lp.aestronglyMeasurable (F 1)).mono_ac hac).norm (by norm_num)
    have h0 : eLpNorm (fun z => ‖F 0 z‖) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal ‖F 0‖ := by
      rw [hμ]
      calc
        eLpNorm (fun z => ‖F 0 z‖) 2 (UnforcedLeray.B0581.cellVol c) =
            eLpNorm (F 0 : Plane → ℝ) 2 (UnforcedLeray.B0581.cellVol c) := by
              rw [eLpNorm_norm]
        _ ≤ eLpNorm (F 0 : Plane → ℝ) 2 (cellMeasure c m) :=
              eLpNorm_mono_measure _ (UnforcedLeray.B0581.cellVol_le_cellMeasure c (by linarith))
        _ = ENNReal.ofReal ‖F 0‖ := by
              rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (F 0)), ← Lp.norm_def]
    have h1 : eLpNorm (fun z => ‖F 1 z‖) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal ‖F 1‖ := by
      rw [hμ]
      calc
        eLpNorm (fun z => ‖F 1 z‖) 2 (UnforcedLeray.B0581.cellVol c) =
            eLpNorm (F 1 : Plane → ℝ) 2 (UnforcedLeray.B0581.cellVol c) := by
              rw [eLpNorm_norm]
        _ ≤ eLpNorm (F 1 : Plane → ℝ) 2 (cellMeasure c m) :=
              eLpNorm_mono_measure _ (UnforcedLeray.B0581.cellVol_le_cellMeasure c (by linarith))
        _ = ENNReal.ofReal ‖F 1‖ := by
              rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (F 1)), ← Lp.norm_def]
    have h0top : eLpNorm (fun z => ‖F 0 z‖) 2 (Cyl.cellμ c) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0
    have h1top : eLpNorm (fun z => ‖F 1 z‖) 2 (Cyl.cellμ c) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    have hineq := hmajor.trans hsum
    have htop := ENNReal.add_ne_top.mpr ⟨h0top, h1top⟩
    have hreal := ENNReal.toReal_mono htop hineq
    rw [ENNReal.toReal_add h0top h1top] at hreal
    have h0real := ENNReal.toReal_mono ENNReal.ofReal_ne_top h0
    have h1real := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h0real
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h1real
    linarith
  have hnormN : (eLpNorm T 2 (UnforcedLeray.B0284.cellMeasure c)).toReal =
      ‖xFluxPeriodicTensorInput hc hm F‖ := by
    calc
      _ = (eLpNorm (xFluxPeriodicTensorInput hc hm F : Plane → Plane × Plane) 2
          (UnforcedLeray.B0284.cellMeasure c)).toReal := by
            congr 1
            exact eLpNorm_congr_ae
              (memLp_xFluxPeriodicTensor_normalized hc hm F).coeFn_toLp.symm
      _ = ‖xFluxPeriodicTensorInput hc hm F‖ := (Lp.norm_def _).symm
  have hsqCell := UnforcedLeray.HeatCylinder.eLpNorm_sq_cellMeasure_eq_cyl hc hTmeas hTper
  have hsqReal := congrArg ENNReal.toReal hsqCell
  have hsq : ‖xFluxPeriodicTensorInput hc hm F‖ ^ 2 =
      c⁻¹ * (eLpNorm T 2 (Cyl.cellμ c)).toReal ^ 2 := by
    have hsqReal' : (eLpNorm T 2 (UnforcedLeray.B0284.cellMeasure c)).toReal ^ 2 =
        c⁻¹ * (eLpNorm T 2 (Cyl.cellμ c)).toReal ^ 2 := by
      rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (le_of_lt hc)] at hsqReal
      exact hsqReal
    rw [← hnormN]
    exact hsqReal'
  have hnonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
  have hsqBound : ‖xFluxPeriodicTensorInput hc hm F‖ ^ 2 ≤
      (Real.sqrt (c⁻¹) * (‖F 0‖ + ‖F 1‖)) ^ 2 := by
    rw [hsq]
    calc
      c⁻¹ * (eLpNorm T 2 (Cyl.cellμ c)).toReal ^ 2 ≤
          c⁻¹ * (‖F 0‖ + ‖F 1‖) ^ 2 := by
            have hcentersq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hcenter
            exact mul_le_mul_of_nonneg_left hcentersq hnonneg
      _ = (Real.sqrt (c⁻¹) * (‖F 0‖ + ‖F 1‖)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hnonneg]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsqBound

theorem norm_xFluxPeriodicTensorInput_le_pi {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F : Fin 2 → X c m) :
    ‖xFluxPeriodicTensorInput hc hm F‖ ≤ 2 * Real.sqrt (c⁻¹) * ‖F‖ := by
  have h0 : ‖F 0‖ ≤ ‖F‖ := by
    simp only [Pi.norm_def]
    have hsup : ‖F 0‖₊ ≤ Finset.univ.sup (fun i : Fin 2 => ‖F i‖₊) :=
      Finset.le_sup (f := fun i : Fin 2 => ‖F i‖₊) (Finset.mem_univ (0 : Fin 2))
    exact_mod_cast hsup
  have h1 : ‖F 1‖ ≤ ‖F‖ := by
    simp only [Pi.norm_def]
    have hsup : ‖F 1‖₊ ≤ Finset.univ.sup (fun i : Fin 2 => ‖F i‖₊) :=
      Finset.le_sup (f := fun i : Fin 2 => ‖F i‖₊) (Finset.mem_univ (1 : Fin 2))
    exact_mod_cast hsup
  have hsqrt : 0 ≤ Real.sqrt (c⁻¹) := Real.sqrt_nonneg _
  calc
    ‖xFluxPeriodicTensorInput hc hm F‖ ≤ Real.sqrt (c⁻¹) * (‖F 0‖ + ‖F 1‖) :=
      norm_xFluxPeriodicTensorInput_le hc hm F
    _ ≤ Real.sqrt (c⁻¹) * (‖F‖ + ‖F‖) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 h1) hsqrt
    _ = 2 * Real.sqrt (c⁻¹) * ‖F‖ := by ring

/-- Continuous normalized-cell input realization on the actual weighted flux product. -/
noncomputable def xFluxPeriodicTensorInputCLM {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) :
    (Fin 2 → X c m) →L[ℝ] Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (xFluxPeriodicTensorInputLinear hc hm).mkContinuous
    (2 * Real.sqrt (c⁻¹)) (norm_xFluxPeriodicTensorInput_le_pi hc hm)

theorem xFluxPeriodicTensor_add_centered_ae {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F G : Fin 2 → X c m) :
    xFluxPeriodicTensor hc (F + G) =ᵐ[Cyl.cellμ c]
      (fun z => xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z) := by
  have hFG := xFluxPeriodicTensor_ae_eq_raw hc (F + G)
  have hF := xFluxPeriodicTensor_ae_eq_raw hc F
  have hG := xFluxPeriodicTensor_ae_eq_raw hc G
  have hraw := xFluxRawTensor_add_ae F G
  filter_upwards [hFG, hF, hG, hraw] with z hfg hf hg hsum
  rw [hfg, hf, hg, hsum]

theorem xFluxPeriodicTensor_add_ae_volume {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (F G : Fin 2 → X c m) :
    xFluxPeriodicTensor hc (F + G) =ᵐ[volume]
      (fun z => xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z) := by
  have hf : UnforcedLeray.B0284.IsQPeriodic c (xFluxPeriodicTensor hc (F + G)) := by
    intro z
    exact periodic_xFluxPeriodicTensor hc (F + G) z
  have hg : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z) := by
    intro z
    change xFluxPeriodicTensor hc F (z.1 + c, z.2) +
      xFluxPeriodicTensor hc G (z.1 + c, z.2) = _
    rw [(periodic_xFluxPeriodicTensor hc F) z, (periodic_xFluxPeriodicTensor hc G) z]
  have hcenter := UnforcedLeray.HeatCylinder.ae_eq_of_ae_centered_periodic hc hf hg
    (xFluxPeriodicTensor_add_centered_ae hc hm F G)
  have hper : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => xFluxPeriodicTensor hc (F + G) z =
        xFluxPeriodicTensor hc F z + xFluxPeriodicTensor hc G z) := by
    intro z
    change (xFluxPeriodicTensor hc (F + G) (z.1 + c, z.2) =
      xFluxPeriodicTensor hc F (z.1 + c, z.2) + xFluxPeriodicTensor hc G (z.1 + c, z.2)) = _
    rw [(periodic_xFluxPeriodicTensor hc (F + G)) z,
      (periodic_xFluxPeriodicTensor hc F) z, (periodic_xFluxPeriodicTensor hc G) z]
  exact UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper hcenter

theorem xFluxPeriodicTensor_smul_centered_ae {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (r : ℝ) (F : Fin 2 → X c m) :
    xFluxPeriodicTensor hc (r • F) =ᵐ[Cyl.cellμ c]
      (fun z => r • xFluxPeriodicTensor hc F z) := by
  have h0 : (r • F 0 : X c m) =ᵐ[Cyl.cellμ c] fun z => r • F 0 z := by
    have h := Lp.coeFn_smul r (F 0)
    have hleft : -(c / 2) = -c / 2 := by ring
    have hc0 : cellMeasure c 0 = Cyl.cellμ c := by
      simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
        B0579.cell, Cyl.cellμ, Cyl.cell, hleft]
    have h0c : (r • F 0 : X c m) =ᵐ[cellMeasure c 0] fun z => r • F 0 z := by
      filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le h] with z hz
      exact hz
    simpa only [hc0] using h0c
  have h1 : (r • F 1 : X c m) =ᵐ[Cyl.cellμ c] fun z => r • F 1 z := by
    have h := Lp.coeFn_smul r (F 1)
    have hleft : -(c / 2) = -c / 2 := by ring
    have hc0 : cellMeasure c 0 = Cyl.cellμ c := by
      simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol,
        B0579.cell, Cyl.cellμ, Cyl.cell, hleft]
    have h1c : (r • F 1 : X c m) =ᵐ[cellMeasure c 0] fun z => r • F 1 z := by
      filter_upwards [(cellMeasure_ac_cellMeasure c 0 m).ae_le h] with z hz
      exact hz
    simpa only [hc0] using h1c
  have hraw : xFluxRawTensor (r • F) =ᵐ[Cyl.cellμ c]
      fun z => r • xFluxRawTensor F z := by
    filter_upwards [h0, h1] with z hz0 hz1
    simp [xFluxRawTensor, scalarFluxTensor, hz0, hz1]
  filter_upwards [xFluxPeriodicTensor_ae_eq_raw hc (r • F),
    xFluxPeriodicTensor_ae_eq_raw hc F, hraw] with z hr hf hsum
  rw [hr, hf, hsum]

theorem xFluxPeriodicTensor_smul_ae_volume {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (r : ℝ) (F : Fin 2 → X c m) :
    xFluxPeriodicTensor hc (r • F) =ᵐ[volume]
      (fun z => r • xFluxPeriodicTensor hc F z) := by
  have hf : UnforcedLeray.B0284.IsQPeriodic c (xFluxPeriodicTensor hc (r • F)) := by
    intro z
    exact periodic_xFluxPeriodicTensor hc (r • F) z
  have hg : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => r • xFluxPeriodicTensor hc F z) := by
    intro z
    change r • xFluxPeriodicTensor hc F (z.1 + c, z.2) = _
    rw [(periodic_xFluxPeriodicTensor hc F) z]
  have hcenter := UnforcedLeray.HeatCylinder.ae_eq_of_ae_centered_periodic hc hf hg
    (xFluxPeriodicTensor_smul_centered_ae hc hm r F)
  have hper : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => xFluxPeriodicTensor hc (r • F) z = r • xFluxPeriodicTensor hc F z) := by
    intro z
    change (xFluxPeriodicTensor hc (r • F) (z.1 + c, z.2) =
      r • xFluxPeriodicTensor hc F (z.1 + c, z.2)) = _
    rw [(periodic_xFluxPeriodicTensor hc (r • F)) z,
      (periodic_xFluxPeriodicTensor hc F) z]
  exact UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper hcenter

theorem cellMeasure_ac_volume_weighted {c m : ℝ} : cellMeasure c m ≪ volume := by
  rw [cellMeasure]
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- The actual normalized-cell B0296 heat-divergence operator on arbitrary weighted flux
columns, with the sign corresponding to `-div F`. This is an actual linear map; its stronger
`X_m`-valued continuity estimate is retained separately with the explicit fixed-cell factor. -/
def xFluxNegativeHeatDivL2Linear {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) :
    (Fin 2 → X c m) →ₗ[ℝ] Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (-1 : ℝ) • ((UnforcedLeray.HeatCylinder.heatDivL2CLM hc hθ).toLinearMap.comp
    (xFluxPeriodicTensorInputLinear hc hm))

/-- Continuous signed heat-divergence response on the actual weighted flux product. -/
noncomputable def xFluxNegativeHeatDivL2CLM {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) :
    (Fin 2 → X c m) →L[ℝ] Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (-1 : ℝ) • ((UnforcedLeray.HeatCylinder.heatDivL2CLM hc hθ).comp
    (xFluxPeriodicTensorInputCLM hc hm))

theorem xFluxNegativeHeatDivL2CLM_apply_eq_linear {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivL2CLM hc hm hθ F = xFluxNegativeHeatDivL2Linear hc hm hθ F := rfl

/-- Explicit fixed-cell operator bound for the continuous signed B0296 heat response. -/
theorem norm_xFluxNegativeHeatDivL2CLM_apply_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (F : Fin 2 → X c m) :
    ‖xFluxNegativeHeatDivL2CLM hc hm hθ F‖ ≤
      UnforcedLeray.HeatCylinder.heatDivL2Coeff θ *
        (2 * Real.sqrt (c⁻¹) * ‖F‖) := by
  have hcoeff : 0 ≤ UnforcedLeray.HeatCylinder.heatDivL2Coeff θ := by
    unfold UnforcedLeray.HeatCylinder.heatDivL2Coeff
    positivity
  change ‖(-1 : ℝ) • (UnforcedLeray.HeatCylinder.heatDivL2CLM hc hθ
    (xFluxPeriodicTensorInputCLM hc hm F))‖ ≤ _
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul]
  calc
    ‖UnforcedLeray.HeatCylinder.heatDivL2CLM hc hθ
        (xFluxPeriodicTensorInputCLM hc hm F)‖ ≤
      UnforcedLeray.HeatCylinder.heatDivL2Coeff θ *
        ‖xFluxPeriodicTensorInputCLM hc hm F‖ :=
          UnforcedLeray.HeatCylinder.heatDivL2CLM_norm_le hc hθ _
    _ ≤ UnforcedLeray.HeatCylinder.heatDivL2Coeff θ *
        (2 * Real.sqrt (c⁻¹) * ‖F‖) := by
          apply mul_le_mul_of_nonneg_left _ hcoeff
          change ‖xFluxPeriodicTensorInput hc hm F‖ ≤ _
          exact norm_xFluxPeriodicTensorInput_le_pi hc hm F

/-- The operator above is represented by the literal sign-corrected Gaussian cylinder
heat-divergence on the chosen centered-cell periodization. -/
theorem xFluxNegativeHeatDivL2Linear_eq_actual {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivL2Linear hc hm hθ F =
      -((UnforcedLeray.HeatCylinder.periodicHeatDivMemLp hc hθ
        (xFluxPeriodicTensor hc F)
        (by
          intro z
          simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
            periodic_xFluxPeriodicTensor hc F z)
        (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable
        (memLp_xFluxPeriodicTensor_normalized hc hm F)).toLp
          (UnforcedLeray.B0296.heatDiv θ (xFluxPeriodicTensor hc F))) := by
  let T := xFluxPeriodicTensor hc F
  let hmem := memLp_xFluxPeriodicTensor_normalized hc hm F
  have hactual := UnforcedLeray.HeatCylinder.heatDivL2CLM_apply_to_periodic hc hθ
    (by
      intro z
      simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
        periodic_xFluxPeriodicTensor hc F z)
    (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable
    (memLp_xFluxPeriodicTensor_normalized hc hm F)
  change (-1 : ℝ) • (UnforcedLeray.HeatCylinder.heatDivL2CLM hc hθ
      (xFluxPeriodicTensorInput hc hm F)) = _
  have hin : xFluxPeriodicTensorInput hc hm F =
      hmem.toLp (xFluxPeriodicTensor hc F) := rfl
  rw [hin, hactual]
  simp

theorem xFluxNegativeHeatDivL2CLM_eq_actual {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivL2CLM hc hm hθ F =
      -((UnforcedLeray.HeatCylinder.periodicHeatDivMemLp hc hθ
        (xFluxPeriodicTensor hc F)
        (by
          intro z
          simpa [UnforcedLeray.B0284.IsQPeriodic, Cyl.IsPeriodic] using
            periodic_xFluxPeriodicTensor hc F z)
        (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable
        (memLp_xFluxPeriodicTensor_normalized hc hm F)).toLp
          (UnforcedLeray.B0296.heatDiv θ (xFluxPeriodicTensor hc F))) := by
  rw [xFluxNegativeHeatDivL2CLM_apply_eq_linear hc hm hθ F]
  exact xFluxNegativeHeatDivL2Linear_eq_actual hc hm hθ F


/-- The signed response to an arbitrary pair of `X_m` flux columns has zero circulation. -/
theorem xFlux_negativeHeatDiv_zero_circulation {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (F : Fin 2 → X c m) :
    ∫ z in Cyl.cell c, (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1 = 0 := by
  exact integral_negativeHeatDiv_scalarFlux_eq_zero_of_cell_L1 hc hθ
    (periodic_xColumnPeriodicRep hc (F 0)) (periodic_xColumnPeriodicRep hc (F 1))
    (stronglyMeasurable_xColumnPeriodicRep hc (F 0))
    (stronglyMeasurable_xColumnPeriodicRep hc (F 1))
    (integrable_xColumnPeriodicRep hc hm (F 0))
    (integrable_xColumnPeriodicRep hc hm (F 1))

/-- For `0<θ≤1`, the signed B0296 response to any two `X_m` flux columns belongs to `X_m`. -/
theorem memLp_xFlux_negativeHeatDiv_fst_X {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) :
    MemLp (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1) 2
      (cellMeasure c m) := by
  exact memLp_negativeHeatDiv_fst_X_of_radialInput hc hθ hθ1 (by linarith : 0 ≤ m)
    (periodic_xFluxPeriodicTensor hc F) (measurable_xFluxPeriodicTensor hc F)
    (memLp_xFluxPeriodicTensor_radial hc hm F)

/-- The actual signed Gaussian response in the weighted vorticity space. -/
def xFluxNegativeHeatDivXOutput {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) : X c m :=
  (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F).toLp
    (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1)

/-- The radial weighted tensor norm of two `X_m` columns is bounded by their separate norms. -/
theorem eLpNorm_xFluxPeriodicTensor_radial_toReal_le {c m : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (F : Fin 2 → X c m) :
    (eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
      2 (Cyl.cellμ c)).toReal ≤ ‖F 0‖ + ‖F 1‖ := by
  let f0 : Plane → ℝ := fun z => bracket z ^ m * xColumnPeriodicRep hc (F 0) z
  let f1 : Plane → ℝ := fun z => bracket z ^ m * xColumnPeriodicRep hc (F 1) z
  have hpoint : ∀ᵐ z ∂(Cyl.cellμ c),
      ‖bracket z ^ m • xFluxPeriodicTensor hc F z‖ ≤ ‖f0 z‖ + ‖f1 z‖ := by
    filter_upwards [xFluxPeriodicTensor_ae_eq_raw hc F,
      xColumnPeriodicRep_ae_eq hc (F 0), xColumnPeriodicRep_ae_eq hc (F 1)] with z hz h0 h1
    rw [hz]
    have hsplit : bracket z ^ m • xFluxRawTensor F z =
        ((bracket z ^ m * F 0 z, (0 : ℝ)), (0 : Plane)) +
          ((0 : Plane), (bracket z ^ m * F 1 z, (0 : ℝ))) := by
      ext <;> simp [xFluxRawTensor, scalarFluxTensor, smul_eq_mul]
    rw [hsplit]
    have hPlane0 (x : ℝ) : ‖((x, (0 : ℝ)) : Plane)‖ = ‖x‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs, norm_zero, max_eq_left (abs_nonneg _)]
    have hA : ‖((bracket z ^ m * F 0 z, (0 : ℝ)), (0 : Plane))‖ =
        ‖bracket z ^ m * F 0 z‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), hPlane0]
    have hB : ‖((0 : Plane), (bracket z ^ m * F 1 z, (0 : ℝ)))‖ =
        ‖bracket z ^ m * F 1 z‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), hPlane0]
    calc
      ‖((bracket z ^ m * F 0 z, (0 : ℝ)), (0 : Plane)) +
          ((0 : Plane), (bracket z ^ m * F 1 z, (0 : ℝ)))‖ ≤
        ‖((bracket z ^ m * F 0 z, (0 : ℝ)), (0 : Plane))‖ +
          ‖((0 : Plane), (bracket z ^ m * F 1 z, (0 : ℝ)))‖ := norm_add_le _ _
      _ = ‖bracket z ^ m * F 0 z‖ + ‖bracket z ^ m * F 1 z‖ := by rw [hA, hB]
      _ = ‖f0 z‖ + ‖f1 z‖ := by
        rw [← h0, ← h1]
  have hmajor : eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
      2 (Cyl.cellμ c) ≤ eLpNorm (fun z => ‖f0 z‖ + ‖f1 z‖) 2 (Cyl.cellμ c) :=
    eLpNorm_mono_ae_real hpoint
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have h0meas : AEStronglyMeasurable (fun z => ‖f0 z‖) (Cyl.cellμ c) := by
    have hrep := stronglyMeasurable_xColumnPeriodicRep hc (F 0)
    have hw : Continuous (fun z : Plane => bracket z ^ m) := continuous_bracket_rpow m
    exact (hw.aestronglyMeasurable.mul hrep.aestronglyMeasurable).norm
  have h1meas : AEStronglyMeasurable (fun z => ‖f1 z‖) (Cyl.cellμ c) := by
    have hrep := stronglyMeasurable_xColumnPeriodicRep hc (F 1)
    have hw : Continuous (fun z : Plane => bracket z ^ m) := continuous_bracket_rpow m
    exact (hw.aestronglyMeasurable.mul hrep.aestronglyMeasurable).norm
  have hsum : eLpNorm (fun z => ‖f0 z‖ + ‖f1 z‖) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => ‖f0 z‖) 2 (Cyl.cellμ c) +
        eLpNorm (fun z => ‖f1 z‖) 2 (Cyl.cellμ c) :=
    eLpNorm_add_le h0meas h1meas (by norm_num)
  have h0ae : f0 =ᵐ[Cyl.cellμ c]
      (fun z => bracket z ^ m * (F 0 : Plane → ℝ) z) := by
    filter_upwards [xColumnPeriodicRep_ae_eq hc (F 0)] with z hz
    simp [f0, hz]
  have h1ae : f1 =ᵐ[Cyl.cellμ c]
      (fun z => bracket z ^ m * (F 1 : Plane → ℝ) z) := by
    filter_upwards [xColumnPeriodicRep_ae_eq hc (F 1)] with z hz
    simp [f1, hz]
  have h0 : eLpNorm (fun z => ‖f0 z‖) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal ‖F 0‖ := by
    have h0normae : (fun z => ‖f0 z‖) =ᵐ[Cyl.cellμ c]
        (fun z => ‖bracket z ^ m * (F 0 : Plane → ℝ) z‖) := by
      filter_upwards [h0ae] with z hz
      rw [hz]
    rw [eLpNorm_congr_ae h0normae, hleft]
    calc
      eLpNorm (fun z => ‖bracket z ^ m * (F 0 : Plane → ℝ) z‖) 2
          (volume.restrict (B0579.cell c)) =
        eLpNorm (fun z => bracket z ^ m * (F 0 : Plane → ℝ) z) 2
          (volume.restrict (B0579.cell c)) := by rw [eLpNorm_norm]
      _ = eLpNorm (F 0 : Plane → ℝ) 2 (cellMeasure c m) := by
        simpa only [bracket_rpow] using
          (B0579.eLpNorm_cellMeasure c m (F 0 : Plane → ℝ)).symm
      _ = ENNReal.ofReal ‖F 0‖ := by
        rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (F 0)), ← Lp.norm_def]
      _ ≤ ENNReal.ofReal ‖F 0‖ := le_rfl
  have h1 : eLpNorm (fun z => ‖f1 z‖) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal ‖F 1‖ := by
    have h1normae : (fun z => ‖f1 z‖) =ᵐ[Cyl.cellμ c]
        (fun z => ‖bracket z ^ m * (F 1 : Plane → ℝ) z‖) := by
      filter_upwards [h1ae] with z hz
      rw [hz]
    rw [eLpNorm_congr_ae h1normae, hleft]
    calc
      eLpNorm (fun z => ‖bracket z ^ m * (F 1 : Plane → ℝ) z‖) 2
          (volume.restrict (B0579.cell c)) =
        eLpNorm (fun z => bracket z ^ m * (F 1 : Plane → ℝ) z) 2
          (volume.restrict (B0579.cell c)) := by rw [eLpNorm_norm]
      _ = eLpNorm (F 1 : Plane → ℝ) 2 (cellMeasure c m) := by
        simpa only [bracket_rpow] using
          (B0579.eLpNorm_cellMeasure c m (F 1 : Plane → ℝ)).symm
      _ = ENNReal.ofReal ‖F 1‖ := by
        rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (F 1)), ← Lp.norm_def]
      _ ≤ ENNReal.ofReal ‖F 1‖ := le_rfl
  have h0top : eLpNorm (fun z => ‖f0 z‖) 2 (Cyl.cellμ c) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0
  have h1top : eLpNorm (fun z => ‖f1 z‖) 2 (Cyl.cellμ c) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have htop := ENNReal.add_ne_top.mpr ⟨h0top, h1top⟩
  have hreal := ENNReal.toReal_mono htop (hmajor.trans hsum)
  rw [ENNReal.toReal_add h0top h1top] at hreal
  have h0real := ENNReal.toReal_mono ENNReal.ofReal_ne_top h0
  have h1real := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h0real
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h1real
  exact hreal.trans (add_le_add h0real h1real)

theorem xFluxNegativeHeatDivXOutput_add {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F G : Fin 2 → X c m) :
    xFluxNegativeHeatDivXOutput hc hm hθ hθ1 (F + G) =
      xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F +
        xFluxNegativeHeatDivXOutput hc hm hθ hθ1 G := by
  let TFG := xFluxPeriodicTensor hc (F + G)
  let TF := xFluxPeriodicTensor hc F
  let TG := xFluxPeriodicTensor hc G
  let Tsum := fun z : Plane => TF z + TG z
  have hFGrep : TFG =ᵐ[volume] Tsum := xFluxPeriodicTensor_add_ae_volume hc hm F G
  have hperFG : UnforcedLeray.B0284.IsQPeriodic c TFG := by
    intro z
    exact periodic_xFluxPeriodicTensor hc (F + G) z
  have hperF : UnforcedLeray.B0284.IsQPeriodic c TF := by
    intro z
    exact periodic_xFluxPeriodicTensor hc F z
  have hperG : UnforcedLeray.B0284.IsQPeriodic c TG := by
    intro z
    exact periodic_xFluxPeriodicTensor hc G z
  have hperSum : UnforcedLeray.B0284.IsQPeriodic c Tsum := by
    intro z
    change TF (z.1 + c, z.2) + TG (z.1 + c, z.2) = _
    rw [hperF z, hperG z]
  have hmeasFG : AEStronglyMeasurable TFG volume :=
    (measurable_xFluxPeriodicTensor hc (F + G)).aestronglyMeasurable
  have hmeasF : AEStronglyMeasurable TF volume :=
    (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable TG volume :=
    (measurable_xFluxPeriodicTensor hc G).aestronglyMeasurable
  have hmeasSum : AEStronglyMeasurable Tsum volume := hmeasF.add hmeasG
  have hmemFG := memLp_xFluxPeriodicTensor_normalized hc hm (F + G)
  have hmemF := memLp_xFluxPeriodicTensor_normalized hc hm F
  have hmemG := memLp_xFluxPeriodicTensor_normalized hc hm G
  have hmemSum : MemLp Tsum 2 (UnforcedLeray.B0284.cellMeasure c) := hmemF.add hmemG
  have hcongr := UnforcedLeray.HeatCylinder.heatDiv_congr_ae hc hθ
    hperFG hperSum hmeasFG hmeasSum hmemFG hmemSum hFGrep
  have hadd := UnforcedLeray.HeatCylinder.heatDiv_add_ae hc hθ
    hperF hperG hmeasF hmeasG hmemF hmemG
  have hcell : negativeHeatDiv θ TFG =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      (fun z => negativeHeatDiv θ TF z + negativeHeatDiv θ TG z) := by
    filter_upwards [hcongr.trans hadd] with z hz
    simpa [negativeHeatDiv, add_comm] using congrArg (fun x : Plane => -x) hz
  have hperOut : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => negativeHeatDiv θ TFG z =
        negativeHeatDiv θ TF z + negativeHeatDiv θ TG z) := by
    intro z
    change (negativeHeatDiv θ TFG (z.1 + c, z.2) =
      negativeHeatDiv θ TF (z.1 + c, z.2) + negativeHeatDiv θ TG (z.1 + c, z.2)) = _
    simp [negativeHeatDiv, UnforcedLeray.B0296.heatDiv_periodic hperFG z,
      UnforcedLeray.B0296.heatDiv_periodic hperF z,
      UnforcedLeray.B0296.heatDiv_periodic hperG z]
  have hglobal := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperOut hcell
  have hAC : cellMeasure c m ≪ volume := @cellMeasure_ac_volume_weighted c m
  have hweighted := hAC.ae_le hglobal
  apply Lp.ext
  filter_upwards [
    (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 (F + G)).coeFn_toLp,
    (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F).coeFn_toLp,
    (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 G).coeFn_toLp,
    hweighted,
    Lp.coeFn_add (xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F)
      (xFluxNegativeHeatDivXOutput hc hm hθ hθ1 G)] with z hfg hf hg hresp haddout
  calc
    xFluxNegativeHeatDivXOutput hc hm hθ hθ1 (F + G) z =
        (negativeHeatDiv θ TFG z).1 := hfg
    _ = (negativeHeatDiv θ TF z + negativeHeatDiv θ TG z).1 := by
      simpa using congrArg Prod.fst hresp
    _ = xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F z +
        xFluxNegativeHeatDivXOutput hc hm hθ hθ1 G z := by
      dsimp [TF, TG]
      dsimp [xFluxNegativeHeatDivXOutput]
      rw [← hf, ← hg]
    _ = (xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F +
        xFluxNegativeHeatDivXOutput hc hm hθ hθ1 G) z := haddout.symm

theorem xFluxNegativeHeatDivXOutput_smul {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (r : ℝ) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivXOutput hc hm hθ hθ1 (r • F) =
      r • xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F := by
  let Tr := xFluxPeriodicTensor hc (r • F)
  let TF := xFluxPeriodicTensor hc F
  let Tsmul := fun z : Plane => r • TF z
  have hFrep : Tr =ᵐ[volume] Tsmul := xFluxPeriodicTensor_smul_ae_volume hc hm r F
  have hperR : UnforcedLeray.B0284.IsQPeriodic c Tr := by
    intro z
    exact periodic_xFluxPeriodicTensor hc (r • F) z
  have hperF : UnforcedLeray.B0284.IsQPeriodic c TF := by
    intro z
    exact periodic_xFluxPeriodicTensor hc F z
  have hperSmul : UnforcedLeray.B0284.IsQPeriodic c Tsmul := by
    intro z
    change r • TF (z.1 + c, z.2) = _
    rw [hperF z]
  have hmeasR : AEStronglyMeasurable Tr volume :=
    (measurable_xFluxPeriodicTensor hc (r • F)).aestronglyMeasurable
  have hmeasF : AEStronglyMeasurable TF volume :=
    (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable
  have hmeasSmul : AEStronglyMeasurable Tsmul volume := hmeasF.const_smul r
  have hmemR := memLp_xFluxPeriodicTensor_normalized hc hm (r • F)
  have hmemF := memLp_xFluxPeriodicTensor_normalized hc hm F
  have hmemSmul : MemLp Tsmul 2 (UnforcedLeray.B0284.cellMeasure c) := hmemF.const_smul r
  have hcongr := UnforcedLeray.HeatCylinder.heatDiv_congr_ae hc hθ
    hperR hperSmul hmeasR hmeasSmul hmemR hmemSmul hFrep
  have hsmul := UnforcedLeray.HeatCylinder.heatDiv_smul_ae hc hθ
    (r := r) hperF hmeasF hmemF
  have hcell : negativeHeatDiv θ Tr =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      (fun z => r • negativeHeatDiv θ TF z) := by
    filter_upwards [hcongr.trans hsmul] with z hz
    simpa [negativeHeatDiv, smul_neg] using congrArg (fun x : Plane => -x) hz
  have hperOut : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => negativeHeatDiv θ Tr z = r • negativeHeatDiv θ TF z) := by
    intro z
    change (negativeHeatDiv θ Tr (z.1 + c, z.2) =
      r • negativeHeatDiv θ TF (z.1 + c, z.2)) = _
    simp [negativeHeatDiv, UnforcedLeray.B0296.heatDiv_periodic hperR z,
      UnforcedLeray.B0296.heatDiv_periodic hperF z]
  have hglobal := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperOut hcell
  have hAC : cellMeasure c m ≪ volume := @cellMeasure_ac_volume_weighted c m
  have hweighted := hAC.ae_le hglobal
  apply Lp.ext
  filter_upwards [
    (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 (r • F)).coeFn_toLp,
    (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F).coeFn_toLp,
    hweighted,
    Lp.coeFn_smul r (xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F)] with z hr hf hresp hsmulout
  calc
    xFluxNegativeHeatDivXOutput hc hm hθ hθ1 (r • F) z =
        (negativeHeatDiv θ Tr z).1 := hr
    _ = (r • negativeHeatDiv θ TF z).1 := by
      simpa using congrArg Prod.fst hresp
    _ = r • xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F z := by
      dsimp [TF]
      dsimp [xFluxNegativeHeatDivXOutput]
      rw [← hf]
    _ = (r • xFluxNegativeHeatDivXOutput hc hm hθ hθ1 F) z := hsmulout.symm

/-- The sign-corrected Gaussian response is a real linear map from arbitrary weighted flux
columns into the actual weighted vorticity space. -/
def xFluxNegativeHeatDivXLinear {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (Fin 2 → X c m) →ₗ[ℝ] X c m where
  toFun := xFluxNegativeHeatDivXOutput hc hm hθ hθ1
  map_add' := xFluxNegativeHeatDivXOutput_add hc hm hθ hθ1
  map_smul' := xFluxNegativeHeatDivXOutput_smul hc hm hθ hθ1

/-- Fixed-cylinder operator bound for the actual signed Gaussian response. The polynomial radial
factor is explicit and this estimate is only for fixed `c`; it is not the uniform passive
transport growth estimate used later in the return argument. -/
theorem norm_xFluxNegativeHeatDivXLinear_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) :
    ‖xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F‖ ≤
      (1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ z : Plane, gradKernelAxialMomentDensity 1 m z) *
        (‖F 0‖ + ‖F 1‖) := by
  let A : ENNReal := ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
    ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
      ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)
  let out : X c m := xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F
  let g : Plane → ℝ := fun z => bracket z ^ m * (negativeHeatDiv θ
    (xFluxPeriodicTensor hc F) z).1
  have hsq := eLpNorm_negativeHeatDiv_fst_sq_le_radialInput hc hθ hθ1
    (by linarith : 0 ≤ m) (periodic_xFluxPeriodicTensor hc F)
    (measurable_xFluxPeriodicTensor hc F)
  have hrad := eLpNorm_xFluxPeriodicTensor_radial_toReal_le hc hm F
  have hradMem := memLp_xFluxPeriodicTensor_radial hc hm F
  have hradTop : eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
      2 (Cyl.cellμ c) ≠ ⊤ := hradMem.eLpNorm_ne_top
  have hradE : eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
      2 (Cyl.cellμ c) ≤ ENNReal.ofReal (‖F 0‖ + ‖F 1‖) := by
    rw [← ENNReal.ofReal_toReal hradTop]
    exact ENNReal.ofReal_le_ofReal hrad
  have hApos : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hradReal : (eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
      2 (Cyl.cellμ c)).toReal ≤ ‖F 0‖ + ‖F 1‖ := hrad
  have htargetTop : A * eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
      2 (Cyl.cellμ c) ≠ ⊤ := by
    have hA_top : A ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top hA_top hradTop
  have hsq' := hsq
  rw [← mul_pow] at hsq'
  have hroot := (ENNReal.pow_le_pow_left_iff (by norm_num : 2 ≠ 0)).1 hsq'
  have hreal := ENNReal.toReal_mono htargetTop hroot
  have houtRep : (out : Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)]
      (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1) := by
    have hrep := (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F).coeFn_toLp
    exact (ac_cellMeasure c m).ae_le hrep
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have houtRepCell : (out : Plane → ℝ) =ᵐ[Cyl.cellμ c]
      (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1) := by
    simpa only [hleft] using houtRep
  have hnorm : ‖out‖ = (eLpNorm g 2 (Cyl.cellμ c)).toReal := by
    rw [B0579.norm_X]
    congr 1
    rw [← hleft]
    apply eLpNorm_congr_ae
    filter_upwards [houtRepCell] with z hz
    simp [g, hz]
  change ‖out‖ ≤ _
  rw [hnorm]
  have hreal' : (eLpNorm g 2 (Cyl.cellμ c)).toReal ≤
      A.toReal * (eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
        2 (Cyl.cellμ c)).toReal := by
    simpa only [ENNReal.toReal_mul] using hreal
  have hA : A.toReal = (1 + c ^ 2 / 4) ^ (m / 2) *
      (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ z : Plane, gradKernelAxialMomentDensity 1 m z) := by
    have hmoment : 0 ≤ ∫ z : Plane, gradKernelAxialMomentDensity 1 m z := by
      apply integral_nonneg_of_ae
      filter_upwards with z
      unfold gradKernelAxialMomentDensity
      positivity
    have hweight : 0 ≤ (1 + c ^ 2 / 4) ^ (m / 2) := by positivity
    have hθpow : 0 < θ ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hθ _
    have h2pow : 0 ≤ (2 : ℝ) ^ (m / 2) :=
      Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (m / 2)
    have hkernel : 0 ≤ 2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ z : Plane, gradKernelAxialMomentDensity 1 m z :=
      mul_nonneg (mul_nonneg h2pow hθpow.le) hmoment
    rw [show A = ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ z : Plane, gradKernelAxialMomentDensity 1 m z) from rfl]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hweight,
      ENNReal.toReal_ofReal hkernel]
  rw [hA] at hreal'
  exact hreal'.trans (mul_le_mul_of_nonneg_left hradReal
    (by rw [← hA]; exact hApos))

/-- The actual fixed-cylinder signed heat response is a continuous linear map from arbitrary
two-column `X_m` fluxes to `X_m`. -/
noncomputable def xFluxNegativeHeatDivXCLM {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (Fin 2 → X c m) →L[ℝ] X c m := by
  let C : ℝ := (1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
      ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)
  let L := xFluxNegativeHeatDivXLinear hc hm hθ hθ1
  have hmoment : 0 ≤ ∫ z : Plane, gradKernelAxialMomentDensity 1 m z := by
    apply integral_nonneg_of_ae
    filter_upwards with z
    unfold gradKernelAxialMomentDensity
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcomp (F : Fin 2 → X c m) : ‖L F‖ ≤ 2 * C * ‖F‖ := by
    have hbound := norm_xFluxNegativeHeatDivXLinear_le hc hm hθ hθ1 F
    have h0 : ‖F 0‖ ≤ ‖F‖ := norm_le_pi_norm F 0
    have h1 : ‖F 1‖ ≤ ‖F‖ := norm_le_pi_norm F 1
    change ‖xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F‖ ≤ _
    calc
      ‖xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F‖ ≤
          C * (‖F 0‖ + ‖F 1‖) := by
        simpa [C, mul_assoc, mul_left_comm, mul_comm] using hbound
      _ ≤ C * (‖F‖ + ‖F‖) := by
        exact mul_le_mul_of_nonneg_left (add_le_add h0 h1) hC
      _ = 2 * C * ‖F‖ := by ring
  exact L.mkContinuous (2 * C) hcomp

theorem xFluxNegativeHeatDivXCLM_apply_eq_actual {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivXCLM hc hm hθ hθ1 F =
      (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F).toLp
        (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1) := by
  rfl

/-- The constructed output of the signed heat-divergence map lies in the physical
zero-circulation subspace, with circulation defined by the actual B0610 cell integral. -/
theorem xFluxNegativeHeatDivXLinear_mem_zeroCirculation {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F ∈
      zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) := by
  rw [mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m)]
  have hrep : (xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F : Plane → ℝ) =ᵐ[
      volume.restrict (B0579.cell c)]
      (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1) := by
    exact (ac_cellMeasure c m).ae_le
      (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F).coeFn_toLp
  have hzero := xFlux_negativeHeatDiv_zero_circulation hc hm hθ F
  have hcell_eq : Cyl.cell c = B0579.cell c := by
    simp only [Cyl.cell, B0579.cell]
    congr 1
    ring
  have hint := integral_congr_ae hrep
  rw [hcell_eq] at hzero
  rw [hint]
  exact hzero

theorem xFluxNegativeHeatDivXCLM_mem_zeroCirculation {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) :
    xFluxNegativeHeatDivXCLM hc hm hθ hθ1 F ∈
      zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) := by
  change xFluxNegativeHeatDivXLinear hc hm hθ hθ1 F ∈ _
  exact xFluxNegativeHeatDivXLinear_mem_zeroCirculation hc hm hθ hθ1 F

/-- The radial Gaussian-moment bound for the signed response to arbitrary `X_m` flux columns. -/
theorem eLpNorm_xFlux_negativeHeatDiv_fst_sq_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (F : Fin 2 → X c m) :
    (eLpNorm (fun z => bracket z ^ m * (negativeHeatDiv θ (xFluxPeriodicTensor hc F) z).1)
      2 (Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)) ^ 2 *
      (eLpNorm (fun z => bracket z ^ m • xFluxPeriodicTensor hc F z)
        2 (Cyl.cellμ c)) ^ 2 := by
  exact eLpNorm_negativeHeatDiv_fst_sq_le_radialInput hc hθ hθ1 (by linarith : 0 ≤ m)
    (periodic_xFluxPeriodicTensor hc F) (measurable_xFluxPeriodicTensor hc F)

#print axioms xColumnPeriodicRep_ae_eq
#print axioms xFluxPeriodicTensorInputLinear
#print axioms norm_xFluxPeriodicTensorInput_le
#print axioms norm_xFluxPeriodicTensorInput_le_pi
#print axioms xFluxPeriodicTensorInputCLM
#print axioms xFluxNegativeHeatDivL2Linear
#print axioms xFluxNegativeHeatDivL2CLM
#print axioms norm_xFluxNegativeHeatDivL2CLM_apply_le
#print axioms xFluxNegativeHeatDivL2CLM_apply_eq_linear
#print axioms xFluxNegativeHeatDivL2CLM_eq_actual
#print axioms xFluxNegativeHeatDivL2Linear_eq_actual
#print axioms memLp_xFluxPeriodicTensor_radial
#print axioms xFlux_negativeHeatDiv_zero_circulation
#print axioms memLp_xFlux_negativeHeatDiv_fst_X
#print axioms eLpNorm_xFlux_negativeHeatDiv_fst_sq_le
#print axioms eLpNorm_xFluxPeriodicTensor_radial_toReal_le
#print axioms norm_xFluxNegativeHeatDivXLinear_le
#print axioms xFluxNegativeHeatDivXCLM
#print axioms xFluxNegativeHeatDivXCLM_apply_eq_actual
#print axioms xFluxNegativeHeatDivXCLM_mem_zeroCirculation

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
