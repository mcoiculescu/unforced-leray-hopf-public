import UnforcedLeray.Lib.HeatCylinder.PeriodicLift
import UnforcedLeray.Units.B0284.Contraction
import UnforcedLeray.Units.B0296.Conv

/-!
# The zero-order Gaussian heat family on normalized cylinder `L²`

This file descends the actual `B0284.heat` Gaussian convolution to the normalized B0284 cell
quotient. The chosen representative is periodic and measurable; the contraction estimate comes
from the concrete kernel proof in B0284. Nonpositive ages follow the actual definition, which is
the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

/-- Select a globally measurable periodic representative of a normalized-cell Plane-valued
`L²` class. -/
theorem exists_measurable_periodic_plane_rep {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    ∃ f : Plane → Plane, Measurable f ∧ IsQPeriodic c f ∧
      f =ᵐ[cellMeasure c] (x : Plane → Plane) := by
  let u : ℝ → Lp Plane 2 (cellMeasure c) := fun _ => x
  have hu : StronglyMeasurable u := stronglyMeasurable_const
  have hfact : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI := hfact
  obtain ⟨F, hF, hrep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep
      (u := u) (μ := cellMeasure c) hu
  let f : Plane → Plane := perLift hc (fun z => F (0, z))
  refine ⟨f, measurable_perLift hc (hF.measurable.comp
    (measurable_const.prodMk measurable_id)), perLift_periodic hc _, ?_⟩
  calc
    f =ᵐ[cellMeasure c] fun z => F (0, z) := perLift_ae_eq_cell hc _
    _ =ᵐ[cellMeasure c] (x : Plane → Plane) := by simpa [u] using hrep 0

/-- The measurable periodic representative selected for a cell `L²` class. -/
noncomputable def planeRep {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : Plane → Plane :=
  Classical.choose (exists_measurable_periodic_plane_rep hc x)

theorem planeRep_spec {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    Measurable (planeRep hc x) ∧ IsQPeriodic c (planeRep hc x) ∧
      planeRep hc x =ᵐ[cellMeasure c] (x : Plane → Plane) :=
  Classical.choose_spec (exists_measurable_periodic_plane_rep hc x)

/-- The selected representative retains the finite cell `L²` class. -/
theorem memLp_planeRep {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : MemLp (planeRep hc x) 2 (cellMeasure c) := by
  have hx := Lp.memLp x
  have hf := planeRep_spec hc x
  refine ⟨hf.1.aestronglyMeasurable.mono_ac (UnforcedLeray.B0284.cellMeasure_ac c), ?_⟩
  rw [eLpNorm_congr_ae hf.2.2]
  exact hx.2

/-- Actual `B0284.heat` applied to a periodic representative, represented as a normalized-cell
`L²` class. -/
noncomputable def heatL2 {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Lp Plane 2 (cellMeasure c) → Lp Plane 2 (cellMeasure c) := fun x =>
  let f := planeRep hc x
  let hf := planeRep_spec hc x
  let hmem := memLp_planeRep hc x
  let hheat : MemLp (UnforcedLeray.B0284.heat θ f) 2 (cellMeasure c) := by
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hf.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hf.2.1
      hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
  hheat.toLp (UnforcedLeray.B0284.heat θ f)

/-- The actual zero-order Gaussian heat family is contractive on normalized-cell `L²`, including
the identity convention for nonpositive ages. -/
theorem norm_heatL2_le {c θ : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) : ‖heatL2 hc θ x‖ ≤ ‖x‖ := by
  let f := planeRep hc x
  let hf := planeRep_spec hc x
  let hmem := memLp_planeRep hc x
  let hheat : MemLp (UnforcedLeray.B0284.heat θ f) 2 (cellMeasure c) := by
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hf.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hf.2.1
      hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
  change ‖hheat.toLp (UnforcedLeray.B0284.heat θ f)‖ ≤ ‖x‖
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top x)
  have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hf.2.1
    hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  calc
    eLpNorm (hheat.toLp (UnforcedLeray.B0284.heat θ f) : Plane → Plane) 2
        (cellMeasure c) ≤ eLpNorm f 2 (cellMeasure c) := by
      rw [eLpNorm_congr_ae hheat.coeFn_toLp]
      exact hcontract
    _ = eLpNorm (x : Plane → Plane) 2 (cellMeasure c) := eLpNorm_congr_ae hf.2.2
    _ = eLpNorm (x : Plane → Plane) 2 (cellMeasure c) := rfl

/-- At every nonpositive age the descended actual Gaussian family is exactly the identity. -/
theorem heatL2_eq_id_of_nonpos {c θ : ℝ} (hc : 0 < c) (hθ : θ ≤ 0)
    (x : Lp Plane 2 (cellMeasure c)) : heatL2 hc θ x = x := by
  let f := planeRep hc x
  let hf := planeRep_spec hc x
  let hmem := memLp_planeRep hc x
  let hheat : MemLp (UnforcedLeray.B0284.heat θ f) 2 (cellMeasure c) := by
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hf.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hf.2.1
      hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
  apply Lp.ext
  change (hheat.toLp (UnforcedLeray.B0284.heat θ f) : Plane → Plane) =ᵐ[cellMeasure c] (x : Plane → Plane)
  filter_upwards [hheat.coeFn_toLp, hf.2.2] with z hzheat hzrep
  calc
    (hheat.toLp (UnforcedLeray.B0284.heat θ f) : Plane → Plane) z =
        UnforcedLeray.B0284.heat θ f z := hzheat
    _ = f z := by rw [UnforcedLeray.B0284.heat_of_nonpos hθ]
    _ = (x : Plane → Plane) z := hzrep

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.norm_heatL2_le
#print axioms UnforcedLeray.HeatCylinder.heatL2_eq_id_of_nonpos
