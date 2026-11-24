import UnforcedLeray.Units.B0289.Periodize
import UnforcedLeray.Units.B0296.Conv
import UnforcedLeray.Lib.SobolevC.CylExtend
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Canonical periodic extension from one cylinder cell

The cylinder `L²` input is represented on one cell, while Gaussian convolution samples the whole
plane. This file starts the canonical bridge: wrap the first coordinate into `[0,c)`, so the
extension is periodic, agrees with the cell representative almost everywhere, and is independent
almost everywhere on the plane of the chosen representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284 (cell cellMeasure IsQPeriodic)

/-- Extend cell data periodically by reducing the first coordinate into `[0,c)`. -/
def perLift {c : ℝ} (hc : 0 < c) {E : Type*} (f : Plane → E) : Plane → E :=
  fun z => f (toIcoMod hc 0 z.1, z.2)

/-- The canonical extension is periodic in the cylinder coordinate. -/
theorem perLift_periodic {c : ℝ} (hc : 0 < c) {E : Type*} (f : Plane → E) :
    IsQPeriodic c (perLift hc f) := by
  intro z
  simp [perLift, toIcoMod_add_right]

/-- The extension is measurable whenever the chosen cell representative is measurable on the
whole plane. -/
theorem measurable_perLift {c : ℝ} (hc : 0 < c) {E : Type*} [MeasurableSpace E]
    {f : Plane → E} (hf : Measurable f) : Measurable (perLift hc f) := by
  exact hf.comp ((UnforcedLeray.Sob.measurable_toIcoMod hc 0).comp measurable_fst |>.prodMk
    measurable_snd)

/-- The periodic extension agrees with its representative almost everywhere on the defining cell
`(0,c] × ℝ`. The only discrepancy is on the null boundary `q=c`. -/
theorem perLift_ae_eq_cell {c : ℝ} (hc : 0 < c) {E : Type*} (f : Plane → E) :
    perLift hc f =ᵐ[cellMeasure c] f := by
  have hcell : ∀ᵐ z ∂cellMeasure c, z ∈ cell c := by
    rw [cellMeasure]
    exact Measure.ae_smul_measure (ae_restrict_mem (UnforcedLeray.B0284.measurableSet_cell c)) _
  have hzero : volume ({z : Plane | z.1 = c}) = 0 := by
    rw [show {z : Plane | z.1 = c} = ({c} : Set ℝ) ×ˢ (univ : Set ℝ) by
      ext z; simp]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hne : ∀ᵐ z ∂cellMeasure c, z.1 ≠ c := by
    rw [ae_iff]
    have hnull := (UnforcedLeray.B0284.cellMeasure_ac c) hzero
    simpa using hnull
  filter_upwards [hcell, hne] with z hzcell hzc
  change z.1 ∈ Ioc 0 c ∧ z.2 ∈ univ at hzcell
  have hq : z.1 ∈ Ico 0 c := ⟨le_of_lt hzcell.1.1, lt_of_le_of_ne hzcell.1.2 hzc⟩
  have hwrap : toIcoMod hc 0 z.1 = z.1 := by
    exact (toIcoMod_eq_self hc).mpr (by simpa using hq)
  simp [perLift, hwrap]

/-- Cell-a.e. equal data have the same canonical periodic extension almost everywhere on the
whole plane. This is the quotient-independence fact required before defining the heat operator on
cylinder `L²`. -/
theorem perLift_congr_ae {c : ℝ} (hc : 0 < c) {E : Type*} {f g : Plane → E}
    (hfg : f =ᵐ[cellMeasure c] g) : perLift hc f =ᵐ[volume] perLift hc g := by
  apply UnforcedLeray.B0289.ae_of_ae_cellMeasure hc
  · intro z
    change (perLift hc f (z.1 + c, z.2) = perLift hc g (z.1 + c, z.2)) =
      (perLift hc f z = perLift hc g z)
    rw [perLift_periodic hc f z, perLift_periodic hc g z]
  · filter_upwards [perLift_ae_eq_cell hc f, perLift_ae_eq_cell hc g, hfg] with z hf hg hfg
    exact hf.trans (hfg.trans hg.symm)

/-- Extend data on the centered train cell `[-c/2,c/2) × ℝ` periodically. This uses the
centered representative expected by `Cyl.H`; it is distinct from `perLift`, whose base cell is
B0284's normalized `(0,c] × ℝ`. -/
def centeredPerLift {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E] (f : Plane → E) : Plane → E :=
  UnforcedLeray.Sob.perExt hc f

/-- The centered periodic extension is periodic in the cylinder coordinate. -/
theorem centeredPerLift_periodic {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E] (f : Plane → E) :
    UnforcedLeray.Cyl.IsPeriodic c (centeredPerLift hc f) := by
  intro z
  change UnforcedLeray.Sob.perExt hc f (z.1 + c, z.2) = _
  rw [show (z.1 + c, z.2) = z + (c, 0) by ext <;> simp]
  exact UnforcedLeray.Sob.perExt_add hc f z

/-- The centered periodic extension agrees pointwise with its data on the centered cell. -/
theorem centeredPerLift_eq_on_cell {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E] (f : Plane → E)
    {z : Plane} (hz : z ∈ UnforcedLeray.Cyl.cell c) :
    centeredPerLift hc f z = f z := by
  have hzq : z.1 ∈ Ico (-(c / 2)) (c / 2) := by
    simpa only [show -c / 2 = -(c / 2) by ring] using hz.1
  exact UnforcedLeray.Sob.perExt_of_mem hc f ⟨hzq, trivial⟩

/-- A centered periodic extension is measurable if the chosen representative is measurable. -/
theorem measurable_centeredPerLift {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {f : Plane → E} (hf : Measurable f) : Measurable (centeredPerLift hc f) := by
  exact hf.comp ((UnforcedLeray.Sob.measurable_toIcoMod hc (-(c / 2))).comp measurable_fst
    |>.prodMk measurable_snd)

/-- Centered cell-a.e. equal data have centered periodic extensions equal almost everywhere on the
plane. The proof uses the centered cell as an actual fundamental domain. -/
theorem centeredPerLift_congr_ae {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E] {f g : Plane → E}
    (hfg : f =ᵐ[UnforcedLeray.Cyl.cellμ c] g) :
    centeredPerLift hc f =ᵐ[volume] centeredPerLift hc g := by
  let S : Set Plane := {z | centeredPerLift hc f z ≠ centeredPerLift hc g z}
  have hSper : UnforcedLeray.B0284.IsQPeriodic c (· ∈ S) := by
    intro z
    change (centeredPerLift hc f (z.1 + c, z.2) ≠ centeredPerLift hc g (z.1 + c, z.2)) = _
    simp [S, centeredPerLift_periodic hc f z, centeredPerLift_periodic hc g z]
  have hcenter : volume (S ∩ UnforcedLeray.Cyl.cell c) = 0 := by
    have hEq : ∀ᵐ z ∂UnforcedLeray.Cyl.cellμ c,
        centeredPerLift hc f z = centeredPerLift hc g z := by
      filter_upwards [hfg, ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hfg hz
      rw [centeredPerLift_eq_on_cell hc f hz, centeredPerLift_eq_on_cell hc g hz]
      exact hfg
    have hzero : volume.restrict (UnforcedLeray.Cyl.cell c) S = 0 := by
      have hz := ae_iff.mp hEq
      simpa [S, UnforcedLeray.Cyl.cellμ] using hz
    rw [Measure.restrict_apply' (UnforcedLeray.Cyl.measurableSet_cell c)] at hzero
    simpa [S, Set.inter_comm] using hzero
  have hnull := (UnforcedLeray.Cyl.isAddFundamentalDomain_cell hc).measure_zero_of_invariant
    S ?_ hcenter
  · exact ae_iff.mpr (by simpa [S] using hnull)
  · rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have e : (-(⟨m • ((c, 0) : Plane), hv⟩ : AddSubgroup.zmultiples ((c, 0) : Plane)) +ᵥ z :
        Plane) = (z.1 + ((-m : ℤ) : ℝ) * c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp <;> ring
    rw [e]
    exact iff_of_eq (UnforcedLeray.B0289.IsQPeriodic.add_int_mul hSper (-m) z)

/-- A strongly measurable path in cylinder tensor `L²` has a jointly strongly measurable,
globally periodic representative on time times the plane. Every time slice still represents its
original cell `L²` class. The construction uses `Infra.JointMeasurableRep` on the cell first, then
the canonical periodic lift. -/
theorem exists_stronglyMeasurable_periodic_tensor_rep {c : ℝ} (hc : 0 < c)
    {u : ℝ → Lp (Plane × Plane) 2 (cellMeasure c)}
    (hu : StronglyMeasurable u) :
    ∃ F : ℝ × Plane → Plane × Plane,
      StronglyMeasurable F ∧
      (∀ t, AEStronglyMeasurable (fun z => F (t, z)) volume) ∧
      (∀ t, IsQPeriodic c (fun z => F (t, z))) ∧
      ∀ t, (fun z => F (t, z)) =ᵐ[cellMeasure c] (u t : Plane → Plane × Plane) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨G, hG, hrep⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep
      (u := u) (μ := cellMeasure c) hu
  let wrap (z : Plane) : Plane := (toIcoMod hc 0 z.1, z.2)
  let F : ℝ × Plane → Plane × Plane := fun q => G (q.1, wrap q.2)
  have hwrap : Measurable wrap := by
    exact (UnforcedLeray.Sob.measurable_toIcoMod hc 0).comp measurable_fst |>.prodMk
      measurable_snd
  have hmap : Measurable (fun q : ℝ × Plane => (q.1, wrap q.2)) :=
    measurable_fst.prodMk (hwrap.comp measurable_snd)
  have hFmeas : Measurable F := by
    exact hG.measurable.comp hmap
  have hFsm : StronglyMeasurable F :=
    hFmeas.stronglyMeasurable
  refine ⟨F, hFsm, ?_, ?_, ?_⟩
  · intro t
    exact (hFmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · intro t z
    change G (t, wrap (z.1 + c, z.2)) = G (t, wrap z)
    have hwrap_periodic : wrap (z.1 + c, z.2) = wrap z := by
      simp [wrap, toIcoMod_add_right]
    rw [hwrap_periodic]
  · intro t
    have hslice : (fun z : Plane => G (t, z)) =ᵐ[cellMeasure c] (u t : Plane → Plane × Plane) :=
      hrep t
    calc
      (fun z : Plane => F (t, z)) =ᵐ[cellMeasure c] fun z => G (t, z) := by
        filter_upwards [perLift_ae_eq_cell hc (fun z => G (t, z))] with z hz
        simpa [F, wrap, perLift] using hz
      _ =ᵐ[cellMeasure c] (u t : Plane → Plane × Plane) := hslice

end UnforcedLeray.HeatCylinder
