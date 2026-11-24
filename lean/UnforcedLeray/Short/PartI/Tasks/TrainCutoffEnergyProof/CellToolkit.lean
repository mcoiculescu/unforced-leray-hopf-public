import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T05b/2/1`: toolkit `CellToolkit`

Source of record: `the November 2 reference manuscript`, lines 276-288 (cutoff
energy method). Proves the two toolkit leaves `CellIntegrableOfSupport` and `CellDerivZero` of
`Sub/T05b_2.lean`, which are used by the cutoff energy leaves.

* `CellIntegrableOfSupport`: a continuous function vanishing for `2R ≤ |η|` is integrable on the
  centred cell (it is supported in the compact box `[-c/2, c/2] × [-2R, 2R]`).
* `CellDerivZero`: for a `C¹`, `c`-periodic `G` vanishing for `2R ≤ |η|`, the cell integrals of
  `∂_q G` and `∂_η G` vanish (`Cyl.integral_cell_deriv_q_of_periodic`,
  `Cyl.integral_cell_deriv_eta`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open MeasureTheory Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cyl (Plane)

/-- A continuous function vanishing for `2R ≤ |η|` is integrable on the centred cell. -/
theorem cellIntegrable_aux (c R : ℝ) (g : Plane → ℝ) (hg : Continuous g)
    (hzero : ∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) :
    IntegrableOn g (Cyl.cell c) := by
  have hKc : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
    isCompact_Icc.prod isCompact_Icc
  have hgK : IntegrableOn g (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
    hg.continuousOn.integrableOn_compact hKc
  refine IntegrableOn.of_forall_sdiff_eq_zero hgK ?_ ?_
  · unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  · intro x hx
    apply hzero
    have hx1 : x ∈ Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := hx.1
    have hlohi : -c / 2 ≤ x.1 ∧ x.1 < c / 2 := Set.mem_Ico.1 (Set.mem_prod.1 hx1).1
    have hK : x ∉ Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) := hx.2
    have hη : ¬ (-(2 * R) ≤ x.2 ∧ x.2 ≤ 2 * R) := by
      intro h
      exact hK (Set.mk_mem_prod ⟨hlohi.1, hlohi.2.le⟩ ⟨h.1, h.2⟩)
    by_contra hcon
    rw [not_le, abs_lt] at hcon
    exact hη ⟨hcon.1.le, hcon.2.le⟩

/-- **`CellIntegrableOfSupport`** (proved). -/
theorem cellIntegrable_of_support : CellIntegrableOfSupport := by
  unfold CellIntegrableOfSupport
  intro c R _hc _hR g hg hzero
  exact cellIntegrable_aux c R g hg hzero

/-- **`CellDerivZero`** (proved). -/
theorem cellDerivZero_of_periodic : CellDerivZero := by
  unfold CellDerivZero
  intro c R hc hR G hG hper hzero
  have hd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hQc : Continuous (Cyl.partialQ G) := (Cyl.C1_partial_of_contDiff hG).1
  have hEc : Continuous (Cyl.partialEta G) := (Cyl.C1_partial_of_contDiff hG).2
  -- `∂_q G` vanishes for `2R ≤ |η|`: the slice `q ↦ G (q, η)` is identically zero there.
  have hQ0 : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialQ G z = 0 := by
    intro z hz
    have hfun : (fun q : ℝ => G (q, z.2)) = fun _ => (0 : ℝ) :=
      funext fun q => hzero (q, z.2) hz
    show deriv (fun q : ℝ => G (q, z.2)) z.1 = 0
    rw [hfun, deriv_const]
  -- `∂_η G` vanishes for `2R < |η|`: the slice `η' ↦ G (q, η')` is zero near `η`.
  have hE0 : ∀ z : Plane, 2 * R < |z.2| → Cyl.partialEta G z = 0 := by
    intro z hz
    have hopen : IsOpen {η : ℝ | 2 * R < |η|} := isOpen_lt continuous_const continuous_abs
    have hev : (fun η : ℝ => G (z.1, η)) =ᶠ[nhds z.2] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds (show z.2 ∈ {η : ℝ | 2 * R < |η|} from hz)] with η hη
      have hη' : 2 * R < |η| := hη
      exact hzero (z.1, η) hη'.le
    show deriv (fun η : ℝ => G (z.1, η)) z.2 = 0
    rw [hev.deriv_eq, deriv_const]
  have hGi : IntegrableOn G (Cyl.cell c) := cellIntegrable_aux c R G hG.continuous hzero
  have hQi : IntegrableOn (Cyl.partialQ G) (Cyl.cell c) :=
    cellIntegrable_aux c R (Cyl.partialQ G) hQc hQ0
  have hEi : IntegrableOn (Cyl.partialEta G) (Cyl.cell c) :=
    cellIntegrable_aux c (2 * R) (Cyl.partialEta G) hEc (fun z hz => hE0 z (by linarith))
  exact ⟨Cyl.integral_cell_deriv_q_of_periodic hc hper (fun q η => Cyl.hasDerivAt_sliceQ hd q η) hQi,
    Cyl.integral_cell_deriv_eta (fun q η => Cyl.hasDerivAt_sliceEta hd q η) hGi hEi⟩

/-- **Toolkit `CellToolkit`**: both cell leaves hold. -/
theorem cellToolkit : CellIntegrableOfSupport ∧ CellDerivZero :=
  ⟨cellIntegrable_of_support, cellDerivZero_of_periodic⟩

end UnforcedLeray.Short.PartI
