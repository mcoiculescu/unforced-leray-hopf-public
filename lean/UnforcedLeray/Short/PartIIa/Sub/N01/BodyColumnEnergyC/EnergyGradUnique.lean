import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.CellWeakUnique

/-!
# `PartII-a:N01/9/1/3/3/1`: `energyGradUnique`

Source `the November 2 reference manuscript` lines 3426-3430 (energy class).
Two energy fields whose velocities agree a.e. for `ageμ c (-3/2)` have gradients agreeing a.e.
for `ageμ c (-1/2)`.

Route. (1) Fubini on the product `ageμ c a = (s^a ds|_{s>0}) ⊗ avgμ c` turns the a.e. equality of
velocities into: for Lebesgue-a.e. `s > 0`, the slices agree a.e. on the cell.  (2) At such an `s`,
for each component `i j`, both `b(s,·) i` and `b'(s,·) i` (equal a.e. on the cell) have the weak
cell derivative `G(s,·) i j` resp. `G'(s,·) i j`, so `IIIa.cellWeakUnique` gives
`G(s,·) i j = G'(s,·) i j` a.e. on the cell.  (3) Fubini back to `ageμ c (-1/2)`; the two age
densities have the same Lebesgue null sets (positive density on `s > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Axi (ageμ measurable_ofReal_rpow)

namespace UnforcedLeray.Short.PartIIa.N01

/-- Cell-level a.e. equality: the `avgμ` null sets are those of `volume.restrict (B0579.cell c)`. -/
private theorem avg_ae_iff_cell {c : ℝ} (hc : 0 < c) {p : ℝ × ℝ → Prop} :
    (∀ᵐ x ∂(UnforcedLeray.Cyl.avgμ c), p x) ↔
      ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), p x := by
  have hcell : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [hcell]
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'

/-- Age density `s ↦ s^a` is positive on `(0, ∞)`, so it has full support there. -/
private theorem ae_density_ne_zero (a : ℝ) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (s ^ a) ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs a)).ne'

theorem energyGradUnique : UnforcedLeray.Short.PartIIa.N01.EnergyGradUnique := by
  intro c hc b b' G G' hE hE' hbb
  -- Step 1: Fubini on `ageμ c (-3/2)`: for Lebesgue-a.e. `s > 0`, `b(s,·) = b'(s,·)` a.e. on the cell.
  have hE1 : ∀ᵐ z ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))).prod (UnforcedLeray.Cyl.avgμ c),
        b z = b' z := hbb
  have hE2 := Measure.ae_ae_of_ae_prod (p := fun z => b z = b' z) hE1
  have hac1 : (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) ≪
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))) :=
    withDensity_absolutelyContinuous' (measurable_ofReal_rpow _).aemeasurable
      (ae_density_ne_zero _)
  have hLeb : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(UnforcedLeray.Cyl.avgμ c), b (s, x) = b' (s, x) :=
    (Measure.ae_le_iff_absolutelyContinuous.2 hac1) hE2
  have hslice : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), b (s, x) = b' (s, x) :=
    hLeb.mono fun s hs => (avg_ae_iff_cell hc).1 hs
  -- Step 2: for a.e. `s > 0`, the gradients agree a.e. on the cell.
  have hfin : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), G (s, x) = G' (s, x) := by
    filter_upwards [ae_restrict_of_ae hE.weakGradAE, ae_restrict_of_ae hE'.weakGradAE,
      hslice, ae_restrict_mem measurableSet_Ioi] with s hw hw' hsl hs
    have hs0 : (0 : ℝ) < s := hs
    have hcomp : ∀ i j, ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
        G (s, x) i j = G' (s, x) i j := by
      intro i j
      have hφ : (fun x => b (s, x) i) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
          (fun x => b' (s, x) i) := by
        filter_upwards [hsl] with x hx
        show b (s, x) i = b' (s, x) i
        rw [hx]
      have hw'φ : UnforcedLeray.Short.IIIa.HasWeakCellDerivC c j (fun x => b (s, x) i)
          (fun x => G' (s, x) i j) :=
        UnforcedLeray.Short.IIIa.HasWeakCellDerivC.congr_ae hφ
          (Filter.EventuallyEq.refl _ _) (hw' hs0 i j)
      exact UnforcedLeray.Short.IIIa.cellWeakUnique c j (fun x => b (s, x) i)
        (fun x => G (s, x) i j) (fun x => G' (s, x) i j) hc (hw hs0 i j) hw'φ
    have hall : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), ∀ i j,
        G (s, x) i j = G' (s, x) i j :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hcomp i j
    filter_upwards [hall] with x hx
    funext i
    funext j
    exact hx i j
  -- Step 3: Fubini back to `ageμ c (-1/2)`, using the density of `ageμ c (-1/2)` in `s`.
  have hGm : Measurable G :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hE.gradMeasurable i j
  have hG'm : Measurable G' :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hE'.gradMeasurable i j
  have hmeas : MeasurableSet {z : ℝ × (ℝ × ℝ) | G z = G' z} :=
    measurableSet_eq_fun hGm hG'm
  have hac2 : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) ≪
      (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) :=
    withDensity_absolutelyContinuous _ _
  have hinner : ∀ᵐ s ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))),
        ∀ᵐ x ∂(UnforcedLeray.Cyl.avgμ c), G (s, x) = G' (s, x) := by
    have h : ∀ᵐ s ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))), ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
        G (s, x) = G' (s, x) := (Measure.ae_le_iff_absolutelyContinuous.2 hac2) hfin
    exact h.mono fun s hs => (avg_ae_iff_cell hc).2 hs
  show ∀ᵐ z ∂(ageμ c (-1 / 2)), G z = G' z
  unfold ageμ
  exact (Measure.ae_prod_iff_ae_ae hmeas).2 hinner

end UnforcedLeray.Short.PartIIa.N01
