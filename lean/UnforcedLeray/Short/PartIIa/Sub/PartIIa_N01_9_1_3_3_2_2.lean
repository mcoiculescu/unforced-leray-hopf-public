import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntPeriodic
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.PeriodicWeakDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.CellWeakUnique

/-!
# `PartII-a:N01/9/1/3/3/2/2` (decomposition): `WeakGradIsClassical` from `HeatIntRegular`

Source `the November 2 reference manuscript`
lines 3426-3430.  For every `s > 0` the slice of `u = smoothHeatInt` is `C¹` and `c`-periodic
(`HeatIntRegular`, `heatIntPeriodic`), so its classical gradient is a weak cell derivative
(`periodicWeakDeriv`); weak derivatives are a.e. unique on the cell (`cellWeakUnique`); Fubini as
in `energyGradUnique`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Axi (ageμ)

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)

private theorem avg_ae_iff_cell' {c : ℝ} (hc : 0 < c) {p : ℝ × ℝ → Prop} :
    (∀ᵐ x ∂(UnforcedLeray.Cyl.avgμ c), p x) ↔
      ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), p x := by
  have hcell : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [hcell]
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'

theorem weakGradIsClassical_of (hReg : HeatIntRegular) : WeakGradIsClassical := by
  intro c ν hc hν μ F hF Gr hE
  obtain ⟨hcont, hdiff, hfc⟩ := hReg c ν hc hν μ F hF
  have hper := heatIntPeriodic c ν hc hν μ F hF
  have hvel : velF c (smoothHeatInt c ν μ F) = fun x i => smoothHeatInt c ν μ F x i :=
    velF_of_periodic c _ hper
  set u := smoothHeatInt c ν μ F with hu
  -- classical weak derivative at every positive age
  have hclass : ∀ s : ℝ, 0 < s → ∀ i j, UnforcedLeray.Short.IIIa.HasWeakCellDerivC c j
      (fun x => u (s, x) i) (fun x => gradOf (velF c u) (s, x) i j) := by
    intro s hs i j
    have hC1 : ContDiff ℝ 1 (fun y : ℝ × ℝ => u (s, y) i) := by
      rw [contDiff_one_iff_fderiv]
      refine ⟨hdiff s hs i, ?_⟩
      have h0 : ContinuousOn ((fun p : Chart => fderiv ℝ (fun y : ℝ × ℝ => u (p.1, y) i) p.2) ∘
          fun y : ℝ × ℝ => ((s, y) : Chart)) univ :=
        (hfc i).comp (f := fun y : ℝ × ℝ => ((s, y) : Chart)) (by fun_prop : Continuous
          fun y : ℝ × ℝ => ((s, y) : Chart)).continuousOn (fun y _ => ⟨hs, mem_univ _⟩)
      exact continuousOn_univ.1 h0
    have hp : ∀ x : ℝ × ℝ, u (s, (x.1 + c, x.2)) i = u (s, x) i := fun x => by
      have := hper s x.1 x.2
      simp only [this]
    have := periodicWeakDeriv c hc _ hC1 hp j
    convert this using 2 with x
    simp [gradOf, hs, hvel]
  -- measurability of the classical gradient
  have hgm : Measurable (gradOf (velF c u)) := by
    have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      measurableSet_Ioi.prod MeasurableSet.univ
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    have hD : ContinuousOn (fun p : Chart => fderiv ℝ (fun y : ℝ × ℝ => u (p.1, y) i) p.2
        (UnforcedLeray.B0579.dir j)) (Ioi (0 : ℝ) ×ˢ univ) :=
      (ContinuousLinearMap.apply ℝ ℂ (UnforcedLeray.B0579.dir j)).continuous.comp_continuousOn
        (hfc i)
    have := hD.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const hS
    convert this using 1
    funext x
    by_cases hx : 0 < x.1
    · have : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hx, mem_univ _⟩
      simp [Set.piecewise, this, gradOf, hx, hvel]
    · have : x ∉ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := fun h => hx h.1
      simp [Set.piecewise, this, gradOf, hx]
  have hGm : Measurable Gr :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hE.gradMeasurable i j
  have hmeas : MeasurableSet {z : ℝ × (ℝ × ℝ) | Gr z = gradOf (velF c u) z} :=
    measurableSet_eq_fun hGm hgm
  have hac1 : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) ≪
      (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) :=
    withDensity_absolutelyContinuous _ _
  have hfin : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), Gr (s, x) = gradOf (velF c u) (s, x) := by
    filter_upwards [ae_restrict_of_ae hE.weakGradAE, ae_restrict_mem measurableSet_Ioi] with s hw hs
    have hs0 : (0 : ℝ) < s := hs
    have hcomp : ∀ i j, ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
        Gr (s, x) i j = gradOf (velF c u) (s, x) i j := by
      intro i j
      have hw' : UnforcedLeray.Short.IIIa.HasWeakCellDerivC c j (fun x => velF c u (s, x) i)
          (fun x => gradOf (velF c u) (s, x) i j) := by
        simpa [hvel] using hclass s hs0 i j
      exact UnforcedLeray.Short.IIIa.cellWeakUnique c j (fun x => velF c u (s, x) i)
        (fun x => Gr (s, x) i j) (fun x => gradOf (velF c u) (s, x) i j) hc (hw hs0 i j) hw'
    have hall : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), ∀ i j,
        Gr (s, x) i j = gradOf (velF c u) (s, x) i j :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hcomp i j
    filter_upwards [hall] with x hx
    funext i
    funext j
    exact hx i j
  have hinner : ∀ᵐ s ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))),
        ∀ᵐ x ∂(UnforcedLeray.Cyl.avgμ c), Gr (s, x) = gradOf (velF c u) (s, x) := by
    have h : ∀ᵐ s ∂(((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))), ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
        Gr (s, x) = gradOf (velF c u) (s, x) := hac1.ae_le hfin
    exact h.mono fun s hs => (avg_ae_iff_cell' hc).2 hs
  show ∀ᵐ z ∂(ageμ c (-1 / 2)), Gr z = gradOf (velF c u) z
  unfold ageμ
  exact (Measure.ae_prod_iff_ae_ae hmeas).2 hinner

end UnforcedLeray.Short.PartIIa.N01
