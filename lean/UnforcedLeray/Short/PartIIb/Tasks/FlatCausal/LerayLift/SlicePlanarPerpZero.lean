import UnforcedLeray.Short.PartIIb.Sub.T12_2_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePerSolTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.CellPeriodizeMulIntegrable

/-!
# Part II-b, task `PartII-b:T12/2/6/3`: one age, planar orthogonality from cell orthogonality

Source of record: `the November 2 reference manuscript` (SP 1901-1903, 1923-1926).
Proves the Prop `SlicePlanarPerpZero` of `Sub/T12_2_6.lean`. The periodized planar test is a cell
solenoidal test (`slicePerSolTest_proof`), the cell integrand unfolds by `integral_cell_periodize_mul`,
and the cell identity for the periodized test gives zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem slicePlanarPerpZero_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SlicePlanarPerpZero := by
  intro c u w hc hu hw hup hwp hcell Ψ s hΨ hint
  have hΨc := slicePerSolTest_proof c Ψ hc hΨ s
  have hz : ∫ z : ℝ × ℝ, ∑ i : Fin 2, (u z i - w z i) *
      ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ)
        ∂(UnforcedLeray.Cyl.avgμ c) = 0 := (hcell _ hΨc).2
  have hΨi : ∀ i : Fin 2, Continuous (fun x : Coord => Ψ x i) :=
    fun i => (hΨ.smooth i).smooth.continuous
  have hfs : ∀ i : Fin 2, StronglyMeasurable (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) := by
    intro i
    have hcont : Continuous (fun z : ℝ × ℝ => Ψ (s, z) i) :=
      (hΨi i).comp (Continuous.prodMk continuous_const continuous_id)
    exact (Complex.continuous_ofReal.comp hcont).stronglyMeasurable
  have hgs : ∀ i : Fin 2, StronglyMeasurable (fun z : ℝ × ℝ => u z i - w z i) := by
    intro i
    have hu' : StronglyMeasurable (fun z : ℝ × ℝ => u z i) :=
      (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hu
    have hw' : StronglyMeasurable (fun z : ℝ × ℝ => w z i) :=
      (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw
    exact hu'.sub hw'
  have hgper : ∀ i : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => u z i - w z i) := by
    intro i z
    show u (z.1 + c, z.2) i - w (z.1 + c, z.2) i = u z i - w z i
    rw [hup z, hwp z]
  have hper_i : ∀ i : Fin 2, ∀ z : ℝ × ℝ,
      UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) z =
        ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) := by
    intro i z
    unfold UnforcedLeray.Cyl.periodize UnforcedLeray.Short.IIb.pcellPer
    rw [Complex.ofReal_tsum]
  have hPf : ∀ i : Fin 2,
      StronglyMeasurable (UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ))) := by
    intro i
    have heq : UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) =
        fun z => ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) :=
      funext (hper_i i)
    rw [heq]
    have hcont : Continuous (fun z : ℝ × ℝ => UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z)) :=
      (hΨc.comp i).smooth.continuous
    exact (Complex.continuous_ofReal.comp hcont).stronglyMeasurable
  have hfgI : ∀ i : Fin 2,
      Integrable (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ) * (u z i - w z i)) := fun i =>
    (hint i).congr (ae_of_all _ fun z => mul_comm _ _)
  have hcellI : ∀ i : Fin 2, IntegrableOn
      (fun z : ℝ × ℝ => UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) z *
        (u z i - w z i)) (UnforcedLeray.Cyl.cell c) := fun i =>
    UnforcedLeray.Short.IIb.LerayLiftSub.cellPeriodizeMulIntegrable_proof c _ _ hc (hfs i) (hgs i)
      (hPf i) (hgper i) (hfgI i)
  have hcellI' : ∀ i : Fin 2, IntegrableOn
      (fun z : ℝ × ℝ => (u z i - w z i) *
        ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ))
        (UnforcedLeray.Cyl.cell c) := by
    intro i
    exact Integrable.congr (hcellI i) (ae_of_all _ fun z => by dsimp only; rw [hper_i i z]; ring)
  have key : ∀ i : Fin 2,
      ∫ z in UnforcedLeray.Cyl.cell c, (u z i - w z i) *
          ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) =
        ∫ z : ℝ × ℝ, (u z i - w z i) * ((Ψ (s, z) i : ℝ) : ℂ) := by
    intro i
    have h1 : ∫ z in UnforcedLeray.Cyl.cell c,
        UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) z * (u z i - w z i) =
          ∫ z : ℝ × ℝ, ((Ψ (s, z) i : ℝ) : ℂ) * (u z i - w z i) :=
      UnforcedLeray.Cyl.integral_cell_periodize_mul hc (hfs i) (hgs i) (hgper i) (hfgI i)
    calc ∫ z in UnforcedLeray.Cyl.cell c, (u z i - w z i) *
            ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ)
        = ∫ z in UnforcedLeray.Cyl.cell c,
            UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) z *
              (u z i - w z i) :=
          integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [hper_i i z]; ring)
      _ = ∫ z : ℝ × ℝ, ((Ψ (s, z) i : ℝ) : ℂ) * (u z i - w z i) := h1
      _ = ∫ z : ℝ × ℝ, (u z i - w z i) * ((Ψ (s, z) i : ℝ) : ℂ) :=
          integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have hsplit : ∫ z : ℝ × ℝ, ∑ i : Fin 2, (u z i - w z i) * ((Ψ (s, z) i : ℝ) : ℂ) =
      ∑ i : Fin 2, ∫ z : ℝ × ℝ, (u z i - w z i) * ((Ψ (s, z) i : ℝ) : ℂ) :=
    integral_finsetSum _ (fun i _ => hint i)
  have hcsplit : ∫ z in UnforcedLeray.Cyl.cell c, ∑ i : Fin 2, (u z i - w z i) *
      ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) =
      ∑ i : Fin 2, ∫ z in UnforcedLeray.Cyl.cell c, (u z i - w z i) *
        ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) :=
    integral_finsetSum _ (fun i _ => hcellI' i)
  have hX : ∫ z in UnforcedLeray.Cyl.cell c, ∑ i : Fin 2, (u z i - w z i) *
      ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) = 0 := by
    have h0 := UnforcedLeray.Cyl.integral_avgμ hc.le (fun z : ℝ × ℝ => ∑ i : Fin 2,
      (u z i - w z i) * ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ))
    have h1 : c⁻¹ • ∫ z in UnforcedLeray.Cyl.cell c, ∑ i : Fin 2,
        (u z i - w z i) * ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) = 0 :=
      h0.symm.trans hz
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h (inv_ne_zero hc.ne')
    · exact h
  calc ∫ z : ℝ × ℝ, ∑ i : Fin 2, (u z i - w z i) * ((Ψ (s, z) i : ℝ) : ℂ)
      = ∑ i : Fin 2, ∫ z : ℝ × ℝ, (u z i - w z i) * ((Ψ (s, z) i : ℝ) : ℂ) := hsplit
    _ = ∑ i : Fin 2, ∫ z in UnforcedLeray.Cyl.cell c, (u z i - w z i) *
          ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) :=
        Finset.sum_congr rfl (fun i _ => (key i).symm)
    _ = ∫ z in UnforcedLeray.Cyl.cell c, ∑ i : Fin 2, (u z i - w z i) *
          ((UnforcedLeray.Short.IIb.pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) := hcsplit.symm
    _ = 0 := hX

end UnforcedLeray.Short.IIb.LerayLiftSub
