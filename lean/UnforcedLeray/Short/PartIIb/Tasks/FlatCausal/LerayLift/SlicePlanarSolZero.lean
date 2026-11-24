import UnforcedLeray.Short.PartIIb.Sub.T12_2_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePerCylTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePerFDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.CellPeriodizeMulIntegrable

/-!
# Part II-b, task `PartII-b:T12/2/5/8`: one age, planar identity from the cell identity

Source of record: `the November 2 reference manuscript` (SP 1923-1926). Proves the Prop
`SlicePlanarSolZero` of `Sub/T12_2_5.lean`: the cell identity for the periodized test
`Φ = pcellPer c φ (s, ·)` (`SlicePerCylTest`, `SlicePerFDeriv`) is unfolded, by
`Cyl.integral_cell_periodize_mul` and `CellPeriodizeMulIntegrable`, into the planar integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem slicePlanarSolZero_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SlicePlanarSolZero := by
  intro c g hc hgs hgper hZ φ s hφ hI1 hI2
  have hΦ : CylTest c (fun z : ℝ × ℝ => pcellPer c φ (s, z)) :=
    UnforcedLeray.Short.IIb.LerayLiftSub.slicePerCylTest_proof c φ hc hφ.smooth hφ.compact s
  obtain ⟨-, hZ0⟩ := hZ _ hΦ
  -- derivatives of the periodized test are periodizations of the derivatives of φ
  have hd1 : ∀ z : ℝ × ℝ, fderiv ℝ (fun z : ℝ × ℝ => pcellPer c φ (s, z)) z (1, 0) =
      pcellPer c (cpd 1 φ) (s, z) := by
    intro z
    rw [UnforcedLeray.Short.IIb.LerayLiftSub.slicePerFDeriv_proof c φ hc hφ.smooth hφ.compact s z (1, 0)]
    rfl
  have hd2 : ∀ z : ℝ × ℝ, fderiv ℝ (fun z : ℝ × ℝ => pcellPer c φ (s, z)) z (0, 1) =
      pcellPer c (cpd 2 φ) (s, z) := by
    intro z
    rw [UnforcedLeray.Short.IIb.LerayLiftSub.slicePerFDeriv_proof c φ hc hφ.smooth hφ.compact s z (0, 1)]
    rfl
  -- real periodizations are the ℂ-valued periodization of the complex cast
  have hP : ∀ (j : Fin 3) (z : ℝ × ℝ),
      ((pcellPer c (cpd j φ) (s, z) : ℝ) : ℂ) =
        UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd j φ (s, w) : ℝ) : ℂ)) z := by
    intro j z
    show ((∑' n : ℤ, cpd j φ (s, (z.1 - n * c, z.2)) : ℝ) : ℂ) =
      ∑' n : ℤ, ((cpd j φ (s, (z.1 - n * c, z.2)) : ℝ) : ℂ)
    exact Complex.ofReal_tsum _
  have hcont : ∀ j : Fin 3, Continuous (fun w : ℝ × ℝ => cpd j φ (s, w)) := by
    intro j
    unfold cpd
    exact ((hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  have hsm : ∀ j : Fin 3, StronglyMeasurable (fun w : ℝ × ℝ => ((cpd j φ (s, w) : ℝ) : ℂ)) :=
    fun j => (Complex.continuous_ofReal.comp (hcont j)).stronglyMeasurable
  have hgi : ∀ i : Fin 2, StronglyMeasurable (fun z : ℝ × ℝ => g z i) := fun i =>
    (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hgs
  have hgp : ∀ i : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => g z i) := by
    intro i z
    show g (z.1 + c, z.2) i = g z i
    rw [hgper z]
  -- continuity of the periodized derivatives, hence their strong measurability
  have hPc1 : Continuous (fun z : ℝ × ℝ => pcellPer c (cpd 1 φ) (s, z)) :=
    ((hΦ.smooth.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := ((1 : ℝ), (0 : ℝ))))).congr (fun z => hd1 z)
  have hPc2 : Continuous (fun z : ℝ × ℝ => pcellPer c (cpd 2 φ) (s, z)) :=
    ((hΦ.smooth.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := ((0 : ℝ), (1 : ℝ))))).congr (fun z => hd2 z)
  have hPs1 : StronglyMeasurable (UnforcedLeray.Cyl.periodize c
      (fun w : ℝ × ℝ => ((cpd 1 φ (s, w) : ℝ) : ℂ))) := by
    have : UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 1 φ (s, w) : ℝ) : ℂ)) =
        fun z => ((pcellPer c (cpd 1 φ) (s, z) : ℝ) : ℂ) :=
      funext fun z => (hP 1 z).symm
    rw [this]
    exact (Complex.continuous_ofReal.comp hPc1).stronglyMeasurable
  have hPs2 : StronglyMeasurable (UnforcedLeray.Cyl.periodize c
      (fun w : ℝ × ℝ => ((cpd 2 φ (s, w) : ℝ) : ℂ))) := by
    have : UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 2 φ (s, w) : ℝ) : ℂ)) =
        fun z => ((pcellPer c (cpd 2 φ) (s, z) : ℝ) : ℂ) :=
      funext fun z => (hP 2 z).symm
    rw [this]
    exact (Complex.continuous_ofReal.comp hPc2).stronglyMeasurable
  -- the unfolding of each planar pairing
  have hfg1 : Integrable (fun z : ℝ × ℝ => ((cpd 1 φ (s, z) : ℝ) : ℂ) * g z 0) :=
    hI1.congr (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hfg2 : Integrable (fun z : ℝ × ℝ => ((cpd 2 φ (s, z) : ℝ) : ℂ) * g z 1) :=
    hI2.congr (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hA : ∫ z : ℝ × ℝ, g z 0 * ((cpd 1 φ (s, z) : ℝ) : ℂ) =
      ∫ z in UnforcedLeray.Cyl.cell c,
        UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 1 φ (s, w) : ℝ) : ℂ)) z * g z 0 := by
    rw [UnforcedLeray.Cyl.integral_cell_periodize_mul hc (hsm 1) (hgi 0) (hgp 0) hfg1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hB : ∫ z : ℝ × ℝ, g z 1 * ((cpd 2 φ (s, z) : ℝ) : ℂ) =
      ∫ z in UnforcedLeray.Cyl.cell c,
        UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 2 φ (s, w) : ℝ) : ℂ)) z * g z 1 := by
    rw [UnforcedLeray.Cyl.integral_cell_periodize_mul hc (hsm 2) (hgi 1) (hgp 1) hfg2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hcI1 : IntegrableOn (fun z : ℝ × ℝ =>
      UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 1 φ (s, w) : ℝ) : ℂ)) z * g z 0)
      (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Short.IIb.LerayLiftSub.cellPeriodizeMulIntegrable_proof c _ _ hc (hsm 1)
      (hgi 0) hPs1 (hgp 0) hfg1
  have hcI2 : IntegrableOn (fun z : ℝ × ℝ =>
      UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 2 φ (s, w) : ℝ) : ℂ)) z * g z 1)
      (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Short.IIb.LerayLiftSub.cellPeriodizeMulIntegrable_proof c _ _ hc (hsm 2)
      (hgi 1) hPs2 (hgp 1) hfg2
  -- the cell identity for Φ
  simp only [hd1, hd2, hP] at hZ0
  have hcellZ : ∫ z in UnforcedLeray.Cyl.cell c,
      (g z 0 * UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 1 φ (s, w) : ℝ) : ℂ)) z +
        g z 1 * UnforcedLeray.Cyl.periodize c (fun w : ℝ × ℝ => ((cpd 2 φ (s, w) : ℝ) : ℂ)) z) = 0 := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ at hZ0
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le)] at hZ0
    rcases smul_eq_zero.1 hZ0 with h | h
    · exact absurd h (inv_ne_zero hc.ne')
    · exact h
  rw [integral_add hI1 hI2, hA, hB, ← integral_add hcI1 hcI2]
  rw [← hcellZ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

end UnforcedLeray.Short.IIb.LerayLiftSub
