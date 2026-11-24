import UnforcedLeray.Lib.TrainB.InitialDatumH3Class
import UnforcedLeray.Lib.CylinderB.Leray
import UnforcedLeray.Lib.Cylinder.IBP

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

private theorem isCylSmooth_test_smul_periodic {c : ℝ} {u : Plane → ℝ}
    {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) (hu : ContDiff ℝ ∞ u)
    (hper : IsPeriodic c u) : Sob.IsCylSmooth c (fun z => φ z • u z) := by
  refine ⟨hφ.smooth.smul hu, fun z => ?_, ?_⟩
  · rw [hφ.periodic]
    have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    rw [hz, hper]
  · obtain ⟨R, hR⟩ := hφ.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩

private theorem periodic_fderiv_apply {c : ℝ} {u : Plane → ℝ}
    (hper : IsPeriodic c u) (v : Plane) :
    IsPeriodic c (fun z => fderiv ℝ u z v) := by
  intro z
  change fderiv ℝ u (z.1 + c, z.2) v = fderiv ℝ u z v
  have e : (fun y : Plane => u (y + (c, 0))) = u := by
    funext y
    have hy : y + (c, 0) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : Plane)
  rw [e] at hd
  have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
  rw [← hz, ← hd]

/-- A smooth periodic square-integrable field with pointwise zero divergence represents a vector
in the actual weak cylinder solenoidal subspace. The proof is periodic integration by parts on the
centered cell, using compact-axial support only for the test. -/
theorem mem_divFree_of_smooth_divergence_zero {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : ContDiff ℝ ∞ u) (hper : IsPeriodic c u)
    (hdiv : ∀ z, Cyl.divergence u z = 0) (hmem : MemLp u 2 (Cyl.cellμ c)) :
    (hmem.toLp u : Cyl.L2v c) ∈ Cyl.divFree c := by
  rw [Cyl.mem_divFree]
  intro φ hφ
  rw [real_inner_comm]
  change ⟪hmem.toLp u, (Cyl.memLp_gradT hφ).toLp (Cyl.gradT φ)⟫_ℝ = 0
  rw [Cyl.inner_toLp_eq hmem (Cyl.memLp_gradT hφ)]
  have h0clm : ContDiff ℝ ∞ (fun z => u z 0) :=
    (EuclideanSpace.proj 0 : Vec2 →L[ℝ] ℝ).contDiff.comp hu
  have h1clm : ContDiff ℝ ∞ (fun z => u z 1) :=
    (EuclideanSpace.proj 1 : Vec2 →L[ℝ] ℝ).contDiff.comp hu
  have h0per : IsPeriodic c (fun z => u z 0) := by
    intro z
    have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    rw [← hz]
    simpa only [hz] using congrArg (fun v : Vec2 => v 0) (hper z)
  have h1per : IsPeriodic c (fun z => u z 1) := by
    intro z
    have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    rw [← hz]
    simpa only [hz] using congrArg (fun v : Vec2 => v 1) (hper z)
  have h0q : ContDiff ℝ ∞ (Cyl.partialQ (fun z => u z 0)) := by
    have hfd : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => u z 0) z ((1 : ℝ), (0 : ℝ))) :=
      (ContDiff.fderiv_right (m := ∞) h0clm (by simp)).clm_apply contDiff_const
    have heq : Cyl.partialQ (fun z => u z 0) =
        fun z => fderiv ℝ (fun z => u z 0) z ((1 : ℝ), (0 : ℝ)) := by
      funext z
      exact Cyl.partialQ_eq_fderiv (h0clm.differentiable (by simp)) z
    rw [heq]
    exact hfd
  have h1eta : ContDiff ℝ ∞ (Cyl.partialEta (fun z => u z 1)) := by
    have hfd : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => u z 1) z ((0 : ℝ), (1 : ℝ))) :=
      (ContDiff.fderiv_right (m := ∞) h1clm (by simp)).clm_apply contDiff_const
    have heq : Cyl.partialEta (fun z => u z 1) =
        fun z => fderiv ℝ (fun z => u z 1) z ((0 : ℝ), (1 : ℝ)) := by
      funext z
      exact Cyl.partialEta_eq_fderiv (h1clm.differentiable (by simp)) z
    rw [heq]
    exact hfd
  have h0qper : IsPeriodic c (Cyl.partialQ (fun z => u z 0)) := by
    have hp := periodic_fderiv_apply h0per ((1 : ℝ), (0 : ℝ))
    intro z
    rw [Cyl.partialQ_eq_fderiv (h0clm.differentiable (by simp))]
    rw [Cyl.partialQ_eq_fderiv (h0clm.differentiable (by simp))]
    exact hp z
  have h1etaper : IsPeriodic c (Cyl.partialEta (fun z => u z 1)) := by
    have hp := periodic_fderiv_apply h1per ((0 : ℝ), (1 : ℝ))
    intro z
    rw [Cyl.partialEta_eq_fderiv (h1clm.differentiable (by simp))]
    rw [Cyl.partialEta_eq_fderiv (h1clm.differentiable (by simp))]
    exact hp z
  have hq0 : IntegrableOn (fun z => Cyl.partialQ φ z * u z 0) (Cyl.cell c) := by
    rw [Sob.cyl_cell_eq]
    simpa only [smul_eq_mul] using
      (isCylSmooth_test_smul_periodic (isCylTest_partialQ hφ) h0clm h0per).integrableOn
  have hq1 : IntegrableOn (fun z => φ z * Cyl.partialQ (fun w => u w 0) z)
      (Cyl.cell c) := by
    rw [Sob.cyl_cell_eq]
    simpa only [smul_eq_mul] using
      (isCylSmooth_test_smul_periodic hφ h0q h0qper).integrableOn
  have hqparts := Cyl.integral_cell_partialQ_mul hc hφ.differentiable
    (h0clm.differentiable (by simp))
    hφ.isPeriodic h0per hq0 hq1
  have he0 : IntegrableOn (fun z => Cyl.partialEta φ z * u z 1) (Cyl.cell c) := by
    rw [Sob.cyl_cell_eq]
    simpa only [smul_eq_mul] using
      (isCylSmooth_test_smul_periodic (isCylTest_partialEta hφ) h1clm h1per).integrableOn
  have he1 : IntegrableOn (fun z => φ z * Cyl.partialEta (fun w => u w 1) z)
      (Cyl.cell c) := by
    rw [Sob.cyl_cell_eq]
    simpa only [smul_eq_mul] using
      (isCylSmooth_test_smul_periodic hφ h1eta h1etaper).integrableOn
  have heparts := Cyl.integral_cell_partialEta_mul hφ.differentiable
    (h1clm.differentiable (by simp))
    (hφ.integrableOn_mul h1clm.continuous) he0 he1
  have hsum :
      ∫ z in Cyl.cell c, (Cyl.partialQ φ z * u z 0 + Cyl.partialEta φ z * u z 1) = 0 := by
    rw [integral_add hq0 he0, hqparts, heparts]
    have hdivfun : (fun z => Cyl.partialQ (fun w => u w 0) z +
        Cyl.partialEta (fun w => u w 1) z) = Cyl.divergence u := by rfl
    have hsum_int :
        (∫ z in Cyl.cell c, φ z * Cyl.partialQ (fun w => u w 0) z) +
          ∫ z in Cyl.cell c, φ z * Cyl.partialEta (fun w => u w 1) z =
            ∫ z in Cyl.cell c, φ z *
              (Cyl.partialQ (fun w => u w 0) z + Cyl.partialEta (fun w => u w 1) z) := by
      rw [← integral_add hq1 he1]
      congr 1
      funext z
      ring
    have hdivfun' : (fun z => φ z *
        (Cyl.partialQ (fun w => u w 0) z + Cyl.partialEta (fun w => u w 1) z)) =
        (fun z => φ z * Cyl.divergence u z) := by
      funext z
      exact congrArg (fun x => φ z * x) (congrFun hdivfun z)
    have hdivint :
        (∫ z in Cyl.cell c, φ z * Cyl.partialQ (fun w => u w 0) z) +
          ∫ z in Cyl.cell c, φ z * Cyl.partialEta (fun w => u w 1) z = 0 := by
      rw [hsum_int, hdivfun']
      simp [hdiv]
    linarith
  have hinner : ∀ z, ⟪u z, Cyl.gradT φ z⟫_ℝ =
      Cyl.partialQ φ z * u z 0 + Cyl.partialEta φ z * u z 1 := by
    intro z
    rw [Cyl.gradT, Cyl.inner_vec]
    ring
  simpa only [hinner] using hsum

/-- The actual Gaussian Train datum is fixed by the cylinder Leray projection in centered-cell
L². -/
theorem P0_datum_eq_datum {c : ℝ} (hc : 0 < c) :
    Cyl.P0 c ((memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c)) =
      (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) := by
  apply Cyl.P0_eq_self
  apply mem_divFree_of_smooth_divergence_zero hc (Train.datum_contDiff hc.ne')
    (Train.datum_periodic c) (Train.datum_div hc.ne')

#print axioms UnforcedLeray.TrainB.mem_divFree_of_smooth_divergence_zero
#print axioms UnforcedLeray.TrainB.P0_datum_eq_datum

end UnforcedLeray.TrainB
