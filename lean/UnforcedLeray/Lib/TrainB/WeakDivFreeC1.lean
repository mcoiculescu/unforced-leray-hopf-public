import UnforcedLeray.Lib.TrainB.InitialDatumSolenoidal

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

private theorem periodic_fderiv_apply_c1 {c : ℝ} {u : Plane → ℝ}
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

private theorem integrableOn_test_smul_continuous {c : ℝ} {u φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (hu : Continuous u) :
    IntegrableOn (fun z => φ z • u z) (Cyl.cell c) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  rw [Sob.cyl_cell_eq]
  exact Sob.integrableOn_cylCell (hφ.smooth.continuous.smul hu) (R := R)
    (fun z hz => by rw [hR z hz, zero_smul])

private theorem periodic_component_c1 {c : ℝ} {u : Plane → Vec2}
    (hper : IsPeriodic c u) (i : Fin 2) : IsPeriodic c (fun z => u z i) := by
  intro z
  have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
  rw [← hz]
  simpa only [hz] using congrArg (fun v : Vec2 => v i) (hper z)

/-- A C¹ periodic, square-integrable field with pointwise zero divergence is weakly solenoidal
on the centered cylinder. This regularity is enough for Gaussian heat outputs, whose axial tails
prevent `IsCylSmooth` while their first derivatives are continuous. -/
theorem mem_divFree_of_C1_divergence_zero {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : ContDiff ℝ 1 u) (hper : IsPeriodic c u)
    (hdiv : ∀ z, Cyl.divergence u z = 0) (hmem : MemLp u 2 (Cyl.cellμ c)) :
    (hmem.toLp u : Cyl.L2v c) ∈ Cyl.divFree c := by
  rw [Cyl.mem_divFree]
  intro φ hφ
  rw [real_inner_comm]
  change ⟪hmem.toLp u, (Cyl.memLp_gradT hφ).toLp (Cyl.gradT φ)⟫_ℝ = 0
  rw [Cyl.inner_toLp_eq hmem (Cyl.memLp_gradT hφ)]
  have h0clm : ContDiff ℝ 1 (fun z => u z 0) :=
    (EuclideanSpace.proj 0 : Vec2 →L[ℝ] ℝ).contDiff.comp hu
  have h1clm : ContDiff ℝ 1 (fun z => u z 1) :=
    (EuclideanSpace.proj 1 : Vec2 →L[ℝ] ℝ).contDiff.comp hu
  have h0cont : Continuous (fun z => u z 0) := by
    change Continuous ((EuclideanSpace.proj 0 : Vec2 →L[ℝ] ℝ) ∘ u)
    exact (EuclideanSpace.proj 0 : Vec2 →L[ℝ] ℝ).continuous.comp hu.continuous
  have h1cont : Continuous (fun z => u z 1) := by
    change Continuous ((EuclideanSpace.proj 1 : Vec2 →L[ℝ] ℝ) ∘ u)
    exact (EuclideanSpace.proj 1 : Vec2 →L[ℝ] ℝ).continuous.comp hu.continuous
  have h0per := periodic_component_c1 hper 0
  have h1per := periodic_component_c1 hper 1
  have h0q : ContDiff ℝ 0 (Cyl.partialQ (fun z => u z 0)) :=
    Cyl.contDiff_partialQ (n := (0 : WithTop ℕ∞)) (by simpa using h0clm)
  have h1eta : ContDiff ℝ 0 (Cyl.partialEta (fun z => u z 1)) :=
    Cyl.contDiff_partialEta (n := (0 : WithTop ℕ∞)) (by simpa using h1clm)
  have h0qper : IsPeriodic c (Cyl.partialQ (fun z => u z 0)) := by
    have hp := periodic_fderiv_apply_c1 h0per ((1 : ℝ), (0 : ℝ))
    intro z
    rw [Cyl.partialQ_eq_fderiv (h0clm.differentiable (by simp))]
    rw [Cyl.partialQ_eq_fderiv (h0clm.differentiable (by simp))]
    exact hp z
  have h1etaper : IsPeriodic c (Cyl.partialEta (fun z => u z 1)) := by
    have hp := periodic_fderiv_apply_c1 h1per ((0 : ℝ), (1 : ℝ))
    intro z
    rw [Cyl.partialEta_eq_fderiv (h1clm.differentiable (by simp))]
    rw [Cyl.partialEta_eq_fderiv (h1clm.differentiable (by simp))]
    exact hp z
  have hq0 : IntegrableOn (fun z => Cyl.partialQ φ z * u z 0) (Cyl.cell c) := by
    simpa only [smul_eq_mul] using
      integrableOn_test_smul_continuous (isCylTest_partialQ hφ) h0cont
  have hq1 : IntegrableOn (fun z => φ z * Cyl.partialQ (fun w => u w 0) z)
      (Cyl.cell c) := by
    simpa only [smul_eq_mul] using
      integrableOn_test_smul_continuous hφ h0q.continuous
  have hqparts := Cyl.integral_cell_partialQ_mul hc hφ.differentiable
    (h0clm.differentiable (by simp)) hφ.isPeriodic h0per hq0 hq1
  have he0 : IntegrableOn (fun z => Cyl.partialEta φ z * u z 1) (Cyl.cell c) := by
    simpa only [smul_eq_mul] using
      integrableOn_test_smul_continuous (isCylTest_partialEta hφ) h1cont
  have he1 : IntegrableOn (fun z => φ z * Cyl.partialEta (fun w => u w 1) z)
      (Cyl.cell c) := by
    simpa only [smul_eq_mul] using
      integrableOn_test_smul_continuous hφ h1eta.continuous
  have heparts := Cyl.integral_cell_partialEta_mul hφ.differentiable
    (h1clm.differentiable (by simp))
    (hφ.integrableOn_mul h1clm.continuous) he0 he1
  have hsum :
      ∫ z in Cyl.cell c,
        (Cyl.partialQ φ z * u z 0 + Cyl.partialEta φ z * u z 1) = 0 := by
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
    have hdivInt :
        (∫ z in Cyl.cell c, φ z * Cyl.partialQ (fun w => u w 0) z) +
          ∫ z in Cyl.cell c, φ z * Cyl.partialEta (fun w => u w 1) z = 0 := by
      calc
        _ = ∫ z in Cyl.cell c, φ z *
            (Cyl.partialQ (fun w => u w 0) z + Cyl.partialEta (fun w => u w 1) z) := hsum_int
        _ = ∫ z in Cyl.cell c, φ z * Cyl.divergence u z := by
          congr 1
        _ = 0 := by simp [hdiv]
    linarith
  have hinner : ∀ z, ⟪u z, Cyl.gradT φ z⟫_ℝ =
      Cyl.partialQ φ z * u z 0 + Cyl.partialEta φ z * u z 1 := by
    intro z
    rw [Cyl.gradT, Cyl.inner_vec]
    ring
  simpa only [hinner] using hsum

#print axioms UnforcedLeray.TrainB.mem_divFree_of_C1_divergence_zero

end UnforcedLeray.TrainB
