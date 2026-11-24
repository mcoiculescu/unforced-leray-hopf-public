import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Contraction

/-!
# Actual H³ contraction of ordinary cylinder heat on smooth inputs

The derivative-wise vector Gaussian Young inequality sums exactly to the unweighted centered
`W` graph norm. This is the period-independent estimate needed to extend actual heat from the
smooth core to arbitrary H³ classes by completion.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem heatVecH3_measure_eq_cell' (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- The exact graph norm square of the actual smooth ordinary heat output. -/
theorem heatVecH3_norm_sq {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ‖heatVecH3 hc hθ hT‖ ^ 2 =
      ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (heatVecH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 := by
  rw [heatVecH3, UnforcedLeray.Sob.W.norm_sq]
  simp_rw [UnforcedLeray.Sob.W.deriv_ofFields, Lp.norm_toLp,
    heatVecH3_measure_eq_cell' c]

/-- The exact graph norm square of the smooth input class. -/
private theorem ofCylSmooth_vec_norm_sq {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ‖UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc T hT‖ ^ 2 =
      ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 := by
  let x := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc T hT
  have hterm (α : UnforcedLeray.Sob.Idx 2 3) :
      ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x‖ =
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal := by
    calc
      _ = (eLpNorm (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x) 2
          (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))).toReal := by rw [Lp.norm_def]
      _ = (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal := by
        rw [eLpNorm_congr_ae
          (UnforcedLeray.Sob.W.deriv_ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) hc T hT α),
          heatVecH3_measure_eq_cell' c]
  change ‖x‖ ^ 2 = _
  rw [UnforcedLeray.Sob.W.norm_sq]
  apply Finset.sum_congr rfl
  intro α _
  rw [hterm α]

/-- The actual smooth-input ordinary heat operator is a contraction in the centered H³ graph
norm, uniformly in the cylinder period and positive heat age. -/
theorem norm_heatVecH3_le_ofCylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ‖heatVecH3 hc hθ hT‖ ≤
      ‖UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT‖ := by
  have hsq : ‖heatVecH3 hc hθ hT‖ ^ 2 ≤
      ‖UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT‖ ^ 2 := by
    rw [heatVecH3_norm_sq hc hθ hT, ofCylSmooth_vec_norm_sq hc hT]
    apply Finset.sum_le_sum
    intro α _
    have hout := memLp_heatVecH3Field hc hθ hT α
    have hin : MemLp (UnforcedLeray.Sob.iterD
        ((UnforcedLeray.Sob.cylinder c).word α) T) 2
        (UnforcedLeray.Cyl.cellμ c) := by
      have hD := hT.iterD ((UnforcedLeray.Sob.cylinder c).word α)
      have h := hD.memLp (1 : UnforcedLeray.Sob.Weight Plane) 2
      simpa [UnforcedLeray.Sob.wμ_one, UnforcedLeray.Sob.cylinder_μ,
        UnforcedLeray.Sob.cyl_cell_eq, UnforcedLeray.Cyl.cellμ] using h
    have hbound := eLpNorm_heatVecH3Field_le hc hθ hT α
    have hreal :
        (eLpNorm (heatVecH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal ≤
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal :=
      ENNReal.toReal_mono hin.eLpNorm_ne_top hbound
    exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hreal
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3_norm_sq
#print axioms UnforcedLeray.HeatCylinder.norm_heatVecH3_le_ofCylSmooth
