import UnforcedLeray.Lib.HeatCylinder.HeatVecIteratedDerivative
import UnforcedLeray.Lib.HeatCylinder.WeakOutput
import UnforcedLeray.Lib.HeatCylinder.CellBridge
import UnforcedLeray.Lib.CylinderB.Space

/-!
# Smooth ordinary Gaussian heat in the centered cylinder H³ graph

For smooth periodic compact-axial vector fields, the actual vector Gaussian convolution has all
ordered weak derivatives in the centered-cell H³ graph. The output itself has Gaussian tails and
is represented with `W.ofFields`, not as a compact-axial smooth field.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem heatVecH3_measure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- The classical derivative fields of actual vector Gaussian heat. -/
noncomputable def heatVecH3Field {c θ : ℝ} (T : Plane → Vec)
    (α : UnforcedLeray.Sob.Idx 2 3) (z : Plane) : Vec :=
  heatVecConvolution θ
    (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T) z

private theorem isQPeriodic_iterD_vec {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact (hT.iterD vs).periodic z

private theorem integrableOn_test_smul_continuous {c : ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : Plane → ℝ} (hφ : UnforcedLeray.Sob.IsCylTest c φ)
    {u : Plane → F} (hu : Continuous u) :
    Integrable (fun z => φ z • u z)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  have h := UnforcedLeray.Sob.integrableOn_cylCell (c := c)
    (hφ.smooth.continuous.smul hu) (R := R)
      (fun z hz => by
        change φ z • u z = 0
        rw [hR z hz, zero_smul])
  change Integrable (fun z => φ z • u z)
    (volume.restrict (UnforcedLeray.Cyl.cell c))
  rw [UnforcedLeray.Sob.cyl_cell_eq]
  exact h

/-- Smooth compact-axial periodic vector derivatives have finite normalized-cell L² norm. -/
theorem memLp_iterD_vec_cylSmooth_normalized {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    MemLp (UnforcedLeray.Sob.iterD vs T) 2 (UnforcedLeray.B0284.cellMeasure c) := by
  let hD := hT.iterD vs
  have hcenter : MemLp (UnforcedLeray.Sob.iterD vs T) 2 (UnforcedLeray.Cyl.cellμ c) := by
    have h := hD.memLp (1 : UnforcedLeray.Sob.Weight Plane) 2
    simpa [UnforcedLeray.Sob.wμ_one, UnforcedLeray.Sob.cylinder_μ,
      UnforcedLeray.Sob.cyl_cell_eq, UnforcedLeray.Cyl.cellμ] using h
  exact UnforcedLeray.HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    hD.smooth.continuous.measurable (isQPeriodic_iterD_vec hT vs) hcenter

/-- A matching actual heat derivative is L², by vector-kernel Young contraction on the normalized
cell and the exact periodic/centered transfer. -/
theorem memLp_heatVecH3Field {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    MemLp (heatVecH3Field (c := c) (θ := θ) T α) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [heatVecH3_measure_eq_cell]
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD vs T
  have hTα : UnforcedLeray.Sob.IsCylSmooth c Tα := hT.iterD vs
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := isQPeriodic_iterD_vec hT vs
  have hmeas : Measurable Tα := hTα.smooth.continuous.measurable
  have hmem : MemLp Tα 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_iterD_vec_cylSmooth_normalized hc hT vs
  have hcontract := eLpNorm_heatVecConvolution_le hc hθ hper
    hmeas.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  have hOutMeas : Measurable (heatVecConvolution θ Tα) := by
    exact (differentiable_heatVecConvolution_of_cylSmooth hc hθ hTα).continuous.measurable
  have hOutPer : UnforcedLeray.B0284.IsQPeriodic c (heatVecConvolution θ Tα) :=
    heatVecConvolution_periodic hc hθ hTα
  have hnormTop : eLpNorm (heatVecConvolution θ Tα) 2
      (UnforcedLeray.B0284.cellMeasure c) < ⊤ :=
    lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
  have hOutMem : MemLp (heatVecConvolution θ Tα) 2
      (UnforcedLeray.B0284.cellMeasure c) := ⟨hOutMeas.aestronglyMeasurable, hnormTop⟩
  exact UnforcedLeray.HeatCylinder.memLp_cyl_of_memLp_cellMeasure hc hOutMeas hOutPer hOutMem

/-- The actual vector heat output is differentiable for every smooth periodic compact-axial input.
-/
theorem differentiable_heatVecH3Output {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    Differentiable ℝ (heatVecConvolution θ T) :=
  differentiable_heatVecConvolution_of_cylSmooth hc hθ hT

/-- Every finite ordered derivative of actual vector heat satisfies the genuine cylinder weak
derivative identity. -/
theorem hasWeakDeriv_iterD_heatVecConvolution {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) vs
      (heatVecConvolution θ T)
      (UnforcedLeray.Sob.iterD vs (heatVecConvolution θ T)) := by
  induction vs with
  | nil =>
    refine UnforcedLeray.Sob.HasWeakDeriv.nil fun φ hφ => ?_
    have hφ' : UnforcedLeray.Sob.IsCylTest c φ := hφ
    have hcont := (differentiable_heatVecConvolution_of_cylSmooth hc hθ hT).continuous
    rw [UnforcedLeray.Sob.cylinder_μ]
    change Integrable (fun z => φ z • heatVecConvolution θ T z)
      (volume.restrict (UnforcedLeray.Sob.cylCell c))
    have hInt := integrableOn_test_smul_continuous hφ' hcont
    rw [UnforcedLeray.Sob.cyl_cell_eq] at hInt
    exact hInt
  | cons e vs ih =>
    have hcomm := iterD_heatVecConvolution_commute hc hθ hT vs
    have hweakOne := UnforcedLeray.HeatCylinder.hasWeakDeriv_cylinder_dir_of_continuous_fderiv
      hc (differentiable_heatVecConvolution_of_cylSmooth hc hθ (hT.iterD vs))
      (differentiable_heatVecConvolution_of_cylSmooth hc hθ (hT.iterD vs)).continuous
      (heatVecConvolution_periodic hc hθ (hT.iterD vs))
      (fun e' => by
        have heq : (fun z => fderiv ℝ
            (heatVecConvolution θ (UnforcedLeray.Sob.iterD vs T)) z e') =
            heatVecConvolution θ (fun x => fderiv ℝ
              (UnforcedLeray.Sob.iterD vs T) x e') := by
          funext z
          exact fderiv_heatVecConvolution_apply hc hθ (hT.iterD vs) z e'
        rw [heq]
        exact (differentiable_heatVecConvolution_of_cylSmooth hc hθ
          ((hT.iterD vs).dir e')).continuous) e
    have hsource : (fun z => heatVecConvolution θ
        (UnforcedLeray.Sob.iterD vs T) z) =ᵐ[(UnforcedLeray.Sob.cylinder c).μ]
        UnforcedLeray.Sob.iterD vs (heatVecConvolution θ T) := by
      filter_upwards [] with z
      exact (congrFun hcomm z).symm
    have hweakOne' := hweakOne.congr_ae hsource (by
      filter_upwards [] with z
      have h := fderiv_heatVecConvolution_apply hc hθ (hT.iterD vs) z e
      calc
        fderiv ℝ (heatVecConvolution θ (UnforcedLeray.Sob.iterD vs T)) z e =
            heatVecConvolution θ (fun x => fderiv ℝ
              (UnforcedLeray.Sob.iterD vs T) x e) z := h
        _ = heatVecConvolution θ (UnforcedLeray.Sob.iterD (e :: vs) T) z := by
          simp [UnforcedLeray.Sob.iterD_cons]
        _ = UnforcedLeray.Sob.iterD (e :: vs) (heatVecConvolution θ T) z := by
          exact (congrFun (iterD_heatVecConvolution_commute hc hθ hT (e :: vs)) z).symm)
    exact ih.cons hweakOne'

/-- The actual ordinary heat output of a smooth compact-axial periodic vector field belongs to
centered cylinder `H³`, with its actual Gaussian-tailed derivatives represented by `W.ofFields`.
-/
noncomputable def heatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    UnforcedLeray.Cyl.H ℝ Vec c 0 3 := by
  let g : UnforcedLeray.Sob.Idx 2 3 → Plane → Vec := heatVecH3Field (c := c) (θ := θ) T
  have hmem : ∀ α, MemLp (g α) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    exact memLp_heatVecH3Field hc hθ hT α
  have hweak : ∀ α : UnforcedLeray.Sob.Idx 2 3,
      UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c)
        ((UnforcedLeray.Sob.cylinder c).word α) (g UnforcedLeray.Sob.Idx.zero) (g α) := by
    intro α
    have h := hasWeakDeriv_iterD_heatVecConvolution hc hθ hT
      ((UnforcedLeray.Sob.cylinder c).word α)
    exact h.congr_ae (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun z =>
        congrFun (iterD_heatVecConvolution_commute hc hθ hT
          ((UnforcedLeray.Sob.cylinder c).word α)) z)
  exact UnforcedLeray.Sob.W.ofFields (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec) (k := 3) (p := 2)
    g hmem hweak

/-- The H³ class represents the actual Gaussian convolution at derivative order zero. -/
theorem heatVecH3_value_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 (heatVecH3 hc hθ hT) : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] heatVecConvolution θ T := by
  rw [heatVecH3, UnforcedLeray.Sob.W.value_ofFields]
  rw [← heatVecH3_measure_eq_cell c]
  have hmem := memLp_heatVecH3Field hc hθ hT UnforcedLeray.Sob.Idx.zero
  filter_upwards [hmem.coeFn_toLp] with z hz
  simpa [heatVecH3Field, UnforcedLeray.Cyl.word_zero,
    UnforcedLeray.Sob.iterD_nil] using hz

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.memLp_iterD_vec_cylSmooth_normalized
#print axioms UnforcedLeray.HeatCylinder.hasWeakDeriv_iterD_heatVecConvolution
#print axioms UnforcedLeray.HeatCylinder.heatVecH3
#print axioms UnforcedLeray.HeatCylinder.heatVecH3_value_ae
