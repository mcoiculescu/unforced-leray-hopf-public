import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianActualPairing
import UnforcedLeray.Lib.HeatCylinder.HeatL2Density
import UnforcedLeray.Lib.HeatCylinder.CenteredGaussianShiftAverageP0

/-!
# Identification of actual cylinder heat with Gaussian translation averaging

The smooth pairing formula, the actual order-zero Sobolev density, and contraction of both
operators identify the literal normalized-cell B0284 heat with the Bochner average of centered
translations on the whole centered-cell vector `L²` space.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (cellμ L2v)
open UnforcedLeray.B0284 (cellMeasure)

private abbrev VecW0 (c : ℝ) :=
  UnforcedLeray.Sob.W (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2

private theorem wμ_zero_eq_cell_local (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem w0_to_cell_mp_local {c : ℝ} :
    MeasurePreserving id (cellμ c)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [← wμ_zero_eq_cell_local c]
  exact MeasurePreserving.id _

private noncomputable def w0ToCellL2_local {c : ℝ} :
    Lp Vec 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) →ₗᵢ[ℝ] L2v c :=
  Lp.compMeasurePreservingₗᵢ ℝ id w0_to_cell_mp_local

private noncomputable def w0ValueL2_local {c : ℝ} : VecW0 c →L[ℝ] L2v c :=
  w0ToCellL2_local.toContinuousLinearMap.comp
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2)

private theorem w0ValueL2_centeredVecW0_local {c : ℝ} (hc : 0 < c)
    (x : L2v c) : w0ValueL2_local (centeredVecW0 hc x) = x := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2 (centeredVecW0 hc x))
    w0_to_cell_mp_local
  have hval := centeredVecW0_value_ae hc x
  filter_upwards [hcomp, hval] with z hzcomp hzval
  change (w0ValueL2_local (centeredVecW0 hc x) : Plane → Vec) z = _
  exact hzcomp.trans hzval

private theorem isQPeriodic_smooth_local {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) : UnforcedLeray.B0284.IsQPeriodic c T := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact hT.periodic z

private theorem memLp_smooth_centered_local {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) : MemLp T 2 (cellμ c) := by
  have hm : MemLp T 2 (cellMeasure c) := memLp_iterD_vec_cylSmooth_normalized hc hT []
  exact memLp_cyl_of_memLp_cellMeasure hc hT.smooth.continuous.measurable
    (isQPeriodic_smooth_local hT) hm

private noncomputable def smoothVecL2_local {c : ℝ} (hc : 0 < c)
    (T : {f : Plane → Vec // UnforcedLeray.Sob.IsCylSmooth c f}) : L2v c :=
  (memLp_smooth_centered_local hc T.2).toLp T.1

private theorem w0ValueL2_ofCylSmooth_local {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    w0ValueL2_local
        (UnforcedLeray.Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2) hc T hT) =
      (memLp_smooth_centered_local hc hT).toLp T := by
  let y := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2) hc T hT
  let hm := memLp_smooth_centered_local hc hT
  have hval := UnforcedLeray.Sob.W.value_ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2)
    hc T hT
  have hvalCell :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2 y : Plane → Vec) =ᵐ[cellμ c] T := by
    simpa only [UnforcedLeray.Cyl.cylinder_μ_eq] using
      (UnforcedLeray.Sob.ae_eq_wμ_iff
        (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))).mp hval
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2 y) w0_to_cell_mp_local
  filter_upwards [hcomp, hvalCell, hm.coeFn_toLp] with z hzcomp hzval hzm
  change (w0ValueL2_local y : Plane → Vec) z = _
  exact hzcomp.trans (hzval.trans hzm.symm)

/-- The actual compact-axial smooth vector classes are dense in centered-cell vector `L²`. -/
theorem denseRange_smoothVecL2_centered {c : ℝ} (hc : 0 < c) :
    DenseRange (smoothVecL2_local hc) := by
  intro x
  obtain ⟨y, u, hu, hy, hlim⟩ := exists_smooth_centeredVecW0_sequence hc x
  have hvalue : Tendsto (fun n => w0ValueL2_local (y n)) atTop (𝓝 x) := by
    have hvalue0 : Tendsto (fun n => w0ValueL2_local (y n)) atTop
        (𝓝 (w0ValueL2_local (centeredVecW0 hc x))) := by
      change Tendsto (w0ValueL2_local ∘ y) atTop
        (𝓝 (w0ValueL2_local (centeredVecW0 hc x)))
      exact (w0ValueL2_local.continuous.tendsto (centeredVecW0 hc x)).comp hlim
    change Tendsto (fun n => w0ValueL2_local (y n)) atTop
      (𝓝 (w0ValueL2_local (centeredVecW0 hc x))) at hvalue0
    rw [w0ValueL2_centeredVecW0_local hc x] at hvalue0
    exact hvalue0
  have hsmooth : ∀ n, w0ValueL2_local (y n) = smoothVecL2_local hc ⟨u n, hu n⟩ := by
    intro n
    rw [hy n]
    exact w0ValueL2_ofCylSmooth_local hc (hu n)
  have hseq : Tendsto (fun n => smoothVecL2_local hc ⟨u n, hu n⟩) atTop (𝓝 x) :=
    hvalue.congr' (Filter.Eventually.of_forall fun n => hsmooth n)
  exact mem_closure_of_tendsto hseq
    (Filter.Eventually.of_forall fun n => ⟨⟨u n, hu n⟩, rfl⟩)

private theorem centeredHeat_eq_average_smooth_local {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    centeredHeatVecL2CLM hc θ (smoothVecL2_local hc ⟨T, hT⟩) =
      centeredGaussianShiftAverageCLM hc hθ (smoothVecL2_local hc ⟨T, hT⟩) := by
  apply (denseRange_smoothVecL2_centered hc).eq_of_inner_left ℝ
  intro V
  exact inner_centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM_of_cylSmooth
    hc hθ hT V.2 (memLp_smooth_centered_local hc hT)
    (memLp_smooth_centered_local hc V.2)

/-- The actual centered B0284 Gaussian heat equals the Bochner Gaussian average of actual
centered-cell planar translations, for every centered vector `L²` class. -/
theorem centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (x : L2v c) :
    centeredHeatVecL2CLM hc θ x = centeredGaussianShiftAverageCLM hc hθ x := by
  obtain ⟨y, u, hu, hy, hlim⟩ := exists_smooth_centeredVecW0_sequence hc x
  let f : ℕ → L2v c := fun n => smoothVecL2_local hc ⟨u n, hu n⟩
  have hf : Tendsto f atTop (𝓝 x) := by
    have hvalue0 : Tendsto (fun n => w0ValueL2_local (y n)) atTop
        (𝓝 (w0ValueL2_local (centeredVecW0 hc x))) := by
      change Tendsto (w0ValueL2_local ∘ y) atTop
        (𝓝 (w0ValueL2_local (centeredVecW0 hc x)))
      exact (w0ValueL2_local.continuous.tendsto (centeredVecW0 hc x)).comp hlim
    change Tendsto (fun n => w0ValueL2_local (y n)) atTop
      (𝓝 (w0ValueL2_local (centeredVecW0 hc x))) at hvalue0
    have hvalue : Tendsto (fun n => w0ValueL2_local (y n)) atTop (𝓝 x) := by
      rw [w0ValueL2_centeredVecW0_local hc x] at hvalue0
      exact hvalue0
    have hsame : ∀ n, w0ValueL2_local (y n) = f n := by
      intro n
      rw [hy n]
      exact w0ValueL2_ofCylSmooth_local hc (hu n)
    exact hvalue.congr' (Filter.Eventually.of_forall fun n => hsame n)
  have hA : Tendsto (fun n => centeredHeatVecL2CLM hc θ (f n)) atTop
      (𝓝 (centeredHeatVecL2CLM hc θ x)) :=
    (centeredHeatVecL2CLM hc θ).continuous.tendsto x |>.comp hf
  have hB : Tendsto (fun n => centeredGaussianShiftAverageCLM hc hθ (f n)) atTop
      (𝓝 (centeredGaussianShiftAverageCLM hc hθ x)) :=
    (centeredGaussianShiftAverageCLM hc hθ).continuous.tendsto x |>.comp hf
  have hEq : ∀ n, centeredHeatVecL2CLM hc θ (f n) =
      centeredGaussianShiftAverageCLM hc hθ (f n) := by
    intro n
    exact centeredHeat_eq_average_smooth_local hc hθ (hu n)
  exact tendsto_nhds_unique hA
    (hB.congr' (Filter.Eventually.of_forall fun n => (hEq n).symm))

/-- The actual centered heat commutes with the centered Leray projection. -/
theorem centeredHeatVecL2CLM_P0_comm_actual {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : L2v c) :
    centeredHeatVecL2CLM hc θ (UnforcedLeray.Cyl.P0 c x) =
      UnforcedLeray.Cyl.P0 c (centeredHeatVecL2CLM hc θ x) := by
  have havg (y : L2v c) := centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM hc hθ y
  rw [havg (UnforcedLeray.Cyl.P0 c x), centeredGaussianShiftAverageCLM_P0_comm hc hθ x,
    ← havg x]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.denseRange_smoothVecL2_centered
#print axioms UnforcedLeray.HeatCylinder.centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM
#print axioms UnforcedLeray.HeatCylinder.centeredHeatVecL2CLM_P0_comm_actual
