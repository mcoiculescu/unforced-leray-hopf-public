import UnforcedLeray.Lib.HeatCylinder.HeatL2Density
import UnforcedLeray.Lib.TrainB.P0W1Rough
import UnforcedLeray.Lib.TrainB.P0W1MeasurePreserving

/-!
# Strong continuity of cylinder translations on centered vector `L²`

Smooth compact-axial fields are dense in the order-zero cylinder Sobolev graph. The smooth
`W¹` translation estimates therefore extend to every centered-cell `L²` class.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (cellμ)

private abbrev VecW0 (c : ℝ) :=
  UnforcedLeray.Sob.W (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2

private abbrev VecW1 (c : ℝ) :=
  UnforcedLeray.TrainB.VecH1 c

private theorem wμ_zero_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem w0_to_cell_mp {c : ℝ} :
    MeasurePreserving id (cellμ c)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [← wμ_zero_eq_cell c]
  exact MeasurePreserving.id _

private noncomputable def w0ToCellL2 {c : ℝ} :
    Lp Vec 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) →ₗᵢ[ℝ] UnforcedLeray.Cyl.L2v c :=
  Lp.compMeasurePreservingₗᵢ ℝ id w0_to_cell_mp

private noncomputable def vecW0ValueL2 {c : ℝ} : VecW0 c →L[ℝ] UnforcedLeray.Cyl.L2v c :=
  w0ToCellL2.toContinuousLinearMap.comp
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2)

private theorem vecW0ValueL2_centeredVecW0 {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.L2v c) :
    vecW0ValueL2 (UnforcedLeray.HeatCylinder.centeredVecW0 hc x) = x := by
  apply Lp.ext
  have hval := UnforcedLeray.HeatCylinder.centeredVecW0_value_ae hc x
  have hcomp := Lp.coeFn_compMeasurePreserving
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2
      (UnforcedLeray.HeatCylinder.centeredVecW0 hc x)) w0_to_cell_mp
  filter_upwards [hcomp, hval] with z hz₁ hz₂
  have hz₁' : (vecW0ValueL2 (UnforcedLeray.HeatCylinder.centeredVecW0 hc x) :
      Plane → Vec) z =
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2
        (UnforcedLeray.HeatCylinder.centeredVecW0 hc x) : Plane → Vec) z := by
    calc
      _ = (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2
          (UnforcedLeray.HeatCylinder.centeredVecW0 hc x) : Plane → Vec) (id z) := by
        change ((Lp.compMeasurePreserving id w0_to_cell_mp
          (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2
            (UnforcedLeray.HeatCylinder.centeredVecW0 hc x)) :
          Lp Vec 2 (cellμ c)) : Plane → Vec) z = _
        exact hz₁
      _ = _ := rfl
  exact hz₁'.trans hz₂

private theorem smoothW0Value_eq_smoothW1Value {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec} (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    vecW0ValueL2 (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec) (k := 0)
      (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu) =
      UnforcedLeray.TrainB.vecH1ValueCellCLM_MP
        (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec) (k := 1)
          (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu) := by
  apply Lp.ext
  have hleft := Lp.coeFn_compMeasurePreserving
    ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2)
      (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec) (k := 0)
        (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu)) w0_to_cell_mp
  have hleftValue := UnforcedLeray.Sob.W.value_ofCylSmooth (c := c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec) (k := 0) (p := 2)
    hc u hu
  have hrightValue := UnforcedLeray.TrainB.vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu
  have hleftValue' :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 0 2
        (UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec) (k := 0)
          (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu) :
        Plane → Vec) =ᵐ[cellμ c] u := by
    simpa only [wμ_zero_eq_cell] using hleftValue
  filter_upwards [hleft, hleftValue', hrightValue] with z hz₁ hz₂ hz₃
  exact hz₁.trans (hz₂.trans hz₃.symm)

private theorem tendsTo_centered_qShift {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.L2v c) :
    Tendsto (fun h => UnforcedLeray.TrainB.qShiftL2 hc h x) (𝓝 0) (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, u, hu, hy, hlim⟩ :=
    UnforcedLeray.HeatCylinder.exists_smooth_centeredVecW0_sequence hc x
  have hval := vecW0ValueL2.continuous.tendsto (UnforcedLeray.HeatCylinder.centeredVecW0 hc x)
    |>.comp hlim
  have hxval : vecW0ValueL2 (UnforcedLeray.HeatCylinder.centeredVecW0 hc x) = x :=
    vecW0ValueL2_centeredVecW0 hc x
  have hlimx0 : Tendsto (vecW0ValueL2 ∘ y) atTop (𝓝 x) := by
    simpa only [hxval] using hval
  have hlimx : Tendsto (fun n => vecW0ValueL2 (y n)) atTop (𝓝 x) := by
    change Tendsto (vecW0ValueL2 ∘ y) atTop (𝓝 x)
    exact hlimx0
  have hevent := (Metric.tendsto_nhds.mp hlimx) (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let n := N
  have hclose : ‖vecW0ValueL2 (y n) - x‖ < ε / 4 := by
    have := hN n (le_rfl : N ≤ n)
    rwa [dist_eq_norm] at this
  let z : VecW1 c := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec)
    (k := 1) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)
  have hvalEq := smoothW0Value_eq_smoothW1Value hc (hu n)
  have hbound : ∀ᶠ h : ℝ in 𝓝 0,
      |h| * ‖UnforcedLeray.TrainB.vecH1DqCellCLM_MP z‖ < ε / 2 := by
    have hcont : Tendsto (fun h : ℝ => |h| *
        ‖UnforcedLeray.TrainB.vecH1DqCellCLM_MP z‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const
        ‖UnforcedLeray.TrainB.vecH1DqCellCLM_MP z‖
    filter_upwards [(Metric.tendsto_nhds.mp hcont) (ε / 2) (by positivity)] with h hh
    have hnonneg : 0 ≤ |h| * ‖UnforcedLeray.TrainB.vecH1DqCellCLM_MP z‖ :=
      mul_nonneg (abs_nonneg _) (norm_nonneg _)
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hh
  filter_upwards [hbound] with h hh
  have hsmooth := UnforcedLeray.TrainB.norm_qShift_sub_le_ofCylSmooth
    (c := c) (h := h) hc (hu n)
  have hshiftClose : ‖UnforcedLeray.TrainB.qShiftL2 hc h x - x‖ ≤
      2 * ‖vecW0ValueL2 (y n) - x‖ +
        ‖UnforcedLeray.TrainB.qShiftL2 hc h (vecW0ValueL2 (y n)) -
          vecW0ValueL2 (y n)‖ := by
    let S := UnforcedLeray.TrainB.qShiftL2Isometry hc h
    have hmap := S.map_sub x (vecW0ValueL2 (y n))
    have hnorm := S.norm_map (x - vecW0ValueL2 (y n))
    calc
      ‖S x - x‖ = ‖(S x - S (vecW0ValueL2 (y n))) +
          (S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)) +
          (vecW0ValueL2 (y n) - x)‖ := by congr 1 <;> abel
      _ ≤ ‖S x - S (vecW0ValueL2 (y n))‖ +
          ‖S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)‖ +
          ‖vecW0ValueL2 (y n) - x‖ := by
        calc
          _ ≤ ‖(S x - S (vecW0ValueL2 (y n))) +
              (S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n))‖ +
              ‖vecW0ValueL2 (y n) - x‖ := norm_add_le _ _
          _ ≤ _ := add_le_add_left (norm_add_le _ _) _
      _ = 2 * ‖vecW0ValueL2 (y n) - x‖ +
          ‖S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)‖ := by
        rw [← hmap, hnorm, norm_sub_rev]
        ring
  have hsmooth' : ‖UnforcedLeray.TrainB.qShiftL2 hc h (vecW0ValueL2 (y n)) -
      vecW0ValueL2 (y n)‖ ≤ |h| *
        ‖UnforcedLeray.TrainB.vecH1DqCellCLM_MP z‖ := by
    rw [hy n, hvalEq]
    simpa [z] using hsmooth
  have hfinal : ‖UnforcedLeray.TrainB.qShiftL2 hc h x - x‖ < ε := by
    calc
      ‖UnforcedLeray.TrainB.qShiftL2 hc h x - x‖ ≤
          2 * ‖vecW0ValueL2 (y n) - x‖ +
            ‖UnforcedLeray.TrainB.qShiftL2 hc h (vecW0ValueL2 (y n)) -
              vecW0ValueL2 (y n)‖ := hshiftClose
      _ ≤ 2 * (ε / 4) + |h| *
          ‖UnforcedLeray.TrainB.vecH1DqCellCLM_MP z‖ :=
        add_le_add (by nlinarith [hclose]) hsmooth'
      _ < ε := by nlinarith [hh]
  simpa [dist_eq_norm] using hfinal

private theorem tendsTo_centered_etaShift {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.L2v c) :
    Tendsto (fun h => UnforcedLeray.TrainB.etaShiftL2 c h x) (𝓝 0) (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, u, hu, hy, hlim⟩ :=
    UnforcedLeray.HeatCylinder.exists_smooth_centeredVecW0_sequence hc x
  have hval := vecW0ValueL2.continuous.tendsto (UnforcedLeray.HeatCylinder.centeredVecW0 hc x)
    |>.comp hlim
  have hxval : vecW0ValueL2 (UnforcedLeray.HeatCylinder.centeredVecW0 hc x) = x :=
    vecW0ValueL2_centeredVecW0 hc x
  have hlimx0 : Tendsto (vecW0ValueL2 ∘ y) atTop (𝓝 x) := by
    simpa only [hxval] using hval
  have hlimx : Tendsto (fun n => vecW0ValueL2 (y n)) atTop (𝓝 x) := by
    change Tendsto (vecW0ValueL2 ∘ y) atTop (𝓝 x)
    exact hlimx0
  have hevent := (Metric.tendsto_nhds.mp hlimx) (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let n := N
  have hclose : ‖vecW0ValueL2 (y n) - x‖ < ε / 4 := by
    have := hN n (le_rfl : N ≤ n)
    rwa [dist_eq_norm] at this
  let z : VecW1 c := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec)
    (k := 1) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)
  have hvalEq := smoothW0Value_eq_smoothW1Value hc (hu n)
  have hbound : ∀ᶠ h : ℝ in 𝓝 0,
      |h| * ‖UnforcedLeray.TrainB.vecH1DetaCellCLM_MP z‖ < ε / 2 := by
    have hcont : Tendsto (fun h : ℝ => |h| *
        ‖UnforcedLeray.TrainB.vecH1DetaCellCLM_MP z‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const
        ‖UnforcedLeray.TrainB.vecH1DetaCellCLM_MP z‖
    filter_upwards [(Metric.tendsto_nhds.mp hcont) (ε / 2) (by positivity)] with h hh
    have hnonneg : 0 ≤ |h| * ‖UnforcedLeray.TrainB.vecH1DetaCellCLM_MP z‖ :=
      mul_nonneg (abs_nonneg _) (norm_nonneg _)
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hh
  filter_upwards [hbound] with h hh
  have hsmooth := UnforcedLeray.TrainB.norm_etaShift_sub_le_ofCylSmooth
    (c := c) (h := h) hc (hu n)
  have hsmooth' : ‖UnforcedLeray.TrainB.etaShiftL2 c h (vecW0ValueL2 (y n)) -
      vecW0ValueL2 (y n)‖ ≤ |h| *
        ‖UnforcedLeray.TrainB.vecH1DetaCellCLM_MP z‖ := by
    rw [hy n, hvalEq]
    simpa [z] using hsmooth
  let S := UnforcedLeray.TrainB.etaShiftL2 c h
  have hshiftClose : ‖S x - x‖ ≤
      2 * ‖vecW0ValueL2 (y n) - x‖ + ‖S (vecW0ValueL2 (y n)) -
        vecW0ValueL2 (y n)‖ := by
    have hmap := S.map_sub x (vecW0ValueL2 (y n))
    have hnorm := S.norm_map (x - vecW0ValueL2 (y n))
    calc
      ‖S x - x‖ = ‖(S x - S (vecW0ValueL2 (y n))) +
          (S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)) +
          (vecW0ValueL2 (y n) - x)‖ := by congr 1 <;> abel
      _ ≤ ‖S x - S (vecW0ValueL2 (y n))‖ +
          ‖S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)‖ +
          ‖vecW0ValueL2 (y n) - x‖ := by
        calc
          _ ≤ ‖(S x - S (vecW0ValueL2 (y n))) +
              (S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n))‖ +
              ‖vecW0ValueL2 (y n) - x‖ := norm_add_le _ _
          _ ≤ _ := add_le_add_left (norm_add_le _ _) _
      _ = 2 * ‖vecW0ValueL2 (y n) - x‖ +
          ‖S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)‖ := by
        rw [← hmap, hnorm, norm_sub_rev]
        ring
  have hfinal : ‖S x - x‖ < ε := by
    calc
      ‖S x - x‖ ≤ 2 * ‖vecW0ValueL2 (y n) - x‖ +
          ‖S (vecW0ValueL2 (y n)) - vecW0ValueL2 (y n)‖ := hshiftClose
      _ ≤ 2 * (ε / 4) + |h| *
          ‖UnforcedLeray.TrainB.vecH1DetaCellCLM_MP z‖ :=
        add_le_add (by nlinarith [hclose]) hsmooth'
      _ < ε := by nlinarith [hh]
  simpa [S, dist_eq_norm] using hfinal

/-- Horizontal translation is strongly continuous at zero on the centered-cell vector `L²`
quotient. -/
theorem tendsto_qShiftL2_centered {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.L2v c) :
    Tendsto (fun h => UnforcedLeray.TrainB.qShiftL2 hc h x) (𝓝 0) (𝓝 x) :=
  tendsTo_centered_qShift hc x

/-- Axial translation is strongly continuous at zero on the centered-cell vector `L²` quotient. -/
theorem tendsto_etaShiftL2_centered {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.L2v c) :
    Tendsto (fun h => UnforcedLeray.TrainB.etaShiftL2 c h x) (𝓝 0) (𝓝 x) :=
  tendsTo_centered_etaShift hc x

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_qShiftL2_centered
#print axioms UnforcedLeray.HeatCylinder.tendsto_etaShiftL2_centered
