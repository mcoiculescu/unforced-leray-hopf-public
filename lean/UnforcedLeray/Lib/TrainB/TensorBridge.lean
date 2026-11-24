import UnforcedLeray.Lib.Train.Ops
import UnforcedLeray.Lib.TrainB.VecBridge
import UnforcedLeray.Lib.TrainB.WeakGraph
import UnforcedLeray.Lib.Sobolev.Complexify

/-!
# Vector-valued H³ component bridge

This leaf lifts the already proved scalar H³ product to the coordinate maps of the actual
Euclidean train carrier. It is the first step toward the row-oriented tensor field used by NS.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open MeasureTheory
open UnforcedLeray.Train (Vec)
open UnforcedLeray.GaussianVortex (Plane)

namespace UnforcedLeray.TrainB

abbrev VectorH3 (c : ℝ) := UnforcedLeray.Cyl.H ℝ Vec c 0 3

/-- The continuous Sobolev coordinate projection from vector H³ to scalar H³. -/
def vectorH3Component {c : ℝ} (i : Fin 2) : VectorH3 c →L[ℝ] ScalarH3 c :=
  UnforcedLeray.Sob.W.mapCLM (EuclideanSpace.proj i)

/-- Its value agrees a.e. with the corresponding coordinate of the vector value. -/
theorem vectorH3Component_value_ae {c : ℝ} (i : Fin 2) (x : VectorH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (vectorH3Component i x) : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x) z i) := by
  let L : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
  have hmap := UnforcedLeray.Sob.W.value_mapCLM
    (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (𝕜' := ℝ) (F := Vec) (G := ℝ) (k := 3) (p := 2) L x
  have hLp : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (vectorH3Component i x) : Plane → ℝ) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun z => L ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec) z)) := by
    have hcoe := L.coeFn_compLp'
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
    filter_upwards [hcoe] with z hz
    exact congrArg (fun f : Lp ℝ 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → ℝ) z) hmap |>.trans hz
  have hcell := (congrArg (fun μ : Measure Plane =>
      ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (vectorH3Component i x) : Plane → ℝ) =ᵐ[μ]
       fun z => L ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x) z)))
      (UnforcedLeray.TrainB.scalarH2_measure_eq_cell c)).mp hLp
  filter_upwards [hcell] with z hz
  simpa [L] using hz


/-- The Hilbert value carrier for the actual two-row tensor. -/
abbrev TensorVal := WithLp 2 (Vec × Vec)
abbrev TensorH3 (c : ℝ) := UnforcedLeray.Cyl.H ℝ TensorVal c 0 3

/-- A coordinate basis tensor in the Hilbert product of the two Euclidean rows. -/
def tensorBasis (i j : Fin 2) : TensorVal :=
  WithLp.toLp 2 (if i = 0 then
    (EuclideanSpace.single j (1 : ℝ), (0 : Vec)) else
    ((0 : Vec), EuclideanSpace.single j (1 : ℝ)))

/-- Insert one scalar field as a single coordinate of the row tensor. -/
def tensorEntryCLM (i j : Fin 2) : ℝ →L[ℝ] TensorVal :=
  LinearMap.mkContinuous
    { toFun := fun r => r • tensorBasis i j
      map_add' := by intro r s; simp [add_smul]
      map_smul' := by intro a r; simp [mul_smul] }
    ‖tensorBasis i j‖ (by
      intro r
      change ‖r • tensorBasis i j‖ ≤ ‖tensorBasis i j‖ * ‖r‖
      rw [norm_smul]
      exact le_of_eq (mul_comm (‖r‖) (‖tensorBasis i j‖)))

/-- Every scalar H³ entry embeds continuously into the tensor-valued H³ graph. -/
def scalarH3TensorEntry {c : ℝ} (i j : Fin 2) : ScalarH3 c →L[ℝ] TensorH3 c :=
  UnforcedLeray.Sob.W.mapCLM (tensorEntryCLM i j)

/-- The finite four-entry assembly of scalar products into the actual Hilbert tensor carrier. -/
def tensorH3ProductValue {c : ℝ} (hc1 : 1 ≤ c) (x y : VectorH3 c) : TensorH3 c :=
  ∑ ij : Fin 2 × Fin 2,
    scalarH3TensorEntry (c := c) ij.1 ij.2
      (scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x) (vectorH3Component (c := c) ij.2 y))

/-- A concrete bound obtained by summing the four entrywise graph estimates. -/
def tensorH3ProductConstant {c : ℝ} : ℝ :=
  ∑ ij : Fin 2 × Fin 2,
    384 * ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖ *
      ‖vectorH3Component (c := c) ij.1‖ * ‖vectorH3Component (c := c) ij.2‖

theorem tensorH3ProductValue_norm_le {c : ℝ} (hc1 : 1 ≤ c) (x y : VectorH3 c) :
    ‖tensorH3ProductValue hc1 x y‖ ≤
      tensorH3ProductConstant (c := c) * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ∑ ij : Fin 2 × Fin 2,
        ‖scalarH3TensorEntry (c := c) ij.1 ij.2
          (scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x) (vectorH3Component (c := c) ij.2 y))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ij : Fin 2 × Fin 2,
        (384 * ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖ *
          ‖vectorH3Component (c := c) ij.1‖ * ‖vectorH3Component (c := c) ij.2‖) * ‖x‖ * ‖y‖ := by
      apply Finset.sum_le_sum
      intro ij hij
      calc
        _ ≤ ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖ *
            ‖scalarH3Mul hc1 (vectorH3Component (c := c) ij.1 x) (vectorH3Component (c := c) ij.2 y)‖ :=
          (scalarH3TensorEntry (c := c) ij.1 ij.2).le_opNorm _
        _ ≤ ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖ *
            (384 * ‖vectorH3Component (c := c) ij.1 x‖ * ‖vectorH3Component (c := c) ij.2 y‖) := by
          gcongr
          exact scalarH3Mul_norm_le hc1 _ _
        _ ≤ (384 * ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖ *
              ‖vectorH3Component (c := c) ij.1‖ * ‖vectorH3Component (c := c) ij.2‖) * ‖x‖ * ‖y‖ := by
          have h1 := (vectorH3Component (c := c) ij.1).le_opNorm x
          have h2 := (vectorH3Component (c := c) ij.2).le_opNorm y
          have hp := mul_le_mul h1 h2
            (norm_nonneg (vectorH3Component (c := c) ij.2 y))
            (mul_nonneg (norm_nonneg (vectorH3Component (c := c) ij.1)) (norm_nonneg x))
          calc
            _ = (384 * ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖) *
                (‖vectorH3Component (c := c) ij.1 x‖ * ‖vectorH3Component (c := c) ij.2 y‖) := by ring
            _ ≤ (384 * ‖scalarH3TensorEntry (c := c) ij.1 ij.2‖) *
                ((‖vectorH3Component (c := c) ij.1‖ * ‖x‖) *
                  (‖vectorH3Component (c := c) ij.2‖ * ‖y‖)) :=
              mul_le_mul_of_nonneg_left hp (by positivity)
            _ = _ := by ring
    _ = tensorH3ProductConstant (c := c) * ‖x‖ * ‖y‖ := by
      simp only [tensorH3ProductConstant]
      rw [Finset.sum_mul]
      rw [Finset.sum_mul]

/-- Every one-coordinate basis tensor has Hilbert norm one. -/
theorem norm_tensorBasis (i j : Fin 2) : ‖tensorBasis i j‖ = 1 := by
  fin_cases i <;> fin_cases j <;> simp [tensorBasis]

/-- The scalar-to-tensor insertion is isometric. -/
def tensorEntryIsometry (i j : Fin 2) : ℝ →ₗᵢ[ℝ] TensorVal where
  toLinearMap := (tensorEntryCLM i j).toLinearMap
  norm_map' r := by
    change ‖r • tensorBasis i j‖ = ‖r‖
    rw [norm_smul, norm_tensorBasis]
    simp

theorem tensorH3Entry_norm_eq {c : ℝ} (i j : Fin 2) (x : ScalarH3 c) :
    ‖scalarH3TensorEntry (c := c) i j x‖ = ‖x‖ := by
  exact UnforcedLeray.Sob.W.norm_mapCLM (tensorEntryIsometry i j) x

/-- Coordinate projection on Euclidean two-space is contractive. -/
theorem norm_euclidean_proj_le_one (i : Fin 2) :
    ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro v
    change ‖v i‖ ≤ 1 * ‖v‖
    simpa using (PiLp.norm_apply_le v i)

/-- Componentwise value maps on cylinder H³ remain contractive, independently of the period. -/
theorem norm_vectorH3Component_apply_le {c : ℝ} (i : Fin 2) (x : VectorH3 c) :
    ‖vectorH3Component (c := c) i x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [UnforcedLeray.Sob.W.norm_sq, UnforcedLeray.Sob.W.norm_sq]
  apply Finset.sum_le_sum
  intro α hα
  rw [vectorH3Component, UnforcedLeray.Sob.W.deriv_mapCLM]
  have hL := norm_euclidean_proj_le_one i
  have hcomp : ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ).compLp
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x)‖ ≤
      ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x‖ := by
    calc
      _ ≤ ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ *
          ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x‖ :=
        (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).norm_compLp_le _
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hL
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hcomp

theorem norm_vectorH3Component_le_one {c : ℝ} (i : Fin 2) :
    ‖vectorH3Component (c := c) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro x
    simpa using norm_vectorH3Component_apply_le i x

theorem norm_scalarH3TensorEntry_le_one {c : ℝ} (i j : Fin 2) :
    ‖scalarH3TensorEntry (c := c) i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro x
    rw [tensorH3Entry_norm_eq]
    simp

/-- Uniform tensor product coefficient: four entries, each bounded by the scalar H³ coefficient. -/
theorem tensorH3ProductConstant_le_1536 {c : ℝ} :
    tensorH3ProductConstant (c := c) ≤ 1536 := by
  unfold tensorH3ProductConstant
  calc
    _ ≤ ∑ _ij : Fin 2 × Fin 2, (384 : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hi := norm_vectorH3Component_le_one (c := c) ij.1
      have hj := norm_vectorH3Component_le_one (c := c) ij.2
      have he := norm_scalarH3TensorEntry_le_one (c := c) ij.1 ij.2
      calc
        _ ≤ (384 : ℝ) * 1 * 1 * 1 := by gcongr
        _ = 384 := by ring
    _ = 1536 := by norm_num


def tensorH3Bilinear {c : ℝ} (hc1 : 1 ≤ c) :
    VectorH3 c →L[ℝ] VectorH3 c →L[ℝ] TensorH3 c :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (tensorH3ProductValue hc1)
      (by
        intro x₁ x₂ y
        simp only [tensorH3ProductValue, map_add, scalarH3Mul_add_left]
        rw [Finset.sum_add_distrib])
      (by
        intro a x y
        simp only [tensorH3ProductValue, map_smul, scalarH3Mul_smul_left]
        rw [Finset.smul_sum])
      (by
        intro x y₁ y₂
        simp only [tensorH3ProductValue, map_add, scalarH3Mul_add_right]
        rw [Finset.sum_add_distrib])
      (by
        intro a x y
        simp only [tensorH3ProductValue, map_smul, scalarH3Mul_smul_right]
        rw [Finset.smul_sum]))
    1536
    (by
      intro x y
      calc
        ‖tensorH3ProductValue hc1 x y‖ ≤
            tensorH3ProductConstant (c := c) * ‖x‖ * ‖y‖ :=
          tensorH3ProductValue_norm_le hc1 x y
        _ ≤ 1536 * ‖x‖ * ‖y‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (tensorH3ProductConstant_le_1536 (c := c)) (norm_nonneg x))
            (norm_nonneg y))


/-- A single row/column component of the row-oriented Navier--Stokes tensor, obtained by
multiplying the corresponding scalar coordinates with the proved weak scalar H³ product. -/
def vectorComponentProduct {c : ℝ} (hc1 : 1 ≤ c) (i j : Fin 2) :
    VectorH3 c →L[ℝ] VectorH3 c →L[ℝ] ScalarH3 c :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun x y => scalarH3Mul hc1 (vectorH3Component i x) (vectorH3Component j y))
      (by intro x₁ x₂ y; simp only [map_add]; exact scalarH3Mul_add_left hc1 _ _ _)
      (by intro a x y; simp only [map_smul]; exact scalarH3Mul_smul_left hc1 a _ _)
      (by intro x y₁ y₂; simp only [map_add]; exact scalarH3Mul_add_right hc1 _ _ _)
      (by intro a x y; simp only [map_smul]; exact scalarH3Mul_smul_right hc1 a _ _))
    (384 * ‖vectorH3Component i‖ * ‖vectorH3Component j‖)
    (by
      intro x y
      have hix : ‖vectorH3Component i x‖ ≤ ‖vectorH3Component i‖ * ‖x‖ :=
        (vectorH3Component i).le_opNorm x
      have hjy : ‖vectorH3Component j y‖ ≤ ‖vectorH3Component j‖ * ‖y‖ :=
        (vectorH3Component j).le_opNorm y
      calc
        ‖scalarH3Mul hc1 (vectorH3Component i x) (vectorH3Component j y)‖ ≤
            384 * ‖vectorH3Component i x‖ * ‖vectorH3Component j y‖ :=
          scalarH3Mul_norm_le hc1 _ _
        _ ≤ 384 * (‖vectorH3Component i‖ * ‖x‖) *
              (‖vectorH3Component j‖ * ‖y‖) := by gcongr
        _ = (384 * ‖vectorH3Component i‖ * ‖vectorH3Component j‖) * ‖x‖ * ‖y‖ := by ring)

theorem vectorComponentProduct_value_ae {c : ℝ} (hc1 : 1 ≤ c) (i j : Fin 2)
    (x y : VectorH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (vectorComponentProduct hc1 i j x y) : Plane → ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x) z i) *
        ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) z j)) := by
  have hp := scalarH3Mul_value_ae hc1 (vectorH3Component i x) (vectorH3Component j y)
  have hx := vectorH3Component_value_ae i x
  have hy := vectorH3Component_value_ae j y
  change (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
      (scalarH3Mul hc1 (vectorH3Component i x) (vectorH3Component j y)) : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
    (fun z => ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x) z i) *
      ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) z j))
  filter_upwards [hp, hx, hy] with z hp hx hy
  rw [hp, hx, hy]


/-- The tensor-valued H³ representative of a scalar coordinate insertion. -/
theorem scalarH3TensorEntry_value_ae {c : ℝ} (i j : Fin 2) (x : ScalarH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (scalarH3TensorEntry i j x) : Plane → TensorVal) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
      (fun z => tensorEntryCLM i j
        ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x) z)) := by
  let L : ℝ →L[ℝ] TensorVal := tensorEntryCLM i j
  have hmap := UnforcedLeray.Sob.W.value_mapCLM
    (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (𝕜' := ℝ) (F := ℝ) (G := TensorVal) (k := 3) (p := 2) L x
  have hLp : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (scalarH3TensorEntry i j x) : Plane → TensorVal) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun z => L ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) z)) := by
    have hcoe := L.coeFn_compLp'
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x)
    filter_upwards [hcoe] with z hz
    exact congrArg (fun f : Lp TensorVal 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → TensorVal) z) hmap |>.trans hz
  exact (congrArg (fun μ : Measure Plane =>
    ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (scalarH3TensorEntry i j x) : Plane → TensorVal) =ᵐ[μ]
     fun z => L ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) z)))
    (scalarH2_measure_eq_cell c)).mp hLp

/-- Addition of graph elements agrees with pointwise addition of their L² representatives. -/
theorem tensorH3_value_add_ae {c : ℝ} (x y : TensorH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 (x + y) :
      Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 x) z +
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 y) z) := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
  have hmap := map_add V x y
  have hLp : (V (x + y) : Plane → TensorVal) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun z => (V x : Plane → TensorVal) z + (V y : Plane → TensorVal) z) := by
    filter_upwards [Lp.coeFn_add (V x) (V y)] with z hz
    exact congrArg (fun f : Lp TensorVal 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → TensorVal) z) hmap |>.trans hz
  exact (congrArg (fun μ : Measure Plane =>
    ((V (x + y) : Plane → TensorVal) =ᵐ[μ]
      fun z => (V x : Plane → TensorVal) z + (V y : Plane → TensorVal) z))
    (scalarH2_measure_eq_cell c)).mp hLp

/-- A finite sum of H³ tensor graph elements has the corresponding pointwise representative. -/
theorem tensorH3_value_finset_sum_ae {c : ℝ} {ι : Type*} (s : Finset ι)
    (f : ι → TensorH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 (∑ i ∈ s, f i) :
      Plane → TensorVal) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => ∑ i ∈ s, (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 (f i)) z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
    have hmap := map_zero V
    have hLp : (V 0 : Plane → TensorVal) =ᵐ[
        UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))] (fun _ => 0) := by
      filter_upwards [Lp.coeFn_zero (E := TensorVal) (p := 2)
        (μ := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))] with z hz
      exact congrArg (fun f : Lp TensorVal 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → TensorVal) z) hmap |>.trans hz
    have hcell := (congrArg (fun μ : Measure Plane =>
      ((V 0 : Plane → TensorVal) =ᵐ[μ] fun _ => 0))
      (scalarH2_measure_eq_cell c)).mp hLp
    simpa using hcell
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hadd := tensorH3_value_add_ae (f a) (∑ i ∈ s, f i)
    filter_upwards [hadd, ih] with z hz htail
    rw [hz, htail]
/-- Pointwise tensor expansion in the row/column coordinate basis. -/
def tensorCoordinateExpansion (u v : Plane → Vec) : Plane → TensorVal := fun z =>
  ∑ ij : Fin 2 × Fin 2, ((u z ij.1) * (v z ij.2)) • tensorBasis ij.1 ij.2


/-- The row-oriented tensor `u ⊗ v` in the Euclidean train coordinates. -/
def rowTensorValue (u v : Plane → Vec) : Plane → TensorVal := fun z =>
  WithLp.toLp 2 (u z 0 • v z, u z 1 • v z)

theorem tensorCoordinateExpansion_eq_rowTensor (u v : Plane → Vec) (z : Plane) :
    tensorCoordinateExpansion u v z = rowTensorValue u v z := by
  apply (WithLp.linearEquiv 2 ℝ (Vec × Vec)).injective
  change (∑ ij : Fin 2 × Fin 2,
      ((u z ij.1) * (v z ij.2)) •
        (if ij.1 = 0 then (EuclideanSpace.single ij.2 (1 : ℝ), (0 : Vec))
          else ((0 : Vec), EuclideanSpace.single ij.2 (1 : ℝ)))) =
    (u z 0 • v z, u z 1 • v z)
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Prod.ext
  · ext k
    fin_cases k <;> simp [Fin.sum_univ_two, EuclideanSpace.single, Pi.single_apply]
  · ext k
    fin_cases k <;> simp [Fin.sum_univ_two, EuclideanSpace.single, Pi.single_apply]



/-- The inverse coordinate bridge from Euclidean row tensors to the kernel's product-plane value
carrier. It is an algebraic equivalence; its norm comparison is established separately rather than
claiming an isometry. -/
def tensorToPlaneLE : TensorVal ≃ₗ[ℝ] (Plane × Plane) where
  toFun T :=
    (planeOfVec (WithLp.ofLp T).1, planeOfVec (WithLp.ofLp T).2)
  invFun T := WithLp.toLp 2 (UnforcedLeray.Train.toVec T.1,
    UnforcedLeray.Train.toVec T.2)
  left_inv T := by
    apply (WithLp.linearEquiv 2 ℝ (Vec × Vec)).injective
    change (UnforcedLeray.Train.toVec (planeOfVec (WithLp.ofLp T).1),
      UnforcedLeray.Train.toVec (planeOfVec (WithLp.ofLp T).2)) =
        ((WithLp.ofLp T).1, (WithLp.ofLp T).2)
    exact Prod.ext (toVec_planeOfVec _) (toVec_planeOfVec _)
  right_inv T := by
    ext <;> simp [planeOfVec]
  map_add' T U := by
    ext <;> simp [planeOfVec]
  map_smul' a T := by
    ext <;> simp [planeOfVec]

/-- The coordinate equivalence as a continuous linear equivalence, since the carriers are finite
dimensional normed spaces. -/
def tensorToPlaneCLE : TensorVal ≃L[ℝ] (Plane × Plane) :=
  LinearEquiv.toContinuousLinearEquiv tensorToPlaneLE

@[simp] theorem tensorToPlaneCLE_apply (T : TensorVal) :
    tensorToPlaneCLE T =
      (planeOfVec (WithLp.ofLp T).1, planeOfVec (WithLp.ofLp T).2) := by
  change tensorToPlaneLE T = _
  rfl

@[simp] theorem tensorToPlaneCLE_symm_apply (T : Plane × Plane) :
    tensorToPlaneCLE.symm T =
      WithLp.toLp 2 (UnforcedLeray.Train.toVec T.1, UnforcedLeray.Train.toVec T.2) := by
  change tensorToPlaneLE.symm T = _
  rfl


/-- Each Euclidean vector's coordinate pair uses the product max norm and is contractive. -/
theorem norm_planeOfVec_le_one (v : Vec) : ‖planeOfVec v‖ ≤ ‖v‖ := by
  rw [planeOfVec, Prod.norm_def]
  apply max_le
  · simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v 0)
  · simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v 1)

/-- Pointwise, the Hilbert-to-kernel tensor bridge is contractive (l²⁴ to l∞⁴). -/
theorem norm_tensorToPlaneCLE_apply_le_one (T : TensorVal) :
    ‖tensorToPlaneCLE T‖ ≤ ‖T‖ := by
  rw [tensorToPlaneCLE_apply, Prod.norm_def]
  apply max_le
  · exact (norm_planeOfVec_le_one (WithLp.ofLp T).1).trans (by simpa using (WithLp.norm_fst_le (α := Vec) (β := Vec) T))
  · exact (norm_planeOfVec_le_one (WithLp.ofLp T).2).trans (by simpa using (WithLp.norm_snd_le (α := Vec) (β := Vec) T))

/-- The continuous linear map sent to the Gaussian heat module has operator norm at most one. -/
theorem norm_tensorToPlaneCLE_le_one :
    ‖(tensorToPlaneCLE.toContinuousLinearMap : TensorVal →L[ℝ] (Plane × Plane))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro T
    simpa using norm_tensorToPlaneCLE_apply_le_one T


/-- Converting the Hilbert row tensor to the Gaussian-kernel carrier gives the actual two-plane
row tensor, with each Euclidean scalar multiplication transferred through `planeOfVec`. -/
theorem tensorToPlaneCLE_rowTensorValue (u v : Plane → Vec) (z : Plane) :
    tensorToPlaneCLE (rowTensorValue u v z) =
      (u z 0 • planeOfVec (v z), u z 1 • planeOfVec (v z)) := by
  change (planeOfVec (u z 0 • v z), planeOfVec (u z 1 • v z)) = _
  simp only [planeOfVec_eq_toVecL_symm, map_smul]
/-- The assembled four-entry H³ tensor agrees with its literal row/column coordinate expansion. -/
theorem tensorH3ProductValue_value_ae {c : ℝ} (hc1 : 1 ≤ c) (x y : VectorH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (tensorH3ProductValue hc1 x y) : Plane → TensorVal) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
      tensorCoordinateExpansion
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) := by
  classical
  let term : Fin 2 × Fin 2 → TensorH3 c := fun ij =>
    scalarH3TensorEntry ij.1 ij.2
      (scalarH3Mul hc1 (vectorH3Component ij.1 x) (vectorH3Component ij.2 y))
  have hsum := tensorH3_value_finset_sum_ae Finset.univ term
  have h00 := scalarH3TensorEntry_value_ae (0 : Fin 2) (0 : Fin 2)
    (scalarH3Mul hc1 (vectorH3Component (c := c) 0 x) (vectorH3Component (c := c) 0 y))
  have h01 := scalarH3TensorEntry_value_ae (0 : Fin 2) (1 : Fin 2)
    (scalarH3Mul hc1 (vectorH3Component (c := c) 0 x) (vectorH3Component (c := c) 1 y))
  have h10 := scalarH3TensorEntry_value_ae (1 : Fin 2) (0 : Fin 2)
    (scalarH3Mul hc1 (vectorH3Component (c := c) 1 x) (vectorH3Component (c := c) 0 y))
  have h11 := scalarH3TensorEntry_value_ae (1 : Fin 2) (1 : Fin 2)
    (scalarH3Mul hc1 (vectorH3Component (c := c) 1 x) (vectorH3Component (c := c) 1 y))
  have hq00 := scalarH3Mul_value_ae hc1 (vectorH3Component (c := c) 0 x)
    (vectorH3Component (c := c) 0 y)
  have hq01 := scalarH3Mul_value_ae hc1 (vectorH3Component (c := c) 0 x)
    (vectorH3Component (c := c) 1 y)
  have hq10 := scalarH3Mul_value_ae hc1 (vectorH3Component (c := c) 1 x)
    (vectorH3Component (c := c) 0 y)
  have hq11 := scalarH3Mul_value_ae hc1 (vectorH3Component (c := c) 1 x)
    (vectorH3Component (c := c) 1 y)
  have hx0 := vectorH3Component_value_ae (c := c) 0 x
  have hx1 := vectorH3Component_value_ae (c := c) 1 x
  have hy0 := vectorH3Component_value_ae (c := c) 0 y
  have hy1 := vectorH3Component_value_ae (c := c) 1 y
  filter_upwards [hsum, h00, h01, h10, h11, hq00, hq01, hq10, hq11,
    hx0, hx1, hy0, hy1]
    with z hsum h00 h01 h10 h11 hq00 hq01 hq10 hq11 hx0 hx1 hy0 hy1
  let X : Plane → Vec := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x
  let Y : Plane → Vec := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y
  have hterm (ij : Fin 2 × Fin 2) :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 (term ij)) z =
      (X z ij.1 * Y z ij.2) • tensorBasis ij.1 ij.2 := by
    fin_cases ij
    · change (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (scalarH3TensorEntry 0 0 (scalarH3Mul hc1
            (vectorH3Component (c := c) 0 x) (vectorH3Component (c := c) 0 y)))) z =
          (X z 0 * Y z 0) • tensorBasis 0 0
      rw [h00, hq00, hx0, hy0]
      rfl
    · change (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (scalarH3TensorEntry 0 1 (scalarH3Mul hc1
            (vectorH3Component (c := c) 0 x) (vectorH3Component (c := c) 1 y)))) z =
          (X z 0 * Y z 1) • tensorBasis 0 1
      rw [h01, hq01, hx0, hy1]
      rfl
    · change (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (scalarH3TensorEntry 1 0 (scalarH3Mul hc1
            (vectorH3Component (c := c) 1 x) (vectorH3Component (c := c) 0 y)))) z =
          (X z 1 * Y z 0) • tensorBasis 1 0
      rw [h10, hq10, hx1, hy0]
      rfl
    · change (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (scalarH3TensorEntry 1 1 (scalarH3Mul hc1
            (vectorH3Component (c := c) 1 x) (vectorH3Component (c := c) 1 y)))) z =
          (X z 1 * Y z 1) • tensorBasis 1 1
      rw [h11, hq11, hx1, hy1]
      rfl
  calc
    _ = (∑ ij : Fin 2 × Fin 2,
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 (term ij)) z) := hsum
    _ = tensorCoordinateExpansion X Y z := by
      rw [tensorCoordinateExpansion]
      exact Finset.sum_congr rfl (fun ij hij => hterm ij)


/-- The actual bounded bilinear tensor map has the literal row-oriented representative `u ⊗ v` on
the centered cylinder cell. -/
theorem tensorH3Bilinear_value_ae {c : ℝ} (hc1 : 1 ≤ c)
    (x y : VectorH3 c) :
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (tensorH3Bilinear hc1 x y) : Plane → TensorVal) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
      rowTensorValue
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) := by
  have h := tensorH3ProductValue_value_ae hc1 x y
  filter_upwards [h] with z hz
  calc
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (tensorH3Bilinear hc1 x y) : Plane → TensorVal) z =
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (tensorH3ProductValue hc1 x y)) z := rfl
    _ = tensorCoordinateExpansion
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) z := hz
    _ = rowTensorValue
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) z :=
      tensorCoordinateExpansion_eq_rowTensor _ _ _

/-- The actual two-row tensor in the Gaussian-kernel Plane×Plane carrier. -/
def planeRowTensorValue (u v : Plane → Vec) : Plane → Plane × Plane := fun z =>
  (u z 0 • planeOfVec (v z), u z 1 • planeOfVec (v z))

/-- The actual bounded H³ row tensor, after coordinate conversion, agrees a.e. with the two
physical Plane rows used by the Gaussian divergence kernel. -/
theorem tensorH3Bilinear_planeValue_ae {c : ℝ} (hc1 : 1 ≤ c)
    (x y : VectorH3 c) :
    (fun z => tensorToPlaneCLE
      ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (tensorH3Bilinear hc1 x y) : Plane → TensorVal) z)) =ᵐ[
            UnforcedLeray.Cyl.cellμ c]
      planeRowTensorValue
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
        (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y) := by
  filter_upwards [tensorH3Bilinear_value_ae hc1 x y] with z hz
  rw [hz]
  exact tensorToPlaneCLE_rowTensorValue _ _ _

#print axioms UnforcedLeray.TrainB.tensorCoordinateExpansion_eq_rowTensor
#print axioms UnforcedLeray.TrainB.tensorH3Bilinear_value_ae
#print axioms UnforcedLeray.TrainB.tensorH3Bilinear_planeValue_ae
#print axioms UnforcedLeray.TrainB.tensorToPlaneCLE
#print axioms UnforcedLeray.TrainB.tensorToPlaneCLE_rowTensorValue
#print axioms UnforcedLeray.TrainB.norm_tensorToPlaneCLE_le_one
#print axioms UnforcedLeray.TrainB.tensorH3ProductValue_value_ae
#print axioms UnforcedLeray.TrainB.tensorH3ProductConstant_le_1536
#print axioms UnforcedLeray.TrainB.tensorH3Bilinear
#print axioms UnforcedLeray.TrainB.scalarH3TensorEntry
#print axioms UnforcedLeray.TrainB.vectorH3Component
#print axioms UnforcedLeray.TrainB.tensorH3ProductValue_value_ae
#print axioms UnforcedLeray.TrainB.tensorH3ProductConstant_le_1536
#print axioms UnforcedLeray.TrainB.tensorH3Bilinear
#print axioms UnforcedLeray.TrainB.scalarH3TensorEntry
#print axioms UnforcedLeray.TrainB.vectorH3Component_value_ae
#print axioms UnforcedLeray.TrainB.vectorComponentProduct_value_ae

end UnforcedLeray.TrainB
