import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Lib.CZL2.RieszL2
import UnforcedLeray.Lib.CZL2.L2OffSupport
import UnforcedLeray.Analysis.Pressure.ConvolutionIdentity

/-!
# The concrete L² Riesz pressure of a background stress

For the actual background `U`, the pressure in (2.5) is obtained by applying the bounded
Newton-Hessian operators `R_i R_j` to the tensor entries `U_i U_j`. This file begins with the
fixed-phase construction: whenever the concrete stress columns are in L², the resulting pressure
is an actual L² function. The next step is the weak identity relating this pressure to the
projected stress pairing.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp

/-- The scalar entry `U_i U_j` of the tensor `U ⊗ U`, ordered to match column `j`. -/
def tensorEntry (U : SpatialField) (i j : Fin 3) : Space → ℝ :=
  fun y => (U y j) * (U y i)

/-- Each scalar entry of the concrete stress belongs to L² when its columns do. -/
theorem tensorEntry_memLp {U : SpatialField}
    (hU : ColumnsL2 (tensorColumns U U)) (i j : Fin 3) :
    MemLp (tensorEntry U i j) 2 volume := by
  have h := (hU j).continuousLinearMap_comp
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : Space →L[ℝ] ℝ)
  change MemLp (fun y : Space => (U y j) * (U y i)) 2 volume
  exact h

/-- The scalar L² class of one stress entry. -/
def tensorEntryL2 (U : SpatialField) (hU : ColumnsL2 (tensorColumns U U))
    (i j : Fin 3) : ScalarL2 :=
  (tensorEntry_memLp hU i j).toLp (tensorEntry U i j)

/-- The L² pressure of a stress, `p = Σᵢⱼ RᵢRⱼ(UᵢUⱼ)`, using the bounded L² Riesz-pair
operators from INF01 T4. -/
def stressPressureL2 (U : SpatialField) (hU : ColumnsL2 (tensorColumns U U)) : ScalarL2 :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    rieszPairL2 i j (tensorEntryL2 U hU i j)

/-- The phase path of the concrete L² pressure. -/
def stressPressureL2Path (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))) : ℝ → ScalarL2 :=
  fun τ => stressPressureL2 (U τ) (hU τ)

/-- Continuous L² tensor entries give a continuous L² pressure path, since every Riesz pair is a
bounded L² operator. -/
theorem continuous_stressPressureL2Path (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hEntry : ∀ i j, Continuous (fun τ => tensorEntryL2 (U τ) (hU τ) i j)) :
    Continuous (stressPressureL2Path U hU) := by
  unfold stressPressureL2Path stressPressureL2
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact (rieszPairL2 i j).continuous.comp (hEntry i j)

/-- If the concrete tensor entries are periodic in L², then so is the reconstructed pressure. -/
theorem periodic_stressPressureL2Path {P : ℝ} (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hEntry : ∀ i j, Function.Periodic (fun τ => tensorEntryL2 (U τ) (hU τ) i j) P) :
    Function.Periodic (stressPressureL2Path U hU) P := by
  intro τ
  simp only [stressPressureL2Path, stressPressureL2]
  congr 1
  funext i
  congr 1
  funext j
  exact congrArg (rieszPairL2 i j) (hEntry i j τ)

/-- Periodicity of the actual background makes every scalar tensor entry periodic in L²; proof
choices in `toLp` do not affect the resulting equivalence class. -/
theorem periodic_tensorEntryL2 {P : ℝ} (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hperiod : Function.Periodic U P) (i j : Fin 3) :
    Function.Periodic (fun τ => tensorEntryL2 (U τ) (hU τ) i j) P := by
  intro τ
  apply Lp.ext
  filter_upwards [
    (tensorEntry_memLp (hU (τ + P)) i j).coeFn_toLp,
    (tensorEntry_memLp (hU τ) i j).coeFn_toLp] with y h₁ h₂
  dsimp only [tensorEntryL2] at *
  rw [h₁, h₂, hperiod τ]

/-- The concrete spatial pressure field at phase `τ` for a background with L² stress at every
phase. -/
def stressPressure (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))) : ℝ → Space → ℝ :=
  fun τ y => stressPressureL2Path U hU τ y

/-- The stress pressure belongs to L² at each phase; the construction uses no pressure premise. -/
theorem stressPressure_memLp (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))) (τ : ℝ) :
    MemLp (stressPressure U hU τ) 2 volume := by
  exact Lp.memLp _

/-- The Riesz pair acting on the Laplacian of a compact scalar test is the negative
corresponding Hessian entry. This is the L² Poisson identity needed to cancel the stress
Hessian in the pressure reconstruction. -/
theorem rieszPairL2_laplacian_test {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ)
    (i k : Fin 3) :
    rieszPairL2 i k (((UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ).memLp 2).toLp
        (Heat.laplacian Φ)) =
      -((((hΦ.derivative k).derivative i).memLp 2).toLp
        (spatialTestDerivative i (spatialTestDerivative k Φ))) := by
  rw [rieszPairL2_toLp (UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ) i k]
  apply Lp.ext
  filter_upwards [
    (memLp_rieszPairTest (UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ) i k).coeFn_toLp,
    (((hΦ.derivative k).derivative i).memLp 2).coeFn_toLp,
    Lp.coeFn_neg ((((hΦ.derivative k).derivative i).memLp 2).toLp
      (spatialTestDerivative i (spatialTestDerivative k Φ)))] with y h₁ h₂ h₃
  rw [h₁, h₃]
  change rieszPairTest i k (Heat.laplacian Φ) y =
    -((((hΦ.derivative k).derivative i).memLp 2).toLp
      (spatialTestDerivative i (spatialTestDerivative k Φ)) y)
  have hconv : newtonConv (Heat.laplacian Φ) = fun x => -Φ x :=
    funext fun x => newtonConv_laplacian_test hΦ x
  rw [h₂,
    rieszPairTest_eq_newtonConv (UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ) i k,
    ← spatialTestDerivative_newtonConv
      ((UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ).derivative k) i,
    ← spatialTestDerivative_newtonConv
      (UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ) k,
    hconv]
  have hneg : spatialTestDerivative k (fun x => -Φ x) =
      fun x => -spatialTestDerivative k Φ x := by
    funext x
    simp [spatialTestDerivative, fderiv_fun_neg]
  rw [hneg]
  simp [spatialTestDerivative, fderiv_fun_neg]
  rfl

/-- The actual L² pressure reconstructed from `U ⊗ U` cancels the tensor against every
compact scalar Hessian. This is the concrete pressure condition used by the weak pressure
projection argument. -/
theorem stressPressureL2_hessian_identity (U : SpatialField)
    (hU : ColumnsL2 (tensorColumns U U)) {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    inner ℝ (stressPressureL2 U hU)
        (((UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ).memLp 2).toLp
          (Heat.laplacian Φ)) =
      -∑ i : Fin 3, ∑ j : Fin 3,
        inner ℝ (tensorEntryL2 U hU i j)
          ((((hΦ.derivative j).derivative i).memLp 2).toLp
            (spatialTestDerivative i (spatialTestDerivative j Φ))) := by
  have hinner (s : Finset (Fin 3)) (f : Fin 3 → ScalarL2) :
      inner ℝ (∑ i ∈ s, f i)
          (((UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ).memLp 2).toLp
            (Heat.laplacian Φ)) =
        ∑ i ∈ s, inner ℝ (f i)
          (((UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ).memLp 2).toLp
            (Heat.laplacian Φ)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, inner_add_left, ih]
  rw [stressPressureL2]
  change inner ℝ (∑ i : Fin 3, ∑ j : Fin 3,
      rieszPairL2 i j (tensorEntryL2 U hU i j))
      (((UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ).memLp 2).toLp
        (Heat.laplacian Φ)) = _
  rw [hinner Finset.univ (fun i => ∑ j : Fin 3, rieszPairL2 i j
      (tensorEntryL2 U hU i j))]
  simp only [hinner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm, inner_rieszPairL2, real_inner_comm,
    rieszPairL2_laplacian_test hΦ j i, inner_neg_right]
  have hcomm : spatialTestDerivative j (spatialTestDerivative i Φ) =
      spatialTestDerivative i (spatialTestDerivative j Φ) :=
    (SobolevGraph.spatialTestDerivative_comm hΦ i j).symm
  have hcommL2 :
      (((hΦ.derivative i).derivative j).memLp 2).toLp
          (spatialTestDerivative j (spatialTestDerivative i Φ)) =
        (((hΦ.derivative j).derivative i).memLp 2).toLp
          (spatialTestDerivative i (spatialTestDerivative j Φ)) := by
    apply Lp.ext
    filter_upwards [
      (((hΦ.derivative i).derivative j).memLp 2).coeFn_toLp,
      (((hΦ.derivative j).derivative i).memLp 2).coeFn_toLp] with y h₁ h₂
    rw [h₁, h₂, hcomm]
  rw [hcommL2]


#print axioms stressPressure_memLp
#print axioms rieszPairL2_laplacian_test
#print axioms stressPressureL2_hessian_identity

end UnforcedLeray.Cons.C03.Concrete
