import UnforcedLeray.Cons.L2.BackgroundConcrete.Pressure
import UnforcedLeray.Cons.C09PressureProjection.Poisson
import UnforcedLeray.Lib.CZL2.PressureIdentity
import UnforcedLeray.Loc.L01Coefficient.Basic
import UnforcedLeray.Loc.L01Coefficient.Operators
import UnforcedLeray.Loc.Hyp.H2ProductBound.L4

/-!
# The concrete pressure in C09's phasewise Hessian relation
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp UnforcedLeray.Cons.C09
open UnforcedLeray.Blueprint.L01
open UnforcedLeray.Blueprint.L10.H2Prod

local instance fact_one_le_four_pressure : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance holder_four_four_two_pressure : ENNReal.HolderTriple 4 4 2 := holder_four_four

/-- The Hölder tensor column of a continuous L⁴ path is a continuous L² path. -/
theorem continuous_tensorColumn_of_L4 (W : ℝ → Lp Space 4 (volume : Measure Space))
    (hW : Continuous W) (j : Fin 3) :
    Continuous (fun τ => hol j 4 4 (W τ) (W τ)) := by
  have hA : Continuous (fun τ => hol j 4 4 (W τ)) :=
    (hol j 4 4).continuous.comp hW
  exact hA.clm_apply hW

/-- The Hölder column built from an L⁴ representative is the actual L² class of the tensor
column whenever that representative agrees almost everywhere with the concrete field. -/
theorem tensorColumnL2_eq_hol {U : ℝ → SpatialField}
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (W : ℝ → Lp Space 4 (volume : Measure Space))
    (hW : ∀ τ, (W τ : SpatialField) =ᵐ[volume] U τ) (τ : ℝ) (j : Fin 3) :
    hol j 4 4 (W τ) (W τ) = toL2 (tensorColumns (U τ) (U τ) j) := by
  apply Lp.ext
  filter_upwards [coeFn_hol j (W τ) (W τ), hW τ, coeFn_toL2 (hU τ j)]
    with y hhol hWτ hcol
  change (hol j 4 4 (W τ) (W τ) : SpatialField) y =
    (toL2 (tensorColumns (U τ) (U τ) j) : SpatialField) y
  rw [hhol, hcol, hWτ]
  simp [prodJ, tensorColumns]

/-- Coordinate decomposition of the Euclidean-vector L² inner product into scalar L² pairings.
This keeps the scalar and vector L² coercions explicit. -/
theorem inner_vectorL2_eq_sum_coord (F G : L2Space) :
    inner ℝ F G = ∑ i : Fin 3, inner ℝ (coordL2 i F) (coordL2 i G) := by
  conv_lhs => rw [← sum_embedL2_coordL2 F]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  exact (inner_coordL2 (coordL2 i F) G i).symm

private theorem toLp_scalarClass (f : ScalarL2) :
    (Lp.memLp f).toLp (f : Space → ℝ) = f := by
  apply Lp.ext
  filter_upwards [(Lp.memLp f).coeFn_toLp] with y hy
  exact hy

private theorem coordL2_tensorColumn (U : SpatialField)
    (hU : ColumnsL2 (tensorColumns U U)) (i j : Fin 3) :
    coordL2 i (toL2 (tensorColumns U U j)) = tensorEntryL2 U hU i j := by
  apply Lp.ext
  filter_upwards [coeFn_coordL2 i (toL2 (tensorColumns U U j)),
    coeFn_toL2 (hU j), (tensorEntry_memLp hU i j).coeFn_toLp] with y h₁ h₂ h₃
  dsimp only [tensorEntryL2] at *
  rw [h₁, h₂, h₃]
  simp [tensorColumns, tensorEntry]

/-- The concrete scalar stress entries vary continuously in L² whenever the actual field has
a continuous L⁴ representative. -/
theorem continuous_tensorEntryL2_of_L4 (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (W : ℝ → Lp Space 4 (volume : Measure Space)) (hWc : Continuous W)
    (hW : ∀ τ, (W τ : SpatialField) =ᵐ[volume] U τ) (i j : Fin 3) :
    Continuous (fun τ => tensorEntryL2 (U τ) (hU τ) i j) := by
  have hColumn : Continuous (fun τ => hol j 4 4 (W τ) (W τ)) :=
    continuous_tensorColumn_of_L4 W hWc j
  have hEntry : Continuous (fun τ => coordL2 i (hol j 4 4 (W τ) (W τ))) :=
    (coordL2 i).continuous.comp hColumn
  apply hEntry.congr
  intro τ
  rw [tensorColumnL2_eq_hol hU W hW τ j]
  exact coordL2_tensorColumn (U τ) (hU τ) i j

private theorem coordL2_hessColumn {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ)
    (i j : Fin 3) :
    coordL2 i (hessL2 Φ j) =
      (((hΦ.derivative j).derivative i).memLp 2).toLp
        (spatialTestDerivative i (spatialTestDerivative j Φ)) := by
  have hgrad := memLp_gradField_test (hΦ.derivative j)
  have hsecond := ((hΦ.derivative j).derivative i).memLp 2
  apply Lp.ext
  filter_upwards [coeFn_coordL2 i (hessL2 Φ j), coeFn_toL2 hgrad,
    hsecond.coeFn_toLp] with y h₁ h₂ h₃
  dsimp only [hessL2] at *
  rw [h₁, h₂, h₃, gradField_apply]

private theorem coordL2_pressureColumn {p : Space → ℝ} (hp : MemLp p 2 volume)
    (i j : Fin 3) :
    coordL2 i (toL2 (fun y => p y • coordinateVector j)) =
      if i = j then (hp.toLp p) else 0 := by
  have hcol := memLp_smul_coordinateVector hp j
  apply Lp.ext
  filter_upwards [coeFn_coordL2 i (toL2 (fun y => p y • coordinateVector j)),
    coeFn_toL2 hcol, hp.coeFn_toLp] with y h₁ h₂ h₃
  rw [h₁, h₂]
  change (p y • coordinateVector j).ofLp i =
    (if i = j then (hp.toLp p : ScalarL2) else 0) y
  by_cases hij : i = j
  · subst i
    simp [coordinateVector, h₃]
  · simp [coordinateVector, hij]

/-- The canonical Riesz pressure satisfies C09's exact stress–Hessian relation. -/
theorem stressPressureL2_c09Relation (U : SpatialField)
    (hU : ColumnsL2 (tensorColumns U U)) {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    colPairing
      (stressL2 (fun _ => U) (fun _ => stressPressureL2 U hU) 0)
      (hessL2 Φ) = 0 := by
  let p : Space → ℝ := stressPressureL2 U hU
  have hp : MemLp p 2 volume := Lp.memLp _
  have hpClass : (hp.toLp p) = stressPressureL2 U hU := by
    dsimp [p]
    exact toLp_scalarClass _
  have hLap : IsSpatialTest (Heat.laplacian Φ) :=
    UnforcedLeray.PressureAnalysis.scalarTest_laplacian hΦ
  let hsecond : Fin 3 → Fin 3 → ScalarL2 := fun i j =>
    (((hΦ.derivative j).derivative i).memLp 2).toLp
      (spatialTestDerivative i (spatialTestDerivative j Φ))
  have hsumCoe (s : Finset (Fin 3)) :
      (∑ j ∈ s, hsecond j j : ScalarL2) =ᵐ[volume]
        fun y => ∑ j ∈ s, spatialTestDerivative j (spatialTestDerivative j Φ) y := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [] with y
        simp
    | @insert j s hj ih =>
        filter_upwards [Lp.coeFn_add (hsecond j j) (∑ k ∈ s, hsecond k k), ih,
          (((hΦ.derivative j).derivative j).memLp 2).coeFn_toLp] with y h₁ h₂ h₃
        rw [Finset.sum_insert hj, h₁, Pi.add_apply, h₂, Finset.sum_insert hj]
        dsimp only [hsecond]
        rw [h₃]
  have hLapClass :
      (∑ j : Fin 3, hsecond j j) = (hLap.memLp 2).toLp (Heat.laplacian Φ) := by
    apply Lp.ext
    filter_upwards [hsumCoe Finset.univ, (hLap.memLp 2).coeFn_toLp] with y hsum hΔ
    rw [hsum, hΔ]
    simp only [Heat.laplacian]
    rfl
  have hpressureSum :
      (∑ j : Fin 3, inner ℝ (hp.toLp p) (hsecond j j)) =
        inner ℝ (hp.toLp p) ((hLap.memLp 2).toLp (Heat.laplacian Φ)) := by
    calc
      (∑ j : Fin 3, inner ℝ (hp.toLp p) (hsecond j j)) =
          ∑ j : Fin 3, inner ℝ (hsecond j j) (hp.toLp p) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact real_inner_comm _ _
      _ = inner ℝ (∑ j : Fin 3, hsecond j j) (hp.toLp p) := by rw [sum_inner]
      _ = inner ℝ (hp.toLp p) ((hLap.memLp 2).toLp (Heat.laplacian Φ)) := by
        rw [hLapClass, real_inner_comm]
  have hdiagPressure (j : Fin 3) :
      (∑ i : Fin 3, inner ℝ
        (coordL2 i (toL2 (fun y => p y • coordinateVector j)))
        (coordL2 i (hessL2 Φ j))) = inner ℝ (hp.toLp p) (hsecond j j) := by
    classical
    rw [Finset.sum_eq_single j]
    · rw [coordL2_pressureColumn hp j j, if_pos rfl,
        coordL2_hessColumn hΦ j j]
    · intro i hi hij
      rw [coordL2_pressureColumn hp i j]
      simp [hij]
    · simp
  have hT := stressPressureL2_hessian_identity U hU hΦ
  rw [← hpClass] at hT
  unfold colPairing stressL2
  simp only [inner_add_left, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun j _ => inner_vectorL2_eq_sum_coord _ _]
  simp_rw [coordL2_tensorColumn U hU, coordL2_hessColumn hΦ]
  rw [Finset.sum_congr rfl fun j _ => inner_vectorL2_eq_sum_coord _ _]
  rw [Finset.sum_congr rfl fun j _ => hdiagPressure j, hpressureSum]
  rw [Finset.sum_comm]
  linarith

/-- The phasewise C09 relation for the canonical Riesz pressure path of an actual background. -/
theorem stressPressure_c09Relation_path (U : ℝ → SpatialField)
    (hU : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))) (τ : ℝ)
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) :
    colPairing (stressL2 U (stressPressure U hU) τ) (hessL2 Φ) = 0 := by
  change colPairing
    (stressL2 (fun _ => U τ)
      (fun _ => stressPressureL2 (U τ) (hU τ)) 0) (hessL2 Φ) = 0
  exact stressPressureL2_c09Relation (U τ) (hU τ) hΦ

#print axioms inner_vectorL2_eq_sum_coord
#print axioms stressPressureL2_c09Relation
#print axioms stressPressure_c09Relation_path
#print axioms continuous_tensorEntryL2_of_L4

end UnforcedLeray.Cons.C03.Concrete
