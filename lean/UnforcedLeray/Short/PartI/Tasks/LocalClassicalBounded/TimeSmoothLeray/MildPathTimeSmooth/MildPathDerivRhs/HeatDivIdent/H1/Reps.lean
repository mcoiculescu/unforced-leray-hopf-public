import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionBase

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/2`: continuous representatives of the advection and divergence terms

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `AdvDivContinuousReps` (`Short/PartI/Sub/PartI_T02_1_4_4_1_5_1.lean`).

* `A(w) = B (res4 w) (res4 w)` with `B` the bounded advection bilinear map of `advectionBase`
  (`AdvectionBase.lean`, leaf A1).
* `E(w) = (div w) w`: the scalar `div w = ∑_i (∂_i w)_i` in `H^3` (`advDivS`) multiplied by the
  vector `res3 w`, written as `∑_k (div w · (res3 w)_k) e_k` with the coordinate embeddings
  `advBaseCoord k` of `AdvectionBase.lean` and the scalar product `scalarH3Mul`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The scalar divergence `∑_i (∂_i w)_i` of `w ∈ H^5`, as an element of the scalar `H^3`. -/
def advDivS {c : ℝ} (w : Cyl.H ℝ Cyl.Vec2 c 0 5) : ScalarH3 c :=
  ∑ i : Fin 2, vectorH3Component (c := c) i
    (Sob.W.restrict (by norm_num : 3 ≤ 4) (Sob.W.partialDeriv (k := 4) i w))

/-- `E(w) = (div w) w` in `H^3`, built from the coordinate embeddings and the scalar product. -/
def advDivE {c : ℝ} (hc1 : 1 ≤ c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) : VectorH3 c :=
  ∑ k : Fin 2, advBaseCoord (c := c) k
    (scalarH3Bilinear hc1 (advDivS w)
      (vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w)))

theorem scalarValue_add_ae {c : ℝ} (x y : ScalarH3 c) :
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (x + y) : Plane → ℝ) =ᵐ[Cyl.cellμ c]
      fun z => (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) z +
        (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 y : Plane → ℝ) z := by
  rw [map_add]
  exact (Lp.coeFn_add _ _).filter_mono (ae_cell_le c)

theorem advDivS_value_ae {c : ℝ} (w : Cyl.H ℝ Cyl.Vec2 c 0 5) :
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (advDivS w) : Plane → ℝ)
      =ᵐ[Cyl.cellμ c] fun z => ∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i := by
  unfold advDivS
  rw [Fin.sum_univ_two]
  filter_upwards [scalarValue_add_ae
      (vectorH3Component (c := c) 0 (Sob.W.restrict (by norm_num : 3 ≤ 4) (Sob.W.partialDeriv (k := 4) 0 w)))
      (vectorH3Component (c := c) 1 (Sob.W.restrict (by norm_num : 3 ≤ 4) (Sob.W.partialDeriv (k := 4) 1 w))),
    vectorH3Component_value_ae (c := c) 0
      (Sob.W.restrict (by norm_num : 3 ≤ 4) (Sob.W.partialDeriv (k := 4) 0 w)),
    vectorH3Component_value_ae (c := c) 1
      (Sob.W.restrict (by norm_num : 3 ≤ 4) (Sob.W.partialDeriv (k := 4) 1 w))] with z hs h0 h1
  rw [hs, h0, h1, Fin.sum_univ_two]
  rfl

theorem advDivE_hVal_ae {c : ℝ} (hc1 : 1 ≤ c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) :
    hVal (advDivE hc1 w) =ᵐ[Cyl.cellμ c] fun z =>
      (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) •
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z := by
  unfold advDivE
  have hbil : ∀ x y : ScalarH3 c, scalarH3Bilinear hc1 x y = scalarH3Mul hc1 x y := fun x y => rfl
  simp only [hbil]
  have hS := advBase_hVal_sum (m := 3) Finset.univ (fun k : Fin 2 =>
    advBaseCoord (c := c) k (scalarH3Mul hc1 (advDivS w)
      (vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w))))
  have hC := ae_all_iff.mpr fun k : Fin 2 => advBase_coord_value_ae (c := c) k
    (scalarH3Mul hc1 (advDivS w) (vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w)))
  have hM := ae_all_iff.mpr fun k : Fin 2 => scalarH3Mul_value_ae hc1 (advDivS w)
    (vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w))
  have hV := ae_all_iff.mpr fun k : Fin 2 => vectorH3Component_value_ae (c := c) k
    (Sob.W.restrict (by norm_num : 3 ≤ 5) w)
  have hD := advDivS_value_ae w
  filter_upwards [hS, hC, hM, hV, hD] with z h1 h2 h3 h4 h5
  rw [h1, Finset.sum_congr rfl fun k _ => h2 k]
  have hk : ∀ k : Fin 2, advBaseBasis k
      ((Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2
        (scalarH3Mul hc1 (advDivS w)
          (vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w))) : Plane → ℝ) z) =
      ((∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) *
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z k) •
        (EuclideanSpace.single k (1 : ℝ) : Cyl.Vec2) := by
    intro k
    rw [h3 k, h5, h4 k, advBaseBasis_apply]
    rfl
  simp only [hk]
  exact advBase_sum_single _ _

theorem advDivS_continuous {c : ℝ} : Continuous (advDivS (c := c)) := by
  unfold advDivS
  refine continuous_finsetSum _ fun i _ => ?_
  have hd : Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 => Sob.W.partialDeriv (k := 4) i w) :=
    (Sob.W.partialDeriv (k := 4) i).continuous
  have hr : Continuous (fun x : Cyl.H ℝ Cyl.Vec2 c 0 4 =>
      (Sob.W.restrict (by norm_num : 3 ≤ 4) x : Cyl.H ℝ Cyl.Vec2 c 0 3)) :=
    (Sob.W.restrict (by norm_num : 3 ≤ 4)).continuous
  exact (vectorH3Component (c := c) i).continuous.comp (hr.comp hd)

theorem vecComp_continuous {c : ℝ} (k : Fin 2) :
    Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w)) := by
  have hr : Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)) :=
    (Sob.W.restrict (by norm_num : 3 ≤ 5)).continuous
  exact (vectorH3Component (c := c) k).continuous.comp hr

theorem advDivE_term_continuous {c : ℝ} (hc1 : 1 ≤ c) (k : Fin 2) :
    Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      advBaseCoord (c := c) k (scalarH3Bilinear hc1 (advDivS w)
        (vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w)))) := by
  have hx : Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 => advDivS w) := advDivS_continuous
  have hy : Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      vectorH3Component (c := c) k (Sob.W.restrict (by norm_num : 3 ≤ 5) w)) := vecComp_continuous k
  exact (advBaseCoord (c := c) k).continuous.comp
    (((scalarH3Bilinear hc1).continuous.comp hx).clm_apply hy)

theorem advDivE_continuous {c : ℝ} (hc1 : 1 ≤ c) : Continuous (advDivE (c := c) hc1) :=
  continuous_finsetSum Finset.univ fun k _ => advDivE_term_continuous hc1 k

/-- **Lemma R (continuous representatives)**, target `AdvDivContinuousReps`. -/
theorem advDivContinuousReps : AdvDivContinuousReps := by
  intro c hc hc1
  obtain ⟨B, hB⟩ := advectionBase c hc hc1
  refine ⟨fun w => B (Sob.W.restrict (by norm_num : 4 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 4)
      (Sob.W.restrict (by norm_num : 4 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 4),
    advDivE hc1, ?_, advDivE_continuous hc1, fun w => ⟨?_, advDivE_hVal_ae hc1 w⟩⟩
  · have hr : Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
        (Sob.W.restrict (by norm_num : 4 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 4)) :=
      (Sob.W.restrict (by norm_num : 4 ≤ 5)).continuous
    exact (B.continuous.comp hr).clm_apply hr
  · unfold IsAdvectionTerm
    exact hB _ _

end UnforcedLeray.Short.PartI
