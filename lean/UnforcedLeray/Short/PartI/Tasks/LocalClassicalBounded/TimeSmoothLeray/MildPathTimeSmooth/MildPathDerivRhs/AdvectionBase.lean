import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1

/-!
# Part I, task `PartI:T02/1/4/4/1/1`: the base advection estimate `AdvectionBase`

Source of record: `the November 2 reference manuscript`, lines 261-288.
Target: `AdvectionBase` (leaf A1 of `Short/PartI/Sub/T02_1_4_4_1.lean`): for `c > 0`, `c ≥ 1`,
the map `(v, w) ↦ ∑_i v_i ∂_i w` is a bounded bilinear map `H^4 × H^4 → H^3`, in the a.e. sense.

Construction.  For `v, w ∈ H^4` and `i, k : Fin 2` the scalar weak product `scalarH3Mul` of the
`i`-th coordinate of `v` (restricted to `H^3`) with the `k`-th coordinate of `∂_i w ∈ H^3` is a
bounded bilinear map (`scalarH3Bilinear`, `Lib/TrainB/WeakGraph.lean`).  The coordinate line
`r ↦ r e_k` is embedded into `H^3(ℝ²)` by `Sob.W.mapCLM`.  Summing over `(i, k)` gives
`∑_i ∑_k (v_i (∂_i w)_k) e_k = ∑_i v_i ∂_i w`.  Bilinearity and the norm bound are inherited from
`ContinuousLinearMap.bilinearComp` and `ContinuousLinearMap.compL`.
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

/-! ### The coordinate embedding and the building blocks -/

/-- The embedding `r ↦ r e_k` of the scalar line into the plane vectors. -/
def advBaseBasis (k : Fin 2) : ℝ →L[ℝ] Cyl.Vec2 :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single k (1 : ℝ))

theorem advBaseBasis_apply (k : Fin 2) (r : ℝ) :
    advBaseBasis k r = r • (EuclideanSpace.single k (1 : ℝ) : Cyl.Vec2) := by
  simp [advBaseBasis]

/-- The `k`-th coordinate line of `H^3(ℝ)`, embedded componentwise in `H^3(ℝ²)`. -/
def advBaseCoord {c : ℝ} (k : Fin 2) : ScalarH3 c →L[ℝ] VectorH3 c :=
  UnforcedLeray.Sob.W.mapCLM (advBaseBasis k)

/-- The `i`-th velocity coordinate of `v ∈ H^4`, read in `H^3`. -/
def advBaseA {c : ℝ} (i : Fin 2) : Cyl.H ℝ Cyl.Vec2 c 0 4 →L[ℝ] ScalarH3 c :=
  (vectorH3Component (c := c) i).comp (UnforcedLeray.Sob.W.restrict (by norm_num : 3 ≤ 4))

/-- The `k`-th coordinate of the `i`-th weak partial derivative of `w ∈ H^4`, in `H^3`. -/
def advBaseB {c : ℝ} (i k : Fin 2) : Cyl.H ℝ Cyl.Vec2 c 0 4 →L[ℝ] ScalarH3 c :=
  (vectorH3Component (c := c) k).comp (UnforcedLeray.Sob.W.partialDeriv (k := 3) i)

/-- The `(i, k)` term of the advection bilinear map: `(v, w) ↦ (v_i (∂_i w)_k) e_k`. -/
def advBaseTerm {c : ℝ} (hc1 : 1 ≤ c) (i k : Fin 2) :
    Cyl.H ℝ Cyl.Vec2 c 0 4 →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 4 →L[ℝ] VectorH3 c :=
  (ContinuousLinearMap.compL ℝ (Cyl.H ℝ Cyl.Vec2 c 0 4) (ScalarH3 c) (VectorH3 c)
      (advBaseCoord k)).comp
    ((scalarH3Bilinear hc1).bilinearComp (advBaseA i) (advBaseB i k))

/-- The advection bilinear map `H^4 × H^4 → H^3`, the sum of the `(i, k)` terms. -/
def advBaseCLM {c : ℝ} (hc1 : 1 ≤ c) :
    Cyl.H ℝ Cyl.Vec2 c 0 4 →L[ℝ] Cyl.H ℝ Cyl.Vec2 c 0 4 →L[ℝ] VectorH3 c :=
  ∑ i : Fin 2, ∑ k : Fin 2, advBaseTerm hc1 i k

/-- The `i`-th row `∑_k (v_i (∂_i w)_k) e_k` of the advection sum. -/
def advBaseRow {c : ℝ} (hc1 : 1 ≤ c) (v w : Cyl.H ℝ Cyl.Vec2 c 0 4) (i : Fin 2) : VectorH3 c :=
  ∑ k : Fin 2, advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w))

theorem advBaseTerm_apply {c : ℝ} (hc1 : 1 ≤ c) (i k : Fin 2) (v w : Cyl.H ℝ Cyl.Vec2 c 0 4) :
    advBaseTerm hc1 i k v w = advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w)) :=
  rfl

theorem advBaseCLM_apply {c : ℝ} (hc1 : 1 ≤ c) (v w : Cyl.H ℝ Cyl.Vec2 c 0 4) :
    advBaseCLM hc1 v w = ∑ i : Fin 2, advBaseRow hc1 v w i := by
  simp only [advBaseCLM, advBaseRow, sum_apply, advBaseTerm_apply]

/-! ### Values of the value map, a.e. -/

/-- Additivity of the representative, almost everywhere on the cell. -/
theorem advBase_hVal_add {c : ℝ} {m : ℕ} (x y : Cyl.H ℝ Cyl.Vec2 c 0 m) :
    hVal (x + y) =ᵐ[UnforcedLeray.Cyl.cellμ c] fun z => hVal x z + hVal y z := by
  have hmap := congrArg (fun f : Lp Cyl.Vec2 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) =>
        (f : Plane → Cyl.Vec2))
    (map_add (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2) x y)
  have hLp : (hVal (x + y) : Plane → Cyl.Vec2) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun z => hVal x z + hVal y z) := by
    filter_upwards [Lp.coeFn_add
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 x)
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 y)] with q hq
    exact congrArg (fun f : Plane → Cyl.Vec2 => f q) hmap |>.trans hq
  exact (congrArg (fun μ : Measure Plane =>
    ((hVal (x + y) : Plane → Cyl.Vec2) =ᵐ[μ] fun z => hVal x z + hVal y z))
    (scalarH2_measure_eq_cell c)).mp hLp

/-- The representative of the zero element vanishes almost everywhere on the cell. -/
theorem advBase_hVal_zero {c : ℝ} {m : ℕ} :
    hVal (0 : Cyl.H ℝ Cyl.Vec2 c 0 m) =ᵐ[UnforcedLeray.Cyl.cellμ c] fun _ => (0 : Cyl.Vec2) := by
  have hLp : (hVal (0 : Cyl.H ℝ Cyl.Vec2 c 0 m) : Plane → Cyl.Vec2) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      fun _ => (0 : Cyl.Vec2) := by
    unfold hVal
    rw [map_zero]
    exact Lp.coeFn_zero _ _ _
  exact (congrArg (fun μ : Measure Plane =>
    ((hVal (0 : Cyl.H ℝ Cyl.Vec2 c 0 m) : Plane → Cyl.Vec2) =ᵐ[μ] fun _ => (0 : Cyl.Vec2)))
    (scalarH2_measure_eq_cell c)).mp hLp

/-- The representative of a finite sum is the a.e. sum of the representatives. -/
theorem advBase_hVal_sum {c : ℝ} {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Cyl.H ℝ Cyl.Vec2 c 0 m) :
    hVal (∑ i ∈ s, f i) =ᵐ[UnforcedLeray.Cyl.cellμ c] fun z => ∑ i ∈ s, hVal (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact advBase_hVal_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [advBase_hVal_add (f a) (∑ i ∈ s, f i), ih] with z h1 h2
    rw [h1, h2]

/-- The coordinate embedding is the a.e. scalar multiple of the coordinate basis vector. -/
theorem advBase_coord_value_ae {c : ℝ} (k : Fin 2) (x : ScalarH3 c) :
    hVal (m := 3) (advBaseCoord k x) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      fun z => advBaseBasis k ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) z) := by
  have hmap := UnforcedLeray.Sob.W.value_mapCLM
    (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (𝕜' := ℝ) (F := ℝ) (G := Cyl.Vec2) (k := 3) (p := 2) (advBaseBasis k) x
  have hLp : (hVal (m := 3) (advBaseCoord k x) : Plane → Cyl.Vec2) =ᵐ[
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun z => advBaseBasis k ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) z)) := by
    have hcoe := (advBaseBasis k).coeFn_compLp'
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x)
    filter_upwards [hcoe] with z hz
    exact (congrArg (fun f : Lp Cyl.Vec2 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → Cyl.Vec2) z) hmap).trans hz
  exact (congrArg (fun μ : Measure Plane =>
    ((hVal (m := 3) (advBaseCoord k x) : Plane → Cyl.Vec2) =ᵐ[μ]
      (fun z => advBaseBasis k ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 x : Plane → ℝ) z))))
    (scalarH2_measure_eq_cell c)).mp hLp

/-- One `(i, k)` term, in the a.e. sense, as a multiple of the coordinate vector `e_k`. -/
theorem advBase_coord_ae {c : ℝ} (hc1 : 1 ≤ c) (v w : Cyl.H ℝ Cyl.Vec2 c 0 4) (i k : Fin 2) :
    ∀ᵐ z ∂UnforcedLeray.Cyl.cellμ c,
      hVal (m := 3) (advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w))) z =
        (hVal v z i * hVal (UnforcedLeray.Sob.W.partialDeriv (k := 3) i w) z k) •
          (EuclideanSpace.single k (1 : ℝ) : Cyl.Vec2) := by
  have h1 := advBase_coord_value_ae (c := c) k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w))
  have h2 := scalarH3Mul_value_ae hc1 (advBaseA i v) (advBaseB i k w)
  have h3 : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (advBaseA i v) : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] fun z => hVal v z i :=
    vectorH3Component_value_ae (c := c) i (UnforcedLeray.Sob.W.restrict (by norm_num : 3 ≤ 4) v)
  have h4 : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 (advBaseB i k w) : Plane → ℝ) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] fun z => hVal (UnforcedLeray.Sob.W.partialDeriv (k := 3) i w) z k :=
    vectorH3Component_value_ae (c := c) k (UnforcedLeray.Sob.W.partialDeriv (k := 3) i w)
  filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
  rw [hz1, hz2, hz3, hz4, advBaseBasis_apply]

/-- Coordinate identity `∑_k (a x_k) e_k = a x` in the plane. -/
theorem advBase_sum_single (a : ℝ) (x : Cyl.Vec2) :
    ∑ k : Fin 2, (a * x k) • (EuclideanSpace.single k (1 : ℝ) : Cyl.Vec2) = a • x := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_two]

/-! ### The bilinear map is the advection term -/

/-- `IsAdvectionOp` for the bilinear map `advBaseCLM`: the a.e. formula at level `3`. -/
theorem advBase_isOp {c : ℝ} (hc1 : 1 ≤ c) : IsAdvectionOp c 3 (advBaseCLM hc1) := by
  classical
  intro v w
  rw [advBaseCLM_apply hc1 v w]
  have hOuter : hVal (m := 3) (∑ i : Fin 2, advBaseRow hc1 v w i) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      fun z => ∑ i : Fin 2, hVal (m := 3) (advBaseRow hc1 v w i) z :=
    advBase_hVal_sum (m := 3) Finset.univ (fun i => advBaseRow hc1 v w i)
  have hInner : ∀ i : Fin 2, hVal (m := 3) (advBaseRow hc1 v w i) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      fun z => ∑ k : Fin 2,
        hVal (m := 3) (advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w))) z :=
    fun i => advBase_hVal_sum (m := 3) Finset.univ
      (fun k => advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w)))
  have hIn : ∀ᵐ z ∂UnforcedLeray.Cyl.cellμ c, ∀ i : Fin 2,
      hVal (m := 3) (advBaseRow hc1 v w i) z =
        ∑ k : Fin 2,
          hVal (m := 3) (advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w))) z :=
    ae_all_iff.mpr hInner
  have hCo : ∀ᵐ z ∂UnforcedLeray.Cyl.cellμ c, ∀ i k : Fin 2,
      hVal (m := 3) (advBaseCoord k (scalarH3Mul hc1 (advBaseA i v) (advBaseB i k w))) z =
        (hVal v z i * hVal (UnforcedLeray.Sob.W.partialDeriv (k := 3) i w) z k) •
          (EuclideanSpace.single k (1 : ℝ) : Cyl.Vec2) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => advBase_coord_ae hc1 v w i k
  filter_upwards [hOuter, hIn, hCo] with z h1 h2 h3
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  simp only [h3 i]
  exact advBase_sum_single (hVal v z i) (hVal (UnforcedLeray.Sob.W.partialDeriv (k := 3) i w) z)

/-! ### The leaf -/

/-- **Leaf A1** (`AdvectionBase`, source lines 261-288): the advection map exists at level `3`
for every `c > 0`, `c ≥ 1`. -/
theorem advectionBase : AdvectionBase := by
  intro c _ hc1
  unfold AdvectionAt
  exact ⟨advBaseCLM hc1, advBase_isOp hc1⟩

end UnforcedLeray.Short.PartI
