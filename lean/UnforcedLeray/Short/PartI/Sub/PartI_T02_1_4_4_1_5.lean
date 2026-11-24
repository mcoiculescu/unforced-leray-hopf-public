import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupP0

/-!
# Part I, `PartI:T02/1/4/4/1/5`: `HeatDivIdent` reduced to two lemmas

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic: the mild solution is smooth; mild Duhamel formula in semigroup form).

`HeatDivIdent` (`Short/PartI/Sub/T02_1_4_4_1.lean`) follows from
* `HeatDivIdentGeneral`: for every `w ∈ H^5` (no solenoidality), the heat-divergence orbit of the
  row tensor `w ⊗ w` is `S(θ)(A + E)` where `A = (w·∇)w` and `E = (div w) w`
  (the divergence of `w ⊗ w` is `(w·∇)w + (div w) w`, a statement about smooth tensors, extended by
  density of smooth cylinder fields in `H^5` and continuity of both sides in `w`);
* `WeakDivZeroH5`: a `P₀`-fixed `H^5` field is weakly divergence free.
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

/-- **Lemma 1** (source lines 261-288; no solenoidality).  For `w ∈ H^5`, `A = (w·∇)w ∈ H^3`
(`IsAdvectionTerm`) and `E ∈ H^3` with representative `(div w) w`, the Gaussian heat-divergence
orbit of the row tensor `w ⊗ w ∈ TensorH3` at age `θ > 0` equals `S(θ)(A + E)`, `S` the `H^3`
vector heat semigroup.  Proof idea: for cylinder-smooth `w`, `div(w ⊗ w) = (w·∇)w + (div w) w`
(pointwise calculus), the smooth heat-divergence identity
`actualHeatDivH3CLM_apply_ofCylSmooth` (`Lib/HeatCylinder/H3RoughOrbitContinuity.lean`) turns
`heatDiv` of the smooth tensor into the vector heat orbit of its row divergence; then extend to
all `w ∈ H^5` by density of smooth cylinder fields (`Lib/HeatCylinder/H3Density.lean`) and
continuity of both sides in `w` (`tensorH3Bilinear` bounded on `H^3`, the advection and
divergence terms bounded `H^5 → H^3` by the product estimate at level `4`). -/
def HeatDivIdentGeneral : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5)
    (A E : Cyl.H ℝ Cyl.Vec2 c 0 3),
    IsAdvectionTerm c w A →
    (hVal E =ᵐ[Cyl.cellμ c] fun z =>
      (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) •
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z) →
    ∀ θ : ℝ, 0 < θ →
      HeatCylinder.actualHeatDivH3Orbit hc
          (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
            (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ =
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (A + E)

/-- **Lemma 2** (weak divergence of a `P₀`-fixed `H^5` field vanishes; source lines 261-288).
If `w ∈ H^5` and its `H^3` restriction is fixed by `P₀`, then `∑_i (∂_i w)_i = 0` a.e. on the
cell.  Route: `P0H3CLM_value_mem_divFree` (`Lib/TrainB/P0H3Range.lean`) gives membership in
`Cyl.divFree`, then `Cyl.mem_divFree` and the weak derivative calculus. -/
def WeakDivZeroH5 : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5),
    P0H3CLM hc (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) =
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) →
    ∀ᵐ z ∂(Cyl.cellμ c), ∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i = 0

/-- `HeatDivIdent` from the two lemmas. -/
theorem heatDivIdent_of (h1 : HeatDivIdentGeneral) (h2 : WeakDivZeroH5) : HeatDivIdent := by
  intro c hc hc1 w A hP hA θ hθ
  have hz := h2 c hc w hP
  have e : Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
    rw [Cyl.wμ_ρwW, Cyl.wμ]
    have h1 : (fun z => ENNReal.ofReal (Cyl.ρw c z ^ (0 : ℝ))) = 1 := by
      funext z; simp
    rw [h1, MeasureTheory.withDensity_one]
  have hle : MeasureTheory.ae (Cyl.cellμ c) ≤
      MeasureTheory.ae (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [e]
  have h0 : hVal (0 : Cyl.H ℝ Cyl.Vec2 c 0 3) =ᵐ[Cyl.cellμ c] (0 : Plane → Cyl.Vec2) := by
    unfold hVal
    rw [map_zero]
    exact (Lp.coeFn_zero Cyl.Vec2 2 _).filter_mono hle
  have hE : hVal (0 : Cyl.H ℝ Cyl.Vec2 c 0 3) =ᵐ[Cyl.cellμ c] fun z =>
      (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) •
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z := by
    filter_upwards [hz, h0] with z hz0 h0z
    rw [h0z, hz0]
    simp
  have key := h1 c hc hc1 w A 0 hA hE θ hθ
  rw [key, add_zero]
  exact HeatCylinder.heatVecH3Semigroup_P0H3CLM_comm hc A

end UnforcedLeray.Short.PartI
