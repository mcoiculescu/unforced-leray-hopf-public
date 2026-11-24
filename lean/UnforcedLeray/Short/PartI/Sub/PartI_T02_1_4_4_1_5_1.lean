import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5
import UnforcedLeray.Lib.SobolevC.CylDensity
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2

/-!
# Part I, `PartI:T02/1/4/4/1/5/1`: `HeatDivIdentGeneral` from the smooth case and continuous
representatives

Source of record: `the November 2 reference manuscript`, lines 3594-3625 (the
heat-divergence identity is proved first for smooth tensors and then completed by density in the
Sobolev scale; the tensor divergence is "interpreted by completion from smooth tensors", lines
1549, 3594).  Lines 261-288 (the mild solution lives in every `H^k`) supply the regularity class.

`HeatDivIdentGeneral` follows from
* `HeatDivSmoothCase`: the identity for `w ∈ H^5` having a smooth cylinder representative;
* `AdvDivContinuousReps`: the advection term `(w·∇)w` and the term `(div w) w` are the values of
  continuous maps `H^5 → H^3` (product estimate `H^4 × H^4 → H^3`, `AdvectionAt c 3`, and the
  bounded scalar product on `H^3`);
and density of smooth cylinder fields (`Sob.W.exists_seq_cylSmooth`), the continuity of the
bilinear tensor map and of the Gaussian divergence operator and of the semigroup.
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

/-- **Lemma S (smooth case)**, source lines 3594-3625: the heat-divergence identity of
`HeatDivIdentGeneral` for `w ∈ H^5` whose field is a.e. a smooth periodic cylinder field `u`.
Proof idea: for smooth `u`, `div(u ⊗ u) = (u·∇)u + (div u) u` pointwise;
`HeatCylinder.actualHeatDivH3CLM_apply_ofCylSmooth` (`Lib/HeatCylinder/H3RoughOrbitContinuity.lean`)
turns the actual heat-divergence orbit of the smooth tensor `ofCylSmooth (u ⊗ u)` into the smooth
Gaussian output `heatDivH3`, which is the vector heat orbit of the row divergence
(`NeedRowDivHeat`, `Short/PartI/Tasks/LocalClassicalBounded/TimeSmoothLeray/RepLeray/StressGenerator/StressOrbitIsHeat/Needed.lean`). -/
def HeatDivSmoothCase : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (w : Cyl.H ℝ Cyl.Vec2 c 0 5)
    (A E : Cyl.H ℝ Cyl.Vec2 c 0 3),
    (∃ u : Plane → Cyl.Vec2, Sob.IsCylSmooth c u ∧ hVal w =ᵐ[(Sob.cylinder c).μ] u) →
    IsAdvectionTerm c w A →
    (hVal E =ᵐ[Cyl.cellμ c] fun z =>
      (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) •
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z) →
    ∀ θ : ℝ, 0 < θ →
      HeatCylinder.actualHeatDivH3Orbit hc
          (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
            (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ =
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (A + E)

/-- **Lemma R (continuous representatives)**, source lines 261-288: the advection term
`A(w) = (w·∇)w` and the divergence term `E(w) = (div w) w` are continuous maps `H^5 → H^3`.
Proof idea: `A(w) = B(res w, res w)` with the bounded bilinear map `B : H^4 × H^4 → H^3` of
`AdvectionBase` (`Short/PartI/Sub/T02_1_4_4_1.lean`); `E(w) = ∑_i (∂_i w)_i · res w` with the
bounded scalar product `H^3 × H^3 → H^3` (`TrainB.scalarH3Bilinear`, `Lib/TrainB/WeakGraph.lean`)
applied to the `i`-th component of `∂_i w ∈ H^3` (`vectorH3Component`,
`Lib/TrainB/TensorBridge.lean`) and `res w ∈ H^3`, the `∂_i` and restriction being continuous
linear maps. -/
def AdvDivContinuousReps : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c),
    ∃ (𝒜 ℰ : Cyl.H ℝ Cyl.Vec2 c 0 5 → Cyl.H ℝ Cyl.Vec2 c 0 3),
      Continuous 𝒜 ∧ Continuous ℰ ∧ ∀ w : Cyl.H ℝ Cyl.Vec2 c 0 5,
        IsAdvectionTerm c w (𝒜 w) ∧
        (hVal (ℰ w) =ᵐ[Cyl.cellμ c] fun z =>
          (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i) •
            hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z)

set_option maxHeartbeats 1000000 in
theorem heatDivIdentGeneral_of (hS : HeatDivSmoothCase) (hR : AdvDivContinuousReps) :
    HeatDivIdentGeneral := by
  intro c hc hc1 w A E hA hE θ hθ
  obtain ⟨𝒜, ℰ, h𝒜, hℰ, hrep⟩ := hR c hc hc1
  have eA : ∀ v : Cyl.H ℝ Cyl.Vec2 c 0 5, ∀ A' : Cyl.H ℝ Cyl.Vec2 c 0 3,
      IsAdvectionTerm c v A' → A' = 𝒜 v := fun v A' h => by
    apply hVal_ext
    exact h.trans (hrep v).1.symm
  have eE : ∀ v : Cyl.H ℝ Cyl.Vec2 c 0 5, ∀ E' : Cyl.H ℝ Cyl.Vec2 c 0 3,
      (hVal E' =ᵐ[Cyl.cellμ c] fun z =>
        (∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i v) z i) •
          hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3) z) →
      E' = ℰ v := fun v E' h => by
    apply hVal_ext
    exact h.trans (hrep v).2.symm
  obtain ⟨y, hy, hlim⟩ := Sob.W.exists_seq_cylSmooth (𝕜 := ℝ) (F := Cyl.Vec2) (k := 5)
    (ρ := Cyl.ρwW c ^ (0 : ℝ)) (p := 2) hc (by simp) w
  have hΦ : Continuous fun v : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      HeatCylinder.actualHeatDivH3Orbit hc
        (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)
          (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ := by
    have : (fun v : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
        HeatCylinder.actualHeatDivH3Orbit hc
          (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)
            (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ) =
        fun v => HeatCylinder.actualHeatDivH3CLM hc hθ
          (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)
            (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)) := by
      funext v
      unfold HeatCylinder.actualHeatDivH3Orbit
      rw [dif_pos hθ]
    rw [this]
    have hr : Continuous (fun v : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
        (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)) :=
      (Sob.W.restrict (by norm_num : 3 ≤ 5)).continuous
    exact (HeatCylinder.actualHeatDivH3CLM hc hθ).continuous.comp
      (((tensorH3Bilinear hc1).continuous.comp hr).clm_apply hr)
  have hΨ : Continuous fun v : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (𝒜 v + ℰ v) :=
    (HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc).continuous.comp (h𝒜.add hℰ)
  have hseq : ∀ j, HeatCylinder.actualHeatDivH3Orbit hc
      (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) (y j) : Cyl.H ℝ Cyl.Vec2 c 0 3)
        (Sob.W.restrict (by norm_num : 3 ≤ 5) (y j) : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ =
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (𝒜 (y j) + ℰ (y j)) :=
    fun j => hS c hc hc1 (y j) (𝒜 (y j)) (ℰ (y j)) (hy j) (hrep (y j)).1 (hrep (y j)).2 θ hθ
  have t1 := (hΦ.tendsto w).comp hlim
  have t2 := (hΨ.tendsto w).comp hlim
  have e : (fun v : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      HeatCylinder.actualHeatDivH3Orbit hc
        (tensorH3Bilinear hc1 (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)
          (Sob.W.restrict (by norm_num : 3 ≤ 5) v : Cyl.H ℝ Cyl.Vec2 c 0 3)) θ) ∘ y =
      (fun v : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
        HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (𝒜 v + ℰ v)) ∘ y := by
    funext j; exact hseq j
  rw [e] at t1
  rw [eA w A hA, eE w E hE]
  exact tendsto_nhds_unique t1 t2

end UnforcedLeray.Short.PartI
