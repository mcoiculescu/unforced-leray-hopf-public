import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4

/-!
# Part I, task `PartI:T02/1/4/6/4/5`: the advection of the representative is a continuous `L²` path

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1, the mild solution and its spatial representative).

Target: `AdvectionL2Representative` (`Short/PartI/Sub/T02_1_4_6_4.lean`).

This file does not yet prove the target unconditionally.  It proves the assembly
`advectionL2Representative_of` from two analytic leaves, stated as `Prop`s:

* `AdvectionMemLpLeaf` (membership): for every `r ∈ [0,T]` the advection `(w r·∇) w r` of the
  smooth periodic representative lies in `L²(cell)`;
* `AdvectionLipLeaf` (uniform bound): there is `K ≥ 0` with
  `‖(w r·∇)w r - (w s·∇)w s‖_{L²(cell)} ≤ K ‖u r - u s‖_{H³}` for all `r, s ∈ [0,T]`.

The leaf bound is the Gallay-Slijepcevic estimate: `(a·∇)b` is bilinear, with the sup-norm of the
zero-order factor bounded by the `H²` norm (`smooth_cyl_sup_le_h2norm`) and the first derivatives
in `L²` through `vecH3CellDerivCLM`; the constant `K` is uniform because `t ↦ u t` is continuous on
the compact `[0,T]`.

Given the leaves, the path `G r := [(w (clamp r)·∇) w (clamp r)]` is continuous on `Icc 0 T`
(the `L²` distance is at most `K ‖u r - u s‖`, and `u` is continuous), and `G r` represents the
advection at each `r ∈ [0,T]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-! ### The two analytic leaves -/

/-- **Leaf A** (membership in `L²(cell)`).  For the smooth periodic spatial representative `w` of
the mild `H³` train `u`, each advection `(w r·∇) w r`, `r ∈ [0,T]`, is square integrable on the
cell.  Uses `IsSpatialRepOn.bounded` (sup bound of `w`) and `IsSpatialRepOn.represents` at the
order-one words (`L²` classes `vecH3CellDerivCLM`). -/
def AdvectionMemLpLeaf : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∀ r ∈ Icc (0 : ℝ) T, MemLp (Train.advection (w r)) 2 (Cyl.cellμ c)

/-- **Leaf B** (uniform `L²` Lipschitz bound in the `H³` norm).  For the smooth periodic
representative `w` of the mild `H³` train `u` there is a constant `K ≥ 0` such that for all
`r, s ∈ [0,T]` the `L²(cell)` norm of the advection difference is at most `K ‖u r - u s‖_{H³}`.
Proof idea: the difference is `(w r - w s)_j ∂_j w r + w_j s ∂_j (w r - w s)`; bound the first
factor in sup by `12 ‖·‖_{H²}` (`smooth_cyl_sup_le_h2norm`, `smooth_multiplier_L2_bound`) and
identify `‖w r - w s‖_{H²}` with the `H³` norm of `u r - u s` (`represents`, `forgetH3toH2`), and
bound the rest by `sup_{[0,T]} ‖u‖_{H³}`, finite by continuity of `u` on a compact interval. -/
def AdvectionLipLeaf : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)),
    IsMildTrain ν c T hν hc hc1 hT u → ∀ w : ℝ → Plane → Vec, IsSpatialRepOn c T u w →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r (hr : r ∈ Icc (0 : ℝ) T) s (hs : s ∈ Icc (0 : ℝ) T),
      eLpNorm (fun z => Train.advection (w r) z - Train.advection (w s) z) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖u ⟨r, hr⟩ - u ⟨s, hs⟩‖

/-! ### Assembly: the target from the two leaves -/

/-- The target `AdvectionL2Representative` follows from the membership leaf and the uniform
Lipschitz leaf.  The path is `G r = [adv (w (projIcc r))]`, continuous because the `L²` distance of
`F t` and `F t'` is bounded by `K ‖u t - u t'‖` and `u` is continuous on `Icc 0 T`. -/
theorem advectionL2Representative_of (hMem : AdvectionMemLpLeaf) (hLip : AdvectionLipLeaf) :
    AdvectionL2Representative := by
  intro ν c T hν hc hc1 hT u hu w hw
  obtain ⟨K, hK0, hK⟩ := hLip ν c T hν hc hc1 hT u hu w hw
  have hmem := hMem ν c T hν hc hc1 hT u hu w hw
  -- the `L²` class of the advection, indexed by the compact interval `Icc 0 T`
  let F : Icc (0 : ℝ) T → Cyl.L2v c := fun t => (hmem t.1 t.2).toLp (Train.advection (w t.1))
  have hFdist : ∀ t t' : Icc (0 : ℝ) T, ‖F t - F t'‖ ≤ K * ‖u t - u t'‖ := by
    intro t t'
    have h1 : F t - F t' = ((hmem t.1 t.2).sub (hmem t'.1 t'.2)).toLp
        (fun z => Train.advection (w t.1) z - Train.advection (w t'.1) z) :=
      (MemLp.toLp_sub (hmem t.1 t.2) (hmem t'.1 t'.2)).symm
    have hb := hK t.1 t.2 t'.1 t'.2
    rw [← ENNReal.ofReal_mul hK0] at hb
    have hN : 0 ≤ K * ‖u t - u t'‖ := mul_nonneg hK0 (norm_nonneg _)
    rw [h1, Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans (ENNReal.toReal_ofReal hN).le
  have hFcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have hu0 : Tendsto (fun t : Icc (0 : ℝ) T => ‖u t - u t₀‖) (𝓝 t₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (u.continuous.tendsto t₀)
    have hKu : Tendsto (fun t : Icc (0 : ℝ) T => K * ‖u t - u t₀‖) (𝓝 t₀) (𝓝 0) := by
      have := hu0.const_mul K
      rwa [mul_zero] at this
    exact tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun t => norm_nonneg _) (fun t => hFdist t t₀) hKu)
  refine ⟨fun r => F (projIcc 0 T hT.le r), (hFcont.comp continuous_projIcc).continuousOn, ?_⟩
  intro r hr
  have hp : projIcc 0 T hT.le r = ⟨r, hr⟩ := projIcc_of_mem hT.le hr
  show (F (projIcc 0 T hT.le r) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.advection (w r)
  rw [hp]
  exact (hmem r hr).coeFn_toLp

end UnforcedLeray.Short.PartI
