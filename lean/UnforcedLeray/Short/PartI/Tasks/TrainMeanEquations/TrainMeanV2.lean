import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part I, task `PartI:T01/2`: the mean of the horizontal velocity vanishes

Source of record: `the November 2 reference manuscript`, lines 399-404
(`\overline v_2 = 0`, "follows from divergence and finite energy").

Route. Write `v₂ = ∂_q ψ` (`IsTrain.stream`) and `v₁ = -∂_η ψ`.

* (a) `q ↦ ψ(q, η)` is `c`-periodic: the difference `D(η) = ψ(q+c, η) - ψ(q, η)` has
  `∂_η D = -v₁(q+c, η) + v₁(q, η) = 0` by `periodic_v`, so `D` is constant in `η`; it tends to
  `0` as `η → +∞` by `stream_decay` (translation in `q` does not change `|z.2|`), so `D = 0`.
* (b) The `q`-integral of `v₂(·, η) = ∂_q ψ(·, η)` over `(-c/2, c/2]` is
  `ψ(c/2, η) - ψ(-c/2, η) = 0` by the fundamental theorem of calculus and (a).

Only the `η`-derivative of `ψ` is used in (a), so the two-dimensional constancy argument is not
needed. The `q`-integrand is continuous (from `smooth_v`), which gives interval integrability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **`PartI:T01/2`.** The horizontal average of `v₂` vanishes (`sct:mean`, `\bar v₂ = 0`). -/
theorem trainMeanV2 : TrainMeanV2 := by
  intro ν c hν hc tr s hs η
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs.le
  have hstream := tr.isTrain.stream s hs.le
  have hper : ∀ z : Plane, tr.v s (z.1 + c, z.2) = tr.v s z := tr.isTrain.periodic_v s hs.le
  have hper0 : ∀ a y : ℝ, tr.v s (a + c, y) 0 = tr.v s (a, y) 0 := fun a y =>
    congrArg (fun w : Vec => w 0) (hper (a, y))
  -- the η-derivative of the stream is `-v₁`
  have hHasY : ∀ a y : ℝ, HasDerivAt (fun y' => tr.ψ s (a, y')) (-(tr.v s (a, y) 0)) y := by
    intro a y
    have hd : DifferentiableAt ℝ (fun y' => tr.ψ s (a, y')) y :=
      (hψd (a, y)).comp y ((differentiableAt_const a).prodMk differentiableAt_id)
    have he : tr.v s (a, y) 0 = -deriv (fun y' => tr.ψ s (a, y')) y := by
      rw [hstream (a, y)]
      rfl
    rw [he, neg_neg]
    exact hd.hasDerivAt
  -- the q-derivative of the stream is `v₂`
  have hHasX : ∀ x y : ℝ, HasDerivAt (fun x' => tr.ψ s (x', y)) (tr.v s (x, y) 1) x := by
    intro x y
    have hd : DifferentiableAt ℝ (fun x' => tr.ψ s (x', y)) x :=
      (hψd (x, y)).comp x (differentiableAt_id.prodMk (differentiableAt_const y))
    have he : tr.v s (x, y) 1 = deriv (fun x' => tr.ψ s (x', y)) x := by
      rw [hstream (x, y)]
      rfl
    rw [he]
    exact hd.hasDerivAt
  -- (a) the stream is `c`-periodic in `q`
  have hP : ∀ q y : ℝ, tr.ψ s (q + c, y) = tr.ψ s (q, y) := by
    intro q y
    have hD : ∀ y' : ℝ, HasDerivAt (fun y'' => tr.ψ s (q + c, y'') - tr.ψ s (q, y'')) 0 y' := by
      intro y'
      have h := (hHasY (q + c) y').sub (hHasY q y')
      have e : -(tr.v s (q + c, y') 0) - -(tr.v s (q, y') 0) = 0 := by
        rw [hper0 q y']
        ring
      rw [e] at h
      exact h
    have hconst : ∀ y' : ℝ,
        tr.ψ s (q + c, y') - tr.ψ s (q, y') = tr.ψ s (q + c, 0) - tr.ψ s (q, 0) :=
      fun y' => is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
        (fun t => (hD t).deriv) y' 0
    have hl : ∀ a : ℝ, Tendsto (fun y' : ℝ => tr.ψ s (a, y')) atTop (𝓝 0) := by
      intro a
      have hmap : Tendsto (fun y' : ℝ => ((a, y') : Plane)) atTop
          (comap (fun z : Plane => |z.2|) atTop) := by
        rw [tendsto_comap_iff]
        exact tendsto_abs_atTop_atTop
      exact (tr.isTrain.stream_decay s hs.le).comp hmap
    have hlim : Tendsto (fun y' : ℝ => tr.ψ s (q + c, y') - tr.ψ s (q, y')) atTop (𝓝 0) := by
      have h := (hl (q + c)).sub (hl q)
      simpa only [sub_zero] using h
    have hzero : tr.ψ s (q + c, 0) - tr.ψ s (q, 0) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds (Tendsto.congr hconst hlim)
    exact sub_eq_zero.1 ((hconst y).trans hzero)
  -- the horizontal integrand `v₂(·, η)` is continuous
  have hcontX : ∀ y : ℝ, Continuous (fun x : ℝ => tr.v s (x, y) 1) := by
    intro y
    have hC : ContinuousOn (fun w : ℝ × Plane => tr.v w.1 w.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hmaps : ∀ x : ℝ, ((s, (x, y)) : ℝ × Plane) ∈ Ici 0 ×ˢ (univ : Set Plane) :=
      fun x => ⟨hs.le, mem_univ _⟩
    have hcomp : Continuous (fun x : ℝ => tr.v s (x, y)) :=
      hC.comp_continuous (f := fun x : ℝ => ((s, (x, y)) : ℝ × Plane))
        (continuous_const.prodMk (continuous_id.prodMk continuous_const)) hmaps
    have hw : Continuous (fun w : Vec => w 1) :=
      PiLp.continuous_apply 2 _ 1
    exact hw.comp hcomp
  -- (b) the fundamental theorem of calculus in `q`
  have hFTC : ∀ y : ℝ, ∫ q in Ioc (-c / 2) (c / 2), tr.v s (q, y) 1 =
      tr.ψ s (c / 2, y) - tr.ψ s (-c / 2, y) := by
    intro y
    rw [← intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => tr.ψ s (x, y))
      (fun x _ => hHasX x y) ((hcontX y).intervalIntegrable _ _)
  have hP' : tr.ψ s (c / 2, η) = tr.ψ s (-c / 2, η) := by
    have h := hP (-c / 2) η
    rwa [show -c / 2 + c = c / 2 by ring] at h
  show c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), tr.v s (q, η) 1 = 0
  rw [hFTC η, hP', sub_self, smul_zero]

end UnforcedLeray.Short.PartI
