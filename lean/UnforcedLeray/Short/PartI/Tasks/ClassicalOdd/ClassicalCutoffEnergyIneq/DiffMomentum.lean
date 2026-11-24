import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.IntegrandDecomp

/-!
# Part I, task `PartI:T02/3/11`: `CcDiffMomentum` (leaf, equation for the difference)

Source of record: `the November 2 reference manuscript`, lines 276-288 (energy
method: the difference `w = v - v'` of two classical solutions).
Target: `ccDiffMomentum`, the proof of `CcDiffMomentum` (`Short/PartI/Sub/T02_3_11.lean`, line 179).

Route. Fix `s ∈ (0, T)` and `z`. The slices `v s`, `v' s`, `p s`, `p' s` are `C^∞` by `hS`.
The time derivative of `t ↦ w t z` at `s` is the difference of the time derivatives of `v` and `v'`,
each differentiable at `s` because `v` and `v'` are smooth on `[0, T] × ℝ²` and `s` is an interior
point. Subtracting the two momentum equations (`Train.momentumResidual ν v p s z = 0` and the same for
`v'`, `p'`) and using the difference identities `cid_vecLaplacian_sub`, `cid_gradS_sub`,
`cid_advection_sub` from `Tasks/TrainCutoffEnergyProof/IntegrandDecomp.lean` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Differentiability in the time variable at an interior time `s ∈ (0, T)` of a field that is
`C^∞` on `[0, T] × ℝ²` (the slice `t ↦ u t z` at a fixed point `z`). -/
theorem ccDM_diff_time {T s : ℝ} {u : ℝ → Plane → Vec}
    (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) (Icc 0 T ×ˢ univ))
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    DifferentiableAt ℝ (fun t => u t z) s := by
  have h2 : (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) ∈ 𝓝 (s, z) :=
    prod_mem_nhds (Icc_mem_nhds hs.1 hs.2) univ_mem
  have h3 : DifferentiableAt ℝ (fun x : ℝ × Plane => u x.1 x.2) (s, z) :=
    (hu.differentiableOn (by norm_num)).differentiableAt h2
  have hline : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) s :=
    (differentiableAt_id).prodMk (differentiableAt_const z)
  exact h3.comp s hline

/-- **`PartI:T02/3/11`, auxiliary `CcDiffMomentum`**: for `s ∈ (0, T)` and every `z`,
`∂_s w = -(v·∇)w - (w·∇)v' + νΔw - ∇π` with `w = v - v'` and `π = p - p'`. -/
theorem ccDiffMomentum (hS : CcSliceSmooth) : CcDiffMomentum := by
  intro ν c T M v v' p p' h s hs z
  have hs' : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
  obtain ⟨hv, hp⟩ := hS ν c T v p h.cl s hs'
  obtain ⟨hv', hp'⟩ := hS ν c T v' p' h.cl' s hs'
  have hw_eq : ccDiffV v v' s = fun x => v s x - v' s x := rfl
  have hP_eq : ccDiffP p p' s = fun x => p s x - p' s x := rfl
  have hD : deriv (fun t => ccDiffV v v' t z) s =
      deriv (fun t => v t z) s - deriv (fun t => v' t z) s :=
    deriv_sub (ccDM_diff_time h.cl.smooth_v hs z) (ccDM_diff_time h.cl'.smooth_v hs z)
  have M := h.cl.momentum s hs z
  have M' := h.cl'.momentum s hs z
  unfold Train.momentumResidual at M M'
  have hadv := cid_advection_sub hv hv' hw_eq z
  rw [hD, cid_vecLaplacian_sub hv hv' hw_eq z, cid_gradS_sub hp hp' hP_eq z]
  linear_combination (norm := module) M - M' - hadv

end UnforcedLeray.Short.PartI
