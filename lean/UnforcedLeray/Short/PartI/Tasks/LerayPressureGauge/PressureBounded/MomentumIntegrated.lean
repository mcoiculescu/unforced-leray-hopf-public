import UnforcedLeray.Short.PartI.Sub.T02_2_3
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.SlicePartials

/-!
# Part I, task `PartI:T02/2/3/8`: the momentum equation integrated in time

Source of record: `the November 2 reference manuscript`, line 447 (the momentum
equation, integrated over `[a,b]`) and line 277.  Target `pbMomentumIntegrated : PbMomentumIntegrated`
(the definition with its proof sketch is in `Sub/T02_2_3.lean`).

## Proof

Fix `a ≤ b` in `[0,T]` and `z`.  Write `X σ = advection (v σ) z - ν • vecLaplacian (v σ) z` and
`Y σ = gradS (p σ) z`.

1. Continuity on `[0,T]`.  For a jointly `C^∞` family `K` on `[0,T] × ℝ²`, the slices `σ ↦ K σ z`,
   `σ ↦ ∂_q (K σ) z`, `σ ↦ ∂_η (K σ) z`, `σ ↦ Δ(K σ) z` are continuous on `[0,T]`
   (`pbMI_slice`, from `pbSlicePartials` applied twice).  Hence `Y` and `X` are continuous on
   `[0,T]` (`pbMI_adv_cont`, `pbMI_lap_cont`), so `Y` and `X` are interval integrable on `[a,b]`.
2. Interior identity.  For `σ ∈ (0,T)` the function `t ↦ v t z` is differentiable at `σ`
   (`pbMI_diff_time`, joint smoothness on the open set `(0,T) × ℝ²`), and the momentum identity
   gives `deriv (fun t => v t z) σ = -X σ - Y σ` (`key`).
3. Fundamental theorem of calculus, `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, applied
   to the continuous function `t ↦ v t z` on `[a,b]` with derivative `-X - Y` on `(a,b) ⊂ (0,T)`,
   gives `∫_a^b (-X - Y) = v b z - v a z`.  Splitting the integral (`integral_sub`, `integral_neg`)
   and rearranging yields the claimed formula.

No placeholder proofs and no extra declarations.  Helper names start with `pbMI`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- Restriction of a jointly smooth family to a fixed `z` is continuous in time on `[0,T]`. -/
theorem pbMI_pt {T : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × Plane → E} (hF : ContDiffOn ℝ ∞ F (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (z : Plane) : ContinuousOn (fun σ => F (σ, z)) (Icc (0 : ℝ) T) :=
  hF.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
    (fun _ hσ => ⟨hσ, mem_univ z⟩)

/-- A vector whose two coordinates are continuous is continuous. -/
theorem pbMI_toVec_cont {f g : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun σ => toVec (f σ, g σ)) s :=
  Train.toVecL.continuous.comp_continuousOn (hf.prodMk hg)

/-- Slices of a jointly smooth family and of its first and second partials are continuous in
time at each fixed `z`.  Uses `pbSlicePartials` for `∂_q`, `∂_η`, and again for the second
partials. -/
theorem pbMI_slice {T : ℝ} (hT : 0 < T) {K : ℝ → Plane → ℝ}
    (hK : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => K x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (z : Plane) :
    ContinuousOn (fun σ => K σ z) (Icc (0 : ℝ) T) ∧
    ContinuousOn (fun σ => Cyl.partialQ (K σ) z) (Icc (0 : ℝ) T) ∧
    ContinuousOn (fun σ => Cyl.partialEta (K σ) z) (Icc (0 : ℝ) T) ∧
    ContinuousOn (fun σ => Train.lapS (K σ) z) (Icc (0 : ℝ) T) := by
  obtain ⟨hQ, hE⟩ := pbSlicePartials T K hT hK
  have hQQ := (pbSlicePartials T (fun σ w => Cyl.partialQ (K σ) w) hT hQ).1
  have hEE := (pbSlicePartials T (fun σ w => Cyl.partialEta (K σ) w) hT hE).2
  exact ⟨pbMI_pt hK z, pbMI_pt hQ z, pbMI_pt hE z, (pbMI_pt hQQ z).add (pbMI_pt hEE z)⟩

/-- Each coordinate of a jointly smooth vector field is jointly smooth. -/
theorem pbMI_comp {T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2 i) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hv

/-- The transport term `(v·∇)v` is continuous in time at a fixed point. -/
theorem pbMI_adv_cont {T : ℝ} (hT : 0 < T) {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (z : Plane) :
    ContinuousOn (fun σ => Train.advection (v σ) z) (Icc (0 : ℝ) T) := by
  obtain ⟨a0, q0, e0, -⟩ := pbMI_slice (K := fun σ w => v σ w 0) hT (pbMI_comp (v := v) hv 0) z
  obtain ⟨a1, q1, e1, -⟩ := pbMI_slice (K := fun σ w => v σ w 1) hT (pbMI_comp (v := v) hv 1) z
  unfold Train.advection
  refine pbMI_toVec_cont ?_ ?_
  · exact (a0.mul q0).add (a1.mul e0)
  · exact (a0.mul q1).add (a1.mul e1)

/-- The vector Laplacian is continuous in time at a fixed point. -/
theorem pbMI_lap_cont {T : ℝ} (hT : 0 < T) {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (z : Plane) :
    ContinuousOn (fun σ => Train.vecLaplacian (v σ) z) (Icc (0 : ℝ) T) := by
  obtain ⟨-, -, -, l0⟩ := pbMI_slice (K := fun σ w => v σ w 0) hT (pbMI_comp (v := v) hv 0) z
  obtain ⟨-, -, -, l1⟩ := pbMI_slice (K := fun σ w => v σ w 1) hT (pbMI_comp (v := v) hv 1) z
  unfold Train.vecLaplacian
  exact pbMI_toVec_cont l0 l1

/-- A jointly smooth family is differentiable in time at interior times, at each fixed `z`. -/
theorem pbMI_diff_time {T : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Plane → E}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) T) (z : Plane) :
    DifferentiableAt ℝ (fun t => F t z) σ := by
  have hopen : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ∈ 𝓝 (σ, z) :=
    IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) ⟨hσ, mem_univ z⟩
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    prod_mono Ioo_subset_Icc_self subset_rfl
  have hmem : (σ, z) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    ⟨Ioo_subset_Icc_self hσ, mem_univ z⟩
  have hd : DifferentiableAt ℝ (fun x : ℝ × Plane => F x.1 x.2) (σ, z) :=
    (hF.differentiableOn (by simp) (σ, z) hmem).differentiableAt
      (Filter.mem_of_superset hopen hsub)
  have hp : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) σ :=
    differentiableAt_id.prodMk (differentiableAt_const z)
  exact hd.comp σ hp

/-- **The momentum equation integrated in time** (source line 447): for `0 ≤ a ≤ b ≤ T`, the pressure
gradient is interval integrable in time, and its time integral equals `-(v b - v a)` minus the time
integral of the transport and viscous terms. -/
theorem pbMomentumIntegrated : PbMomentumIntegrated := by
  intro ν c T v p h a ha b hb hab z
  have hT : 0 < T := h.T_pos
  have hS : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    h.classical.smooth_v
  have hP : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    h.classical.smooth_p
  have hsub : uIcc a b ⊆ Icc (0 : ℝ) T := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc ha.1 hb.2
  -- continuity in time on `[0,T]` of the pressure gradient and of the viscous/transport terms
  have hYc : ContinuousOn (fun σ => Train.gradS (p σ) z) (Icc (0 : ℝ) T) := by
    obtain ⟨-, q, e, -⟩ := pbMI_slice (K := p) hT hP z
    unfold Train.gradS
    exact pbMI_toVec_cont q e
  have hXc : ContinuousOn (fun σ => Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)
      (Icc (0 : ℝ) T) :=
    (pbMI_adv_cont (v := v) hT hS z).sub
      ((continuous_const_smul ν : Continuous fun x : Vec => ν • x).comp_continuousOn
        (pbMI_lap_cont (v := v) hT hS z))
  have hGc : ContinuousOn
      (fun σ => -(Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z) - Train.gradS (p σ) z)
      (Icc (0 : ℝ) T) :=
    hXc.neg.sub hYc
  have hYint : IntervalIntegrable (fun σ => Train.gradS (p σ) z) volume a b :=
    (hYc.mono hsub).intervalIntegrable
  have hXint : IntervalIntegrable
      (fun σ => Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z) volume a b :=
    (hXc.mono hsub).intervalIntegrable
  -- the momentum identity in the interior, solved for the time derivative
  have key : ∀ x ∈ Ioo (0 : ℝ) T, deriv (fun t => v t z) x =
      -(Train.advection (v x) z - ν • Train.vecLaplacian (v x) z) - Train.gradS (p x) z := by
    intro x hx
    have e := h.classical.momentum x hx z
    unfold Train.momentumResidual at e
    calc deriv (fun t => v t z) x
        = (deriv (fun t => v t z) x + Train.advection (v x) z - ν • Train.vecLaplacian (v x) z
            + Train.gradS (p x) z) - (Train.advection (v x) z - ν • Train.vecLaplacian (v x) z)
            - Train.gradS (p x) z := by abel
      _ = -(Train.advection (v x) z - ν • Train.vecLaplacian (v x) z) - Train.gradS (p x) z := by
          rw [e, zero_sub]
  -- fundamental theorem of calculus for `t ↦ v t z`
  have hFTC : ∫ σ in a..b, (-(Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)
      - Train.gradS (p σ) z) = v b z - v a z := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t => v t z) hab
      ((pbMI_pt hS z).mono (Icc_subset_Icc ha.1 hb.2)) ?_ (hGc.mono hsub).intervalIntegrable
    intro x hx
    have hx0 : x ∈ Ioo (0 : ℝ) T := ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
    have h2 := (pbMI_diff_time (F := v) hS hx0 z).hasDerivAt
    rw [key x hx0] at h2
    exact h2
  have hneg : IntervalIntegrable
      (fun σ => -(Train.advection (v σ) z - ν • Train.vecLaplacian (v σ) z)) volume a b :=
    hXint.neg
  have hsplit := intervalIntegral.integral_sub hneg hYint
  rw [intervalIntegral.integral_neg] at hsplit
  rw [hsplit] at hFTC
  refine ⟨hYint, ?_⟩
  rw [← hFTC]
  abel

end UnforcedLeray.Short.PartI
