import UnforcedLeray.Units.B0140
import UnforcedLeray.Lib.Train.PeriodizedVortex
import UnforcedLeray.Units.B0238.Partials

/-!
# Part I, task `PartI:T06`: the train error equation

Source of record: `the November 2 reference manuscript`, lines 326-336
("the residual of the periodized vortex is `div Q`, `Q = sum_{i≠j} V_i ⊗ V_j`").

For the train `v`, `p` (`B0140.TrainSol`) and the periodized isolated vortices `V_c = Train.Vc`,
`p_c = Train.pc`, the error `e = v - V_c` and `π = p - p_c` satisfy
`∂ₛ e + (v·∇v - V_c·∇V_c) - νΔe + ∇π = -div Q_c` for `s > 0`.
The transport bracket is written as `Train.advection (v s) z - Train.advection (V_c s) z`.
This is the bilinear expansion `(V_c·∇)e + (e·∇)V_c + (e·∇)e`, because `v = V_c + e`.

Proof. Subtract the evolution form of the residual identity of `V_c` (`Train.Vc_hasDerivAt`)
from the momentum equation of the train. Every partial derivative involved is a genuine
derivative at every point: the train is jointly smooth for `s ≥ 0` (`smooth_v`, `smooth_p`), and
`V_c`, `p_c` have genuine partials (`Train.Vc_classical`). Hence `deriv`, `partialQ`,
`partialEta`, `vecLaplacian` and `gradS` are linear on the differences.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI.TrainErrorEquation

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec toVec)

/-- Horizontal differentiability at every point. -/
abbrev LineQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Plane → E) : Prop :=
  ∀ w : Plane, DifferentiableAt ℝ (fun t : ℝ => f (t, w.2)) w.1

/-- Vertical differentiability at every point. -/
abbrev LineE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Plane → E) : Prop :=
  ∀ w : Plane, DifferentiableAt ℝ (fun t : ℝ => f (w.1, t)) w.2

/-- Both first partials of a scalar field are genuine derivatives everywhere. -/
abbrev G1 (f : Plane → ℝ) : Prop := LineQ f ∧ LineE f

/-- The first partials, and the second partials used by the Laplacian, are genuine everywhere. -/
abbrev G2 (f : Plane → ℝ) : Prop := G1 f ∧ LineQ (partialQ f) ∧ LineE (partialEta f)

theorem partialQ_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Plane → E} (hf : LineQ f) (hg : LineQ g) (w : Plane) :
    partialQ (fun u => f u - g u) w = partialQ f w - partialQ g w :=
  ((hf w).hasDerivAt.sub (hg w).hasDerivAt).deriv

theorem partialEta_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Plane → E} (hf : LineE f) (hg : LineE g) (w : Plane) :
    partialEta (fun u => f u - g u) w = partialEta f w - partialEta g w :=
  ((hf w).hasDerivAt.sub (hg w).hasDerivAt).deriv

theorem lineQ_of_contDiff {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) : LineQ F := by
  intro w
  have h : DifferentiableAt ℝ F (w.1, w.2) := hF.differentiable (by simp) _
  exact h.comp w.1 (differentiableAt_id.prodMk (differentiableAt_const w.2))

theorem lineE_of_contDiff {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) : LineE F := by
  intro w
  have h : DifferentiableAt ℝ F (w.1, w.2) := hF.differentiable (by simp) _
  exact h.comp w.2 ((differentiableAt_const w.1).prodMk differentiableAt_id)

theorem partialQ_contDiff {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialQ F) := by
  have h : partialQ F = fun w => fderiv ℝ F w (1, 0) :=
    funext fun w => UnforcedLeray.B0238.partialQ_eq_fderiv (hF.differentiable (by simp) w)
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem partialEta_contDiff {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialEta F) := by
  have h : partialEta F = fun w => fderiv ℝ F w (0, 1) :=
    funext fun w => UnforcedLeray.B0238.partialEta_eq_fderiv (hF.differentiable (by simp) w)
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem G2_of_contDiff {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) : G2 F :=
  ⟨⟨lineQ_of_contDiff hF, lineE_of_contDiff hF⟩, lineQ_of_contDiff (partialQ_contDiff hF),
    lineE_of_contDiff (partialEta_contDiff hF)⟩

theorem G1_of_contDiff {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) : G1 F :=
  ⟨lineQ_of_contDiff hF, lineE_of_contDiff hF⟩

/-- A slice `f s` of a jointly smooth field on `[0, ∞) × ℝ²` is smooth. -/
theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Plane → E}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ici 0 ×ˢ univ)) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (f s) := by
  have h := hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
    (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
  exact contDiffOn_univ.1 h

/-- The train velocity is differentiable in time at every point, for `s > 0`. -/
theorem differentiableAt_time {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s)
    (z : Plane) : DifferentiableAt ℝ (fun t => tr.v t z) s := by
  have hopen : Ioi (0 : ℝ) ×ˢ (univ : Set Plane) ∈ 𝓝 (s, z) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, mem_univ z⟩
  have hsub : Ioi (0 : ℝ) ×ˢ (univ : Set Plane) ⊆ Ici 0 ×ˢ univ :=
    Set.prod_mono Ioi_subset_Ici_self Subset.rfl
  have hc : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (s, z) :=
    tr.isTrain.smooth_v.contDiffAt (Filter.mem_of_superset hopen hsub)
  have hd : DifferentiableAt ℝ (fun x : ℝ × Plane => tr.v x.1 x.2) (s, z) :=
    hc.differentiableAt (by simp)
  have hf : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) s :=
    differentiableAt_id.prodMk (differentiableAt_const z)
  exact hd.comp s hf

/-! ### Regularity of `V_c` and `p_c` (from `Train.Vc_classical`) -/

theorem G2_Vc0 {ν c s : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) :
    G2 (fun w => Train.Vc ν c s w 0) :=
  ⟨⟨fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).1,
      fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.1⟩,
    fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.2.1,
    fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.2.2.1⟩

theorem G2_Vc1 {ν c s : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) :
    G2 (fun w => Train.Vc ν c s w 1) :=
  ⟨⟨fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.1,
      fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.1⟩,
    fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.2.2.2.1,
    fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.2.2.2.2.1⟩

theorem G1_pc {ν c s : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) :
    G1 (Train.pc ν c s) :=
  ⟨fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.2.2.2.2.2.1,
    fun w => HasDerivAt.differentiableAt (Train.Vc_classical hν hc hs w).2.2.2.2.2.2.2.2.2.1⟩

/-! ### Linearity of the operators on differences -/

theorem lapS_sub_eq {f g : Plane → ℝ} (hf : G2 f) (hg : G2 g) (z : Plane) :
    Train.lapS (fun u => f u - g u) z = Train.lapS f z - Train.lapS g z := by
  have h1 : partialQ (fun u => f u - g u) = fun w => partialQ f w - partialQ g w :=
    funext (partialQ_sub_eq hf.1.1 hg.1.1)
  have h2 : partialEta (fun u => f u - g u) = fun w => partialEta f w - partialEta g w :=
    funext (partialEta_sub_eq hf.1.2 hg.1.2)
  unfold Train.lapS
  rw [h1, h2, partialQ_sub_eq hf.2.1 hg.2.1 z, partialEta_sub_eq hf.2.2 hg.2.2 z]
  ring

theorem vecLaplacian_sub_eq {u u' : Plane → Vec} (hu0 : G2 (fun w => u w 0))
    (hu1 : G2 (fun w => u w 1)) (hv0 : G2 (fun w => u' w 0)) (hv1 : G2 (fun w => u' w 1))
    (z : Plane) :
    Train.vecLaplacian (fun w => u w - u' w) z =
      Train.vecLaplacian u z - Train.vecLaplacian u' z := by
  have h0 := lapS_sub_eq hu0 hv0 z
  have h1 := lapS_sub_eq hu1 hv1 z
  unfold Train.vecLaplacian
  rw [← Train.toVec_sub, Prod.mk_sub_mk]
  congr 1
  rw [Prod.mk.injEq]
  exact ⟨h0, h1⟩

theorem gradS_sub_eq {P Q : Plane → ℝ} (hP : G1 P) (hQ : G1 Q) (z : Plane) :
    Train.gradS (fun w => P w - Q w) z = Train.gradS P z - Train.gradS Q z := by
  unfold Train.gradS
  rw [partialQ_sub_eq hP.1 hQ.1 z, partialEta_sub_eq hP.2 hQ.2 z, ← Train.toVec_sub]
  rfl

/-! ### The main theorem -/

/-- **The train error equation** (tex lines 326-336, `sct:train`). For `s > 0`, the error
`e = v - V_c` and `π = p - p_c` of the train satisfy
`∂ₛe + (v·∇v - V_c·∇V_c) - νΔe + ∇π = -div Q_c` at every point `z`, with
`Q_c = ∑_{i≠j} V_i ⊗ V_j` (`Train.Qc`). -/
theorem train_error_equation {ν c : ℝ} (tr : B0140.TrainSol ν c) (hν : 0 < ν) (hc : c ≠ 0)
    (s : ℝ) (hs : 0 < s) (z : Cyl.Plane) :
    deriv (fun t => tr.v t z - Train.Vc ν c t z) s
      + (Train.advection (tr.v s) z - Train.advection (Train.Vc ν c s) z)
      - ν • Train.vecLaplacian (fun w => tr.v s w - Train.Vc ν c s w) z
      + Train.gradS (fun w => tr.p s w - Train.pc ν c s w) z
      = -Train.matDiv (Train.Qc ν c s) z := by
  have hs0 : (0 : ℝ) ≤ s := hs.le
  have hmom : Train.momentumResidual ν tr.v tr.p s z = 0 := tr.isTrain.momentum s hs z
  unfold Train.momentumResidual at hmom
  have hVc := Train.Vc_hasDerivAt hν hc hs0 z
  have hVt := (differentiableAt_time tr hs z).hasDerivAt
  have hde : deriv (fun t => tr.v t z - Train.Vc ν c t z) s =
      deriv (fun t => tr.v t z) s -
        (ν • Train.vecLaplacian (Train.Vc ν c s) z - Train.advection (Train.Vc ν c s) z
          - Train.gradS (Train.pc ν c s) z + Train.matDiv (Train.Qc ν c s) z) :=
    (hVt.sub hVc).deriv
  have hL := vecLaplacian_sub_eq
    (G2_of_contDiff (UnforcedLeray.B0238.contDiff_comp_apply
      (contDiff_slice (f := tr.v) tr.isTrain.smooth_v hs0) 0))
    (G2_of_contDiff (UnforcedLeray.B0238.contDiff_comp_apply
      (contDiff_slice (f := tr.v) tr.isTrain.smooth_v hs0) 1))
    (G2_Vc0 hν hc hs0) (G2_Vc1 hν hc hs0) z
  have hG := gradS_sub_eq
    (G1_of_contDiff (contDiff_slice (f := tr.p) tr.isTrain.smooth_p hs0))
    (G1_pc hν hc hs0) z
  rw [hde, hL, hG]
  linear_combination (norm := module) hmom

end UnforcedLeray.Short.PartI.TrainErrorEquation
