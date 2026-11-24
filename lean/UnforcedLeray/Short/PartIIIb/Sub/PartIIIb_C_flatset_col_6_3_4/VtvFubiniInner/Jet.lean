import UnforcedLeray.Units.B0579
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FubiniInner

/-- `∂_s` of a function of `(s, x)`. -/
def Ds (H : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ := fderiv ℝ H p ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))

/-- `∂_j` (spatial) of a function of `(s, x)`. -/
def Pj (j : Fin 2) (H : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ H p ((0 : ℝ), B0579.dir j)

theorem smooth_apply {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (w : ℝ × (ℝ × ℝ)) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ H p w) :=
  ((contDiff_infty_iff_fderiv.1 hH).2).clm_apply contDiff_const

theorem smooth_Ds {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (Ds H) :=
  smooth_apply hH _

theorem smooth_Pj (j : Fin 2) {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (Pj j H) :=
  smooth_apply hH _

theorem fderiv_apply_eq {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (p v w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fun q => fderiv ℝ H q w) p v = fderiv ℝ (fderiv ℝ H) p v w := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ H) p :=
    ((contDiff_infty_iff_fderiv.1 hH).2).differentiable (by simp) p
  have h2 : HasFDerivAt (fun q => fderiv ℝ H q w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ H) p)) p :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp p h1.hasFDerivAt
  rw [h2.fderiv]
  rfl

theorem sym_snd {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (p v w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fderiv ℝ H) p v w = fderiv ℝ (fderiv ℝ H) p w v := by
  have hs : IsSymmSndFDerivAt ℝ H p :=
    (hH.contDiffAt).isSymmSndFDerivAt (by simp)
  exact hs v w

theorem Ds_Pj {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (j : Fin 2) :
    Ds (Pj j H) = Pj j (Ds H) := by
  funext p
  unfold Ds Pj
  rw [fderiv_apply_eq hH, fderiv_apply_eq hH, sym_snd hH]

theorem hasDerivAt_s {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (s : ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun s' => H (s', y)) (Ds H (s, y)) s := by
  have hd : DifferentiableAt ℝ H (s, y) := hH.differentiable (by simp) _
  have hline : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × (ℝ × ℝ))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s y)
  exact hd.hasFDerivAt.comp_hasDerivAt s hline

theorem deriv_s {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (s : ℝ) (y : ℝ × ℝ) :
    deriv (fun s' => H (s', y)) s = Ds H (s, y) :=
  (hasDerivAt_s hH s y).deriv

theorem pd_eq {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (j : Fin 2) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd j (fun y => H (s, y)) x = Pj j H (s, x) := by
  have hd : DifferentiableAt ℝ H (s, x) := hH.differentiable (by simp) _
  have hin : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have hc := hd.hasFDerivAt.comp x hin
  unfold B0579.pd Pj
  have : (fun y : ℝ × ℝ => H (s, y)) = H ∘ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) := rfl
  rw [this, hc.fderiv]
  simp

theorem zero_Ds {H : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hz : ∀ p ∈ U, H p = 0) : ∀ p ∈ U, Ds H p = 0 := by
  intro p hp
  have : H =ᶠ[𝓝 p] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hp) hz
  unfold Ds
  rw [this.fderiv_eq]
  simp

theorem zero_Pj {H : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hz : ∀ p ∈ U, H p = 0) (j : Fin 2) : ∀ p ∈ U, Pj j H p = 0 := by
  intro p hp
  have : H =ᶠ[𝓝 p] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hp) hz
  unfold Pj
  rw [this.fderiv_eq]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FubiniInner
