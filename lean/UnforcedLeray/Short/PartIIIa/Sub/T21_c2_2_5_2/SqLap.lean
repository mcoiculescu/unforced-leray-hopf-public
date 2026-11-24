import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_2

/-!
# `PartIII-a:T21/c2/2/5/2`, leaf `DiffSqLap`: `Δ(g²) = 2gΔg + 2|∇g|²` (SP 2950-2954)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem sqlap_pd_mul {f h : B0579.Plane → ℝ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun y => f y * h y) x = f x * B0579.pd j h x + h x * B0579.pd j f x := by
  unfold B0579.pd
  rw [show (fun y => f y * h y) = f * h from rfl, fderiv_mul (hf x) (hh x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem sqlap_pd_sq {g : B0579.Plane → ℝ} (hg : Differentiable ℝ g) (j : Fin 2)
    (x : B0579.Plane) :
    B0579.pd j (fun y => g y ^ 2) x = 2 * g x * B0579.pd j g x := by
  have : (fun y => g y ^ 2) = fun y => g y * g y := by funext y; ring
  rw [this, sqlap_pd_mul hg hg]
  ring

theorem diffSqLap : DiffSqLap := by
  intro g hg
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hpd : ∀ j : Fin 2, ContDiff ℝ 1 (B0579.pd j g) := fun j => DbCommon.pd_contDiff_one hg j
  have hpdd : ∀ j : Fin 2, Differentiable ℝ (B0579.pd j g) :=
    fun j => (hpd j).differentiable (by norm_num)
  refine ⟨hg.pow 2, fun x => ?_, fun x => sqlap_pd_sq hd 1 x⟩
  have e : ∀ j : Fin 2, B0579.pd j (fun y => g y ^ 2) = fun y => 2 * g y * B0579.pd j g y := by
    intro j; funext y; exact sqlap_pd_sq hd j y
  have step : ∀ j : Fin 2, B0579.pd j (B0579.pd j (fun y => g y ^ 2)) x =
      2 * (B0579.pd j g x) ^ 2 + 2 * g x * B0579.pd j (B0579.pd j g) x := by
    intro j
    rw [e j]
    have h2 : Differentiable ℝ (fun y => 2 * g y) := (differentiable_const 2).mul hd
    rw [sqlap_pd_mul h2 (hpdd j) j x]
    have : B0579.pd j (fun y => 2 * g y) x = 2 * B0579.pd j g x := by
      unfold B0579.pd
      rw [fderiv_const_mul (hd x)]
      simp
    rw [this]
    ring
  unfold lapP
  rw [step 0, step 1]
  ring

end UnforcedLeray.Short.IIIa
