import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3

/-!
# `kerFFderiv` (`PartIII-b:C/rep/2/6/3/3/3`, source 3603-3626, 3800-3807, 4171-4200, 5223)

`y`-derivative of `kerF` is `kerF` of the `y`-derivative of the kernel: `T` does not depend on `y`,
and the sums and products with the constants `T(τ-h,z)_{jk}` commute with `fderiv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(L3)** `fderiv` of `kerF` in `y` is `kerF` of the `fderiv` of the kernel. -/
theorem kerFFderiv : KerFFderiv := by
  intro T τ i Φ p y v hd
  have hk : kerF T τ i Φ p = fun y' => ∑ j : Fin 3, ∑ k : Fin 3,
      Φ p.1 y' p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ) := rfl
  have hk' : kerF T τ i (fun h y z i j k => fderiv ℝ (fun y'' => Φ h y'' z i j k) y v) p y =
      ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ (fun y'' => Φ p.1 y'' p.2 i j k) y v *
        ((T (τ - p.1) p.2 j k : ℝ) : ℂ) := rfl
  rw [hk, hk', fderiv_fun_sum (fun j _ => DifferentiableAt.fun_sum
    (fun k _ => (hd j k).mul_const _)), sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_sum (fun k _ => (hd j k).mul_const _), sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_mul_const (hd j k)]
  simp [smul_eq_mul, mul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete
