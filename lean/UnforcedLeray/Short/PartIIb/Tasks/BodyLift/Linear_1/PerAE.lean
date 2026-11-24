import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1.Lift

/-!
# `PartII-b:P1/1/1`, `BLRPerAE`: a periodic a.e. property holds a.e. on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem blrPerAE_proof : BLRPerAE := by
  intro P hP q hq hae
  have hper : Function.Periodic q P := fun τ => propext (hq τ)
  have hT : volume {x : ℝ | ¬ (x ∈ Ioc (0 : ℝ) P → q x)} = 0 :=
    ae_iff.1 ((ae_restrict_iff' measurableSet_Ioc).1 hae)
  apply ae_iff.2
  have hcov : {τ : ℝ | ¬ q τ} ⊆
      ⋃ m : ℤ, (fun x : ℝ => x + -(m • P)) ⁻¹' {x : ℝ | ¬ (x ∈ Ioc (0 : ℝ) P → q x)} := by
    intro τ hτ
    have hτ' : ¬ q τ := hτ
    obtain ⟨m, r, hmem, hsum⟩ : ∃ (m : ℤ) (r : ℝ), r ∈ Ioc (0 : ℝ) P ∧ r + m • P = τ :=
      ⟨toIocDiv hP 0 τ, toIocMod hP 0 τ, by simpa using toIocMod_mem_Ioc hP 0 τ,
        by simpa using toIocMod_add_toIocDiv_zsmul hP 0 τ⟩
    have h1 : q τ = q r := by
      rw [zsmul_eq_mul] at hsum
      rw [← hsum]
      exact (hper.int_mul m) r
    have e : τ + -(m • P) = r := by
      rw [← hsum]
      abel
    refine mem_iUnion.2 ⟨m, ?_⟩
    show τ + -(m • P) ∈ {x : ℝ | ¬ (x ∈ Ioc (0 : ℝ) P → q x)}
    rw [e]
    intro h
    exact hτ' (by rw [h1]; exact h hmem)
  refine measure_mono_null hcov ?_
  refine (measure_iUnion_null_iff).2 fun m => ?_
  rw [measure_preimage_add_right]
  exact hT

end UnforcedLeray.Short.IIb
