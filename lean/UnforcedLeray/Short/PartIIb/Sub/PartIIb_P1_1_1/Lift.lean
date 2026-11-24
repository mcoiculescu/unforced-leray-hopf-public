import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1.Strip

/-!
# `PartII-b:P1/1/1`, step (3): `BLRLift` from `blrStrip` and periodic a.e. extension

Source `the November 2 reference manuscript` 1902-1906.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Axi

/-- A `P`-periodic property of `τ ∈ ℝ` that holds a.e. on one period holds a.e. on `ℝ`. -/
def BLRPerAE : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ q : ℝ → Prop, (∀ τ, q (τ + P) ↔ q τ) →
    (∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), q τ) → ∀ᵐ τ : ℝ, q τ

theorem blrLift_of (h : BLRPerAE) : BLRLift := by
  intro R c P hR hc hP W hW hper hsym
  have hPpos : 0 < P := hP ▸ div_pos (by positivity) hR
  obtain ⟨B₀, hB₀m, hB₀⟩ := blrStrip hR hc hP W hW hsym
  have hLm : Measurable (liftFun R c B₀) := measurable_liftFun R c hB₀m
  have hstrip := ae_slice hB₀
  have hτ : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, liftFun R c B₀ (τ, y) = W (τ, y) := by
    refine h P hPpos _ (fun τ => ?_) hstrip
    simp only [liftFun_add_period hR hc hP B₀ τ, hper τ]
  have hx : ∀ᵐ x : ℝ × Space, liftFun R c B₀ x = W x := by
    rw [Measure.volume_eq_prod]
    refine (Measure.ae_prod_iff_ae_ae (p := fun x => liftFun R c B₀ x = W x)
      (measurableSet_eq_fun hLm hW)).2 ?_
    exact hτ
  refine ⟨(√Real.pi * R)⁻¹ • B₀, hB₀m.const_smul _, ?_⟩
  filter_upwards [hx] with x hx
  rw [← hx]
  have e : Axi.perExt c ((√Real.pi * R)⁻¹ • B₀) = (√Real.pi * R)⁻¹ • Axi.perExt c B₀ := rfl
  rw [e, Nv_smul]
  rfl

end UnforcedLeray.Short.IIb
