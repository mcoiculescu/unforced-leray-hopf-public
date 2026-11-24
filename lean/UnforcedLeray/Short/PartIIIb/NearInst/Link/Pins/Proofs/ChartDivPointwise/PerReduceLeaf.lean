import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem perReduceLeaf : PerReduceLeaf := by
  intro c R hc hR E f hf τ y
  have hint := per_int c f hf
  -- `log(R²/ϱ²) = -2 log(ϱ/R)` for every `ϱ`, with Lean's junk values on the axis
  have hlog : Real.log (Axi.age R y) = -2 * Real.log (Axi.ϱ y / R) := by
    unfold Axi.age
    rw [show R ^ 2 / Axi.ϱ y ^ 2 = (Axi.ϱ y / R)⁻¹ ^ 2 by rw [inv_div, div_pow],
      Real.log_pow, Real.log_inv]
    push_cast
    ring
  have hq : Axi.phase R τ y = R * Real.log (Axi.ϱ y / R) + R * τ / 2 := by
    unfold Axi.phase
    rw [hlog]
    ring
  have hA : chartOf R c y τ = (Axi.age R y, (Axi.phase R τ y -
      c * ((⌊(R * Real.log (Axi.ϱ y / R) + R * τ / 2) / c + 1 / 2⌋ : ℤ) : ℝ),
      Axi.trans R y)) := by
    rw [hq]
    rfl
  have hfin : ∀ (s q η : ℝ), f (s, (q - c * ((⌊(R * Real.log (Axi.ϱ y / R) + R * τ / 2) / c
      + 1 / 2⌋ : ℤ) : ℝ), η)) = f (s, (q, η)) := by
    intro s q η
    have h := hint (⌊(R * Real.log (Axi.ϱ y / R) + R * τ / 2) / c + 1 / 2⌋) s
      (q - c * ((⌊(R * Real.log (Axi.ϱ y / R) + R * τ / 2) / c + 1 / 2⌋ : ℤ) : ℝ)) η
    rw [show q - c * ((⌊(R * Real.log (Axi.ϱ y / R) + R * τ / 2) / c + 1 / 2⌋ : ℤ) : ℝ) +
        ((⌊(R * Real.log (Axi.ϱ y / R) + R * τ / 2) / c + 1 / 2⌋ : ℤ) : ℝ) * c = q by ring] at h
    exact h.symm
  unfold Axi.chart
  rw [hA]
  exact hfin _ _ _

end UnforcedLeray.Short.PartIIIb.NearInst
