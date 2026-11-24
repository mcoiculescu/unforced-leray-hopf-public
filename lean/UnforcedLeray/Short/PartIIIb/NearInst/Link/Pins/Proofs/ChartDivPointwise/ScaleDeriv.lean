import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1

/-!
# `ScaleDeriv` (task `PartIII-b:C/near/pins/4/1/7`)

Product rule for `p ↦ p.1 * A p` in the chart `Chart = ℝ × (ℝ × ℝ)`.  The directional derivatives
`Axi.dQ`, `Axi.dS`, `Axi.dEta` are `fderiv` in the directions `(0,(1,0))`, `(1,(0,0))`,
`(0,(0,1))`; the `s`-component of these directions is `0`, `1`, `0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem scaleDeriv : ScaleDeriv := by
  unfold ScaleDeriv
  intro A p hA
  have hc : HasFDerivAt (fun q : Chart => q.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hm := hc.mul hA.hasFDerivAt
  have hfd : fderiv ℝ (fun q : Chart => q.1 * A q) p =
      p.1 • fderiv ℝ A p + A p • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) := hm.fderiv
  refine ⟨?_, ?_, ?_⟩
  · simp only [UnforcedLeray.Axi.dQ]
    rw [hfd]
    simp [smul_eq_mul]
  · simp only [UnforcedLeray.Axi.dEta]
    rw [hfd]
    simp [smul_eq_mul]
  · simp only [UnforcedLeray.Axi.dS]
    rw [hfd]
    simp [smul_eq_mul]
    ring

end UnforcedLeray.Short.PartIIIb.NearInst
