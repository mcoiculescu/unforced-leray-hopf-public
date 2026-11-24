import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

theorem lateEqOps : LateEqOps := by
  unfold LateEqOps
  intro F G h
  refine ⟨?_, ?_, ?_⟩
  · intro ν c hν hc tr htr x hx
    have hEq : F ν c tr =ᶠ[𝓝 x] G ν c tr :=
      Filter.eventuallyEq_of_mem (isOpen_late.mem_nhds hx) (h ν c hν hc tr htr)
    have hd := hEq.fderiv_eq (𝕜 := ℝ)
    show ageOperator (F ν c tr) x = ageOperator (G ν c tr) x
    unfold ageOperator partialEta partialAge
    rw [hd]
  · intro ν c hν hc tr htr x hx
    have hEq : F ν c tr =ᶠ[𝓝 x] G ν c tr :=
      Filter.eventuallyEq_of_mem (isOpen_late.mem_nhds hx) (h ν c hν hc tr htr)
    have hd := hEq.fderiv_eq (𝕜 := ℝ)
    show partialEta (F ν c tr) x = partialEta (G ν c tr) x
    unfold partialEta
    rw [hd]
  · intro ν c hν hc tr htr x hx
    have hEq : F ν c tr =ᶠ[𝓝 x] G ν c tr :=
      Filter.eventuallyEq_of_mem (isOpen_late.mem_nhds hx) (h ν c hν hc tr htr)
    have hd := hEq.fderiv_eq (𝕜 := ℝ)
    show partialQ (F ν c tr) x = partialQ (G ν c tr) x
    unfold partialQ
    rw [hd]

end UnforcedLeray.Short.PartIIa.Jet
