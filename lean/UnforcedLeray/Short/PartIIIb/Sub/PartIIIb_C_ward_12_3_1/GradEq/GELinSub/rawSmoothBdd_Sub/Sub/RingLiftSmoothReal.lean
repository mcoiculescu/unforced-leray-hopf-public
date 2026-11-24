import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt

/-!


Source `the November 2 reference manuscript`
lines 1214, 1305-1322.

This file proves `ringLiftSmoothReal : RingLiftSmoothReal` by combining the reduction
`ringLiftSmoothReal_of_ext` (taking real parts coordinatewise of the complex-valued smooth lift
from `RingLiftSmoothExt`) with `PartII-b:R1/6` (`ringLiftSmoothExt_of`) and `PartII-a:R06`
(`ringAxisSmooth`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

/-- Conditional form: `RingLiftSmoothExt` implies `RingLiftSmoothReal`. -/
theorem ringLiftSmoothReal_of_ext (h : UnforcedLeray.Short.IIb.RingLiftSmoothExt) :
    RingLiftSmoothReal := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun ν hν ψ pr hpr R hR => ?_⟩
  obtain ⟨U, Pw, hU, _hP, _hper, _hdiv, hoff⟩ := H ν hν ψ pr hpr R hR
  refine ⟨fun x => WithLp.toLp 2 (fun j => (U x j).re), ?_, ?_⟩
  · apply contDiff_piLp'
    intro j
    exact Complex.reCLM.contDiff.comp (((contDiff_piLp 2).1 hU) j)
  · intro x hx
    obtain ⟨hU', _⟩ := hoff x hx
    ext j
    simp only [hU', UnforcedLeray.B0412.realC_apply, Complex.ofReal_re]

/-- Unconditional smooth real-valued similarity lift across the axis. -/
theorem ringLiftSmoothReal : RingLiftSmoothReal :=
  ringLiftSmoothReal_of_ext
    (UnforcedLeray.Short.IIb.ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth)

end UnforcedLeray.Short.PartIIIb.Concrete
