import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Transfer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.EarlyThinBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Kernel.Ungained

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/org` (b): the ungained far kernel, repair source → repair receiver

Source `the November 2 reference manuscript` 5303-5308 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`; late-output part `(1-χ_y)F_far`, early-source part `χ_yF_far(1-χ_o)`),
5318-5319 (gains), 5323-5339 (table entry `ε^{79/22}e^{3m₀/(2ν)}`, common `P_νS^k`; "the
repair-to-repair entry uses the source `L^{22/19}` norm and the `L^{11/3}` kernel"; receiver factor
`√ρ`, 5336), 3902-3920 (`S_far = S_μ - S_N`).

`LateSepKernelAt` (`LateRepRep/Props.lean`) is the gain transfer (`Transfer.lean`) applied to one
leaf, the separated-kernel bound of the whole far operator `F_far = S_μ - S_N` on an arbitrary
repair source `(0,T₂)`, read on the scaled repair receiver **without the gain**:

* **`FarRepRepUng`** (leaf): `‖(M_UF_far(0,T₂))₂‖_{ρ_b^{-1/2}H_T} ≤
  P_νS^{k₀}ε^{95/22}e^{m₀/(2ν)}‖𝒩_TT₂‖_{L²_τL^{22/19}}` (all output ages `s < S`).  The powers:
  the order-four velocity kernel in `L^{11/3}` (Young `19/22 + 3/11 = 1 + 3/22`, source `L^{22/19}`
  into velocity `L^{22/3}`) has off-diagonal norm `D^{-35/11}`, `D ≥ (1-e^{-δ/2})R/√S`, i.e.
  `ε^{35/11}S^{35/22}`; the scaled repair receiver costs `R⁻¹ρ_b^{-1/2}‖r_b‖_{C_τL^{11/4}} ≤
  P_ν ε √ρ` (normalized lift `‖T₂‖_{H_T} = (πR²)^{-1/2}‖𝒩_TT₂‖_{L²}`, Hölder `1/2 = 4/11 + 3/22`,
  5134-5139); `1 + 35/11 + 3/22 = 95/22`, `√ρ = ε^{3/22}e^{m₀/(2ν)}`.

The leaf `FarRepRepUng` (with `SeqData.FarRepRepUngAt`), `lrr_early_level` and
`earlyRepRepKernel_of_farRepRepUng` (the same leaf gives the early-source kernel estimate
`EarlyRepRepKernel`, task `PartIII-b:C/rep/4/4/1/org/8/1`) are those of
`EarlyRepRep/Kernel/Ungained.lean`, imported above; this file used to declare identical copies,
removed so that both files can be imported together (organizer item `ORG:clash-pass`).

Proved here:
* `lateSepKernelAt_of`, `lateSepKernel_of_farRepRepUng`: the late-output entry (gain
  `e^{-4γ/(9ν)}` on `s ≥ 0.8/ν`, `lrr_late_level`, with `multYoung`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- **`LateSepKernelAt` from the ungained far kernel** (source 5318, 5323-5339): the late-output
gain `g(s)^{-1} ≤ e^{-4γ/(9ν)}` on the support `s ≥ 0.8/ν` of `(1-χ_y)(M_UF_far x)₂`. -/
theorem lateSepKernelAt_of (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) (hγ : 0 ≤ gRate D.Pl)
    (hA : D.FarRepRepUngAt k₀) (hM : D.MultYoungAt hχ) : D.LateSepKernelAt hχ k₀ := by
  obtain ⟨C, k, hC, eA⟩ := hA
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [eA, hM] with n a m
  intro z hz w
  have c1 := lrr_late_level D.Pl D.K (D.level n) (D.mu n z) hχ hγ (fun v => (m v).2)
    (repPart (multOp D.Pl D.K (D.level n) w))
  have c2 := a z hz (multOp D.Pl D.K (D.level n) w)
  have hA0 : 0 ≤ C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
      (D.level n).ε ^ (95 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) := by
    have := (D.level n).ν_pos
    have := (D.level n).ε_pos
    positivity
  calc _ ≤ _ := c1.trans (mul_le_mul' le_rfl c2)
    _ = _ := by
      rw [ENNReal.ofReal_mul hA0]
      unfold repStressFull
      ring

end SeqData

/-- **`LateSepKernel` from the far-kernel leaf** (source 5318, 5323-5339), with `multYoung`
(proved). -/
theorem lateSepKernel_of_farRepRepUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hA : FarRepRepUng Pl σ₀ mZ dm dp) : LateSepKernel Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hA
  exact ⟨k₀, fun D hP hσ hZ hst => D.lateSepKernelAt_of hst.chiY k₀ hst.gamma_pos.le
    (hk D hP hσ hZ hst) (multYoung dm dp D hst)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
