import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2.farOutMeasurable
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PartIIIb_C_near_masked_22
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarPointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.TailL1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.YoungDilated
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.PhaseMinkowski
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarSeparation
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.DilationMargin
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PeriodShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajFixedL
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajMeasurable
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.DilMajAxisym
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.RotExists
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.FarKernL1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Majorant
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Source
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.NsSymNormLe
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.FarMajorantPointwise

/-!
# `stripFar_holds` (source 4003-4005): far part of the partial strip

Source of record: `the November 2 reference manuscript`, lines 4003-4005.

`farMajorantL2_holds` assembles `FarMajorantL2` from the proved leaves. `stripFar_of` derives
`StripFar` from `FarPointwiseMajorant` (`sep:kernel` pointwise majorant), `FarMajorantL2` and the
measurability `FarOutMeasurable`, by the same band-restricted assembly as `forbiddenKernelBound_of_sub`.
The remaining open piece for the unconditional `stripFar_holds` is `FarOutMeasurable`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem farMajorantL2_holds : FarMajorantL2 :=
  farMajorantL2_of
    (farMajorantPointwise_of farSeparation_holds cartLiftNormOffAxis_holds axisNull_holds)
    (farKernL1_of tailL1_holds) dilationMargin_holds
    (dilMajL2_of (dilMajFixedL_of youngDilated_holds periodShift_holds dilMajMeasurable_holds)
      phaseMinkowski_holds dilMajMeasurable_holds)
    dilMajMeasurable_holds (dilMajAxisym_of rotExists_holds) gAxFacts_holds
    (chartL2Majorant_of ageShift_holds polarReduction_holds
      (chartChange_of chartChangeSE_holds chartChangeTQ_holds))
    (chartL2Source_of ageShift_holds polarReduction_holds
      (chartChange_of chartChangeSE_holds chartChangeTQ_holds) gAxFacts_holds)
    nsSymNormLe_holds

/-- `StripFar` from the open measurability piece `FarOutMeasurable`. -/
theorem stripFar_of (hM : FarOutMeasurable) (hK : IIIa.SepKernelBounds) (hY : IIIa.SepYoung) :
    StripFar := by
  intro Kset hKc hKs dm dp hdm b δ hb hb1 hδ
  obtain ⟨CA, hCA, hA⟩ := farPointwiseMajorant_of hK
  obtain ⟨CB, k, ν₀, hν₀, hB⟩ := farMajorantL2_holds Kset hKc hKs dm dp hdm b δ hb hb1 hδ
  refine ⟨CA * CB, k, ν₀, hν₀, ?_⟩
  intro p d hreg hν μ hμ l r hl hlr hrl hrS g hg hsupp
  have hr : 0 < r := hl.trans hlr
  have hRpos : 0 < p.R := by
    have : p.R = p.ε⁻¹ := by simp [Params.R]
    rw [this]
    exact inv_pos.2 p.ε_pos
  have hBB := hB p d hreg hν μ hμ r hr hrS g hg (fun x hx => (hsupp x hx).2)
  have hμ0 : -(1 / 4) < μ := by linarith [(hKs hμ).1, (hKs hμ).2]
  have hmeas : MeasurableSet (ageBelow r) := measurableSet_lt measurable_fst measurable_const
  set G : Chart → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMajE p.R p.c δ μ g x with hG
  have hpt : ∀ x, ‖(ageBand l r).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) g) x‖ₑ ≤
      ENNReal.ofReal CA * (ageBelow r).indicator G x := by
    intro x
    by_cases hx : x ∈ ageBand l r
    · have hxB : x ∈ ageBelow r := show x.1 < r from (show l ≤ x.1 ∧ x.1 < r from hx).2
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxB]
      exact hA p.R p.c p.ν δ (p.ε ^ (-b)) μ p.ν_pos g x
    · simp [Set.indicator_of_notMem hx]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  refine ⟨?_, ?_⟩
  · exact (hM p.R p.c p.ν δ (p.ε ^ (-b)) μ hRpos p.c_pos p.ν_pos hδ (Real.rpow_pos_of_pos p.ε_pos _) hμ0 g hg).indicator
      (measurableSet_ageBand l r)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  have hind : ∫⁻ x, ((ageBelow r).indicator G x) ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2)) =
      ∫⁻ x in ageBelow r, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2)) := by
    rw [← lintegral_indicator hmeas]
    congr 1
    ext x
    by_cases hx : x ∈ ageBelow r
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have step1 : ∫⁻ x, ‖(ageBand l r).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) g) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ p.c (-3 / 2)) ≤
      ENNReal.ofReal CA ^ (2 : ℝ) *
        ∫⁻ x in ageBelow r, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2)) := by
    rw [← hind, ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (hpt x) (by norm_num)
  calc (∫⁻ x, ‖(ageBand l r).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) g) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal CA ^ (2 : ℝ) *
          ∫⁻ x in ageBelow r, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step1 (by norm_num)
    _ = ENNReal.ofReal CA *
          (∫⁻ x in ageBelow r, G x ^ (2 : ℝ) ∂(ageμ p.c (-3 / 2))) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
    _ ≤ ENNReal.ofReal CA * (ENNReal.ofReal (CB * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
          eLpNorm g 2 (ageμ p.c (-1 / 2))) := by
        gcongr
    _ = ENNReal.ofReal (CA * CB * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
          eLpNorm g 2 (ageμ p.c (-1 / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCA]
        congr 2
        ring

/-- `StripFar` (source 4003-4005), unconditionally: the open measurability piece
`farOutMeasurable` (`Proofs/FarKernelL2/farOutMeasurable.lean`) discharges `FarOutMeasurable`. -/
theorem stripFar_holds (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) (hY : UnforcedLeray.Short.IIIa.SepYoung) : StripFar :=
  stripFar_of farOutMeasurable hK hY

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
