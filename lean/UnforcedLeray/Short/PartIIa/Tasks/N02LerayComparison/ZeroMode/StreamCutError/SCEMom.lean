import UnforcedLeray.Short.PartIIa.Sub.N02_3_8
import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Twin of `GradCutError/GCEMom.lean` with the component index `0` (`f_r`) in place of `1` (`f_z`).
`etaFr f p = |η| ‖f_r p‖` with `f_r = (fun r => f r 0)`. Pointwise `‖f p 0‖ ≤ ‖f p‖`, so
`etaFr f p ^ 2 ≤ (|η|^1)^2 ‖f p‖^2`. Both integrands are integrable on `measureH c`
by `avgIntegrable_wnorm`, and `zMom c 0 1 f` unfolds to the integral of the right-hand integrand,
since `opS^[0] f = f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

open ZeroStreamCutErrorAux

/-- **Tail bound.** `‖|η| ‖f_r‖‖_{L²} ≤ zMom c 0 1 f`. -/
theorem sCEMom : UnforcedLeray.Short.PartIIa.ZeroStreamCutErrorAux.SCEMom := by
  unfold ZeroStreamCutErrorAux.SCEMom
  intro c f hc hf
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hgS : ContDiff ℝ ∞ (fun r => f r 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  have hb1 : ∀ p : Profile, (fun r => f r 0) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
    fun p hp => hb p (fun h => hp (by simp [h]))
  have ig1 : Integrable (fun p : Profile => (|p.2.2| ^ 1) ^ 2 * ‖f p 0‖ ^ 2) (measureH c) :=
    avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 1 hgS.continuous hb1
  have iF1 : Integrable (fun p : Profile => (|p.2.2| ^ 1) ^ 2 * ‖f p‖ ^ 2) (measureH c) :=
    avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 1 hf.smooth.continuous hb
  have ie : Integrable (fun p : Profile => etaFr f p ^ 2) (measureH c) := by
    refine ig1.congr (ae_of_all _ fun p => ?_)
    simp [etaFr, mul_pow]
  have hsq : ∀ p : Profile, etaFr f p ^ 2 ≤ (|p.2.2| ^ 1) ^ 2 * ‖f p‖ ^ 2 := by
    intro p
    have h1 : ‖f p 0‖ ≤ ‖f p‖ := PiLp.norm_apply_le (f p) 0
    have h0 : 0 ≤ ‖f p 0‖ := norm_nonneg _
    have h2 : ‖f p 0‖ ^ 2 ≤ ‖f p‖ ^ 2 := by nlinarith
    simp only [etaFr, pow_one, mul_pow]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hmono : ∫ p, etaFr f p ^ 2 ∂(measureH c)
      ≤ ∫ p, (|p.2.2| ^ 1) ^ 2 * ‖f p‖ ^ 2 ∂(measureH c) :=
    integral_mono ie iF1 hsq
  have hz : zMom c 0 1 f = (∫ p, (|p.2.2| ^ 1) ^ 2 * ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    unfold zMom
    simp only [Function.iterate_zero, id_eq]
  rw [hz]
  exact Real.rpow_le_rpow (integral_nonneg fun p => sq_nonneg _) hmono (by norm_num)

end UnforcedLeray.Short.PartIIa
