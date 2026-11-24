import UnforcedLeray.Short.PartIIa.Sub.N02_3_8
import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Twin of `GradCutError/GCEWin0.lean` with the component index `0` (`f_r`) in place of `1` (`f_z`).
From `ZeroWindowBound` with `g = f_r = (fun r => f r 0)`, `R = 2L`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

open ZeroGradCutErrorAux ZeroStreamCutErrorAux

namespace SCEWin0Aux

theorem winP_sq (L : ℝ) (g : Profile → ℂ) (p : Profile) :
    winP L g p ^ 2 = {p : Profile | |p.2.2| ≤ 2 * L}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p := by
  unfold winP
  by_cases h : |p.2.2| ≤ 2 * L
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

theorem zMom00 (c : ℝ) (f : Profile → MeridC) :
    zMom c 0 0 f = (∫ p, ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
  unfold zMom
  simp

theorem zMom01 (c : ℝ) (f : Profile → MeridC) :
    zMom c 0 1 f = (∫ p, p.2.2 ^ 2 * ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
  unfold zMom
  simp

theorem two_rpow_half_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
  calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

end SCEWin0Aux

open SCEWin0Aux in
/-- **Window bound, `S⁰` part** (`SCEWin0`). -/
theorem sCEWin0 : UnforcedLeray.Short.PartIIa.ZeroStreamCutErrorAux.SCEWin0 := by
  unfold ZeroStreamCutErrorAux.SCEWin0
  intro hW
  obtain ⟨C, hC, hB⟩ := hW
  refine ⟨2 * C, by linarith, fun c L f hc hL hf => ?_⟩
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hgS : ContDiff ℝ ∞ (fun r => f r 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  have hgc : Continuous (fun r => f r 0) := hgS.continuous
  have hb1 : ∀ p : Profile, (fun r => f r 0) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L0 :=
    fun p hp => hb p (fun h => hp (by simp [h]))
  have hBw := hB c (2 * L) (fun r => f r 0) hc (by linarith) hgS ⟨s0, s1, L0, hs0, hb1⟩
  beta_reduce at hBw
  rw [zMom00, zMom01]
  have hLHS : (∫ p, winP L (fun r => f r 0) p ^ 2 ∂(measureH c))
      = ∫ p, {p : Profile | |p.2.2| ≤ 2 * L}.indicator (fun p => ‖zPrimC (fun r => f r 0) p‖ ^ 2) p
          ∂(measureH c) := by
    simp only [winP_sq]
  rw [hLHS]
  have iF : Integrable (fun p : Profile => ‖f p‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 0
      hf.smooth.continuous hb
  have iF1 : Integrable (fun p : Profile => p.2.2 ^ 2 * ‖f p‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 1
      hf.smooth.continuous hb
  have ig : Integrable (fun p : Profile => ‖f p 0‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 0
      hgc hb1
  have ig1 : Integrable (fun p : Profile => p.2.2 ^ 2 * ‖f p 0‖ ^ 2) (measureH c) := by
    simpa using avgIntegrable_wnorm (c := c) (s0 := s0) (s1 := s1) (L := L0) hs0 1
      hgc hb1
  have hpt : ∀ p : Profile, ‖f p 0‖ ^ 2 ≤ ‖f p‖ ^ 2 := fun p => by
    have h1 : ‖f p 0‖ ≤ ‖f p‖ := PiLp.norm_apply_le (f p) 0
    have h0 : 0 ≤ ‖f p 0‖ := norm_nonneg _
    nlinarith
  have hA : (∫ p, ‖f p 0‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ (∫ p, ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg fun p => sq_nonneg _) _ (by norm_num)
    exact integral_mono ig iF hpt
  have hB' : (∫ p, p.2.2 ^ 2 * ‖f p 0‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ (∫ p, p.2.2 ^ 2 * ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg fun p => by positivity) _ (by norm_num)
    exact integral_mono ig1 iF1 fun p => mul_le_mul_of_nonneg_left (hpt p) (sq_nonneg _)
  have hpow : (2 * L) ^ (1 / 2 : ℝ) ≤ 2 * L ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hL.le]
    exact mul_le_mul_of_nonneg_right two_rpow_half_le (Real.rpow_nonneg hL.le _)
  have hr : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hL.le _
  calc (∫ p, {p : Profile | |p.2.2| ≤ 2 * L}.indicator (fun p => ‖zPrimC (fun r => f r 0) p‖ ^ 2) p
          ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ C * (2 * L) ^ (1 / 2 : ℝ) *
          ((∫ p, ‖f p 0‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖f p 0‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := hBw
    _ ≤ C * (2 * L ^ (1 / 2 : ℝ)) *
          ((∫ p, ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) (add_le_add hA hB')
          (add_nonneg (Real.rpow_nonneg (integral_nonneg fun p => sq_nonneg _) _)
            (Real.rpow_nonneg (integral_nonneg fun p => by positivity) _))
          (mul_nonneg hC (mul_nonneg (by norm_num) hr))
    _ = 2 * C * L ^ (1 / 2 : ℝ) *
          ((∫ p, ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) +
            (∫ p, p.2.2 ^ 2 * ‖f p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)) := by ring

end UnforcedLeray.Short.PartIIa
