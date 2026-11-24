import UnforcedLeray.Blueprint.Localization.Nonlinear
import UnforcedLeray.Loc.L11AffineBound.Forcing

/-!
# Step L11: the affine, linear and bilinear bounds of the correction maps

`paper/main.tex` lines 493–514 (`loc:eq:local-fixed-point`, line 495; `loc:eq:affine-bound`,
line 511); blueprint units B1021 (the two direct correction maps) and B1023 (the affine,
linear and bilinear bounds in `𝒵_β`).

The step `UnforcedLeray.Blueprint.AffineBoundStep` (`Blueprint/Localization/Nonlinear.lean`)
asks, for every package `D`, linear theory `ld` (steps L1–L8), compact datum `u₀` and
nonlinear maps `nm` (step L10), for constants `C₀ > 0`, `C ≥ 0` independent of `τ₀ ≤ 0` and
correction maps `Bq`, `L_j`, `G_j` on `𝒵_β(τ₀)` with the literal forcing formulas of
`IsCorrectionMaps` and the three bounds of `loc:eq:affine-bound`.

The manuscript's argument (lines 504–514) is: the `H²` product bound and multiplication by
`W^{2,∞}` fields bound the forcings in `𝒳_β`, and `loc:eq:inverse-bound` (`‖𝓡_β‖ ≤ C_β`,
B1020) transfers the bounds to `𝒵_β`. In the interface layer these analytic inputs are part
of the hypotheses of the step:
* the `H²` product bound is the boundedness of the bilinear map `nm.N : Z →L Z →L X`
  (`NonlinearMaps`, step L10);
* the `W^{2,∞}` multiplication bound is `IsNonlinearMaps.CK_bound` (line 506);
* the force bound `loc:eq:force-bound` (B0722) is `IsNonlinearMaps.force_bound`;
* `loc:eq:inverse-bound` is `IsGreenOperator.bound` (step L8);
* `b̂` is bounded because it is continuous and periodic (`IsRegularMode`, B1011);
* `σ < β < 2σ` is `IsSpectralSplitting` (`loc:eq:weight`, B1013) and `σ < 1/4` is in the
  package (line 172).
What is proved here (and in `L11AffineBound/Forcing.lean`) is the construction of the three
forcings as bounded continuous functions on `(-∞, τ₀]`, the correction maps through `𝓡_β`, and
the exponential bookkeeping of lines 504–514.

Main result: `UnforcedLeray.Loc.L11.affineBoundStep : AffineBoundStep`, with constants
`C₀ = C_R(C_G + C_K M_b + ‖𝓝‖M_b²) + 1` and `C = C_R(C_K + 2‖𝓝‖M_b + ‖𝓝‖)`, where `C_R`
bounds `𝓡_β`, `C_K`, `C_G` are the constants of L10 and `M_b = sup ‖b̂‖`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped BoundedContinuousFunction

namespace UnforcedLeray.Loc.L11

open UnforcedLeray.Blueprint

theorem jcoef_nonneg (j : Fin 2) : 0 ≤ jcoef j := by
  unfold jcoef; positivity

theorem jcoef_le_one (j : Fin 2) : jcoef j ≤ 1 := by
  fin_cases j <;> simp [jcoef]

/-- **Step L11** `AffineBoundStep` (`paper/main.tex` lines 493–514, `loc:eq:local-fixed-point`
and `loc:eq:affine-bound`; blueprint units B1021, B1023). For every package, linear theory,
compact datum and nonlinear maps there are constants `C₀ > 0`, `C ≥ 0`, uniform in `τ₀ ≤ 0`,
and correction maps on `𝒵_β(τ₀)` given by the literal forcing formulas, with
`‖G_j‖ ≤ C₀(e^{(1/2-β)τ₀} + e^{(2σ-β)τ₀})`, `‖L_j‖ ≤ C(e^{τ₀/2} + e^{στ₀})` and
`‖B‖ ≤ Ce^{βτ₀}`. -/
theorem affineBoundStep : AffineBoundStep := by
  intro D hD ld hld u₀ _hu₀ nm hnm
  obtain ⟨CR, hCR⟩ := hld.green.bound
  have hCR0 : 0 ≤ CR := (norm_nonneg (ld.R 0)).trans (hCR 0 le_rfl)
  obtain ⟨CK, hCK0, hCK⟩ := exists_nonneg_bound hnm.CK_bound
  obtain ⟨CG, hCG0, hCG⟩ := exists_nonneg_bound hnm.force_bound
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bound_of_periodic hld.mode.periodic
    hD.1.period_pos.ne' hld.mode.continuous
  have h : Hyp nm.CK nm.Gstar ld.bhat D.σ ld.sp.β CK CG Mb :=
    { σ_pos := hD.2.σ_pos
      σ_lt := hD.2.σ_lt
      β_gt := hld.splitting.weight_lower
      β_lt := hld.splitting.weight_upper
      K_cont := hnm.CK_continuous
      G_cont := hnm.Gstar_continuous
      b_cont := hld.mode.continuous
      CK_nonneg := hCK0
      CG_nonneg := hCG0
      Mb_nonneg := hMb0
      K_bound := hCK
      G_bound := hCG
      b_bound := hMb }
  have hβ0 : 0 ≤ ld.sp.β := h.β_pos.le
  have hN0 : 0 ≤ ‖nm.N‖ := norm_nonneg nm.N
  have hNMb : 0 ≤ 2 * ‖nm.N‖ * Mb := mul_nonneg (mul_nonneg zero_le_two hN0) hMb0
  have hA0 : 0 ≤ CG + CK * Mb + ‖nm.N‖ * Mb ^ 2 :=
    add_nonneg (add_nonneg hCG0 (mul_nonneg hCK0 hMb0)) (mul_nonneg hN0 (sq_nonneg Mb))
  have hL0 : 0 ≤ CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖ :=
    add_nonneg (add_nonneg hCK0 hNMb) hN0
  refine ⟨CR * (CG + CK * Mb + ‖nm.N‖ * Mb ^ 2) + 1, CR * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖),
    add_pos_of_nonneg_of_pos (mul_nonneg hCR0 hA0) one_pos, mul_nonneg hCR0 hL0, ?_⟩
  intro τ₀ hτ₀
  have hRle : ‖ld.R τ₀‖ ≤ CR := hCR τ₀ hτ₀
  let R : (Iic τ₀ →ᵇ X) →L[ℝ] (Iic τ₀ →ᵇ Z) := ld.R τ₀
  have hRle' : ‖R‖ ≤ CR := hRle
  let Bq : WeightedZ τ₀ →L[ℝ] WeightedZ τ₀ →L[ℝ] WeightedZ τ₀ := bilCorr nm.N hβ0 R
  let L : Fin 2 → (WeightedZ τ₀ →L[ℝ] WeightedZ τ₀) := fun j =>
    linCorr nm.N h (jcoef_nonneg j) (jcoef_le_one j) hτ₀ R
  let GF : Fin 2 → (Iic τ₀ →ᵇ X) := fun j =>
    affForcing nm.N h (jcoef_nonneg j) (jcoef_le_one j) hτ₀
  let G : Fin 2 → WeightedZ τ₀ := fun j => R (GF j)
  refine ⟨⟨Bq, L, G⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `Bq_spec`
    intro w₁ w₂
    exact ⟨bilForcing nm.N hβ0 w₁ w₂, fun τ => rfl, rfl⟩
  · -- `L_spec`
    intro j w
    exact ⟨linForcing nm.N h (jcoef_nonneg j) (jcoef_le_one j) hτ₀ w, fun τ => rfl, rfl⟩
  · -- `G_spec`
    intro j
    exact ⟨GF j, fun τ => rfl, rfl⟩
  · -- the affine bound
    intro j
    have hG : ‖GF j‖ ≤ affBound nm.N D.σ ld.sp.β CK CG Mb τ₀ :=
      norm_affForcing_le nm.N h (jcoef_nonneg j) (jcoef_le_one j) hτ₀
    have hE1 : 0 < Real.exp ((1 / 2 - ld.sp.β) * τ₀) := Real.exp_pos _
    have hE2 : 0 < Real.exp ((2 * D.σ - ld.sp.β) * τ₀) := Real.exp_pos _
    have hstep : ‖R (GF j)‖ ≤ CR * affBound nm.N D.σ ld.sp.β CK CG Mb τ₀ :=
      (R.le_opNorm _).trans (mul_le_mul hRle' hG (norm_nonneg _) hCR0)
    show ‖R (GF j)‖ ≤ (CR * (CG + CK * Mb + ‖nm.N‖ * Mb ^ 2) + 1) *
      (Real.exp ((1 / 2 - ld.sp.β) * τ₀) + Real.exp ((2 * D.σ - ld.sp.β) * τ₀))
    refine hstep.trans ?_
    unfold affBound
    have hA : 0 ≤ CG + CK * Mb := add_nonneg hCG0 (mul_nonneg hCK0 hMb0)
    have hB : 0 ≤ ‖nm.N‖ * Mb ^ 2 := mul_nonneg hN0 (sq_nonneg Mb)
    have key : (CG + CK * Mb) * Real.exp ((1 / 2 - ld.sp.β) * τ₀) +
        ‖nm.N‖ * Mb ^ 2 * Real.exp ((2 * D.σ - ld.sp.β) * τ₀) ≤
        (CG + CK * Mb + ‖nm.N‖ * Mb ^ 2) *
          (Real.exp ((1 / 2 - ld.sp.β) * τ₀) + Real.exp ((2 * D.σ - ld.sp.β) * τ₀)) := by
      nlinarith [mul_nonneg hA hE2.le, mul_nonneg hB hE1.le]
    have hsum : 0 ≤ Real.exp ((1 / 2 - ld.sp.β) * τ₀) + Real.exp ((2 * D.σ - ld.sp.β) * τ₀) :=
      add_nonneg hE1.le hE2.le
    calc CR * ((CG + CK * Mb) * Real.exp ((1 / 2 - ld.sp.β) * τ₀) +
          ‖nm.N‖ * Mb ^ 2 * Real.exp ((2 * D.σ - ld.sp.β) * τ₀))
        ≤ CR * ((CG + CK * Mb + ‖nm.N‖ * Mb ^ 2) *
          (Real.exp ((1 / 2 - ld.sp.β) * τ₀) + Real.exp ((2 * D.σ - ld.sp.β) * τ₀))) :=
          mul_le_mul_of_nonneg_left key hCR0
      _ ≤ (CR * (CG + CK * Mb + ‖nm.N‖ * Mb ^ 2) + 1) *
          (Real.exp ((1 / 2 - ld.sp.β) * τ₀) + Real.exp ((2 * D.σ - ld.sp.β) * τ₀)) := by
          nlinarith
  · -- the linear bound
    intro j
    have hEa := Real.exp_pos ((1 / 2) * τ₀)
    have hEs := Real.exp_pos (D.σ * τ₀)
    have hlin : linBound nm.N D.σ CK Mb τ₀ ≤
        (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖) * (Real.exp ((1 / 2) * τ₀) + Real.exp (D.σ * τ₀)) := by
      unfold linBound
      nlinarith [mul_nonneg hCK0 hEs.le, mul_nonneg hNMb hEa.le,
        mul_nonneg hN0 hEa.le, mul_nonneg hN0 hEs.le]
    have hC0 : 0 ≤ CR * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖) *
        (Real.exp ((1 / 2) * τ₀) + Real.exp (D.σ * τ₀)) :=
      mul_nonneg (mul_nonneg hCR0 hL0) (add_nonneg hEa.le hEs.le)
    refine ContinuousLinearMap.opNorm_le_bound (L j) hC0 (fun w => ?_)
    have hw := norm_linCorr_apply_le nm.N h (jcoef_nonneg j) (jcoef_le_one j) hτ₀ R w
    have hRL : ‖R‖ * linBound nm.N D.σ CK Mb τ₀ ≤
        CR * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖) *
          (Real.exp ((1 / 2) * τ₀) + Real.exp (D.σ * τ₀)) := by
      rw [mul_assoc CR]
      exact mul_le_mul hRle' hlin (linBound_nonneg nm.N h τ₀) hCR0
    exact hw.trans (mul_le_mul_of_nonneg_right hRL (norm_nonneg _))
  · -- the bilinear bound
    have hEb := Real.exp_pos (ld.sp.β * τ₀)
    have hC0 : 0 ≤ CR * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖) * Real.exp (ld.sp.β * τ₀) :=
      mul_nonneg (mul_nonneg hCR0 hL0) hEb.le
    refine ContinuousLinearMap.opNorm_le_bound₂ Bq hC0 (fun w₁ w₂ => ?_)
    have hw := norm_bilCorr_apply_le nm.N hβ0 R w₁ w₂
    have hNle : ‖nm.N‖ ≤ CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖ := by
      have : 0 ≤ CK + 2 * ‖nm.N‖ * Mb := add_nonneg hCK0 hNMb
      linarith
    have hRB : ‖R‖ * (Real.exp (ld.sp.β * τ₀) * ‖nm.N‖) ≤
        CR * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖) * Real.exp (ld.sp.β * τ₀) := by
      calc ‖R‖ * (Real.exp (ld.sp.β * τ₀) * ‖nm.N‖)
          ≤ CR * (Real.exp (ld.sp.β * τ₀) * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖)) :=
            mul_le_mul hRle' (mul_le_mul_of_nonneg_left hNle hEb.le)
              (mul_nonneg hEb.le hN0) hCR0
        _ = CR * (CK + 2 * ‖nm.N‖ * Mb + ‖nm.N‖) * Real.exp (ld.sp.β * τ₀) := by ring
    exact hw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hRB (norm_nonneg _)) (norm_nonneg _))

end UnforcedLeray.Loc.L11
