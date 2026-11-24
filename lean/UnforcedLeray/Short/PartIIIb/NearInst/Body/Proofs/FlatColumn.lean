import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced

/-!
# The flat body column (source 4116-4119): proof of `FlatBodyColumnBound`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

theorem flatBodyColumnBound_of (hM1 : Delta.TrainMultRestr) (hFT : FlatTrainMultBound)
    (hG : GainInvContract) (hN : BodyFormNorm) : FlatBodyColumnBound := by
  intro Kset _hK hKsub mZ hmZ dm dp _hdm
  obtain ⟨C7, k7, ν7, hν7, h7⟩ := hFT mZ hmZ
  refine ⟨8 * |C7|, k7, ν7, hν7, ?_⟩
  intro p d hBG hνle ρb γ hρb hγ μ hμ M0 hM0 R0 hR0 f
  have hν : (0:ℝ) < p.ν := p.ν_pos
  have hc : (0:ℝ) < p.c := p.c_pos
  have hμI := hKsub hμ
  have hB0 : 0 ≤ |C7| * p.ν⁻¹ ^ k7 :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (inv_nonneg.2 hν.le) _)
  -- the flat train multiplier on the whole chart
  have hM := hM1 p.c mZ ρb γ p.ν hν p.trainData M0 univ (|C7| * p.ν⁻¹ ^ k7) hc
    MeasurableSet.univ hB0 hM0
    (fun pt _ hpt =>
      le_trans ((h7 p.ν ⟨hν, hνle⟩ p.c hBG.c_eq p.trainData hBG.train_buc).2 pt hpt)
        (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (inv_nonneg.2 hν.le) _)))
  -- the free body bound `‖T_0‖ ≤ 4`
  have hμpos : 0 < (μ : ℂ).re + 1 / 4 := by
    rw [Complex.ofReal_re]; linarith [hμI.1]
  have hR := UnforcedLeray.B0225.norm_R0_le (E := UnforcedLeray.B0223.MeridC) p.c_pos p.ν (μ := (μ : ℂ)) hμpos
  rw [Complex.ofReal_re] at hR
  have h4 : (μ + 1 / 4)⁻¹ ≤ 4 := by
    calc (μ + 1 / 4)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith [hμI.1])
      _ = 4 := by norm_num
  have hRn : ‖(UnforcedLeray.B0225.R0 (E := UnforcedLeray.B0223.MeridC) p.c_pos p.ν (μ : ℂ))‖ ≤ 4 :=
    le_trans hR h4
  have hPe : ‖UnforcedLeray.Short.PartIIa.PepsC 0 p.c‖ ≤ 1 := by
    unfold UnforcedLeray.Short.PartIIa.PepsC
    exact Submodule.starProjection_norm_le _
  have hT : ‖UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)‖ ≤ 4 := by
    unfold UnforcedLeray.Short.PartIIa.T0flat
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have := mul_le_mul hRn hPe (norm_nonneg _) (by norm_num)
    linarith
  -- the body form bound `‖R_0 f‖ ≤ 4‖f‖`
  have hR0f : ‖R0 f‖ ≤ 4 * ‖f‖ :=
    le_trans (hN p.c hc R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) hR0 f)
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  -- `g⁻¹` is a contraction on `H`
  have hGI : ‖(gainH p.c γ hν).symm (R0 f)‖ ≤ ‖R0 f‖ :=
    (hG p.c mZ ρb γ p.ν hν hγ).1 (R0 f)
  -- `G⁻¹ M_0 (R_0 f) = gainRestrM univ M_0 (g⁻¹ R_0 f)`
  have hkey : Delta.gainRestrM γ hν univ M0 ((gainH p.c γ hν).symm (R0 f)) =
      (gainEquiv p.c mZ ρb γ hν).symm (M0 (R0 f)) := by
    rw [Delta.gainRestrM_univ, Delta.gainConjM_apply, ContinuousLinearEquiv.apply_symm_apply]
  have h1 : ‖(gainEquiv p.c mZ ρb γ hν).symm (M0 (R0 f))‖ ≤
      2 * (|C7| * p.ν⁻¹ ^ k7) * ‖(gainH p.c γ hν).symm (R0 f)‖ := by
    rw [← hkey]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  calc ‖(gainEquiv p.c mZ ρb γ hν).symm (M0 (R0 f))‖
      ≤ 2 * (|C7| * p.ν⁻¹ ^ k7) * ‖(gainH p.c γ hν).symm (R0 f)‖ := h1
    _ ≤ 2 * (|C7| * p.ν⁻¹ ^ k7) * (4 * ‖f‖) :=
        mul_le_mul_of_nonneg_left (le_trans hGI hR0f) (mul_nonneg (by norm_num) hB0)
    _ = 8 * |C7| * p.ν⁻¹ ^ k7 * ‖f‖ := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Body
