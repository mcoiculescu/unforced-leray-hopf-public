import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Short weak smoothing from the physical weak-to-strong cost (SP 3040-3094)

Source: `the November 2 reference manuscript` lines 3083-3094.
`ShortWeakSmoothing` (`Clock/Stages.lean`) follows from `WeakSmoothingPhys m` (the physical cost
`C_b ν^{-(m+2)/2}(s-t)^{-1/2}`, SP 3083-3084) by three elementary reductions:

* `b ≤ θ(s)` from `s ≤ coreEnd ν b` (`theta_ge_of_le_coreEnd`);
* zero circulation of the datum from the flow's own Biot-Savart velocity at age `t`
  (`zeroCircInitial_of`, from the six leaves of `ZeroCircLeaves.lean`, SP 3100-3101);
* the gain ratio `g(t)/g(s) ≤ exp |γ|` on gaps `≤ 1` (`gainG_ratio_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `s ≤ coreEnd ν b` gives `b ≤ θ(s)` (`ν, b > 0`). -/
theorem theta_ge_of_le_coreEnd {ν b s : ℝ} (hν : 0 < ν) (hb : 0 < b) (hs : 0 ≤ s)
    (h : s ≤ coreEnd ν b) : b ≤ clockTheta ν s := by
  unfold coreEnd at h
  unfold clockTheta clockA
  have h1 : ν * s ≤ (ν * b)⁻¹ - 1 := by
    have := mul_le_mul_of_nonneg_left h hν.le
    rwa [← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul] at this
  have h2 : 1 + ν * s ≤ (ν * b)⁻¹ := by linarith
  have hpos : 0 < 1 + ν * s := by positivity
  have hνb : 0 < ν * b := mul_pos hν hb
  rw [le_inv_comm₀ hb (by positivity)]
  have h3 : ν * (1 + ν * s) ≤ b⁻¹ := by
    have := mul_le_mul_of_nonneg_left h2 hν.le
    calc ν * (1 + ν * s) ≤ ν * (ν * b)⁻¹ := this
      _ = b⁻¹ := by field_simp
  exact h3

/-- Gain ratio: for `ν > 0`, `0 ≤ t ≤ s`, `s - t ≤ 1`,
`g(t)/g(s) ≤ exp |γ|`. -/
theorem gainG_ratio_le (γ ν : ℝ) (hν : 0 < ν) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hgap : s - t ≤ 1) : gainG γ ν t / gainG γ ν s ≤ Real.exp |γ| := by
  unfold gainG
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.2
  have ha : 0 < 1 + ν * t := by positivity
  have hb : 0 < 1 + ν * s := by nlinarith
  have e : γ * t / (1 + ν * t) - γ * s / (1 + ν * s) =
      γ * ((t - s) / ((1 + ν * t) * (1 + ν * s))) := by
    field_simp
    ring
  rw [e]
  have hs0 : 0 ≤ s := ht.trans hts
  have hden : 1 ≤ (1 + ν * t) * (1 + ν * s) := by
    nlinarith [mul_nonneg hν.le ht, mul_nonneg hν.le hs0,
      mul_nonneg (mul_nonneg hν.le ht) (mul_nonneg hν.le hs0)]
  have hq : |(t - s) / ((1 + ν * t) * (1 + ν * s))| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + ν * t) * (1 + ν * s)),
      div_le_one (by positivity), abs_of_nonpos (by linarith)]
    linarith
  calc _ ≤ |γ * ((t - s) / ((1 + ν * t) * (1 + ν * s)))| := le_abs_self _
    _ = |γ| * |(t - s) / ((1 + ν * t) * (1 + ν * s))| := abs_mul _ _
    _ ≤ |γ| * 1 := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
    _ = |γ| := mul_one _

/-- The datum of a weak linearised flow in `X_{m,c}`, `m > 1`, has zero circulation (the flow's
own `L²` Biot-Savart velocity at age `t`, SP 3100-3101). -/
def ZeroCircInitial : Prop :=
  ∀ ν c m : ℝ, 0 < c → 1 < m → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, ∀ t : ℝ,
    ∀ f w u, IsLinearisedFlow ν c m tr t f w u → HasZeroCirculation c f

theorem zeroCircInitial_of (h1 : ZCCellIntegrable) (h2 : ZCCutoffTest) (h3 : ZCChiDeriv)
    (h4 : ZCBandL2) (h5 : ZCCauchySchwarz) (h6 : ZCCutoffLimit) : ZeroCircInitial := by
  intro ν c m hc hm tr t f w u hw
  have hint := h1 c m hm (w t) (hw.memX t le_rfl)
  have hz := integral_cell_eq_zero_of_isBiotSavart_of h2 h3 h4 h5 h6 hc hint
    (hw.biotSavart t le_rfl)
  have hae := hw.initial
  refine ⟨(integrableOn_congr_fun_ae hae).1 hint, ?_⟩
  rw [← integral_congr_ae hae]
  exact hz

/-- **Short weak smoothing from the physical weak-to-strong cost** (SP 3083-3094). -/
theorem shortWeakSmoothing_of (hW : ∀ m : ℝ, 8 < m → WeakSmoothingPhys m)
    (hZ : ZeroCircInitial) : ShortWeakSmoothing := by
  intro P _ m hm
  obtain ⟨b₀, hb₀⟩ := hW m hm
  refine ⟨max b₀ 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have hbb : b₀ ≤ b := le_trans (le_max_left _ _) hb
  obtain ⟨C, ν₀, hν₀, hC⟩ := hb₀ b hbb
  refine ⟨Real.exp |P.eigenvalue.re| * C, ν₀, hν₀, fun ν hν tr htr t s ht hts hgap hcore f hf w u hw => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hνpos _
  have hθ : b ≤ clockTheta ν s :=
    theta_ge_of_le_coreEnd hνpos (by linarith) (by linarith) hcore
  have hbase := hC ν hν tr htr t s ht.le hts hgap hθ f hf
    (hZ ν _ m hc (by linarith) tr t f w u hw) w u hw
  have hg := gainG_ratio_le P.eigenvalue.re ν hνpos ht.le hts.le hgap
  have hg0 : 0 ≤ gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s := by
    unfold gainG; positivity
  calc ENNReal.ofReal (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
        xNorm (ν ^ (-2 : ℝ)) m (w s)
      ≤ ENNReal.ofReal (Real.exp |P.eigenvalue.re|) *
        (ENNReal.ofReal (C * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ)) *
          negNorm (ν ^ (-2 : ℝ)) m f) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp |P.eigenvalue.re| * C * ν ^ (-((m + 2) / 2)) *
          (s - t) ^ (-1 / 2 : ℝ)) * negNorm (ν ^ (-2 : ℝ)) m f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        ring

end UnforcedLeray.Short.IIIa
