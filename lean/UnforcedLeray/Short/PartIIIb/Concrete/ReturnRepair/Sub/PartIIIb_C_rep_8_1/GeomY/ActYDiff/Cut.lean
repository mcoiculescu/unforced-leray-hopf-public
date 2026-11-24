import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff.Comm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff.Wre

/-!
# `PartIII-b:C/rep/8/1/1/2/3/1`: `YA = 𝒞_y W_μ` of a separated source is differentiable

Source `the November 2 reference manuscript` 4178-4186, 5400-5406.  Where
`ν·age > 1` the stream cut vanishes in a neighbourhood; elsewhere `ϱ ≥ R√ν` lies in the young region,
where `Re W_μ` is `C²` and its outward primitive differentiable (`wre_outPrim_hasFDerivAt`), so the
cut is differentiable (`wgx_cut_hasFDerivAt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

theorem le_of_age_le {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {y : Space} (hy : 0 < ϱ y)
    (h : ν * age R y ≤ 1) : R * Real.sqrt ν ≤ ϱ y := by
  have hρ2 : 0 < ϱ y ^ 2 := pow_pos hy 2
  have hL : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have e1 : (R * Real.sqrt ν) ^ 2 = ν * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]; ring
  rw [← sq_le_sq₀ hL.le hy.le, e1]
  rw [age_eq, ← mul_div_assoc, div_le_one hρ2] at h
  linarith

theorem cutW_diffAt {ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ) (hP : 0 < P)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y := by
  by_cases hold : 1 < ν * age R y
  · have hc : ContinuousAt (fun y' : Space => ν * (R ^ 2 / ϱ y' ^ 2)) y :=
      (continuousAt_const.div ((continuous_ϱ.pow 2).continuousAt) (pow_ne_zero 2 hy.ne')).const_mul ν
    have hev : ∀ᶠ y' in 𝓝 y, 1 < ν * age R y' := continuousAt_const.eventually_lt hc hold
    have h0 : wardStreamCut ν R χy (sepWre ν μ T) τ =ᶠ[𝓝 y] fun _ => (0 : Space) := by
      filter_upwards [hev] with y' hy'
      exact wardStreamCut_eq_zero_old hχ _ τ hy'
    exact (differentiableAt_const (0 : Space)).congr_of_eventuallyEq h0
  · have hL : R * Real.sqrt ν ≤ ϱ y := le_of_age_le hν hR hy (not_lt.1 hold)
    have hLpos : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
    have hlt : R * Real.sqrt (5 * ν / 6) < ϱ y := by
      have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
        Real.sqrt_lt_sqrt (by positivity) (by linarith)
      have h2 : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h1 hR
      exact lt_of_lt_of_le h2 hL
    have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
    have hopen : IsOpen {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} :=
      isOpen_lt continuous_const continuous_ϱ
    have hZ : DifferentiableAt ℝ (sepWre ν μ T τ) y :=
      ((wre_contDiffOn hν hμ hr0 hP hT hM τ).contDiffAt (hopen.mem_nhds hlt)).differentiableAt
        (by norm_num)
    obtain ⟨Ψd, hΨ⟩ := wre_outPrim_hasFDerivAt hν hR hμ hP hT hM hA τ hlt
    obtain ⟨M1, M2, -, -, hM1, hM2⟩ := wgx_chi_bounds hχ
    have hLsq : ν * R ^ 2 = (R * Real.sqrt ν) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hν.le]; ring
    obtain ⟨D, hD, -⟩ := wgx_cut_hasFDerivAt hχ hM1 hM2 hν hLpos hLsq hL hZ.hasFDerivAt hΨ
      (le_refl ‖Ψd‖)
    exact hD.differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
