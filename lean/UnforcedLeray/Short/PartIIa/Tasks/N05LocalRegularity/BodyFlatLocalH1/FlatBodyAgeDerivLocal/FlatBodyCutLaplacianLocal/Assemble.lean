import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Main

/-!
# `PartII-a:N05/2/2/1`: the cylinder data of `w = R₀(μ)g`

Source: `the November 2 reference manuscript`, lines 1794-1799.
`cyl_data`: the cylinder heat estimate (with constant `C₀`, `r = 2`) applied to `u_i = θ w̃_i`
gives the weak `∂_q²u_i`, `∂_η²u_i` with `‖ν ∂_j² u_i‖_{cell} ≤ C₀ ‖f_i‖_{cell}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell periodize QPeriodic
  periodize_of_mem)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

/-- The body of `CylHeatMaxRegL` at `r = 2` with constant `C`. -/
def CylBound2 (C : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ u f : Coord → ℂ,
    QPeriodicSL c u → QPeriodicSL c f → AEStronglyMeasurable u volume →
    AEStronglyMeasurable f volume → eLpNorm u (ENNReal.ofReal 2) (cylMeasL c) < ⊤ →
    eLpNorm f (ENNReal.ofReal 2) (cylMeasL c) < ⊤ → IsCylHeatL ν u f →
    ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      (QPeriodicSL c Dt ∧ AEStronglyMeasurable Dt volume) ∧
      (∀ i j, QPeriodicSL c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume) ∧
      (∀ φ, IsSTTestCoordL φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, Dt x * (φ x : ℂ)) ∧
      (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoordL φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) ∧
      eLpNorm Dt (ENNReal.ofReal 2) (cylMeasL c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal 2) (cylMeasL c) ∧
      ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal 2) (cylMeasL c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal 2) (cylMeasL c)

/-- The weak second derivatives of `u_i` with their cell bounds. -/
theorem cyl_data {C0 M0 : ℝ} (hC0pos : 0 < C0) (hC0 : CylBound2 C0) (hM0n : 0 ≤ M0)
    (hM0 : ∀ t, |deriv Real.smoothTransition t| ≤ M0) {ν c σ H1 : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hσ : 0 < σ) (hσH : σ ≤ H1) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (g : HSpace c MeridC)
    (i : Fin 2) :
    ∃ D : Fin 2 → Coord → ℂ,
      (∀ j, QPeriodicSL c (D j) ∧ AEStronglyMeasurable (D j) volume) ∧
      (∀ (j : Fin 2) (φ : Coord → ℝ), IsSTTestCoordL φ →
        ∫ x, uCut c σ H1 (UnforcedLeray.B0225.R0 hc ν μ g : Profile → MeridC) i x *
            (cpd j.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D j x * (φ x : ℂ)) ∧
      (∀ j, eLpNorm (D j) 2 (cylMeasL c) < ⊤) ∧
      (∀ j, eLpNorm (fun x => (ν : ℂ) * D j x) 2 (cellMeasure c) ≤
        ENNReal.ofReal (C0 * (2 / σ * (1 + 2 * H1) * ‖g‖ +
          ‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖UnforcedLeray.B0225.R0 hc ν μ g‖) +
            3 * M0 / σ * (1 + 2 * H1) * ‖UnforcedLeray.B0225.R0 hc ν μ g‖))) := by
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  set V : HSpace c MeridC := UnforcedLeray.B0225.R0 hc ν μ g with hVdef
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cylHeat_hyps hc hσ hσH μ V g i
  obtain ⟨Dt, D2, -, hD2pm, -, hD2w, -, hD2b⟩ :=
    hC0 ν c hν hc _ _ h1 h2 h3 h4 h5 h6 (isCylHeat_uCut hc hν hσ hσH hμ g i)
  have hofr : ENNReal.ofReal 2 = 2 := by norm_num
  rw [hofr] at h6
  have hb : ∀ j, eLpNorm (fun x => (ν : ℂ) * D2 j j x) 2 (cylMeasL c) ≤
      ENNReal.ofReal C0 * eLpNorm (fCut c σ H1 μ (V : Profile → MeridC) (g : Profile → MeridC) i)
        2 (cylMeasL c) := fun j => by
    have := hD2b j j
    rwa [hofr] at this
  set Kf : ℝ := 2 / σ * (1 + 2 * H1) * ‖g‖ + ‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖V‖) +
    3 * M0 / σ * (1 + 2 * H1) * ‖V‖ with hKfdef
  have hfcell := eLpNorm_fCut_le hc hσ hσH hM0n hM0 μ V g i
  refine ⟨fun j => D2 j j, fun j => hD2pm j j, fun j φ hφ => hD2w j j φ hφ, fun j => ?_,
    fun j => ?_⟩
  · have hne : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    have heq : D2 j j = (ν : ℂ)⁻¹ • (fun x => (ν : ℂ) * D2 j j x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    change eLpNorm (D2 j j) 2 (cylMeasL c) < ⊤
    rw [heq, eLpNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top
      ((hb j).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h6))
  · have hper : QPeriodicSL c (fun x => (ν : ℂ) * D2 j j x) := by
      filter_upwards [(hD2pm j j).1] with x hx
      rw [hx]
    have hFper := fCut_periodic (σ := σ) (H1 := H1) hc μ (V : Profile → MeridC)
      (g : Profile → MeridC) i
    have hFpos : ∀ x : Coord, x.1 ≤ 0 →
        fCut c σ H1 μ (V : Profile → MeridC) (g : Profile → MeridC) i x = 0 := fun x hx =>
      fCut_zero (c := c) (x := x) hσ hH μ _ _ i fun h => by linarith [h.1]
    have hsq : eLpNorm (fun x => (ν : ℂ) * D2 j j x) 2 (cellMeasure c) ^ (2 : ℝ) ≤
        ENNReal.ofReal (C0 * Kf) ^ (2 : ℝ) := by
      calc eLpNorm (fun x => (ν : ℂ) * D2 j j x) 2 (cellMeasure c) ^ (2 : ℝ)
          ≤ ENNReal.ofReal c * eLpNorm (fun x => (ν : ℂ) * D2 j j x) 2 (cylMeasL c) ^ (2 : ℝ) :=
            eLpNorm_cell_sq_le hc hper
        _ ≤ ENNReal.ofReal c * (ENNReal.ofReal C0 * eLpNorm (fCut c σ H1 μ (V : Profile → MeridC)
              (g : Profile → MeridC) i) 2 (cylMeasL c)) ^ (2 : ℝ) := by
            gcongr
            exact hb j
        _ = ENNReal.ofReal C0 ^ (2 : ℝ) * (ENNReal.ofReal c * eLpNorm (fCut c σ H1 μ
              (V : Profile → MeridC) (g : Profile → MeridC) i) 2 (cylMeasL c) ^ (2 : ℝ)) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
            ring
        _ = ENNReal.ofReal C0 ^ (2 : ℝ) * eLpNorm (fCut c σ H1 μ (V : Profile → MeridC)
              (g : Profile → MeridC) i) 2 (cellMeasure c) ^ (2 : ℝ) := by
            have hcc : ∀ X : ℝ≥0∞, ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * X) = X := fun X => by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
                one_mul]
            rw [eLpNorm_cyl_sq_eq hc hFper hFpos, hcc]
        _ ≤ ENNReal.ofReal C0 ^ (2 : ℝ) * ENNReal.ofReal Kf ^ (2 : ℝ) := by
            gcongr
        _ = ENNReal.ofReal (C0 * Kf) ^ (2 : ℝ) := by
            rw [ENNReal.ofReal_mul hC0pos.le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 hsq

end UnforcedLeray.Short.PartIIa.FBCLL
