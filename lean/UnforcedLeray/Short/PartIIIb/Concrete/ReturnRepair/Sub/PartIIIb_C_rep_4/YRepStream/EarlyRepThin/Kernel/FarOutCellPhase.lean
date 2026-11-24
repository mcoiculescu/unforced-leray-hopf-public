import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.FarDomChart

/-!
# `farOutCellPhase` (source 2666-2689, 3611-3621, 3905-3912): one cell in `q` is one phase period.

With `τ = 2q/R + log s` and `P = 2c/R`, the cell `|q| < c/2` is one period; the masked
source is `P`-periodic in `τ`, hence so is the response `τ ↦ sepWfar … τ`; the change of
variables is the affine `lintegral_periodic_affine` (applied three times).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Periodicity of the separated response in the phase, for a `P`-periodic source. -/
theorem fco_sepW_periodic (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (P : ℝ)
    (hT : ∀ τ z, T (τ + P) z = T τ z) (y : Space) (τ : ℝ) :
    UnforcedLeray.Short.IIIa.sepW ν μ T y (τ + P) = UnforcedLeray.Short.IIIa.sepW ν μ T y τ := by
  unfold UnforcedLeray.Short.IIIa.sepW
  simp only [add_right_comm τ P, hT]

/-- The meridional far output, pointwise: `|s^{-1/2} Re(-w)|² ≤ 2 s^{-1} |w|²`. -/
theorem fco_norm_sq (s : ℝ) (hs : 0 < s) (v : Fin 3 → ℂ) :
    ‖(Real.sqrt s)⁻¹ • NearInst.merRe (-v)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * s⁻¹) * ‖v‖ₑ ^ (2 : ℝ) := by
  have ha : 0 ≤ (Real.sqrt s)⁻¹ := by positivity
  have hm := fd_merRe_bound v
  have hr : ((Real.sqrt s)⁻¹ * Real.sqrt 2) ^ 2 = 2 * s⁻¹ := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hs.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  calc ‖(Real.sqrt s)⁻¹ • NearInst.merRe (-v)‖ₑ ^ (2 : ℝ)
      = (ENNReal.ofReal (Real.sqrt s)⁻¹ * ‖NearInst.merRe (-v)‖ₑ) ^ (2 : ℝ) := by
        rw [enorm_smul, Real.enorm_eq_ofReal ha]
    _ ≤ (ENNReal.ofReal (Real.sqrt s)⁻¹ * (ENNReal.ofReal (Real.sqrt 2) * ‖v‖ₑ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hm zero_le) (by norm_num)
    _ = ENNReal.ofReal (2 * s⁻¹) * ‖v‖ₑ ^ (2 : ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg ha (Real.sqrt_nonneg 2)) (by norm_num),
          Real.rpow_two ((Real.sqrt s)⁻¹ * Real.sqrt 2), hr]

/-- The affine change of variables over one cell `|q| < c/2` (source 2666-2689): the cell is one
period of `τ = 2q/R + a` and `G` is `P`-periodic, `P = 2c/R`. -/
theorem fco_cell (R c a : ℝ) (hR : 0 < R) (hc : 0 < c) (G : ℝ → ℝ≥0∞)
    (hG : Function.Periodic G (2 * c / R)) :
    ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * G (2 * q / R + a) =
      (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), G τ := by
  have hR0 : R ≠ 0 := hR.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hP : 0 < 2 * c / R := by positivity
  have hper1 : Function.Periodic (fun q => G (2 * q / R + a)) c := by
    intro x
    show G (2 * (x + c) / R + a) = G (2 * x / R + a)
    have e : 2 * (x + c) / R + a = (2 * x / R + a) + 2 * c / R := by ring
    rw [e]
    exact hG _
  have s1 := UnforcedLeray.Axi.lintegral_periodic_affine hc one_pos
    (fun q => G (2 * q / R + a)) hper1 0
  simp only [div_one, one_mul, add_zero, inv_one, ENNReal.ofReal_one] at s1
  have hneg : -c / 2 = -(c / 2) := by ring
  rw [hneg] at s1
  have hPk : 2 * c / R / (2 / R) = c := by field_simp
  have s2 := UnforcedLeray.Axi.lintegral_periodic_affine hP (show (0 : ℝ) < 2 / R by positivity)
    G hG a
  rw [hPk] at s2
  have s3 := UnforcedLeray.Axi.lintegral_periodic_affine hP one_pos G hG 0
  simp only [div_one, one_mul, add_zero, inv_one, ENNReal.ofReal_one] at s3
  have e2 : ∫⁻ τ in Ioc 0 c, G (2 * τ / R + a) = ∫⁻ τ in Ioc 0 c, G (2 / R * τ + a) := by
    apply lintegral_congr
    intro τ
    congr 1
    ring
  have key : ∫⁻ q in Ico (-(c / 2)) (c / 2), G (2 * q / R + a) =
      ENNReal.ofReal (2 / R)⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), G τ := by
    rw [← s1, e2, s2, ← s3]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, key]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c⁻¹),
    ← ENNReal.ofReal_inv_of_pos hP]
  have hreal : c⁻¹ * (2 / R)⁻¹ = (2 * c / R)⁻¹ := by field_simp
  rw [hreal]

theorem farOutCellPhase : FarOutCellPhase := by
  intro R c ν μ δ S hR hc f s η hs
  by_cases hsS : s < S
  · rw [if_pos hsS]
    obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ≥0∞, ∀ τ, G τ =
        ‖NearInst.sepWfar ν (μ : ℂ) R δ s (NearInst.cartLift R c f)
          (NearInst.chartY R (s, (0, η))) τ‖ₑ ^ (2 : ℝ) := ⟨_, fun τ => rfl⟩
    have hGper : Function.Periodic G (2 * c / R) := by
      intro x
      rw [hGdef, hGdef]
      unfold NearInst.sepWfar
      rw [fco_sepW_periodic ν (μ : ℂ) _ (2 * c / R) ?_ _ x]
      intro τ z
      dsimp only
      rw [fd_cartLift_period R c hR hc f τ z]
    have hpt : ∀ q : ℝ, ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (2 * s⁻¹) * G (2 * q / R + Real.log s) := by
      intro q
      have h1 : NearInst.Masked.farOut R c ν μ δ S f (s, (q, η)) =
          (Real.sqrt s)⁻¹ • NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ s
            (NearInst.cartLift R c f) (NearInst.chartY R (s, (0, η))) (2 * q / R + Real.log s)) := by
        simp only [NearInst.Masked.farOut, hsS, if_true]
        rfl
      rw [h1, hGdef]
      exact fco_norm_sq s hs _
    have hfp : farPt R c ν μ δ f (s, (0, η)) ^ (2 : ℝ) =
        (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), G τ := by
      simp only [farPt, UnforcedLeray.Short.IIIa.ltauAt]
      rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
      simp only [hGdef]
    rw [hfp]
    calc ∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal (2 * s⁻¹) * (ENNReal.ofReal c⁻¹ * G (2 * q / R + Real.log s)) := by
          apply lintegral_mono
          intro q
          calc ENNReal.ofReal c⁻¹ * ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ)
              ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (2 * s⁻¹) * G (2 * q / R + Real.log s)) :=
                mul_le_mul_of_nonneg_left (hpt q) zero_le
            _ = ENNReal.ofReal (2 * s⁻¹) * (ENNReal.ofReal c⁻¹ * G (2 * q / R + Real.log s)) := by
                ring
      _ = ENNReal.ofReal (2 * s⁻¹) * ∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * G (2 * q / R + Real.log s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 * s⁻¹) * ((ENNReal.ofReal (2 * c / R))⁻¹ *
          ∫⁻ τ in Ioc 0 (2 * c / R), G τ) := by
          rw [fco_cell R c (Real.log s) hR hc G hGper]
  · rw [if_neg hsS]
    have hz : ∀ q : ℝ, ENNReal.ofReal c⁻¹ *
        ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ) = 0 := by
      intro q
      have h0 : NearInst.Masked.farOut R c ν μ δ S f (s, (q, η)) = 0 := by
        simp [NearInst.Masked.farOut, hsS]
      rw [h0, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2), mul_zero]
    have hI : ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ) = 0 := by
      simp only [hz, lintegral_zero]
    exact hI.le

end UnforcedLeray.Short.PartIIIb.Concrete
