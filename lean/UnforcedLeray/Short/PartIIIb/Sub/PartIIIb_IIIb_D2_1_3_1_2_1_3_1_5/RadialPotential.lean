import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ParamT
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.RadialV

/-!
# `RadialPotential`

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  With `b(z) = γ(|z|²)` (`RadialV.lean`), `V(z) = -½B(|z|²)`
(`∇V = z b(z)`), the potential is `u(z) = ∫_{1/2}^1 V(r z) dr = T₀ V`, and
`Δu = T₂(ΔV) = ∫_0^1 d/dt[c(t)³ b(c(t) z)] dt = b(z) - b(z/2)/8 = b - b_{(2)}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Spatial partial derivative `∂_j f`. -/
def sd (j : Fin 3) (f : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ f y (coordinateVector j)

theorem radialPot_contDiff_sd (j : Fin 3) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (sd j f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem dy_liftS (j : Fin 3) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    UnforcedLeray.PhaseSpace.dy j (liftS f) = liftS (sd j f) := by
  funext p
  have h1 : HasFDerivAt (liftS f)
      (Complex.ofRealCLM.comp ((fderiv ℝ f p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p
      ((hf.differentiable (by simp) p.2).hasFDerivAt.comp p (hasFDerivAt_snd))
  unfold UnforcedLeray.PhaseSpace.dy
  rw [h1.fderiv]
  simp [liftS, sd]

theorem lapT_liftS (u : Space → ℝ) (hu : ContDiff ℝ ∞ u) (x : ℝ × Space) :
    lapT (liftS u) x = ((∑ j : Fin 3, sd j (sd j u) x.2 : ℝ) : ℂ) := by
  unfold UnforcedLeray.PhaseSpace.lapT
  simp only [dy_liftS _ hu, dy_liftS _ (radialPot_contDiff_sd _ hu), liftS]
  push_cast
  rfl

theorem sd_Tk (j : Fin 3) (k : ℕ) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    sd j (Tk k f) = Tk (k + 1) (sd j f) := by
  funext z
  exact fderiv_Tk k hf z _

theorem Tk_sum {k : ℕ} {g : Fin 3 → Space → ℝ} (hg : ∀ j, ContDiff ℝ ∞ (g j)) (z : Space) :
    ∑ j, Tk k (g j) z = ∫ t in (0 : ℝ)..1, (1 / 2) * cc t ^ k * ∑ j, g j (cc t • z) := by
  unfold Tk
  rw [← intervalIntegral.integral_finsetSum]
  · simp [Finset.mul_sum]
  · intro j _
    have := contDiff_cc.continuous
    have := (hg j).continuous
    exact (by fun_prop : Continuous fun t : ℝ => (1 / 2) * cc t ^ k * g j (cc t • z)).intervalIntegrable 0 1

theorem sd_radV (j : Fin 3) : sd j radV = fun y => radB y * y j := by
  funext y
  simp only [sd, radV_fderiv, coordinateVector, EuclideanSpace.inner_single_right]
  simp

theorem sdsd_radV_sum (w : Space) :
    ∑ j : Fin 3, sd j (sd j radV) w = 3 * radB w + fderiv ℝ radB w w := by
  have hj : ∀ j : Fin 3, sd j (sd j radV) w = fderiv ℝ radB w (coordinateVector j) * w j + radB w := by
    intro j
    rw [sd_radV]
    have h1 : HasFDerivAt (fun y : Space => radB y * y j)
        (radB w • (EuclideanSpace.proj j : Space →L[ℝ] ℝ) +
          (w j) • fderiv ℝ radB w) w :=
      ((radB_contDiff.differentiable (by simp) w).hasFDerivAt).mul
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
    simp only [sd]
    rw [h1.fderiv]
    simp [coordinateVector]
    ring
  simp only [hj, Finset.sum_add_distrib]
  have hw : w = ∑ j : Fin 3, w j • coordinateVector j := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  have : fderiv ℝ radB w w = ∑ j : Fin 3, w j * fderiv ℝ radB w (coordinateVector j) := by
    refine (congrArg (fderiv ℝ radB w) hw).trans ?_
    simp [map_sum]
  rw [this]
  simp [mul_comm]
  ring

theorem Tk2_ftc (z : Space) :
    ∫ t in (0 : ℝ)..1, (1 / 2) * cc t ^ 2 * (3 * radB (cc t • z) + fderiv ℝ radB (cc t • z) (cc t • z))
      = radB z - (2⁻¹ : ℝ) ^ 3 * radB ((2⁻¹ : ℝ) • z) := by
  have hcc : ∀ t, HasDerivAt cc (1 / 2 : ℝ) t := by
    intro t
    unfold cc
    have := ((hasDerivAt_id t).const_add 1).div_const 2
    simpa using this
  have hF : ∀ t, HasDerivAt (fun t => cc t ^ 3 * radB (cc t • z))
      ((1 / 2) * cc t ^ 2 * (3 * radB (cc t • z) + fderiv ℝ radB (cc t • z) (cc t • z))) t := by
    intro t
    have h1 : HasDerivAt (fun t => cc t • z) ((1 / 2 : ℝ) • z) t := (hcc t).smul_const z
    have h2 := (radB_contDiff.differentiable (by simp) (cc t • z)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := ((hcc t).pow 3).mul h2
    refine h3.congr_deriv ?_
    simp only [Function.comp, Pi.pow_apply, Pi.mul_apply, map_smul, smul_eq_mul, Nat.cast_ofNat]
    ring
  have hc : Continuous fun t : ℝ => (1 / 2) * cc t ^ 2 *
      (3 * radB (cc t • z) + fderiv ℝ radB (cc t • z) (cc t • z)) := by
    have := contDiff_cc.continuous
    have h1 : Continuous radB := radB_contDiff.continuous
    have h2 : Continuous (fun y => fderiv ℝ radB y) := radB_contDiff.continuous_fderiv (by simp)
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hc.intervalIntegrable _ _)]
  have c1 : cc 1 = 1 := by unfold cc; norm_num
  have c0 : cc 0 = 2⁻¹ := by unfold cc; norm_num
  simp [c1, c0]

theorem radU_laplacian (z : Space) :
    ∑ j : Fin 3, sd j (sd j (Tk 0 radV)) z = radB z - (2⁻¹ : ℝ) ^ 3 * radB ((2⁻¹ : ℝ) • z) := by
  have e1 : ∀ j, sd j (sd j (Tk 0 radV)) = Tk 2 (sd j (sd j radV)) := by
    intro j
    rw [sd_Tk j 0 radV_contDiff, sd_Tk j 1 (radialPot_contDiff_sd j radV_contDiff)]
  simp only [e1]
  rw [Tk_sum (fun j => radialPot_contDiff_sd j (radialPot_contDiff_sd j radV_contDiff))]
  rw [← Tk2_ftc z]
  congr 1
  funext t
  rw [sdsd_radV_sum]

theorem radU_support : HasCompactSupport (Tk 0 radV) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2) fun z hz => ?_
  have hz2 : 2 < ‖z‖ := by simpa using hz
  unfold Tk
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
  · simp
  · rw [uIcc_of_le zero_le_one] at ht
    have hcc : 1 / 2 ≤ cc t := by unfold cc; linarith [ht.1]
    have hn : 1 < ‖cc t • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith
    have : radV (cc t • z) = 0 := by
      unfold radV
      rw [radBB_zero_of_one_le (by nlinarith), mul_zero]
    simp [this]

theorem radialPotential : UnforcedLeray.Short.PartIIIb.Concrete.RadialPotential := by
  refine ⟨radB, Tk 0 radV, radB_nonneg, ⟨radB_contDiff, radB_support⟩,
    ⟨contDiff_Tk 0 radV_contDiff, radU_support⟩, radB_integral, fun x => ?_⟩
  rw [lapT_liftS _ (contDiff_Tk 0 radV_contDiff), radU_laplacian]
  simp [dilK]

end UnforcedLeray.Short.PartIIIb.Concrete
