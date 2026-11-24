import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.FriedDeriv
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2/5`: the first moment of `∇ρ_n` (`stMolMoment`)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(the regularization; Friedrichs' lemma needs `∫ |∇ρ_n(z)| |z| dz` bounded in `n`).

Route: with `s = n + 1`, the normalized bump scales, `molKer n x = s² molKer 0 (s • x)`
(`smm_molKer_scale`: `molBump n x = molBump 0 (s • x)` and the Haar scaling of the normalizing
integral).  Then `∂_l molKer n y = s³ (∂_l molKer 0)(s • y)` (`smm_pd_scale`), and the substitution
`z = s • y` gives the exact identity `∫ |∂_l molKer n| ‖y‖ = ∫ |∂_l molKer 0| ‖z‖` (`smm_integral_eq`),
so `C = Σ_l ∫ |∂_l molKer 0| ‖z‖` works for every `n`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The radius identities of the bump of `molKer n`. -/
theorem smm_rIn (n : ℕ) : (molBump n).rIn = 1 / (2 * ((n : ℝ) + 1)) := rfl

theorem smm_rOut (n : ℕ) : (molBump n).rOut = 1 / ((n : ℝ) + 1) := rfl

theorem smm_ratio (n : ℕ) : (molBump n).rOut / (molBump n).rIn = 2 := by
  rw [smm_rIn, smm_rOut]
  have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp

theorem smm_inv (n : ℕ) : (molBump n).rIn⁻¹ = 2 * ((n : ℝ) + 1) := by
  rw [smm_rIn]
  have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp

/-- `molBump n x = molBump 0 (s • x)` with `s = n + 1`. -/
theorem smm_bump_scale (n : ℕ) (x : ℝ × ℝ) :
    molBump n x = molBump 0 (((n : ℝ) + 1) • x) := by
  rw [ContDiffBump.apply (molBump n) x, ContDiffBump.apply (molBump 0) (((n : ℝ) + 1) • x),
    smm_ratio n, smm_ratio 0, smm_inv n, smm_inv 0]
  simp only [sub_zero, smul_smul, Nat.cast_zero, zero_add, mul_one]

/-- The integral of the bump at scale `n`. -/
theorem smm_integral_bump (n : ℕ) :
    ∫ y, molBump n y = (((n : ℝ) + 1) ^ 2)⁻¹ * ∫ y, molBump 0 y := by
  have hfun : (fun y => molBump n y) = fun y => molBump 0 (((n : ℝ) + 1) • y) :=
    funext (smm_bump_scale n)
  have hfr : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [hfun, Measure.integral_comp_smul volume (fun y => molBump 0 y) ((n : ℝ) + 1), hfr,
    abs_of_pos (inv_pos.2 (pow_pos hpos 2)), smul_eq_mul]

/-- `molKer n` is the rescaled `molKer 0`: `molKer n x = s² molKer 0 (s • x)`. -/
theorem smm_molKer_scale (n : ℕ) (x : ℝ × ℝ) :
    molKer n x = ((n : ℝ) + 1) ^ 2 * molKer 0 (((n : ℝ) + 1) • x) := by
  unfold molKer
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, smm_integral_bump n, smm_bump_scale n x]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- The derivative of a rescaled function. -/
theorem smm_pd_comp (l : Fin 2) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (s : ℝ) (y : ℝ × ℝ) :
    B0579.pd l (fun x => g (s • x)) y = s * B0579.pd l g (s • y) := by
  have h1 := (hg.differentiable (by simp) (s • y)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => s • x) (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul s
  have h := h1.comp y h2
  have key : fderiv ℝ (fun x : ℝ × ℝ => g (s • x)) y =
      (fderiv ℝ g (s • y)).comp (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)) := h.fderiv
  unfold B0579.pd
  rw [key]
  simp

/-- The derivative of `s² g(s • ·)`. -/
theorem smm_pd_scale (l : Fin 2) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (A s : ℝ) (y : ℝ × ℝ) :
    B0579.pd l (fun x => A * g (s • x)) y = A * (s * B0579.pd l g (s • y)) := by
  have hd : Differentiable ℝ (fun x : ℝ × ℝ => g (s • x)) := by
    intro x
    exact ((hg.differentiable (by simp)) (s • x)).comp x
      ((hasFDerivAt_id x).const_smul s).differentiableAt
  rw [← smm_pd_comp l hg s y]
  unfold B0579.pd
  have hdiff : HasFDerivAt (fun x : ℝ × ℝ => g (s • x))
      (fderiv ℝ (fun x : ℝ × ℝ => g (s • x)) y) y :=
    (hd y).hasFDerivAt
  rw [((hdiff.const_mul A)).fderiv]
  simp

/-- The pointwise identity behind the substitution. -/
theorem smm_pointwise (n : ℕ) (l : Fin 2) (y : ℝ × ℝ) :
    |B0579.pd l (molKer n) y| * ‖y‖ =
      ((n : ℝ) + 1) ^ 2 * (|B0579.pd l (molKer 0) (((n : ℝ) + 1) • y)| *
        ‖((n : ℝ) + 1) • y‖) := by
  have hmol : molKer n = fun x => ((n : ℝ) + 1) ^ 2 * molKer 0 (((n : ℝ) + 1) • x) :=
    funext (smm_molKer_scale n)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpd : B0579.pd l (molKer n) y =
      ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) * B0579.pd l (molKer 0) (((n : ℝ) + 1) • y)) := by
    rw [hmol]
    exact smm_pd_scale l (st_molKer_contDiff 0) _ _ y
  rw [hpd, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  simp only [abs_mul, abs_of_pos hpos, abs_of_pos (pow_pos hpos 2)]
  ring

/-- The exact scaling identity for the first moment (independent of `n`). -/
theorem smm_integral_eq (n : ℕ) (l : Fin 2) :
    ∫ y, |B0579.pd l (molKer n) y| * ‖y‖ = ∫ y, |B0579.pd l (molKer 0) y| * ‖y‖ := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfr : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  calc ∫ y, |B0579.pd l (molKer n) y| * ‖y‖
      = ∫ y, ((n : ℝ) + 1) ^ 2 * (|B0579.pd l (molKer 0) (((n : ℝ) + 1) • y)| *
          ‖((n : ℝ) + 1) • y‖) :=
        integral_congr_ae (ae_of_all _ fun y => smm_pointwise n l y)
    _ = ((n : ℝ) + 1) ^ 2 * ∫ y, |B0579.pd l (molKer 0) (((n : ℝ) + 1) • y)| *
          ‖((n : ℝ) + 1) • y‖ := integral_const_mul _ _
    _ = ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ *
          ∫ y, |B0579.pd l (molKer 0) y| * ‖y‖ := by
        rw [Measure.integral_comp_smul volume (fun y => |B0579.pd l (molKer 0) y| * ‖y‖)
          ((n : ℝ) + 1),
          hfr, abs_of_pos (inv_pos.2 (pow_pos hpos 2)), smul_eq_mul]
        ring
    _ = ∫ y, |B0579.pd l (molKer 0) y| * ‖y‖ := by
        have hne : ((n : ℝ) + 1) ^ 2 ≠ 0 := (pow_pos hpos 2).ne'
        field_simp

/-- The support of `molKer n` is the open ball of radius `rOut`. -/
theorem smm_support (n : ℕ) : Function.support (molKer n) = Metric.ball 0 (molBump n).rOut :=
  (molBump n).support_normed_eq

theorem smm_vanish (n : ℕ) (l : Fin 2) (y : ℝ × ℝ) (hy : 1 < ‖y‖) :
    B0579.pd l (molKer n) y = 0 := by
  have hr : (molBump n).rOut ≤ 1 := by
    rw [smm_rOut]
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by linarith)]
    linarith
  have hlt : (molBump n).rOut < ‖y‖ := lt_of_le_of_lt hr hy
  have hev : molKer n =ᶠ[𝓝 y] (0 : ℝ × ℝ → ℝ) := by
    have hopen : IsOpen {z : ℝ × ℝ | (molBump n).rOut < ‖z‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds (show y ∈ {z : ℝ × ℝ | (molBump n).rOut < ‖z‖} from hlt)]
      with z hz
    simp only [Pi.zero_apply]
    by_contra hne
    have hmem : z ∈ Function.support (molKer n) := hne
    rw [smm_support n, Metric.mem_ball, dist_zero_right] at hmem
    have hz' : (molBump n).rOut < ‖z‖ := hz
    linarith
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

theorem smm_integrable (n : ℕ) (l : Fin 2) :
    Integrable (fun y => |B0579.pd l (molKer n) y| * ‖y‖) := by
  have hcd : ContDiff ℝ ∞ (B0579.pd l (molKer n)) := st_pd_contDiff (st_molKer_contDiff n) l
  have hc : Continuous (fun y => |B0579.pd l (molKer n) y| * ‖y‖) :=
    (hcd.continuous.abs).mul continuous_norm
  have hs : HasCompactSupport (B0579.pd l (molKer n)) :=
    HasCompactSupport.fderiv_apply ℝ (st_molKer_hasCompactSupport n) (B0579.dir l)
  exact hc.integrable_of_hasCompactSupport (hs.abs.mul_right)

/-- **(5) The first moment of `∇ρ_n` is bounded uniformly in `n`** (SP 3060-3071). -/
theorem stMolMoment : UnforcedLeray.Short.IIIa.StMolMoment := by
  refine ⟨(∫ y, |B0579.pd 0 (molKer 0) y| * ‖y‖) + (∫ y, |B0579.pd 1 (molKer 0) y| * ‖y‖), ?_⟩
  intro n l
  refine ⟨(st_pd_contDiff (st_molKer_contDiff n) l).continuous,
    fun y hy => smm_vanish n l y hy, smm_integrable n l, ?_⟩
  rw [smm_integral_eq n l]
  have h0 : 0 ≤ ∫ y, |B0579.pd 0 (molKer 0) y| * ‖y‖ :=
    integral_nonneg fun y => by positivity
  have h1 : 0 ≤ ∫ y, |B0579.pd 1 (molKer 0) y| * ‖y‖ :=
    integral_nonneg fun y => by positivity
  rcases (show l = 0 ∨ l = 1 by fin_cases l <;> simp) with rfl | rfl
  · linarith
  · linarith

end UnforcedLeray.Short.IIIa
