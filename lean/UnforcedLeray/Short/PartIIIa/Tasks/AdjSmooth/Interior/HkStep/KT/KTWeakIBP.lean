import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTWeakIBP`: integration by parts against a smooth bounded field on the cell

Source: `the November 2 reference manuscript` (SP) lines 3052-3058.

The cutoff `x ↦ cutB (x.2 / R)` equals `1` on `|x.2| ≤ R` and `0` on `|x.2| ≥ 2R`. Testing the
weak derivative against `G * cutB(x.2/R)` gives an identity for each `R > 0`; the error term
carries the derivative of the cutoff, which is `O(1/R)`, and `R → ∞` is taken by dominated
convergence.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace KTWeakIBPAux

/-! ### The cutoff profile -/

/-- A smooth bump: `1` on `|t| ≤ 1`, `0` for `|t| ≥ 2`. -/
def cutB : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma cutB_contDiff : ContDiff ℝ ∞ cutB := cutB.contDiff

lemma cutB_nonneg (t : ℝ) : 0 ≤ cutB t := cutB.nonneg

lemma cutB_le_one (t : ℝ) : cutB t ≤ 1 := cutB.le_one

lemma cutB_one {t : ℝ} (ht : |t| ≤ 1) : cutB t = 1 := by
  apply cutB.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact ht

lemma cutB_zero {t : ℝ} (ht : 2 ≤ |t|) : cutB t = 0 := by
  apply cutB.zero_of_le_dist
  rw [Real.dist_eq, sub_zero]
  exact ht

lemma cutB_deriv_bound : ∃ D : ℝ, ∀ t : ℝ, |deriv cutB t| ≤ D := by
  have hc : Continuous (deriv cutB) := cutB_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv cutB) := cutB.hasCompactSupport.deriv
  obtain ⟨D, hD⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨D, fun t => by rw [← Real.norm_eq_abs]; exact hD t⟩

/-! ### The scaled cutoff `x ↦ cutB (x.2 / R)` -/

lemma cut_smooth (R : ℝ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => cutB (x.2 / R)) :=
  cutB_contDiff.comp (contDiff_snd.div_const R)

lemma cut_cont (R : ℝ) : Continuous (fun x : ℝ × ℝ => cutB (x.2 / R)) :=
  (cut_smooth R).continuous

lemma cut_abs_le_one (R : ℝ) (x : ℝ × ℝ) : |cutB (x.2 / R)| ≤ 1 := by
  rw [abs_of_nonneg (cutB_nonneg _)]
  exact cutB_le_one _

lemma cut_eq_one {R : ℝ} (hR : 0 < R) {t : ℝ} (h : |t| ≤ R) : cutB (t / R) = 1 := by
  apply cutB_one
  rw [abs_div, abs_of_pos hR]
  exact (div_le_one hR).2 h

lemma cut_eq_zero {R : ℝ} (hR : 0 < R) {t : ℝ} (h : 2 * R < |t|) : cutB (t / R) = 0 := by
  apply cutB_zero
  rw [abs_div, abs_of_pos hR]
  exact (le_div_iff₀ hR).2 h.le

lemma cut_tendsto_one (t : ℝ) : Tendsto (fun R : ℝ => cutB (t / R)) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop |t|, eventually_gt_atTop 0] with R h1 h2
  exact (cut_eq_one h2 h1).symm

/-! ### Partial derivatives of the cutoff -/

lemma pd0_eq' {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (x : ℝ × ℝ) {D : ℝ}
    (h : HasDerivAt (fun t => ψ (t, x.2)) D x.1) : B0579.pd 0 ψ x = D := by
  have hc : HasDerivAt (fun t : ℝ => ((t, x.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x.1 :=
    (hasDerivAt_id' x.1).prodMk (hasDerivAt_const x.1 x.2)
  have h2 := (hψ (x.1, x.2)).hasFDerivAt.comp_hasDerivAt x.1 hc
  have hdir : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]
  have h3 : HasDerivAt (fun t => ψ (t, x.2)) (fderiv ℝ ψ (x.1, x.2) ((1 : ℝ), (0 : ℝ))) x.1 := h2
  unfold B0579.pd
  rw [hdir]
  exact h3.unique h

lemma pd1_eq' {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (x : ℝ × ℝ) {D : ℝ}
    (h : HasDerivAt (fun s => ψ (x.1, s)) D x.2) : B0579.pd 1 ψ x = D := by
  have hc : HasDerivAt (fun s : ℝ => ((x.1, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id' x.2)
  have h2 := (hψ (x.1, x.2)).hasFDerivAt.comp_hasDerivAt x.2 hc
  have hdir : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]
  have h3 : HasDerivAt (fun s => ψ (x.1, s)) (fderiv ℝ ψ (x.1, x.2) ((0 : ℝ), (1 : ℝ))) x.2 := h2
  unfold B0579.pd
  rw [hdir]
  exact h3.unique h

lemma pd_cut_zero (R : ℝ) (x : ℝ × ℝ) : B0579.pd 0 (fun y : ℝ × ℝ => cutB (y.2 / R)) x = 0 := by
  apply pd0_eq' ((cut_smooth R).differentiable (by simp)) x
  exact hasDerivAt_const x.1 (cutB (x.2 / R))

lemma pd_cut_one (R : ℝ) (x : ℝ × ℝ) :
    B0579.pd 1 (fun y : ℝ × ℝ => cutB (y.2 / R)) x = deriv cutB (x.2 / R) / R := by
  have hψ : Differentiable ℝ (fun y : ℝ × ℝ => cutB (y.2 / R)) :=
    (cut_smooth R).differentiable (by simp)
  apply pd1_eq' hψ x
  have h1 : HasDerivAt cutB (deriv cutB (x.2 / R)) (x.2 / R) :=
    ((cutB_contDiff.differentiable (by simp)) _).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => s / R) (1 / R) x.2 := (hasDerivAt_id x.2).div_const R
  have h3 := h1.comp x.2 h2
  have e : deriv cutB (x.2 / R) * (1 / R) = deriv cutB (x.2 / R) / R := by ring
  rw [e] at h3
  exact h3

lemma pd_cut_abs_le {D : ℝ} (hD : ∀ t, |deriv cutB t| ≤ D) {R : ℝ} (hR : 0 < R) (k : Fin 2)
    (x : ℝ × ℝ) : |B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x| ≤ D / R := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  · rw [pd_cut_zero, abs_zero]
    exact div_nonneg hD0 hR.le
  · rw [pd_cut_one, abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right (hD _) hR.le

/-! ### Test functions and elementary bounds -/

lemma isCylTest_cutG {c R : ℝ} (hR : 0 < R) {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hper : ∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) :
    B0579.IsCylTest c (fun x => G x * cutB (x.2 / R)) where
  smooth := hG.mul (cut_smooth R)
  periodic x := by
    show G (x.1 + c, x.2) * cutB (x.2 / R) = G x * cutB (x.2 / R)
    rw [hper x]
  band := ⟨2 * R, fun x hx => by
    show G x * cutB (x.2 / R) = 0
    rw [cut_eq_zero hR hx, mul_zero]⟩

lemma continuous_pd_of {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (k : Fin 2) :
    Continuous (B0579.pd k H) := by
  unfold B0579.pd
  exact (hH.continuous_fderiv (by simp)).clm_apply continuous_const

lemma abs_mul_le_mul' {a b M N : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ N) : |a * b| ≤ M * N := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma abs_mul_le_of_le_one {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ 1) : |a * b| ≤ M :=
  (abs_mul_le_mul' ha hb).trans_eq (mul_one M)

/-- Integrability of `F` times a bounded continuous real factor on the cell. -/
lemma integrable_mul_bdd_cell {c : ℝ} {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F (B0579.cell c))
    {w : ℝ × ℝ → ℝ} (hw : Continuous w) {M : ℝ} (hM : ∀ x, |w x| ≤ M) :
    IntegrableOn (fun x => F x * ((w x : ℝ) : ℂ)) (B0579.cell c) := by
  refine Integrable.mul_bdd (c := M) hF (Complex.continuous_ofReal.comp hw).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  show ‖((w x : ℝ) : ℂ)‖ ≤ M
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hM x

/-! ### Dominated convergence for the two limits -/

/-- The main term: `∫ h · (u · χ_R) → ∫ h · u` as `R → ∞`. -/
lemma tendsto_cutMul {c : ℝ} {h : ℝ × ℝ → ℂ} (hh : IntegrableOn h (B0579.cell c))
    {u : ℝ × ℝ → ℝ} {M : ℝ} (hu : Continuous u) (hM : ∀ x, |u x| ≤ M) :
    Tendsto (fun R : ℝ => ∫ x in B0579.cell c, h x * ((u x * cutB (x.2 / R) : ℝ) : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, h x * ((u x : ℝ) : ℂ))) := by
  have hcont : ∀ R : ℝ, Continuous (fun x : ℝ × ℝ => ((u x * cutB (x.2 / R) : ℝ) : ℂ)) :=
    fun R => Complex.continuous_ofReal.comp (hu.mul (cut_cont R))
  have hb : ∀ R : ℝ, ∀ x : ℝ × ℝ, ‖((u x * cutB (x.2 / R) : ℝ) : ℂ)‖ ≤ M := fun R x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_mul_le_of_le_one (hM x) (cut_abs_le_one R x)
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖h x‖ * M)
  · exact Filter.Eventually.of_forall fun R =>
      (Integrable.aestronglyMeasurable hh).mul (hcont R).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun R => ae_of_all _ fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb R x) (norm_nonneg _)
  · exact Integrable.mul_const (Integrable.norm hh) M
  · refine ae_of_all _ fun x => ?_
    have ht : Tendsto (fun R : ℝ => ((u x * cutB (x.2 / R) : ℝ) : ℂ)) atTop
        (𝓝 ((u x * 1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul (cut_tendsto_one x.2))
    have := (tendsto_const_nhds (x := h x)).mul ht
    simpa only [mul_one] using this

/-- The error term: `∫ F · (G · ∂_k χ_R) → 0`, as `∂_k χ_R = O(1/R)`. -/
lemma err_tendsto {c : ℝ} {F : ℝ × ℝ → ℂ} (hFi : IntegrableOn F (B0579.cell c))
    {G : ℝ × ℝ → ℝ} {M : ℝ} (hGM : ∀ x, |G x| ≤ M) {D : ℝ}
    (hD : ∀ t, |deriv cutB t| ≤ D) (k : Fin 2) :
    Tendsto (fun R : ℝ => ∫ x in B0579.cell c,
        F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ)) atTop (𝓝 0) := by
  have key : ∀ R : ℝ, 0 < R →
      ‖∫ x in B0579.cell c,
        F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ)‖ ≤
        (∫ x in B0579.cell c, ‖F x‖) * (M * (D / R)) := by
    intro R hR
    have hg : Integrable (fun x => ‖F x‖ * (M * (D / R))) (volume.restrict (B0579.cell c)) :=
      Integrable.mul_const (Integrable.norm hFi) _
    have hle : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        ‖F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ)‖ ≤
          ‖F x‖ * (M * (D / R)) := ae_of_all _ fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (abs_mul_le_mul' (hGM x) (pd_cut_abs_le hD hR k x)) (norm_nonneg _)
    have := norm_integral_le_of_norm_le hg hle
    rw [integral_mul_const] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact key R hR
  · have hd : Tendsto (fun R : ℝ => D / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (hd.const_mul M).const_mul (∫ x in B0579.cell c, ‖F x‖)
    simpa using h2

end KTWeakIBPAux

open KTWeakIBPAux

/-! ### The theorem -/

theorem ktWeakIBP : UnforcedLeray.Short.IIIa.KTWeakIBP := by
  intro c _hc k F g' G hF hFi hgi hG hper hbd
  obtain ⟨M, hM⟩ := hbd
  have hGM : ∀ x, |G x| ≤ M := fun x => (hM x).1
  have hpdM : ∀ x, |B0579.pd k G x| ≤ M := fun x => (hM x).2
  obtain ⟨D, hD⟩ := cutB_deriv_bound
  have hGc : Continuous G := hG.continuous
  have hpdc : Continuous (B0579.pd k G) := continuous_pd_of hG k
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hF2 : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, F x * (B0579.pd k ψ x : ℂ) =
        -∫ x in B0579.cell c, g' x * (ψ x : ℂ) := by
    have hF' := hF
    unfold HasWeakCellDerivC at hF'
    exact hF'.2
  have hI1 : IntegrableOn (fun x => F x * (B0579.pd k G x : ℂ)) (B0579.cell c) :=
    integrable_mul_bdd_cell hFi hpdc hpdM
  have hI2 : IntegrableOn (fun x => g' x * (G x : ℂ)) (B0579.cell c) :=
    integrable_mul_bdd_cell hgi hGc hGM
  have hid : ∀ R : ℝ, 0 < R →
      (∫ x in B0579.cell c, F x * ((B0579.pd k G x * cutB (x.2 / R) : ℝ) : ℂ)) +
        (∫ x in B0579.cell c,
          F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ)) =
      -∫ x in B0579.cell c, g' x * ((G x * cutB (x.2 / R) : ℝ) : ℂ) := by
    intro R hR
    have hcut : Differentiable ℝ (fun y : ℝ × ℝ => cutB (y.2 / R)) :=
      (cut_smooth R).differentiable (by simp)
    have hψ : B0579.IsCylTest c (fun x => G x * cutB (x.2 / R)) :=
      isCylTest_cutG hR hG hper
    have h1 : ∫ x in B0579.cell c,
        F x * ((B0579.pd k (fun x => G x * cutB (x.2 / R)) x : ℝ) : ℂ) =
        -∫ x in B0579.cell c, g' x * ((G x * cutB (x.2 / R) : ℝ) : ℂ) := hF2 _ hψ
    have hp : ∀ x : ℝ × ℝ, B0579.pd k (fun y => G y * cutB (y.2 / R)) x =
        B0579.pd k G x * cutB (x.2 / R) + G x * B0579.pd k (fun y => cutB (y.2 / R)) x :=
      fun x => B0579.pd_mul hGd hcut k x
    have hP1 : IntegrableOn (fun x => F x * ((B0579.pd k G x * cutB (x.2 / R) : ℝ) : ℂ))
        (B0579.cell c) :=
      integrable_mul_bdd_cell hFi
        (hpdc.mul (cut_cont R)) (fun x => abs_mul_le_of_le_one (hpdM x) (cut_abs_le_one R x))
    have hP2 : IntegrableOn
        (fun x => F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ))
        (B0579.cell c) :=
      integrable_mul_bdd_cell hFi (hGc.mul (continuous_pd_of (cut_smooth R) k))
        (fun x => abs_mul_le_mul' (hGM x) (pd_cut_abs_le hD hR k x))
    have hsplit : ∫ x in B0579.cell c,
        F x * ((B0579.pd k (fun x => G x * cutB (x.2 / R)) x : ℝ) : ℂ) =
        (∫ x in B0579.cell c, F x * ((B0579.pd k G x * cutB (x.2 / R) : ℝ) : ℂ)) +
        ∫ x in B0579.cell c,
          F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ) := by
      rw [← integral_add hP1 hP2]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [hp x]
        push_cast
        ring
    rw [← hsplit]
    exact h1
  have hA := tendsto_cutMul hFi hpdc hpdM
  have hE := err_tendsto hFi hGM hD k
  have hQ := tendsto_cutMul hgi hGc hGM
  have hsum := hA.add hE
  have hneg := hQ.neg
  have heq : (fun R : ℝ =>
      (∫ x in B0579.cell c, F x * ((B0579.pd k G x * cutB (x.2 / R) : ℝ) : ℂ)) +
        ∫ x in B0579.cell c,
          F x * ((G x * B0579.pd k (fun y : ℝ × ℝ => cutB (y.2 / R)) x : ℝ) : ℂ)) =ᶠ[atTop]
      (fun R : ℝ => -∫ x in B0579.cell c, g' x * ((G x * cutB (x.2 / R) : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact hid R hR
  have hlim := tendsto_nhds_unique (hsum.congr' heq) hneg
  refine ⟨hI1, hI2, ?_⟩
  simp only [add_zero] at hlim
  exact hlim

end UnforcedLeray.Short.IIIa
