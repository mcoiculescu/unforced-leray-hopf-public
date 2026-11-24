import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_of
import UnforcedLeray.Lib.LerayLp.Helmholtz

/-!
# `PartII-b:T10/org/2/3/3/6` (`CutoffCurlConverge`): `L^r` convergence of cutoff curls

Source `the November 2 reference manuscript` lines 1409-1412.  For `A` smooth with
`|A| ≲ (1+|x|)⁻²` and `|DA| ≲ (1+|x|)⁻³`, and `χ` smooth, compactly supported, `χ = 1` on the unit
ball, the cutoff curls `curl (χ(·/n) A)` converge to `curl A` in `L^r`, `1 < r < ∞`.

Pointwise: `χ(·/n) A = A` near `x` once `n > |x|`, so the curls agree eventually.  Uniform bound:
`|curl(χ(·/n)A) - curl A| ≲ (1+|x|)⁻³` uniformly in `n ≥ 0`, since the cutoff derivative
`n⁻¹ Dχ(x/n)` is supported in `|x| ≤ R n` (so `n⁻¹ ≤ C(1+|x|)⁻¹` there).  Dominated convergence in
`L^r` (`(1+|x|)⁻³ ∈ L^r`, `memLp_powWeight_three`) finishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

theorem cc_rpow_neg_two (x : Space) : (1 + ‖x‖) ^ (-2 : ℝ) = ((1 + ‖x‖) ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

theorem cc_rpow_neg_three (x : Space) : (1 + ‖x‖) ^ (-3 : ℝ) = ((1 + ‖x‖) ^ 3)⁻¹ := by
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

theorem cc_powWeight_three (x : Space) : powWeight 3 x = ((1 + ‖x‖) ^ 3)⁻¹ := by
  unfold powWeight
  exact cc_rpow_neg_three x

theorem cc_norm_const_pw (K : ℝ) (hK : 0 ≤ K) (x : Space) :
    ‖K * powWeight 3 x‖ = K * powWeight 3 x :=
  Real.norm_of_nonneg (mul_nonneg hK (powWeight_nonneg _ _))

theorem cc_inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr h)

/-- A vector with all coordinates bounded by `M` has norm at most `3 M`. -/
theorem cc_norm_le_three {v : CVec3} {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, ‖v i‖ ≤ M) :
    ‖v‖ ≤ 3 * M := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have s0 : ‖v 0‖ ^ 2 ≤ M ^ 2 := by nlinarith [h 0, norm_nonneg (v 0)]
  have s1 : ‖v 1‖ ^ 2 ≤ M ^ 2 := by nlinarith [h 1, norm_nonneg (v 1)]
  have s2 : ‖v 2‖ ^ 2 ≤ M ^ 2 := by nlinarith [h 2, norm_nonneg (v 2)]
  rw [Fin.sum_univ_three]
  nlinarith [sq_nonneg M]

theorem cc_coord_le (L : Space →L[ℝ] CVec3) (j k : Fin 3) :
    ‖L (EuclideanSpace.single j (1 : ℝ)) k‖ ≤ ‖L‖ := by
  calc ‖L (EuclideanSpace.single j (1 : ℝ)) k‖ ≤ ‖L (EuclideanSpace.single j (1 : ℝ))‖ :=
        PiLp.norm_apply_le _ _
    _ ≤ ‖L‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Space)‖ := L.le_opNorm _
    _ = ‖L‖ := by rw [EuclideanSpace.norm_single, norm_one, mul_one]

theorem cc_curl_sub_le {G H : Space → CVec3} (x : Space) :
    ‖curlC G x - curlC H x‖ ≤ 3 * (2 * ‖fderiv ℝ G x - fderiv ℝ H x‖) := by
  refine cc_norm_le_three (M := 2 * ‖fderiv ℝ G x - fderiv ℝ H x‖) (by positivity) ?_
  intro i
  have key : (curlC G x - curlC H x) i =
      (fderiv ℝ G x - fderiv ℝ H x) (EuclideanSpace.single (i + 1) (1 : ℝ)) (i + 2) -
      (fderiv ℝ G x - fderiv ℝ H x) (EuclideanSpace.single (i + 2) (1 : ℝ)) (i + 1) := by
    unfold curlC
    simp only [PiLp.sub_apply, PiLp.toLp_apply, ContinuousLinearMap.sub_apply]
    ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  linarith [cc_coord_le (fderiv ℝ G x - fderiv ℝ H x) (i + 1) (i + 2),
    cc_coord_le (fderiv ℝ G x - fderiv ℝ H x) (i + 2) (i + 1)]

theorem cc_curl_le (G : Space → CVec3) (x : Space) :
    ‖curlC G x‖ ≤ 3 * (2 * ‖fderiv ℝ G x‖) := by
  refine cc_norm_le_three (M := 2 * ‖fderiv ℝ G x‖) (by positivity) ?_
  intro i
  have key : curlC G x i =
      fderiv ℝ G x (EuclideanSpace.single (i + 1) (1 : ℝ)) (i + 2) -
      fderiv ℝ G x (EuclideanSpace.single (i + 2) (1 : ℝ)) (i + 1) := by
    unfold curlC
    rfl
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  linarith [cc_coord_le (fderiv ℝ G x) (i + 1) (i + 2), cc_coord_le (fderiv ℝ G x) (i + 2) (i + 1)]

theorem cc_continuous_curlC {G : Space → CVec3} (hG : ContDiff ℝ ∞ G) :
    Continuous (curlC G) := by
  have hd : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  have hc : ∀ (e : Space) (j : Fin 3), Continuous (fun x => fderiv ℝ G x e j) := by
    intro e j
    have h1 : Continuous (fun x => fderiv ℝ G x e) := hd.clm_apply continuous_const
    exact Continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j) h1
  have hf : Continuous (fun x : Space => fun i : Fin 3 =>
      fderiv ℝ G x (EuclideanSpace.single (i + 1) (1 : ℝ)) (i + 2) -
      fderiv ℝ G x (EuclideanSpace.single (i + 2) (1 : ℝ)) (i + 1)) :=
    continuous_pi fun i => (hc (EuclideanSpace.single (i + 1) (1 : ℝ)) (i + 2)).sub
      (hc (EuclideanSpace.single (i + 2) (1 : ℝ)) (i + 1))
  unfold curlC
  exact Continuous.comp (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)) hf

theorem cc_fderiv_sub_eq {χ : Space → ℝ} {A : Space → CVec3} (hχd : Differentiable ℝ χ)
    (hAd : Differentiable ℝ A) (c : ℝ) (x : Space) :
    fderiv ℝ (fun y => χ (c • y) • A y) x - fderiv ℝ A x =
      (χ (c • x) • fderiv ℝ A x - fderiv ℝ A x) +
        ((fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)).smulRight (A x) := by
  have h1 : HasFDerivAt (fun y => χ (c • y))
      ((fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)) x := by
    have := (hχd (c • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
    exact this
  have h2 : HasFDerivAt (fun y => χ (c • y) • A y)
      (χ (c • x) • fderiv ℝ A x +
        ((fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)).smulRight (A x)) x :=
    h1.smul (hAd x).hasFDerivAt
  rw [h2.fderiv]
  abel

theorem cc_norm_smulRight_le {L : Space →L[ℝ] ℝ} (v : CVec3) :
    ‖L.smulRight v‖ ≤ ‖L‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖L y‖ * ‖v‖ ≤ (‖L‖ * ‖y‖) * ‖v‖ := mul_le_mul_of_nonneg_right (L.le_opNorm y) (norm_nonneg _)
    _ = ‖L‖ * ‖v‖ * ‖y‖ := by ring

theorem cc_norm_c_comp_le {χ : Space → ℝ} (c : ℝ) (y : Space) (K1 : ℝ)
    (hK1 : ∀ z, ‖fderiv ℝ χ z‖ ≤ K1) :
    ‖(fderiv ℝ χ (c • y)).comp (c • ContinuousLinearMap.id ℝ Space)‖ ≤ K1 * |c| := by
  have hid : ‖c • ContinuousLinearMap.id ℝ Space‖ ≤ |c| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  calc ‖(fderiv ℝ χ (c • y)).comp (c • ContinuousLinearMap.id ℝ Space)‖
      ≤ ‖fderiv ℝ χ (c • y)‖ * ‖c • ContinuousLinearMap.id ℝ Space‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K1 * |c| := mul_le_mul (hK1 (c • y)) hid (norm_nonneg _)
        (le_trans (norm_nonneg _) (hK1 (c • y)))

theorem cc_key_bound {χ : Space → ℝ} (c : ℝ) (x : Space) (K1 Rp : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hK1 : 0 ≤ K1) (hRp : 0 ≤ Rp)
    (hK1b : ∀ z, ‖fderiv ℝ χ z‖ ≤ K1) (hz : ∀ z : Space, Rp < ‖z‖ → fderiv ℝ χ z = 0) :
    ‖(fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)‖ * ((1 + ‖x‖) ^ 2)⁻¹ ≤
      K1 * (1 + Rp) * ((1 + ‖x‖) ^ 3)⁻¹ := by
  by_cases hcx : Rp < ‖c • x‖
  · rw [hz _ hcx, ContinuousLinearMap.zero_comp, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg hK1 (by linarith)) (by positivity)
  · push_neg at hcx
    have hnorm : ‖c • x‖ = c * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    have hcx' : c * ‖x‖ ≤ Rp := by rw [← hnorm]; exact hcx
    have hct : c * (1 + ‖x‖) ≤ 1 + Rp := by nlinarith
    have ht : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have hL : ‖(fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)‖ ≤ K1 * c := by
      have := cc_norm_c_comp_le (χ := χ) c x K1 hK1b
      rwa [abs_of_nonneg hc0] at this
    have hc_le : c ≤ (1 + Rp) * (1 + ‖x‖)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ ht]
      linarith
    have hcw : c * ((1 + ‖x‖) ^ 2)⁻¹ ≤ (1 + Rp) * ((1 + ‖x‖) ^ 3)⁻¹ := by
      have h3 : ((1 + ‖x‖) ^ 3)⁻¹ = (1 + ‖x‖)⁻¹ * ((1 + ‖x‖) ^ 2)⁻¹ := by
        rw [← mul_inv]
        congr 1
        ring
      rw [h3]
      calc c * ((1 + ‖x‖) ^ 2)⁻¹ ≤ ((1 + Rp) * (1 + ‖x‖)⁻¹) * ((1 + ‖x‖) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hc_le (by positivity)
        _ = (1 + Rp) * ((1 + ‖x‖)⁻¹ * ((1 + ‖x‖) ^ 2)⁻¹) := by ring
    calc ‖(fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)‖ * ((1 + ‖x‖) ^ 2)⁻¹
        ≤ (K1 * c) * ((1 + ‖x‖) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = K1 * (c * ((1 + ‖x‖) ^ 2)⁻¹) := by ring
      _ ≤ K1 * ((1 + Rp) * ((1 + ‖x‖) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hcw hK1
      _ = K1 * (1 + Rp) * ((1 + ‖x‖) ^ 3)⁻¹ := by ring

theorem cc_fderiv_diff_le {χ : Space → ℝ} {A : Space → CVec3} (hχd : Differentiable ℝ χ)
    (hAd : Differentiable ℝ A) (c : ℝ) (x : Space) (K0 K1 Rp C2 C3 : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hRp : 0 ≤ Rp) (hC2 : 0 ≤ C2)
    (hχb : ∀ y, ‖χ y‖ ≤ K0) (hK1b : ∀ z, ‖fderiv ℝ χ z‖ ≤ K1)
    (hz : ∀ z : Space, Rp < ‖z‖ → fderiv ℝ χ z = 0)
    (hA2 : ‖A x‖ ≤ C2 * ((1 + ‖x‖) ^ 2)⁻¹) (hA3 : ‖fderiv ℝ A x‖ ≤ C3 * powWeight 3 x) :
    ‖fderiv ℝ (fun y => χ (c • y) • A y) x - fderiv ℝ A x‖ ≤
      ((K0 + 1) * C3 + C2 * K1 * (1 + Rp)) * powWeight 3 x := by
  rw [cc_powWeight_three x] at hA3
  rw [cc_fderiv_sub_eq hχd hAd c x, cc_powWeight_three x]
  have hχ' : |χ (c • x)| ≤ K0 := by
    have := hχb (c • x)
    rwa [Real.norm_eq_abs] at this
  have h1 : ‖χ (c • x) • fderiv ℝ A x - fderiv ℝ A x‖ ≤ (K0 + 1) * (C3 * ((1 + ‖x‖) ^ 3)⁻¹) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have e1 : |χ (c • x)| * ‖fderiv ℝ A x‖ ≤ K0 * ‖fderiv ℝ A x‖ :=
      mul_le_mul_of_nonneg_right hχ' (norm_nonneg _)
    have e2 : K0 * ‖fderiv ℝ A x‖ ≤ K0 * (C3 * ((1 + ‖x‖) ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_left hA3 hK0
    nlinarith [hA3]
  have hL := cc_key_bound (χ := χ) c x K1 Rp hc0 hc1 hK1 hRp hK1b hz
  have h2 : ‖((fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)).smulRight (A x)‖
      ≤ C2 * (K1 * (1 + Rp) * ((1 + ‖x‖) ^ 3)⁻¹) := by
    refine (cc_norm_smulRight_le (A x)).trans ?_
    calc ‖(fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)‖ * ‖A x‖
        ≤ ‖(fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)‖ *
            (C2 * ((1 + ‖x‖) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hA2 (norm_nonneg _)
      _ = C2 * (‖(fderiv ℝ χ (c • x)).comp (c • ContinuousLinearMap.id ℝ Space)‖ *
            ((1 + ‖x‖) ^ 2)⁻¹) := by ring
      _ ≤ C2 * (K1 * (1 + Rp) * ((1 + ‖x‖) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hL hC2
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq (by ring)))

/-- Dominated convergence in `L^p`, for `0 < p < ∞`, with an `L^p` dominating function. -/
theorem cc_tendsto_eLpNorm {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (hp1 : p ≠ 0)
    (hp2 : p ≠ ⊤) {D : ℕ → Space → E} (hD : ∀ n, AEStronglyMeasurable (D n) volume)
    {B : Space → ℝ} (hB : MemLp B p volume) (hbound : ∀ n x, ‖D n x‖ ≤ ‖B x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖D n x‖) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (D n) p volume) atTop (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp1 hp2
  have heq : ∀ n, eLpNorm (D n) p volume =
      ENNReal.ofReal ((∫ x, ‖D n x‖ ^ p.toReal) ^ p.toReal⁻¹) := by
    intro n
    have hDm : MemLp (D n) p volume := hB.of_le (hD n) (Eventually.of_forall fun x => hbound n x)
    exact hDm.eLpNorm_eq_integral_rpow_norm hp1 hp2
  have hint : Tendsto (fun n => ∫ x, ‖D n x‖ ^ p.toReal) atTop (𝓝 0) := by
    have hBi : Integrable (fun x => ‖B x‖ ^ p.toReal) volume := hB.integrable_norm_rpow hp1 hp2
    have h := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun n x => ‖D n x‖ ^ p.toReal) (f := fun _ => (0 : ℝ))
      (fun x => ‖B x‖ ^ p.toReal)
      (fun n => ((hD n).norm.aemeasurable.pow_const _).aestronglyMeasurable)
      hBi
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbound n x) hq.le)
      (Eventually.of_forall fun x => by
        have h0 : (0 : ℝ) ^ p.toReal = 0 := Real.zero_rpow hq.ne'
        have := ((Real.continuous_rpow_const hq.le).tendsto 0).comp (hlim x)
        simpa [Function.comp_def, h0] using this)
    simpa using h
  have hc : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ p.toReal⁻¹)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.comp
      (Real.continuous_rpow_const (inv_nonneg.2 hq.le))).tendsto 0
    simpa [Function.comp_def, Real.zero_rpow (inv_ne_zero hq.ne')] using this
  simp_rw [heq]
  exact hc.comp hint

theorem cutoffCurlConverge_proof : UnforcedLeray.Short.IIb.CutoffCurlConverge := by
  unfold CutoffCurlConverge
  intro r _ h1 h2 A hA hA2 hA3 χ hχ hχc hχ1
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  have hp1 : r ≠ 0 := (lt_trans zero_lt_one h1).ne'
  obtain ⟨K0', hK0'⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hcs : HasCompactSupport (fderiv ℝ χ) := HasCompactSupport.fderiv ℝ hχc
  have hcf : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  obtain ⟨K1', hK1'⟩ := hcf.bounded_above_of_compact_support hcs
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_closedBall (0 : Space)
  obtain ⟨K0, hK0n, hK0⟩ : ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ y, ‖χ y‖ ≤ K0 :=
    ⟨max K0' 0, le_max_right _ _, fun y => (hK0' y).trans (le_max_left _ _)⟩
  obtain ⟨K1, hK1n, hK1⟩ : ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ z, ‖fderiv ℝ χ z‖ ≤ K1 :=
    ⟨max K1' 0, le_max_right _ _, fun z => (hK1' z).trans (le_max_left _ _)⟩
  obtain ⟨Rp, hRp0, hz⟩ : ∃ Rp : ℝ, 0 ≤ Rp ∧ ∀ z : Space, Rp < ‖z‖ → fderiv ℝ χ z = 0 := by
    refine ⟨max R 0, le_max_right _ _, fun z hzR => ?_⟩
    by_contra hne
    have hsub : Function.support (fderiv ℝ χ) ⊆ tsupport χ := support_fderiv_subset ℝ
    have hmem : z ∈ tsupport χ := hsub hne
    have h3 := hR hmem
    rw [mem_closedBall, dist_zero_right] at h3
    linarith [le_max_left R 0]
  obtain ⟨C2, hC2n, hC2⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖A x‖ ≤ C * ((1 + ‖x‖) ^ 2)⁻¹ := by
    obtain ⟨C, hC⟩ := hA2
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    rw [← cc_rpow_neg_two x]
    exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨C3, hC3n, hC3⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ A x‖ ≤ C * powWeight 3 x := by
    obtain ⟨C, hC⟩ := hA3
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (powWeight_nonneg 3 x))
  obtain ⟨Kt, hKt0, hDiff⟩ : ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ (n : ℕ) (x : Space),
      ‖fderiv ℝ (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x - fderiv ℝ A x‖ ≤ Kt * powWeight 3 x := by
    refine ⟨(K0 + 1) * C3 + C2 * K1 * (1 + Rp), ?_, fun n x => ?_⟩
    · exact add_nonneg (mul_nonneg (by linarith) hC3n)
        (mul_nonneg (mul_nonneg hC2n hK1n) (by linarith))
    · exact cc_fderiv_diff_le hχd hAd ((n : ℝ)⁻¹) x K0 K1 Rp C2 C3
        (inv_nonneg.2 (Nat.cast_nonneg n)) (cc_inv_nat_le_one n) hK0n hK1n hRp0 hC2n hK0 hK1
        hz (hC2 x) (hC3 x)
  have hψc : ∀ n : ℕ, ContDiff ℝ ∞ (fun y : Space => χ ((n : ℝ)⁻¹ • y) • A y) := fun n =>
    (hχ.comp (by fun_prop : ContDiff ℝ ∞ (fun y : Space => ((n : ℝ))⁻¹ • y))).smul hA
  have hcAb : ∀ x, ‖curlC A x‖ ≤ 6 * C3 * powWeight 3 x := fun x => by
    have := cc_curl_le A x
    have := hC3 x
    linarith
  have hDb : ∀ (n : ℕ) (x : Space),
      ‖curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x - curlC A x‖ ≤ 6 * Kt * powWeight 3 x :=
    fun n x => by
      have := cc_curl_sub_le (G := fun y => χ ((n : ℝ)⁻¹ • y) • A y) (H := A) x
      have := hDiff n x
      linarith
  have hcA_mem : MemLp (curlC A) r volume := by
    refine MemLp.of_le ((memLp_powWeight_three h1).const_mul (6 * C3))
      (cc_continuous_curlC hA).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    show ‖curlC A x‖ ≤ ‖(6 * C3) * powWeight 3 x‖
    rw [cc_norm_const_pw (6 * C3) (by linarith) x]
    exact hcAb x
  have hn_mem : ∀ n : ℕ, MemLp (curlC fun x => χ ((n : ℝ)⁻¹ • x) • A x) r volume := by
    intro n
    refine MemLp.of_le ((memLp_powWeight_three h1).const_mul (6 * C3 + 6 * Kt))
      (cc_continuous_curlC (hψc n)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    show ‖curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x‖ ≤ ‖(6 * C3 + 6 * Kt) * powWeight 3 x‖
    rw [cc_norm_const_pw (6 * C3 + 6 * Kt) (by linarith) x]
    have e : curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x =
        curlC A x + (curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x - curlC A x) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := hcAb x
    have := hDb n x
    linarith
  have hbound : ∀ (n : ℕ) (x : Space),
      ‖curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x - curlC A x‖ ≤ ‖(6 * Kt) * powWeight 3 x‖ := by
    intro n x
    rw [cc_norm_const_pw (6 * Kt) (by linarith) x]
    linarith [hDb n x]
  have hpt : ∀ x : Space, Tendsto
      (fun n : ℕ => curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x - curlC A x) atTop (𝓝 0) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
    have hxn : ‖x‖ < (n : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
    have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg _) hxn
    have hev : (fun y : Space => χ ((n : ℝ)⁻¹ • y) • A y) =ᶠ[𝓝 x] A := by
      refine Filter.eventually_of_mem
        (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : Space) (n : ℝ) from
          mem_ball_zero_iff.2 hxn)) fun y hy => ?_
      have hyn : ‖y‖ < (n : ℝ) := mem_ball_zero_iff.1 hy
      have hle : ‖(n : ℝ)⁻¹ • y‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hnpos.le)]
        calc (n : ℝ)⁻¹ * ‖y‖ ≤ (n : ℝ)⁻¹ * n :=
              mul_le_mul_of_nonneg_left hyn.le (inv_nonneg.2 hnpos.le)
          _ = 1 := inv_mul_cancel₀ hnpos.ne'
      show χ ((n : ℝ)⁻¹ • y) • A y = A y
      rw [hχ1 _ hle, one_smul]
    have hfd : fderiv ℝ (fun y : Space => χ ((n : ℝ)⁻¹ • y) • A y) x = fderiv ℝ A x :=
      hev.fderiv_eq
    rw [eq_comm, sub_eq_zero]
    unfold curlC
    rw [hfd]
  have hmain := cc_tendsto_eLpNorm (p := r) hp1 h2
    (D := fun n x => curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y) x - curlC A x)
    (fun n => ((cc_continuous_curlC (hψc n)).sub (cc_continuous_curlC hA)).aestronglyMeasurable)
    (B := fun x => (6 * Kt) * powWeight 3 x)
    ((memLp_powWeight_three h1).const_mul (6 * Kt)) hbound
    (fun x => tendsto_zero_iff_norm_tendsto_zero.1 (hpt x))
  refine ⟨hcA_mem, hn_mem, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n : ℕ => curlC (fun y => χ ((n : ℝ)⁻¹ • y) • A y)) hn_mem (curlC A) hcA_mem).2 hmain

end UnforcedLeray.Short.IIb
