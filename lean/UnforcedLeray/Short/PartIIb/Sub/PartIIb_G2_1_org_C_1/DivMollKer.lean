import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollExists
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollWeakD2
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivSmooth.WeakClassical

/-!
# Commutator Kernel and Mean-Zero Approximate Identity for `PartII-b:G2/1/org/C/1`

Builds the Cartesian Friedrichs commutator kernel
`psi0(w) = 2 w_s ∂_s ρ(w) + w_η ∂_η ρ(w) + 3 ρ(w) = ∂_s(2 w_s ρ(w)) + ∂_η(w_η ρ(w))`
associated with `ρ = mollExistsRho` (`ContDiffBump` of outer radius `2` on `Coord`), proves its
scaling identity `molN psi0 n` under `κ_n = molN ρ n`, its vanishing outside `closedBall 0 2`,
its zero integral, and `cylNorm c r (convK (molN psi0 n) f) → 0` by decomposing `psi0` as a scaled
difference `M • (rhoPlus - rhoBig)` of two positive mollifiers and invoking `mollApprox_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.PhysKOutCandMoll

open UnforcedLeray.Short.IIb

/-- Base Friedrichs commutator kernel for `Q_ε` under Cartesian convolution with `mollExistsRho`:
`psi0(w) = 2 w_s ∂_s ρ(w) + w_η ∂_η ρ(w) + 3 ρ(w)`. -/
def psi0 : Coord → ℝ :=
  fun w => 2 * w.1 * cpd 0 mollExistsRho w + w.2.2 * cpd 2 mollExistsRho w + 3 * mollExistsRho w

theorem mollExistsRho_zero_of_two_le {w : Coord} (hw : 2 ≤ ‖w‖) : mollExistsRho w = 0 := by
  by_contra hne
  have hmem : w ∈ Function.support mollExistsRho := hne
  rw [mollExistsRho, mollExistsBump.support_normed_eq] at hmem
  have hlt : ‖w‖ < 2 := by simpa [mollExistsBump] using hmem
  linarith

theorem tsupport_mollExistsRho_eq : tsupport mollExistsRho = Metric.closedBall (0 : Coord) 2 := by
  simpa [mollExistsRho, mollExistsBump] using
    (mollExistsBump.tsupport_normed_eq (μ := (volume : Measure Coord)))

private theorem psi0_zero_of_two_lt {z : Coord} (hz : 2 < ‖z‖) : psi0 z = 0 := by
  have hnot : z ∉ tsupport mollExistsRho := by
    rw [tsupport_mollExistsRho_eq, Metric.mem_closedBall, dist_zero_right]
    linarith
  have hc0 : cpd 0 mollExistsRho z = 0 := by
    unfold cpd; rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]; simp
  have hc2 : cpd 2 mollExistsRho z = 0 := by
    unfold cpd; rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]; simp
  simp [psi0, hc0, hc2, mollExistsRho_zero_of_two_le hz.le]

theorem psi0_zero_of_two_le {w : Coord} (hw : 2 ≤ ‖w‖) : psi0 w = 0 := by
  by_cases hgt : 2 < ‖w‖
  · exact psi0_zero_of_two_lt hgt
  · have hcl : Continuous psi0 := by
      unfold psi0
      have hρ := mollExists_base_isMollifier.1.1
      have hc0 := (mwd2_cpd_contDiff 0 mollExistsRho hρ).continuous
      have hc2 := (mwd2_cpd_contDiff 2 mollExistsRho hρ).continuous
      exact (((continuous_const.mul continuous_fst).mul hc0).add
        ((continuous_snd.comp continuous_snd).mul hc2)).add (continuous_const.mul hρ.continuous)
    have hseq : ∀ k : ℕ, psi0 ((1 + (((k + 1 : ℕ) : ℝ))⁻¹) • w) = 0 := by
      intro k
      apply psi0_zero_of_two_lt
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have hw2 : ‖w‖ = 2 := le_antisymm (not_lt.mp hgt) hw
      have hkpos : (0 : ℝ) < (((k + 1 : ℕ) : ℝ))⁻¹ := by positivity
      rw [hw2]
      linarith
    have htend : Tendsto (fun k : ℕ => (1 + (((k + 1 : ℕ) : ℝ))⁻¹) • w) atTop (𝓝 w) := by
      have hinv : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
      have h1 : Tendsto (fun k : ℕ => (1 : ℝ) + (((k + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add hinv
      simpa [one_smul] using h1.smul (tendsto_const_nhds (x := w))
    have hcomp := hcl.continuousAt.tendsto.comp htend
    have hzero_seq : (psi0 ∘ fun k : ℕ => (1 + (((k + 1 : ℕ) : ℝ))⁻¹) • w) = fun _ => 0 :=
      funext hseq
    rw [hzero_seq] at hcomp
    exact tendsto_nhds_unique hcomp tendsto_const_nhds

theorem tsupport_psi0_subset : tsupport psi0 ⊆ Metric.closedBall (0 : Coord) 2 := by
  refine closure_minimal (fun w hw => ?_) Metric.isClosed_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  exact hw (psi0_zero_of_two_le (le_of_lt (not_le.mp hlt)))

theorem isKer_psi0 : IsKer psi0 := by
  have hρ := mollExists_base_isMollifier.1.1
  refine ⟨?_, ?_⟩
  · unfold psi0
    have hc0 := mwd2_cpd_contDiff 0 mollExistsRho hρ
    have hc2 := mwd2_cpd_contDiff 2 mollExistsRho hρ
    exact (((contDiff_const.mul contDiff_fst).mul hc0).add
      ((contDiff_snd.comp contDiff_snd).mul hc2)).add (contDiff_const.mul hρ)
  · exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Coord) 2)
      fun w hw => tsupport_psi0_subset (subset_tsupport _ hw)

theorem psi0_eq_div (w : Coord) :
    psi0 w = cpd 0 (fun z : Coord => (2 * z.1) * mollExistsRho z) w +
      cpd 2 (fun z : Coord => z.2.2 * mollExistsRho z) w := by
  have hρd : DifferentiableAt ℝ mollExistsRho w :=
    mollExists_base_isMollifier.1.1.differentiable (by simp) w
  have h1 : HasFDerivAt (fun z : Coord => 2 * z.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) w :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.const_smul (2 : ℝ)
  have h2 : HasFDerivAt (fun z : Coord => z.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) w :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hp1 := h1.mul hρd.hasFDerivAt
  have hp2 := h2.mul hρd.hasFDerivAt
  have hc0 : cpd 0 (fun z : Coord => (2 * z.1) * mollExistsRho z) w =
      2 * w.1 * cpd 0 mollExistsRho w + 2 * mollExistsRho w := by
    unfold cpd
    change fderiv ℝ ((fun z : Coord => 2 * z.1) * mollExistsRho) w (cdir 0) = _
    rw [hp1.fderiv]
    simp [cdir]
    ring
  have hc2 : cpd 2 (fun z : Coord => z.2.2 * mollExistsRho z) w =
      w.2.2 * cpd 2 mollExistsRho w + mollExistsRho w := by
    unfold cpd
    change fderiv ℝ ((fun z : Coord => z.2.2) * mollExistsRho) w (cdir 2) = _
    rw [hp2.fderiv]
    simp [cdir]
  rw [hc0, hc2]
  unfold psi0
  ring

private theorem integral_cpd_eq_zero (j : Fin 3) {g : Coord → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ w : Coord, cpd j g w = 0 := by
  have hC := DivWeakClassicalHelp.ibp_dir g hg hgc (fun _ : Coord => (1 : ℂ))
    contDiff_const (cdir j)
  have hR : -∫ x : Coord, g x • fderiv ℝ (fun _ : Coord => (1 : ℂ)) x (cdir j) = 0 := by simp
  rw [hR] at hC
  have hL : (∫ x : Coord, (cpd j g x : ℂ)) = 0 := by
    simpa [cpd, Complex.real_smul, mul_one] using hC
  have hi : Integrable (cpd j g) volume :=
    (mwd2_cpd_contDiff j g hg).continuous.integrable_of_hasCompactSupport
      (mwd2_cpd_hasCompact j g hgc)
  have hcomm : (∫ x : Coord, (cpd j g x : ℂ)) = Complex.ofReal (∫ x : Coord, cpd j g x) := by
    simpa using Complex.ofRealCLM.integral_comp_comm hi
  rw [hcomm] at hL
  exact Complex.ofReal_eq_zero.mp hL

theorem integral_psi0 : ∫ w : Coord, psi0 w = 0 := by
  have hρ := mollExists_base_isMollifier.1
  set g0 : Coord → ℝ := fun z => (2 * z.1) * mollExistsRho z
  set g2 : Coord → ℝ := fun z => z.2.2 * mollExistsRho z
  have hg0_sm : ContDiff ℝ ∞ g0 := (contDiff_const.mul contDiff_fst).mul hρ.1
  have hg0_cs : HasCompactSupport g0 := hρ.2.mul_left
  have hg2_sm : ContDiff ℝ ∞ g2 := (contDiff_snd.comp contDiff_snd).mul hρ.1
  have hg2_cs : HasCompactSupport g2 := hρ.2.mul_left
  have hi0 : Integrable (cpd 0 g0) volume :=
    (mwd2_cpd_contDiff 0 g0 hg0_sm).continuous.integrable_of_hasCompactSupport
      (mwd2_cpd_hasCompact 0 g0 hg0_cs)
  have hi2 : Integrable (cpd 2 g2) volume :=
    (mwd2_cpd_contDiff 2 g2 hg2_sm).continuous.integrable_of_hasCompactSupport
      (mwd2_cpd_hasCompact 2 g2 hg2_cs)
  have heq : psi0 = fun w => cpd 0 g0 w + cpd 2 g2 w := funext psi0_eq_div
  rw [heq, integral_add hi0 hi2,
    integral_cpd_eq_zero 0 hg0_sm hg0_cs, integral_cpd_eq_zero 2 hg2_sm hg2_cs, add_zero]

/-- Scaling of `cpd j (molN ρ n)` and identity with `molN psi0 n`. -/
theorem cpd_molN_eq (j : Fin 3) {κ : Coord → ℝ} (hκ : ContDiff ℝ ∞ κ) (n : ℕ) (w : Coord) :
    cpd j (molN κ n) w = ((n : ℝ) + 1) ^ 4 * cpd j κ (((n : ℝ) + 1) • w) := by
  set a : ℝ := (n : ℝ) + 1
  have h1 : HasFDerivAt (fun z : Coord => a • z) (a • ContinuousLinearMap.id ℝ Coord) w :=
    (hasFDerivAt_id w).const_smul a
  have h2 : HasFDerivAt (fun z : Coord => κ (a • z))
      ((fderiv ℝ κ (a • w)).comp (a • ContinuousLinearMap.id ℝ Coord)) w :=
    (hκ.differentiable (by simp) (a • w)).hasFDerivAt.comp w h1
  unfold cpd molN
  change fderiv ℝ (fun z : Coord => a ^ 3 * κ (a • z)) w (cdir j) =
    a ^ 4 * fderiv ℝ κ (a • w) (cdir j)
  rw [fderiv_const_mul h2.differentiableAt, h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

theorem molN_psi0_eq (n : ℕ) (w : Coord) :
    2 * w.1 * cpd 0 (molN mollExistsRho n) w +
      w.2.2 * cpd 2 (molN mollExistsRho n) w +
      3 * molN mollExistsRho n w = molN psi0 n w := by
  have hρ := mollExists_base_isMollifier.1.1
  rw [cpd_molN_eq 0 hρ n w, cpd_molN_eq 2 hρ n w]
  unfold molN psi0
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ## Decomposition of `psi0` into two positive mollifiers and mean-zero approximate identity -/

private def bigBump : ContDiffBump (0 : Coord) where
  rIn := 3
  rOut := 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def rhoBig : Coord → ℝ := bigBump.normed volume

private theorem isMollifier_rhoBig : IsMollifier rhoBig :=
  ⟨⟨bigBump.contDiff_normed, bigBump.hasCompactSupport_normed⟩,
    bigBump.nonneg_normed, bigBump.integral_normed⟩

private theorem rhoBig_pos_at_zero : 0 < rhoBig 0 := by
  have hmem : (0 : Coord) ∈ Function.support rhoBig := by
    rw [rhoBig, bigBump.support_normed_eq]
    exact Metric.mem_ball_self (by norm_num [bigBump])
  exact lt_of_le_of_ne (bigBump.nonneg_normed 0) (Ne.symm (Function.mem_support.mp hmem))

private theorem rhoBig_eq_on_ball2 {w : Coord} (hw : w ∈ Metric.closedBall (0 : Coord) 2) :
    rhoBig w = rhoBig 0 := by
  have hw3 : w ∈ Metric.closedBall (0 : Coord) bigBump.rIn :=
    Metric.closedBall_subset_closedBall (by norm_num [bigBump]) hw
  have h03 : (0 : Coord) ∈ Metric.closedBall (0 : Coord) bigBump.rIn :=
    Metric.mem_closedBall_self (by norm_num [bigBump])
  simp only [rhoBig, ContDiffBump.normed_def, bigBump.one_of_mem_closedBall hw3,
    bigBump.one_of_mem_closedBall h03]

private theorem exists_mollifier_pair_for_psi0 :
    ∃ (M : ℝ) (ρ₁ ρ₂ : Coord → ℝ), 0 < M ∧
      IsMollifier ρ₁ ∧ (∀ n : ℕ, IsMollifier (molN ρ₁ n)) ∧
      IsMollifier ρ₂ ∧ (∀ n : ℕ, IsMollifier (molN ρ₂ n)) ∧
      ∀ z : Coord, psi0 z = M * (ρ₁ z - ρ₂ z) := by
  obtain ⟨B0, hB0⟩ :=
    (isCompact_closedBall (0 : Coord) 2).exists_bound_of_continuousOn
      isKer_psi0.1.continuous.continuousOn
  set B : ℝ := max B0 1 + 1
  have hB_pos : 0 < B := by positivity
  have hpsi_bd : ∀ w : Coord, |psi0 w| ≤ B := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : Coord) 2
    · have h1 : |psi0 w| ≤ B0 := by simpa [Real.norm_eq_abs] using hB0 w hw
      have h2 : B0 ≤ max B0 1 := le_max_left _ _
      linarith
    · have hw2 : 2 ≤ ‖w‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        linarith
      rw [psi0_zero_of_two_le hw2, abs_zero]
      exact hB_pos.le
  set c0 : ℝ := rhoBig 0
  have hc0_pos : 0 < c0 := rhoBig_pos_at_zero
  set M : ℝ := B / c0
  have hM_pos : 0 < M := div_pos hB_pos hc0_pos
  set ρ₁ : Coord → ℝ := fun z => rhoBig z + M⁻¹ * psi0 z
  have hρ₁_ker : IsKer ρ₁ := by
    refine ⟨isMollifier_rhoBig.1.1.add (contDiff_const.mul isKer_psi0.1), ?_⟩
    exact isMollifier_rhoBig.1.2.add (isKer_psi0.2.mul_left)
  have hρ₁_nn : ∀ z : Coord, 0 ≤ ρ₁ z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : Coord) 2
    · have hrb : rhoBig z = c0 := rhoBig_eq_on_ball2 hz
      have habs : -B ≤ psi0 z := (abs_le.mp (hpsi_bd z)).1
      have hMinv : M⁻¹ = c0 / B := by simp [M, inv_div]
      show 0 ≤ rhoBig z + M⁻¹ * psi0 z
      rw [hrb, hMinv]
      have hmul : -(c0 / B * B) ≤ c0 / B * psi0 z := by
        have hnn : 0 ≤ c0 / B := div_nonneg hc0_pos.le hB_pos.le
        nlinarith
      have hcancel : c0 / B * B = c0 := div_mul_cancel₀ c0 hB_pos.ne'
      linarith
    · have hz2 : 2 ≤ ‖z‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        linarith
      show 0 ≤ rhoBig z + M⁻¹ * psi0 z
      rw [psi0_zero_of_two_le hz2, mul_zero, add_zero]
      exact isMollifier_rhoBig.2.1 z
  have hρ₁_int : ∫ z : Coord, ρ₁ z = 1 := by
    have hi_big : Integrable rhoBig volume := bigBump.integrable_normed
    have hi_psi : Integrable psi0 volume :=
      isKer_psi0.1.continuous.integrable_of_hasCompactSupport isKer_psi0.2
    show ∫ z : Coord, (rhoBig z + M⁻¹ * psi0 z) = 1
    rw [integral_add hi_big (hi_psi.const_mul M⁻¹), isMollifier_rhoBig.2.2,
      integral_const_mul, integral_psi0, mul_zero, add_zero]
  have hρ₁_moll : IsMollifier ρ₁ := ⟨hρ₁_ker, hρ₁_nn, hρ₁_int⟩
  refine ⟨M, ρ₁, rhoBig, hM_pos,
    hρ₁_moll, fun n => mollExists_molN_isMollifier ρ₁ hρ₁_moll n,
    isMollifier_rhoBig, fun n => mollExists_molN_isMollifier rhoBig isMollifier_rhoBig n,
    fun z => ?_⟩
  show psi0 z = M * ((rhoBig z + M⁻¹ * psi0 z) - rhoBig z)
  have hMne : M ≠ 0 := hM_pos.ne'
  field_simp [hMne]
  ring

private theorem convK_ker_linear {M : ℝ} {κ₁ κ₂ : Coord → ℝ} (hκ₁ : IsKer κ₁) (hκ₂ : IsKer κ₂)
    {f : Coord → ℂ} (hf : LocallyIntegrable f volume) (x : Coord) :
    convK (fun z => M * (κ₁ z - κ₂ z)) f x =
      (M : ℂ) * (convK κ₁ f x - convK κ₂ f x) := by
  have int_of_ker : ∀ {κ : Coord → ℝ}, IsKer κ →
      Integrable (fun y : Coord => f y * (κ (x - y) : ℂ)) volume := by
    intro κ hκ
    have hc : Continuous (fun y : Coord => (κ (x - y) : ℂ)) :=
      Complex.continuous_ofReal.comp (hκ.1.continuous.comp (continuous_const.sub continuous_id))
    have hs : HasCompactSupport (fun y : Coord => (κ (x - y) : ℂ)) := by
      have : HasCompactSupport (fun y : Coord => κ (x - y)) :=
        hκ.2.comp_homeomorph (Homeomorph.subLeft x)
      exact this.comp_left Complex.ofReal_zero
    simpa [mul_comm] using hf.integrable_smul_left_of_hasCompactSupport hc hs
  have h1 := int_of_ker hκ₁
  have h2 := int_of_ker hκ₂
  unfold convK
  have heq : (fun y : Coord => f y * ((M * (κ₁ (x - y) - κ₂ (x - y)) : ℝ) : ℂ)) =
      fun y : Coord => (M : ℂ) * (f y * (κ₁ (x - y) : ℂ) - f y * (κ₂ (x - y) : ℂ)) := by
    funext y; push_cast; ring
  rw [heq, integral_const_mul, integral_sub h1 h2]

/-- **Mean-zero approximate identity**: `convK (molN psi0 n) f → 0` in `L^r(cylMeas c)`. -/
theorem tendsto_convK_molN_psi0_zero {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    {f : Coord → ℂ} (hper : QPeriodicS c f) (hfm : AEStronglyMeasurable f volume)
    (hfin : cylNorm c r f < ⊤) :
    Tendsto (fun n : ℕ => cylNorm c r (convK (molN psi0 n) f)) atTop (𝓝 0) := by
  obtain ⟨M, ρ₁, ρ₂, hM_pos, hρ₁, hρ₁n, hρ₂, hρ₂n, hdecomp⟩ := exists_mollifier_pair_for_psi0
  have hfloc : LocallyIntegrable f volume := mollLoc_proof c r hc hr f hper hfm hfin
  have ht1 := mollApprox_proof c r hc hr ρ₁ hρ₁ hρ₁n f hper hfm hfin
  have ht2 := mollApprox_proof c r hc hr ρ₂ hρ₂ hρ₂n f hper hfm hfin
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have hac := mollApprox_cylMeas_ac c
  have hfm_cyl : AEStronglyMeasurable f (cylMeas c) := hfm.mono_ac hac
  have hbound : ∀ n : ℕ, cylNorm c r (convK (molN psi0 n) f) ≤
      ENNReal.ofReal M * (cylNorm c r (fun x => convK (molN ρ₁ n) f x - f x) +
        cylNorm c r (fun x => convK (molN ρ₂ n) f x - f x)) := by
    intro n
    have hmol_eq : molN psi0 n = fun z => M * (molN ρ₁ n z - molN ρ₂ n z) := by
      funext z; unfold molN; rw [hdecomp (((n : ℝ) + 1) • z)]; ring
    have hpt : convK (molN psi0 n) f =
        (M : ℂ) • ((fun x => convK (molN ρ₁ n) f x - f x) -
          (fun x => convK (molN ρ₂ n) f x - f x)) := by
      funext x
      rw [hmol_eq, convK_ker_linear (hρ₁n n).1 (hρ₂n n).1 hfloc x]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have hm1 : AEStronglyMeasurable (fun x => convK (molN ρ₁ n) f x - f x) (cylMeas c) :=
      ((mollConvNice_proof c (molN ρ₁ n) f (hρ₁n n).1 hper hfloc).1.continuous.aestronglyMeasurable
        ).sub hfm_cyl
    have hm2 : AEStronglyMeasurable (fun x => convK (molN ρ₂ n) f x - f x) (cylMeas c) :=
      ((mollConvNice_proof c (molN ρ₂ n) f (hρ₂n n).1 hper hfloc).1.continuous.aestronglyMeasurable
        ).sub hfm_cyl
    unfold cylNorm
    rw [hpt, eLpNorm_const_smul]
    have hMnorm : ‖(M : ℂ)‖ₑ = ENNReal.ofReal M := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    rw [hMnorm]
    have hsub_le : eLpNorm (((fun x => convK (molN ρ₁ n) f x - f x) -
        (fun x => convK (molN ρ₂ n) f x - f x))) (ENNReal.ofReal r) (cylMeas c) ≤
        cylNorm c r (fun x => convK (molN ρ₁ n) f x - f x) +
          cylNorm c r (fun x => convK (molN ρ₂ n) f x - f x) := by
      have hsub_eq : ((fun x => convK (molN ρ₁ n) f x - f x) -
          (fun x => convK (molN ρ₂ n) f x - f x)) =
          (fun x => convK (molN ρ₁ n) f x - f x) +
            fun x => -(convK (molN ρ₂ n) f x - f x) := by
        funext x; simp [sub_eq_add_neg]
      rw [hsub_eq]
      refine (eLpNorm_add_le hm1 hm2.neg hp1).trans ?_
      rw [eLpNorm_neg]
    exact mul_le_mul_of_nonneg_left hsub_le bot_le
  have hsum0 : Tendsto (fun n : ℕ =>
      ENNReal.ofReal M * (cylNorm c r (fun x => convK (molN ρ₁ n) f x - f x) +
        cylNorm c r (fun x => convK (molN ρ₂ n) f x - f x))) atTop (𝓝 0) := by
    have hadd : Tendsto (fun n : ℕ =>
        cylNorm c r (fun x => convK (molN ρ₁ n) f x - f x) +
          cylNorm c r (fun x => convK (molN ρ₂ n) f x - f x)) atTop (𝓝 (0 + 0)) :=
      ht1.add ht2
    rw [add_zero] at hadd
    simpa using ENNReal.Tendsto.const_mul hadd (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
    (fun _ => bot_le) hbound

/-- Support containment for `convK (molN κ n) f` when `κ` vanishes for `2 ≤ ‖w‖`. -/
theorem convK_molN_zero_off_window {κ : Coord → ℝ} (hκ2 : ∀ w : Coord, 2 ≤ ‖w‖ → κ w = 0)
    {s₀ s₁ L δ_r : ℝ} (hδ : 0 < δ_r) {n : ℕ} (hn : 2 / ((n : ℝ) + 1) ≤ δ_r)
    {f : Coord → ℂ} (hf : ∀ y : Coord, (y.1 < s₀ ∨ s₁ < y.1 ∨ L < |y.2.2|) → f y = 0)
    {x : Coord} (hx : x.1 < s₀ - δ_r ∨ s₁ + δ_r < x.1 ∨ L + δ_r < |x.2.2|) :
    convK (molN κ n) f x = 0 := by
  unfold convK
  have hzero : (fun y : Coord => f y * (molN κ n (x - y) : ℂ)) = fun _ => 0 := by
    funext y
    by_cases hy : y.1 < s₀ ∨ s₁ < y.1 ∨ L < |y.2.2|
    · simp [hf y hy]
    · push Not at hy
      obtain ⟨hys0, hys1, hyL⟩ := hy
      have hdist : δ_r < ‖x - y‖ := by
        rcases hx with hx1 | hx2 | hx3
        · have h1 : δ_r < |x.1 - y.1| := by
            rw [abs_of_neg (by linarith)]; linarith
          exact h1.trans_le (by simpa [Real.norm_eq_abs] using norm_fst_le (x - y))
        · have h1 : δ_r < |x.1 - y.1| := by
            rw [abs_of_pos (by linarith)]; linarith
          exact h1.trans_le (by simpa [Real.norm_eq_abs] using norm_fst_le (x - y))
        · have h1 : δ_r < |x.2.2 - y.2.2| := by
            have := abs_sub_abs_le_abs_sub x.2.2 y.2.2
            linarith
          have hle2 : |x.2.2 - y.2.2| ≤ ‖(x - y).2‖ := by
            simpa [Real.norm_eq_abs] using norm_snd_le (x - y).2
          exact h1.trans_le (hle2.trans (norm_snd_le (x - y)))
      have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2le : 2 ≤ ‖((n : ℝ) + 1) • (x - y)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hn1_pos.le]
        have hmul : ((n : ℝ) + 1) * (2 / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left (hn.trans hdist.le) hn1_pos.le
        have hcancel : ((n : ℝ) + 1) * (2 / ((n : ℝ) + 1)) = 2 :=
          mul_div_cancel₀ 2 hn1_pos.ne'
        linarith
      simp [molN, hκ2 _ h2le]
  rw [hzero, integral_zero]

end UnforcedLeray.Short.IIb.PhysKOutCandMoll

end
