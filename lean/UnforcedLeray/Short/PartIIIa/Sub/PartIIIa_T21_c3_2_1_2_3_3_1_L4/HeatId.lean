import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.HeatDecomp
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit

/-!
# Helper 1 for `PartIII-a:T21/c3/2/1/2/3/3/1/4`: Heat/Oscillator Pairing Identity

Source of record: `the November 2 reference manuscript` (SP), lines 2905-2918.

Proves that for sufficiently large moving cell length `d = cellLen (ν ^ (-2 : ℝ)) (clockA ν r)`,
the moving heat-dual pairing against the periodized growing mode `perE κ d k` equals the
normalised dual pairing against the oscillator/cell-drift residual `movOscRes κ ν r k`:
`∫ y in B0579.cell d, movLamDualHeat κ ν r i y * perE κ d k y =`
`  ∫ y in B0579.cell d, perLam κ d i y * movOscRes κ ν r k y`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.MovFrameLeavesAux

private lemma partialQ_sub_const {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (c z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ (fun w => g (w - c)) z = UnforcedLeray.Cyl.partialQ g (z - c) := by
  have hdg : Differentiable ℝ (fun w => g (w - c)) :=
    hg.comp (differentiable_id.sub (differentiable_const c))
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hdg z, UnforcedLeray.Cyl.partialQ_eq_fderiv hg (z - c)]
  have hf : fderiv ℝ (fun w => g (w - c)) z = fderiv ℝ g (z - c) :=
    ((hg (z - c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)).fderiv
  rw [hf]

private lemma partialEta_sub_const {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (c z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta (fun w => g (w - c)) z =
      UnforcedLeray.Cyl.partialEta g (z - c) := by
  have hdg : Differentiable ℝ (fun w => g (w - c)) :=
    hg.comp (differentiable_id.sub (differentiable_const c))
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hdg z,
    UnforcedLeray.Cyl.partialEta_eq_fderiv hg (z - c)]
  have hf : fderiv ℝ (fun w => g (w - c)) z = fderiv ℝ g (z - c) :=
    ((hg (z - c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)).fderiv
  rw [hf]

private lemma cyl_laplacian_sub_const {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) (c z : ℝ × ℝ) :
    UnforcedLeray.Cyl.laplacian (fun w => L (w - c)) z =
      UnforcedLeray.Cyl.laplacian L (z - c) := by
  have hC2 := UnforcedLeray.Cyl.C2.of_contDiff hL
  have hQ : UnforcedLeray.Cyl.partialQ (fun w => L (w - c)) =
      fun w => UnforcedLeray.Cyl.partialQ L (w - c) :=
    funext (partialQ_sub_const hC2.diff c)
  have hE : UnforcedLeray.Cyl.partialEta (fun w => L (w - c)) =
      fun w => UnforcedLeray.Cyl.partialEta L (w - c) :=
    funext (partialEta_sub_const hC2.diff c)
  unfold UnforcedLeray.Cyl.laplacian
  rw [hQ, hE, partialQ_sub_const hC2.diffQ c z, partialEta_sub_const hC2.diffEta c z]

private lemma dualGen_sub_fst {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) (a : ℝ) (z : ℝ × ℝ) :
    let c : ℝ × ℝ := (a, 0)
    UnforcedLeray.Gaussian.dualGen L (z - c) =
      UnforcedLeray.Gaussian.dualGen (fun w => L (w - c)) z +
        (a / 2 : ℝ) • pdCx 0 L (z - c) := by
  intro c
  have hdL : Differentiable ℝ L := hL.differentiable (by norm_num)
  have hf : fderiv ℝ (fun w => L (w - c)) z = fderiv ℝ L (z - c) :=
    ((hdL (z - c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)).fderiv
  have hz_eq : z = (z - c) + a • B0579.dir 0 := by
    ext <;> simp [c, B0579.dir]
  have hlin : fderiv ℝ (fun w => L (w - c)) z z =
      fderiv ℝ L (z - c) (z - c) + a • pdCx 0 L (z - c) := by
    rw [hf]
    have h := (fderiv ℝ L (z - c)).map_add (z - c) (a • B0579.dir 0)
    rw [← hz_eq, map_smul] at h
    exact h
  unfold UnforcedLeray.Gaussian.dualGen
  rw [cyl_laplacian_sub_const hL c z, hlin]
  module

private lemma det_ne_zero_of_near_id {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hnear : ∀ i j : Fin 2, ‖M i j - (if i = j then 1 else 0)‖ ≤ 1 / 4) :
    IsUnit M.det := by
  have h00 := hnear 0 0
  have h11 := hnear 1 1
  have h01 := hnear 0 1
  have h10 := hnear 1 0
  simp only [ite_true, ite_false, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, sub_zero,
    one_ne_zero] at h00 h11 h01 h10
  have ha : 3 / 4 ≤ ‖M 0 0‖ := by
    have := norm_sub_norm_le (1 : ℂ) (M 0 0)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hd : 3 / 4 ≤ ‖M 1 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (M 1 1)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have had : 9 / 16 ≤ ‖M 0 0 * M 1 1‖ := by
    rw [norm_mul]
    nlinarith
  have hbc : ‖M 0 1 * M 1 0‖ ≤ 1 / 16 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (M 0 1), norm_nonneg (M 1 0)]
  have hdet_pos : 0 < ‖M.det‖ := by
    rw [Matrix.det_fin_two]
    have := norm_sub_norm_le (M 0 0 * M 1 1) (M 0 1 * M 1 0)
    linarith
  exact isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hdet_pos)

/-- Termwise planar identity for the `n`-th lattice shift of `D^# (κ.lamP m)` against `κ.e k`:
`∫ y, D^#(κ.lamP m)(y) * κ.e k (y.1 + n d, y.2) = oscGramTerm κ d m k n - (d / 2) * gramTermDeriv κ d m k n`. -/
private lemma dualGen_cross_term_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    (d : ℝ) (m k : Fin 2) (n : ℤ) :
    ∫ y : ℝ × ℝ, UnforcedLeray.Gaussian.dualGen (κ.lamP m) y *
        κ.e k (y.1 + (n : ℝ) * d, y.2) =
      oscGramTerm κ d m k n + (-(d / 2 : ℂ)) * ComplCouplingHeat.gramTermDeriv κ d m k n := by
  obtain ⟨hCD, C, hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨hsm_e, hdec_e⟩ := OscillatorForceSub.seed_e_smooth_decay hκ
  obtain ⟨B0, hB0, hb0⟩ := hdec_e k 0
  obtain ⟨B1, hB1, hb1⟩ := hdec_e k 1
  obtain ⟨B2, hB2, hb2⟩ := hdec_e k 2
  set a : ℝ := (n : ℝ) * d
  set c : ℝ × ℝ := (a, 0)
  set La : ℝ × ℝ → ℂ := fun z => κ.lamP m (z - c)
  have hw1 : ∀ z : ℝ × ℝ, ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ 1 := fun z => by
    have h1z : 1 ≤ 1 + |z.1| + |z.2| := by linarith [abs_nonneg z.1, abs_nonneg z.2]
    have hi : (1 + |z.1| + |z.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1z
    have hi0 : 0 ≤ (1 + |z.1| + |z.2|)⁻¹ := by positivity
    nlinarith
  have hw3 : ∀ z : ℝ × ℝ, ((1 + |z.1| + |z.2|)⁻¹) ^ 3 ≤ 1 := fun z => by
    have h1z : 1 ≤ 1 + |z.1| + |z.2| := by linarith [abs_nonneg z.1, abs_nonneg z.2]
    have hi : (1 + |z.1| + |z.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1z
    exact pow_le_one₀ (by positivity) hi
  have he_gw : ∀ y : ℝ × ℝ, ‖κ.e k y‖ ≤ B0 * OscGramIBP.gw y := fun y => by
    have := hb0 y
    rw [norm_iteratedFDeriv_zero] at this
    have hgw : OscGramIBP.gw y = Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := rfl
    rw [hgw]
    nlinarith [norm_nonneg y, norm_nonneg (κ.e k y)]
  -- Shift `y = z - c` on the LHS
  have hshift_lhs :
      (∫ y : ℝ × ℝ, UnforcedLeray.Gaussian.dualGen (κ.lamP m) y *
          κ.e k (y.1 + a, y.2)) =
        ∫ z : ℝ × ℝ, UnforcedLeray.Gaussian.dualGen (κ.lamP m) (z - c) * κ.e k z := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun y : ℝ × ℝ => UnforcedLeray.Gaussian.dualGen (κ.lamP m) y * κ.e k (y.1 + a, y.2)) c
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    have h2 : ((z - c).1 + a, (z - c).2) = z := by
      ext <;> simp [c, sub_add_cancel]
    rw [h2]
  -- Integrability of `z ↦ dualGen (κ.lamP m) (z - c) * κ.e k z` and `z ↦ ((a/2) • pdCx 0 ...) * κ.e k z`
  have hΨ_cont : Continuous (UnforcedLeray.Gaussian.dualGen (κ.lamP m)) :=
    ComplCouplingHeat.continuous_dualGen (hCD m)
  have hInt_sum : Integrable
      (fun z : ℝ × ℝ => UnforcedLeray.Gaussian.dualGen (κ.lamP m) (z - c) * κ.e k z) := by
    refine OscGramIBP.integrable_of_le_gw
      ((hΨ_cont.comp (continuous_id.sub continuous_const)).mul (κ.e_cont k))
      (M := (7 / 2 * C) * B0) (fun z => ?_)
    have hΨb : ‖UnforcedLeray.Gaussian.dualGen (κ.lamP m) (z - c)‖ ≤ 7 / 2 * C := by
      have hb := ComplCouplingHeat.norm_dualGen_le_inv_sq (hCD m) (h0 m) (h1 m) (h2 m) (z - c)
      exact hb.trans (mul_le_of_le_one_right (by positivity) (hw1 (z - c)))
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hΨb (he_gw z) (norm_nonneg _) (by positivity)
  have hpd_cont : Continuous (pdCx 0 (κ.lamP m)) := by
    unfold pdCx
    exact (((hCD m).fderiv_right (m := 1) (by norm_num)).continuous).clm_apply continuous_const
  have hInt_drift : Integrable
      (fun z : ℝ × ℝ => ((a / 2 : ℝ) • pdCx 0 (κ.lamP m) (z - c)) * κ.e k z) := by
    refine OscGramIBP.integrable_of_le_gw
      (((hpd_cont.comp (continuous_id.sub continuous_const)).const_smul (a / 2 : ℝ)).mul
        (κ.e_cont k))
      (M := (|a / 2| * (2 * |C|)) * B0) (fun z => ?_)
    have hpdb : ‖(a / 2 : ℝ) • pdCx 0 (κ.lamP m) (z - c)‖ ≤ |a / 2| * (2 * |C|) := by
      rw [norm_smul, Real.norm_eq_abs]
      have hb := (ComplCouplingHeat.norm_pdCx_zero_le_inv_cube (h1 m) (z - c)).trans
        (mul_le_of_le_one_right (by positivity) (hw3 (z - c)))
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hpdb (he_gw z) (norm_nonneg _) (by positivity)
  have hpt_split : ∀ z : ℝ × ℝ,
      UnforcedLeray.Gaussian.dualGen (κ.lamP m) (z - c) * κ.e k z =
        UnforcedLeray.Gaussian.dualGen La z * κ.e k z +
          ((a / 2 : ℝ) • pdCx 0 (κ.lamP m) (z - c)) * κ.e k z := by
    intro z
    rw [dualGen_sub_fst (hCD m) a z, add_mul]
  have hInt_La : Integrable (fun z : ℝ × ℝ => UnforcedLeray.Gaussian.dualGen La z * κ.e k z) := by
    have heq : (fun z : ℝ × ℝ => UnforcedLeray.Gaussian.dualGen La z * κ.e k z) =
        fun z => UnforcedLeray.Gaussian.dualGen (κ.lamP m) (z - c) * κ.e k z -
          ((a / 2 : ℝ) • pdCx 0 (κ.lamP m) (z - c)) * κ.e k z := by
      funext z
      rw [hpt_split z, add_sub_cancel_right]
    rw [heq]
    exact hInt_sum.sub hInt_drift
  -- Apply planar `D^#` vs `D` IBP to `La` and `κ.e k`
  have hLa_CD : ContDiff ℝ 2 La := (hCD m).comp (contDiff_id.sub contDiff_const)
  have hc_norm : ‖c‖ = |a| := by simp [c, Prod.norm_def]
  have hd_m : Differentiable ℝ (κ.lamP m) := (hCD m).differentiable (by norm_num)
  have hLa_0 : ∀ z : ℝ × ℝ, ‖La z‖ ≤ C * (1 + |a|) := fun z => by
    have hb : ‖La z‖ ≤ C := (h0 m (z - c)).trans (mul_le_of_le_one_right hC0 (hw1 (z - c)))
    nlinarith [abs_nonneg a]
  have hLa_1 : ∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ La z‖ ≤ C * (1 + |a|) := fun z => by
    have hf : fderiv ℝ La z = fderiv ℝ (κ.lamP m) (z - c) :=
      ((hd_m (z - c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)).fderiv
    rw [hf]
    have htri : ‖z‖ ≤ ‖z - c‖ + |a| := by
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = ‖z - c‖ + |a| := by rw [hc_norm]
    have h1z : 1 + ‖z‖ ≤ (1 + |a|) * (1 + ‖z - c‖) := by
      nlinarith [norm_nonneg (z - c), abs_nonneg a]
    have hb : (1 + ‖z - c‖) * ‖fderiv ℝ (κ.lamP m) (z - c)‖ ≤ C :=
      (h1 m (z - c)).trans (mul_le_of_le_one_right hC0 (hw1 (z - c)))
    calc (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP m) (z - c)‖
        ≤ ((1 + |a|) * (1 + ‖z - c‖)) * ‖fderiv ℝ (κ.lamP m) (z - c)‖ :=
          mul_le_mul_of_nonneg_right h1z (norm_nonneg _)
      _ = (1 + |a|) * ((1 + ‖z - c‖) * ‖fderiv ℝ (κ.lamP m) (z - c)‖) := by ring
      _ ≤ (1 + |a|) * C := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * (1 + |a|) := by ring
  have hLa_2 : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 La z‖ ≤ C * (1 + |a|) := fun z => by
    change ‖iteratedFDeriv ℝ 2 (fun w => κ.lamP m (w - c)) z‖ ≤ C * (1 + |a|)
    rw [iteratedFDeriv_comp_sub 2 c z]
    have hb : ‖iteratedFDeriv ℝ 2 (κ.lamP m) (z - c)‖ ≤ C :=
      (h2 m (z - c)).trans (mul_le_of_le_one_right hC0 (hw1 (z - c)))
    nlinarith [abs_nonneg a]
  have hgw : ∀ y : ℝ × ℝ, OscGramIBP.gw y = Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := fun _ => rfl
  have hibp := OscGramIBP.integral_dualGen_mul (C := C * (1 + |a|)) (B := B0 + B1 + B2)
    hLa_CD ((hsm_e k).of_le (by simp)) hLa_0 hLa_1 hLa_2
    (fun y => by
      have := hb0 y; rw [norm_iteratedFDeriv_zero] at this; rw [hgw]
      nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8)])
    (fun y => by
      have := hb1 y; rw [norm_iteratedFDeriv_one] at this; rw [hgw]
      nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8)])
    (fun y => by
      have := hb2 y; rw [hgw]
      nlinarith [Real.exp_pos (-(y.1 ^ 2 + y.2 ^ 2) / 8),
        norm_nonneg (iteratedFDeriv ℝ 2 (κ.e k) y), norm_nonneg y])
  -- Shift back `z - c = y` to get `oscGramTerm`
  have hshift_osc : (∫ z : ℝ × ℝ, La z * movD (κ.e k) z) = oscGramTerm κ d m k n := by
    unfold oscGramTerm
    have h := integral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
      (fun y : ℝ × ℝ => κ.lamP m y * movD (κ.e k) (y.1 + a, y.2)) c
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only [La]
    have h2 : ((z - c).1 + a, (z - c).2) = z := by
      ext <;> simp [c, sub_add_cancel]
    rw [h2]
  -- Match the drift term with `-(d / 2) * gramTermDeriv`
  have hdrift_eq :
      (∫ z : ℝ × ℝ, ((a / 2 : ℝ) • pdCx 0 (κ.lamP m) (z - c)) * κ.e k z) =
        (-(d / 2 : ℂ)) * ComplCouplingHeat.gramTermDeriv κ d m k n := by
    rw [ComplCouplingHeat.gramTermDeriv_eq_shift_lamP, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    have hzc : z - c = (z.1 - (n : ℝ) * d, z.2) := by ext <;> simp [c, a]
    rw [hzc]
    simp only [a, Complex.real_smul]
    push_cast
    ring
  rw [hshift_lhs, show (fun z => UnforcedLeray.Gaussian.dualGen (κ.lamP m) (z - c) * κ.e k z) =
      fun z => UnforcedLeray.Gaussian.dualGen La z * κ.e k z +
        ((a / 2 : ℝ) • pdCx 0 (κ.lamP m) (z - c)) * κ.e k z from funext hpt_split,
    integral_add hInt_La hInt_drift, hibp, hshift_osc, hdrift_eq]

/-- Unnormalised heat-dual pairing identity on `B0579.cell d` (`d > 0`):
`∫_{cell d} movLam0DualHeat κ ν r m * perE κ d k =`
`  ∫_{cell d} perLam0 κ d m * movOscRes κ ν r k - (θ(r)⁻¹ * (d / 2)) * perGramDeriv κ d m k`. -/
private lemma integral_movLam0DualHeat_mul_perE_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (m k : Fin 2) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    ∫ y in B0579.cell d, movLam0DualHeat κ ν r m y * perE κ d k y =
      (∫ y in B0579.cell d, perLam0 κ d m y * movOscRes κ ν r k y) -
        ((clockTheta ν r : ℂ)⁻¹ * (d / 2 : ℂ)) * ComplCouplingHeat.perGramDeriv κ d m k := by
  intro d
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hd0 : 0 < d := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha0)
  obtain ⟨hCD, C, _hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  obtain ⟨ht0, ht1, ht2⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 m) (h1 m) (h2 m)
  have hid : ∀ y, movLam0DualHeat κ ν r m y =
      (clockTheta ν r : ℂ)⁻¹ * perSum d (UnforcedLeray.Gaussian.dualGen (κ.lamP m)) y :=
    fun y => ComplCouplingHeat.movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen
      κ hν hr m (hCD m) ht0 ht1 ht2 y
  have hlhs : (∫ y in B0579.cell d, movLam0DualHeat κ ν r m y * perE κ d k y) =
      (clockTheta ν r : ℂ)⁻¹ *
        ∫ y in B0579.cell d,
          perSum d (UnforcedLeray.Gaussian.dualGen (κ.lamP m)) y * perSum d (κ.e k) y := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_Ico.prod MeasurableSet.univ) fun y _ => ?_
    rw [hid y]
    simp only [perE]
    ring
  have hΨc : Continuous (UnforcedLeray.Gaussian.dualGen (κ.lamP m)) :=
    ComplCouplingHeat.continuous_dualGen (hCD m)
  have hΨb : ∀ y : ℝ × ℝ,
      ‖UnforcedLeray.Gaussian.dualGen (κ.lamP m) y‖ ≤ (7 / 2 * C) * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
    fun y => ComplCouplingHeat.norm_dualGen_le_inv_sq (hCD m) (h0 m) (h1 m) (h2 m) y
  obtain ⟨hS_dual, hunf_dual⟩ := OscGramDual.unfold hΨc (κ.e_cont k) hΨb (hCe k) hd0
  obtain ⟨hS_osc, hunf_osc⟩ := OscGramSub.oscGram_unfold hκ hd0 m k
  have hterm := dualGen_cross_term_eq hκ d m k
  have hS_scaled_g : Summable
      (fun n : ℤ => (-(d / 2 : ℂ)) * ComplCouplingHeat.gramTermDeriv κ d m k n) := by
    have heq : (fun n : ℤ => (-(d / 2 : ℂ)) * ComplCouplingHeat.gramTermDeriv κ d m k n) =
        fun n : ℤ =>
          (∫ y : ℝ × ℝ, UnforcedLeray.Gaussian.dualGen (κ.lamP m) y *
              κ.e k (y.1 + (n : ℝ) * d, y.2)) - oscGramTerm κ d m k n := by
      funext n
      rw [hterm n, add_sub_cancel_left]
    rw [heq]
    exact hS_dual.sub hS_osc
  have hd2_ne : (-(d / 2 : ℂ)) ≠ 0 := by
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    simp [hdC]
  have hS_g : Summable (fun n : ℤ => ComplCouplingHeat.gramTermDeriv κ d m k n) := by
    have heq : (fun n : ℤ => ComplCouplingHeat.gramTermDeriv κ d m k n) =
        fun n : ℤ => (-(d / 2 : ℂ))⁻¹ *
          ((-(d / 2 : ℂ)) * ComplCouplingHeat.gramTermDeriv κ d m k n) := by
      funext n
      rw [← mul_assoc, inv_mul_cancel₀ hd2_ne, one_mul]
    rw [heq]
    exact hS_scaled_g.mul_left _
  have htsum_eq :
      (∑' n : ℤ, ∫ y : ℝ × ℝ, UnforcedLeray.Gaussian.dualGen (κ.lamP m) y *
          κ.e k (y.1 + (n : ℝ) * d, y.2)) =
        oscGram κ d m k + (-(d / 2 : ℂ)) * ComplCouplingHeat.perGramDeriv κ d m k := by
    simp_rw [hterm]
    rw [hS_osc.tsum_add hS_scaled_g, ← hunf_osc, tsum_mul_left]
    rfl
  have hosc_cell : (∫ y in B0579.cell d, perLam0 κ d m y * movOscRes κ ν r k y) =
      (clockTheta ν r : ℂ)⁻¹ * oscGram κ d m k :=
    OscGramSub.integral_perLam0_mul_movOscRes_eq hκ hν hr m k
  rw [hlhs, hunf_dual, htsum_eq, hosc_cell]
  ring

/-- **Heat / Oscillator pairing identity**: for `IsSeedKernels κ`, there exists `D_H ≥ 1` such that
whenever `d = cellLen (ν ^ (-2 : ℝ)) (clockA ν r) ≥ D_H` (`0 < ν`, `0 ≤ r`) and
`MemLp (movOscRes κ ν r k) 2 (B0579.cellMeasure d m_wt)` (`8 < m_wt`),
`∫_{cell d} movLamDualHeat κ ν r i * perE κ d k = ∫_{cell d} perLam κ d i * movOscRes κ ν r k`. -/
theorem movLamDualHeat_pairing_perE_eq_movOscRes {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ D_H : ℝ, 1 ≤ D_H ∧
      ∀ {ν r m_wt : ℝ}, 0 < ν → 0 ≤ r → 8 < m_wt →
        D_H ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) →
        ∀ (i k : Fin 2),
          MemLp (movOscRes κ ν r k) 2
            (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m_wt) →
          ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
              movLamDualHeat κ ν r i y *
                perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k y =
            ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
              perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i y *
                movOscRes κ ν r k y := by
  obtain ⟨C_G, D_G, hCG0, hDG1, hGnear⟩ := ComplCouplingEuler.perGram_sub_id_bound κ
  obtain ⟨hCD, C, hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨C_Gd, hCGd0, hGd⟩ := ComplCouplingHeat.hasDerivAt_perGram_and_bound κ hCD h1
  set D_H : ℝ := 2 * max D_G (2 * Real.sqrt C_G + 1)
  have hDH1 : 1 ≤ D_H := by
    have : 1 ≤ max D_G (2 * Real.sqrt C_G + 1) := le_trans hDG1 (le_max_left _ _)
    linarith
  refine ⟨D_H, hDH1, fun {ν r m_wt} hν hr hm hd_ge i k hOscMem => ?_⟩
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd1 : 1 ≤ d := hDH1.trans hd_ge
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  -- Near-identity bound on `(d / 2, ∞)`
  have hnear_Ioi : ∀ d' : ℝ, d / 2 < d' →
      ∀ m n : Fin 2, ‖perGram κ d' m n - (if m = n then 1 else 0)‖ ≤ 1 / 4 := by
    intro d' hd' m n
    have hmax_le : max D_G (2 * Real.sqrt C_G + 1) ≤ d' := by
      have : 2 * max D_G (2 * Real.sqrt C_G + 1) ≤ d := hd_ge
      linarith
    have hd'_DG : D_G ≤ d' := (le_max_left _ _).trans hmax_le
    have hd'_sq : 2 * Real.sqrt C_G + 1 ≤ d' := (le_max_right _ _).trans hmax_le
    have hd'_pos : 0 < d' := by linarith [Real.sqrt_nonneg C_G]
    have h4CG : 4 * C_G ≤ d' ^ 2 := by
      have hsq : (2 * Real.sqrt C_G) ^ 2 = 4 * C_G := by
        calc (2 * Real.sqrt C_G) ^ 2 = 4 * (Real.sqrt C_G) ^ 2 := by ring
          _ = 4 * C_G := by rw [Real.sq_sqrt hCG0]
      have hle : 2 * Real.sqrt C_G ≤ d' := by linarith
      nlinarith [Real.sqrt_nonneg C_G]
    refine (hGnear d' hd'_DG m n).trans ?_
    rw [div_le_iff₀ (sq_pos_of_pos hd'_pos)]
    linarith
  -- Differentiate `(perGram κ ·)⁻¹` and `(perGram κ ·)⁻¹ * perGram κ · = 1` at `d`
  have hd_half : d / 2 < d := by linarith
  have hB0 : 0 ≤ C_Gd / d ^ 3 := by positivity
  have hinv_der : ∀ m : Fin 2, ∃ g' : ℂ,
      HasDerivAt (fun d' => (perGram κ d')⁻¹ i m) g' d := by
    intro m
    obtain ⟨g', hg', -⟩ := ComplCouplingHeat.hasDerivAt_matrix_inv_fin2 (G := perGram κ)
      (G' := fun a b => ComplCouplingHeat.perGramDeriv κ d a b) hB0
      (hnear_Ioi d hd_half) (fun a b => (hGd hd0 a b).1) (fun a b => (hGd hd0 a b).2) i m
    exact ⟨g', hg'⟩
  choose g' hg' using hinv_der
  have hprod_der : HasDerivAt
      (fun d' => (perGram κ d')⁻¹ i 0 * perGram κ d' 0 k +
        (perGram κ d')⁻¹ i 1 * perGram κ d' 1 k)
      ((g' 0 * perGram κ d 0 k +
          (perGram κ d)⁻¹ i 0 * ComplCouplingHeat.perGramDeriv κ d 0 k) +
        (g' 1 * perGram κ d 1 k +
          (perGram κ d)⁻¹ i 1 * ComplCouplingHeat.perGramDeriv κ d 1 k)) d :=
    ((hg' 0).mul (hGd hd0 0 k).1).add ((hg' 1).mul (hGd hd0 1 k).1)
  have hprod_ev : (fun d' => (perGram κ d')⁻¹ i 0 * perGram κ d' 0 k +
        (perGram κ d')⁻¹ i 1 * perGram κ d' 1 k) =ᶠ[𝓝 d]
      fun _ => (if i = k then (1 : ℂ) else 0) := by
    filter_upwards [lt_mem_nhds hd_half] with d' hd'
    have hdet := det_ne_zero_of_near_id (hnear_Ioi d' hd')
    have hmul : (perGram κ d')⁻¹ * perGram κ d' = 1 := Matrix.nonsing_inv_mul _ hdet
    have hent := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i k) hmul
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] using hent
  have hprod_zero :
      (g' 0 * perGram κ d 0 k +
          (perGram κ d)⁻¹ i 0 * ComplCouplingHeat.perGramDeriv κ d 0 k) +
        (g' 1 * perGram κ d 1 k +
          (perGram κ d)⁻¹ i 1 * ComplCouplingHeat.perGramDeriv κ d 1 k) = 0 :=
    hprod_der.unique ((hasDerivAt_const d (if i = k then (1 : ℂ) else 0)).congr_of_eventuallyEq
      hprod_ev)
  -- Pointwise decomposition of `movLamDualHeat κ ν r i`
  obtain ⟨ht0_0, ht1_0, ht2_0⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 0) (h1 0) (h2 0)
  obtain ⟨ht0_1, ht1_1, ht2_1⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 1) (h1 1) (h2 1)
  have ht0 : ∀ m : Fin 2, ∀ z, ‖κ.lamP m z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro m; fin_cases m; exacts [ht0_0, ht0_1]
  have ht1 : ∀ m : Fin 2, ∀ z, (1 + ‖z‖) * ‖fderiv ℝ (κ.lamP m) z‖ ≤
      |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro m; fin_cases m; exacts [ht1_0, ht1_1]
  have ht2 : ∀ m : Fin 2, ∀ z, ‖iteratedFDeriv ℝ 2 (κ.lamP m) z‖ ≤
      |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro m; fin_cases m; exacts [ht2_0, ht2_1]
  have hG_diff : ∀ m : Fin 2, DifferentiableWithinAt ℝ
      (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i m) (Ici r) r := by
    intro m
    exact ((DirectHeatDecomp.hasDerivAt_perGram_inv_comp_cellLen κ hν hr i m (hg' m)).differentiableAt).differentiableWithinAt
  have hmov_split : ∀ y : ℝ × ℝ, movLamDualHeat κ ν r i y =
      (∑ m : Fin 2, (perGram κ d)⁻¹ i m * movLam0DualHeat κ ν r m y) +
      (∑ m : Fin 2, movGramInvDeriv κ ν r i m * perLam0 κ d m y) :=
    fun y => DirectHeatDecomp.movLamDualHeat_eq_sum_of_diff κ hν hr hCD ht0 ht1 ht2 i hG_diff y
  have hGinv_der_eq : ∀ m : Fin 2, movGramInvDeriv κ ν r i m =
      -((clockTheta ν r : ℂ)⁻¹ * (d / 2 : ℂ)) * g' m := by
    intro m
    rw [DirectHeatDecomp.movGramInvDeriv_eq_of_hasDerivAt κ hν hr i m (hg' m), Complex.real_smul]
    push_cast
    ring
  -- Integrability on `B0579.cell d` of each piece via `CutLimitAux.integrable_complex`
  obtain ⟨_, _, hperE_all⟩ := DirectHeatDecomp.perE_memLp_cellMeasure κ hm
  have hperE_mem : MemLp (perE κ d k) 2 (B0579.cellMeasure d m_wt) := (hperE_all hd1 k).1
  obtain ⟨_, _, hLam0_mem⟩ := ComplCouplingHeat.memLp_and_xNorm_perLam0_neg κ (m := m_wt)
    (by linarith)
  have hInt_lam0_perE : ∀ m : Fin 2,
      IntegrableOn (fun y => perLam0 κ d m y * perE κ d k y) (B0579.cell d) := by
    intro m
    have h := CutLimitAux.integrable_complex hperE_mem (hLam0_mem d hd1 m).1
    exact h.congr (ae_of_all _ fun y => mul_comm _ _)
  have hInt_lam0_osc : ∀ m : Fin 2,
      IntegrableOn (fun y => perLam0 κ d m y * movOscRes κ ν r k y) (B0579.cell d) := by
    intro m
    have h := CutLimitAux.integrable_complex hOscMem (hLam0_mem d hd1 m).1
    exact h.congr (ae_of_all _ fun y => mul_comm _ _)
  have hInt_dual0_perE : ∀ m : Fin 2,
      IntegrableOn (fun y => movLam0DualHeat κ ν r m y * perE κ d k y) (B0579.cell d) := by
    intro m
    have hΨc : Continuous (UnforcedLeray.Gaussian.dualGen (κ.lamP m)) :=
      ComplCouplingHeat.continuous_dualGen (hCD m)
    have hΨb : ∀ z : ℝ × ℝ,
        ‖UnforcedLeray.Gaussian.dualGen (κ.lamP m) z‖ ≤
          (7 / 2 * C) * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
      fun z => ComplCouplingHeat.norm_dualGen_le_inv_sq (hCD m) (h0 m) (h1 m) (h2 m) z
    obtain ⟨_, _, hΨ_mem⟩ :=
      ComplCouplingHeat.memLp_and_xNorm_perSum_of_inv_sq_decay (m := m_wt) (by linarith) hΨc hΨb
    obtain ⟨ht0_m, ht1_m, ht2_m⟩ := ComplCouplingHeat.translate_jet2_bounds (h0 m) (h1 m) (h2 m)
    have hmem : MemLp (movLam0DualHeat κ ν r m) 2 (B0579.cellMeasure d (-m_wt)) := by
      have heq : movLam0DualHeat κ ν r m =
          fun y => (clockTheta ν r : ℂ)⁻¹ *
            perSum d (UnforcedLeray.Gaussian.dualGen (κ.lamP m)) y :=
        funext fun y => ComplCouplingHeat.movLam0DualHeat_eq_inv_clockTheta_mul_perSum_dualGen
          κ hν hr m (hCD m) ht0_m ht1_m ht2_m y
      rw [heq]
      exact (hΨ_mem d hd1).1.const_mul _
    have h := CutLimitAux.integrable_complex hperE_mem hmem
    exact h.congr (ae_of_all _ fun y => mul_comm _ _)
  -- Expand LHS and RHS integrals over `Fin 2` and cancel `(G⁻¹ G)' = 0`
  set c0 : ℂ := (perGram κ d)⁻¹ i 0
  set c1 : ℂ := (perGram κ d)⁻¹ i 1
  set b0 : ℂ := movGramInvDeriv κ ν r i 0
  set b1 : ℂ := movGramInvDeriv κ ν r i 1
  have hA0 : IntegrableOn (fun y => c0 * (movLam0DualHeat κ ν r 0 y * perE κ d k y))
      (B0579.cell d) := (hInt_dual0_perE 0).const_mul c0
  have hA1 : IntegrableOn (fun y => c1 * (movLam0DualHeat κ ν r 1 y * perE κ d k y))
      (B0579.cell d) := (hInt_dual0_perE 1).const_mul c1
  have hB0_int : IntegrableOn (fun y => b0 * (perLam0 κ d 0 y * perE κ d k y))
      (B0579.cell d) := (hInt_lam0_perE 0).const_mul b0
  have hB1_int : IntegrableOn (fun y => b1 * (perLam0 κ d 1 y * perE κ d k y))
      (B0579.cell d) := (hInt_lam0_perE 1).const_mul b1
  have hlhs_exp :
      (∫ y in B0579.cell d, movLamDualHeat κ ν r i y * perE κ d k y) =
        (c0 * (∫ y in B0579.cell d, movLam0DualHeat κ ν r 0 y * perE κ d k y) +
          c1 * (∫ y in B0579.cell d, movLam0DualHeat κ ν r 1 y * perE κ d k y)) +
        (b0 * perGram κ d 0 k + b1 * perGram κ d 1 k) := by
    have hcongr : (fun y => movLamDualHeat κ ν r i y * perE κ d k y) =
        fun y =>
          (c0 * (movLam0DualHeat κ ν r 0 y * perE κ d k y) +
            c1 * (movLam0DualHeat κ ν r 1 y * perE κ d k y)) +
          (b0 * (perLam0 κ d 0 y * perE κ d k y) +
            b1 * (perLam0 κ d 1 y * perE κ d k y)) := by
      funext y
      rw [hmov_split y]
      simp only [Fin.sum_univ_two, c0, c1, b0, b1]
      ring
    rw [hcongr,
      integral_add (f := fun y => c0 * (movLam0DualHeat κ ν r 0 y * perE κ d k y) +
          c1 * (movLam0DualHeat κ ν r 1 y * perE κ d k y))
        (g := fun y => b0 * (perLam0 κ d 0 y * perE κ d k y) +
          b1 * (perLam0 κ d 1 y * perE κ d k y))
        (hA0.add hA1) (hB0_int.add hB1_int),
      integral_add (f := fun y => c0 * (movLam0DualHeat κ ν r 0 y * perE κ d k y))
        (g := fun y => c1 * (movLam0DualHeat κ ν r 1 y * perE κ d k y)) hA0 hA1,
      integral_add (f := fun y => b0 * (perLam0 κ d 0 y * perE κ d k y))
        (g := fun y => b1 * (perLam0 κ d 1 y * perE κ d k y)) hB0_int hB1_int,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  have hO0 : IntegrableOn (fun y => c0 * (perLam0 κ d 0 y * movOscRes κ ν r k y))
      (B0579.cell d) := (hInt_lam0_osc 0).const_mul c0
  have hO1 : IntegrableOn (fun y => c1 * (perLam0 κ d 1 y * movOscRes κ ν r k y))
      (B0579.cell d) := (hInt_lam0_osc 1).const_mul c1
  have hrhs_exp :
      (∫ y in B0579.cell d, perLam κ d i y * movOscRes κ ν r k y) =
        c0 * (∫ y in B0579.cell d, perLam0 κ d 0 y * movOscRes κ ν r k y) +
          c1 * (∫ y in B0579.cell d, perLam0 κ d 1 y * movOscRes κ ν r k y) := by
    have hcongr : (fun y => perLam κ d i y * movOscRes κ ν r k y) =
        fun y =>
          c0 * (perLam0 κ d 0 y * movOscRes κ ν r k y) +
            c1 * (perLam0 κ d 1 y * movOscRes κ ν r k y) := by
      funext y
      unfold perLam
      simp only [Fin.sum_univ_two, c0, c1]
      ring
    rw [hcongr,
      integral_add (f := fun y => c0 * (perLam0 κ d 0 y * movOscRes κ ν r k y))
        (g := fun y => c1 * (perLam0 κ d 1 y * movOscRes κ ν r k y)) hO0 hO1,
      integral_const_mul, integral_const_mul]
  rw [hlhs_exp, hrhs_exp,
    integral_movLam0DualHeat_mul_perE_eq hκ hν hr 0 k,
    integral_movLam0DualHeat_mul_perE_eq hκ hν hr 1 k]
  have hb0_eq : b0 = -((clockTheta ν r : ℂ)⁻¹ * (d / 2 : ℂ)) * g' 0 := hGinv_der_eq 0
  have hb1_eq : b1 = -((clockTheta ν r : ℂ)⁻¹ * (d / 2 : ℂ)) * g' 1 := hGinv_der_eq 1
  rw [hb0_eq, hb1_eq]
  dsimp only [d, c0, c1] at hprod_zero ⊢
  linear_combination -((clockTheta ν r : ℂ)⁻¹ * (d / 2 : ℂ)) * hprod_zero

end UnforcedLeray.Short.IIIa.MovFrameLeavesAux
