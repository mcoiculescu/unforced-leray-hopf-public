import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_1

/-!
# Part III-a, task `PartIII-a:T22/2/2/2`: canonical column weak equation (`ColumnWeakEq`)

Source of record: `the November 2 reference manuscript`, lines 3130-3140
(`eq:ct-moving-period`).

Proves `ResidualBoundAux.CanonicalColumnWeakEq` via:
1. 2D Hermite-Laguerre Gaussian mode expansion of `planarMode (P.canonical θ)` on `(0, ∞) × ℝ²`,
   supplying `LamJetInf.Good` spatial regularity, uniform Gaussian jet bounds on compact `θ`-windows,
   and the global planar operator identities `movD (Φ θ) = planarMode (oscillatorD (P.canonical θ))`
   and `movLPlanar (Φ θ) = planarMode (generatorL0 (P.canonical θ))`.
2. Fixed-period physical-coordinate calculus on `cell (ν ^ (-2 : ℝ))`, cancelling the `θ⁻¹ movD`
   term against `(∂_s - ν Δ)` and identifying `canonicalPhysResidual` with the physical PDE residual
   `∂_s w - ν Δ w + (v · ∇) w + (K_c w · ∇) E`.
3. Unconditional `IsBUCTrain` + `ComplMildGAux` exponential velocity-tail estimates giving
   `IsBiotSavart`, `MemLp` in `X_{m,c}`, `xNorm c m`-continuity on `[0, clockAge ν r_min]`,
   `IsCentrallyEven`, `HasZeroCirculation`, and the cylinder weak identity via IBP + FTC.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIIa.T22Sub.ColumnWeakEqAux

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.IIIa.T22Sub
open UnforcedLeray.Short.IIIa.T22Sub.ResidualBoundAux

/-! ## 1. Basic periodization, parity, and cell-reflection helpers -/

private theorem periodizeC_eq_perSum (d : ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    periodizeC d g x = perSum d g x := by
  unfold periodizeC perSum
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  ext <;> simp [sub_eq_add_neg, neg_mul]

private theorem perSum_periodic (d : ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perSum d g (x.1 + d, x.2) = perSum d g x := by
  unfold perSum
  rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  apply Prod.ext <;> simp
  ring

private theorem periodizeC_periodic (d : ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    periodizeC d g (x.1 + d, x.2) = periodizeC d g x := by
  rw [periodizeC_eq_perSum, periodizeC_eq_perSum]
  exact perSum_periodic d g x

private theorem periodizeC_neg {d : ℝ} {g : ℝ × ℝ → ℂ} (hg : ∀ y, g (-y) = g y) (x : ℝ × ℝ) :
    periodizeC d g (-x) = periodizeC d g x := by
  unfold periodizeC
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  have hpt : ((-x).1 - ((Equiv.neg ℤ n : ℤ) : ℝ) * d, (-x).2) = -(x.1 - (n : ℝ) * d, x.2) := by
    apply Prod.ext <;> simp
    ring
  rw [hpt, hg]

private theorem angTwo_neg_pt (x : ℝ × ℝ) : angTwo (-x) = angTwo x := by
  unfold angTwo
  simp only [Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg, neg_sq]
  congr 1
  ring

private theorem planarMode_neg_pt (f : Profile) (x : ℝ × ℝ) :
    planarMode f (-x) = planarMode f x := by
  unfold planarMode
  rw [angTwo_neg_pt]
  simp

private theorem jscale_neg {a : ℝ} {W : ℝ × ℝ → ℂ} (hW : ∀ y, W (-y) = W y) (x : ℝ × ℝ) :
    Jscale a W (-x) = Jscale a W x := by
  unfold Jscale
  have hpt : ((-x).1 / Real.sqrt a, (-x).2 / Real.sqrt a) =
      -(x.1 / Real.sqrt a, x.2 / Real.sqrt a) := by
    ext <;> simp [neg_div]
  rw [hpt, hW]

private theorem isCentrallyEven_canonicalPhysColumn (P : PlanarData) {ν s : ℝ}
    (hν : 0 < ν) (ha : 0 < clockA ν s) :
    IsCentrallyEven (canonicalPhysColumn P ν s) := by
  intro x
  rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha (-x),
    canonicalPhysColumn_eq_periodizeC_planar P hν ha x,
    periodizeC_neg (jscale_neg (planarMode_neg_pt _))]

private theorem integral_cell_comp_neg {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × ℝ → E) :
    (∫ z in B0579.cell c, F (-z)) = ∫ z in B0579.cell c, F z := by
  let S : Set (ℝ × ℝ) := Ioc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)
  have hpre : Neg.neg ⁻¹' B0579.cell c = S := by
    ext ⟨q, η⟩
    simp only [mem_preimage, B0579.cell, S, mem_prod, mem_Ico, mem_Ioc, mem_univ, and_true,
      Prod.fst_neg]
    constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hline_null : ∀ a : ℝ, volume ({a} ×ˢ (univ : Set ℝ)) = 0 := by
    intro a
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hae : S =ᵐ[volume] B0579.cell c := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun ⟨q, η⟩ h => ?_) (hline_null (c / 2))
      rcases h with ⟨⟨⟨hq1, hq2⟩, _⟩, hnot⟩
      have hge : c / 2 ≤ q := by
        by_contra hlt
        exact hnot ⟨⟨hq1.le, not_le.1 hlt⟩, trivial⟩
      exact ⟨mem_singleton_iff.2 (le_antisymm hq2 hge), trivial⟩
    · refine measure_mono_null (fun ⟨q, η⟩ h => ?_) (hline_null (-(c / 2)))
      rcases h with ⟨⟨⟨hq1, hq2⟩, _⟩, hnot⟩
      have hle : q ≤ -(c / 2) := by
        by_contra hgt
        exact hnot ⟨⟨not_le.1 hgt, hq2.le⟩, trivial⟩
      exact ⟨mem_singleton_iff.2 (le_antisymm hle hq1), trivial⟩
  have hind : (fun z => S.indicator F (-z)) = (B0579.cell c).indicator (fun z => F (-z)) := by
    funext z
    have hmem : -z ∈ S ↔ z ∈ B0579.cell c := by
      rw [← hpre, mem_preimage, neg_neg]
    by_cases hz : z ∈ B0579.cell c
    · rw [indicator_of_mem hz, indicator_of_mem (hmem.2 hz)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (mt hmem.1 hz)]
  calc ∫ z in B0579.cell c, F (-z)
      = ∫ z, (B0579.cell c).indicator (fun w => F (-w)) z :=
          (integral_indicator (measurableSet_Ico.prod MeasurableSet.univ)).symm
    _ = ∫ z, S.indicator F (-z) := by rw [hind]
    _ = ∫ z, S.indicator F z := integral_neg_eq_self (S.indicator F) volume
    _ = ∫ z in S, F z := integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)
    _ = ∫ z in B0579.cell c, F z := setIntegral_congr_set hae

/-! ## 2. 2D Hermite-Laguerre Gaussian modes and jet bounds -/

private noncomputable def hermiteProf (ℓ : ℕ) : Profile :=
  UnforcedLeray.B0094.profFun (UnforcedLeray.B0121.lev ℓ)

private noncomputable def hermiteMode (ℓ : ℕ) : ℝ × ℝ → ℂ :=
  ⇑(UnforcedLeray.B0121.gS (UnforcedLeray.B0121.φS ℓ))

private theorem sqG_le_exp_div_eight (z : ℝ × ℝ) :
    UnforcedLeray.B0121.sqG z ≤ Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  have hsq : UnforcedLeray.B0121.sqG z ^ 2 ≤ (Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) ^ 2 := by
    rw [UnforcedLeray.B0121.sqG_sq, ← Real.exp_nat_mul]
    unfold UnforcedLeray.B0093.gaussianWeight UnforcedLeray.GaussianVortex.planarGaussian
      UnforcedLeray.GaussianVortex.radiusSq
    have h4pi : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
    have hinv : (4 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h4pi
    have hexp_eq : ((2 : ℕ) : ℝ) * (-(z.1 ^ 2 + z.2 ^ 2) / 8) = -((z.1 ^ 2 + z.2 ^ 2) / 4) := by
      push_cast; ring
    rw [hexp_eq]
    calc (4 * Real.pi)⁻¹ * Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 4))
        ≤ 1 * Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 4)) :=
          mul_le_mul_of_nonneg_right hinv (Real.exp_nonneg _)
      _ = Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 4)) := one_mul _
  rw [sq, sq] at hsq
  exact nonneg_le_nonneg_of_sq_le_sq (Real.exp_nonneg _) hsq

private theorem planarMode_eq_seedPlanar (f : Profile) (x : ℝ × ℝ) :
    planarMode f x = UnforcedLeray.Short.PartI.seedPlanar f (planeToC x) := by
  have hnorm_sq : ‖planeToC x‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 :=
    OscillatorForceSub.norm_planeToC_sq x
  have hnorm : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) = ‖planeToC x‖ := by
    rw [← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hp_eq : (x.1 : ℂ) + (x.2 : ℂ) * Complex.I = planeToC x := by
    apply Complex.ext <;> simp [planeToC]
  have hc : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) = (‖planeToC x‖ : ℂ) ^ 2 := by
    exact_mod_cast hnorm_sq.symm
  unfold planarMode angTwo UnforcedLeray.Short.PartI.seedPlanar
    UnforcedLeray.Planar.NUE.Ang.ofProfile UnforcedLeray.Planar.NUE.Ang.angPhase
  rw [hnorm, hp_eq, hc, zpow_ofNat, div_pow]

private theorem planarMode_eq_angularTwoField_of_ne (f : Profile) {x : ℝ × ℝ} (hx : x ≠ 0) :
    planarMode f x = UnforcedLeray.B0010.angularTwoField f x := by
  unfold planarMode angTwo UnforcedLeray.B0010.angularTwoField
  have hpol1 : (polarCoord x).1 = Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := rfl
  have hpol2 : (polarCoord x).2 =
      Complex.arg (Complex.equivRealProd.symm x) := rfl
  rw [hpol1, hpol2]
  congr 1
  set z : ℂ := Complex.equivRealProd.symm x
  have hz_eq : z = (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [z]
  have hz_ne : z ≠ 0 := by
    intro h0
    apply hx
    apply Prod.ext <;> dsimp
    · simpa using congrArg Complex.re (hz_eq.symm.trans h0)
    · simpa using congrArg Complex.im (hz_eq.symm.trans h0)
  have hnsq : ‖z‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    rw [hz_eq, Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  have hpolar := congrArg (fun w : ℂ => w ^ 2) (Complex.norm_mul_exp_arg_mul_I z)
  rw [mul_pow, ← Complex.exp_nat_mul] at hpolar
  have hexp_arg : ((2 : ℕ) : ℂ) * (↑(Complex.arg z) * Complex.I) =
      2 * Complex.I * ↑(Complex.arg z) := by push_cast; ring
  rw [hexp_arg] at hpolar
  have hden_eq : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    exact_mod_cast hnsq.symm
  have hden_ne : (‖z‖ : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz_ne))
  rw [← hz_eq, hden_eq, div_eq_iff hden_ne, mul_comm _ ((‖z‖ : ℂ) ^ 2)]
  exact hpolar.symm

private theorem planarMode_hermiteProf_eq_hermiteMode (ℓ : ℕ) (x : ℝ × ℝ) :
    planarMode (hermiteProf ℓ) x = hermiteMode ℓ x := by
  have hne : ∀ y : ℝ × ℝ, y ≠ 0 → planarMode (hermiteProf ℓ) y = hermiteMode ℓ y := by
    intro y hy
    unfold hermiteMode
    rw [← UnforcedLeray.B0121.angularTwoField_schProf_eq_gS (UnforcedLeray.B0121.isAngularTwo_φS ℓ),
      UnforcedLeray.B0121.φS, UnforcedLeray.B0094.schProf_coreS]
    exact planarMode_eq_angularTwoField_of_ne (hermiteProf ℓ) hy
  by_cases hx : x = 0
  · subst hx
    have h0 : planarMode (hermiteProf ℓ) (0 : ℝ × ℝ) = 0 := by simp [planarMode, angTwo]
    rw [h0]
    have hcont : Continuous (hermiteMode ℓ) := (UnforcedLeray.B0121.gS _).smooth'.continuous
    have hseq : Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹ : ℝ)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have ht1 : Tendsto (fun n : ℕ => hermiteMode ℓ (((n + 1 : ℝ)⁻¹), 0)) atTop
        (𝓝 (hermiteMode ℓ (0, 0))) :=
      (hcont.tendsto (0, 0)).comp (hseq.prodMk_nhds tendsto_const_nhds)
    have ht2 : Tendsto (fun n : ℕ => hermiteMode ℓ (0, ((n + 1 : ℝ)⁻¹))) atTop
        (𝓝 (hermiteMode ℓ (0, 0))) :=
      (hcont.tendsto (0, 0)).comp (tendsto_const_nhds.prodMk_nhds hseq)
    have hneg : (fun n : ℕ => hermiteMode ℓ (0, ((n + 1 : ℝ)⁻¹))) =
        fun n : ℕ => -hermiteMode ℓ (((n + 1 : ℝ)⁻¹), 0) := by
      funext n
      set r : ℝ := ((n + 1 : ℝ)⁻¹)
      have hr : 0 < r := by positivity
      have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
      rw [← hne (0, r) (by intro h; have h' : r = 0 := congrArg Prod.snd h; linarith),
        ← hne (r, 0) (by intro h; have h' : r = 0 := congrArg Prod.fst h; linarith)]
      unfold planarMode angTwo
      have hsq1 : Real.sqrt (0 ^ 2 + r ^ 2) = r := by simpa using Real.sqrt_sq hr.le
      have hsq2 : Real.sqrt (r ^ 2 + 0 ^ 2) = r := by simpa using Real.sqrt_sq hr.le
      rw [hsq1, hsq2]
      have hdiv1 : ((0 : ℝ) + (r : ℂ) * Complex.I) ^ 2 / ((0 ^ 2 + r ^ 2 : ℝ) : ℂ) = -1 := by
        rw [Complex.ofReal_zero, zero_add, mul_pow, Complex.I_sq]
        have hd : ((0 ^ 2 + r ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ 2 := by push_cast; ring
        rw [hd]
        field_simp [hrC]
      have hdiv2 : ((r : ℂ) + (0 : ℝ) * Complex.I) ^ 2 / ((r ^ 2 + 0 ^ 2 : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_zero, zero_mul, add_zero]
        have hd : ((r ^ 2 + 0 ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ 2 := by push_cast; ring
        rw [hd]
        exact div_self (pow_ne_zero 2 hrC)
      rw [hdiv1, hdiv2]
      ring
    have heq_neg : hermiteMode ℓ (0, 0) = -hermiteMode ℓ (0, 0) :=
      tendsto_nhds_unique ht2 (by rw [hneg]; exact ht1.neg)
    have hzero : hermiteMode ℓ (0, 0) = 0 := by
      apply Complex.ext
      · have hre := congrArg Complex.re heq_neg
        simp only [Complex.neg_re] at hre
        simp only [Complex.zero_re]
        linarith
      · have him := congrArg Complex.im heq_neg
        simp only [Complex.neg_im] at him
        simp only [Complex.zero_im]
        linarith
    exact hzero.symm
  · exact hne x hx

private theorem hermiteMode_pos_real (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    hermiteMode ℓ (r, 0) = hermiteProf ℓ r := by
  rw [← planarMode_hermiteProf_eq_hermiteMode]
  unfold planarMode angTwo
  have hsq : Real.sqrt (r ^ 2 + 0 ^ 2) = r := by
    simpa using Real.sqrt_sq hr.le
  rw [hsq]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp [sq, hrC]

private theorem hermiteProf_ae_oscBasis (ℓ : ℕ) :
    hermiteProf ℓ =ᵐ[UnforcedLeray.B0010.xGMeasure]
      ((UnforcedLeray.B0094.oscBasis ℓ : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
  have h1 := UnforcedLeray.B0121.toXG_φS ℓ
  unfold UnforcedLeray.B0121.toXG UnforcedLeray.B0121.φS at h1
  have h2 := (UnforcedLeray.B0094.memLp_schProf
    (UnforcedLeray.B0094.coreS (UnforcedLeray.B0121.lev ℓ))).coeFn_toLp
  rw [h1, UnforcedLeray.B0094.schProf_coreS] at h2
  exact h2.symm

private theorem norm_J_dop_sq_le_Aop (i : Fin 2) (φ : UnforcedLeray.B0121.S2) :
    ‖UnforcedLeray.B0121.J (UnforcedLeray.B0121.dop i φ)‖ ^ 2 ≤
      ‖UnforcedLeray.B0121.J (UnforcedLeray.B0121.Aop i φ)‖ ^ 2 := by
  open UnforcedLeray.B0121 in
  have hcomm : Bop i (Aop i φ) - Aop i (Bop i φ) = (2⁻¹ : ℂ) • φ := by
    rw [Bop_Aop]
    rw [Aop_apply i (Bop i φ), Bop_apply i φ, map_sub, map_smul, map_neg,
      map_sub, map_smul, map_neg, dop_X, crdL_ev_self]
    ext z
    simp only [add_apply, sub_apply, neg_apply, smul_apply, X_apply, smul_eq_mul,
      Complex.ofReal_one]
    ring
  have hA : ‖J (Aop i φ)‖ ^ 2 = (⟪J φ, J (Bop i (Aop i φ))⟫_ℂ).re := by
    rw [← inner_Aop, norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl
  have hB : ‖J (Bop i φ)‖ ^ 2 = (⟪J φ, J (Aop i (Bop i φ))⟫_ℂ).re := by
    have h1 : ⟪J (Bop i φ), J (Bop i φ)⟫_ℂ = ⟪J (Aop i (Bop i φ)), J φ⟫_ℂ :=
      (inner_Aop i (Bop i φ) φ).symm
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h1, inner_re_symm]
    rfl
  have hB_le : ‖J (Bop i φ)‖ ^ 2 ≤ ‖J (Aop i φ)‖ ^ 2 := by
    have hdiff : ‖J (Aop i φ)‖ ^ 2 - ‖J (Bop i φ)‖ ^ 2 = (2⁻¹ : ℝ) * ‖J φ‖ ^ 2 := by
      rw [hA, hB, ← Complex.sub_re, ← inner_sub_right, ← map_sub, hcomm, map_smul,
        inner_smul_right]
      have hre : ((2⁻¹ : ℂ) * ⟪J φ, J φ⟫_ℂ).re = (2⁻¹ : ℝ) * (⟪J φ, J φ⟫_ℂ).re := by
        simp [Complex.mul_re]
      have hsq_re : (⟪J φ, J φ⟫_ℂ).re = ‖J φ‖ ^ 2 :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) (J φ)).symm
      rw [hre, hsq_re]
    linarith [sq_nonneg ‖J φ‖]
  have hdop : dop i φ = (2⁻¹ : ℂ) • (Aop i φ - Bop i φ) := by
    rw [Aop_apply, Bop_apply]
    ext z
    simp only [sub_apply, neg_apply, smul_apply, smul_eq_mul]
    ring
  have htri : ‖J (dop i φ)‖ ≤ (2⁻¹ : ℝ) * (‖J (Aop i φ)‖ + ‖J (Bop i φ)‖) := by
    rw [hdop, map_smul, map_sub, norm_smul]
    have hn : ‖(2⁻¹ : ℂ)‖ = (2⁻¹ : ℝ) := by norm_num
    rw [hn]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
  nlinarith [norm_nonneg (J (dop i φ)), norm_nonneg (J (Aop i φ)), norm_nonneg (J (Bop i φ)),
    sq_nonneg (‖J (Aop i φ)‖ - ‖J (Bop i φ)‖)]

private theorem dop_comm_Aop_diff (ζ : UnforcedLeray.B0121.S2) :
    UnforcedLeray.B0121.Aop 0 (UnforcedLeray.B0121.dop 1 ζ) =
      UnforcedLeray.B0121.dop 1 (UnforcedLeray.B0121.Aop 0 ζ) := by
  open UnforcedLeray.B0121 in
  rw [Aop_apply, Aop_apply, map_sub, map_smul, dop_X, crdL_zero_ev_one, Complex.ofReal_zero,
    zero_smul, zero_add, dop_comm 0 1 ζ]

/-- Elementary 2D unit-square Sobolev `L^∞` estimate for Schwartz functions, with NO square roots
or cutoff functions. -/
private theorem schwartz_pointwise_le_Aop_sq (ζ : UnforcedLeray.B0121.S2) (z : ℝ × ℝ) :
    ‖ζ z‖ ≤ 2 + (1 / 2 : ℝ) *
      (‖UnforcedLeray.B0121.J ζ‖ ^ 2 +
        ‖UnforcedLeray.B0121.J (UnforcedLeray.B0121.Aop 0 ζ)‖ ^ 2 +
        ‖UnforcedLeray.B0121.J (UnforcedLeray.B0121.Aop 1 ζ)‖ ^ 2 +
        ‖UnforcedLeray.B0121.J (UnforcedLeray.B0121.Aop 1 (UnforcedLeray.B0121.Aop 0 ζ))‖ ^ 2) := by
  open UnforcedLeray.B0121 in
  have hζs : ContDiff ℝ ∞ ⇑ζ := ζ.smooth'
  have hd1s : ContDiff ℝ ∞ ⇑(dop 1 ζ) := (dop 1 ζ).smooth'
  set a₁ : ℝ := z.1 - 1
  set a₂ : ℝ := z.2 - 1
  let F : ℝ → ℂ := fun s => ((s - a₁ : ℝ) : ℂ) * ζ (s, z.2)
  let G : ℝ → ℝ → ℂ := fun s t =>
    ((t - a₂ : ℝ) : ℂ) * (ζ (s, t) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, t))
  let H : ℝ × ℝ → ℂ := fun p =>
    (ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 ζ p) +
      ((p.2 - a₂ : ℝ) : ℂ) * (dop 1 ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) p)
  have hF_deriv : ∀ s : ℝ, HasDerivAt F (ζ (s, z.2) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, z.2)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => ((u - a₁ : ℝ) : ℂ)) 1 s :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).sub_const a₁)
    have h2 : HasDerivAt (fun u : ℝ => ζ (u, z.2)) (dop 0 ζ (s, z.2)) s := by
      have hf := (ζ.hasFDerivAt (s, z.2)).comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s z.2))
      refine hf.congr_deriv ?_
      rw [dop_apply]
      rfl
    exact (h1.fun_mul h2).congr_deriv (by ring)
  have hG_deriv : ∀ s t : ℝ, HasDerivAt (G s) (H (s, t)) t := by
    intro s t
    have h1 : HasDerivAt (fun v : ℝ => ((v - a₂ : ℝ) : ℂ)) 1 t :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).sub_const a₂)
    have h2a : HasDerivAt (fun v : ℝ => ζ (s, v)) (dop 1 ζ (s, t)) t := by
      have hf := (ζ.hasFDerivAt (s, t)).comp_hasDerivAt t
        ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
      refine hf.congr_deriv ?_
      rw [dop_apply]
      rfl
    have h2b : HasDerivAt (fun v : ℝ => dop 0 ζ (s, v)) (dop 0 (dop 1 ζ) (s, t)) t := by
      have hf := ((dop 0 ζ).hasFDerivAt (s, t)).comp_hasDerivAt t
        ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
      refine hf.congr_deriv ?_
      rw [dop_comm 0 1 ζ, dop_apply]
      rfl
    have h2 : HasDerivAt (fun v : ℝ => ζ (s, v) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, v))
        (dop 1 ζ (s, t) + ((s - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) (s, t)) t :=
      h2a.add (h2b.const_mul _)
    exact (h1.fun_mul h2).congr_deriv (by dsimp [H]; ring)
  have hH_cont : Continuous H := by
    dsimp [H]
    fun_prop
  have hftc2 : ∀ s : ℝ, ζ (s, z.2) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, z.2) =
      ∫ t in a₂..z.2, H (s, t) := by
    intro s
    have hint : IntervalIntegrable (fun t => H (s, t)) volume a₂ z.2 :=
      (hH_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG_deriv s t) hint
    have hGa₂ : G s a₂ = 0 := by simp [G]
    have hGz₂ : G s z.2 = ζ (s, z.2) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, z.2) := by
      simp [G, a₂]
    rw [hGa₂, hGz₂, sub_zero] at h
    exact h.symm
  have hftc1 : ζ z = ∫ s in a₁..z.1, ∫ t in a₂..z.2, H (s, t) := by
    have hintF : IntervalIntegrable (fun s => ζ (s, z.2) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, z.2))
        volume a₁ z.1 := by
      have hc : Continuous (fun s => ζ (s, z.2) + ((s - a₁ : ℝ) : ℂ) * dop 0 ζ (s, z.2)) := by
        fun_prop
      exact hc.intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF_deriv s) hintF
    have hFa₁ : F a₁ = 0 := by simp [F]
    have hFz₁ : F z.1 = ζ z := by simp [F, a₁]
    rw [hFa₁, hFz₁, sub_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun s _ => hftc2 s
  let Q : Set (ℝ × ℝ) := Ioc a₁ z.1 ×ˢ Ioc a₂ z.2
  have ha₁_le : a₁ ≤ z.1 := by dsimp [a₁]; linarith
  have ha₂_le : a₂ ≤ z.2 := by dsimp [a₂]; linarith
  have hQ_meas : MeasurableSet Q := measurableSet_Ioc.prod measurableSet_Ioc
  have hQ_vol : volume.real Q = 1 := by
    dsimp [Q]
    rw [Measure.volume_eq_prod, measureReal_def, Measure.prod_prod, Real.volume_Ioc,
      Real.volume_Ioc]
    have h1 : z.1 - a₁ = 1 := by dsimp [a₁]; ring
    have h2 : z.2 - a₂ = 1 := by dsimp [a₂]; ring
    rw [h1, h2]
    simp
  have hQ_sub : Q ⊆ Icc a₁ z.1 ×ˢ Icc a₂ z.2 :=
    prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hQ_cpt : IsCompact (Icc a₁ z.1 ×ˢ Icc a₂ z.2) :=
    isCompact_Icc.prod isCompact_Icc
  have hiter : ∫ s in a₁..z.1, (∫ t in a₂..z.2, H (s, t)) = ∫ p in Q, H p := by
    rw [intervalIntegral.integral_of_le ha₁_le]
    have hinner : ∀ s, ∫ t in a₂..z.2, H (s, t) = ∫ t in Ioc a₂ z.2, H (s, t) :=
      fun _ => intervalIntegral.integral_of_le ha₂_le
    simp_rw [hinner]
    have hintQ : IntegrableOn H (Ioc a₁ z.1 ×ˢ Ioc a₂ z.2) :=
      (hH_cont.continuousOn.integrableOn_compact hQ_cpt).mono_set hQ_sub
    change (∫ s in Ioc a₁ z.1, ∫ t in Ioc a₂ z.2, H (s, t)) =
      ∫ p in Ioc a₁ z.1 ×ˢ Ioc a₂ z.2, H p
    rw [Measure.volume_eq_prod, setIntegral_prod _ hintQ]
  rw [hftc1, hiter]
  have hpt_Q : ∀ p ∈ Q, ‖H p‖ ≤
      (1 / 2 : ℝ) * 4 + (1 / 2 : ℝ) *
        (‖ζ p‖ ^ 2 + ‖dop 0 ζ p‖ ^ 2 + ‖dop 1 ζ p‖ ^ 2 + ‖dop 0 (dop 1 ζ) p‖ ^ 2) := by
    intro p ⟨hp1, hp2⟩
    have hs1 : ‖((p.1 - a₁ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hp1.1])]
      dsimp [a₁]; linarith [hp1.2]
    have ht1 : ‖((p.2 - a₂ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hp2.1])]
      dsimp [a₂]; linarith [hp2.2]
    have htri1 : ‖H p‖ ≤ ‖ζ p‖ + ‖dop 0 ζ p‖ + ‖dop 1 ζ p‖ + ‖dop 0 (dop 1 ζ) p‖ := by
      dsimp [H]
      have b1 := norm_add_le (ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 ζ p)
        (((p.2 - a₂ : ℝ) : ℂ) * (dop 1 ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) p))
      have b2 := norm_add_le (ζ p) (((p.1 - a₁ : ℝ) : ℂ) * dop 0 ζ p)
      have b3 := norm_add_le (dop 1 ζ p) (((p.1 - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) p)
      rw [norm_mul] at b1 b2 b3
      have m1 : ‖((p.1 - a₁ : ℝ) : ℂ)‖ * ‖dop 0 ζ p‖ ≤ 1 * ‖dop 0 ζ p‖ :=
        mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      have m2 : ‖((p.1 - a₁ : ℝ) : ℂ)‖ * ‖dop 0 (dop 1 ζ) p‖ ≤ 1 * ‖dop 0 (dop 1 ζ) p‖ :=
        mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      have m3 : ‖((p.2 - a₂ : ℝ) : ℂ)‖ *
          ‖dop 1 ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) p‖ ≤
          1 * (‖dop 1 ζ p‖ + ‖dop 0 (dop 1 ζ) p‖) := by
        calc ‖((p.2 - a₂ : ℝ) : ℂ)‖ *
              ‖dop 1 ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) p‖
            ≤ 1 * ‖dop 1 ζ p + ((p.1 - a₁ : ℝ) : ℂ) * dop 0 (dop 1 ζ) p‖ :=
              mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
          _ ≤ 1 * (‖dop 1 ζ p‖ + ‖dop 0 (dop 1 ζ) p‖) := by linarith
      linarith
    nlinarith [sq_nonneg (‖ζ p‖ - 1), sq_nonneg (‖dop 0 ζ p‖ - 1),
      sq_nonneg (‖dop 1 ζ p‖ - 1), sq_nonneg (‖dop 0 (dop 1 ζ) p‖ - 1)]
  have hL2_le : ∀ ψ : S2, ∫ p in Q, ‖ψ p‖ ^ 2 ≤ ‖J ψ‖ ^ 2 := by
    intro ψ
    have hint : Integrable (fun p => ‖ψ p‖ ^ 2) volume := by
      have h := (Lp.memLp (J ψ)).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
      refine h.congr ?_
      filter_upwards [ψ.coeFn_toLp 2 volume] with p hp
      simp [J, hp]
    have hwhole : ∫ p, ‖ψ p‖ ^ 2 = ‖J ψ‖ ^ 2 := by
      have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (J ψ)
      rw [h1, inner_J, UnforcedLeray.B0094.pairS]
      change _ = (∫ p, conj (ψ p) * ψ p).re
      rw [← BSAux.integral_re' (UnforcedLeray.B0094.integrable_conj_mul ψ ψ)]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      dsimp only
      rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [← hwhole]
    exact setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)
  let maj : ℝ × ℝ → ℝ := fun p =>
    2 + (1 / 2 : ℝ) * (‖ζ p‖ ^ 2 + ‖dop 0 ζ p‖ ^ 2 + ‖dop 1 ζ p‖ ^ 2 + ‖dop 0 (dop 1 ζ) p‖ ^ 2)
  have hmaj_int : IntegrableOn maj Q := by
    have hcont : Continuous maj := by dsimp [maj]; fun_prop
    exact (hcont.continuousOn.integrableOn_compact hQ_cpt).mono_set hQ_sub
  have hint_norm : ‖∫ p in Q, H p‖ ≤ ∫ p in Q, maj p := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on ?_ hmaj_int hQ_meas fun p hp => ?_
    · exact ((hH_cont.continuousOn.integrableOn_compact hQ_cpt).mono_set hQ_sub).norm
    · dsimp [maj]; linarith [hpt_Q p hp]
  have hsplit : ∫ p in Q, maj p ≤
      2 + (1 / 2 : ℝ) * (‖J ζ‖ ^ 2 + ‖J (dop 0 ζ)‖ ^ 2 + ‖J (dop 1 ζ)‖ ^ 2 +
        ‖J (dop 0 (dop 1 ζ))‖ ^ 2) := by
    have ic : IntegrableOn (fun _ : ℝ × ℝ => (2 : ℝ)) Q :=
      (continuous_const.continuousOn.integrableOn_compact hQ_cpt).mono_set hQ_sub
    have i0 : IntegrableOn (fun p => ‖ζ p‖ ^ 2) Q :=
      ((ζ.smooth'.continuous.norm.pow 2).continuousOn.integrableOn_compact hQ_cpt).mono_set hQ_sub
    have i1 : IntegrableOn (fun p => ‖dop 0 ζ p‖ ^ 2) Q :=
      (((dop 0 ζ).smooth'.continuous.norm.pow 2).continuousOn.integrableOn_compact
        hQ_cpt).mono_set hQ_sub
    have i2 : IntegrableOn (fun p => ‖dop 1 ζ p‖ ^ 2) Q :=
      (((dop 1 ζ).smooth'.continuous.norm.pow 2).continuousOn.integrableOn_compact
        hQ_cpt).mono_set hQ_sub
    have i3 : IntegrableOn (fun p => ‖dop 0 (dop 1 ζ) p‖ ^ 2) Q :=
      (((dop 0 (dop 1 ζ)).smooth'.continuous.norm.pow 2).continuousOn.integrableOn_compact
        hQ_cpt).mono_set hQ_sub
    have hmaj_eq : ∫ p in Q, maj p =
        (∫ _p in Q, (2 : ℝ)) + (1 / 2 : ℝ) *
          ((((∫ p in Q, ‖ζ p‖ ^ 2) + (∫ p in Q, ‖dop 0 ζ p‖ ^ 2)) +
            (∫ p in Q, ‖dop 1 ζ p‖ ^ 2)) + (∫ p in Q, ‖dop 0 (dop 1 ζ) p‖ ^ 2)) := by
      have s01 := integral_add (μ := volume.restrict Q) i0 i1
      have s012 := integral_add (μ := volume.restrict Q) (i0.add i1) i2
      have s0123 := integral_add (μ := volume.restrict Q) ((i0.add i1).add i2) i3
      have smul := integral_const_mul (μ := volume.restrict Q) (1 / 2 : ℝ)
        (fun p => ‖ζ p‖ ^ 2 + ‖dop 0 ζ p‖ ^ 2 + ‖dop 1 ζ p‖ ^ 2 + ‖dop 0 (dop 1 ζ) p‖ ^ 2)
      have sadd := integral_add (μ := volume.restrict Q) ic
        ((((i0.add i1).add i2).add i3).const_mul (1 / 2))
      simp only [Pi.add_apply] at s012 s0123 sadd
      dsimp [maj]
      rw [sadd, smul, s0123, s012, s01]
    rw [hmaj_eq, setIntegral_const, hQ_vol, smul_eq_mul, one_mul]
    have b0 := hL2_le ζ
    have b1 := hL2_le (dop 0 ζ)
    have b2 := hL2_le (dop 1 ζ)
    have b3 := hL2_le (dop 0 (dop 1 ζ))
    linarith
  have hd0 := norm_J_dop_sq_le_Aop 0 ζ
  have hd1 := norm_J_dop_sq_le_Aop 1 ζ
  have hd01 : ‖J (dop 0 (dop 1 ζ))‖ ^ 2 ≤ ‖J (Aop 1 (Aop 0 ζ))‖ ^ 2 := by
    calc ‖J (dop 0 (dop 1 ζ))‖ ^ 2
        ≤ ‖J (Aop 0 (dop 1 ζ))‖ ^ 2 := norm_J_dop_sq_le_Aop 0 (dop 1 ζ)
      _ = ‖J (dop 1 (Aop 0 ζ))‖ ^ 2 := by rw [dop_comm_Aop_diff]
      _ ≤ ‖J (Aop 1 (Aop 0 ζ))‖ ^ 2 := norm_J_dop_sq_le_Aop 1 (Aop 0 ζ)
  linarith

private noncomputable def dopW : (k : ℕ) → (Fin k → Fin 2) →
    (UnforcedLeray.B0121.S2 →L[ℂ] UnforcedLeray.B0121.S2)
  | 0, _ => ContinuousLinearMap.id ℂ UnforcedLeray.B0121.S2
  | k + 1, w => (UnforcedLeray.B0121.dop (w 0)).comp (dopW k (Fin.tail w))

private theorem dopW_gS (k : ℕ) (w : Fin k → Fin 2) (ψ : UnforcedLeray.B0121.S2) :
    dopW k w (UnforcedLeray.B0121.gS ψ) = UnforcedLeray.B0121.gS (UnforcedLeray.B0121.Aw k w ψ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dopW, ContinuousLinearMap.comp_apply, ih, UnforcedLeray.B0121.dop_gS,
      UnforcedLeray.B0121.Aw_succ]

private theorem iteratedFDeriv_schwartz_eq_sum (k : ℕ) (φ : UnforcedLeray.B0121.S2)
    (z : ℝ × ℝ) (m : Fin k → ℝ × ℝ) :
    iteratedFDeriv ℝ k (⇑φ) z m =
      ∑ w : Fin k → Fin 2,
        ((∏ j : Fin k, UnforcedLeray.B0121.crdL (w j) (m j) : ℝ) : ℂ) * dopW k w φ z := by
  induction k generalizing z with
  | zero =>
    rw [iteratedFDeriv_zero_apply, Fintype.sum_subsingleton _ Fin.elim0]
    simp [dopW]
  | succ k ih =>
    rw [iteratedFDeriv_succ_apply_left]
    let evTail : ((ℝ × ℝ) [×k]→L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × ℝ) ℂ (Fin.tail m)
    have hev : ((fderiv ℝ (iteratedFDeriv ℝ k ⇑φ) z) (m 0)) (Fin.tail m) =
        fderiv ℝ (fun y => iteratedFDeriv ℝ k (⇑φ) y (Fin.tail m)) z (m 0) := by
      have hdiff_it : DifferentiableAt ℝ (iteratedFDeriv ℝ k ⇑φ) z :=
        (((φ.smooth' : ContDiff ℝ ∞ ⇑φ).iteratedFDeriv_right (m := ∞)
          (by exact_mod_cast le_top)).differentiable (by simp)) z
      have hcomp := (evTail.hasFDerivAt.comp z hdiff_it.hasFDerivAt).fderiv
      exact (congrArg (fun L => L (m 0)) hcomp).symm
    have hfun : (fun y => iteratedFDeriv ℝ k (⇑φ) y (Fin.tail m)) =
        fun y => ∑ w' : Fin k → Fin 2,
          ((∏ j : Fin k, UnforcedLeray.B0121.crdL (w' j) (Fin.tail m j) : ℝ) : ℂ) *
            dopW k w' φ y := by
      funext y
      exact ih y (Fin.tail m)
    rw [hev, hfun]
    have hdiff : ∀ w' : Fin k → Fin 2,
        HasFDerivAt (fun y =>
          ((∏ j : Fin k, UnforcedLeray.B0121.crdL (w' j) (Fin.tail m j) : ℝ) : ℂ) *
            dopW k w' φ y)
          (((∏ j : Fin k, UnforcedLeray.B0121.crdL (w' j) (Fin.tail m j) : ℝ) : ℂ) •
            fderiv ℝ (⇑(dopW k w' φ)) z) z := by
      intro w'
      exact ((dopW k w' φ).hasFDerivAt z).const_mul _
    rw [(HasFDerivAt.fun_sum fun w' _ => hdiff w').fderiv, FunLike.coe_sum,
      Finset.sum_apply, UnforcedLeray.B0121.sum_words_succ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [FunLike.coe_smul, Pi.smul_apply]
    have hm0 : m 0 = UnforcedLeray.B0121.crdL 0 (m 0) • UnforcedLeray.B0121.ev 0 +
        UnforcedLeray.B0121.crdL 1 (m 0) • UnforcedLeray.B0121.ev 1 := by
      ext <;> simp [UnforcedLeray.B0121.crdL, UnforcedLeray.B0121.ev,
        UnforcedLeray.B0094.e1, UnforcedLeray.B0094.e2]
    conv_lhs => rw [hm0]
    rw [map_add, map_smul, map_smul, Fin.sum_univ_two]
    simp only [dopW, ContinuousLinearMap.comp_apply, UnforcedLeray.B0121.dop_apply,
      Fin.cons_zero, Fin.cons_succ, Fin.tail_cons, Fin.tail, Fin.prod_univ_succ,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring

private theorem norm_iteratedFDeriv_gS_le (k : ℕ) (ψ : UnforcedLeray.B0121.S2) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (⇑(UnforcedLeray.B0121.gS ψ)) z‖ ≤
      ∑ w : Fin k → Fin 2, ‖UnforcedLeray.B0121.gS (UnforcedLeray.B0121.Aw k w ψ) z‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m => ?_
  rw [iteratedFDeriv_schwartz_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [dopW_gS, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_
  rcases w j with ⟨_ | _ | _, hn⟩
  · simpa [UnforcedLeray.B0121.crdL] using norm_fst_le (m j)
  · simpa [UnforcedLeray.B0121.crdL] using norm_snd_le (m j)
  · omega

private theorem norm_iteratedFDeriv_hermiteMode_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ k (hermiteMode ℓ) z‖ ≤
        C * (1 + (ℓ : ℝ)) ^ (k + 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
  open UnforcedLeray.B0121 in
  set C₀ : ℝ := (2 : ℝ) ^ k *
      (2 + Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * 4))
  have hC₀_pos : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, hC₀_pos, fun ℓ z => ?_⟩
  have hchi : chi ({ℓ} : Finset ℕ) (fun _ => 1) = φS ℓ := by simp [chi]
  have hAw_norm : ∀ (m : ℕ) (hm : m ≤ k + 2) (u : Fin m → Fin 2),
      ‖J (Aw m u (φS ℓ))‖ ^ 2 ≤
        2 * Real.pi * (2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * (1 + (ℓ : ℝ)) ^ (k + 2) := by
    intro m hm u
    have h1 := norm_J_Aw_chi_le m u ({ℓ} : Finset ℕ) (fun _ => 1)
    rw [hchi] at h1
    simp only [Finset.sum_singleton, norm_one, one_pow, mul_one] at h1
    have h2 := qpoly_le hm ℓ
    have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc ‖J (Aw m u (φS ℓ))‖ ^ 2
        ≤ 2 * Real.pi * qpoly m (2 + ℓ) := h1
      _ ≤ 2 * Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * (1 + (ℓ : ℝ)) ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left h2 h2pi
      _ = 2 * Real.pi * (2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * (1 + (ℓ : ℝ)) ^ (k + 2) := by ring
  have hword_pt : ∀ w : Fin k → Fin 2,
      ‖gS (Aw k w (φS ℓ)) z‖ ≤
        (2 + Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * 4)) *
          (1 + (ℓ : ℝ)) ^ (k + 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro w
    rw [gS_apply, norm_mul, sqGc, Complex.norm_real, Real.norm_of_nonneg (sqG_pos z).le]
    have hsup := schwartz_pointwise_le_Aop_sq (Aw k w (φS ℓ)) z
    have h0 := hAw_norm k (by omega) w
    have h1 : ‖J (Aop 0 (Aw k w (φS ℓ)))‖ ^ 2 ≤
        2 * Real.pi * (2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * (1 + (ℓ : ℝ)) ^ (k + 2) := by
      have heq : Aop 0 (Aw k w (φS ℓ)) = Aw (k + 1) (Fin.cons 0 w) (φS ℓ) := by
        simp [Aw_succ]
      rw [heq]
      exact hAw_norm (k + 1) (by omega) _
    have h2 : ‖J (Aop 1 (Aw k w (φS ℓ)))‖ ^ 2 ≤
        2 * Real.pi * (2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * (1 + (ℓ : ℝ)) ^ (k + 2) := by
      have heq : Aop 1 (Aw k w (φS ℓ)) = Aw (k + 1) (Fin.cons 1 w) (φS ℓ) := by
        simp [Aw_succ]
      rw [heq]
      exact hAw_norm (k + 1) (by omega) _
    have h3 : ‖J (Aop 1 (Aop 0 (Aw k w (φS ℓ))))‖ ^ 2 ≤
        2 * Real.pi * (2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * (1 + (ℓ : ℝ)) ^ (k + 2) := by
      have heq : Aop 1 (Aop 0 (Aw k w (φS ℓ))) =
          Aw (k + 2) (Fin.cons 1 (Fin.cons 0 w)) (φS ℓ) := by
        simp [Aw_succ]
      rw [heq]
      exact hAw_norm (k + 2) le_rfl _
    have h1_le : (1 : ℝ) ≤ (1 + (ℓ : ℝ)) ^ (k + 2) :=
      one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg ℓ))
    have hzeta : ‖Aw k w (φS ℓ) z‖ ≤
        (2 + Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * 4)) * (1 + (ℓ : ℝ)) ^ (k + 2) := by
      nlinarith
    calc sqG z * ‖Aw k w (φS ℓ) z‖
        ≤ Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) *
            ((2 + Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * 4)) *
              (1 + (ℓ : ℝ)) ^ (k + 2)) :=
          mul_le_mul (sqG_le_exp_div_eight z) hzeta (norm_nonneg _) (Real.exp_nonneg _)
      _ = (2 + Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * 4)) *
            (1 + (ℓ : ℝ)) ^ (k + 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by ring
  have hsum := norm_iteratedFDeriv_gS_le k (φS ℓ) z
  refine hsum.trans ?_
  calc ∑ w : Fin k → Fin 2, ‖gS (Aw k w (φS ℓ)) z‖
      ≤ ∑ _w : Fin k → Fin 2,
          (2 + Real.pi * ((2 + ((k + 2 : ℕ) : ℝ)) ^ (k + 2) * 4)) *
            (1 + (ℓ : ℝ)) ^ (k + 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) :=
        Finset.sum_le_sum fun w _ => hword_pt w
    _ = C₀ * (1 + (ℓ : ℝ)) ^ (k + 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
        simp [C₀, mul_assoc]

private theorem movD_gS_eq_oscL (φ : UnforcedLeray.B0121.S2) (z : ℝ × ℝ) :
    movD (⇑(UnforcedLeray.B0121.gS φ)) z =
      UnforcedLeray.B0121.gS (UnforcedLeray.B0121.oscL φ) z := by
  open UnforcedLeray.B0121 in
  have hpd : ∀ (i : Fin 2) (ψ : S2) (y : ℝ × ℝ), pdCx i (⇑ψ) y = dop i ψ y := by
    intro i ψ y
    fin_cases i <;> rfl
  have hpd2 : ∀ (i : Fin 2) (ψ : S2) (y : ℝ × ℝ),
      pdCx i (pdCx i (⇑ψ)) y = dop i (dop i ψ) y := by
    intro i ψ y
    have hfn : pdCx i (⇑ψ) = ⇑(dop i ψ) := funext (hpd i ψ)
    rw [hfn, hpd i (dop i ψ) y]
  unfold movD ladLapCx
  rw [hpd2 0 (gS φ) z, hpd2 1 (gS φ) z, hpd 0 (gS φ) z, hpd 1 (gS φ) z,
    dop_gS, dop_gS, dop_gS, dop_gS]
  have halg : Aop 0 (Aop 0 φ) + Aop 1 (Aop 1 φ) +
      (2⁻¹ : ℂ) • (X 0 (Aop 0 φ) + X 1 (Aop 1 φ)) + (2 : ℂ) • φ = oscL φ := by
    simp only [Aop_apply, oscL_apply, map_sub, map_smul, dop_X, crdL_ev_self,
      Complex.ofReal_one, one_smul]
    ext y
    simp only [add_apply, sub_apply, smul_apply, X_apply, smul_eq_mul]
    ring
  rw [← halg]
  simp only [map_add, map_smul, add_apply, smul_apply, gS_apply,
    X_apply, crdC, crdL, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

private theorem movD_hermiteMode_eq (ℓ : ℕ) (z : ℝ × ℝ) :
    movD (hermiteMode ℓ) z = -(ℓ : ℂ) * hermiteMode ℓ z := by
  unfold hermiteMode
  rw [movD_gS_eq_oscL, UnforcedLeray.B0121.oscL_φS, map_smul, smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem oscillatorD_hermiteProf_eq (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    oscillatorD (hermiteProf ℓ) r = -(ℓ : ℂ) * hermiteProf ℓ r := by
  unfold hermiteProf
  rw [UnforcedLeray.Short.Spine.oscProfOde_proof _ r hr]
  have hcore := UnforcedLeray.B0094.coreS_lag (UnforcedLeray.B0121.lev ℓ)
  have hosc := UnforcedLeray.B0121.oscL_φS ℓ
  rw [UnforcedLeray.B0121.oscL_eq, UnforcedLeray.B0121.φS, ← hcore] at hosc
  have h1 : UnforcedLeray.B0094.profFun (UnforcedLeray.B0094.lag (UnforcedLeray.B0121.lev ℓ)) r =
      UnforcedLeray.B0094.schProf
        (⇑(UnforcedLeray.B0094.coreS (UnforcedLeray.B0094.lag (UnforcedLeray.B0121.lev ℓ)))) r :=
    (congrFun (UnforcedLeray.B0094.schProf_coreS _) r).symm
  have hsmul : ∀ (c : ℂ) (ψ : UnforcedLeray.B0121.S2),
      UnforcedLeray.B0094.schProf (⇑(c • ψ)) r = c * UnforcedLeray.B0094.schProf (⇑ψ) r :=
    fun c ψ => by simp only [UnforcedLeray.B0094.schProf, smul_apply, smul_eq_mul]; ring
  rw [h1, hosc, hsmul, congrFun (UnforcedLeray.B0094.schProf_coreS _) r]
  push_cast
  ring

/-! ## 3. Canonical planar mode series, smoothness, `Good` bounds, and planar operator identities -/

private noncomputable def canonMode (P : PlanarData) (θ : ℝ) (y : ℝ × ℝ) : ℂ :=
  planarMode (P.canonical θ) y

private noncomputable def cCoef (V : ℝ → UnforcedLeray.B0010.XG) (ℓ : ℕ) (θ : ℝ) : ℂ :=
  inner ℂ (UnforcedLeray.B0094.oscBasis ℓ) (V θ)

private theorem cCoef_rapid_decay {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (k q : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ M : ℝ, 0 < M ∧
      Summable (fun ℓ : ℕ => M * (1 + (ℓ : ℝ)) ^ q / (1 + (ℓ : ℝ)) ^ (q + 2)) ∧
      ∀ (ℓ : ℕ) (θ : ℝ), θ ∈ Icc a b →
        ‖iteratedDeriv k (cCoef V ℓ) θ‖ * (1 + (ℓ : ℝ)) ^ q ≤ M / (1 + (ℓ : ℝ)) ^ 2 := by
  obtain ⟨_, hbd⟩ := UnforcedLeray.Short.Spine.coefficientBounds_proof V hSmoothAll
  obtain ⟨C, hC⟩ := hbd k (2 * q + 4) a b ha hab
  set M : ℝ := max C 0 + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hsum_inv : Summable (fun ℓ : ℕ => M / (1 + (ℓ : ℝ)) ^ 2) := by
    have h1 : Summable (fun ℓ : ℕ => (1 : ℝ) / ((ℓ + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
    refine (h1.mul_left M).congr fun ℓ => ?_
    push_cast
    ring
  refine ⟨M, hM_pos, ?_, fun ℓ θ hθ => ?_⟩
  · refine hsum_inv.congr fun ℓ => ?_
    have hpos : (0 : ℝ) < 1 + (ℓ : ℝ) := by positivity
    rw [pow_add]
    field_simp [hpos.ne']
  · obtain ⟨hsum_θ, hle_C⟩ := hC θ hθ
    have hterm : (1 + (ℓ : ℝ)) ^ (2 * q + 4) * ‖iteratedDeriv k (cCoef V ℓ) θ‖ ^ 2 ≤ C := by
      refine le_trans ?_ hle_C
      exact hsum_θ.le_tsum ℓ fun m _ => by positivity
    have hsq_M : ((1 + (ℓ : ℝ)) ^ (q + 2) * ‖iteratedDeriv k (cCoef V ℓ) θ‖) ^ 2 ≤ M ^ 2 := by
      have heq : ((1 + (ℓ : ℝ)) ^ (q + 2) * ‖iteratedDeriv k (cCoef V ℓ) θ‖) ^ 2 =
          (1 + (ℓ : ℝ)) ^ (2 * q + 4) * ‖iteratedDeriv k (cCoef V ℓ) θ‖ ^ 2 := by ring
      rw [heq]
      have hCM : C ≤ M := by dsimp [M]; linarith [le_max_left C 0]
      have hM1 : 1 ≤ M := by dsimp [M]; linarith [le_max_right C 0]
      nlinarith
    have hlin : (1 + (ℓ : ℝ)) ^ (q + 2) * ‖iteratedDeriv k (cCoef V ℓ) θ‖ ≤ M := by
      rw [sq, sq] at hsq_M
      exact nonneg_le_nonneg_of_sq_le_sq hM_pos.le hsq_M
    have hpos2 : 0 < (1 + (ℓ : ℝ)) ^ 2 := by positivity
    rw [le_div_iff₀ hpos2]
    calc ‖iteratedDeriv k (cCoef V ℓ) θ‖ * (1 + (ℓ : ℝ)) ^ q * (1 + (ℓ : ℝ)) ^ 2
        = (1 + (ℓ : ℝ)) ^ (q + 2) * ‖iteratedDeriv k (cCoef V ℓ) θ‖ := by ring
      _ ≤ M := hlin

private theorem canonMode_eq_tsum_hermiteMode {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {θ : ℝ} (hθ : 0 < θ) (y : ℝ × ℝ) :
    canonMode P θ y = ∑' ℓ : ℕ, cCoef V ℓ θ * hermiteMode ℓ y := by
  obtain ⟨C₀, _, hmode0⟩ := norm_iteratedFDeriv_hermiteMode_le 0
  have hmode_pt : ∀ (ℓ : ℕ) (z : ℝ × ℝ),
      ‖hermiteMode ℓ z‖ ≤ C₀ * (1 + (ℓ : ℝ)) ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
    intro ℓ z
    simpa [norm_iteratedFDeriv_zero] using hmode0 ℓ z
  have hprof_bd : ∀ a b : ℝ, 0 < a → a < b →
      ∃ C : ℝ, ∃ q : ℕ, ∀ n : ℕ, ∀ r ∈ Icc a b, ‖hermiteProf n r‖ ≤ C * (1 + (n : ℝ)) ^ q := by
    intro a b ha _
    refine ⟨C₀, 2, fun n r hr => ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    rw [← hermiteMode_pos_real n hr0]
    have hexp : Real.exp (-((r : ℝ) ^ 2 + 0 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
    calc ‖hermiteMode n (r, 0)‖
        ≤ C₀ * (1 + (n : ℝ)) ^ 2 * Real.exp (-((r : ℝ) ^ 2 + 0 ^ 2) / 8) := hmode_pt n (r, 0)
      _ ≤ C₀ * (1 + (n : ℝ)) ^ 2 * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C₀ * (1 + (n : ℝ)) ^ 2 := mul_one _
  have hV_mem : ∀ j : ℕ, V θ ∈ UnforcedLeray.B0123.XGj j := by
    intro j
    obtain ⟨U, hU, -⟩ := hSmoothAll j
    exact (hU θ hθ).choose
  have hae_ser := UnforcedLeray.Short.Spine.seriesIdentify_proof hermiteProf (V θ)
    hermiteProf_ae_oscBasis hprof_bd hV_mem
  obtain ⟨M, _, _, hM⟩ := cCoef_rapid_decay hSmoothAll 0 2 (a := θ / 2) (b := θ + 1)
    (by linarith) (by linarith)
  have hθ_mem : θ ∈ Icc (θ / 2) (θ + 1) := ⟨by linarith, by linarith⟩
  have hsum_2d : Summable (fun ℓ : ℕ => C₀ * M / (1 + (ℓ : ℝ)) ^ 2) := by
    have h1 : Summable (fun ℓ : ℕ => (1 : ℝ) / ((ℓ + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
    refine (h1.mul_left (C₀ * M)).congr fun ℓ => ?_
    push_cast; ring
  have hterm_le : ∀ (ℓ : ℕ) (z : ℝ × ℝ),
      ‖cCoef V ℓ θ * hermiteMode ℓ z‖ ≤ C₀ * M / (1 + (ℓ : ℝ)) ^ 2 := by
    intro ℓ z
    rw [norm_mul]
    have hc_le : ‖cCoef V ℓ θ‖ * (1 + (ℓ : ℝ)) ^ 2 ≤ M / (1 + (ℓ : ℝ)) ^ 2 := by
      simpa [iteratedDeriv_zero] using hM ℓ θ hθ_mem
    have hexp : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
    calc ‖cCoef V ℓ θ‖ * ‖hermiteMode ℓ z‖
        ≤ ‖cCoef V ℓ θ‖ * (C₀ * (1 + (ℓ : ℝ)) ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left ((hmode_pt ℓ z).trans
            (mul_le_mul_of_nonneg_left hexp (by positivity))) (norm_nonneg _)
      _ = C₀ * (‖cCoef V ℓ θ‖ * (1 + (ℓ : ℝ)) ^ 2) := by ring
      _ ≤ C₀ * (M / (1 + (ℓ : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left hc_le (by positivity)
      _ = C₀ * M / (1 + (ℓ : ℝ)) ^ 2 := by ring
  have hcont_2d : Continuous (fun z : ℝ × ℝ => ∑' ℓ : ℕ, cCoef V ℓ θ * hermiteMode ℓ z) :=
    continuous_tsum (fun ℓ => continuous_const.mul (UnforcedLeray.B0121.gS _).smooth'.continuous)
      hsum_2d hterm_le
  have hcont_prof_ser : ContinuousOn (fun r : ℝ => ∑' ℓ : ℕ, cCoef V ℓ θ * hermiteProf ℓ r)
      (Ioi 0) := by
    have hc : ContinuousOn (fun r : ℝ => ∑' ℓ : ℕ, cCoef V ℓ θ * hermiteMode ℓ (r, 0)) (Ioi 0) :=
      (hcont_2d.comp (continuous_id.prodMk continuous_const)).continuousOn
    refine hc.congr fun r hr => tsum_congr fun ℓ => ?_
    rw [hermiteMode_pos_real ℓ hr]
  have hcont_P : ContinuousOn (P.canonical θ) (Ioi 0) :=
    hP.canonical.smooth.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      fun r hr => ⟨hθ, hr⟩
  have heq_prof : EqOn (P.canonical θ) (fun r : ℝ => ∑' ℓ : ℕ, cCoef V ℓ θ * hermiteProf ℓ r)
      (Ioi 0) :=
    UnforcedLeray.Short.Spine.aeEqOfContinuousOn_proof _ _ hcont_P hcont_prof_ser
      ((hVae θ hθ).trans hae_ser.symm)
  unfold canonMode
  by_cases hy : y = 0
  · subst hy
    have hp0 : planarMode (P.canonical θ) 0 = 0 := by simp [planarMode, angTwo]
    have hm0 : ∀ ℓ : ℕ, hermiteMode ℓ 0 = 0 := by
      intro ℓ
      rw [← planarMode_hermiteProf_eq_hermiteMode]
      simp [planarMode, angTwo]
    simp [hp0, hm0]
  · have hr_pos : 0 < Real.sqrt (y.1 ^ 2 + y.2 ^ 2) := by
      refine Real.sqrt_pos.2 ?_
      by_contra hle
      apply hy
      apply Prod.ext <;> dsimp <;> nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    unfold planarMode
    rw [heq_prof hr_pos, ← tsum_mul_right]
    refine tsum_congr fun ℓ => ?_
    rw [mul_assoc, ← planarMode_hermiteProf_eq_hermiteMode ℓ y]
    rfl

private theorem norm_iteratedFDeriv_slice_le {G : ℝ × (ℝ × ℝ) → ℂ} (hG : ContDiff ℝ ∞ G)
    (m : ℕ) (θ : ℝ) (y : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ m (fun z => G (θ, z)) y‖ ≤ ‖iteratedFDeriv ℝ m G (θ, y)‖ := by
  have hinr_norm : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v => ?_
  let H : ℝ × (ℝ × ℝ) → ℂ := fun p => G ((θ, (0 : ℝ × ℝ)) + p)
  have hH : ContDiff ℝ ∞ H := hG.comp (contDiff_const.add contDiff_id)
  have hfn : (fun z : ℝ × ℝ => G (θ, z)) = H ∘ ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) := by
    funext z; simp [H]
  have hcomp : iteratedFDeriv ℝ m (fun z => G (θ, z)) y =
      (iteratedFDeriv ℝ m G (θ, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    rw [hfn, ContinuousLinearMap.iteratedFDeriv_comp_right _ hH y (by exact_mod_cast le_top)]
    congr 1
    dsimp [H]
    rw [iteratedFDeriv_comp_add_left]
    simp
  rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ((iteratedFDeriv ℝ m G (θ, y)).le_opNorm _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
    ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).le_opNorm (v i)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hinr_norm)

private theorem norm_iteratedFDeriv_timeDeriv_slice_le {G : ℝ × (ℝ × ℝ) → ℂ}
    (hG : ContDiff ℝ ∞ G) (m : ℕ) (θ : ℝ) (y : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ m (fun z => deriv (fun t => G (t, z)) θ) y‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) G (θ, y)‖ := by
  let eval10 : (ℝ × (ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousLinearMap.apply ℝ ℂ (1, (0 : ℝ × ℝ))
  have heval_norm : ‖eval10‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => by
      simpa [eval10, one_mul] using L.le_opNorm (1, (0 : ℝ × ℝ))
  have hdt_eq : (fun z : ℝ × ℝ => deriv (fun t => G (t, z)) θ) =
      fun z : ℝ × ℝ => (⇑eval10 ∘ fderiv ℝ G) (θ, z) := by
    funext z
    have hd : HasDerivAt (fun t : ℝ => G (t, z)) (fderiv ℝ G (θ, z) (1, (0 : ℝ × ℝ))) θ :=
      (hG.differentiable (by simp) (θ, z)).hasFDerivAt.comp_hasDerivAt θ
        ((hasDerivAt_id θ).prodMk (hasDerivAt_const θ z))
    exact hd.deriv
  have hG1_sm : ContDiff ℝ ∞ (⇑eval10 ∘ fderiv ℝ G) :=
    eval10.contDiff.comp (hG.fderiv_right (m := ∞) (by simp))
  rw [hdt_eq]
  refine (norm_iteratedFDeriv_slice_le hG1_sm m θ y).trans ?_
  rw [eval10.iteratedFDeriv_comp_left
    ((hG.fderiv_right (m := ∞) (by simp)).contDiffAt) (by exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc ‖eval10‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ G) (θ, y)‖
      ≤ 1 * ‖iteratedFDeriv ℝ m (fderiv ℝ G) (θ, y)‖ :=
        mul_le_mul_of_nonneg_right heval_norm (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (m + 1) G (θ, y)‖ := by
        rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- Cut-off global series on `ℝ × (ℝ × ℝ)` agreeing with `canonMode P` on `[θ₁, θ₂] ×ˢ univ`. -/
private theorem canonMode_window_jet_and_smooth {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (h12 : θ₁ ≤ θ₂) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => canonMode P p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      (∀ (m : ℕ), ∃ B : ℝ, 0 < B ∧ ∀ θ ∈ Icc θ₁ θ₂, ∀ y : ℝ × ℝ,
        ‖iteratedFDeriv ℝ m (canonMode P θ) y‖ ≤
          B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ∧
        ‖iteratedFDeriv ℝ m (fun z => deriv (fun t => canonMode P t z) θ) y‖ ≤
          B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) ∧
      (∃ F : ℝ × (ℝ × ℝ) → ℂ, ContDiff ℝ ∞ F ∧
        (∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Ioo (θ₁ - θ₁ / 4) (θ₂ + θ₁ / 4) → F p = canonMode P p.1 p.2) ∧
        (∀ (m : ℕ), ∃ B : ℝ, 0 < B ∧ ∀ (θ : ℝ) (y : ℝ × ℝ),
          ‖iteratedFDeriv ℝ m (fun z => F (θ, z)) y‖ ≤
            B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ∧
          ‖iteratedFDeriv ℝ m (fun z => deriv (fun t => F (t, z)) θ) y‖ ≤
            B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))) := by
  obtain ⟨hc_sm, _⟩ := UnforcedLeray.Short.Spine.coefficientBounds_proof V hSmoothAll
  -- Local bump helper on any `[a, b] ⊂ (0, ∞)`
  have hloc : ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∃ F : ℝ × (ℝ × ℝ) → ℂ, ContDiff ℝ ∞ F ∧
        (∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Ioo (a - a / 4) (b + a / 4) → F p = canonMode P p.1 p.2) ∧
        (∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ (θ : ℝ) (y : ℝ × ℝ),
          ‖iteratedFDeriv ℝ m (fun z => F (θ, z)) y‖ ≤
            B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ∧
          ‖iteratedFDeriv ℝ m (fun z => deriv (fun t => F (t, z)) θ) y‖ ≤
            B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by
    intro a b ha hab
    set rIn : ℝ := (b - a) / 2 + a / 4
    set rOut : ℝ := (b - a) / 2 + a / 2
    let bump : ContDiffBump ((a + b) / 2) :=
      { rIn := rIn
        rOut := rOut
        rIn_pos := by dsimp [rIn]; linarith
        rIn_lt_rOut := by dsimp [rIn, rOut]; linarith }
    let gCoef : ℕ → ℝ → ℂ := fun ℓ t =>
      if 0 < t then (bump t : ℂ) * cCoef V ℓ t else 0
    have hbump_zero : ∀ t : ℝ, t ∉ Icc (a / 2) (b + a / 2) → bump t = 0 := by
      intro t ht
      have hball : Metric.closedBall ((a + b) / 2) rOut = Icc (a / 2) (b + a / 2) := by
        rw [Real.closedBall_eq_Icc]
        congr 1 <;> (dsimp [rOut]; ring)
      rw [← hball, Metric.mem_closedBall, not_le] at ht
      exact bump.zero_of_le_dist ht.le
    have hg_eq : ∀ ℓ : ℕ, EqOn (gCoef ℓ) (fun t => (bump t : ℂ) * cCoef V ℓ t) (Ioi (a / 4)) := by
      intro ℓ t ht
      have ht0 : 0 < t := by linarith [show a / 4 < t from ht]
      simp [gCoef, ht0]
    have hg_zero : ∀ (ℓ : ℕ) (t : ℝ), t ≤ a / 3 → gCoef ℓ t = 0 := by
      intro ℓ t ht
      by_cases ht0 : 0 < t
      · have hnot : t ∉ Icc (a / 2) (b + a / 2) := fun hm => by linarith [hm.1]
        simp [gCoef, ht0, hbump_zero t hnot]
      · simp [gCoef, ht0]
    have hg_smooth : ∀ ℓ : ℕ, ContDiff ℝ ∞ (gCoef ℓ) := by
      intro ℓ
      rw [contDiff_iff_contDiffAt]
      intro t
      by_cases ht : a / 4 < t
      · have h1 : ContDiffOn ℝ ∞ (fun u => (bump u : ℂ) * cCoef V ℓ u) (Ioi (a / 4)) :=
          ((Complex.ofRealCLM.contDiff.comp bump.contDiff).contDiffOn).mul
            ((hc_sm ℓ).mono fun u hu => by
              have hu' : a / 4 < u := hu
              exact show (0 : ℝ) < u by linarith)
        exact (h1.contDiffAt (Ioi_mem_nhds ht)).congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) (hg_eq ℓ))
      · have ht' : t < a / 3 := by linarith
        exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (Iio_mem_nhds ht') fun u hu => hg_zero ℓ u (le_of_lt hu))
    -- Derivative bound on `gCoef ℓ` uniform in `t ∈ ℝ`
    have hg_deriv_bd : ∀ (k q : ℕ), ∃ Mg : ℝ, 0 < Mg ∧ ∀ (ℓ : ℕ) (t : ℝ),
        ‖iteratedFDeriv ℝ k (gCoef ℓ) t‖ * (1 + (ℓ : ℝ)) ^ q ≤ Mg / (1 + (ℓ : ℝ)) ^ 2 := by
      intro k q
      have hbc : ContDiff ℝ ∞ (fun t : ℝ => (bump t : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp bump.contDiff
      have hb_cpt : ∀ j ≤ k, ∃ Bj : ℝ, 0 ≤ Bj ∧ ∀ t : ℝ,
          ‖iteratedFDeriv ℝ j (fun u : ℝ => (bump u : ℂ)) t‖ ≤ Bj := by
        intro j _
        obtain ⟨Bj, hBj⟩ := (isCompact_Icc (a := a / 2) (b := b + a / 2)).exists_bound_of_continuousOn
          ((hbc.continuous_iteratedFDeriv (by simp)).continuousOn)
        refine ⟨max Bj 0, le_max_right _ _, fun t => ?_⟩
        by_cases ht : t ∈ Icc (a / 2) (b + a / 2)
        · exact (hBj t ht).trans (le_max_left _ _)
        · have hopen : IsOpen (Icc (a / 2) (b + a / 2))ᶜ := isClosed_Icc.isOpen_compl
          have hev : (fun u : ℝ => (bump u : ℂ)) =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℂ) := by
            filter_upwards [hopen.mem_nhds ht] with u hu
            simp [hbump_zero u hu]
          rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
          exact le_max_right _ _
      choose B_b hBb0 hBb using fun j : Fin (k + 1) => hb_cpt j.1 (Nat.lt_succ_iff.1 j.2)
      have hc_fin : ∀ j : Fin (k + 1), ∃ Mc : ℝ, 0 < Mc ∧ ∀ (ℓ : ℕ) (t : ℝ),
          t ∈ Icc (a / 2) (b + a / 2) →
            ‖iteratedDeriv j.1 (cCoef V ℓ) t‖ * (1 + (ℓ : ℝ)) ^ q ≤ Mc / (1 + (ℓ : ℝ)) ^ 2 := by
        intro j
        obtain ⟨Mc, hMc0, _, hMc⟩ := cCoef_rapid_decay hSmoothAll j.1 q
          (a := a / 2) (b := b + a / 2) (by linarith) (by linarith)
        exact ⟨Mc, hMc0, hMc⟩
      choose M_c hMc0 hMc using hc_fin
      set Mg : ℝ := 1 + ∑ j : Fin (k + 1),
        (k.choose j.1 : ℝ) * B_b ⟨k - j.1, by omega⟩ * M_c j
      have hMg_pos : 0 < Mg := by
        dsimp [Mg]
        refine add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _ => ?_)
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hBb0 _)) (hMc0 j).le
      refine ⟨Mg, hMg_pos, fun ℓ t => ?_⟩
      by_cases ht : t ∈ Icc (a / 2) (b + a / 2)
      · have ht_gt : a / 4 < t := by linarith [ht.1]
        have hev : gCoef ℓ =ᶠ[𝓝 t] fun u => (bump u : ℂ) * cCoef V ℓ u :=
          Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht_gt) (hg_eq ℓ)
        rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
        have hcd_c : ContDiffOn ℝ ∞ (cCoef V ℓ) (Ioi (a / 4)) :=
          (hc_sm ℓ).mono fun u hu => by
            have hu' : a / 4 < u := hu
            exact show (0 : ℝ) < u by linarith
        have hleib0 := norm_iteratedFDerivWithin_mul_le (N := ∞)
          hbc.contDiffOn hcd_c (uniqueDiffOn_Ioi (a / 4)) ht_gt (n := k) (by simp)
        have hmem_t : t ∈ Ioi (a / 4) := ht_gt
        rw [iteratedFDerivWithin_of_isOpen k isOpen_Ioi hmem_t,
          ← Finset.sum_range_reflect] at hleib0
        rw [Finset.sum_range] at hleib0
        calc ‖iteratedFDeriv ℝ k (fun u => (bump u : ℂ) * cCoef V ℓ u) t‖ * (1 + (ℓ : ℝ)) ^ q
            ≤ (∑ j : Fin (k + 1), (k.choose j.1 : ℝ) *
                ‖iteratedFDeriv ℝ (k - j.1) (fun u => (bump u : ℂ)) t‖ *
                ‖iteratedFDeriv ℝ j.1 (cCoef V ℓ) t‖) * (1 + (ℓ : ℝ)) ^ q := by
              refine mul_le_mul_of_nonneg_right
                (hleib0.trans (Finset.sum_le_sum fun j _ => ?_)) (by positivity)
              have hj_le : j.1 ≤ k := Nat.lt_succ_iff.1 j.2
              have hsub1 : k + 1 - 1 - j.1 = k - j.1 := by omega
              have hsub2 : k - (k - j.1) = j.1 := Nat.sub_sub_self hj_le
              rw [hsub1, iteratedFDerivWithin_of_isOpen (k - j.1) isOpen_Ioi hmem_t,
                iteratedFDerivWithin_of_isOpen (k - (k - j.1)) isOpen_Ioi hmem_t,
                hsub2, Nat.choose_symm hj_le]
          _ = ∑ j : Fin (k + 1), (k.choose j.1 : ℝ) *
                ‖iteratedFDeriv ℝ (k - j.1) (fun u => (bump u : ℂ)) t‖ *
                (‖iteratedDeriv j.1 (cCoef V ℓ) t‖ * (1 + (ℓ : ℝ)) ^ q) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv (f := cCoef V ℓ)]
              ring
          _ ≤ ∑ j : Fin (k + 1), (k.choose j.1 : ℝ) * B_b ⟨k - j.1, by omega⟩ *
                (M_c j / (1 + (ℓ : ℝ)) ^ 2) := by
              refine Finset.sum_le_sum fun j _ => ?_
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left (hBb ⟨k - j.1, by omega⟩ t) (Nat.cast_nonneg _))
                (hMc j ℓ t ht) (by positivity)
                (mul_nonneg (Nat.cast_nonneg _) (hBb0 _))
          _ ≤ Mg / (1 + (ℓ : ℝ)) ^ 2 := by
              have hpos2 : 0 < (1 + (ℓ : ℝ)) ^ 2 := by positivity
              rw [le_div_iff₀ hpos2]
              have hsum_eq : (∑ j : Fin (k + 1), (k.choose j.1 : ℝ) * B_b ⟨k - j.1, by omega⟩ *
                  (M_c j / (1 + (ℓ : ℝ)) ^ 2)) * (1 + (ℓ : ℝ)) ^ 2 =
                  ∑ j : Fin (k + 1), (k.choose j.1 : ℝ) * B_b ⟨k - j.1, by omega⟩ * M_c j := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun j _ => ?_
                field_simp [hpos2.ne']
              rw [hsum_eq]
              dsimp [Mg]; linarith
      · have hopen : IsOpen (Icc (a / 2) (b + a / 2))ᶜ := isClosed_Icc.isOpen_compl
        have hev : gCoef ℓ =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℂ) := by
          filter_upwards [hopen.mem_nhds ht] with u hu
          by_cases hu0 : 0 < u
          · simp [gCoef, hu0, hbump_zero u hu]
          · simp [gCoef, hu0]
        rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply,
          norm_zero, zero_mul]
        positivity
    let term : ℕ → ℝ × (ℝ × ℝ) → ℂ := fun ℓ p => gCoef ℓ p.1 * hermiteMode ℓ p.2
    have hterm_sm : ∀ ℓ : ℕ, ContDiff ℝ ∞ (term ℓ) := fun ℓ =>
      ((hg_smooth ℓ).comp contDiff_fst).mul
        ((UnforcedLeray.B0121.gS _).smooth'.comp contDiff_snd)
    have hterm_jet : ∀ k : ℕ, ∃ K : ℝ, 0 < K ∧
        Summable (fun ℓ : ℕ => K / (1 + (ℓ : ℝ)) ^ 2) ∧
        ∀ (ℓ : ℕ) (p : ℝ × (ℝ × ℝ)),
          ‖iteratedFDeriv ℝ k (term ℓ) p‖ ≤
            (K / (1 + (ℓ : ℝ)) ^ 2) * Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) := by
      intro k
      choose C_m hCm0 hCm using fun j : Fin (k + 1) => norm_iteratedFDeriv_hermiteMode_le j.1
      choose M_g hMg0 hMg using fun j : Fin (k + 1) => hg_deriv_bd (k - j.1) (j.1 + 2)
      set K : ℝ := 1 + ∑ j : Fin (k + 1), (k.choose j.1 : ℝ) * M_g j * C_m j
      have hK0 : 0 < K := by
        dsimp [K]
        refine add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _ => ?_)
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hMg0 j).le) (hCm0 j).le
      have hsumK : Summable (fun ℓ : ℕ => K / (1 + (ℓ : ℝ)) ^ 2) := by
        have h1 : Summable (fun ℓ : ℕ => (1 : ℝ) / ((ℓ + 1 : ℕ) : ℝ) ^ 2) :=
          (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
        refine (h1.mul_left K).congr fun ℓ => ?_
        push_cast; ring
      refine ⟨K, hK0, hsumK, fun ℓ p => ?_⟩
      have h1 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => gCoef ℓ q.1) :=
        (hg_smooth ℓ).comp contDiff_fst
      have h2 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => hermiteMode ℓ q.2) :=
        (UnforcedLeray.B0121.gS _).smooth'.comp contDiff_snd
      have hleib := norm_iteratedFDeriv_mul_le h1 h2 p (n := k) (by simp)
      rw [← Finset.sum_range_reflect, Finset.sum_range] at hleib
      have hf1 : ∀ m : ℕ, ‖iteratedFDeriv ℝ m (fun q : ℝ × (ℝ × ℝ) => gCoef ℓ q.1) p‖ ≤
          ‖iteratedFDeriv ℝ m (gCoef ℓ) p.1‖ := by
        intro m
        have eq1 : (fun q : ℝ × (ℝ × ℝ) => gCoef ℓ q.1) =
            (gCoef ℓ) ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := rfl
        rw [eq1, ContinuousLinearMap.iteratedFDeriv_comp_right _
          (hg_smooth ℓ) p (by exact_mod_cast le_top)]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        have hfst : ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
            simpa [one_mul] using norm_fst_le q
        calc ‖iteratedFDeriv ℝ m (gCoef ℓ) p.1‖ * ∏ _i : Fin m, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖
            ≤ ‖iteratedFDeriv ℝ m (gCoef ℓ) p.1‖ * ∏ _i : Fin m, (1 : ℝ) :=
              mul_le_mul_of_nonneg_left
                (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun _ _ => hfst) (norm_nonneg _)
          _ = ‖iteratedFDeriv ℝ m (gCoef ℓ) p.1‖ := by simp
      have hf2 : ∀ m : ℕ, ‖iteratedFDeriv ℝ m (fun q : ℝ × (ℝ × ℝ) => hermiteMode ℓ q.2) p‖ ≤
          ‖iteratedFDeriv ℝ m (hermiteMode ℓ) p.2‖ := by
        intro m
        have hhm : ContDiff ℝ ∞ (hermiteMode ℓ) := (UnforcedLeray.B0121.gS _).smooth'
        have eq2 : (fun q : ℝ × (ℝ × ℝ) => hermiteMode ℓ q.2) =
            (hermiteMode ℓ) ∘ (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := rfl
        rw [eq2, ContinuousLinearMap.iteratedFDeriv_comp_right _
          hhm p (by exact_mod_cast le_top)]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
            simpa [one_mul] using norm_snd_le q
        calc ‖iteratedFDeriv ℝ m (hermiteMode ℓ) p.2‖ *
              ∏ _i : Fin m, ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖
            ≤ ‖iteratedFDeriv ℝ m (hermiteMode ℓ) p.2‖ * ∏ _i : Fin m, (1 : ℝ) :=
              mul_le_mul_of_nonneg_left
                (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun _ _ => hsnd) (norm_nonneg _)
          _ = ‖iteratedFDeriv ℝ m (hermiteMode ℓ) p.2‖ := by simp
      calc ‖iteratedFDeriv ℝ k (term ℓ) p‖
          ≤ ∑ j : Fin (k + 1), (k.choose j.1 : ℝ) *
              ‖iteratedFDeriv ℝ (k - j.1) (gCoef ℓ) p.1‖ *
              ‖iteratedFDeriv ℝ j.1 (hermiteMode ℓ) p.2‖ := by
            refine hleib.trans (Finset.sum_le_sum fun j _ => ?_)
            have hj_le : j.1 ≤ k := Nat.lt_succ_iff.1 j.2
            have hsub1 : k + 1 - 1 - j.1 = k - j.1 := by omega
            have hsub2 : k - (k - j.1) = j.1 := Nat.sub_sub_self hj_le
            rw [hsub1, hsub2, Nat.choose_symm hj_le]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hf1 _) (Nat.cast_nonneg _)) (hf2 _)
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        _ ≤ ∑ j : Fin (k + 1), (k.choose j.1 : ℝ) *
              (M_g j / (1 + (ℓ : ℝ)) ^ 2 * C_m j * Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            calc ‖iteratedFDeriv ℝ (k - j.1) (gCoef ℓ) p.1‖ *
                  ‖iteratedFDeriv ℝ j.1 (hermiteMode ℓ) p.2‖
                ≤ ‖iteratedFDeriv ℝ (k - j.1) (gCoef ℓ) p.1‖ *
                    (C_m j * (1 + (ℓ : ℝ)) ^ (j.1 + 2) *
                      Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8)) :=
                  mul_le_mul_of_nonneg_left (hCm j ℓ p.2) (norm_nonneg _)
              _ = (‖iteratedFDeriv ℝ (k - j.1) (gCoef ℓ) p.1‖ * (1 + (ℓ : ℝ)) ^ (j.1 + 2)) *
                    C_m j * Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) := by ring
              _ ≤ (M_g j / (1 + (ℓ : ℝ)) ^ 2) * C_m j *
                    Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (hMg j ℓ p.1) (hCm0 j).le) (Real.exp_nonneg _)
        _ ≤ (K / (1 + (ℓ : ℝ)) ^ 2) * Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) := by
            have hpos2 : 0 < (1 + (ℓ : ℝ)) ^ 2 := by positivity
            have hsum_eq : (∑ j : Fin (k + 1), (k.choose j.1 : ℝ) *
                (M_g j / (1 + (ℓ : ℝ)) ^ 2 * C_m j *
                  Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8))) =
                ((∑ j : Fin (k + 1), (k.choose j.1 : ℝ) * M_g j * C_m j) / (1 + (ℓ : ℝ)) ^ 2) *
                  Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) := by
              rw [Finset.sum_div, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
            rw [hsum_eq]
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
            exact div_le_div_of_nonneg_right (by dsimp [K]; linarith) hpos2.le
    choose K_t hKt0 hKt_sum hKt_bd using hterm_jet
    have hKt_unif : ∀ (k ℓ : ℕ) (p : ℝ × (ℝ × ℝ)),
        ‖iteratedFDeriv ℝ k (term ℓ) p‖ ≤ K_t k / (1 + (ℓ : ℝ)) ^ 2 := by
      intro k ℓ p
      have hexp : Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg p.2.1, sq_nonneg p.2.2])
      exact (hKt_bd k ℓ p).trans (mul_le_of_le_one_right (by have := hKt0 k; positivity) hexp)
    obtain ⟨F, hF_def⟩ : ∃ F : ℝ × (ℝ × ℝ) → ℂ, F = fun p => ∑' ℓ : ℕ, term ℓ p := ⟨_, rfl⟩
    have hF_sm : ContDiff ℝ ∞ F := by
      rw [hF_def, contDiff_infty]
      intro r
      exact contDiff_tsum (N := (r : ℕ∞)) (f := term)
        (v := fun k ℓ => K_t k / (1 + (ℓ : ℝ)) ^ 2)
        (fun ℓ => (hterm_sm ℓ).of_le (by simp))
        (fun k _ => hKt_sum k)
        (fun k ℓ p _ => hKt_unif k ℓ p)
    have hF_eq : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Ioo (a - a / 4) (b + a / 4) →
        F p = canonMode P p.1 p.2 := by
      intro p hp
      have hp0 : 0 < p.1 := by linarith [hp.1]
      have hmem_in : p.1 ∈ Metric.closedBall ((a + b) / 2) rIn := by
        rw [Real.closedBall_eq_Icc]
        constructor <;> (dsimp [rIn]; linarith [hp.1, hp.2])
      have hb1 : bump p.1 = 1 := bump.one_of_mem_closedBall hmem_in
      rw [hF_def, canonMode_eq_tsum_hermiteMode hP hSmoothAll hVae hp0 p.2]
      exact tsum_congr fun ℓ => by simp [term, gCoef, hp0, hb1]
    have hF_iter : ∀ (r : ℕ) (p : ℝ × (ℝ × ℝ)),
        ‖iteratedFDeriv ℝ r F p‖ ≤
          (∑' ℓ : ℕ, K_t r / (1 + (ℓ : ℝ)) ^ 2) *
            Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) := by
      intro r p
      have heq_it := iteratedFDeriv_tsum_apply (N := (r : ℕ∞))
        (v := fun k ℓ => K_t k / (1 + (ℓ : ℝ)) ^ 2) (f := term)
        (fun ℓ => (hterm_sm ℓ).of_le (by simp))
        (fun k _ => hKt_sum k)
        (fun k ℓ q _ => hKt_unif k ℓ q)
        (le_rfl : (r : ℕ∞) ≤ (r : ℕ∞)) p
      rw [hF_def, heq_it]
      have hsum_norm : Summable (fun ℓ : ℕ => ‖iteratedFDeriv ℝ r (term ℓ) p‖) :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun ℓ => hKt_unif r ℓ p) (hKt_sum r)
      calc ‖∑' ℓ : ℕ, iteratedFDeriv ℝ r (term ℓ) p‖
          ≤ ∑' ℓ : ℕ, ‖iteratedFDeriv ℝ r (term ℓ) p‖ := norm_tsum_le_tsum_norm hsum_norm
        _ ≤ ∑' ℓ : ℕ, (K_t r / (1 + (ℓ : ℝ)) ^ 2) *
              Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) :=
            hsum_norm.tsum_le_tsum (fun ℓ => hKt_bd r ℓ p)
              ((hKt_sum r).mul_right _)
        _ = (∑' ℓ : ℕ, K_t r / (1 + (ℓ : ℝ)) ^ 2) *
              Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 8) := tsum_mul_right
    clear hF_def
    refine ⟨F, hF_sm, hF_eq, fun m => ?_⟩
    set S : ℝ := 1 + (∑' ℓ : ℕ, K_t m / (1 + (ℓ : ℝ)) ^ 2) +
      (∑' ℓ : ℕ, K_t (m + 1) / (1 + (ℓ : ℝ)) ^ 2)
    have hS0 : 0 < S := by
      dsimp [S]
      have s0 : 0 ≤ ∑' ℓ : ℕ, K_t m / (1 + (ℓ : ℝ)) ^ 2 :=
        tsum_nonneg fun _ => by have := hKt0 m; positivity
      have s1 : 0 ≤ ∑' ℓ : ℕ, K_t (m + 1) / (1 + (ℓ : ℝ)) ^ 2 :=
        tsum_nonneg fun _ => by have := hKt0 (m + 1); positivity
      linarith
    refine ⟨S, hS0, fun θ y => ?_⟩
    constructor
    · refine (norm_iteratedFDeriv_slice_le hF_sm m θ y).trans ((hF_iter m (θ, y)).trans ?_)
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
      dsimp [S]
      have s1 : 0 ≤ ∑' ℓ : ℕ, K_t (m + 1) / (1 + (ℓ : ℝ)) ^ 2 :=
        tsum_nonneg fun _ => by have := hKt0 (m + 1); positivity
      linarith
    · refine (norm_iteratedFDeriv_timeDeriv_slice_le hF_sm m θ y).trans
        ((hF_iter (m + 1) (θ, y)).trans ?_)
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
      dsimp [S]
      have s0 : 0 ≤ ∑' ℓ : ℕ, K_t m / (1 + (ℓ : ℝ)) ^ 2 :=
        tsum_nonneg fun _ => by have := hKt0 m; positivity
      linarith
  refine ⟨?_, ?_, hloc θ₁ θ₂ hθ₁ h12⟩
  · -- Joint `ContDiffOn ℝ ∞` on `Ioi 0 ×ˢ univ`
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    obtain ⟨F, hF_sm, hF_eq, -⟩ := hloc p.1 p.1 hp0 le_rfl
    have hnhds : Ioo (p.1 - p.1 / 4) (p.1 + p.1 / 4) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 p :=
      prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) univ_mem
    exact (hF_sm.contDiffAt.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hnhds fun q hq => (hF_eq q hq.1).symm)).contDiffWithinAt
  · -- Window jet bounds on `Icc θ₁ θ₂`
    obtain ⟨F, _, hF_eq, hF_bd⟩ := hloc θ₁ θ₂ hθ₁ h12
    intro m
    obtain ⟨B, hB0, hB⟩ := hF_bd m
    refine ⟨B, hB0, fun θ hθ y => ?_⟩
    have hθ_in : θ ∈ Ioo (θ₁ - θ₁ / 4) (θ₂ + θ₁ / 4) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hslice_eq : canonMode P θ = fun z => F (θ, z) :=
      funext fun z => (hF_eq (θ, z) hθ_in).symm
    have hdt_eq : (fun z => deriv (fun t => canonMode P t z) θ) =
        fun z => deriv (fun t => F (t, z)) θ := by
      funext z
      have hev : (fun t => canonMode P t z) =ᶠ[𝓝 θ] fun t => F (t, z) := by
        filter_upwards [Ioo_mem_nhds hθ_in.1 hθ_in.2] with t ht
        exact (hF_eq (t, z) ht).symm
      exact hev.deriv_eq
    rw [hslice_eq, hdt_eq]
    exact hB θ y

private theorem good_of_gauss_jet {g : ℝ × ℝ → ℂ} (hsm : ContDiff ℝ ∞ g)
    (hbd : ∀ k : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ × ℝ,
      ‖iteratedFDeriv ℝ k g y‖ ≤ B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    LamJetInf.Good g := by
  refine ⟨hsm, fun k => ?_⟩
  obtain ⟨B, hB0, hB⟩ := hbd k
  set C : ℝ := B * (2 : ℝ) ^ (k + 2) *
    (1 + (((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2)))
  refine ⟨C, by positivity, fun y => ?_⟩
  set u : ℝ := y.1 ^ 2 + y.2 ^ 2
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hnorm_sq : ‖y‖ ^ 2 ≤ u := by
    have hmax : ‖y‖ = max |y.1| |y.2| := rfl
    rw [hmax]
    rcases max_cases |y.1| |y.2| with ⟨h1, _⟩ | ⟨h2, _⟩
    · rw [h1, sq_abs]; dsimp [u]; linarith [sq_nonneg y.2]
    · rw [h2, sq_abs]; dsimp [u]; linarith [sq_nonneg y.1]
  have hfactor : (1 + ‖y‖) ^ (k + 2) * Real.exp (-u / 8) ≤
      (2 : ℝ) ^ (k + 2) * (1 + (((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2))) := by
    by_cases hy1 : ‖y‖ ≤ 1
    · have hp : (1 + ‖y‖) ^ (k + 2) ≤ (2 : ℝ) ^ (k + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (k + 2)
      have hexp : Real.exp (-u / 8) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc (1 + ‖y‖) ^ (k + 2) * Real.exp (-u / 8)
          ≤ (2 : ℝ) ^ (k + 2) * 1 :=
            mul_le_mul hp hexp (Real.exp_nonneg _) (by positivity)
        _ ≤ (2 : ℝ) ^ (k + 2) * (1 + (((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have : 0 ≤ ((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2) := by positivity
            linarith
    · have hy1' : 1 < ‖y‖ := lt_of_not_ge hy1
      have hy_le_u : ‖y‖ ≤ u := by nlinarith [hnorm_sq]
      have hp : (1 + ‖y‖) ^ (k + 2) ≤ (2 : ℝ) ^ (k + 2) * u ^ (k + 2) := by
        calc (1 + ‖y‖) ^ (k + 2) ≤ (2 * u) ^ (k + 2) :=
              pow_le_pow_left₀ (by positivity) (by linarith) (k + 2)
          _ = (2 : ℝ) ^ (k + 2) * u ^ (k + 2) := mul_pow 2 u (k + 2)
      have hexp_eq : Real.exp (-u / 8) = Real.exp (-((1 / 8 : ℝ) * u)) := by
        congr 1; ring
      have hpe := pow_mul_exp_neg_le (k + 2) (β := 1 / 8) (u := u) (by norm_num) hu0
      calc (1 + ‖y‖) ^ (k + 2) * Real.exp (-u / 8)
          ≤ ((2 : ℝ) ^ (k + 2) * u ^ (k + 2)) * Real.exp (-((1 / 8 : ℝ) * u)) := by
            rw [← hexp_eq]
            exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
        _ = (2 : ℝ) ^ (k + 2) * (u ^ (k + 2) * Real.exp (-((1 / 8 : ℝ) * u))) := by ring
        _ ≤ (2 : ℝ) ^ (k + 2) * (((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2)) :=
            mul_le_mul_of_nonneg_left hpe (by positivity)
        _ ≤ (2 : ℝ) ^ (k + 2) * (1 + (((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc ‖iteratedFDeriv ℝ k g y‖ * (1 + ‖y‖) ^ (k + 2)
      ≤ (B * Real.exp (-u / 8)) * (1 + ‖y‖) ^ (k + 2) :=
        mul_le_mul_of_nonneg_right (by simpa [u] using hB y) (by positivity)
    _ = B * ((1 + ‖y‖) ^ (k + 2) * Real.exp (-u / 8)) := by ring
    _ ≤ B * ((2 : ℝ) ^ (k + 2) * (1 + (((k + 2).factorial : ℝ) / (1 / 8 : ℝ) ^ (k + 2)))) :=
        mul_le_mul_of_nonneg_left hfactor hB0.le
    _ = C := by dsimp [C]; ring

/-! ## 4. Planar operator identities, rotation antisymmetry, and physical-coordinate PDE -/

private theorem angTwo_rot90 (x : ℝ × ℝ) : angTwo (-x.2, x.1) = -angTwo x := by
  unfold angTwo
  dsimp only
  have hnum : ((-x.2 : ℝ) + (x.1 : ℂ) * Complex.I) ^ 2 =
      -((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2 := by
    have hfac : ((-x.2 : ℝ) : ℂ) + (x.1 : ℂ) * Complex.I =
        Complex.I * ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) := by
      push_cast
      linear_combination -(x.2 : ℂ) * Complex.I_sq
    rw [hfac, mul_pow, Complex.I_sq]
    ring
  have hden : (-x.2) ^ 2 + x.1 ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by ring
  rw [hnum, hden, neg_div]

private theorem planarMode_rot90 (f : Profile) (x : ℝ × ℝ) :
    planarMode f (-x.2, x.1) = -planarMode f x := by
  unfold planarMode
  have hrad : (-x.2) ^ 2 + x.1 ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by ring
  rw [angTwo_rot90]
  dsimp only
  rw [hrad, mul_neg]

private theorem integral_plane_eq_zero_of_rot90 {g : ℝ × ℝ → ℂ}
    (_hgc : Continuous g) (hgi : Integrable g) (hrot : ∀ x : ℝ × ℝ, g (-x.2, x.1) = -g x) :
    ∫ x : ℝ × ℝ, g x = 0 := by
  have hg_rot_int : Integrable (fun x : ℝ × ℝ => g (-x.2, x.1)) := (funext hrot) ▸ hgi.neg
  have hneg_int : (∫ x : ℝ × ℝ, g (-x.2, x.1)) = -∫ x : ℝ × ℝ, g x := by
    have hfn : (fun x : ℝ × ℝ => g (-x.2, x.1)) = fun x => -g x := funext hrot
    rw [hfn, integral_neg]
  have heq_int : (∫ x : ℝ × ℝ, g (-x.2, x.1)) = ∫ x : ℝ × ℝ, g x := by
    have hg_prod : Integrable (Function.uncurry fun q η : ℝ => g (q, η)) (volume.prod volume) := by
      rwa [← Measure.volume_eq_prod]
    have hg_rot_prod :
        Integrable (Function.uncurry fun q η : ℝ => g (-η, q)) (volume.prod volume) := by
      rwa [← Measure.volume_eq_prod]
    rw [Measure.volume_eq_prod, integral_prod (fun x : ℝ × ℝ => g (-x.2, x.1)) hg_rot_prod,
      integral_prod g hg_prod, integral_integral_swap hg_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    exact integral_neg_eq_self (fun η : ℝ => g (η, q)) volume
  have hself : ∫ x : ℝ × ℝ, g x = -∫ x : ℝ × ℝ, g x := heq_int.symm.trans hneg_int
  apply Complex.ext
  · have hre := congrArg Complex.re hself
    simp only [Complex.neg_re] at hre
    simp only [Complex.zero_re]
    linarith
  · have him := congrArg Complex.im hself
    simp only [Complex.neg_im] at him
    simp only [Complex.zero_im]
    linarith

private theorem integral_cell_periodizeC_eq_plane {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hgc : Continuous g) (hgi : Integrable g) :
    ∫ x in B0579.cell c, periodizeC c g x = ∫ x : ℝ × ℝ, g x := by
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have h1 := UnforcedLeray.Cyl.integral_cell_periodize_mul (𝕜 := ℂ) (f := g)
    (g := fun _ : ℝ × ℝ => (1 : ℂ)) hc
    hgc.stronglyMeasurable stronglyMeasurable_const (fun _ => rfl) (by simpa [mul_one] using hgi)
  rw [hcell]
  simpa [periodizeC, UnforcedLeray.Cyl.periodize, mul_one] using h1

private theorem contDiff_canonMode_slice {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {θ : ℝ} (hθ : 0 < θ) :
    ContDiff ℝ ∞ (canonMode P θ) := by
  obtain ⟨hsm, _, _⟩ := canonMode_window_jet_and_smooth hP hSmoothAll hVae hθ le_rfl
  rw [← contDiffOn_univ]
  exact hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y _ => ⟨hθ, mem_univ y⟩

private theorem movD_canonMode_eq {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {θ : ℝ} (hθ : 0 < θ) (y : ℝ × ℝ) :
    movD (canonMode P θ) y = planarMode (oscillatorD (P.canonical θ)) y := by
  have hmovD_form : ∀ (g : ℝ × ℝ → ℂ), ContDiff ℝ 2 g → ∀ z : ℝ × ℝ,
      movD g z = iteratedFDeriv ℝ 2 g z ![(1, 0), (1, 0)] +
        iteratedFDeriv ℝ 2 g z ![(0, 1), (0, 1)] +
        (2 : ℝ) • g z + (1 / 2 : ℝ) • iteratedFDeriv ℝ 1 g z ![z] := by
    intro g hg z
    rw [OscillatorForceSub.movD_eq_dilationGen hg z, UnforcedLeray.Gaussian.dilationGen_eq,
      UnforcedLeray.Gaussian.laplacian_eq_iteratedFDeriv hg, iteratedFDeriv_one_apply]
    simp only [Matrix.cons_val_fin_one]
    abel
  choose C_m hCm0 hCm using fun k : Fin 3 => norm_iteratedFDeriv_hermiteMode_le k.1
  obtain ⟨M_c, hMc0, _, hMc⟩ :=
    cCoef_rapid_decay hSmoothAll 0 4 (a := θ / 2) (b := θ + 1) (by linarith) (by linarith)
  have hθ_mem : θ ∈ Icc (θ / 2) (θ + 1) := ⟨by linarith, by linarith⟩
  let term2d : ℕ → ℝ × ℝ → ℂ := fun ℓ z => cCoef V ℓ θ * hermiteMode ℓ z
  have hterm2d_sm : ∀ ℓ : ℕ, ContDiff ℝ ∞ (term2d ℓ) := fun ℓ =>
    contDiff_const.mul (UnforcedLeray.B0121.gS _).smooth'
  let v_bd : ℕ → ℕ → ℝ := fun k ℓ =>
    if hk : k < 3 then M_c * C_m ⟨k, hk⟩ / (1 + (ℓ : ℝ)) ^ 2 else 0
  have hv_sum : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (v_bd k) := by
    intro k hk
    have hk3 : k < 3 := by
      have hk2 : k ≤ 2 := by exact_mod_cast hk
      omega
    have h1 : Summable (fun ℓ : ℕ => (1 : ℝ) / ((ℓ + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
    refine (h1.mul_left (M_c * C_m ⟨k, hk3⟩)).congr fun ℓ => ?_
    simp only [v_bd, hk3, ↓reduceDIte]
    push_cast; ring
  have hv_le : ∀ (k ℓ : ℕ) (z : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k (term2d ℓ) z‖ ≤ v_bd k ℓ := by
    intro k ℓ z hk
    have hk2 : k ≤ 2 := by exact_mod_cast hk
    have hk3 : k < 3 := by omega
    simp only [v_bd, hk3, ↓reduceDIte]
    have hsm_h : ContDiff ℝ ∞ (hermiteMode ℓ) := (UnforcedLeray.B0121.gS _).smooth'
    have hit_eq : iteratedFDeriv ℝ k (term2d ℓ) z =
        cCoef V ℓ θ • iteratedFDeriv ℝ k (hermiteMode ℓ) z := by
      have hfn : term2d ℓ = cCoef V ℓ θ • hermiteMode ℓ := by
        funext w; simp [term2d]
      rw [hfn]
      exact iteratedFDeriv_const_smul_apply (a := cCoef V ℓ θ)
        (hsm_h.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [hit_eq, norm_smul]
    have hc4 : ‖cCoef V ℓ θ‖ * (1 + (ℓ : ℝ)) ^ 4 ≤ M_c / (1 + (ℓ : ℝ)) ^ 2 := by
      simpa [iteratedDeriv_zero] using hMc ℓ θ hθ_mem
    have hp_le : (1 + (ℓ : ℝ)) ^ (k + 2) ≤ (1 + (ℓ : ℝ)) ^ 4 :=
      pow_le_pow_right₀ (by linarith [ Nat.cast_nonneg (α := ℝ) ℓ ]) (by omega)
    have hexp : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
    have hCk : 0 < C_m ⟨k, hk3⟩ := hCm0 ⟨k, hk3⟩
    calc ‖cCoef V ℓ θ‖ * ‖iteratedFDeriv ℝ k (hermiteMode ℓ) z‖
        ≤ ‖cCoef V ℓ θ‖ * (C_m ⟨k, hk3⟩ * (1 + (ℓ : ℝ)) ^ (k + 2) * 1) :=
          mul_le_mul_of_nonneg_left
            ((hCm ⟨k, hk3⟩ ℓ z).trans (mul_le_mul_of_nonneg_left hexp (by positivity)))
            (norm_nonneg _)
      _ ≤ ‖cCoef V ℓ θ‖ * (C_m ⟨k, hk3⟩ * (1 + (ℓ : ℝ)) ^ 4) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp_le hCk.le) (norm_nonneg _)
      _ = C_m ⟨k, hk3⟩ * (‖cCoef V ℓ θ‖ * (1 + (ℓ : ℝ)) ^ 4) := by ring
      _ ≤ C_m ⟨k, hk3⟩ * (M_c / (1 + (ℓ : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hc4 hCk.le
      _ = M_c * C_m ⟨k, hk3⟩ / (1 + (ℓ : ℝ)) ^ 2 := by ring
  -- 2D series for `movD (canonMode P θ) y`
  have hcanon_eq : canonMode P θ = fun z => ∑' ℓ : ℕ, term2d ℓ z :=
    funext fun z => canonMode_eq_tsum_hermiteMode hP hSmoothAll hVae hθ z
  have hcanon_c2 : ContDiff ℝ 2 (canonMode P θ) :=
    (contDiff_canonMode_slice hP hSmoothAll hVae hθ).of_le (by simp)
  have hit1 := iteratedFDeriv_tsum_apply (N := (2 : ℕ∞)) (v := v_bd) (f := term2d)
    (fun ℓ => (hterm2d_sm ℓ).of_le (by simp)) hv_sum hv_le (by decide : (1 : ℕ∞) ≤ 2) y
  have hit2 := iteratedFDeriv_tsum_apply (N := (2 : ℕ∞)) (v := v_bd) (f := term2d)
    (fun ℓ => (hterm2d_sm ℓ).of_le (by simp)) hv_sum hv_le le_rfl y
  have hs0 : Summable (fun ℓ : ℕ => term2d ℓ y) :=
    Summable.of_norm_bounded (hv_sum 0 (by decide)) fun ℓ => by
      simpa [norm_iteratedFDeriv_zero] using hv_le 0 ℓ y (by decide)
  have hs1 : Summable (fun ℓ : ℕ => iteratedFDeriv ℝ 1 (term2d ℓ) y) :=
    Summable.of_norm_bounded (hv_sum 1 (by decide)) fun ℓ => hv_le 1 ℓ y (by decide)
  have hs2 : Summable (fun ℓ : ℕ => iteratedFDeriv ℝ 2 (term2d ℓ) y) :=
    Summable.of_norm_bounded (hv_sum 2 le_rfl) fun ℓ => hv_le 2 ℓ y le_rfl
  have he2a := (ContinuousMultilinearMap.hasSum_eval hs2.hasSum ![(1, 0), (1, 0)])
  have he2b := (ContinuousMultilinearMap.hasSum_eval hs2.hasSum ![(0, 1), (0, 1)])
  have he1 := (ContinuousMultilinearMap.hasSum_eval hs1.hasSum ![y])
  have hmovD_ser : movD (canonMode P θ) y =
      ∑' ℓ : ℕ, cCoef V ℓ θ * (-(ℓ : ℂ) * hermiteMode ℓ y) := by
    rw [hmovD_form (canonMode P θ) hcanon_c2 y]
    rw [show iteratedFDeriv ℝ 2 (canonMode P θ) y = _ from hcanon_eq ▸ hit2,
      show iteratedFDeriv ℝ 1 (canonMode P θ) y = _ from hcanon_eq ▸ hit1,
      congrFun hcanon_eq y]
    have hcomb := (((he2a.add he2b).add (hs0.hasSum.const_smul (2 : ℝ))).add
      (he1.const_smul (1 / 2 : ℝ))).tsum_eq
    rw [← hcomb]
    refine tsum_congr fun ℓ => ?_
    have hterm_c2 : ContDiff ℝ 2 (term2d ℓ) := (hterm2d_sm ℓ).of_le (by simp)
    have hm_term : movD (term2d ℓ) y = cCoef V ℓ θ * movD (hermiteMode ℓ) y := by
      unfold movD ladLapCx pdCx term2d
      have hd_hm : Differentiable ℝ (hermiteMode ℓ) :=
        ((UnforcedLeray.B0121.gS _).smooth').differentiable (by simp)
      have hpd_s : ∀ i : Fin 2, (fun w => fderiv ℝ (fun u => cCoef V ℓ θ * hermiteMode ℓ u) w
          (B0579.dir i)) = fun w => cCoef V ℓ θ * fderiv ℝ (hermiteMode ℓ) w (B0579.dir i) := by
        intro i; funext w
        rw [((hd_hm w).hasFDerivAt.const_mul (cCoef V ℓ θ)).fderiv]
        simp
      have hd_pd : ∀ i : Fin 2, Differentiable ℝ
          (fun w => fderiv ℝ (hermiteMode ℓ) w (B0579.dir i)) := fun i =>
        ((((UnforcedLeray.B0121.gS _).smooth').fderiv_right (m := ∞) (by simp)).clm_apply
          contDiff_const).differentiable (by simp)
      rw [hpd_s 0, hpd_s 1, congrFun (hpd_s 0) y, congrFun (hpd_s 1) y,
        (((hd_pd 0 y).hasFDerivAt).const_mul (cCoef V ℓ θ)).fderiv,
        (((hd_pd 1 y).hasFDerivAt).const_mul (cCoef V ℓ θ)).fderiv]
      simp only [smul_apply, smul_eq_mul]
      ring
    rw [← hmovD_form (term2d ℓ) hterm_c2 y, hm_term, movD_hermiteMode_eq]
  -- Now compare with `planarMode (oscillatorD (P.canonical θ)) y`
  by_cases hy : y = 0
  · subst hy
    have hp0 : planarMode (oscillatorD (P.canonical θ)) 0 = 0 := by simp [planarMode, angTwo]
    have hm0 : ∀ ℓ : ℕ, hermiteMode ℓ 0 = 0 := fun ℓ => by
      rw [← planarMode_hermiteProf_eq_hermiteMode]; simp [planarMode, angTwo]
    simp [hmovD_ser, hp0, hm0]
  · set r : ℝ := Real.sqrt (y.1 ^ 2 + y.2 ^ 2)
    have hr : 0 < r := by
      refine Real.sqrt_pos.2 ?_
      by_contra hle
      apply hy
      apply Prod.ext <;> dsimp <;> nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    -- 1D differentiation of `t ↦ term2d ℓ (t, 0)` on `ℝ`
    let g0 : ℕ → ℝ → ℂ := fun ℓ t => term2d ℓ (t, 0)
    let g1 : ℕ → ℝ → ℂ := fun ℓ t => fderiv ℝ (term2d ℓ) (t, 0) (1, 0)
    let g2 : ℕ → ℝ → ℂ := fun ℓ t => fderiv ℝ (g1 ℓ) t 1
    have hg0_deriv : ∀ (ℓ : ℕ) (t : ℝ), HasDerivAt (g0 ℓ) (g1 ℓ t) t := by
      intro ℓ t
      have hd : HasFDerivAt (term2d ℓ) (fderiv ℝ (term2d ℓ) (t, 0)) (t, 0) :=
        ((hterm2d_sm ℓ).differentiable (by simp) (t, 0)).hasFDerivAt
      have h1 := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ)))
      change HasDerivAt (fun s => term2d ℓ (s, 0)) (fderiv ℝ (term2d ℓ) (t, 0) (1, 0)) t
      exact h1
    have hg1_sm : ∀ ℓ : ℕ, ContDiff ℝ ∞ (g1 ℓ) := fun ℓ =>
      (((hterm2d_sm ℓ).fderiv_right (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
    have hg1_deriv : ∀ (ℓ : ℕ) (t : ℝ), HasDerivAt (g1 ℓ) (g2 ℓ t) t := fun ℓ t =>
      ((hg1_sm ℓ).differentiable (by simp) t).hasFDerivAt.hasDerivAt
    have hg0_bd : ∀ (ℓ : ℕ) (t : ℝ), ‖g0 ℓ t‖ ≤ v_bd 0 ℓ := fun ℓ t => by
      simpa [g0, norm_iteratedFDeriv_zero] using hv_le 0 ℓ (t, 0) (by decide)
    have hg1_bd : ∀ (ℓ : ℕ) (t : ℝ), ‖g1 ℓ t‖ ≤ v_bd 1 ℓ := by
      intro ℓ t
      have h1 := (fderiv ℝ (term2d ℓ) (t, 0)).le_opNorm (1, 0)
      have hn10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp
      calc ‖g1 ℓ t‖ ≤ ‖fderiv ℝ (term2d ℓ) (t, 0)‖ * 1 :=
            h1.trans (mul_le_mul_of_nonneg_left hn10 (norm_nonneg _))
        _ = ‖iteratedFDeriv ℝ 1 (term2d ℓ) (t, 0)‖ := by rw [mul_one, norm_iteratedFDeriv_one]
        _ ≤ v_bd 1 ℓ := hv_le 1 ℓ (t, 0) (by decide)
    have hg2_bd : ∀ (ℓ : ℕ) (t : ℝ), ‖g2 ℓ t‖ ≤ v_bd 2 ℓ := by
      have h_gen : ∀ (Ψ : ℝ × ℝ → ℂ), ContDiff ℝ ∞ Ψ → ∀ t : ℝ,
          HasDerivAt (fun s : ℝ => fderiv ℝ Ψ (s, (0 : ℝ)) ((1 : ℝ), (0 : ℝ)))
            (iteratedFDeriv ℝ 2 Ψ (t, (0 : ℝ)) ![((1 : ℝ), (0 : ℝ)), (1, 0)]) t := by
        intro Ψ hΨ t
        let ev10 : ((ℝ × ℝ) [×1]→L[ℝ] ℂ) →L[ℝ] ℂ :=
          ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℂ ![((1 : ℝ), (0 : ℝ))]
        have hd_it : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 Ψ) (t, (0 : ℝ)) :=
          (hΨ.differentiable_iteratedFDeriv (by simp)) (t, (0 : ℝ))
        have hpath : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) t :=
          (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ))
        have hc1 := (ev10.hasFDerivAt.comp (t, (0 : ℝ)) hd_it.hasFDerivAt).comp_hasDerivAt t hpath
        have hval : (ev10.comp (fderiv ℝ (iteratedFDeriv ℝ 1 Ψ) (t, (0 : ℝ)))) ((1 : ℝ), (0 : ℝ)) =
            iteratedFDeriv ℝ 2 Ψ (t, (0 : ℝ)) ![((1 : ℝ), (0 : ℝ)), (1, 0)] := by
          dsimp [ev10]
          rw [iteratedFDeriv_succ_eq_comp_left]
          rfl
        exact (hc1.congr_of_eventuallyEq (Eventually.of_forall fun s => by
          simp [ev10, Function.comp_def, iteratedFDeriv_one_apply])).congr_deriv hval
      intro ℓ t
      have hg2_eq : g2 ℓ t = iteratedFDeriv ℝ 2 (term2d ℓ) (t, (0 : ℝ)) ![(1, 0), (1, 0)] :=
        (hg1_deriv ℓ t).unique (h_gen (term2d ℓ) (hterm2d_sm ℓ) t)
      rw [hg2_eq]
      calc ‖iteratedFDeriv ℝ 2 (term2d ℓ) (t, 0) ![(1, 0), (1, 0)]‖
          ≤ ‖iteratedFDeriv ℝ 2 (term2d ℓ) (t, 0)‖ *
              ∏ i : Fin 2, ‖(![((1 : ℝ), (0 : ℝ)), (1, 0)] i)‖ :=
            (iteratedFDeriv ℝ 2 (term2d ℓ) (t, 0)).le_opNorm ![(1, 0), (1, 0)]
        _ ≤ ‖iteratedFDeriv ℝ 2 (term2d ℓ) (t, 0)‖ * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [Fin.prod_univ_two]
            simp
        _ ≤ v_bd 2 ℓ := by rw [mul_one]; exact hv_le 2 ℓ (t, 0) le_rfl
    have hsum_g0 : ∀ t : ℝ, Summable (fun ℓ => g0 ℓ t) := fun t =>
      Summable.of_norm_bounded (hv_sum 0 (by decide)) fun ℓ => hg0_bd ℓ t
    have hsum_g1 : ∀ t : ℝ, Summable (fun ℓ => g1 ℓ t) := fun t =>
      Summable.of_norm_bounded (hv_sum 1 (by decide)) fun ℓ => hg1_bd ℓ t
    have hsum_g2 : Summable (fun ℓ => g2 ℓ r) :=
      Summable.of_norm_bounded (hv_sum 2 le_rfl) fun ℓ => hg2_bd ℓ r
    have hd1_all : ∀ t : ℝ, HasDerivAt (fun s => ∑' ℓ, g0 ℓ s) (∑' ℓ, g1 ℓ t) t := fun t =>
      hasDerivAt_tsum_of_isPreconnected (hv_sum 1 (by decide)) isOpen_univ isPreconnected_univ
        (fun ℓ s _ => hg0_deriv ℓ s) (fun ℓ s _ => hg1_bd ℓ s) (mem_univ 0) (hsum_g0 0) (mem_univ t)
    have hd2_r : HasDerivAt (fun s => ∑' ℓ, g1 ℓ s) (∑' ℓ, g2 ℓ r) r :=
      hasDerivAt_tsum_of_isPreconnected (hv_sum 2 le_rfl) isOpen_univ isPreconnected_univ
        (fun ℓ s _ => hg1_deriv ℓ s) (fun ℓ s _ => hg2_bd ℓ s) (mem_univ 0) (hsum_g1 0) (mem_univ r)
    have hP_ray : P.canonical θ =ᶠ[𝓝 r] fun s => ∑' ℓ, g0 ℓ s := by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      have hs0' : 0 < s := hs
      have hcm := canonMode_eq_tsum_hermiteMode hP hSmoothAll hVae hθ (s, 0)
      unfold canonMode planarMode angTwo at hcm
      have hsq : Real.sqrt (s ^ 2 + 0 ^ 2) = s := by simpa using Real.sqrt_sq hs0'.le
      have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0'.ne'
      have hang1 : ((s : ℂ) + (0 : ℝ) * Complex.I) ^ 2 / ((s ^ 2 + 0 ^ 2 : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_zero, zero_mul, add_zero]
        have hd : ((s ^ 2 + 0 ^ 2 : ℝ) : ℂ) = (s : ℂ) ^ 2 := by push_cast; ring
        rw [hd]
        exact div_self (pow_ne_zero 2 hsC)
      rw [hsq, hang1, mul_one] at hcm
      exact hcm
    have hdP1 : deriv (P.canonical θ) r = ∑' ℓ, g1 ℓ r := by
      rw [hP_ray.deriv_eq, (hd1_all r).deriv]
    have hdP2 : deriv (deriv (P.canonical θ)) r = ∑' ℓ, g2 ℓ r := by
      have hev1 : deriv (P.canonical θ) =ᶠ[𝓝 r] fun s => ∑' ℓ, g1 ℓ s := by
        filter_upwards [hP_ray.eventuallyEq_nhds] with s hs
        rw [hs.deriv_eq, (hd1_all s).deriv]
      rw [hev1.deriv_eq, hd2_r.deriv]
    have hprof_ev : ∀ ℓ : ℕ, (fun s => cCoef V ℓ θ * hermiteProf ℓ s) =ᶠ[𝓝 r] g0 ℓ := by
      intro ℓ
      filter_upwards [Ioi_mem_nhds hr] with s hs
      dsimp [g0, term2d]
      rw [hermiteMode_pos_real ℓ hs]
    have hg0_r : ∀ ℓ : ℕ, g0 ℓ r = cCoef V ℓ θ * hermiteProf ℓ r := fun ℓ =>
      ((hprof_ev ℓ).self_of_nhds).symm
    have hg1_r : ∀ ℓ : ℕ, g1 ℓ r = cCoef V ℓ θ * deriv (hermiteProf ℓ) r := by
      intro ℓ
      have hd_prof : DifferentiableAt ℝ (hermiteProf ℓ) r := by
        have hloc_eq : hermiteProf ℓ =ᶠ[𝓝 r] fun s => hermiteMode ℓ (s, 0) := by
          filter_upwards [Ioi_mem_nhds hr] with s hs
          exact (hermiteMode_pos_real ℓ hs).symm
        exact (((UnforcedLeray.B0121.gS _).smooth'.comp
          (contDiff_id.prodMk contDiff_const)).differentiable (by simp) r).congr_of_eventuallyEq
          hloc_eq
      rw [← (hg0_deriv ℓ r).deriv, ← (hprof_ev ℓ).deriv_eq, deriv_const_mul _ hd_prof]
    have hg2_r : ∀ ℓ : ℕ, g2 ℓ r = cCoef V ℓ θ * deriv (deriv (hermiteProf ℓ)) r := by
      intro ℓ
      have hev_d1 : g1 ℓ =ᶠ[𝓝 r] fun s => cCoef V ℓ θ * deriv (hermiteProf ℓ) s := by
        filter_upwards [Ioi_mem_nhds hr, (hprof_ev ℓ).eventuallyEq_nhds] with s hs hpe
        have hd_prof_s : DifferentiableAt ℝ (hermiteProf ℓ) s := by
          have hloc_eq : hermiteProf ℓ =ᶠ[𝓝 s] fun u => hermiteMode ℓ (u, 0) := by
            filter_upwards [Ioi_mem_nhds hs] with u hu
            exact (hermiteMode_pos_real ℓ hu).symm
          exact (((UnforcedLeray.B0121.gS _).smooth'.comp
            (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s).congr_of_eventuallyEq
            hloc_eq
        rw [← (hg0_deriv ℓ s).deriv, ← hpe.deriv_eq, deriv_const_mul _ hd_prof_s]
      have hd_dprof : DifferentiableAt ℝ (deriv (hermiteProf ℓ)) r := by
        have h_d1 : ∀ (Ψ : ℝ × ℝ → ℂ), ContDiff ℝ ∞ Ψ →
            (∀ s : ℝ, deriv (fun u : ℝ => Ψ (u, (0 : ℝ))) s =
              fderiv ℝ Ψ (s, (0 : ℝ)) ((1 : ℝ), (0 : ℝ))) ∧
            DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ Ψ (s, (0 : ℝ)) ((1 : ℝ), (0 : ℝ))) r := by
          intro Ψ hΨ
          refine ⟨fun s => ?_, ?_⟩
          · exact (((hΨ.differentiable (by simp) (s, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt s
              ((hasDerivAt_id s).prodMk (hasDerivAt_const s (0 : ℝ)))).congr_of_eventuallyEq
              (Eventually.of_forall fun _ => rfl)).deriv
          · exact (((hΨ.fderiv_right (m := ∞) (by simp)).comp
              (contDiff_id.prodMk (contDiff_const (c := (0 : ℝ))))).clm_apply
              (contDiff_const (c := ((1 : ℝ), (0 : ℝ))))).differentiable (by simp) r
        obtain ⟨h_sl, h_df⟩ :=
          h_d1 (hermiteMode ℓ) (UnforcedLeray.B0121.gS (UnforcedLeray.B0121.φS ℓ)).smooth'
        have hloc_d1 : deriv (hermiteProf ℓ) =ᶠ[𝓝 r]
            fun s : ℝ => fderiv ℝ (hermiteMode ℓ) (s, (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
          filter_upwards [Ioi_mem_nhds hr] with s hs
          have hloc_eq : hermiteProf ℓ =ᶠ[𝓝 s] fun u : ℝ => hermiteMode ℓ (u, (0 : ℝ)) := by
            filter_upwards [Ioi_mem_nhds hs] with u hu
            exact (hermiteMode_pos_real ℓ hu).symm
          rw [hloc_eq.deriv_eq]
          exact h_sl s
        exact h_df.congr_of_eventuallyEq hloc_d1
      rw [← (hg1_deriv ℓ r).deriv, hev_d1.deriv_eq, deriv_const_mul _ hd_dprof]
    have hPr_eq : P.canonical θ r = ∑' ℓ, g0 ℓ r := hP_ray.self_of_nhds
    have hosc_ser : oscillatorD (P.canonical θ) r =
        ∑' ℓ : ℕ, cCoef V ℓ θ * (-(ℓ : ℂ) * hermiteProf ℓ r) := by
      unfold oscillatorD
      rw [hdP2, hdP1, hPr_eq]
      have hs_a := hsum_g2.hasSum
      have hs_b := (hsum_g1 r).hasSum.div_const (r : ℂ)
      have hs_c := ((hsum_g0 r).hasSum.mul_left (4 : ℂ)).div_const ((r : ℂ) ^ 2)
      have hs_d := (hsum_g1 r).hasSum.mul_left ((r : ℂ) / 2)
      have hs_e := (hsum_g0 r).hasSum.mul_left (2 : ℂ)
      rw [← ((((hs_a.add hs_b).sub hs_c).add hs_d).add hs_e).tsum_eq]
      refine tsum_congr fun ℓ => ?_
      rw [hg2_r ℓ, hg1_r ℓ, hg0_r ℓ, ← oscillatorD_hermiteProf_eq ℓ hr]
      unfold oscillatorD
      ring
    rw [hmovD_ser]
    unfold planarMode
    change _ = oscillatorD (P.canonical θ) r * angTwo y
    rw [hosc_ser, ← tsum_mul_right]
    refine tsum_congr fun ℓ => ?_
    rw [mul_assoc, mul_assoc, ← planarMode_hermiteProf_eq_hermiteMode ℓ y]
    rfl

private theorem movLPlanar_canonMode_eq {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {θ : ℝ} (hθ : 0 < θ) (y : ℝ × ℝ) :
    movLPlanar (canonMode P θ) y = planarMode (generatorL0 (P.canonical θ)) y := by
  set h : Profile := P.canonical θ
  have hcanon_seed : canonMode P θ = fun x => UnforcedLeray.Short.PartI.seedPlanar h (planeToC x) :=
    funext (planarMode_eq_seedPlanar h)
  have htoPlane_sm : ContDiff ℝ ∞ UnforcedLeray.B0009.toPlane := by
    have heq : UnforcedLeray.B0009.toPlane = fun z : ℂ => (Complex.reCLM z, Complex.imCLM z) := rfl
    rw [heq]
    exact Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  have hseed_eq : UnforcedLeray.Short.PartI.seedPlanar h =
      (canonMode P θ) ∘ UnforcedLeray.B0009.toPlane := by
    funext z
    simp [Function.comp_apply, hcanon_seed, EulerErrorEig.planeToC_toPlane]
  have hsm : ContDiff ℝ ∞ (UnforcedLeray.Short.PartI.seedPlanar h) := by
    rw [hseed_eq]
    exact (contDiff_canonMode_slice hP hSmoothAll hVae hθ).comp htoPlane_sm
  have hon : ContDiffOn ℝ ∞ h (Ioi 0) :=
    hP.canonical.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun r hr => ⟨hθ, hr⟩
  obtain ⟨_, hwin, _⟩ := canonMode_window_jet_and_smooth hP hSmoothAll hVae hθ le_rfl
  obtain ⟨B₀, hB₀_pos, hB₀⟩ := hwin 0
  have hqb : ∀ z : ℂ, ‖UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h z‖ ≤
      B₀ * Real.exp (-(‖z‖ ^ 2) / 8) := by
    intro z
    have h1 : UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h z =
        canonMode P θ (UnforcedLeray.B0009.toPlane z) := by
      change UnforcedLeray.Short.PartI.seedPlanar h z = _
      rw [hseed_eq]; rfl
    have hnsq : (UnforcedLeray.B0009.toPlane z).1 ^ 2 + (UnforcedLeray.B0009.toPlane z).2 ^ 2 =
        ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [UnforcedLeray.B0009.toPlane, sq]
    rw [h1, ← hnsq]
    simpa [norm_iteratedFDeriv_zero] using (hB₀ θ ⟨le_rfl, le_rfl⟩ (UnforcedLeray.B0009.toPlane z)).1
  have hqc : Continuous (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h) := hsm.continuous
  have hK : ∀ z : ℂ, ‖UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h z‖ ≤ B₀ := by
    intro z
    refine (hqb z).trans ?_
    have h1 : Real.exp (-(‖z‖ ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖z‖])
    exact mul_le_of_le_one_right hB₀_pos.le h1
  have hint : Integrable (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h) :=
    Integrable.mono'
      (UnforcedLeray.Short.PartI.BiotSavartCurlAux.integrable_exp_neg_sq_div_eight.const_mul B₀)
      hqc.aestronglyMeasurable (Eventually.of_forall hqb)
  have hi : IntegrableOn (fun ρ => ‖h ρ‖ * ρ) (Ioi 0) := by
    have hg := ((integrable_mul_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).const_mul
      B₀).integrableOn (s := Ioi (0 : ℝ))
    refine Integrable.mono' hg ?_ ?_
    · exact (hon.continuousOn.norm.mul continuousOn_id).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      have hb := hqb (ρ : ℂ)
      have hsp : UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h (ρ : ℂ) = h ρ :=
        _root_.seedPlanar_ofReal_eq h ρ hρ'
      rw [hsp, Complex.norm_real, Real.norm_of_nonneg hρ'.le] at hb
      have hb' : ‖h ρ‖ ≤ B₀ * Real.exp (-(1 / 8) * ρ ^ 2) :=
        hb.trans (le_of_eq (by congr 2; ring))
      rw [norm_mul, norm_norm, Real.norm_of_nonneg hρ'.le]
      calc ‖h ρ‖ * ρ ≤ B₀ * Real.exp (-(1 / 8) * ρ ^ 2) * ρ :=
            mul_le_mul_of_nonneg_right hb' hρ'.le
        _ = B₀ * (ρ * Real.exp (-(1 / 8) * ρ ^ 2)) := by ring
  have hlim := PlanarDualSub.dot_biotSavart_ofProfile_lim (m := 2)
    (by norm_num) hon hqc hK hint hi (planeToC y)
  have hre' : (planeToC y).re = y.1 := rfl
  have him' : (planeToC y).im = y.2 := rfl
  rw [hre', him'] at hlim
  have hbs : (fun z => (fun x => UnforcedLeray.Short.PartI.seedPlanar h (planeToC x))
      (UnforcedLeray.B0009.toPlane z)) = UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h := by
    funext z
    simp only [EulerErrorEig.planeToC_toPlane, UnforcedLeray.Short.PartI.seedPlanar]
  have htr := EulerErrorEig.trans_seed hsm y
  rw [hcanon_seed, planarMode_eq_seedPlanar]
  unfold movLPlanar kerVelPlanarCx
  rw [hbs, htr, EulerErrorEig.pd_omega0 0 y, EulerErrorEig.pd_omega0 1 y]
  simp only [Fin.isValue, ite_true, one_ne_zero, ite_false]
  have hcomb : UnforcedLeray.B0009.biotSavart (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h) 0
        (planeToC y) * (((UnforcedLeray.GaussianVortex.radialK ‖planeToC y‖ * y.1 : ℝ)) : ℂ) +
      UnforcedLeray.B0009.biotSavart (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h) 1
        (planeToC y) * (((UnforcedLeray.GaussianVortex.radialK ‖planeToC y‖ * y.2 : ℝ)) : ℂ) =
      (UnforcedLeray.GaussianVortex.radialK ‖planeToC y‖ : ℂ) *
        ((y.1 : ℂ) * UnforcedLeray.B0009.biotSavart (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h) 0
            (planeToC y) +
          (y.2 : ℂ) * UnforcedLeray.B0009.biotSavart (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 h) 1
            (planeToC y)) := by
    push_cast; ring
  rw [hcomb, hlim]
  simp only [UnforcedLeray.Short.PartI.seedPlanar, UnforcedLeray.Planar.NUE.Ang.ofProfile]
  rw [EulerErrorEig.gauss0_eq_radialOmega]
  have hnat : Int.natAbs (2 : ℤ) = 2 := rfl
  rw [hnat]
  by_cases hy : planeToC y = 0
  · have hphase : UnforcedLeray.Planar.NUE.Ang.angPhase 2 (planeToC y) = 0 := by
      rw [hy]; simp [UnforcedLeray.Planar.NUE.Ang.angPhase]
    rw [hphase]; simp
  · have hr : 0 < ‖planeToC y‖ := norm_pos_iff.2 hy
    have hwprof : UnforcedLeray.B0011.WProf h :=
      UnforcedLeray.Cons.C01.wprof_of_memXG (hP.canonical.memXG θ hθ)
    have hgn : UnforcedLeray.Planar.greenN 2 h ‖planeToC y‖ = greenInverse h ‖planeToC y‖ :=
      UnforcedLeray.Planar.greenN_two_eq_R hwprof hr
    rw [hgn, ← UnforcedLeray.Cons.C01.vortexOmega_eq, ← UnforcedLeray.Cons.C01.strainK_eq]
    unfold generatorL0
    push_cast
    ring

private theorem deriv_canonMode_eq_pde {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {θ : ℝ} (hθ : 0 < θ) (y : ℝ × ℝ) :
    -deriv (fun t => canonMode P t y) θ =
      movLPlanar (canonMode P θ) y + (θ : ℂ)⁻¹ * movD (canonMode P θ) y := by
  rw [movLPlanar_canonMode_eq hP hSmoothAll hVae hθ y,
    movD_canonMode_eq hP hSmoothAll hVae hθ y]
  by_cases hy : y = 0
  · subst hy
    have h0 : (fun t => canonMode P t 0) = fun _ => (0 : ℂ) := by
      funext t; simp [canonMode, planarMode, angTwo]
    rw [h0, deriv_const]
    simp [planarMode, angTwo]
  · set r : ℝ := Real.sqrt (y.1 ^ 2 + y.2 ^ 2)
    have hr : 0 < r := by
      refine Real.sqrt_pos.2 ?_
      by_contra hle
      apply hy
      apply Prod.ext <;> dsimp <;> nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hdiff : DifferentiableAt ℝ (fun t => P.canonical t r) θ := by
      have hon : ContDiffOn ℝ ∞ (fun t => P.canonical t r) (Ioi 0) :=
        hP.canonical.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          fun t ht => ⟨ht, hr⟩
      exact (hon.contDiffAt (Ioi_mem_nhds hθ)).differentiableAt (by simp)
    have hfn : (fun t => canonMode P t y) = fun t => P.canonical t r * angTwo y := rfl
    rw [hfn, deriv_mul_const hdiff, ← neg_mul, hP.canonical.equation θ hθ r hr]
    unfold planarMode
    change _ = generatorL0 (P.canonical θ) r * angTwo y +
      (θ : ℂ)⁻¹ * (oscillatorD (P.canonical θ) r * angTwo y)
    ring

private theorem translate_bounds_of_gauss_jet {q : ℝ × ℝ → ℂ}
    (hbd : ∀ m : Fin 3, ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ × ℝ,
      ‖iteratedFDeriv ℝ m.1 q y‖ ≤ B * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : ℝ × ℝ, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 q z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∀ z : ℝ × ℝ,
        ‖iteratedFDeriv ℝ k q z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) := by
  choose B hB0 hB using hbd
  set Bmax : ℝ := max (B 0) (max (B 1) (B 2))
  have hBm0 : 0 < Bmax := lt_of_lt_of_le (hB0 0) (le_max_left _ _)
  set K3 : ℝ := (2 : ℝ) ^ 3 * (1 + (((Nat.factorial 3 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 3))
  set C : ℝ := Bmax * K3
  have hC0 : 0 < C := by dsimp [C, K3]; positivity
  have hexp_wt : ∀ z : ℝ × ℝ, (1 + ‖z‖) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤
      K3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro z
    set u : ℝ := z.1 ^ 2 + z.2 ^ 2
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hnorm_sq : ‖z‖ ^ 2 ≤ u := by
      have hmax : ‖z‖ = max |z.1| |z.2| := rfl
      rw [hmax]
      rcases max_cases |z.1| |z.2| with ⟨h1, _⟩ | ⟨h2, _⟩
      · rw [h1, sq_abs]; dsimp [u]; linarith [sq_nonneg z.2]
      · rw [h2, sq_abs]; dsimp [u]; linarith [sq_nonneg z.1]
    have hcub : (1 + ‖z‖) ^ 3 * Real.exp (-u / 8) ≤ K3 := by
      by_cases hz1 : ‖z‖ ≤ 1
      · have hp : (1 + ‖z‖) ^ 3 ≤ (2 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 3
        have hexp : Real.exp (-u / 8) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        calc (1 + ‖z‖) ^ 3 * Real.exp (-u / 8)
            ≤ (2 : ℝ) ^ 3 * 1 := mul_le_mul hp hexp (Real.exp_nonneg _) (by positivity)
          _ ≤ K3 := by
              dsimp [K3]
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have : 0 ≤ ((Nat.factorial 3 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 3 := by positivity
              linarith
      · have hz1' : 1 < ‖z‖ := lt_of_not_ge hz1
        have hz_le_u : ‖z‖ ≤ u := by nlinarith [hnorm_sq]
        have hp : (1 + ‖z‖) ^ 3 ≤ (2 : ℝ) ^ 3 * u ^ 3 := by
          calc (1 + ‖z‖) ^ 3 ≤ (2 * u) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
            _ = (2 : ℝ) ^ 3 * u ^ 3 := mul_pow 2 u 3
        have hexp_eq : Real.exp (-u / 8) = Real.exp (-((1 / 8 : ℝ) * u)) := by congr 1; ring
        have hpe := pow_mul_exp_neg_le 3 (β := 1 / 8) (u := u) (by norm_num) hu0
        calc (1 + ‖z‖) ^ 3 * Real.exp (-u / 8)
            ≤ ((2 : ℝ) ^ 3 * u ^ 3) * Real.exp (-((1 / 8 : ℝ) * u)) := by
              rw [← hexp_eq]; exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
          _ = (2 : ℝ) ^ 3 * (u ^ 3 * Real.exp (-((1 / 8 : ℝ) * u))) := by ring
          _ ≤ (2 : ℝ) ^ 3 * (((Nat.factorial 3 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 3) :=
              mul_le_mul_of_nonneg_left hpe (by positivity)
          _ ≤ K3 := by dsimp [K3]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hz1_le : 1 + |z.1| ≤ 1 + ‖z‖ := by
      have : |z.1| ≤ ‖z‖ := le_max_left |z.1| |z.2|
      linarith
    have hpos1 : 0 < (1 + |z.1|) ^ 2 := by positivity
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |z.1|), Real.rpow_two, ← div_eq_mul_inv,
      le_div_iff₀ hpos1]
    calc (1 + ‖z‖) * Real.exp (-u / 8) * (1 + |z.1|) ^ 2
        ≤ (1 + ‖z‖) * Real.exp (-u / 8) * (1 + ‖z‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz1_le 2) (by positivity)
      _ = (1 + ‖z‖) ^ 3 * Real.exp (-u / 8) := by ring
      _ ≤ K3 := hcub
  have hk_bd : ∀ (m : Fin 3) (z : ℝ × ℝ),
      (1 + ‖z‖) * ‖iteratedFDeriv ℝ m.1 q z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro m z
    have hBm : B m ≤ Bmax := by
      fin_cases m
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    calc (1 + ‖z‖) * ‖iteratedFDeriv ℝ m.1 q z‖
        ≤ (1 + ‖z‖) * (B m * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_left (hB m z) (by positivity)
      _ ≤ (1 + ‖z‖) * (Bmax * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBm (Real.exp_nonneg _)) (by positivity)
      _ = Bmax * ((1 + ‖z‖) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) := by ring
      _ ≤ Bmax * (K3 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hexp_wt z) hBm0.le
      _ = C * (1 + |z.1|) ^ (-(2 : ℝ)) := by dsimp [C]; ring
  have hdrop : ∀ (m : Fin 3) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ m.1 q z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro m z
    refine (le_trans ?_ (hk_bd m z))
    nlinarith [norm_nonneg z, norm_nonneg (iteratedFDeriv ℝ m.1 q z)]
  refine ⟨C, hC0, ?_, ?_, ?_, ?_⟩
  · intro z; simpa [norm_iteratedFDeriv_zero] using hdrop 0 z
  · intro z; simpa [norm_iteratedFDeriv_one] using hk_bd 1 z
  · intro z; exact hdrop 2 z
  · intro k hk z
    have hk2 : k ≤ 2 := by exact_mod_cast hk
    exact hdrop ⟨k, by omega⟩ z

private theorem jscale_eq_heatDilation {a : ℝ} (ha : 0 < a) (g : ℝ × ℝ → ℂ) (z : ℝ × ℝ) :
    Jscale a g z = UnforcedLeray.Gaussian.heatDilation a g z := by
  unfold Jscale UnforcedLeray.Gaussian.heatDilation
  rw [Real.rpow_neg ha.le, Real.rpow_two, inv_pow, Complex.real_smul]
  congr 2
  ext <;> simp [div_eq_inv_mul]

/-- Uniform lattice sum bound `∑_{n : ℤ} (1 + |q - n d|)^{-2} ≤ S_lat` for all `d ≥ 1` and `q : ℝ`. -/
private theorem tsum_translate_sq_le_unif :
    ∃ S_lat : ℝ, 0 < S_lat ∧ ∀ {d : ℝ}, 1 ≤ d → ∀ q : ℝ,
      Summable (fun n : ℤ => (1 + |q - (n : ℝ) * d|) ^ (-(2 : ℝ))) ∧
        (∑' n : ℤ, (1 + |q - (n : ℝ) * d|) ^ (-(2 : ℝ))) ≤ S_lat := by
  have hd0 : (1 : ℝ) ≠ 0 := one_ne_zero
  have hdom : Summable (fun k : ℤ => (4 : ℝ) * (1 + |(k : ℝ)|) ^ (-(2 : ℝ))) := by
    have hs := UnforcedLeray.Gaussian.summable_translate (s := 2) (c := 1) (by norm_num) hd0 0
    refine (hs.mul_left 4).congr fun k => ?_
    congr 2
    simp
  refine ⟨1 + ∑' k : ℤ, (4 : ℝ) * (1 + |(k : ℝ)|) ^ (-(2 : ℝ)), ?_, ?_⟩
  · have hnn : 0 ≤ ∑' k : ℤ, (4 : ℝ) * (1 + |(k : ℝ)|) ^ (-(2 : ℝ)) :=
      tsum_nonneg fun k => by positivity
    linarith
  · intro d hd q
    have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd
    have hsum_q : Summable (fun n : ℤ => (1 + |q - (n : ℝ) * d|) ^ (-(2 : ℝ))) :=
      UnforcedLeray.Gaussian.summable_translate (by norm_num) hd_pos.ne' q
    refine ⟨hsum_q, ?_⟩
    set m₀ : ℤ := ⌊q / d⌋
    set r : ℝ := q - (m₀ : ℝ) * d
    have hr0 : 0 ≤ r := by
      dsimp [r]
      have := Int.floor_le (q / d)
      have := (le_div_iff₀ hd_pos).1 this
      linarith
    have hrd : r < d := by
      dsimp [r]
      have := Int.lt_floor_add_one (q / d)
      have := (div_lt_iff₀ hd_pos).1 this
      linarith
    rw [← (Equiv.addRight m₀).tsum_eq]
    have hterm : ∀ k : ℤ,
        (1 + |q - ((Equiv.addRight m₀ k : ℤ) : ℝ) * d|) ^ (-(2 : ℝ)) ≤
          (4 : ℝ) * (1 + |(k : ℝ)|) ^ (-(2 : ℝ)) := by
      intro k
      have harg : q - ((Equiv.addRight m₀ k : ℤ) : ℝ) * d = r - (k : ℝ) * d := by
        have heq : (Equiv.addRight m₀ k : ℤ) = k + m₀ := rfl
        rw [heq]
        dsimp [r]
        push_cast
        ring
      rw [harg]
      have hbase : (1 / 2 : ℝ) * (1 + |(k : ℝ)|) ≤ 1 + |r - (k : ℝ) * d| := by
        by_cases hk0 : k = 0
        · subst hk0; simp [abs_of_nonneg hr0]; linarith
        · by_cases hk1 : k = 1
          · subst hk1
            push_cast
            have : |r - 1 * d| = d - r := by
              rw [one_mul, abs_sub_comm, abs_of_pos (by linarith)]
            rw [this, abs_one]
            linarith
          · rcases lt_trichotomy k 0 with hneg | rfl | hpos
            · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
              have habs_k : |(k : ℝ)| = -(k : ℝ) := abs_of_neg (by linarith)
              have hrk : 0 ≤ r - (k : ℝ) * d := by nlinarith
              rw [habs_k, abs_of_nonneg hrk]
              have hkd : -(k : ℝ) ≤ -(k : ℝ) * d := by nlinarith
              linarith
            · exact (hk0 rfl).elim
            · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
                have : (2 : ℤ) ≤ k := by omega
                exact_mod_cast this
              have habs_k : |(k : ℝ)| = (k : ℝ) := abs_of_pos (by linarith)
              have hrk : r - (k : ℝ) * d ≤ 0 := by nlinarith
              rw [habs_k, abs_of_nonpos hrk]
              have hkd : ((k : ℝ) - 1) * 1 ≤ ((k : ℝ) - 1) * d :=
                mul_le_mul_of_nonneg_left hd (by linarith)
              linarith
      have hp1 : 0 < (1 / 2 : ℝ) * (1 + |(k : ℝ)|) := by positivity
      have hp2 : 0 < 1 + |r - (k : ℝ) * d| := by positivity
      rw [Real.rpow_neg hp2.le, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |(k : ℝ)|),
        Real.rpow_two, Real.rpow_two]
      have hsq : ((1 / 2 : ℝ) * (1 + |(k : ℝ)|)) ^ 2 ≤ (1 + |r - (k : ℝ) * d|) ^ 2 :=
        pow_le_pow_left₀ hp1.le hbase 2
      have hk_pos : (0 : ℝ) < 1 + |(k : ℝ)| := by positivity
      calc ((1 + |r - (k : ℝ) * d|) ^ 2)⁻¹
          ≤ (((1 / 2 : ℝ) * (1 + |(k : ℝ)|)) ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
        _ = (4 : ℝ) * ((1 + |(k : ℝ)|) ^ 2)⁻¹ := by
            field_simp [hk_pos.ne']
            ring
    have hsum_shift : Summable (fun k : ℤ =>
        (1 + |q - ((Equiv.addRight m₀ k : ℤ) : ℝ) * d|) ^ (-(2 : ℝ))) :=
      (Equiv.addRight m₀).summable_iff.2 hsum_q
    have hle := hsum_shift.tsum_le_tsum hterm hdom
    linarith

/-- Single-atom `s`-derivative for `τ ↦ heatDilation (clockA ν τ) (F (clockTheta ν τ, ·)) z`
when `clockA ν τ > 0`. -/
private theorem hasDerivAt_atom_heatDilation {F : ℝ × (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    {ν τ : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν τ) (z : ℝ × ℝ) :
    HasDerivAt
      (fun r => UnforcedLeray.Gaussian.heatDilation (clockA ν r)
        (fun y => F (clockTheta ν r, y)) z)
      (-(ν * (clockA ν τ)⁻¹) • UnforcedLeray.Gaussian.heatDilation (clockA ν τ)
          (UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν τ, y))) z -
        (((clockA ν τ) ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation (clockA ν τ)
          (fun y => deriv (fun t => F (t, y)) (clockTheta ν τ)) z) τ := by
  set b : ℝ := clockA ν τ
  set θ : ℝ := clockTheta ν τ
  set y : ℝ × ℝ := (Real.sqrt b)⁻¹ • z
  have hb_ne : b ≠ 0 := ha.ne'
  have hsq_pos : 0 < Real.sqrt b := Real.sqrt_pos.2 ha
  have hda : HasDerivAt (clockA ν) ν τ := by
    unfold clockA
    simpa using (hasDerivAt_id τ).const_mul ν |>.const_add 1
  have hd_theta : HasDerivAt (clockTheta ν) (-((b ^ 2)⁻¹)) τ := by
    have hmul : HasDerivAt (fun r => ν * clockA ν r) (ν * ν) τ := hda.const_mul ν
    have hinv := hmul.inv (mul_pos hν ha).ne'
    refine hinv.congr_deriv ?_
    dsimp [b]
    field_simp [hν.ne', hb_ne]
  have hd_isqrt : HasDerivAt (fun r => (Real.sqrt (clockA ν r))⁻¹)
      (-(1 / 2 : ℝ) * ν * b⁻¹ * (Real.sqrt b)⁻¹) τ := by
    have hsq := hda.sqrt ha.ne'
    have hinv := hsq.inv hsq_pos.ne'
    refine hinv.congr_deriv ?_
    change -(ν / (2 * Real.sqrt b)) / Real.sqrt b ^ 2 = _
    rw [Real.sq_sqrt ha.le]
    field_simp [hsq_pos.ne', hb_ne]
  have hd_pt : HasDerivAt (fun r => (clockTheta ν r, (Real.sqrt (clockA ν r))⁻¹ • z))
      (-((b ^ 2)⁻¹), (-(1 / 2 : ℝ) * ν * b⁻¹) • y) τ := by
    refine hd_theta.prodMk ?_
    have hz := hd_isqrt.smul_const z
    refine hz.congr_deriv ?_
    dsimp [y]
    rw [smul_smul]
  have hd_F : HasDerivAt (fun r => F (clockTheta ν r, (Real.sqrt (clockA ν r))⁻¹ • z))
      (fderiv ℝ F (θ, y) (-((b ^ 2)⁻¹), (-(1 / 2 : ℝ) * ν * b⁻¹) • y)) τ :=
    (hF.differentiable (by simp) (θ, y)).hasFDerivAt.comp_hasDerivAt τ hd_pt
  have hd_pref : HasDerivAt (fun r => (clockA ν r)⁻¹ ^ 2) (-2 * ν * b⁻¹ * (b⁻¹ ^ 2)) τ := by
    have hinv := hda.inv ha.ne'
    have hpow := hinv.pow 2
    refine hpow.congr_deriv ?_
    dsimp [b]
    field_simp [hb_ne]
  have htot := hd_pref.smul hd_F
  refine htot.congr_deriv ?_
  -- Identify directional derivatives of `F` with slice derivatives
  have hv_split : ((-((b ^ 2)⁻¹) : ℝ), (-(1 / 2 : ℝ) * ν * b⁻¹) • y) =
      (-((b ^ 2)⁻¹)) • ((1 : ℝ), (0 : ℝ × ℝ)) +
        (-(1 / 2 : ℝ) * ν * b⁻¹) • ((0 : ℝ), y) := by
    ext <;> simp
  have hf_t : fderiv ℝ F (θ, y) (1, 0) = deriv (fun t => F (t, y)) θ := by
    have hd : HasDerivAt (fun t => F (t, y)) (fderiv ℝ F (θ, y) (1, 0)) θ :=
      (hF.differentiable (by simp) (θ, y)).hasFDerivAt.comp_hasDerivAt θ
        ((hasDerivAt_id θ).prodMk (hasDerivAt_const θ y))
    exact hd.deriv.symm
  have hf_y : fderiv ℝ F (θ, y) (0, y) = fderiv ℝ (fun w => F (θ, w)) y y := by
    have hd : HasFDerivAt (fun w => F (θ, w))
        ((fderiv ℝ F (θ, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y :=
      (hF.differentiable (by simp) (θ, y)).hasFDerivAt.comp y
        ((hasFDerivAt_const θ y).prodMk (hasFDerivAt_id y))
    rw [hd.fderiv]
    simp
  rw [hv_split, map_add, map_smul, map_smul, hf_t, hf_y]
  unfold UnforcedLeray.Gaussian.heatDilation UnforcedLeray.Gaussian.dilationDrift
  dsimp only [b, θ, y]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Pointwise physical-coordinate PDE for `canonicalPhysColumn` on `s ≥ 0` (`eq:ct-moving-period`,
SP 3130-3140): `(∂_s - ν Δ) w + v · ∇w + u · ∇E_c = canonicalPhysResidual`. -/
private theorem canonicalPhysResidual_eq_pde {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ × ℝ) :
    canonicalPhysResidual P tr s x =
      deriv (fun τ => canonicalPhysColumn P ν τ x) s -
        (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν s) x +
        ladTransport tr s (canonicalPhysColumn P ν s) x +
        (canonicalPhysVel P ν s x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
          canonicalPhysVel P ν s x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hc_ne : c ≠ 0 := hc0.ne'
  let a : ℝ := clockA ν s
  have ha1 : 1 ≤ a := by dsimp [a, clockA]; nlinarith
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  let θ : ℝ := clockTheta ν s
  have hθ : 0 < θ := by dsimp [θ, clockTheta]; exact inv_pos.2 (mul_pos hν ha)
  let d : ℝ := cellLen c a
  -- Open age neighborhood `I_s = Ioo (-1/(2*ν)) (s + 1)` around `s`
  set s_lo : ℝ := -(1 / (2 * ν))
  set s_hi : ℝ := s + 1
  have hs_mem : s ∈ Ioo s_lo s_hi := by
    dsimp [s_lo, s_hi]
    have : 0 < 1 / (2 * ν) := by positivity
    exact ⟨by linarith, by linarith⟩
  set θ_lo : ℝ := (ν * clockA ν s_hi)⁻¹
  set θ_hi : ℝ := (ν * (1 / 2 : ℝ))⁻¹
  have ha_hi : 1 < clockA ν s_hi := by dsimp [clockA, s_hi]; nlinarith
  have hθ_lo_pos : 0 < θ_lo := inv_pos.2 (mul_pos hν (by linarith))
  have hθ_le : θ_lo ≤ θ_hi := inv_anti₀ (by positivity) (by nlinarith)
  obtain ⟨_, _, ⟨F, hF_sm, hF_eq, hF_bd⟩⟩ :=
    canonMode_window_jet_and_smooth hP hSmoothAll hVae hθ_lo_pos hθ_le
  -- Uniform translate bounds on `F(t, ·)` and `∂_t F(t, ·)` for all `t : ℝ`
  have htr_F : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (∀ z : ℝ × ℝ, ‖F (t, z)‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ (fun y => F (t, y)) z‖ ≤
        C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 (fun y => F (t, y)) z‖ ≤
        C * (1 + |z.1|) ^ (-(2 : ℝ))) ∧
      (∀ z : ℝ × ℝ, ‖deriv (fun u => F (u, z)) t‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) := by
    choose B hB0 hB using fun m : Fin 3 => hF_bd m.1
    set Bmax : ℝ := max (B 0) (max (B 1) (B 2))
    have hBm0 : 0 < Bmax := lt_of_lt_of_le (hB0 0) (le_max_left _ _)
    -- Apply `translate_bounds_of_gauss_jet` with uniform constant `Bmax`
    have hunif_F : ∀ t : ℝ, ∀ m : Fin 3, ∀ y : ℝ × ℝ,
        ‖iteratedFDeriv ℝ m.1 (fun z => F (t, z)) y‖ ≤
          Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      intro t m y
      have hBm : B m ≤ Bmax := by
        fin_cases m
        · exact le_max_left _ _
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact (le_max_right _ _).trans (le_max_right _ _)
      exact ((hB m t y).1).trans (mul_le_mul_of_nonneg_right hBm (Real.exp_nonneg _))
    set K3 : ℝ := (2 : ℝ) ^ 3 * (1 + (((Nat.factorial 3 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 3))
    refine ⟨16 * Bmax + Bmax * K3, by positivity, fun t => ?_⟩
    have hexp16 : ∀ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤
        16 * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z => FrameCont.exp_le_translate_weight z.1 z.2
    refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_⟩
    · have h0 := hunif_F t 0 z
      dsimp at h0
      rw [norm_iteratedFDeriv_zero] at h0
      calc ‖F (t, z)‖ ≤ Bmax * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
            h0.trans (mul_le_mul_of_nonneg_left (hexp16 z) hBm0.le)
        _ ≤ (16 * Bmax + Bmax * K3) * (1 + |z.1|) ^ (-(2 : ℝ)) := by
            have : 0 ≤ Bmax * K3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by dsimp [K3]; positivity
            linarith
    · have h1 := hunif_F t 1 z
      dsimp at h1
      rw [norm_iteratedFDeriv_one] at h1
      set u : ℝ := z.1 ^ 2 + z.2 ^ 2
      have hu0 : 0 ≤ u := by dsimp [u]; positivity
      have hnorm_sq : ‖z‖ ^ 2 ≤ u := by
        have hmax : ‖z‖ = max |z.1| |z.2| := rfl
        rw [hmax]
        rcases max_cases |z.1| |z.2| with ⟨hm1, _⟩ | ⟨hm2, _⟩
        · rw [hm1, sq_abs]; dsimp [u]; linarith [sq_nonneg z.2]
        · rw [hm2, sq_abs]; dsimp [u]; linarith [sq_nonneg z.1]
      have hcub : (1 + ‖z‖) ^ 3 * Real.exp (-u / 8) ≤ K3 := by
        by_cases hz1 : ‖z‖ ≤ 1
        · have hp : (1 + ‖z‖) ^ 3 ≤ (2 : ℝ) ^ 3 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 3
          have hexp : Real.exp (-u / 8) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          calc (1 + ‖z‖) ^ 3 * Real.exp (-u / 8)
              ≤ (2 : ℝ) ^ 3 * 1 := mul_le_mul hp hexp (Real.exp_nonneg _) (by positivity)
            _ ≤ K3 := by
                dsimp [K3]
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                have : 0 ≤ ((Nat.factorial 3 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 3 := by positivity
                linarith
        · have hz1' : 1 < ‖z‖ := lt_of_not_ge hz1
          have hz_le_u : ‖z‖ ≤ u := by nlinarith [hnorm_sq]
          have hp : (1 + ‖z‖) ^ 3 ≤ (2 : ℝ) ^ 3 * u ^ 3 := by
            calc (1 + ‖z‖) ^ 3 ≤ (2 * u) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
              _ = (2 : ℝ) ^ 3 * u ^ 3 := mul_pow 2 u 3
          have hexp_eq : Real.exp (-u / 8) = Real.exp (-((1 / 8 : ℝ) * u)) := by congr 1; ring
          have hpe := pow_mul_exp_neg_le 3 (β := 1 / 8) (u := u) (by norm_num) hu0
          calc (1 + ‖z‖) ^ 3 * Real.exp (-u / 8)
              ≤ ((2 : ℝ) ^ 3 * u ^ 3) * Real.exp (-((1 / 8 : ℝ) * u)) := by
                rw [← hexp_eq]; exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
            _ = (2 : ℝ) ^ 3 * (u ^ 3 * Real.exp (-((1 / 8 : ℝ) * u))) := by ring
            _ ≤ (2 : ℝ) ^ 3 * (((Nat.factorial 3 : ℕ) : ℝ) / (1 / 8 : ℝ) ^ 3) :=
                mul_le_mul_of_nonneg_left hpe (by positivity)
            _ ≤ K3 := by dsimp [K3]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hz1_le : 1 + |z.1| ≤ 1 + ‖z‖ := by
        have : |z.1| ≤ ‖z‖ := le_max_left |z.1| |z.2|
        linarith
      have hexp_wt : (1 + ‖z‖) * Real.exp (-u / 8) ≤ K3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
        have hpos1 : 0 < (1 + |z.1|) ^ 2 := by positivity
        rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |z.1|), Real.rpow_two, ← div_eq_mul_inv,
          le_div_iff₀ hpos1]
        calc (1 + ‖z‖) * Real.exp (-u / 8) * (1 + |z.1|) ^ 2
            ≤ (1 + ‖z‖) * Real.exp (-u / 8) * (1 + ‖z‖) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz1_le 2) (by positivity)
          _ = (1 + ‖z‖) ^ 3 * Real.exp (-u / 8) := by ring
          _ ≤ K3 := hcub
      calc (1 + ‖z‖) * ‖fderiv ℝ (fun y => F (t, y)) z‖
          ≤ (1 + ‖z‖) * (Bmax * Real.exp (-u / 8)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Bmax * ((1 + ‖z‖) * Real.exp (-u / 8)) := by ring
        _ ≤ Bmax * (K3 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hexp_wt hBm0.le
        _ ≤ (16 * Bmax + Bmax * K3) * (1 + |z.1|) ^ (-(2 : ℝ)) := by
            have : 0 ≤ 16 * Bmax * (1 + |z.1|) ^ (-(2 : ℝ)) := by positivity
            linarith
    · have h2 := hunif_F t 2 z
      calc ‖iteratedFDeriv ℝ 2 (fun y => F (t, y)) z‖
          ≤ Bmax * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
            h2.trans (mul_le_mul_of_nonneg_left (hexp16 z) hBm0.le)
        _ ≤ (16 * Bmax + Bmax * K3) * (1 + |z.1|) ^ (-(2 : ℝ)) := by
            have : 0 ≤ Bmax * K3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by dsimp [K3]; positivity
            linarith
    · have hdt := (hB 0 t z).2
      dsimp at hdt
      rw [norm_iteratedFDeriv_zero] at hdt
      have hB0_le : B 0 ≤ Bmax := le_max_left _ _
      calc ‖deriv (fun u => F (u, z)) t‖
          ≤ Bmax * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
            (hdt.trans (mul_le_mul_of_nonneg_right hB0_le (Real.exp_nonneg _))).trans
              (mul_le_mul_of_nonneg_left (hexp16 z) hBm0.le)
        _ ≤ (16 * Bmax + Bmax * K3) * (1 + |z.1|) ^ (-(2 : ℝ)) := by
            have : 0 ≤ Bmax * K3 * (1 + |z.1|) ^ (-(2 : ℝ)) := by dsimp [K3]; positivity
            linarith
  obtain ⟨C_tr, hCtr_pos, hCtr⟩ := htr_F
  -- Differentiate the periodized sum wrt `τ` on `Ioo s_lo s_hi` at `τ = s`
  set r₀ : ℝ := (Real.sqrt (clockA ν s_hi))⁻¹
  have hr₀_pos : 0 < r₀ := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  set K_dom : ℝ := (ν * 2 * (2 : ℝ) ^ 2 * (3 * C_tr) + 4 * (2 : ℝ) ^ 2 * C_tr) *
    (min 1 r₀) ^ (-(2 : ℝ))
  let g_n : ℤ → ℝ → ℂ := fun n r =>
    UnforcedLeray.Gaussian.heatDilation (clockA ν r) (fun y => F (clockTheta ν r, y))
      (x.1 - (n : ℝ) * c, x.2)
  let g'_n : ℤ → ℝ → ℂ := fun n r =>
    -(ν * (clockA ν r)⁻¹) • UnforcedLeray.Gaussian.heatDilation (clockA ν r)
        (UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν r, y)))
        (x.1 - (n : ℝ) * c, x.2) -
      (((clockA ν r) ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation (clockA ν r)
        (fun y => deriv (fun u => F (u, y)) (clockTheta ν r))
        (x.1 - (n : ℝ) * c, x.2)
  have hg_deriv : ∀ (n : ℤ) (r : ℝ), r ∈ Ioo s_lo s_hi → HasDerivAt (g_n n) (g'_n n r) r := by
    intro n r hr_in
    have har : 0 < clockA ν r := by
      dsimp [clockA, s_lo] at hr_in ⊢
      have : -(1 / 2 : ℝ) < ν * r := by
        have := mul_lt_mul_of_pos_left hr_in.1 hν
        field_simp [hν.ne'] at this
        linarith
      linarith
    exact hasDerivAt_atom_heatDilation hF_sm hν har (x.1 - (n : ℝ) * c, x.2)
  have hg'_bd : ∀ (n : ℤ) (r : ℝ), r ∈ Ioo s_lo s_hi →
      ‖g'_n n r‖ ≤ K_dom * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
    intro n r hr_in
    set b : ℝ := clockA ν r
    have hb_lo : 1 / 2 < b := by
      dsimp [b, clockA, s_lo] at hr_in ⊢
      have := mul_lt_mul_of_pos_left hr_in.1 hν
      field_simp [hν.ne'] at this
      linarith
    have hb_hi : b < clockA ν s_hi := by
      dsimp [b, clockA]; nlinarith [hr_in.2]
    have hb0 : 0 < b := by linarith
    have hrb : r₀ ≤ (Real.sqrt b)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt hb_hi.le)
    have hbinv : b⁻¹ ≤ 2 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hb_lo.le
      norm_num at this; exact this
    have hb2inv : (b ^ 2)⁻¹ ≤ 4 := by
      have : (1 / 4 : ℝ) ≤ b ^ 2 := by nlinarith
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) this
      norm_num at h; exact h
    obtain ⟨h0t, h1t, _, hdtt⟩ := hCtr (clockTheta ν r)
    have hdr := UnforcedLeray.Gaussian.translate_bound_comp_smul (s := 2) (by norm_num) hr₀_pos hrb
      (UnforcedLeray.Gaussian.norm_dilationDrift_le h0t h1t) (x.1 - (n : ℝ) * c, x.2)
    have hdt := UnforcedLeray.Gaussian.translate_bound_comp_smul (s := 2) (by norm_num) hr₀_pos hrb
      hdtt (x.1 - (n : ℝ) * c, x.2)
    have hgn_r : g'_n n r =
        -(ν * b⁻¹) • UnforcedLeray.Gaussian.heatDilation b
            (UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν r, y)))
            (x.1 - (n : ℝ) * c, x.2) -
          ((b ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation b
            (fun y => deriv (fun u => F (u, y)) (clockTheta ν r))
            (x.1 - (n : ℝ) * c, x.2) := rfl
    rw [hgn_r]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_neg, UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
      norm_smul, UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
      Real.norm_of_nonneg (mul_nonneg hν.le (inv_nonneg.2 hb0.le)),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b⁻¹ ^ 2),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (b ^ 2)⁻¹)]
    have hb_sq_le : b⁻¹ ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hb0.le) hbinv 2
    have t1 : ν * b⁻¹ * (b⁻¹ ^ 2 *
        ‖UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν r, y))
          ((Real.sqrt b)⁻¹ • (x.1 - (n : ℝ) * c, x.2))‖) ≤
        ν * 2 * ((2 : ℝ) ^ 2 *
          (3 * C_tr * (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)))) := by
      gcongr
    have t2 : (b ^ 2)⁻¹ * (b⁻¹ ^ 2 *
        ‖deriv (fun u => F (u, (Real.sqrt b)⁻¹ • (x.1 - (n : ℝ) * c, x.2))) (clockTheta ν r)‖) ≤
        4 * ((2 : ℝ) ^ 2 *
          (C_tr * (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)))) := by
      gcongr
    calc _ ≤ ν * 2 * ((2 : ℝ) ^ 2 *
            (3 * C_tr * (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)))) +
          4 * ((2 : ℝ) ^ 2 *
            (C_tr * (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)))) :=
          add_le_add t1 t2
      _ = K_dom * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by dsimp [K_dom]; ring
  have hu_dom : Summable (fun n : ℤ => K_dom * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
    (UnforcedLeray.Gaussian.summable_translate (by norm_num) hc_ne x.1).mul_left K_dom
  have hsum_s : Summable (fun n : ℤ => g_n n s) :=
    UnforcedLeray.Gaussian.summable_periodize (s := 2) (by norm_num) hc_ne
      (UnforcedLeray.Gaussian.norm_heatDilation_le (by norm_num) ha (hCtr θ).1) x
  have htsum_deriv := hasDerivAt_tsum_of_isPreconnected hu_dom isOpen_Ioo isPreconnected_Ioo
    hg_deriv hg'_bd hs_mem hsum_s hs_mem
  -- On `Ioo s_lo s_hi`, `F(clockTheta ν r, ·) = canonMode P (clockTheta ν r)`
  have hθ_in_win : ∀ r ∈ Ioo s_lo s_hi,
      clockTheta ν r ∈ Ioo (θ_lo - θ_lo / 4) (θ_hi + θ_lo / 4) := by
    intro r hr_in
    have hb_lo : 1 / 2 < clockA ν r := by
      dsimp [clockA, s_lo] at hr_in ⊢
      have := mul_lt_mul_of_pos_left hr_in.1 hν
      field_simp [hν.ne'] at this; linarith
    have hb_hi : clockA ν r < clockA ν s_hi := by dsimp [clockA]; nlinarith [hr_in.2]
    have ht_lo : θ_lo < clockTheta ν r :=
      inv_strictAnti₀ (mul_pos hν (by linarith)) (mul_lt_mul_of_pos_left hb_hi hν)
    have ht_hi : clockTheta ν r < θ_hi :=
      inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hb_lo hν)
    exact ⟨by linarith, by linarith⟩
  have hw_ev : (fun τ => canonicalPhysColumn P ν τ x) =ᶠ[𝓝 s]
      fun τ => P.gaugeFactor ν * ∑' n : ℤ, g_n n τ := by
    filter_upwards [Ioo_mem_nhds hs_mem.1 hs_mem.2] with τ hτ
    have ha_τ : 0 < clockA ν τ := by
      dsimp [clockA, s_lo] at hτ ⊢
      have := mul_lt_mul_of_pos_left hτ.1 hν
      field_simp [hν.ne'] at this; linarith
    rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha_τ x]
    congr 1
    unfold periodizeC
    refine tsum_congr fun n => ?_
    rw [jscale_eq_heatDilation ha_τ]
    have hfn : canonMode P (clockTheta ν τ) = fun y => F (clockTheta ν τ, y) :=
      funext fun y => (hF_eq (clockTheta ν τ, y) (hθ_in_win τ hτ)).symm
    change UnforcedLeray.Gaussian.heatDilation (clockA ν τ) (canonMode P (clockTheta ν τ))
      (x.1 - (n : ℝ) * c, x.2) = g_n n τ
    rw [hfn]
  have hF_slice_θ : (fun y => F (θ, y)) = canonMode P θ :=
    funext fun y => hF_eq (θ, y) (hθ_in_win s hs_mem)
  have hF_dt_θ : (fun y => deriv (fun u => F (u, y)) θ) =
      fun y => deriv (fun u => canonMode P u y) θ := by
    funext y
    have hev : (fun u => F (u, y)) =ᶠ[𝓝 θ] fun u => canonMode P u y := by
      filter_upwards [Ioo_mem_nhds (hθ_in_win s hs_mem).1 (hθ_in_win s hs_mem).2] with u hu
      exact hF_eq (u, y) hu
    exact hev.deriv_eq
  have hdw_eq : deriv (fun τ => canonicalPhysColumn P ν τ x) s =
      P.gaugeFactor ν * ∑' n : ℤ, g'_n n s := by
    rw [hw_ev.deriv_eq, (htsum_deriv.const_mul (P.gaugeFactor ν)).deriv]
  -- Spatial Laplacian of `canonicalPhysColumn P ν s`
  have hΦ_sm : ContDiff ℝ ∞ (canonMode P θ) := by
    rw [← hF_slice_θ]
    exact hF_sm.comp (contDiff_const.prodMk contDiff_id)
  have hΦ_c2 : ContDiff ℝ 2 (canonMode P θ) := hΦ_sm.of_le (by simp)
  have hΦ_tr0 : ∀ z : ℝ × ℝ, ‖canonMode P θ z‖ ≤ C_tr * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    rw [← hF_slice_θ]; exact (hCtr θ).1
  have hΦ_tr1 : ∀ z : ℝ × ℝ, (1 + ‖z‖) * ‖fderiv ℝ (canonMode P θ) z‖ ≤
      C_tr * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    rw [← hF_slice_θ]; exact (hCtr θ).2.1
  have hΦ_tr2 : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ 2 (canonMode P θ) z‖ ≤
      C_tr * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    rw [← hF_slice_θ]; exact (hCtr θ).2.2.1
  have hD_dil : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ k (UnforcedLeray.Gaussian.heatDilation a (canonMode P θ)) z‖ ≤
        C' * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro k hk
    have hk' : k ≤ 2 := by exact_mod_cast hk
    have hqk : ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ k (canonMode P θ) z‖ ≤
        C_tr * (1 + |z.1|) ^ (-(2 : ℝ)) := by
      interval_cases k
      · simpa [norm_iteratedFDeriv_zero] using hΦ_tr0
      · intro z; rw [norm_iteratedFDeriv_one]
        refine le_trans ?_ (hΦ_tr1 z)
        nlinarith [norm_nonneg (fderiv ℝ (canonMode P θ) z), norm_nonneg z]
      · exact hΦ_tr2
    exact ⟨_, UnforcedLeray.Gaussian.norm_iteratedFDeriv_heatDilation_le (by norm_num) ha k hqk⟩
  have hP_sm : ContDiff ℝ 2
      (UnforcedLeray.Gaussian.periodize c
        (UnforcedLeray.Gaussian.heatDilation a (canonMode P θ))) :=
    UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (by norm_num) hc_ne
      ((UnforcedLeray.Gaussian.contDiff_heatDilation hΦ_c2 a) :
        ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) _) hD_dil
  have hlap_eq_cyl : ∀ (Ψ : ℝ × ℝ → ℂ), ContDiff ℝ 2 Ψ →
      ladLapCx Ψ x = UnforcedLeray.Cyl.laplacian Ψ x := by
    intro Ψ hΨ
    have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
    have h11 : ContDiff ℝ (1 + 1) Ψ := by rwa [one_add_one_eq_two]
    have hdQ : Differentiable ℝ (UnforcedLeray.Cyl.partialQ Ψ) :=
      (UnforcedLeray.Cyl.contDiff_partialQ h11).differentiable (by norm_num)
    have hdE : Differentiable ℝ (UnforcedLeray.Cyl.partialEta Ψ) :=
      (UnforcedLeray.Cyl.contDiff_partialEta h11).differentiable (by norm_num)
    have hpQ : UnforcedLeray.Cyl.partialQ Ψ = pdCx 0 Ψ :=
      funext fun z => UnforcedLeray.Cyl.partialQ_eq_fderiv hd z
    have hpE : UnforcedLeray.Cyl.partialEta Ψ = pdCx 1 Ψ :=
      funext fun z => UnforcedLeray.Cyl.partialEta_eq_fderiv hd z
    unfold UnforcedLeray.Cyl.laplacian ladLapCx
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hdQ x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv hdE x, hpQ, hpE]
    rfl
  have hw_s_eq : canonicalPhysColumn P ν s = fun z =>
      P.gaugeFactor ν * UnforcedLeray.Gaussian.periodize c
        (UnforcedLeray.Gaussian.heatDilation a (canonMode P θ)) z := by
    funext z
    rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha z]
    congr 1
    unfold periodizeC UnforcedLeray.Gaussian.periodize
    exact tsum_congr fun n => jscale_eq_heatDilation ha (canonMode P θ) _
  have hlap_w : ladLapCx (canonicalPhysColumn P ν s) x =
      P.gaugeFactor ν * ((a⁻¹ : ℝ) • UnforcedLeray.Gaussian.periodize c
        (UnforcedLeray.Gaussian.heatDilation a (UnforcedLeray.Cyl.laplacian (canonMode P θ))) x) := by
    have hsm_mul : ContDiff ℝ 2 (canonicalPhysColumn P ν s) := by
      rw [hw_s_eq]; exact contDiff_const.mul hP_sm
    rw [hlap_eq_cyl _ hsm_mul]
    have hc_lap : UnforcedLeray.Cyl.laplacian (canonicalPhysColumn P ν s) x =
        P.gaugeFactor ν * UnforcedLeray.Cyl.laplacian
          (UnforcedLeray.Gaussian.periodize c
            (UnforcedLeray.Gaussian.heatDilation a (canonMode P θ))) x := by
      rw [UnforcedLeray.Gaussian.laplacian_eq_iteratedFDeriv hsm_mul,
        UnforcedLeray.Gaussian.laplacian_eq_iteratedFDeriv hP_sm]
      have hit_c : iteratedFDeriv ℝ 2 (canonicalPhysColumn P ν s) x =
          P.gaugeFactor ν • iteratedFDeriv ℝ 2
            (UnforcedLeray.Gaussian.periodize c
              (UnforcedLeray.Gaussian.heatDilation a (canonMode P θ))) x := by
        have hfn : canonicalPhysColumn P ν s = P.gaugeFactor ν •
            UnforcedLeray.Gaussian.periodize c
              (UnforcedLeray.Gaussian.heatDilation a (canonMode P θ)) := by
          funext z; rw [hw_s_eq]; simp
        rw [hfn]
        exact iteratedFDeriv_const_smul_apply (a := P.gaugeFactor ν) hP_sm.contDiffAt
      rw [hit_c]
      simp [smul_eq_mul, mul_add]
    rw [hc_lap, UnforcedLeray.Gaussian.laplacian_periodize
      (UnforcedLeray.Gaussian.contDiff_heatDilation hΦ_c2 a) (by norm_num) hc_ne hD_dil x]
    congr 1
    unfold UnforcedLeray.Gaussian.periodize
    rw [← tsum_const_smul'']
    congr 1; funext n
    exact UnforcedLeray.Gaussian.laplacian_heatDilation hΦ_c2 ha _
  -- Combine `∂_s w - ν Δ w` and cancel `movD`
  have hs_drift : Summable (fun n : ℤ =>
      UnforcedLeray.Gaussian.heatDilation a
        (UnforcedLeray.Gaussian.dilationDrift (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2)) :=
    UnforcedLeray.Gaussian.summable_periodize (s := 2) (by norm_num) hc_ne
      (UnforcedLeray.Gaussian.norm_heatDilation_le (by norm_num) ha
        (UnforcedLeray.Gaussian.norm_dilationDrift_le hΦ_tr0 hΦ_tr1)) x
  have hs_dt : Summable (fun n : ℤ =>
      UnforcedLeray.Gaussian.heatDilation a
        (fun y => deriv (fun u => canonMode P u y) θ) (x.1 - (n : ℝ) * c, x.2)) :=
    UnforcedLeray.Gaussian.summable_periodize (s := 2) (by norm_num) hc_ne
      (UnforcedLeray.Gaussian.norm_heatDilation_le (by norm_num) ha
        (fun z => by rw [← congrFun hF_dt_θ z]; exact (hCtr θ).2.2.2 z)) x
  have hs_lap : Summable (fun n : ℤ =>
      UnforcedLeray.Gaussian.heatDilation a
        (UnforcedLeray.Cyl.laplacian (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2)) :=
    UnforcedLeray.Gaussian.summable_periodize (s := 2) (by norm_num) hc_ne
      (UnforcedLeray.Gaussian.norm_heatDilation_le (by norm_num) ha
        (UnforcedLeray.Gaussian.norm_laplacian_le_translate hΦ_c2 hΦ_tr2)) x
  have hlin_part : deriv (fun τ => canonicalPhysColumn P ν τ x) s -
      (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν s) x =
      P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        periodizeC c (Jscale a (movLPlanar (canonMode P θ))) x := by
    rw [hdw_eq, hlap_w]
    have hgn_s : (fun n : ℤ => g'_n n s) = fun n : ℤ =>
        -(ν * a⁻¹) • UnforcedLeray.Gaussian.heatDilation a
            (UnforcedLeray.Gaussian.dilationDrift (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2) -
          ((a ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation a
            (fun y => deriv (fun u => canonMode P u y) θ) (x.1 - (n : ℝ) * c, x.2) := by
      funext n
      dsimp [g'_n, a, θ]
      rw [hF_slice_θ, hF_dt_θ]
    rw [hgn_s]
    have hs_12 : Summable (fun n : ℤ =>
        -(ν * a⁻¹) • UnforcedLeray.Gaussian.heatDilation a
            (UnforcedLeray.Gaussian.dilationDrift (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2) -
          ((a ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation a
            (fun y => deriv (fun u => canonMode P u y) θ) (x.1 - (n : ℝ) * c, x.2)) :=
      (hs_drift.const_smul (-(ν * a⁻¹))).sub (hs_dt.const_smul ((a ^ 2)⁻¹))
    have hs_3 : Summable (fun n : ℤ =>
        (ν * a⁻¹) • UnforcedLeray.Gaussian.heatDilation a
          (UnforcedLeray.Cyl.laplacian (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2)) :=
      hs_lap.const_smul (ν * a⁻¹)
    unfold UnforcedLeray.Gaussian.periodize
    have hν_smul : (ν : ℂ) * (P.gaugeFactor ν * ((a⁻¹ : ℝ) •
        ∑' n : ℤ, UnforcedLeray.Gaussian.heatDilation a
          (UnforcedLeray.Cyl.laplacian (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2))) =
        P.gaugeFactor ν * ∑' n : ℤ, (ν * a⁻¹) •
          UnforcedLeray.Gaussian.heatDilation a
            (UnforcedLeray.Cyl.laplacian (canonMode P θ)) (x.1 - (n : ℝ) * c, x.2) := by
      rw [(hs_lap.hasSum.const_smul (ν * a⁻¹)).tsum_eq]
      simp only [Complex.real_smul]
      push_cast; ring
    rw [hν_smul, ← mul_sub, ← (hs_12.hasSum.sub hs_3.hasSum).tsum_eq]
    rw [mul_assoc]
    congr 1
    unfold periodizeC
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    set z_n : ℝ × ℝ := (x.1 - (n : ℝ) * c, x.2)
    set y_n : ℝ × ℝ := (z_n.1 / Real.sqrt a, z_n.2 / Real.sqrt a)
    have hsm_eq : (Real.sqrt a)⁻¹ • z_n = y_n := by
      ext <;> simp [y_n, div_eq_inv_mul]
    have hpde_yn := deriv_canonMode_eq_pde hP hSmoothAll hVae hθ y_n
    have hdt_yn : deriv (fun u => canonMode P u y_n) θ =
        -(movLPlanar (canonMode P θ) y_n + (θ : ℂ)⁻¹ * movD (canonMode P θ) y_n) := by
      linear_combination -hpde_yn
    have hmovD_yn := OscillatorForceSub.movD_eq_dilationGen hΦ_c2 y_n
    have hθ_inv : (θ : ℂ)⁻¹ = (ν : ℂ) * (a : ℂ) := by
      dsimp [θ, clockTheta]
      rw [Complex.ofReal_inv, inv_inv, Complex.ofReal_mul]
    have halg : ∀ (aC νC L_y D_y Δ_y : ℂ), aC ≠ 0 →
        -(νC * aC⁻¹) * (aC⁻¹ ^ 2 * D_y) -
          (aC ^ 2)⁻¹ * (aC⁻¹ ^ 2 * -(L_y + (νC * aC) * (Δ_y + D_y))) -
          (νC * aC⁻¹) * (aC⁻¹ ^ 2 * Δ_y) =
        (aC ^ 2)⁻¹ * ((aC ^ 2)⁻¹ * L_y) := by
      intro aC νC L_y D_y Δ_y haC
      field_simp [haC]
      ring
    unfold UnforcedLeray.Gaussian.heatDilation Jscale
    rw [hsm_eq]
    dsimp only
    change -(ν * a⁻¹) • a⁻¹ ^ 2 • UnforcedLeray.Gaussian.dilationDrift (canonMode P θ) y_n -
          ((a ^ 2)⁻¹ : ℝ) • a⁻¹ ^ 2 • deriv (fun u => canonMode P u y_n) θ -
        (ν * a⁻¹) • a⁻¹ ^ 2 • UnforcedLeray.Cyl.laplacian (canonMode P θ) y_n =
      ↑(a ^ (-2 : ℝ)) * (↑(a ^ (-2 : ℝ)) * movLPlanar (canonMode P θ) y_n)
    rw [hdt_yn, hθ_inv, hmovD_yn]
    unfold UnforcedLeray.Gaussian.dilationGen
    rw [Real.rpow_neg ha.le, Real.rpow_two]
    simp only [Complex.real_smul]
    push_cast
    exact halg (a : ℂ) (ν : ℂ) (movLPlanar (canonMode P θ) y_n)
      (UnforcedLeray.Gaussian.dilationDrift (canonMode P θ) y_n)
      (UnforcedLeray.Cyl.laplacian (canonMode P θ) y_n) (Complex.ofReal_ne_zero.2 ha.ne')
  -- Now unfold `canonicalPhysResidual` and match the transport + Biot-Savart stretch pieces
  unfold canonicalPhysResidual
  set y : ℝ × ℝ := (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
  have hsq_pos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsq_ne : Real.sqrt a ≠ 0 := hsq_pos.ne'
  have hxy : (Real.sqrt a * y.1, Real.sqrt a * y.2) = x := by
    ext <;> simp [y, mul_div_cancel₀ _ hsq_ne]
  set W : ℝ × ℝ → ℂ := periodizeC d (canonMode P θ)
  have hres_sum : canonGaussRes P d θ y + canonTrainRes P tr s y =
      periodizeC d (movLPlanar (canonMode P θ)) y - movL tr s W y := by
    unfold canonGaussRes canonTrainRes
    exact sub_add_sub_cancel _ _ _
  have hj_sub : Jscale a (fun y' => canonGaussRes P d θ y' + canonTrainRes P tr s y') x =
      Jscale a (periodizeC d (movLPlanar (canonMode P θ))) x -
        ((a ^ (-2 : ℝ) : ℝ) : ℂ) * movL tr s W y := by
    unfold Jscale
    change ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (canonGaussRes P d θ y + canonTrainRes P tr s y) = _
    rw [hres_sum]
    ring
  rw [show cellLen (ν ^ (-2 : ℝ)) (clockA ν s) = d from rfl,
    show clockTheta ν s = θ from rfl, show clockA ν s = a from rfl,
    hj_sub, mul_sub, jscale_periodizeC_cellLen ha, ← hlin_part]
  -- Relate `pdCx k (canonicalPhysColumn P ν s) x` to `pdCx k W y`
  have hW_diff : Differentiable ℝ W := by
    have hd_pos : 0 < d := div_pos hc0 hsq_pos
    have hD_W : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z : ℝ × ℝ,
        ‖iteratedFDeriv ℝ k (canonMode P θ) z‖ ≤ C' * (1 + |z.1|) ^ (-(2 : ℝ)) := by
      intro k hk
      have hk' : k ≤ 2 := by exact_mod_cast hk
      refine ⟨C_tr, ?_⟩
      interval_cases k
      · simpa [norm_iteratedFDeriv_zero] using hΦ_tr0
      · intro z; rw [norm_iteratedFDeriv_one]
        refine le_trans ?_ (hΦ_tr1 z)
        nlinarith [norm_nonneg (fderiv ℝ (canonMode P θ) z), norm_nonneg z]
      · exact hΦ_tr2
    have hW_c2 : ContDiff ℝ 2 W :=
      UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (by norm_num) hd_pos.ne'
        (hΦ_c2 : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) _) hD_W
    exact hW_c2.differentiable (by norm_num)
  have hpd_w : ∀ k : Fin 2, pdCx k (canonicalPhysColumn P ν s) x =
      P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * pdCx k W y := by
    intro k
    have hw_W : canonicalPhysColumn P ν s = fun z =>
        (P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ)) *
          W ((Real.sqrt a)⁻¹ • z) := by
      funext z
      rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha z, ← jscale_periodizeC_cellLen ha]
      unfold Jscale
      rw [← mul_assoc]
      congr 2
      ext <;> simp [div_eq_inv_mul]
    have hlin_smul : HasFDerivAt (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z)
        ((Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
      (hasFDerivAt_id x).const_smul (Real.sqrt a)⁻¹
    have hcomp_W : HasFDerivAt (fun z : ℝ × ℝ => W ((Real.sqrt a)⁻¹ • z))
        ((fderiv ℝ W ((Real.sqrt a)⁻¹ • x)).comp
          ((Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
      (hW_diff ((Real.sqrt a)⁻¹ • x)).hasFDerivAt.comp x hlin_smul
    have htot_W := hcomp_W.const_mul (P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ))
    unfold pdCx
    rw [hw_W, htot_W.fderiv]
    have hx_y : (Real.sqrt a)⁻¹ • x = y := by ext <;> simp [y, div_eq_inv_mul]
    rw [hx_y]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, Complex.real_smul, smul_eq_mul]
    ring
  -- Relate `P.gaugeFactor ν * kerVelCx d W y k` to `canonicalPhysVel P ν s x k`
  have hjs_inv_w : JscaleInv a (canonicalPhysColumn P ν s) = fun z => P.gaugeFactor ν * W z := by
    funext z
    have hw_z : canonicalPhysColumn P ν s = fun u => P.gaugeFactor ν * Jscale a W u := by
      funext u
      rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha u, ← jscale_periodizeC_cellLen ha]
      rfl
    have hmul : JscaleInv a (fun u => P.gaugeFactor ν * Jscale a W u) z =
        P.gaugeFactor ν * JscaleInv a (Jscale a W) z := by
      unfold JscaleInv; ring
    rw [hw_z, hmul, jscaleInv_jscale_eq ha]
  have hvel_scale : ∀ k : Fin 2, P.gaugeFactor ν * kerVelCx d W y k =
      ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * canonicalPhysVel P ν s x k := by
    intro k
    have h1 := ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.kerVelCx_jscaleInv (c := c) ha
      (canonicalPhysColumn P ν s) y k
    rw [hjs_inv_w, hxy, ComplMildTestedSplit.kerVelCx_const_mul] at h1
    exact h1
  -- Match the exponents `-2 + (-2) + 3/2 = -2 - 1/2` and `-2 + (-2) + 3/2 + 5/2 = 0`
  have hexp_tr : (a ^ (-2 : ℝ)) * (a ^ (-2 : ℝ)) * (a ^ (3 / 2 : ℝ)) =
      (a ^ (-2 : ℝ)) * (Real.sqrt a)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ha.le, ← Real.rpow_add ha, ← Real.rpow_add ha,
      ← Real.rpow_add ha]
    norm_num
  have hexp_bs : (a ^ (-2 : ℝ)) * (a ^ (-2 : ℝ)) * (a ^ ((3 : ℝ) / 2)) * (a ^ ((5 : ℝ) / 2)) =
      1 := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha, ← Real.rpow_add ha]
    norm_num
  unfold movL movingTrainV movingTrainGradE ladTransport
  rw [show cellLen (ν ^ (-2 : ℝ)) (clockA ν s) = d from rfl,
    show clockA ν s = a from rfl, hxy, hpd_w 0, hpd_w 1]
  have hv0 := hvel_scale 0
  have hv1 := hvel_scale 1
  have htr_eq : P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
      (((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((((a ^ (3 / 2 : ℝ) * tr.v s x 0 : ℝ) : ℂ) * pdCx 0 W y +
          ((a ^ (3 / 2 : ℝ) * tr.v s x 1 : ℝ) : ℂ) * pdCx 1 W y))) =
      ((tr.v s x 0 : ℝ) : ℂ) *
          (P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
            pdCx 0 W y) +
        ((tr.v s x 1 : ℝ) : ℂ) *
          (P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
            pdCx 1 W y) := by
    have hc_tr : ((a ^ (-2 : ℝ) : ℝ) : ℂ) * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) =
        ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast hexp_tr
    simp only [Complex.ofReal_mul]
    linear_combination
      (P.gaugeFactor ν * ((tr.v s x 0 : ℝ) : ℂ) * pdCx 0 W y +
        P.gaugeFactor ν * ((tr.v s x 1 : ℝ) : ℂ) * pdCx 1 W y) * hc_tr
  have hbs_eq : P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
      (((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        (kerVelCx d W y 0 * ((a ^ ((5 : ℝ) / 2) * B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℝ) : ℂ) +
          kerVelCx d W y 1 * ((a ^ ((5 : ℝ) / 2) * B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℝ) : ℂ))) =
      canonicalPhysVel P ν s x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
        canonicalPhysVel P ν s x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ) := by
    have hc_bs : ((a ^ (-2 : ℝ) : ℝ) : ℂ) * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * ((a ^ ((5 : ℝ) / 2) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hexp_bs
    simp only [Complex.ofReal_mul]
    linear_combination
      (((a ^ (-2 : ℝ) : ℝ) : ℂ) * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((a ^ ((5 : ℝ) / 2) : ℝ) : ℂ) * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) * hv0 +
      (((a ^ (-2 : ℝ) : ℝ) : ℂ) * ((a ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((a ^ ((5 : ℝ) / 2) : ℝ) : ℂ) * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) * hv1 +
      (canonicalPhysVel P ν s x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
        canonicalPhysVel P ν s x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) * hc_bs
  linear_combination htr_eq + hbs_eq

/-! ## 5. Exponential-tail `X_{m,c}` bounds, Biot-Savart, and continuity helpers -/

private theorem exp_sq_le_exp_abs {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    Real.exp (-β * u ^ 2) ≤ Real.exp β * Real.exp (-β * |u|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hsq : |u| - 1 ≤ u ^ 2 := by
    have h0 : 0 ≤ (|u| - 1) ^ 2 := sq_nonneg (|u| - 1)
    have h1 : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [abs_nonneg u]
  nlinarith

private theorem memLp_of_exp_eta {c m α M : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (hα : 0 < α) (hM : 0 ≤ M) {g : ℝ × ℝ → ℂ}
    (hg_sm : AEStronglyMeasurable g (B0579.cellMeasure c m))
    (hg_bd : ∀ x ∈ B0579.cell c, ‖g x‖ ≤ M * Real.exp (-α * |x.2|)) :
    MemLp g 2 (B0579.cellMeasure c m) := by
  obtain ⟨K_p, _, hKp⟩ := EulerErrorSub.xNorm_le_of_jb_pow hm
  set k_w : ℕ := Nat.ceil m + 2
  set C_e : ℝ := (2 : ℝ) ^ (2 * k_w) * (1 + (((2 * k_w).factorial : ℝ) / α ^ (2 * k_w)))
  have hCe_nn : 0 ≤ C_e := by dsimp [C_e]; positivity
  have hexp_pow : ∀ u : ℝ, 0 ≤ u → (1 + u) ^ (2 * k_w) * Real.exp (-α * u) ≤ C_e := by
    intro u hu
    by_cases hu1 : u ≤ 1
    · have hp : (1 + u) ^ (2 * k_w) ≤ (2 : ℝ) ^ (2 * k_w) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (2 * k_w)
      have hexp : Real.exp (-α * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc (1 + u) ^ (2 * k_w) * Real.exp (-α * u)
          ≤ (2 : ℝ) ^ (2 * k_w) * 1 := mul_le_mul hp hexp (Real.exp_nonneg _) (by positivity)
        _ ≤ C_e := by
            dsimp [C_e]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have : 0 ≤ ((2 * k_w).factorial : ℝ) / α ^ (2 * k_w) := by positivity
            linarith
    · have hu1' : 1 < u := lt_of_not_ge hu1
      have hp : (1 + u) ^ (2 * k_w) ≤ (2 : ℝ) ^ (2 * k_w) * u ^ (2 * k_w) := by
        calc (1 + u) ^ (2 * k_w) ≤ (2 * u) ^ (2 * k_w) :=
              pow_le_pow_left₀ (by positivity) (by linarith) (2 * k_w)
          _ = (2 : ℝ) ^ (2 * k_w) * u ^ (2 * k_w) := mul_pow 2 u (2 * k_w)
      have hexp_eq : Real.exp (-α * u) = Real.exp (-(α * u)) := by congr 1; ring
      have hpe := pow_mul_exp_neg_le (2 * k_w) hα hu
      calc (1 + u) ^ (2 * k_w) * Real.exp (-α * u)
          ≤ ((2 : ℝ) ^ (2 * k_w) * u ^ (2 * k_w)) * Real.exp (-(α * u)) := by
            rw [← hexp_eq]; exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
        _ = (2 : ℝ) ^ (2 * k_w) * (u ^ (2 * k_w) * Real.exp (-(α * u))) := by ring
        _ ≤ (2 : ℝ) ^ (2 * k_w) * (((2 * k_w).factorial : ℝ) / α ^ (2 * k_w)) :=
            mul_le_mul_of_nonneg_left hpe (by positivity)
        _ ≤ C_e := by
            dsimp [C_e]
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  set M_jb : ℝ := M * (1 + (c / 2) ^ 2) ^ k_w * C_e
  have hMjb_nn : 0 ≤ M_jb := by dsimp [M_jb]; positivity
  have hjb_bd : ∀ x ∈ B0579.cell c, B0579.jb x ^ k_w * ‖g x‖ ≤ M_jb := by
    intro x hx
    have hx1_sq : x.1 ^ 2 ≤ (c / 2) ^ 2 := by
      have h1 : -(c / 2) ≤ x.1 := hx.1.1
      have h2 : x.1 < c / 2 := hx.1.2
      nlinarith
    have hjb_le : B0579.jb x ≤ (1 + (c / 2) ^ 2) * (1 + |x.2|) ^ 2 := by
      unfold B0579.jb
      have h2 : x.2 ^ 2 = |x.2| ^ 2 := (sq_abs x.2).symm
      nlinarith [abs_nonneg x.2, sq_nonneg (c / 2), mul_nonneg (sq_nonneg (c / 2)) (abs_nonneg x.2),
        mul_nonneg (sq_nonneg (c / 2)) (sq_nonneg |x.2|)]
    have hjb_pow : B0579.jb x ^ k_w ≤ (1 + (c / 2) ^ 2) ^ k_w * (1 + |x.2|) ^ (2 * k_w) := by
      calc B0579.jb x ^ k_w ≤ ((1 + (c / 2) ^ 2) * (1 + |x.2|) ^ 2) ^ k_w :=
            pow_le_pow_left₀ (B0579.jb_pos x).le hjb_le k_w
        _ = (1 + (c / 2) ^ 2) ^ k_w * (1 + |x.2|) ^ (2 * k_w) := by
            rw [mul_pow, ← pow_mul]
    calc B0579.jb x ^ k_w * ‖g x‖
        ≤ ((1 + (c / 2) ^ 2) ^ k_w * (1 + |x.2|) ^ (2 * k_w)) * (M * Real.exp (-α * |x.2|)) :=
          mul_le_mul hjb_pow (hg_bd x hx) (norm_nonneg _) (by positivity)
      _ = M * (1 + (c / 2) ^ 2) ^ k_w * ((1 + |x.2|) ^ (2 * k_w) * Real.exp (-α * |x.2|)) := by ring
      _ ≤ M * (1 + (c / 2) ^ 2) ^ k_w * C_e :=
          mul_le_mul_of_nonneg_left (hexp_pow |x.2| (abs_nonneg x.2)) (by positivity)
      _ = M_jb := rfl
  have hx := hKp c M_jb g hMjb_nn hjb_bd
  exact ⟨hg_sm, hx.trans_lt ENNReal.ofReal_lt_top⟩

private theorem tendsto_xNorm_of_exp_eta {c m α M : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (hα : 0 < α) (hM : 0 ≤ M) {I : Set ℝ} {s : ℝ} (hs : s ∈ I)
    {G : ℝ → ℝ × ℝ → ℂ}
    (hG_sm : ∀ τ ∈ I, AEStronglyMeasurable (G τ) (B0579.cellMeasure c m))
    (hG_bd : ∀ τ ∈ I, ∀ x ∈ B0579.cell c, ‖G τ x‖ ≤ M * Real.exp (-α * |x.2|))
    (hG_cont : ∀ x ∈ B0579.cell c, ContinuousWithinAt (fun τ => G τ x) I s) :
    Tendsto (fun s' => xNorm c m (G s' - G s)) (𝓝[I] s) (𝓝 0) := by
  let μ : Measure (ℝ × ℝ) := B0579.cellMeasure c m
  have hae_cell : ∀ {Q : ℝ × ℝ → Prop}, (∀ x ∈ B0579.cell c, Q x) → ∀ᵐ x ∂μ, Q x := fun hQ =>
    (withDensity_absolutelyContinuous (volume.restrict (B0579.cell c)) _).ae_le
      ((ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Eventually.of_forall hQ))
  let g_dom : ℝ × ℝ → ℂ := fun x => (((2 * M) * Real.exp (-α * |x.2|) : ℝ) : ℂ)
  have hg_dom_cont : Continuous g_dom :=
    Complex.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_snd.abs)))
  have hg_dom_mem : MemLp g_dom 2 μ :=
    memLp_of_exp_eta hc hm hα (by positivity : 0 ≤ 2 * M) hg_dom_cont.aestronglyMeasurable
      fun x _ => by
        dsimp [g_dom]
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hdom_int : Integrable (fun x => ‖g_dom x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg_dom_cont.aestronglyMeasurable).1 hg_dom_mem
  have htend_int : Tendsto (fun s' => ∫ x, ‖G s' x - G s x‖ ^ 2 ∂μ) (𝓝[I] s) (𝓝 0) := by
    rw [show (0 : ℝ) = ∫ _x, (0 : ℝ) ∂μ from (MeasureTheory.integral_zero (ℝ × ℝ) ℝ).symm]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖g_dom x‖ ^ 2) ?_ ?_
      hdom_int ?_
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      exact (((hG_sm s' hs').sub (hG_sm s hs)).norm.pow 2)
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      refine hae_cell fun x hx => ?_
      have htri : ‖G s' x - G s x‖ ≤ ‖g_dom x‖ := by
        dsimp [g_dom]
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        calc ‖G s' x - G s x‖ ≤ ‖G s' x‖ + ‖G s x‖ := norm_sub_le _ _
          _ ≤ M * Real.exp (-α * |x.2|) + M * Real.exp (-α * |x.2|) :=
              add_le_add (hG_bd s' hs' x hx) (hG_bd s hs x hx)
          _ = 2 * M * Real.exp (-α * |x.2|) := by ring
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    · refine hae_cell fun x hx => ?_
      have hsub : Tendsto (fun s' => G s' x - G s x) (𝓝[I] s) (𝓝 (G s x - G s x)) :=
        (hG_cont x hx).sub continuousWithinAt_const
      rw [sub_self] at hsub
      simpa using (hsub.norm.pow 2)
  have hcont_enn : Tendsto (fun u : ℝ => (ENNReal.ofReal u) ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have h1 := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto (ENNReal.ofReal 0)
    have h2 := ENNReal.continuous_ofReal.tendsto 0
    simpa [Function.comp_def, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h1.comp h2
  refine (hcont_enn.comp htend_int).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s' hs'
  dsimp [Function.comp_def]
  have hmem_diff : MemLp (G s' - G s) 2 μ :=
    (memLp_of_exp_eta hc hm hα hM (hG_sm s' hs') (hG_bd s' hs')).sub
      (memLp_of_exp_eta hc hm hα hM (hG_sm s hs) (hG_bd s hs))
  have hint_sq : Integrable (fun x => ‖(G s' - G s) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm ((hG_sm s' hs').sub (hG_sm s hs))).1 hmem_diff
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have h_lint : (∫⁻ x, ‖(G s' - G s) x‖ₑ ^ (2 : ℝ) ∂μ) =
      ENNReal.ofReal (∫ x, ‖G s' x - G s x‖ ^ 2 ∂μ) := by
    have hint_sq' : Integrable (fun x => ‖G s' x - G s x‖ ^ 2) μ := hint_sq
    rw [ofReal_integral_eq_lintegral_ofReal hint_sq' (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    change ‖G s' x - G s x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖G s' x - G s x‖ ^ 2)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]
  rw [h_lint]

private theorem exp_div_eight_split (y : ℝ × ℝ) :
    Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
      16 * (1 + |y.1|) ^ (-(2 : ℝ)) * Real.exp (-(y.2 ^ 2) / 8) := by
  have hsplit : -(y.1 ^ 2 + y.2 ^ 2) / 8 = -((y.1 ^ 2 + (0 : ℝ) ^ 2)) / 8 + (-(y.2 ^ 2) / 8) := by
    ring
  rw [hsplit, Real.exp_add]
  exact mul_le_mul_of_nonneg_right (FrameCont.exp_le_translate_weight y.1 0) (Real.exp_nonneg _)

private theorem exp_div_sixteen_split (y : ℝ × ℝ) :
    Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) ≤
      64 * (1 + |y.1|) ^ (-(2 : ℝ)) * Real.exp (-(y.2 ^ 2) / 16) := by
  have hsplit : -(y.1 ^ 2 + y.2 ^ 2) / 16 = -(y.1 ^ 2 / 16) + (-(y.2 ^ 2) / 16) := by ring
  rw [hsplit, Real.exp_add]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  have hpos : 0 < (1 + |y.1|) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |y.1|), Real.rpow_two, ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  by_cases hy1 : |y.1| ≤ 1
  · calc Real.exp (-(y.1 ^ 2 / 16)) * (1 + |y.1|) ^ 2
        ≤ 1 * (2 : ℝ) ^ 2 := mul_le_mul
            (Real.exp_le_one_iff.2 (by have := sq_nonneg y.1; linarith))
            (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity) zero_le_one
      _ ≤ 64 := by norm_num
  · have hy1' : 1 < |y.1| := lt_of_not_ge hy1
    have hp : (1 + |y.1|) ^ 2 ≤ 4 * y.1 ^ 2 := by
      calc (1 + |y.1|) ^ 2 ≤ (|y.1| + |y.1|) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith [hy1']) 2
        _ = 4 * |y.1| ^ 2 := by ring
        _ = 4 * y.1 ^ 2 := by rw [sq_abs]
    have hpe := pow_mul_exp_neg_le 1 (β := 1 / 16) (u := y.1 ^ 2) (by norm_num) (sq_nonneg y.1)
    have heq : Real.exp (-(y.1 ^ 2 / 16)) = Real.exp (-((1 / 16 : ℝ) * y.1 ^ 2)) := by
      congr 1; ring
    rw [heq]
    norm_num at hpe
    calc Real.exp (-((1 / 16 : ℝ) * y.1 ^ 2)) * (1 + |y.1|) ^ 2
        ≤ Real.exp (-((1 / 16 : ℝ) * y.1 ^ 2)) * (4 * y.1 ^ 2) :=
          mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
      _ = 4 * (y.1 ^ 2 * Real.exp (-((1 / 16 : ℝ) * y.1 ^ 2))) := by ring
      _ ≤ 4 * 16 := mul_le_mul_of_nonneg_left hpe (by norm_num)
      _ ≤ 64 := by norm_num

private theorem continuous_iteratedFDeriv_slice {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF_sm : ContDiff ℝ ∞ F) (m : ℕ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ m (fun z => F (p.1, z)) p.2) := by
  let inrL : ℝ × ℝ →L[ℝ] ℝ × (ℝ × ℝ) := ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
  have heq : (fun p : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ m (fun z => F (p.1, z)) p.2) =
      fun p => (iteratedFDeriv ℝ m F p).compContinuousLinearMap (fun _ => inrL) := by
    funext ⟨t, y⟩
    dsimp only
    have hfn : (fun z : ℝ × ℝ => F (t, z)) =
        ((fun q : ℝ × (ℝ × ℝ) => F ((t, (0 : ℝ × ℝ)) + q)) ∘ inrL) := by
      funext z; simp [inrL]
    have hG : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => F ((t, (0 : ℝ × ℝ)) + q)) :=
      hF_sm.comp (contDiff_const.add contDiff_id)
    rw [hfn, inrL.iteratedFDeriv_comp_right hG y (by exact_mod_cast le_top)]
    congr 1
    have hadd := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) m (t, (0 : ℝ × ℝ)) (inrL y)
    simpa [inrL] using hadd
  rw [heq]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => inrL)).continuous.comp
    (hF_sm.continuous_iteratedFDeriv (by simp))

private theorem continuous_dt_slice {F : ℝ × (ℝ × ℝ) → ℂ} (hF_sm : ContDiff ℝ ∞ F) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => deriv (fun u => F (u, p.2)) p.1) := by
  have heq : (fun p : ℝ × (ℝ × ℝ) => deriv (fun u => F (u, p.2)) p.1) =
      fun p => fderiv ℝ F p (1, (0 : ℝ × ℝ)) := by
    funext ⟨t, y⟩
    have hd : HasDerivAt (fun u => F (u, y)) (fderiv ℝ F (t, y) (1, (0 : ℝ × ℝ))) t :=
      (hF_sm.differentiable (by simp) (t, y)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact hd.deriv
  rw [heq]
  exact ((ContinuousLinearMap.apply ℝ ℂ (1, (0 : ℝ × ℝ))).continuous).comp
    (hF_sm.continuous_fderiv (by simp))

private theorem norm_dilationDrift_gauss_le {F : ℝ × (ℝ × ℝ) → ℂ} {t Bmax : ℝ} {y : ℝ × ℝ}
    (hBm0 : 0 ≤ Bmax)
    (h0 : ‖F (t, y)‖ ≤ Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))
    (h1 : ‖fderiv ℝ (fun z => F (t, z)) y‖ ≤ Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ‖UnforcedLeray.Gaussian.dilationDrift (fun z => F (t, z)) y‖ ≤
      (11 * Bmax) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
  unfold UnforcedLeray.Gaussian.dilationDrift
  have hy_exp : ‖y‖ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
      16 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    set u : ℝ := y.1 ^ 2 + y.2 ^ 2
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hnsq : ‖y‖ ^ 2 ≤ u := by
      have hmax : ‖y‖ = max |y.1| |y.2| := rfl
      rw [hmax]
      rcases max_cases |y.1| |y.2| with ⟨hm1, _⟩ | ⟨hm2, _⟩
      · rw [hm1, sq_abs]; dsimp [u]; linarith [sq_nonneg y.2]
      · rw [hm2, sq_abs]; dsimp [u]; linarith [sq_nonneg y.1]
    have hy_le : ‖y‖ ≤ 1 + u / 4 := by nlinarith [sq_nonneg (‖y‖ - 2)]
    have hsplit : -u / 8 = -(u / 16) + (-((1 / 16 : ℝ) * u)) := by ring
    have hu_exp : (1 + u / 4) * Real.exp (-((1 / 16 : ℝ) * u)) ≤ 16 := by
      have h1e : Real.exp (-((1 / 16 : ℝ) * u)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have hpe := pow_mul_exp_neg_le 1 (β := 1 / 16) (u := u) (by norm_num) hu0
      norm_num at hpe
      nlinarith [Real.exp_nonneg (-((1 / 16 : ℝ) * u))]
    calc ‖y‖ * Real.exp (-u / 8)
        ≤ (1 + u / 4) * (Real.exp (-(u / 16)) * Real.exp (-((1 / 16 : ℝ) * u))) := by
          rw [hsplit, Real.exp_add]
          exact mul_le_mul_of_nonneg_right hy_le (by positivity)
      _ = ((1 + u / 4) * Real.exp (-((1 / 16 : ℝ) * u))) * Real.exp (-u / 16) := by ring
      _ ≤ 16 * Real.exp (-u / 16) := mul_le_mul_of_nonneg_right hu_exp (Real.exp_nonneg _)
  have h_first : ‖(2 : ℝ) • F (t, y)‖ ≤ 3 * Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    have hexp16 : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
        Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg y.1, sq_nonneg y.2])
    nlinarith [hBm0, Real.exp_nonneg (-(y.1 ^ 2 + y.2 ^ 2) / 16)]
  have h_second : ‖(1 / 2 : ℝ) • fderiv ℝ (fun z => F (t, z)) y y‖ ≤
      8 * Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    have hop := (fderiv ℝ (fun z => F (t, z)) y).le_opNorm y
    calc (1 / 2 : ℝ) * ‖fderiv ℝ (fun z => F (t, z)) y y‖
        ≤ (1 / 2 : ℝ) * (Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) * ‖y‖) :=
          mul_le_mul_of_nonneg_left
            (hop.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg y))) (by norm_num)
      _ = (1 / 2 : ℝ) * Bmax * (‖y‖ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) := by ring
      _ ≤ (1 / 2 : ℝ) * Bmax * (16 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) :=
          mul_le_mul_of_nonneg_left hy_exp (by positivity)
      _ = 8 * Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by ring
  exact (norm_add_le _ _).trans (by linarith)

private theorem continuous_dilationDrift_slice {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF_sm : ContDiff ℝ ∞ F) :
    Continuous (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.Gaussian.dilationDrift (fun y => F (p.1, y)) p.2) := by
  unfold UnforcedLeray.Gaussian.dilationDrift
  have hf1_c : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun y => F (p.1, y)) p.2 p.2) := by
    have heq : (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y => F (p.1, y)) p.2 p.2) =
        fun p => fderiv ℝ F p ((0 : ℝ), p.2) := by
      funext ⟨t, y⟩
      have hd : HasFDerivAt (fun z : ℝ × ℝ => F (t, z))
          ((fderiv ℝ F (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y :=
        ((hF_sm.differentiable (by simp) (t, y)).hasFDerivAt.comp y
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)).congr_of_eventuallyEq
          (Eventually.of_forall fun _ => rfl)
      rw [hd.fderiv]
      rfl
    rw [heq]
    have hc0 : Continuous (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)) := continuous_const
    exact (hF_sm.continuous_fderiv (by simp)).clm_apply (hc0.prodMk continuous_snd)
  exact (hF_sm.continuous.const_smul (2 : ℝ)).add (hf1_c.const_smul (1 / 2 : ℝ))

private theorem ladLapCx_eq_iteratedFDeriv_two {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (x : ℝ × ℝ) :
    ladLapCx g x =
      iteratedFDeriv ℝ 2 g x ![(1, 0), (1, 0)] +
        iteratedFDeriv ℝ 2 g x ![(0, 1), (0, 1)] := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have h11 : ContDiff ℝ (1 + 1) g := hg.of_le (by simp)
  have hdQ := (UnforcedLeray.Cyl.contDiff_partialQ h11).differentiable (by norm_num)
  have hdE := (UnforcedLeray.Cyl.contDiff_partialEta h11).differentiable (by norm_num)
  have hpQ : UnforcedLeray.Cyl.partialQ g = pdCx 0 g :=
    funext fun z => UnforcedLeray.Cyl.partialQ_eq_fderiv hd z
  have hpE : UnforcedLeray.Cyl.partialEta g = pdCx 1 g :=
    funext fun z => UnforcedLeray.Cyl.partialEta_eq_fderiv hd z
  rw [← UnforcedLeray.Gaussian.laplacian_eq_iteratedFDeriv (hg.of_le (by simp)) x]
  unfold UnforcedLeray.Cyl.laplacian ladLapCx
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hdQ x,
    UnforcedLeray.Cyl.partialEta_eq_fderiv hdE x, hpQ, hpE]
  rfl

private theorem norm_ladLapCx_le_two_iteratedFDeriv {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (x : ℝ × ℝ) :
    ‖ladLapCx g x‖ ≤ ‖iteratedFDeriv ℝ 2 g x‖ + ‖iteratedFDeriv ℝ 2 g x‖ := by
  rw [ladLapCx_eq_iteratedFDeriv_two hg x]
  have hv1 : ∀ i : Fin 2, ‖(![(1, (0 : ℝ)), (1, 0)] : Fin 2 → ℝ × ℝ) i‖ ≤ 1 := by
    intro i; fin_cases i <;> simp
  have hv2 : ∀ i : Fin 2, ‖(![((0 : ℝ), 1), (0, 1)] : Fin 2 → ℝ × ℝ) i‖ ≤ 1 := by
    intro i; fin_cases i <;> simp
  have hev1 : ‖iteratedFDeriv ℝ 2 g x ![(1, 0), (1, 0)]‖ ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
    refine ((iteratedFDeriv ℝ 2 g x).le_opNorm _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ 2 g x‖ * ∏ _i : Fin 2, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hv1 i) (norm_nonneg _)
      _ = _ := by simp
  have hev2 : ‖iteratedFDeriv ℝ 2 g x ![(0, 1), (0, 1)]‖ ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
    refine ((iteratedFDeriv ℝ 2 g x).le_opNorm _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ 2 g x‖ * ∏ _i : Fin 2, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hv2 i) (norm_nonneg _)
      _ = _ := by simp
  exact (norm_add_le _ _).trans (add_le_add hev1 hev2)

/-- Spatial half of `canonicalPhysColumn_window_props`: `ContDiff ℝ ∞`, `c`-periodicity, Gaussian
`η`-decay up to order `2`, and `τ`-continuity of `w`, `pdCx k w`, and `ladLapCx w` on `U`. -/
private theorem canonicalPhysColumn_window_spatial {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {ν T : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hT0 : 0 ≤ T) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let U : Set ℝ := Ioo (-(1 / (4 * ν))) (T + 1 / 2)
    let β : ℝ := 1 / (16 * clockA ν (T + 1))
    ∃ M_sp : ℝ, 0 < M_sp ∧ 0 < β ∧
      (∀ τ ∈ U, ContDiff ℝ ∞ (canonicalPhysColumn P ν τ)) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        canonicalPhysColumn P ν τ (x.1 + c, x.2) = canonicalPhysColumn P ν τ x) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        ‖canonicalPhysColumn P ν τ x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2) ∧
        (∀ k : Fin 2, ‖pdCx k (canonicalPhysColumn P ν τ) x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2)) ∧
        (‖ladLapCx (canonicalPhysColumn P ν τ) x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2) ∧
          ‖iteratedFDeriv ℝ 2 (canonicalPhysColumn P ν τ) x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2))) ∧
      (∀ x : ℝ × ℝ,
        ContinuousOn (fun τ => canonicalPhysColumn P ν τ x) U ∧
        (∀ k : Fin 2, ContinuousOn (fun τ => pdCx k (canonicalPhysColumn P ν τ) x) U) ∧
        ContinuousOn (fun τ => ladLapCx (canonicalPhysColumn P ν τ) x) U) := by
  intro c U β
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hc_ne : c ≠ 0 := hc0.ne'
  set s_lo : ℝ := -(1 / (2 * ν))
  set s_hi : ℝ := T + 1
  have hU_sub : U ⊆ Ioo s_lo s_hi := fun r hr => by
    dsimp [U, s_lo, s_hi] at hr ⊢
    have h4 : 1 / (4 * ν) < 1 / (2 * ν) :=
      div_lt_div_of_pos_left zero_lt_one (by positivity) (by linarith)
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have ha_hi : 1 < clockA ν s_hi := by dsimp [clockA, s_hi]; nlinarith
  set a_max : ℝ := clockA ν s_hi
  have hamax_pos : 0 < a_max := lt_trans zero_lt_one ha_hi
  have hβ_def : β = 1 / (16 * a_max) := rfl
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  set θ_lo : ℝ := (ν * a_max)⁻¹
  set θ_hi : ℝ := (ν * (1 / 2 : ℝ))⁻¹
  have hθ_lo_pos : 0 < θ_lo := inv_pos.2 (mul_pos hν hamax_pos)
  have hθ_le : θ_lo ≤ θ_hi := inv_anti₀ (by positivity) (by nlinarith)
  obtain ⟨_, _, ⟨F, hF_sm, hF_eq, hF_bd⟩⟩ :=
    canonMode_window_jet_and_smooth hP hSmoothAll hVae hθ_lo_pos hθ_le
  have ha_bounds : ∀ r ∈ Ioo s_lo s_hi, 1 / 2 < clockA ν r ∧ clockA ν r < a_max := by
    intro r hr
    constructor
    · dsimp [clockA, s_lo] at hr ⊢
      have := mul_lt_mul_of_pos_left hr.1 hν
      field_simp [hν.ne'] at this; linarith
    · dsimp [a_max, clockA]; nlinarith [hr.2]
  have hθ_in_win : ∀ r ∈ Ioo s_lo s_hi,
      clockTheta ν r ∈ Ioo (θ_lo - θ_lo / 4) (θ_hi + θ_lo / 4) := by
    intro r hr
    obtain ⟨hb_lo, hb_hi⟩ := ha_bounds r hr
    have hbr_pos : 0 < clockA ν r := by linarith
    have ht_lo : θ_lo < clockTheta ν r :=
      inv_strictAnti₀ (mul_pos hν hbr_pos) (mul_lt_mul_of_pos_left hb_hi hν)
    have ht_hi : clockTheta ν r < θ_hi :=
      inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hb_lo hν)
    exact ⟨by linarith, by linarith⟩
  have hw_sm_all : ∀ τ ∈ Ioo s_lo s_hi, ContDiff ℝ ∞ (canonicalPhysColumn P ν τ) := by
    intro τ hτ
    obtain ⟨hb_lo, _⟩ := ha_bounds τ hτ
    have ha : 0 < clockA ν τ := by linarith
    have hθ : 0 < clockTheta ν τ := inv_pos.2 (mul_pos hν ha)
    have hΦ_sm : ContDiff ℝ ∞ (canonMode P (clockTheta ν τ)) :=
      contDiff_canonMode_slice hP hSmoothAll hVae hθ
    have hw_eq : canonicalPhysColumn P ν τ = fun z =>
        P.gaugeFactor ν * UnforcedLeray.Gaussian.periodize c
          (UnforcedLeray.Gaussian.heatDilation (clockA ν τ) (canonMode P (clockTheta ν τ))) z := by
      funext z
      rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha z]
      congr 1
      unfold periodizeC UnforcedLeray.Gaussian.periodize
      exact tsum_congr fun n => jscale_eq_heatDilation ha _ _
    rw [hw_eq]
    refine contDiff_const.mul (contDiff_infty.2 fun N => ?_)
    refine UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (by norm_num) hc_ne
      (UnforcedLeray.Gaussian.contDiff_heatDilation
        (hΦ_sm.of_le (by simp) : ContDiff ℝ N _) (clockA ν τ)) ?_
    intro k _
    obtain ⟨Bk, hBk0, hBk⟩ := hF_bd k
    have hqk : ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ k (canonMode P (clockTheta ν τ)) y‖ ≤
        (16 * Bk) * (1 + |y.1|) ^ (-(2 : ℝ)) := by
      intro y
      have hslice : canonMode P (clockTheta ν τ) = fun z => F (clockTheta ν τ, z) :=
        funext fun z => (hF_eq (clockTheta ν τ, z) (hθ_in_win τ hτ)).symm
      rw [hslice]
      calc ‖iteratedFDeriv ℝ k (fun z => F (clockTheta ν τ, z)) y‖
          ≤ Bk * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := (hBk (clockTheta ν τ) y).1
        _ ≤ Bk * (16 * (1 + |y.1|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (FrameCont.exp_le_translate_weight y.1 y.2) hBk0.le
        _ = (16 * Bk) * (1 + |y.1|) ^ (-(2 : ℝ)) := by ring
    exact ⟨_, UnforcedLeray.Gaussian.norm_iteratedFDeriv_heatDilation_le (by norm_num) ha k hqk⟩
  have hw_per_all : ∀ τ ∈ Ioo s_lo s_hi, ∀ x : ℝ × ℝ,
      canonicalPhysColumn P ν τ (x.1 + c, x.2) = canonicalPhysColumn P ν τ x := by
    intro τ hτ x
    have ha : 0 < clockA ν τ := by linarith [(ha_bounds τ hτ).1]
    rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha (x.1 + c, x.2),
      canonicalPhysColumn_eq_periodizeC_planar P hν ha x, periodizeC_periodic]
  obtain ⟨S_lat, hSlat_pos, hSlat⟩ := tsum_translate_sq_le_unif
  set r₀ : ℝ := (Real.sqrt a_max)⁻¹
  have hr₀_pos : 0 < r₀ := inv_pos.2 (Real.sqrt_pos.2 hamax_pos)
  obtain ⟨B₀, hB₀_pos, hB₀⟩ := hF_bd 0
  obtain ⟨B₁, hB₁_pos, hB₁⟩ := hF_bd 1
  obtain ⟨B₂, hB₂_pos, hB₂⟩ := hF_bd 2
  let B : Fin 3 → ℝ := ![B₀, B₁, B₂]
  have hB0 : ∀ m : Fin 3, 0 < B m := fun m => by
    fin_cases m <;> dsimp [B] <;> assumption
  have hB : ∀ (m : Fin 3) (θ : ℝ) (y : ℝ × ℝ),
      ‖iteratedFDeriv ℝ m.1 (fun z => F (θ, z)) y‖ ≤
        B m * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := fun m θ y => by
    fin_cases m <;> dsimp [B]
    · exact (hB₀ θ y).1
    · exact (hB₁ θ y).1
    · exact (hB₂ θ y).1
  set Bmax : ℝ := max (B 0) (max (B 1) (B 2))
  have hBm0 : 0 < Bmax := lt_of_lt_of_le (hB0 0) (le_max_left _ _)
  have hexp_split : ∀ y : ℝ × ℝ, Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) ≤
      16 * (1 + |y.1|) ^ (-(2 : ℝ)) * Real.exp (-(y.2 ^ 2) / 8) := exp_div_eight_split
  have hexp_eta_dil : ∀ {b : ℝ}, 0 < b → b ≤ a_max → ∀ z : ℝ × ℝ,
      Real.exp (-(((Real.sqrt b)⁻¹ • z).2 ^ 2) / 8) ≤ Real.exp (-β * z.2 ^ 2) := by
    intro b hb0 hb_le z
    refine Real.exp_le_exp.2 ?_
    have hy2 : ((Real.sqrt b)⁻¹ • z).2 ^ 2 = z.2 ^ 2 / b := by
      dsimp
      rw [mul_pow, inv_pow, Real.sq_sqrt hb0.le, div_eq_inv_mul]
    rw [hy2]
    have hdiv : z.2 ^ 2 / (16 * a_max) ≤ z.2 ^ 2 / b / 8 := by
      rw [div_div]
      refine div_le_div_of_nonneg_left (sq_nonneg z.2) (by positivity) (by linarith)
    have hβz : -β * z.2 ^ 2 = -(z.2 ^ 2 / (16 * a_max)) := by
      rw [hβ_def, neg_mul, one_div_mul_eq_div]
    rw [hβz, neg_div]
    exact neg_le_neg hdiv
  have hit_F_cont : ∀ m : ℕ, Continuous
      (fun p : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ m (fun z => F (p.1, z)) p.2) :=
    continuous_iteratedFDeriv_slice hF_sm
  set K_sp : ℝ := (2 : ℝ) ^ 2 * (2 : ℝ) ^ 2 * (16 * Bmax * (min 1 r₀) ^ (-(2 : ℝ)))
  have hKsp_pos : 0 < K_sp := by dsimp [K_sp]; positivity
  have hsp_atom_bd : ∀ (m : Fin 3) (n : ℤ) (r : ℝ), r ∈ Ioo s_lo s_hi → ∀ x : ℝ × ℝ,
      ‖((clockA ν r)⁻¹ ^ 2 * (Real.sqrt (clockA ν r))⁻¹ ^ m.1) •
        iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν r, z))
          ((Real.sqrt (clockA ν r))⁻¹ • (x - UnforcedLeray.Gaussian.shiftVec c n))‖ ≤
        K_sp * Real.exp (-β * x.2 ^ 2) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
    intro m n r hr x
    set b : ℝ := clockA ν r
    obtain ⟨hb_lo, hb_hi⟩ := ha_bounds r hr
    have hb0 : 0 < b := by linarith
    have hbinv : b⁻¹ ≤ 2 := by
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hb_lo.le
      norm_num at h; exact h
    have hsq_inv : (Real.sqrt b)⁻¹ ≤ 2 := by
      have hsq : (1 / 2 : ℝ) ≤ Real.sqrt b := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsq
      norm_num at h; exact h
    have hm_pow : (Real.sqrt b)⁻¹ ^ m.1 ≤ (2 : ℝ) ^ 2 := by
      fin_cases m <;> dsimp
      · norm_num
      · nlinarith [inv_nonneg.2 (Real.sqrt_nonneg b)]
      · exact pow_le_pow_left₀ (inv_nonneg.2 (Real.sqrt_nonneg b)) hsq_inv 2
    have hb_pow : b⁻¹ ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hb0.le) hbinv 2
    have hrb : r₀ ≤ (Real.sqrt b)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt hb_hi.le)
    set z_n : ℝ × ℝ := x - UnforcedLeray.Gaussian.shiftVec c n
    have hzn1 : z_n.1 = x.1 - (n : ℝ) * c := by simp [z_n, UnforcedLeray.Gaussian.shiftVec]
    have hzn2 : z_n.2 = x.2 := by simp [z_n, UnforcedLeray.Gaussian.shiftVec]
    have hBm_le : B m ≤ Bmax := by
      fin_cases m
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    set y_n : ℝ × ℝ := (Real.sqrt b)⁻¹ • z_n
    have h1 := (hB m (clockTheta ν r) y_n).trans
      (mul_le_mul_of_nonneg_right hBm_le (Real.exp_nonneg _))
    have h2 := (hexp_split y_n).trans
      (mul_le_mul_of_nonneg_left (hexp_eta_dil hb0 hb_hi.le z_n) (by positivity))
    have htr_1d : 16 * (1 + |y_n.1|) ^ (-(2 : ℝ)) ≤
        16 * (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |z_n.1|) ^ (-(2 : ℝ)) := by
      have h := UnforcedLeray.Gaussian.one_add_abs_mul_rpow_neg_le (s := 2)
        (by norm_num) hr₀_pos hrb z_n.1
      have hy1 : y_n.1 = (Real.sqrt b)⁻¹ * z_n.1 := rfl
      rw [hy1]
      nlinarith
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hpref : b⁻¹ ^ 2 * (Real.sqrt b)⁻¹ ^ m.1 ≤ (2 : ℝ) ^ 2 * (2 : ℝ) ^ 2 :=
      mul_le_mul hb_pow hm_pow (by positivity) (by positivity)
    have hval : ‖iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν r, z)) y_n‖ ≤
        (16 * Bmax * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
          (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
      calc ‖iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν r, z)) y_n‖
          ≤ Bmax * (16 * (1 + |y_n.1|) ^ (-(2 : ℝ)) * Real.exp (-β * z_n.2 ^ 2)) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hBm0.le)
        _ ≤ Bmax * ((16 * (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |z_n.1|) ^ (-(2 : ℝ))) *
              Real.exp (-β * z_n.2 ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right htr_1d (Real.exp_nonneg _)) hBm0.le
        _ = (16 * Bmax * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
              (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by rw [hzn1, hzn2]; ring
    calc b⁻¹ ^ 2 * (Real.sqrt b)⁻¹ ^ m.1 *
          ‖iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν r, z)) y_n‖
        ≤ ((2 : ℝ) ^ 2 * (2 : ℝ) ^ 2) *
            ((16 * Bmax * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
              (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
          mul_le_mul hpref hval (norm_nonneg _) (by positivity)
      _ = K_sp * Real.exp (-β * x.2 ^ 2) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
          dsimp [K_sp]; ring
  have hsp_tsum : ∀ (m : Fin 3) (r : ℝ), r ∈ Ioo s_lo s_hi → ∀ x : ℝ × ℝ,
      iteratedFDeriv ℝ m.1 (canonicalPhysColumn P ν r) x =
        P.gaugeFactor ν • ∑' n : ℤ,
          ((clockA ν r)⁻¹ ^ 2 * (Real.sqrt (clockA ν r))⁻¹ ^ m.1) •
            iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν r, z))
              ((Real.sqrt (clockA ν r))⁻¹ • (x - UnforcedLeray.Gaussian.shiftVec c n)) := by
    intro m r hr x
    have ha : 0 < clockA ν r := by linarith [(ha_bounds r hr).1]
    have hθ : 0 < clockTheta ν r := inv_pos.2 (mul_pos hν ha)
    have hΦ_sm : ContDiff ℝ ∞ (canonMode P (clockTheta ν r)) :=
      contDiff_canonMode_slice hP hSmoothAll hVae hθ
    have hslice : canonMode P (clockTheta ν r) = fun z => F (clockTheta ν r, z) :=
      funext fun z => (hF_eq (clockTheta ν r, z) (hθ_in_win r hr)).symm
    have hP_fn : canonicalPhysColumn P ν r = P.gaugeFactor ν •
        UnforcedLeray.Gaussian.periodize c
          (UnforcedLeray.Gaussian.heatDilation (clockA ν r) (canonMode P (clockTheta ν r))) := by
      funext z
      rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha z]
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      unfold periodizeC UnforcedLeray.Gaussian.periodize
      exact tsum_congr fun n => jscale_eq_heatDilation ha _ _
    have hD_dil : ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z : ℝ × ℝ,
        ‖iteratedFDeriv ℝ k
          (UnforcedLeray.Gaussian.heatDilation (clockA ν r) (canonMode P (clockTheta ν r))) z‖ ≤
          C' * (1 + |z.1|) ^ (-(2 : ℝ)) := by
      intro k hk
      have hk2 : k ≤ 2 := by exact_mod_cast hk
      have hqk : ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ k (canonMode P (clockTheta ν r)) y‖ ≤
          (16 * B ⟨k, by omega⟩) * (1 + |y.1|) ^ (-(2 : ℝ)) := by
        intro y
        rw [hslice]
        calc ‖iteratedFDeriv ℝ k (fun z => F (clockTheta ν r, z)) y‖
            ≤ B ⟨k, by omega⟩ * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
              hB ⟨k, by omega⟩ (clockTheta ν r) y
          _ ≤ B ⟨k, by omega⟩ * (16 * (1 + |y.1|) ^ (-(2 : ℝ))) :=
              mul_le_mul_of_nonneg_left (FrameCont.exp_le_translate_weight y.1 y.2)
                (hB0 ⟨k, by omega⟩).le
          _ = (16 * B ⟨k, by omega⟩) * (1 + |y.1|) ^ (-(2 : ℝ)) := by ring
      exact ⟨_, UnforcedLeray.Gaussian.norm_iteratedFDeriv_heatDilation_le (by norm_num) ha k hqk⟩
    have hP_sm : ContDiff ℝ 2
        (UnforcedLeray.Gaussian.periodize c
          (UnforcedLeray.Gaussian.heatDilation (clockA ν r) (canonMode P (clockTheta ν r)))) :=
      UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (by norm_num) hc_ne
        ((UnforcedLeray.Gaussian.contDiff_heatDilation (hΦ_sm.of_le (by simp)) (clockA ν r)) :
          ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) _) hD_dil
    have hm2 : (m.1 : ℕ∞) ≤ 2 := by fin_cases m <;> decide
    have hm_top : (m.1 : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hm2
    rw [hP_fn, iteratedFDeriv_const_smul_apply (a := P.gaugeFactor ν)
      (hP_sm.contDiffAt.of_le hm_top)]
    congr 1
    have hit_per := UnforcedLeray.Gaussian.iteratedFDeriv_periodize (N := (2 : ℕ∞)) (s := 2)
      (by norm_num) hc_ne
      (UnforcedLeray.Gaussian.contDiff_heatDilation (hΦ_sm.of_le (by simp)) (clockA ν r))
      hD_dil hm2
    rw [congrFun hit_per x]
    refine tsum_congr fun n => ?_
    rw [UnforcedLeray.Gaussian.iteratedFDeriv_heatDilation, hslice]
  set M_sp : ℝ := 1 + ‖P.gaugeFactor ν‖ * (2 * K_sp) * S_lat
  have hMsp_pos : 0 < M_sp := by dsimp [M_sp]; positivity
  have hMsp_1 : ‖P.gaugeFactor ν‖ * K_sp * S_lat ≤ M_sp := by
    have hle : ‖P.gaugeFactor ν‖ * K_sp * S_lat ≤ ‖P.gaugeFactor ν‖ * (2 * K_sp) * S_lat :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)) hSlat_pos.le
    dsimp [M_sp]; linarith
  have hMsp_2 : ‖P.gaugeFactor ν‖ * K_sp * S_lat + ‖P.gaugeFactor ν‖ * K_sp * S_lat ≤ M_sp := by
    have h2 : ‖P.gaugeFactor ν‖ * K_sp * S_lat + ‖P.gaugeFactor ν‖ * K_sp * S_lat =
        ‖P.gaugeFactor ν‖ * (2 * K_sp) * S_lat := by ring
    dsimp [M_sp]; linarith
  have hbd_sp : ∀ τ ∈ Ioo s_lo s_hi, ∀ x : ℝ × ℝ,
      ‖canonicalPhysColumn P ν τ x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2) ∧
      (∀ k : Fin 2, ‖pdCx k (canonicalPhysColumn P ν τ) x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2)) ∧
      (‖ladLapCx (canonicalPhysColumn P ν τ) x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2) ∧
        ‖iteratedFDeriv ℝ 2 (canonicalPhysColumn P ν τ) x‖ ≤ M_sp * Real.exp (-β * x.2 ^ 2)) := by
    intro τ hτ x
    have hnorm_it : ∀ m : Fin 3, ‖iteratedFDeriv ℝ m.1 (canonicalPhysColumn P ν τ) x‖ ≤
        ‖P.gaugeFactor ν‖ * K_sp * S_lat * Real.exp (-β * x.2 ^ 2) := by
      intro m
      rw [hsp_tsum m τ hτ x, norm_smul]
      have hsum : Summable (fun n : ℤ =>
          (K_sp * Real.exp (-β * x.2 ^ 2)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
        (hSlat hc1 x.1).1.mul_left _
      have hts : ‖∑' n : ℤ,
          ((clockA ν τ)⁻¹ ^ 2 * (Real.sqrt (clockA ν τ))⁻¹ ^ m.1) •
            iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν τ, z))
              ((Real.sqrt (clockA ν τ))⁻¹ • (x - UnforcedLeray.Gaussian.shiftVec c n))‖ ≤
          ∑' n : ℤ,
            (K_sp * Real.exp (-β * x.2 ^ 2)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) :=
        tsum_of_norm_bounded hsum.hasSum fun n => hsp_atom_bd m n τ hτ x
      rw [tsum_mul_left] at hts
      have hsl := (hSlat hc1 x.1).2
      calc ‖P.gaugeFactor ν‖ * ‖∑' n : ℤ, _‖
          ≤ ‖P.gaugeFactor ν‖ * (K_sp * Real.exp (-β * x.2 ^ 2) * S_lat) :=
            mul_le_mul_of_nonneg_left
              (hts.trans (mul_le_mul_of_nonneg_left hsl (by positivity)))
              (norm_nonneg _)
        _ = ‖P.gaugeFactor ν‖ * K_sp * S_lat * Real.exp (-β * x.2 ^ 2) := by ring
    have hw_sm_τ := hw_sm_all τ hτ
    refine ⟨?_, fun k => ?_, ?_⟩
    · have h0 := hnorm_it 0
      dsimp at h0
      rw [norm_iteratedFDeriv_zero] at h0
      exact h0.trans (mul_le_mul_of_nonneg_right hMsp_1 (Real.exp_nonneg _))
    · have h1 := hnorm_it 1
      dsimp at h1
      rw [norm_iteratedFDeriv_one] at h1
      have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
      have hpd_le : ‖pdCx k (canonicalPhysColumn P ν τ) x‖ ≤
          ‖fderiv ℝ (canonicalPhysColumn P ν τ) x‖ := by
        unfold pdCx
        exact ((fderiv ℝ (canonicalPhysColumn P ν τ) x).le_opNorm (B0579.dir k)).trans
          (mul_le_of_le_one_right (norm_nonneg _) hdir)
      exact (hpd_le.trans h1).trans (mul_le_mul_of_nonneg_right hMsp_1 (Real.exp_nonneg _))
    · have h2 := hnorm_it 2
      dsimp at h2
      refine ⟨?_, h2.trans (mul_le_mul_of_nonneg_right hMsp_1 (Real.exp_nonneg _))⟩
      have hsum_2 : ‖ladLapCx (canonicalPhysColumn P ν τ) x‖ ≤
          (‖P.gaugeFactor ν‖ * K_sp * S_lat + ‖P.gaugeFactor ν‖ * K_sp * S_lat) *
            Real.exp (-β * x.2 ^ 2) := by
        calc ‖ladLapCx (canonicalPhysColumn P ν τ) x‖
            ≤ ‖iteratedFDeriv ℝ 2 (canonicalPhysColumn P ν τ) x‖ +
                ‖iteratedFDeriv ℝ 2 (canonicalPhysColumn P ν τ) x‖ :=
              norm_ladLapCx_le_two_iteratedFDeriv hw_sm_τ x
          _ ≤ ‖P.gaugeFactor ν‖ * K_sp * S_lat * Real.exp (-β * x.2 ^ 2) +
                ‖P.gaugeFactor ν‖ * K_sp * S_lat * Real.exp (-β * x.2 ^ 2) := add_le_add h2 h2
          _ = _ := by ring
      exact hsum_2.trans (mul_le_mul_of_nonneg_right hMsp_2 (Real.exp_nonneg _))
  have hcont_sp_U : ∀ x : ℝ × ℝ,
      ContinuousOn (fun τ => canonicalPhysColumn P ν τ x) U ∧
      (∀ k : Fin 2, ContinuousOn (fun τ => pdCx k (canonicalPhysColumn P ν τ) x) U) ∧
      ContinuousOn (fun τ => ladLapCx (canonicalPhysColumn P ν τ) x) U := by
    intro x
    have ha_cont : ContinuousOn (clockA ν) U :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    have ha_ne : ∀ r ∈ U, clockA ν r ≠ 0 := fun r hr =>
      (show 0 < clockA ν r by linarith [(ha_bounds r (hU_sub hr)).1]).ne'
    have hsq_cont : ContinuousOn (fun r => (Real.sqrt (clockA ν r))⁻¹) U :=
      (Real.continuous_sqrt.continuousOn.comp ha_cont (mapsTo_univ _ _)).inv₀ fun r hr =>
        (Real.sqrt_pos.2 (by linarith [(ha_bounds r (hU_sub hr)).1])).ne'
    have hθ_cont : ContinuousOn (clockTheta ν) U :=
      ((continuousOn_const (c := ν)).mul ha_cont).inv₀ fun r hr => mul_ne_zero hν.ne' (ha_ne r hr)
    have hit_cont : ∀ m : Fin 3,
        ContinuousOn (fun τ => iteratedFDeriv ℝ m.1 (canonicalPhysColumn P ν τ) x) U := by
      intro m
      have hts_c : ContinuousOn (fun τ => ∑' n : ℤ,
          ((clockA ν τ)⁻¹ ^ 2 * (Real.sqrt (clockA ν τ))⁻¹ ^ m.1) •
            iteratedFDeriv ℝ m.1 (fun z => F (clockTheta ν τ, z))
              ((Real.sqrt (clockA ν τ))⁻¹ • (x - UnforcedLeray.Gaussian.shiftVec c n))) U := by
        refine continuousOn_tsum (fun n => ?_)
          ((hSlat hc1 x.1).1.mul_left (K_sp * Real.exp (-β * x.2 ^ 2)))
          (fun n τ hτ => hsp_atom_bd m n τ (hU_sub hτ) x)
        exact (((ha_cont.inv₀ ha_ne).pow 2).mul (hsq_cont.pow m.1)).smul
          ((hit_F_cont m.1).comp_continuousOn
            (hθ_cont.prodMk (hsq_cont.smul (continuousOn_const (c := x - UnforcedLeray.Gaussian.shiftVec c n)))))
      exact ((continuousOn_const (c := P.gaugeFactor ν)).smul hts_c).congr fun τ hτ =>
        hsp_tsum m τ (hU_sub hτ) x
    refine ⟨?_, fun k => ?_, ?_⟩
    · have h0 := hit_cont 0
      dsimp at h0
      refine ((continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) ℂ).continuous.comp_continuousOn h0).congr
        fun τ _ => by simp [iteratedFDeriv_zero_eq_comp]
    · have h1 := hit_cont 1
      dsimp at h1
      let evk : ((ℝ × ℝ) [×1]→L[ℝ] ℂ) →L[ℝ] ℂ :=
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℂ ![B0579.dir k]
      refine (evk.continuous.comp_continuousOn h1).congr fun τ _ => ?_
      dsimp [evk]
      rw [iteratedFDeriv_one_apply]
      rfl
    · have h2 := hit_cont 2
      dsimp at h2
      let ev00 : ((ℝ × ℝ) [×2]→L[ℝ] ℂ) →L[ℝ] ℂ :=
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℂ ![(1, 0), (1, 0)]
      let ev11 : ((ℝ × ℝ) [×2]→L[ℝ] ℂ) →L[ℝ] ℂ :=
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℂ ![(0, 1), (0, 1)]
      refine ((ev00.continuous.comp_continuousOn h2).add
        (ev11.continuous.comp_continuousOn h2)).congr fun τ hτ => ?_
      dsimp [ev00, ev11]
      exact ladLapCx_eq_iteratedFDeriv_two (hw_sm_all τ (hU_sub hτ)) x
  exact ⟨M_sp, hMsp_pos, hβ_pos,
    fun τ hτ => hw_sm_all τ (hU_sub hτ),
    fun τ hτ => hw_per_all τ (hU_sub hτ),
    fun τ hτ => hbd_sp τ (hU_sub hτ),
    hcont_sp_U⟩

private theorem continuous_linComb_heatDilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f₁ f₂ : ℝ × ℝ → E} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (a c₁ c₂ : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      c₁ • UnforcedLeray.Gaussian.heatDilation a f₁ z -
        c₂ • UnforcedLeray.Gaussian.heatDilation a f₂ z) := by
  unfold UnforcedLeray.Gaussian.heatDilation
  have hz : Continuous (fun z : ℝ × ℝ => (Real.sqrt a)⁻¹ • z) :=
    (continuous_id (X := ℝ × ℝ)).const_smul (Real.sqrt a)⁻¹
  exact (((hf₁.comp hz).const_smul (a⁻¹ ^ 2)).const_smul c₁).sub
    (((hf₂.comp hz).const_smul (a⁻¹ ^ 2)).const_smul c₂)

private theorem continuousOn_g'_atom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℝ} {a : ℝ → ℝ} {f₁ f₂ : ℝ → ℝ × ℝ → E} (ν : ℝ) (z : ℝ × ℝ)
    (ha : ContinuousOn a U) (ha_ne : ∀ r ∈ U, a r ≠ 0)
    (hd₁ : ContinuousOn (fun r => f₁ r ((Real.sqrt (a r))⁻¹ • z)) U)
    (hd₂ : ContinuousOn (fun r => f₂ r ((Real.sqrt (a r))⁻¹ • z)) U) :
    ContinuousOn (fun r =>
      -(ν * (a r)⁻¹) • UnforcedLeray.Gaussian.heatDilation (a r) (f₁ r) z -
        ((a r) ^ 2)⁻¹ • UnforcedLeray.Gaussian.heatDilation (a r) (f₂ r) z) U := by
  unfold UnforcedLeray.Gaussian.heatDilation
  have ha_inv : ContinuousOn (fun r => (a r)⁻¹) U := ha.inv₀ ha_ne
  have ha_inv2 : ContinuousOn (fun r => (a r)⁻¹ ^ 2) U := ha_inv.pow 2
  have ha2_inv : ContinuousOn (fun r => ((a r) ^ 2)⁻¹) U :=
    (ha.pow 2).inv₀ fun r hr => pow_ne_zero 2 (ha_ne r hr)
  exact ((((continuousOn_const (c := ν)).mul ha_inv).neg).smul (ha_inv2.smul hd₁)).sub
    (ha2_inv.smul (ha_inv2.smul hd₂))

/-- Time-derivative half of `canonicalPhysColumn_window_props`: `HasDerivAt`, spatial continuity,
Gaussian `η`-decay, `τ`-continuity on `U`, and Lipschitz bound on `Icc 0 T`. -/
private theorem canonicalPhysColumn_window_timeDeriv {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {ν T : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hT0 : 0 ≤ T) :
    let U : Set ℝ := Ioo (-(1 / (4 * ν))) (T + 1 / 2)
    let β : ℝ := 1 / (16 * clockA ν (T + 1))
    ∃ M_dt : ℝ, 0 < M_dt ∧
      (∀ τ ∈ U, Continuous (fun x : ℝ × ℝ => deriv (fun r => canonicalPhysColumn P ν r x) τ)) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        HasDerivAt (fun r => canonicalPhysColumn P ν r x)
          (deriv (fun r => canonicalPhysColumn P ν r x) τ) τ) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        ‖deriv (fun r => canonicalPhysColumn P ν r x) τ‖ ≤ M_dt * Real.exp (-β * x.2 ^ 2)) ∧
      (∀ x : ℝ × ℝ,
        ContinuousOn (fun τ => deriv (fun r => canonicalPhysColumn P ν r x) τ) U) ∧
      (∀ τ₁ ∈ Icc (0 : ℝ) T, ∀ τ₂ ∈ Icc (0 : ℝ) T, ∀ x : ℝ × ℝ,
        ‖canonicalPhysColumn P ν τ₁ x - canonicalPhysColumn P ν τ₂ x‖ ≤
          M_dt * Real.exp (-β * x.2 ^ 2) * ‖τ₁ - τ₂‖) := by
  intro U β
  set c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hc_ne : c ≠ 0 := hc0.ne'
  set s_lo : ℝ := -(1 / (2 * ν))
  set s_hi : ℝ := T + 1
  have hU_sub : U ⊆ Ioo s_lo s_hi := fun r hr => by
    dsimp [U, s_lo, s_hi] at hr ⊢
    have h4 : 1 / (4 * ν) < 1 / (2 * ν) :=
      div_lt_div_of_pos_left zero_lt_one (by positivity) (by linarith)
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have ha_hi : 1 < clockA ν s_hi := by dsimp [clockA, s_hi]; nlinarith
  set a_max : ℝ := clockA ν s_hi
  have hamax_pos : 0 < a_max := lt_trans zero_lt_one ha_hi
  have hβ_def : β = 1 / (16 * a_max) := rfl
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  set θ_lo : ℝ := (ν * a_max)⁻¹
  set θ_hi : ℝ := (ν * (1 / 2 : ℝ))⁻¹
  have hθ_lo_pos : 0 < θ_lo := inv_pos.2 (mul_pos hν hamax_pos)
  have hθ_le : θ_lo ≤ θ_hi := inv_anti₀ (by positivity) (by nlinarith)
  obtain ⟨_, _, ⟨F, hF_sm, hF_eq, hF_bd⟩⟩ :=
    canonMode_window_jet_and_smooth hP hSmoothAll hVae hθ_lo_pos hθ_le
  have ha_bounds : ∀ r ∈ Ioo s_lo s_hi, 1 / 2 < clockA ν r ∧ clockA ν r < a_max := by
    intro r hr
    constructor
    · dsimp [clockA, s_lo] at hr ⊢
      have := mul_lt_mul_of_pos_left hr.1 hν
      field_simp [hν.ne'] at this; linarith
    · dsimp [a_max, clockA]; nlinarith [hr.2]
  have hθ_in_win : ∀ r ∈ Ioo s_lo s_hi,
      clockTheta ν r ∈ Ioo (θ_lo - θ_lo / 4) (θ_hi + θ_lo / 4) := by
    intro r hr
    obtain ⟨hb_lo, hb_hi⟩ := ha_bounds r hr
    have hbr_pos : 0 < clockA ν r := by linarith
    have ht_lo : θ_lo < clockTheta ν r :=
      inv_strictAnti₀ (mul_pos hν hbr_pos) (mul_lt_mul_of_pos_left hb_hi hν)
    have ht_hi : clockTheta ν r < θ_hi :=
      inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hb_lo hν)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨S_lat, hSlat_pos, hSlat⟩ := tsum_translate_sq_le_unif
  set r₀ : ℝ := (Real.sqrt a_max)⁻¹
  have hr₀_pos : 0 < r₀ := inv_pos.2 (Real.sqrt_pos.2 hamax_pos)
  obtain ⟨B₀, hB₀_pos, hB₀⟩ := hF_bd 0
  obtain ⟨B₁, _, hB₁⟩ := hF_bd 1
  set Bmax : ℝ := max B₀ B₁
  have hBm0 : 0 < Bmax := lt_of_lt_of_le hB₀_pos (le_max_left _ _)
  have hdt_F_cont : Continuous (fun p : ℝ × (ℝ × ℝ) => deriv (fun u => F (u, p.2)) p.1) :=
    continuous_dt_slice hF_sm
  let g_n : ℝ × ℝ → ℤ → ℝ → ℂ := fun x n r =>
    UnforcedLeray.Gaussian.heatDilation (clockA ν r) (fun y => F (clockTheta ν r, y))
      (x.1 - (n : ℝ) * c, x.2)
  let g'_n : ℝ × ℝ → ℤ → ℝ → ℂ := fun x n r =>
    -(ν * (clockA ν r)⁻¹) • UnforcedLeray.Gaussian.heatDilation (clockA ν r)
        (UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν r, y)))
        (x.1 - (n : ℝ) * c, x.2) -
      (((clockA ν r) ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation (clockA ν r)
        (fun y => deriv (fun u => F (u, y)) (clockTheta ν r))
        (x.1 - (n : ℝ) * c, x.2)
  have hdrift_gauss : ∀ (t : ℝ) (y : ℝ × ℝ),
      ‖UnforcedLeray.Gaussian.dilationDrift (fun z => F (t, z)) y‖ ≤
        (11 * Bmax) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16) := by
    intro t y
    have h0 : ‖F (t, y)‖ ≤ Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      have h := (hB₀ t y).1
      rw [norm_iteratedFDeriv_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    have h1 : ‖fderiv ℝ (fun z => F (t, z)) y‖ ≤ Bmax * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      have h := (hB₁ t y).1
      rw [norm_iteratedFDeriv_one] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))
    exact norm_dilationDrift_gauss_le hBm0.le h0 h1
  set K_dt : ℝ := (ν * 2 * (2 : ℝ) ^ 2 * (11 * Bmax) + 4 * (2 : ℝ) ^ 2 * Bmax) *
    (64 * (min 1 r₀) ^ (-(2 : ℝ)))
  have hKdt_pos : 0 < K_dt := by dsimp [K_dt]; positivity
  have hg'_bd_eta : ∀ (x : ℝ × ℝ) (n : ℤ) (r : ℝ), r ∈ Ioo s_lo s_hi →
      ‖g'_n x n r‖ ≤ K_dt * Real.exp (-β * x.2 ^ 2) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
    intro x n r hr
    set b : ℝ := clockA ν r
    obtain ⟨hb_lo, hb_hi⟩ := ha_bounds r hr
    have hb0 : 0 < b := by linarith
    have hbinv : b⁻¹ ≤ 2 := by
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hb_lo.le
      norm_num at h; exact h
    have hb2inv : (b ^ 2)⁻¹ ≤ 4 := by
      have hb2_ge : (1 / 4 : ℝ) ≤ b ^ 2 := by
        calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
          _ ≤ b ^ 2 := pow_le_pow_left₀ (by norm_num) hb_lo.le 2
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hb2_ge
      norm_num at h; exact h
    have hb_sq_le : b⁻¹ ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hb0.le) hbinv 2
    have hrb : r₀ ≤ (Real.sqrt b)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt hb_hi.le)
    set z_n : ℝ × ℝ := (x.1 - (n : ℝ) * c, x.2)
    set y_n : ℝ × ℝ := (Real.sqrt b)⁻¹ • z_n
    have hexp_yn : Real.exp (-(y_n.1 ^ 2 + y_n.2 ^ 2) / 16) ≤
        (64 * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
          (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
      have heta16 : Real.exp (-(y_n.2 ^ 2) / 16) ≤ Real.exp (-β * x.2 ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        have hy2 : y_n.2 ^ 2 = x.2 ^ 2 / b := by
          dsimp [y_n, z_n]
          rw [mul_pow, inv_pow, Real.sq_sqrt hb0.le, div_eq_inv_mul]
        rw [hy2]
        have hdiv : x.2 ^ 2 / (16 * a_max) ≤ x.2 ^ 2 / b / 16 := by
          rw [div_div]
          exact div_le_div_of_nonneg_left (sq_nonneg x.2) (by positivity) (by linarith)
        have hβx : -β * x.2 ^ 2 = -(x.2 ^ 2 / (16 * a_max)) := by
          rw [hβ_def, neg_mul, one_div_mul_eq_div]
        rw [hβx, neg_div]
        exact neg_le_neg hdiv
      have htr1 : (1 + |y_n.1|) ^ (-(2 : ℝ)) ≤
          (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |z_n.1|) ^ (-(2 : ℝ)) := by
        have hy1 : y_n.1 = (Real.sqrt b)⁻¹ * z_n.1 := rfl
        rw [hy1]
        exact UnforcedLeray.Gaussian.one_add_abs_mul_rpow_neg_le (s := 2)
          (by norm_num) hr₀_pos hrb z_n.1
      have hzn1 : z_n.1 = x.1 - (n : ℝ) * c := rfl
      calc Real.exp (-(y_n.1 ^ 2 + y_n.2 ^ 2) / 16)
          ≤ 64 * (1 + |y_n.1|) ^ (-(2 : ℝ)) * Real.exp (-β * x.2 ^ 2) :=
            (exp_div_sixteen_split y_n).trans (mul_le_mul_of_nonneg_left heta16 (by positivity))
        _ ≤ 64 * ((min 1 r₀) ^ (-(2 : ℝ)) * (1 + |z_n.1|) ^ (-(2 : ℝ))) *
              Real.exp (-β * x.2 ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htr1 (by norm_num))
              (Real.exp_nonneg _)
        _ = (64 * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
              (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by rw [hzn1]; ring
    have hdr_yn : ‖UnforcedLeray.Gaussian.dilationDrift (fun z => F (clockTheta ν r, z)) y_n‖ ≤
        (11 * Bmax) * ((64 * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
          (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
      (hdrift_gauss (clockTheta ν r) y_n).trans
        (mul_le_mul_of_nonneg_left hexp_yn (by positivity))
    have hdt_yn : ‖deriv (fun u => F (u, y_n)) (clockTheta ν r)‖ ≤
        Bmax * ((64 * (min 1 r₀) ^ (-(2 : ℝ))) * Real.exp (-β * x.2 ^ 2) *
          (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) := by
      have h := (hB₀ (clockTheta ν r) y_n).2
      rw [norm_iteratedFDeriv_zero] at h
      have hexp8_16 : Real.exp (-(y_n.1 ^ 2 + y_n.2 ^ 2) / 8) ≤
          Real.exp (-(y_n.1 ^ 2 + y_n.2 ^ 2) / 16) :=
        Real.exp_le_exp.2 (by have h1 := sq_nonneg y_n.1; have h2 := sq_nonneg y_n.2; linarith)
      have hB0_le : B₀ ≤ Bmax := le_max_left _ _
      have hstep1 : ‖deriv (fun u => F (u, y_n)) (clockTheta ν r)‖ ≤
          Bmax * Real.exp (-(y_n.1 ^ 2 + y_n.2 ^ 2) / 16) :=
        h.trans (mul_le_mul hB0_le hexp8_16 (Real.exp_nonneg _) hBm0.le)
      exact hstep1.trans (mul_le_mul_of_nonneg_left hexp_yn hBm0.le)
    have hgn_eq : g'_n x n r =
        -(ν * b⁻¹) • UnforcedLeray.Gaussian.heatDilation b
            (UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν r, y))) z_n -
          ((b ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation b
            (fun y => deriv (fun u => F (u, y)) (clockTheta ν r)) z_n := rfl
    rw [hgn_eq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_neg, UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
      norm_smul, UnforcedLeray.Gaussian.heatDilation_apply, norm_smul,
      Real.norm_of_nonneg (mul_nonneg hν.le (inv_nonneg.2 hb0.le)),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b⁻¹ ^ 2),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (b ^ 2)⁻¹)]
    change ν * b⁻¹ * (b⁻¹ ^ 2 *
        ‖UnforcedLeray.Gaussian.dilationDrift (fun z => F (clockTheta ν r, z)) y_n‖) +
      (b ^ 2)⁻¹ * (b⁻¹ ^ 2 * ‖deriv (fun u => F (u, y_n)) (clockTheta ν r)‖) ≤ _
    have t1 : ν * b⁻¹ * (b⁻¹ ^ 2 *
        ‖UnforcedLeray.Gaussian.dilationDrift (fun z => F (clockTheta ν r, z)) y_n‖) ≤
        ν * 2 * ((2 : ℝ) ^ 2 * ((11 * Bmax) * ((64 * (min 1 r₀) ^ (-(2 : ℝ))) *
          Real.exp (-β * x.2 ^ 2) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbinv hν.le)
        (mul_le_mul hb_sq_le hdr_yn (norm_nonneg _) (by norm_num))
        (by positivity) (by positivity)
    have t2 : (b ^ 2)⁻¹ * (b⁻¹ ^ 2 * ‖deriv (fun u => F (u, y_n)) (clockTheta ν r)‖) ≤
        4 * ((2 : ℝ) ^ 2 * (Bmax * ((64 * (min 1 r₀) ^ (-(2 : ℝ))) *
          Real.exp (-β * x.2 ^ 2) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))))) :=
      mul_le_mul hb2inv
        (mul_le_mul hb_sq_le hdt_yn (norm_nonneg _) (by norm_num))
        (by positivity) (by norm_num)
    calc _ ≤ _ := add_le_add t1 t2
      _ = K_dt * Real.exp (-β * x.2 ^ 2) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
          dsimp only [K_dt]; ring
  have hderiv_tsum : ∀ τ ∈ Ioo s_lo s_hi, ∀ x : ℝ × ℝ,
      HasDerivAt (fun r => canonicalPhysColumn P ν r x)
        (P.gaugeFactor ν * ∑' n : ℤ, g'_n x n τ) τ := by
    intro τ hτ x
    have ha_τ : 0 < clockA ν τ := by linarith [(ha_bounds τ hτ).1]
    have hg_d : ∀ (n : ℤ) (r : ℝ), r ∈ Ioo s_lo s_hi → HasDerivAt (g_n x n) (g'_n x n r) r :=
      fun n r hr => hasDerivAt_atom_heatDilation hF_sm hν (by linarith [(ha_bounds r hr).1])
        (x.1 - (n : ℝ) * c, x.2)
    have hu_dom : Summable (fun n : ℤ =>
        (K_dt * Real.exp (-β * x.2 ^ 2)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
      (hSlat hc1 x.1).1.mul_left _
    have hsum_τ : Summable (fun n : ℤ => g_n x n τ) := by
      set b : ℝ := clockA ν τ
      have hb_hi : b < a_max := (ha_bounds τ hτ).2
      have hrb : r₀ ≤ (Real.sqrt b)⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.2 ha_τ) (Real.sqrt_le_sqrt hb_hi.le)
      set C_τ : ℝ := b⁻¹ ^ 2 * (16 * B₀ * (min 1 r₀) ^ (-(2 : ℝ)))
      refine Summable.of_norm_bounded ((hSlat hc1 x.1).1.mul_left C_τ) fun n => ?_
      set z_n : ℝ × ℝ := (x.1 - (n : ℝ) * c, x.2)
      set y_n : ℝ × ℝ := (Real.sqrt b)⁻¹ • z_n
      have hzn1 : z_n.1 = x.1 - (n : ℝ) * c := rfl
      have hf0 : ‖F (clockTheta ν τ, y_n)‖ ≤
          B₀ * Real.exp (-(y_n.1 ^ 2 + y_n.2 ^ 2) / 8) := by
        have h := (hB₀ (clockTheta ν τ) y_n).1
        rw [norm_iteratedFDeriv_zero] at h
        exact h
      have htr : (1 + |y_n.1|) ^ (-(2 : ℝ)) ≤
          (min 1 r₀) ^ (-(2 : ℝ)) * (1 + |z_n.1|) ^ (-(2 : ℝ)) := by
        have hy1 : y_n.1 = (Real.sqrt b)⁻¹ * z_n.1 := rfl
        rw [hy1]
        exact UnforcedLeray.Gaussian.one_add_abs_mul_rpow_neg_le (s := 2)
          (by norm_num) hr₀_pos hrb z_n.1
      have hgn : g_n x n τ = (b⁻¹ ^ 2 : ℝ) • F (clockTheta ν τ, y_n) := rfl
      rw [hgn, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hval : ‖F (clockTheta ν τ, y_n)‖ ≤
          (16 * B₀ * (min 1 r₀) ^ (-(2 : ℝ))) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
        calc ‖F (clockTheta ν τ, y_n)‖
            ≤ B₀ * (16 * (1 + |y_n.1|) ^ (-(2 : ℝ))) :=
              hf0.trans (mul_le_mul_of_nonneg_left
                (FrameCont.exp_le_translate_weight y_n.1 y_n.2) hB₀_pos.le)
          _ ≤ B₀ * (16 * ((min 1 r₀) ^ (-(2 : ℝ)) * (1 + |z_n.1|) ^ (-(2 : ℝ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htr (by norm_num)) hB₀_pos.le
          _ = (16 * B₀ * (min 1 r₀) ^ (-(2 : ℝ))) *
                (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by rw [hzn1]; ring
      calc b⁻¹ ^ 2 * ‖F (clockTheta ν τ, y_n)‖
          ≤ b⁻¹ ^ 2 * ((16 * B₀ * (min 1 r₀) ^ (-(2 : ℝ))) *
              (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hval (by positivity)
        _ = C_τ * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by dsimp only [C_τ]; ring
    have hts := hasDerivAt_tsum_of_isPreconnected hu_dom isOpen_Ioo isPreconnected_Ioo
      hg_d (fun n r hr => hg'_bd_eta x n r hr) hτ hsum_τ hτ
    have hw_ev : (fun r => canonicalPhysColumn P ν r x) =ᶠ[𝓝 τ]
        fun r => P.gaugeFactor ν * ∑' n : ℤ, g_n x n r := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with r hr
      have ha_r : 0 < clockA ν r := by linarith [(ha_bounds r hr).1]
      rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha_r x]
      congr 1
      unfold periodizeC
      refine tsum_congr fun n => ?_
      rw [jscale_eq_heatDilation ha_r]
      have hfn : canonMode P (clockTheta ν r) = fun y => F (clockTheta ν r, y) :=
        funext fun y => (hF_eq (clockTheta ν r, y) (hθ_in_win r hr)).symm
      change UnforcedLeray.Gaussian.heatDilation (clockA ν r) (canonMode P (clockTheta ν r))
        (x.1 - (n : ℝ) * c, x.2) = g_n x n r
      rw [hfn]
    exact (hts.const_mul (P.gaugeFactor ν)).congr_of_eventuallyEq hw_ev
  have hdt_sp_cont : ∀ τ ∈ Ioo s_lo s_hi,
      Continuous (fun x : ℝ × ℝ => deriv (fun r => canonicalPhysColumn P ν r x) τ) := by
    intro τ hτ
    let g_sp : ℝ × ℝ → ℂ := fun z =>
      -(ν * (clockA ν τ)⁻¹) • UnforcedLeray.Gaussian.heatDilation (clockA ν τ)
          (UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν τ, y))) z -
        (((clockA ν τ) ^ 2)⁻¹ : ℝ) • UnforcedLeray.Gaussian.heatDilation (clockA ν τ)
          (fun y => deriv (fun u => F (u, y)) (clockTheta ν τ)) z
    have hfn : (fun x : ℝ × ℝ => deriv (fun r => canonicalPhysColumn P ν r x) τ) =
        fun x => P.gaugeFactor ν * ∑' n : ℤ, g_sp (x - UnforcedLeray.Gaussian.shiftVec c n) := by
      funext x
      rw [(hderiv_tsum τ hτ x).deriv]
      congr 1
      refine tsum_congr fun n => ?_
      have hsh : x - UnforcedLeray.Gaussian.shiftVec c n = (x.1 - (n : ℝ) * c, x.2) := by
        ext <;> simp [UnforcedLeray.Gaussian.shiftVec]
      dsimp only [g_sp]
      rw [hsh]
    have hg_sp_cont : Continuous g_sp := by
      have hc_id : Continuous (fun y : ℝ × ℝ => y) := continuous_id
      have hc_θ : Continuous (fun _ : ℝ × ℝ => clockTheta ν τ) := continuous_const
      have hc_dr : Continuous
          (UnforcedLeray.Gaussian.dilationDrift (fun w => F (clockTheta ν τ, w))) :=
        (continuous_dilationDrift_slice hF_sm).comp (hc_θ.prodMk hc_id)
      have hc_dt : Continuous (fun y : ℝ × ℝ => deriv (fun u => F (u, y)) (clockTheta ν τ)) :=
        hdt_F_cont.comp (hc_θ.prodMk hc_id)
      exact continuous_linComb_heatDilation hc_dr hc_dt (clockA ν τ)
        (-(ν * (clockA ν τ)⁻¹)) (((clockA ν τ) ^ 2)⁻¹)
    have hg_sp_bd : ∀ z : ℝ × ℝ, ‖g_sp z‖ ≤ K_dt * (1 + |z.1|) ^ (-(2 : ℝ)) := by
      intro z
      have h := hg'_bd_eta z 0 τ hτ
      have hexp1 : Real.exp (-β * z.2 ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hβ_pos.le) (sq_nonneg z.2))
      have heq_z : g_sp z = g'_n z 0 τ := by
        dsimp only [g_sp, g'_n]
        simp
      rw [heq_z]
      have h0 : |z.1 - ((0 : ℤ) : ℝ) * c| = |z.1| := by simp
      rw [h0] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hKdt_pos.le hexp1) (by positivity))
    rw [hfn]
    have hc_gf : Continuous (fun _ : ℝ × ℝ => P.gaugeFactor ν) := continuous_const
    exact hc_gf.mul
      (UnforcedLeray.Gaussian.continuous_tsum_translates (g := g_sp) (C := K_dt) (s := 2)
        hg_sp_cont (by norm_num) hc_ne hg_sp_bd)
  set M_dt : ℝ := 1 + ‖P.gaugeFactor ν‖ * K_dt * S_lat
  have hMdt_pos : 0 < M_dt := by dsimp only [M_dt]; positivity
  have hMdt_le : ‖P.gaugeFactor ν‖ * K_dt * S_lat ≤ M_dt := by dsimp only [M_dt]; linarith
  have hbd_dt : ∀ τ ∈ Ioo s_lo s_hi, ∀ x : ℝ × ℝ,
      ‖deriv (fun r => canonicalPhysColumn P ν r x) τ‖ ≤ M_dt * Real.exp (-β * x.2 ^ 2) := by
    intro τ hτ x
    rw [(hderiv_tsum τ hτ x).deriv, norm_mul]
    have hsum : Summable (fun n : ℤ =>
        (K_dt * Real.exp (-β * x.2 ^ 2)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
      (hSlat hc1 x.1).1.mul_left _
    have hts : ‖∑' n : ℤ, g'_n x n τ‖ ≤
        ∑' n : ℤ,
          (K_dt * Real.exp (-β * x.2 ^ 2)) * (1 + |x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) :=
      tsum_of_norm_bounded hsum.hasSum fun n => hg'_bd_eta x n τ hτ
    rw [tsum_mul_left] at hts
    have hsl := (hSlat hc1 x.1).2
    calc ‖P.gaugeFactor ν‖ * ‖∑' n : ℤ, g'_n x n τ‖
        ≤ ‖P.gaugeFactor ν‖ * (K_dt * Real.exp (-β * x.2 ^ 2) * S_lat) :=
          mul_le_mul_of_nonneg_left
            (hts.trans (mul_le_mul_of_nonneg_left hsl (by positivity)))
            (norm_nonneg _)
      _ = (‖P.gaugeFactor ν‖ * K_dt * S_lat) * Real.exp (-β * x.2 ^ 2) := by ring
      _ ≤ M_dt * Real.exp (-β * x.2 ^ 2) :=
          mul_le_mul_of_nonneg_right hMdt_le (Real.exp_nonneg _)
  have hcont_dt_U : ∀ x : ℝ × ℝ,
      ContinuousOn (fun τ => deriv (fun r => canonicalPhysColumn P ν r x) τ) U := by
    intro x
    have ha_cont : ContinuousOn (clockA ν) U :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    have ha_ne : ∀ r ∈ U, clockA ν r ≠ 0 := fun r hr =>
      (show 0 < clockA ν r by linarith [(ha_bounds r (hU_sub hr)).1]).ne'
    have hsq_cont : ContinuousOn (fun r => (Real.sqrt (clockA ν r))⁻¹) U :=
      (Real.continuous_sqrt.continuousOn.comp ha_cont (mapsTo_univ _ _)).inv₀ fun r hr =>
        (Real.sqrt_pos.2 (by linarith [(ha_bounds r (hU_sub hr)).1])).ne'
    have hθ_cont : ContinuousOn (clockTheta ν) U :=
      ((continuousOn_const (c := ν)).mul ha_cont).inv₀ fun r hr => mul_ne_zero hν.ne' (ha_ne r hr)
    have hg'_cont : ∀ n : ℤ, ContinuousOn (g'_n x n) U := by
      intro n
      set z_n : ℝ × ℝ := (x.1 - (n : ℝ) * c, x.2)
      have hyn_c : ContinuousOn (fun r => (Real.sqrt (clockA ν r))⁻¹ • z_n) U :=
        hsq_cont.smul (continuousOn_const (c := z_n))
      have hdr_c : ContinuousOn (fun r =>
          UnforcedLeray.Gaussian.dilationDrift (fun y => F (clockTheta ν r, y))
            ((Real.sqrt (clockA ν r))⁻¹ • z_n)) U :=
        ((continuous_dilationDrift_slice hF_sm).comp_continuousOn
          (hθ_cont.prodMk hyn_c)).congr fun _ _ => rfl
      have hdt_c : ContinuousOn
          (fun r => deriv (fun u => F (u, (Real.sqrt (clockA ν r))⁻¹ • z_n)) (clockTheta ν r)) U :=
        (hdt_F_cont.comp_continuousOn (hθ_cont.prodMk hyn_c)).congr fun _ _ => rfl
      exact continuousOn_g'_atom ν z_n ha_cont ha_ne hdr_c hdt_c
    have hts_dt : ContinuousOn (fun τ => ∑' n : ℤ, g'_n x n τ) U :=
      continuousOn_tsum hg'_cont
        ((hSlat hc1 x.1).1.mul_left (K_dt * Real.exp (-β * x.2 ^ 2)))
        fun n τ hτ => hg'_bd_eta x n τ (hU_sub hτ)
    exact ((continuousOn_const (c := P.gaugeFactor ν)).mul hts_dt).congr fun τ hτ =>
      (hderiv_tsum τ (hU_sub hτ) x).deriv
  have hIcc_U : Icc (0 : ℝ) T ⊆ U := fun r hr => by
    dsimp [U]
    have : 0 < 1 / (4 * ν) := by positivity
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hlip : ∀ τ₁ ∈ Icc (0 : ℝ) T, ∀ τ₂ ∈ Icc (0 : ℝ) T, ∀ x : ℝ × ℝ,
      ‖canonicalPhysColumn P ν τ₁ x - canonicalPhysColumn P ν τ₂ x‖ ≤
        M_dt * Real.exp (-β * x.2 ^ 2) * ‖τ₁ - τ₂‖ := by
    intro τ₁ hτ₁ τ₂ hτ₂ x
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr =>
        ((hderiv_tsum r (hU_sub (hIcc_U hr)) x).congr_deriv
          (hderiv_tsum r (hU_sub (hIcc_U hr)) x).deriv.symm).hasDerivWithinAt)
      (fun r hr => hbd_dt r (hU_sub (hIcc_U hr)) x)
      (convex_Icc 0 T) hτ₂ hτ₁
  exact ⟨M_dt, hMdt_pos,
    fun τ hτ => hdt_sp_cont τ (hU_sub hτ),
    fun τ hτ x => (hderiv_tsum τ (hU_sub hτ) x).congr_deriv
      (hderiv_tsum τ (hU_sub hτ) x).deriv.symm,
    fun τ hτ => hbd_dt τ (hU_sub hτ),
    hcont_dt_U, hlip⟩

/-- Joint window smoothness, Gaussian `η`-decay, `τ`-continuity, and Lipschitz properties of
`canonicalPhysColumn` on an open neighborhood `Ioo (-(1/(4*ν))) (T + 1/2)` of `[0, T]`. -/
private theorem canonicalPhysColumn_window_props {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {ν T : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hT0 : 0 ≤ T) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let U : Set ℝ := Ioo (-(1 / (4 * ν))) (T + 1 / 2)
    ∃ M_w β : ℝ, 0 < M_w ∧ 0 < β ∧
      (∀ τ ∈ U, ContDiff ℝ ∞ (canonicalPhysColumn P ν τ)) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        canonicalPhysColumn P ν τ (x.1 + c, x.2) = canonicalPhysColumn P ν τ x) ∧
      (∀ τ ∈ U, Continuous (fun x : ℝ × ℝ => deriv (fun r => canonicalPhysColumn P ν r x) τ)) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        HasDerivAt (fun r => canonicalPhysColumn P ν r x)
          (deriv (fun r => canonicalPhysColumn P ν r x) τ) τ) ∧
      (∀ τ ∈ U, ∀ x : ℝ × ℝ,
        ‖canonicalPhysColumn P ν τ x‖ ≤ M_w * Real.exp (-β * x.2 ^ 2) ∧
        (∀ k : Fin 2, ‖pdCx k (canonicalPhysColumn P ν τ) x‖ ≤ M_w * Real.exp (-β * x.2 ^ 2)) ∧
        (‖ladLapCx (canonicalPhysColumn P ν τ) x‖ ≤ M_w * Real.exp (-β * x.2 ^ 2) ∧
          ‖iteratedFDeriv ℝ 2 (canonicalPhysColumn P ν τ) x‖ ≤ M_w * Real.exp (-β * x.2 ^ 2)) ∧
        ‖deriv (fun r => canonicalPhysColumn P ν r x) τ‖ ≤ M_w * Real.exp (-β * x.2 ^ 2)) ∧
      (∀ x : ℝ × ℝ,
        ContinuousOn (fun τ => canonicalPhysColumn P ν τ x) U ∧
        (∀ k : Fin 2, ContinuousOn (fun τ => pdCx k (canonicalPhysColumn P ν τ) x) U) ∧
        ContinuousOn (fun τ => ladLapCx (canonicalPhysColumn P ν τ) x) U ∧
        ContinuousOn (fun τ => deriv (fun r => canonicalPhysColumn P ν r x) τ) U) ∧
      (∀ τ₁ ∈ Icc (0 : ℝ) T, ∀ τ₂ ∈ Icc (0 : ℝ) T, ∀ x : ℝ × ℝ,
        ‖canonicalPhysColumn P ν τ₁ x - canonicalPhysColumn P ν τ₂ x‖ ≤
          M_w * Real.exp (-β * x.2 ^ 2) * ‖τ₁ - τ₂‖) := by
  intro c U
  obtain ⟨M_sp, hMsp_pos, hβ_pos, hw_sm, hw_per, hbd_sp, hcont_sp⟩ :=
    canonicalPhysColumn_window_spatial hP hSmoothAll hVae hν hν1 hT0
  obtain ⟨M_dt, hMdt_pos, hdt_sp_cont, hderiv_at, hbd_dt, hcont_dt, hlip_dt⟩ :=
    canonicalPhysColumn_window_timeDeriv hP hSmoothAll hVae hν hν1 hT0
  let β : ℝ := 1 / (16 * clockA ν (T + 1))
  let M_w : ℝ := max M_sp M_dt
  have hMw_pos : 0 < M_w := lt_of_lt_of_le hMsp_pos (le_max_left _ _)
  have hsp_le : ∀ x : ℝ × ℝ, M_sp * Real.exp (-β * x.2 ^ 2) ≤ M_w * Real.exp (-β * x.2 ^ 2) :=
    fun x => mul_le_mul_of_nonneg_right (le_max_left M_sp M_dt) (Real.exp_nonneg _)
  have hdt_le : ∀ x : ℝ × ℝ, M_dt * Real.exp (-β * x.2 ^ 2) ≤ M_w * Real.exp (-β * x.2 ^ 2) :=
    fun x => mul_le_mul_of_nonneg_right (le_max_right M_sp M_dt) (Real.exp_nonneg _)
  refine ⟨M_w, β, hMw_pos, hβ_pos, hw_sm, hw_per, hdt_sp_cont, hderiv_at, ?_, ?_, ?_⟩
  · intro τ hτ x
    obtain ⟨h0, h1, ⟨hlap, hit2⟩⟩ := hbd_sp τ hτ x
    exact ⟨h0.trans (hsp_le x), fun k => (h1 k).trans (hsp_le x),
      ⟨hlap.trans (hsp_le x), hit2.trans (hsp_le x)⟩,
      (hbd_dt τ hτ x).trans (hdt_le x)⟩
  · intro x
    obtain ⟨hc0, hc1, hclap⟩ := hcont_sp x
    exact ⟨hc0, hc1, hclap, hcont_dt x⟩
  · intro τ₁ hτ₁ τ₂ hτ₂ x
    exact (hlip_dt τ₁ hτ₁ τ₂ hτ₂ x).trans
      (mul_le_mul_of_nonneg_right (hdt_le x) (norm_nonneg _))

/-- Zero cell integral for `periodizeC d (Jscale b (canonMode P θ))` (`d > 0`, `b > 0`, `θ > 0`). -/
private theorem integral_cell_periodizeC_jscale_canonMode {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {d b θ : ℝ} (hd : 0 < d) (hb : 0 < b) (hθ : 0 < θ) :
    ∫ x in B0579.cell d, periodizeC d (Jscale b (canonMode P θ)) x = 0 := by
  set g : ℝ × ℝ → ℂ := Jscale b (canonMode P θ)
  have hΦ_sm := contDiff_canonMode_slice hP hSmoothAll hVae hθ
  have hg_cont : Continuous g := by
    have heq : g = UnforcedLeray.Gaussian.heatDilation b (canonMode P θ) :=
      funext fun z => jscale_eq_heatDilation hb _ z
    rw [heq]
    exact (UnforcedLeray.Gaussian.contDiff_heatDilation hΦ_sm b).continuous
  obtain ⟨_, hbd_win, _⟩ := canonMode_window_jet_and_smooth hP hSmoothAll hVae hθ le_rfl
  obtain ⟨B₀, hB₀_pos, hB₀⟩ := hbd_win 0
  have hg_int : Integrable g := by
    have hgauss : Integrable (fun z : ℝ × ℝ =>
        (b ^ (-2 : ℝ) * B₀) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * b))) :=
      (ComplMildGAux.integrable_gauss (a := 8 * b) (by positivity)).const_mul _
    refine hgauss.mono' hg_cont.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    unfold g Jscale
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hb.le _)]
    have h0 := (hB₀ θ ⟨le_rfl, le_rfl⟩ (z.1 / Real.sqrt b, z.2 / Real.sqrt b)).1
    rw [norm_iteratedFDeriv_zero] at h0
    have hexp_eq : -((z.1 / Real.sqrt b) ^ 2 + (z.2 / Real.sqrt b) ^ 2) / 8 =
        -(z.1 ^ 2 + z.2 ^ 2) / (8 * b) := by
      rw [div_pow, div_pow, Real.sq_sqrt hb.le]
      have hb_ne : b ≠ 0 := hb.ne'
      field_simp [hb_ne]
    rw [hexp_eq] at h0
    calc b ^ (-2 : ℝ) * ‖canonMode P θ (z.1 / Real.sqrt b, z.2 / Real.sqrt b)‖
        ≤ b ^ (-2 : ℝ) * (B₀ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * b))) :=
          mul_le_mul_of_nonneg_left h0 (Real.rpow_nonneg hb.le _)
      _ = (b ^ (-2 : ℝ) * B₀) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * b)) := by ring
  have hg_rot : ∀ z : ℝ × ℝ, g (-z.2, z.1) = -g z := by
    intro z
    unfold g Jscale canonMode
    dsimp only
    rw [neg_div, planarMode_rot90 (P.canonical θ) (z.1 / Real.sqrt b, z.2 / Real.sqrt b), mul_neg]
  rw [integral_cell_periodizeC_eq_plane hd hg_cont hg_int]
  exact integral_plane_eq_zero_of_rot90 hg_cont hg_int hg_rot

/-- `IsBiotSavart` for `canonicalPhysColumn P ν s` and `canonicalPhysVel P ν s` (`m > 8`). -/
private theorem isBiotSavart_canonicalPhysColumn {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {m ν s : ℝ} (hm : 8 < m) (hν : 0 < ν) (hν1 : ν ≤ 1) (hs : 0 ≤ s) :
    IsBiotSavart (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) (canonicalPhysVel P ν s) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have : Fact (0 < c) := ⟨hc0⟩
  have ha : 0 < clockA ν s := by unfold clockA; nlinarith
  have hθ : 0 < clockTheta ν s := inv_pos.2 (mul_pos hν ha)
  obtain ⟨M_w, β, hMw_pos, hβ_pos, hw_sm, _, _, _, hw_bd, _, _⟩ :=
    canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hs
  have hs_U : s ∈ Ioo (-(1 / (4 * ν))) (s + 1 / 2) := by
    have : 0 < 1 / (4 * ν) := by positivity
    exact ⟨by linarith, by linarith⟩
  set Ω : ℝ × ℝ → ℂ := canonicalPhysColumn P ν s
  have hΩ_mem : MemLp Ω 2 (B0579.cellMeasure c m) := by
    refine memLp_of_exp_eta hc0 (by linarith) hβ_pos (by positivity : 0 ≤ M_w * Real.exp β)
      (hw_sm s hs_U).continuous.aestronglyMeasurable fun x _ => ?_
    calc ‖Ω x‖ ≤ M_w * Real.exp (-β * x.2 ^ 2) := (hw_bd s hs_U x).1
      _ ≤ M_w * (Real.exp β * Real.exp (-β * |x.2|)) :=
          mul_le_mul_of_nonneg_left (exp_sq_le_exp_abs hβ_pos x.2) hMw_pos.le
      _ = (M_w * Real.exp β) * Real.exp (-β * |x.2|) := by ring
  have hΩ_zc : HasZeroCirculation c Ω := by
    refine ⟨zcCellIntegrable c m (by linarith) Ω hΩ_mem, ?_⟩
    have hfn : Ω = fun x => P.gaugeFactor ν *
        periodizeC c (Jscale (clockA ν s) (canonMode P (clockTheta ν s))) x :=
      funext fun x => canonicalPhysColumn_eq_periodizeC_planar P hν ha x
    rw [hfn, integral_const_mul,
      integral_cell_periodizeC_jscale_canonMode hP hSmoothAll hVae hc0 ha hθ, mul_zero]
  obtain ⟨C_bs, _, hCbs⟩ := CTE.realBiotSavartUniform m (by linarith)
  obtain ⟨hint, hz⟩ := hΩ_zc
  have hre : MemLp (fun x => (Ω x).re) 2 (B0579.cellMeasure c m) := hΩ_mem.re
  have him : MemLp (fun x => (Ω x).im) 2 (B0579.cellMeasure c m) := hΩ_mem.im
  have hzre : ∫ x in B0579.cell c, (Ω x).re = 0 := by simpa [hz] using integral_re hint
  have hzim : ∫ x in B0579.cell c, (Ω x).im = 0 := by simpa [hz] using integral_im hint
  set ωr : B0579.X c m := hre.toLp (fun x => (Ω x).re)
  set ωi : B0579.X c m := him.toLp (fun x => (Ω x).im)
  have hωr_int : ∫ x in B0579.cell c, ωr x = 0 := by
    rw [integral_congr_ae ((B0579.ac_cellMeasure c m).ae_le hre.coeFn_toLp)]; exact hzre
  have hωi_int : ∫ x in B0579.cell c, ωi x = 0 := by
    rw [integral_congr_ae ((B0579.ac_cellMeasure c m).ae_le him.coeFn_toLp)]; exact hzim
  obtain ⟨Ur, hUr, _⟩ := hCbs c hc1 ωr hωr_int
  obtain ⟨Ui, hUi, _⟩ := hCbs c hc1 ωi hωi_int
  have hUr' : IsBiotSavart c (fun x => (((Ω x).re : ℝ) : ℂ)) Ur := by
    refine UnforcedLeray.Short.IIIa.isBiotSavart_congr_ae hUr ?_
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le hre.coeFn_toLp] with x hx
    show ((ωr x : ℝ) : ℂ) = (((Ω x).re : ℝ) : ℂ)
    rw [hx]
  have hUi' : IsBiotSavart c (fun x => (((Ω x).im : ℝ) : ℂ)) Ui := by
    refine UnforcedLeray.Short.IIIa.isBiotSavart_congr_ae hUi ?_
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le him.coeFn_toLp] with x hx
    show ((ωi x : ℝ) : ℂ) = (((Ω x).im : ℝ) : ℂ)
    rw [hx]
  have hcomb := UnforcedLeray.Short.IIIa.isBiotSavart_comb hUr' hUi' hre.ofReal him.ofReal Complex.I
  have hΩeq : (fun x => (((Ω x).re : ℝ) : ℂ) + Complex.I * (((Ω x).im : ℝ) : ℂ)) = Ω := by
    funext x; apply Complex.ext <;> simp
  rw [hΩeq] at hcomb
  have hae := ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.kerVelCx_ae_eq_of_isBiotSavart
    hc1 hm hΩ_mem ⟨hint, hz⟩ hcomb
  exact BSAux.isBS_congr hcomb fun j => by
    filter_upwards [hae] with x hx
    exact hx j

/-- Uniform exponential `η`-decay and `τ`-continuity of `canonicalPhysVel P ν τ` on `[0, clockAge ν r_min]`. -/
private theorem canonicalPhysVel_window_props {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {r_min ν : ℝ} (hr_min : 0 < r_min) (hν : 0 < ν) (hν_min : ν ≤ min 1 r_min)
    (hT0 : 0 ≤ clockAge ν r_min) :
    let I : Set ℝ := Icc (0 : ℝ) (clockAge ν r_min)
    ∃ M_u α_u : ℝ, 0 < M_u ∧ 0 < α_u ∧
      (∀ τ ∈ I, ∀ (x : ℝ × ℝ) (k : Fin 2),
        ‖canonicalPhysVel P ν τ x k‖ ≤ M_u * Real.exp (-α_u * |x.2|)) ∧
      (∀ (x : ℝ × ℝ) (k : Fin 2), ContinuousOn (fun τ => canonicalPhysVel P ν τ x k) I) := by
  intro I
  have hν1 : ν ≤ 1 := hν_min.trans (min_le_left _ _)
  have hνr : ν ≤ r_min := hν_min.trans (min_le_right _ _)
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  set T : ℝ := clockAge ν r_min
  -- Since `0 ∈ I`, `clockWindow_bounds` gives `r_min ≤ ν⁻¹`
  have h0_mem : (0 : ℝ) ∈ I := ⟨le_rfl, hT0⟩
  obtain ⟨_, _, hθ0_mem, _, _, _⟩ := clockWindow_bounds hν hν1 hr_min hνr h0_mem
  have hr_le_inv : r_min ≤ ν⁻¹ := hθ0_mem.1.trans hθ0_mem.2
  obtain ⟨_, hbd_win, _⟩ := canonMode_window_jet_and_smooth hP hSmoothAll hVae hr_min hr_le_inv
  obtain ⟨B₀, hB₀_pos, hB₀⟩ := hbd_win 0
  obtain ⟨B₁, hB₁_pos, hB₁⟩ := hbd_win 1
  obtain ⟨B₂, hB₂_pos, hB₂⟩ := hbd_win 2
  obtain ⟨S_lat, hSlat_pos, hSlat⟩ := tsum_translate_sq_le_unif
  obtain ⟨C_cv, hCcv0, hconv⟩ := ComplMildGAux.kerConv_le
  set G₃₂ : ℝ := ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)
  have hG₃₂_nn : 0 ≤ G₃₂ := integral_nonneg fun _ => (Real.exp_pos _).le
  set M_0 : ℝ := 16 * B₀ * S_lat
  set M_E : ℝ := M_0 * Real.exp ((c / 2) ^ 2 / 16)
  have hME_pos : 0 < M_E := by dsimp [M_E, M_0]; positivity
  set I_E : ℝ := M_E * G₃₂
  have hIE_nn : 0 ≤ I_E := mul_nonneg hME_pos.le hG₃₂_nn
  set Q_dec : ℝ := 2 * I_E + C_cv * M_E + (C_cv + 1) * (M_E * G₃₂)
  have hQ_nn : 0 ≤ Q_dec := by dsimp [Q_dec]; positivity
  set γ : ℝ := min (1 / 64 : ℝ) (Real.pi / c)
  have hγ_pos : 0 < γ := lt_min (by norm_num) (div_pos Real.pi_pos hc0)
  set a_top : ℝ := clockA ν T
  have hatop_ge1 : 1 ≤ a_top := (clockWindow_bounds hν hν1 hr_min hνr ⟨hT0, le_rfl⟩).1
  have hatop_pos : 0 < a_top := lt_of_lt_of_le zero_lt_one hatop_ge1
  set α_u : ℝ := γ / Real.sqrt a_top
  have hαu_pos : 0 < α_u := div_pos hγ_pos (Real.sqrt_pos.2 hatop_pos)
  set M_mov : ℝ := 2 * Q_dec + (C_cv * M_E + C_cv * I_E) * Real.exp (2 * γ)
  have htail_nn : 0 ≤ (C_cv * M_E + C_cv * I_E) * Real.exp (2 * γ) := by positivity
  set M_u : ℝ := 1 + ‖P.gaugeFactor ν‖ * M_mov
  have hMu_pos : 0 < M_u := by dsimp [M_u, M_mov, Q_dec]; positivity
  -- 1. Exponential spatial decay on `I`
  have hdecay : ∀ τ ∈ I, ∀ (x : ℝ × ℝ) (k : Fin 2),
      ‖canonicalPhysVel P ν τ x k‖ ≤ M_u * Real.exp (-α_u * |x.2|) := by
    intro τ hτ x k
    obtain ⟨ha1, ha0, hθ_mem, hθ0, hd1_θ, _⟩ := clockWindow_bounds hν hν1 hr_min hνr hτ
    set a : ℝ := clockA ν τ
    set θ : ℝ := clockTheta ν τ
    set d : ℝ := cellLen c a
    have hd_eq : d = dOfTheta ν θ := (dOfTheta_eq_cellLen hν ha0).symm
    have hd1 : 1 ≤ d := by rwa [hd_eq]
    have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
    have hd_le_c : d ≤ c := by
      dsimp [d, cellLen]
      exact div_le_self hc0.le (Real.one_le_sqrt.2 ha1)
    have ha_le_top : a ≤ a_top := by dsimp [a, a_top, clockA]; nlinarith [hτ.2]
    set W : ℝ × ℝ → ℂ := periodizeC d (canonMode P θ)
    -- Regularity & Gaussian bounds on `W`
    have hW_cont : Continuous W := by
      have hΦ_sm := contDiff_canonMode_slice hP hSmoothAll hVae hθ0
      have hD_W : ∀ j : ℕ, (j : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z : ℝ × ℝ,
          ‖iteratedFDeriv ℝ j (canonMode P θ) z‖ ≤ C' * (1 + |z.1|) ^ (-(2 : ℝ)) := by
        intro j hj
        have hj2 : j ≤ 2 := by exact_mod_cast hj
        interval_cases j
        · refine ⟨16 * B₀, fun z => ?_⟩
          have h := (hB₀ θ hθ_mem z).1
          rw [norm_iteratedFDeriv_zero] at h ⊢
          calc ‖canonMode P θ z‖
              ≤ B₀ * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
                h.trans (mul_le_mul_of_nonneg_left
                  (FrameCont.exp_le_translate_weight z.1 z.2) hB₀_pos.le)
            _ = (16 * B₀) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
        · refine ⟨16 * B₁, fun z => ?_⟩
          have h := (hB₁ θ hθ_mem z).1
          calc ‖iteratedFDeriv ℝ 1 (canonMode P θ) z‖
              ≤ B₁ * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
                h.trans (mul_le_mul_of_nonneg_left
                  (FrameCont.exp_le_translate_weight z.1 z.2) hB₁_pos.le)
            _ = (16 * B₁) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
        · refine ⟨16 * B₂, fun z => ?_⟩
          have h := (hB₂ θ hθ_mem z).1
          calc ‖iteratedFDeriv ℝ 2 (canonMode P θ) z‖
              ≤ B₂ * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) :=
                h.trans (mul_le_mul_of_nonneg_left
                  (FrameCont.exp_le_translate_weight z.1 z.2) hB₂_pos.le)
            _ = (16 * B₂) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring
      have hW_c2 : ContDiff ℝ 2 W := by
        have heq : W = UnforcedLeray.Gaussian.periodize d (canonMode P θ) := rfl
        rw [heq]
        exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (by norm_num) hd0.ne'
          (hΦ_sm.of_le (by simp) : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) _) hD_W
      exact hW_c2.continuous
    have hW_per : ∀ z : ℝ × ℝ, W (z.1 + d, z.2) = W z := periodizeC_periodic d _
    have hW_eta8 : ∀ z : ℝ × ℝ, ‖W z‖ ≤ M_0 * Real.exp (-(z.2 ^ 2) / 8) := by
      intro z
      unfold W periodizeC
      have hterm : ∀ n : ℤ, ‖canonMode P θ (z.1 - (n : ℝ) * d, z.2)‖ ≤
          (16 * B₀ * Real.exp (-(z.2 ^ 2) / 8)) * (1 + |z.1 - (n : ℝ) * d|) ^ (-(2 : ℝ)) := by
        intro n
        have h := (hB₀ θ hθ_mem (z.1 - (n : ℝ) * d, z.2)).1
        rw [norm_iteratedFDeriv_zero] at h
        have hsp : -((z.1 - (n : ℝ) * d) ^ 2 + z.2 ^ 2) / 8 =
            -((z.1 - (n : ℝ) * d) ^ 2 + (0 : ℝ) ^ 2) / 8 + (-(z.2 ^ 2) / 8) := by ring
        rw [hsp, Real.exp_add] at h
        calc ‖canonMode P θ (z.1 - (n : ℝ) * d, z.2)‖
            ≤ B₀ * (16 * (1 + |z.1 - (n : ℝ) * d|) ^ (-(2 : ℝ)) * Real.exp (-(z.2 ^ 2) / 8)) :=
              h.trans (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  (FrameCont.exp_le_translate_weight (z.1 - (n : ℝ) * d) 0) (Real.exp_nonneg _))
                hB₀_pos.le)
          _ = (16 * B₀ * Real.exp (-(z.2 ^ 2) / 8)) *
                (1 + |z.1 - (n : ℝ) * d|) ^ (-(2 : ℝ)) := by ring
      have hdom := (hSlat hd1 z.1).1.mul_left (16 * B₀ * Real.exp (-(z.2 ^ 2) / 8))
      have hsum := Summable.of_norm_bounded hdom hterm
      have hle := hsum.norm.tsum_le_tsum hterm hdom
      rw [tsum_mul_left] at hle
      calc ‖∑' n : ℤ, canonMode P θ (z.1 - (n : ℝ) * d, z.2)‖
          ≤ (16 * B₀ * Real.exp (-(z.2 ^ 2) / 8)) * S_lat :=
            (norm_tsum_le_tsum_norm hsum.norm).trans
              (hle.trans (mul_le_mul_of_nonneg_left (hSlat hd1 z.1).2 (by positivity)))
        _ = M_0 * Real.exp (-(z.2 ^ 2) / 8) := by dsimp [M_0]; ring
    have hW_all : ∀ z : ℝ × ℝ, ‖W z‖ ≤ M_E * Real.exp (-(z.2 ^ 2) / 16) := by
      intro z
      refine (hW_eta8 z).trans ?_
      dsimp [M_E]
      have h1 : 1 ≤ Real.exp ((c / 2) ^ 2 / 16) := Real.one_le_exp (by positivity)
      have h2 : Real.exp (-(z.2 ^ 2) / 8) ≤ Real.exp (-(z.2 ^ 2) / 16) :=
        Real.exp_le_exp.2 (by have := sq_nonneg z.2; linarith)
      exact mul_le_mul (le_mul_of_one_le_right (by dsimp [M_0]; positivity) h1) h2
        (Real.exp_nonneg _) (by dsimp [M_0]; positivity)
    have hW_sup : ∀ z : ℝ × ℝ, ‖W z‖ ≤ M_E := fun z =>
      (hW_all z).trans (mul_le_of_le_one_right hME_pos.le
        (Real.exp_le_one_iff.2 (by have := sq_nonneg z.2; linarith)))
    have hW_cell : ∀ z ∈ B0579.cell d, ‖W z‖ ≤ M_E * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) := by
      intro z hz
      have hz1 : z.1 ^ 2 ≤ (c / 2) ^ 2 := by
        have h1 : -(c / 2) ≤ z.1 := by linarith [hz.1.1]
        have h2 : z.1 ≤ c / 2 := by linarith [hz.1.2]
        exact sq_le_sq.2 ((abs_le.2 ⟨h1, h2⟩).trans (le_abs_self (c / 2)))
      refine (hW_eta8 z).trans ?_
      have hrhs : M_E * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16) =
          M_0 * Real.exp ((c / 2) ^ 2 / 16 + (-(z.1 ^ 2 + z.2 ^ 2) / 16)) := by
        dsimp [M_E]
        rw [mul_assoc, ← Real.exp_add]
      rw [hrhs]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by dsimp [M_0]; positivity)
      linarith [sq_nonneg z.2]
    have hW_IE : (∫⁻ z in B0579.cell d, ‖W z‖ₑ) ≤ ENNReal.ofReal I_E := by
      refine ComplMildGAux.lintegral_cell_le_gauss32 hME_pos.le fun z hz => ?_
      refine (hW_cell z hz).trans (mul_le_mul_of_nonneg_left ?_ hME_pos.le)
      exact Real.exp_le_exp.2 (by have h1 := sq_nonneg z.1; have h2 := sq_nonneg z.2; linarith)
    have hW_0 : ∫ z in B0579.cell d, W z = 0 := by
      have hj1 : Jscale 1 (canonMode P θ) = canonMode P θ := by
        funext z; unfold Jscale; simp
      change ∫ z in B0579.cell d, periodizeC d (canonMode P θ) z = 0
      rw [← hj1]
      exact integral_cell_periodizeC_jscale_canonMode hP hSmoothAll hVae hd0 zero_lt_one hθ0
    -- Bound `‖kerVelCx d W y k‖` at `y = (x.1 / √a, x.2 / √a)`
    set y : ℝ × ℝ := (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hker_bd : ‖kerVelCx d W y k‖ ≤ M_mov * Real.exp (-γ * |y.2|) := by
      by_cases hy2 : 2 < |y.2|
      · set R : ℝ := |y.2| / 2
        have hR1 : 1 < R := by dsimp [R]; linarith
        have hRy : |y.2| = 2 * R := by dsimp [R]; ring
        have hcore := ComplMildGAux.kerVel_decay_abstract (k := k) (y := y) hCcv0 hME_pos.le hIE_nn
          (fun W' hW' S L hS hL hsup hL1 => hconv d hd1 W' hW' S L hS hL hsup hL1 y k)
          hd1 hR1 hRy hW_cont hW_per hW_cell hW_all hW_sup hW_IE hW_0
          (EulerErrorSub.measurable_kerD d k)
        change _ ≤ _ at hcore
        have hRR : R ≤ R ^ 2 := by
          calc R = 1 * R := (one_mul R).symm
            _ ≤ R * R := mul_le_mul_of_nonneg_right hR1.le (by linarith)
            _ = R ^ 2 := (sq R).symm
        have hγ_32 : γ * |y.2| ≤ (1 / 32 : ℝ) * R := by
          have hγ1 : γ ≤ 1 / 64 := min_le_left _ _
          calc γ * |y.2| = (2 * γ) * R := by rw [hRy]; ring
            _ ≤ (1 / 32 : ℝ) * R := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have hex1 : Real.exp (-(R ^ 2) / 16) ≤ Real.exp (-γ * |y.2|) :=
          Real.exp_le_exp.2 (by linarith)
        have hex2 : Real.exp (-(R ^ 2) / 32) ≤ Real.exp (-γ * |y.2|) :=
          Real.exp_le_exp.2 (by linarith)
        have hex3 : Real.exp (-(2 * Real.pi / d) * R) ≤ Real.exp (-γ * |y.2|) := by
          refine Real.exp_le_exp.2 ?_
          have hγ2 : γ ≤ Real.pi / c := min_le_right _ _
          have hpic : Real.pi / c ≤ Real.pi / d :=
            div_le_div_of_nonneg_left Real.pi_pos.le hd0 hd_le_c
          have hγd : γ * |y.2| ≤ (2 * Real.pi / d) * R := by
            calc γ * |y.2| = (2 * γ) * R := by rw [hRy]; ring
              _ ≤ (2 * (Real.pi / d)) * R :=
                  mul_le_mul_of_nonneg_right (by linarith) (by linarith)
              _ = (2 * Real.pi / d) * R := by ring
          linarith
        have hG_eq : (∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)) = G₃₂ := rfl
        rw [hG_eq] at hcore
        refine hcore.trans ?_
        have t1 : I_E * (2 * Real.exp (-(2 * Real.pi / d) * R)) ≤
            2 * I_E * Real.exp (-γ * |y.2|) := by
          calc I_E * (2 * Real.exp (-(2 * Real.pi / d) * R))
              = (2 * I_E) * Real.exp (-(2 * Real.pi / d) * R) := by ring
            _ ≤ (2 * I_E) * Real.exp (-γ * |y.2|) :=
                mul_le_mul_of_nonneg_left hex3 (by positivity)
        have t2 : C_cv * (M_E * Real.exp (-(R ^ 2) / 16)) ≤
            C_cv * M_E * Real.exp (-γ * |y.2|) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hex1 (mul_nonneg hCcv0 hME_pos.le)
        have t3 : C_cv * (M_E * Real.exp (-(R ^ 2) / 32) * G₃₂) ≤
            C_cv * (M_E * G₃₂) * Real.exp (-γ * |y.2|) := by
          have : C_cv * (M_E * Real.exp (-(R ^ 2) / 32) * G₃₂) =
              (C_cv * (M_E * G₃₂)) * Real.exp (-(R ^ 2) / 32) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hex2 (by positivity)
        have t4 : 1 / 2 * (M_E * Real.exp (-(R ^ 2) / 32) * G₃₂) ≤
            1 * (M_E * G₃₂) * Real.exp (-γ * |y.2|) := by
          have heq : 1 / 2 * (M_E * Real.exp (-(R ^ 2) / 32) * G₃₂) =
              (1 / 2 * (M_E * G₃₂)) * Real.exp (-(R ^ 2) / 32) := by ring
          rw [heq]
          have hMG : 0 ≤ M_E * G₃₂ := mul_nonneg hME_pos.le hG₃₂_nn
          exact mul_le_mul (by linarith) hex2 (Real.exp_nonneg _) (by linarith)
        have hsum_q : 2 * I_E * Real.exp (-γ * |y.2|) +
            (C_cv * M_E * Real.exp (-γ * |y.2|) + C_cv * (M_E * G₃₂) * Real.exp (-γ * |y.2|)) +
            1 * (M_E * G₃₂) * Real.exp (-γ * |y.2|) = Q_dec * Real.exp (-γ * |y.2|) := by
          dsimp [Q_dec]; ring
        refine (add_le_add (add_le_add t1 (add_le_add t2 t3)) t4).trans ?_
        rw [hsum_q]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        dsimp [M_mov]; linarith [hQ_nn, htail_nn]
      · have hy2' : |y.2| ≤ 2 := not_lt.1 hy2
        have hcv := hconv d hd1 W hW_per M_E I_E hME_pos.le hIE_nn hW_sup hW_IE y k
        have hker_le : ‖kerVelCx d W y k‖ ≤ C_cv * M_E + C_cv * I_E := by
          unfold kerVelCx
          have hen_eq : ∫⁻ z in B0579.cell d, ‖W z * (kerD d (y - z) k : ℂ)‖ₑ =
              ∫⁻ z in B0579.cell d, ‖W z‖ₑ * ‖kerD d (y - z) k‖ₑ :=
            setLIntegral_congr_fun (B0579.measurableSet_cell d) fun z _ => by
              rw [enorm_mul]; congr 1; rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
          have hen := (enorm_integral_le_lintegral_enorm _).trans (hen_eq.trans_le hcv)
          rw [← ofReal_norm] at hen
          exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hen
        have hexp_ge : 1 ≤ Real.exp (2 * γ) * Real.exp (-γ * |y.2|) := by
          rw [← Real.exp_add]
          have hγy : γ * |y.2| ≤ 2 * γ := by
            calc γ * |y.2| ≤ γ * 2 := mul_le_mul_of_nonneg_left hy2' hγ_pos.le
              _ = 2 * γ := mul_comm _ _
          exact Real.one_le_exp (by linarith)
        calc ‖kerVelCx d W y k‖ ≤ (C_cv * M_E + C_cv * I_E) * 1 := by rw [mul_one]; exact hker_le
          _ ≤ (C_cv * M_E + C_cv * I_E) * (Real.exp (2 * γ) * Real.exp (-γ * |y.2|)) :=
              mul_le_mul_of_nonneg_left hexp_ge (by positivity)
          _ ≤ M_mov * Real.exp (-γ * |y.2|) := by
              have : (C_cv * M_E + C_cv * I_E) * Real.exp (2 * γ) ≤ M_mov := by
                dsimp [M_mov]; linarith [hQ_nn]
              calc (C_cv * M_E + C_cv * I_E) * (Real.exp (2 * γ) * Real.exp (-γ * |y.2|))
                  = ((C_cv * M_E + C_cv * I_E) * Real.exp (2 * γ)) * Real.exp (-γ * |y.2|) := by ring
                _ ≤ M_mov * Real.exp (-γ * |y.2|) :=
                    mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)
    -- Rescale `kerVelCx d W y k` to `canonicalPhysVel P ν τ x k`
    have hxy : (Real.sqrt a * y.1, Real.sqrt a * y.2) = x := by
      ext <;> simp [y, mul_div_cancel₀ _ (Real.sqrt_pos.2 ha0).ne']
    have hjs_inv_w : JscaleInv a (canonicalPhysColumn P ν τ) = fun z => P.gaugeFactor ν * W z := by
      funext z
      have hw_z : canonicalPhysColumn P ν τ = fun u => P.gaugeFactor ν * Jscale a W u :=
        funext fun u => by
          rw [canonicalPhysColumn_eq_periodizeC_planar P hν ha0 u, ← jscale_periodizeC_cellLen ha0]
          rfl
      have hmul : JscaleInv a (fun u => P.gaugeFactor ν * Jscale a W u) z =
          P.gaugeFactor ν * JscaleInv a (Jscale a W) z := by unfold JscaleInv; ring
      rw [hw_z, hmul, jscaleInv_jscale_eq ha0]
    have hvel_scale : P.gaugeFactor ν * kerVelCx d W y k =
        ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * canonicalPhysVel P ν τ x k := by
      have h1 := ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.kerVelCx_jscaleInv (c := c) ha0
        (canonicalPhysColumn P ν τ) y k
      rw [hjs_inv_w, hxy, ComplMildTestedSplit.kerVelCx_const_mul] at h1
      exact h1
    have ha32 : 1 ≤ a ^ ((3 : ℝ) / 2) := Real.one_le_rpow ha1 (by norm_num)
    have hnorm_sc := congrArg norm hvel_scale
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (by linarith)] at hnorm_sc
    have hu_le_mov : ‖canonicalPhysVel P ν τ x k‖ ≤ ‖P.gaugeFactor ν‖ * ‖kerVelCx d W y k‖ := by
      have h1 : 1 * ‖canonicalPhysVel P ν τ x k‖ ≤
          a ^ ((3 : ℝ) / 2) * ‖canonicalPhysVel P ν τ x k‖ :=
        mul_le_mul_of_nonneg_right ha32 (norm_nonneg _)
      linarith
    have hexp_yx : Real.exp (-γ * |y.2|) ≤ Real.exp (-α_u * |x.2|) := by
      refine Real.exp_le_exp.2 ?_
      have hy2_abs : |y.2| = |x.2| / Real.sqrt a := by
        dsimp [y]; rw [abs_div, abs_of_pos (Real.sqrt_pos.2 ha0)]
      rw [hy2_abs]
      have hdiv : |x.2| / Real.sqrt a_top ≤ |x.2| / Real.sqrt a :=
        div_le_div_of_nonneg_left (abs_nonneg x.2) (Real.sqrt_pos.2 ha0)
          (Real.sqrt_le_sqrt ha_le_top)
      have hmul := mul_le_mul_of_nonneg_left hdiv hγ_pos.le
      dsimp [α_u]
      have : γ / Real.sqrt a_top * |x.2| = γ * (|x.2| / Real.sqrt a_top) := by ring
      linarith
    calc ‖canonicalPhysVel P ν τ x k‖
        ≤ ‖P.gaugeFactor ν‖ * (M_mov * Real.exp (-α_u * |x.2|)) :=
          hu_le_mov.trans (mul_le_mul_of_nonneg_left
            (hker_bd.trans (mul_le_mul_of_nonneg_left hexp_yx
              (by dsimp [M_mov]; linarith [hQ_nn, htail_nn])))
            (norm_nonneg _))
      _ ≤ M_u * Real.exp (-α_u * |x.2|) := by
          have : ‖P.gaugeFactor ν‖ * M_mov ≤ M_u := by dsimp [M_u]; linarith
          calc ‖P.gaugeFactor ν‖ * (M_mov * Real.exp (-α_u * |x.2|))
              = (‖P.gaugeFactor ν‖ * M_mov) * Real.exp (-α_u * |x.2|) := by ring
            _ ≤ M_u * Real.exp (-α_u * |x.2|) :=
                mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)
  -- 2. Lipschitz continuity in `τ` on `I = Icc 0 T`
  obtain ⟨M_w, β, hMw_pos, hβ_pos, hw_sm, hw_per, _, _, hw_bd, _, hw_lip⟩ :=
    canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hT0
  have hI_U : I ⊆ Ioo (-(1 / (4 * ν))) (T + 1 / 2) := fun r hr => by
    have : 0 < 1 / (4 * ν) := by positivity
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  set J_prod : ℝ × ℝ → ℝ := fun z => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / β⁻¹)
  have hJ_int : Integrable J_prod := ComplMildGAux.integrable_gauss (a := β⁻¹) (inv_pos.2 hβ_pos)
  set I_J : ℝ := ∫ z, J_prod z
  have hJ_nn : 0 ≤ I_J := integral_nonneg fun _ => (Real.exp_pos _).le
  set K_cell : ℝ := Real.exp (β * (c / 2) ^ 2)
  have hcell_J : ∀ z ∈ B0579.cell c, Real.exp (-β * z.2 ^ 2) ≤ K_cell * J_prod z := by
    intro z hz
    have hz1 : z.1 ^ 2 ≤ (c / 2) ^ 2 :=
      sq_le_sq.2 ((abs_le.2 ⟨hz.1.1, hz.1.2.le⟩).trans (le_abs_self (c / 2)))
    have hβz1 : β * z.1 ^ 2 ≤ β * (c / 2) ^ 2 := mul_le_mul_of_nonneg_left hz1 hβ_pos.le
    dsimp [K_cell, J_prod]
    rw [← Real.exp_add, div_inv_eq_mul]
    refine Real.exp_le_exp.2 ?_
    have hrhs : β * (c / 2) ^ 2 + -(z.1 ^ 2 + z.2 ^ 2) * β =
        (β * (c / 2) ^ 2 - β * z.1 ^ 2) + (-β * z.2 ^ 2) := by ring
    rw [hrhs]
    linarith
  have hcont_u : ∀ (x : ℝ × ℝ) (k : Fin 2),
      ContinuousOn (fun τ => canonicalPhysVel P ν τ x k) I := by
    intro x k
    set L_u : ℝ := C_cv * M_w + C_cv * (M_w * K_cell * I_J)
    refine Metric.continuousOn_iff.2 fun τ₂ hτ₂ ε hε => ?_
    refine ⟨ε / (L_u + 1), div_pos hε (by dsimp [L_u, K_cell]; positivity), fun τ₁ hτ₁ hdist => ?_⟩
    -- Integrability of each single kernel integrand on `B0579.cell c`
    have hint_single : ∀ r ∈ I, IntegrableOn
        (fun z => canonicalPhysColumn P ν r z * (kerD c (x - z) k : ℂ)) (B0579.cell c) := by
      intro r hr
      have hsm_ker : Measurable (fun z => kerD c (x - z) k) :=
        (EulerErrorSub.measurable_kerD c k).comp (measurable_const.sub measurable_id)
      have haesm : AEStronglyMeasurable
          (fun z => canonicalPhysColumn P ν r z * (kerD c (x - z) k : ℂ))
          (volume.restrict (B0579.cell c)) :=
        ((hw_sm r (hI_U hr)).continuous.stronglyMeasurable.mul
          (Complex.continuous_ofReal.measurable.comp hsm_ker).stronglyMeasurable).aestronglyMeasurable
      have hL1_r : (∫⁻ z in B0579.cell c, ‖canonicalPhysColumn P ν r z‖ₑ) ≤
          ENNReal.ofReal ((M_w * K_cell) * I_J) := by
        have h := ComplMildGAux.lintegral_cell_le_of_integrable (d := c)
          (hJ_int.const_mul (M_w * K_cell))
          (fun z => by dsimp [K_cell, J_prod]; positivity)
          (F := canonicalPhysColumn P ν r) fun z hz => by
            calc ‖canonicalPhysColumn P ν r z‖ ≤ M_w * Real.exp (-β * z.2 ^ 2) :=
                  (hw_bd r (hI_U hr) z).1
              _ ≤ M_w * (K_cell * J_prod z) :=
                  mul_le_mul_of_nonneg_left (hcell_J z hz) hMw_pos.le
              _ = (M_w * K_cell) * J_prod z := by ring
        rwa [integral_const_mul] at h
      have hcv_r := hconv c hc1 (canonicalPhysColumn P ν r) (hw_per r (hI_U hr))
        M_w ((M_w * K_cell) * I_J) hMw_pos.le (by dsimp [K_cell]; positivity)
        (fun z => ((hw_bd r (hI_U hr) z).1).trans
          (mul_le_of_le_one_right hMw_pos.le (Real.exp_le_one_iff.2
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hβ_pos.le) (sq_nonneg z.2)))))
        hL1_r x k
      refine ⟨haesm, ?_⟩
      unfold HasFiniteIntegral
      refine (le_of_eq_of_le (setLIntegral_congr_fun (B0579.measurableSet_cell c) fun z _ => ?_)
        hcv_r).trans_lt ENNReal.ofReal_lt_top
      rw [enorm_mul]; congr 1; rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
    -- Apply `kerConv_le` to `Δw = canonicalPhysColumn P ν τ₁ - canonicalPhysColumn P ν τ₂`
    set Δw : ℝ × ℝ → ℂ := fun z => canonicalPhysColumn P ν τ₁ z - canonicalPhysColumn P ν τ₂ z
    have hsub_eq : canonicalPhysVel P ν τ₁ x k - canonicalPhysVel P ν τ₂ x k =
        kerVelCx c Δw x k := by
      unfold canonicalPhysVel kerVelCx
      change (∫ z in B0579.cell c, canonicalPhysColumn P ν τ₁ z * (kerD c (x - z) k : ℂ)) -
          (∫ z in B0579.cell c, canonicalPhysColumn P ν τ₂ z * (kerD c (x - z) k : ℂ)) = _
      rw [← integral_sub (hint_single τ₁ hτ₁) (hint_single τ₂ hτ₂)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      dsimp [Δw]; ring
    have hΔ_per : ∀ z : ℝ × ℝ, Δw (z.1 + c, z.2) = Δw z := fun z => by
      dsimp [Δw]; rw [hw_per τ₁ (hI_U hτ₁) z, hw_per τ₂ (hI_U hτ₂) z]
    set δ : ℝ := ‖τ₁ - τ₂‖
    have hΔ_sup : ∀ z : ℝ × ℝ, ‖Δw z‖ ≤ M_w * δ := fun z => by
      have h := hw_lip τ₁ hτ₁ τ₂ hτ₂ z
      have hexp1 : Real.exp (-β * z.2 ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hβ_pos.le) (sq_nonneg z.2))
      calc ‖Δw z‖ ≤ M_w * Real.exp (-β * z.2 ^ 2) * δ := h
        _ ≤ M_w * 1 * δ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp1 hMw_pos.le) (norm_nonneg _)
        _ = M_w * δ := by ring
    have hΔ_L1 : (∫⁻ z in B0579.cell c, ‖Δw z‖ₑ) ≤
        ENNReal.ofReal ((M_w * δ * K_cell) * I_J) := by
      have h := ComplMildGAux.lintegral_cell_le_of_integrable (d := c)
        (hJ_int.const_mul (M_w * δ * K_cell))
        (fun z => by dsimp [K_cell, J_prod, δ]; positivity) (F := Δw) fun z hz => by
          calc ‖Δw z‖ ≤ M_w * Real.exp (-β * z.2 ^ 2) * δ := hw_lip τ₁ hτ₁ τ₂ hτ₂ z
            _ ≤ M_w * (K_cell * J_prod z) * δ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hcell_J z hz) hMw_pos.le) (norm_nonneg _)
            _ = (M_w * δ * K_cell) * J_prod z := by ring
      rwa [integral_const_mul] at h
    have hcv_Δ := hconv c hc1 Δw hΔ_per (M_w * δ) ((M_w * δ * K_cell) * I_J)
      (by dsimp [δ]; positivity) (by dsimp [K_cell, δ]; positivity) hΔ_sup hΔ_L1 x k
    have hnorm_Δ : ‖kerVelCx c Δw x k‖ ≤ L_u * δ := by
      unfold kerVelCx
      have hen_eq : ∫⁻ z in B0579.cell c, ‖Δw z * (kerD c (x - z) k : ℂ)‖ₑ =
          ∫⁻ z in B0579.cell c, ‖Δw z‖ₑ * ‖kerD c (x - z) k‖ₑ :=
        setLIntegral_congr_fun (B0579.measurableSet_cell c) fun z _ => by
          rw [enorm_mul]; congr 1; rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
      have hen := (enorm_integral_le_lintegral_enorm _).trans (hen_eq.trans_le hcv_Δ)
      rw [← ofReal_norm] at hen
      have hle := (ENNReal.ofReal_le_ofReal_iff (by dsimp [K_cell, δ]; positivity)).1 hen
      calc ‖∫ z in B0579.cell c, Δw z * (kerD c (x - z) k : ℂ)‖
          ≤ C_cv * (M_w * δ) + C_cv * ((M_w * δ * K_cell) * I_J) := hle
        _ = L_u * δ := by dsimp [L_u]; ring
    rw [dist_eq_norm, hsub_eq]
    have hLu_nn : 0 ≤ L_u := by dsimp [L_u, K_cell]; positivity
    have hδ_lt : δ < ε / (L_u + 1) := by rw [dist_eq_norm] at hdist; exact hdist
    have hLu_pos : 0 < L_u + 1 := by linarith
    calc ‖kerVelCx c Δw x k‖ ≤ L_u * δ := hnorm_Δ
      _ ≤ (L_u + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (L_u + 1) * (ε / (L_u + 1)) := mul_lt_mul_of_pos_left hδ_lt hLu_pos
      _ = ε := mul_div_cancel₀ ε hLu_pos.ne'
  exact ⟨M_u, α_u, hMu_pos, hαu_pos, hdecay, hcont_u⟩

/-! ## 6. Residual symmetry, zero circulation, weak cylinder identity, and main theorem -/

private theorem isCentrallyEven_canonicalPhysResidual {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {ν s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (hs : 0 ≤ s) :
    IsCentrallyEven (canonicalPhysResidual P tr s) := by
  intro x
  rw [canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hs (-x),
    canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hs x]
  let c : ℝ := ν ^ (-2 : ℝ)
  obtain ⟨_, _, _, _, hw_sm, _, _, _, _, _, _⟩ :=
    canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hs
  have hs_U : s ∈ Ioo (-(1 / (4 * ν))) (s + 1 / 2) := by
    have : 0 < 1 / (4 * ν) := by positivity
    exact ⟨by linarith, by linarith⟩
  have hw_s_sm : ContDiff ℝ ∞ (canonicalPhysColumn P ν s) := hw_sm s hs_U
  -- 1. `∂_s w (-x) = ∂_s w x`
  have hdt_even : deriv (fun τ => canonicalPhysColumn P ν τ (-x)) s =
      deriv (fun τ => canonicalPhysColumn P ν τ x) s := by
    have hev : (fun τ => canonicalPhysColumn P ν τ (-x)) =ᶠ[𝓝 s]
        fun τ => canonicalPhysColumn P ν τ x := by
      filter_upwards [Ioo_mem_nhds hs_U.1 hs_U.2] with τ hτ
      have ha_τ : 0 < clockA ν τ := by
        unfold clockA
        have := mul_lt_mul_of_pos_left hτ.1 hν
        field_simp [hν.ne'] at this; linarith
      exact isCentrallyEven_canonicalPhysColumn P hν ha_τ x
    exact hev.deriv_eq
  -- 2. Parity of `pdCx` and `ladLapCx` on `canonicalPhysColumn P ν s`
  have ha_s : 0 < clockA ν s := by unfold clockA; nlinarith
  have hw_even : ∀ z : ℝ × ℝ, canonicalPhysColumn P ν s (-z) = canonicalPhysColumn P ν s z :=
    isCentrallyEven_canonicalPhysColumn P hν ha_s
  have hpd_parity : ∀ {g : ℝ × ℝ → ℂ}, Differentiable ℝ g → ∀ {sgn : ℂ},
      (∀ z, g (-z) = sgn * g z) → ∀ (k : Fin 2) (z : ℝ × ℝ),
        pdCx k g (-z) = -sgn * pdCx k g z := by
    intro g hg sgn hpar k z
    let negL : ℝ × ℝ →L[ℝ] ℝ × ℝ := -ContinuousLinearMap.id ℝ (ℝ × ℝ)
    have hcomp : HasFDerivAt (fun u => g (-u)) ((fderiv ℝ g (-z)).comp negL) z :=
      (hg (-z)).hasFDerivAt.comp z negL.hasFDerivAt
    have hfn : (fun u => g (-u)) = fun u => sgn * g u := funext hpar
    have hrhs : HasFDerivAt (fun u => sgn * g u) (sgn • fderiv ℝ g z) z :=
      (hg z).hasFDerivAt.const_mul sgn
    have heq_fd : (fderiv ℝ g (-z)).comp negL = sgn • fderiv ℝ g z := by
      rw [← hcomp.fderiv, hfn, hrhs.fderiv]
    have hap := ContinuousLinearMap.ext_iff.1 heq_fd (-B0579.dir k)
    simp only [negL, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, neg_neg, map_neg, smul_apply, smul_eq_mul] at hap
    unfold pdCx
    rw [hap]; ring
  have hpd_w_odd : ∀ (k : Fin 2) (z : ℝ × ℝ),
      pdCx k (canonicalPhysColumn P ν s) (-z) = -pdCx k (canonicalPhysColumn P ν s) z := by
    intro k z
    simpa using hpd_parity (hw_s_sm.differentiable (by simp))
      (sgn := 1) (fun u => by simpa using hw_even u) k z
  have hlap_even : ladLapCx (canonicalPhysColumn P ν s) (-x) =
      ladLapCx (canonicalPhysColumn P ν s) x := by
    unfold ladLapCx
    have hp0 := hpd_parity ((ibpPdCx_smooth hw_s_sm 0).differentiable (by simp))
      (sgn := -1) (fun u => by simpa using hpd_w_odd 0 u) 0 x
    have hp1 := hpd_parity ((ibpPdCx_smooth hw_s_sm 1).differentiable (by simp))
      (sgn := -1) (fun u => by simpa using hpd_w_odd 1 u) 1 x
    simp only [neg_neg, one_mul] at hp0 hp1
    rw [hp0, hp1]
  -- 3. `ladTransport` is even (`odd * odd`)
  have htr_even : ladTransport tr s (canonicalPhysColumn P ν s) (-x) =
      ladTransport tr s (canonicalPhysColumn P ν s) x := by
    unfold ladTransport
    have hv_odd := tr.isTrain.odd s hs x
    have hv0 : tr.v s (-x) 0 = -tr.v s x 0 := congrArg (fun u => u 0) hv_odd
    have hv1 : tr.v s (-x) 1 = -tr.v s x 1 := congrArg (fun u => u 1) hv_odd
    rw [hv0, hv1, hpd_w_odd 0 x, hpd_w_odd 1 x]
    push_cast; ring
  -- 4. Biot-Savart velocity is odd and `∇(Ec tr s)` is odd
  have hu_odd : ∀ k : Fin 2, canonicalPhysVel P ν s (-x) k = -canonicalPhysVel P ν s x k := by
    intro k
    unfold canonicalPhysVel kerVelCx
    rw [← integral_cell_comp_neg
      (fun z => canonicalPhysColumn P ν s z * (kerD (ν ^ (-2 : ℝ)) (-x - z) k : ℂ))]
    have hpt : (fun z : ℝ × ℝ =>
        canonicalPhysColumn P ν s (-z) * (kerD (ν ^ (-2 : ℝ)) (-x - -z) k : ℂ)) =
        fun z => -(canonicalPhysColumn P ν s z * (kerD (ν ^ (-2 : ℝ)) (x - z) k : ℂ)) := by
      funext z
      have harg : -x - -z = -(x - z) := by abel
      rw [hw_even z, harg, kerD_neg]
      push_cast; ring
    rw [hpt, integral_neg]
  have hEc_odd : ∀ k : Fin 2,
      B0579.pd k (UnforcedLeray.B0238.Ec tr s) (-x) =
        -B0579.pd k (UnforcedLeray.B0238.Ec tr s) x := by
    intro k
    have hEc_d : Differentiable ℝ (UnforcedLeray.B0238.Ec tr s) :=
      (ChiBoundAux.contDiff_Ec_slice tr hs).differentiable (by simp)
    let negL : ℝ × ℝ →L[ℝ] ℝ × ℝ := -ContinuousLinearMap.id ℝ (ℝ × ℝ)
    have hcomp : HasFDerivAt (fun z => UnforcedLeray.B0238.Ec tr s (-z))
        ((fderiv ℝ (UnforcedLeray.B0238.Ec tr s) (-x)).comp negL) x :=
      (hEc_d (-x)).hasFDerivAt.comp x negL.hasFDerivAt
    have hfn : (fun z => UnforcedLeray.B0238.Ec tr s (-z)) = UnforcedLeray.B0238.Ec tr s :=
      funext (UnforcedLeray.B0238.Ec_even tr hs)
    have heq_fd : (fderiv ℝ (UnforcedLeray.B0238.Ec tr s) (-x)).comp negL =
        fderiv ℝ (UnforcedLeray.B0238.Ec tr s) x := by
      rw [← hcomp.fderiv, hfn]
    have hap := ContinuousLinearMap.ext_iff.1 heq_fd (-B0579.dir k)
    simp only [negL, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, neg_neg, map_neg] at hap
    unfold B0579.pd
    rw [hap]
  rw [hdt_even, hlap_even, htr_even, hu_odd 0, hu_odd 1, hEc_odd 0, hEc_odd 1]
  push_cast; ring

/-- Spatial IBP identity on `B0579.cell c`:
`∫_cell flowIntegrand + ∫_cell canonicalPhysResidual * φ = ∫_cell (∂_s w) * φ`. -/
private theorem spatial_ibp_canonicalPhysColumn {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {m ν τ : ℝ} (hm : 8 < m) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (hτ : 0 ≤ τ)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest (ν ^ (-2 : ℝ)) φ) :
    let c : ℝ := ν ^ (-2 : ℝ)
    IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ)
      (B0579.cell c) ∧
    IntegrableOn (fun x => canonicalPhysResidual P tr τ x * (φ x : ℂ)) (B0579.cell c) ∧
    (∫ x in B0579.cell c,
        flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ x) +
      (∫ x in B0579.cell c, canonicalPhysResidual P tr τ x * (φ x : ℂ)) =
      ∫ x in B0579.cell c,
        deriv (fun r => canonicalPhysColumn P ν r x) τ * (φ x : ℂ) := by
  intro c
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  obtain ⟨_, _, _, _, hw_sm, hw_per, hdt_cont, _, _, _, _⟩ :=
    canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hτ
  have hτ_U : τ ∈ Ioo (-(1 / (4 * ν))) (τ + 1 / 2) := by
    have : 0 < 1 / (4 * ν) := by positivity
    exact ⟨by linarith, by linarith⟩
  set w : ℝ × ℝ → ℂ := canonicalPhysColumn P ν τ
  set u : ℝ × ℝ → Fin 2 → ℂ := canonicalPhysVel P ν τ
  have hws : ContDiff ℝ ∞ w := hw_sm τ hτ_U
  have hwp : ∀ x : ℝ × ℝ, w (x.1 + c, x.2) = w x := hw_per τ hτ_U
  have hwd : Differentiable ℝ w := hws.differentiable (by simp)
  have hBS : IsBiotSavart c w u :=
    isBiotSavart_canonicalPhysColumn hP hSmoothAll hVae hm hν hν1 hτ
  -- Train regularity & incompressibility at `τ ≥ 0` (same pattern as `AdjIBP.lean`)
  have hvC : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v τ x) :=
    tr.isTrain.smooth_v.comp_contDiff (contDiff_const.prodMk contDiff_id)
      fun _ => ⟨hτ, mem_univ _⟩
  have hcoord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 2) => v j) := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff
  have hvr : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => tr.v τ x j) := fun j =>
    ((hcoord j).comp hvC).differentiable (by simp)
  have hvj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v τ x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp ((hcoord j).comp hvC)
  have hvd : ∀ j : Fin 2, Differentiable ℝ (fun x : ℝ × ℝ => ((tr.v τ x j : ℝ) : ℂ)) :=
    fun j => (hvj j).differentiable (by simp)
  have hvper : ∀ x : ℝ × ℝ, tr.v τ (x.1 + c, x.2) = tr.v τ x :=
    fun x => tr.isTrain.periodic_v τ hτ x
  have hdiv : ∀ x : ℝ × ℝ, pdCx 0 (fun y => ((tr.v τ y 0 : ℝ) : ℂ)) x +
      pdCx 1 (fun y => ((tr.v τ y 1 : ℝ) : ℂ)) x = 0 := by
    intro x
    rw [ibpPdCx_ofReal _ (hvr 0) 0 x, ibpPdCx_ofReal _ (hvr 1) 1 x, ← Complex.ofReal_add]
    have hd := tr.isTrain.solenoidal τ hτ x
    unfold UnforcedLeray.Cyl.divergence at hd
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv (hvr 0) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv (hvr 1) x] at hd
    have hd' : B0579.pd 0 (fun y => tr.v τ y 0) x + B0579.pd 1 (fun y => tr.v τ y 1) x = 0 := hd
    rw [hd', Complex.ofReal_zero]
  have hΦs : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x => w x * ((tr.v τ x j : ℝ) : ℂ)) :=
    fun j => hws.mul (hvj j)
  have hΦper : ∀ j : Fin 2, ∀ x : ℝ × ℝ,
      w (x.1 + c, x.2) * ((tr.v τ (x.1 + c, x.2) j : ℝ) : ℂ) =
        w x * ((tr.v τ x j : ℝ) : ℂ) :=
    fun j x => by rw [hwp x, hvper x]
  have hP_tr : ∀ j : Fin 2,
      IntegrableOn (fun x => w x * ((tr.v τ x j : ℝ) : ℂ) * (B0579.pd j φ x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx j (fun y => w y * ((tr.v τ y j : ℝ) : ℂ)) x * (φ x : ℂ))
        (B0579.cell c) ∧
      ∫ x in B0579.cell c, w x * ((tr.v τ x j : ℝ) : ℂ) * (B0579.pd j φ x : ℂ) =
        -∫ x in B0579.cell c, pdCx j (fun y => w y * ((tr.v τ y j : ℝ) : ℂ)) x * (φ x : ℂ) :=
    fun j => mpWeakCore c hc0 _ (hΦs j) (hΦper j) j φ hφ
  have hLap : ∀ k : Fin 2,
      IntegrableOn (fun x => w x * (B0579.pd k (B0579.pd k φ) x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => pdCx k (pdCx k w) x * (φ x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, w x * (B0579.pd k (B0579.pd k φ) x : ℂ) =
        ∫ x in B0579.cell c, pdCx k (pdCx k w) x * (φ x : ℂ) := by
    intro k
    obtain ⟨i1, _, e1⟩ := mpWeakCore c hc0 w hws hwp k (B0579.pd k φ) (hφ.pd k)
    obtain ⟨_, i2, e2⟩ := mpWeakCore c hc0 (pdCx k w) (ibpPdCx_smooth hws k)
      (ibpPdCx_periodic k w hwp) k φ hφ
    refine ⟨i1, i2, ?_⟩
    rw [e1, e2, neg_neg]
  have hTpt : ∀ x : ℝ × ℝ,
      pdCx 0 (fun y => w y * ((tr.v τ y 0 : ℝ) : ℂ)) x * (φ x : ℂ) +
        pdCx 1 (fun y => w y * ((tr.v τ y 1 : ℝ) : ℂ)) x * (φ x : ℂ) =
        ladTransport tr τ w x * (φ x : ℂ) := by
    intro x
    rw [ibpPdCx_mul hwd (hvd 0) 0 x, ibpPdCx_mul hwd (hvd 1) 1 x]
    have hdx := hdiv x
    simp only [ladTransport]
    linear_combination (w x * (φ x : ℂ)) * hdx
  have hTint : IntegrableOn (fun x => ladTransport tr τ w x * (φ x : ℂ)) (B0579.cell c) :=
    ((hP_tr 0).2.1.add (hP_tr 1).2.1).congr_fun (fun x _ => by
      simp only [Pi.add_apply]; exact hTpt x) (B0579.measurableSet_cell c)
  have hLap_int_lhs : IntegrableOn (fun x => w x * (lapP φ x : ℂ)) (B0579.cell c) :=
    ((hLap 0).1.add (hLap 1).1).congr_fun (fun x _ => by
      simp only [Pi.add_apply, lapP]; push_cast; ring) (B0579.measurableSet_cell c)
  have hLap_int_rhs : IntegrableOn (fun x => ladLapCx w x * (φ x : ℂ)) (B0579.cell c) :=
    ((hLap 0).2.1.add (hLap 1).2.1).congr_fun (fun x _ => by
      simp only [Pi.add_apply, ladLapCx]; ring) (B0579.measurableSet_cell c)
  have hLap_ibp : ∫ x in B0579.cell c, w x * (lapP φ x : ℂ) =
      ∫ x in B0579.cell c, ladLapCx w x * (φ x : ℂ) := by
    have hsplit : (fun x => w x * (lapP φ x : ℂ)) = fun x =>
        w x * (B0579.pd 0 (B0579.pd 0 φ) x : ℂ) + w x * (B0579.pd 1 (B0579.pd 1 φ) x : ℂ) := by
      funext x; simp only [lapP]; push_cast; ring
    rw [hsplit, integral_add (hLap 0).1 (hLap 1).1, (hLap 0).2.2, (hLap 1).2.2,
      ← integral_add (hLap 0).2.1 (hLap 1).2.1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ladLapCx]; ring
  have hTr_int_lhs : IntegrableOn
      (fun x => w x * ((tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x : ℝ) : ℂ))
      (B0579.cell c) :=
    ((hP_tr 0).1.add (hP_tr 1).1).congr_fun (fun x _ => by
      simp only [Pi.add_apply]; push_cast; ring) (B0579.measurableSet_cell c)
  have hTr_ibp : ∫ x in B0579.cell c,
      w x * ((tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x : ℝ) : ℂ) =
      -∫ x in B0579.cell c, ladTransport tr τ w x * (φ x : ℂ) := by
    have hsplit : (fun x =>
        w x * ((tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x : ℝ) : ℂ)) =
        fun x => w x * ((tr.v τ x 0 : ℝ) : ℂ) * (B0579.pd 0 φ x : ℂ) +
          w x * ((tr.v τ x 1 : ℝ) : ℂ) * (B0579.pd 1 φ x : ℂ) := by
      funext x; push_cast; ring
    rw [hsplit, integral_add (hP_tr 0).1 (hP_tr 1).1, (hP_tr 0).2.2, (hP_tr 1).2.2, ← neg_add,
      ← integral_add (hP_tr 0).2.1 (hP_tr 1).2.1]
    congr 1
    exact integral_congr_ae (Eventually.of_forall hTpt)
  -- Biot-Savart stretch piece: `B0579.pd k (Ec tr τ) * φ` is a `B0579.IsCylTest c`
  have hEc_test : ∀ k : Fin 2, B0579.IsCylTest c
      (fun x => B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x * φ x) := by
    intro k
    have hEc_sm := ChiBoundAux.contDiff_Ec_slice tr hτ
    have hpd_sm : ContDiff ℝ ∞ (B0579.pd k (UnforcedLeray.B0238.Ec tr τ)) :=
      ((contDiff_infty_iff_fderiv.1 hEc_sm).2).clm_apply contDiff_const
    exact
      { smooth := hpd_sm.mul hφ.smooth
        periodic := fun x => by
          rw [ChiBoundAux.periodic_pd_Ec tr hτ k x, hφ.periodic x]
        band := by
          obtain ⟨R, hR⟩ := hφ.band
          exact ⟨R, fun x hx => by rw [hR x hx, mul_zero]⟩ }
  have hBS_int_k : ∀ k : Fin 2, IntegrableOn
      (fun x => u x k * (B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x : ℂ) * (φ x : ℂ))
      (B0579.cell c) := by
    intro k
    refine IntegrableOn.congr_fun (BSAux.integrable_u_mul (fun x => u x k) (hBS.1 k) (hEc_test k))
      (fun x _ => ?_) (B0579.measurableSet_cell c)
    push_cast; ring
  have hBS_int : IntegrableOn
      (fun x => (u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
        u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) * (φ x : ℂ))
      (B0579.cell c) :=
    IntegrableOn.congr_fun ((hBS_int_k 0).add (hBS_int_k 1)) (fun x _ => by
      simp only [Pi.add_apply]; ring) (B0579.measurableSet_cell c)
  have hflow_lhs_1 : IntegrableOn
      (fun x => w x * ((ν * lapP φ x +
        (tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x) : ℝ) : ℂ))
      (B0579.cell c) :=
    IntegrableOn.congr_fun ((hLap_int_lhs.const_mul (ν : ℂ)).add hTr_int_lhs) (fun x _ => by
      simp only [Pi.add_apply]; push_cast; ring) (B0579.measurableSet_cell c)
  have hflow_int : IntegrableOn (flowIntegrand tr w u τ φ) (B0579.cell c) :=
    hflow_lhs_1.sub hBS_int
  -- Time-derivative pairing integrability
  have hdt_φ_int : IntegrableOn
      (fun x => deriv (fun r => canonicalPhysColumn P ν r x) τ * (φ x : ℂ)) (B0579.cell c) := by
    have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
      unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
    rw [hcell]
    obtain ⟨R, hR⟩ := hφ.band
    have hv : UnforcedLeray.Cyl.VanishesOutside R
        (fun x => deriv (fun r => canonicalPhysColumn P ν r x) τ * (φ x : ℂ)) :=
      fun x hx => by simp [hR x hx]
    exact hv.integrableOn_cell
      ((hdt_cont τ hτ_U).mul (Complex.continuous_ofReal.comp hφ.continuous)) c
  -- Residual pairing integrability and cancellation
  have hres_pt : ∀ x : ℝ × ℝ, canonicalPhysResidual P tr τ x * (φ x : ℂ) =
      deriv (fun r => canonicalPhysColumn P ν r x) τ * (φ x : ℂ) -
        (ν : ℂ) * (ladLapCx w x * (φ x : ℂ)) +
        ladTransport tr τ w x * (φ x : ℂ) +
        (u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
          u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) * (φ x : ℂ) := by
    intro x
    rw [canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hτ x]
    dsimp [w, u]; ring
  have hres_int : IntegrableOn (fun x => canonicalPhysResidual P tr τ x * (φ x : ℂ))
      (B0579.cell c) :=
    (((hdt_φ_int.sub (hLap_int_rhs.const_mul (ν : ℂ))).add hTint).add hBS_int).congr_fun
      (fun x _ => (hres_pt x).symm) (B0579.measurableSet_cell c)
  refine ⟨hflow_int, hres_int, ?_⟩
  rw [← integral_add hflow_int hres_int]
  have hsum_pt : (fun x => flowIntegrand tr w u τ φ x +
      canonicalPhysResidual P tr τ x * (φ x : ℂ)) =
      fun x => deriv (fun r => canonicalPhysColumn P ν r x) τ * (φ x : ℂ) +
        ((ν : ℂ) * (w x * (lapP φ x : ℂ) - ladLapCx w x * (φ x : ℂ)) +
          (w x * ((tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x : ℝ) : ℂ) +
            ladTransport tr τ w x * (φ x : ℂ))) := by
    funext x
    unfold flowIntegrand
    rw [hres_pt x]
    push_cast; ring
  have h1_int : IntegrableOn (fun x => (ν : ℂ) * (w x * (lapP φ x : ℂ) - ladLapCx w x * (φ x : ℂ)))
      (B0579.cell c) := (hLap_int_lhs.sub hLap_int_rhs).const_mul (ν : ℂ)
  have h2_int : IntegrableOn (fun x =>
      w x * ((tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x : ℝ) : ℂ) +
        ladTransport tr τ w x * (φ x : ℂ)) (B0579.cell c) := hTr_int_lhs.add hTint
  have h12_int : IntegrableOn (fun x =>
      (ν : ℂ) * (w x * (lapP φ x : ℂ) - ladLapCx w x * (φ x : ℂ)) +
        (w x * ((tr.v τ x 0 * B0579.pd 0 φ x + tr.v τ x 1 * B0579.pd 1 φ x : ℝ) : ℂ) +
          ladTransport tr τ w x * (φ x : ℂ))) (B0579.cell c) :=
    IntegrableOn.congr_fun (h1_int.add h2_int) (fun _ _ => rfl) (B0579.measurableSet_cell c)
  rw [hsum_pt, integral_add hdt_φ_int h12_int, integral_add h1_int h2_int,
    integral_const_mul, integral_sub hLap_int_lhs hLap_int_rhs, hLap_ibp, sub_self, mul_zero,
    integral_add hTr_int_lhs hTint, hTr_ibp, neg_add_cancel, add_zero, add_zero]

/-- Zero circulation `HasZeroCirculation c (canonicalPhysResidual P tr s)` (`m > 8`). -/
private theorem hasZeroCirculation_canonicalPhysResidual {P : PlanarData} (hP : IsPlanarReference P)
    {V : ℝ → UnforcedLeray.B0010.XG}
    (hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {m ν s : ℝ} (hm : 8 < m) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hBUC : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hs : 0 ≤ s)
    (hmem : MemLp (canonicalPhysResidual P tr s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) :
    HasZeroCirculation (ν ^ (-2 : ℝ)) (canonicalPhysResidual P tr s) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hint_res : IntegrableOn (canonicalPhysResidual P tr s) (B0579.cell c) :=
    zcCellIntegrable c m (by linarith) _ hmem
  refine ⟨hint_res, ?_⟩
  obtain ⟨M_w, β, hMw_pos, hβ_pos, hw_sm, hw_per, hdt_cont, hw_hd, hw_bd, _, _⟩ :=
    canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hs
  let U : Set ℝ := Ioo (-(1 / (4 * ν))) (s + 1 / 2)
  have hs_U : s ∈ U := by
    dsimp [U]
    have : 0 < 1 / (4 * ν) := by positivity
    exact ⟨by linarith, by linarith⟩
  have hcell_eq : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  -- Helper: any continuous `g` bounded by `C * exp(-β * x.2 ^ 2)` is `IntegrableOn` on `B0579.cell c`
  have hint_gauss : ∀ {g : ℝ × ℝ → ℂ} {C_g : ℝ}, 0 ≤ C_g → Continuous g →
      (∀ x : ℝ × ℝ, ‖g x‖ ≤ C_g * Real.exp (-β * x.2 ^ 2)) →
      IntegrableOn g (B0579.cell c) := by
    intro g C_g hCg hg_c hg_b
    refine zcCellIntegrable c m (by linarith) g ?_
    refine memLp_of_exp_eta hc0 (by linarith) hβ_pos (by positivity : 0 ≤ C_g * Real.exp β)
      hg_c.aestronglyMeasurable fun x _ => ?_
    calc ‖g x‖ ≤ C_g * Real.exp (-β * x.2 ^ 2) := hg_b x
      _ ≤ C_g * (Real.exp β * Real.exp (-β * |x.2|)) :=
          mul_le_mul_of_nonneg_left (exp_sq_le_exp_abs hβ_pos x.2) hCg
      _ = (C_g * Real.exp β) * Real.exp (-β * |x.2|) := by ring
  -- Piece 1: `∫_{cell c} deriv (w · x) s = 0` by differentiating `r ↦ ∫_{cell c} w r x = 0` at `s`
  have hint_dt : IntegrableOn (fun x => deriv (fun r => canonicalPhysColumn P ν r x) s)
      (B0579.cell c) ∧
      ∫ x in B0579.cell c, deriv (fun r => canonicalPhysColumn P ν r x) s = 0 := by
    let μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
    have hdom_exp : Integrable (fun x : ℝ × ℝ => M_w * Real.exp (-β * x.2 ^ 2)) μ := by
      have hc_dom : Continuous (fun x : ℝ × ℝ => ((M_w * Real.exp (-β * x.2 ^ 2) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp
          (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
            (continuous_snd.pow 2))))
      have hi := hint_gauss hMw_pos.le hc_dom fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact IntegrableOn.congr_fun hi.re (fun _ _ => rfl) (B0579.measurableSet_cell c)
    have hhd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun r x => canonicalPhysColumn P ν r x)
      (F' := fun r x => deriv (fun t => canonicalPhysColumn P ν t x) r)
      (bound := fun x => M_w * Real.exp (-β * x.2 ^ 2))
      (Ioo_mem_nhds hs_U.1 hs_U.2)
      (by filter_upwards [Ioo_mem_nhds hs_U.1 hs_U.2] with r hr
          exact (hw_sm r hr).continuous.aestronglyMeasurable)
      (hint_gauss hMw_pos.le (hw_sm s hs_U).continuous fun x => (hw_bd s hs_U x).1)
      (hdt_cont s hs_U).aestronglyMeasurable
      (Eventually.of_forall fun x r hr => (hw_bd r hr x).2.2.2)
      hdom_exp
      (Eventually.of_forall fun x r hr => hw_hd r hr x)
    refine ⟨hhd.1, ?_⟩
    have hzero_U : ∀ r ∈ U, ∫ x in B0579.cell c, canonicalPhysColumn P ν r x = 0 := by
      intro r hr
      have ha_r : 0 < clockA ν r := by
        unfold clockA
        have := mul_lt_mul_of_pos_left hr.1 hν
        field_simp [hν.ne'] at this; linarith
      have hθ_r : 0 < clockTheta ν r := inv_pos.2 (mul_pos hν ha_r)
      have hfn : canonicalPhysColumn P ν r = fun x => P.gaugeFactor ν *
          periodizeC c (Jscale (clockA ν r) (canonMode P (clockTheta ν r))) x :=
        funext fun x => canonicalPhysColumn_eq_periodizeC_planar P hν ha_r x
      rw [hfn, integral_const_mul,
        integral_cell_periodizeC_jscale_canonMode hP hSmoothAll hVae hc0 ha_r hθ_r, mul_zero]
    have hev0 : (fun r => ∫ x, canonicalPhysColumn P ν r x ∂μ) =ᶠ[𝓝 s] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds hs_U.1 hs_U.2] with r hr
      exact hzero_U r hr
    exact hhd.2.unique ((hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq hev0)
  -- Piece 2: `∫_{cell c} ladLapCx (w s) = 0` via `Cyl.integral_cell_deriv_q_of_periodic` & `deriv_eta`
  set w : ℝ × ℝ → ℂ := canonicalPhysColumn P ν s
  have hws : ContDiff ℝ ∞ w := hw_sm s hs_U
  have hwp : ∀ x : ℝ × ℝ, w (x.1 + c, x.2) = w x := hw_per s hs_U
  have hslice_deriv : ∀ {G : ℝ × ℝ → ℂ}, Differentiable ℝ G → ∀ q η : ℝ,
      HasDerivAt (fun q' => G (q', η)) (pdCx 0 G (q, η)) q ∧
      HasDerivAt (fun η' => G (q, η')) (pdCx 1 G (q, η)) η := by
    intro G hG q η
    constructor
    · have h := (hG (q, η)).hasFDerivAt.comp_hasDerivAt q
        ((hasDerivAt_id q).prodMk (hasDerivAt_const q η))
      simpa [pdCx, B0579.dir, Function.comp_def] using h
    · have h := (hG (q, η)).hasFDerivAt.comp_hasDerivAt η
        ((hasDerivAt_const η q).prodMk (hasDerivAt_id η))
      simpa [pdCx, B0579.dir, Function.comp_def] using h
  have hpd2_eq_it : ∀ (k : Fin 2) (x : ℝ × ℝ),
      pdCx k (pdCx k w) x = iteratedFDeriv ℝ 2 w x ![B0579.dir k, B0579.dir k] := by
    intro k x
    have h1 : pdCx k w = fun y => iteratedFDeriv ℝ 1 w y ![B0579.dir k] := by
      funext y; rw [iteratedFDeriv_one_apply]; rfl
    unfold pdCx
    change fderiv ℝ (pdCx k w) x (B0579.dir k) = _
    rw [h1]
    let evk : ((ℝ × ℝ) [×1]→L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × ℝ) ℂ ![B0579.dir k]
    have hcomp : HasFDerivAt (fun y => evk (iteratedFDeriv ℝ 1 w y))
        (evk.comp (fderiv ℝ (iteratedFDeriv ℝ 1 w) x)) x :=
      evk.hasFDerivAt.comp x
        ((hws.differentiable_iteratedFDeriv (by simp)) x).hasFDerivAt
    rw [show (fun y => iteratedFDeriv ℝ 1 w y ![B0579.dir k]) =
      fun y => evk (iteratedFDeriv ℝ 1 w y) from rfl, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, evk, ContinuousMultilinearMap.apply_apply]
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl
  have hpd2_bd : ∀ (k : Fin 2) (x : ℝ × ℝ),
      ‖pdCx k (pdCx k w) x‖ ≤ M_w * Real.exp (-β * x.2 ^ 2) := by
    intro k x
    rw [hpd2_eq_it k x]
    have hv_dir : ∀ i : Fin 2, ‖(![B0579.dir k, B0579.dir k] : Fin 2 → ℝ × ℝ) i‖ ≤ 1 := by
      intro i; fin_cases i <;> fin_cases k <;> simp [B0579.dir]
    have hev : ‖iteratedFDeriv ℝ 2 w x ![B0579.dir k, B0579.dir k]‖ ≤ ‖iteratedFDeriv ℝ 2 w x‖ := by
      refine ((iteratedFDeriv ℝ 2 w x).le_opNorm _).trans ?_
      calc _ ≤ ‖iteratedFDeriv ℝ 2 w x‖ * ∏ _i : Fin 2, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hv_dir i)
              (norm_nonneg _)
        _ = _ := by simp
    exact hev.trans (hw_bd s hs_U x).2.2.1.2
  have hint_pd2 : ∀ k : Fin 2, IntegrableOn (pdCx k (pdCx k w)) (B0579.cell c) :=
    fun k => hint_gauss hMw_pos.le (ibpPdCx_smooth (ibpPdCx_smooth hws k) k).continuous (hpd2_bd k)
  have hz_pd00 : ∫ x in B0579.cell c, pdCx 0 (pdCx 0 w) x = 0 := by
    rw [hcell_eq]
    exact UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc0 (ibpPdCx_periodic 0 w hwp)
      (fun q η => (hslice_deriv ((ibpPdCx_smooth hws 0).differentiable (by simp)) q η).1)
      (hcell_eq ▸ hint_pd2 0)
  have hz_pd11 : ∫ x in B0579.cell c, pdCx 1 (pdCx 1 w) x = 0 := by
    rw [hcell_eq]
    exact UnforcedLeray.Cyl.integral_cell_deriv_eta
      (fun q η => (hslice_deriv ((ibpPdCx_smooth hws 1).differentiable (by simp)) q η).2)
      (hcell_eq ▸ hint_gauss hMw_pos.le (ibpPdCx_smooth hws 1).continuous
        fun x => (hw_bd s hs_U x).2.1 1)
      (hcell_eq ▸ hint_pd2 1)
  have hint_lap : IntegrableOn (ladLapCx w) (B0579.cell c) :=
    ((hint_pd2 0).add (hint_pd2 1)).congr_fun (fun _ _ => rfl) (B0579.measurableSet_cell c)
  have hz_lap : ∫ x in B0579.cell c, ladLapCx w x = 0 := by
    have hfn : ladLapCx w = fun x => pdCx 0 (pdCx 0 w) x + pdCx 1 (pdCx 1 w) x := rfl
    rw [hfn, integral_add (hint_pd2 0) (hint_pd2 1), hz_pd00, hz_pd11, add_zero]
  -- Piece 3: `∫_{cell c} ladTransport tr s w = 0` via divergence-free form `∂_q (w v_q) + ∂_η (w v_η)`
  obtain ⟨V₀, hV₀⟩ := hBUC.sup_bound hs
  obtain ⟨V₁, hV₁⟩ := hBUC.deriv_bound hs 1
  set C_V : ℝ := |V₀| + |V₁| + 1
  have hCV_pos : 0 < C_V := by dsimp [C_V]; positivity
  have hvC : ContDiff ℝ ∞ (tr.v s) := UnforcedLeray.B0238.contDiff_Vc tr hs
  have hv_r : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v s x j) := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hvC
  have hvj : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v s x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp (hv_r j)
  have hv0_bd : ∀ (j : Fin 2) (x : ℝ × ℝ), ‖((tr.v s x j : ℝ) : ℂ)‖ ≤ C_V := by
    intro j x
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |tr.v s x j| = ‖tr.v s x j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖tr.v s x‖ := PiLp.norm_apply_le (tr.v s x) j
      _ ≤ V₀ := hV₀ s ⟨hs, le_rfl⟩ x
      _ ≤ C_V := (le_abs_self V₀).trans (by dsimp [C_V]; linarith [abs_nonneg V₁])
  have hv_pd_bd : ∀ (k j : Fin 2) (x : ℝ × ℝ),
      |B0579.pd k (fun y => tr.v s y j) x| ≤ C_V := by
    intro k j x
    have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
    have h1 : ‖B0579.pd k (fun y => tr.v s y j) x‖ ≤
        ‖fderiv ℝ (fun y => tr.v s y j) x‖ :=
      ((fderiv ℝ (fun y => tr.v s y j) x).le_opNorm (B0579.dir k)).trans
        (mul_le_of_le_one_right (norm_nonneg _) hdir)
    rw [← Real.norm_eq_abs]
    calc ‖B0579.pd k (fun y => tr.v s y j) x‖
        ≤ ‖iteratedFDeriv ℝ 1 (fun y => tr.v s y j) x‖ := by rwa [norm_iteratedFDeriv_one]
      _ ≤ ‖iteratedFDeriv ℝ 1 (tr.v s) x‖ :=
          ChiBoundAux.norm_iteratedFDeriv_proj_le (tr.v s) hvC j 1 x
      _ ≤ V₁ := hV₁ s ⟨hs, le_rfl⟩ x
      _ ≤ C_V := (le_abs_self V₁).trans (by dsimp [C_V]; linarith [abs_nonneg V₀])
  set F_tr : Fin 2 → ℝ × ℝ → ℂ := fun j x => w x * ((tr.v s x j : ℝ) : ℂ)
  have hFtr_sm : ∀ j : Fin 2, ContDiff ℝ ∞ (F_tr j) := fun j => hws.mul (hvj j)
  have hFtr_bd : ∀ (j : Fin 2) (x : ℝ × ℝ),
      ‖F_tr j x‖ ≤ (M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by
    intro j x
    dsimp [F_tr]
    rw [norm_mul]
    calc ‖w x‖ * ‖((tr.v s x j : ℝ) : ℂ)‖
        ≤ (M_w * Real.exp (-β * x.2 ^ 2)) * C_V :=
          mul_le_mul ((hw_bd s hs_U x).1) (hv0_bd j x) (norm_nonneg _) (by positivity)
      _ = (M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by ring
  have hdFtr_bd : ∀ (j : Fin 2) (x : ℝ × ℝ),
      ‖pdCx j (F_tr j) x‖ ≤ (2 * M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by
    intro j x
    have hmul := ibpPdCx_mul (hws.differentiable (by simp))
      ((hvj j).differentiable (by simp)) j x
    change pdCx j (F_tr j) x = _ at hmul
    rw [hmul, ibpPdCx_ofReal _ ((hv_r j).differentiable (by simp)) j x]
    have hp1 : ‖pdCx j w x * ((tr.v s x j : ℝ) : ℂ)‖ ≤
        (M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by
      rw [norm_mul]
      calc ‖pdCx j w x‖ * ‖((tr.v s x j : ℝ) : ℂ)‖
          ≤ (M_w * Real.exp (-β * x.2 ^ 2)) * C_V :=
            mul_le_mul ((hw_bd s hs_U x).2.1 j) (hv0_bd j x) (norm_nonneg _) (by positivity)
        _ = (M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by ring
    have hp2 : ‖w x * (B0579.pd j (fun y => tr.v s y j) x : ℂ)‖ ≤
        (M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖w x‖ * |B0579.pd j (fun y => tr.v s y j) x|
          ≤ (M_w * Real.exp (-β * x.2 ^ 2)) * C_V :=
            mul_le_mul ((hw_bd s hs_U x).1) (hv_pd_bd j j x) (abs_nonneg _) (by positivity)
        _ = (M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by ring
    calc ‖pdCx j w x * ((tr.v s x j : ℝ) : ℂ) + w x * (B0579.pd j (fun y => tr.v s y j) x : ℂ)‖
        ≤ ‖pdCx j w x * ((tr.v s x j : ℝ) : ℂ)‖ +
            ‖w x * (B0579.pd j (fun y => tr.v s y j) x : ℂ)‖ := norm_add_le _ _
      _ ≤ (2 * M_w * C_V) * Real.exp (-β * x.2 ^ 2) := by linarith
  have hint_Ftr : ∀ j : Fin 2, IntegrableOn (F_tr j) (B0579.cell c) := fun j =>
    hint_gauss (by positivity) (hFtr_sm j).continuous (hFtr_bd j)
  have hint_dFtr : ∀ j : Fin 2, IntegrableOn (pdCx j (F_tr j)) (B0579.cell c) := fun j =>
    hint_gauss (by positivity) (ibpPdCx_smooth (hFtr_sm j) j).continuous (hdFtr_bd j)
  have hFtr0_per : UnforcedLeray.Cyl.IsPeriodic c (F_tr 0) := fun x => by
    dsimp [F_tr]
    rw [hwp x, tr.isTrain.periodic_v s hs x]
  have hz_tr0 : ∫ x in B0579.cell c, pdCx 0 (F_tr 0) x = 0 := by
    rw [hcell_eq]
    exact UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc0 hFtr0_per
      (fun q η => (hslice_deriv ((hFtr_sm 0).differentiable (by simp)) q η).1)
      (hcell_eq ▸ hint_dFtr 0)
  have hz_tr1 : ∫ x in B0579.cell c, pdCx 1 (F_tr 1) x = 0 := by
    rw [hcell_eq]
    exact UnforcedLeray.Cyl.integral_cell_deriv_eta
      (fun q η => (hslice_deriv ((hFtr_sm 1).differentiable (by simp)) q η).2)
      (hcell_eq ▸ hint_Ftr 1) (hcell_eq ▸ hint_dFtr 1)
  have htr_div : ∀ x : ℝ × ℝ, pdCx 0 (F_tr 0) x + pdCx 1 (F_tr 1) x = ladTransport tr s w x := by
    intro x
    have hm0 := ibpPdCx_mul (hws.differentiable (by simp)) ((hvj 0).differentiable (by simp)) 0 x
    have hm1 := ibpPdCx_mul (hws.differentiable (by simp)) ((hvj 1).differentiable (by simp)) 1 x
    change pdCx 0 (F_tr 0) x = _ at hm0
    change pdCx 1 (F_tr 1) x = _ at hm1
    rw [hm0, hm1, ibpPdCx_ofReal _ ((hv_r 0).differentiable (by simp)) 0 x,
      ibpPdCx_ofReal _ ((hv_r 1).differentiable (by simp)) 1 x]
    have hd := tr.isTrain.solenoidal s hs x
    unfold UnforcedLeray.Cyl.divergence at hd
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv ((hv_r 0).differentiable (by simp)) x,
      UnforcedLeray.Cyl.partialEta_eq_fderiv ((hv_r 1).differentiable (by simp)) x] at hd
    have hd' : B0579.pd 0 (fun y => tr.v s y 0) x + B0579.pd 1 (fun y => tr.v s y 1) x = 0 := hd
    have hdc : (B0579.pd 0 (fun y => tr.v s y 0) x : ℂ) +
        (B0579.pd 1 (fun y => tr.v s y 1) x : ℂ) = 0 := by
      rw [← Complex.ofReal_add, hd', Complex.ofReal_zero]
    simp only [ladTransport]
    linear_combination w x * hdc
  have hint_tr : IntegrableOn (ladTransport tr s w) (B0579.cell c) :=
    ((hint_dFtr 0).add (hint_dFtr 1)).congr_fun
      (fun x _ => by simp only [Pi.add_apply]; exact htr_div x) (B0579.measurableSet_cell c)
  have hz_tr : ∫ x in B0579.cell c, ladTransport tr s w x = 0 := by
    have hfn : ladTransport tr s w = fun x => pdCx 0 (F_tr 0) x + pdCx 1 (F_tr 1) x :=
      funext fun x => (htr_div x).symm
    rw [hfn, integral_add (hint_dFtr 0) (hint_dFtr 1), hz_tr0, hz_tr1, add_zero]
  -- Piece 4: `∫_{cell c} (u · ∇(Ec tr s)) = 0` via `div u = 0` tested against `Ec tr s * cutT n`
  set u : ℝ × ℝ → Fin 2 → ℂ := canonicalPhysVel P ν s
  have hBS : IsBiotSavart c w u :=
    isBiotSavart_canonicalPhysColumn hP hSmoothAll hVae hm hν hν1 hs
  set S_bs : ℝ × ℝ → ℂ := fun x =>
    u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
      u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)
  have hres_eq : ∀ x : ℝ × ℝ, canonicalPhysResidual P tr s x =
      deriv (fun r => canonicalPhysColumn P ν r x) s - (ν : ℂ) * ladLapCx w x +
        ladTransport tr s w x + S_bs x :=
    fun x => canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hs x
  have hSbs_int : IntegrableOn S_bs (B0579.cell c) :=
    (hint_res.sub ((hint_dt.1.sub (hint_lap.const_mul (ν : ℂ))).add hint_tr)).congr_fun
      (fun x _ => by simp only [Pi.sub_apply, Pi.add_apply]; rw [hres_eq x]; ring)
      (B0579.measurableSet_cell c)
  have hEc_sm : ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr s) := ChiBoundAux.contDiff_Ec_slice tr hs
  have hEc_per : ∀ z : ℝ × ℝ,
      UnforcedLeray.B0238.Ec tr s (z.1 + c, z.2) = UnforcedLeray.B0238.Ec tr s z := by
    intro z
    have hp1 : UnforcedLeray.Cyl.IsPeriodic c (fun z' : ℝ × ℝ => tr.v s z' 1) :=
      fun z' => congrArg (fun q => q 1) (tr.isTrain.periodic_v s hs z')
    have hp0 : UnforcedLeray.Cyl.IsPeriodic c (fun z' : ℝ × ℝ => tr.v s z' 0) :=
      fun z' => congrArg (fun q => q 0) (tr.isTrain.periodic_v s hs z')
    unfold UnforcedLeray.B0238.Ec UnforcedLeray.Cyl.curl
    rw [hp1.partialQ z, hp0.partialEta z]
  have hEc_bd : ∀ x : ℝ × ℝ, |UnforcedLeray.B0238.Ec tr s x| ≤ 2 * C_V := by
    intro x
    have heq := congrFun (ChiBoundAux.Ec_eq_pd_sub tr hs) x
    dsimp at heq
    rw [heq]
    calc |B0579.pd 0 (fun z => tr.v s z 1) x - B0579.pd 1 (fun z => tr.v s z 0) x|
        ≤ |B0579.pd 0 (fun z => tr.v s z 1) x| + |B0579.pd 1 (fun z => tr.v s z 0) x| :=
          abs_sub _ _
      _ ≤ C_V + C_V := add_le_add (hv_pd_bd 0 1 x) (hv_pd_bd 1 0 x)
      _ = 2 * C_V := by ring
  have hz_Sbs : ∫ x in B0579.cell c, S_bs x = 0 := by
    let μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
    obtain ⟨M_chi, hMchi0, hMchi⟩ := zcChiDeriv
    set A : ℝ := (eLpNorm (fun x => u x 1) 2 μ).toReal
    set C_g : ℝ := 2 * C_V * M_chi
    have hCg0 : 0 ≤ C_g := by dsimp [C_g]; positivity
    set B : ℕ → ℝ := fun n => C_g * Real.sqrt (4 * c * (1 / ((n : ℝ) + 1)))
    have hbound : ∀ n : ℕ, ‖∫ x in B0579.cell c, S_bs x * (B0285.cutT n x : ℂ)‖ ≤ A * B n := by
      intro n
      obtain ⟨htest, hpd0, hpd1⟩ := zcCutoffTest c n
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      let ψ_n : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0238.Ec tr s x * B0285.cutT n x
      let g_n : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0238.Ec tr s x * B0579.pd 1 (B0285.cutT n) x
      have hψ_test : B0579.IsCylTest c ψ_n :=
        { smooth := hEc_sm.mul htest.smooth
          periodic := fun x => by dsimp [ψ_n]; rw [hEc_per x, htest.periodic x]
          band := by
            obtain ⟨R, hR⟩ := htest.band
            exact ⟨R, fun x hx => by dsimp [ψ_n]; rw [hR x hx, mul_zero]⟩ }
      have hg_test : B0579.IsCylTest c g_n :=
        { smooth := hEc_sm.mul (htest.pd 1).smooth
          periodic := fun x => by dsimp [g_n]; rw [hEc_per x, (htest.pd 1).periodic x]
          band := by
            obtain ⟨R, hR⟩ := (htest.pd 1).band
            exact ⟨R, fun x hx => by dsimp [g_n]; rw [hR x hx, mul_zero]⟩ }
      have hpd_ψ : ∀ (k : Fin 2) (x : ℝ × ℝ), B0579.pd k ψ_n x =
          B0579.pd k (UnforcedLeray.B0238.Ec tr s) x * B0285.cutT n x +
            UnforcedLeray.B0238.Ec tr s x * B0579.pd k (B0285.cutT n) x := by
        intro k x
        have hfd := ((hEc_sm.differentiable (by simp) x).hasFDerivAt.mul
          (htest.smooth.differentiable (by simp) x).hasFDerivAt).fderiv
        unfold B0579.pd
        change fderiv ℝ (UnforcedLeray.B0238.Ec tr s * B0285.cutT n) x (B0579.dir k) = _
        rw [hfd]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      have hpt_div : ∀ x : ℝ × ℝ,
          u x 0 * (B0579.pd 0 ψ_n x : ℂ) + u x 1 * (B0579.pd 1 ψ_n x : ℂ) =
            S_bs x * (B0285.cutT n x : ℂ) + u x 1 * (g_n x : ℂ) := by
        intro x
        rw [hpd_ψ 0 x, hpd_ψ 1 x, hpd0 x]
        dsimp [S_bs, g_n]
        push_cast; ring
      have hlhs_int : IntegrableOn
          (fun x => u x 0 * (B0579.pd 0 ψ_n x : ℂ) + u x 1 * (B0579.pd 1 ψ_n x : ℂ))
          (B0579.cell c) :=
        (BSAux.integrable_u_mul _ (hBS.1 0) (hψ_test.pd 0)).add
          (BSAux.integrable_u_mul _ (hBS.1 1) (hψ_test.pd 1))
      have hgu_int : IntegrableOn (fun x => u x 1 * (g_n x : ℂ)) (B0579.cell c) :=
        BSAux.integrable_u_mul _ (hBS.1 1) hg_test
      have hScut_int : IntegrableOn (fun x => S_bs x * (B0285.cutT n x : ℂ)) (B0579.cell c) :=
        IntegrableOn.congr_fun (hlhs_int.sub hgu_int)
          (fun x _ => by simp only [Pi.sub_apply]; rw [hpt_div x]; ring)
          (B0579.measurableSet_cell c)
      have hdiv0 := hBS.2.1 ψ_n hψ_test
      have hsum0 : (∫ x in B0579.cell c, S_bs x * (B0285.cutT n x : ℂ)) +
          (∫ x in B0579.cell c, u x 1 * (g_n x : ℂ)) = 0 := by
        rw [← integral_add hScut_int hgu_int]
        exact (integral_congr_ae (Eventually.of_forall fun x => (hpt_div x).symm)).trans hdiv0
      have hid_norm : ‖∫ x in B0579.cell c, S_bs x * (B0285.cutT n x : ℂ)‖ =
          ‖∫ x in B0579.cell c, u x 1 * (g_n x : ℂ)‖ := by
        rw [eq_neg_of_add_eq_zero_left hsum0, norm_neg]
      have hgb : ∀ x : ℝ × ℝ, |g_n x| ≤ C_g / ((n : ℝ) + 1) := by
        intro x
        dsimp [g_n, C_g]
        rw [abs_mul, hpd1 x, abs_mul, abs_inv, abs_of_pos hpos]
        calc |UnforcedLeray.B0238.Ec tr s x| * (|deriv B0285.chi0 (((n : ℝ) + 1)⁻¹ * x.2)| *
              ((n : ℝ) + 1)⁻¹)
            ≤ (2 * C_V) * (M_chi * ((n : ℝ) + 1)⁻¹) :=
              mul_le_mul (hEc_bd x)
                (mul_le_mul_of_nonneg_right (hMchi _).1 (inv_nonneg.2 hpos.le))
                (by positivity) (by positivity)
          _ = 2 * C_V * M_chi / ((n : ℝ) + 1) := by rw [div_eq_mul_inv]; ring
      have hgv : ∀ x : ℝ × ℝ, 2 * ((n : ℝ) + 1) < |x.2| → g_n x = 0 := by
        intro x hx
        have hy : 2 < |((n : ℝ) + 1)⁻¹ * x.2| := by
          rw [abs_mul, abs_inv, abs_of_pos hpos, lt_inv_mul_iff₀ hpos]
          linarith
        dsimp [g_n]
        rw [hpd1 x, (hMchi _).2 hy, zero_mul, mul_zero]
      have hL2 := zcBandL2 c hc0 g_n (C_g / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1))
        (div_nonneg hCg0 hpos.le) (by positivity) hg_test.continuous hgb hgv
      have hmemg : MemLp g_n 2 μ :=
        ⟨hg_test.continuous.aestronglyMeasurable, hL2.trans_lt ENNReal.ofReal_lt_top⟩
      have hCS := zcCauchySchwarz μ (fun x => u x 1) g_n (hBS.1 1) hmemg
      have hgle : (eLpNorm g_n 2 μ).toReal ≤ B n := by
        have heq := zc_bound_eq C_g c ((n : ℝ) + 1) hpos
        dsimp [B]
        rw [← heq]
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL2
      rw [hid_norm]
      exact hCS.trans (mul_le_mul_of_nonneg_left hgle ENNReal.toReal_nonneg)
    have hlim : Tendsto (fun n : ℕ => A * B n) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcont : Continuous fun ε : ℝ => A * (C_g * Real.sqrt (4 * c * ε)) := by fun_prop
      simpa [Function.comp_def, B] using (hcont.tendsto 0).comp h1
    exact tendsto_nhds_unique (zcCutoffLimit c S_bs hSbs_int) (squeeze_zero_norm hbound hlim)
  -- Combine all four pieces
  have h1_res_int : IntegrableOn
      (fun x => deriv (fun r => canonicalPhysColumn P ν r x) s - (ν : ℂ) * ladLapCx w x)
      (B0579.cell c) :=
    IntegrableOn.congr_fun (hint_dt.1.sub (hint_lap.const_mul (ν : ℂ))) (fun _ _ => rfl)
      (B0579.measurableSet_cell c)
  have h2_res_int : IntegrableOn (fun x => ladTransport tr s w x + S_bs x) (B0579.cell c) :=
    IntegrableOn.congr_fun (hint_tr.add hSbs_int) (fun _ _ => rfl) (B0579.measurableSet_cell c)
  have hfn_res : canonicalPhysResidual P tr s = fun x =>
      (deriv (fun r => canonicalPhysColumn P ν r x) s - (ν : ℂ) * ladLapCx w x) +
        (ladTransport tr s w x + S_bs x) := by
    funext x; rw [hres_eq x]; ring
  rw [hfn_res, integral_add h1_res_int h2_res_int,
    integral_sub hint_dt.1 (hint_lap.const_mul (ν : ℂ)), integral_const_mul,
    integral_add hint_tr hSbs_int, hint_dt.2, hz_lap, hz_tr, hz_Sbs]
  ring

end UnforcedLeray.Short.IIIa.T22Sub.ColumnWeakEqAux

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.IIIa.T22Sub.ResidualBoundAux
open UnforcedLeray.Short.IIIa.T22Sub.ColumnWeakEqAux

/-- Proof of `ResidualBoundAux.CanonicalColumnWeakEq` (SP 3130-3140). -/
theorem canonicalColumnWeakEq_proof : ResidualBoundAux.CanonicalColumnWeakEq := by
  intro P hP V _hCan hSmoothAll hVae m hm r_min hr_min ν hν hν_min tr hBUC
  let c : ℝ := ν ^ (-2 : ℝ)
  have hν1 : ν ≤ 1 := hν_min.trans (min_le_left _ _)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two]
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  constructor
  · -- First conjunct: regularity, zero circulation, central parity, and `X_{m,c}`-continuity on `[0, T]`
    intro s hs
    set T : ℝ := clockAge ν r_min
    have hT0 : 0 ≤ T := hs.1.trans hs.2
    let I : Set ℝ := Icc (0 : ℝ) T
    let U : Set ℝ := Ioo (-(1 / (4 * ν))) (T + 1 / 2)
    have hI_U : I ⊆ U := fun r hr => by
      dsimp [U]
      have : 0 < 1 / (4 * ν) := by positivity
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    obtain ⟨M_w, β, hMw_pos, hβ_pos, hw_sm, _, hdt_cont, _, hw_bd, hw_cont, _⟩ :=
      canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hT0
    obtain ⟨M_u, α_u, hMu_pos, hαu_pos, hu_bd, hu_cont⟩ :=
      canonicalPhysVel_window_props hP hSmoothAll hVae hr_min hν hν_min hT0
    obtain ⟨V₀, hV₀⟩ := hBUC.sup_bound hT0
    obtain ⟨V₂, hV₂⟩ := hBUC.deriv_bound hT0 2
    set K_tr : ℝ := |V₀| + 2 * |V₂| + 1
    have hKtr_pos : 0 < K_tr := by dsimp [K_tr]; positivity
    set α : ℝ := min β α_u
    have hα_pos : 0 < α := lt_min hβ_pos hαu_pos
    set M_R : ℝ := (1 + ν + 2 * K_tr) * (M_w * Real.exp β) + 2 * K_tr * M_u
    have hMR_nn : 0 ≤ M_R := by dsimp [M_R]; positivity
    -- Train bounds on `I`
    have hv_bd_I : ∀ τ ∈ I, ∀ (x : ℝ × ℝ) (k : Fin 2), |tr.v τ x k| ≤ K_tr := by
      intro τ hτ x k
      calc |tr.v τ x k| = ‖tr.v τ x k‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖tr.v τ x‖ := PiLp.norm_apply_le (tr.v τ x) k
        _ ≤ V₀ := hV₀ τ hτ x
        _ ≤ K_tr := (le_abs_self V₀).trans (by dsimp [K_tr]; linarith [abs_nonneg V₂])
    have hpdEc_bd_I : ∀ τ ∈ I, ∀ (x : ℝ × ℝ) (k : Fin 2),
        |B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x| ≤ K_tr := by
      intro τ hτ x k
      have h0 := ChiBoundAux.norm_iteratedFDeriv_pd_Ec_le tr hτ.1 k 0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
      calc |B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x|
          ≤ 2 * ‖iteratedFDeriv ℝ 2 (tr.v τ) x‖ := h0
        _ ≤ 2 * V₂ := mul_le_mul_of_nonneg_left (hV₂ τ hτ x) (by norm_num)
        _ ≤ K_tr := by
            have : V₂ ≤ |V₂| := le_abs_self V₂
            dsimp [K_tr]; linarith [abs_nonneg V₀]
    -- Strong measurability of `canonicalPhysResidual P tr τ` for `τ ∈ I`
    have hres_sm : ∀ τ ∈ I,
        AEStronglyMeasurable (canonicalPhysResidual P tr τ) (B0579.cellMeasure c m) := by
      intro τ hτ
      have hw_τ := hw_sm τ (hI_U hτ)
      have hv_τ := UnforcedLeray.B0238.contDiff_Vc tr hτ.1
      have hEc_τ := ChiBoundAux.contDiff_Ec_slice tr hτ.1
      have h1 : StronglyMeasurable (fun x => deriv (fun r => canonicalPhysColumn P ν r x) τ) :=
        (hdt_cont τ (hI_U hτ)).stronglyMeasurable
      have h2 : StronglyMeasurable (fun x => (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x) :=
        (continuous_const.mul ((ibpPdCx_smooth (ibpPdCx_smooth hw_τ 0) 0).continuous.add
          (ibpPdCx_smooth (ibpPdCx_smooth hw_τ 1) 1).continuous)).stronglyMeasurable
      have h3 : StronglyMeasurable (ladTransport tr τ (canonicalPhysColumn P ν τ)) := by
        have hv_c : ∀ k : Fin 2, Continuous (fun x : ℝ × ℝ => ((tr.v τ x k : ℝ) : ℂ)) := fun k =>
          Complex.continuous_ofReal.comp
            (((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv_τ).continuous)
        exact (((hv_c 0).mul (ibpPdCx_smooth hw_τ 0).continuous).add
          ((hv_c 1).mul (ibpPdCx_smooth hw_τ 1).continuous)).stronglyMeasurable
      have h4 : ∀ k : Fin 2, StronglyMeasurable (fun x =>
          canonicalPhysVel P ν τ x k * (B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) := by
        intro k
        have hu_sm : StronglyMeasurable (fun x => canonicalPhysVel P ν τ x k) :=
          EulerErrorSub.stronglyMeasurable_kerVelCx c hw_τ.continuous.stronglyMeasurable k
        have hEc_pd_c : Continuous (fun x => (B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) :=
          Complex.continuous_ofReal.comp
            (((contDiff_infty_iff_fderiv.1 hEc_τ).2).clm_apply contDiff_const).continuous
        exact hu_sm.mul hEc_pd_c.stronglyMeasurable
      have hfn : canonicalPhysResidual P tr τ = fun x =>
          deriv (fun r => canonicalPhysColumn P ν r x) τ -
            (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x +
            ladTransport tr τ (canonicalPhysColumn P ν τ) x +
            (canonicalPhysVel P ν τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
              canonicalPhysVel P ν τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) :=
        funext fun x => canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hτ.1 x
      rw [hfn]
      exact (((h1.sub h2).add h3).add ((h4 0).add (h4 1))).aestronglyMeasurable
    -- Uniform exponential `η`-decay bound `M_R * exp(-α * |x.2|)` on `I`
    have hres_bd : ∀ τ ∈ I, ∀ x ∈ B0579.cell c,
        ‖canonicalPhysResidual P tr τ x‖ ≤ M_R * Real.exp (-α * |x.2|) := by
      intro τ hτ x _
      rw [canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hτ.1 x]
      have hexp_w : Real.exp (-β * x.2 ^ 2) ≤ Real.exp β * Real.exp (-α * |x.2|) := by
        refine (exp_sq_le_exp_abs hβ_pos x.2).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
        exact Real.exp_le_exp.2 (by
          have : α ≤ β := min_le_left _ _
          nlinarith [abs_nonneg x.2])
      have hexp_u : Real.exp (-α_u * |x.2|) ≤ Real.exp (-α * |x.2|) :=
        Real.exp_le_exp.2 (by
          have : α ≤ α_u := min_le_right _ _
          nlinarith [abs_nonneg x.2])
      have hb_dt : ‖deriv (fun r => canonicalPhysColumn P ν r x) τ‖ ≤
          (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by
        calc ‖deriv (fun r => canonicalPhysColumn P ν r x) τ‖
            ≤ M_w * (Real.exp β * Real.exp (-α * |x.2|)) :=
              ((hw_bd τ (hI_U hτ) x).2.2.2).trans (mul_le_mul_of_nonneg_left hexp_w hMw_pos.le)
          _ = (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by ring
      have hb_lap : ‖(ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x‖ ≤
          ν * (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by
        rw [norm_mul, Complex.norm_of_nonneg hν.le]
        calc ν * ‖ladLapCx (canonicalPhysColumn P ν τ) x‖
            ≤ ν * (M_w * (Real.exp β * Real.exp (-α * |x.2|))) :=
              mul_le_mul_of_nonneg_left
                (((hw_bd τ (hI_U hτ) x).2.2.1.1).trans
                  (mul_le_mul_of_nonneg_left hexp_w hMw_pos.le)) hν.le
          _ = ν * (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by ring
      have hb_tr_k : ∀ k : Fin 2,
          ‖((tr.v τ x k : ℝ) : ℂ) * pdCx k (canonicalPhysColumn P ν τ) x‖ ≤
            K_tr * (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by
        intro k
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |tr.v τ x k| * ‖pdCx k (canonicalPhysColumn P ν τ) x‖
            ≤ K_tr * (M_w * (Real.exp β * Real.exp (-α * |x.2|))) :=
              mul_le_mul (hv_bd_I τ hτ x k)
                (((hw_bd τ (hI_U hτ) x).2.1 k).trans
                  (mul_le_mul_of_nonneg_left hexp_w hMw_pos.le))
                (norm_nonneg _) hKtr_pos.le
          _ = K_tr * (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by ring
      have hb_tr : ‖ladTransport tr τ (canonicalPhysColumn P ν τ) x‖ ≤
          (2 * K_tr) * (M_w * Real.exp β) * Real.exp (-α * |x.2|) := by
        unfold ladTransport
        exact (norm_add_le _ _).trans (by linarith [hb_tr_k 0, hb_tr_k 1])
      have hb_bs_k : ∀ k : Fin 2,
          ‖canonicalPhysVel P ν τ x k * (B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ ≤
            K_tr * M_u * Real.exp (-α * |x.2|) := by
        intro k
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖canonicalPhysVel P ν τ x k‖ * |B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x|
            ≤ (M_u * Real.exp (-α * |x.2|)) * K_tr :=
              mul_le_mul ((hu_bd τ hτ x k).trans (mul_le_mul_of_nonneg_left hexp_u hMu_pos.le))
                (hpdEc_bd_I τ hτ x k) (abs_nonneg _) (by positivity)
          _ = K_tr * M_u * Real.exp (-α * |x.2|) := by ring
      have hb_bs : ‖canonicalPhysVel P ν τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
          canonicalPhysVel P ν τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ ≤
          (2 * K_tr * M_u) * Real.exp (-α * |x.2|) :=
        (norm_add_le _ _).trans (by linarith [hb_bs_k 0, hb_bs_k 1])
      calc ‖deriv (fun r => canonicalPhysColumn P ν r x) τ -
              (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x +
              ladTransport tr τ (canonicalPhysColumn P ν τ) x +
              (canonicalPhysVel P ν τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
                canonicalPhysVel P ν τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ))‖
          ≤ ‖deriv (fun r => canonicalPhysColumn P ν r x) τ -
                (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x +
                ladTransport tr τ (canonicalPhysColumn P ν τ) x‖ +
              ‖canonicalPhysVel P ν τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
                canonicalPhysVel P ν τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ (‖deriv (fun r => canonicalPhysColumn P ν r x) τ‖ +
              ‖(ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x‖ +
              ‖ladTransport tr τ (canonicalPhysColumn P ν τ) x‖) +
            ‖canonicalPhysVel P ν τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
              canonicalPhysVel P ν τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ := by
            have htri1 := norm_add_le
              (deriv (fun r => canonicalPhysColumn P ν r x) τ -
                (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x)
              (ladTransport tr τ (canonicalPhysColumn P ν τ) x)
            have htri2 := norm_sub_le
              (deriv (fun r => canonicalPhysColumn P ν r x) τ)
              ((ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x)
            linarith
        _ ≤ M_R * Real.exp (-α * |x.2|) := by
            dsimp [M_R]; linarith
    -- Pointwise `τ`-continuity on `I`
    have hres_cont : ∀ x ∈ B0579.cell c,
        ContinuousWithinAt (fun τ => canonicalPhysResidual P tr τ x) I s := by
      intro x _
      have hv_slice_c : ContinuousOn (fun τ : ℝ => tr.v τ x) I :=
        tr.isTrain.smooth_v.continuousOn.comp
          (continuous_id.prodMk continuous_const).continuousOn
          (fun τ hτ => ⟨hτ.1, mem_univ x⟩)
      have hv_k_c : ∀ k : Fin 2, ContinuousOn (fun τ : ℝ => ((tr.v τ x k : ℝ) : ℂ)) I := fun k =>
        (Complex.continuous_ofReal.comp
          (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp_continuousOn
          hv_slice_c
      have hEc_k_c : ∀ k : Fin 2,
          ContinuousOn (fun τ : ℝ => (B0579.pd k (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) I := fun k =>
        Complex.continuous_ofReal.comp_continuousOn
          ((PdEc.pdEc_continuousOn tr k x).mono fun _ hτ => hτ.1)
      have hc_on : ContinuousOn (fun τ => canonicalPhysResidual P tr τ x) I := by
        have hc_rhs : ContinuousOn (fun τ =>
            deriv (fun r => canonicalPhysColumn P ν r x) τ -
              (ν : ℂ) * ladLapCx (canonicalPhysColumn P ν τ) x +
              (((tr.v τ x 0 : ℝ) : ℂ) * pdCx 0 (canonicalPhysColumn P ν τ) x +
                ((tr.v τ x 1 : ℝ) : ℂ) * pdCx 1 (canonicalPhysColumn P ν τ) x) +
              (canonicalPhysVel P ν τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
                canonicalPhysVel P ν τ x 1 *
                  (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ))) I :=
          ((((hw_cont x).2.2.2.mono hI_U).sub
            (continuousOn_const.mul ((hw_cont x).2.2.1.mono hI_U))).add
            (((hv_k_c 0).mul (((hw_cont x).2.1 0).mono hI_U)).add
              ((hv_k_c 1).mul (((hw_cont x).2.1 1).mono hI_U)))).add
            (((hu_cont x 0).mul (hEc_k_c 0)).add ((hu_cont x 1).mul (hEc_k_c 1)))
        exact hc_rhs.congr fun τ hτ =>
          canonicalPhysResidual_eq_pde hP hSmoothAll hVae hν hν1 tr hτ.1 x
      exact hc_on.continuousWithinAt hs
    have hmem_s : MemLp (canonicalPhysResidual P tr s) 2 (B0579.cellMeasure c m) :=
      memLp_of_exp_eta hc0 (by linarith) hα_pos hMR_nn (hres_sm s hs) (hres_bd s hs)
    exact ⟨isBiotSavart_canonicalPhysColumn hP hSmoothAll hVae hm hν hν1 hs.1,
      hmem_s,
      hasZeroCirculation_canonicalPhysResidual hP hSmoothAll hVae hm hν hν1 tr hBUC hs.1 hmem_s,
      isCentrallyEven_canonicalPhysResidual hP hSmoothAll hVae hν hν1 tr hs.1,
      tendsto_xNorm_of_exp_eta hc0 (by linarith) hα_pos hMR_nn hs hres_sm hres_bd hres_cont⟩
  · -- Second conjunct: cylinder weak identity on `[0, s]` via spatial IBP + Leibniz + FTC
    intro φ hφ s hs
    refine ⟨(spatial_ibp_canonicalPhysColumn hP hSmoothAll hVae hm hν hν1 tr hs.1 hφ).1, ?_⟩
    obtain ⟨M_w, β, hMw_pos, _, hw_sm, _, hdt_cont, hw_hd, hw_bd, hw_cont, _⟩ :=
      canonicalPhysColumn_window_props hP hSmoothAll hVae hν hν1 hs.1
    let U : Set ℝ := Ioo (-(1 / (4 * ν))) (s + 1 / 2)
    have hIs_U : Icc (0 : ℝ) s ⊆ U := fun r hr => by
      dsimp [U]
      have : 0 < 1 / (4 * ν) := by positivity
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    let μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
    set H : ℝ → ℂ := fun r => ∫ x in B0579.cell c, canonicalPhysColumn P ν r x * (φ x : ℂ)
    set H' : ℝ → ℂ := fun r =>
      ∫ x in B0579.cell c, deriv (fun t => canonicalPhysColumn P ν t x) r * (φ x : ℂ)
    set bound_φ : ℝ × ℝ → ℝ := fun x => M_w * ‖(φ x : ℂ)‖
    have hbound_int : Integrable bound_φ μ := by
      show IntegrableOn bound_φ (B0579.cell c)
      have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
        unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
      rw [hcell]
      obtain ⟨R, hR⟩ := hφ.band
      have hv : UnforcedLeray.Cyl.VanishesOutside R bound_φ :=
        fun x hx => by simp [bound_φ, hR x hx]
      exact hv.integrableOn_cell
        (continuous_const.mul (Complex.continuous_ofReal.comp hφ.continuous).norm) c
    have hexp_le1 : ∀ x : ℝ × ℝ, Real.exp (-β * x.2 ^ 2) ≤ 1 :=
      fun x => Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x.2])
    have hH_hd : ∀ r ∈ U, HasDerivAt H (H' r) r := by
      intro r hr
      have hwφ_int : Integrable (fun x => canonicalPhysColumn P ν r x * (φ x : ℂ)) μ := by
        refine hbound_int.mono'
          (((hw_sm r hr).continuous.mul
            (Complex.continuous_ofReal.comp hφ.continuous)).aestronglyMeasurable)
          (Eventually.of_forall fun x => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (((hw_bd r hr x).1).trans (mul_le_of_le_one_right hMw_pos.le (hexp_le1 x)))
          (norm_nonneg _)
      exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (F := fun t x => canonicalPhysColumn P ν t x * (φ x : ℂ))
        (F' := fun t x => deriv (fun q => canonicalPhysColumn P ν q x) t * (φ x : ℂ))
        (bound := bound_φ)
        (Ioo_mem_nhds hr.1 hr.2)
        (by filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
            exact ((hw_sm t ht).continuous.mul
              (Complex.continuous_ofReal.comp hφ.continuous)).aestronglyMeasurable)
        hwφ_int
        ((hdt_cont r hr).mul (Complex.continuous_ofReal.comp hφ.continuous)).aestronglyMeasurable
        (Eventually.of_forall fun x t ht => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (((hw_bd t ht x).2.2.2).trans (mul_le_of_le_one_right hMw_pos.le (hexp_le1 x)))
            (norm_nonneg _))
        hbound_int
        (Eventually.of_forall fun x t ht => (hw_hd t ht x).mul_const (φ x : ℂ))).2
    have hH'_cont : ContinuousOn H' U := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine continuous_iff_continuousAt.2 fun r₀ => ?_
      refine tendsto_integral_filter_of_dominated_convergence bound_φ
        (Eventually.of_forall fun r =>
          ((hdt_cont r.1 r.2).mul
            (Complex.continuous_ofReal.comp hφ.continuous)).aestronglyMeasurable)
        (Eventually.of_forall fun r => Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (((hw_bd r.1 r.2 x).2.2.2).trans (mul_le_of_le_one_right hMw_pos.le (hexp_le1 x)))
            (norm_nonneg _))
        hbound_int
        (Eventually.of_forall fun x =>
          (((continuousOn_iff_continuous_domRestrict.1 (hw_cont x).2.2.2).tendsto r₀).mul_const
            (φ x : ℂ)))
    have hH'_ii : IntervalIntegrable H' volume 0 s :=
      (hH'_cont.mono hIs_U).intervalIntegrable_of_Icc hs.1
    have hibp_eq : ∀ τ ∈ Icc (0 : ℝ) s,
        (∫ x in B0579.cell c,
            flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ x) +
          (∫ x in B0579.cell c, canonicalPhysResidual P tr τ x * (φ x : ℂ)) = H' τ :=
      fun τ hτ => (spatial_ibp_canonicalPhysColumn hP hSmoothAll hVae hm hν hν1 tr hτ.1 hφ).2.2
    have hG_ii : IntervalIntegrable (fun τ =>
        (∫ x in B0579.cell c,
            flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ x) +
          (∫ x in B0579.cell c, canonicalPhysResidual P tr τ x * (φ x : ℂ))) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).2
        (((intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).1 hH'_ii).congr_fun
          (fun τ hτ => (hibp_eq τ hτ).symm) measurableSet_Icc)
    refine ⟨hG_ii, ?_⟩
    have hint_eq : (∫ τ in (0 : ℝ)..s,
        ((∫ x in B0579.cell c,
            flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ x) +
          (∫ x in B0579.cell c, canonicalPhysResidual P tr τ x * (φ x : ℂ)))) =
        H s - H 0 := by
      rw [intervalIntegral.integral_congr
        (fun τ hτ => hibp_eq τ (by rwa [uIcc_of_le hs.1] at hτ))]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun τ hτ => hH_hd τ (hIs_U (by rwa [uIcc_of_le hs.1] at hτ))) hH'_ii
    have hH0 : H 0 = ∫ x in B0579.cell c, preparedDatum P ν x * (φ x : ℂ) := by
      dsimp [H]
      rw [canonicalPhysColumn_zero_eq_preparedDatum P hν]
    change H s = _
    rw [hint_eq, ← hH0, add_sub_cancel]

end UnforcedLeray.Short.IIIa.T22Sub

end
