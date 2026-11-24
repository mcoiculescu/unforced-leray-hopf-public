import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2

/-!
# Part III-a, task `PartIII-a:T21/c5/2/2` sub-infrastructure: linearised Euler direct error (`DirectEulerSubBound`, SP 2866-2889, 2905-2918, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2889,
2905-2918, and 2991-2995 (`eq:short-causal-ampl-moving`).

## Mathematical structure and proved reductions

1. **Planar eigenvalue uniqueness between `IsPlanarReference P` and `IsSeedKernels κ` (proved here)**:
   * `gaussianWeightInv_eq`, `memLp_of_memXG`, `vortexOmega_eq`, `strainK_eq`, and
     `generatorL0_eq_L0Fun`: bridge the blueprint profile space `MemXG` and classical radial
     generator `generatorL0` to `B0010.XG` and `B0012.L0`.
   * `planar_eigenvalue_eq_seed`: uses `Planar.L0_eigen_unique` (`Short/PartI/Tasks/SeedUniqueness.lean`)
     to prove that for any planar reference `P` (`IsPlanarReference P`) and any Part I seed triple
     `(lam, h, ℓ)` (`PartI.IsSeedXG lam (hh.toLp h) ℓ`), the growing eigenvalues coincide:
     `P.eigenvalue = lam`, and the radial growing modes are collinear in `B0010.XG`.

2. **Quantitative Gram-inverse `O(d⁻²) = O(ν³ / θ(r))` off-diagonal cancellation (proved here)**:
   * `perGram_inv_sub_id_bound` and `memLp_and_xNorm_perLam0`: prove that for `d ≥ D_G`,
     `‖(perGram κ d)⁻¹ i k - δ_{i,k}‖ ≤ (6 * C_G) / d ^ 2`, and for `m > 8` and `d ≥ 1`,
     `MemLp (perLam0 κ d k) 2 (B0579.cellMeasure d (-m))` with
     `xNorm d (-m) (perLam0 κ d k) ≤ ENNReal.ofReal C_0`.
   * `movLamDualEulerSub_eq_sum_add_offDiag`: proves the exact algebraic decomposition of
     `movLamDualEulerSub κ lam tr r i` into the Gram-weighted unnormalised Euler residual
     `∑ k, (perGram κ d)⁻¹ i k * movLam0DualEulerSub κ lam tr r k` plus the off-diagonal
     eigenvalue mismatch `∑ k, (perGram κ d)⁻¹ i k * (seedModeEigen lam k - seedModeEigen lam i) * perLam0 κ d k`.
   * `offDiag_gram_coeff_eq`: since `seedModeEigen lam k - seedModeEigen lam i = 0` when `k = i`,
     the diagonal `(k = i)` term vanishes identically and the coefficient equals
     `((perGram κ d)⁻¹ i k - δ_{i,k}) * (seedModeEigen lam k - seedModeEigen lam i)`, which is
     `O(d⁻²) = O(ν³ / clockTheta ν r)`!
   * `memLp_and_xNorm_movLamDualEulerSub`: combines the triangle inequality in
     `L²(B0579.cellMeasure d (-m))` with `inv_cellLen_sq_eq_nu_cube_div_theta` to prove that
     `movLamDualEulerSub κ lam tr r i` belongs to `X_{-m, d(r)}` with norm bounded by
     `((6 * C_0e + 24 * C_G * ‖lam‖ * C_0) * ν ^ 3 / clockTheta ν r)`.

3. **Conditional assemblies (`directEulerSubBound_of` and `movLamDualEulerSubBound_of`)**:
   * Assemble both `DirectEulerSubBound κ` (`PartIII-a:T21/c5/2/2`) and
     `MovLamDualEulerSubBound κ` (`PartIII-a:T21/c5/3/2`) from the unnormalised pullback linearity
     `MovLam0EulerPullback κ` (`PartIII-a:T21/c5/2/2/1`) and the unnormalised planar-to-cylinder
     Euler comparison leaf `MovLam0EulerSubBound κ` (`PartIII-a:T21/c5/2/2/2`) with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Unnormalised linearised Euler dual rows and eigenvalue-subtracted residual -/

/-- Physical-variable unnormalised dual test function `φ⁰_k(r, x) = a(r)⁻¹ Λ⁰_k(d(r), x / √a(r))`
associated with `perLam0 κ d(r) k` (SP 2898-2905). -/
def physFrameLam0Euler (κ : PlanarFrameKernels) (ν r : ℝ) (k : Fin 2) : ℝ × ℝ → ℂ :=
  physAdj (clockA ν r) (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k)

/-- Physical-variable linearised Euler (drift + nonlocal Biot-Savart) part on the unnormalised
dual row `physFrameLam0Euler κ ν r k` (SP 2905-2918). -/
def physLam0DualEuler (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (k : Fin 2)
    (x : ℝ × ℝ) : ℂ :=
  ladTransport tr r (physFrameLam0Euler κ ν r k) x -
    kerAdj (ν ^ (-2 : ℝ)) (fun l y => physFrameLam0Euler κ ν r k y *
      (B0579.pd l (UnforcedLeray.B0238.Ec tr r) y : ℂ)) x

/-- Moving-variable linearised Euler adjoint on the unnormalised dual row `perLam0 κ d(r) k`
minus the planar seed eigenvalue `seedModeEigen lam k * perLam0 κ d(r) k`:
`a(r)² * movingPhi ν (physLam0DualEuler κ tr · k) r - λ_k * perLam0 κ d(r) k`
(SP 2866-2889, 2905-2918, 2990-2997). -/
def movLam0DualEulerSub (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (k : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y -
    seedModeEigen lam k * perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k y

/-! ## Unnormalised analytical leaves for `DirectEulerSubBound` -/

/-- **Analytical Leaf A (`MovLam0EulerPullback`, `PartIII-a:T21/c5/2/2/1`, SP 2905-2918)**:
At fixed age `r`, `physFrameLam κ ν r i = ∑ k, (perGram κ d(r))⁻¹ i k * physFrameLam0Euler κ ν r k`
is a linear combination with spatial-constant coefficients `(perGram κ d(r))⁻¹ i k`, so the spatial
operator `physLamDualEuler` (`ladTransport - kerAdj`) and its moving pullback commute with the
Gram-inverse sum. -/
def MovLam0EulerPullback (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ D_ep : ℝ, 1 ≤ D_ep ∧
    ∀ ν : ℝ, ν ∈ Ioc 0 1 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
    ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
      let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
      D_ep ≤ d →
      ∀ i : Fin 2, ∀ y : ℝ × ℝ,
        (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
          movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y =
          ∑ k : Fin 2, (perGram κ d)⁻¹ i k *
            ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
              movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y)

/-- **Analytical Leaf B (`MovLam0EulerSubBound`, `PartIII-a:T21/c5/2/2/2`, SP 2866-2889, 2905-2918, 2991-2995)**:
For any Part I seed triple `(lam, h, ℓ)` (`PartI.IsSeedXG lam (hh.toLp h) ℓ`) realizing `κ`,
planar seed duality `L_0^* λ_k = λ_k λ_k` cancels the leading Gaussian vortex/strain generator on
`perLam0 κ d(r) k`, and the remaining cylinder Biot-Savart tail `O(d(r)⁻²) = O(ν³ / θ(r))` plus the
rescaled BUC train comparison (`Sub/T21_2_6/TrainWeightedJetPoly.lean`) bound the unnormalised
residual `movLam0DualEulerSub κ lam tr r k` in `X_{-m, d(r)}` by `C_0e * ν ^ 3 / clockTheta ν r`. -/
def MovLam0EulerSubBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ →
    (∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) →
    (∀ y, κ.e 1 y = starRingEnd ℂ (PartI.seedPlanar h (planeToC y))) →
    (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y, κ.lamP 0 y * f (planeToC y) = PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
      ∫ y, κ.lamP 1 y * f (planeToC y) =
        starRingEnd ℂ (PartI.seedEll h (fun r => starRingEnd ℂ (Planar.NUE.Polar.angularSector f (-2) r)))) →
    ∀ m : ℝ, 8 < m →
    ∃ C_0e b_0e : ℝ, 0 ≤ C_0e ∧ 1 ≤ b_0e ∧
      ∀ b : ℝ, b_0e ≤ b →
        ∃ ν_0e : ℝ, 0 < ν_0e ∧
          ∀ ν : ℝ, ν ∈ Ioc 0 ν_0e →
          ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
          ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            MemLp (movLam0DualEulerSub κ lam tr r k) 2 (B0579.cellMeasure d (-m)) ∧
            xNorm d (-m) (movLam0DualEulerSub κ lam tr r k) ≤
              ENNReal.ofReal (C_0e * ν ^ 3 / clockTheta ν r)

namespace DirectEulerSub

open ComplCouplingSub

/-! ## Planar eigenvalue uniqueness (`P.eigenvalue = lam`) from `Planar.L0_eigen_unique` -/

theorem gaussianWeightInv_eq (r : ℝ) :
    gaussianWeightInv r = (B0010.radialGaussianWeight r)⁻¹ := by
  rw [B0010.radialGaussianWeight_inv]
  rfl

theorem memLp_of_memXG {f : Profile} (hf : MemXG f) : MemLp f 2 B0010.xGMeasure := by
  rw [B0010.memLp_iff_integrableOn hf.measurable]
  refine hf.integrable.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [gaussianWeightInv_eq]
  ring

theorem vortexOmega_eq (r : ℝ) :
    vortexOmega r = UnforcedLeray.GaussianVortex.radialOmega r := by
  simp only [vortexOmega, UnforcedLeray.GaussianVortex.radialOmega, neg_div]

theorem strainK_eq (r : ℝ) :
    strainK r = UnforcedLeray.GaussianVortex.radialK r := by
  rw [UnforcedLeray.GaussianVortex.radialK, ← vortexOmega_eq]
  rfl

theorem generatorL0_eq_L0Fun (f : Profile) (r : ℝ) :
    generatorL0 f r = B0012.L0Fun f r := by
  rw [generatorL0, B0012.L0Fun, vortexOmega_eq, strainK_eq]
  rfl

/-- Any planar reference `P` (`IsPlanarReference P`) and any Part I seed triple `(lam, q, ℓ)`
(`PartI.IsSeedXG lam q ℓ`) have the exact same growing eigenvalue `P.eigenvalue = lam`. -/
theorem planar_eigenvalue_eq_seed (P : PlanarData) (hP : IsPlanarReference P)
    {lam : ℂ} {q : B0010.XG} {ℓ : B0010.XG →L[ℂ] ℂ} (hIS : PartI.IsSeedXG lam q ℓ) :
    P.eigenvalue = lam := by
  let hm_P := memLp_of_memXG hP.eigenpair.memXG
  let q_P : B0010.XG := hm_P.toLp P.mode
  have hq_P_eigen : B0012.L0 q_P = P.eigenvalue • q_P := by
    change B0012.L0 (hm_P.toLp P.mode) = P.eigenvalue • q_P
    rw [B0012.L0_toLp hm_P]
    apply Lp.ext
    filter_upwards [B0012.ae_xG_pos, (B0012.memLp_L0Fun hm_P).coeFn_toLp,
      hm_P.coeFn_toLp, Lp.coeFn_smul P.eigenvalue q_P] with r hr hL hq hsmul
    have hq' : ((q_P : B0010.XG) : ℝ → ℂ) r = P.mode r := hq
    rw [hL]
    change B0012.L0Fun P.mode r = ((P.eigenvalue • q_P : B0010.XG) : ℝ → ℂ) r
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hq', ← generatorL0_eq_L0Fun P.mode r,
      hP.eigenpair.eigen r hr]
  have hq_P_ne : q_P ≠ 0 := by
    intro h0
    apply hP.eigenpair.nonzero
    have hzeroX : P.mode =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [hm_P.coeFn_toLp,
        (show (⇑q_P : ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [h0]; exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)] with r h1 h2
      rw [← h1, h2]
    exact B0012.restrict_ac.ae_le hzeroX
  obtain ⟨hlam_eq, -, -⟩ := Planar.L0_eigen_unique hIS.re_pos hP.eigenpair.re_pos
    hIS.eigen hq_P_eigen hIS.ne_zero hq_P_ne
  exact hlam_eq

/-! ## Quantitative Gram-inverse `O(d⁻²)` bound and uniform `X_{-m, d}` bound for `perLam0` -/

theorem perGram_sub_id_bound (κ : PlanarFrameKernels) :
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d → ∀ i j : Fin 2,
        ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ C_G / d ^ 2 ∧
        ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4 := by
  have h1 := perGramUnfold κ
  have h2 := perGramTail κ
  obtain ⟨D₁, hD₁⟩ := perGramNear_of κ h1 h2 (1 / 4) (by norm_num)
  obtain ⟨C, D₀, hC⟩ := h2
  refine ⟨max C 0, max (max D₀ D₁) 1, le_max_right _ _, le_max_right _ _, fun d hd i j => ?_⟩
  have hd0 : D₀ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hd1 : D₁ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  have hd_ge_one : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hdpos : 0 < d := by linarith
  refine ⟨?_, hD₁ d hd1 i j⟩
  obtain ⟨hs, he⟩ := h1 d hdpos i j
  have hsplit := hs.tsum_eq_add_tsum_ite 0
  have h0 : gramTerm κ d i j 0 = if i = j then 1 else 0 := by
    simp only [gramTerm, Int.cast_zero, zero_mul, add_zero]
    exact κ.biorth i j
  have hrest : perGram κ d i j - (if i = j then 1 else 0) =
      ∑' k : ℤ, (if k = 0 then (0 : ℂ) else gramTerm κ d i j k) := by
    rw [he, hsplit, h0]
    simp only [add_sub_cancel_left]
  rw [hrest]
  refine (hC d hd0 i j).trans ?_
  gcongr
  exact le_max_left _ _

theorem gram_inv_sub_id_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (hU : IsUnit G.det) (i j : Fin 2) :
    G⁻¹ i j - (if i = j then 1 else 0) =
      ∑ k : Fin 2, G⁻¹ i k * ((if k = j then 1 else 0) - G k j) := by
  have hmul := Matrix.nonsing_inv_mul G hU
  have hentry := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  simp_rw [mul_sub, Finset.sum_sub_distrib, hentry]
  congr 1
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

theorem gram_inv_sub_id_bound (G : Matrix (Fin 2) (Fin 2) ℂ) {E : ℝ}
    (h14 : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hE : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ E) (i j : Fin 2) :
    ‖G⁻¹ i j - (if i = j then 1 else 0)‖ ≤ 6 * E := by
  obtain ⟨hU, hinv⟩ := gram_inv_bound G h14
  rw [gram_inv_sub_id_eq G hU i j, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_sub_rev (if (0 : Fin 2) = j then 1 else 0),
    norm_sub_rev (if (1 : Fin 2) = j then 1 else 0)]
  have h0 := hinv i 0
  have h1 := hinv i 1
  have e0 := hE 0 j
  have e1 := hE 1 j
  nlinarith [norm_nonneg (G⁻¹ i 0), norm_nonneg (G⁻¹ i 1),
    norm_nonneg (G 0 j - if (0 : Fin 2) = j then 1 else 0),
    norm_nonneg (G 1 j - if (1 : Fin 2) = j then 1 else 0),
    mul_le_mul h0 e0 (norm_nonneg _) (by norm_num),
    mul_le_mul h1 e1 (norm_nonneg _) (by norm_num)]

theorem perGram_inv_sub_id_bound (κ : PlanarFrameKernels) :
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d →
        (∀ i j : Fin 2, ‖(perGram κ d)⁻¹ i j‖ ≤ 3) ∧
        (∀ i j : Fin 2, ‖(perGram κ d)⁻¹ i j - (if i = j then 1 else 0)‖ ≤ (6 * C_G) / d ^ 2) := by
  obtain ⟨C_G, D_G, hCG, hDG, hG⟩ := perGram_sub_id_bound κ
  refine ⟨C_G, D_G, hCG, hDG, fun d hd => ?_⟩
  have h14 : ∀ i j : Fin 2, ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4 :=
    fun i j => (hG d hd i j).2
  have hE : ∀ i j : Fin 2, ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ C_G / d ^ 2 :=
    fun i j => (hG d hd i j).1
  obtain ⟨-, hinv⟩ := gram_inv_bound (perGram κ d) h14
  refine ⟨hinv, fun i j => ?_⟩
  have hbd := gram_inv_sub_id_bound (perGram κ d) h14 hE i j
  exact hbd.trans (by ring_nf; rfl)

theorem memLp_and_xNorm_perLam0 (κ : PlanarFrameKernels) {m : ℝ} (hm : 8 < m) :
    ∃ C_0 : ℝ, 0 ≤ C_0 ∧
      ∀ d : ℝ, 1 ≤ d → ∀ k : Fin 2,
        MemLp (perLam0 κ d k) 2 (B0579.cellMeasure d (-m)) ∧
        xNorm d (-m) (perLam0 κ d k) ≤ ENNReal.ofReal C_0 := by
  obtain ⟨B, hB0, hB⟩ := Lam0B.perLam0_sup κ
  set G : ℝ × ℝ → ℝ := fun y => B * B0579.jb y ^ ((-m) / 2) with hG
  have hGmem : MemLp G 2 volume := by
    have hcont : Continuous G :=
      continuous_const.mul (B0579.continuous_jb_rpow _)
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine (Lam0B.integrable_jb_neg_two.const_mul (B ^ 2)).mono'
      (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hj0 : 0 ≤ B0579.jb y := (B0579.jb_pos y).le
    have e1 : (B0579.jb y ^ ((-m) / 2)) ^ 2 = B0579.jb y ^ (-m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0]
      congr 1; push_cast; ring
    have e2 : B0579.jb y ^ (-m) ≤ B0579.jb y ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (Lam0B.jb_ge_one y) (by linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _), hG]
    simp only
    rw [mul_pow, e1]
    exact mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
  set C_0 : ℝ := (eLpNorm G 2 volume).toReal with hC0
  have hGfin : eLpNorm G 2 volume ≠ ⊤ := hGmem.2.ne
  refine ⟨C_0, ENNReal.toReal_nonneg, fun d hd k => ?_⟩
  have hd0 : 0 < d := by linarith
  have hFc : Continuous (perLam0 κ d k) := Lam0B.perLam0_continuous κ hd0 k
  have hle : xNorm d (-m) (perLam0 κ d k) ≤ ENNReal.ofReal C_0 := by
    change eLpNorm (perLam0 κ d k) 2 (B0579.cellMeasure d (-m)) ≤ ENNReal.ofReal C_0
    rw [Lam0B.eLpNorm_cellMeasure_cx]
    have hmono : eLpNorm (fun x => ((B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) * perLam0 κ d k x) 2
        (volume.restrict (B0579.cell d)) ≤ eLpNorm G 2 (volume.restrict (B0579.cell d)) := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with y hy
      have h1 := hB d hd k y hy
      have hj0 : 0 ≤ B0579.jb y ^ ((-m) / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
      have hGnn : 0 ≤ G y := mul_nonneg hB0 hj0
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hj0, Real.norm_of_nonneg hGnn]
      dsimp [G]
      linarith [mul_le_mul_of_nonneg_left h1 hj0]
    refine hmono.trans ?_
    refine (eLpNorm_mono_measure G Measure.restrict_le_self).trans ?_
    rw [hC0, ENNReal.ofReal_toReal hGfin]
  refine ⟨⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, hle⟩

/-! ## Off-diagonal Gram-normalisation identity and `X_{-m, d}` bound for `movLamDualEulerSub` -/

/-- Because `seedModeEigen lam k - seedModeEigen lam i = 0` when `k = i`, the coefficient
`(perGram κ d)⁻¹ i k * (seedModeEigen lam k - seedModeEigen lam i)` equals
`((perGram κ d)⁻¹ i k - δ_{i,k}) * (seedModeEigen lam k - seedModeEigen lam i)`. -/
theorem offDiag_gram_coeff_eq (Ginv : Matrix (Fin 2) (Fin 2) ℂ) (lam : ℂ) (i k : Fin 2) :
    Ginv i k * (seedModeEigen lam k - seedModeEigen lam i) =
      (Ginv i k - (if i = k then 1 else 0)) * (seedModeEigen lam k - seedModeEigen lam i) := by
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

/-- Norm of `seedModeEigen lam k - seedModeEigen lam i` is at most `2 * ‖lam‖`. -/
theorem norm_seedModeEigen_sub_le (lam : ℂ) (i k : Fin 2) :
    ‖seedModeEigen lam k - seedModeEigen lam i‖ ≤ 2 * ‖lam‖ := by
  have hnorm : ∀ j : Fin 2, ‖seedModeEigen lam j‖ = ‖lam‖ := by
    intro j
    unfold seedModeEigen
    fin_cases j <;> simp
  refine (norm_sub_le _ _).trans ?_
  rw [hnorm k, hnorm i]
  ring_nf
  rfl

/-- Pointwise decomposition of `movLamDualEulerSub κ lam tr r i` into the Gram-weighted sum of
`movLam0DualEulerSub κ lam tr r k` plus the off-diagonal Gram-normalisation error on `perLam0`. -/
theorem movLamDualEulerSub_eq_sum_add_offDiag (κ : PlanarFrameKernels) (lam : ℂ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (hpull : ∀ y : ℝ × ℝ,
      (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y =
        ∑ k : Fin 2,
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k *
            ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
              movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y))
    (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movLamDualEulerSub κ lam tr r i y =
      (∑ k : Fin 2, (perGram κ d)⁻¹ i k * movLam0DualEulerSub κ lam tr r k y) +
      (∑ k : Fin 2,
        ((perGram κ d)⁻¹ i k - (if i = k then 1 else 0)) *
          (seedModeEigen lam k - seedModeEigen lam i) * perLam0 κ d k y) := by
  intro d
  unfold movLamDualEulerSub movLam0DualEulerSub
  rw [hpull y]
  change (∑ k : Fin 2, (perGram κ d)⁻¹ i k *
      ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y)) -
    seedModeEigen lam i * (∑ k : Fin 2, (perGram κ d)⁻¹ i k * perLam0 κ d k y) = _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcoeff := offDiag_gram_coeff_eq (perGram κ d)⁻¹ lam i k
  linear_combination perLam0 κ d k y * hcoeff

/-- From the pullback decomposition, the `X_{-m, d}` bound on `movLam0DualEulerSub`, and the
`O(d⁻²)` Gram-inverse bound, `movLamDualEulerSub κ lam tr r i` belongs to
`MemLp · 2 (B0579.cellMeasure d (-m))` with `xNorm` bounded by
`(6 * C_0e + 24 * C_G * ‖lam‖ * C_0) * ν ^ 3 / clockTheta ν r`. -/
theorem memLp_and_xNorm_movLamDualEulerSub (κ : PlanarFrameKernels) (lam : ℂ) {ν r m C_G C_0 C_0e : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i : Fin 2)
    (hν : 0 < ν) (hr : 0 ≤ r) (hθ : 1 ≤ clockTheta ν r)
    (hCG : 0 ≤ C_G) (hC0 : 0 ≤ C_0) (hC0e : 0 ≤ C_0e)
    (hGinv : ∀ k : Fin 2, ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k‖ ≤ 3)
    (hGsub : ∀ k : Fin 2,
      ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k - (if i = k then 1 else 0)‖ ≤
        (6 * C_G) / (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2)
    (hpull : ∀ y : ℝ × ℝ,
      (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLamDualEuler κ tr r' i) r y =
        ∑ k : Fin 2,
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k *
            ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
              movingPhi ν (fun r' => physLam0DualEuler κ tr r' k) r y))
    (h0e : ∀ k : Fin 2,
      MemLp (movLam0DualEulerSub κ lam tr r k) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLam0DualEulerSub κ lam tr r k) ≤
        ENNReal.ofReal (C_0e * ν ^ 3 / clockTheta ν r))
    (hlam0 : ∀ k : Fin 2,
      MemLp (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)
        (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k) ≤ ENNReal.ofReal C_0) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    MemLp (movLamDualEulerSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) ∧
    xNorm d (-m) (movLamDualEulerSub κ lam tr r i) ≤
      ENNReal.ofReal ((6 * C_0e + 24 * C_G * ‖lam‖ * C_0) * ν ^ 3 / clockTheta ν r) := by
  intro d
  set c_off : Fin 2 → ℂ := fun k =>
    ((perGram κ d)⁻¹ i k - (if i = k then 1 else 0)) * (seedModeEigen lam k - seedModeEigen lam i)
  have hfeq : movLamDualEulerSub κ lam tr r i =
      (((perGram κ d)⁻¹ i 0 • movLam0DualEulerSub κ lam tr r 0) +
        ((perGram κ d)⁻¹ i 1 • movLam0DualEulerSub κ lam tr r 1)) +
      ((c_off 0 • perLam0 κ d 0) + (c_off 1 • perLam0 κ d 1)) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c_off]
    rw [movLamDualEulerSub_eq_sum_add_offDiag κ lam tr r i hpull y,
      Fin.sum_univ_two, Fin.sum_univ_two]
  have hm00 : MemLp ((perGram κ d)⁻¹ i 0 • movLam0DualEulerSub κ lam tr r 0) 2
      (B0579.cellMeasure d (-m)) := (h0e 0).1.const_smul _
  have hm01 : MemLp ((perGram κ d)⁻¹ i 1 • movLam0DualEulerSub κ lam tr r 1) 2
      (B0579.cellMeasure d (-m)) := (h0e 1).1.const_smul _
  have hm10 : MemLp (c_off 0 • perLam0 κ d 0) 2
      (B0579.cellMeasure d (-m)) := (hlam0 0).1.const_smul _
  have hm11 : MemLp (c_off 1 • perLam0 κ d 1) 2
      (B0579.cellMeasure d (-m)) := (hlam0 1).1.const_smul _
  have hmem : MemLp (movLamDualEulerSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) := by
    rw [hfeq]
    exact (hm00.add hm01).add (hm10.add hm11)
  refine ⟨hmem, ?_⟩
  change eLpNorm (movLamDualEulerSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) ≤ _
  rw [hfeq]
  have htri1 := eLpNorm_add_le (hm00.add hm01).aestronglyMeasurable
    (hm10.add hm11).aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htri2 := eLpNorm_add_le hm00.aestronglyMeasurable hm01.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htri3 := eLpNorm_add_le hm10.aestronglyMeasurable hm11.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hbd_0 : ∀ k : Fin 2,
      eLpNorm ((perGram κ d)⁻¹ i k • movLam0DualEulerSub κ lam tr r k) 2
        (B0579.cellMeasure d (-m)) ≤
        ENNReal.ofReal (3 * (C_0e * ν ^ 3 / clockTheta ν r)) := by
    intro k
    rw [eLpNorm_const_smul, ← ofReal_norm]
    refine (mul_le_mul (ENNReal.ofReal_le_ofReal (hGinv k)) (h0e k).2 zero_le
      zero_le).trans ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
  have hcoff_bd : ∀ k : Fin 2,
      ‖c_off k‖ ≤ (12 * C_G * ‖lam‖) * (ν ^ 3 / clockTheta ν r) := by
    intro k
    dsimp [c_off]
    rw [norm_mul]
    have a1 := hGsub k
    have b1 := norm_seedModeEigen_sub_le lam i k
    have hprod : ‖(perGram κ d)⁻¹ i k - (if i = k then 1 else 0)‖ *
        ‖seedModeEigen lam k - seedModeEigen lam i‖ ≤
        ((6 * C_G) / d ^ 2) * (2 * ‖lam‖) :=
      mul_le_mul a1 b1 (norm_nonneg _) (by positivity)
    refine hprod.trans_eq ?_
    have hd_eq : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
      inv_cellLen_sq_eq_nu_cube_div_theta hν hr
    calc ((6 * C_G) / d ^ 2) * (2 * ‖lam‖)
        = (12 * C_G * ‖lam‖) * (1 / d ^ 2) := by ring
      _ = (12 * C_G * ‖lam‖) * (ν ^ 3 / clockTheta ν r) := by rw [hd_eq]
  have hbd_1 : ∀ k : Fin 2,
      eLpNorm (c_off k • perLam0 κ d k) 2 (B0579.cellMeasure d (-m)) ≤
        ENNReal.ofReal (((12 * C_G * ‖lam‖) * (ν ^ 3 / clockTheta ν r)) * C_0) := by
    intro k
    rw [eLpNorm_const_smul, ← ofReal_norm]
    refine (mul_le_mul (ENNReal.ofReal_le_ofReal (hcoff_bd k)) (hlam0 k).2 zero_le
      zero_le).trans ?_
    have hθpos : 0 < clockTheta ν r := by linarith
    rw [← ENNReal.ofReal_mul (by positivity)]
  refine (htri1.trans (add_le_add htri2 htri3)).trans ?_
  refine (add_le_add (add_le_add (hbd_0 0) (hbd_0 1)) (add_le_add (hbd_1 0) (hbd_1 1))).trans ?_
  have hθpos : 0 < clockTheta ν r := by linarith
  have hpos1 : 0 ≤ 3 * (C_0e * ν ^ 3 / clockTheta ν r) := by positivity
  have hpos2 : 0 ≤ ((12 * C_G * ‖lam‖) * (ν ^ 3 / clockTheta ν r)) * C_0 := by positivity
  rw [← ENNReal.ofReal_add hpos1 hpos1, ← ENNReal.ofReal_add hpos2 hpos2,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by ring_nf; linarith)

/-! ## Conditional assemblies of `DirectEulerSubBound` and `MovLamDualEulerSubBound` -/

/-- **Conditional assembly of `DirectEulerSubBound` (`PartIII-a:T21/c5/2/2`)** from
`MovLam0EulerPullback κ` and `MovLam0EulerSubBound κ` with zero sorry. -/
theorem directEulerSubBound_of (κ : PlanarFrameKernels)
    (hPull : MovLam0EulerPullback κ)
    (hSub0 : MovLam0EulerSubBound κ) : DirectEulerSubBound κ := by
  intro hκ P hP m hm
  obtain ⟨D_ep, hDep, hEp⟩ := hPull hκ
  have hκ' := hκ
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, hcl⟩ := hκ'
  have hP_lam : P.eigenvalue = lam := planar_eigenvalue_eq_seed P hP hIS
  obtain ⟨C_G, D_G, hCG, hDG, hGram⟩ := perGram_inv_sub_id_bound κ
  obtain ⟨C_0, hC0, hLam0⟩ := memLp_and_xNorm_perLam0 κ hm
  obtain ⟨C_0e, b_0e, hC0e, hb0e, hE0⟩ := hSub0 hκ lam h hh ℓ hIS he0 he1 hcl m hm
  set D := max D_G D_ep
  have hD_ge_one : 1 ≤ D := le_trans hDG (le_max_left _ _)
  have hD_nonneg : 0 ≤ D := by linarith
  set C_e := 6 * C_0e + 24 * C_G * ‖lam‖ * C_0
  refine ⟨C_e, b_0e, by positivity, hb0e, fun b hb => ?_⟩
  obtain ⟨ν_0e, hν0e, hνE⟩ := hE0 b hb
  refine ⟨min ν_0e (1 / (D + 1) ^ 2), lt_min hν0e (by positivity),
    fun ν hν tr htr r hr hbr i => ?_⟩
  have hν_e : ν ∈ Ioc 0 ν_0e := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_D : ν ≤ 1 / (D + 1) ^ 2 := hν.2.trans (min_le_right _ _)
  have hν1 : ν ∈ Ioc 0 1 := ⟨hν.1, hν_D.trans (by
    rw [div_le_one (by positivity)]
    nlinarith)⟩
  have hb1 : 1 ≤ b := le_trans hb0e hb
  have hθ : 1 ≤ clockTheta ν r := le_trans hb1 hbr
  have hdD : D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    cellLen_ge hD_nonneg hν.1 hν_D hb1 hr hbr
  have hdDG : D_G ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_left _ _) hdD
  have hdDep : D_ep ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_right _ _) hdD
  have hd1 : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans hD_ge_one hdD
  obtain ⟨hGinv, hGsub⟩ := hGram _ hdDG
  have hpull := hEp ν hν1 tr htr r hr hθ hdDep i
  have h0e := hνE ν hν_e tr htr r hr hbr
  rw [hP_lam]
  exact memLp_and_xNorm_movLamDualEulerSub κ lam tr i hν.1 hr hθ hCG hC0 hC0e
    (hGinv i) (hGsub i) hpull h0e (hLam0 _ hd1)

/-- **Conditional assembly of `MovLamDualEulerSubBound` (`PartIII-a:T21/c5/3/2`)** from
`MovLam0EulerPullback κ` and `MovLam0EulerSubBound κ` with zero sorry. -/
theorem movLamDualEulerSubBound_of (κ : PlanarFrameKernels)
    (hPull : MovLam0EulerPullback κ)
    (hSub0 : MovLam0EulerSubBound κ) : MovLamDualEulerSubBound κ := by
  intro hκ m hm
  obtain ⟨D_ep, hDep, hEp⟩ := hPull hκ
  have hκ' := hκ
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, hcl⟩ := hκ'
  obtain ⟨C_G, D_G, hCG, hDG, hGram⟩ := perGram_inv_sub_id_bound κ
  obtain ⟨C_0, hC0, hLam0⟩ := memLp_and_xNorm_perLam0 κ hm
  obtain ⟨C_0e, b_0e, hC0e, hb0e, hE0⟩ := hSub0 hκ lam h hh ℓ hIS he0 he1 hcl m hm
  set D := max D_G D_ep
  have hD_ge_one : 1 ≤ D := le_trans hDG (le_max_left _ _)
  have hD_nonneg : 0 ≤ D := by linarith
  set C_e := 6 * C_0e + 24 * C_G * ‖lam‖ * C_0
  refine ⟨lam, C_e, b_0e, by positivity, hb0e, fun b hb => ?_⟩
  obtain ⟨ν_0e, hν0e, hνE⟩ := hE0 b hb
  refine ⟨min ν_0e (1 / (D + 1) ^ 2), lt_min hν0e (by positivity),
    fun ν hν tr htr r hr hbr i => ?_⟩
  have hν_e : ν ∈ Ioc 0 ν_0e := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_D : ν ≤ 1 / (D + 1) ^ 2 := hν.2.trans (min_le_right _ _)
  have hν1 : ν ∈ Ioc 0 1 := ⟨hν.1, hν_D.trans (by
    rw [div_le_one (by positivity)]
    nlinarith)⟩
  have hb1 : 1 ≤ b := le_trans hb0e hb
  have hθ : 1 ≤ clockTheta ν r := le_trans hb1 hbr
  have hdD : D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    cellLen_ge hD_nonneg hν.1 hν_D hb1 hr hbr
  have hdDG : D_G ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_left _ _) hdD
  have hdDep : D_ep ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_right _ _) hdD
  have hd1 : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans hD_ge_one hdD
  obtain ⟨hGinv, hGsub⟩ := hGram _ hdDG
  have hpull := hEp ν hν1 tr htr r hr hθ hdDep i
  have h0e := hνE ν hν_e tr htr r hr hbr
  obtain ⟨hmem, hnorm⟩ := memLp_and_xNorm_movLamDualEulerSub κ lam tr i hν.1 hr hθ hCG hC0 hC0e
    (hGinv i) (hGsub i) hpull h0e (hLam0 _ hd1)
  refine ⟨hmem, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hCe_nn : 0 ≤ C_e := by positivity
  have hθpos : 0 < clockTheta ν r := by linarith
  have hν3_le : ν ^ 3 ≤ 1 := pow_le_one₀ hν1.1.le hν1.2
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (by nlinarith) hθpos.le

end DirectEulerSub

/-- Top-level conditional assembly of `DirectEulerSubBound κ` (`PartIII-a:T21/c5/2/2`) from
`MovLam0EulerPullback κ` (`PartIII-a:T21/c5/2/2/1`) and
`MovLam0EulerSubBound κ` (`PartIII-a:T21/c5/2/2/2`). -/
theorem directEulerSubBound_of (κ : PlanarFrameKernels)
    (hPull : MovLam0EulerPullback κ)
    (hSub0 : MovLam0EulerSubBound κ) : DirectEulerSubBound κ :=
  DirectEulerSub.directEulerSubBound_of κ hPull hSub0

end UnforcedLeray.Short.IIIa
