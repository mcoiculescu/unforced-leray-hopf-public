import UnforcedLeray.Short.PartIIa.Tasks.N06BandLimited.HighFreqBounds
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Low-Frequency Subspace, Norm Comparison, and Bernstein `H⁶` Bound (`BernsteinTest`)

Defines the finite-dimensional low-frequency subspace `bandSubspace B N : Submodule ℂ (HSpace B.c MeridC)`
spanned by box-restricted 3D trigonometric polynomials with frequencies in `B.freqSet N`, proves:
1. Self-adjointness of real bounded multipliers `mulChi` on `HSpace c MeridC`;
2. Two-sided `L²` norm comparison between `HSpace B.c MeridC` (`measureH B.c`) and `B.boxMeas`
   on `B.boxSet`;
3. Global `cNorm8 χ` bounds on all iterated derivatives `iteratedFDeriv ℝ k χ` (`k ≤ 8`) for
   `IsNearCutoff c σ H1 L1 χ`;
4. Exact spectral Bernstein + Leibniz `H⁶` bound `h6Norm B.c ζ ≤ C_bern * Gamma^2 * N^6 * ‖z‖`
   for `z ∈ B.bandSubspace N` (`1 ≤ N`), where `ζ = χ • P` represents `(mulChi χ)† z`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N06Aux

open UnforcedLeray.B0220 UnforcedLeray.B0223

/-! ### 1. Self-adjointness of `mulChi` on `HSpace c MeridC` -/

theorem mulChi_coeFn_ae (c : ℝ) (χ : Profile → ℝ) (hm : Measurable χ) {M : ℝ}
    (hM : ∀ p, |χ p| ≤ M) (W : HSpace c MeridC) :
    ((mulChi (measureH c) χ hm hM W : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
      fun p => χ p • (W : Profile → MeridC) p :=
  (memLp_chi_smul (measureH c) χ hm hM (Lp.memLp W)).coeFn_toLp

theorem mulChi_adjoint_apply (c : ℝ) (χ : Profile → ℝ) (hm : Measurable χ) {M : ℝ}
    (hM : ∀ p, |χ p| ≤ M) (Z : HSpace c MeridC) :
    ContinuousLinearMap.adjoint (mulChi (E := MeridC) (measureH c) χ hm hM) Z =
      mulChi (E := MeridC) (measureH c) χ hm hM Z := by
  refine ext_inner_left ℂ fun X => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulChi_coeFn_ae c χ hm hM X, mulChi_coeFn_ae c χ hm hM Z] with p hX hZ
  rw [hX, hZ, ← algebraMap_smul ℂ (χ p) _, ← algebraMap_smul ℂ (χ p) _]
  change inner ℂ ((χ p : ℂ) • (X : Profile → MeridC) p) ((Z : Profile → MeridC) p) =
    inner ℂ ((X : Profile → MeridC) p) ((χ p : ℂ) • (Z : Profile → MeridC) p)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-! ### 2. Global `cNorm8` bounds on higher derivatives of `IsNearCutoff` -/

theorem qPeriodic_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ} (k : ℕ)
    {f : Profile → F} (hf : QPeriodic c f) :
    QPeriodic c (iteratedFDeriv ℝ k f) := by
  intro p
  have e : ∀ x : Profile, (x.1, x.2.1 + c, x.2.2) = x + (0, c, 0) := fun x => by
    ext <;> simp
  have h : (fun x : Profile => f (x + (0, c, 0))) = f := by
    funext x; rw [← e x]; exact hf x
  have hsh := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) k ((0, c, 0) : Profile) p
  rw [h, ← e p] at hsh
  exact hsh.symm

theorem iteratedFDeriv_support_box {c σ H1 L1 : ℝ} (k : ℕ) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {p : Profile} (h : iteratedFDeriv ℝ k χ p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  have hcl : IsClosed {p : Profile | σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd))
          continuous_const))
  have hts : tsupport χ ⊆ {p : Profile | σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1} :=
    closure_minimal (fun q hq => hχ.support q hq) hcl
  exact hts (support_iteratedFDeriv_subset k h)

theorem norm_iteratedFDeriv_le_cNorm8 {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {k : ℕ} (hk : k ≤ 8) (p : Profile) :
    ‖iteratedFDeriv ℝ k χ p‖ ≤ cNorm8 χ := by
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous (iteratedFDeriv ℝ k χ) :=
    hχ.smooth.continuous_iteratedFDeriv (by simp)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hper := qPeriodic_iteratedFDeriv (E := Profile) k hχ.periodic
  have hbdd : BddAbove (range fun q : Profile => ‖iteratedFDeriv ℝ k χ q‖) := by
    refine ⟨max C0 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : iteratedFDeriv ℝ k χ q' = iteratedFDeriv ℝ k χ q :=
      periodic_reduceIoc_eq _ hper q.1 q.2.1 q.2.2
    rw [← hpeq]
    by_cases h0 : iteratedFDeriv ℝ k χ q' = 0
    · simp [h0]
    · obtain ⟨hs1, hs2, hη⟩ := iteratedFDeriv_support_box k hχ h0
      have hq' : q' ∈ K := ⟨⟨hs1, hs2⟩, Ioc_subset_Icc_self (reduceIoc_mem hc q.2.1), abs_le.1 hη⟩
      exact (hC0 q' hq').trans (le_max_left C0 0)
  calc ‖iteratedFDeriv ℝ k χ p‖
      ≤ ⨆ q, ‖iteratedFDeriv ℝ k χ q‖ := le_ciSup hbdd p
    _ ≤ ∑ j ∈ Finset.range 9, ⨆ q, ‖iteratedFDeriv ℝ j χ q‖ :=
        Finset.single_le_sum (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ = cNorm8 χ := rfl

namespace BoxParams

/-! ### 3. Continuous integrability on `B.boxMeas`, `trigMerid`, and `bandSubspace` -/

theorem integrable_boxMeas_of_continuous (B : BoxParams) {E : Type*} [NormedAddCommGroup E]
    {g : Profile → E} (hg : Continuous g) : Integrable g B.boxMeas := by
  have : IsFiniteMeasure B.boxMeas := B.isFiniteMeasure_boxMeas
  let K : Set Profile := Icc B.as B.bs ×ˢ (Icc 0 B.c ×ˢ Icc B.aη B.bη)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have hsub : B.boxSet ⊆ K := by
    rintro ⟨s, q, η⟩ ⟨hs, hq, hη⟩
    exact ⟨Ioc_subset_Icc_self hs, Ioc_subset_Icc_self hq, Ioc_subset_Icc_self hη⟩
  refine (integrable_const C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem B.measurableSet_boxSet] with p hp
  exact hC p (hsub hp)

/-- Meridional trigonometric polynomial supported on frequencies in `B.freqSet N`. -/
def trigMerid (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) (p : Profile) : MeridC :=
  ∑ n ∈ B.freqSet N, B.mode3D n p • a n

/-- Coefficient map extracting the `B.coeff3D` Fourier modes of `u : Profile → MeridC`. -/
def coeffMerid (B : BoxParams) (u : Profile → MeridC) (n : ℤ × ℤ × ℤ) : MeridC :=
  !₂[B.coeff3D (fun q => u q 0) n, B.coeff3D (fun q => u q 1) n]

theorem trigMerid_apply_coord (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC)
    (p : Profile) (j : Fin 2) :
    B.trigMerid N a p j = B.trigSum (B.freqSet N) (fun n => a n j) p := by
  unfold trigMerid trigSum
  have hproj := map_sum (EuclideanSpace.proj j : MeridC →L[ℂ] ℂ)
    (fun n => B.mode3D n p • a n) (B.freqSet N)
  simpa only [EuclideanSpace.coe_proj, map_smul, smul_eq_mul, mul_comm] using hproj

theorem trigMerid_coeffMerid_eq_projMerid (B : BoxParams) (N : ℝ) (u : Profile → MeridC) :
    B.trigMerid N (B.coeffMerid u) = B.projMerid N u := by
  funext p
  ext j
  rw [B.trigMerid_apply_coord]
  fin_cases j <;> simp [coeffMerid, projMerid]

theorem contDiff_trigMerid (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) :
    ContDiff ℝ ∞ (B.trigMerid N a) := by
  unfold trigMerid
  exact ContDiff.sum fun n _ => (B.contDiff_mode3D n).smul contDiff_const

theorem qPeriodic_trigMerid (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) :
    QPeriodic B.c (B.trigMerid N a) := by
  intro p
  unfold trigMerid
  simp only [B.qPeriodic_mode3D _ p]

theorem trigMerid_add (B : BoxParams) (N : ℝ) (a b : (ℤ × ℤ × ℤ) → MeridC) (p : Profile) :
    B.trigMerid N (a + b) p = B.trigMerid N a p + B.trigMerid N b p := by
  unfold trigMerid
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem trigMerid_smul (B : BoxParams) (N : ℝ) (z : ℂ) (a : (ℤ × ℤ × ℤ) → MeridC) (p : Profile) :
    B.trigMerid N (z • a) p = z • B.trigMerid N a p := by
  unfold trigMerid
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Pi.smul_apply, smul_comm]

/-- Box-restricted trigonometric polynomial `1_{B.boxSet} • trigMerid B N a`. -/
def boxIndTrig (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) : Profile → MeridC :=
  B.boxSet.indicator (B.trigMerid N a)

/-! ### 4. Two-sided `weightH` bounds on `B.boxSet` and `HSpace` vs `B.boxMeas` norms -/

theorem mem_boxSet_of_cell_support (B : BoxParams) {p : Profile} (hcell : p ∈ cell B.c)
    (hs1 : B.σ ≤ p.1) (hs2 : p.1 ≤ B.H1) (hη : |p.2.2| ≤ B.L1) :
    p ∈ B.boxSet := by
  rcases hcell with ⟨_, hq, _⟩
  rw [abs_le] at hη
  refine ⟨⟨?_, ?_⟩, hq, ⟨?_, ?_⟩⟩
  · unfold as; linarith [B.hσ]
  · unfold bs; linarith
  · unfold aη; linarith
  · unfold bη; linarith

theorem weightH_le_on_boxSet (B : BoxParams) {p : Profile} (hp : p ∈ B.boxSet) :
    weightH p ≤ ENNReal.ofReal ((1 + 2 * B.σ⁻¹) ^ 2) := by
  rcases hp with ⟨⟨hs1, _⟩, _, _⟩
  unfold as at hs1
  have hσ_pos := B.hσ
  have hs_pos : 0 < p.1 := by linarith
  have hinv_le : p.1⁻¹ ≤ 2 * B.σ⁻¹ := by
    have h1 : (B.σ / 2)⁻¹ = 2 * B.σ⁻¹ := by ring
    rw [← h1]
    exact inv_anti₀ (by positivity) hs1.le
  have h1_le : 1 ≤ 1 + 2 * B.σ⁻¹ := by
    have : 0 ≤ 2 * B.σ⁻¹ := by positivity
    linarith
  have hp_le : p.1⁻¹ ≤ 1 + 2 * B.σ⁻¹ := by linarith
  have hrpow : p.1 ^ (-(3 / 2 : ℝ)) ≤ (1 + 2 * B.σ⁻¹) ^ 2 := by
    calc p.1 ^ (-(3 / 2 : ℝ))
        = (p.1⁻¹) ^ (3 / 2 : ℝ) := by rw [Real.inv_rpow hs_pos.le, Real.rpow_neg hs_pos.le]
      _ ≤ (1 + 2 * B.σ⁻¹) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hs_pos.le) hp_le (by norm_num)
      _ ≤ (1 + 2 * B.σ⁻¹) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1_le (by norm_num)
      _ = (1 + 2 * B.σ⁻¹) ^ 2 := Real.rpow_two _
  unfold weightH
  exact ENNReal.ofReal_le_ofReal hrpow

theorem one_le_mul_weightH_on_boxSet (B : BoxParams) {p : Profile} (hp : p ∈ B.boxSet) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((3 + B.H1) ^ 2) * weightH p := by
  rcases hp with ⟨⟨hs1, hs2⟩, _, _⟩
  unfold as at hs1
  unfold bs at hs2
  have hσ_pos := B.hσ
  have hH1_pos : 0 < B.H1 := lt_of_lt_of_le hσ_pos B.hσH1
  have hs_pos : 0 < p.1 := by linarith
  have h1_le : 1 ≤ 3 + B.H1 := by linarith
  have hp_le : p.1 ≤ 3 + B.H1 := by linarith
  have hrpow : p.1 ^ (3 / 2 : ℝ) ≤ (3 + B.H1) ^ 2 := by
    calc p.1 ^ (3 / 2 : ℝ)
        ≤ (3 + B.H1) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp_le (by norm_num)
      _ ≤ (3 + B.H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1_le (by norm_num)
      _ = (3 + B.H1) ^ 2 := Real.rpow_two _
  have h1 : (1 : ℝ) ≤ (3 + B.H1) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) := by
    calc (1 : ℝ)
        = p.1 ^ (3 / 2 : ℝ) * p.1 ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hs_pos]; norm_num
      _ ≤ (3 + B.H1) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
  unfold weightH
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h1

/-- Exact reduction of the `measureH B.c` lintegral to `B.boxMeas` for any function vanishing on
`cell B.c \ B.boxSet`. -/
private theorem lintegral_measureH_eq_boxMeas_of_zero_outside (B : BoxParams)
    {w : Profile → MeridC} (hw : AEStronglyMeasurable w (cellMeasure B.c))
    (hsupp : ∀ p ∈ cell B.c, p ∉ B.boxSet → w p = 0) :
    ∫⁻ p, ‖w p‖ₑ ^ (2 : ℝ) ∂(measureH B.c) =
      ∫⁻ p, weightH p * ‖w p‖ₑ ^ (2 : ℝ) ∂B.boxMeas := by
  rw [measureH, lintegral_withDensity_eq_lintegral_mul₀ measurable_weightH.aemeasurable
    (hw.aemeasurable.enorm.pow_const (2 : ℝ))]
  change ∫⁻ p, weightH p * ‖w p‖ₑ ^ (2 : ℝ) ∂(cellMeasure B.c) = _
  rw [← B.cellMeasure_restrict_boxSet, ← lintegral_indicator B.measurableSet_boxSet]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell B.c)] with p hp
  by_cases hpB : p ∈ B.boxSet
  · simp [Set.indicator, hpB]
  · simp [Set.indicator, hpB, hsupp p hp hpB]

private theorem lintegral_enorm_sq_eq_ofReal_integral (μ : Measure Profile)
    {w : Profile → MeridC} (hw : MemLp w 2 μ) :
    ∫⁻ p, ‖w p‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ p, ‖w p‖ ^ 2 ∂μ) := by
  have hint : Integrable (fun p => ‖w p‖ ^ 2) μ := hw.integrable_norm_pow two_ne_zero
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
  refine lintegral_congr fun p => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

private theorem lintegral_measureH_eq_ofReal_norm_sq (c : ℝ) (W : HSpace c MeridC)
    {w : Profile → MeridC} (hae : (W : Profile → MeridC) =ᵐ[measureH c] w) :
    ∫⁻ p, ‖w p‖ₑ ^ (2 : ℝ) ∂(measureH c) = ENNReal.ofReal (‖W‖ ^ 2) := by
  have hcongr : ∫⁻ p, ‖w p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ∫⁻ p, ‖(W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp]
  have hLp : eLpNorm (W : Profile → MeridC) 2 (measureH c) = ENNReal.ofReal ‖W‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top W)]
  have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := measureH c)
    (f := (W : Profile → MeridC)) two_ne_zero ENNReal.ofNat_ne_top
  rw [hLp, ENNReal.toReal_ofNat] at heq
  have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
  rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg W) (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_two] at hpow
  exact hcongr.trans hpow

theorem memLp_trigMerid_boxMeas (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) :
    MemLp (B.trigMerid N a) 2 B.boxMeas := by
  have hc : Continuous (B.trigMerid N a) := (B.contDiff_trigMerid N a).continuous
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  exact B.integrable_boxMeas_of_continuous (hc.norm.pow 2)

theorem memLp_boxIndTrig_measureH (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) :
    MemLp (B.boxIndTrig N a) 2 (measureH B.c) := by
  have hm_ind : Measurable (B.boxIndTrig N a) :=
    (B.contDiff_trigMerid N a).continuous.measurable.indicator B.measurableSet_boxSet
  refine ⟨hm_ind.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hred := B.lintegral_measureH_eq_boxMeas_of_zero_outside hm_ind.aestronglyMeasurable
    (fun p _ hpB => by simp [boxIndTrig, Set.indicator, hpB])
  have hle : ∫⁻ p, ‖B.boxIndTrig N a p‖ₑ ^ (2 : ℝ) ∂(measureH B.c) ≤
      ENNReal.ofReal ((1 + 2 * B.σ⁻¹) ^ 2) *
        ENNReal.ofReal (∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) := by
    rw [hred, ← lintegral_enorm_sq_eq_ofReal_integral B.boxMeas (B.memLp_trigMerid_boxMeas N a),
      ← lintegral_const_mul _
        ((B.contDiff_trigMerid N a).continuous.measurable.enorm.pow_const (2 : ℝ))]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem B.measurableSet_boxSet] with p hp
    have hind : B.boxIndTrig N a p = B.trigMerid N a p := Set.indicator_of_mem hp _
    rw [hind]
    exact mul_le_mul_of_nonneg_right (B.weightH_le_on_boxSet hp) zero_le
  have hfin : ENNReal.ofReal ((1 + 2 * B.σ⁻¹) ^ 2) *
      ENNReal.ofReal (∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle hfin).ne

/-- `ℂ`-linear evaluation map sending Fourier coefficients `a` to `[1_{boxSet} • trigMerid B N a]`
in `HSpace B.c MeridC`. -/
def evalTrig (B : BoxParams) (N : ℝ) : ((ℤ × ℤ × ℤ) → MeridC) →ₗ[ℂ] HSpace B.c MeridC where
  toFun a := (B.memLp_boxIndTrig_measureH N a).toLp (B.boxIndTrig N a)
  map_add' a b := by
    apply Lp.ext
    filter_upwards [(B.memLp_boxIndTrig_measureH N (a + b)).coeFn_toLp,
      (B.memLp_boxIndTrig_measureH N a).coeFn_toLp,
      (B.memLp_boxIndTrig_measureH N b).coeFn_toLp,
      Lp.coeFn_add ((B.memLp_boxIndTrig_measureH N a).toLp _)
        ((B.memLp_boxIndTrig_measureH N b).toLp _)] with p h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    by_cases hp : p ∈ B.boxSet
    · simp [boxIndTrig, Set.indicator, hp, B.trigMerid_add]
    · simp [boxIndTrig, Set.indicator, hp]
  map_smul' z a := by
    apply Lp.ext
    filter_upwards [(B.memLp_boxIndTrig_measureH N (z • a)).coeFn_toLp,
      (B.memLp_boxIndTrig_measureH N a).coeFn_toLp,
      Lp.coeFn_smul z ((B.memLp_boxIndTrig_measureH N a).toLp _)] with p h1 h2 h3
    simp only [RingHom.id_apply, h1, h3, Pi.smul_apply, h2]
    by_cases hp : p ∈ B.boxSet
    · simp [boxIndTrig, Set.indicator, hp, B.trigMerid_smul]
    · simp [boxIndTrig, Set.indicator, hp]

theorem evalTrig_coeFn_ae (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC) :
    ((B.evalTrig N a : HSpace B.c MeridC) : Profile → MeridC) =ᵐ[measureH B.c]
      B.boxIndTrig N a :=
  (B.memLp_boxIndTrig_measureH N a).coeFn_toLp

/-- Finite-dimensional band-limited subspace `V ⊆ HSpace B.c MeridC` at cutoff `N`. -/
def bandSubspace (B : BoxParams) (N : ℝ) : Submodule ℂ (HSpace B.c MeridC) :=
  LinearMap.range (B.evalTrig N)

/-- Upper comparison: for box-supported `u` representing `U ∈ HSpace B.c MeridC`,
`‖U - evalTrig B N a‖_H ≤ (1 + 2 σ⁻¹) ‖u - trigMerid B N a‖_{L²(boxMeas)}`. -/
theorem norm_sub_evalTrig_le (B : BoxParams) (N : ℝ) {U : HSpace B.c MeridC}
    {u : Profile → MeridC} (hae : (U : Profile → MeridC) =ᵐ[measureH B.c] u)
    (hu : MemLp u 2 (cellMeasure B.c))
    (hsupp : ∀ p : Profile, u p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1)
    (a : (ℤ × ℤ × ℤ) → MeridC) :
    ‖U - B.evalTrig N a‖ ≤
      (1 + 2 * B.σ⁻¹) * (∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) := by
  let w : Profile → MeridC := fun p => u p - B.boxIndTrig N a p
  have hm_ind : Measurable (B.boxIndTrig N a) :=
    (B.contDiff_trigMerid N a).continuous.measurable.indicator B.measurableSet_boxSet
  have hw_meas : AEStronglyMeasurable w (cellMeasure B.c) :=
    hu.1.sub hm_ind.aestronglyMeasurable
  have hw_ae : ((U - B.evalTrig N a : HSpace B.c MeridC) : Profile → MeridC) =ᵐ[measureH B.c] w := by
    filter_upwards [Lp.coeFn_sub U (B.evalTrig N a), hae, B.evalTrig_coeFn_ae N a] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hw_supp : ∀ p ∈ cell B.c, p ∉ B.boxSet → w p = 0 := by
    intro p hp hpB
    have hu0 : u p = 0 := by
      by_contra hne
      obtain ⟨hs1, hs2, hη⟩ := hsupp p hne
      exact hpB (B.mem_boxSet_of_cell_support hp hs1 hs2 hη)
    simp [w, hu0, boxIndTrig, Set.indicator, hpB]
  have hu_box : MemLp u 2 B.boxMeas := by
    rw [← B.cellMeasure_restrict_boxSet]
    exact hu.restrict B.boxSet
  have hdiff_box : MemLp (fun p => u p - B.trigMerid N a p) 2 B.boxMeas :=
    hu_box.sub (B.memLp_trigMerid_boxMeas N a)
  have hlint_le :
      ENNReal.ofReal (‖U - B.evalTrig N a‖ ^ 2) ≤
        ENNReal.ofReal (((1 + 2 * B.σ⁻¹) ^ 2) *
          ∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) := by
    rw [← lintegral_measureH_eq_ofReal_norm_sq B.c (U - B.evalTrig N a) hw_ae,
      B.lintegral_measureH_eq_boxMeas_of_zero_outside hw_meas hw_supp,
      ENNReal.ofReal_mul (sq_nonneg _),
      ← lintegral_enorm_sq_eq_ofReal_integral B.boxMeas hdiff_box]
    have hw_eq_ae :
        (fun p => weightH p * ‖w p‖ₑ ^ (2 : ℝ)) =ᵐ[B.boxMeas]
          fun p => weightH p * ‖u p - B.trigMerid N a p‖ₑ ^ (2 : ℝ) := by
      filter_upwards [ae_restrict_mem B.measurableSet_boxSet] with p hp
      simp [w, boxIndTrig, Set.indicator_of_mem hp]
    rw [lintegral_congr_ae hw_eq_ae]
    calc ∫⁻ p, weightH p * ‖u p - B.trigMerid N a p‖ₑ ^ (2 : ℝ) ∂B.boxMeas
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + 2 * B.σ⁻¹) ^ 2) *
            ‖u p - B.trigMerid N a p‖ₑ ^ (2 : ℝ) ∂B.boxMeas := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem B.measurableSet_boxSet] with p hp
          exact mul_le_mul_of_nonneg_right (B.weightH_le_on_boxSet hp) zero_le
      _ = ENNReal.ofReal ((1 + 2 * B.σ⁻¹) ^ 2) *
            ∫⁻ p, ‖u p - B.trigMerid N a p‖ₑ ^ (2 : ℝ) ∂B.boxMeas :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hrhs_nn : 0 ≤ (1 + 2 * B.σ⁻¹) *
      (∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) := by
    have := B.hσ
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)
  have hint_nn : 0 ≤ ∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas :=
    integral_nonneg fun _ => sq_nonneg _
  have hreal_sq : ‖U - B.evalTrig N a‖ ^ 2 ≤
      ((1 + 2 * B.σ⁻¹) *
        (∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ)) ^ 2 := by
    have h1 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) hint_nn)).1 hlint_le
    have h2 : ((1 + 2 * B.σ⁻¹) ^ 2) * ∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas =
        ((1 + 2 * B.σ⁻¹) *
          (∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hint_nn]
    rwa [h2] at h1
  calc ‖U - B.evalTrig N a‖
      = Real.sqrt (‖U - B.evalTrig N a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((1 + 2 * B.σ⁻¹) *
          (∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt hreal_sq
    _ = (1 + 2 * B.σ⁻¹) * (∫ p, ‖u p - B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) :=
        Real.sqrt_sq hrhs_nn

/-- Lower comparison: `‖trigMerid B N a‖_{L²(boxMeas)} ≤ (3 + H1) ‖evalTrig B N a‖_H`. -/
theorem boxL2_trigMerid_le_norm_evalTrig (B : BoxParams) (N : ℝ)
    (a : (ℤ × ℤ × ℤ) → MeridC) :
    (∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) ≤
      (3 + B.H1) * ‖B.evalTrig N a‖ := by
  have hm_ind : Measurable (B.boxIndTrig N a) :=
    (B.contDiff_trigMerid N a).continuous.measurable.indicator B.measurableSet_boxSet
  have hlint_le :
      ENNReal.ofReal (∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) ≤
        ENNReal.ofReal (((3 + B.H1) * ‖B.evalTrig N a‖) ^ 2) := by
    rw [← lintegral_enorm_sq_eq_ofReal_integral B.boxMeas (B.memLp_trigMerid_boxMeas N a)]
    have hstep :
        ∫⁻ p, ‖B.trigMerid N a p‖ₑ ^ (2 : ℝ) ∂B.boxMeas ≤
          ENNReal.ofReal ((3 + B.H1) ^ 2) *
            ∫⁻ p, weightH p * ‖B.boxIndTrig N a p‖ₑ ^ (2 : ℝ) ∂B.boxMeas := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem B.measurableSet_boxSet] with p hp
      have hind : B.boxIndTrig N a p = B.trigMerid N a p := Set.indicator_of_mem hp _
      rw [hind, ← mul_assoc]
      calc ‖B.trigMerid N a p‖ₑ ^ (2 : ℝ)
          = 1 * ‖B.trigMerid N a p‖ₑ ^ (2 : ℝ) := (one_mul _).symm
        _ ≤ (ENNReal.ofReal ((3 + B.H1) ^ 2) * weightH p) *
              ‖B.trigMerid N a p‖ₑ ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_right (B.one_le_mul_weightH_on_boxSet hp) zero_le
    refine hstep.trans ?_
    rw [← B.lintegral_measureH_eq_boxMeas_of_zero_outside hm_ind.aestronglyMeasurable
      (fun p _ hpB => by simp [boxIndTrig, Set.indicator, hpB]),
      lintegral_measureH_eq_ofReal_norm_sq B.c (B.evalTrig N a) (B.evalTrig_coeFn_ae N a),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  have hreal_sq := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 hlint_le
  have hH1_pos : 0 < B.H1 := lt_of_lt_of_le B.hσ B.hσH1
  have hrhs_nn : 0 ≤ (3 + B.H1) * ‖B.evalTrig N a‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  rw [← Real.sqrt_eq_rpow]
  calc Real.sqrt (∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas)
      ≤ Real.sqrt (((3 + B.H1) * ‖B.evalTrig N a‖) ^ 2) := Real.sqrt_le_sqrt hreal_sq
    _ = (3 + B.H1) * ‖B.evalTrig N a‖ := Real.sqrt_sq hrhs_nn

/-! ### 5. Spectral Bernstein inequality on `trigMerid` and Leibniz `H⁶` bound -/

private theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : ∀ i, ∑ j ∈ s, (f i - f j) ^ 2 =
      (s.card : ℝ) * f i ^ 2 - 2 * f i * (∑ j ∈ s, f j) + ∑ j ∈ s, f j ^ 2 := by
    intro i
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_assoc, ← Finset.mul_sum]
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at h0
  have h2 : ∑ i ∈ s, 2 * f i * (∑ j ∈ s, f j) = 2 * (∑ i ∈ s, f i) ^ 2 := by
    rw [← Finset.sum_mul]
    simp_rw [← Finset.mul_sum]
    ring
  linarith

private def basisVec : Fin 3 → Profile
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)

private def coordOf (v : Profile) : Fin 3 → ℝ
  | 0 => v.1
  | 1 => v.2.1
  | 2 => v.2.2

private theorem profile_eq_sum_basisVec (v : Profile) :
    v = ∑ d : Fin 3, coordOf v d • basisVec d := by
  ext <;> simp [Fin.sum_univ_three, basisVec, coordOf]

private theorem abs_coordOf_le_norm (v : Profile) (d : Fin 3) :
    |coordOf v d| ≤ ‖v‖ := by
  fin_cases d
  · simp [coordOf, Prod.norm_def]
  · simp only [coordOf, Prod.norm_def, Real.norm_eq_abs]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · simp only [coordOf, Prod.norm_def, Real.norm_eq_abs]
    exact (le_max_right _ _).trans (le_max_right _ _)

private theorem opNorm_multilinear_le_sum_basisVec {k : ℕ}
    (M : Profile [×k]→L[ℝ] MeridC) :
    ‖M‖ ≤ ∑ α : Fin k → Fin 3, ‖M (basisVec ∘ α)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m => ?_
  have hm_eq : m = fun r : Fin k => ∑ d : Fin 3, coordOf (m r) d • basisVec d :=
    funext fun r => profile_eq_sum_basisVec (m r)
  conv_lhs => rw [hm_eq]
  rw [M.map_sum]
  have hterm : ∀ α : Fin k → Fin 3,
      M (fun r => coordOf (m r) (α r) • basisVec (α r)) =
        (∏ r : Fin k, coordOf (m r) (α r)) • M (basisVec ∘ α) :=
    fun α => M.map_smul_univ (fun r => coordOf (m r) (α r)) (fun r => basisVec (α r))
  simp_rw [hterm]
  calc ‖∑ α : Fin k → Fin 3, (∏ r : Fin k, coordOf (m r) (α r)) • M (basisVec ∘ α)‖
      ≤ ∑ α : Fin k → Fin 3, ‖(∏ r : Fin k, coordOf (m r) (α r)) • M (basisVec ∘ α)‖ :=
        norm_sum_le _ _
    _ = ∑ α : Fin k → Fin 3, (∏ r : Fin k, |coordOf (m r) (α r)|) * ‖M (basisVec ∘ α)‖ := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ ∑ α : Fin k → Fin 3, (∏ r : Fin k, ‖m r‖) * ‖M (basisVec ∘ α)‖ := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun r _ => abs_coordOf_le_norm (m r) (α r)
    _ = (∑ α : Fin k → Fin 3, ‖M (basisVec ∘ α)‖) * ∏ r : Fin k, ‖m r‖ := by
        rw [← Finset.mul_sum, mul_comm]

theorem iteratedFDeriv_mode3D_apply (B : BoxParams) (n : ℤ × ℤ × ℤ) :
    ∀ (k : ℕ) (p : Profile) (m : Fin k → Profile),
      iteratedFDeriv ℝ k (B.mode3D n) p m =
        (∏ r : Fin k, (I * (B.phaseCLM n (m r) : ℂ))) * B.mode3D n p
  | 0, p, m => by simp
  | k + 1, p, m => by
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k (B.mode3D n)) p :=
        (B.contDiff_mode3D n).differentiable_iteratedFDeriv
          (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top k)) p
      rw [hd.iteratedFDeriv_succ_apply_left']
      set c_tail : ℂ := ∏ r : Fin k, (I * (B.phaseCLM n (Fin.tail m r) : ℂ))
      have hfun : (fun y : Profile => iteratedFDeriv ℝ k (B.mode3D n) y (Fin.tail m)) =
          fun y => c_tail * B.mode3D n y := by
        funext y
        exact B.iteratedFDeriv_mode3D_apply n k y (Fin.tail m)
      rw [hfun]
      let Lc : ℂ →L[ℝ] ℂ := (c_tail • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
      have hfd : HasFDerivAt (fun y : Profile => c_tail * B.mode3D n y)
          (Lc.comp ((I * B.mode3D n p) • (Complex.ofRealCLM.comp (B.phaseCLM n)))) p := by
        change HasFDerivAt (Lc ∘ B.mode3D n) _ p
        exact Lc.hasFDerivAt.comp p (B.hasFDerivAt_mode3D n p)
      rw [hfd.fderiv, Fin.prod_univ_succ]
      simp only [Lc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
        smul_apply, ContinuousLinearMap.id_apply, Complex.ofRealCLM_apply, smul_eq_mul]
      dsimp only [c_tail, Fin.tail]
      ring

theorem iteratedFDeriv_trigMerid_coord (B : BoxParams) (N : ℝ) (a : (ℤ × ℤ × ℤ) → MeridC)
    (k : ℕ) (p : Profile) (m : Fin k → Profile) (j : Fin 2) :
    (iteratedFDeriv ℝ k (B.trigMerid N a) p m) j =
      B.trigSum (B.freqSet N)
        (fun n => (∏ r : Fin k, (I * (B.phaseCLM n (m r) : ℂ))) * a n j) p := by
  let projR : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj j : MeridC →L[ℂ] ℂ).restrictScalars ℝ
  have hcomp := projR.iteratedFDeriv_comp_left
    ((B.contDiff_trigMerid N a).contDiffAt (x := p)) (i := k) (by simp)
  have happ := congrArg (fun M : Profile [×k]→L[ℝ] ℂ => M m) hcomp
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    projR, ContinuousLinearMap.coe_restrictScalars', EuclideanSpace.coe_proj] at happ
  rw [← happ]
  have hfn : (fun x : MeridC => x j) ∘ B.trigMerid N a =
      fun q => ∑ n ∈ B.freqSet N,
        (((a n j • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ) ∘ B.mode3D n) q := by
    funext q
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      B.trigMerid_apply_coord, trigSum, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, mul_comm]
  rw [hfn, iteratedFDeriv_fun_sum_apply fun n _ =>
    (((a n j • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.comp
      (B.contDiff_mode3D n)).contDiffAt.of_le (by simp),
    sum_apply]
  unfold trigSum
  refine Finset.sum_congr rfl fun n _ => ?_
  let La : ℂ →L[ℝ] ℂ := (a n j • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
  have hLa := La.iteratedFDeriv_comp_left ((B.contDiff_mode3D n).contDiffAt (x := p)) (i := k) (by simp)
  have hLa_app := congrArg (fun M : Profile [×k]→L[ℝ] ℂ => M m) hLa
  change iteratedFDeriv ℝ k (La ∘ B.mode3D n) p m = _
  rw [hLa_app]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    La, ContinuousLinearMap.coe_restrictScalars', smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, B.iteratedFDeriv_mode3D_apply n k p m]
  ring

private theorem abs_phaseCLM_basisVec_le (B : BoxParams) {N : ℝ} (hN : 0 ≤ N)
    {n : ℤ × ℤ × ℤ} (hn : n ∈ B.freqSet N) (d : Fin 3) :
    |B.phaseCLM n (basisVec d)| ≤ 2 * Real.pi * N := by
  obtain ⟨hws, hwq, hwη⟩ := B.lowFreq_wavenumber_le hN hn
  fin_cases d
  · simpa [basisVec, phaseCLM_apply, ws] using hws
  · simpa [basisVec, phaseCLM_apply, wq] using hwq
  · simpa [basisVec, phaseCLM_apply, wη] using hwη

/-- Spectral Bernstein inequality on `B.boxMeas`:
`∫ ‖D^k (trigMerid B N a)‖² ∂B.boxMeas ≤ ((6 π N)^k)² ∫ ‖trigMerid B N a‖² ∂B.boxMeas`. -/
theorem bernstein_trigMerid_sq (B : BoxParams) {N : ℝ} (hN : 0 ≤ N)
    (a : (ℤ × ℤ × ℤ) → MeridC) (k : ℕ) :
    ∫ p, ‖iteratedFDeriv ℝ k (B.trigMerid N a) p‖ ^ 2 ∂B.boxMeas ≤
      ((6 * Real.pi * N) ^ k) ^ 2 * ∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas := by
  have hpiN_nn : 0 ≤ 2 * Real.pi * N := by positivity
  have h_dir_coord : ∀ (α : Fin k → Fin 3) (j : Fin 2),
      ∫ p, ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) j‖ ^ 2 ∂B.boxMeas ≤
        ((2 * Real.pi * N) ^ k) ^ 2 * ∫ p, ‖B.trigMerid N a p j‖ ^ 2 ∂B.boxMeas := by
    intro α j
    simp_rw [B.iteratedFDeriv_trigMerid_coord N a k _ (basisVec ∘ α) j,
      B.trigMerid_apply_coord N a _ j]
    rw [B.integral_trigSum_sq, B.integral_trigSum_sq]
    have hsum_le :
        ∑ n ∈ B.freqSet N, ‖(∏ r : Fin k, (I * (B.phaseCLM n (basisVec (α r)) : ℂ))) * a n j‖ ^ 2 ≤
          ∑ n ∈ B.freqSet N, ((2 * Real.pi * N) ^ k) ^ 2 * ‖a n j‖ ^ 2 := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [norm_mul, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hprod_le : ‖∏ r : Fin k, (I * (B.phaseCLM n (basisVec (α r)) : ℂ))‖ ≤
          (2 * Real.pi * N) ^ k := by
        rw [norm_prod]
        calc ∏ r : Fin k, ‖I * (B.phaseCLM n (basisVec (α r)) : ℂ)‖
            ≤ ∏ _r : Fin k, (2 * Real.pi * N) := by
              refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r _ => ?_
              rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
              exact B.abs_phaseCLM_basisVec_le hN hn (α r)
          _ = (2 * Real.pi * N) ^ k := by simp
      exact pow_le_pow_left₀ (norm_nonneg _) hprod_le 2
    calc B.volBox * ∑ n ∈ B.freqSet N,
            ‖(∏ r : Fin k, (I * (B.phaseCLM n (basisVec (α r)) : ℂ))) * a n j‖ ^ 2
        ≤ B.volBox * ∑ n ∈ B.freqSet N, ((2 * Real.pi * N) ^ k) ^ 2 * ‖a n j‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsum_le B.hvolBox_pos.le
      _ = ((2 * Real.pi * N) ^ k) ^ 2 * (B.volBox * ∑ n ∈ B.freqSet N, ‖a n j‖ ^ 2) := by
          rw [← Finset.mul_sum]; ring
  have hcont_it : Continuous (iteratedFDeriv ℝ k (B.trigMerid N a)) :=
    (B.contDiff_trigMerid N a).continuous_iteratedFDeriv (by simp)
  have hcont_dir : ∀ α : Fin k → Fin 3,
      Continuous (fun p => iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) :=
    fun α => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Profile) MeridC (basisVec ∘ α)).continuous.comp
      hcont_it
  have h_dir : ∀ α : Fin k → Fin 3,
      ∫ p, ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2 ∂B.boxMeas ≤
        ((2 * Real.pi * N) ^ k) ^ 2 * ∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas := by
    intro α
    have hc0 : Continuous (fun p => ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) 0‖ ^ 2) :=
      (((EuclideanSpace.proj 0 : MeridC →L[ℂ] ℂ).continuous.comp (hcont_dir α)).norm).pow 2
    have hc1 : Continuous (fun p => ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) 1‖ ^ 2) :=
      (((EuclideanSpace.proj 1 : MeridC →L[ℂ] ℂ).continuous.comp (hcont_dir α)).norm).pow 2
    have hp0 : Continuous (fun p => ‖B.trigMerid N a p 0‖ ^ 2) :=
      (((EuclideanSpace.proj 0 : MeridC →L[ℂ] ℂ).continuous.comp
        (B.contDiff_trigMerid N a).continuous).norm).pow 2
    have hp1 : Continuous (fun p => ‖B.trigMerid N a p 1‖ ^ 2) :=
      (((EuclideanSpace.proj 1 : MeridC →L[ℂ] ℂ).continuous.comp
        (B.contDiff_trigMerid N a).continuous).norm).pow 2
    have hsplit1 : ∫ p, ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2 ∂B.boxMeas =
        (∫ p, ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) 0‖ ^ 2 ∂B.boxMeas) +
        (∫ p, ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) 1‖ ^ 2 ∂B.boxMeas) := by
      have hpt : ∀ p, ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2 =
          ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) 0‖ ^ 2 +
          ‖(iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)) 1‖ ^ 2 := by
        intro p; rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp_rw [hpt]
      exact integral_add (B.integrable_boxMeas_of_continuous hc0)
        (B.integrable_boxMeas_of_continuous hc1)
    have hsplit2 : ∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas =
        (∫ p, ‖B.trigMerid N a p 0‖ ^ 2 ∂B.boxMeas) +
        (∫ p, ‖B.trigMerid N a p 1‖ ^ 2 ∂B.boxMeas) := by
      have hpt : ∀ p, ‖B.trigMerid N a p‖ ^ 2 =
          ‖B.trigMerid N a p 0‖ ^ 2 + ‖B.trigMerid N a p 1‖ ^ 2 := by
        intro p; rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp_rw [hpt]
      exact integral_add (B.integrable_boxMeas_of_continuous hp0)
        (B.integrable_boxMeas_of_continuous hp1)
    rw [hsplit1, hsplit2]
    linarith [h_dir_coord α 0, h_dir_coord α 1]
  have hcard : ((Finset.univ : Finset (Fin k → Fin 3)).card : ℝ) = (3 : ℝ) ^ k := by
    simp
  have hpt_op : ∀ p : Profile,
      ‖iteratedFDeriv ℝ k (B.trigMerid N a) p‖ ^ 2 ≤
        (3 : ℝ) ^ k * ∑ α : Fin k → Fin 3,
          ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2 := by
    intro p
    have h1 := pow_le_pow_left₀ (norm_nonneg _)
      (opNorm_multilinear_le_sum_basisVec (iteratedFDeriv ℝ k (B.trigMerid N a) p)) 2
    have h2 := sq_sum_le_card_mul_sum_sq (Finset.univ : Finset (Fin k → Fin 3))
      (fun α => ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖)
    rw [hcard] at h2
    exact h1.trans h2
  have hint_lhs : Integrable (fun p => ‖iteratedFDeriv ℝ k (B.trigMerid N a) p‖ ^ 2) B.boxMeas :=
    B.integrable_boxMeas_of_continuous (hcont_it.norm.pow 2)
  have hint_dir : ∀ α : Fin k → Fin 3,
      Integrable (fun p => ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2) B.boxMeas :=
    fun α => B.integrable_boxMeas_of_continuous ((hcont_dir α).norm.pow 2)
  have hint_sum : Integrable
      (fun p => (3 : ℝ) ^ k * ∑ α : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2) B.boxMeas :=
    (integrable_finsetSum _ fun α _ => hint_dir α).const_mul _
  calc ∫ p, ‖iteratedFDeriv ℝ k (B.trigMerid N a) p‖ ^ 2 ∂B.boxMeas
      ≤ ∫ p, (3 : ℝ) ^ k * ∑ α : Fin k → Fin 3,
          ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2 ∂B.boxMeas :=
        integral_mono hint_lhs hint_sum hpt_op
    _ = (3 : ℝ) ^ k * ∑ α : Fin k → Fin 3,
          ∫ p, ‖iteratedFDeriv ℝ k (B.trigMerid N a) p (basisVec ∘ α)‖ ^ 2 ∂B.boxMeas := by
        rw [integral_const_mul, integral_finsetSum _ fun α _ => hint_dir α]
    _ ≤ (3 : ℝ) ^ k * ∑ _α : Fin k → Fin 3,
          (((2 * Real.pi * N) ^ k) ^ 2 * ∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => h_dir α) (by positivity)
    _ = ((6 * Real.pi * N) ^ k) ^ 2 * ∫ p, ‖B.trigMerid N a p‖ ^ 2 ∂B.boxMeas := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        have hp : (3 : ℝ) ^ k * (3 : ℝ) ^ k * ((2 * Real.pi * N) ^ k) ^ 2 =
            ((6 * Real.pi * N) ^ k) ^ 2 := by
          have h6 : (6 * Real.pi * N) ^ k = (3 : ℝ) ^ k * (2 * Real.pi * N) ^ k := by
            rw [← mul_pow]; ring
          rw [h6]; ring
        rw [← mul_assoc, ← mul_assoc, hp]

/-- Explicit constant for the localized Bernstein `H⁶` test bound. -/
def C_bern : ℝ := 98 * 64 * (6 * Real.pi) ^ 6

theorem C_bern_nonneg : 0 ≤ C_bern := by
  unfold C_bern; positivity

/-- **Main Bernstein dual-vector theorem**: for every `z ∈ B.bandSubspace N` (`1 ≤ N`), there is a
smooth box-supported test `ζ` representing `(mulChi χ)† z` a.e. under `measureH B.c` with
`h6Norm B.c ζ ≤ C_bern * Gamma^2 * N^6 * ‖z‖`. -/
theorem bandSubspace_bernstein_h6 (B : BoxParams) {ν M γs : ℝ} {χ χ1 : Profile → ℝ}
    (hν : 0 < ν) (hL1 : 0 ≤ B.L1) (hγ : 0 < γs) (hM0 : 0 ≤ M)
    (hχ : IsNearCutoff B.c B.σ B.H1 B.L1 χ)
    (hm : Measurable χ) {Mχ : ℝ} (hMχ : ∀ p, |χ p| ≤ Mχ)
    {N : ℝ} (hN : 1 ≤ N) {z : HSpace B.c MeridC} (hz : z ∈ B.bandSubspace N) :
    ∃ ζ : Profile → MeridC, IsMeridTest B.c ζ ∧
      (∀ p, ζ p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1) ∧
      ((ContinuousLinearMap.adjoint (mulChi (measureH B.c) χ hm hMχ) z : HSpace B.c MeridC) :
        Profile → MeridC) =ᵐ[measureH B.c] ζ ∧
      h6Norm B.c ζ ≤ C_bern * Gamma ν B.c B.σ B.H1 B.L1 M γs χ χ1 ^ 2 * N ^ (6 : ℕ) * ‖z‖ := by
  obtain ⟨a, rfl⟩ := hz
  set P : Profile → MeridC := B.trigMerid N a
  set ζ : Profile → MeridC := fun p => χ p • P p
  have hζ_smooth : ContDiff ℝ ∞ ζ := hχ.smooth.smul (B.contDiff_trigMerid N a)
  have hζ_per : QPeriodic B.c ζ := by
    intro p
    show χ (p.1, p.2.1 + B.c, p.2.2) • P (p.1, p.2.1 + B.c, p.2.2) = χ p • P p
    dsimp only [P]
    rw [hχ.periodic p, B.qPeriodic_trigMerid N a p]
  have hζ_supp : ∀ p : Profile, ζ p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1 := by
    intro p hp
    refine hχ.support p fun h0 => hp ?_
    simp [ζ, h0]
  have hζ_test : IsMeridTest B.c ζ := by
    refine ⟨hζ_smooth, hζ_per, ⟨B.σ, B.H1, B.L1, B.hσ, ?_⟩⟩
    intro p hp
    obtain ⟨hs1, hs2, hη⟩ := hζ_supp p hp
    exact ⟨⟨hs1, hs2⟩, hη⟩
  have hζ_ae :
      ((ContinuousLinearMap.adjoint (mulChi (measureH B.c) χ hm hMχ) (B.evalTrig N a) :
          HSpace B.c MeridC) : Profile → MeridC) =ᵐ[measureH B.c] ζ := by
    rw [mulChi_adjoint_apply]
    have hae_cell : ∀ᵐ p ∂(cellMeasure B.c), χ p • B.boxIndTrig N a p = ζ p := by
      filter_upwards [ae_restrict_mem (measurableSet_cell B.c)] with p hp
      by_cases h0 : χ p = 0
      · simp [ζ, h0]
      · obtain ⟨hs1, hs2, hη⟩ := hχ.support p h0
        have hpB := B.mem_boxSet_of_cell_support hp hs1 hs2 hη
        simp [ζ, P, boxIndTrig, Set.indicator_of_mem hpB]
    have hae_H : (fun p => χ p • B.boxIndTrig N a p) =ᵐ[measureH B.c] ζ :=
      (withDensity_absolutelyContinuous (cellMeasure B.c) weightH).ae_eq hae_cell
    filter_upwards [mulChi_coeFn_ae B.c χ hm hMχ (B.evalTrig N a),
      B.evalTrig_coeFn_ae N a, hae_H] with p h1 h2 h3
    rw [h1, h2, h3]
  refine ⟨ζ, hζ_test, hζ_supp, hζ_ae, ?_⟩
  have hN0 : 0 ≤ N := by linarith
  have h1_le_6piN : 1 ≤ 6 * Real.pi * N := by
    have hpi : 1 ≤ 6 * Real.pi := by linarith [Real.two_le_pi]
    nlinarith
  have hχ_nn : 0 ≤ cNorm8 χ :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hP_L2_le := B.boxL2_trigMerid_le_norm_evalTrig N a
  have hP_int_le :
      ∫ p, ‖P p‖ ^ 2 ∂B.boxMeas ≤ ((3 + B.H1) * ‖B.evalTrig N a‖) ^ 2 := by
    have hnn : 0 ≤ ∫ p, ‖P p‖ ^ 2 ∂B.boxMeas := integral_nonneg fun _ => sq_nonneg _
    have h1 := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) hP_L2_le 2
    rwa [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn] at h1
  have h_each_m : ∀ m ∈ Finset.range 7,
      (∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂(cellMeasure B.c)) ^ (1 / 2 : ℝ) ≤
        7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖ := by
    intro m hm_mem
    have hm_le : m ≤ 6 := by simp only [Finset.mem_range] at hm_mem; omega
    have hit_supp : ∀ p : Profile, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ≠ 0 →
        B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1 := by
      intro p hp
      have hne : iteratedFDeriv ℝ m ζ p ≠ 0 := fun h0 => hp (by simp [h0])
      have hcl : IsClosed {q : Profile | B.σ ≤ q.1 ∧ q.1 ≤ B.H1 ∧ |q.2.2| ≤ B.L1} :=
        (isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_fst continuous_const).inter
            (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd))
              continuous_const))
      have hts : tsupport ζ ⊆ {q : Profile | B.σ ≤ q.1 ∧ q.1 ≤ B.H1 ∧ |q.2.2| ≤ B.L1} :=
        closure_minimal (fun q hq => hζ_supp q hq) hcl
      exact hts (support_iteratedFDeriv_subset m hne)
    have hcell_eq_box :
        ∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂(cellMeasure B.c) =
          ∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂B.boxMeas :=
      B.integral_cellMeasure_eq_boxMeas hit_supp
    have hpt_le : ∀ p : Profile,
        ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ≤
          7 * (64 * cNorm8 χ) ^ 2 *
            ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2 := by
      intro p
      have hleib := norm_iteratedFDeriv_smul_le hχ.smooth (B.contDiff_trigMerid N a) p
        (n := m) (by simp)
      have hterm : ∀ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ p‖ * ‖iteratedFDeriv ℝ (m - i) P p‖ ≤
            (64 * cNorm8 χ) * ‖iteratedFDeriv ℝ (m - i) P p‖ := by
        intro i hi
        have hi_le : i ≤ 8 := by simp only [Finset.mem_range] at hi; omega
        have hch_nat : m.choose i ≤ 64 := by
          have hsum := Nat.sum_range_choose m
          have h1 : m.choose i ≤ ∑ j ∈ Finset.range (m + 1), m.choose j :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
          have h2 : 2 ^ m ≤ 64 := by
            calc 2 ^ m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hm_le
              _ = 64 := by norm_num
          omega
        have hch : (m.choose i : ℝ) ≤ 64 := by exact_mod_cast hch_nat
        have hχi := norm_iteratedFDeriv_le_cNorm8 B.hc hχ hi_le p
        have hmul1 : (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ p‖ ≤ 64 * cNorm8 χ :=
          mul_le_mul hch hχi (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hmul1 (norm_nonneg _)
      have hsum_le :
          ‖iteratedFDeriv ℝ m ζ p‖ ≤
            (64 * cNorm8 χ) * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ := by
        calc ‖iteratedFDeriv ℝ m ζ p‖
            ≤ ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ p‖ * ‖iteratedFDeriv ℝ (m - i) P p‖ := hleib
          _ ≤ ∑ i ∈ Finset.range (m + 1),
                (64 * cNorm8 χ) * ‖iteratedFDeriv ℝ (m - i) P p‖ := Finset.sum_le_sum hterm
          _ = (64 * cNorm8 χ) * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ :=
              (Finset.mul_sum _ _ _).symm
      have hsq1 := pow_le_pow_left₀ (norm_nonneg _) hsum_le 2
      have hcs := sq_sum_le_card_mul_sum_sq (Finset.range (m + 1))
        (fun i => ‖iteratedFDeriv ℝ (m - i) P p‖)
      have hcard_le : ((Finset.range (m + 1)).card : ℝ) ≤ 7 := by
        rw [Finset.card_range]; exact_mod_cast (show m + 1 ≤ 7 by omega)
      have hsum_sq_nn : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc ‖iteratedFDeriv ℝ m ζ p‖ ^ 2
          ≤ (64 * cNorm8 χ) ^ 2 *
              (∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖) ^ 2 := by
            rwa [mul_pow] at hsq1
        _ ≤ (64 * cNorm8 χ) ^ 2 *
              (((Finset.range (m + 1)).card : ℝ) *
                ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
        _ ≤ (64 * cNorm8 χ) ^ 2 *
              (7 * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcard_le hsum_sq_nn) (sq_nonneg _)
        _ = 7 * (64 * cNorm8 χ) ^ 2 *
              ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2 := by ring
    have hint_ζ : Integrable (fun p => ‖iteratedFDeriv ℝ m ζ p‖ ^ 2) B.boxMeas :=
      B.integrable_boxMeas_of_continuous
        ((hζ_smooth.continuous_iteratedFDeriv (by simp)).norm.pow 2)
    have hint_P : ∀ k : ℕ, Integrable (fun p => ‖iteratedFDeriv ℝ k P p‖ ^ 2) B.boxMeas :=
      fun k => B.integrable_boxMeas_of_continuous
        (((B.contDiff_trigMerid N a).continuous_iteratedFDeriv (by simp)).norm.pow 2)
    have hint_rhs : Integrable
        (fun p => 7 * (64 * cNorm8 χ) ^ 2 *
          ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2) B.boxMeas :=
      (integrable_finsetSum _ fun i _ => hint_P (m - i)).const_mul _
    have hint_le :
        ∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂(cellMeasure B.c) ≤
          (7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖) ^ 2 := by
      rw [hcell_eq_box]
      calc ∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂B.boxMeas
          ≤ ∫ p, 7 * (64 * cNorm8 χ) ^ 2 *
              ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2 ∂B.boxMeas :=
            integral_mono hint_ζ hint_rhs hpt_le
        _ = 7 * (64 * cNorm8 χ) ^ 2 *
              ∑ i ∈ Finset.range (m + 1), ∫ p, ‖iteratedFDeriv ℝ (m - i) P p‖ ^ 2 ∂B.boxMeas := by
            rw [integral_const_mul, integral_finsetSum _ fun i _ => hint_P (m - i)]
        _ ≤ 7 * (64 * cNorm8 χ) ^ 2 *
              ∑ _i ∈ Finset.range (m + 1),
                (((6 * Real.pi * N) ^ 6) ^ 2 * ∫ p, ‖P p‖ ^ 2 ∂B.boxMeas) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
            refine (B.bernstein_trigMerid_sq hN0 a (m - i)).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => sq_nonneg _)
            exact pow_le_pow_left₀ (by positivity)
              (pow_le_pow_right₀ h1_le_6piN (by omega)) 2
        _ ≤ 7 * (64 * cNorm8 χ) ^ 2 *
              (7 * (((6 * Real.pi * N) ^ 6) ^ 2 * ∫ p, ‖P p‖ ^ 2 ∂B.boxMeas)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
            have hcard_le : ((m + 1 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show m + 1 ≤ 7 by omega)
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcard_le
                (mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)))
              (by positivity)
        _ ≤ 7 * (64 * cNorm8 χ) ^ 2 *
              (7 * (((6 * Real.pi * N) ^ 6) ^ 2 * ((3 + B.H1) * ‖B.evalTrig N a‖) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hP_int_le (sq_nonneg _)) (by norm_num))
              (by positivity)
        _ = (7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖) ^ 2 := by
            ring
    have hH1_pos : 0 < B.H1 := lt_of_lt_of_le B.hσ B.hσH1
    have hrhs_nn : 0 ≤ 7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hχ_nn) (by linarith))
        (by positivity)) (norm_nonneg _)
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂(cellMeasure B.c))
        ≤ Real.sqrt ((7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖) ^ 2) :=
          Real.sqrt_le_sqrt hint_le
      _ = 7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖ :=
          Real.sqrt_sq hrhs_nn
  set G := Gamma ν B.c B.σ B.H1 B.L1 M γs χ χ1
  have hχ1_nn : 0 ≤ cNorm8 χ1 :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have h2_H1_le_G : 2 + B.H1 ≤ G := by
    dsimp [G]; unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < B.c⁻¹ := inv_pos.2 B.hc
    have : 0 < B.σ⁻¹ := inv_pos.2 B.hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [B.hc, hL1, hM0, hχ_nn, hχ1_nn]
  have h1_le_G : 1 ≤ G := by
    have hH1_pos : 0 < B.H1 := lt_of_lt_of_le B.hσ B.hσH1
    linarith
  have h3_H1_le : 3 + B.H1 ≤ 2 * G := by linarith
  have hχ_le_G : cNorm8 χ ≤ G := by
    dsimp [G]; unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < B.c⁻¹ := inv_pos.2 B.hc
    have : 0 < B.σ⁻¹ := inv_pos.2 B.hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have hH1_pos : 0 < B.H1 := lt_of_lt_of_le B.hσ B.hσH1
    linarith [B.hc, hL1, hM0, hχ1_nn]
  have hprod_G : cNorm8 χ * (3 + B.H1) ≤ 2 * G ^ 2 := by
    have hH1_pos : 0 < B.H1 := lt_of_lt_of_le B.hσ B.hσH1
    calc cNorm8 χ * (3 + B.H1) ≤ G * (2 * G) :=
          mul_le_mul hχ_le_G h3_H1_le (by linarith) (by linarith)
      _ = 2 * G ^ 2 := by ring
  unfold h6Norm
  calc ∑ m ∈ Finset.range 7, (∫ p, ‖iteratedFDeriv ℝ m ζ p‖ ^ 2 ∂(cellMeasure B.c)) ^ (1 / 2 : ℝ)
      ≤ ∑ _m ∈ Finset.range 7,
          (7 * 64 * (6 * Real.pi) ^ 6 * cNorm8 χ * (3 + B.H1) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖) :=
        Finset.sum_le_sum h_each_m
    _ = (49 * 64 * (6 * Real.pi) ^ 6) * (cNorm8 χ * (3 + B.H1)) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (49 * 64 * (6 * Real.pi) ^ 6) * (2 * G ^ 2) * N ^ (6 : ℕ) * ‖B.evalTrig N a‖ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod_G (by positivity))
            (by positivity))
          (norm_nonneg _)
    _ = C_bern * G ^ 2 * N ^ (6 : ℕ) * ‖B.evalTrig N a‖ := by
        unfold C_bern; ring

end BoxParams

end UnforcedLeray.Short.PartIIa.N06Aux
