import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2

/-!
# `FlatBodyAgeDerivLocal` (`PartII-a:N05/2/2`)

Source of record: `the November 2 reference manuscript`,
lines 1794-1799.

## Structure of this file

1. **Measure absolute continuity `cellMeasure c ≪ measureH c` and representative reduction**
   (`cellMeasure_eq_measureH_withDensity`, `cellMeasure_ac_measureH`,
   `u_ae_eq_flatStressCutRep_cellMeasure`):
   Every representative `u` satisfying `mulChi (measureH c) χ hm hB W =ᵐ[measureH c] u` agrees
   almost everywhere with `flatStressCutRep c χ W` under `cellMeasure c`, reducing the `ibp_s`
   pairing `-∫ ⟨u, pdS φ⟩ ∂(cellMeasure c)` to the concrete representative `flatStressCutRep c χ W`.
2. **Age-multiplier operator `sMul` (`s • ·`) and `dsFromS` inversion on `[σ, H1]`**
   (`sMul`, `dsFromS_sMul`, `sMul_dsFromS`, `memLp_sMul_flat`, `cellL2Norm_sMul_flat_le`):
   Proves `dsFromS (sMul f) = f` pointwise on `[σ, H1]` (`σ > 0`) and
   `cellL2Norm c (sMul f) ≤ Gamma ν c σ H1 L1 M γs χ χ1 * cellL2Norm c f`.
3. **Explicit constituent terms of `Su = S(χ w) = (s ∂_s χ) w - μ χ w + χ P_0 b + ν s χ Δ_{q,η} w`**
   (`flatCutAgeCutoffTerm`, `flatCutAgeDriftTerm`, `flatCutAgeForceTerm`,
   `flatCutAgeExplicitPart`, `cellL2Norm_flatCutAgeExplicitPart_T0flat_le`):
   Constructs and bounds the three zero/first-order constituent terms of `Su` in `L²(cellMeasure c)`:
   - `(s ∂_s χ) w` (`flatCutAgeCutoffTerm c χ W`): `≤ Gamma^4 * ‖b‖`;
   - `-μ χ w` (`flatCutAgeDriftTerm c χ μ W`): `≤ Gamma^4 * ‖b‖`;
   - `χ P_0 b` (`flatCutAgeForceTerm c χ b`): `≤ Gamma^4 * ‖b‖`;
   giving `cellL2Norm c (flatCutAgeExplicitPart c χ μ b (T0flat hc ν μ b)) ≤ 3 * Gamma^4 * ‖b‖`.
4. **Unconditional `s`-Leibniz integration-by-parts reduction on `cellMeasure c`**
   (`pdS_smul_cutoff`, `flatCutAgeExplicitPart_ibp_s_eq`):
   Combines `pdS (χ • φ) = pdS χ • φ + χ • pdS φ` with `dsFromS_sMul` and `periodize_of_mem` to
   reduce `∫ ⟨dsFromS Su, φ⟩ + ∫ ⟨u, pdS φ⟩ = 0` for `Su = flatCutAgeExplicitPart + S_lap` to the
   weak flat heat identity for the localized scaled-Laplacian term `S_lap = ν s χ Δ_{q,η} w`.
5. **Conditional assembly (`flatBodyAgeDerivLocal_of`)**:
   Combines (1)–(4) with the localized periodic heat maximal-regularity leaf
   `FlatBodyCutLaplacianLocal` on `[σ, H1]` (via `IsLargerCutoff c χ χ1` and `B0423.freeStress11`)
   to establish `FlatBodyAgeDerivLocal`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_2Aux N05_4Aux

namespace N05_2_2Aux

/-! ### 1. Absolute continuity `cellMeasure c ≪ measureH c` and representative reduction -/

theorem ae_cell_cellMeasure (c : ℝ) : ∀ᵐ p ∂(cellMeasure c), p ∈ cell c :=
  ae_restrict_mem (measurableSet_cell c)

theorem cellMeasure_eq_measureH_withDensity (c : ℝ) :
    (measureH c).withDensity (fun p => ENNReal.ofReal (p.1 ^ (3 / 2 : ℝ))) = cellMeasure c := by
  have hm : Measurable fun p : Profile => ENNReal.ofReal (p.1 ^ (3 / 2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const (3 / 2 : ℝ))
  rw [measureH, ← withDensity_mul _ measurable_weightH hm]
  conv_rhs => rw [← withDensity_one (μ := cellMeasure c)]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_cell_cellMeasure c] with p hp
  have hs : 0 < p.1 := hp.1
  rw [Pi.mul_apply, Pi.one_apply, weightH, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
    ← Real.rpow_add hs]
  norm_num

theorem cellMeasure_ac_measureH (c : ℝ) : cellMeasure c ≪ measureH c := by
  rw [← cellMeasure_eq_measureH_withDensity c]
  exact withDensity_absolutelyContinuous _ _

theorem u_ae_eq_flatStressCutRep_cellMeasure {c : ℝ} (hc : 0 < c) (χ : Profile → ℝ)
    (hm : Measurable χ) {B : ℝ} (hB : ∀ p, |χ p| ≤ B) (W : HSpace c MeridC)
    {u : Profile → MeridC}
    (hae : ((mulChi (measureH c) χ hm hB W : HSpace c MeridC) : Profile → MeridC)
      =ᵐ[measureH c] u) :
    u =ᵐ[cellMeasure c] flatStressCutRep c χ W :=
  (cellMeasure_ac_measureH c).ae_le (hae.symm.trans (flatStressCutRep_ae_eq hc χ hm hB W))

/-! ### 2. Age-multiplier `sMul` (`s • ·`) and `dsFromS` inversion on `[σ, H1]` -/

/-- Pointwise multiplication by the age coordinate `s = p.1`: `sMul f p = p.1 • f p`. -/
def sMul (f : Profile → MeridC) (p : Profile) : MeridC :=
  (p.1 : ℝ) • f p

theorem qPeriodic_sMul {c : ℝ} {f : Profile → MeridC} (hf : QPeriodic c f) :
    QPeriodic c (sMul f) := by
  intro p
  simp only [sMul, hf p]

theorem sMul_support {σ H1 L1 : ℝ} {f : Profile → MeridC}
    (hsupp : ∀ p : Profile, f p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (p : Profile) (hp : sMul f p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  refine hsupp p fun h0 => hp ?_
  simp [sMul, h0]

theorem dsFromS_sMul {σ H1 L1 : ℝ} (hσ : 0 < σ) {f : Profile → MeridC}
    (hsupp : ∀ p : Profile, f p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    dsFromS (sMul f) = f := by
  funext p
  by_cases h0 : f p = 0
  · simp [dsFromS, sMul, h0]
  · have hs : 0 < p.1 := lt_of_lt_of_le hσ (hsupp p h0).1
    rw [dsFromS, sMul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem sMul_dsFromS {σ H1 L1 : ℝ} (hσ : 0 < σ) {f : Profile → MeridC}
    (hsupp : ∀ p : Profile, f p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    sMul (dsFromS f) = f := by
  funext p
  by_cases h0 : f p = 0
  · simp [sMul, dsFromS, h0]
  · have hs : 0 < p.1 := lt_of_lt_of_le hσ (hsupp p h0).1
    rw [sMul, dsFromS, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

theorem memLp_sMul_flat {c σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH : σ ≤ H1) {f : Profile → MeridC}
    (hsupp : ∀ p : Profile, f p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hf : MemLp f 2 (cellMeasure c)) :
    MemLp (sMul f) 2 (cellMeasure c) := by
  have hm : AEStronglyMeasurable (sMul f) (cellMeasure c) :=
    measurable_fst.aestronglyMeasurable.smul hf.1
  have hH1 : 0 < H1 := lt_of_lt_of_le hσ hσH
  refine hf.of_le_mul (c := H1) hm (Eventually.of_forall fun p => ?_)
  by_cases h0 : f p = 0
  · simp [sMul, h0]
  · have hpσ : σ ≤ p.1 := (hsupp p h0).1
    have hpH : p.1 ≤ H1 := (hsupp p h0).2.1
    have hp0 : 0 < p.1 := lt_of_lt_of_le hσ hpσ
    rw [sMul, norm_smul, Real.norm_of_nonneg hp0.le]
    exact mul_le_mul_of_nonneg_right hpH (norm_nonneg _)

theorem norm_sMul_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hγ : 0 < γs)
    (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (f : Profile → MeridC) {p : Profile}
    (hpσ : σ ≤ p.1) (hpH : p.1 ≤ H1) :
    ‖sMul f p‖ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * ‖f p‖ := by
  have hp0 : 0 < p.1 := lt_of_lt_of_le hσ hpσ
  have hG : H1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  rw [sMul, norm_smul, Real.norm_of_nonneg hp0.le]
  exact mul_le_mul_of_nonneg_right (hpH.trans hG) (norm_nonneg _)

theorem cellL2Norm_sMul_flat_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) {f : Profile → MeridC}
    (hsupp : ∀ p : Profile, f p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hf : MemLp f 2 (cellMeasure c)) :
    cellL2Norm c (sMul f) ≤ Gamma ν c σ H1 L1 M γs χ χ1 * cellL2Norm c f := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM
  have hG0 : 0 ≤ G := by linarith
  have hsM : MemLp (sMul f) 2 (cellMeasure c) := memLp_sMul_flat hσ hσH hsupp hf
  have hpt : ∀ p : Profile, ‖sMul f p‖ ≤ G * ‖f p‖ := fun p => by
    by_cases h0 : f p = 0
    · simp [sMul, h0]
    · exact norm_sMul_le_gamma χ χ1 hν hc hσ hγ hL1 hM f (hsupp p h0).1 (hsupp p h0).2.1
  have hint : ∫ p, ‖sMul f p‖ ^ 2 ∂(cellMeasure c) ≤ (G * cellL2Norm c f) ^ 2 := by
    have h1 : ∫ p, ‖sMul f p‖ ^ 2 ∂(cellMeasure c) ≤
        ∫ p, G ^ 2 * ‖f p‖ ^ 2 ∂(cellMeasure c) := by
      refine integral_mono hsM.norm.integrable_sq (hf.norm.integrable_sq.const_mul (G ^ 2))
        (fun p => ?_)
      calc ‖sMul f p‖ ^ 2 ≤ (G * ‖f p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hpt p) 2
        _ = G ^ 2 * ‖f p‖ ^ 2 := by ring
    have hA : 0 ≤ ∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
    have hsq_sqrt : ((∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)) ^ 2 =
        ∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c) := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA]
    calc ∫ p, ‖sMul f p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∫ p, G ^ 2 * ‖f p‖ ^ 2 ∂(cellMeasure c) := h1
      _ = G ^ 2 * ∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c) := integral_const_mul _ _
      _ = G ^ 2 * (cellL2Norm c f) ^ 2 := by rw [cellL2Norm, hsq_sqrt]
      _ = (G * cellL2Norm c f) ^ 2 := by ring
  unfold cellL2Norm
  calc (∫ p, ‖sMul f p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ ((G * cellL2Norm c f) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint (by norm_num)
    _ = G * cellL2Norm c f := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (mul_nonneg hG0 (cellL2Norm_nonneg c f))]

/-! ### 3. Cutoff derivative `pdS χ` bounds on `cellMeasure c` -/

theorem fderiv_periodic_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) : QPeriodic c (fderiv ℝ χ) := by
  intro p
  let τ : Profile → Profile := fun q => (q.1, q.2.1 + c, q.2.2)
  have hτ_eq : χ ∘ τ = χ := funext fun q => hχ.periodic q
  have hτ : HasFDerivAt τ (ContinuousLinearMap.id ℝ Profile) p := by
    have h1 : HasFDerivAt (fun q : Profile => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
      hasFDerivAt_fst
    have h21 : HasFDerivAt (fun q : Profile => q.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      hasFDerivAt_fst.comp p hasFDerivAt_snd
    have h22 : HasFDerivAt (fun q : Profile => q.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      hasFDerivAt_snd.comp p hasFDerivAt_snd
    have h21c : HasFDerivAt (fun q : Profile => q.2.1 + c)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p := by
      simpa using h21.add_const c
    exact h1.prodMk (h21c.prodMk h22)
  have hd : DifferentiableAt ℝ χ (τ p) :=
    (hχ.smooth.differentiable (by decide)).differentiableAt
  have hcomp : HasFDerivAt (χ ∘ τ) (fderiv ℝ χ (τ p)) p := by
    simpa using hd.hasFDerivAt.comp p hτ
  rw [hτ_eq] at hcomp
  exact hcomp.fderiv.symm

theorem fderiv_support_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) (hp : fderiv ℝ χ p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  have hclosed : IsClosed {q : Profile | σ ≤ q.1 ∧ q.1 ≤ H1 ∧ |q.2.2| ≤ L1} := by
    refine (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter ?_)
    exact isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const
  have hsub : tsupport χ ⊆ {q : Profile | σ ≤ q.1 ∧ q.1 ≤ H1 ∧ |q.2.2| ≤ L1} :=
    closure_minimal (fun q hq => hχ.support q hq) hclosed
  exact hsub (support_fderiv_subset ℝ hp)

theorem norm_fderiv_le_cNorm8_of_nearCutoff {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    ‖fderiv ℝ χ p‖ ≤ cNorm8 χ := by
  have hcont : Continuous (fun q => ‖iteratedFDeriv ℝ 1 χ q‖) :=
    (hχ.smooth.continuous_iteratedFDeriv (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).norm
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hbdd : BddAbove (range fun q => ‖iteratedFDeriv ℝ 1 χ q‖) := by
    refine ⟨max C1 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_one]
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : fderiv ℝ χ q' = fderiv ℝ χ q :=
      periodic_reduceIoc_eq (fderiv ℝ χ) (fderiv_periodic_of_nearCutoff hχ) q.1 q.2.1 q.2.2
    rw [← hpeq]
    by_cases h0 : fderiv ℝ χ q' = 0
    · simp [h0]
    · obtain ⟨hs1, hs2, hη⟩ := fderiv_support_of_nearCutoff hχ q' h0
      have hq' : q' ∈ K := ⟨⟨hs1, hs2⟩, Ioc_subset_Icc_self (reduceIoc_mem hc q.2.1), abs_le.1 hη⟩
      have hle : ‖fderiv ℝ χ q'‖ ≤ C1 := by simpa using hC1 q' hq'
      exact hle.trans (le_max_left C1 0)
  rw [← norm_iteratedFDeriv_one]
  calc ‖iteratedFDeriv ℝ 1 χ p‖
      ≤ ⨆ q, ‖iteratedFDeriv ℝ 1 χ q‖ := le_ciSup hbdd p
    _ ≤ ∑ k ∈ Finset.range 9, ⨆ q, ‖iteratedFDeriv ℝ k χ q‖ :=
        Finset.single_le_sum (fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ = cNorm8 χ := rfl

theorem isNearCutoff_pdS {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) :
    IsNearCutoff c σ H1 L1 (pdS χ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((hχ.smooth.fderiv_right (by decide)).clm_apply contDiff_const)
  · intro p
    change fderiv ℝ χ (p.1, p.2.1 + c, p.2.2) (1, 0, 0) = fderiv ℝ χ p (1, 0, 0)
    rw [fderiv_periodic_of_nearCutoff hχ p]
  · intro p hp
    refine fderiv_support_of_nearCutoff hχ p ?_
    intro h0
    apply hp
    change fderiv ℝ χ p (1, 0, 0) = 0
    simp [h0]

theorem abs_pdS_le_cNorm8 {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    |pdS χ p| ≤ cNorm8 χ := by
  have hv : ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_mk]
  calc |pdS χ p| = ‖fderiv ℝ χ p (1, 0, 0)‖ := Real.norm_eq_abs _
    _ ≤ ‖fderiv ℝ χ p‖ * ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ cNorm8 χ * 1 :=
        mul_le_mul (norm_fderiv_le_cNorm8_of_nearCutoff hc hχ p) hv (norm_nonneg _)
          (cNorm8_nonneg χ)
    _ = cNorm8 χ := mul_one _

theorem lintegral_flatStressCutRep_pdS_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c (pdS χ) W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  have hmdχ : Measurable (pdS χ) := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c (pdS χ) W
  have hu : Measurable u := measurable_flatStressCutRep c hmdχ W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono (flatStressCutRep_enorm_sq_le hσ hσH hdχ W)
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ)))
      _ = ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _ measurable_weightH
            (hu.enorm.pow_const (2 : ℝ))]
          rfl
  have hB : ∀ p, |pdS χ p| ≤ cNorm8 χ := abs_pdS_le_cNorm8 hc hχ
  let U := mulChi (measureH c) (pdS χ) hmdχ hB W
  have hae : (U : Profile → MeridC) =ᵐ[measureH c] u :=
    flatStressCutRep_ae_eq hc (pdS χ) hmdχ hB W
  have hU_norm : ‖U‖ ≤ cNorm8 χ * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) (pdS χ) hmdχ hB (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) (pdS χ) hmdχ hB (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB p) (norm_nonneg _)
  have hstep2 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤
      ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) := by
    have hcongr : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ∫⁻ p, ‖(U : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    have hLp : eLpNorm (U : Profile → MeridC) 2 (measureH c) = ENNReal.ofReal ‖U‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U)]
    have hlint : ∫⁻ p, ‖(U : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ENNReal.ofReal (‖U‖ ^ 2) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := measureH c)
        (f := (U : Profile → MeridC)) two_ne_zero ENNReal.ofNat_ne_top
      rw [hLp, ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg U) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two] at hpow
      exact hpow
    rw [hcongr, hlint]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg U) hU_norm 2)
  calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal ((1 + H1) ^ 2) * ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

theorem cellL2Norm_flatStressCutRep_pdS_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c (pdS χ) W) ≤ (1 + H1) * cNorm8 χ * ‖W‖ := by
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  have hmdχ : Measurable (pdS χ) := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c (pdS χ) W
  have hmem := memLp_flatStressCutRep hc hσ hσH hdχ hmdχ W
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hC0 : 0 ≤ (1 + H1) * cNorm8 χ * ‖W‖ :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg W)
  have hint_le : ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * ‖W‖) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_flatStressCutRep_pdS_sq_le hc hσ hσH hχ W
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * ‖W‖ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hC0]

theorem cellL2Norm_flatStressCutRep_pdS_T0flat_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (b : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c (pdS χ) (T0flat hc ν μ b)) ≤
      Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖b‖ := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ G := by linarith
  have h1H1_G : 1 + H1 ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have : 0 < H1 := lt_of_lt_of_le hσ hσH
    linarith [cNorm8_nonneg χ1]
  have hL2 := cellL2Norm_flatStressCutRep_pdS_le_mul hc hσ hσH hχ (T0flat hc ν μ b)
  have hT0 := norm_T0flat_apply_le χ χ1 hν hc hσ hσH hL1 hγ hμM hμγ b
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  calc cellL2Norm c (flatStressCutRep c (pdS χ) (T0flat hc ν μ b))
      ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ b‖ := hL2
    _ ≤ (1 + H1) * cNorm8 χ * (G * ‖b‖) :=
        mul_le_mul_of_nonneg_left hT0 (mul_nonneg (by linarith) (cNorm8_nonneg χ))
    _ = (1 + H1) * cNorm8 χ * G * ‖b‖ := by ring
    _ ≤ G * G * G * ‖b‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg b)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hG0
    _ = G ^ 3 * ‖b‖ := by ring

/-! ### 4. Triangle inequality and scalar multiplication for `cellL2Norm` -/

theorem cellL2Norm_const_smul_le (c : ℝ) (a : ℂ) (f : Profile → MeridC) :
    cellL2Norm c (fun p => a • f p) ≤ ‖a‖ * cellL2Norm c f := by
  unfold cellL2Norm
  have heq : (fun p : Profile => ‖a • f p‖ ^ 2) = fun p => ‖a‖ ^ 2 * ‖f p‖ ^ 2 := by
    funext p
    rw [norm_smul, mul_pow]
  rw [heq, integral_const_mul,
    Real.mul_rpow (sq_nonneg ‖a‖) (integral_nonneg fun _ => sq_nonneg _),
    ← Real.sqrt_eq_rpow (‖a‖ ^ 2), Real.sqrt_sq (norm_nonneg a)]

theorem cellL2Norm_add_le {c : ℝ} {f g : Profile → MeridC}
    (hf : MemLp f 2 (cellMeasure c)) (hg : MemLp g 2 (cellMeasure c)) :
    cellL2Norm c (fun p => f p + g p) ≤ cellL2Norm c f + cellL2Norm c g := by
  have hfg : MemLp (f + g) 2 (cellMeasure c) := hf.add hg
  have h_eq : ∀ (h : Profile → MeridC) (hh : MemLp h 2 (cellMeasure c)),
      cellL2Norm c h = ‖hh.toLp h‖ := fun h hh => by
    have hint : Integrable (fun p => ‖h p‖ ^ 2) (cellMeasure c) :=
      hh.integrable_norm_pow two_ne_zero
    have hLp : eLpNorm ((hh.toLp h : Lp MeridC 2 (cellMeasure c)) : Profile → MeridC)
        2 (cellMeasure c) = ENNReal.ofReal ‖hh.toLp h‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (hh.toLp h))]
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := cellMeasure c)
      (f := h) two_ne_zero ENNReal.ofNat_ne_top
    rw [eLpNorm_congr_ae hh.coeFn_toLp.symm, hLp, ENNReal.toReal_ofNat] at heq
    have hofReal : ∫⁻ p, ‖h p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) =
        ENNReal.ofReal (∫ p, ‖h p‖ ^ 2 ∂(cellMeasure c)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun p => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    have hpow : (∫⁻ p, ‖h p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)) ^ (1 / (2 : ℝ)) =
        ENNReal.ofReal (cellL2Norm c h) := by
      rw [hofReal, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => sq_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rfl
    rw [hpow] at heq
    exact ((ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (cellL2Norm_nonneg c h)).1 heq).symm
  rw [show (fun p => f p + g p) = f + g from rfl, h_eq (f + g) hfg, h_eq f hf, h_eq g hg,
    MemLp.toLp_add]
  exact norm_add_le _ _

/-! ### 5. Explicit constituent terms of `Su = (s ∂_s χ) w - μ χ w + χ P_0 b + S_lap` -/

/-- The cutoff-derivative term `(s ∂_s χ) w = sMul (flatStressCutRep c (pdS χ) W)`. -/
def flatCutAgeCutoffTerm (c : ℝ) (χ : Profile → ℝ) (W : HSpace c MeridC) : Profile → MeridC :=
  sMul (flatStressCutRep c (pdS χ) W)

/-- The drift term `-μ χ w = (-μ) • flatStressCutRep c χ W`. -/
def flatCutAgeDriftTerm (c : ℝ) (χ : Profile → ℝ) (μ : ℂ) (W : HSpace c MeridC) (p : Profile) :
    MeridC :=
  (-μ) • flatStressCutRep c χ W p

/-- The projected body-force term `χ P_0 b = flatStressCutRep c χ (PepsC 0 c b)`. -/
def flatCutAgeForceTerm (c : ℝ) (χ : Profile → ℝ) (b : HSpace c MeridC) : Profile → MeridC :=
  flatStressCutRep c χ (PepsC 0 c b)

/-- The combined explicit (non-Laplacian) part of `Su = S(χ w)`:
`flatCutAgeExplicitPart = (s ∂_s χ) w - μ χ w + χ P_0 b`. -/
def flatCutAgeExplicitPart (c : ℝ) (χ : Profile → ℝ) (μ : ℂ) (b W : HSpace c MeridC)
    (p : Profile) : MeridC :=
  flatCutAgeCutoffTerm c χ W p + flatCutAgeDriftTerm c χ μ W p + flatCutAgeForceTerm c χ b p

theorem qPeriodic_flatCutAgeExplicitPart {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (μ : ℂ) (b W : HSpace c MeridC) :
    QPeriodic c (flatCutAgeExplicitPart c χ μ b W) := by
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  have hp1 : QPeriodic c (flatCutAgeCutoffTerm c χ W) :=
    qPeriodic_sMul (flatStressCutRep_periodic hc hdχ W)
  have hp2 : QPeriodic c (flatCutAgeDriftTerm c χ μ W) := fun p => by
    simp only [flatCutAgeDriftTerm, flatStressCutRep_periodic hc hχ W p]
  have hp3 : QPeriodic c (flatCutAgeForceTerm c χ b) :=
    flatStressCutRep_periodic hc hχ (PepsC 0 c b)
  intro p
  simp only [flatCutAgeExplicitPart, hp1 p, hp2 p, hp3 p]

theorem flatCutAgeExplicitPart_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (μ : ℂ) (b W : HSpace c MeridC) (p : Profile)
    (hp : flatCutAgeExplicitPart c χ μ b W p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  by_cases h1 : flatCutAgeCutoffTerm c χ W p = 0
  · by_cases h2 : flatCutAgeDriftTerm c χ μ W p = 0
    · refine flatStressCutRep_support hχ (PepsC 0 c b) p fun h3 => hp ?_
      simp [flatCutAgeExplicitPart, flatCutAgeForceTerm, h1, h2, h3]
    · refine flatStressCutRep_support hχ W p fun hW => h2 ?_
      simp [flatCutAgeDriftTerm, hW]
  · exact sMul_support (flatStressCutRep_support hdχ W) p h1

theorem memLp_flatCutAgeExplicitPart {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (μ : ℂ) (b W : HSpace c MeridC) :
    MemLp (flatCutAgeExplicitPart c χ μ b W) 2 (cellMeasure c) := by
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  have hmdχ : Measurable (pdS χ) := hdχ.smooth.continuous.measurable
  have hm1 : MemLp (flatCutAgeCutoffTerm c χ W) 2 (cellMeasure c) :=
    memLp_sMul_flat hσ hσH (flatStressCutRep_support hdχ W)
      (memLp_flatStressCutRep hc hσ hσH hdχ hmdχ W)
  have hm2 : MemLp (flatCutAgeDriftTerm c χ μ W) 2 (cellMeasure c) :=
    (memLp_flatStressCutRep hc hσ hσH hχ hm W).const_smul (-μ)
  have hm3 : MemLp (flatCutAgeForceTerm c χ b) 2 (cellMeasure c) :=
    memLp_flatStressCutRep hc hσ hσH hχ hm (PepsC 0 c b)
  exact (hm1.add hm2).add hm3

theorem cellL2Norm_flatCutAgeExplicitPart_T0flat_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (b : HSpace c MeridC) :
    cellL2Norm c (flatCutAgeExplicitPart c χ μ b (T0flat hc ν μ b)) ≤
      3 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 4 * ‖b‖ := by
  let W := T0flat hc ν μ b
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ G := by linarith
  have hM_G : M ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have : 0 < H1 := lt_of_lt_of_le hσ hσH
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have : 0 < H1 := lt_of_lt_of_le hσ hσH
    linarith [cNorm8_nonneg χ1]
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  have hmdχ : Measurable (pdS χ) := hdχ.smooth.continuous.measurable
  -- 1. Cutoff derivative term `(s ∂_s χ) W`
  have hm_pdS : MemLp (flatStressCutRep c (pdS χ) W) 2 (cellMeasure c) :=
    memLp_flatStressCutRep hc hσ hσH hdχ hmdχ W
  have hm1 : MemLp (flatCutAgeCutoffTerm c χ W) 2 (cellMeasure c) :=
    memLp_sMul_flat hσ hσH (flatStressCutRep_support hdχ W) hm_pdS
  have hbd1 : cellL2Norm c (flatCutAgeCutoffTerm c χ W) ≤ G ^ 4 * ‖b‖ := by
    calc cellL2Norm c (flatCutAgeCutoffTerm c χ W)
        ≤ G * cellL2Norm c (flatStressCutRep c (pdS χ) W) :=
          cellL2Norm_sMul_flat_le χ χ1 hν hc hσ hσH hL1 hγ hM0
            (flatStressCutRep_support hdχ W) hm_pdS
      _ ≤ G * (G ^ 3 * ‖b‖) :=
          mul_le_mul_of_nonneg_left
            (cellL2Norm_flatStressCutRep_pdS_T0flat_le χ χ1 hν hc hσ hσH hL1 hγ hχ hμM hμγ b) hG0
      _ = G ^ 4 * ‖b‖ := by ring
  -- 2. Drift term `-μ χ W`
  have hm2 : MemLp (flatCutAgeDriftTerm c χ μ W) 2 (cellMeasure c) :=
    (memLp_flatStressCutRep hc hσ hσH hχ hm W).const_smul (-μ)
  have hμ_G : ‖-μ‖ ≤ G := by
    rw [norm_neg]
    exact hμM.trans hM_G
  have hbd2 : cellL2Norm c (flatCutAgeDriftTerm c χ μ W) ≤ G ^ 4 * ‖b‖ := by
    calc cellL2Norm c (flatCutAgeDriftTerm c χ μ W)
        ≤ ‖-μ‖ * cellL2Norm c (flatStressCutRep c χ W) :=
          cellL2Norm_const_smul_le c (-μ) (flatStressCutRep c χ W)
      _ ≤ G * (G ^ 3 * ‖b‖) :=
          mul_le_mul hμ_G
            (cellL2Norm_flatStressCutRep_T0flat_le χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ b)
            (cellL2Norm_nonneg c _) hG0
      _ = G ^ 4 * ‖b‖ := by ring
  -- 3. Force term `χ (PepsC 0 c b)`
  have hm3 : MemLp (flatCutAgeForceTerm c χ b) 2 (cellMeasure c) :=
    memLp_flatStressCutRep hc hσ hσH hχ hm (PepsC 0 c b)
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hG24 : G ^ 2 ≤ G ^ 4 := pow_le_pow_right₀ hG1 (by omega)
  have hbd3 : cellL2Norm c (flatCutAgeForceTerm c χ b) ≤ G ^ 4 * ‖b‖ := by
    calc cellL2Norm c (flatCutAgeForceTerm c χ b)
        ≤ (1 + H1) * cNorm8 χ * ‖PepsC 0 c b‖ :=
          cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm (PepsC 0 c b)
      _ ≤ (1 + H1) * cNorm8 χ * ‖b‖ :=
          mul_le_mul_of_nonneg_left (norm_PepsC0_apply_le c b)
            (mul_nonneg (by linarith) (cNorm8_nonneg χ))
      _ ≤ G * G * ‖b‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg b)
          exact mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0
      _ = G ^ 2 * ‖b‖ := by ring
      _ ≤ G ^ 4 * ‖b‖ := mul_le_mul_of_nonneg_right hG24 (norm_nonneg b)
  -- Combine via triangle inequality
  have htri1 : cellL2Norm c (flatCutAgeExplicitPart c χ μ b W) ≤
      cellL2Norm c (fun p => flatCutAgeCutoffTerm c χ W p + flatCutAgeDriftTerm c χ μ W p) +
        cellL2Norm c (flatCutAgeForceTerm c χ b) :=
    cellL2Norm_add_le (hm1.add hm2) hm3
  have htri2 := cellL2Norm_add_le hm1 hm2
  linarith

/-! ### 6. Unconditional `s`-Leibniz rule and integration-by-parts reduction on `cellMeasure c` -/

theorem pdS_smul_cutoff {χ : Profile → ℝ} {φ : Profile → MeridC}
    (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (p : Profile) :
    pdS (fun q => χ q • φ q) p = pdS χ p • φ p + χ p • pdS φ p := by
  have hdχ : DifferentiableAt ℝ χ p := (hχ.differentiable (by decide)).differentiableAt
  have hdφ : DifferentiableAt ℝ φ p := (hφ.differentiable (by decide)).differentiableAt
  have h := (hdχ.hasFDerivAt.smul hdφ.hasFDerivAt).fderiv
  have h_apply := congrArg (fun L : Profile →L[ℝ] MeridC => L (1, 0, 0)) h
  dsimp only [pdS]
  rw [show (fun q => χ q • φ q) = χ • φ from rfl, h_apply,
    add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, add_comm]

theorem fderiv_periodic_of_isMeridTest {c : ℝ} {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) : QPeriodic c (fderiv ℝ φ) := by
  intro p
  let τ : Profile → Profile := fun q => (q.1, q.2.1 + c, q.2.2)
  have hτ_eq : φ ∘ τ = φ := funext fun q => hφ.periodic q
  have hτ : HasFDerivAt τ (ContinuousLinearMap.id ℝ Profile) p := by
    have h1 : HasFDerivAt (fun q : Profile => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
      hasFDerivAt_fst
    have h21 : HasFDerivAt (fun q : Profile => q.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      hasFDerivAt_fst.comp p hasFDerivAt_snd
    have h22 : HasFDerivAt (fun q : Profile => q.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      hasFDerivAt_snd.comp p hasFDerivAt_snd
    have h21c : HasFDerivAt (fun q : Profile => q.2.1 + c)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p := by
      simpa using h21.add_const c
    exact h1.prodMk (h21c.prodMk h22)
  have hd : DifferentiableAt ℝ φ (τ p) :=
    (hφ.smooth.differentiable (by decide)).differentiableAt
  have hcomp : HasFDerivAt (φ ∘ τ) (fderiv ℝ φ (τ p)) p := by
    simpa using hd.hasFDerivAt.comp p hτ
  rw [hτ_eq] at hcomp
  exact hcomp.fderiv.symm

theorem fderiv_support_of_isMeridTest {c : ℝ} {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) :
    ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, fderiv ℝ φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  obtain ⟨s0, s1, L, hs0, hsupp⟩ := hφ.band
  refine ⟨s0, s1, L, hs0, fun p hp => ?_⟩
  have hclosed : IsClosed {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L} := by
    refine (isClosed_Icc.preimage continuous_fst).inter ?_
    exact isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const
  have hsub : tsupport φ ⊆ {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L} :=
    closure_minimal (fun q hq => hsupp q hq) hclosed
  exact hsub (support_fderiv_subset ℝ hp)

theorem isMeridTest_pdS {c : ℝ} {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) : IsMeridTest c (pdS φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hφ.smooth.fderiv_right (by decide)).clm_apply contDiff_const
  · intro p
    change fderiv ℝ φ (p.1, p.2.1 + c, p.2.2) (1, 0, 0) = fderiv ℝ φ p (1, 0, 0)
    rw [fderiv_periodic_of_isMeridTest hφ p]
  · obtain ⟨s0, s1, L, hs0, hsupp⟩ := fderiv_support_of_isMeridTest hφ
    refine ⟨s0, s1, L, hs0, fun p hp => hsupp p fun h0 => hp ?_⟩
    change fderiv ℝ φ p (1, 0, 0) = 0
    simp [h0]

theorem memLp_of_isMeridTest_cellMeasure {c : ℝ} (_hc : 0 < c) {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) : MemLp φ 2 (cellMeasure c) := by
  obtain ⟨s0, s1, L, hs0, hsupp⟩ := hφ.band
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKm : MeasurableSet K :=
    measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hKfin : volume K < ⊤ := hK.measure_lt_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.smooth.continuous.continuousOn
  let M : ℝ := max C 0
  have hM0 : 0 ≤ M := le_max_right C 0
  refine ⟨hφ.smooth.continuous.measurable.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hbound : ∀ᵐ p ∂(cellMeasure c), ‖φ p‖ₑ ^ (2 : ℝ) ≤
      K.indicator (fun _ => ENNReal.ofReal (M ^ 2)) p := by
    filter_upwards [ae_cell_cellMeasure c] with p hpcell
    by_cases hp0 : φ p = 0
    · simp [hp0]
    · obtain ⟨hs, hη⟩ := hsupp p hp0
      have hpK : p ∈ K := ⟨hs, Ioc_subset_Icc_self hpcell.2.1, abs_le.1 hη⟩
      rw [indicator_of_mem hpK, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) ((hC p hpK).trans (le_max_left C 0)) 2)
  have hle : ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (M ^ 2) * volume K := by
    calc ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal (M ^ 2)) p ∂(cellMeasure c) :=
          lintegral_mono_ae hbound
      _ ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal (M ^ 2)) p ∂volume :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal (M ^ 2) * volume K := lintegral_indicator_const hKm _
  have hlt : ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) < ⊤ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

theorem integrable_inner_cellMeasure {c : ℝ} {f g : Profile → MeridC}
    (hf : MemLp f 2 (cellMeasure c)) (hg : MemLp g 2 (cellMeasure c)) :
    Integrable (fun p => inner ℂ (f p) (g p)) (cellMeasure c) := by
  have hfg : Integrable (fun p => ‖f p‖ * ‖g p‖) (cellMeasure c) :=
    hf.norm.integrable_mul hg.norm
  have hm : AEStronglyMeasurable (fun p => inner ℂ (f p) (g p)) (cellMeasure c) :=
    hf.1.inner hg.1
  refine hfg.mono' hm (Eventually.of_forall fun p => norm_inner_le_norm (f p) (g p))

/-- Unconditional `s`-Leibniz reduction on `cellMeasure c`: for any `u` with
`mulChi (measureH c) χ hm hB W =ᵐ[measureH c] u` and any `φ : Profile → MeridC` (`IsMeridTest c φ`),
the sum `∫ ⟨dsFromS (flatCutAgeExplicitPart c χ μ b W), φ⟩ + ∫ ⟨u, pdS φ⟩` equals
`∫ (⟨W, pdS (χ • φ)⟩ + ⟨(-μ / s) • W + (1 / s) • PepsC 0 c b, χ • φ⟩) ∂(cellMeasure c)`. -/
theorem flatCutAgeExplicitPart_ibp_s_eq {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {B : ℝ} (hB : ∀ p, |χ p| ≤ B) (μ : ℂ) (b W : HSpace c MeridC)
    {u : Profile → MeridC}
    (hae : ((mulChi (measureH c) χ hm hB W : HSpace c MeridC) : Profile → MeridC)
      =ᵐ[measureH c] u)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (dsFromS (flatCutAgeExplicitPart c χ μ b W) p) (φ p) ∂(cellMeasure c) +
        ∫ p, inner ℂ (u p) (pdS φ p) ∂(cellMeasure c) =
      ∫ p, (inner ℂ ((W : Profile → MeridC) p) (pdS (fun q => χ q • φ q) p) +
        inner ℂ (dsFromS (fun q => flatCutAgeDriftTerm c χ μ W q + flatCutAgeForceTerm c χ b q) p)
          (φ p)) ∂(cellMeasure c) := by
  let u₀ := flatStressCutRep c χ W
  have hu_ae : u =ᵐ[cellMeasure c] u₀ := u_ae_eq_flatStressCutRep_cellMeasure hc χ hm hB W hae
  have hu_int_eq : ∫ p, inner ℂ (u p) (pdS φ p) ∂(cellMeasure c) =
      ∫ p, inner ℂ (u₀ p) (pdS φ p) ∂(cellMeasure c) := by
    refine integral_congr_ae ?_
    filter_upwards [hu_ae] with p hp
    rw [hp]
  rw [hu_int_eq]
  have hdχ : IsNearCutoff c σ H1 L1 (pdS χ) := isNearCutoff_pdS hχ
  have hmdχ : Measurable (pdS χ) := hdχ.smooth.continuous.measurable
  have hm_exp : MemLp (dsFromS (flatCutAgeExplicitPart c χ μ b W)) 2 (cellMeasure c) :=
    memLp_dsFromS_flat hσ (flatCutAgeExplicitPart_support hχ μ b W)
      (memLp_flatCutAgeExplicitPart hc hσ hσH hχ hm μ b W)
  have hm_u₀ : MemLp u₀ 2 (cellMeasure c) := memLp_flatStressCutRep hc hσ hσH hχ hm W
  have hm_φ : MemLp φ 2 (cellMeasure c) := memLp_of_isMeridTest_cellMeasure hc hφ
  have hm_pdφ : MemLp (pdS φ) 2 (cellMeasure c) :=
    memLp_of_isMeridTest_cellMeasure hc (isMeridTest_pdS hφ)
  have hInt1 : Integrable (fun p =>
      inner ℂ (dsFromS (flatCutAgeExplicitPart c χ μ b W) p) (φ p)) (cellMeasure c) :=
    integrable_inner_cellMeasure hm_exp hm_φ
  have hInt2 : Integrable (fun p => inner ℂ (u₀ p) (pdS φ p)) (cellMeasure c) :=
    integrable_inner_cellMeasure hm_u₀ hm_pdφ
  rw [← integral_add hInt1 hInt2]
  refine integral_congr_ae ?_
  filter_upwards [ae_cell_cellMeasure c] with p hpcell
  have hds_cut : dsFromS (flatCutAgeCutoffTerm c χ W) p =
      pdS χ p • (W : Profile → MeridC) p := by
    have h1 := congrFun (dsFromS_sMul hσ (flatStressCutRep_support hdχ W)) p
    rw [flatCutAgeCutoffTerm, h1, flatStressCutRep, periodize_of_mem hc _ hpcell]
  have hu₀_eq : u₀ p = χ p • (W : Profile → MeridC) p := by
    dsimp only [u₀, flatStressCutRep]
    rw [periodize_of_mem hc _ hpcell]
  have hds_add : dsFromS (flatCutAgeExplicitPart c χ μ b W) p =
      dsFromS (flatCutAgeCutoffTerm c χ W) p +
        dsFromS (fun q => flatCutAgeDriftTerm c χ μ W q + flatCutAgeForceTerm c χ b q) p := by
    simp only [dsFromS, flatCutAgeExplicitPart, add_assoc, smul_add]
  have hleib : pdS (fun q => χ q • φ q) p = pdS χ p • φ p + χ p • pdS φ p :=
    pdS_smul_cutoff hχ.smooth hφ.smooth p
  have hsmul_inner : ∀ (r : ℝ) (x y : MeridC), inner ℂ (r • x) y = inner ℂ x (r • y) := by
    intro r x y
    rw [← Complex.coe_smul r x, ← Complex.coe_smul r y,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [hds_add, hds_cut, hu₀_eq, hleib, inner_add_left, inner_add_right,
    hsmul_inner (pdS χ p), hsmul_inner (χ p)]
  ring

end N05_2_2Aux

open N05_2_2Aux

/-! ### 7. Localized periodic heat maximal-regularity leaf and conditional assembly -/

/-- **Leaf 1 (`PartII-a:N05/2/2/1`) — localized periodic heat maximal-regularity leaf for `PartII-a:N05/2/2`**
(source `the November 2 reference manuscript`,
lines 1794-1799): cutting off the flat heat equation
`(∂_s + μ / s - ν Δ_{q,η}) w = P_0 b / s` (`N05_2Aux.flat_body_energy_and_weak_all`) with the
larger cutoff `χ1` (`IsLargerCutoff c χ χ1`) on `[σ, H1]` and applying the Fourier heat estimate
(`B0423.freeStress11`) over periodically extended cells controls the localized scaled-Laplacian
term `S_lap = ν s χ Δ_{q,η} (T0flat hc ν μ b)` in `L²(cellMeasure c)` with
`cellL2Norm c S_lap ≤ C_L * Gamma^k_L * ‖b‖` and identifies `dsFromS S_lap = ν χ Δ_{q,η} w`
with `∂_s w + (μ / s) w - (P_0 b) / s` against every localized test `χ • φ`.
Composed by task `PartII-a:N05/2/2` via `flatBodyAgeDerivLocal_of`. -/
def FlatBodyCutLaplacianLocal : Prop :=
  ∃ (k_L : ℕ) (C_L : ℝ), 0 ≤ C_L ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      Measurable χ →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ b : HSpace c MeridC,
          ∃ S_lap : Profile → MeridC,
            QPeriodic c S_lap ∧
            (∀ p : Profile, S_lap p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) ∧
            MemLp S_lap 2 (cellMeasure c) ∧
            (∀ φ : Profile → MeridC, IsMeridTest c φ →
              ∫ p, inner ℂ (dsFromS S_lap p) (φ p) ∂(cellMeasure c) =
                -∫ p, (inner ℂ ((T0flat hc ν μ b : Profile → MeridC) p)
                    (pdS (fun q => χ q • φ q) p) +
                  inner ℂ (dsFromS (fun q =>
                      flatCutAgeDriftTerm c χ μ (T0flat hc ν μ b) q +
                        flatCutAgeForceTerm c χ b q) p) (φ p)) ∂(cellMeasure c)) ∧
            cellL2Norm c S_lap ≤ C_L * Gamma ν c σ H1 L1 M γs χ χ1 ^ k_L * ‖b‖

/-- **Conditional assembly of `FlatBodyAgeDerivLocal` (`PartII-a:N05/2/2`)** from
`FlatBodyCutLaplacianLocal`, the measure absolute continuity reduction `cellMeasure_ac_measureH`,
the explicit constituent `L²(cellMeasure c)` bound `cellL2Norm_flatCutAgeExplicitPart_T0flat_le`,
and the unconditional `s`-Leibniz integration-by-parts reduction `flatCutAgeExplicitPart_ibp_s_eq`. -/
theorem flatBodyAgeDerivLocal_of (hLap : FlatBodyCutLaplacianLocal) :
    UnforcedLeray.Short.PartIIa.FlatBodyAgeDerivLocal := by
  obtain ⟨k_L, C_L, hCL, hL⟩ := hLap
  set K := max 4 k_L
  refine ⟨K, C_L + 3, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ b u hae _hpu _hsu _hmu
  obtain ⟨S_lap, hp_lap, hs_lap, hm_lap, hibp_lap, hbd_lap⟩ :=
    hL ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm μ hμM hμγ b
  let W : HSpace c MeridC := T0flat hc ν μ b
  let S_exp : Profile → MeridC := flatCutAgeExplicitPart c χ μ b W
  let Su : Profile → MeridC := fun p => S_exp p + S_lap p
  have hp_exp : QPeriodic c S_exp := qPeriodic_flatCutAgeExplicitPart hc hχ μ b W
  have hs_exp : ∀ p : Profile, S_exp p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 :=
    flatCutAgeExplicitPart_support hχ μ b W
  have hm_exp : MemLp S_exp 2 (cellMeasure c) :=
    memLp_flatCutAgeExplicitPart hc hσ hσH hχ hm μ b W
  refine ⟨Su, ?_, ?_, hm_exp.add hm_lap, ?_, ?_⟩
  · intro p
    simp only [Su, hp_exp p, hp_lap p]
  · intro p hp
    by_cases h1 : S_exp p = 0
    · refine hs_lap p fun h2 => hp ?_
      simp [Su, h1, h2]
    · exact hs_exp p h1
  · intro φ hφ
    have hds_Su : dsFromS Su = fun p => dsFromS S_exp p + dsFromS S_lap p := by
      funext p
      simp only [dsFromS, Su, smul_add]
    have hm_ds_exp : MemLp (dsFromS S_exp) 2 (cellMeasure c) :=
      memLp_dsFromS_flat hσ hs_exp hm_exp
    have hm_ds_lap : MemLp (dsFromS S_lap) 2 (cellMeasure c) :=
      memLp_dsFromS_flat hσ hs_lap hm_lap
    have hm_φ : MemLp φ 2 (cellMeasure c) := memLp_of_isMeridTest_cellMeasure hc hφ
    have hInt_exp : Integrable (fun p => inner ℂ (dsFromS S_exp p) (φ p)) (cellMeasure c) :=
      integrable_inner_cellMeasure hm_ds_exp hm_φ
    have hInt_lap : Integrable (fun p => inner ℂ (dsFromS S_lap p) (φ p)) (cellMeasure c) :=
      integrable_inner_cellMeasure hm_ds_lap hm_φ
    have hsplit : ∫ p, inner ℂ (dsFromS Su p) (φ p) ∂(cellMeasure c) =
        (∫ p, inner ℂ (dsFromS S_exp p) (φ p) ∂(cellMeasure c)) +
          ∫ p, inner ℂ (dsFromS S_lap p) (φ p) ∂(cellMeasure c) := by
      rw [← integral_add hInt_exp hInt_lap]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [hds_Su, inner_add_left]
    have hleib := flatCutAgeExplicitPart_ibp_s_eq hc hσ hσH hχ hm hB μ b W hae hφ
    have hlap := hibp_lap φ hφ
    change (∫ p, inner ℂ (dsFromS S_exp p) (φ p) ∂(cellMeasure c)) +
        ∫ p, inner ℂ (u p) (pdS φ p) ∂(cellMeasure c) =
      ∫ p, (inner ℂ ((W : Profile → MeridC) p) (pdS (fun q => χ q • φ q) p) +
        inner ℂ (dsFromS (fun q => flatCutAgeDriftTerm c χ μ W q + flatCutAgeForceTerm c χ b q) p)
          (φ p)) ∂(cellMeasure c) at hleib
    change ∫ p, inner ℂ (dsFromS S_lap p) (φ p) ∂(cellMeasure c) =
      -∫ p, (inner ℂ ((W : Profile → MeridC) p) (pdS (fun q => χ q • φ q) p) +
        inner ℂ (dsFromS (fun q => flatCutAgeDriftTerm c χ μ W q + flatCutAgeForceTerm c χ b q) p)
          (φ p)) ∂(cellMeasure c) at hlap
    linear_combination hsplit + hlap + hleib
  · set G := Gamma ν c σ H1 L1 M γs χ χ1
    have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
    have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
    have hG4K : G ^ 4 ≤ G ^ K := pow_le_pow_right₀ hG1 (le_max_left 4 k_L)
    have hGLK : G ^ k_L ≤ G ^ K := pow_le_pow_right₀ hG1 (le_max_right 4 k_L)
    have hbd_exp : cellL2Norm c S_exp ≤ 3 * G ^ K * ‖b‖ := by
      calc cellL2Norm c S_exp
          ≤ 3 * G ^ 4 * ‖b‖ :=
            cellL2Norm_flatCutAgeExplicitPart_T0flat_le χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ b
        _ ≤ 3 * G ^ K * ‖b‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG4K (by norm_num))
              (norm_nonneg b)
    have hbd_lap' : cellL2Norm c S_lap ≤ C_L * G ^ K * ‖b‖ := by
      calc cellL2Norm c S_lap
          ≤ C_L * G ^ k_L * ‖b‖ := hbd_lap
        _ ≤ C_L * G ^ K * ‖b‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGLK hCL) (norm_nonneg b)
    have htri := cellL2Norm_add_le hm_exp hm_lap
    linarith

end UnforcedLeray.Short.PartIIa
