import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyFirstOrderLocal.GradBound

/-!
# Sub-file for `PartII-a:N05/4/1`: spatial `(q, η)` 1/2-Hölder `L²(cellMeasure c)` translation bound for `χ S_0 F`

Source of record: `the November 2 reference manuscript`,
lines 1757–1758, 1785–1788 (`near:local-smoothing`, flat stress case).

## Structure of this file

1. **Shift `lintegral` invariances on `cellMeasure c`** (`lintegral_shiftEta_eq`,
   `lintegral_shiftQ_eq`, `lintegral_shiftS_le`):
   - `shiftEta h` preserves `cellMeasure c` for every measurable `f : Profile → ℝ≥0∞`;
   - `shiftQ h` preserves `cellMeasure c` for every measurable `c`-periodic `f : Profile → ℝ≥0∞`;
   - `shiftS h` contracts `cellMeasure c` (`∫⁻ p, f (shiftS h p) ≤ ∫⁻ p, f p`) for every measurable
     `f : Profile → ℝ≥0∞` vanishing on `p.1 ≤ 0`.
2. **Unconditional difference and shift-stability bounds for `flatStressCutRep`**
   (`flatStressCutRep_sub_ae_cellMeasure`, `flatStressCutRep_shift_sub_ae_cellMeasure`,
   `lintegral_shift_sub_flatStressCutRep_sq_le`) and **complete density extension** from smooth
   tensor tests `N01.testSub c` (`N01.testSub_dense`) to all `F : HTSpace c`
   (`integral_shift_sub_sq_le_of_testSub`).
3. **Unconditional cutoff-derivative and Leibniz spatial gradient bounds on `cellMeasure c`**:
   - For any near cutoff `χ` (`IsNearCutoff c σ H1 L1 χ`), `fderiv ℝ χ` is smooth, `c`-periodic in
     `q`, supported in `[σ, H1] × ℝ × [-L1, L1]`, and satisfies `‖fderiv ℝ χ p‖ ≤ cNorm8 χ`; hence
     `pdS χ`, `pdQ χ`, `pdEta χ` satisfy `IsNearCutoff c σ H1 L1` and `|pd• χ p| ≤ cNorm8 χ`.
   - Pulling back the recentred causal spatial gradient `Gr : Chart → Fin 2 → Fin 2 → ℂ` via
     `Masked.cpcHT_eq` converts the `s^{-1/2}`-weighted bound `√c ‖Gr‖_𝒯 ≤ ν⁻¹ √2 ‖F‖` from
     `N05_4Aux.flatSmoothEnergyAndGrad` into the unweighted `L²(cellMeasure c)` bound
     `cellL2Norm c (flatGradCutRep c χ Gr j) ≤ 2 * Gamma^3 * ‖F‖`, and combines with the cutoff
     derivative term by the Leibniz rule `∇_{q,η}(χ b) = (∇_{q,η} χ) b + χ Gr` to give
     `cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr j) ≤ 3 * Gamma^3 * ‖F‖`, along
     with measurability, `c`-periodicity, box support, and `MemLp · 2 (cellMeasure c)` membership
     of `flatCutSpatialDeriv`.
4. **Decomposition into two leaf obligations (`PartII-a:N05/4/1/1`, `PartII-a:N05/4/1/2`) and
   conditional assembly (`flatStressSpatialHolderHalf_of`)**:
   - `FlatCutSpatialIBP` (`PartII-a:N05/4/1/1`): the Leibniz weak spatial integration-by-parts
     identities `ibp_q` and `ibp_eta` on `cellMeasure c` for `u = flatStressCutRep c χ (T0flat hc ν μ G)`
     and `dq = flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 0`,
     `deta = flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 1`, deduced from
     `b =ᵐ[ageμ c (-3/2)] velF c (T0flat hc ν μ G)` and `IsCausalEnergySolution.weakGrad`.
   - `CellWeakSpatialDiffQuotient` (`PartII-a:N05/4/1/2`): the 1D Sobolev difference-quotient
     bound on `cellMeasure c` for any box-supported `c`-periodic `u, dq, deta ∈ L²(cellMeasure c)`
     satisfying `ibp_q` and `ibp_eta` against all `IsMeridTest c φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
  (IsEnergyFieldAE volCyl_ac_ageμ fderiv_clm_comp')
open UnforcedLeray.Short.IIIa (tnorm2 tCalNorm HasWeakCellDerivC IsCausalEnergySolution)
open UnforcedLeray.Short.PartIIIb.NearInst (cellPt)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv cpcHT_eq)
open N05_4Aux

namespace N05_4_1Aux

/-! ### 1. Shift `lintegral` invariances on `cellMeasure c` -/

theorem measurable_shiftS (h : ℝ) : Measurable (shiftS h) :=
  measurable_shiftS_uncurry.comp (measurable_const.prodMk measurable_id)

theorem measurable_shiftQ (h : ℝ) : Measurable (shiftQ h) :=
  measurable_shiftQ_uncurry.comp (measurable_const.prodMk measurable_id)

theorem measurable_shiftEta (h : ℝ) : Measurable (shiftEta h) :=
  measurable_shiftEta_uncurry.comp (measurable_const.prodMk measurable_id)

/-- `shiftEta h` preserves `lintegral` on `cellMeasure c`. -/
theorem lintegral_shiftEta_eq (c h : ℝ) {f : Profile → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f (shiftEta h p) ∂(cellMeasure c) = ∫⁻ p, f p ∂(cellMeasure c) := by
  rw [lintegral_cellMeasure c (fun p => f (shiftEta h p)) (hf.comp (measurable_shiftEta h)),
    lintegral_cellMeasure c f hf]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
  exact lintegral_add_right_eq_self (fun η => f (s, q, η)) h

/-- `shiftQ h` preserves `lintegral` on `cellMeasure c` for `c`-periodic integrands. -/
theorem lintegral_shiftQ_eq {c : ℝ} (hc : 0 < c) (h : ℝ) {f : Profile → ℝ≥0∞}
    (hf : Measurable f) (hper : QPeriodic c f) :
    ∫⁻ p, f (shiftQ h p) ∂(cellMeasure c) = ∫⁻ p, f p ∂(cellMeasure c) := by
  rw [lintegral_cellMeasure c (fun p => f (shiftQ h p)) (hf.comp (measurable_shiftQ h)),
    lintegral_cellMeasure c f hf]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  let g : ℝ → ℝ≥0∞ := fun q => ∫⁻ η, f (s, q, η)
  have hgper : Function.Periodic g c := fun q => by
    dsimp only [g]
    congr 1
    funext η
    exact hper (s, q, η)
  have hshift := lintegral_period_shift (ε := 1 / 2) (by norm_num) hc g hgper h
  have hc1 : (2 : ℝ) * (1 / 2) * c = c := by ring
  have hc2 : ENNReal.ofReal ((2 : ℝ) * (1 / 2)) = 1 := by norm_num
  rw [hc1, hc2, one_mul] at hshift
  refine Eq.trans ?_ hshift
  refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
  dsimp only [g, shiftQ]
  have hq : q + h = h + q / ((2 : ℝ) * (1 / 2)) := by ring
  rw [hq]

/-- `shiftS h` contracts `lintegral` on `cellMeasure c` for integrands vanishing on `s ≤ 0`. -/
theorem lintegral_shiftS_le (c h : ℝ) {f : Profile → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ p : Profile, p.1 ≤ 0 → f p = 0) :
    ∫⁻ p, f (shiftS h p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c) := by
  rw [lintegral_cellMeasure c (fun p => f (shiftS h p)) (hf.comp (measurable_shiftS h)),
    lintegral_cellMeasure c f hf]
  let N : ℝ → ℝ≥0∞ := fun s => ∫⁻ q in Ioc 0 c, ∫⁻ η, f (s, q, η)
  change ∫⁻ s in Ioi (0 : ℝ), N (s + h) ≤ ∫⁻ s in Ioi (0 : ℝ), N s
  calc ∫⁻ s in Ioi (0 : ℝ), N (s + h)
      ≤ ∫⁻ s, N (s + h) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ s, N s := lintegral_add_right_eq_self N h
    _ = ∫⁻ s in Ioi (0 : ℝ), N s := by
        symm
        refine setLIntegral_eq_of_support_subset fun s hs => ?_
        rw [mem_Ioi]
        by_contra hle
        apply hs
        have hs0 : s ≤ 0 := not_lt.1 hle
        have hzero : ∀ q η, f (s, q, η) = 0 := fun q η => hsupp (s, q, η) hs0
        simp [N, hzero]

/-! ### 2. `flatStressCutRep` difference identities and density extension from `N01.testSub c` -/

theorem ae_cell_cellMeasure (c : ℝ) : ∀ᵐ p ∂(cellMeasure c), p ∈ cell c := by
  have hcell : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  exact ae_restrict_mem hcell

theorem ae_cellMeasure_of_ae_measureH {c : ℝ} {P : Profile → Prop}
    (hP : ∀ᵐ p ∂(measureH c), P p) : ∀ᵐ p ∂(cellMeasure c), P p := by
  have h1 : ∀ᵐ p ∂(cellMeasure c), weightH p ≠ 0 → P p :=
    (ae_withDensity_iff measurable_weightH).1 hP
  filter_upwards [h1, ae_cell_cellMeasure c] with p hp hpcell
  refine hp ?_
  unfold weightH
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpcell.1 _)).ne'

theorem flatStressCutRep_sub_ae_cellMeasure {c : ℝ} (hc : 0 < c) (χ : Profile → ℝ)
    (W₁ W₂ : HSpace c MeridC) :
    (fun p => flatStressCutRep c χ W₁ p - flatStressCutRep c χ W₂ p) =ᵐ[cellMeasure c]
      flatStressCutRep c χ (W₁ - W₂) := by
  have hsub : ∀ᵐ p ∂(cellMeasure c),
      (W₁ - W₂ : HSpace c MeridC) p = W₁ p - W₂ p :=
    ae_cellMeasure_of_ae_measureH (Lp.coeFn_sub W₁ W₂)
  filter_upwards [hsub, ae_cell_cellMeasure c] with p hp hpcell
  simp only [flatStressCutRep, periodize_of_mem hc _ hpcell, hp, smul_sub]

theorem flatStressCutRep_shift_sub_ae_cellMeasure {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (hlint : ∀ f : Profile → ℝ≥0∞, Measurable f → QPeriodic c f →
      (∀ p : Profile, p.1 ≤ 0 → f p = 0) →
      ∫⁻ p, f (shift p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c))
    (W₁ W₂ : HSpace c MeridC) :
    (fun p => flatStressCutRep c χ W₁ (shift p) - flatStressCutRep c χ W₂ (shift p))
      =ᵐ[cellMeasure c]
      (fun p => flatStressCutRep c χ (W₁ - W₂) (shift p)) := by
  let g : Profile → MeridC := fun p =>
    flatStressCutRep c χ W₁ p - flatStressCutRep c χ W₂ p - flatStressCutRep c χ (W₁ - W₂) p
  have hg_meas : Measurable g :=
    ((measurable_flatStressCutRep c hm W₁).sub (measurable_flatStressCutRep c hm W₂)).sub
      (measurable_flatStressCutRep c hm (W₁ - W₂))
  have hg_per : QPeriodic c g := fun p => by
    simp only [g, flatStressCutRep_periodic hc hχ W₁ p, flatStressCutRep_periodic hc hχ W₂ p,
      flatStressCutRep_periodic hc hχ (W₁ - W₂) p]
  have hg_supp : ∀ p : Profile, p.1 ≤ 0 → ‖g p‖ₑ = 0 := fun p hp0 => by
    have hχ0 : χ p = 0 := by
      by_contra hne
      have hs := (hχ.support p hne).1
      linarith
    simp [g, flatStressCutRep, hχ0]
  have hg_ae : g =ᵐ[cellMeasure c] 0 := by
    filter_upwards [flatStressCutRep_sub_ae_cellMeasure hc χ W₁ W₂] with p hp
    simp [g, hp]
  have hlint0 : ∫⁻ p, ‖g p‖ₑ ∂(cellMeasure c) = 0 := by
    rw [lintegral_eq_zero_iff hg_meas.enorm]
    filter_upwards [hg_ae] with p hp
    simp [hp]
  have hshift0 : ∫⁻ p, ‖g (shift p)‖ₑ ∂(cellMeasure c) = 0 := by
    refine le_antisymm ?_ (by positivity)
    rw [← hlint0]
    exact hlint (fun p => ‖g p‖ₑ) hg_meas.enorm (fun p => by dsimp only; rw [hg_per p]) hg_supp
  have hae_shift : (fun p => ‖g (shift p)‖ₑ) =ᵐ[cellMeasure c] 0 :=
    (lintegral_eq_zero_iff (hg_meas.comp hshift).enorm).1 hshift0
  filter_upwards [hae_shift] with p hp
  have h0 : g (shift p) = 0 := enorm_eq_zero.1 hp
  exact sub_eq_zero.1 h0

/-- Unconditional `L²(cellMeasure c)` shift-difference bound for `flatStressCutRep c χ W`. -/
theorem lintegral_shift_sub_flatStressCutRep_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (hlint : ∀ f : Profile → ℝ≥0∞, Measurable f → QPeriodic c f →
      (∀ p : Profile, p.1 ≤ 0 → f p = 0) →
      ∫⁻ p, f (shift p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c))
    (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((2 * ((1 + H1) * cNorm8 χ * ‖W‖)) ^ 2) := by
  let u := flatStressCutRep c χ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
  have hpt : ∀ p : Profile,
      ‖u (shift p) - u p‖ₑ ^ (2 : ℝ) ≤
        2 * ‖u (shift p)‖ₑ ^ (2 : ℝ) + 2 * ‖u p‖ₑ ^ (2 : ℝ) := fun p => by
    have hreal : ‖u (shift p) - u p‖ ^ 2 ≤ 2 * ‖u (shift p)‖ ^ 2 + 2 * ‖u p‖ ^ 2 := by
      have htri : ‖u (shift p) - u p‖ ≤ ‖u (shift p)‖ + ‖u p‖ := norm_sub_le _ _
      have hsq : ‖u (shift p) - u p‖ ^ 2 ≤ (‖u (shift p)‖ + ‖u p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖u (shift p)‖ - ‖u p‖)]
    have h1 : ‖u (shift p) - u p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖u (shift p) - u p‖ ^ 2) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    have h2 : 2 * ‖u (shift p)‖ₑ ^ (2 : ℝ) + 2 * ‖u p‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (2 * ‖u (shift p)‖ ^ 2 + 2 * ‖u p‖ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ← ofReal_norm, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two, Real.rpow_two]
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hreal
  have hf_meas : Measurable (fun p => ‖u p‖ₑ ^ (2 : ℝ)) := hu.enorm.pow_const (2 : ℝ)
  have hf_per : QPeriodic c (fun p => ‖u p‖ₑ ^ (2 : ℝ)) := fun p => by
    dsimp only [u]
    rw [flatStressCutRep_periodic hc hχ W p]
  have hf_supp : ∀ p : Profile, p.1 ≤ 0 → ‖u p‖ₑ ^ (2 : ℝ) = 0 := fun p hp0 => by
    have h0 : u p = 0 := by
      by_contra hne
      have hs := (flatStressCutRep_support hχ W p hne).1
      linarith
    simp [h0]
  have hshift_le := hlint _ hf_meas hf_per hf_supp
  have hbase := lintegral_flatStressCutRep_sq_le hc hσ hσH hχ hm W
  have hsh_meas : Measurable (fun p => ‖u (shift p)‖ₑ ^ (2 : ℝ)) := hf_meas.comp hshift
  calc ∫⁻ p, ‖u (shift p) - u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ∫⁻ p, (2 * ‖u (shift p)‖ₑ ^ (2 : ℝ) + 2 * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ p, ‖u (shift p)‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) +
          2 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
        rw [lintegral_add_left (hsh_meas.const_mul 2),
          lintegral_const_mul 2 hsh_meas, lintegral_const_mul 2 hf_meas]
    _ ≤ 2 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) +
          2 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by gcongr
    _ = 4 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by ring
    _ ≤ 4 * ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 * ((1 + H1) * cNorm8 χ * ‖W‖)) ^ 2) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- Unconditional density extension from smooth tensor tests (`N01.testSub c`) to all `F : HTSpace c`:
any shift-difference bound on smooth tensor tests extends to all `F : HTSpace c` with a factor of `2`
in the squared norm. -/
theorem integral_shift_sub_sq_le_of_testSub {ν c σ H1 L1 : ℝ} (hc : 0 < c) (_hν : 0 < ν)
    (hσ : 0 < σ) (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    (hm : Measurable χ) {μ : ℂ} (_hγ : 0 < μ.re + 1 / 4)
    {S0 : HTSpace c →L[ℂ] HSpace c MeridC} (hS0 : IsStressMap c 0 (T0flat hc ν μ) S0)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (hlint : ∀ f : Profile → ℝ≥0∞, Measurable f → QPeriodic c f →
      (∀ p : Profile, p.1 ≤ 0 → f p = 0) →
      ∫⁻ p, f (shift p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c))
    {K : ℝ} (hK : 0 ≤ K)
    (hsmooth : ∀ (M : Profile → TensorVal), IsTensorTest c M →
      ∀ (x : HTSpace c) (G : HSpace c MeridC),
      (x : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∫ p, ‖flatStressCutRep c χ (T0flat hc ν μ G) (shift p) -
          flatStressCutRep c χ (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c) ≤ K * ‖x‖ ^ 2)
    (F : HTSpace c) :
    ∫ p, ‖flatStressCutRep c χ (S0 F) (shift p) -
        flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c) ≤ 2 * (K * ‖F‖ ^ 2) := by
  let uF := flatStressCutRep c χ (S0 F)
  have huF_meas : Measurable (fun p => uF (shift p) - uF p) :=
    ((measurable_flatStressCutRep c hm (S0 F)).comp hshift).sub
      (measurable_flatStressCutRep c hm (S0 F))
  have huF_lint := lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (S0 F)
  have huF_int : Integrable (fun p => ‖uF (shift p) - uF p‖ ^ 2) (cellMeasure c) := by
    have hmem : MemLp (fun p => uF (shift p) - uF p) 2 (cellMeasure c) := by
      refine ⟨huF_meas.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lt_of_le_of_lt huF_lint ENNReal.ofReal_lt_top).ne
    exact hmem.integrable_norm_pow two_ne_zero
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  let C_op : ℝ := 2 * ((1 + H1) * cNorm8 χ * ‖S0‖) + 1
  have hCop_pos : 0 < C_op := by
    dsimp only [C_op]
    have : 0 ≤ (1 + H1) * cNorm8 χ * ‖S0‖ :=
      mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg S0)
    linarith
  let δ1 : ℝ := Real.sqrt (ε / 4) / C_op
  let δ2 : ℝ := ε / (4 * (K + 1) * (2 * ‖F‖ + 1))
  let δ : ℝ := min 1 (min δ1 δ2)
  have hδ_pos : 0 < δ := by
    dsimp only [δ, δ1, δ2]
    refine lt_min zero_lt_one (lt_min ?_ ?_) <;> positivity
  have hdense := Metric.mem_closure_iff.1 (N01.testSub_dense c hc F) δ hδ_pos
  obtain ⟨x, ⟨x_sub, rfl⟩, hdist⟩ := hdense
  let x : HTSpace c := x_sub.1
  obtain ⟨M, hM, hxM⟩ := x_sub.2
  let G : HSpace c MeridC :=
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c 0 hc M hM).toLp _
  have hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) :=
    MemLp.coeFn_toLp _
  have hS0x : S0 x = T0flat hc ν μ G := hS0 M hM x G hxM hG
  let ux := flatStressCutRep c χ (S0 x)
  let ud := flatStressCutRep c χ (S0 (F - x))
  have hux_int : Integrable (fun p => ‖ux (shift p) - ux p‖ ^ 2) (cellMeasure c) := by
    have hm_ux : Measurable (fun p => ux (shift p) - ux p) :=
      ((measurable_flatStressCutRep c hm (S0 x)).comp hshift).sub
        (measurable_flatStressCutRep c hm (S0 x))
    have hmem : MemLp (fun p => ux (shift p) - ux p) 2 (cellMeasure c) := by
      refine ⟨hm_ux.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lt_of_le_of_lt
          (lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (S0 x))
          ENNReal.ofReal_lt_top).ne
    exact hmem.integrable_norm_pow two_ne_zero
  have hud_int : Integrable (fun p => ‖ud (shift p) - ud p‖ ^ 2) (cellMeasure c) := by
    have hm_ud : Measurable (fun p => ud (shift p) - ud p) :=
      ((measurable_flatStressCutRep c hm (S0 (F - x))).comp hshift).sub
        (measurable_flatStressCutRep c hm (S0 (F - x)))
    have hmem : MemLp (fun p => ud (shift p) - ud p) 2 (cellMeasure c) := by
      refine ⟨hm_ud.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lt_of_le_of_lt
          (lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (S0 (F - x)))
          ENNReal.ofReal_lt_top).ne
    exact hmem.integrable_norm_pow two_ne_zero
  have hae_diff : ∀ᵐ p ∂(cellMeasure c),
      uF (shift p) - uF p = (ux (shift p) - ux p) + (ud (shift p) - ud p) := by
    have hS0_sub : S0 F - S0 x = S0 (F - x) := (map_sub S0 F x).symm
    have h1 := flatStressCutRep_sub_ae_cellMeasure hc χ (S0 F) (S0 x)
    have h2 := flatStressCutRep_shift_sub_ae_cellMeasure hc hσ hχ hm hshift hlint (S0 F) (S0 x)
    filter_upwards [h1, h2] with p hp1 hp2
    dsimp only [uF, ux, ud] at hp1 hp2 ⊢
    rw [← hS0_sub, ← hp1, ← hp2]
    abel
  have hpt_le : ∀ᵐ p ∂(cellMeasure c),
      ‖uF (shift p) - uF p‖ ^ 2 ≤
        2 * ‖ux (shift p) - ux p‖ ^ 2 + 2 * ‖ud (shift p) - ud p‖ ^ 2 := by
    filter_upwards [hae_diff] with p hp
    rw [hp]
    have htri : ‖(ux (shift p) - ux p) + (ud (shift p) - ud p)‖ ≤
        ‖ux (shift p) - ux p‖ + ‖ud (shift p) - ud p‖ := norm_add_le _ _
    have hsq : ‖(ux (shift p) - ux p) + (ud (shift p) - ud p)‖ ^ 2 ≤
        (‖ux (shift p) - ux p‖ + ‖ud (shift p) - ud p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖ux (shift p) - ux p‖ - ‖ud (shift p) - ud p‖)]
  have hint_split : ∫ p, ‖uF (shift p) - uF p‖ ^ 2 ∂(cellMeasure c) ≤
      2 * ∫ p, ‖ux (shift p) - ux p‖ ^ 2 ∂(cellMeasure c) +
      2 * ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) := by
    calc ∫ p, ‖uF (shift p) - uF p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∫ p, (2 * ‖ux (shift p) - ux p‖ ^ 2 + 2 * ‖ud (shift p) - ud p‖ ^ 2) ∂(cellMeasure c) :=
          integral_mono_ae huF_int ((hux_int.const_mul 2).add (hud_int.const_mul 2)) hpt_le
      _ = 2 * ∫ p, ‖ux (shift p) - ux p‖ ^ 2 ∂(cellMeasure c) +
          2 * ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) := by
          rw [integral_add (hux_int.const_mul 2) (hud_int.const_mul 2),
            integral_const_mul, integral_const_mul]
  have hux_le : ∫ p, ‖ux (shift p) - ux p‖ ^ 2 ∂(cellMeasure c) ≤ K * ‖x‖ ^ 2 := by
    dsimp only [ux]
    rw [hS0x]
    exact hsmooth M hM x G hxM hG
  have hud_le : ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) ≤
      (2 * ((1 + H1) * cNorm8 χ * ‖S0 (F - x)‖)) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hud_int (Eventually.of_forall fun _ => sq_nonneg _)]
    have hcongr : (∫⁻ p, ENNReal.ofReal (‖ud (shift p) - ud p‖ ^ 2) ∂(cellMeasure c)) =
        ∫⁻ p, ‖ud (shift p) - ud p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
      refine lintegral_congr fun p => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    rw [hcongr]
    exact lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (S0 (F - x))
  have hFx_lt : ‖F - x‖ < δ := by rwa [← dist_eq_norm]
  have hFx_le1 : ‖F - x‖ ≤ 1 := hFx_lt.le.trans (min_le_left 1 _)
  have hFx_le_δ1 : ‖F - x‖ ≤ δ1 :=
    hFx_lt.le.trans ((min_le_right 1 _).trans (min_le_left δ1 δ2))
  have hFx_le_δ2 : ‖F - x‖ ≤ δ2 :=
    hFx_lt.le.trans ((min_le_right 1 _).trans (min_le_right δ1 δ2))
  have hud_bound : 2 * ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) ≤ ε / 2 := by
    have h1 : 2 * ((1 + H1) * cNorm8 χ * ‖S0 (F - x)‖) ≤ C_op * ‖F - x‖ := by
      have hS0_op : ‖S0 (F - x)‖ ≤ ‖S0‖ * ‖F - x‖ := S0.le_opNorm (F - x)
      calc 2 * ((1 + H1) * cNorm8 χ * ‖S0 (F - x)‖)
          ≤ 2 * ((1 + H1) * cNorm8 χ * (‖S0‖ * ‖F - x‖)) := by
            gcongr
            exact mul_nonneg (by linarith) (cNorm8_nonneg χ)
        _ = (2 * ((1 + H1) * cNorm8 χ * ‖S0‖)) * ‖F - x‖ := by ring
        _ ≤ C_op * ‖F - x‖ := by
            dsimp only [C_op]
            nlinarith [norm_nonneg (F - x)]
    have h2 : C_op * ‖F - x‖ ≤ Real.sqrt (ε / 4) := by
      calc C_op * ‖F - x‖ ≤ C_op * δ1 := mul_le_mul_of_nonneg_left hFx_le_δ1 hCop_pos.le
        _ = Real.sqrt (ε / 4) := mul_div_cancel₀ _ hCop_pos.ne'
    have h3 : (2 * ((1 + H1) * cNorm8 χ * ‖S0 (F - x)‖)) ^ 2 ≤ ε / 4 := by
      have h0_lhs : 0 ≤ 2 * ((1 + H1) * cNorm8 χ * ‖S0 (F - x)‖) :=
        mul_nonneg zero_le_two
          (mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg _))
      calc (2 * ((1 + H1) * cNorm8 χ * ‖S0 (F - x)‖)) ^ 2
          ≤ (Real.sqrt (ε / 4)) ^ 2 :=
            pow_le_pow_left₀ h0_lhs (h1.trans h2) 2
        _ = ε / 4 := Real.sq_sqrt (by positivity)
    linarith
  have hux_bound : 2 * (K * ‖x‖ ^ 2) < 2 * (K * ‖F‖ ^ 2) + ε / 2 := by
    have hx_le : ‖x‖ ≤ ‖F‖ + ‖F - x‖ := by
      have := norm_sub_le F (F - x)
      simpa using this
    have hx_sq : ‖x‖ ^ 2 ≤ ‖F‖ ^ 2 + (2 * ‖F‖ + 1) * ‖F - x‖ := by
      have hsq : ‖x‖ ^ 2 ≤ (‖F‖ + ‖F - x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg x) hx_le 2
      have hpow : ‖F - x‖ ^ 2 ≤ ‖F - x‖ := by
        nlinarith [norm_nonneg (F - x)]
      nlinarith
    have hK_diff : 2 * K * ((2 * ‖F‖ + 1) * ‖F - x‖) < ε / 2 := by
      calc 2 * K * ((2 * ‖F‖ + 1) * ‖F - x‖)
          ≤ 2 * K * ((2 * ‖F‖ + 1) * δ2) := by gcongr
        _ < 2 * (K + 1) * ((2 * ‖F‖ + 1) * δ2) := by
            have hδ2_pos : 0 < (2 * ‖F‖ + 1) * δ2 := by
              dsimp only [δ2]; positivity
            nlinarith
        _ = ε / 2 := by
            dsimp only [δ2]
            have hne1 : K + 1 ≠ 0 := by linarith
            have hne2 : 2 * ‖F‖ + 1 ≠ 0 := by positivity
            field_simp
            ring
    nlinarith
  linarith

/-! ### 3. Unconditional cutoff-derivative and Leibniz spatial gradient bounds on `cellMeasure c` -/

/-- For any near cutoff `χ`, `fderiv ℝ χ` is `c`-periodic in `q`. -/
theorem fderiv_periodic_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    fderiv ℝ χ (p.1, p.2.1 + c, p.2.2) = fderiv ℝ χ p := by
  let a : Profile := (0, c, 0)
  have hpa : (p.1, p.2.1 + c, p.2.2) = p + a := by
    ext <;> simp [a]
  have hfun : (χ ∘ fun q : Profile => q + a) = χ := by
    funext q
    change χ (q + a) = χ q
    have hqa : q + a = (q.1, q.2.1 + c, q.2.2) := by
      ext <;> simp [a]
    rw [hqa]
    exact hχ.periodic q
  have hd1 : HasFDerivAt χ (fderiv ℝ χ (p + a)) (p + a) :=
    (hχ.smooth.differentiable (by decide) (p + a)).hasFDerivAt
  have hd2 : HasFDerivAt (fun q : Profile => q + a) (ContinuousLinearMap.id ℝ Profile) p := by
    simpa using (hasFDerivAt_id p).add_const a
  have hcomp : HasFDerivAt (χ ∘ fun q : Profile => q + a) (fderiv ℝ χ (p + a)) p := by
    simpa using hd1.comp p hd2
  rw [hfun] at hcomp
  rw [hpa, hcomp.fderiv]

/-- For any near cutoff `χ`, `fderiv ℝ χ` is supported in `[σ, H1] × ℝ × [-L1, L1]`. -/
theorem fderiv_support_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) (hp : fderiv ℝ χ p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  by_contra hnot
  apply hp
  let S : Set Profile := {q : Profile | σ ≤ q.1 ∧ q.1 ≤ H1 ∧ |q.2.2| ≤ L1}
  have hS_closed : IsClosed S :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le (continuous_snd.comp continuous_snd).abs continuous_const))
  have hp_mem : Sᶜ ∈ 𝓝 p := hS_closed.isOpen_compl.mem_nhds hnot
  have hev : χ =ᶠ[𝓝 p] (0 : Profile → ℝ) :=
    Filter.eventuallyEq_iff_exists_mem.2
      ⟨Sᶜ, hp_mem, fun q hq => by_contra fun h0 => hq (hχ.support q h0)⟩
  rw [hev.fderiv_eq]
  simp

/-- Pointwise bound `‖fderiv ℝ χ p‖ ≤ cNorm8 χ` for any near cutoff `χ`. -/
theorem norm_fderiv_le_cNorm8_of_nearCutoff {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    ‖fderiv ℝ χ p‖ ≤ cNorm8 χ := by
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous (fun q : Profile => ‖fderiv ℝ χ q‖) :=
    (hχ.smooth.continuous_fderiv (by decide)).norm
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hper1 : QPeriodic c (fun q : Profile => ‖fderiv ℝ χ q‖) := fun q => by
    dsimp only
    rw [fderiv_periodic_of_nearCutoff hχ q]
  have hbdd : BddAbove (range fun q : Profile => ‖iteratedFDeriv ℝ 1 χ q‖) := by
    refine ⟨max C1 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_one]
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : ‖fderiv ℝ χ q'‖ = ‖fderiv ℝ χ q‖ :=
      periodic_reduceIoc_eq (fun r => ‖fderiv ℝ χ r‖) hper1 q.1 q.2.1 q.2.2
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

/-- Directional derivative `fun p => fderiv ℝ χ p v` of a near cutoff `χ` is itself a near cutoff. -/
theorem isNearCutoff_fderiv_apply {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (v : Profile) :
    IsNearCutoff c σ H1 L1 (fun p => fderiv ℝ χ p v) where
  smooth := (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
    (hχ.smooth.fderiv_right (by decide))
  periodic p := by
    dsimp only
    rw [fderiv_periodic_of_nearCutoff hχ p]
  support p hp :=
    fderiv_support_of_nearCutoff hχ p fun h0 => hp (by simp [h0])

theorem abs_fderiv_apply_le_cNorm8 {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {v : Profile} (hv : ‖v‖ ≤ 1) (p : Profile) :
    |fderiv ℝ χ p v| ≤ cNorm8 χ := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ χ p v‖
      ≤ ‖fderiv ℝ χ p‖ * ‖v‖ := (fderiv ℝ χ p).le_opNorm v
    _ ≤ cNorm8 χ * 1 := mul_le_mul (norm_fderiv_le_cNorm8_of_nearCutoff hc hχ p) hv
        (norm_nonneg v) (cNorm8_nonneg χ)
    _ = cNorm8 χ := mul_one _

/-- Unweighted `L²(cellMeasure c)` bound on `flatStressCutRep c dχ W` for any directional
derivative `dχ = fun p => fderiv ℝ χ p v` with `‖v‖ ≤ 1`. -/
theorem lintegral_flatStressCutRep_fderiv_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1) (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c (fun q => fderiv ℝ χ q v) W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hm : Measurable dχ := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c dχ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
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
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  have hB : ∀ p, |dχ p| ≤ cNorm8 χ := abs_fderiv_apply_le_cNorm8 hc hχ hv
  let U₀ := mulChi (measureH c) dχ hm hB W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    flatStressCutRep_ae_eq hc dχ hm hB W
  have hU0_norm : ‖U₀‖ ≤ cNorm8 χ * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) dχ hm hB (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) dχ hm hB (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB p) (norm_nonneg _)
  have hstep2 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤
      ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) := by
    have hcongr : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    have hLp : eLpNorm (U₀ : Profile → MeridC) 2 (measureH c) = ENNReal.ofReal ‖U₀‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U₀)]
    have hlint : ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ENNReal.ofReal (‖U₀‖ ^ 2) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := measureH c)
        (f := (U₀ : Profile → MeridC)) two_ne_zero ENNReal.ofNat_ne_top
      rw [hLp, ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg U₀) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two] at hpow
      exact hpow
    rw [hcongr, hlint]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg U₀) hU0_norm 2)
  calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal ((1 + H1) ^ 2) * ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

theorem cellL2Norm_flatStressCutRep_fderiv_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1) (W : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c (fun q => fderiv ℝ χ q v) W) ≤
      (1 + H1) * cNorm8 χ * ‖W‖ := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hm : Measurable dχ := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c dχ W
  have hmem := memLp_flatStressCutRep hc hσ hσH hdχ hm W
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hB0 : 0 ≤ (1 + H1) * cNorm8 χ * ‖W‖ :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg W)
  have hint_le : ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * ‖W‖) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_flatStressCutRep_fderiv_sq_le hc hσ hσH hχ hv W
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * ‖W‖ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

/-- Pullback of the `j`-th column (`j = 0` for `∂_q`, `j = 1` for `∂_η`) of a recentred gradient
`Gr : Chart → Fin 2 → Fin 2 → ℂ` to `Profile`. -/
def flatGradCol (c : ℝ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile) : MeridC :=
  WithLp.toLp 2 (fun i : Fin 2 => Gr (cellPt c p) i j)

/-- Concrete box-supported `c`-periodic representative of `χ • ∂_{q,η} b` on `Profile`. -/
def flatGradCutRep (c : ℝ) (χ : Profile → ℝ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2)
    (p : Profile) : MeridC :=
  χ p • periodize c (flatGradCol c Gr j) p

/-- Full Leibniz spatial derivative representative `(∇_{q,η} χ) b + χ Gr` on `Profile`:
`j = 0` is the `q`-derivative `(pdQ χ) b + χ Gr_q`, `j = 1` is the `η`-derivative
`(pdEta χ) b + χ Gr_η`. -/
def flatCutSpatialDeriv (c : ℝ) (χ : Profile → ℝ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile) : MeridC :=
  flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) W p + flatGradCutRep c χ Gr j p

theorem measurable_flatGradCol (c : ℝ) {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hGr : ∀ i j, Measurable (fun x => Gr x i j)) (j : Fin 2) :
    Measurable (flatGradCol c Gr j) := by
  unfold flatGradCol
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℂ)).comp (measurable_pi_iff.2 fun i => ?_)
  exact (hGr i j).comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c)

theorem measurable_flatGradCutRep (c : ℝ) {χ : Profile → ℝ} (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j)) (j : Fin 2) :
    Measurable (flatGradCutRep c χ Gr j) :=
  hm.smul (measurable_periodize_meridC c (measurable_flatGradCol c hGr j))

theorem flatGradCutRep_periodic {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) :
    QPeriodic c (flatGradCutRep c χ Gr j) := by
  intro p
  simp only [flatGradCutRep, hχ.periodic p, qPeriodic_periodize hc (flatGradCol c Gr j) p]

theorem flatGradCutRep_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile)
    (hp : flatGradCutRep c χ Gr j p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  refine hχ.support p ?_
  intro h0
  apply hp
  simp [flatGradCutRep, h0]

theorem norm_flatGradCol_le_tnorm2 (c : ℝ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2)
    (p : Profile) :
    ‖flatGradCol c Gr j p‖ ≤ tnorm2 (Gr (cellPt c p)) := by
  unfold flatGradCol tnorm2
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two]
  fin_cases j <;> dsimp <;>
    nlinarith [sq_nonneg ‖Gr (cellPt c p) 0 0‖, sq_nonneg ‖Gr (cellPt c p) 0 1‖,
      sq_nonneg ‖Gr (cellPt c p) 1 0‖, sq_nonneg ‖Gr (cellPt c p) 1 1‖]

theorem measurable_tnorm2 {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hGr : ∀ i j, Measurable (fun x => Gr x i j)) :
    Measurable (fun x => tnorm2 (Gr x)) := by
  unfold tnorm2
  refine Real.continuous_sqrt.measurable.comp ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (hGr i j).norm.pow_const 2

/-- Unweighted `L²(cellMeasure c)` bound on `flatGradCutRep c χ Gr j` from `√c ‖Gr‖_𝒯 ≤ B_Gr`. -/
theorem lintegral_flatGradCutRep_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    ∫⁻ p, ‖flatGradCutRep c χ Gr j p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) := by
  let g := flatGradCutRep c χ Gr j
  have hg_meas : Measurable g := measurable_flatGradCutRep c hm hGr j
  have htn_meas : Measurable (fun x => tnorm2 (Gr x)) := measurable_tnorm2 hGr
  have hcell_pt : ∀ᵐ p ∂(cellMeasure c),
      ‖g p‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
          (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [ae_cell_cellMeasure c] with p hpcell
    by_cases hp0 : g p = 0
    · simp [hp0]
    · obtain ⟨hs1, hs2, _⟩ := flatGradCutRep_support hχ Gr j p hp0
      have hs_pos : 0 < p.1 := lt_of_lt_of_le hσ hs1
      have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
      have h1H1 : 1 ≤ 1 + H1 := by linarith
      have hp1H1 : p.1 ≤ 1 + H1 := by linarith
      have hrpow : p.1 ^ (1 / 2 : ℝ) ≤ (1 + H1) ^ 2 := by
        calc p.1 ^ (1 / 2 : ℝ)
            ≤ (1 + H1) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp1H1 (by norm_num)
          _ ≤ (1 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1H1 (by norm_num)
          _ = (1 + H1) ^ 2 := Real.rpow_two (1 + H1)
      have h1 : 1 ≤ (1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ)) := by
        calc (1 : ℝ)
            = p.1 ^ (1 / 2 : ℝ) * p.1 ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hs_pos]; norm_num
          _ ≤ (1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
      have hgnorm : ‖g p‖ ≤ cNorm8 χ * ‖tnorm2 (Gr (cellPt c p))‖ := by
        dsimp only [g, flatGradCutRep]
        rw [periodize_of_mem hc _ hpcell, norm_smul, Real.norm_eq_abs,
          Real.norm_of_nonneg (by unfold tnorm2; exact Real.sqrt_nonneg _)]
        exact mul_le_mul (abs_le_cNorm8_of_nearCutoff hc hχ p)
          (norm_flatGradCol_le_tnorm2 c Gr j p) (norm_nonneg _) (cNorm8_nonneg χ)
      have hgsq : ‖g p‖ ^ 2 ≤ ((1 + H1) * cNorm8 χ) ^ 2 *
          (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by
        calc ‖g p‖ ^ 2
            ≤ (cNorm8 χ * ‖tnorm2 (Gr (cellPt c p))‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hgnorm 2
          _ = 1 * (cNorm8 χ ^ 2 * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by ring
          _ ≤ ((1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ))) *
                (cNorm8 χ ^ 2 * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = ((1 + H1) * cNorm8 χ) ^ 2 *
                (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by ring
      have hLHS : ‖g p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g p‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two]
      have hRHS : ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) =
          ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2 *
            (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2)) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs_pos.le _),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
      rw [hLHS, hRHS]
      exact ENNReal.ofReal_le_ofReal hgsq
  have hstep1 : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
        ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) := by
    have hm_tn : Measurable (fun p => ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) :=
      (htn_meas.comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c)).enorm.pow_const (2 : ℝ)
    have hm_w : Measurable (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
    calc ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) *
              ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono_ae hcell_pt
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) *
              ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (hm_w.mul hm_tn)
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) := by
          rw [measureHT, lintegral_withDensity_eq_lintegral_mul _ hm_w hm_tn]
          rfl
  have hstep2 : ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) ≤
      ENNReal.ofReal (B_Gr ^ 2) := by
    have hmap : Measure.map (cellPt c) (measureHT c) = ENNReal.ofReal c • ageμ c (-1 / 2) :=
      cpcHT_eq c hc
    have hmap_lint : ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) =
        ENNReal.ofReal c * ∫⁻ x, ‖tnorm2 (Gr x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
      rw [← lintegral_map (htn_meas.enorm.pow_const (2 : ℝ))
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c), hmap,
        lintegral_smul_measure, smul_eq_mul]
    have hCal_sq : ENNReal.ofReal c * ∫⁻ x, ‖tnorm2 (Gr x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) =
        (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := ageμ c (-1 / 2))
        (f := fun x => tnorm2 (Gr x)) two_ne_zero ENNReal.ofNat_ne_top
      rw [ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at hpow
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg c) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two, Real.sq_sqrt hc.le, ← hpow]
      rfl
    rw [hmap_lint, hCal_sq]
    calc (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal B_Gr) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hCal (by norm_num)
      _ = ENNReal.ofReal (B_Gr ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  calc ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) * ENNReal.ofReal (B_Gr ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

theorem memLp_flatGradCutRep {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    MemLp (flatGradCutRep c χ Gr j) 2 (cellMeasure c) := by
  refine ⟨(measurable_flatGradCutRep c hm hGr j).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hle := lintegral_flatGradCutRep_sq_le hc hσ hσH hχ hm hGr hB0 hCal j
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne

theorem cellL2Norm_flatGradCutRep_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    cellL2Norm c (flatGradCutRep c χ Gr j) ≤ (1 + H1) * cNorm8 χ * B_Gr := by
  let g := flatGradCutRep c χ Gr j
  have hmem := memLp_flatGradCutRep hc hσ hσH hχ hm hGr hB0 hCal j
  have hint : Integrable (fun p => ‖g p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hC0 : 0 ≤ (1 + H1) * cNorm8 χ * B_Gr :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) hB0
  have hint_le : ∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * B_Gr) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_flatGradCutRep_sq_le hc hσ hσH hχ hm hGr hB0 hCal j
  unfold cellL2Norm
  calc (∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * B_Gr := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hC0]

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

theorem measurable_flatCutSpatialDeriv {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) (W : HSpace c MeridC)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j)) (j : Fin 2) :
    Measurable (flatCutSpatialDeriv c χ W Gr j) := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hv_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    funext q
    by_cases hj : j = 0 <;> simp [hj, v, pdQ, pdEta]
  have hdχ_near : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hv_eq]
    exact isNearCutoff_fderiv_apply hχ v
  exact (measurable_flatStressCutRep c hdχ_near.smooth.continuous.measurable W).add
    (measurable_flatGradCutRep c hm hGr j)

theorem flatCutSpatialDeriv_periodic {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) :
    QPeriodic c (flatCutSpatialDeriv c χ W Gr j) := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hv_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    funext q
    by_cases hj : j = 0 <;> simp [hj, v, pdQ, pdEta]
  have hdχ_near : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hv_eq]
    exact isNearCutoff_fderiv_apply hχ v
  intro p
  simp only [flatCutSpatialDeriv, flatStressCutRep_periodic hc hdχ_near W p,
    flatGradCutRep_periodic hc hχ Gr j p]

theorem flatCutSpatialDeriv_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile)
    (hp : flatCutSpatialDeriv c χ W Gr j p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hv_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    funext q
    by_cases hj : j = 0 <;> simp [hj, v, pdQ, pdEta]
  have hdχ_near : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hv_eq]
    exact isNearCutoff_fderiv_apply hχ v
  by_cases h1 : flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) W p ≠ 0
  · exact flatStressCutRep_support hdχ_near W p h1
  · rw [not_ne_iff] at h1
    have h2 : flatGradCutRep c χ Gr j p ≠ 0 := by
      intro h0
      apply hp
      simp [flatCutSpatialDeriv, h1, h0]
    exact flatGradCutRep_support hχ Gr j p h2

theorem memLp_flatCutSpatialDeriv {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) (W : HSpace c MeridC)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    MemLp (flatCutSpatialDeriv c χ W Gr j) 2 (cellMeasure c) := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hv_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    funext q
    by_cases hj : j = 0 <;> simp [hj, v, pdQ, pdEta]
  have hdχ_near : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hv_eq]
    exact isNearCutoff_fderiv_apply hχ v
  have hmem1 : MemLp (flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) W)
      2 (cellMeasure c) :=
    memLp_flatStressCutRep hc hσ hσH hdχ_near hdχ_near.smooth.continuous.measurable W
  have hmem2 : MemLp (flatGradCutRep c χ Gr j) 2 (cellMeasure c) :=
    memLp_flatGradCutRep hc hσ hσH hχ hm hGr hB0 hCal j
  exact hmem1.add hmem2

/-- Unconditional `3 * Gamma^3 * ‖F‖` bound on the full Leibniz spatial derivative representative
`flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr j` on `cellMeasure c`. -/
theorem cellL2Norm_flatCutSpatialDeriv_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (F : HTSpace c) (G : HSpace c MeridC)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    (hH : ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤
      ENNReal.ofReal (ν⁻¹ * (Real.sqrt 2 * ‖F‖)))
    (j : Fin 2) :
    cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr j) ≤
      3 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖F‖ := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hG0 : 0 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hv_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    funext q
    by_cases hj : j = 0 <;> simp [hj, v, pdQ, pdEta]
  have hv_norm : ‖v‖ ≤ 1 := by
    by_cases hj : j = 0 <;> simp [hj, v, Prod.norm_def]
  have hdχ_near : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hv_eq]
    exact isNearCutoff_fderiv_apply hχ v
  have hmem1 : MemLp (flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) (T0flat hc ν μ G))
      2 (cellMeasure c) :=
    memLp_flatStressCutRep hc hσ hσH hdχ_near hdχ_near.smooth.continuous.measurable
      (T0flat hc ν μ G)
  have hB0 : 0 ≤ ν⁻¹ * (Real.sqrt 2 * ‖F‖) := by positivity
  have hmem2 : MemLp (flatGradCutRep c χ Gr j) 2 (cellMeasure c) :=
    memLp_flatGradCutRep hc hσ hσH hχ hm hGr hB0 hCal j
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hnorm1 : cellL2Norm c
      (flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) (T0flat hc ν μ G)) ≤
      Gam ^ 3 * ‖F‖ := by
    rw [hv_eq]
    calc cellL2Norm c (flatStressCutRep c (fun q => fderiv ℝ χ q v) (T0flat hc ν μ G))
        ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖ :=
          cellL2Norm_flatStressCutRep_fderiv_le_mul hc hσ hσH hχ hv_norm (T0flat hc ν μ G)
      _ ≤ (1 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :=
          mul_le_mul_of_nonneg_left hH (mul_nonneg (by linarith) (cNorm8_nonneg χ))
      _ = (1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by ring
      _ ≤ Gam * Gam * Gam * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
          refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
            (by positivity) (mul_nonneg hG0 hG0)
      _ = Gam ^ 3 * ‖F‖ := by ring
  have hnorm2 : cellL2Norm c (flatGradCutRep c χ Gr j) ≤ 2 * Gam ^ 3 * ‖F‖ := by
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      have hsq : (Real.sqrt 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2
    calc cellL2Norm c (flatGradCutRep c χ Gr j)
        ≤ (1 + H1) * cNorm8 χ * (ν⁻¹ * (Real.sqrt 2 * ‖F‖)) :=
          cellL2Norm_flatGradCutRep_le_mul hc hσ hσH hχ hm hGr hB0 hCal j
      _ ≤ (1 + H1) * cNorm8 χ * (ν⁻¹ * (2 * ‖F‖)) := by
          gcongr
          exact mul_nonneg (by linarith) (cNorm8_nonneg χ)
      _ = 2 * ((1 + H1) * cNorm8 χ * ν⁻¹) * ‖F‖ := by ring
      _ ≤ 2 * (Gam * Gam * Gam) * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (norm_nonneg F)
          refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hν_G
            hνi.le (mul_nonneg hG0 hG0)
      _ = 2 * Gam ^ 3 * ‖F‖ := by ring
  calc cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr j)
      ≤ cellL2Norm c (flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) (T0flat hc ν μ G)) +
          cellL2Norm c (flatGradCutRep c χ Gr j) :=
        cellL2Norm_add_le hmem1 hmem2
    _ ≤ Gam ^ 3 * ‖F‖ + 2 * Gam ^ 3 * ‖F‖ := add_le_add hnorm1 hnorm2
    _ = 3 * Gam ^ 3 * ‖F‖ := by ring

/-! ### 4. Unconditional `(q, η)` integration by parts (`flatCutSpatialDeriv_ibp`) -/

/-- Unified spatial profile derivative: `j = 0` is `pdQ`, `j = 1` is `pdEta`. -/
def pdSpatial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (f : Profile → E) : Profile → E :=
  if j = 0 then pdQ f else pdEta f

theorem pdSpatial_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (f : Profile → E) (p : Profile) :
    pdSpatial j f p = fderiv ℝ f p (0, UnforcedLeray.B0579.dir j) := by
  fin_cases j <;> rfl

theorem isMeridTest_pdSpatial {c : ℝ} {φ : Profile → MeridC} (hφ : IsMeridTest c φ) (j : Fin 2) :
    IsMeridTest c (pdSpatial j φ) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hφ.band
  have hK : IsClosed (Icc s0 s1 ×ˢ (univ : Set (ℝ × ℝ)) ∩ {p : Profile | |p.2.2| ≤ L}) :=
    (isClosed_Icc.prod isClosed_univ).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hsub : tsupport φ ⊆ Icc s0 s1 ×ˢ (univ : Set (ℝ × ℝ)) ∩ {p : Profile | |p.2.2| ≤ L} := by
    refine closure_minimal (fun p hp => ?_) hK
    obtain ⟨h1, h2⟩ := hband p hp
    exact ⟨⟨h1, trivial⟩, h2⟩
  refine ⟨?_, ?_, ⟨s0, s1, L, hs0, fun p hp => ?_⟩⟩
  · fin_cases j
    · exact UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.isMeridTest_pdQ_aux hφ
    · exact UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.isMeridTest_pdEta_aux hφ
  · intro p
    rw [pdSpatial_eq_fderiv, pdSpatial_eq_fderiv]
    exact UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.pd_periodic_aux hφ.periodic _ p
  · rw [pdSpatial_eq_fderiv] at hp
    have hdf : fderiv ℝ φ p ≠ 0 := fun h0 => hp (by simp [h0])
    have hm := hsub (support_fderiv_subset ℝ hdf)
    exact ⟨hm.1.1, hm.2⟩

theorem isMeridTest_smul_cutoff {c σ H1 L1 : ℝ} (hσ : 0 < σ) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    IsMeridTest c (fun p => χ p • φ p) where
  smooth := hχ.smooth.smul hφ.smooth
  periodic p := by simp only [hχ.periodic p, hφ.periodic p]
  band := ⟨σ, H1, L1, hσ, fun p hp => by
    have hχ0 : χ p ≠ 0 := fun h0 => hp (by simp [h0])
    obtain ⟨hs1, hs2, hη⟩ := hχ.support p hχ0
    exact ⟨⟨hs1, hs2⟩, hη⟩⟩

theorem pdSpatial_smul_cutoff {χ : Profile → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {φ : Profile → MeridC} (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) (p : Profile) :
    pdSpatial j (fun q => χ q • φ q) p =
      pdSpatial j χ p • φ p + χ p • pdSpatial j φ p := by
  rw [pdSpatial_eq_fderiv, pdSpatial_eq_fderiv, pdSpatial_eq_fderiv]
  have hdχ : DifferentiableAt ℝ χ p := (hχ.differentiable (by decide)) p
  have hdφ : DifferentiableAt ℝ φ p := (hφ.differentiable (by decide)) p
  have hsmul := hdχ.hasFDerivAt.smul hdφ.hasFDerivAt
  rw [show (fun q => χ q • φ q) = χ • φ from rfl, hsmul.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  exact add_comm _ _

theorem memLp_of_isMeridTest_cellMeasure {c : ℝ} (hc : 0 < c) {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) : MemLp φ 2 (cellMeasure c) := by
  obtain ⟨M, hM⟩ := UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.merid_test_bounded
    c hc φ hφ
  obtain ⟨s0, s1, L, _hs0, hband⟩ := hφ.band
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK_compact : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_meas : MeasurableSet K := measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hcell_K : ∀ᵐ p ∂(cellMeasure c), φ p ≠ 0 → p ∈ K := by
    filter_upwards [ae_cell_cellMeasure c] with p hpcell hp0
    obtain ⟨hs, hη⟩ := hband p hp0
    exact ⟨hs, Ioc_subset_Icc_self hpcell.2.1, abs_le.1 hη⟩
  have hM0 : 0 ≤ max M 0 := le_max_right M 0
  refine ⟨hφ.smooth.continuous.measurable.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hle : ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((max M 0) ^ 2) * cellMeasure c K := by
    calc ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal ((max M 0) ^ 2)) p ∂(cellMeasure c) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hcell_K] with p hpK
          by_cases hp0 : φ p = 0
          · simp [hp0]
          · rw [indicator_of_mem (hpK hp0), ← ofReal_norm,
              ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
            exact ENNReal.ofReal_le_ofReal
              (pow_le_pow_left₀ (norm_nonneg _) ((hM p).trans (le_max_left M 0)) 2)
      _ = ENNReal.ofReal ((max M 0) ^ 2) * cellMeasure c K := by
          rw [lintegral_indicator hK_meas, setLIntegral_const]
  have hK_fin : cellMeasure c K < ⊤ :=
    lt_of_le_of_lt (Measure.restrict_le_self.trans le_rfl _) hK_compact.measure_lt_top
  have hprod_fin : ENNReal.ofReal ((max M 0) ^ 2) * cellMeasure c K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_fin
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle hprod_fin).ne

theorem integrable_inner_cellMeasure {c : ℝ} {f g : Profile → MeridC}
    (hf : MemLp f 2 (cellMeasure c)) (hg : MemLp g 2 (cellMeasure c)) :
    Integrable (fun p => inner ℂ (f p) (g p)) (cellMeasure c) :=
  (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Eventually.of_forall fun p => by
      simpa only [Pi.mul_apply] using norm_inner_le_norm (𝕜 := ℂ) (f p) (g p))

theorem isCylTest_clm_slice {c : ℝ} {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ)
    (L : MeridC →L[ℝ] ℝ) (s : ℝ) :
    UnforcedLeray.B0579.IsCylTest c (fun y : ℝ × ℝ => L (ψ (s, y))) where
  smooth := L.contDiff.comp (hψ.smooth.comp (contDiff_const.prodMk contDiff_id))
  periodic y := congrArg L (hψ.periodic (s, y))
  band := by
    obtain ⟨s0, s1, R, _hs0, hband⟩ := hψ.band
    refine ⟨R, fun y hy => ?_⟩
    have h0 : ψ (s, y) = 0 := by
      by_contra hne
      have := (hband (s, y) hne).2
      linarith
    simp [h0]

theorem pd_clm_slice {ψ : Profile → MeridC} (hψ : ContDiff ℝ ∞ ψ)
    (L : MeridC →L[ℝ] ℝ) (s : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    UnforcedLeray.B0579.pd j (fun z : ℝ × ℝ => L (ψ (s, z))) y =
      L (pdSpatial j ψ (s, y)) := by
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hdLψ : Differentiable ℝ (fun p : Profile => L (ψ p)) := L.differentiable.comp hdψ
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => L (ψ (s, z)))
      ((fderiv ℝ (fun p : Profile => L (ψ p)) (s, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y :=
    (hdLψ (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [UnforcedLeray.B0579.pd, h1.fderiv, pdSpatial_eq_fderiv]
  change fderiv ℝ (fun p : Profile => L (ψ p)) (s, y) (0, UnforcedLeray.B0579.dir j) =
    L (fderiv ℝ ψ (s, y) (0, UnforcedLeray.B0579.dir j))
  exact fderiv_clm_comp' L (hdψ (s, y)) (0, UnforcedLeray.B0579.dir j)

theorem slice_ibp_clm {c : ℝ} {f g : ℝ × ℝ → ℂ} {j : Fin 2}
    (hw : HasWeakCellDerivC c j f g) {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ)
    (L : MeridC →L[ℝ] ℝ) (s : ℝ) :
    IntegrableOn (fun y : ℝ × ℝ =>
        star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) +
        star (g y) * (L (ψ (s, y)) : ℂ)) (UnforcedLeray.B0579.cell c) ∧
      ∫ y in UnforcedLeray.B0579.cell c,
        (star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) +
          star (g y) * (L (ψ (s, y)) : ℂ)) = 0 := by
  have hcyl := isCylTest_clm_slice hψ L s
  obtain ⟨hI1, hI2⟩ := hw.1 _ hcyl
  have hEq := hw.2 _ hcyl
  have hpd_eq : ∀ y : ℝ × ℝ,
      (UnforcedLeray.B0579.pd j (fun z => L (ψ (s, z))) y : ℂ) =
        (L (pdSpatial j ψ (s, y)) : ℂ) := fun y =>
    congrArg Complex.ofReal (pd_clm_slice hψ.smooth L s j y)
  have hI1' : IntegrableOn (fun y => f y * (L (pdSpatial j ψ (s, y)) : ℂ))
      (UnforcedLeray.B0579.cell c) :=
    hI1.congr_fun (fun y _ => by dsimp only; rw [hpd_eq y]) (UnforcedLeray.B0579.measurableSet_cell c)
  have hsum : IntegrableOn (fun y =>
      f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ))
      (UnforcedLeray.B0579.cell c) := hI1'.add hI2
  have hsum_zero : ∫ y in UnforcedLeray.B0579.cell c,
      (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)) = 0 := by
    rw [integral_add hI1' hI2]
    have h1 : ∫ y in UnforcedLeray.B0579.cell c, f y * (L (pdSpatial j ψ (s, y)) : ℂ) =
        ∫ y in UnforcedLeray.B0579.cell c,
          f y * (UnforcedLeray.B0579.pd j (fun z => L (ψ (s, z))) y : ℂ) :=
      setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell c) fun y _ => by rw [hpd_eq y]
    rw [h1, hEq, neg_add_cancel]
  have hconj_pt : ∀ y : ℝ × ℝ,
      star (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)) =
        star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L (ψ (s, y)) : ℂ) := by
    intro y
    simp
  have hIconj0 : IntegrableOn (fun y =>
      star (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)))
      (UnforcedLeray.B0579.cell c) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hsum
  have hIconj : IntegrableOn (fun y =>
      star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L (ψ (s, y)) : ℂ))
      (UnforcedLeray.B0579.cell c) :=
    hIconj0.congr_fun (fun y _ => hconj_pt y) (UnforcedLeray.B0579.measurableSet_cell c)
  refine ⟨hIconj, ?_⟩
  calc ∫ y in UnforcedLeray.B0579.cell c,
          (star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L (ψ (s, y)) : ℂ))
      = ∫ y in UnforcedLeray.B0579.cell c,
          star (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)) :=
        setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell c) fun y _ =>
          (hconj_pt y).symm
    _ = star (∫ y in UnforcedLeray.B0579.cell c,
          (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ))) :=
        integral_conj
    _ = 0 := by rw [hsum_zero, star_zero]

theorem slice_ibp_coord {c : ℝ} {f g : ℝ × ℝ → ℂ} {j : Fin 2}
    (hw : HasWeakCellDerivC c j f g) {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ)
    (s : ℝ) (i : Fin 2) :
    ∫ y in UnforcedLeray.B0579.cell c,
      (star (f y) * pdSpatial j ψ (s, y) i + star (g y) * ψ (s, y) i) = 0 := by
  let L_re : MeridC →L[ℝ] ℝ :=
    Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  let L_im : MeridC →L[ℝ] ℝ :=
    Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  obtain ⟨hIre, hZre⟩ := slice_ibp_clm hw hψ L_re s
  obtain ⟨hIim, hZim⟩ := slice_ibp_clm hw hψ L_im s
  have hpt : ∀ y : ℝ × ℝ,
      star (f y) * pdSpatial j ψ (s, y) i + star (g y) * ψ (s, y) i =
        (star (f y) * (L_re (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L_re (ψ (s, y)) : ℂ)) +
        Complex.I * (star (f y) * (L_im (pdSpatial j ψ (s, y)) : ℂ) +
          star (g y) * (L_im (ψ (s, y)) : ℂ)) := by
    intro y
    have h1 : (L_re (pdSpatial j ψ (s, y)) : ℂ) + Complex.I * (L_im (pdSpatial j ψ (s, y)) : ℂ) =
        pdSpatial j ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    have h2 : (L_re (ψ (s, y)) : ℂ) + Complex.I * (L_im (ψ (s, y)) : ℂ) = ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    linear_combination -(star (f y)) * h1 - (star (g y)) * h2
  have hfun : (fun y : ℝ × ℝ => star (f y) * pdSpatial j ψ (s, y) i + star (g y) * ψ (s, y) i) =
      fun y =>
        (star (f y) * (L_re (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L_re (ψ (s, y)) : ℂ)) +
        Complex.I * (star (f y) * (L_im (pdSpatial j ψ (s, y)) : ℂ) +
          star (g y) * (L_im (ψ (s, y)) : ℂ)) := funext hpt
  rw [hfun, integral_add hIre (hIim.const_mul Complex.I), integral_const_mul, hZre, hZim]
  simp

theorem slice_ibp_merid {c : ℝ} {b : Chart → Fin 2 → ℂ} {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    {s : ℝ} {j : Fin 2}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun y => b (s, y) i) (fun y => Gr (s, y) i j))
    {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    ∫ y in UnforcedLeray.B0579.cell c,
      ∑ i : Fin 2, (star (b (s, y) i) * pdSpatial j ψ (s, y) i +
        star (Gr (s, y) i j) * ψ (s, y) i) = 0 := by
  let L_re (i : Fin 2) : MeridC →L[ℝ] ℝ :=
    Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  let L_im (i : Fin 2) : MeridC →L[ℝ] ℝ :=
    Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  have hI : ∀ i : Fin 2, IntegrableOn (fun y : ℝ × ℝ =>
      star (b (s, y) i) * pdSpatial j ψ (s, y) i +
        star (Gr (s, y) i j) * ψ (s, y) i) (UnforcedLeray.B0579.cell c) := by
    intro i
    obtain ⟨hIre, _⟩ := slice_ibp_clm (hw i j) hψ (L_re i) s
    obtain ⟨hIim, _⟩ := slice_ibp_clm (hw i j) hψ (L_im i) s
    refine (hIre.add (hIim.const_mul Complex.I)).congr_fun (fun y _ => ?_)
      (UnforcedLeray.B0579.measurableSet_cell c)
    simp only [Pi.add_apply]
    have h1 : (L_re i (pdSpatial j ψ (s, y)) : ℂ) +
        Complex.I * (L_im i (pdSpatial j ψ (s, y)) : ℂ) = pdSpatial j ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    have h2 : (L_re i (ψ (s, y)) : ℂ) + Complex.I * (L_im i (ψ (s, y)) : ℂ) = ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    linear_combination (star (b (s, y) i)) * h1 + (star (Gr (s, y) i j)) * h2
  rw [integral_finsetSum _ fun i _ => hI i]
  exact Finset.sum_eq_zero fun i _ => slice_ibp_coord (hw i j) hψ s i

theorem cellPt_cellPtInv_of_mem {c : ℝ} {x : Chart}
    (hx : x ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) :
    cellPt c (cellPtInv c x) = x := by
  rcases x with ⟨s, q, η⟩
  obtain ⟨_, ⟨hq1, hq2⟩, _⟩ := hx
  change (s, UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT c (N01.ctInvT c q), η) = (s, q, η)
  congr 2
  unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT N01.ctInvT
  split_ifs <;> first | rfl | (exfalso; linarith) | ring

theorem qPeriodic_cellPtInv' {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w)
    (x : Chart) : w (cellPtInv c x) = w x := by
  rcases x with ⟨s, q, η⟩
  unfold cellPtInv
  by_cases h : 0 < q
  · simp [h]
  · simp only [ite_eq_right_iff.2 (fun h' => False.elim (h h'))]
    exact hw (s, q, η)

/-- Main unconditional `(q, η)` integration-by-parts identity for `u = flatStressCutRep c χ W` and
`flatCutSpatialDeriv c χ W Gr j` on `cellMeasure c`. -/
theorem flatCutSpatialDeriv_ibp {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {W : HSpace c MeridC} {w_rep : Chart → Fin 2 → ℂ} {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hw_rep : w_rep =ᵐ[ageμ c (-3 / 2)] velF c W) (hE : IsEnergyFieldAE c w_rep Gr)
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr)
    (j : Fin 2) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (flatCutSpatialDeriv c χ W Gr j p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (flatStressCutRep c χ W p) (pdSpatial j φ p) ∂(cellMeasure c) := by
  let u := flatStressCutRep c χ W
  let dj := flatCutSpatialDeriv c χ W Gr j
  let ψ : Profile → MeridC := fun p => χ p • φ p
  have hψ : IsMeridTest c ψ := isMeridTest_smul_cutoff hσ hχ hφ
  have hpdφ : IsMeridTest c (pdSpatial j φ) := isMeridTest_pdSpatial hφ j
  have hpdψ : IsMeridTest c (pdSpatial j ψ) := isMeridTest_pdSpatial hψ j
  have hmem_u : MemLp u 2 (cellMeasure c) := memLp_flatStressCutRep hc hσ hσH hχ hm W
  have hmem_dj : MemLp dj 2 (cellMeasure c) :=
    memLp_flatCutSpatialDeriv hc hσ hσH hχ hm W hE.gradMeasurable hB0 hCal j
  have hmem_φ : MemLp φ 2 (cellMeasure c) := memLp_of_isMeridTest_cellMeasure hc hφ
  have hmem_pdφ : MemLp (pdSpatial j φ) 2 (cellMeasure c) :=
    memLp_of_isMeridTest_cellMeasure hc hpdφ
  have hInt_dj : Integrable (fun p => inner ℂ (dj p) (φ p)) (cellMeasure c) :=
    integrable_inner_cellMeasure hmem_dj hmem_φ
  have hInt_u : Integrable (fun p => inner ℂ (u p) (pdSpatial j φ p)) (cellMeasure c) :=
    integrable_inner_cellMeasure hmem_u hmem_pdφ
  let K_cell : Profile → ℂ := fun p =>
    inner ℂ (dj p) (φ p) + inner ℂ (u p) (pdSpatial j φ p)
  have hInt_K : Integrable K_cell (cellMeasure c) := hInt_dj.add hInt_u
  have hK_cell_eq : ∀ p ∈ cell c,
      K_cell p = inner ℂ ((W : Profile → MeridC) p) (pdSpatial j ψ p) +
        inner ℂ (flatGradCol c Gr j p) (ψ p) := by
    intro p hpcell
    have hdχ_eq : (if j = 0 then pdQ χ else pdEta χ) p = pdSpatial j χ p := by
      fin_cases j <;> rfl
    have hu_eq : u p = χ p • (W : Profile → MeridC) p := by
      dsimp only [u, flatStressCutRep]
      rw [periodize_of_mem hc _ hpcell]
    have hdj_eq : dj p = pdSpatial j χ p • (W : Profile → MeridC) p +
        χ p • flatGradCol c Gr j p := by
      dsimp only [dj, flatCutSpatialDeriv, flatStressCutRep, flatGradCutRep]
      rw [hdχ_eq, periodize_of_mem hc _ hpcell, periodize_of_mem hc _ hpcell]
    have hleib : pdSpatial j ψ p = pdSpatial j χ p • φ p + χ p • pdSpatial j φ p :=
      pdSpatial_smul_cutoff hχ.smooth hφ.smooth j p
    have hsmul_inner : ∀ (r : ℝ) (x y : MeridC), inner ℂ (r • x) y = inner ℂ x (r • y) := by
      intro r x y
      simp only [PiLp.inner_apply, WithLp.ofLp_smul, Pi.smul_apply, RCLike.inner_apply,
        Complex.real_smul, map_mul, Complex.conj_ofReal]
      congr 1; ext i; ring
    dsimp only [K_cell, ψ]
    rw [hdj_eq, hu_eq, hleib, inner_add_left, inner_add_right,
      hsmul_inner (pdSpatial j χ p), hsmul_inner (χ p), hsmul_inner (χ p)]
    ring
  let S : Set Chart := Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c
  have hSm : MeasurableSet S :=
    measurableSet_Ioi.prod (UnforcedLeray.B0579.measurableSet_cell c)
  have hmap : Measure.map (cellPtInv c) (volume.restrict S) = cellMeasure c :=
    N01.cellPtInv_map hc
  have hmp : MeasurePreserving (cellPtInv c) (volume.restrict S) (cellMeasure c) :=
    ⟨measurable_cellPtInv c, hmap⟩
  have hInt_comp : IntegrableOn (K_cell ∘ cellPtInv c) S :=
    (hmp.integrable_comp hInt_K.aestronglyMeasurable).2 hInt_K
  have hVal_map : ∫ p, K_cell p ∂(cellMeasure c) = ∫ x in S, K_cell (cellPtInv c x) := by
    rw [← hmap]
    exact integral_map (measurable_cellPtInv c).aemeasurable
      (by rw [hmap]; exact hInt_K.aestronglyMeasurable)
  let K_chart : Chart → ℂ := fun x =>
    ∑ i : Fin 2, (star (w_rep x i) * pdSpatial j ψ x i + star (Gr x i j) * ψ x i)
  have hac := volCyl_ac_ageμ hc (-3 / 2)
  have hw_ae_S : w_rep =ᵐ[volume.restrict S] velF c (W : Profile → MeridC) :=
    hac.ae_le hw_rep
  have hcellPtInv_mem : ∀ x ∈ S, cellPtInv c x ∈ cell c := by
    rintro ⟨s, q, η⟩ ⟨hs, ⟨hq1, hq2⟩, _⟩
    refine ⟨hs, ?_, trivial⟩
    change N01.ctInvT c q ∈ Ioc 0 c
    unfold N01.ctInvT
    split_ifs with hq0
    · exact ⟨hq0, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hcongr_S : (K_cell ∘ cellPtInv c) =ᵐ[volume.restrict S] K_chart := by
    filter_upwards [ae_restrict_mem hSm, hw_ae_S] with x hx hwx
    simp only [Function.comp_apply]
    rw [hK_cell_eq (cellPtInv c x) (hcellPtInv_mem x hx),
      qPeriodic_cellPtInv' hpdψ.periodic x, qPeriodic_cellPtInv' hψ.periodic x]
    have hgrad_eq : flatGradCol c Gr j (cellPtInv c x) =
        WithLp.toLp 2 (fun i : Fin 2 => Gr x i j) := by
      unfold flatGradCol
      rw [cellPt_cellPtInv_of_mem hx]
    rw [hgrad_eq]
    simp only [K_chart, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]
    have hw0 : (W : Profile → MeridC) (cellPtInv c x) 0 = w_rep x 0 :=
      (congrFun hwx 0).symm
    have hw1 : (W : Profile → MeridC) (cellPtInv c x) 1 = w_rep x 1 :=
      (congrFun hwx 1).symm
    rw [hw0, hw1]
    simp only [Complex.star_def]
    ring
  have hInt_chart : IntegrableOn K_chart S := hInt_comp.congr hcongr_S
  have hVal_chart : ∫ p, K_cell p ∂(cellMeasure c) = ∫ x in S, K_chart x := by
    rw [hVal_map]
    exact integral_congr_ae hcongr_S
  have hμ : (volume : Measure Chart).restrict S =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    dsimp only [S]
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hInt_prod : Integrable K_chart
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (UnforcedLeray.B0579.cell c))) := by
    rw [← hμ]
    exact hInt_chart
  have hK_zero : ∫ p, K_cell p ∂(cellMeasure c) = 0 := by
    rw [hVal_chart, show ∫ x in S, K_chart x = ∫ x, K_chart x ∂(volume.restrict S) from rfl,
      hμ, integral_prod _ hInt_prod]
    have hae_slice : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ∫ y in UnforcedLeray.B0579.cell c, K_chart (s, y) = 0 := by
      filter_upwards [ae_restrict_of_ae hE.weakGradAE, ae_restrict_mem measurableSet_Ioi]
        with s hs hs0
      exact slice_ibp_merid (hs hs0) hψ
    rw [integral_congr_ae hae_slice, integral_zero]
  have hadd_zero : (∫ p, inner ℂ (dj p) (φ p) ∂(cellMeasure c)) +
      ∫ p, inner ℂ (u p) (pdSpatial j φ p) ∂(cellMeasure c) = 0 := by
    rw [← integral_add hInt_dj hInt_u]
    exact hK_zero
  exact eq_neg_of_add_eq_zero_left hadd_zero

theorem isEnergyFieldAE_of_causal {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : Chart → Fin 2 → Fin 2 → ℂ} {b : Chart → Fin 2 → ℂ} {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hsol : IsCausalEnergySolution c ν μ vel F b Gr) :
    IsEnergyFieldAE c b Gr :=
  ⟨hsol.measurable, hsol.gradMeasurable, hsol.energyLoc, hsol.zeroEntrance,
    Eventually.of_forall hsol.divFree, Eventually.of_forall hsol.weakGrad⟩

end N05_4_1Aux

open N05_4_1Aux

/-! ### 5. Leaf obligations (`PartII-a:N05/4/1/1`, `PartII-a:N05/4/1/2`) and conditional assembly -/

/-- **Leaf 1 (`PartII-a:N05/4/1/1`): 1D periodic `q`-shift difference-quotient bound on `cellMeasure c`**
(source `the November 2 reference manuscript`,
lines 1757–1758, 1785–1788): for any measurable `c`-periodic box-supported fields
`u, dq : Profile → MeridC` in `MemLp · 2 (cellMeasure c)` satisfying `ibp_q` against every
`IsMeridTest c φ`, the `L²(cellMeasure c)` squared norm of `u (shiftQ h p) - u p` is bounded for
`h ∈ Icc (-1 : ℝ) 1` by `(cellL2Norm c dq) ^ 2 * |h|`. -/
def CellWeakQDiffQuotient : Prop :=
  ∀ (c σ H1 L1 : ℝ), 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 →
    ∀ (u dq : Profile → MeridC),
      Measurable u → Measurable dq →
      QPeriodic c u → QPeriodic c dq →
      (∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      (∀ p : Profile, dq p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      MemLp u 2 (cellMeasure c) →
      MemLp dq 2 (cellMeasure c) →
      (∀ φ : Profile → MeridC, IsMeridTest c φ →
        ∫ p, inner ℂ (dq p) (φ p) ∂(cellMeasure c) =
          -∫ p, inner ℂ (u p) (pdQ φ p) ∂(cellMeasure c)) →
      ∀ h ∈ Icc (-1 : ℝ) 1,
        ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤
          (cellL2Norm c dq) ^ 2 * |h|

/-- **Leaf 2 (`PartII-a:N05/4/1/2`): 1D compact-support `η`-shift difference-quotient bound on `cellMeasure c`**
(source `the November 2 reference manuscript`,
lines 1757–1758, 1785–1788): for any measurable `c`-periodic box-supported fields
`u, deta : Profile → MeridC` in `MemLp · 2 (cellMeasure c)` satisfying `ibp_eta` against every
`IsMeridTest c φ`, the `L²(cellMeasure c)` squared norm of `u (shiftEta h p) - u p` is bounded for
`h ∈ Icc (-1 : ℝ) 1` by `(cellL2Norm c deta) ^ 2 * |h|`. -/
def CellWeakEtaDiffQuotient : Prop :=
  ∀ (c σ H1 L1 : ℝ), 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 →
    ∀ (u deta : Profile → MeridC),
      Measurable u → Measurable deta →
      QPeriodic c u → QPeriodic c deta →
      (∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      (∀ p : Profile, deta p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      MemLp u 2 (cellMeasure c) →
      MemLp deta 2 (cellMeasure c) →
      (∀ φ : Profile → MeridC, IsMeridTest c φ →
        ∫ p, inner ℂ (deta p) (φ p) ∂(cellMeasure c) =
          -∫ p, inner ℂ (u p) (pdEta φ p) ∂(cellMeasure c)) →
      ∀ h ∈ Icc (-1 : ℝ) 1,
        ∫ p, ‖u (shiftEta h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤
          (cellL2Norm c deta) ^ 2 * |h|

/-- **Conditional assembly of `FlatStressSpatialHolderHalf` (`PartII-a:N05/4/1`)** from
`CellWeakQDiffQuotient` (`PartII-a:N05/4/1/1`) and `CellWeakEtaDiffQuotient` (`PartII-a:N05/4/1/2`),
using the unconditional `(q, η)` integration by parts `flatCutSpatialDeriv_ibp`,
`N05_4Aux.flatSmoothEnergyAndGrad`, `cellL2Norm_flatCutSpatialDeriv_le_gamma`, and the
density extension `integral_shift_sub_sq_le_of_testSub` from `N01.testSub c` to `HTSpace c`. -/
theorem flatStressSpatialHolderHalf_of (hDiffQ : CellWeakQDiffQuotient)
    (hDiffEta : CellWeakEtaDiffQuotient) :
    FlatStressSpatialHolderHalf := by
  refine ⟨3, 6, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ _hχ1 hm _B _hB μ hμM hμγ S0 hS0 F
  have hμ_pos : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  constructor
  · intro h _hh
    have hK0 : 0 ≤ (3 * Gam ^ 3) ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
    have hext := integral_shift_sub_sq_le_of_testSub hc hν hσ hσH hχ hm hμ_pos hS0
      (measurable_shiftQ h)
      (fun f hf hper _ => (lintegral_shiftQ_eq hc h hf hper).le)
      hK0
      (fun M' hM' x G hxM' hG => by
        obtain ⟨b, Gr, hbv, hsol, hH, hCal⟩ :=
          flatSmoothEnergyAndGrad hc hν hμ_pos hM' x G hxM' hG
        have hB0 : 0 ≤ ν⁻¹ * (Real.sqrt 2 * ‖x‖) := by positivity
        have hibp0 : ∀ φ : Profile → MeridC, IsMeridTest c φ →
            ∫ p, inner ℂ (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 0 p) (φ p)
                ∂(cellMeasure c) =
              -∫ p, inner ℂ (flatStressCutRep c χ (T0flat hc ν μ G) p) (pdQ φ p)
                ∂(cellMeasure c) := fun φ hφ =>
          flatCutSpatialDeriv_ibp hc hσ hσH hχ hm hbv (isEnergyFieldAE_of_causal hsol) hB0 hCal 0 hφ
        have hdq := hDiffQ c σ H1 L1 hc hσ hσH hL1
          (flatStressCutRep c χ (T0flat hc ν μ G))
          (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 0)
          (measurable_flatStressCutRep c hm (T0flat hc ν μ G))
          (measurable_flatCutSpatialDeriv hχ hm (T0flat hc ν μ G) hsol.gradMeasurable 0)
          (flatStressCutRep_periodic hc hχ (T0flat hc ν μ G))
          (flatCutSpatialDeriv_periodic hc hχ (T0flat hc ν μ G) Gr 0)
          (flatStressCutRep_support hχ (T0flat hc ν μ G))
          (flatCutSpatialDeriv_support hχ (T0flat hc ν μ G) Gr 0)
          (memLp_flatStressCutRep hc hσ hσH hχ hm (T0flat hc ν μ G))
          (memLp_flatCutSpatialDeriv hc hσ hσH hχ hm (T0flat hc ν μ G) hsol.gradMeasurable hB0 hCal 0)
          hibp0 h _hh
        have hgrad := cellL2Norm_flatCutSpatialDeriv_le_gamma χ χ1 hν hc hσ hσH hL1 hγ
          hχ hm hμM hμγ x G hsol.gradMeasurable hH hCal 0
        have hgrad_sq : (cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 0)) ^ 2 ≤
            (3 * Gam ^ 3) ^ 2 * ‖x‖ ^ 2 := by
          calc (cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 0)) ^ 2
              ≤ (3 * Gam ^ 3 * ‖x‖) ^ 2 :=
                pow_le_pow_left₀ (cellL2Norm_nonneg c _) hgrad 2
            _ = (3 * Gam ^ 3) ^ 2 * ‖x‖ ^ 2 := by ring
        calc ∫ p, ‖flatStressCutRep c χ (T0flat hc ν μ G) (shiftQ h p) -
                flatStressCutRep c χ (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c)
            ≤ (cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 0)) ^ 2 * |h| := hdq
          _ ≤ ((3 * Gam ^ 3) ^ 2 * ‖x‖ ^ 2) * |h| :=
              mul_le_mul_of_nonneg_right hgrad_sq (abs_nonneg h)
          _ = ((3 * Gam ^ 3) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring)
      F
    calc ∫ p, ‖flatStressCutRep c χ (S0 F) (shiftQ h p) -
            flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c)
        ≤ 2 * (((3 * Gam ^ 3) ^ 2 * |h|) * ‖F‖ ^ 2) := hext
      _ ≤ (6 * Gam ^ 3 * ‖F‖) ^ 2 * |h| := by
          have : 0 ≤ ‖F‖ ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
          have : 0 ≤ Gam ^ 6 := pow_nonneg hG0 6
          nlinarith
  · intro h _hh
    have hK0 : 0 ≤ (3 * Gam ^ 3) ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
    have hext := integral_shift_sub_sq_le_of_testSub hc hν hσ hσH hχ hm hμ_pos hS0
      (measurable_shiftEta h)
      (fun f hf _ _ => (lintegral_shiftEta_eq c h hf).le)
      hK0
      (fun M' hM' x G hxM' hG => by
        obtain ⟨b, Gr, hbv, hsol, hH, hCal⟩ :=
          flatSmoothEnergyAndGrad hc hν hμ_pos hM' x G hxM' hG
        have hB0 : 0 ≤ ν⁻¹ * (Real.sqrt 2 * ‖x‖) := by positivity
        have hibp1 : ∀ φ : Profile → MeridC, IsMeridTest c φ →
            ∫ p, inner ℂ (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 1 p) (φ p)
                ∂(cellMeasure c) =
              -∫ p, inner ℂ (flatStressCutRep c χ (T0flat hc ν μ G) p) (pdEta φ p)
                ∂(cellMeasure c) := fun φ hφ =>
          flatCutSpatialDeriv_ibp hc hσ hσH hχ hm hbv (isEnergyFieldAE_of_causal hsol) hB0 hCal 1 hφ
        have hde := hDiffEta c σ H1 L1 hc hσ hσH hL1
          (flatStressCutRep c χ (T0flat hc ν μ G))
          (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 1)
          (measurable_flatStressCutRep c hm (T0flat hc ν μ G))
          (measurable_flatCutSpatialDeriv hχ hm (T0flat hc ν μ G) hsol.gradMeasurable 1)
          (flatStressCutRep_periodic hc hχ (T0flat hc ν μ G))
          (flatCutSpatialDeriv_periodic hc hχ (T0flat hc ν μ G) Gr 1)
          (flatStressCutRep_support hχ (T0flat hc ν μ G))
          (flatCutSpatialDeriv_support hχ (T0flat hc ν μ G) Gr 1)
          (memLp_flatStressCutRep hc hσ hσH hχ hm (T0flat hc ν μ G))
          (memLp_flatCutSpatialDeriv hc hσ hσH hχ hm (T0flat hc ν μ G) hsol.gradMeasurable hB0 hCal 1)
          hibp1 h _hh
        have hgrad := cellL2Norm_flatCutSpatialDeriv_le_gamma χ χ1 hν hc hσ hσH hL1 hγ
          hχ hm hμM hμγ x G hsol.gradMeasurable hH hCal 1
        have hgrad_sq : (cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 1)) ^ 2 ≤
            (3 * Gam ^ 3) ^ 2 * ‖x‖ ^ 2 := by
          calc (cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 1)) ^ 2
              ≤ (3 * Gam ^ 3 * ‖x‖) ^ 2 :=
                pow_le_pow_left₀ (cellL2Norm_nonneg c _) hgrad 2
            _ = (3 * Gam ^ 3) ^ 2 * ‖x‖ ^ 2 := by ring
        calc ∫ p, ‖flatStressCutRep c χ (T0flat hc ν μ G) (shiftEta h p) -
                flatStressCutRep c χ (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c)
            ≤ (cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ G) Gr 1)) ^ 2 * |h| := hde
          _ ≤ ((3 * Gam ^ 3) ^ 2 * ‖x‖ ^ 2) * |h| :=
              mul_le_mul_of_nonneg_right hgrad_sq (abs_nonneg h)
          _ = ((3 * Gam ^ 3) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring)
      F
    calc ∫ p, ‖flatStressCutRep c χ (S0 F) (shiftEta h p) -
            flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c)
        ≤ 2 * (((3 * Gam ^ 3) ^ 2 * |h|) * ‖F‖ ^ 2) := hext
      _ ≤ (6 * Gam ^ 3 * ‖F‖) ^ 2 * |h| := by
          have : 0 ≤ ‖F‖ ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
          have : 0 ≤ Gam ^ 6 := pow_nonneg hG0 6
          nlinarith

end UnforcedLeray.Short.PartIIa
