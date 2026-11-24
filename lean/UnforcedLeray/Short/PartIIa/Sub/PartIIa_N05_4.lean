import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatReduction
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatColumnC
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatVelTransport
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatBlkTransport
import UnforcedLeray.Short.PartIIa.Sub.N01.Completion

/-!
# `Sub/PartII-a_N05_4`: Decomposition of `StressFlatLocalH14` (`PartII-a:N05/4`)

Source of record: `the November 2 reference manuscript`,
lines 1757–1764, 1785–1788 (`near:local-smoothing`, flat stress case).

## Structure of this file

1. **Unconditional flat smooth-test energy + gradient dissipation theorem**
   (`flatSmoothEnergyAndGrad`): combines `N01.flatColumnC` (`Sub/N01/FlatColumnC.lean`),
   `Delta.freeEnergyFlat_of (Delta.freeEnergyFlatSq_of IIIa.weightedEnergyIdentity)` (both the
   `H`-norm bound and the `L²(s^{-1/2})` gradient bound `tCalNorm c Gr ≤ ν⁻¹ tCalNorm c (tblkF c M)`),
   `N01.flatVelTransport`, and `N01.flatBlkTransport` on smooth tensor tests `M`.
2. **Unconditional `S_0` operator bound on all `F ∈ H_T`** (`stressMap_flat_norm_le`): uses density
   of smooth tensor tests (`N01.testSub_dense`) to prove
   `‖S0 F‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖` for every `S0` satisfying
   `IsStressMap c 0 (T0flat hc ν μ) S0`.
3. **Concrete box-supported periodic representative `flatStressCutRep`**:
   `flatStressCutRep c χ W p := χ p • B0220.periodize c (W : Profile → MeridC) p`, with unconditional
   proofs of a.e. agreement with `mulChi (measureH c) χ hm hB W` (`flatStressCutRep_ae_eq`),
   `c`-periodicity in `q` (`flatStressCutRep_periodic`), box support `σ ≤ s ≤ H1`, `|η| ≤ L1`
   (`flatStressCutRep_support`), Borel measurability (`measurable_flatStressCutRep`),
   `AEStronglyMeasurable` of the `L²(cellMeasure c)` difference-quotient functions in
   `(shiftS, shiftQ, shiftEta)`, and `cellL2Norm c (flatStressCutRep c χ (S0 F)) ≤ Gamma^3 * ‖F‖`.
4. **Two leaf obligations and conditional assembly (`stressFlatLocalH14_of`)**:
   * `FlatStressSpatialHolderHalf` (`PartII-a:N05/4/1`): spatial `(shiftQ, shiftEta)`
     1/2-Hölder `L²(cellMeasure c)` translation bounds on `flatStressCutRep c χ (S0 F)` from the
     flat causal gradient bound of `flatSmoothEnergyAndGrad`;
   * `FlatStressAgeHolderHalf` (`PartII-a:N05/4/2`): age `shiftS` 1/2-Hölder `L²(cellMeasure c)`
     translation bound on `flatStressCutRep c χ (S0 F)` from the flat equation
     `(∂_s + μ/s - νΔ_{q,η}) b = P_0 div_0 M` (`∂_s u ∈ L²_s H⁻¹_{q,η}`) and
     `‖|∂_s|^{1/2} u‖_2² ≤ ‖∂_s u‖_{L²_s H⁻¹} ‖u‖_{L²_s H¹}` (source lines 1758–1763);
   assembled via `hasCellH14_of_holderHalf` (`Sub/PartII-a_N05.lean`) and composed in
   `PartII-a:N05/4`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)

/-- Concrete `c`-periodic representative of `mulChi (measureH c) χ hm hB W` supported in the
observation box `σ ≤ s ≤ H1`, `|η| ≤ L1`: periodise `W` in `q` from the cell `(0, c]` and
multiply pointwise by the smooth periodic cutoff `χ`. -/
def flatStressCutRep (c : ℝ) (χ : Profile → ℝ) (W : HSpace c MeridC) (p : Profile) : MeridC :=
  χ p • periodize c (W : Profile → MeridC) p

namespace N05_4Aux

/-! ### 1. Unconditional flat smooth-test energy and gradient dissipation bound -/

/-- Unconditional flat smooth-test bound (`N01.FlatSmoothBound`) assembled from `N01.flatColumnC`,
`N01.flatVelTransport`, and `N01.flatBlkTransport`. -/
theorem flatSmoothBound : N01.FlatSmoothBound :=
  N01.flatSmoothBound_of N01.flatColumnC N01.flatVelTransport N01.flatBlkTransport

/-- For every smooth tensor test `M` with `F =ᵐ[measureHT c] M` and `G =ᵐ[measureH c] s div_0 M`,
`T0flat hc ν μ G` (transported to the recentred chart by `Delta.velF`) has a causal zero-entrance
energy solution `(b, Gr)` of the flat equation `(∂_s + μ/s - νΔ_{q,η}) b = P_0 div_0 M` satisfying
both the `H` energy bound and the `L²(s^{-1/2})` spatial gradient bound
`√c ‖Gr‖_𝒯 ≤ ν⁻¹ √2 ‖F‖_{H_T}` (source lines 1684–1689, 1757–1758). -/
theorem flatSmoothEnergyAndGrad {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) {M : Profile → TensorVal} (hM : IsTensorTest c M)
    (F : HTSpace c) (G : HSpace c MeridC)
    (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] M)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p)) :
    ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
      b =ᵐ[UnforcedLeray.Axi.ageμ c (-3 / 2)]
          UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c (T0flat hc ν μ G) ∧
      UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
          (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) b Gr ∧
      ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ ∧
      ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.tCalNorm c Gr ≤
        ENNReal.ofReal (ν⁻¹ * (Real.sqrt 2 * ‖F‖)) := by
  obtain ⟨b, Gr, hbv, hsol⟩ := N01.flatColumnC c ν hc hν μ hγ M hM G hG
  have hmeas : ∀ i j, Measurable fun p =>
      UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M p i j := fun i j =>
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.fsf_measurable_tblkF
      hM.smooth.continuous.measurable i j
  have hblk := N01.flatBlkTransport c hc M F hF
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hfin : UnforcedLeray.Short.IIIa.tCalNorm c
      (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) < ⊤ := by
    have h1 := lt_of_le_of_lt hblk ENNReal.ofReal_lt_top
    rcases ENNReal.mul_lt_top_iff.1 h1 with h | h | h
    · exact h.2
    · exact absurd h (by rw [ENNReal.ofReal_eq_zero, not_le]; exact hsc)
    · rw [h]; exact ENNReal.zero_lt_top
  have hE := (UnforcedLeray.Short.PartIIIb.NearInst.Delta.freeEnergyFlat_of
    (UnforcedLeray.Short.PartIIIb.NearInst.Delta.freeEnergyFlatSq_of
      UnforcedLeray.Short.IIIa.weightedEnergyIdentity) c ν μ hc hν hγ _ hmeas hfin b Gr hsol).2
  have hH := flatSmoothBound ν c hc hν μ hγ M hM F G hF hG
  refine ⟨b, Gr, hbv, hsol, hH, ?_⟩
  rw [ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.tCalNorm c Gr
      ≤ ENNReal.ofReal (Real.sqrt c) * (ENNReal.ofReal ν⁻¹ * UnforcedLeray.Short.IIIa.tCalNorm c
          (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M)) := by gcongr
    _ = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.tCalNorm c
          (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M)) := by ring
    _ ≤ ENNReal.ofReal ν⁻¹ * ENNReal.ofReal (Real.sqrt 2 * ‖F‖) := by gcongr

/-- Unconditional `H`-norm bound on any flat stress map `S0` by density of `N01.testSub c`. -/
theorem stressMap_flat_norm_le {ν c : ℝ} (hc : 0 < c) (hν : 0 < ν) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) {S0 : HTSpace c →L[ℂ] HSpace c MeridC}
    (hS0 : IsStressMap c 0 (T0flat hc ν μ) S0) (F : HTSpace c) :
    ‖S0 F‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by
  refine isClosed_property (N01.testSub_dense c hc)
    (isClosed_le S0.continuous.norm (continuous_const.mul continuous_norm)) (fun x => ?_) F
  obtain ⟨M, hM, hFM⟩ := x.2
  let G : HSpace c MeridC :=
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c 0 hc M hM).toLp _
  have hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) :=
    MemLp.coeFn_toLp _
  show ‖S0 (x : HTSpace c)‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖(x : HTSpace c)‖
  rw [hS0 M hM x.1 G hFM hG]
  exact flatSmoothBound ν c hc hν μ hγ M hM x.1 G hFM hG

/-! ### 2. Properties of `flatStressCutRep` -/

theorem flatStressCutRep_ae_eq {c : ℝ} (hc : 0 < c) (χ : Profile → ℝ) (hm : Measurable χ)
    {B : ℝ} (hB : ∀ p, |χ p| ≤ B) (W : HSpace c MeridC) :
    (mulChi (measureH c) χ hm hB W : Profile → MeridC) =ᵐ[measureH c]
      flatStressCutRep c χ W := by
  have h1 : (mulChi (measureH c) χ hm hB W : Profile → MeridC) =ᵐ[measureH c]
      fun p => χ p • (W : Profile → MeridC) p :=
    (memLp_chi_smul (measureH c) χ hm hB (Lp.memLp W)).coeFn_toLp
  filter_upwards [h1, ae_cell_measureH c] with p hp hpcell
  rw [hp, flatStressCutRep, periodize_of_mem hc (W : Profile → MeridC) hpcell]

theorem flatStressCutRep_periodic {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC) :
    QPeriodic c (flatStressCutRep c χ W) := by
  intro p
  simp only [flatStressCutRep, hχ.periodic p, qPeriodic_periodize hc (W : Profile → MeridC) p]

theorem flatStressCutRep_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC) (p : Profile)
    (hp : flatStressCutRep c χ W p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  refine hχ.support p ?_
  intro h0
  apply hp
  simp [flatStressCutRep, h0]

theorem measurable_periodize_meridC (c : ℝ) {f : Profile → MeridC} (hf : Measurable f) :
    Measurable (periodize c f) := by
  unfold periodize
  exact hf.comp (measurable_fst.prodMk
    (((measurable_reduceIoc c).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

theorem measurable_flatStressCutRep (c : ℝ) {χ : Profile → ℝ} (hm : Measurable χ)
    (W : HSpace c MeridC) :
    Measurable (flatStressCutRep c χ W) :=
  hm.smul (measurable_periodize_meridC c (Lp.stronglyMeasurable W).measurable)

theorem measurable_shiftS_uncurry :
    Measurable (fun hp : ℝ × Profile => shiftS hp.1 hp.2) := by
  unfold shiftS
  exact ((measurable_fst.comp measurable_snd).add measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_shiftQ_uncurry :
    Measurable (fun hp : ℝ × Profile => shiftQ hp.1 hp.2) := by
  unfold shiftQ
  exact (measurable_fst.comp measurable_snd).prodMk
    (((measurable_fst.comp (measurable_snd.comp measurable_snd)).add measurable_fst).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_shiftEta_uncurry :
    Measurable (fun hp : ℝ × Profile => shiftEta hp.1 hp.2) := by
  unfold shiftEta
  exact (measurable_fst.comp measurable_snd).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_snd)).add measurable_fst))

theorem aestronglyMeasurable_diff_integral (c : ℝ) {shift : ℝ → Profile → Profile}
    (hshift : Measurable (fun hp : ℝ × Profile => shift hp.1 hp.2))
    {u : Profile → MeridC} (hu : Measurable u) :
    AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)) := by
  have : SFinite (cellMeasure c) := by unfold cellMeasure; infer_instance
  have hprod : Measurable (fun hp : ℝ × Profile => ‖u (shift hp.1 hp.2) - u hp.2‖ ^ 2) :=
    (((hu.comp hshift).sub (hu.comp measurable_snd)).norm).pow_const 2
  have hsm : StronglyMeasurable (fun h : ℝ => ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c)) :=
    hprod.stronglyMeasurable.integral_prod_right'
  exact hsm.aestronglyMeasurable

/-- Pointwise bound `|χ p| ≤ cNorm8 χ` for any near cutoff `χ` (`IsNearCutoff c σ H1 L1 χ`). -/
theorem abs_le_cNorm8_of_nearCutoff {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    |χ p| ≤ cNorm8 χ := by
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hχ.smooth.continuous.continuousOn
  have hbdd : BddAbove (range fun q : Profile => ‖iteratedFDeriv ℝ 0 χ q‖) := by
    refine ⟨max C0 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : χ q' = χ q := periodic_reduceIoc_eq χ hχ.periodic q.1 q.2.1 q.2.2
    rw [← hpeq]
    by_cases h0 : χ q' = 0
    · simp [h0]
    · obtain ⟨hs1, hs2, hη⟩ := hχ.support q' h0
      have hq' : q' ∈ K := ⟨⟨hs1, hs2⟩, Ioc_subset_Icc_self (reduceIoc_mem hc q.2.1), abs_le.1 hη⟩
      have hle : |χ q'| ≤ C0 := by simpa [Real.norm_eq_abs] using hC0 q' hq'
      exact hle.trans (le_max_left C0 0)
  have h0 : |χ p| = ‖iteratedFDeriv ℝ 0 χ p‖ := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rw [h0]
  calc ‖iteratedFDeriv ℝ 0 χ p‖
      ≤ ⨆ q, ‖iteratedFDeriv ℝ 0 χ q‖ := le_ciSup hbdd p
    _ ≤ ∑ k ∈ Finset.range 9, ⨆ q, ‖iteratedFDeriv ℝ k χ q‖ :=
        Finset.single_le_sum (fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ = cNorm8 χ := rfl

theorem flatStressCutRep_enorm_sq_le {c σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC) (p : Profile) :
    ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * (weightH p * ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ)) := by
  by_cases hp0 : flatStressCutRep c χ W p = 0
  · simp [hp0]
  · obtain ⟨hs1, hs2, _⟩ := flatStressCutRep_support hχ W p hp0
    have hs_pos : 0 < p.1 := lt_of_lt_of_le hσ hs1
    have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
    have h1H1 : 1 ≤ 1 + H1 := by linarith
    have hp1H1 : p.1 ≤ 1 + H1 := by linarith
    have hrpow : p.1 ^ (3 / 2 : ℝ) ≤ (1 + H1) ^ 2 := by
      calc p.1 ^ (3 / 2 : ℝ)
          ≤ (1 + H1) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp1H1 (by norm_num)
        _ ≤ (1 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1H1 (by norm_num)
        _ = (1 + H1) ^ 2 := Real.rpow_two (1 + H1)
    have h1 : 1 ≤ (1 + H1) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) := by
      calc (1 : ℝ)
          = p.1 ^ (3 / 2 : ℝ) * p.1 ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_add hs_pos]; norm_num
        _ ≤ (1 + H1) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + H1) ^ 2) * weightH p := by
      unfold weightH
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h1
    calc ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ)
        = 1 * ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) := (one_mul _).symm
      _ ≤ (ENNReal.ofReal ((1 + H1) ^ 2) * weightH p) *
            ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) := by gcongr
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ)) := mul_assoc _ _ _

theorem lintegral_flatStressCutRep_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
  let u := flatStressCutRep c χ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono (flatStressCutRep_enorm_sq_le hσ hσH hχ W)
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ ((measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ))))
      _ = ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  let U₀ := mulChi (measureH c) χ hm (abs_le_cNorm8_of_nearCutoff hc hχ) W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    flatStressCutRep_ae_eq hc χ hm (abs_le_cNorm8_of_nearCutoff hc hχ) W
  have hU0_norm : ‖U₀‖ ≤ cNorm8 χ * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) χ hm
      (abs_le_cNorm8_of_nearCutoff hc hχ) (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) χ hm
      (abs_le_cNorm8_of_nearCutoff hc hχ) (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_le_cNorm8_of_nearCutoff hc hχ p) (norm_nonneg _)
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
      ≤ ENNReal.ofReal ((1 + H1) ^ 2) * ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) := by
        refine hstep1.trans ?_
        gcongr
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Unconditional `L²(cellMeasure c)` membership of `flatStressCutRep c χ W`. -/
theorem memLp_flatStressCutRep {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (W : HSpace c MeridC) :
    MemLp (flatStressCutRep c χ W) 2 (cellMeasure c) := by
  refine ⟨(measurable_flatStressCutRep c hm W).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hle := lintegral_flatStressCutRep_sq_le hc hσ hσH hχ hm W
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne

/-- Unconditional unweighted `L²(cellMeasure c)` norm bound on `flatStressCutRep c χ W`. -/
theorem cellL2Norm_flatStressCutRep_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (W : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c χ W) ≤ (1 + H1) * cNorm8 χ * ‖W‖ := by
  let u := flatStressCutRep c χ W
  have hmem := memLp_flatStressCutRep hc hσ hσH hχ hm W
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
    exact lintegral_flatStressCutRep_sq_le hc hσ hσH hχ hm W
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * ‖W‖ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

/-- Unconditional `Gamma^3` bound on `cellL2Norm c (flatStressCutRep c χ (S0 F))`. -/
theorem cellL2Norm_flatStressCutRep_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) {S0 : HTSpace c →L[ℂ] HSpace c MeridC}
    (hS0 : IsStressMap c 0 (T0flat hc ν μ) S0) (F : HTSpace c) :
    cellL2Norm c (flatStressCutRep c χ (S0 F)) ≤
      Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖F‖ := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hG0 : 0 ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ G := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ G ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    have h3 : (Real.sqrt (γs * ν))⁻¹ ≤ G :=
      (abs_le_of_sq_le_sq' h2 hG0).2
    exact h1.trans h3
  have hS0F := stressMap_flat_norm_le hc hν (lt_of_lt_of_le hγ hμγ) hS0 F
  have hL2 := cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm (S0 F)
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  calc cellL2Norm c (flatStressCutRep c χ (S0 F))
      ≤ (1 + H1) * cNorm8 χ * ‖S0 F‖ := hL2
    _ ≤ (1 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :=
        mul_le_mul_of_nonneg_left hS0F (mul_nonneg (by linarith) (cNorm8_nonneg χ))
    _ = (1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by ring
    _ ≤ G * G * G * ‖F‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
        refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
          (by positivity) (mul_nonneg hG0 hG0)
    _ = G ^ 3 * ‖F‖ := by ring

theorem gamma_ge_one {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) :
    1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

end N05_4Aux

open N05_4Aux

/-! ### 3. Self-contained 1/2-Hölder translation leaves and assembly of `StressFlatLocalH14` -/

/-- **Leaf 1 (`PartII-a:N05/4/1`): spatial `(q, η)` 1/2-Hölder `L²(cellMeasure c)` translation
bound for `χ S_0 F`**
(source `the November 2 reference manuscript`,
lines 1757–1758, 1785–1788): from the flat causal energy and gradient bound
(`N05_4Aux.flatSmoothEnergyAndGrad`), the localised flat stress output
`u = flatStressCutRep c χ (S0 F)` satisfies the `O(|h|^{1/2})` spatial difference-quotient bounds
in `shiftQ` and `shiftEta`. -/
def FlatStressSpatialHolderHalf : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (_hm : Measurable χ) (B : ℝ) (_hB : ∀ p, |χ p| ≤ B),
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ S0 : HTSpace c →L[ℂ] HSpace c MeridC,
          IsStressMap c 0 (T0flat hc ν μ) S0 →
          ∀ F : HTSpace c,
            (∀ h ∈ Icc (-1 : ℝ) 1,
              ∫ p, ‖flatStressCutRep c χ (S0 F) (shiftQ h p) -
                  flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c) ≤
                (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ^ 2 * |h|) ∧
            (∀ h ∈ Icc (-1 : ℝ) 1,
              ∫ p, ‖flatStressCutRep c χ (S0 F) (shiftEta h p) -
                  flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c) ≤
                (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ^ 2 * |h|)

/-- **Leaf 2 (`PartII-a:N05/4/2`): age `s` 1/2-Hölder `L²(cellMeasure c)` translation bound for
`χ S_0 F`**
(source `the November 2 reference manuscript`,
lines 1758–1764, 1785–1788): from the flat equation `(∂_s + μ/s - νΔ_{q,η}) b = P_0 div_0 M`,
`u = flatStressCutRep c χ (S0 F)` satisfies `u ∈ L²_s H¹_{q,η}` and `∂_s u ∈ L²_s H⁻¹_{q,η}`, so
`‖|∂_s|^{1/2} u‖_2² ≤ ‖∂_s u‖_{L²_s H⁻¹} ‖u‖_{L²_s H¹}` yields the `O(|h|^{1/2})` age
difference-quotient bound in `shiftS`. -/
def FlatStressAgeHolderHalf : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (_hm : Measurable χ) (B : ℝ) (_hB : ∀ p, |χ p| ≤ B),
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ S0 : HTSpace c →L[ℂ] HSpace c MeridC,
          IsStressMap c 0 (T0flat hc ν μ) S0 →
          ∀ F : HTSpace c,
            ∀ h ∈ Icc (-1 : ℝ) 1,
              ∫ p, ‖flatStressCutRep c χ (S0 F) (shiftS h p) -
                  flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c) ≤
                (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ^ 2 * |h|

/-- **Assembly of `StressFlatLocalH14` (`PartII-a:N05/4`)** from `FlatStressSpatialHolderHalf`
and `FlatStressAgeHolderHalf` via `hasCellH14_of_holderHalf` (`Sub/PartII-a_N05.lean`). -/
theorem stressFlatLocalH14_of (hSpat : FlatStressSpatialHolderHalf)
    (hAge : FlatStressAgeHolderHalf) : StressFlatLocalH14 := by
  obtain ⟨k1, C1, hC1, hS1⟩ := hSpat
  obtain ⟨k2, C2, hC2, hA2⟩ := hAge
  let k := max 3 (max k1 k2)
  refine ⟨k, 7 * (1 + C1 + C2), by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ S0 hS0 F
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 :=
    gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  set A : ℝ := (1 + C1 + C2) * G ^ k * ‖F‖
  have hA0 : 0 ≤ A := by positivity
  have hA0_le : G ^ 3 * ‖F‖ ≤ A := by
    have hk : G ^ 3 ≤ G ^ k := pow_le_pow_right₀ hG1 (le_max_left 3 (max k1 k2))
    have hC : (1 : ℝ) ≤ 1 + C1 + C2 := by linarith
    calc G ^ 3 * ‖F‖ = 1 * G ^ 3 * ‖F‖ := by ring
      _ ≤ (1 + C1 + C2) * G ^ k * ‖F‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hC hk (pow_nonneg (zero_le_one.trans hG1) _) (by positivity))
            (norm_nonneg F)
  have hA1 : C1 * G ^ k1 * ‖F‖ ≤ A := by
    have hk : G ^ k1 ≤ G ^ k :=
      pow_le_pow_right₀ hG1 ((le_max_left k1 k2).trans (le_max_right 3 (max k1 k2)))
    have hC : C1 ≤ 1 + C1 + C2 := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hC hk (pow_nonneg (zero_le_one.trans hG1) _) (by positivity))
      (norm_nonneg F)
  have hA2_le : C2 * G ^ k2 * ‖F‖ ≤ A := by
    have hk : G ^ k2 ≤ G ^ k :=
      pow_le_pow_right₀ hG1 ((le_max_right k1 k2).trans (le_max_right 3 (max k1 k2)))
    have hC : C2 ≤ 1 + C1 + C2 := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hC hk (pow_nonneg (zero_le_one.trans hG1) _) (by positivity))
      (norm_nonneg F)
  obtain ⟨hhq, hhe⟩ :=
    hS1 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ S0 hS0 F
  have hhs :=
    hA2 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ S0 hS0 F
  let u := flatStressCutRep c χ (S0 F)
  have hu_meas : Measurable u := measurable_flatStressCutRep c hm (S0 F)
  have hmem : MemLp u 2 (cellMeasure c) := memLp_flatStressCutRep hc hσ hσH hχ hm (S0 F)
  have hL2 : cellL2Norm c u ≤ A :=
    (cellL2Norm_flatStressCutRep_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ hS0 F).trans
      hA0_le
  have hA1_sq : (C1 * G ^ k1 * ‖F‖) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA1 2
  have hA2_sq : (C2 * G ^ k2 * ‖F‖) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA2_le 2
  have hcomb := hasCellH14_of_holderHalf hA0 (mulChi (measureH c) χ hm hB (S0 F)) u
    (flatStressCutRep_ae_eq hc χ hm hB (S0 F))
    (flatStressCutRep_periodic hc hχ (S0 F))
    (flatStressCutRep_support hχ (S0 F))
    hmem
    hL2
    (aestronglyMeasurable_diff_integral c measurable_shiftS_uncurry hu_meas)
    (aestronglyMeasurable_diff_integral c measurable_shiftQ_uncurry hu_meas)
    (aestronglyMeasurable_diff_integral c measurable_shiftEta_uncurry hu_meas)
    (fun h hh => (hhs h hh).trans (mul_le_mul_of_nonneg_right hA2_sq (abs_nonneg h)))
    (fun h hh => (hhq h hh).trans (mul_le_mul_of_nonneg_right hA1_sq (abs_nonneg h)))
    (fun h hh => (hhe h hh).trans (mul_le_mul_of_nonneg_right hA1_sq (abs_nonneg h)))
  refine ⟨u, hcomb.1, ?_⟩
  calc cellH14Norm c u
      ≤ 7 * A := hcomb.2
    _ = 7 * (1 + C1 + C2) * G ^ k * ‖F‖ := by
      simp only [A]
      ring

end UnforcedLeray.Short.PartIIa
