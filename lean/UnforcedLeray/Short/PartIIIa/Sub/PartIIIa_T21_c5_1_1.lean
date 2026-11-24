import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.DualBounds
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2

/-!
# Part III-a, task `PartIII-a:T21/c5/1/1` decomposition (`Sub/PartIII-a_T21_c5_1_1.lean`, SP 2891-2918, 2998-3000)

Source of record: `the November 2 reference manuscript` (SP), lines 2891-2918 and
2998-3000 (`eq:short-causal-moving-eq`, `eq:short-causal-ampl-moving`).

## Proved infrastructure in this file and `CutFTC/DualBounds.lean`

1. **Periodicity and operator identities (`CutFTCDual`)**:
   * `normPhysFrameLam_periodic` and `contDiffOn_normPhysFrameLam`: shows that
     `φ = normPhysFrameLam κ P ν t · i` is `c = ν⁻²`-periodic in `x.1` and jointly `C^∞` on
     `Ico t (s + 1) ×ˢ univ` whenever `physFrameLam κ ν · i` is.
   * `ladChi_normPhysFrameLam_eq`: proves the pointwise operator decomposition
     `ladChi tr φ ρ x = normPhysLamDual κ P tr t ρ i x + kerAdj c (fun k y => φ ρ y * (pd k (Ec tr ρ) y : ℂ)) x`.
2. **Pullback `X_{-m,c}` bounds, spatial gradient pullback, and kernel adjoint transposition**:
   * `memLp_and_xNorm_physAdj_neg`, `memLp_and_xNorm_physFrameLam_and_physLamDual`,
     `memLp_and_xNorm_normPhysFrameLam_and_Dual`: pulls the moving-variable `X_{-m,d(r)}` bounds
     `MovLamDualHeatBound κ` and `MovLamDualEulerSubBound κ` back to uniform physical-variable
     `X_{-m,c}` bounds on `[t, s]`.
   * `pdCx_physAdj_eq` and `physFrameLamRegularity_of`: proves the exact spatial derivative
     pullback `pdCx k (physAdj a Φ) x = (√a)⁻¹ * physAdj a (pdCx k Φ) x` and combines
     `SeedLamGradPerSum κ`, `memLp_and_xNorm_perSum_of_inv_sq_decay`, `perGram_inv_entry_bound`,
     and `memLp_and_xNorm_physAdj_neg` to deduce the uniform `X_{-m, ν⁻²}` gradient bound for
     `pdCx k (physFrameLam κ ν r i)` on `[t, s]` from `SeedLamGradPerSum κ` and
     `PhysFrameLamSmooth κ`.
   * `kerAdj_memLp_and_transposition`: bounds `kerAdj c (φ ρ ∇Ec(ρ))` in `X_{-m,c}` uniformly on
     `[0, s]` and proves its exact transposition
     `∫_{C_c} w(ρ) kerAdj c (φ ρ ∇Ec(ρ)) = ∫_{C_c} (u(ρ)·∇Ec(ρ)) φ(ρ)`
     against any zero-circulation Biot-Savart pair `(w(ρ), u(ρ))`.
3. **Cutoff rate limit, uniform domination, and conditional assembly (`normAmplCutFTC_of`)**:
   * `ladComm_bound_and_vanish`: proves `ladComm tr w φ R ρ → 0` as `R → ∞` and a uniform bound
     for `R ≥ 1` and `ρ ∈ Ioo t s`.
   * `ladRate_tendsto_and_bound`: combines `ladRateSplit`, `ladCutLimit`, `kerAdj` transposition
     cancellation, and `WeakFTCSub.normPhysLamDual_pairing_eq_amplResidual` to prove that for every
     `ρ ∈ Ioo t s`, `ladRate tr w u φ R ρ` is uniformly bounded for `R ≥ 1` and converges as
     `R → ∞` to `a(ρ)⁻² * ((clockNC P ν t ρ i)⁻¹ * amplResidual κ P F tr w ρ i)`.
   * `normAmplCutFTC_of`: passes `R → ∞` in `ladProductRule` by dominated convergence to establish
     both `AEMeasurable` of `amplResidual` on `volume.restrict (Ioc t s)` and the Bochner integral
     identity for `normAmpl F P t w s i - normAmpl F P t w t i` from `SeedLamGradPerSum κ`
     (`PartIII-a:T21/c5/1/1/1`) and `PhysFrameLamSmooth κ` (`PartIII-a:T21/c5/1/1/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-! ## Analytical leaves for spatial gradient periodization and joint smoothness of `physFrameLam` -/

/-- **Leaf 1 (`PartIII-a:T21/c5/1/1/1`, `SeedLamGradPerSum`, SP 593-610, 2891-2905)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), the spatial partial derivatives
`pdCx k (κ.lamP j)` of the planar dual kernels are continuous on `ℝ × ℝ` with
`O((1 + |z₁| + |z₂|)⁻²)` decay, and for `d ≥ 1` the unnormalised periodized rows `perLam0 κ d j`
are differentiable on `ℝ × ℝ` with termwise derivative
`pdCx k (perLam0 κ d j) y = perSum d (pdCx k (κ.lamP j)) y`.
Composed by task `PartIII-a:T21/c5/1/1` via `normAmplCutFTC_of`. -/
def SeedLamGradPerSum (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ C_g : ℝ, 0 ≤ C_g ∧
    (∀ j k : Fin 2, Continuous (pdCx k (κ.lamP j))) ∧
    (∀ (j k : Fin 2) (z : ℝ × ℝ),
      ‖pdCx k (κ.lamP j) z‖ ≤ C_g * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) ∧
    (∀ {d : ℝ}, 1 ≤ d → ∀ (j k : Fin 2) (y : ℝ × ℝ),
      DifferentiableAt ℝ (perLam0 κ d j) y ∧
      pdCx k (perLam0 κ d j) y = perSum d (pdCx k (κ.lamP j)) y)

/-- **Leaf 2 (`PartIII-a:T21/c5/1/1/2`, `PhysFrameLamSmooth`, SP 2891-2905)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), in the regime `b ≥ b_sm ≥ 1`,
`ν ∈ (0, ν_sm]`, `0 ≤ t ≤ s`, `b ≤ clockTheta ν s`, the physical-variable periodized dual row
`(r, x) ↦ physFrameLam κ ν r i x` is jointly `C^∞` on `Ico t (s + 1) ×ˢ univ`.
Composed by task `PartIII-a:T21/c5/1/1` via `normAmplCutFTC_of`. -/
def PhysFrameLamSmooth (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ b_sm : ℝ, 1 ≤ b_sm ∧
    ∀ b : ℝ, b_sm ≤ b →
      ∃ ν_sm : ℝ, 0 < ν_sm ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_sm →
        ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ i : Fin 2,
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
            (Ico t (s + 1) ×ˢ univ)

/-- Combined regularity bundle (`PhysFrameLamRegularity`, SP 2891-2905): joint `C^∞` smoothness of
`physFrameLam κ ν · i` on `Ico t (s + 1) ×ˢ univ` together with uniform `X_{-m, ν⁻²}` bounds on its
spatial partial derivatives `pdCx k (physFrameLam κ ν r i)` for `r ∈ Icc t s`. -/
def PhysFrameLamRegularity (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ b_reg : ℝ, 1 ≤ b_reg ∧
    ∀ b : ℝ, b_reg ≤ b →
      ∃ ν_reg : ℝ, 0 < ν_reg ∧
        ∀ ν : ℝ, ν ∈ Ioc 0 ν_reg →
        ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ i : Fin 2,
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
            (Ico t (s + 1) ×ˢ univ) ∧
          ∃ M_g : ℝ, 0 ≤ M_g ∧
            ∀ r ∈ Icc t s, ∀ k : Fin 2,
              MemLp (pdCx k (physFrameLam κ ν r i)) 2
                (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
              xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (physFrameLam κ ν r i)) ≤
                ENNReal.ofReal M_g

namespace CutFTCAux

open ComplCouplingSub ComplCouplingHeat ComplCouplingEuler WeakFTCSub CutFTCDual

/-- Linearity of `pdCx k` on a two-term linear combination of differentiable functions. -/
theorem pdCx_linear_comb_two (c0 c1 : ℂ) {f0 f1 : ℝ × ℝ → ℂ} (k : Fin 2) (y : ℝ × ℝ)
    (hf0 : DifferentiableAt ℝ f0 y) (hf1 : DifferentiableAt ℝ f1 y) :
    pdCx k (fun z => c0 * f0 z + c1 * f1 z) y = c0 * pdCx k f0 y + c1 * pdCx k f1 y := by
  have h : HasFDerivAt (fun z => c0 * f0 z + c1 * f1 z)
      (c0 • fderiv ℝ f0 y + c1 • fderiv ℝ f1 y) y :=
    (hf0.hasFDerivAt.const_mul c0).add (hf1.hasFDerivAt.const_mul c1)
  unfold pdCx
  rw [h.fderiv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Spatial derivative of `perLam κ d i` as a Gram-inverse linear combination of
`pdCx k (perLam0 κ d j)`. -/
theorem pdCx_perLam_eq (κ : PlanarFrameKernels) (d : ℝ) (i k : Fin 2) (y : ℝ × ℝ)
    (hd0 : DifferentiableAt ℝ (perLam0 κ d 0) y)
    (hd1 : DifferentiableAt ℝ (perLam0 κ d 1) y) :
    pdCx k (perLam κ d i) y =
      ∑ j : Fin 2, (perGram κ d)⁻¹ i j * pdCx k (perLam0 κ d j) y := by
  have hfun : perLam κ d i =
      fun z => (perGram κ d)⁻¹ i 0 * perLam0 κ d 0 z + (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 z := by
    funext z
    unfold perLam
    simp [Fin.sum_univ_two]
  rw [hfun, pdCx_linear_comb_two _ _ k y hd0 hd1, Fin.sum_univ_two]

/-- Pointwise spatial partial derivative of `physAdj a Φ` in physical coordinates:
`pdCx k (physAdj a Φ) x = ((Real.sqrt a)⁻¹ : ℂ) * physAdj a (pdCx k Φ) x`. -/
theorem pdCx_physAdj_eq {a : ℝ} (ha : 0 < a) (Φ : ℝ × ℝ → ℂ) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (physAdj a Φ) x = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * physAdj a (pdCx k Φ) x := by
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hx : x = (Real.sqrt a * (x.1 / Real.sqrt a), Real.sqrt a * (x.2 / Real.sqrt a)) := by
    ext <;> simp [mul_div_cancel₀ _ hsa]
  conv_lhs => rw [hx]
  rw [pdCx_physAdj_scale a ha Φ k (x.1 / Real.sqrt a, x.2 / Real.sqrt a)]
  unfold physAdj
  push_cast
  ring

/-- Deduces `PhysFrameLamRegularity κ` from `SeedLamGradPerSum κ` and `PhysFrameLamSmooth κ`:
combines `memLp_and_xNorm_perSum_of_inv_sq_decay`, `perGram_inv_entry_bound`,
`memLp_and_xNorm_linear_comb_two`, and `memLp_and_xNorm_physAdj_neg` to bound
`pdCx k (physFrameLam κ ν r i)` in `X_{-m, ν⁻²}` uniformly on `[t, s]`. -/
theorem physFrameLamRegularity_of (κ : PlanarFrameKernels)
    (hGrad : SeedLamGradPerSum κ) (hSmooth : PhysFrameLamSmooth κ) :
    PhysFrameLamRegularity κ := by
  intro hκ m hm
  have hm1 : 1 < m := by linarith
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨C_g, _, hcont, hdecay, hder0⟩ := hGrad hκ
  obtain ⟨b_sm, hb_sm1, hSm⟩ := hSmooth hκ
  obtain ⟨D_1, hD_1, hGramInv⟩ := perGram_inv_entry_bound κ
  have hD_pos : 0 < D_1 := lt_of_lt_of_le zero_lt_one hD_1
  -- Uniform `X_{-m, d}` bounds on `perSum d (pdCx k (κ.lamP j))` for all `j, k : Fin 2` and `d ≥ 1`
  obtain ⟨K00, hK00, hB00⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 0 0) (hdecay 0 0)
  obtain ⟨K01, hK01, hB01⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 0 1) (hdecay 0 1)
  obtain ⟨K10, hK10, hB10⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 1 0) (hdecay 1 0)
  obtain ⟨K11, hK11, hB11⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hcont 1 1) (hdecay 1 1)
  set K_g : ℝ := max (max K00 K01) (max K10 K11)
  have hK_g0 : 0 ≤ K_g := le_trans hK00 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hPerLam0Grad : ∀ {d : ℝ}, 1 ≤ d → ∀ j k : Fin 2,
      MemLp (pdCx k (perLam0 κ d j)) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (pdCx k (perLam0 κ d j)) ≤ ENNReal.ofReal K_g := by
    intro d hd j k
    have hfun : pdCx k (perLam0 κ d j) = perSum d (pdCx k (κ.lamP j)) :=
      funext fun y => (hder0 hd j k y).2
    rw [hfun]
    fin_cases j <;> fin_cases k
    · exact ⟨(hB00 d hd).1, (hB00 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_left _ _) (le_max_left _ _)))⟩
    · exact ⟨(hB01 d hd).1, (hB01 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_right _ _) (le_max_left _ _)))⟩
    · exact ⟨(hB10 d hd).1, (hB10 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_left _ _) (le_max_right _ _)))⟩
    · exact ⟨(hB11 d hd).1, (hB11 d hd).2.trans (ENNReal.ofReal_le_ofReal
        (le_trans (le_max_right _ _) (le_max_right _ _)))⟩
  refine ⟨b_sm, hb_sm1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans hb_sm1 hb
  obtain ⟨ν_sm, hν_sm, hSm_b⟩ := hSm b hb
  set ν_D : ℝ := 1 / (D_1 + 1) ^ 2
  have hν_D : 0 < ν_D := by positivity
  set ν_reg : ℝ := min ν_sm (min ν_D 1)
  have hν_reg_pos : 0 < ν_reg := lt_min hν_sm (lt_min hν_D zero_lt_one)
  refine ⟨ν_reg, hν_reg_pos, fun ν hν t s ht hts hbs i => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_sm' : ν ≤ ν_sm := le_trans hν.2 (min_le_left _ _)
  have hν_D' : ν ≤ ν_D := le_trans (le_trans hν.2 (min_le_right _ _)) (min_le_left _ _)
  have hν1 : ν ≤ 1 := le_trans (le_trans hν.2 (min_le_right _ _)) (min_le_right _ _)
  let c := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  refine ⟨hSm_b ν ⟨hν0, hν_sm'⟩ t s ht hts hbs i, ?_⟩
  set M_g : ℝ := (clockA ν s) ^ (3 / 2 : ℝ) * (2 * (3 * K_g))
  have ha_s : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν0.le (ht.trans hts))
  have hM_g0 : 0 ≤ M_g := by unfold M_g; positivity
  refine ⟨M_g, hM_g0, fun r hr k => ?_⟩
  have hr0 : 0 ≤ r := ht.trans hr.1
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν0.le hr0
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hθr : b ≤ clockTheta ν r := hbs.trans (theta_anti hν0 hr0 hr.2)
  have hd_D1 : D_1 ≤ cellLen c (clockA ν r) := cellLen_ge hD_pos.le hν0 hν_D' hb1 hr0 hθr
  have hd1 : 1 ≤ cellLen c (clockA ν r) := le_trans hD_1 hd_D1
  set d := cellLen c (clockA ν r)
  -- `X_{-m, d}` bound for `pdCx k (perLam κ d i)`
  have hterm_grad : ∀ j : Fin 2,
      MemLp (fun y => (perGram κ d)⁻¹ i j * pdCx k (perLam0 κ d j) y) 2
        (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (fun y => (perGram κ d)⁻¹ i j * pdCx k (perLam0 κ d j) y) ≤
        ENNReal.ofReal (3 * K_g) := by
    intro j
    refine ⟨(hPerLam0Grad hd1 j k).1.const_mul _, ?_⟩
    refine (xNorm_const_mul_le hK_g0 (hPerLam0Grad hd1 j k).2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (hGramInv d hd_D1 i j) hK_g0
  have hperLam_eq : pdCx k (perLam κ d i) =
      fun y => (perGram κ d)⁻¹ i 0 * pdCx k (perLam0 κ d 0) y +
        (perGram κ d)⁻¹ i 1 * pdCx k (perLam0 κ d 1) y := by
    funext y
    rw [pdCx_perLam_eq κ d i k y (hder0 hd1 0 k y).1 (hder0 hd1 1 k y).1, Fin.sum_univ_two]
  obtain ⟨hperLam_mem, hperLam_x⟩ :
      MemLp (pdCx k (perLam κ d i)) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (pdCx k (perLam κ d i)) ≤ ENNReal.ofReal (2 * (3 * K_g)) := by
    rw [hperLam_eq]
    obtain ⟨hm01, hx01⟩ := memLp_and_xNorm_add_le (by positivity) (by positivity)
      (hterm_grad 0).1 (hterm_grad 1).1 (hterm_grad 0).2 (hterm_grad 1).2
    refine ⟨hm01, hx01.trans ?_⟩
    rw [show 3 * K_g + 3 * K_g = 2 * (3 * K_g) by ring]
  -- Pull back to `X_{-m, c}` via `physAdj (clockA ν r)`
  obtain ⟨hphys_mem, hphys_x⟩ :=
    memLp_and_xNorm_physAdj_neg hc0 hm0 ha1 (by positivity) hperLam_mem hperLam_x
  have hphys_eq : pdCx k (physFrameLam κ ν r i) =
      fun x => (((Real.sqrt (clockA ν r))⁻¹ : ℝ) : ℂ) *
        physAdj (clockA ν r) (pdCx k (perLam κ d i)) x :=
    funext fun x => pdCx_physAdj_eq ha0 (perLam κ d i) k x
  rw [hphys_eq]
  refine ⟨hphys_mem.const_mul _, ?_⟩
  have hnorm_inv : ‖(((Real.sqrt (clockA ν r))⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 ha1)
  have ha_le : clockA ν r ≤ clockA ν s := clockA_mono hν0.le hr.2
  have hrpow_le : (clockA ν r) ^ (3 / 2 : ℝ) ≤ (clockA ν s) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ha0.le ha_le (by norm_num)
  refine (xNorm_const_mul_le (by positivity) hphys_x).trans (ENNReal.ofReal_le_ofReal ?_)
  calc ‖(((Real.sqrt (clockA ν r))⁻¹ : ℝ) : ℂ)‖ * ((clockA ν r) ^ (3 / 2 : ℝ) * (2 * (3 * K_g)))
      ≤ 1 * ((clockA ν s) ^ (3 / 2 : ℝ) * (2 * (3 * K_g))) := by gcongr
    _ = M_g := one_mul M_g

/-- Uniform bound (for `R ≥ 1`) and `R → ∞` vanishing of `ladComm tr w φ R ρ` at a fixed
`ρ ∈ Icc t s` when `w ρ ∈ X_{m,c}` and `φ ρ, pdCx k (φ ρ) ∈ X_{-m,c}` have explicit norm bounds. -/
theorem ladComm_bound_and_vanish {ν c m C_tr A_w M_φ M_g' ρ : ℝ}
    (_hc0 : 0 < c) (hC_tr0 : 0 ≤ C_tr) (hA_w0 : 0 ≤ A_w) (_hM_φ0 : 0 ≤ M_φ) (_hM_g'0 : 0 ≤ M_g')
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C_tr)
    {w φ : ℝ → ℝ × ℝ → ℂ}
    (hw_mem : MemLp (w ρ) 2 (B0579.cellMeasure c m))
    (hw_norm : (xNorm c m (w ρ)).toReal ≤ A_w)
    (hφ_mem : MemLp (φ ρ) 2 (B0579.cellMeasure c (-m)))
    (hφ_norm : (xNorm c (-m) (φ ρ)).toReal ≤ M_φ)
    (hgrad_mem : ∀ k : Fin 2, MemLp (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m)))
    (hgrad_norm : ∀ k : Fin 2, (xNorm c (-m) (pdCx k (φ ρ))).toReal ≤ M_g')
    {K_cut : ℝ} (hK_cut0 : 0 ≤ K_cut)
    (hp_cut : ∀ R : ℝ, 0 < R → ∀ (x : ℝ × ℝ) (j : Fin 2), |B0579.pd j (ladCut R) x| ≤ K_cut / R)
    (hl_cut : ∀ R : ℝ, 0 < R → ∀ x : ℝ × ℝ, |lapP (ladCut R) x| ≤ K_cut / R ^ 2) :
    (∀ R : ℝ, 1 ≤ R →
      ‖ladComm tr w φ R ρ‖ ≤
        (3 * |ν| * K_cut + 2 * C_tr * K_cut) * (A_w * M_φ + 2 * (A_w * M_g'))) ∧
    Tendsto (fun R : ℝ => ladComm tr w φ R ρ) atTop (𝓝 0) := by
  have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem hφ_mem
  have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem (hgrad_mem 0)
  have i3 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem (hgrad_mem 1)
  have hI : IntegrableOn (fun x => ‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (B0579.cell c) := (i1.add i2).add i3
  set I := ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖)
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hint_eq : I =
      (∫ x in B0579.cell c, ‖w ρ x‖ * ‖φ ρ x‖) +
        (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖) +
        (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
    unfold I
    rw [integral_add (f := fun x => ‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖)
      (g := fun x => ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (i1.add i2) i3,
      integral_add i1 i2]
  have c1 : (∫ x in B0579.cell c, ‖w ρ x‖ * ‖φ ρ x‖) ≤ A_w * M_φ :=
    (RateBoundAux.cs_norm c m hw_mem hφ_mem).trans
      (mul_le_mul hw_norm hφ_norm ENNReal.toReal_nonneg hA_w0)
  have c2 : (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖) ≤ A_w * M_g' :=
    (RateBoundAux.cs_norm c m hw_mem (hgrad_mem 0)).trans
      (mul_le_mul hw_norm (hgrad_norm 0) ENNReal.toReal_nonneg hA_w0)
  have c3 : (∫ x in B0579.cell c, ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) ≤ A_w * M_g' :=
    (RateBoundAux.cs_norm c m hw_mem (hgrad_mem 1)).trans
      (mul_le_mul hw_norm (hgrad_norm 1) ENNReal.toReal_nonneg hA_w0)
  have hI_le : I ≤ A_w * M_φ + 2 * (A_w * M_g') := by
    rw [hint_eq]
    linarith
  have hcomm_R := RateBoundAux.comm_bound tr w φ ρ K_cut C_tr hK_cut0 hC_tr0
    hp_cut hl_cut hv hI
  refine ⟨fun R hR1 => ?_, ?_⟩
  · have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
    have hK2 : 0 ≤ 3 * |ν| * K_cut + 2 * C_tr * K_cut := by positivity
    calc ‖ladComm tr w φ R ρ‖
        ≤ (3 * |ν| * K_cut + 2 * C_tr * K_cut) * R⁻¹ * I := hcomm_R R hR1
      _ ≤ (3 * |ν| * K_cut + 2 * C_tr * K_cut) * 1 * I := by gcongr
      _ = (3 * |ν| * K_cut + 2 * C_tr * K_cut) * I := by ring
      _ ≤ (3 * |ν| * K_cut + 2 * C_tr * K_cut) * (A_w * M_φ + 2 * (A_w * M_g')) :=
          mul_le_mul_of_nonneg_left hI_le hK2
  · have hT : Tendsto (fun R : ℝ => (3 * |ν| * K_cut + 2 * C_tr * K_cut) * R⁻¹ * I)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      simpa using (h0.const_mul (3 * |ν| * K_cut + 2 * C_tr * K_cut)).mul_const I
    refine squeeze_zero_norm' ?_ hT
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR using hcomm_R R hR

set_option maxHeartbeats 1200000 in
/-- Pointwise `R → ∞` limit and uniform `R ≥ 1` bound for `ladRate` on `normPhysFrameLam`. -/
theorem ladRate_tendsto_and_bound (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K t s ρ C_tr A_w F_u M_NC M_g M_φ M_ND M_ker : ℝ}
    (_hm : 8 < m) (hν : 0 < ν) (hν1 : ν ≤ 1) (ht : 0 ≤ t) (hts : t ≤ s)
    (hρ : ρ ∈ Ioo t s) (hF : PerFrameFacts κ ν m b K)
    (hC_tr0 : 0 ≤ C_tr) (hA_w0 : 0 ≤ A_w) (hF_u0 : 0 ≤ F_u)
    (hM_NC0 : 0 ≤ M_NC) (hM_g0 : 0 ≤ M_g) (hM_φ0 : 0 ≤ M_φ)
    (hM_ND0 : 0 ≤ M_ND) (hM_ker0 : 0 ≤ M_ker)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hBdd : LadTrainBdd tr m s C_tr)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u)
    (hw_norm : (xNorm (ν ^ (-2 : ℝ)) m (w ρ)).toReal ≤ A_w)
    (hforce_mem : MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hforce_norm : (xNorm (ν ^ (-2 : ℝ)) m (ladForce tr (u ρ) ρ)).toReal ≤ F_u)
    (i : Fin 2)
    (hSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
      (Ico t (s + 1) ×ˢ univ))
    (hNC : ‖(clockNC P ν t ρ i)⁻¹‖ ≤ M_NC)
    (hLam_mem : MemLp (physFrameLam κ ν ρ i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hDual_mem : MemLp (physLamDual κ tr ρ i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hφ_mem : MemLp (normPhysFrameLam κ P ν t ρ i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hφ_x : xNorm (ν ^ (-2 : ℝ)) (-m) (normPhysFrameLam κ P ν t ρ i) ≤ ENNReal.ofReal M_φ)
    (hND_mem : MemLp (normPhysLamDual κ P tr t ρ i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hND_x : xNorm (ν ^ (-2 : ℝ)) (-m) (normPhysLamDual κ P tr t ρ i) ≤ ENNReal.ofReal M_ND)
    (hKer_mem : MemLp
      (kerAdj (ν ^ (-2 : ℝ)) (fun k y => normPhysFrameLam κ P ν t ρ i y *
        ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))
      2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
    (hKer_x : xNorm (ν ^ (-2 : ℝ)) (-m)
      (kerAdj (ν ^ (-2 : ℝ)) (fun k y => normPhysFrameLam κ P ν t ρ i y *
        ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ))) ≤ ENNReal.ofReal M_ker)
    (hTransp : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      w ρ x * kerAdj (ν ^ (-2 : ℝ)) (fun k y => normPhysFrameLam κ P ν t ρ i y *
        ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ladForce tr (u ρ) ρ x * normPhysFrameLam κ P ν t ρ i x)
    (hgrad_phys : ∀ k : Fin 2,
      MemLp (pdCx k (physFrameLam κ ν ρ i)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (physFrameLam κ ν ρ i)) ≤ ENNReal.ofReal M_g)
    {K_cut : ℝ} (hK_cut0 : 0 ≤ K_cut)
    (hK_cut : ∀ R : ℝ, 0 < R →
      (∀ c : ℝ, B0579.IsCylTest c (ladCut R)) ∧
      (∀ x : ℝ × ℝ, 0 ≤ ladCut R x ∧ ladCut R x ≤ 1) ∧
      (∀ x : ℝ × ℝ, x.2 ^ 2 ≤ R ^ 2 → ladCut R x = 1) ∧
      (∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 → ladCut R x = 0) ∧
      (∀ (x : ℝ × ℝ) (j : Fin 2), |B0579.pd j (ladCut R) x| ≤ K_cut / R) ∧
      (∀ x : ℝ × ℝ, |lapP (ladCut R) x| ≤ K_cut / R ^ 2)) :
    let φ := fun r' x' => normPhysFrameLam κ P ν t r' i x'
    let F_fr := periodizedFrame κ ν m b K hν hF
    let M_rate := A_w * (M_ND + M_ker) + F_u * M_φ +
      (3 * |ν| * K_cut + 2 * C_tr * K_cut) * (A_w * M_φ + 2 * (A_w * (M_NC * M_g)))
    (Tendsto (fun R : ℝ => ladRate tr w u φ R ρ) atTop
      (𝓝 ((((clockA ν ρ) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((clockNC P ν t ρ i)⁻¹ * amplResidual κ P F_fr tr w ρ i)))) ∧
    (∀ R : ℝ, 1 ≤ R → ‖ladRate tr w u φ R ρ‖ ≤ M_rate) := by
  intro φ _F_fr M_rate
  let c := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨hρ0, hρ.2.le⟩
  have hρ_s1 : ρ ∈ Ioo t (s + 1) := ⟨hρ.1, by linarith [hρ.2]⟩
  have hts1 : t < s + 1 := by linarith
  have hw_mem : MemLp (w ρ) 2 (B0579.cellMeasure c m) := hw.memX ρ hρ.1.le
  -- Smoothness of `φ` and its slice at `ρ`
  have hφ_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
      (Ico t (s + 1) ×ˢ univ) :=
    contDiffOn_normPhysFrameLam κ P hν ht i hSmooth
  have hslice_phys : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
    RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x')
      ⟨hρ.1.le, hρ_s1.2⟩ hSmooth
  -- Gradient bounds for `φ ρ`
  have hgrad_φ : ∀ k : Fin 2,
      MemLp (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (pdCx k (φ ρ))).toReal ≤ M_NC * M_g := by
    intro k
    have heq : pdCx k (φ ρ) =
        fun x => (clockNC P ν t ρ i)⁻¹ * pdCx k (physFrameLam κ ν ρ i) x :=
      funext fun x => pdCx_normPhysFrameLam κ P ν t ρ i k x
        ((hslice_phys.differentiable (by simp)) x)
    rw [heq]
    have hm_k : MemLp (fun x => (clockNC P ν t ρ i)⁻¹ * pdCx k (physFrameLam κ ν ρ i) x) 2
        (B0579.cellMeasure c (-m)) := (hgrad_phys k).1.const_mul _
    have hx_k : xNorm c (-m)
        (fun x => (clockNC P ν t ρ i)⁻¹ * pdCx k (physFrameLam κ ν ρ i) x) ≤
        ENNReal.ofReal (M_NC * M_g) := by
      refine (xNorm_const_mul_le hM_g0 (hgrad_phys k).2).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hNC hM_g0
    exact ⟨hm_k, ENNReal.toReal_le_of_le_ofReal (mul_nonneg hM_NC0 hM_g0) hx_k⟩
  -- `ladChi tr φ ρ` decomposition and `X_{-m,c}` bound
  have hχ_eq : ladChi tr φ ρ =
      fun x => normPhysLamDual κ P tr t ρ i x +
        kerAdj c (fun k y => φ ρ y *
          ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x :=
    funext fun x => ladChi_normPhysFrameLam_eq κ P hν ht hρ_s1 i tr hSmooth x
  obtain ⟨hχ_mem, hχ_x⟩ :
      MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (ladChi tr φ ρ) ≤ ENNReal.ofReal (M_ND + M_ker) := by
    rw [hχ_eq]
    exact memLp_and_xNorm_add_le hM_ND0 hM_ker0 hND_mem hKer_mem hND_x hKer_x
  have hχ_norm : (xNorm c (-m) (ladChi tr φ ρ)).toReal ≤ M_ND + M_ker :=
    ENNReal.toReal_le_of_le_ofReal (add_nonneg hM_ND0 hM_ker0) hχ_x
  have hφ_norm : (xNorm c (-m) (φ ρ)).toReal ≤ M_φ :=
    ENNReal.toReal_le_of_le_ofReal hM_φ0 hφ_x
  -- Commutator bound and vanishing
  have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C_tr :=
    fun x hx j => (hBdd ρ hρS x hx).1 j
  obtain ⟨hcomm_bd, hcomm_lim⟩ := ladComm_bound_and_vanish hc0 hC_tr0 hA_w0 hM_φ0
    (mul_nonneg hM_NC0 hM_g0) hv hw_mem hw_norm hφ_mem hφ_norm
    (fun k => (hgrad_φ k).1) (fun k => (hgrad_φ k).2) hK_cut0
    (fun R hR x j => (hK_cut R hR).2.2.2.2.1 x j)
    (fun R hR x => (hK_cut R hR).2.2.2.2.2 x)
  refine ⟨?_, fun R hR1 => ?_⟩
  · -- Pointwise limit as `R → ∞`
    have hA_lim := ladCutLimit c m (w ρ) (ladChi tr φ ρ) hw_mem hχ_mem
    have hB_lim := ladCutLimit c m (ladForce tr (u ρ) ρ) (φ ρ) hforce_mem hφ_mem
    have hsum_lim := (hA_lim.sub hB_lim).add hcomm_lim
    -- Evaluate `∫ w ρ * ladChi tr φ ρ - ∫ ladForce * φ ρ + 0`
    have hInt_ND : IntegrableOn (fun x => w ρ x * normPhysLamDual κ P tr t ρ i x) (B0579.cell c) :=
      CutLimitAux.integrable_complex hw_mem hND_mem
    have hInt_Ker : IntegrableOn (fun x => w ρ x * kerAdj c (fun k y => φ ρ y *
        ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x) (B0579.cell c) :=
      CutLimitAux.integrable_complex hw_mem hKer_mem
    have hInt_Dual : IntegrableOn (fun x => w ρ x * physLamDual κ tr ρ i x) (B0579.cell c) :=
      CutLimitAux.integrable_complex hw_mem hDual_mem
    have hInt_Lam : IntegrableOn (fun x => w ρ x * physFrameLam κ ν ρ i x) (B0579.cell c) :=
      CutLimitAux.integrable_complex hw_mem hLam_mem
    have hχ_int_eq : (∫ x in B0579.cell c, w ρ x * ladChi tr φ ρ x) =
        (∫ x in B0579.cell c, w ρ x * normPhysLamDual κ P tr t ρ i x) +
          ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x := by
      have heq_pt : (fun x => w ρ x * ladChi tr φ ρ x) =
          fun x => w ρ x * normPhysLamDual κ P tr t ρ i x +
            w ρ x * kerAdj c (fun k y => φ ρ y *
              ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := by
        funext x; rw [hχ_eq]; ring
      rw [heq_pt, integral_add hInt_ND hInt_Ker, hTransp]
    have hres_eq := normPhysLamDual_pairing_eq_amplResidual κ P (m := m) (b := b) (K := K)
      (t := t) hν hρ0 hF tr w i hInt_Dual hInt_Lam
    rw [hχ_int_eq, hres_eq, add_sub_cancel_right, add_zero] at hsum_lim
    refine hsum_lim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (ladRateSplit ν c m tr t (s + 1) f w u φ hc0 ht hts1 hw hφ_smooth R hR ρ hρ_s1).symm
  · -- Uniform bound for `R ≥ 1`
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    rw [ladRateSplit ν c m tr t (s + 1) f w u φ hc0 ht hts1 hw hφ_smooth R hR0 ρ hρ_s1]
    have hcut := hK_cut R hR0
    have hcont : Continuous (ladCut R) := (hcut.1 c).continuous
    have hcb : ∀ x, |ladCut R x| ≤ 1 := fun x => by
      rw [abs_of_nonneg (hcut.2.1 x).1]; exact (hcut.2.1 x).2
    have ea : ‖∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)‖ ≤
        A_w * (M_ND + M_ker) :=
      (RateBoundAux.cs_cut c m hcont hcb hw_mem hχ_mem).trans
        (mul_le_mul hw_norm hχ_norm ENNReal.toReal_nonneg hA_w0)
    have eb : ‖∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x‖ ≤
        F_u * M_φ :=
      (RateBoundAux.cs_cut c m hcont hcb hforce_mem hφ_mem).trans
        (mul_le_mul hforce_norm hφ_norm ENNReal.toReal_nonneg hF_u0)
    have ec := hcomm_bd R hR1
    have hsub := norm_add_le
      ((∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
        ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
      (ladComm tr w φ R ρ)
    have hsub2 := norm_sub_le
      (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x))
      (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
    unfold M_rate
    linarith [hsub, hsub2, ea, eb, ec]

end CutFTCAux

set_option maxHeartbeats 1200000 in
open ComplCouplingSub ComplCouplingHeat WeakFTCSub CutFTCDual CutFTCAux in
/-- Conditional proof of `NormAmplCutFTC κ` from `PhysFrameLamRegularity κ`. -/
theorem normAmplCutFTC_of_reg (κ : PlanarFrameKernels) (hReg : PhysFrameLamRegularity κ) :
    NormAmplCutFTC κ := by
  intro hHeat hEuler hκ P _hP m hm K
  have hm1 : 1 < m := by linarith
  obtain ⟨C_h, b_h, hC_h0, hb_h, hHeat'⟩ := hHeat hκ m hm
  obtain ⟨lam, C_e, b_e, hC_e0, hb_e, hEuler'⟩ := hEuler hκ m hm
  obtain ⟨b_reg, hb_reg, hReg'⟩ := hReg hκ m hm
  obtain ⟨D_1, hD_1, hGramInv⟩ := ComplCouplingHeat.perGram_inv_entry_bound κ
  set M_G : ℝ := 3
  have hM_G0 : 0 ≤ M_G := by norm_num
  obtain ⟨K₀, hK₀, hLam0⟩ := ComplCouplingHeat.memLp_and_xNorm_perLam0_neg κ hm1
  obtain ⟨ν_B, hν_B, hTrainBdd⟩ := CutFTCDual.ladTrainBddAll_unconditional m
  obtain ⟨K_cut, hK_cut0, hK_cut⟩ := ladCutProps
  set b_c : ℝ := max (max b_h b_e) b_reg
  have hb_c1 : 1 ≤ b_c := le_trans hb_reg (le_max_right _ _)
  refine ⟨b_c, hb_c1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans hb_c1 hb
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hb_bh : b_h ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hb_be : b_e ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
  have hb_breg : b_reg ≤ b := le_trans (le_max_right _ _) hb
  obtain ⟨ν_h, hν_h, hHeat_b⟩ := hHeat' b hb_bh
  obtain ⟨ν_e, hν_e, hEuler_b⟩ := hEuler' b hb_be
  obtain ⟨ν_reg, hν_reg, hReg_b⟩ := hReg' b hb_breg
  have hD_pos : 0 < D_1 := lt_of_lt_of_le zero_lt_one hD_1
  set ν_D : ℝ := 1 / (D_1 + 1) ^ 2
  have hν_D : 0 < ν_D := by positivity
  set ν_c : ℝ := min (min (min (min ν_h ν_e) ν_reg) ν_B) (min ν_D 1)
  have hν_c_pos : 0 < ν_c :=
    lt_min (lt_min (lt_min (lt_min hν_h hν_e) hν_reg) hν_B) (lt_min hν_D zero_lt_one)
  refine ⟨ν_c, hν_c_pos, fun ν hν hF tr htr t s ht hts hbs f w u hw hf0 => ?_⟩
  intro F
  have hν0 : 0 < ν := hν.1
  have hν_left : ν ≤ min (min (min ν_h ν_e) ν_reg) ν_B :=
    le_trans hν.2 (min_le_left _ _)
  have hν_right : ν ≤ min ν_D 1 := le_trans hν.2 (min_le_right _ _)
  have hν1 : ν ≤ 1 := le_trans hν_right (min_le_right _ _)
  have hν_le_D : ν ≤ ν_D := le_trans hν_right (min_le_left _ _)
  have hν_le_B : ν ≤ ν_B := le_trans hν_left (min_le_right _ _)
  have hν_le_reg : ν ≤ ν_reg :=
    le_trans (le_trans hν_left (min_le_left _ _)) (min_le_right _ _)
  have hν_le_he : ν ≤ min ν_h ν_e :=
    le_trans (le_trans hν_left (min_le_left _ _)) (min_le_left _ _)
  have hν_le_h : ν ≤ ν_h := le_trans hν_le_he (min_le_left _ _)
  have hν_le_e : ν ≤ ν_e := le_trans hν_le_he (min_le_right _ _)
  let c := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  -- Train bound on `[0, s]`
  obtain ⟨C_tr, hBdd⟩ := hTrainBdd ν ⟨hν0, hν_le_B⟩ tr htr s (ht.trans hts)
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c := ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
  have hC_tr0 : 0 ≤ C_tr := (abs_nonneg _).trans ((hBdd t ⟨ht, hts⟩ _ hx0).1 0)
  -- Uniform bounds on `w`, `u`, and `ladForce tr (u ρ) ρ` on `[t, s]`
  have hwc : ContinuousOn (fun ρ => (xNorm c m (w ρ)).toReal) (Ici t) :=
    RateBoundAux.contOn_norm w (fun ρ h => hw.memX ρ h) (fun ρ h => hw.strongCont ρ h)
  obtain ⟨A_w, hA_w0, hA_w⟩ :=
    RateBoundAux.bdd_of_cont (hwc.mono (Icc_subset_Ici_self : Icc t s ⊆ Ici t))
  obtain ⟨Cl, hCl⟩ := ladVelLip m hm ν c tr t f w u hc1 hf0 hw
  have hu2 : ∀ ρ, t ≤ ρ → ∀ j : Fin 2,
      MemLp (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) :=
    fun ρ h j => (hw.biotSavart ρ h).1 j
  have hAe : ∀ ρ ∈ Icc t s, xNorm c m (w ρ) ≤ ENNReal.ofReal A_w := fun ρ hρ =>
    RateBoundAux.ofReal_toReal_le (hw.memX ρ hρ.1).eLpNorm_ne_top hA_w0 (hA_w ρ hρ)
  have hU : ∀ ρ ∈ Icc t s, ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
          eLpNorm (fun x => u t x j) 2 (volume.restrict (B0579.cell c)) := by
    intro ρ hρ j
    have h1 := eLpNorm_add_le (p := 2) (μ := volume.restrict (B0579.cell c))
      ((hu2 ρ hρ.1 j).1.sub (hu2 t le_rfl j).1) (hu2 t le_rfl j).1 one_le_two
    rw [sub_add_cancel] at h1
    have h2 : eLpNorm ((fun x => u ρ x j) - fun x => u t x j) 2
        (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal Cl * xNorm c m (w ρ - w t) :=
      hCl ρ t hρ.1 le_rfl j
    have h3 : xNorm c m (w ρ - w t) ≤ xNorm c m (w ρ) + xNorm c m (w t) :=
      eLpNorm_sub_le (hw.memX ρ hρ.1).1 (hw.memX t le_rfl).1 one_le_two
    have h4 : xNorm c m (w ρ - w t) ≤ ENNReal.ofReal A_w + ENNReal.ofReal A_w :=
      h3.trans (add_le_add (hAe ρ hρ) (hAe t ⟨le_rfl, hts⟩))
    exact h1.trans (add_le_add (h2.trans (mul_le_mul' le_rfl h4)) le_rfl)
  set Fe : ℝ≥0∞ := ENNReal.ofReal C_tr *
    ((ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
        eLpNorm (fun x => u t x 0) 2 (volume.restrict (B0579.cell c))) +
      (ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
        eLpNorm (fun x => u t x 1) 2 (volume.restrict (B0579.cell c))))
  have hFe : Fe ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) <;>
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩),
        (hu2 t le_rfl _).eLpNorm_ne_top⟩
  have hforce : ∀ ρ ∈ Icc t s, MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ Fe.toReal := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := ladForceMemX m ν c tr s C_tr ρ hBdd ⟨ht.trans hρ.1, hρ.2⟩ (u ρ)
      (fun j => hu2 ρ hρ.1 j)
    exact ⟨h1, ENNReal.toReal_mono hFe
      (h2.trans (mul_le_mul' le_rfl (add_le_add (hU ρ hρ 0) (hU ρ hρ 1))))⟩
  -- Uniform bounds on `clockNC⁻¹`, `modeDiag`, `physFrameLam`, `physLamDual`, `normPhysFrameLam`, `normPhysLamDual`
  obtain ⟨M_NC, M_diag, hM_NC0, hM_diag0, hNC_diag⟩ :=
    exists_clockNC_inv_and_modeDiag_bound P (s := s) hν0 ht
  set K_lam := (clockA ν s) ^ (3 / 2 : ℝ) * (2 * M_G * K₀)
  have hK_lam0 : 0 ≤ K_lam := by
    have ha_s : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν0.le (ht.trans hts))
    unfold K_lam; positivity
  set K_dual := (clockA ν s) ^ (3 / 2 : ℝ) *
    (C_h + C_e + max ‖seedModeEigen lam 0‖ ‖seedModeEigen lam 1‖ * (2 * M_G * K₀))
  have hK_dual0 : 0 ≤ K_dual := by
    have ha_s : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν0.le (ht.trans hts))
    unfold K_dual; positivity
  set M_φ := M_NC * K_lam
  have hM_φ0 : 0 ≤ M_φ := mul_nonneg hM_NC0 hK_lam0
  set M_ND := M_NC * K_dual + M_diag * M_φ
  have hM_ND0 : 0 ≤ M_ND := by unfold M_ND; positivity
  have hDualAll : ∀ r ∈ Icc t s, ∀ i : Fin 2,
      (MemLp (physFrameLam κ ν r i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (physFrameLam κ ν r i) ≤ ENNReal.ofReal K_lam) ∧
      (MemLp (physLamDual κ tr r i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (physLamDual κ tr r i) ≤ ENNReal.ofReal K_dual) ∧
      (MemLp (normPhysFrameLam κ P ν t r i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (normPhysFrameLam κ P ν t r i) ≤ ENNReal.ofReal M_φ) ∧
      (MemLp (normPhysLamDual κ P tr t r i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (normPhysLamDual κ P tr t r i) ≤ ENNReal.ofReal M_ND) := by
    intro r hr i
    have hr0 : 0 ≤ r := ht.trans hr.1
    have hθr : b ≤ clockTheta ν r := hbs.trans (theta_anti hν0 hr0 hr.2)
    have hθr1 : 1 ≤ clockTheta ν r := hb1.trans hθr
    have hd_D1 : D_1 ≤ cellLen c (clockA ν r) := cellLen_ge hD_pos.le hν0 hν_le_D hb1 hr0 hθr
    have hd1 : 1 ≤ cellLen c (clockA ν r) := le_trans hD_1 hd_D1
    obtain ⟨hPhysLam, hPhysDual⟩ := memLp_and_xNorm_physFrameLam_and_physLamDual κ lam
      hm hν0 hr0 hr.2 hθr1 hC_h0 hC_e0 hM_G0 hK₀ i
      (fun j => hLam0 (cellLen c (clockA ν r)) hd1 j)
      (fun j => hGramInv (cellLen c (clockA ν r)) hd_D1 i j)
      (hHeat_b ν ⟨hν0, hν_le_h⟩ r hr0 hθr i)
      (hEuler_b ν ⟨hν0, hν_le_e⟩ tr htr r hr0 hθr i)
    have hPhysDual' : MemLp (physLamDual κ tr r i) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (physLamDual κ tr r i) ≤ ENNReal.ofReal K_dual := by
      refine ⟨hPhysDual.1, hPhysDual.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      have ha_s : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν0.le (ht.trans hts))
      have heig : ‖seedModeEigen lam i‖ ≤ max ‖seedModeEigen lam 0‖ ‖seedModeEigen lam 1‖ := by
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
      unfold K_dual
      gcongr
    obtain ⟨hNormLam, hNormDual⟩ := memLp_and_xNorm_normPhysFrameLam_and_Dual κ P
      hν0 hr0 hK_lam0 hK_dual0 hM_NC0 hM_diag0 i (hNC_diag r hr i).1 (hNC_diag r hr i).2
      hPhysLam hPhysDual'
    exact ⟨hPhysLam, hPhysDual', hNormLam, hNormDual⟩
  -- Kernel adjoint uniform constant `M_ker` on `[0, s]`
  obtain ⟨M_ker, hM_ker0, hKerAll⟩ := kerAdj_memLp_and_transposition (K_Φ := M_φ)
    hm hc1 hC_tr0 hM_φ0 hBdd
  -- Prove both conjuncts for each mode `i : Fin 2`
  have hBoth : ∀ i : Fin 2,
      AEMeasurable (fun r => amplResidual κ P F tr w r i) (volume.restrict (Ioc t s)) ∧
      normAmpl F P t w s i - normAmpl F P t w t i =
        ∫ r in Ioc t s,
          (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
            ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i) := by
    intro i
    obtain ⟨hSmooth, M_g, hM_g0, hgrad_phys⟩ := hReg_b ν ⟨hν0, hν_le_reg⟩ t s ht hts hbs i
    set φ := fun r' x' => normPhysFrameLam κ P ν t r' i x'
    have hφ_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
        (Ico t (s + 1) ×ˢ univ) :=
      contDiffOn_normPhysFrameLam κ P hν0 ht i hSmooth
    have hφ_per : ∀ r ∈ Ico t (s + 1), ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x :=
      fun r hr x => normPhysFrameLam_periodic κ P hν0 (ht.trans hr.1) i x
    have hts1 : t < s + 1 := by linarith
    have hs_mem : s ∈ Ico t (s + 1) := ⟨hts, by linarith⟩
    have hprod : ∀ R : ℝ, 0 < R →
        IntervalIntegrable (fun ρ => ladRate tr w u φ R ρ) volume t s ∧
          ladCutPair c R w φ s - ladCutPair c R w φ t = ∫ ρ in t..s, ladRate tr w u φ R ρ :=
      fun R hR => ladProductRule ν c m tr t (s + 1) f w u φ hν0 hc0 ht hts1 hw ⟨Cl, hCl⟩
        hφ_smooth hφ_per R hR s hs_mem
    set M_rate := A_w * (M_ND + M_ker) + Fe.toReal * M_φ +
      (3 * |ν| * K_cut + 2 * C_tr * K_cut) * (A_w * M_φ + 2 * (A_w * (M_NC * M_g)))
    have hRate_pt : ∀ ρ ∈ Ioo t s,
        Tendsto (fun R : ℝ => ladRate tr w u φ R ρ) atTop
          (𝓝 ((((clockA ν ρ) ^ (-2 : ℝ) : ℝ) : ℂ) *
            ((clockNC P ν t ρ i)⁻¹ * amplResidual κ P F tr w ρ i))) ∧
        (∀ R : ℝ, 1 ≤ R → ‖ladRate tr w u φ R ρ‖ ≤ M_rate) := by
      intro ρ hρ
      have hρI : ρ ∈ Icc t s := ⟨hρ.1.le, hρ.2.le⟩
      have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨ht.trans hρ.1.le, hρ.2.le⟩
      have hD_ρ := hDualAll ρ hρI i
      have hK_ρ := hKerAll hρS hD_ρ.2.2.1.1 hD_ρ.2.2.1.2
      have hz_ρ : HasZeroCirculation c (w ρ) :=
        ladFlowZeroCirc m (by linarith) ν c tr t f w u hc1 hf0 hw ρ hρ.1.le
      exact ladRate_tendsto_and_bound κ P hm hν0 hν1 ht hts hρ hF
        hC_tr0 hA_w0 ENNReal.toReal_nonneg hM_NC0 hM_g0 hM_φ0 hM_ND0 hM_ker0
        hBdd hw (hA_w ρ hρI) (hforce ρ hρI).1 (hforce ρ hρI).2 i hSmooth
        (hNC_diag ρ hρI i).1 hD_ρ.1.1 hD_ρ.2.1.1 hD_ρ.2.2.1.1 hD_ρ.2.2.1.2
        hD_ρ.2.2.2.1 hD_ρ.2.2.2.2 hK_ρ.1.1 hK_ρ.1.2
        (hK_ρ.2 (w ρ) (u ρ) (hw.memX ρ hρ.1.le) hz_ρ (hw.biotSavart ρ hρ.1.le))
        (hgrad_phys ρ hρI) hK_cut0 hK_cut
    set g_lim : ℝ → ℂ := fun ρ =>
      (((clockA ν ρ) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((clockNC P ν t ρ i)⁻¹ * amplResidual κ P F tr w ρ i)
    have hI : Ι t s = Ioc t s := Set.uIoc_of_le hts
    -- 1. `AEMeasurable` of `amplResidual` on `volume.restrict (Ioc t s)`
    have haesm_g : AEStronglyMeasurable g_lim (volume.restrict (Ioc t s)) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun (n : ℕ) ρ => ladRate tr w u φ ((n : ℝ) + 1) ρ) (fun n => ?_) ?_
      · have hInt_n := (hprod ((n : ℝ) + 1) (by positivity)).1
        have h1 := (intervalIntegrable_iff.mp hInt_n).aestronglyMeasurable
        rwa [hI] at h1
      · rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [lad_ae_ne s] with ρ hρs hρ_Ioc
        have hρ_Ioo : ρ ∈ Ioo t s := ⟨hρ_Ioc.1, lt_of_le_of_ne hρ_Ioc.2 hρs⟩
        have h_atTop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        exact (hRate_pt ρ hρ_Ioo).1.comp h_atTop
    have haemeas_res : AEMeasurable (fun r => amplResidual κ P F tr w r i)
        (volume.restrict (Ioc t s)) := by
      have hsub_Ioc : Ioc t s ⊆ Ici 0 := fun r hr => ht.trans hr.1.le
      have hA_cont : ContinuousOn (fun r => (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ)) (Ioc t s) := by
        have h1 : Continuous (clockA ν) := by unfold clockA; fun_prop
        exact Complex.continuous_ofReal.comp_continuousOn
          (h1.continuousOn.rpow_const fun _ _ => Or.inr (by norm_num))
      have hNC_cont : ContinuousOn (fun r => clockNC P ν t r i) (Ioc t s) := by
        have h1 := (contDiffOn_clockNC_inv P hν0 ht i).continuousOn.mono hsub_Ioc
        have h2 := h1.inv₀ (fun r hr => inv_ne_zero (FrameAmplSub.clockNC_ne_zero P hν0 ht (ht.trans hr.1.le) i))
        exact h2.congr fun r _ => (inv_inv _).symm
      have hfac_aesm : AEStronglyMeasurable
          (fun r => (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * clockNC P ν t r i)
          (volume.restrict (Ioc t s)) :=
        (hA_cont.mul hNC_cont).aestronglyMeasurable measurableSet_Ioc
      have hprod_aesm : AEStronglyMeasurable
          (fun r => ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * clockNC P ν t r i) * g_lim r)
          (volume.restrict (Ioc t s)) := hfac_aesm.mul haesm_g
      refine (hprod_aesm.congr ?_).aemeasurable
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun r hr => ?_
      have hr0 : 0 ≤ r := ht.trans hr.1.le
      have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν0.le hr0)
      have ha_cancel : (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add ha0]
        norm_num
      have hNC_cancel : clockNC P ν t r i * (clockNC P ν t r i)⁻¹ = 1 :=
        mul_inv_cancel₀ (FrameAmplSub.clockNC_ne_zero P hν0 ht hr0 i)
      unfold g_lim
      calc ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * clockNC P ν t r i) *
            ((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
              ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i))
          = ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)) *
              (clockNC P ν t r i * (clockNC P ν t r i)⁻¹) * amplResidual κ P F tr w r i := by
            ring
        _ = amplResidual κ P F tr w r i := by
            rw [ha_cancel, hNC_cancel, one_mul, one_mul]
    -- 2. Dominated convergence on `t..s` as `R → ∞`
    have hlimInt : Tendsto (fun R : ℝ => ∫ ρ in t..s, ladRate tr w u φ R ρ) atTop
        (𝓝 (∫ ρ in t..s, g_lim ρ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (l := atTop) (f := g_lim)
        (F := fun R ρ => ladRate tr w u φ R ρ) (fun _ => M_rate) ?_ ?_
        intervalIntegrable_const ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        exact (intervalIntegrable_iff.mp (hprod R hR).1).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        filter_upwards [lad_ae_ne s] with ρ hρs hρI
        rw [hI] at hρI
        exact (hRate_pt ρ ⟨hρI.1, lt_of_le_of_ne hρI.2 hρs⟩).2 R hR
      · filter_upwards [lad_ae_ne s] with ρ hρs hρI
        rw [hI] at hρI
        exact (hRate_pt ρ ⟨hρI.1, lt_of_le_of_ne hρI.2 hρs⟩).1
    have hcuts : Tendsto (fun R : ℝ => ladCutPair c R w φ s) atTop (𝓝 (ladPair c w φ s)) :=
      ladCutLimit c m (w s) (φ s) (hw.memX s hts) (hDualAll s ⟨hts, le_rfl⟩ i).2.2.1.1
    have hcutt : Tendsto (fun R : ℝ => ladCutPair c R w φ t) atTop (𝓝 (ladPair c w φ t)) :=
      ladCutLimit c m (w t) (φ t) (hw.memX t le_rfl) (hDualAll t ⟨le_rfl, hts⟩ i).2.2.1.1
    have hdiff_lim : Tendsto (fun R : ℝ => ladCutPair c R w φ s - ladCutPair c R w φ t) atTop
        (𝓝 (∫ ρ in t..s, g_lim ρ)) := by
      refine hlimInt.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact ((hprod R hR).2).symm
    have heq_pair : ladPair c w φ s - ladPair c w φ t = ∫ ρ in t..s, g_lim ρ :=
      tendsto_nhds_unique (hcuts.sub hcutt) hdiff_lim
    rw [← normAmpl_eq_ladPair κ P hν0 (ht.trans hts) hF w i,
      ← normAmpl_eq_ladPair κ P hν0 ht hF w i,
      intervalIntegral.integral_of_le hts] at heq_pair
    exact ⟨haemeas_res, heq_pair⟩
  exact ⟨fun i => (hBoth i).1, fun i => (hBoth i).2⟩

/-- Conditional proof of `NormAmplCutFTC κ` (`PartIII-a:T21/c5/1/1`) from
`SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`) and `PhysFrameLamSmooth κ`
(`PartIII-a:T21/c5/1/1/2`). -/
theorem normAmplCutFTC_of (κ : PlanarFrameKernels)
    (hGrad : SeedLamGradPerSum κ) (hSmooth : PhysFrameLamSmooth κ) :
    NormAmplCutFTC κ :=
  normAmplCutFTC_of_reg κ (CutFTCAux.physFrameLamRegularity_of κ hGrad hSmooth)

end UnforcedLeray.Short.IIIa
