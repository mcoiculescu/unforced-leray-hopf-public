import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Smooth approximation of `L²_m` data vanishing on a cell (helper for `RelExteriorBlockBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2974-2980
("the localized interaction is compact by source and observation truncation").

`exists_smooth_approx_vanishing`: every `V ∈ L²_m` vanishing a.e. on the strip `B0579.cell d`
(`d > 0`) is an `L²_m`-limit of smooth compactly supported functions that vanish identically on the
closed strip `|Re z| ≤ d/2` (cutoff `stripCut d k` times a Mathlib smooth approximant, dominated
convergence for the cutoff error; the line `Re z = d/2` is Lebesgue-null).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace RelExteriorSub

/-- Smooth cutoff `χ_k(z) = s(k (Re z² - d²/4) - 1)`: it vanishes on the closed strip
`|Re z| ≤ d/2` and is eventually `1` off it. -/
def stripCut (d : ℝ) (k : ℕ) (z : ℂ) : ℝ :=
  Real.smoothTransition ((k : ℝ) * (z.re ^ 2 - d ^ 2 / 4) - 1)

theorem contDiff_re : ContDiff ℝ ∞ (fun z : ℂ => z.re) :=
  Complex.reCLM.contDiff

theorem contDiff_stripCut (d : ℝ) (k : ℕ) : ContDiff ℝ ∞ (stripCut d k) := by
  unfold stripCut
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul ((contDiff_re.pow 2).sub contDiff_const)).sub contDiff_const)

theorem stripCut_nonneg (d : ℝ) (k : ℕ) (z : ℂ) : 0 ≤ stripCut d k z :=
  Real.smoothTransition.nonneg _

theorem stripCut_le_one (d : ℝ) (k : ℕ) (z : ℂ) : stripCut d k z ≤ 1 :=
  Real.smoothTransition.le_one _

theorem stripCut_eq_zero {d : ℝ} (k : ℕ) {z : ℂ} (hz : z.re ^ 2 ≤ d ^ 2 / 4) :
    stripCut d k z = 0 := by
  unfold stripCut
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk (sub_nonpos.2 hz)]

theorem stripCut_eventually_one {d : ℝ} {z : ℂ} (hz : d ^ 2 / 4 < z.re ^ 2) :
    ∀ᶠ k : ℕ in atTop, stripCut d k z = 1 := by
  have ha : 0 < z.re ^ 2 - d ^ 2 / 4 := by linarith
  refine eventually_atTop.2 ⟨⌈2 / (z.re ^ 2 - d ^ 2 / 4)⌉₊, fun k hk => ?_⟩
  unfold stripCut
  apply Real.smoothTransition.one_of_one_le
  have h1 : 2 / (z.re ^ 2 - d ^ 2 / 4) ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have h2 : 2 ≤ (k : ℝ) * (z.re ^ 2 - d ^ 2 / 4) := by
    rwa [div_le_iff₀ ha] at h1
  linarith

/-- The vertical line `Re z = c` is Lebesgue-null. -/
theorem volume_re_eq (c : ℝ) : (volume : Measure ℂ) {z : ℂ | z.re = c} = 0 := by
  have hset : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem contDiff_planeToC : ContDiff ℝ ∞ planeToC :=
  (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).contDiff

theorem continuous_cToPlane : Continuous cToPlane :=
  Complex.continuous_re.prodMk Complex.continuous_im

/-- **Approximation lemma.** If `V ∈ L²_m` vanishes a.e. on `B0579.cell d` (`d > 0`), then for
every `ε > 0` there is a smooth compactly supported `Φ` on the plane, vanishing on the cell, whose
`L²_m` class is `ε`-close to `V`. -/
theorem exists_smooth_approx_vanishing {m d : ℝ} (hd : 0 < d) (V : Planar.L2w m)
    (hV : ∀ᵐ z ∂(volume : Measure ℂ), cToPlane z ∈ B0579.cell d → (V : ℂ → ℂ) z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ (∀ y ∈ B0579.cell d, Φ y = 0) ∧
      ∃ W : Planar.L2w m, (⇑W =ᵐ[volume] fun z => Φ (cToPlane z)) ∧ ‖W - V‖ < ε := by
  classical
  have : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  -- `V` vanishes a.e. on the closed strip `|Re z| ≤ d/2`.
  have hline : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ {z : ℂ | z.re = d / 2} :=
    measure_eq_zero_iff_ae_notMem.1 (volume_re_eq (d / 2))
  have hV2 : ∀ᵐ z ∂(Planar.wMeasure m), z.re ^ 2 ≤ d ^ 2 / 4 → (V : ℂ → ℂ) z = 0 := by
    have h' : ∀ᵐ z ∂(volume : Measure ℂ), z.re ^ 2 ≤ d ^ 2 / 4 → (V : ℂ → ℂ) z = 0 := by
      filter_upwards [hV, hline] with z hz hl hsq
      apply hz
      have hsq' : z.re ^ 2 ≤ (d / 2) ^ 2 := by nlinarith
      have hab := abs_le_of_sq_le_sq' hsq' (by linarith)
      have hne : z.re ≠ d / 2 := hl
      simp only [B0579.cell, cToPlane, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true]
      exact ⟨hab.1, lt_of_le_of_ne hab.2 hne⟩
    exact (Planar.wMeasure_ac m).ae_le h'
  -- Dominated convergence for the cutoff error `(1 - χ_k) V`.
  have hVm : AEStronglyMeasurable (V : ℂ → ℂ) (Planar.wMeasure m) := Lp.aestronglyMeasurable V
  have hcut_cont : ∀ k : ℕ, Continuous fun z : ℂ => ((1 - stripCut d k z : ℝ) : ℂ) := fun k =>
    Complex.continuous_ofReal.comp (continuous_const.sub (contDiff_stripCut d k).continuous)
  set F : ℕ → ℂ → ℝ≥0∞ := fun k z =>
    ‖((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z‖ₑ ^ (2 : ℝ) with hFdef
  have hF_meas : ∀ k, AEMeasurable (F k) (Planar.wMeasure m) := fun k =>
    ((((hcut_cont k).aestronglyMeasurable.mul hVm).enorm).pow_const _)
  have hF_bound : ∀ k, F k ≤ᵐ[Planar.wMeasure m] fun z => ‖(V : ℂ → ℂ) z‖ₑ ^ (2 : ℝ) :=
    fun k => Eventually.of_forall fun z => by
      have h0 := stripCut_nonneg d k z
      have h1 := stripCut_le_one d k z
      have hle : ‖((1 - stripCut d k z : ℝ) : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
        exact ENNReal.ofReal_le_one.2 (by linarith)
      simp only [hFdef]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [enorm_mul]
      calc ‖((1 - stripCut d k z : ℝ) : ℂ)‖ₑ * ‖(V : ℂ → ℂ) z‖ₑ
          ≤ 1 * ‖(V : ℂ → ℂ) z‖ₑ := by gcongr
        _ = ‖(V : ℂ → ℂ) z‖ₑ := one_mul _
  have h_fin : ∫⁻ z, ‖(V : ℂ → ℂ) z‖ₑ ^ (2 : ℝ) ∂(Planar.wMeasure m) ≠ (⊤ : ℝ≥0∞) := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
      ENNReal.ofNat_ne_top (Lp.eLpNorm_lt_top V)
    simpa using this.ne
  have h_lim : ∀ᵐ z ∂(Planar.wMeasure m), Tendsto (fun k => F k z) atTop (𝓝 0) := by
    filter_upwards [hV2] with z hz
    by_cases hz2 : z.re ^ 2 ≤ d ^ 2 / 4
    · have h0 : (V : ℂ → ℂ) z = 0 := hz hz2
      simp only [hFdef, h0, mul_zero, enorm_zero]
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
      exact tendsto_const_nhds
    · replace hz2 := not_le.1 hz2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [stripCut_eventually_one hz2] with k hk
      simp only [hFdef, hk, sub_self, Complex.ofReal_zero, zero_mul, enorm_zero]
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  have hlim := tendsto_lintegral_of_dominated_convergence' _ hF_meas hF_bound h_fin h_lim
  rw [lintegral_zero] at hlim
  have hlim2 : Tendsto (fun k : ℕ =>
      eLpNorm (fun z => ((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z) 2 (Planar.wMeasure m))
      atTop (𝓝 0) := by
    have hc := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp hlim
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    refine hc.congr (fun k => ?_)
    simp only [Function.comp_apply]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp [hFdef]
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨k, hk⟩ := (hlim2.eventually (gt_mem_nhds hη)).exists
  -- A smooth compactly supported approximant of `V`.
  obtain ⟨Ψ₀, hΨc, hΨs, hΨerr⟩ := (Lp.memLp V).exist_eLpNorm_sub_le (p := 2)
    ENNReal.ofNat_ne_top (by norm_num) (ε := ε / 3) (by linarith)
  set Ψ : ℂ → ℂ := fun z => ((stripCut d k z : ℝ) : ℂ) * Ψ₀ z with hΨdef
  have hΨsmooth : ContDiff ℝ ∞ Ψ :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_stripCut d k)).mul hΨs
  have hΨsupp : HasCompactSupport Ψ := hΨc.mul_left
  have hΨmem : MemLp Ψ 2 (Planar.wMeasure m) :=
    hΨsmooth.continuous.memLp_of_hasCompactSupport hΨsupp
  refine ⟨fun y => Ψ (planeToC y), hΨsmooth.comp contDiff_planeToC, ?_, ?_,
    hΨmem.toLp Ψ, ?_, ?_⟩
  · refine HasCompactSupport.intro (K := cToPlane '' tsupport Ψ)
      (hΨsupp.isCompact.image continuous_cToPlane) fun y hy => ?_
    have : planeToC y ∉ tsupport Ψ := fun h => hy ⟨planeToC y, h, cToPlane_planeToC y⟩
    exact image_eq_zero_of_notMem_tsupport this
  · intro y hy
    simp only [B0579.cell, Set.mem_prod, Set.mem_Ico] at hy
    have hre : (planeToC y).re = y.1 := rfl
    have hsq : (planeToC y).re ^ 2 ≤ d ^ 2 / 4 := by
      rw [hre]; nlinarith [hy.1.1, hy.1.2]
    simp only [hΨdef, stripCut_eq_zero k hsq, Complex.ofReal_zero, zero_mul]
  · have h1 := (Planar.volume_ac m).ae_le hΨmem.coeFn_toLp
    filter_upwards [h1] with z hz
    rw [hz, planeToC_cToPlane]
  · -- the error estimate
    have hsplit : (Ψ - (V : ℂ → ℂ)) = (fun z => ((stripCut d k z : ℝ) : ℂ) * (Ψ₀ z - V z)) +
        (fun z => -(((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z)) := by
      funext z
      simp only [hΨdef, Pi.sub_apply, Pi.add_apply, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hcutm : Continuous fun z : ℂ => ((stripCut d k z : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (contDiff_stripCut d k).continuous
    have hA : AEStronglyMeasurable (fun z => ((stripCut d k z : ℝ) : ℂ) * (Ψ₀ z - V z))
        (Planar.wMeasure m) :=
      hcutm.aestronglyMeasurable.mul (hΨs.continuous.aestronglyMeasurable.sub hVm)
    have hB : AEStronglyMeasurable (fun z => -(((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z))
        (Planar.wMeasure m) :=
      ((hcut_cont k).aestronglyMeasurable.mul hVm).neg
    have hle1 : eLpNorm (fun z => ((stripCut d k z : ℝ) : ℂ) * (Ψ₀ z - V z)) 2
        (Planar.wMeasure m) ≤ ENNReal.ofReal (ε / 3) := by
      refine (eLpNorm_mono (g := fun z => Ψ₀ z - V z) fun z => ?_).trans ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (stripCut_nonneg d k z)]
        exact mul_le_of_le_one_left (norm_nonneg _) (stripCut_le_one d k z)
      · have : (fun z => Ψ₀ z - V z) = Ψ₀ - (V : ℂ → ℂ) := rfl
        rw [this, eLpNorm_sub_comm]
        exact hΨerr
    have hle2 : eLpNorm (fun z => -(((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z)) 2
        (Planar.wMeasure m) < ENNReal.ofReal (ε / 3) := by
      have : (fun z => -(((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z)) =
          -(fun z => ((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z) := rfl
      rw [this, eLpNorm_neg]
      exact hk
    have htot : eLpNorm (Ψ - (V : ℂ → ℂ)) 2 (Planar.wMeasure m) <
        ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
      rw [hsplit]
      calc eLpNorm ((fun z => ((stripCut d k z : ℝ) : ℂ) * (Ψ₀ z - V z)) +
            (fun z => -(((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z))) 2 (Planar.wMeasure m)
          ≤ eLpNorm (fun z => ((stripCut d k z : ℝ) : ℂ) * (Ψ₀ z - V z)) 2 (Planar.wMeasure m) +
            eLpNorm (fun z => -(((1 - stripCut d k z : ℝ) : ℂ) * (V : ℂ → ℂ) z)) 2
              (Planar.wMeasure m) := eLpNorm_add_le hA hB (by norm_num)
        _ < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
          ENNReal.add_lt_add_of_le_of_lt (hle1.trans_lt ENNReal.ofReal_lt_top).ne hle1 hle2
    have hcongr : eLpNorm (⇑(hΨmem.toLp Ψ - V)) 2 (Planar.wMeasure m) =
        eLpNorm (Ψ - (V : ℂ → ℂ)) 2 (Planar.wMeasure m) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (hΨmem.toLp Ψ) V, hΨmem.coeFn_toLp] with z h1 h2
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply]
    rw [Lp.norm_def, hcongr]
    have h3 : ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) = ENNReal.ofReal (2 * ε / 3) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
    rw [h3] at htot
    exact (ENNReal.toReal_lt_of_lt_ofReal htot).trans (by linarith)

end RelExteriorSub

end UnforcedLeray.Short.IIIa
