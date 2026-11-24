import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Transpose
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Unfold

/-!
# Helpers for `PartII-a:N05/2/2/1`: cell `L²` bounds, scalar tests and periodization

Source: `the November 2 reference manuscript`, lines 1794-1799.

* `lintegral_ksmul_le`, `memLp_ksmul`: an age cutoff `k(s)` supported in `s ≤ b` maps `H` into
  `L²(cellMeasure c)`, `‖k w‖² ≤ K² b^{3/2} ‖w‖²_H` (the weight `s^{-3/2}` is `≥ b^{-3/2}`).
* `memLp_of_cont_band`, `integrable_inner_band`: continuous band-supported fields are square
  integrable on the cell and pair integrably with `k(s) w`.
* `vecOf i h = h e_i`: a real scalar test in the component `i`, with its derivatives.
* `perT_lincomb`, `perT_qCut_mul`: the `q`-periodization of tests is linear and inverts the
  multiplication by the partition function `qCut`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure weightH cell periodize QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)
open UnforcedLeray.Short.IIb (Coord cpd cdir)

/-! ### Age cutoffs of `H` fields in the cell measure -/

theorem eLpNorm_two_rpow_two {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
  simpa using h

theorem lintegral_measureH_sq {c : ℝ} (V : HSpace c MeridC) :
    ∫⁻ p, ‖(V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) = ENNReal.ofReal (‖V‖ ^ 2) := by
  have h := Lp.eLpNorm_ne_top V
  rw [← eLpNorm_two_rpow_two, Lp.norm_def, ← ENNReal.ofReal_toReal h,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), Real.rpow_two,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

theorem integrable_inner_cell {c : ℝ} {f g : Profile → MeridC}
    (hf : MemLp f 2 (cellMeasure c)) (hg : MemLp g 2 (cellMeasure c)) :
    Integrable (fun p => inner ℂ (f p) (g p)) (cellMeasure c) := by
  have hfg : Integrable (fun p => ‖f p‖ * ‖g p‖) (cellMeasure c) :=
    hf.norm.integrable_mul hg.norm
  exact hfg.mono' (hf.1.inner hg.1) (Eventually.of_forall fun p => norm_inner_le_norm (f p) (g p))

theorem enorm_sq_ksmul_le {b K : ℝ} {k : ℝ → ℝ} (hK : ∀ s, |k s| ≤ K)
    (hk0 : ∀ s, b < s → k s = 0) (p : Profile) (hp : 0 < p.1) (v : MeridC) :
    ‖k p.1 • v‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (K ^ 2 * (1 + b) ^ 2) * (weightH p * ‖v‖ₑ ^ (2 : ℝ)) := by
  by_cases hpb : b < p.1
  · simp [hk0 _ hpb]
  · push_neg at hpb
    have hb : 0 < b := lt_of_lt_of_le hp hpb
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc]
    gcongr
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), weightH,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ‖k p.1‖ ^ (2 : ℝ) ≤ K ^ 2 := by
      rw [Real.rpow_two, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK _) 2
    have h1b : (1 : ℝ) ≤ 1 + b := by linarith
    have hrpow : p.1 ^ (3 / 2 : ℝ) ≤ (1 + b) ^ 2 := by
      calc p.1 ^ (3 / 2 : ℝ)
          ≤ (1 + b) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hp.le (by linarith) (by norm_num)
        _ ≤ (1 + b) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1b (by norm_num)
        _ = (1 + b) ^ 2 := Real.rpow_two (1 + b)
    have h2 : 1 ≤ (1 + b) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) := by
      calc (1 : ℝ)
          = p.1 ^ (3 / 2 : ℝ) * p.1 ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_add hp]; norm_num
        _ ≤ (1 + b) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hp.le _)
    calc ‖k p.1‖ ^ (2 : ℝ) ≤ K ^ 2 * 1 := by rw [mul_one]; exact h1
      _ ≤ K ^ 2 * ((1 + b) ^ 2 * p.1 ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg K)
      _ = K ^ 2 * (1 + b) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) := by ring

/-- **Age cutoffs**: `∫_cell |k(s) w|² ≤ K² (1 + b)² ‖w‖²_H` for `|k| ≤ K`, `k = 0` on `s > b`. -/
theorem lintegral_ksmul_le {c b K : ℝ} (V : HSpace c MeridC) {k : ℝ → ℝ}
    (hK : ∀ s, |k s| ≤ K) (hk0 : ∀ s, b < s → k s = 0) :
    ∫⁻ p, ‖k p.1 • (V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (K ^ 2 * (1 + b) ^ 2) * ENNReal.ofReal (‖V‖ ^ 2) := by
  have hV : Measurable (V : Profile → MeridC) := (Lp.stronglyMeasurable V).measurable
  calc ∫⁻ p, ‖k p.1 • (V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ∫⁻ p, ENNReal.ofReal (K ^ 2 * (1 + b) ^ 2) *
          (weightH p * ‖(V : Profile → MeridC) p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_cell c] with p hp
        exact enorm_sq_ksmul_le hK hk0 p hp.1 _
    _ = ENNReal.ofReal (K ^ 2 * (1 + b) ^ 2) *
          ∫⁻ p, ‖(V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
        have hmeas : Measurable fun p : Profile =>
            weightH p * ‖(V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) :=
          UnforcedLeray.B0220.measurable_weightH.mul (hV.enorm.pow_const _)
        have hwd : ∫⁻ p, ‖(V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
            ∫⁻ p, weightH p * ‖(V : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH
            (hV.enorm.pow_const _)
        rw [lintegral_const_mul _ hmeas, hwd]
    _ = _ := by rw [lintegral_measureH_sq V]

/-- `‖f‖_{L²} ≤ X` from `∫ |f|² ≤ X²`. -/
theorem eLpNorm_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] {f : α → E} {X : ℝ} (hX : 0 ≤ X)
    (h : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal (X ^ 2)) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal X := by
  rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2), eLpNorm_two_rpow_two,
    ENNReal.ofReal_rpow_of_nonneg hX (by norm_num), Real.rpow_two]
  exact h

theorem eLpNorm_ksmul_le {c b K : ℝ} (hK0 : 0 ≤ K) (hb : 0 ≤ b) (V : HSpace c MeridC)
    {k : ℝ → ℝ} (hK : ∀ s, |k s| ≤ K) (hk0 : ∀ s, b < s → k s = 0) :
    eLpNorm (fun p : Profile => k p.1 • (V : Profile → MeridC) p) 2 (cellMeasure c) ≤
      ENNReal.ofReal (K * (1 + b) * ‖V‖) := by
  refine eLpNorm_le_of_lintegral_le (by positivity) ((lintegral_ksmul_le V hK hk0).trans ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg V]

theorem memLp_two_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ⊤) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

theorem memLp_ksmul {c b K : ℝ} (V : HSpace c MeridC) {k : ℝ → ℝ} (hk : Measurable k)
    (hK : ∀ s, |k s| ≤ K) (hk0 : ∀ s, b < s → k s = 0) :
    MemLp (fun p : Profile => k p.1 • (V : Profile → MeridC) p) 2 (cellMeasure c) :=
  memLp_two_of_lintegral
    ((hk.comp measurable_fst).aestronglyMeasurable.smul
      (Lp.stronglyMeasurable V).aestronglyMeasurable)
    ((lintegral_ksmul_le V hK hk0).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

/-! ### Band-supported fields -/

/-- A continuous field supported in a band `s ∈ [s₀, s₁]`, `|η| ≤ L` is square integrable on the
cell. -/
theorem memLp_of_cont_band {c : ℝ} {E : Type*} [NormedAddCommGroup E] {f : Profile → E}
    (hf : Continuous f) {s0 s1 L : ℝ}
    (hband : ∀ p, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    MemLp f 2 (cellMeasure c) := by
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKm : MeasurableSet K :=
    measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hKfin : volume K < ⊤ := hK.measure_lt_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  let M : ℝ := max C 0
  refine memLp_two_of_lintegral hf.aestronglyMeasurable ?_
  have hbound : ∀ᵐ p ∂(cellMeasure c), ‖f p‖ₑ ^ (2 : ℝ) ≤
      K.indicator (fun _ => ENNReal.ofReal (M ^ 2)) p := by
    filter_upwards [ae_mem_cell c] with p hpcell
    by_cases hp0 : f p = 0
    · simp [hp0]
    · obtain ⟨hs, hη⟩ := hband p hp0
      have hpK : p ∈ K := ⟨hs, Ioc_subset_Icc_self hpcell.2.1, abs_le.1 hη⟩
      rw [indicator_of_mem hpK, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) ((hC p hpK).trans (le_max_left C 0)) 2)
  calc ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal (M ^ 2)) p ∂(cellMeasure c) :=
        lintegral_mono_ae hbound
    _ ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal (M ^ 2)) p ∂volume :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (M ^ 2) * volume K := lintegral_indicator_const hKm _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin

/-- A continuous band field pairs integrably with `k(s) w`, `k` bounded on the band. -/
theorem integrable_inner_band {c : ℝ} (V : HSpace c MeridC) {Ψ : Profile → MeridC}
    (hΨ : Continuous Ψ) {s0 s1 L : ℝ} (hband : ∀ p, Ψ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    {k : ℝ → ℝ} (hk : Measurable k) {K : ℝ} (hK : ∀ s ∈ Icc s0 s1, |k s| ≤ K) :
    Integrable (fun p => inner ℂ (Ψ p) (k p.1 • (V : Profile → MeridC) p)) (cellMeasure c) := by
  have hK0 : ∀ s, |(Icc s0 s1).indicator k s| ≤ max K 0 := by
    intro s
    by_cases hs : s ∈ Icc s0 s1
    · rw [indicator_of_mem hs]
      exact (hK s hs).trans (le_max_left _ _)
    · rw [indicator_of_notMem hs, abs_zero]
      exact le_max_right _ _
  have hk0 : ∀ s, s1 < s → (Icc s0 s1).indicator k s = 0 := fun s hs =>
    indicator_of_notMem (fun h => absurd h.2 (not_le.2 hs)) _
  have hm := memLp_ksmul (c := c) V (hk.indicator measurableSet_Icc) hK0 hk0
  have hint := integrable_inner_cell
    (memLp_of_cont_band hΨ hband) hm
  refine hint.congr (Eventually.of_forall fun p => ?_)
  by_cases hp : Ψ p = 0
  · simp [hp]
  · simp only
    rw [indicator_of_mem (hband p hp).1]

/-- Partial derivatives of a band field are band fields. -/
theorem band_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    {s0 s1 L : ℝ} (hband : ∀ p, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (v : Profile) :
    ∀ p, fderiv ℝ f p v ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  intro p hp
  by_contra hout
  have hclosed : IsClosed {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hev : f =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hout] with q hq
    by_contra h
    exact hq (hband q h)
  apply hp
  rw [hev.fderiv_eq, fderiv_const_apply]
  rfl

/-! ### Scalar tests in one component -/

/-- The unit vector `e_i` of `ℂ²`. -/
def eVec (i : Fin 2) : MeridC := EuclideanSpace.single i (1 : ℂ)

/-- The real scalar profile `h` placed in the component `i`. -/
def vecOf (i : Fin 2) (h : Profile → ℝ) : Profile → MeridC := fun p => h p • eVec i

theorem inner_vecOf (i : Fin 2) (h : Profile → ℝ) (p : Profile) (v : MeridC) :
    inner ℂ (vecOf i h p) v = (h p : ℂ) * v i := by
  rw [vecOf, inner_real_smul_left, eVec, EuclideanSpace.inner_single_left, map_one, one_mul]

theorem fderiv_vecOf (i : Fin 2) {h : Profile → ℝ} {p : Profile} (hh : DifferentiableAt ℝ h p)
    (w : Profile) : fderiv ℝ (vecOf i h) p w = fderiv ℝ h p w • eVec i := by
  unfold vecOf
  rw [fderiv_smul_const hh]
  simp

theorem pdS_vecOf (i : Fin 2) {h : Profile → ℝ} (hh : Differentiable ℝ h) :
    pdS (vecOf i h) = vecOf i (pdS h) := by
  funext p
  exact fderiv_vecOf i (hh p) _

theorem pdQ_vecOf (i : Fin 2) {h : Profile → ℝ} (hh : Differentiable ℝ h) :
    pdQ (vecOf i h) = vecOf i (pdQ h) := by
  funext p
  exact fderiv_vecOf i (hh p) _

theorem pdEta_vecOf (i : Fin 2) {h : Profile → ℝ} (hh : Differentiable ℝ h) :
    pdEta (vecOf i h) = vecOf i (pdEta h) := by
  funext p
  exact fderiv_vecOf i (hh p) _

theorem contDiff_pdS' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Profile → E}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pdS F) := by
  unfold pdS
  exact (hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem contDiff_pdQ' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Profile → E}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pdQ F) := by
  unfold pdQ
  exact (hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem contDiff_pdEta' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Profile → E}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pdEta F) := by
  unfold pdEta
  exact (hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- The real `Δ_{q,η}`. -/
def lapR (h : Profile → ℝ) : Profile → ℝ := fun p => pdQ (pdQ h) p + pdEta (pdEta h) p

theorem lapQE_vecOf (i : Fin 2) {h : Profile → ℝ} (hh : ContDiff ℝ ∞ h) :
    lapQE (vecOf i h) = vecOf i (lapR h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hdQ : Differentiable ℝ (pdQ h) := (contDiff_pdQ' hh).differentiable (by simp)
  have hdE : Differentiable ℝ (pdEta h) := (contDiff_pdEta' hh).differentiable (by simp)
  funext p
  simp only [lapQE, lapR]
  rw [pdQ_vecOf i hd, pdQ_vecOf i hdQ, pdEta_vecOf i hd, pdEta_vecOf i hdE]
  simp only [vecOf]
  rw [show lapR h p = pdQ (pdQ h) p + pdEta (pdEta h) p from rfl, add_smul]

theorem isMeridTest_vecOf {c : ℝ} (i : Fin 2) {h : Profile → ℝ} (hh : ContDiff ℝ ∞ h)
    (hper : QPeriodic c h) {s0 s1 L : ℝ} (hs0 : 0 < s0)
    (hband : ∀ p, h p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    IsMeridTest c (vecOf i h) where
  smooth := hh.smul contDiff_const
  periodic p := by simp only [vecOf, hper p]
  band := ⟨s0, s1, L, hs0, fun p hp => hband p fun h0 => hp (by simp [vecOf, h0])⟩

/-! ### Periodization of tests -/

theorem qbound_of_compact {φ : Coord → ℝ} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ x : Coord, R < |x.2.1| → φ x = 0 := by
  obtain ⟨R, -, hR⟩ := exists_qbound hφ
  exact ⟨R, fun x hx => eq_zero_of_qbound hR hx⟩

/-- `perT` is linear on compactly supported tests. -/
theorem perT_lincomb {c : ℝ} (hc : 0 < c) {A B D : Coord → ℝ} (hA : HasCompactSupport A)
    (hB : HasCompactSupport B) (hD : HasCompactSupport D) (ν : ℝ) :
    perT c (fun x => -A x - ν * (B x + D x)) =
      fun x => -perT c A x - ν * (perT c B x + perT c D x) := by
  obtain ⟨RA, hRA⟩ := qbound_of_compact hA
  obtain ⟨RB, hRB⟩ := qbound_of_compact hB
  obtain ⟨RD, hRD⟩ := qbound_of_compact hD
  set R := max (max RA RB) RD with hR
  have hA' : ∀ x : Coord, R < |x.2.1| → A x = 0 := fun x hx =>
    hRA x (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hx)
  have hB' : ∀ x : Coord, R < |x.2.1| → B x = 0 := fun x hx =>
    hRB x (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hx)
  have hD' : ∀ x : Coord, R < |x.2.1| → D x = 0 := fun x hx =>
    hRD x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hF : ∀ x : Coord, R < |x.2.1| → -A x - ν * (B x + D x) = 0 := fun x hx => by
    rw [hA' x hx, hB' x hx, hD' x hx]
    ring
  funext x
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + |x.2.1|) / c)
  have hN' : R + |x.2.1| ≤ N * c := by rwa [div_le_iff₀ hc] at hN
  rw [perT_eq_sum hc hF hN' le_rfl, perT_eq_sum hc hA' hN' le_rfl, perT_eq_sum hc hB' hN' le_rfl,
    perT_eq_sum hc hD' hN' le_rfl, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, Finset.sum_add_distrib]

/-- `Σ_k qCut(q + (k - N)c) = 1` for `|q| ≤ Nc`. -/
theorem sum_qCut_plus {c : ℝ} (hc : 0 < c) (N : ℕ) {q : ℝ} (hq : |q| ≤ N * c) :
    ∑ k ∈ Finset.range (2 * N + 1), qCut c (q + ((((k : ℤ) - N : ℤ) : ℝ)) * c) = 1 := by
  have h := sum_qCut hc N hq
  rw [← Finset.sum_range_reflect] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- `perT (qCut · a) = a` for a `q`-periodic `a`. -/
theorem perT_qCut_mul {c : ℝ} (hc : 0 < c) {a : Coord → ℝ} (hper : ∀ x, a (x + qv c) = a x) :
    perT c (fun x => qCut c x.2.1 * a x) = a := by
  have hF : ∀ x : Coord, c < |x.2.1| → qCut c x.2.1 * a x = 0 := by
    intro x hx
    have hq : x.2.1 ∉ Ioc (-c) c := fun h => by
      have := abs_le.2 ⟨h.1.le, h.2⟩
      linarith
    rw [qCut_eq_zero_of_not_mem hc hq, zero_mul]
  funext x
  obtain ⟨N, hN⟩ := exists_nat_ge ((c + |x.2.1|) / c)
  have hN' : c + |x.2.1| ≤ N * c := by rwa [div_le_iff₀ hc] at hN
  rw [perT_eq_sum hc hF hN' le_rfl]
  have hterm : ∀ k ∈ Finset.range (2 * N + 1),
      qCut c (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c)).2.1 *
          a (x + qv ((((k : ℤ) - N : ℤ) : ℝ) * c)) =
        qCut c (x.2.1 + ((((k : ℤ) - N : ℤ) : ℝ)) * c) * a x := by
    intro k _
    rw [add_qv_snd_fst, periodic_int hper]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    sum_qCut_plus hc N (by linarith [abs_nonneg x.2.1] : |x.2.1| ≤ N * c), one_mul]

end UnforcedLeray.Short.PartIIa.FBCLL
