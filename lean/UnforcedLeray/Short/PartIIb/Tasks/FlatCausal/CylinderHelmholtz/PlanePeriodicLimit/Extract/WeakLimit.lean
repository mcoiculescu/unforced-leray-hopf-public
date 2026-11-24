import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_2
import UnforcedLeray.Infra.WeaklyNullCompact.Extraction
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Part II-b, leaf `PartII-b:T12/1/4/2/1` (`PPLWeakLimit`): weak extraction on the windows

Source of record: `the November 2 reference manuscript` lines 1933-1935.

Strategy. All windows are handled at once by one weighted Hilbert space `L²(μ)`,
`μ = vol.withDensity w`, with the window weight `w z = ∑_M a_M 1_{W_M}(z)`,
`a_M = 2^{-(M+1)} / (M+1)`. The weight is positive on each window (`≥ a_M` on `W_M`) and at most
`1`, and `∑_M 2^{-(M+1)} M/(M+1) ≤ 1` gives a uniform `L²(μ)` bound for `H N` from `bound2`.
One weak subsequence limit `x` in `L²(μ)` exists (`Infra.WeaklyNullCompact.exists_subseq_weakTendsto`),
and testing against `ψ̄ / w` on `W_M` gives the window pairings of `PPLWeak`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Window weights `a_M = 2^{-(M+1)} / (M+1)`. -/
def ppA (M : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (M + 1) * ((M : ℝ≥0∞) + 1)⁻¹

/-- The window weight `w z = ∑_M a_M 1_{W_M}(z)`. -/
def ppWeight (c : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ∑' M : ℕ, (ppWindow c M).indicator (fun _ => ppA M) z

/-- The weighted measure `μ = w · vol`. -/
def ppMeas (c : ℝ) : Measure (ℝ × ℝ) := volume.withDensity (ppWeight c)

lemma measurableSet_ppWindow (c : ℝ) (M : ℕ) : MeasurableSet (ppWindow c M) := by
  unfold ppWindow
  exact (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_const)

lemma ppWeight_measurable (c : ℝ) : Measurable (ppWeight c) :=
  Measurable.ennreal_tsum fun M =>
    (measurable_const (a := ppA M)).indicator (measurableSet_ppWindow c M)

lemma ppA_ne_zero (M : ℕ) : ppA M ≠ 0 := by
  unfold ppA
  refine mul_ne_zero (pow_ne_zero _ (by simp)) ?_
  simp

lemma ppA_ne_top (M : ℕ) : ppA M ≠ ⊤ := by
  unfold ppA
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
    (ENNReal.inv_ne_top.2 (by simp))

lemma ppA_le_geom (M : ℕ) : ppA M ≤ (2⁻¹ : ℝ≥0∞) ^ (M + 1) := by
  unfold ppA
  exact mul_le_of_le_one_right zero_le (ENNReal.inv_le_one.2 (by simp))

lemma ppA_mul_nat_le (M : ℕ) : ppA M * (M : ℝ≥0∞) ≤ (2⁻¹ : ℝ≥0∞) ^ (M + 1) := by
  unfold ppA
  have h1 : ((M : ℝ≥0∞) + 1)⁻¹ * (M : ℝ≥0∞) ≤ 1 := by
    calc ((M : ℝ≥0∞) + 1)⁻¹ * (M : ℝ≥0∞) ≤ ((M : ℝ≥0∞) + 1)⁻¹ * ((M : ℝ≥0∞) + 1) :=
          by gcongr; exact le_self_add
      _ = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
  calc (2⁻¹ : ℝ≥0∞) ^ (M + 1) * ((M : ℝ≥0∞) + 1)⁻¹ * (M : ℝ≥0∞)
      = (2⁻¹ : ℝ≥0∞) ^ (M + 1) * (((M : ℝ≥0∞) + 1)⁻¹ * (M : ℝ≥0∞)) := by ring
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (M + 1) * 1 := by gcongr
    _ = _ := mul_one _

lemma sum_geom_half : ∑' M : ℕ, (2⁻¹ : ℝ≥0∞) ^ (M + 1) = 1 := by
  simp only [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

lemma ppWeight_le_one (c : ℝ) (z : ℝ × ℝ) : ppWeight c z ≤ 1 := by
  unfold ppWeight
  have h1 : ∀ M : ℕ, (ppWindow c M).indicator (fun _ => ppA M) z ≤ (2⁻¹ : ℝ≥0∞) ^ (M + 1) :=
    fun M => by
      by_cases h : z ∈ ppWindow c M <;> simp [h, ppA_le_geom M]
  exact (ENNReal.tsum_le_tsum h1).trans (le_of_eq sum_geom_half)

lemma ppWeight_ge (c : ℝ) {M : ℕ} {z : ℝ × ℝ} (hz : z ∈ ppWindow c M) :
    ppA M ≤ ppWeight c z := by
  unfold ppWeight
  calc ppA M = (ppWindow c M).indicator (fun _ => ppA M) z :=
        (Set.indicator_of_mem hz (fun _ => ppA M)).symm
    _ ≤ _ := ENNReal.le_tsum M

lemma ppWeight_ne_top (c : ℝ) (z : ℝ × ℝ) : ppWeight c z ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (ppWeight_le_one c z)

lemma iUnion_ppWindow {c : ℝ} (hc : 0 < c) : (⋃ M : ℕ, ppWindow c M) = univ := by
  apply eq_univ_of_forall
  intro z
  have hx : |z.1| / c < ((⌊|z.1| / c⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hlt : |z.1| < ((⌊|z.1| / c⌋₊ + 1 : ℕ) : ℝ) * c := by
    rwa [div_lt_iff₀ hc] at hx
  refine mem_iUnion.2 ⟨⌊|z.1| / c⌋₊ + 1, ?_, ?_⟩
  · show -(((⌊|z.1| / c⌋₊ + 1 : ℕ)) : ℝ) * c ≤ z.1
    linarith [neg_abs_le z.1]
  · show z.1 < ((⌊|z.1| / c⌋₊ + 1 : ℕ) : ℝ) * c
    linarith [le_abs_self z.1]

lemma aestronglyMeasurable_of_windows {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → CMerid}
    (hf : ∀ M : ℕ, AEStronglyMeasurable f (volume.restrict (ppWindow c M))) :
    AEStronglyMeasurable f volume := by
  have h := (aestronglyMeasurable_iUnion_iff (μ := volume) (s := fun M => ppWindow c M)
    (f := f)).2 hf
  rwa [iUnion_ppWindow hc, Measure.restrict_univ] at h

lemma lintegral_ppMeas (c : ℝ) {g : ℝ × ℝ → ℝ≥0∞} (hg : AEMeasurable g volume) :
    ∫⁻ z, g z ∂(ppMeas c) = ∑' M : ℕ, ppA M * ∫⁻ z in ppWindow c M, g z := by
  unfold ppMeas
  rw [lintegral_withDensity_eq_lintegral_mul₀ (ppWeight_measurable c).aemeasurable hg]
  have hw : ∀ z, (ppWeight c * g) z = ∑' M : ℕ,
      (ppWindow c M).indicator (fun z => ppA M * g z) z := by
    intro z
    rw [Pi.mul_apply, ppWeight, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun M => by by_cases h : z ∈ ppWindow c M <;> simp [h]
  simp_rw [hw]
  rw [lintegral_tsum]
  · congr 1
    ext M
    rw [lintegral_indicator (measurableSet_ppWindow c M), lintegral_const_mul' _ _ (ppA_ne_top M)]
  · intro M
    exact ((hg.const_mul (ppA M)).indicator (measurableSet_ppWindow c M))

/-- The window measure is dominated by `a_M⁻¹ μ`: `vol|W_M ≤ a_M⁻¹ • μ`. -/
lemma restrict_window_le_smul (c : ℝ) (M : ℕ) :
    volume.restrict (ppWindow c M) ≤ (ppA M)⁻¹ • ppMeas c := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul]
  unfold ppMeas
  rw [withDensity_apply _ hs]
  have hW := measurableSet_ppWindow c M
  calc volume (s ∩ ppWindow c M)
      = (ppA M)⁻¹ * (ppA M * volume (s ∩ ppWindow c M)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (ppA_ne_zero M) (ppA_ne_top M), one_mul]
    _ = (ppA M)⁻¹ * ∫⁻ _ in s ∩ ppWindow c M, ppA M := by
        rw [setLIntegral_const]
    _ ≤ (ppA M)⁻¹ * ∫⁻ z in s, ppWeight c z :=
        mul_le_mul_of_nonneg_left (le_trans
          (setLIntegral_mono' (hs.inter hW) fun z hz => ppWeight_ge c hz.2)
          (lintegral_mono_set Set.inter_subset_left)) zero_le



/-- Squared `L²` norm over a window, as a lintegral. -/
lemma eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (f : α → E)
    (μ' : Measure α) : eLpNorm f 2 μ' ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ' := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma rpow_half_sq' (X : ℝ≥0∞) : (X ^ (1 / (2 : ℝ))) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Uniform `L²(μ)` bound from the window bounds. -/
lemma sq_bound_ppMeas {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → CMerid}
    (hfm : AEStronglyMeasurable f volume) {A : ℝ≥0∞}
    (hb : ∀ M : ℕ, eLpNorm f 2 (volume.restrict (ppWindow c M)) ≤
      3 * ENNReal.ofReal (2 * M * c) ^ (1 / (2 : ℝ)) * A) :
    eLpNorm f 2 (ppMeas c) ^ 2 ≤ 9 * ENNReal.ofReal (2 * c) * A ^ 2 := by
  have hc2 : (0 : ℝ) ≤ 2 * c := by linarith
  have hg : AEMeasurable (fun z => ‖f z‖ₑ ^ 2) volume := (hfm.aemeasurable.enorm).pow_const 2
  rw [eLpNorm_two_sq, lintegral_ppMeas c hg]
  have key : ∀ M : ℕ, ppA M * ∫⁻ z in ppWindow c M, ‖f z‖ₑ ^ 2 ≤
      9 * ENNReal.ofReal (2 * c) * A ^ 2 * (2⁻¹ : ℝ≥0∞) ^ (M + 1) := by
    intro M
    have h1 : ∫⁻ z in ppWindow c M, ‖f z‖ₑ ^ 2 ≤ 9 * ENNReal.ofReal (2 * M * c) * A ^ 2 := by
      rw [← eLpNorm_two_sq]
      calc eLpNorm f 2 (volume.restrict (ppWindow c M)) ^ 2
          ≤ (3 * ENNReal.ofReal (2 * M * c) ^ (1 / (2 : ℝ)) * A) ^ 2 := by
            gcongr; exact hb M
        _ = 9 * ENNReal.ofReal (2 * M * c) * A ^ 2 := by
            rw [mul_pow, mul_pow, rpow_half_sq']; norm_num
    have h2 : ENNReal.ofReal (2 * M * c) = ENNReal.ofReal (2 * c) * (M : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc2]
      congr 1
      ring
    calc ppA M * ∫⁻ z in ppWindow c M, ‖f z‖ₑ ^ 2
        ≤ ppA M * (9 * ENNReal.ofReal (2 * M * c) * A ^ 2) := by gcongr
      _ = (9 * ENNReal.ofReal (2 * c) * A ^ 2) * (ppA M * (M : ℝ≥0∞)) := by rw [h2]; ring
      _ ≤ (9 * ENNReal.ofReal (2 * c) * A ^ 2) * (2⁻¹ : ℝ≥0∞) ^ (M + 1) := by
            gcongr; exact ppA_mul_nat_le M
  calc ∑' M : ℕ, ppA M * ∫⁻ z in ppWindow c M, ‖f z‖ₑ ^ 2
      ≤ ∑' M : ℕ, 9 * ENNReal.ofReal (2 * c) * A ^ 2 * (2⁻¹ : ℝ≥0∞) ^ (M + 1) :=
        ENNReal.tsum_le_tsum key
    _ = 9 * ENNReal.ofReal (2 * c) * A ^ 2 := by
        rw [ENNReal.tsum_mul_left, sum_geom_half, mul_one]

/-- Coordinatewise complex conjugate of a vector in `ℂ²`. -/
def conjVec (v : CMerid) : CMerid := WithLp.toLp 2 (fun i => (starRingEnd ℂ) (v i))

lemma conjVec_apply (v : CMerid) (i : Fin 2) : conjVec v i = (starRingEnd ℂ) (v i) := by
  simp [conjVec]

lemma norm_conjVec (v : CMerid) : ‖conjVec v‖ = ‖v‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

lemma continuous_conjVec : Continuous conjVec := by
  unfold conjVec
  fun_prop

/-- The test function `z ↦ 1_{W_M}(z) · conj(ψ z) / w(z)`. -/
def ppTest (c : ℝ) (M : ℕ) (ψ : ℝ × ℝ → CMerid) (z : ℝ × ℝ) : CMerid :=
  (ppWindow c M).indicator (fun z => ((ppWeight c z).toReal)⁻¹ • conjVec (ψ z)) z

lemma ppWeight_toReal_pos {c : ℝ} {M : ℕ} {z : ℝ × ℝ} (hz : z ∈ ppWindow c M) :
    0 < (ppWeight c z).toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (ppA_ne_zero M))
    (ppWeight_ge c hz))) (ppWeight_ne_top c z)

lemma memLp_ppTest {c : ℝ} (hc : 0 < c) {M : ℕ} {ψ : ℝ × ℝ → CMerid}
    (hψ : MemLp ψ 2 (volume.restrict (ppWindow c M))) :
    MemLp (ppTest c M ψ) 2 (ppMeas c) := by
  have hW := measurableSet_ppWindow c M
  set K : ℝ := ((ppA M).toReal)⁻¹ with hK
  have hg : MemLp (fun z => (ppWindow c M).indicator (fun z => K * ‖ψ z‖) z) 2 volume := by
    rw [memLp_indicator_iff_restrict hW]
    exact hψ.norm.const_mul K
  have hle : ppMeas c ≤ volume := by
    rw [Measure.le_iff]
    intro s hs
    unfold ppMeas
    rw [withDensity_apply _ hs]
    calc ∫⁻ z in s, ppWeight c z ≤ ∫⁻ _ in s, 1 :=
          setLIntegral_mono' hs fun z _ => ppWeight_le_one c z
      _ = volume s := by simp
  have hg' := hg.mono_measure hle
  have hA : AEStronglyMeasurable (ppTest c M ψ) volume := by
    unfold ppTest
    refine (aestronglyMeasurable_indicator_iff hW).2 ?_
    have hr : AEStronglyMeasurable (fun z => ((ppWeight c z).toReal)⁻¹)
        (volume.restrict (ppWindow c M)) :=
      ((ppWeight_measurable c).ennreal_toReal.inv).aestronglyMeasurable
    have hv : AEStronglyMeasurable (fun z => conjVec (ψ z)) (volume.restrict (ppWindow c M)) :=
      continuous_conjVec.comp_aestronglyMeasurable hψ.aestronglyMeasurable
    exact hr.smul hv
  refine hg'.of_le (hA.mono_ac (withDensity_absolutelyContinuous _ _)) (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ ppWindow c M
  · have hpos := ppWeight_toReal_pos hz
    have hle' : (ppA M).toReal ≤ (ppWeight c z).toReal :=
      ENNReal.toReal_mono (ppWeight_ne_top c z) (ppWeight_ge c hz)
    have hpa : 0 < (ppA M).toReal := ENNReal.toReal_pos (ppA_ne_zero M) (ppA_ne_top M)
    have hK0 : 0 ≤ K := inv_nonneg.2 ENNReal.toReal_nonneg
    simp only [ppTest, Set.indicator_of_mem hz]
    rw [norm_smul, norm_conjVec, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
      Real.norm_of_nonneg (mul_nonneg hK0 (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hpa hle') (norm_nonneg _)
  · simp [ppTest, Set.indicator_of_notMem hz]

/-- Pairing identity: the `L²(μ)` inner product of `x` with a window test is the conjugate
window pairing of any representative `f` of `x`. -/
lemma inner_toLp_gen {c : ℝ} (hc : 0 < c) (x : Lp CMerid 2 (ppMeas c)) {f : ℝ × ℝ → CMerid}
    (hxf : ⇑x =ᵐ[ppMeas c] f) {M : ℕ} {ψ : ℝ × ℝ → CMerid}
    (hψ : MemLp ψ 2 (volume.restrict (ppWindow c M))) :
    inner ℂ x ((memLp_ppTest hc hψ).toLp (ppTest c M ψ)) =
      (starRingEnd ℂ) (∫ z in ppWindow c M, ∑ i : Fin 2, f z i * ψ z i) := by
  have hW := measurableSet_ppWindow c M
  rw [L2.inner_def]
  have h1 : ∀ᵐ z ∂(ppMeas c), inner ℂ (x z) ((memLp_ppTest hc hψ).toLp (ppTest c M ψ) z) =
      inner ℂ (f z) (ppTest c M ψ z) := by
    filter_upwards [hxf, (memLp_ppTest hc hψ).coeFn_toLp] with z h1 h2
    rw [h1, h2]
  rw [integral_congr_ae h1]
  unfold ppMeas
  rw [integral_withDensity_eq_integral_toReal_smul (ppWeight_measurable c)
    (ae_of_all _ fun z => lt_top_iff_ne_top.2 (ppWeight_ne_top c z))]
  have h2 : ∀ z, (ppWeight c z).toReal • inner ℂ (f z) (ppTest c M ψ z) =
      (ppWindow c M).indicator (fun z => (starRingEnd ℂ) (∑ i : Fin 2, f z i * ψ z i)) z := by
    intro z
    by_cases hz : z ∈ ppWindow c M
    · have hpos : (0 : ℝ) < (ppWeight c z).toReal := ppWeight_toReal_pos hz
      have hne : ((ppWeight c z).toReal : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [Set.indicator_of_mem hz]
      simp only [ppTest, Set.indicator_of_mem hz, PiLp.inner_apply, conjVec_apply,
        RCLike.inner_apply, PiLp.smul_apply, Complex.real_smul, map_sum, map_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      field_simp
    · simp [ppTest, Set.indicator_of_notMem hz]
  simp_rw [h2]
  rw [integral_indicator hW, integral_conj]

/-- **Leaf `PartII-b:T12/1/4/2/1`** (weak extraction on the windows). -/
theorem pplWeakLimit : PPLWeakLimit := by
  unfold PPLWeakLimit
  intro r C c F H hctx
  obtain ⟨hr, hC, hc, hF, hF2, hP⟩ := hctx
  have hA' : eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c) ≠ ⊤ := by
    have h := hF2.2.eLpNorm_lt_top
    rw [ENNReal.ofReal_ofNat] at h
    exact h.ne
  set A := eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c) with hAdef
  have hwin : ∀ N M : ℕ, MemLp (H N) 2 (volume.restrict (ppWindow c M)) :=
    fun N M => (hP.memLp N M).1
  have hfm : ∀ N : ℕ, AEStronglyMeasurable (H N) volume := fun N =>
    aestronglyMeasurable_of_windows hc fun M => (hwin N M).aestronglyMeasurable
  have hsq : ∀ N : ℕ, eLpNorm (H N) 2 (ppMeas c) ^ 2 ≤ 9 * ENNReal.ofReal (2 * c) * A ^ 2 :=
    fun N => sq_bound_ppMeas hc (hfm N) (fun M => hP.bound2 N M)
  have hfin : 9 * ENNReal.ofReal (2 * c) * A ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top hA')
  have hmem : ∀ N : ℕ, MemLp (H N) 2 (ppMeas c) := by
    intro N
    refine ⟨(hfm N).mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
    apply lt_top_iff_ne_top.2
    intro h
    have h2 := hsq N
    rw [h, ENNReal.top_pow two_ne_zero] at h2
    exact hfin (top_le_iff.1 h2)
  set M0 : ℝ := Real.sqrt (9 * ENNReal.ofReal (2 * c) * A ^ 2).toReal with hM0
  have hbound : ∀ n : ℕ, ‖(hmem n).toLp (H n)‖ ≤ M0 := by
    intro n
    rw [Lp.norm_toLp]
    have h1 : (eLpNorm (H n) 2 (ppMeas c)).toReal ^ 2 ≤
        (9 * ENNReal.ofReal (2 * c) * A ^ 2).toReal := by
      rw [← ENNReal.toReal_pow]
      exact ENNReal.toReal_mono hfin (hsq n)
    calc (eLpNorm (H n) 2 (ppMeas c)).toReal
        = Real.sqrt ((eLpNorm (H n) 2 (ppMeas c)).toReal ^ 2) :=
          (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ M0 := Real.sqrt_le_sqrt h1
  obtain ⟨φ, hφ, x, _, hw⟩ :=
    UnforcedLeray.Infra.WeaklyNullCompact.exists_subseq_weakTendsto (𝕜 := ℂ)
      (u := fun n => (hmem n).toLp (H n)) (M := M0) hbound
  have hxmem : MemLp (⇑x) 2 (ppMeas c) := Lp.memLp x
  refine ⟨φ, hφ, ⇑x, ?_, ?_⟩
  · intro M
    exact MemLp.of_measure_le_smul (ENNReal.inv_ne_top.2 (ppA_ne_zero M))
      (restrict_window_le_smul c M) hxmem
  · intro M ψ hψ
    have key := hw ((memLp_ppTest hc hψ).toLp (ppTest c M ψ))
    have e1 : ∀ n : ℕ, inner ℂ ((memLp_ppTest hc hψ).toLp (ppTest c M ψ))
        ((hmem (φ n)).toLp (H (φ n))) = ∫ z in ppWindow c M, ∑ i : Fin 2, H (φ n) z i * ψ z i := by
      intro n
      rw [← inner_conj_symm, inner_toLp_gen hc _ (hmem (φ n)).coeFn_toLp hψ]
      simp
    have e2 : inner ℂ ((memLp_ppTest hc hψ).toLp (ppTest c M ψ)) x =
        ∫ z in ppWindow c M, ∑ i : Fin 2, ⇑x z i * ψ z i := by
      rw [← inner_conj_symm, inner_toLp_gen hc _ EventuallyEq.rfl hψ]
      simp
    rw [e2] at key
    exact Filter.Tendsto.congr (fun n => e1 n) key

end UnforcedLeray.Short.IIb
