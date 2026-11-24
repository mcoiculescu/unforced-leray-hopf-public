import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.Smooth2D
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartII-b:F8/2` helper: `H¹ ⊂ L^{11/4}` on the periodic strip

For `c ≥ 4` and a `c`-periodic `u : ℝ × ℝ → ℂ` whose weak derivatives `g₁ = ∂_q u`, `g₂ = ∂_η u`
(tested against the mollifiers `kern n (x - ·)`) are `c`-periodic, all three square integrable
on the cell `[-c/2, c/2) × ℝ`:
`‖u‖_{L^{11/4}(cell)} ≤ planeK (‖u‖_{L²(cell)} + ‖g₁‖_{L²(cell)} + ‖g₂‖_{L²(cell)})`
with `planeK` independent of `c`.  Proof: cut off by `cut2 (c/2) n`, mollify by `kern n`, apply
`smooth_lintegral_le`, bound the `L²` norms on three cells by periodicity, and pass to the limit
with Fatou's lemma.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb.FlatKH2

/-! ## 1. Strips and periodicity -/

/-- The strip `[a, b) × ℝ`. -/
def strip (a b : ℝ) : Set (ℝ × ℝ) := Ico a b ×ˢ univ

theorem measurableSet_strip (a b : ℝ) : MeasurableSet (strip a b) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- `c`-periodicity in the first variable, almost everywhere. -/
def APer (c : ℝ) (f : ℝ × ℝ → ℂ) : Prop := ∀ᵐ y : ℝ × ℝ, f (y + (c, 0)) = f y

theorem aper_shift {c : ℝ} {f : ℝ × ℝ → ℂ} (h : APer c f) (v : ℝ × ℝ) :
    ∀ᵐ y : ℝ × ℝ, f (y + v + (c, 0)) = f (y + v) :=
  (measurePreserving_add_right volume v).quasiMeasurePreserving.ae h

theorem aper_int {c : ℝ} {f : ℝ × ℝ → ℂ} (h : APer c f) (k : ℤ) :
    ∀ᵐ y : ℝ × ℝ, f (y + ((k : ℝ) * c, 0)) = f y := by
  induction k using Int.induction_on with
  | zero =>
    refine Eventually.of_forall (fun y => ?_)
    simp only [Int.cast_zero, zero_mul]
    rw [Prod.mk_zero_zero, add_zero]
  | succ i ih =>
    filter_upwards [ih, aper_shift h (((i : ℤ) : ℝ) * c, 0)] with y h1 h2
    have e : y + ((((i : ℤ) + 1 : ℤ) : ℝ) * c, (0 : ℝ)) =
        y + (((i : ℤ) : ℝ) * c, 0) + (c, 0) := by
      ext
      · simp only [Prod.fst_add]
        push_cast
        ring
      · simp
    rw [e, h2, h1]
  | pred i ih =>
    filter_upwards [ih, aper_shift h ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c, 0)] with y h1 h2
    have e : y + ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c, (0 : ℝ)) + (c, 0) =
        y + (((-(i : ℤ) : ℤ) : ℝ) * c, 0) := by
      ext
      · simp only [Prod.fst_add]
        push_cast
        ring
      · simp
    rw [← h2, e, h1]

/-- Integrals over strips are invariant under integer period shifts. -/
theorem lintegral_strip_shift {c : ℝ} {f : ℝ × ℝ → ℂ} (h : APer c f) (G : ℂ → ℝ≥0∞) (k : ℤ)
    (a b : ℝ) :
    ∫⁻ y in strip (a + k * c) (b + k * c), G (f y) = ∫⁻ y in strip a b, G (f y) := by
  set v : ℝ × ℝ := ((k : ℝ) * c, 0) with hv
  have hmem : ∀ y : ℝ × ℝ, y + v ∈ strip (a + k * c) (b + k * c) ↔ y ∈ strip a b := by
    intro y
    simp only [strip, mem_prod, mem_Ico, mem_univ, and_true, hv, Prod.fst_add]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  calc ∫⁻ y in strip (a + k * c) (b + k * c), G (f y)
      = ∫⁻ y, (strip (a + k * c) (b + k * c)).indicator (fun y => G (f y)) y :=
        (lintegral_indicator (measurableSet_strip _ _) _).symm
    _ = ∫⁻ y, (strip (a + k * c) (b + k * c)).indicator (fun y => G (f y)) (y + v) :=
        (lintegral_add_right_eq_self _ v).symm
    _ = ∫⁻ y, (strip a b).indicator (fun y => G (f y)) y := by
        apply lintegral_congr_ae
        filter_upwards [aper_int h k] with y hy
        by_cases hy' : y ∈ strip a b
        · rw [indicator_of_mem ((hmem y).2 hy'), indicator_of_mem hy']
          simp only [hv]
          rw [hy]
        · rw [indicator_of_notMem (fun h' => hy' ((hmem y).1 h')), indicator_of_notMem hy']
    _ = ∫⁻ y in strip a b, G (f y) := lintegral_indicator (measurableSet_strip _ _) _

/-- The strip of `2N + 1` cells carries at most `2N + 1` times the cell integral. -/
theorem lintegral_stripN_le {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (h : APer c f)
    (G : ℂ → ℝ≥0∞) (N : ℕ) :
    ∫⁻ y in strip (-(((N : ℝ) + 1 / 2) * c)) (((N : ℝ) + 1 / 2) * c), G (f y) ≤
      (2 * N + 1) * ∫⁻ y in strip (-(c / 2)) (c / 2), G (f y) := by
  induction N with
  | zero =>
    have e : (((0 : ℕ) : ℝ) + 1 / 2) * c = c / 2 := by push_cast; ring
    rw [e]
    simp
  | succ N ih =>
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    set I := ∫⁻ y in strip (-(c / 2)) (c / 2), G (f y) with hI
    set L := strip (-(c / 2) + ((-((N : ℤ) + 1) : ℤ) : ℝ) * c)
      (c / 2 + ((-((N : ℤ) + 1) : ℤ) : ℝ) * c) with hLdef
    set R := strip (-(c / 2) + (((N : ℤ) + 1 : ℤ) : ℝ) * c)
      (c / 2 + (((N : ℤ) + 1 : ℤ) : ℝ) * c) with hRdef
    set M := strip (-(((N : ℝ) + 1 / 2) * c)) (((N : ℝ) + 1 / 2) * c) with hMdef
    have hsub : strip (-((((N + 1 : ℕ) : ℝ) + 1 / 2) * c)) ((((N + 1 : ℕ) : ℝ) + 1 / 2) * c) ⊆
        (L ∪ M) ∪ R := by
      intro y hy
      simp only [hLdef, hRdef, hMdef, strip, mem_union, mem_prod, mem_Ico, mem_univ,
        and_true] at hy ⊢
      push_cast at hy ⊢
      obtain ⟨h1, h2⟩ := hy
      by_cases hA : y.1 < -(((N : ℝ) + 1 / 2) * c)
      · left; left; constructor <;> nlinarith
      · by_cases hB : y.1 < ((N : ℝ) + 1 / 2) * c
        · left; right; constructor <;> nlinarith
        · right; constructor <;> nlinarith
    have hL : ∫⁻ y in L, G (f y) = I := lintegral_strip_shift h G _ _ _
    have hR : ∫⁻ y in R, G (f y) = I := lintegral_strip_shift h G _ _ _
    calc ∫⁻ y in strip (-((((N + 1 : ℕ) : ℝ) + 1 / 2) * c)) ((((N + 1 : ℕ) : ℝ) + 1 / 2) * c),
          G (f y)
        ≤ ∫⁻ y in (L ∪ M) ∪ R, G (f y) := lintegral_mono_set hsub
      _ ≤ (∫⁻ y in L ∪ M, G (f y)) + ∫⁻ y in R, G (f y) := lintegral_union_le _ _ _
      _ ≤ ((∫⁻ y in L, G (f y)) + ∫⁻ y in M, G (f y)) + ∫⁻ y in R, G (f y) := by
          gcongr
          exact lintegral_union_le _ _ _
      _ ≤ (I + (2 * N + 1) * I) + I := by
          rw [hL, hR]
          gcongr
      _ = (2 * ((N + 1 : ℕ) : ℝ≥0∞) + 1) * I := by
          push_cast
          ring

/-- `L²` norm of a periodic function on `2N + 1` cells. -/
theorem lintegral_sq_stripN_lt_top {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (h : APer c f)
    (h2 : eLpNorm f 2 (volume.restrict (strip (-(c / 2)) (c / 2))) < ⊤) (N : ℕ) :
    ∫⁻ y in strip (-(((N : ℝ) + 1 / 2) * c)) (((N : ℝ) + 1 / 2) * c), ‖f y‖ₑ ^ (2 : ℝ) < ⊤ := by
  have hcell : ∫⁻ y in strip (-(c / 2)) (c / 2), ‖f y‖ₑ ^ (2 : ℝ) < ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num)
      (by norm_num)).1 h2
    simpa using this
  refine (lintegral_stripN_le hc h (fun z => ‖z‖ₑ ^ (2 : ℝ)) N).trans_lt ?_
  exact ENNReal.mul_lt_top (by finiteness) hcell

/-- A periodic function, square integrable on one cell, is locally integrable. -/
theorem locallyIntegrable_of_aper {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (h : APer c f)
    (h2 : eLpNorm f 2 (volume.restrict (strip (-(c / 2)) (c / 2))) < ⊤) :
    LocallyIntegrable f volume := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ((|x.1| + 1) / c)
  set B : Set (ℝ × ℝ) := Icc (x.1 - 1) (x.1 + 1) ×ˢ Icc (x.2 - 1) (x.2 + 1) with hB
  refine ⟨B, ?_, ?_⟩
  · exact prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
      (Icc_mem_nhds (by linarith) (by linarith))
  · have hBfin : volume B < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin.ne
    have hNc : |x.1| + 1 < N * c := by
      rwa [div_lt_iff₀ hc] at hN
    have hBsub : B ⊆ strip (-(((N : ℝ) + 1 / 2) * c)) (((N : ℝ) + 1 / 2) * c) := by
      intro y hy
      simp only [hB, mem_prod, mem_Icc] at hy
      simp only [strip, mem_prod, mem_Ico, mem_univ, and_true]
      have := neg_abs_le x.1
      have := le_abs_self x.1
      constructor <;> nlinarith
    have hmem : MemLp f 2 (volume.restrict B) := by
      refine ⟨hf.restrict, ?_⟩
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      have := lintegral_sq_stripN_lt_top hc h h2 N
      refine lt_of_le_of_lt ?_ this
      simp only [ENNReal.toReal_ofNat]
      exact lintegral_mono_set hBsub
    exact hmem.integrable (by norm_num)

/-! ## 2. Convolution with the mollifiers -/

theorem kern_contDiff1 (n : ℕ) : ContDiff ℝ 1 (kern n) := (bump n).contDiff_normed (n := 1)

/-- The convolution as an integral against `kern n (x - ·)`. -/
theorem conv_apply (n : ℕ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      ∫ y, (kern n (x - y) : ℂ) * g y := by
  rw [convolution_eq_swap]
  congr 1

/-- The derivative of a mollification is the convolution with the derivative of the kernel. -/
theorem fderiv_conv_apply (n : ℕ) {u : ℝ × ℝ → ℂ} (hu : LocallyIntegrable u volume)
    (x e : ℝ × ℝ) :
    fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e =
      ∫ y, ((fderiv ℝ (kern n) (x - y) e : ℝ) : ℂ) * u y := by
  have hd := (kern_hasCompactSupport n).hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hu (kern_contDiff1 n) x
  rw [← convolution_flip, hd.fderiv,
    convolution_precompR_apply _ hu ((kern_hasCompactSupport n).fderiv ℝ)
      ((kern_contDiff1 n).continuous_fderiv (by norm_num))]
  rw [convolution_def]
  congr 1

/-- Young's inequality for the normalized kernel. -/
theorem conv_eLpNorm_le (n : ℕ) {h : ℝ × ℝ → ℂ} (hh : AEStronglyMeasurable h volume) :
    eLpNorm (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) 2 volume ≤
      eLpNorm h 2 volume := by
  have hk : Continuous (kern n) := (kern_contDiff n).continuous
  have hF : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => kern n p.2 • h (p.1 - p.2)) (volume.prod volume) :=
    hk.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hh
  have hm := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le
    (F := fun x y : ℝ × ℝ => kern n y • h (x - y)) hF
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  have htranslate (y : ℝ × ℝ) :
      eLpNorm (fun x : ℝ × ℝ => h (x - y)) 2 volume = eLpNorm h 2 volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      eLpNorm_comp_measurePreserving hh
        (measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (-y))
  have hnorm (y : ℝ × ℝ) :
      eLpNorm (fun x : ℝ × ℝ => kern n y • h (x - y)) 2 volume =
        ENNReal.ofReal (kern n y) * eLpNorm h 2 volume := by
    change eLpNorm ((kern n y) • (fun x : ℝ × ℝ => h (x - y))) 2 volume = _
    rw [eLpNorm_const_smul, htranslate, Real.enorm_eq_ofReal (kern_nonneg n y)]
  have hmass : (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (kern n y)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (kern_integrable n)
      (Eventually.of_forall (kern_nonneg n)), kern_integral]
    norm_num
  change eLpNorm (fun x : ℝ × ℝ => ∫ y, kern n y • h (x - y)) 2 volume ≤ _
  calc _ ≤ ∫⁻ y : ℝ × ℝ, eLpNorm (fun x : ℝ × ℝ => kern n y • h (x - y)) 2 volume := hm
    _ = (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (kern n y)) * eLpNorm h 2 volume := by
      simp_rw [hnorm]
      exact lintegral_mul_const _ (ENNReal.continuous_ofReal.comp hk).measurable
    _ = _ := by rw [hmass, one_mul]

/-- The three-cell strip `[-3c/2, 3c/2) × ℝ`. -/
def strip3 (c : ℝ) : Set (ℝ × ℝ) := strip (-((1 + 1 / 2) * c)) ((1 + 1 / 2) * c)

/-- Near the cell the mollification only sees the three-cell strip. -/
theorem conv_eq_conv_indicator {c : ℝ} (hc : 4 ≤ c) (n : ℕ) (h : ℝ × ℝ → ℂ) {y : ℝ × ℝ}
    (hy : |y.1| ≤ c / 2 + 1) :
    (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y =
      (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (strip3 c).indicator h) y := by
  rw [convolution_def, convolution_def]
  congr 1
  funext t
  by_cases ht : kern n t = 0
  · simp [ht]
  · have htn : ‖t‖ < 1 / 2 := by
      by_contra hcon
      exact ht (kern_eq_zero (not_lt.mp hcon))
    have ht1 : |t.1| < 1 / 2 := lt_of_le_of_lt (by simpa using norm_fst_le t) htn
    have hmem : y - t ∈ strip3 c := by
      simp only [strip3, strip, mem_prod, mem_Ico, mem_univ, and_true, Prod.fst_sub]
      have a1 := abs_le.mp hy
      have a2 := abs_lt.mp ht1
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    rw [indicator_of_mem hmem]

/-- The `L²` norm on three cells. -/
theorem eLpNorm_indicator_strip3_le {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (h : APer c f) :
    eLpNorm ((strip3 c).indicator f) 2 volume ≤
      (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm f 2 (volume.restrict (strip (-(c / 2)) (c / 2))) := by
  simp only [strip3]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_strip _ _),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have h1 := lintegral_stripN_le hc h (fun z => ‖z‖ₑ ^ (2 : ℝ)) 1
  simp only [Nat.cast_one] at h1
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  convert h1 using 2
  norm_num

/-! ## 3. Extension of the derivative identity from a dense set -/

theorem ident_ext (n : ℕ) {u g : ℝ × ℝ → ℂ} (hlu : LocallyIntegrable u volume)
    (hlg : LocallyIntegrable g volume) {D : Set (ℝ × ℝ)} (hD : Dense D) (e : ℝ × ℝ)
    (hid : ∀ x ∈ D, ∫ y, (kern n (x - y) : ℂ) * g y =
      ∫ y, ((fderiv ℝ (kern n) (x - y) e : ℝ) : ℂ) * u y) (x : ℝ × ℝ) :
    fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e =
      (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hc1 : Continuous (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    (kern_hasCompactSupport n).continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (kern_contDiff n).continuous hlg
  have hsm : ContDiff ℝ 1 (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) :=
    (kern_hasCompactSupport n).contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (kern_contDiff1 n) hlu
  have hc2 : Continuous
      (fun x => fderiv ℝ (kern n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e) :=
    (hsm.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have heq := Continuous.ext_on hD hc2 hc1 (fun x hx => by
    rw [fderiv_conv_apply n hlu x e, conv_apply n g x]
    exact (hid x hx).symm)
  exact congrFun heq x

end UnforcedLeray.Short.IIb.FlatKH2
