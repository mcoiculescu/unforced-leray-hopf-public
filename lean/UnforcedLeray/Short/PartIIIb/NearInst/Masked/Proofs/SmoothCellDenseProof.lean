import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_6
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.SmoothCompactDenseOpen

/-!
# Smooth cell-supported tensors are dense in `H_T` (source 1678)

Proof of `SmoothCellDense`.  Route: `G = s^{-1/4} g` is in `L²(U)` for the open cell
`U = (0,∞) × (0,c) × ℝ` (the slice `q = c` is Lebesgue-null), smooth compactly supported
`φ` approximate `G` in `L²(U)`, and `M = s^{1/4} φ` approximates `g` in `H_T`, because
`s^{-1/2} |g - s^{1/4} φ|² = |G - φ|²` on `U`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff NNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothCellDenseProof

open UnforcedLeray.Short.PartIIa UnforcedLeray.B0220

/-- The open cell `(0,∞) × (0,c) × ℝ`. -/
def openCellU (c : ℝ) : Set (ℝ × ℝ × ℝ) := Ioi 0 ×ˢ (Ioo 0 c ×ˢ univ)

lemma mem_openCellU {c : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ openCellU c ↔ 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < c := by
  simp [openCellU, Set.mem_prod]

lemma isOpen_openCellU (c : ℝ) : IsOpen (openCellU c) :=
  isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_univ)

lemma volume_slice_null (c : ℝ) : volume {p : ℝ × ℝ × ℝ | p.2.1 = c} = 0 := by
  have h : {p : ℝ × ℝ × ℝ | p.2.1 = c} = univ ×ˢ ({c} ×ˢ univ) := by
    ext p
    simp
  rw [h]
  simp [Measure.volume_eq_prod, Measure.prod_prod]

lemma cellMeasure_eq_restrict (c : ℝ) :
    cellMeasure c = volume.restrict (openCellU c) := by
  unfold cellMeasure
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · refine measure_mono_null ?_ (volume_slice_null c)
    rintro p ⟨hcell, hnot⟩
    show p.2.1 = c
    by_contra hne
    apply hnot
    obtain ⟨h1, h2, h3⟩ := hcell
    exact mem_openCellU.2 ⟨h1, h2.1, lt_of_le_of_ne h2.2 hne⟩
  · have hempty : openCellU c \ cell c = ∅ := by
      refine Set.sdiff_eq_empty.2 ?_
      rintro p hp
      obtain ⟨h1, h2, h3⟩ := mem_openCellU.1 hp
      exact ⟨h1, ⟨h2, h3.le⟩, trivial⟩
    rw [hempty, measure_empty]

/-- The density `s^{-1/2}` as an extended nonnegative real. -/
lemma measurable_weight :
    Measurable fun p : ℝ × ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) :=
  (measurable_fst.pow_const _).ennreal_ofReal

lemma weight_ne_zero_of_pos {x : ℝ × ℝ × ℝ} (hx : 0 < x.1) :
    ENNReal.ofReal (x.1 ^ (-(1 / 2 : ℝ))) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx _)).ne'

lemma measureHT_eq_restrict (c : ℝ) :
    measureHT c = (volume.restrict (openCellU c)).withDensity
      (fun p : ℝ × ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ)))) := by
  unfold measureHT
  rw [cellMeasure_eq_restrict]

lemma ac_restrict_HT (c : ℝ) : volume.restrict (openCellU c) ≪ measureHT c := by
  rw [measureHT_eq_restrict]
  refine withDensity_absolutelyContinuous' measurable_weight.aemeasurable ?_
  exact (ae_restrict_mem (isOpen_openCellU c).measurableSet).mono fun x hx =>
    weight_ne_zero_of_pos (mem_openCellU.1 hx).1

lemma weight_mul_sq {s : ℝ} (hs : 0 < s) (x : TensorVal) :
    ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * ‖s ^ (1 / 4 : ℝ) • x‖ₑ ^ (2 : ℝ) =
      ‖x‖ₑ ^ (2 : ℝ) := by
  have ha : 0 ≤ s ^ (1 / 4 : ℝ) := Real.rpow_nonneg hs.le _
  have h1 : ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (s ^ (1 / 4 : ℝ)) ^ (2 : ℝ) = 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le,
      ← Real.rpow_add hs]
    norm_num
  rw [enorm_smul, Real.enorm_eq_ofReal ha, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  calc ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * (ENNReal.ofReal (s ^ (1 / 4 : ℝ)) ^ (2 : ℝ) * ‖x‖ₑ ^ (2 : ℝ))
      = (ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (s ^ (1 / 4 : ℝ)) ^ (2 : ℝ)) *
          ‖x‖ₑ ^ (2 : ℝ) := by ring
    _ = ‖x‖ₑ ^ (2 : ℝ) := by rw [h1, one_mul]

/-- Pointwise: the `H_T` integral of `h = s^{1/4} k` equals the `L²(U)` integral of `k`. -/
lemma key_integral (c : ℝ) (h k : ℝ × ℝ × ℝ → TensorVal)
    (hh : AEStronglyMeasurable h (measureHT c))
    (hid : ∀ x ∈ openCellU c, h x = (x.1 ^ (1 / 4 : ℝ)) • k x) :
    ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂(measureHT c) = ∫⁻ x in openCellU c, ‖k x‖ₑ ^ (2 : ℝ) := by
  have hg : AEMeasurable (fun x => ‖h x‖ₑ ^ (2 : ℝ)) (volume.restrict (openCellU c)) :=
    (hh.enorm.pow_const (2 : ℝ)).mono_ac (ac_restrict_HT c)
  rw [measureHT_eq_restrict,
    lintegral_withDensity_eq_lintegral_mul₀ measurable_weight.aemeasurable hg]
  refine setLIntegral_congr_fun (isOpen_openCellU c).measurableSet (fun x hx => ?_)
  simp only [Pi.mul_apply]
  rw [hid x hx]
  exact weight_mul_sq (mem_openCellU.1 hx).1 (k x)

lemma rpow_mul_neg_quarter {s : ℝ} (hs : 0 < s) : s ^ (1 / 4 : ℝ) * s ^ (-(1 / 4 : ℝ)) = 1 := by
  rw [Real.rpow_neg hs.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs _).ne']

/-- Compact box bounds for a compact set in the open cell. -/
lemma exists_box (c : ℝ) (hc : 0 < c) (K : Set (ℝ × ℝ × ℝ)) (hK : IsCompact K)
    (hKU : K ⊆ openCellU c) :
    ∃ s0 s1 L a b : ℝ, 0 < s0 ∧ 0 < a ∧ a < b ∧ b < c ∧
      ∀ p ∈ K, p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L ∧ p.2.1 ∈ Ioo a b := by
  have hp0U : ((1:ℝ), c / 2, (0:ℝ)) ∈ openCellU c :=
    mem_openCellU.2 ⟨one_pos, half_pos hc, by linarith⟩
  set p₀ : ℝ × ℝ × ℝ := ((1:ℝ), c / 2, (0:ℝ)) with hp₀
  have hK0 : IsCompact (K ∪ {p₀}) := hK.union isCompact_singleton
  have hK0U : K ∪ {p₀} ⊆ openCellU c :=
    union_subset hKU (singleton_subset_iff.2 hp0U)
  have hK0ne : (K ∪ {p₀}).Nonempty := ⟨p₀, Or.inr rfl⟩
  obtain ⟨x1, hx1, hmin1⟩ :=
    hK0.exists_isMinOn hK0ne (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => p.1).continuousOn
  obtain ⟨x2, hx2, hmax2⟩ :=
    hK0.exists_isMaxOn hK0ne (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => p.1).continuousOn
  obtain ⟨xq1, hq1, hminq⟩ :=
    hK0.exists_isMinOn hK0ne (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => p.2.1).continuousOn
  obtain ⟨xq2, hq2, hmaxq⟩ :=
    hK0.exists_isMaxOn hK0ne (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => p.2.1).continuousOn
  obtain ⟨xL, hL, hmaxL⟩ :=
    hK0.exists_isMaxOn hK0ne (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => |p.2.2|).continuousOn
  have h1 : 0 < x1.1 := (mem_openCellU.1 (hK0U hx1)).1
  have hq1pos : 0 < xq1.2.1 := (mem_openCellU.1 (hK0U hq1)).2.1
  have hq2lt : xq2.2.1 < c := (mem_openCellU.1 (hK0U hq2)).2.2
  have hqle : xq1.2.1 ≤ xq2.2.1 := isMinOn_iff.1 hminq xq2 hq2
  refine ⟨x1.1 / 2, x2.1, |xL.2.2|, xq1.2.1 / 2, (xq2.2.1 + c) / 2, by linarith,
    by linarith, by linarith, by linarith, ?_⟩
  intro p hp
  have hpK0 : p ∈ K ∪ {p₀} := Or.inl hp
  have hA : x1.1 ≤ p.1 := isMinOn_iff.1 hmin1 p hpK0
  have hB : p.1 ≤ x2.1 := isMaxOn_iff.1 hmax2 p hpK0
  have hC : xq1.2.1 ≤ p.2.1 := isMinOn_iff.1 hminq p hpK0
  have hD : p.2.1 ≤ xq2.2.1 := isMaxOn_iff.1 hmaxq p hpK0
  have hE : |p.2.2| ≤ |xL.2.2| := isMaxOn_iff.1 hmaxL p hpK0
  refine ⟨⟨by linarith, hB⟩, hE, ⟨by linarith, by linarith⟩⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothCellDenseProof

open UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothCellDenseProof UnforcedLeray.Short.PartIIa UnforcedLeray.B0220 in
/-- **Smooth cell-supported tensors are dense in `H_T`** (source 1678). -/
theorem smoothCellDense : UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothCellDense := by
  unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.SmoothCellDense
  intro c hc F ε hε
  have hgL : MemLp (⇑F) 2 (measureHT c) := Lp.memLp F
  have hgmeas : AEStronglyMeasurable (⇑F) (measureHT c) := hgL.aestronglyMeasurable
  -- the rescaled function `G = s^{-1/4} g`
  have hGmeas : AEStronglyMeasurable
      (fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) (volume.restrict (openCellU c)) :=
    ((measurable_fst.pow_const (-(1 / 4 : ℝ))).aestronglyMeasurable.smul hgmeas).mono_ac
      (ac_restrict_HT c)
  have hidF : ∀ x ∈ openCellU c, (⇑F) x = (x.1 ^ (1 / 4 : ℝ)) •
      ((fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) x) := by
    intro x hx
    simp only [smul_smul, rpow_mul_neg_quarter (mem_openCellU.1 hx).1, one_smul]
  have hGL2 : MemLp (fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) 2
      (volume.restrict (openCellU c)) := by
    refine ⟨hGmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) two_ne_zero
      (by simp : (2:ℝ≥0∞) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    have hint := key_integral c (⇑F) _ hgmeas hidF
    rw [← hint]
    have hF := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) two_ne_zero
      (by simp : (2:ℝ≥0∞) ≠ ⊤)).1 hgL.2
    simpa using hF
  obtain ⟨φ, hφs, hφc, hφU, hφε⟩ :=
    smoothCompactDenseOpen (openCellU c) (isOpen_openCellU c)
      (fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) hGL2 ε hε
  set M : ℝ × ℝ × ℝ → TensorVal := fun p => (p.1 ^ (1 / 4 : ℝ)) • φ p with hMdef
  have hMsm : ContDiff ℝ ∞ M := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hpos : x.1 ≠ 0 := (mem_openCellU.1 (hφU hx)).1.ne'
      exact (contDiff_fst.contDiffAt.rpow_const_of_ne hpos).smul (hφs.contDiffAt)
    · have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
      have hev' : M =ᶠ[𝓝 x] fun _ => (0 : TensorVal) :=
        hev.mono fun y hy => by simp [hMdef, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev'
  have hsupp : ∀ p, M p ≠ 0 → p ∈ tsupport φ := by
    intro p hp
    exact subset_tsupport φ (Function.mem_support.2 fun h0 => hp (by simp [hMdef, h0]))
  obtain ⟨s0, s1, L, a, b, hs0, ha, hab, hbc, hbox⟩ :=
    exists_box c hc (tsupport φ) hφc.isCompact hφU
  have hφL2 : MemLp φ 2 (volume.restrict (openCellU c)) :=
    (hφs.continuous.memLp_of_hasCompactSupport hφc).restrict _
  have hφint : ∫⁻ x in openCellU c, ‖φ x‖ₑ ^ (2 : ℝ) < ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) two_ne_zero
      (by simp : (2:ℝ≥0∞) ≠ ⊤)).1 hφL2.2
    simpa using this
  have hMmeas : AEStronglyMeasurable M (measureHT c) :=
    hMsm.continuous.aestronglyMeasurable
  have hMfin : eLpNorm M 2 (measureHT c) < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) two_ne_zero
      (by simp : (2:ℝ≥0∞) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    rw [key_integral c M φ hMmeas (fun x _ => rfl)]
    exact hφint
  have hML2 : MemLp M 2 (measureHT c) := ⟨hMmeas, hMfin⟩
  refine ⟨M, hMsm, ⟨s0, s1, L, hs0, fun p hp => ⟨(hbox p (hsupp p hp)).1,
    (hbox p (hsupp p hp)).2.1⟩⟩, ⟨a, b, ha, hab, hbc, fun p hp => (hbox p (hsupp p hp)).2.2⟩,
    hML2, ?_⟩
  have hdiffmeas : AEStronglyMeasurable (fun x => (⇑F) x - M x) (measureHT c) :=
    hgmeas.sub hMmeas
  have hidd : ∀ x ∈ openCellU c, (⇑F) x - M x = (x.1 ^ (1 / 4 : ℝ)) •
      ((fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) - φ) x := by
    intro x hx
    simp only [Pi.sub_apply, smul_sub, smul_smul, rpow_mul_neg_quarter (mem_openCellU.1 hx).1,
      one_smul, hMdef]
  have hae : ⇑(F - hML2.toLp M) =ᵐ[measureHT c] fun x => (⇑F) x - M x :=
    (Lp.coeFn_sub F (hML2.toLp M)).trans
      (Filter.EventuallyEq.sub (Filter.EventuallyEq.rfl) hML2.coeFn_toLp)
  have hEq : eLpNorm (fun x => (⇑F) x - M x) 2 (measureHT c) =
      eLpNorm ((fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) - φ) 2
        (volume.restrict (openCellU c)) := by
    have hk := key_integral c (fun x => (⇑F) x - M x)
      ((fun x : ℝ × ℝ × ℝ => (x.1 ^ (-(1 / 4 : ℝ))) • (⇑F) x) - φ) hdiffmeas hidd
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) two_ne_zero (by simp : (2:ℝ≥0∞) ≠ ⊤),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) two_ne_zero (by simp : (2:ℝ≥0∞) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    rw [hk]
  rw [Lp.norm_def, eLpNorm_congr_ae hae, hEq]
  exact ENNReal.toReal_lt_of_lt_ofReal hφε
