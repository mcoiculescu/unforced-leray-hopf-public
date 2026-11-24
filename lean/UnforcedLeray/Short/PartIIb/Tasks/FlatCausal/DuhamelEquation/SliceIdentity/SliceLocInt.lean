import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_6

/-!
# Part II-b, task `PartII-b:T12/7/6/4` (`deqSliceLocInt`): local integrability of a slice pairing

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
A planar slice `g` that is a.e. `c`-periodic with finite `L^r` cell norm is `L^r` on every strip
`[-M, M] × [-N, N]` (finitely many translated cells), hence `L^1` there; multiply by a bounded
compactly supported test.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- translation in the first coordinate -/
def dsT (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + a, z.2)

theorem dsT_mp (a : ℝ) :
    MeasurePreserving (dsT a) (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
  have h : MeasurePreserving (fun z : ℝ × ℝ => z + (a, 0)) volume volume :=
    measurePreserving_add_right volume (a, 0)
  have e : dsT a = fun z : ℝ × ℝ => z + (a, 0) := by funext z; exact Prod.ext rfl (by simp [dsT])
  rw [e]; exact h

theorem dsT_emb (a : ℝ) : MeasurableEmbedding (dsT a) := by
  have h : MeasurableEmbedding (fun z : ℝ × ℝ => z + (a, 0)) :=
    (MeasurableEquiv.addRight (a, 0)).measurableEmbedding
  have e : dsT a = fun z : ℝ × ℝ => z + (a, 0) := by funext z; exact Prod.ext rfl (by simp [dsT])
  rw [e]; exact h

theorem dsT_add (a b : ℝ) (z : ℝ × ℝ) : dsT a (dsT b z) = dsT (a + b) z := by
  simp [dsT, add_assoc, add_comm b a]

theorem dsT_zero (z : ℝ × ℝ) : dsT 0 z = z := by simp [dsT]

theorem ds_ae_nat {c : ℝ} {g : ℝ × ℝ → CMerid} (h : ∀ᵐ z : ℝ × ℝ, g (dsT c z) = g z) (n : ℕ) :
    ∀ᵐ z : ℝ × ℝ, g (dsT (n * c) z) = g z := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun z => by simp [dsT_zero]
  | succ n ih =>
    have h2 : ∀ᵐ z : ℝ × ℝ, g (dsT (n * c) (dsT c z)) = g (dsT c z) :=
      (dsT_mp c).quasiMeasurePreserving.ae ih
    filter_upwards [h, h2] with z hz hz2
    rw [dsT_add] at hz2
    have : ((n : ℝ) + 1) * c = n * c + c := by ring
    push_cast
    rw [this, hz2, hz]

theorem ds_ae_int {c : ℝ} {g : ℝ × ℝ → CMerid} (h : ∀ᵐ z : ℝ × ℝ, g (dsT c z) = g z) (k : ℤ) :
    ∀ᵐ z : ℝ × ℝ, g (dsT (k * c) z) = g z := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using ds_ae_nat h n
  · have h1 := ds_ae_nat h n
    have h2 : ∀ᵐ z : ℝ × ℝ, g (dsT (n * c) (dsT (-(n * c)) z)) = g (dsT (-(n * c)) z) :=
      (dsT_mp (-(n * c))).quasiMeasurePreserving.ae h1
    filter_upwards [h2] with z hz
    rw [dsT_add] at hz
    simp only [add_neg_cancel, dsT_zero] at hz
    push_cast
    rw [neg_mul]
    exact hz.symm

/-- the translated strip -/
def dsS (c N : ℝ) (k : ℤ) : Set (ℝ × ℝ) :=
  Ico (-c / 2 + k * c) (c / 2 + k * c) ×ˢ Icc (-N) N

theorem dsS_eq (c N : ℝ) (k : ℤ) : dsS c N k = dsT (-(k * c)) ⁻¹' dsS c N 0 := by
  ext z
  simp only [dsS, dsT, mem_preimage, mem_prod, mem_Ico, mem_Icc]
  push_cast
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> refine ⟨⟨?_, ?_⟩, h3⟩ <;> linarith

theorem dsS_meas (c N : ℝ) (k : ℤ) : MeasurableSet (dsS c N k) :=
  measurableSet_Ico.prod measurableSet_Icc

theorem ds_strip_eq {c : ℝ} {g : ℝ × ℝ → CMerid} (h : ∀ᵐ z : ℝ × ℝ, g (dsT c z) = g z)
    (r N : ℝ) (k : ℤ) :
    ∫⁻ z in dsS c N k, ‖g z‖ₑ ^ r = ∫⁻ z in dsS c N 0, ‖g z‖ₑ ^ r := by
  have hk := ds_ae_int h (-k)
  have h1 : ∫⁻ z in dsT (-(k * c)) ⁻¹' dsS c N 0, (fun w => ‖g w‖ₑ ^ r) (dsT (-(k * c)) z)
      = ∫⁻ w in dsS c N 0, ‖g w‖ₑ ^ r :=
    (dsT_mp _).setLIntegral_comp_preimage_emb (dsT_emb _) (fun w => ‖g w‖ₑ ^ r) _
  rw [← h1, ← dsS_eq]
  apply lintegral_congr_ae
  apply ae_restrict_of_ae
  filter_upwards [hk] with z hz
  have : ((-k : ℤ) : ℝ) * c = -(k * c) := by push_cast; ring
  rw [this] at hz
  simp only [hz]


theorem ds_cell_lt_top {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {g : ℝ × ℝ → CMerid}
    (hnorm : eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤) :
    ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g z‖ₑ ^ r < ⊤ := by
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr0.le] at hnorm
  have h1 : ∫⁻ z, ‖g z‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos (by positivity)] at hnorm
    exact lt_irrefl _ hnorm
  rw [UnforcedLeray.Cyl.lintegral_avgμ] at h1
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.mul_top (by simpa using inv_pos.2 hc)] at h1
  exact lt_irrefl _ h1

theorem ds_biUnion_le (F : ℝ × ℝ → ℝ≥0∞) (S : ℤ → Set (ℝ × ℝ)) (T : Finset ℤ) :
    ∫⁻ z in ⋃ k ∈ T, S k, F z ≤ ∑ k ∈ T, ∫⁻ z in S k, F z := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add_right ih _)

theorem ds_box_lt_top {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {g : ℝ × ℝ → CMerid}
    (hg : DeqSliceGood c r g) (M N : ℝ) :
    ∫⁻ z in Icc (-M) M ×ˢ Icc (-N) N, ‖g z‖ₑ ^ r < ⊤ := by
  obtain ⟨hper, -, hnorm⟩ := hg
  have h0 : ∫⁻ z in dsS c N 0, ‖g z‖ₑ ^ r < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_set ?_) (ds_cell_lt_top hc hr hnorm)
    intro z hz
    simp only [dsS, mem_prod, mem_Ico] at hz
    refine ⟨?_, trivial⟩
    simpa using hz.1
  set K : ℤ := ⌈M / c⌉ + 1 with hK
  have hcov : Icc (-M) M ×ˢ Icc (-N) N ⊆ ⋃ k ∈ Finset.Icc (-K) K, dsS c N k := by
    intro z hz
    simp only [mem_prod, mem_Icc] at hz
    obtain ⟨⟨hq1, hq2⟩, hη⟩ := hz
    set k : ℤ := ⌊z.1 / c + 1 / 2⌋ with hk
    have a1 := Int.floor_le (z.1 / c + 1 / 2)
    have a2 := Int.lt_floor_add_one (z.1 / c + 1 / 2)
    have b1 : z.1 / c ≤ M / c := div_le_div_of_nonneg_right hq2 hc.le
    have b2 : -M / c ≤ z.1 / c := div_le_div_of_nonneg_right hq1 hc.le
    have b3 : M / c ≤ (⌈M / c⌉ : ℝ) := Int.le_ceil _
    have b4 : -M / c = -(M / c) := by ring
    have hk1 : (k : ℝ) ≤ K := by
      rw [hK]; push_cast; linarith
    have hk2 : (-K : ℝ) ≤ k := by
      rw [hK]; push_cast; linarith
    simp only [mem_iUnion]
    refine ⟨k, Finset.mem_Icc.2 ⟨by exact_mod_cast hk2, by exact_mod_cast hk1⟩, ?_⟩
    simp only [dsS, mem_prod, mem_Ico, mem_Icc]
    refine ⟨⟨?_, ?_⟩, hη⟩
    · have := mul_le_mul_of_nonneg_right a1 hc.le
      have e : (z.1 / c + 1 / 2) * c = z.1 + c / 2 := by field_simp
      have e2 : (k : ℝ) * c ≤ z.1 + c / 2 := by linarith
      linarith
    · have := mul_lt_mul_of_pos_right a2 hc
      have e : (z.1 / c + 1 / 2) * c = z.1 + c / 2 := by field_simp
      nlinarith
  calc ∫⁻ z in Icc (-M) M ×ˢ Icc (-N) N, ‖g z‖ₑ ^ r
      ≤ ∫⁻ z in ⋃ k ∈ Finset.Icc (-K) K, dsS c N k, ‖g z‖ₑ ^ r := lintegral_mono_set hcov
    _ ≤ ∑ k ∈ Finset.Icc (-K) K, ∫⁻ z in dsS c N k, ‖g z‖ₑ ^ r :=
        ds_biUnion_le _ _ _
    _ = ∑ k ∈ Finset.Icc (-K) K, ∫⁻ z in dsS c N 0, ‖g z‖ₑ ^ r :=
        Finset.sum_congr rfl fun k _ => ds_strip_eq hper r N k
    _ < ⊤ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h0

/-- **Task `PartII-b:T12/7/6/4`** (SP 1923-1927). -/
theorem deqSliceLocInt : UnforcedLeray.Short.IIb.DeqSliceLocInt := by
  intro c r t g hc hr hg Ψ hΨ i
  have hr0 : 0 < r := by linarith
  have hcont : Continuous (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth.continuous
  set ψ : ℝ × ℝ → ℝ := fun z => Ψ (t, z) i with hψ
  have hψc : Continuous ψ := hcont.comp (Continuous.prodMk continuous_const continuous_id)
  have hK : IsCompact (Prod.snd '' tsupport (fun x : Coord => Ψ x i)) :=
    (hΨ.smooth i).compact.isCompact.image continuous_snd
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  have hsupp : Function.support (fun z : ℝ × ℝ => g z i * (ψ z : ℂ)) ⊆
      Icc (-R) R ×ˢ Icc (-R) R := by
    intro z hz
    have hz1 : ψ z ≠ 0 := by
      intro h0
      apply hz
      simp [h0]
    have hmem : z ∈ Prod.snd '' tsupport (fun x : Coord => Ψ x i) :=
      ⟨(t, z), subset_tsupport _ hz1, rfl⟩
    have := hR hmem
    rw [mem_closedBall_zero_iff] at this
    have h1 : |z.1| ≤ R := (norm_fst_le z).trans this
    have h2 : |z.2| ≤ R := (norm_snd_le z).trans this
    simp only [mem_prod, mem_Icc]
    exact ⟨abs_le.1 h1, abs_le.1 h2⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖ψ z‖ ≤ C := by
    have hcs : HasCompactSupport ψ := by
      refine HasCompactSupport.of_support_subset_isCompact hK ?_
      intro z hz
      exact ⟨(t, z), subset_tsupport _ hz, rfl⟩
    exact hψc.bounded_above_of_compact_support hcs
  set box : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R with hbox
  have hboxc : IsCompact box := isCompact_Icc.prod isCompact_Icc
  haveI : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict box) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hboxc.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable g ((volume : Measure (ℝ × ℝ)).restrict box) :=
    hg.2.1.restrict
  have hlp : MemLp g (ENNReal.ofReal r) ((volume : Measure (ℝ × ℝ)).restrict box) := by
    refine ⟨hmeas, ?_⟩
    have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
    have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr0.le]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ds_box_lt_top hc hr hg R R).ne
  have hint : Integrable g ((volume : Measure (ℝ × ℝ)).restrict box) :=
    (hlp.mono_exponent (p := 1) (by
      rw [ENNReal.one_le_ofReal]; exact hr.le)).integrable le_rfl
  have hon : IntegrableOn (fun z : ℝ × ℝ => g z i * (ψ z : ℂ)) box := by
    refine Integrable.mono' (g := fun z => ‖g z‖ * C) (hint.norm.mul_const C) ?_ ?_
    · exact (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
        hmeas)).mul (Complex.continuous_ofReal.comp hψc).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul]
      refine mul_le_mul (PiLp.norm_apply_le (g z) i) ?_ (norm_nonneg _) (norm_nonneg _)
      simpa using hC z
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hon

end UnforcedLeray.Short.IIb
