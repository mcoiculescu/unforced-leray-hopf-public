import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_2

/-!
# Local `L¹` bound from the cylinder norm (`CgiLocalL1`)

Source of record: `the November 2 reference manuscript` lines 1933-1935.
A `q`-periodic function is controlled on a compact `K` by finitely many period cells: `K` is
covered by finitely many translates `Z - kc e_q` of the box `Z = [-R,R] × cell × [-R,R]`, each
translate has the same integral as `Z` (periodicity, a.e.), and on `Z` the measure `vol` equals
`c · cylMeas`, so Hölder on the finite-measure set `Z` gives the `L^r(cylMeas c)` bound.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The `q`-translation by `t` on `Coord`, as the vector `(0, (t, 0))`. -/
def l1Sh (t : ℝ) : Coord := (0, (t, 0))

/-- The box `[-R,R] × ([-c/2,c/2) × [-R,R])` in `Coord`. -/
def l1Z (R c : ℝ) : Set Coord := Icc (-R) R ×ˢ (Ico (-c / 2) (c / 2) ×ˢ Icc (-R) R)

/-- The translated box `{x | x + l1Sh (k c) ∈ l1Z R c}`. -/
def l1C (R c : ℝ) (k : ℤ) : Set Coord := (fun x : Coord => x + l1Sh ((k : ℝ) * c)) ⁻¹' l1Z R c

lemma l1_mem_Z (R c : ℝ) (x : Coord) : x ∈ l1Z R c ↔
    (-R ≤ x.1 ∧ x.1 ≤ R) ∧ (-c / 2 ≤ x.2.1 ∧ x.2.1 < c / 2) ∧ (-R ≤ x.2.2 ∧ x.2.2 ≤ R) := by
  simp [l1Z, mem_prod, and_assoc]

lemma l1_cylMeas_eq (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ •
      (volume : Measure Coord).restrict (univ ×ˢ UnforcedLeray.Cyl.cell c) := by
  rw [cylMeas, UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, Measure.prod_smul_right,
    ← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict,
    ← Measure.volume_eq_prod]

lemma l1_restrict_eq_smul (c : ℝ) (hc : 0 < c) (Z : Set Coord)
    (hZ : Z ⊆ univ ×ˢ UnforcedLeray.Cyl.cell c) :
    (volume : Measure Coord).restrict Z = ENNReal.ofReal c • (cylMeas c).restrict Z := by
  have h1 : (volume : Measure Coord).restrict (univ ×ˢ UnforcedLeray.Cyl.cell c) =
      ENNReal.ofReal c • cylMeas c := by
    rw [l1_cylMeas_eq, smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_smul]
  rw [← Measure.restrict_restrict_of_subset (μ := (volume : Measure Coord)) hZ, h1,
    Measure.restrict_smul]

lemma l1_lintegral_restrict (c : ℝ) (hc : 0 < c) (Z : Set Coord)
    (hZ : Z ⊆ univ ×ˢ UnforcedLeray.Cyl.cell c) (F : Coord → ℝ≥0∞) :
    ∫⁻ x in Z, F x = ENNReal.ofReal c * ∫⁻ x in Z, F x ∂(cylMeas c) := by
  show ∫⁻ x, F x ∂((volume : Measure Coord).restrict Z) = _
  rw [l1_restrict_eq_smul c hc Z hZ, lintegral_smul_measure, smul_eq_mul]

lemma l1_cylMeas_Z_ne_top (c : ℝ) (hc : 0 < c) (R : ℝ) : cylMeas c (l1Z R c) ≠ ⊤ := by
  have hZ' : (volume : Measure Coord)
      (Icc (-R) R ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R)) ≠ ⊤ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top.ne
  have hsub : l1Z R c ⊆ Icc (-R) R ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) :=
    prod_mono subset_rfl (prod_mono Ico_subset_Icc_self subset_rfl)
  have hmeas : MeasurableSet (univ ×ˢ UnforcedLeray.Cyl.cell c) :=
    (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod (UnforcedLeray.Cyl.measurableSet_cell c)
  rw [l1_cylMeas_eq, Measure.smul_apply, Measure.restrict_apply' hmeas, smul_eq_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top hZ' (measure_mono ((inter_subset_left).trans hsub)))

lemma l1_cylMeas_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  rw [l1_cylMeas_eq]
  exact (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self)).smul_left _

lemma l1_ae_shift {c : ℝ} {g : Coord → ℂ} (hg : QPeriodicS c g) (k : ℤ) :
    ∀ᵐ x : Coord, g (x + l1Sh ((k : ℝ) * c)) = g x := by
  have hP : ∀ᵐ y : Coord, g (y + l1Sh c) = g y := by
    filter_upwards [hg] with y hy
    rw [← hy]
    congr 1
    ext <;> simp [qShift, l1Sh]
  refine Int.induction_on k ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    have e : x + l1Sh (((0 : ℤ) : ℝ) * c) = x := by ext <;> simp [l1Sh]
    rw [e]
  · intro i hi
    have h1 : ∀ᵐ x : Coord, g (x + l1Sh (((i : ℤ) : ℝ) * c) + l1Sh c)
        = g (x + l1Sh (((i : ℤ) : ℝ) * c)) :=
      (measurePreserving_add_right volume (l1Sh (((i : ℤ) : ℝ) * c))).quasiMeasurePreserving.ae hP
    filter_upwards [h1, hi] with x h1x h2x
    have e : x + l1Sh ((((i : ℤ) + 1 : ℤ) : ℝ) * c) = x + l1Sh (((i : ℤ) : ℝ) * c) + l1Sh c := by
      ext <;> simp [l1Sh] <;> ring
    rw [e, h1x, h2x]
  · intro i hi
    have h1 : ∀ᵐ x : Coord, g (x + l1Sh ((((-(i : ℤ)) - 1 : ℤ) : ℝ) * c) + l1Sh c)
        = g (x + l1Sh ((((-(i : ℤ)) - 1 : ℤ) : ℝ) * c)) :=
      (measurePreserving_add_right volume (l1Sh ((((-(i : ℤ)) - 1 : ℤ) : ℝ) * c))).quasiMeasurePreserving.ae hP
    filter_upwards [h1, hi] with x h1x h2x
    have e : x + l1Sh ((((-(i : ℤ)) - 1 : ℤ) : ℝ) * c) + l1Sh c
        = x + l1Sh ((((-(i : ℤ)) : ℤ) : ℝ) * c) := by
      ext <;> simp [l1Sh] <;> ring
    rw [e, h2x] at h1x
    exact h1x.symm

lemma l1_lintegral_shift {c : ℝ} {g : Coord → ℂ} (hg : QPeriodicS c g) (R : ℝ) (k : ℤ) :
    ∫⁻ x in l1C R c k, ‖g x‖ₑ = ∫⁻ x in l1Z R c, ‖g x‖ₑ := by
  have hk := l1_ae_shift hg k
  calc ∫⁻ x in l1C R c k, ‖g x‖ₑ
      = ∫⁻ x in l1C R c k, ‖g (x + l1Sh ((k : ℝ) * c))‖ₑ := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hk] with x hx
        rw [hx]
    _ = ∫⁻ x in l1Z R c, ‖g x‖ₑ :=
        (measurePreserving_add_right volume (l1Sh ((k : ℝ) * c))).setLIntegral_comp_preimage_emb
          (Homeomorph.addRight (l1Sh ((k : ℝ) * c))).measurableEmbedding (fun x => ‖g x‖ₑ) (l1Z R c)

theorem cgiLocalL1_proof : CgiLocalL1 := by
  intro r hr c hc K hK
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ K, ‖x‖ ≤ R := isBounded_iff_forall_norm_le.1 hK.isBounded
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = R / c := ⟨_, rfl⟩
  have hac : a * c = R := by rw [ha]; exact div_mul_cancel₀ R hc.ne'
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌈a⌉₊ + 2 := ⟨_, rfl⟩
  have hM : a + 2 ≤ (M : ℝ) := by
    rw [hMdef]; push_cast; linarith [Nat.le_ceil a]
  set I : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ) with hI
  -- covering of `K` by finitely many translates
  have hcov : K ⊆ ⋃ i : I, l1C R c (i : ℤ) := by
    intro x hx
    have hn := hR x hx
    have b1 : -R ≤ x.1 ∧ x.1 ≤ R :=
      abs_le.1 (by simpa [Real.norm_eq_abs] using (norm_fst_le x).trans hn)
    have b2 : -R ≤ x.2.1 ∧ x.2.1 ≤ R :=
      abs_le.1 (by simpa [Real.norm_eq_abs] using ((norm_fst_le x.2).trans (norm_snd_le x)).trans hn)
    have b3 : -R ≤ x.2.2 ∧ x.2.2 ≤ R :=
      abs_le.1 (by simpa [Real.norm_eq_abs] using ((norm_snd_le x.2).trans (norm_snd_le x)).trans hn)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (x.2.1 + c / 2) / c := ⟨_, rfl⟩
    have htc : t * c = x.2.1 + c / 2 := by rw [ht]; exact div_mul_cancel₀ _ hc.ne'
    have hfl1 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
    have hfl2 : t - 1 < (⌊t⌋ : ℝ) := Int.sub_one_lt_floor t
    have hfl3 : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
    have ht1 : t ≤ a + 1 := le_of_mul_le_mul_right
      (by rw [htc, add_mul, one_mul, hac]; linarith [b2.2]) hc
    have ht2 : -a - 1 ≤ t := le_of_mul_le_mul_right (by
      have e : (-a - 1) * c = -R - c := by rw [← hac]; ring
      rw [e, htc]; linarith [b2.1]) hc
    have hkM1 : ⌊t⌋ ≤ (M : ℤ) := by
      have : (⌊t⌋ : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast this
    have hkM2 : -(M : ℤ) ≤ ⌊t⌋ := by
      have : -(M : ℝ) ≤ (⌊t⌋ : ℝ) := by linarith
      exact_mod_cast this
    have hlo : (⌊t⌋ : ℝ) * c ≤ t * c := mul_le_mul_of_nonneg_right hfl1 hc.le
    have hhi : t * c < ((⌊t⌋ : ℝ) + 1) * c := mul_lt_mul_of_pos_right hfl3 hc
    have hmem : x ∈ l1C R c (-⌊t⌋) := by
      show x + l1Sh (((-⌊t⌋ : ℤ) : ℝ) * c) ∈ l1Z R c
      rw [l1_mem_Z]
      simp only [l1Sh, Prod.fst_add, Prod.snd_add, add_zero, Int.cast_neg]
      refine ⟨b1, ⟨?_, ?_⟩, b3⟩ <;> nlinarith [htc, hlo, hhi, b2.1, b2.2]
    refine mem_iUnion.2 ⟨⟨-⌊t⌋, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩, hmem⟩
  -- the constant
  have hZT : l1Z R c ⊆ univ ×ˢ UnforcedLeray.Cyl.cell c := by
    intro x hx
    obtain ⟨_, hx2⟩ := mem_prod.1 hx
    exact ⟨mem_univ _, mem_prod.2 ⟨(mem_prod.1 hx2).1, mem_univ _⟩⟩
  have hexp0 : (0 : ℝ) ≤ 1 - 1 / r := by
    have : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hA : (I.card : ℝ≥0∞) * ENNReal.ofReal c * (cylMeas c (l1Z R c)) ^ (1 - 1 / r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hexp0 (l1_cylMeas_Z_ne_top c hc R))
  refine ⟨((I.card : ℝ≥0∞) * ENNReal.ofReal c * (cylMeas c (l1Z R c)) ^ (1 - 1 / r)).toReal,
    fun g hg hgm => ?_⟩
  rw [ENNReal.ofReal_toReal hA]
  haveI : IsFiniteMeasure ((cylMeas c).restrict (l1Z R c)) :=
    isFiniteMeasure_restrict.2 (l1_cylMeas_Z_ne_top c hc R)
  have hgZ : AEStronglyMeasurable g ((cylMeas c).restrict (l1Z R c)) :=
    hgm.mono_ac ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans (l1_cylMeas_ac c))
  have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := (cylMeas c).restrict (l1Z R c))
    (f := g) hpq hgZ
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal) = 1 - 1 / r := by
    rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith)]; norm_num
  have hfin : eLpNorm g 1 ((cylMeas c).restrict (l1Z R c)) ≤
      eLpNorm g (ENNReal.ofReal r) (cylMeas c) * (cylMeas c (l1Z R c)) ^ (1 - 1 / r) := by
    calc eLpNorm g 1 ((cylMeas c).restrict (l1Z R c))
        ≤ eLpNorm g (ENNReal.ofReal r) ((cylMeas c).restrict (l1Z R c)) *
            ((cylMeas c).restrict (l1Z R c)) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal) := hH
      _ = eLpNorm g (ENNReal.ofReal r) ((cylMeas c).restrict (l1Z R c)) *
            (cylMeas c (l1Z R c)) ^ (1 - 1 / r) := by
          rw [Measure.restrict_apply_univ, hexp]
      _ ≤ eLpNorm g (ENNReal.ofReal r) (cylMeas c) * (cylMeas c (l1Z R c)) ^ (1 - 1 / r) :=
          by gcongr; exact Measure.restrict_le_self
  calc eLpNorm g 1 (volume.restrict K)
      = ∫⁻ x in K, ‖g x‖ₑ := eLpNorm_one_eq_lintegral_enorm
    _ ≤ ∫⁻ x in ⋃ i : I, l1C R c (i : ℤ), ‖g x‖ₑ := lintegral_mono_set hcov
    _ ≤ ∑' i : I, ∫⁻ x in l1C R c (i : ℤ), ‖g x‖ₑ := lintegral_iUnion_le _ _
    _ = ∑' i : I, ∫⁻ x in l1Z R c, ‖g x‖ₑ := tsum_congr fun i => l1_lintegral_shift hg R _
    _ = (I.card : ℝ≥0∞) * ∫⁻ x in l1Z R c, ‖g x‖ₑ := by
          rw [tsum_fintype]; simp [Finset.sum_const, nsmul_eq_mul]
    _ = (I.card : ℝ≥0∞) * (ENNReal.ofReal c * ∫⁻ x in l1Z R c, ‖g x‖ₑ ∂(cylMeas c)) := by
          rw [l1_lintegral_restrict c hc _ hZT]
    _ = (I.card : ℝ≥0∞) * (ENNReal.ofReal c * eLpNorm g 1 ((cylMeas c).restrict (l1Z R c))) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (I.card : ℝ≥0∞) * (ENNReal.ofReal c * (eLpNorm g (ENNReal.ofReal r) (cylMeas c) *
          (cylMeas c (l1Z R c)) ^ (1 - 1 / r))) := by
          gcongr
    _ = (I.card : ℝ≥0∞) * ENNReal.ofReal c * (cylMeas c (l1Z R c)) ^ (1 - 1 / r) *
          eLpNorm g (ENNReal.ofReal r) (cylMeas c) := by ring

end UnforcedLeray.Short.IIb
