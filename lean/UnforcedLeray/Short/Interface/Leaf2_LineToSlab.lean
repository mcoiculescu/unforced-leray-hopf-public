import UnforcedLeray.Short.Interface.Statements

/-!
# Interface: helper 2b-3, the line integral equals the slab integral of the periodization

Target `periodicLineToSlab : PeriodicLineToSlab` (`Statements.lean`, Section 2b; source of record
`the November 2 reference manuscript`). For `f` with `B0005.IsY2 P f` and a
continuous compactly supported `g` on `ℝ × ℝ³`, the whole-space integral of `⟨f, g⟩` is the slab
integral of `⟨f, periodizeTest P g⟩`, and the latter integrand is integrable on the slab.

Steps:
* `leaf2Window`: a spatial radius `R` and a finite set `S ⊆ ℤ` with `g(τ + nP, y) = 0` for
  `τ ∈ (0,P]` and `n ∉ S` (from `B0005.exists_window_of_hasCompactSupport`).
* `leaf2IsAddFD`: the slab `(0,P] × ℝ³` is a fundamental domain of `(P,0)ℤ` on `ℝ × ℝ³`. The
  unfoldings `leaf2LIntegralUnfold` (`ℝ≥0∞`) and `leaf2IntegralUnfold` (Bochner) follow from it.
* `leaf2Integrable`: `⟨f, g⟩` is integrable on `ℝ × ℝ³`. On the slab, each shifted integrand is
  bounded by `C ‖f‖` on the box `(0,P] × B(0,R)`, which has finite measure, and `f ∈ L²(slab)`
  gives `L¹` there (`IsY2.memL2`).
* `periodicLineToSlab`: unfold over the finite set `S`, then `integral_finsetSum`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint

/-! ## 1. Basic objects and pointwise facts -/

/-- The integrand `⟨f(τ,·), g(τ,·)⟩` on `ℝ × ℝ³`. -/
def leaf2PairField (f : ℝ → SpatialField) (g : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  inner ℝ (f z.1 z.2) (g z)

/-- The box `(0,P] × B(0,R)` carrying the bound of the pairing on the slab. -/
def leaf2Box (P R : ℝ) : Set SpaceTime := Ioc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R

theorem leaf2Box_mem {P R : ℝ} {z : SpaceTime} :
    z ∈ leaf2Box P R ↔ z.1 ∈ Ioc (0 : ℝ) P ∧ ‖z.2‖ ≤ R := by
  simp only [leaf2Box, mem_prod, Metric.mem_closedBall, dist_zero_right]

theorem measurableSet_leaf2Box (P R : ℝ) : MeasurableSet (leaf2Box P R) :=
  measurableSet_Ioc.prod measurableSet_closedBall

theorem leaf2_enorm_inner (x y : Space) : ‖inner ℝ x y‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm x y)

/-- Shifting the phase by a lattice vector leaves the `f`-factor unchanged (periodicity of `f`). -/
theorem leaf2PairFieldShift {P : ℝ} {f : ℝ → SpatialField} (hf : B0005.IsY2 P f)
    (g : SpaceTime → Space) (z : SpaceTime) (n : ℤ) :
    leaf2PairField f g (z.1 + n * P, z.2) = inner ℝ (f z.1 z.2) (g (z.1 + n * P, z.2)) := by
  unfold leaf2PairField
  show inner ℝ (f (z.1 + n * P) z.2) (g (z.1 + n * P, z.2)) = _
  rw [hf.periodic.int_mul n z.1]

/-! ## 2. The window and the finite set of lattice shifts -/

theorem leaf2Window {P : ℝ} (hP : 0 < P) {g : SpaceTime → Space} (hgs : HasCompactSupport g) :
    ∃ R : ℝ, ∃ S : Finset ℤ, (∀ (t : ℝ) (y : Space), R < ‖y‖ → g (t, y) = 0) ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ P → ∀ (y : Space) (n : ℤ), n ∉ S → g (τ + n * P, y) = 0 := by
  obtain ⟨R, -, hT, hS⟩ := B0005.exists_window_of_hasCompactSupport hgs
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + P) / P)
  have hNP : R + P < (N : ℝ) * P := (div_lt_iff₀ hP).1 hN
  refine ⟨R, Finset.Icc (-(N : ℤ)) (N : ℤ), hS, ?_⟩
  intro τ hτ0 hτP y n hn
  refine hT (τ + n * P) y ?_
  rintro ⟨h1, h2⟩
  have hn' : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := fun h => hn (Finset.mem_Icc.2 h)
  rcases not_and_or.1 hn' with h | h
  · have h3 : n + 1 ≤ -(N : ℤ) := by omega
    have h4 : (n : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast h3
    have h5 := mul_le_mul_of_nonneg_right h4 hP.le
    linarith
  · have h3 : (N : ℤ) + 1 ≤ n := by omega
    have h4 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h3
    have h5 := mul_le_mul_of_nonneg_right h4 hP.le
    linarith

theorem leaf2PeriodizeEq {P : ℝ} (g : SpaceTime → Space) {S : Finset ℤ}
    (hvan : ∀ τ : ℝ, 0 < τ → τ ≤ P → ∀ (y : Space) (n : ℤ), n ∉ S → g (τ + n * P, y) = 0)
    (z : SpaceTime) (hz1 : 0 < z.1) (hz2 : z.1 ≤ P) :
    periodizeTest P g z = ∑ n ∈ S, g (z.1 + n * P, z.2) := by
  unfold periodizeTest
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  by_contra hnS
  exact (Function.mem_support.1 hn) (hvan z.1 hz1 hz2 z.2 n fun h => hnS (Finset.mem_coe.2 h))

/-! ## 3. The slab is a fundamental domain of the lattice `(P,0)ℤ` -/

/-- Translation invariance of Lebesgue measure on `ℝ × ℝ³` (through the product formula). -/
instance leaf2SpaceTimeAddLeftInvariant : (volume : Measure SpaceTime).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod ℝ Space]
  infer_instance

instance leaf2VAddInvariant (v : SpaceTime) :
    VAddInvariantMeasure (AddSubgroup.zmultiples v) SpaceTime volume :=
  ⟨fun g s _ => by
    simp only [AddSubgroup.vadd_def, vadd_eq_add]
    exact measure_preimage_add _ _ _⟩

/-- `n ↦ n • (P, 0)` identifies `ℤ` with the lattice `(P,0)ℤ` in `ℝ × ℝ³`. -/
def leaf2Equiv {P : ℝ} (hP : 0 < P) : ℤ ≃ AddSubgroup.zmultiples ((P, 0) : SpaceTime) :=
  Equiv.ofBijective (fun n => ⟨n • ((P, 0) : SpaceTime), n, rfl⟩) ⟨fun m n h => by
    have h' : m • ((P, 0) : SpaceTime) = n • ((P, 0) : SpaceTime) := congrArg Subtype.val h
    have h1 : (m : ℝ) * P = (n : ℝ) * P := by
      have := congrArg Prod.fst h'
      simpa [zsmul_eq_mul] using this
    exact_mod_cast mul_right_cancel₀ hP.ne' h1, fun g => by
      obtain ⟨g, n, rfl⟩ := g
      exact ⟨n, rfl⟩⟩

theorem leaf2_vadd {P : ℝ} (hP : 0 < P) (n : ℤ) (z : SpaceTime) :
    (leaf2Equiv hP n) +ᵥ z = (z.1 + n * P, z.2) := by
  rw [AddSubgroup.vadd_def]
  show n • ((P, 0) : SpaceTime) + z = _
  refine Prod.ext ?_ ?_
  · simp [zsmul_eq_mul, add_comm]
  · simp

theorem leaf2IsAddFD {P : ℝ} (hP : 0 < P) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples ((P, 0) : SpaceTime)) (periodSlab P) volume := by
  unfold periodSlab
  refine IsAddFundamentalDomain.mk'
    (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet fun x => ?_
  have hinj : Function.Injective (fun n : ℤ => n • ((P, 0) : SpaceTime)) := by
    intro m n h
    have h1 := congrArg Prod.fst h
    simp only [Prod.smul_fst] at h1
    rw [zsmul_eq_mul, zsmul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ hP.ne' h1
  have hbij : Function.Bijective (codRestrict (fun n : ℤ => n • ((P, 0) : SpaceTime))
      (AddSubgroup.zmultiples ((P, 0) : SpaceTime)) fun n => ⟨n, rfl⟩) :=
    (Equiv.ofInjective _ hinj).bijective
  refine hbij.existsUnique_iff.2 ?_
  obtain ⟨n, hn, huniq⟩ := existsUnique_add_zsmul_mem_Ioc hP x.1 0
  refine ⟨n, ?_, ?_⟩
  · simp only [AddSubgroup.vadd_def, codRestrict, vadd_eq_add, mem_prod, mem_univ, and_true,
      Prod.fst_add, Prod.smul_fst]
    simpa [add_comm, zero_add] using hn
  · intro m hm
    apply huniq
    simp only [AddSubgroup.vadd_def, codRestrict, vadd_eq_add, mem_prod, mem_univ, and_true,
      Prod.fst_add, Prod.smul_fst] at hm
    simpa [add_comm, zero_add] using hm

theorem leaf2LIntegralUnfold {P : ℝ} (hP : 0 < P) (H : SpaceTime → ℝ≥0∞) :
    ∫⁻ z, H z = ∑' n : ℤ, ∫⁻ z in periodSlab P, H (z.1 + n * P, z.2) := by
  rw [(leaf2IsAddFD hP).lintegral_eq_tsum'' H, ← (leaf2Equiv hP).tsum_eq]
  simp_rw [leaf2_vadd hP]

theorem leaf2IntegralUnfold {P : ℝ} (hP : 0 < P) {H : SpaceTime → ℝ} (hH : Integrable H volume) :
    ∫ z, H z = ∑' n : ℤ, ∫ z in periodSlab P, H (z.1 + n * P, z.2) := by
  rw [(leaf2IsAddFD hP).integral_eq_tsum'' H hH, ← (leaf2Equiv hP).tsum_eq]
  simp_rw [leaf2_vadd hP]

/-! ## 4. Integrability of `⟨f, g⟩` on `ℝ × ℝ³` -/

/-- The box `(0,P] × B(0,R)` has finite measure, and `f` is `L¹` on it (`f ∈ L²(slab)`). -/
theorem leaf2BoxFinite {P : ℝ} (hP : 0 < P) {f : ℝ → SpatialField} (hf : B0005.IsY2 P f)
    (R : ℝ) : ∫⁻ z in leaf2Box P R, ‖f z.1 z.2‖ₑ < ⊤ := by
  have hsub : leaf2Box P R ⊆ periodSlab P := fun z hz => ⟨(leaf2Box_mem.1 hz).1, mem_univ _⟩
  have hsubC : leaf2Box P R ⊆ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R :=
    Set.prod_mono Ioc_subset_Icc_self subset_rfl
  have hcpt : volume (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) ≠ ⊤ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).measure_lt_top.ne
  have hvol : volume (leaf2Box P R) ≠ ⊤ := ne_top_of_le_ne_top hcpt (measure_mono hsubC)
  haveI : IsFiniteMeasure (volume.restrict (leaf2Box P R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hvol⟩
  have hmem : MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (leaf2Box P R)) :=
    hf.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact (hmem.integrable (by norm_num)).2

theorem leaf2Integrable {P : ℝ} (hP : 0 < P) {f : ℝ → SpatialField} (hf : B0005.IsY2 P f)
    {g : SpaceTime → Space} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (leaf2PairField f g) volume := by
  classical
  obtain ⟨R, S, hSpat, hSvan⟩ := leaf2Window hP hgs
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hgC : ∀ w : SpaceTime, ‖g w‖ₑ ≤ ENNReal.ofReal C := fun w => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC w)
  have hslabMeas : MeasurableSet (periodSlab P) := measurableSet_Ioc.prod MeasurableSet.univ
  -- the pointwise bound on the slab, uniform in the shift `n`
  have hbound_pt : ∀ (n : ℤ) (z : SpaceTime), z ∈ periodSlab P →
      ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ ≤
        (leaf2Box P R).indicator (fun w : SpaceTime => ENNReal.ofReal C * ‖f w.1 w.2‖ₑ) z := by
    intro n z hz
    by_cases hzQ : z ∈ leaf2Box P R
    · rw [Set.indicator_apply, if_pos hzQ, leaf2PairFieldShift hf g z n]
      refine le_trans (leaf2_enorm_inner _ _) ?_
      calc ‖f z.1 z.2‖ₑ * ‖g (z.1 + n * P, z.2)‖ₑ ≤ ‖f z.1 z.2‖ₑ * ENNReal.ofReal C := by
            gcongr
            exact hgC _
        _ = ENNReal.ofReal C * ‖f z.1 z.2‖ₑ := mul_comm _ _
    · rw [Set.indicator_apply, if_neg hzQ]
      have hR : R < ‖z.2‖ := by
        by_contra h
        exact hzQ (leaf2Box_mem.2 ⟨hz.1, not_lt.1 h⟩)
      rw [leaf2PairFieldShift hf g z n, hSpat (z.1 + n * P) z.2 hR]
      simp
  have hbound : ∀ n : ℤ, ∫⁻ z in periodSlab P, ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ z in leaf2Box P R, ‖f z.1 z.2‖ₑ := by
    intro n
    calc ∫⁻ z in periodSlab P, ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ
        ≤ ∫⁻ z in periodSlab P,
            (leaf2Box P R).indicator (fun w : SpaceTime => ENNReal.ofReal C * ‖f w.1 w.2‖ₑ) z :=
          setLIntegral_mono' hslabMeas fun z hz => hbound_pt n z hz
      _ ≤ ∫⁻ z, (leaf2Box P R).indicator (fun w : SpaceTime => ENNReal.ofReal C * ‖f w.1 w.2‖ₑ) z :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ z in leaf2Box P R, ENNReal.ofReal C * ‖f z.1 z.2‖ₑ :=
          lintegral_indicator (measurableSet_leaf2Box P R)
            (fun w : SpaceTime => ENNReal.ofReal C * ‖f w.1 w.2‖ₑ)
      _ = ENNReal.ofReal C * ∫⁻ z in leaf2Box P R, ‖f z.1 z.2‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- the shifts outside `S` do not contribute on the slab
  have hzero : ∀ n ∉ S, ∫⁻ z in periodSlab P, ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ = 0 := by
    intro n hn
    have hpt : ∀ z ∈ periodSlab P, ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ ≤ 0 := by
      intro z hz
      rw [leaf2PairFieldShift hf g z n, hSvan z.1 hz.1.1 hz.1.2 z.2 n hn]
      simp
    exact le_antisymm ((setLIntegral_mono' hslabMeas hpt).trans (le_of_eq lintegral_zero))
      zero_le
  have hfin : ∫⁻ z, ‖leaf2PairField f g z‖ₑ < ⊤ := by
    calc ∫⁻ z, ‖leaf2PairField f g z‖ₑ
        = ∑' n : ℤ, ∫⁻ z in periodSlab P, ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ :=
          leaf2LIntegralUnfold hP (fun z => ‖leaf2PairField f g z‖ₑ)
      _ = ∑ n ∈ S, ∫⁻ z in periodSlab P, ‖leaf2PairField f g (z.1 + n * P, z.2)‖ₑ :=
          tsum_eq_sum hzero
      _ ≤ ∑ n ∈ S, ENNReal.ofReal C * ∫⁻ z in leaf2Box P R, ‖f z.1 z.2‖ₑ :=
          Finset.sum_le_sum fun n _ => hbound n
      _ < ⊤ := ENNReal.sum_lt_top.2 fun n _ =>
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (leaf2BoxFinite hP hf R)
  have hmeas : AEStronglyMeasurable (leaf2PairField f g) volume :=
    hf.measurable.inner hgc.aestronglyMeasurable
  exact ⟨hmeas, hfin⟩

/-! ## 5. The identity -/

theorem periodicLineToSlab : PeriodicLineToSlab := by
  unfold PeriodicLineToSlab
  intro P f g hP hf hgc hgs
  obtain ⟨R, S, -, hvan⟩ := leaf2Window hP hgs
  have hint : Integrable (leaf2PairField f g) volume := leaf2Integrable hP hf hgc hgs
  have hslabMeas : MeasurableSet (periodSlab P) := measurableSet_Ioc.prod MeasurableSet.univ
  -- each shifted integrand is integrable on the slab
  have hshift : ∀ n : ℤ,
      IntegrableOn (fun z : SpaceTime => leaf2PairField f g (z.1 + n * P, z.2)) (periodSlab P) := by
    intro n
    have h := hint.comp_add_right ((n : ℝ) * P, (0 : Space))
    have e : (fun x : SpaceTime => leaf2PairField f g (x + ((n : ℝ) * P, (0 : Space))))
        = fun z : SpaceTime => leaf2PairField f g (z.1 + n * P, z.2) := by
      funext x
      rw [show x + ((n : ℝ) * P, (0 : Space)) = (x.1 + n * P, x.2) from
        Prod.ext rfl (add_zero x.2)]
    rw [e] at h
    exact h.integrableOn
  -- the shifts outside `S` vanish on the slab
  have hvanish : ∀ z ∈ periodSlab P, ∀ n : ℤ, n ∉ S →
      leaf2PairField f g (z.1 + n * P, z.2) = 0 := by
    intro z hz n hn
    rw [leaf2PairFieldShift hf g z n, hvan z.1 hz.1.1 hz.1.2 z.2 n hn, inner_zero_right]
  have hz0 : ∀ n ∉ S, ∫ z in periodSlab P, leaf2PairField f g (z.1 + n * P, z.2) = 0 :=
    fun n hn => setIntegral_eq_zero_of_forall_eq_zero fun z hz => hvanish z hz n hn
  -- the pointwise identity on the slab: finite sum of shifts equals the periodization
  have hpt : ∀ z ∈ periodSlab P, ∑ n ∈ S, leaf2PairField f g (z.1 + n * P, z.2)
      = inner ℝ (f z.1 z.2) (periodizeTest P g z) := by
    intro z hz
    rw [leaf2PeriodizeEq g hvan z hz.1.1 hz.1.2, inner_sum]
    exact Finset.sum_congr rfl fun n _ => leaf2PairFieldShift hf g z n
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun (integrable_finsetSum S fun n _ => hshift n) hpt hslabMeas
  · show ∫ z, leaf2PairField f g z =
      ∫ z in periodSlab P, inner ℝ (f z.1 z.2) (periodizeTest P g z)
    rw [leaf2IntegralUnfold hP hint, tsum_eq_sum hz0,
      ← integral_finsetSum S fun n _ => hshift n]
    exact setIntegral_congr_fun hslabMeas hpt

end UnforcedLeray.Short.Interface
