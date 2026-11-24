import UnforcedLeray.Loc.Hyp.ModeIdentification.Energy
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp

/-!
# H-ModeId helpers: phase slices of the periodic graph

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 136–147 and 172–185 read at almost every phase; blueprint units B0005,
B1007, B1009).

* `ae_of_periodic`: a `𝒯`-periodic property holding a.e. on `(0,𝒯]` holds a.e. on `ℝ`.
* For `f ∈ 𝒴_{2,div}` (`IsY2Div`): `f(τ) ∈ L²` for a.e. `τ` (`Y2.ae_memLp`), and the
  `L²`-valued path `τ ↦ f(τ)` is a.e. strongly measurable and Bochner integrable on every bounded
  interval (`Y2.aestronglyMeasurable`, `Y2.integrableOn`), from the Fubini isometry
  `BochnerTime.stronglyMeasurable_toPath_Lq` and periodicity.
* `ae_forall_tests`: an identity `Λ_τ(φ) = 0`, continuous in the `L²` data of the test `φ`
  (`φ`, `Δφ`, `∂ⱼφ`), that holds for every test at a.e. phase holds at a.e. phase for every test
  (a countable dense family of tests, from separability of `L²`).
* Product tests `ψ(τ,y) = θ(τ)φ(y)` (copied and adapted from
  `Loc/Hyp/BackgroundStrongForm/ProductTest.lean`, lines 96–168) and the Fubini reduction of
  the spacetime pairings to phase pairings (`integral_pairTerm_prodTest`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph
open UnforcedLeray.BochnerTime

/-! ## Periodic a.e. statements -/

theorem ae_of_periodic {T : ℝ} (hT : 0 < T) {p : ℝ → Prop} (hp : ∀ τ, p (τ + T) ↔ p τ)
    (h : ∀ᵐ τ ∂(volume.restrict (Ioc 0 T)), p τ) : ∀ᵐ τ, p τ := by
  have hper : Function.Periodic p T := fun τ => propext (hp τ)
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  have hk : ∀ k : ℤ, ∀ᵐ x, x - k * T ∈ Ioc 0 T → p x := by
    intro k
    have h1 := (measurePreserving_sub_right volume ((k : ℝ) * T)).quasiMeasurePreserving.ae h
    filter_upwards [h1] with x hx hmem
    have h2 := hx hmem
    have h3 := hper.int_mul k (x - k * T)
    rw [sub_add_cancel] at h3
    rw [h3]
    exact h2
  filter_upwards [ae_all_iff.2 hk] with x hx
  obtain ⟨m, hm, -⟩ := existsUnique_sub_zsmul_mem_Ioc hT x 0
  rw [zero_add, zsmul_eq_mul] at hm
  exact hx m hm

/-- Local integrability from integrability on every bounded open interval. -/
theorem locallyIntegrable_of_Ioo {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (h : ∀ lo hi, IntegrableOn g (Ioo lo hi)) : LocallyIntegrable g := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (h (-(R + 1)) (R + 1)).mono_set (fun x hx => ?_)
  have := hR hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  constructor <;> linarith [abs_le.mp this]

/-! ## The periodic graph at a.e. phase -/

theorem volume_restrict_periodSlab (T : ℝ) :
    (volume : Measure SpaceTime).restrict (periodSlab T) =
      (volume.restrict (Ioc 0 T)).prod (volume : Measure Space) := by
  rw [periodSlab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem toPathLq_eq_toL2 (f : ℝ → SpatialField) :
    toPathLq 2 volume (fun z : SpaceTime => f z.1 z.2) = fun τ => toL2 (f τ) := by
  funext τ
  rfl

section Y2

variable {T : ℝ} {f : ℝ → SpatialField}

theorem Y2.memLp_prod (hf : IsY2Div T f) :
    MemLp (fun z : SpaceTime => f z.1 z.2) 2 ((volume.restrict (Ioc 0 T)).prod volume) := by
  have h := hf.memL2
  rwa [volume_restrict_periodSlab] at h

theorem Y2.ae_memLp (hT : 0 < T) (hf : IsY2Div T f) : ∀ᵐ τ, MemLp (f τ) 2 volume := by
  refine ae_of_periodic hT (fun τ => by rw [hf.periodic τ]) ?_
  exact FreeStress.ae_memLp_slice (Y2.memLp_prod hf)

theorem Y2.aestronglyMeasurable (hf : IsY2Div T f) :
    AEStronglyMeasurable (fun τ => toL2 (f τ)) volume := by
  have hm := hf.measurable
  have hF' : StronglyMeasurable (hm.mk _) := hm.stronglyMeasurable_mk
  have hslices := Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Space)) hm.ae_eq_mk
  have hpath : toPathLq 2 volume (fun z : SpaceTime => f z.1 z.2) =ᵐ[volume]
      toPathLq 2 volume (hm.mk _) := by
    filter_upwards [hslices] with t ht using toPathLq_congr_ae ht
  rw [← toPathLq_eq_toL2]
  exact (stronglyMeasurable_toPathLq hF').aestronglyMeasurable.congr hpath.symm

theorem Y2.integrableOn_Ioc (hf : IsY2Div T f) :
    IntegrableOn (fun τ => toL2 (f τ)) (Ioc 0 T) := by
  have h := stronglyMeasurable_toPath_Lq (Y2.memLp_prod hf)
  rw [toPathLq_eq_toL2] at h
  have hmem : MemLp (fun τ => toL2 (f τ)) 2 (volume.restrict (Ioc 0 T)) := by
    refine ⟨h.1, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top, h.2]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (Y2.memLp_prod hf).eLpNorm_ne_top
  exact hmem.integrable one_le_two

theorem Y2.integrableOn (hT : 0 < T) (hf : IsY2Div T f) (lo hi : ℝ) :
    IntegrableOn (fun τ => toL2 (f τ)) (Ioo lo hi) := by
  have hper : Function.Periodic (fun τ => toL2 (f τ)) T := fun τ => by
    simp only [hf.periodic τ]
  have h0 : IntervalIntegrable (fun τ => toL2 (f τ)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 (Y2.integrableOn_Ioc hf)
  rcases le_total lo hi with h | h
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le h).1
      (hper.intervalIntegrable₀ hT.ne' h0 lo hi)
  · rw [Ioo_eq_empty_of_le h]
    exact integrableOn_empty

theorem Y2.locallyIntegrable (hT : 0 < T) (hf : IsY2Div T f) :
    LocallyIntegrable (fun τ => toL2 (f τ)) :=
  locallyIntegrable_of_Ioo (Y2.integrableOn hT hf)

/-- Pairing a `𝒴₂` path with a fixed `L²` class is locally integrable. -/
theorem Y2.locallyIntegrable_inner (hT : 0 < T) (hf : IsY2Div T f) (G : L2Space) :
    LocallyIntegrable (fun τ => inner ℝ (toL2 (f τ)) G) := by
  have : (fun τ => inner ℝ (toL2 (f τ)) G) = fun τ => (innerSL ℝ G) (toL2 (f τ)) := by
    funext τ
    rw [innerSL_apply_apply, real_inner_comm]
  rw [this]
  exact locallyIntegrable_of_Ioo (fun lo hi =>
    (innerSL ℝ G).integrable_comp (Y2.integrableOn hT hf lo hi))

end Y2

/-! ## Tests: `L²` data and a countable dense family -/

/-- `Δφ = ∑ᵢ ∂ᵢ∂ᵢφ` for a vector test. -/
def testLap (φ : Space → Space) : SpatialField :=
  fun y => ∑ i : Fin 3, testPartial (testPartial φ i) i y

theorem isVectorTest_testPartial {φ : Space → Space} (hφ : IsVectorTest φ) (j : Fin 3) :
    IsVectorTest (testPartial φ j) :=
  ⟨(hφ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    hφ.compact.fderiv_apply (𝕜 := ℝ) _⟩

theorem isVectorTest_testLap {φ : Space → Space} (hφ : IsVectorTest φ) :
    IsVectorTest (testLap φ) := by
  have h : ∀ i, IsVectorTest (testPartial (testPartial φ i) i) := fun i =>
    isVectorTest_testPartial (isVectorTest_testPartial hφ i) i
  refine ⟨?_, ?_⟩
  · exact ContDiff.sum (fun i _ => (h i).smooth)
  · have e : testLap φ = fun x => (testPartial (testPartial φ 0) 0 x +
        testPartial (testPartial φ 1) 1 x) + testPartial (testPartial φ 2) 2 x := by
      funext x
      simp [testLap, Fin.sum_univ_three]
    rw [e]
    exact ((h 0).compact.add (h 1).compact).add (h 2).compact

/-- The `L²` data of a test: `φ`, `Δφ` and `∂ⱼφ`. -/
def testData (φ : Space → Space) : L2Space × L2Space × (Fin 3 → L2Space) :=
  (toL2 φ, toL2 (testLap φ), fun j => toL2 (testPartial φ j))

/-- **From each test to all tests at a.e. phase.** If `Λ_τ` is continuous in the `L²` data of
the test and `Λ_τ(φ) = 0` at a.e. phase for every test, then a.e. phase satisfies `Λ_τ(φ) = 0`
for every test. -/
theorem ae_forall_tests {Λ : ℝ → L2Space × L2Space × (Fin 3 → L2Space) → ℝ}
    (hΛ : ∀ τ, Continuous (Λ τ))
    (h : ∀ φ, IsVectorTest φ → ∀ᵐ τ, Λ τ (testData φ) = 0) :
    ∀ᵐ τ, ∀ φ, IsVectorTest φ → Λ τ (testData φ) = 0 := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨ENNReal.ofNat_ne_top⟩
  haveI : SecondCountableTopology L2Space := MeasureTheory.Lp.SecondCountableTopology
  set S := testData '' {φ | IsVectorTest φ} with hS
  obtain ⟨t, htS, htc, hSt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hchoose : ∀ v : t, ∃ φ, IsVectorTest φ ∧ testData φ = v := fun v => htS v.2
  choose φs hφs using hchoose
  haveI := htc.to_subtype
  have hall : ∀ᵐ τ, ∀ v : t, Λ τ v = 0 := by
    rw [ae_all_iff]
    intro v
    have := h (φs v) (hφs v).1
    rwa [(hφs v).2] at this
  filter_upwards [hall] with τ hτ φ hφ
  have hclosed : IsClosed {v | Λ τ v = 0} := isClosed_eq (hΛ τ) continuous_const
  have hsub : t ⊆ {v | Λ τ v = 0} := fun v hv => hτ ⟨v, hv⟩
  exact (hclosed.closure_subset_iff.mpr hsub) (hSt ⟨φ, hφ, rfl⟩)

/-! ## Product tests `ψ(τ,y) = θ(τ)φ(y)` -/

/-- The product test `ψ(τ, y) = θ(τ) φ(y)` (as in `Loc/Hyp/BackgroundStrongForm/ProductTest.lean`,
line 96). -/
def prodTest (θ : ℝ → ℝ) (φ : Space → Space) : SpaceTime → Space := fun z => θ z.1 • φ z.2

variable {θ : ℝ → ℝ} {φ : Space → Space}

theorem isSimilarityTest_prodTest (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hφ : IsVectorTest φ) : IsSimilarityTest (prodTest θ φ) := by
  refine ⟨(hθ.comp contDiff_fst).smul (hφ.smooth.comp contDiff_snd), ?_⟩
  have hsub : tsupport (prodTest θ φ) ⊆ tsupport θ ×ˢ tsupport φ := by
    refine closure_minimal ?_ ((isClosed_tsupport θ).prod (isClosed_tsupport φ))
    intro z hz
    rw [Function.mem_support] at hz
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · intro h0
      apply hz
      simp [prodTest, h0]
    · intro h0
      apply hz
      simp [prodTest, h0]
  exact IsCompact.of_isClosed_subset (IsCompact.prod hθc hφ.compact) (isClosed_tsupport _) hsub

theorem spatialDerivative_prodTest (hφ : IsVectorTest φ) (t : ℝ) (x : Space) :
    spatialDerivative (prodTest θ φ) t x = θ t • fderiv ℝ φ x := by
  unfold spatialDerivative prodTest
  exact fderiv_fun_const_smul (hφ.smooth.differentiable (by simp) x) (θ t)

theorem spatialLaplacian_prodTest (hφ : IsVectorTest φ) (t : ℝ) (x : Space) :
    spatialLaplacian (prodTest θ φ) t x = θ t • testLap φ x := by
  unfold spatialLaplacian testLap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (fun y => spatialDerivative (prodTest θ φ) t y (coordinateVector i)) =
      fun y => θ t • testPartial φ i y := by
    funext y
    rw [spatialDerivative_prodTest hφ]
    rfl
  rw [e, fderiv_fun_const_smul
    ((isVectorTest_testPartial hφ i).smooth.differentiable (by simp) x) (θ t)]
  rfl

theorem testPartial_smul (c : ℝ) (hφ : IsVectorTest φ) (j : Fin 3) :
    testPartial (fun y => c • φ y) j = c • testPartial φ j := by
  funext y
  unfold testPartial
  rw [fderiv_fun_const_smul (hφ.smooth.differentiable (by simp) y) c]
  rfl

theorem lerayDivPairing_smul (col : Fin 3 → SpatialField) (c : ℝ) (hφ : IsVectorTest φ) :
    lerayDivPairing col (fun y => c • φ y) = c * lerayDivPairing col φ := by
  unfold lerayDivPairing
  have e : ∀ j, toL2 (testPartial (fun y => c • φ y) j) = c • toL2 (testPartial φ j) := by
    intro j
    rw [testPartial_smul c hφ j]
    exact L13.toL2_smul' c (L13.isVectorTest_memLp (isVectorTest_testPartial hφ j))
  simp only [e, map_smul, inner_smul_right]
  rw [mul_neg, Finset.mul_sum]

theorem inner_toL2_toL2 {g k : SpatialField} (hg : MemLp g 2 volume) (hk : MemLp k 2 volume) :
    inner ℝ (toL2 g) (toL2 k) = ∫ y, inner ℝ (g y) (k y) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hg, coeFn_toL2 hk] with y h1 h2
  rw [h1, h2]

/-- **Fubini for product tests.** For a spacetime-integrable pairing of `f` with `θ(τ)k(y)`,
`∫∫ ⟨f, θ k⟩ = ∫ θ(τ) ⟨f(τ), k⟩ dτ`, when `f(τ) ∈ L²` at a.e. phase. -/
theorem integral_pair_prod {f : ℝ → SpatialField} {k : SpatialField} (hk : MemLp k 2 volume)
    (hae : ∀ᵐ τ, MemLp (f τ) 2 volume)
    (hint : Integrable (fun z : SpaceTime => inner ℝ (f z.1 z.2) (θ z.1 • k z.2))) :
    ∫ z : SpaceTime, inner ℝ (f z.1 z.2) (θ z.1 • k z.2) =
      ∫ τ, θ τ * inner ℝ (toL2 (f τ)) (toL2 k) := by
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hae] with τ hτ
  simp only [inner_smul_right]
  rw [integral_const_mul, inner_toL2_toL2 hτ hk]

end UnforcedLeray.Blueprint.ModeId
