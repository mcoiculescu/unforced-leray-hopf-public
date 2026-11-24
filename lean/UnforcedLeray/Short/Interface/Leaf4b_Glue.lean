import UnforcedLeray.Short.Interface.WindowSteps

/-!
# Interface: step G2a, gluing the window Laplacians (`WindowGlueLocal`)

Task `Interface:I19`. Target: `WindowGlueLocal` (`Short/Interface/WindowSteps.lean`), the
partition-of-unity step of the patching argument (old manuscript `paper/main.tex` lines
7519-7536; shorter proof `the November 2 reference manuscript`, the window
patching of the free equation, used with `WindowsToGlobalLaplacian`).

Construction. Fix a smooth partition of unity `ρ n` on the phase line, subordinate to the
windows `(n-1, n+1)`, with `∑ₙ ρ n τ = 1`. Put `L τ y = ∑ₙ ρ n τ • Λ n τ y`, a finite sum at
each phase. For a test `ψ`, the pieces `ρ n · ψ` are tests supported in the windows, so
`∫⟨L, ψ⟩ = ∑ₙ ∫⟨Λ n, ρ n ψ⟩ = ∑ₙ ∫⟨w, Δ(ρ n ψ)⟩ = ∫⟨w, Δψ⟩`, because `Δ(ρ n · ψ) = ρ n · Δψ`
(`ρ n` depends on the phase only) and `∑ₙ ρ n = 1` on the phases where `ψ` lives. No
uniqueness of weak Laplacians is needed (the overlap identity is built into the sum).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

open UnforcedLeray UnforcedLeray.Blueprint

namespace UnforcedLeray.Short.Interface

/-! ## 1. Basic facts on the window slab -/

theorem mem_windowSlab {τ₀ r : ℝ} {z : SpaceTime} :
    z ∈ windowSlab τ₀ r ↔ z.1 ∈ Ioo (τ₀ - r) (τ₀ + r) := by
  unfold windowSlab
  simp only [mem_prod, mem_univ, and_true]

theorem windowSlab_measurable (τ₀ r : ℝ) : MeasurableSet (windowSlab τ₀ r) := by
  unfold windowSlab
  exact measurableSet_Ioo.prod MeasurableSet.univ

/-! ## 2. A smooth partition of unity in the phase -/

/-- A smooth partition of unity `ρ n` on `ℝ`, subordinate to the windows `(n-1, n+1)`. -/
theorem exists_phasePartition :
    ∃ ρ : ℤ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (ρ n)) ∧
      (∀ n, tsupport (ρ n) ⊆ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1)) ∧
      (∀ τ, ∑ᶠ n, ρ n τ = 1) := by
  have hcover : (univ : Set ℝ) ⊆ ⋃ n : ℤ, Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) := by
    intro τ _
    refine mem_iUnion.2 ⟨⌊τ⌋, ?_⟩
    exact ⟨by linarith [Int.floor_le τ], by linarith [Int.lt_floor_add_one τ]⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := modelWithCornersSelf ℝ ℝ) (M := ℝ)
    (ι := ℤ) isClosed_univ (fun n : ℤ => Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    (fun n => isOpen_Ioo) hcover
  exact ⟨fun n => (f n : ℝ → ℝ), fun n => contMDiff_iff_contDiff.1 (f n).contMDiff,
    fun n => hf n, fun τ => f.sum_eq_one (mem_univ τ)⟩

/-- The phase cut `ρ n(τ) ψ(τ, y)` of a test field. -/
def phaseCut (ρ : ℤ → ℝ → ℝ) (ψ : SpaceTime → Space) (n : ℤ) : SpaceTime → Space :=
  fun p => ρ n p.1 • ψ p

/-- The glued field `L τ y = ∑ₙ ρ n τ • Λ n τ y` (a finite sum at each phase). -/
def glueLaplacian (ρ : ℤ → ℝ → ℝ) (Λ : ℤ → ℝ → SpatialField) : ℝ → SpatialField :=
  fun τ y => ∑ᶠ n : ℤ, ρ n τ • Λ n τ y

theorem phase_window_of_ne {ρ : ℤ → ℝ → ℝ}
    (hρsub : ∀ n, tsupport (ρ n) ⊆ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    (n : ℤ) (z : SpaceTime) (h : ρ n z.1 ≠ 0) : z ∈ windowSlab (n : ℝ) 1 :=
  mem_windowSlab.2 (hρsub n (subset_tsupport _ (Function.mem_support.2 h)))

theorem phaseCut_tsupport {ρ : ℤ → ℝ → ℝ}
    (hρsub : ∀ n, tsupport (ρ n) ⊆ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    (ψ : SpaceTime → Space) (n : ℤ) :
    tsupport (phaseCut ρ ψ n) ⊆ windowSlab (n : ℝ) 1 := by
  have hsupp : Function.support (phaseCut ρ ψ n) ⊆ Prod.fst ⁻¹' tsupport (ρ n) := by
    intro p hp
    have hρ : ρ n p.1 ≠ 0 := fun h => (Function.mem_support.1 hp) (by simp [phaseCut, h])
    exact subset_tsupport _ (Function.mem_support.2 hρ)
  have hclosed : IsClosed (Prod.fst ⁻¹' tsupport (ρ n)) :=
    (isClosed_tsupport (ρ n)).preimage (continuous_fst : Continuous (Prod.fst : SpaceTime → ℝ))
  refine (closure_minimal hsupp hclosed).trans ?_
  intro p hp
  have hp' : p.1 ∈ tsupport (ρ n) := hp
  exact mem_windowSlab.2 (hρsub n hp')

/-! ## 3. Cutoffs and the finite index set -/

theorem cutoff_of_compact (ψ : SpaceTime → Space) (hψ : IsSimilarityTest ψ) :
    ∃ R : ℝ, ∀ p : SpaceTime, R < |p.1| → ψ p = 0 := by
  have hK : IsCompact (tsupport ψ) := hψ.compact
  have hbdd : Bornology.IsBounded (Prod.fst '' tsupport ψ) := (hK.image continuous_fst).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hbdd
  refine ⟨R, fun p hp => ?_⟩
  by_contra hne
  have hmem : p ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hne)
  have h1 : p.1 ∈ Metric.closedBall (0 : ℝ) R := hR (mem_image_of_mem Prod.fst hmem)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  linarith

theorem phase_zero_of_far {ρ : ℤ → ℝ → ℝ}
    (hρsub : ∀ n, tsupport (ρ n) ⊆ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    {R : ℝ} {N : ℤ} (hRN : R ≤ N) {τ : ℝ} (hτ : |τ| ≤ R) {n : ℤ}
    (hn : n ∉ Finset.Icc (-N) N) : ρ n τ = 0 := by
  by_contra h
  have hmem : τ ∈ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) :=
    hρsub n (subset_tsupport _ (Function.mem_support.2 h))
  obtain ⟨h1, h2⟩ := hmem
  obtain ⟨hτl, hτr⟩ := abs_le.1 hτ
  rw [Finset.mem_Icc] at hn
  by_cases hlow : n < -N
  · have h3 : n + 1 ≤ -N := by omega
    have h4 : (n : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast h3
    linarith
  · have h3 : N + 1 ≤ n := by omega
    have h4 : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h3
    linarith

theorem phase_sum_on_F {ρ : ℤ → ℝ → ℝ}
    (hρsub : ∀ n, tsupport (ρ n) ⊆ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    (hρsum : ∀ τ, ∑ᶠ n, ρ n τ = 1) {R : ℝ} {N : ℤ} (hRN : R ≤ N) {τ : ℝ} (hτ : |τ| ≤ R) :
    ∑ n ∈ Finset.Icc (-N) N, ρ n τ = 1 := by
  have hsupp : Function.support (fun n => ρ n τ) ⊆ ↑(Finset.Icc (-N) N) := by
    intro n hn
    rw [Finset.mem_coe]
    by_contra hF
    exact Function.mem_support.1 hn (phase_zero_of_far hρsub hRN hτ hF)
  calc ∑ n ∈ Finset.Icc (-N) N, ρ n τ = ∑ᶠ n, ρ n τ :=
        (finsum_eq_sum_of_support_subset _ hsupp).symm
    _ = 1 := hρsum τ

/-! ## 4. The spatial Laplacian of a phase-scaled test -/

theorem fderiv_slice_smul (c : ℝ) (g : Space → Space) (hg : ContDiff ℝ ∞ g) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' => c • g y') y (coordinateVector i)) x
        (coordinateVector i)) =
      c • ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector i)) x
        (coordinateVector i) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ g y (coordinateVector i)) x :=
    ((hD.differentiable (by simp)).clm_apply (differentiable_const _)) x
  have h1 : ∀ y, fderiv ℝ (fun y' => c • g y') y = c • fderiv ℝ g y :=
    fun y => fderiv_const_smul ((hg.differentiable (by simp)) y) c
  have h2 : (fun y => fderiv ℝ (fun y' => c • g y') y (coordinateVector i)) =
      fun y => c • fderiv ℝ g y (coordinateVector i) := by
    funext y
    rw [h1 y]
    rfl
  have h3 : fderiv ℝ (fun y => c • fderiv ℝ g y (coordinateVector i)) x =
      c • fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector i)) x :=
    fderiv_const_smul hdiff c
  rw [h2, h3]
  rfl

theorem spatialLaplacian_phase (c : ℝ → ℝ) (ψ : SpaceTime → Space) (hψ : ContDiff ℝ ∞ ψ)
    (t : ℝ) (x : Space) :
    spatialLaplacian (fun z : SpaceTime => c z.1 • ψ z) t x = c t • spatialLaplacian ψ t x := by
  have hpair : ContDiff ℝ ∞ (fun y : Space => ((t, y) : SpaceTime)) :=
    contDiff_const.prodMk contDiff_id
  exact fderiv_slice_smul (c t) (fun y => ψ (t, y)) (hψ.comp hpair) x

theorem spatialLaplacian_zero_of_slice (ψ : SpaceTime → Space) (t : ℝ) (x : Space)
    (h : ∀ y, ψ (t, y) = 0) : spatialLaplacian ψ t x = 0 := by
  have hf : (fun y : Space => ψ (t, y)) = fun _ => 0 := funext h
  have hD : ∀ y, spatialDerivative ψ t y = 0 := fun y => by
    unfold spatialDerivative
    rw [hf]
    simp
  simp [spatialLaplacian, hD]

/-! ## 5. Splitting the two pairings along the partition -/

theorem diffusion_phase_split (ρ : ℤ → ℝ → ℝ) (ψ : SpaceTime → Space) (hψ : ContDiff ℝ ∞ ψ)
    (w : ℝ → SpatialField) (F : Finset ℤ) {R : ℝ}
    (hψR : ∀ p : SpaceTime, R < |p.1| → ψ p = 0)
    (hsum : ∀ τ, |τ| ≤ R → ∑ n ∈ F, ρ n τ = 1) (z : SpaceTime) :
    diffusionTerm w ψ z = ∑ n ∈ F, diffusionTerm w (phaseCut ρ ψ n) z := by
  have hpt : ∀ n, spatialLaplacian (phaseCut ρ ψ n) z.1 z.2 =
      ρ n z.1 • spatialLaplacian ψ z.1 z.2 :=
    fun n => spatialLaplacian_phase (ρ n) ψ hψ z.1 z.2
  by_cases hz : |z.1| ≤ R
  · simp only [diffusionTerm, hpt, real_inner_smul_right]
    rw [← Finset.sum_mul, hsum z.1 hz, one_mul]
  · have h0 : spatialLaplacian ψ z.1 z.2 = 0 :=
      spatialLaplacian_zero_of_slice ψ z.1 z.2 (fun y => hψR (z.1, y) (not_le.1 hz))
    simp [diffusionTerm, hpt, h0]

theorem pair_phase_split (Λ : ℤ → ℝ → SpatialField) (ρ : ℤ → ℝ → ℝ) (ψ : SpaceTime → Space)
    (F : Finset ℤ) {R : ℝ} (hψR : ∀ p : SpaceTime, R < |p.1| → ψ p = 0)
    (hF : ∀ τ, |τ| ≤ R → ∀ n, n ∉ F → ρ n τ = 0) (z : SpaceTime) :
    pairTerm (glueLaplacian ρ Λ) ψ z = ∑ n ∈ F, pairTerm (Λ n) (phaseCut ρ ψ n) z := by
  by_cases hz : |z.1| ≤ R
  · have hsupp : Function.support (fun n => ρ n z.1 • Λ n z.1 z.2) ⊆ ↑F := by
      intro n hn
      rw [Finset.mem_coe]
      by_contra hnF
      exact Function.mem_support.1 hn (by simp [hF z.1 hz n hnF])
    simp only [pairTerm, glueLaplacian, phaseCut]
    rw [finsum_eq_sum_of_support_subset _ hsupp, sum_inner]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [real_inner_smul_left, real_inner_smul_right]
  · have hψz : ψ z = 0 := hψR z (not_le.1 hz)
    simp [pairTerm, phaseCut, hψz]

/-! ## 6. Integrability of the summands -/

theorem summand_memLp {ρ : ℤ → ℝ → ℝ} {Λ : ℤ → ℝ → SpatialField}
    (hρsm : ∀ n, ContDiff ℝ ∞ (ρ n))
    (hρsub : ∀ n, tsupport (ρ n) ⊆ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    (hΛ : ∀ n : ℤ, MemLp (fun z : SpaceTime => Λ n z.1 z.2) 2
      (volume.restrict (windowSlab (n : ℝ) 1)))
    (n : ℤ) :
    MemLp (fun z : SpaceTime => ρ n z.1 • Λ n z.1 z.2) 2 volume := by
  have hcpt : IsCompact (tsupport (ρ n)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport (ρ n)) ((hρsub n).trans Ioo_subset_Icc_self)
  obtain ⟨C, hC⟩ := (hρsm n).continuous.bounded_above_of_compact_support hcpt
  have hφ : MemLp (fun z : SpaceTime => ρ n z.1) ∞ (volume.restrict (windowSlab (n : ℝ) 1)) :=
    memLp_top_of_bound ((hρsm n).continuous.comp continuous_fst).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hC z.1)
  have hres : MemLp (fun z : SpaceTime => ρ n z.1 • Λ n z.1 z.2) 2
      (volume.restrict (windowSlab (n : ℝ) 1)) := MemLp.smul (hΛ n) hφ
  have hsupp : Function.support (fun z : SpaceTime => ρ n z.1 • Λ n z.1 z.2) ⊆
      windowSlab (n : ℝ) 1 := by
    intro z hz
    refine phase_window_of_ne hρsub n z ?_
    intro h
    exact Function.mem_support.1 hz (by simp [h])
  have hind := (memLp_indicator_iff_restrict (windowSlab_measurable (n : ℝ) 1)).2 hres
  rwa [Set.indicator_eq_self.2 hsupp] at hind

/-! ## 7. The gluing step -/

/-- **Step G2a, the window gluing** (`WindowGlueLocal`). The window Laplacians `Λ n` (with
`L²` on `(n-1, n+1) × ℝ³` and the weak Laplacian property for tests in the window) glue to the
field `L τ y = ∑ₙ ρ n τ • Λ n τ y`, where `ρ` is a smooth phase partition of unity subordinate to
the windows. `L` is a.e. strongly measurable and `L²` on each window, and it is a weak Laplacian of
`w` against every similarity test. -/
theorem windowGlueLocal : WindowGlueLocal := by
  intro w Λ hΛ
  obtain ⟨ρ, hρsm, hρsub, hρsum⟩ := exists_phasePartition
  have hΛ' : ∀ n : ℤ, MemLp (fun z : SpaceTime => Λ n z.1 z.2) 2
      (volume.restrict (windowSlab (n : ℝ) 1)) := fun n => (hΛ n).1
  have hG : ∀ n : ℤ, MemLp (fun z : SpaceTime => ρ n z.1 • Λ n z.1 z.2) 2 volume :=
    fun n => summand_memLp hρsm hρsub hΛ' n
  -- `L²` on each window: on `windowSlab m 1` only the summands `n ∈ [m-1, m+1]` survive.
  have hwin : ∀ m : ℤ, MemLp (fun z : SpaceTime => glueLaplacian ρ Λ z.1 z.2) 2
      (volume.restrict (windowSlab (m : ℝ) 1)) := by
    intro m
    have hpt : ∀ z ∈ windowSlab (m : ℝ) 1,
        glueLaplacian ρ Λ z.1 z.2 = ∑ n ∈ Finset.Icc (m - 1) (m + 1), ρ n z.1 • Λ n z.1 z.2 := by
      intro z hz
      have hz1 : z.1 ∈ Ioo ((m : ℝ) - 1) ((m : ℝ) + 1) := mem_windowSlab.1 hz
      show ∑ᶠ n : ℤ, ρ n z.1 • Λ n z.1 z.2 = ∑ n ∈ Finset.Icc (m - 1) (m + 1), ρ n z.1 • Λ n z.1 z.2
      apply finsum_eq_sum_of_support_subset
      intro n hn
      have hρ : ρ n z.1 ≠ 0 := fun h => Function.mem_support.1 hn (by simp [h])
      have h1 : z.1 ∈ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) :=
        hρsub n (subset_tsupport _ (Function.mem_support.2 hρ))
      have hlo : (m : ℝ) - 2 < n := by linarith [h1.1, h1.2, hz1.1, hz1.2]
      have hhi : (n : ℝ) < m + 2 := by linarith [h1.1, h1.2, hz1.1, hz1.2]
      have hlo' : m - 2 < n := by exact_mod_cast hlo
      have hhi' : n < m + 2 := by exact_mod_cast hhi
      rw [Finset.mem_coe, Finset.mem_Icc]
      constructor <;> omega
    have hsumT : MemLp (fun z : SpaceTime => ∑ n ∈ Finset.Icc (m - 1) (m + 1),
        ρ n z.1 • Λ n z.1 z.2) 2 (volume.restrict (windowSlab (m : ℝ) 1)) :=
      memLp_finsetSum _ fun n _ => (hG n).restrict _
    have hae : (fun z : SpaceTime => ∑ n ∈ Finset.Icc (m - 1) (m + 1),
        ρ n z.1 • Λ n z.1 z.2) =ᵐ[volume.restrict (windowSlab (m : ℝ) 1)]
        (fun z : SpaceTime => glueLaplacian ρ Λ z.1 z.2) :=
      ae_restrict_of_forall_mem (windowSlab_measurable _ _) fun z hz => (hpt z hz).symm
    exact MemLp.ae_eq hae hsumT
  -- the windows cover the phase line, so the glued field is a.e. strongly measurable
  have hcov : (⋃ m : ℤ, windowSlab (m : ℝ) 1) = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ⟨⌊z.1⌋, mem_windowSlab.2 ⟨?_, ?_⟩⟩
    · linarith [Int.floor_le z.1]
    · linarith [Int.lt_floor_add_one z.1]
  refine ⟨glueLaplacian ρ Λ, ?_, fun m => hwin m, ?_⟩
  · have h : AEStronglyMeasurable (fun z : SpaceTime => glueLaplacian ρ Λ z.1 z.2)
        (volume.restrict (⋃ m : ℤ, windowSlab (m : ℝ) 1)) :=
      aestronglyMeasurable_iUnion_iff.2 fun m => (hwin m).aestronglyMeasurable
    rw [hcov, Measure.restrict_univ] at h
    exact h
  · intro ψ hψ
    obtain ⟨R, hψR⟩ := cutoff_of_compact ψ hψ
    obtain ⟨N, hN⟩ : ∃ N : ℤ, R ≤ N := ⟨⌈R⌉, Int.le_ceil R⟩
    have hsumF : ∀ τ, |τ| ≤ R → ∑ n ∈ Finset.Icc (-N) N, ρ n τ = 1 :=
      fun τ hτ => phase_sum_on_F hρsub hρsum hN hτ
    have hFzero : ∀ τ, |τ| ≤ R → ∀ n, n ∉ Finset.Icc (-N) N → ρ n τ = 0 :=
      fun τ hτ n hn => phase_zero_of_far hρsub hN hτ hn
    have hcut_test : ∀ n, IsSimilarityTest (phaseCut ρ ψ n) := by
      intro n
      refine ⟨?_, ?_⟩
      · unfold phaseCut
        exact ((hρsm n).comp contDiff_fst).smul hψ.smooth
      · unfold phaseCut
        exact HasCompactSupport.smul_left (f := fun z : SpaceTime => ρ n z.1) hψ.compact
    have hwin' : ∀ n, WeakIdentity (diffusionTerm w (phaseCut ρ ψ n))
        (pairTerm (Λ n) (phaseCut ρ ψ n)) :=
      fun n => (hΛ n).2 (phaseCut ρ ψ n) (hcut_test n) (phaseCut_tsupport hρsub ψ n)
    have hdiff_eq : ∀ z, diffusionTerm w ψ z =
        ∑ n ∈ Finset.Icc (-N) N, diffusionTerm w (phaseCut ρ ψ n) z :=
      fun z => diffusion_phase_split ρ ψ hψ.smooth w (Finset.Icc (-N) N) hψR hsumF z
    have hpair_eq : ∀ z, pairTerm (glueLaplacian ρ Λ) ψ z =
        ∑ n ∈ Finset.Icc (-N) N, pairTerm (Λ n) (phaseCut ρ ψ n) z :=
      fun z => pair_phase_split Λ ρ ψ (Finset.Icc (-N) N) hψR hFzero z
    unfold laplacianPairing
    refine ⟨?_, ?_, ?_⟩
    · have e : diffusionTerm w ψ = fun z =>
          ∑ n ∈ Finset.Icc (-N) N, diffusionTerm w (phaseCut ρ ψ n) z := funext hdiff_eq
      rw [e]
      exact integrable_finsetSum _ fun n _ => (hwin' n).left_integrable
    · have e : pairTerm (glueLaplacian ρ Λ) ψ = fun z =>
          ∑ n ∈ Finset.Icc (-N) N, pairTerm (Λ n) (phaseCut ρ ψ n) z := funext hpair_eq
      rw [e]
      exact integrable_finsetSum _ fun n _ => (hwin' n).right_integrable
    · calc ∫ z, diffusionTerm w ψ z
          = ∫ z, ∑ n ∈ Finset.Icc (-N) N, diffusionTerm w (phaseCut ρ ψ n) z :=
            integral_congr_ae (ae_of_all _ hdiff_eq)
        _ = ∑ n ∈ Finset.Icc (-N) N, ∫ z, diffusionTerm w (phaseCut ρ ψ n) z :=
            integral_finsetSum _ fun n _ => (hwin' n).left_integrable
        _ = ∑ n ∈ Finset.Icc (-N) N, ∫ z, pairTerm (Λ n) (phaseCut ρ ψ n) z :=
            Finset.sum_congr rfl fun n _ => (hwin' n).eq
        _ = ∫ z, ∑ n ∈ Finset.Icc (-N) N, pairTerm (Λ n) (phaseCut ρ ψ n) z :=
            (integral_finsetSum _ fun n _ => (hwin' n).right_integrable).symm
        _ = ∫ z, pairTerm (glueLaplacian ρ Λ) ψ z :=
            integral_congr_ae (ae_of_all _ fun z => (hpair_eq z).symm)

end UnforcedLeray.Short.Interface
