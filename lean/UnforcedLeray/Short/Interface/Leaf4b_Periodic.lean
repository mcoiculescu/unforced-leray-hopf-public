import UnforcedLeray.Short.Interface.Leaf4b_Unique
import UnforcedLeray.Cons.C08PhysicalMode.Slices

/-!
# Interface I20: periodic selection of the weak Laplacian (step G2b)

Proof of `periodicSelection : PeriodicSelection` (`WindowSteps.lean`, line 141), following


Let `w` be `P`-periodic in `𝒴₂` and let `L` be a locally `L²` weak Laplacian of `w`.

* `L` is locally integrable on `ℝ × ℝ³`: every point lies in an open window `(n-1, n+1) × ℝ³`
  on which `L` is `L²`.
* For a shift `c` with `w(· + c) = w`, the translate `L(· + c)` is again a weak Laplacian of
  `w`: translate the test by `-c`, the spatial Laplacian does not see the phase shift.
* `WeakLaplacianUnique` (`Leaf4b_Unique.lean`, I18) with `O = univ` gives `L(· + nP) =ᵐ L`
  for every `n ∈ ℤ`. Hence `L` is almost everywhere `P`-periodic, and the periodization
  `periodize hP L` (`Cons/C08PhysicalMode/Slices.lean`) equals `L` almost everywhere.
* The periodization is a `𝒴₂` field: periodic, measurable, and `L²` on `(0, P] × ℝ³` (it equals
  `L` there, and `(0, P]` lies in finitely many windows). It is a weak Laplacian of `w`, because
  it equals `L` almost everywhere.

Helpers carry the prefix `i20_`. No statement of `WindowSteps.lean` is changed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic

/-! ## Windows -/

theorem i20_mem_windowSlab (τ₀ r : ℝ) (z : SpaceTime) :
    z ∈ windowSlab τ₀ r ↔ z.1 ∈ Ioo (τ₀ - r) (τ₀ + r) := by
  unfold windowSlab
  exact Set.mem_prod.trans (and_iff_left (Set.mem_univ _))

theorem i20_isOpen_windowSlab (τ₀ r : ℝ) : IsOpen (windowSlab τ₀ r) := by
  unfold windowSlab
  exact isOpen_Ioo.prod isOpen_univ

/-- Every point lies in the window of unit radius centred at the floor of its phase. -/
theorem i20_floor_mem_windowSlab (z : SpaceTime) : z ∈ windowSlab (⌊z.1⌋ : ℝ) 1 :=
  (i20_mem_windowSlab _ _ _).2
    (Set.mem_Ioo.2 ⟨by linarith [Int.floor_le z.1], by linarith [Int.lt_floor_add_one z.1]⟩)

/-! ## Local integrability from local `L²` -/

/-- A function that is `L²` on an open neighbourhood of every point is locally integrable. -/
theorem i20_locallyIntegrable_of_cover {F : SpaceTime → Space}
    (h : ∀ x : SpaceTime, ∃ W : Set SpaceTime, IsOpen W ∧ x ∈ W ∧ MemLp F 2 (volume.restrict W)) :
    LocallyIntegrable F volume := by
  intro x
  obtain ⟨W, hWo, hxW, hW⟩ := h x
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hres : MemLp F 2 (volume.restrict (K ∩ W)) := by
    have h2 := hW.restrict K
    rwa [Measure.restrict_restrict hKm] at h2
  have : IsFiniteMeasure (volume.restrict (K ∩ W)) :=
    isFiniteMeasure_restrict.2
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKc.measure_lt_top).ne
  unfold IntegrableAtFilter
  exact ⟨K ∩ W, inter_mem hKn (hWo.mem_nhds hxW), MemLp.integrable (by norm_num) hres⟩

/-- A field that is `L²` on every integer window is locally integrable on `ℝ × ℝ³`. -/
theorem i20_locallyIntegrable_windows {L : ℝ → SpatialField}
    (hwin : ∀ n : ℤ, MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (windowSlab n 1))) :
    LocallyIntegrable (fun z : SpaceTime => L z.1 z.2) volume := by
  apply i20_locallyIntegrable_of_cover
  intro x
  exact ⟨windowSlab (⌊x.1⌋ : ℝ) 1, i20_isOpen_windowSlab _ _, i20_floor_mem_windowSlab x,
    hwin _⟩

/-- Time translation of an `L²` field: the translate is `L²` on the preimage of the window. -/
theorem i20_memLp_translate {L : ℝ → SpatialField} {V : Set SpaceTime} (hV : IsOpen V) (c : ℝ)
    (hL : MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict V)) :
    MemLp (fun z : SpaceTime => L (z.1 + c) z.2) 2
      (volume.restrict ((fun z : SpaceTime => z + (c, (0 : Space))) ⁻¹' V)) := by
  have hrp := (measurePreserving_shift c (0 : Space)).restrict_preimage hV.measurableSet
  have h := hL.comp_measurePreserving hrp
  have e : (fun z : SpaceTime => L (z.1 + c) z.2) =
      (fun u : SpaceTime => L u.1 u.2) ∘ (fun z : SpaceTime => z + (c, (0 : Space))) := by
    funext z
    simp
  rw [e]
  exact h

/-- The time translate `L(· + c)` of a field that is `L²` on every integer window is locally
integrable. -/
theorem i20_locallyIntegrable_shift {L : ℝ → SpatialField} (c : ℝ)
    (hwin : ∀ n : ℤ, MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (windowSlab n 1))) :
    LocallyIntegrable (fun z : SpaceTime => L (z.1 + c) z.2) volume := by
  apply i20_locallyIntegrable_of_cover
  intro x
  refine ⟨(fun z : SpaceTime => z + (c, (0 : Space))) ⁻¹'
      windowSlab (⌊(x + (c, (0 : Space))).1⌋ : ℝ) 1, ?_, ?_, ?_⟩
  · exact IsOpen.preimage (continuous_add_const (c, (0 : Space))) (i20_isOpen_windowSlab _ _)
  · exact i20_floor_mem_windowSlab (x + (c, (0 : Space)))
  · exact i20_memLp_translate (i20_isOpen_windowSlab _ _) c (hwin _)

/-! ## Translating a weak Laplacian -/

/-- If `w` is `c`-periodic, the time translate `L(· + c)` of a weak Laplacian `L` of `w` is a
weak Laplacian of `w`. The test is translated by `-c`; the spatial Laplacian commutes with the
phase shift, and `w(z.1 + -c) = w z.1` by periodicity. -/
theorem i20_shift_laplacianPairing (w L : ℝ → SpatialField) (c : ℝ) (hw : ∀ t, w (t + c) = w t)
    (hL : ∀ ψ, IsSimilarityTest ψ → laplacianPairing w L ψ) :
    ∀ ψ, IsSimilarityTest ψ → laplacianPairing w (fun t => L (t + c)) ψ := by
  intro ψ hψ
  have hsm : ContDiff ℝ ∞ (fun z : SpaceTime => (z.1 + -c, z.2)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  have hψ' : IsSimilarityTest (fun z : SpaceTime => ψ (z.1 + -c, z.2)) :=
    ⟨hψ.smooth.comp hsm, hψ.compact.comp_homeomorph
      (Homeomorph.prodCongr (Homeomorph.addRight (-c)) (Homeomorph.refl Space))⟩
  have hLψ := hL _ hψ'
  have hLψ0 := hL ψ hψ
  unfold laplacianPairing at hLψ hLψ0 ⊢
  have hI2 : ∀ z : SpaceTime, diffusionTerm w (fun y : SpaceTime => ψ (y.1 + -c, y.2)) z =
      diffusionTerm w ψ (z + (-c, (0 : Space))) := by
    intro z
    have hz : z + (-c, (0 : Space)) = (z.1 + -c, z.2) := Prod.ext rfl (add_zero z.2)
    have hwz : w (z.1 + -c) = w z.1 := by
      have h : w (z.1 + -c + c) = w (z.1 + -c) := hw _
      rw [show z.1 + -c + c = z.1 by ring] at h
      exact h.symm
    rw [hz]
    show inner ℝ (w z.1 z.2) (spatialLaplacian ψ (z.1 + -c) z.2) =
      inner ℝ (w (z.1 + -c) z.2) (spatialLaplacian ψ (z.1 + -c) z.2)
    rw [hwz]
  have hI4 : ∀ z : SpaceTime, pairTerm (fun t => L (t + c)) ψ z =
      pairTerm L (fun y : SpaceTime => ψ (y.1 + -c, y.2)) (z + (c, (0 : Space))) := by
    intro z
    have hz : z + (c, (0 : Space)) = (z.1 + c, z.2) := Prod.ext rfl (add_zero z.2)
    have hc : z.1 + c + -c = z.1 := by ring
    rw [hz]
    show inner ℝ (L (z.1 + c) z.2) (ψ z) = inner ℝ (L (z.1 + c) z.2) (ψ (z.1 + c + -c, z.2))
    rw [hc]
  have e1 : ∫ z : SpaceTime, diffusionTerm w (fun y : SpaceTime => ψ (y.1 + -c, y.2)) z =
      ∫ z : SpaceTime, diffusionTerm w ψ z := by
    have h := (measurePreserving_shift (-c) (0 : Space)).integral_comp
      (measurableEmbedding_addRight ((-c : ℝ), (0 : Space))) (diffusionTerm w ψ)
    simp only [hI2]
    exact h
  have e2 : ∫ z : SpaceTime, pairTerm (fun t => L (t + c)) ψ z =
      ∫ z : SpaceTime, pairTerm L (fun y : SpaceTime => ψ (y.1 + -c, y.2)) z := by
    have h := (measurePreserving_shift c (0 : Space)).integral_comp
      (measurableEmbedding_addRight (c, (0 : Space)))
      (pairTerm L (fun y : SpaceTime => ψ (y.1 + -c, y.2)))
    simp only [hI4]
    exact h
  have hfun : pairTerm (fun t => L (t + c)) ψ =
      pairTerm L (fun y : SpaceTime => ψ (y.1 + -c, y.2)) ∘
        (fun z : SpaceTime => z + (c, (0 : Space))) :=
    funext hI4
  refine ⟨hLψ0.left_integrable, ?_, ?_⟩
  · rw [hfun]
    exact ((measurePreserving_shift c (0 : Space)).integrable_comp_emb
      (measurableEmbedding_addRight (c, (0 : Space)))).2 hLψ.right_integrable
  · exact e1.symm.trans (hLψ.eq.trans e2.symm)

/-! ## Integrability on the period slab -/

/-- A field that is `L²` on every integer window is `L²` on the period slab `(0, P] × ℝ³`,
which is covered by the finitely many windows with centres `0, …, ⌈P⌉`. -/
theorem i20_memLp_periodSlab {P : ℝ} {L : ℝ → SpatialField}
    (hLm : AEStronglyMeasurable (fun z : SpaceTime => L z.1 z.2) volume)
    (hLwin : ∀ n : ℤ, MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (windowSlab n 1))) :
    MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (periodSlab P)) := by
  refine (memLp_two_iff_integrable_sq_norm hLm.restrict).2 ?_
  have hcov : periodSlab P ⊆ ⋃ n ∈ Finset.Icc (0 : ℤ) ⌈P⌉, windowSlab (n : ℝ) 1 := by
    intro z hz
    have hz' : z.1 ∈ Ioc (0 : ℝ) P ∧ z.2 ∈ (univ : Set Space) := hz
    have h0 : (0 : ℤ) ≤ ⌊z.1⌋ := Int.floor_nonneg.2 hz'.1.1.le
    have h1 : ⌊z.1⌋ ≤ ⌈P⌉ := (Int.floor_mono hz'.1.2).trans (Int.floor_le_ceil P)
    exact Set.mem_iUnion₂.2 ⟨⌊z.1⌋, Finset.mem_Icc.2 ⟨h0, h1⟩, i20_floor_mem_windowSlab z⟩
  have hint : IntegrableOn (fun z : SpaceTime => ‖L z.1 z.2‖ ^ 2)
      (⋃ n ∈ Finset.Icc (0 : ℤ) ⌈P⌉, windowSlab (n : ℝ) 1) volume :=
    integrableOn_finset_iUnion.2 fun n _ =>
      (memLp_two_iff_integrable_sq_norm hLm.restrict).1 (hLwin n)
  exact hint.mono_set hcov

/-! ## The periodic selection -/

/-- Step G2b (`PeriodicSelection`, `WindowSteps.lean`): the periodization of a locally `L²`
weak Laplacian of a `P`-periodic `𝒴₂` field is a `𝒴₂` weak Laplacian. -/
theorem periodicSelection : PeriodicSelection := by
  intro P w L hP hw hLm hLwin hLweak
  -- `L` is a.e. invariant under each translate by `nP`, by uniqueness on `ℝ × ℝ³`
  have hper : ∀ n : ℤ, ∀ᵐ z : SpaceTime ∂volume, L (z.1 + (n : ℝ) * P) z.2 = L z.1 z.2 := by
    intro n
    have hwn : ∀ t, w (t + (n : ℝ) * P) = w t := fun t => hw.periodic.int_mul n t
    have hsh := i20_shift_laplacianPairing w L ((n : ℝ) * P) hwn hLweak
    have hU := weakLaplacianUnique w (fun t => L (t + (n : ℝ) * P)) L univ isOpen_univ
      (locallyIntegrableOn_univ.2 (i20_locallyIntegrable_shift ((n : ℝ) * P) hLwin))
      (locallyIntegrableOn_univ.2 (i20_locallyIntegrable_windows hLwin))
      (fun ψ hψ _ => hsh ψ hψ) (fun ψ hψ _ => hLweak ψ hψ)
    rw [Measure.restrict_univ] at hU
    exact hU
  have hall : ∀ᵐ z : SpaceTime ∂volume, ∀ n : ℤ, L (z.1 + (n : ℝ) * P) z.2 = L z.1 z.2 :=
    ae_all_iff.2 hper
  -- the periodization agrees with `L` almost everywhere
  have hpt : ∀ᵐ z : SpaceTime ∂volume, periodize hP L z.1 z.2 = L z.1 z.2 := by
    filter_upwards [hall] with z hz
    have key : toIocMod hP 0 z.1 = z.1 + ((-(toIocDiv hP 0 z.1) : ℤ) : ℝ) * P := by
      simp only [toIocMod, zsmul_eq_mul]
      push_cast
      ring
    show L (toIocMod hP 0 z.1) z.2 = L z.1 z.2
    rw [key]
    exact hz _
  refine ⟨periodize hP L, ⟨periodize_periodic L, aestronglyMeasurable_periodize hLm,
    memLp_periodize (i20_memLp_periodSlab (P := P) hLm hLwin)⟩, ?_⟩
  intro ψ hψ
  have hLψ := hLweak ψ hψ
  have hpt' : pairTerm (periodize hP L) ψ =ᵐ[volume] pairTerm L ψ := by
    filter_upwards [hpt] with z hz
    show inner ℝ (periodize hP L z.1 z.2) (ψ z) = inner ℝ (L z.1 z.2) (ψ z)
    rw [hz]
  unfold laplacianPairing at hLψ ⊢
  exact ⟨hLψ.left_integrable, hLψ.right_integrable.congr hpt'.symm,
    hLψ.eq.trans (integral_congr_ae hpt'.symm)⟩

end UnforcedLeray.Short.Interface
