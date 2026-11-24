import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1

/-!
# Part II-a, task `PartII-a:F04/1/7`: periodicity of the global window Laplacian

Proves `windowLapPeriodic_of (hUn : WindowLapUnique) : WindowLapPeriodic` (Sub G of
`Sub/PartIIa_F04_1.lean`). The uniqueness Sub D enters only as the hypothesis `hUn`.

Strategy. `Λ' (p) = Λ (p.1 + P, p.2)` is a window Laplacian of `W` at every centre `s`, by the
translation of test functions and the a.e. `P`-periodicity of `W`. On the windows
`I_s = (s - 1/4, s + 1/4) × ℝ³` both `Λ` and `Λ'` are locally integrable (each lies in one integer
window), so `hUn` gives `Λ = Λ'` a.e. on each `I_s`. Countably many rational `s` cover `ℝ × ℝ³`
up to a null set, and `Measure.ae_prod_iff_ae_ae` gives the slice statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.PhaseSpace
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem measurableSet_winSet'' (τ : ℝ) : MeasurableSet (winSet τ) :=
  measurableSet_Ioo.prod MeasurableSet.univ

theorem sub_neg_shift (P : ℝ) (p : ℝ × Space) : p - (-P, (0 : Space)) = (p.1 + P, p.2) :=
  Prod.ext (by simp [sub_neg_eq_add]) (by simp)

theorem dy_comp_add (Ψ : ℝ × Space → CVec3) (a : ℝ × Space) (j : Fin 3) :
    dy j (fun q => Ψ (q + a)) = fun p => dy j Ψ (p + a) := by
  funext p
  unfold dy
  rw [fderiv_comp_add_right]

theorem lapT_comp_add (Ψ : ℝ × Space → CVec3) (a : ℝ × Space) :
    lapT (fun q => Ψ (q + a)) = fun p => lapT Ψ (p + a) := by
  funext p
  show ∑ j : Fin 3, dy j (dy j (fun q => Ψ (q + a))) p =
    ∑ j : Fin 3, dy j (dy j Ψ) (p + a)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dy_comp_add Ψ a j, dy_comp_add (dy j Ψ) a j]

/-- Translation in the window: a window Laplacian of `W` at centre `c + P`, translated by `P` in
`τ`, is a window Laplacian of `W` at centre `c`, when `W` is a.e. `P`-periodic. -/
theorem isWindowLaplacian_shift (ν P c : ℝ) {W Λ : ℝ × Space → CVec3}
    (hW : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), W (p.1 + P, p.2) = W p)
    (hΛ : IsWindowLaplacian ν (c + P) W Λ) :
    IsWindowLaplacian ν c W (fun p => Λ (p.1 + P, p.2)) := by
  unfold IsWindowLaplacian at hΛ ⊢
  intro ψ hψ hψc hψs
  have hφ : ContDiff ℝ ∞ (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) :=
    hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) :=
    hψc.comp_homeomorph (Homeomorph.addRight (-P, (0 : Space)))
  have hφs : tsupport (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) ⊆ winSet (c + P) := by
    have h1 : tsupport (fun q : ℝ × Space => ψ (q + (-P, (0 : Space)))) ⊆
        (fun q : ℝ × Space => q + (-P, (0 : Space))) ⁻¹' tsupport ψ :=
      closure_minimal
        (fun q hq => subset_tsupport ψ (show q + (-P, (0 : Space)) ∈ Function.support ψ from hq))
        ((isClosed_tsupport ψ).preimage (continuous_id.add continuous_const))
    intro q hq
    obtain ⟨⟨h3, h4⟩, -⟩ := hψs (h1 hq)
    have h3' : c - 1 < q.1 + -P := h3
    have h4' : q.1 + -P < c + 1 := h4
    exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  obtain ⟨H1, H2, H3⟩ := hΛ (fun q => ψ (q + (-P, (0 : Space)))) hφ hφc hφs
  have hLφ := lapT_comp_add ψ (-P, (0 : Space))
  have hadd : ∀ p : ℝ × Space, (p.1 + P, p.2) + (-P, (0 : Space)) = p :=
    fun p => Prod.ext (by simp) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · have h := H1.comp_sub_right (-P, (0 : Space))
    refine h.congr (by
      filter_upwards [hW] with p hp
      simp only [hLφ, sub_neg_shift, hadd, hp])
  · have h := H2.comp_sub_right (-P, (0 : Space))
    refine h.congr (ae_of_all _ (fun p => ?_))
    show dotL (Λ (p - (-P, (0 : Space)))) (ψ (p - (-P, (0 : Space)) + (-P, (0 : Space)))) =
      dotL (Λ (p.1 + P, p.2)) (ψ p)
    rw [sub_add_cancel, sub_neg_shift]
  · have e1 : ∫ p, dotL (W p) (ν • lapT ψ p) = ∫ p, dotL (W (p - (-P, (0 : Space))))
        (ν • lapT ψ p) := by
      refine integral_congr_ae ?_
      filter_upwards [hW] with p hp
      rw [sub_neg_shift, hp]
    have e2 : ∫ p, dotL (W (p - (-P, (0 : Space)))) (ν • lapT ψ p) =
        ∫ q, dotL (W q) (ν • lapT (fun q => ψ (q + (-P, (0 : Space)))) q) := by
      rw [← integral_sub_right_eq_self
        (fun q => dotL (W q) (ν • lapT (fun q => ψ (q + (-P, (0 : Space)))) q))
        (-P, (0 : Space))]
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      simp only [hLφ, sub_add_cancel]
    have e4 : ∫ q, dotL (Λ q) (ψ (q + (-P, (0 : Space)))) =
        ∫ p, dotL (Λ (p.1 + P, p.2)) (ψ p) := by
      rw [← integral_sub_right_eq_self (fun q => dotL (Λ q) (ψ (q + (-P, (0 : Space)))))
        (-P, (0 : Space))]
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      show dotL (Λ (p - (-P, (0 : Space)))) (ψ (p - (-P, (0 : Space)) + (-P, (0 : Space)))) =
        dotL (Λ (p.1 + P, p.2)) (ψ p)
      rw [sub_add_cancel, sub_neg_shift]
    exact e1.trans (e2.trans (H3.trans e4))

theorem locallyIntegrableOn_shift (P : ℝ) {Λ : ℝ × Space → CVec3} {S T : Set (ℝ × Space)}
    (hS : IsOpen S) (hST : (fun p : ℝ × Space => (p.1 + P, p.2)) '' S ⊆ T)
    (hT : LocallyIntegrableOn Λ T (volume : Measure (ℝ × Space))) :
    LocallyIntegrableOn (fun p : ℝ × Space => Λ (p.1 + P, p.2)) S
      (volume : Measure (ℝ × Space)) := by
  rw [locallyIntegrableOn_iff hS.isLocallyClosed]
  intro K hKS hKc
  have hmp : MeasurePreserving (fun p : ℝ × Space => (p.1 + P, p.2))
      (volume : Measure (ℝ × Space)) (volume : Measure (ℝ × Space)) := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right (volume : Measure ℝ) P).prod
      (MeasurePreserving.id (volume : Measure Space))
  have hme : MeasurableEmbedding (fun p : ℝ × Space => (p.1 + P, p.2)) :=
    ((Homeomorph.addRight P).prodCongr (Homeomorph.refl Space)).measurableEmbedding
  have hinj : Function.Injective (fun p : ℝ × Space => (p.1 + P, p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.1) h.2
  have hK' : IsCompact ((fun p : ℝ × Space => (p.1 + P, p.2)) '' K) :=
    hKc.image ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have hsub : (fun p : ℝ × Space => (p.1 + P, p.2)) '' K ⊆ T :=
    (Set.image_mono hKS).trans hST
  have hI : IntegrableOn Λ ((fun p : ℝ × Space => (p.1 + P, p.2)) '' K)
      (volume : Measure (ℝ × Space)) :=
    hT.integrableOn_compact_subset hsub hK'
  have key := hmp.integrableOn_comp_preimage hme (f := Λ)
    (s := (fun p : ℝ × Space => (p.1 + P, p.2)) '' K)
  rw [hinj.preimage_image] at key
  exact key.2 hI

/-- The window `(s - 1/4, s + 1/4)` lies in the integer window of `⌊s + 1/2⌋`. -/
theorem interval_sub_winSet (x : ℝ) :
    Ioo (x - 1 / 4) (x + 1 / 4) ⊆
      Ioo (((⌊x + 1 / 2⌋ : ℤ) : ℝ) - 1) (((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1) := by
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  have h3 := Int.floor_le (x + 1 / 2)
  have h4 := Int.lt_floor_add_one (x + 1 / 2)
  exact ⟨by linarith, by linarith⟩

theorem windowLapPeriodic_of (hUn : WindowLapUnique) : WindowLapPeriodic := by
  unfold WindowLapPeriodic
  intro P ν _ W Λ hWm hΛm hper hwin hloc
  have hm1 : Measurable (fun p : ℝ × Space => W (p.1 + P, p.2)) :=
    hWm.measurable.comp ((measurable_fst.add_const P).prodMk measurable_snd)
  have hmeasW : MeasurableSet {p : ℝ × Space | W (p.1 + P, p.2) = W p} :=
    measurableSet_eq_fun hm1 hWm.measurable
  have hWp : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), W (p.1 + P, p.2) = W p := by
    rw [Measure.volume_eq_prod]
    exact (Measure.ae_prod_iff_ae_ae hmeasW).2 (by
      filter_upwards [hper] with τ hτ
      exact hτ)
  have hΛ' : ∀ s : ℝ, IsWindowLaplacian ν s W (fun p => Λ (p.1 + P, p.2)) := fun s =>
    isWindowLaplacian_shift ν P s hWp (hwin (s + P))
  have hwin_ae : ∀ s : ℝ, ∀ᵐ p ∂(volume : Measure (ℝ × Space)),
      p ∈ Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space) → Λ p = Λ (p.1 + P, p.2) := by
    intro s
    have hLoc1 : LocallyIntegrableOn Λ (Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space))
        (volume : Measure (ℝ × Space)) :=
      (hloc ⌊s + 1 / 2⌋).mono_set (fun p hp => ⟨interval_sub_winSet s hp.1, hp.2⟩)
    have hST : (fun p : ℝ × Space => (p.1 + P, p.2)) ''
        (Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space)) ⊆
        winSet ((⌊s + P + 1 / 2⌋ : ℤ) : ℝ) := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨⟨hp1, hp2⟩, -⟩ := hp
      exact ⟨interval_sub_winSet (s + P)
        (show p.1 + P ∈ Ioo (s + P - 1 / 4) (s + P + 1 / 4) from ⟨by linarith, by linarith⟩),
        mem_univ _⟩
    have hLoc2 : LocallyIntegrableOn (fun p : ℝ × Space => Λ (p.1 + P, p.2))
        (Ioo (s - 1 / 4) (s + 1 / 4) ×ˢ (univ : Set Space)) (volume : Measure (ℝ × Space)) :=
      locallyIntegrableOn_shift P (isOpen_Ioo.prod isOpen_univ) hST (hloc (⌊s + P + 1 / 2⌋))
    have hUs := hUn ν s s (s - 1 / 4) (s + 1 / 4) W Λ (fun p => Λ (p.1 + P, p.2))
      (by linarith) (by linarith) (by linarith) (by linarith) (hwin s) (hΛ' s) hLoc1 hLoc2
    exact (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).1 hUs
  have hall : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), ∀ q : ℚ,
      p ∈ Ioo ((q : ℝ) - 1 / 4) ((q : ℝ) + 1 / 4) ×ˢ (univ : Set Space) →
        Λ p = Λ (p.1 + P, p.2) := by
    rw [ae_all_iff]
    intro q
    exact hwin_ae (q : ℝ)
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), Λ (p.1 + P, p.2) = Λ p := by
    filter_upwards [hall] with p hp
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show p.1 - 1 / 8 < p.1 + 1 / 8 by linarith)
    have hmem : p ∈ Ioo ((q : ℝ) - 1 / 4) ((q : ℝ) + 1 / 4) ×ˢ (univ : Set Space) :=
      ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
    exact (hp q hmem).symm
  have hmeasΛ : MeasurableSet {p : ℝ × Space | Λ (p.1 + P, p.2) = Λ p} :=
    measurableSet_eq_fun
      (hΛm.measurable.comp ((measurable_fst.add_const P).prodMk measurable_snd)) hΛm.measurable
  rw [Measure.volume_eq_prod] at hae
  filter_upwards [(Measure.ae_prod_iff_ae_ae hmeasΛ).1 hae] with τ hτ
  exact hτ

end UnforcedLeray.Short.PartIIa
