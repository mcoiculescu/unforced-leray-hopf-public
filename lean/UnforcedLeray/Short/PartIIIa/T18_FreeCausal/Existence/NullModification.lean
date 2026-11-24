import UnforcedLeray.Short.PartIIIa.Sub.T18_2

/-!
# Part III-a, task `T18_FreeCausal/Existence/NullModification`: the null-set redefinition

Proves `CausalNullModification` (`Sub/T18_2.lean`). Given a causal energy solution `(b, G)` in the
a.e.-in-age class `IsCausalEnergySolutionAE`, the ages `s` at which `divFree` or `weakGrad` may
fail lie in a measurable null set `N` (`exists_measurable_superset_of_null`). Redefining
`(b, G) := 0` on `{p | p.1 ∈ N}` gives a member of `IsCausalEnergySolution`: the zero slices are
divergence free with weak gradient `0`, and the redefinition changes no integral, because
`{p | p.1 ∈ N}` is null for Lebesgue measure and for `ageμ c a`.

Source of record: `the November 2 reference manuscript`, lines 3427-3440
(the zero-entrance construction, "start from zero at `s = δ`, let `δ ↓ 0`").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The redefinition and the good-age predicate -/

/-- Keep `f` off `{p | p.1 ∈ N}` and put `0` on it. -/
def causalNullKeep (N : Set ℝ) (f : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  Set.indicator ((Prod.fst ⁻¹' N)ᶜ) f

/-- The two clauses that the a.e. class asks for at age `s`: divergence freeness and the weak
gradient, both only when `s > 0`. -/
def causalNullGood (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (s : ℝ) : Prop :=
  0 < s → (∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
    ∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)

/-! ## Pointwise facts about `causalNullKeep` -/

theorem causalNullKeep_of_mem {N : Set ℝ} (f : ℝ × (ℝ × ℝ) → ℂ) {p : ℝ × (ℝ × ℝ)}
    (h : p ∈ (Prod.fst ⁻¹' N)ᶜ) : causalNullKeep N f p = f p :=
  Set.indicator_of_mem h f

theorem causalNullKeep_of_null {N : Set ℝ} (f : ℝ × (ℝ × ℝ) → ℂ) {p : ℝ × (ℝ × ℝ)}
    (h : p ∈ Prod.fst ⁻¹' N) : causalNullKeep N f p = 0 :=
  Set.indicator_of_notMem (show p ∉ (Prod.fst ⁻¹' N)ᶜ from not_not.2 h) f

theorem causalNull_measurable {N : Set ℝ} (hN : MeasurableSet N) {f : ℝ × (ℝ × ℝ) → ℂ}
    (hf : Measurable f) : Measurable (causalNullKeep N f) :=
  hf.indicator (measurable_fst hN).compl

/-! ## Null sets `{p | p.1 ∈ N}` -/

theorem causalNull_volume_null {N : Set ℝ} (hN0 : (volume : Measure ℝ) N = 0) :
    (volume : Measure (ℝ × (ℝ × ℝ))) (Prod.fst ⁻¹' N) = 0 := by
  rw [← Set.prod_univ, Measure.volume_eq_prod, Measure.prod_prod, hN0, zero_mul]

theorem causalNull_age_null (c a : ℝ) {N : Set ℝ} (hN : MeasurableSet N)
    (hN0 : (volume : Measure ℝ) N = 0) :
    ageμ c a (Prod.fst ⁻¹' N) = 0 := by
  rw [← Set.prod_univ]
  unfold ageμ
  have : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  rw [Measure.prod_prod]
  have h1 : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) N = 0 := by
    rw [Measure.restrict_apply hN]
    exact measure_mono_null Set.inter_subset_left hN0
  have h2 : (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a)) N = 0 :=
    withDensity_absolutelyContinuous _ _ h1
  rw [h2, zero_mul]

/-- Off a `ρ`-null set `{p | p.1 ∈ N}`, the redefinition is the identity (pointwise, for `b`). -/
theorem causalNull_ae_b {N : Set ℝ} {ρ : Measure (ℝ × (ℝ × ℝ))}
    (h : ρ (Prod.fst ⁻¹' N) = 0) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    ∀ᵐ p ∂ρ, ∀ i, causalNullKeep N (fun q => b q i) p = b p i := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 h] with p hp i
  exact causalNullKeep_of_mem (fun q => b q i) hp

/-- Off a `ρ`-null set `{p | p.1 ∈ N}`, the redefinition is the identity (pointwise, for `G`). -/
theorem causalNull_ae_G {N : Set ℝ} {ρ : Measure (ℝ × (ℝ × ℝ))}
    (h : ρ (Prod.fst ⁻¹' N) = 0) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    ∀ᵐ p ∂ρ, ∀ i j, causalNullKeep N (fun q => G q i j) p = G p i j := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 h] with p hp i j
  exact causalNullKeep_of_mem (fun q => G q i j) hp

/-- The flat integrand depends on `b` only through its values at `p`. -/
theorem causalNull_flat_congr (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) (h : ∀ i, b' p i = b p i) :
    flatIntegrand ν μ vel F b' Φ p = flatIntegrand ν μ vel F b Φ p := by
  unfold flatIntegrand
  simp only [h]

/-- The zero pair satisfies the weak gradient clause. -/
theorem causalNull_hasWeak_zero (c : ℝ) (j : Fin 2) :
    HasWeakCellDerivC c j (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun ψ _ => ⟨?_, ?_⟩, fun ψ _ => ?_⟩ <;> simp

/-! ## The null-set redefinition -/

/-- **Null-set redefinition** (`PartIII-a:T18/2/2`; SP 3427-3440). An a.e.-in-age causal
energy solution is, after redefining `(b, G) := 0` on a measurable null set of ages, a causal
energy solution in the class `IsCausalEnergySolution`. -/
theorem causalNullModification : CausalNullModification := by
  intro c ν μ vel _hc F b G hb
  -- the ages where the two a.e. clauses may fail lie in a measurable null set `N`
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), causalNullGood c b G s := by
    filter_upwards [hb.divFreeAE, hb.weakGradAE] with s h1 h2
    unfold causalNullGood
    exact fun hs => ⟨h1 hs, h2 hs⟩
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 hae)
  have hgood : ∀ s : ℝ, s ∉ N → causalNullGood c b G s := by
    intro s hsN
    by_contra hcon
    have hmem : s ∈ {a : ℝ | ¬ causalNullGood c b G a} := hcon
    exact hsN (hsub hmem)
  have hZv : (volume : Measure (ℝ × (ℝ × ℝ))) (Prod.fst ⁻¹' N) = 0 :=
    causalNull_volume_null hN0
  have hZa : ageμ c (-3 / 2) (Prod.fst ⁻¹' N) = 0 :=
    causalNull_age_null c (-3 / 2) hNmeas hN0
  refine ⟨fun p i => causalNullKeep N (fun q => b q i) p,
    fun p i j => causalNullKeep N (fun q => G q i j) p, ?_⟩
  refine
    { measurable := fun i => causalNull_measurable hNmeas (hb.measurable i)
      gradMeasurable := fun i j => causalNull_measurable hNmeas (hb.gradMeasurable i j)
      energyLoc := ?_
      zeroEntrance := ?_
      divFree := ?_
      weakGrad := ?_
      integrable := ?_
      weak := ?_ }
  · -- energyLoc: the lintegral is unchanged, the integrands agree off `{p | p.1 ∈ N}`
    intro s₁ s₂ h₁ h₂
    refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae ?_) (hb.energyLoc s₁ s₂ h₁ h₂)
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Icc s₁ s₂ ×ˢ B0579.cell c)
        (causalNull_ae_b hZv b),
      MeasureTheory.ae_restrict_of_ae (s := Icc s₁ s₂ ×ˢ B0579.cell c) (causalNull_ae_G hZv G)]
      with p hbp hGp
    simp only [hbp, hGp]
  · -- zeroEntrance: the same redefinition under `ageμ c (-3/2)` restricted to `(0, δ) × ℝ × ℝ`
    obtain ⟨δ, hδ, hfin⟩ := hb.zeroEntrance
    refine ⟨δ, hδ, lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae ?_) hfin⟩
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioo 0 δ ×ˢ univ)
      (causalNull_ae_b hZa b)] with p hbp
    simp only [hbp]
  · -- divFree: zero slices are divergence free; off `N` the old slice is good
    intro s hs ψ hψ
    by_cases hsN : s ∈ N
    · have h0 : ∀ x : ℝ × ℝ, ∀ i, causalNullKeep N (fun q => b q i) (s, x) = 0 :=
        fun x i => causalNullKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      simp [h0]
    · have hgs : causalNullGood c b G s := hgood s hsN
      unfold causalNullGood at hgs
      have hdiv := (hgs hs).1 ψ hψ
      have h1 : ∀ x : ℝ × ℝ, ∀ i, causalNullKeep N (fun q => b q i) (s, x) = b (s, x) i :=
        fun x i => causalNullKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      simp only [h1]
      exact hdiv
  · -- weakGrad: zero slices have weak gradient `0`; off `N` the old slice is good
    intro s hs i j
    by_cases hsN : s ∈ N
    · have h0 : ∀ x : ℝ × ℝ, causalNullKeep N (fun q => b q i) (s, x) = 0 :=
        fun x => causalNullKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      have h0G : ∀ x : ℝ × ℝ, causalNullKeep N (fun q => G q i j) (s, x) = 0 :=
        fun x => causalNullKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      simp only [h0, h0G]
      exact causalNull_hasWeak_zero c j
    · have hgs : causalNullGood c b G s := hgood s hsN
      unfold causalNullGood at hgs
      have hw := (hgs hs).2 i j
      have h1 : ∀ x : ℝ × ℝ, causalNullKeep N (fun q => b q i) (s, x) = b (s, x) i :=
        fun x => causalNullKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      have h2 : ∀ x : ℝ × ℝ, causalNullKeep N (fun q => G q i j) (s, x) = G (s, x) i j :=
        fun x => causalNullKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      simp only [h1, h2]
      exact hw
  · -- integrable: the flat integrand changes only on `{p | p.1 ∈ N}`
    intro Φ hΦ
    refine MeasureTheory.Integrable.congr (hb.integrable Φ hΦ) ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioi (0 : ℝ) ×ˢ B0579.cell c)
      (causalNull_ae_b hZv b)] with p hbp
    exact (causalNull_flat_congr ν μ vel F Φ b (fun p i => causalNullKeep N (fun q => b q i) p)
      p hbp).symm
  · -- weak: the same change, so the weak identity transfers
    intro Φ hΦ
    have hae' : (flatIntegrand ν μ vel F b Φ) =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)]
        (flatIntegrand ν μ vel F (fun p i => causalNullKeep N (fun q => b q i) p) Φ) := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioi (0 : ℝ) ×ˢ B0579.cell c)
        (causalNull_ae_b hZv b)] with p hbp
      exact (causalNull_flat_congr ν μ vel F Φ b (fun p i => causalNullKeep N (fun q => b q i) p)
        p hbp).symm
    exact (MeasureTheory.integral_congr_ae hae'.symm).trans (hb.weak Φ hΦ)

end UnforcedLeray.Short.IIIa
