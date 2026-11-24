import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7

/-!
# `EnergyNullModification` (decomposition of `PartIII-b:C/flatset/col/7`, task 2)

Source of record `the November 2 reference manuscript` 3426-3430.  Model:
`IIIa.causalNullModification` (`Short/PartIII-a/T18_FreeCausal/Existence/NullModification.lean`).
Let `N` be a measurable null set of ages containing the bad ages of `divFreeAE`, `weakGradAE`;
redefine `(b, G) := 0` on `{p | p.1 ∈ N}`.  The zero slices are divergence free with weak gradient
`0`; the set `{p | p.1 ∈ N}` is null for Lebesgue measure and for `ageμ c (-3/2)`, so the new `b`
is a.e. equal to the old one and all `lintegral` clauses are unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (HasWeakCellDerivC)

/-- Keep `f` off `{p | p.1 ∈ N}` and put `0` on it. -/
def enmKeep (N : Set ℝ) (f : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  Set.indicator ((Prod.fst ⁻¹' N)ᶜ) f

theorem enmKeep_of_mem {N : Set ℝ} (f : ℝ × (ℝ × ℝ) → ℂ) {p : ℝ × (ℝ × ℝ)}
    (h : p ∈ (Prod.fst ⁻¹' N)ᶜ) : enmKeep N f p = f p :=
  Set.indicator_of_mem h f

theorem enmKeep_of_null {N : Set ℝ} (f : ℝ × (ℝ × ℝ) → ℂ) {p : ℝ × (ℝ × ℝ)}
    (h : p ∈ Prod.fst ⁻¹' N) : enmKeep N f p = 0 :=
  Set.indicator_of_notMem (show p ∉ (Prod.fst ⁻¹' N)ᶜ from not_not.2 h) f

theorem enm_measurable {N : Set ℝ} (hN : MeasurableSet N) {f : ℝ × (ℝ × ℝ) → ℂ}
    (hf : Measurable f) : Measurable (enmKeep N f) :=
  hf.indicator (measurable_fst hN).compl

/-- The set `{p | p.1 ∈ N}` is Lebesgue-null when `N` is null. -/
theorem enm_volume_null {N : Set ℝ} (hN0 : (volume : Measure ℝ) N = 0) :
    (volume : Measure (ℝ × (ℝ × ℝ))) (Prod.fst ⁻¹' N) = 0 := by
  rw [← Set.prod_univ, Measure.volume_eq_prod, Measure.prod_prod, hN0, zero_mul]

/-- The set `{p | p.1 ∈ N}` is null for the age measure when `N` is measurable and Lebesgue-null. -/
theorem enm_age_null (c a : ℝ) {N : Set ℝ} (hN : MeasurableSet N)
    (hN0 : (volume : Measure ℝ) N = 0) :
    ageμ c a (Prod.fst ⁻¹' N) = 0 := by
  rw [← Set.prod_univ]
  unfold ageμ
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  rw [Measure.prod_prod]
  have h1 : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) N = 0 := by
    rw [Measure.restrict_apply hN]
    exact measure_mono_null Set.inter_subset_left hN0
  have h2 : (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a)) N = 0 :=
    withDensity_absolutelyContinuous _ _ h1
  rw [h2, zero_mul]

/-- Off a `ρ`-null set `{p | p.1 ∈ N}`, the redefinition is the identity (as functions). -/
theorem enm_ae_b {N : Set ℝ} {ρ : Measure (ℝ × (ℝ × ℝ))}
    (h : ρ (Prod.fst ⁻¹' N) = 0) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    ∀ᵐ p ∂ρ, (fun i => enmKeep N (fun q => b q i) p) = b p := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 h] with p hp
  funext i
  exact enmKeep_of_mem _ hp

/-- Off a `ρ`-null set, the redefinition of `G` is the identity. -/
theorem enm_ae_G {N : Set ℝ} {ρ : Measure (ℝ × (ℝ × ℝ))}
    (h : ρ (Prod.fst ⁻¹' N) = 0) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    ∀ᵐ p ∂ρ, (fun i j => enmKeep N (fun q => G q i j) p) = G p := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 h] with p hp
  funext i j
  exact enmKeep_of_mem _ hp

/-- The zero pair satisfies the weak gradient clause. -/
theorem enm_hasWeak_zero (c : ℝ) (j : Fin 2) :
    HasWeakCellDerivC c j (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun ψ _ => ⟨?_, ?_⟩, fun ψ _ => ?_⟩ <;> simp

/-- **Null-set redefinition of the energy class** (source 3426-3430; see `EnergyNullModification`
in `Sub/PartIII-b_C_flatset_col_7.lean`). -/
theorem energyNullModification : EnergyNullModification := by
  intro c hc b G hE
  -- the ages where the two a.e. clauses may fail lie in a measurable null set `N`
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s →
      (∀ ψ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
      ∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j) := by
    filter_upwards [hE.divFreeAE, hE.weakGradAE] with s h1 h2 hs
    exact ⟨h1 hs, h2 hs⟩
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 hae)
  have hgood : ∀ s : ℝ, s ∉ N → 0 < s →
      (∀ ψ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0) ∧
      ∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j) := by
    intro s hsN hs
    by_contra hcon
    exact hsN (hsub (fun hq => hcon (hq hs)))
  have hZv : (volume : Measure (ℝ × (ℝ × ℝ))) (Prod.fst ⁻¹' N) = 0 := enm_volume_null hN0
  have hZa : ageμ c (-3 / 2) (Prod.fst ⁻¹' N) = 0 := enm_age_null c (-3 / 2) hNmeas hN0
  refine ⟨fun p i => enmKeep N (fun q => b q i) p, fun p i j => enmKeep N (fun q => G q i j) p,
    ?_, ?_⟩
  · -- a.e. equality under the age measure
    exact enm_ae_b hZa b
  refine
    { measurable := fun i => enm_measurable hNmeas (hE.measurable i)
      gradMeasurable := fun i j => enm_measurable hNmeas (hE.gradMeasurable i j)
      energyLoc := ?_
      zeroEntrance := ?_
      divFree := ?_
      weakGrad := ?_ }
  · -- energyLoc: the integrand agrees off `{p | p.1 ∈ N}`
    intro s₁ s₂ h₁ h₂
    refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae ?_) (hE.energyLoc s₁ s₂ h₁ h₂)
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Icc s₁ s₂ ×ˢ B0579.cell c)
        (enm_ae_b hZv b),
      MeasureTheory.ae_restrict_of_ae (s := Icc s₁ s₂ ×ˢ B0579.cell c) (enm_ae_G hZv G)]
      with p hbp hGp
    simp only [hbp, hGp]
  · -- zeroEntrance: the same redefinition under `ageμ c (-3/2)` restricted to `(0, δ) × ℝ × ℝ`
    obtain ⟨δ, hδ, hfin⟩ := hE.zeroEntrance
    refine ⟨δ, hδ, lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae ?_) hfin⟩
    filter_upwards [MeasureTheory.ae_restrict_of_ae (s := Ioo 0 δ ×ˢ univ) (enm_ae_b hZa b)]
      with p hbp
    simp only [hbp]
  · -- divFree: zero slices are divergence free; off `N` the old slice is good
    intro s hs ψ hψ
    by_cases hsN : s ∈ N
    · have h0 : ∀ x : ℝ × ℝ, ∀ i, enmKeep N (fun q => b q i) (s, x) = 0 :=
        fun x i => enmKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      simp [h0]
    · have hgs := hgood s hsN hs
      have h1 : ∀ x : ℝ × ℝ, ∀ i, enmKeep N (fun q => b q i) (s, x) = b (s, x) i :=
        fun x i => enmKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      simp only [h1]
      exact hgs.1 ψ hψ
  · -- weakGrad: zero slices have weak gradient `0`; off `N` the old slice is good
    intro s hs i j
    by_cases hsN : s ∈ N
    · have h0 : ∀ x : ℝ × ℝ, enmKeep N (fun q => b q i) (s, x) = 0 :=
        fun x => enmKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      have h0G : ∀ x : ℝ × ℝ, enmKeep N (fun q => G q i j) (s, x) = 0 :=
        fun x => enmKeep_of_null _ (show (s, x) ∈ Prod.fst ⁻¹' N from hsN)
      simp only [h0, h0G]
      exact enm_hasWeak_zero c j
    · have hw := (hgood s hsN hs).2 i j
      have h1 : ∀ x : ℝ × ℝ, enmKeep N (fun q => b q i) (s, x) = b (s, x) i :=
        fun x => enmKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      have h2 : ∀ x : ℝ × ℝ, enmKeep N (fun q => G q i j) (s, x) = G (s, x) i j :=
        fun x => enmKeep_of_mem _ (show (s, x) ∈ (Prod.fst ⁻¹' N)ᶜ from hsN)
      simp only [h1, h2]
      exact hw

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
