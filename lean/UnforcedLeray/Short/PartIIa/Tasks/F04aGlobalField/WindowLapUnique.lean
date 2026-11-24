import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1

/-!
# Part II-a, task `PartII-a:F04/1/4`: uniqueness of the window Laplacian on an interval

Proves the Prop `WindowLapUnique` (Sub D of `Sub/PartIIa_F04_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 1451-1480.

Route: for a smooth compactly supported real `g` supported in the open strip `U = (a,b) × ℝ³`
and a fixed component `c`, the field `ψ = g • e_c` is an admissible test function for both
window identities. The `W`-terms coincide, so `∫ g (Λ_c - Λ'_c) = 0`. The fundamental lemma
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` then gives `Λ_c = Λ'_c` a.e. on `U`, for each
`c`, and the three components are combined.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIa

theorem windowLapUnique : UnforcedLeray.Short.PartIIa.WindowLapUnique := by
  intro ν τ₀ τ₁ a b W Λ Λ' h0a hb0 h1a hb1 hΛ hΛ' hLI hLI'
  have hUopen : IsOpen (Ioo a b ×ˢ (univ : Set Space)) := isOpen_Ioo.prod isOpen_univ
  have hsub0 : Ioo a b ×ˢ (univ : Set Space) ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    Set.prod_mono (Ioo_subset_Ioo h0a hb0) subset_rfl
  have hsub1 : Ioo a b ×ˢ (univ : Set Space) ⊆ Ioo (τ₁ - 1) (τ₁ + 1) ×ˢ (univ : Set Space) :=
    Set.prod_mono (Ioo_subset_Ioo h1a hb1) subset_rfl
  -- scalar test identity, one component at a time
  have hcomp : ∀ (c : Fin 3) (g : ℝ × Space → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b ×ˢ (univ : Set Space) → ∫ x, g x • (Λ x c - Λ' x c) = 0 := by
    intro c g hg hgc hgU
    obtain ⟨v, hv⟩ : ∃ v : CVec3, v = EuclideanSpace.single c 1 := ⟨_, rfl⟩
    have hψc : ContDiff ℝ ∞ (fun x : ℝ × Space => g x • v) := hg.smul contDiff_const
    have hψcs : HasCompactSupport (fun x : ℝ × Space => g x • v) := hgc.smul_right
    have hψsupp : tsupport (fun x : ℝ × Space => g x • v) ⊆
        Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
      (tsupport_smul_subset_left g (fun _ : ℝ × Space => v)).trans (hgU.trans hsub0)
    have hψsupp' : tsupport (fun x : ℝ × Space => g x • v) ⊆
        Ioo (τ₁ - 1) (τ₁ + 1) ×ˢ (univ : Set Space) :=
      (tsupport_smul_subset_left g (fun _ : ℝ × Space => v)).trans (hgU.trans hsub1)
    obtain ⟨_, hΛ1, heq1⟩ := hΛ (fun x => g x • v) hψc hψcs hψsupp
    obtain ⟨_, hΛ1', heq2⟩ := hΛ' (fun x => g x • v) hψc hψcs hψsupp'
    have hpt : ∀ x, g x • (Λ x c - Λ' x c) = dotL (Λ x) (g x • v) - dotL (Λ' x) (g x • v) := by
      intro x
      simp [hv, dotL_apply, EuclideanSpace.single_apply, Complex.real_smul, mul_sub]
    have hint : ∫ x, g x • (Λ x c - Λ' x c)
        = (∫ x, dotL (Λ x) (g x • v)) - ∫ x, dotL (Λ' x) (g x • v) := by
      rw [← integral_sub hΛ1 hΛ1']
      exact integral_congr_ae (Eventually.of_forall hpt)
    rw [hint]
    exact sub_eq_zero.2 (heq1.symm.trans heq2)
  -- local integrability of the components on the strip
  have hLIc : ∀ c : Fin 3, LocallyIntegrableOn (fun x => Λ x c - Λ' x c)
      (Ioo a b ×ˢ (univ : Set Space)) := by
    intro c
    rw [locallyIntegrableOn_iff hUopen.isLocallyClosed]
    intro k hk hkc
    have h1 : IntegrableOn Λ k := hLI.integrableOn_compact_subset hk hkc
    have h2 : IntegrableOn Λ' k := hLI'.integrableOn_compact_subset hk hkc
    have h1c : IntegrableOn (fun x => Λ x c) k :=
      ContinuousLinearMap.integrable_comp (EuclideanSpace.proj c : CVec3 →L[ℂ] ℂ) h1
    have h2c : IntegrableOn (fun x => Λ' x c) k :=
      ContinuousLinearMap.integrable_comp (EuclideanSpace.proj c : CVec3 →L[ℂ] ℂ) h2
    exact h1c.sub h2c
  -- the fundamental lemma, for each component
  have hae : ∀ c : Fin 3, ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      x ∈ Ioo a b ×ˢ (univ : Set Space) → Λ x c - Λ' x c = 0 := fun c =>
    hUopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hLIc c)
      (fun g hg hgc hgU => hcomp c g hg hgc hgU)
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ c : Fin 3,
      x ∈ Ioo a b ×ˢ (univ : Set Space) → Λ x c - Λ' x c = 0 :=
    ae_all_iff.2 hae
  show ∀ᵐ x ∂(volume.restrict (Ioo a b ×ˢ (univ : Set Space))), Λ x = Λ' x
  refine (ae_restrict_iff' hUopen.measurableSet).2 ?_
  filter_upwards [hall] with x hx hxU
  ext c
  exact sub_eq_zero.1 (hx c hxU)
