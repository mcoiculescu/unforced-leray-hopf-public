import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2.DuhamelGradRep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_2

/-!
# `SFCEnergyG` from the Duhamel gradient formula, the slice heat bound and Minkowski
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/5`)

Source `the November 2 reference manuscript`
1684-1689, 3426-3430.  `∇b(s) = ∫₀^s (σ/s)^μ ∇e^{ν(s-σ)Δ}G(σ) dσ`; by Cauchy-Schwarz/Minkowski in
`L²(cell)`, `‖∇b(s)‖² ≤ (s/(μ+1))² sup_σ ‖∇ e^{ν(s-σ)Δ}G(σ)‖²`, and the heat contracts the
gradient.  The remaining analytic inputs are the five Props below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- A measurable representative of the flat-projected datum `sfcGp hc f'` (an `L²` class: the
a.e. class of a `HSpace` element has a measurable representative; e.g. `AEMeasurable.mk`). -/
def MeasRepP : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    ∃ Gm : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
      Measurable Gm ∧ Gm =ᵐ[UnforcedLeray.B0220.measureH c] sfcGp hc f'

/-- **Heat contracts the gradient, slice form** (source 3426-3430): for `σ < s`, a smooth bounded
`q`-periodic slice `Gs(σ,·)` (so `periodize c Gs (σ,·) = Gs(σ,·)`: `reduceIoc` is an integer shift,
`reduceIoc_shift` in `Sub/PartIII-b_C_flatset_col_7_1_1_2_4_2_1_L2/Slices.lean`, by `Int.induction_on`
as in `Sub/PartIII-b_C_flatset_col_7_1_1_2_4_2_4_1_of.lean`) whose cell gradient energy is `≤ C`,
the heat `e^{ν(s-σ)Δ}` of it has cell gradient energy `≤ C`: `SFCHeatGrad` applied to each
component (`f = fun y => Gs (σ,y) i`) and summed over `i`. -/
def SliceHeatP : Prop :=
  SFCHeatGrad → ∀ (c ν σ s C : ℝ) (hc : 0 < c) (Gs : UnforcedLeray.B0220.Profile →
      UnforcedLeray.B0223.MeridC), 0 < ν → σ < s →
    (∀ i, ContDiff ℝ ∞ fun y : ℝ × ℝ => (Gs (σ, y)) i) →
    (∀ q η, Gs (σ, (q + c, η)) = Gs (σ, (q, η))) →
    (∃ C' : ℝ, ∀ y : ℝ × ℝ, ‖Gs (σ, y)‖ ≤ C') →
    ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ
        (fun y : ℝ × ℝ => (Gs (σ, y)) i) x (B0579.dir j)) ^ 2) ≤ ENNReal.ofReal C →
    ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ (fun y : ℝ × ℝ =>
        (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) y) i) x (B0579.dir j)) ^ 2)
      ≤ ENNReal.ofReal C

/-- **Joint (a.e.) measurability of the heat-gradient integrand** (needed for Tonelli): for `Gm`
measurable, equal `measureH`-a.e. to `Gs`, whose slices are, for a.e. `σ ∈ (0,s]`, smooth, periodic
and bounded, the map `(σ,x) ↦ ∂_j (e^{ν(s-σ)Δ} periodize Gm(σ,·))_i (x)` is a.e.-measurable on
`(0,s] × ℝ²`.  (Sketch: for `σ < s` the heat is the Gaussian integral of the datum, jointly
measurable by parametric integration; `fderiv` of it is measurable as a limit of difference quotients,
`measurable_fderiv_with_param`-style, or via differentiation under the integral sign for the good
slices; replace `Gm` by `Gs` on the (measurable-superset-of-the-null) bad set of `σ`.)
The hypothesis `0 < ν` is needed: for `ν ≤ 0` the heat `e^{ν(s-σ)Δ}` is the identity, so the
integrand is the gradient of the merely measurable representative `Gm`, whose differentiability set
has no elementary measurability. -/
def GradIntegrandAEMeasP : Prop :=
  ∀ (c ν s : ℝ) (hc : 0 < c) (Gm Gs : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC),
    0 < ν → Measurable Gm → Gm =ᵐ[UnforcedLeray.B0220.measureH c] Gs →
    (∀ᵐ σ ∂(volume.restrict (Ioc 0 s)),
      (∀ i, ContDiff ℝ ∞ fun y : ℝ × ℝ => (Gs (σ, y)) i) ∧
      (∀ q η, Gs (σ, (q + c, η)) = Gs (σ, (q, η))) ∧
      (∃ C' : ℝ, ∀ y : ℝ × ℝ, ‖Gs (σ, y)‖ ≤ C')) →
    ∀ i j : Fin 2, AEMeasurable (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - p.1))
        (fun z => UnforcedLeray.B0220.periodize c Gm (p.1, z)) y) i) p.2 (B0579.dir j))
      (volume.restrict (Ioc 0 s ×ˢ (univ : Set (ℝ × ℝ))))

/-- **Weighted Minkowski / Cauchy-Schwarz in `L²(S)`** (source 3426-3430): for `s > 0`, `μ > -1`,
`G` a.e.-measurable in `(σ,x)` on `(0,s] × S` with `∫_S |G(σ)|² ≤ K` for a.e. `σ ∈ (0,s]`,
`∫_S |∫₀^s (σ/s)^μ G(σ,x) dσ|² dx ≤ (s/(μ+1))² K`.  (Pointwise `|∫ w G|² ≤ (∫ w)(∫ w |G|²)` for
`w = (σ/s)^μ ≥ 0`, `∫₀^s w = s/(μ+1)`; integrate in `x`, Tonelli; when `σ ↦ w G` is not integrable
the Bochner integral is `0`.) -/
def CellWeightedL2P : Prop :=
  ∀ (s μ K : ℝ) (G : ℝ → ℝ × ℝ → Fin 2 → Fin 2 → ℂ) (S : Set (ℝ × ℝ)),
    0 < s → -1 < μ → MeasurableSet S →
    AEMeasurable (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) (volume.restrict (Ioc 0 s ×ˢ S)) →
    (∀ᵐ σ ∂(volume.restrict (Ioc 0 s)),
      ∫⁻ x in S, ENNReal.ofReal (tnorm2 (G σ x) ^ 2) ≤ ENNReal.ofReal K) →
    ∫⁻ x in S, ENNReal.ofReal (tnorm2 (fun i j =>
      ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * G σ x i j) ^ 2)
      ≤ ENNReal.ofReal ((s / (μ + 1)) ^ 2 * K)

theorem tnorm2_sq_measurable (T : Chart → Fin 2 → Fin 2 → ℂ) (hT : ∀ i j, Measurable fun p => T p i j) :
    Measurable fun p : Chart => ENNReal.ofReal (tnorm2 (T p) ^ 2) := by
  unfold tnorm2
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.pow_const ?_ 2
  refine Measurable.sqrt ?_
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  exact (hT i j).norm.pow_const 2

/-- **Assembly (Minkowski)**: `SFCEnergyG` from `SFCDuhamel`, `SFCHeatGrad`, `SFCProjGrad`,
`SFCDuhamelGrad` and the five analytic Props above. -/
theorem sfcEnergyG_of_sub (hD : SFCDuhamel) (hH : SFCHeatGrad) (hP : SFCProjGrad)
    (hG : SFCDuhamelGrad) (h1 : MeasRepP) (h3 : SliceHeatP) (h4 : GradIntegrandAEMeasP)
    (h5 : CellWeightedL2P) : SFCEnergyG := by
  intro c ν μ hc R0 g hctx b hb hae s₁ s₂ hs1 h12
  have hμ : -1 < μ := by have := hctx.2.1; linarith
  have hν : 0 < ν := hctx.1
  obtain ⟨f', hlift, hbD⟩ := hD c ν μ hc R0 g hctx b hb hae
  obtain ⟨Gs, hGsae, -, hsl⟩ := hP c ν μ hc R0 g hctx f' hlift
  obtain ⟨Gm, hGm, hGmae⟩ := h1 c hc f'
  have hGmGs : Gm =ᵐ[UnforcedLeray.B0220.measureH c] Gs := hGmae.trans hGsae.symm
  have hRep := sfcDuhamelGradRep_of_grad hG c ν μ hc R0 g hctx b hb hae f' hlift hbD Gm hGmae
  obtain ⟨C, hC⟩ := hsl s₂ (by linarith)
  set K : ℝ := max C 0 with hK
  have key : ∀ s ∈ Icc s₁ s₂, ∫⁻ x in B0579.cell c,
      ENNReal.ofReal (tnorm2 (fun i j => cellGrad b (s, x) i j) ^ 2)
        ≤ ENNReal.ofReal ((s / (μ + 1)) ^ 2 * K) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hs1 hs.1
    have hsub : Ioc 0 s ⊆ Ioc 0 s₂ := Ioc_subset_Ioc_right hs.2
    have hC' := ae_restrict_of_ae_restrict_of_subset hsub hC
    have hS' : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), 0 < σ → ∀ᵐ z : ℝ × ℝ,
        UnforcedLeray.B0220.periodize c Gm (σ, z) = UnforcedLeray.B0220.periodize c Gs (σ, z) :=
      ae_restrict_of_ae (ae_slices_of_measureH hc hGmGs)
    have hne : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), σ ≠ s :=
      ae_restrict_of_ae ((Set.countable_singleton s).ae_notMem volume)
    set G : ℝ → ℝ × ℝ → Fin 2 → Fin 2 → ℂ := fun σ x i j =>
      fderiv ℝ (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => UnforcedLeray.B0220.periodize c Gm (σ, z)) y) i) x (B0579.dir j) with hGdef
    have hbound : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)),
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G σ x) ^ 2) ≤ ENNReal.ofReal K := by
      filter_upwards [hC', hS', hne, ae_restrict_mem measurableSet_Ioc] with σ hσ hS hne' hmem
      obtain ⟨hsm, hper, hbd, hen⟩ := hσ
      have hlt : σ < s := lt_of_le_of_ne hmem.2 hne'
      have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hlt)
      have hu : (fun z => UnforcedLeray.B0220.periodize c Gm (σ, z)) =ᵐ[volume]
          (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) := by
        filter_upwards [hS hmem.1] with z hz
        exact hz
      have hfun : ∀ i, (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
            (fun z => UnforcedLeray.B0220.periodize c Gm (σ, z)) y) i) =
          (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
            (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) y) i) := by
        intro i
        funext y
        rw [planeHeat_congr_pt hθ hu y]
      have := h3 hH c ν σ s C hc Gs hν hlt hsm hper hbd hen
      refine le_trans (le_of_eq ?_) (this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      unfold B0579.cell
      simp only [hGdef, hfun]
    have hmeas0 : ∀ i j, AEMeasurable (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2 i j)
        (volume.restrict (Ioc 0 s ×ˢ (univ : Set (ℝ × ℝ)))) := fun i j =>
      h4 c ν s hc Gm Gs hν hGm hGmGs
        (hC'.mono fun σ h => ⟨h.1, h.2.1, h.2.2.1⟩) i j
    have hmeas : AEMeasurable (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2)
        (volume.restrict (Ioc 0 s ×ˢ B0579.cell c)) := by
      refine aemeasurable_pi_iff.2 fun i => aemeasurable_pi_iff.2 fun j => ?_
      exact (hmeas0 i j).mono_measure
        (Measure.restrict_mono (prod_mono subset_rfl (subset_univ _)) le_rfl)
    have hcm : MeasurableSet (B0579.cell c) := measurableSet_Ico.prod MeasurableSet.univ
    have := h5 s μ K G (B0579.cell c) hs0 hμ hcm hmeas hbound
    have hrw : ∀ x : ℝ × ℝ, (fun i j => cellGrad b (s, x) i j) =
        fun i j => ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) * G σ x i j := by
      intro x
      funext i j
      exact hRep s hs0 x i j
    simp only [hrw]
    exact this
  have hmeasF : Measurable fun p : Chart =>
      ENNReal.ofReal (tnorm2 (fun i j => cellGrad b p i j) ^ 2) :=
    tnorm2_sq_measurable (fun p i j => cellGrad b p i j) (fun i j => sfcGradMeas c b hb i j)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeasF.aemeasurable]
  have hμ1 : 0 < μ + 1 := by linarith
  calc ∫⁻ s in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (tnorm2 (fun i j => cellGrad b (s, x) i j) ^ 2)
      ≤ ∫⁻ s in Icc s₁ s₂, ENNReal.ofReal ((s₂ / (μ + 1)) ^ 2 * K) := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => (key s hs).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hs0 : 0 < s := lt_of_lt_of_le hs1 hs.1
        have : s / (μ + 1) ≤ s₂ / (μ + 1) := div_le_div_of_nonneg_right hs.2 hμ1.le
        have h0 : 0 ≤ s / (μ + 1) := by positivity
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 this 2) (le_max_right _ _)
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
