import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_5
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1_aux
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.Pointwise

/-!
# Helper for `PartII-b:T11/5/2` (`SliceJointNull`): joint null set by Fubini

Source: `the November 2 reference manuscript` lines 1923-1938, `Sub/T11.lean` step 4.
Let `b'` be a strongly measurable representative of `b ∈ H_r`.  For a.e. `σ`, `b(σ,·) = b'(σ,·)` on
the cell, so `slicePair σ s = F''(σ, s)` for all `σ < s`, where `F''(σ,s) = ∫ Σ b'_i ∇^⊥H(s-σ)_i`
is jointly measurable (`∇^⊥H(τ) = fderiv H (τ, ·)` on `τ > 0`, measurable for every `H`).  The
hypothesis says the `σ`-sections of `E = {0 < σ < s, F'' ≠ 0}` are null for every `s`, so `E` is
null (Tonelli in the form `prod_apply_symm`), hence for a.e. `σ` the `s`-sections are null, and the
shear `s = σ + τ` (measure preserving) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The components of the gradient of `H` (`perpGrad` of the slice `H(τ,·)` for `τ > 0`). -/
def jnVc (H : Coord → ℝ) (i : Fin 2) (x : Coord) : ℝ :=
  ![fderiv ℝ H x (0, (0, 1)), -fderiv ℝ H x (0, (1, 0))] i

theorem jnVc_measurable (H : Coord → ℝ) (i : Fin 2) : Measurable (jnVc H i) := by
  have hm := measurable_fderiv (𝕜 := ℝ) (f := H)
  have hv : ∀ v : Coord, Measurable fun x : Coord => fderiv ℝ H x v :=
    fun v => ((ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable).comp hm
  fin_cases i
  · exact hv _
  · exact (hv _).neg

theorem jnVc_eq {H : Coord → ℝ} (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {τ : ℝ} (hτ : 0 < τ) (p : ℝ × ℝ) (i : Fin 2) :
    perpGrad (fun z => H (τ, z)) p i = jnVc H i (τ, p) := by
  fin_cases i
  · show fderiv ℝ (fun z => H (τ, z)) p (0, 1) = fderiv ℝ H (τ, p) (0, (0, 1))
    exact fderiv_slice hH hτ p (0, 1)
  · show -fderiv ℝ (fun z => H (τ, z)) p (1, 0) = -fderiv ℝ H (τ, p) (0, (1, 0))
    rw [fderiv_slice hH hτ p (1, 0)]

/-- The integrand `Σ_i b'_i(σ,p) ∇^⊥H(s-σ)_i(p)` as a function of `((σ, s), p)`. -/
def jnPsi (b' : CProf) (H : Coord → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2, b' (q.1.1, q.2) i * ((jnVc H i (q.1.2 - q.1.1, q.2) : ℝ) : ℂ)

theorem jnPsi_measurable {b' : CProf} (hb' : Measurable b') (H : Coord → ℝ) :
    Measurable (jnPsi b' H) := by
  have hq1 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.1, q.2) : Coord) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hq2 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.2 - q.1.1, q.2) : Coord) :=
    ((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd
  unfold jnPsi
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.mul ?_ ?_
  · exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.measurable).comp (hb'.comp hq1)
  · exact Complex.measurable_ofReal.comp ((jnVc_measurable H i).comp hq2)

/-- The jointly measurable slice function `F''(σ,s) = ∫ jnPsi ((σ,s),p) dcell`. -/
def jnF (c : ℝ) (b' : CProf) (H : Coord → ℝ) (x : ℝ × ℝ) : ℂ :=
  ∫ p, jnPsi b' H (x, p) ∂(Cyl.avgμ c)

theorem jnF_measurable {c : ℝ} {b' : CProf} (hb' : StronglyMeasurable b') (H : Coord → ℝ) :
    Measurable (jnF c b' H) := by
  have hm : StronglyMeasurable (jnPsi b' H) :=
    (jnPsi_measurable hb'.measurable H).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := Cyl.avgμ c)).measurable

/-- The bad set `E = {0 < σ < s, F''(σ,s) ≠ 0}`. -/
def jnE (c : ℝ) (b' : CProf) (H : Coord → ℝ) : Set (ℝ × ℝ) :=
  {x | 0 < x.1 ∧ x.1 < x.2 ∧ jnF c b' H x ≠ 0}

theorem jnE_measurable {c : ℝ} {b' : CProf} (hb' : StronglyMeasurable b') (H : Coord → ℝ) :
    MeasurableSet (jnE c b' H) := by
  have hFm := jnF_measurable (c := c) hb' H
  have h1 : MeasurableSet {x : ℝ × ℝ | 0 < x.1} :=
    measurableSet_lt measurable_const measurable_fst
  have h2 : MeasurableSet {x : ℝ × ℝ | x.1 < x.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have h3 : MeasurableSet {x : ℝ × ℝ | jnF c b' H x ≠ 0} :=
    (measurableSet_singleton (0 : ℂ)).compl.preimage hFm
  have heq : jnE c b' H = ({x : ℝ × ℝ | 0 < x.1} ∩ {x : ℝ × ℝ | x.1 < x.2}) ∩
      {x : ℝ × ℝ | jnF c b' H x ≠ 0} := by
    ext x
    simp [jnE, and_assoc]
  rw [heq]
  exact (h1.inter h2).inter h3

/-- **Leaf `PartII-b:T11/5/2`** (`SliceJointNull`): the joint null set via Fubini. -/
theorem sliceJointNull : UnforcedLeray.Short.IIb.SliceJointNull := by
  intro c r ν b H hc hr hb hH hyp
  obtain ⟨b', hb'm, hbb'⟩ := hb.meas
  have hG1 : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ p ∂(Cyl.avgμ c), b (σ, p) = b' (σ, p) :=
    sd_ae_slice (c := c) (r / 2 - 5 / 2) hbb'
  -- on the good slices, `slicePair` equals the jointly measurable `F''`
  have hslice_eq : ∀ σ : ℝ, (∀ᵐ p ∂(Cyl.avgμ c), b (σ, p) = b' (σ, p)) →
      ∀ s : ℝ, 0 < σ → σ < s → slicePair c b H σ s = jnF c b' H (σ, s) := by
    intro σ hσ s hσ0 hσs
    unfold slicePair jnF
    refine integral_congr_ae ?_
    filter_upwards [hσ] with p hp
    simp only [jnPsi]
    rw [hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [jnVc_eq hH.smooth (sub_pos.2 hσs) p i]
  have hFm := jnF_measurable (c := c) hb'm H
  have hEm := jnE_measurable (c := c) hb'm H
  -- every `s`-section of `E` is null
  have hsec : ∀ s : ℝ, volume ((fun σ : ℝ => (σ, s)) ⁻¹' jnE c b' H) = 0 := by
    intro s
    by_cases hs : 0 < s
    · have h1 : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) s)), jnF c b' H (σ, s) = 0 := by
        filter_upwards [hyp s hs, ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hG1,
          ae_restrict_mem measurableSet_Ioo] with σ hσ1 hσ2 hσI
        rw [← hslice_eq σ hσ2 s hσI.1 hσI.2]
        exact hσ1
      apply measure_eq_zero_iff_ae_notMem.2
      rw [ae_restrict_iff' measurableSet_Ioo] at h1
      filter_upwards [h1] with σ hσ hmem
      obtain ⟨h1', h2', h3'⟩ := hmem
      exact h3' (hσ ⟨h1', h2'⟩)
    · apply measure_eq_zero_iff_ae_notMem.2
      refine Filter.Eventually.of_forall fun σ hmem => ?_
      obtain ⟨h1', h2', -⟩ := hmem
      exact absurd (lt_trans h1' h2') (fun h => by linarith [not_lt.1 hs, h])
  -- `E` is null in the plane
  have hE0 : volume (jnE c b' H) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hEm]
    simp only [hsec]
    exact lintegral_zero
  have hae : ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ s ∂(volume : Measure ℝ), (σ, s) ∉ jnE c b' H := by
    have h := measure_eq_zero_iff_ae_notMem.1 hE0
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  filter_upwards [ae_restrict_of_ae hae, hG1, ae_restrict_mem measurableSet_Ioi] with σ hσae hσG1 hσ0
  have hτ := ((measurePreserving_add_left (volume : Measure ℝ) σ).quasiMeasurePreserving).ae hσae
  filter_upwards [ae_restrict_of_ae hτ, ae_restrict_mem measurableSet_Ioi] with τ hτE hτpos
  have hF0 : jnF c b' H (σ, σ + τ) = 0 := by
    by_contra hne
    exact hτE ⟨hσ0, by linarith [show (0 : ℝ) < τ from hτpos], hne⟩
  rw [hslice_eq σ hσG1 (σ + τ) hσ0 (by linarith [show (0 : ℝ) < τ from hτpos])]
  exact hF0

end UnforcedLeray.Short.IIb
