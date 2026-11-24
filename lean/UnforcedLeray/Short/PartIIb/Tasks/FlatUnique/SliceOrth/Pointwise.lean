import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_5
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1_aux
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.DualVanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceAe

/-!
# Helper for `PartII-b:T11/5/3` (`SlicePointwise`): the limit `τ → 0+`

Source: `the November 2 reference manuscript` lines 1923-1938, `Sub/T11.lean` step 4.
For a.e. `σ`, `b(σ,·) ∈ L^r(cell)` and the slice pairing `slicePair σ (σ + τ)` vanishes for a.e.
`τ`.  Writing `slicePair σ (σ+τ) = ∫ Σ b_i (∇^⊥H(τ))_i` and `∫ Σ b_i (∇^⊥ζ)_i = ∫ Σ b_i
(∇^⊥ζ - ∇^⊥H(τ))_i` (both integrable by Hölder), the difference is bounded by
`‖b(σ)‖_{L^r} · ‖∇^⊥H(τ) - ∇^⊥ζ‖_{L^{r'}} → 0` along good `τ`.  The `L^{r'}` convergence is the third
conjunct of the hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Hölder bound for a general pairing `Σ_i b_i h_i` on the cell at a fixed slice `σ`. -/
theorem sp_holder_gen {c r : ℝ} (hr : 1 < r) (b : CProf) (σ : ℝ) (h : Fin 2 → ℝ × ℝ → ℝ)
    (hbs : AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c))
    (hh : ∀ i : Fin 2, AEMeasurable (h i) (Cyl.avgμ c)) :
    ∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i * ((h i p : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c) ≤
      (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
        ∑ i : Fin 2, (∫⁻ p, ‖h i p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
  have hF : ∀ p : ℝ × ℝ, ‖∑ i : Fin 2, b (σ, p) i * ((h i p : ℝ) : ℂ)‖ₑ ≤
      ∑ i : Fin 2, ‖b (σ, p) i‖ₑ * ‖h i p‖ₑ := by
    intro p
    refine (enorm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real]
  have hbi : ∀ i : Fin 2, AEMeasurable (fun p : ℝ × ℝ => ‖b (σ, p) i‖ₑ) (Cyl.avgμ c) := fun i =>
    ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
      hbs).enorm
  have hcomp : ∀ (p : ℝ × ℝ) (i : Fin 2), ‖b (σ, p) i‖ₑ ≤ ‖b (σ, p)‖ₑ := by
    intro p i
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ _)
  have hholder : ∀ i : Fin 2,
      ∫⁻ p, ‖b (σ, p) i‖ₑ * ‖h i p‖ₑ ∂(Cyl.avgμ c) ≤
        (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
          (∫⁻ p, ‖h i p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) := by
    intro i
    have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq (Cyl.avgμ c) hpq (hbi i) (hh i).enorm
    refine h1.trans (mul_le_mul' ?_ ?_)
    · exact ENNReal.rpow_le_rpow
        (lintegral_mono fun p => ENNReal.rpow_le_rpow (hcomp p i) hr0.le) (by positivity)
    · exact le_rfl
  calc ∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i * ((h i p : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c)
      ≤ ∫⁻ p, ∑ i : Fin 2, ‖b (σ, p) i‖ₑ * ‖h i p‖ₑ ∂(Cyl.avgμ c) := lintegral_mono hF
    _ = ∑ i : Fin 2, ∫⁻ p, ‖b (σ, p) i‖ₑ * ‖h i p‖ₑ ∂(Cyl.avgμ c) :=
        lintegral_finsetSum' _ fun i _ => (hbi i).mul (hh i).enorm
    _ ≤ ∑ i : Fin 2, (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
          (∫⁻ p, ‖h i p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) :=
        Finset.sum_le_sum fun i _ => hholder i
    _ = _ := (Finset.mul_sum _ _ _).symm


/-- Integrability of the pairing `Σ_i b_i h_i` on the cell at a fixed slice, from the Hölder bound. -/
theorem sp_integrable {c r : ℝ} (hr : 1 < r) (b : CProf) (σ : ℝ) (h : Fin 2 → ℝ × ℝ → ℝ)
    (hbs : AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c))
    (hh : ∀ i : Fin 2, Measurable (h i))
    (hfin : (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
        ∑ i : Fin 2, (∫⁻ p, ‖h i p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) < ⊤) :
    Integrable (fun p : ℝ × ℝ => ∑ i : Fin 2, b (σ, p) i * ((h i p : ℝ) : ℂ)) (Cyl.avgμ c) := by
  refine ⟨?_, ?_⟩
  · have hm : ∀ i : Fin 2, AEStronglyMeasurable
        (fun p : ℝ × ℝ => b (σ, p) i * ((h i p : ℝ) : ℂ)) (Cyl.avgμ c) := fun i =>
      ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
        hbs).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
          (hh i).aestronglyMeasurable)
    simp only [Fin.sum_univ_two]
    exact (hm 0).add (hm 1)
  · exact (sp_holder_gen hr b σ h hbs fun i => (hh i).aemeasurable).trans_lt hfin

/-- Slice identity: `b = b'` `ageμ`-a.e. gives `b(σ,·) = b'(σ,·)` cell-a.e. for a.e. `σ > 0`. -/
theorem sd_ae_slice {c : ℝ} (a : ℝ) {b b' : CProf} (h : ∀ᵐ z ∂(Axi.ageμ c a), b z = b' z) :
    ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ p ∂(Cyl.avgμ c), b (σ, p) = b' (σ, p) := by
  unfold Axi.ageμ at h
  have h1 := Measure.ae_ae_of_ae_prod h
  rw [ae_withDensity_iff (Axi.measurable_ofReal_rpow a)] at h1
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioi] with σ hσ hσI
  exact hσ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (show (0 : ℝ) < σ from hσI) a)).ne'

/-- Slice finiteness: for `b ∈ H_r`, `∫⁻ ‖b(σ,·)‖^r dcell < ⊤` for a.e. `σ > 0`. -/
theorem sp_B_ae_lt_top {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {b : CProf} (hb : InHr c r b) :
    ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))), ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) < ⊤ := by
  obtain ⟨b', hb'm, hbb'⟩ := hb.meas
  have hfin : eLpNorm b' (ENNReal.ofReal r) (hMeas c r) < ⊤ := by
    rw [← eLpNorm_congr_ae hbb']
    exact hb.finite
  have h1 := deqsa_slice_lt_top hc hr hb'm hfin
  have h2 : ∀ᵐ z ∂(hMeas c r), b z = b' z := hbb'
  have h3 := sd_ae_slice (c := c) (r / 2 - 5 / 2) h2
  filter_upwards [h1, h3] with σ hσ1 hσ2
  have hcongr : (fun p : ℝ × ℝ => ‖b (σ, p)‖ₑ ^ r) =ᵐ[Cyl.avgμ c]
      (fun p : ℝ × ℝ => ‖b' (σ, p)‖ₑ ^ r) :=
    hσ2.mono fun p hp => by simp only [hp]
  rw [lintegral_congr_ae hcongr]
  exact hσ1

/-- A positive-measure window contains a good `τ` for an a.e. property on `(0, ∞)`. -/
theorem sp_exists_good {u : ℝ} (hu : 0 < u) {P : ℝ → Prop}
    (hP : ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), P τ) : ∃ τ ∈ Ioo (0 : ℝ) u, P τ := by
  by_contra hne
  have hae : ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), τ ∉ Ioo (0 : ℝ) u := by
    filter_upwards [hP] with τ hτ hmem
    exact hne ⟨τ, hmem, hτ⟩
  have h0 := measure_eq_zero_iff_ae_notMem.2 hae
  rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 Ioo_subset_Ioi_self,
    Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- Measurability of `p ↦ ∇^⊥(H(τ,·))_i(p)` for an arbitrary `H` (`fderiv` is measurable). -/
theorem sp_perp_measurable (H : Coord → ℝ) (τ : ℝ) (i : Fin 2) :
    Measurable fun p : ℝ × ℝ => perpGrad (fun z => H (τ, z)) p i := by
  have hm := measurable_fderiv (𝕜 := ℝ) (f := fun z : ℝ × ℝ => H (τ, z))
  have hv : ∀ v : ℝ × ℝ, Measurable fun p : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => H (τ, z)) p v :=
    fun v => ((ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable).comp hm
  fin_cases i
  · show Measurable fun p : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => H (τ, z)) p (0, 1)
    exact hv _
  · show Measurable fun p : ℝ × ℝ => -fderiv ℝ (fun z : ℝ × ℝ => H (τ, z)) p (1, 0)
    exact (hv _).neg

/-- The bound `B(σ)^{1/r} Σ_i ‖∇^⊥(H(τ)-ζ)_i‖_{L^{r'}}` for the difference of gradients. -/
def spBound (c r : ℝ) (b : CProf) (σ : ℝ) (ζ : ℝ × ℝ → ℝ) (H : Coord → ℝ) (τ : ℝ) : ℝ≥0∞ :=
  (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
    ∑ i : Fin 2, (∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i‖ₑ ^ (r / (r - 1))
      ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1)))


/-- **Leaf `PartII-b:T11/5/3`** (`SlicePointwise`): the limit `τ → 0+` of the slice pairing. -/
theorem slicePointwise : UnforcedLeray.Short.IIb.SlicePointwise := by
  intro c r b ζ H hc hr hb hζ hT hgood
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < r / (r - 1) := div_pos hr0 (by linarith)
  have hq : (0 : ℝ) < 1 / (r / (r - 1)) := one_div_pos.2 hr1
  have hA := slice_aestronglyMeasurable hc hb
  have hB := sp_B_ae_lt_top hc hr hb
  filter_upwards [hA, hB, hgood] with σ hσA hσB hσG
  have hBne : (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hσB.ne
  have hζm : ∀ i : Fin 2, Measurable fun p : ℝ × ℝ => perpGrad ζ p i := fun i =>
    (pf_perpGrad_continuous ζ hζ.smooth i).measurable
  have hvint : Integrable (fun p : ℝ × ℝ => ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ))
      (Cyl.avgμ c) := by
    refine sp_integrable hr b σ (fun i p => perpGrad ζ p i) hσA hζm ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBne)
      (ENNReal.sum_lt_top.2 fun i _ => ENNReal.rpow_lt_top_of_nonneg hq.le
        (sd_perp_lint_lt_top hc hζ hr1 i).ne)
  -- the Hölder bound tends to `0` as `τ → 0+`
  have hGT : Tendsto (fun τ : ℝ => spBound c r b σ ζ H τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hpow : ∀ i : Fin 2, Tendsto (fun τ : ℝ =>
        (∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i‖ₑ ^ (r / (r - 1))
          ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1)))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      intro i
      have h1 := ((ENNReal.continuous_rpow_const (y := 1 / (r / (r - 1)))).tendsto 0).comp
        (hT i)
      have h2 : ((0 : ℝ≥0∞) ^ (1 / (r / (r - 1)))) = 0 := ENNReal.zero_rpow_of_pos hq
      simp only [h2] at h1
      exact h1
    have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin 2)) fun i _ => hpow i
    have hmul := ENNReal.Tendsto.const_mul hsum (Or.inr hBne)
    simpa [spBound] using hmul
  have hV : ∀ δ : ℝ, 0 < δ →
      ‖∫ p, ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ) ∂(Cyl.avgμ c)‖ ≤ δ := by
    intro δ hδ
    have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), spBound c r b σ ζ H τ < ENNReal.ofReal δ :=
      hGT.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hδ))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    obtain ⟨τ, hτ, hτz⟩ := sp_exists_good hu (P := fun τ => slicePair c b H σ (σ + τ) = 0) hσG
    have hτpos : (0 : ℝ) < τ := hτ.1
    have hGδ : spBound c r b σ ζ H τ < ENNReal.ofReal δ := hsub hτ
    have hGtop : spBound c r b σ ζ H τ < ⊤ := hGδ.trans ENNReal.ofReal_lt_top
    have hsl0 : ∫ p : ℝ × ℝ, ∑ i : Fin 2, b (σ, p) i *
        ((perpGrad (fun z => H (τ, z)) p i : ℝ) : ℂ) ∂(Cyl.avgμ c) = 0 := by
      have h0 := hτz
      simp only [slicePair, add_sub_cancel_left] at h0
      exact h0
    have hwint : Integrable (fun p : ℝ × ℝ => ∑ i : Fin 2, b (σ, p) i *
        ((perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i : ℝ) : ℂ)) (Cyl.avgμ c) :=
      sp_integrable hr b σ (fun i p => perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i) hσA
        (fun i => (sp_perp_measurable H τ i).sub (hζm i)) hGtop
    have huv : (fun p : ℝ × ℝ => ∑ i : Fin 2, b (σ, p) i *
        ((perpGrad (fun z => H (τ, z)) p i : ℝ) : ℂ)) =
        fun p : ℝ × ℝ => (∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i : ℝ) : ℂ)) +
          ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ) := by
      funext p
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [huv, integral_add hwint hvint] at hsl0
    have hVw : ∫ p : ℝ × ℝ, ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ) ∂(Cyl.avgμ c) =
        -∫ p : ℝ × ℝ, ∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i : ℝ) : ℂ) ∂(Cyl.avgμ c) := by
      linear_combination hsl0
    rw [hVw, norm_neg]
    have hh := norm_integral_le_lintegral_norm (μ := Cyl.avgμ c)
      (fun p : ℝ × ℝ => ∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i : ℝ) : ℂ))
    simp only [ofReal_norm_eq_enorm] at hh
    have hbd := sp_holder_gen hr b σ (fun i p => perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i)
      hσA (fun i => ((sp_perp_measurable H τ i).sub (hζm i)).aemeasurable)
    refine hh.trans ((ENNReal.toReal_mono hGtop.ne hbd).trans ?_)
    exact ENNReal.toReal_le_of_le_ofReal hδ.le hGδ.le
  have hV0 : ‖∫ p : ℝ × ℝ, ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ)
      ∂(Cyl.avgμ c)‖ ≤ 0 :=
    le_of_forall_pos_le_add fun δ hδ => by
      have := hV δ hδ
      linarith
  exact norm_le_zero_iff.1 hV0

end UnforcedLeray.Short.IIb
