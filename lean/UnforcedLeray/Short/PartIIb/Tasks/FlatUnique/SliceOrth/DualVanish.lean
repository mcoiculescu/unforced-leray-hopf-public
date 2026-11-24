import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_5
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1_aux
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SmallSlice
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.ProductFormula

/-!
# Helper for `PartII-b:T11/5/1` (`SliceDualVanish`): slice pairing vanishes

Source: `the November 2 reference manuscript` lines 1923-1938, `Sub/T11.lean` steps 2-3.
Three ingredients: `flatDualConstancy` (`F(σ) = κ` a.e.), a Hölder bound for the slice pairing
`|slicePair σ s| ≤ (∫|b(σ)|^r)^{1/r} · D` with `D` the `L^{r'}` norm of `∇^⊥ζ` (contraction
`hcon`), and `smallSliceNorm` (small slice norm on a set of positive measure).  Then
`|κ| ≤ D ε^{1/r} s^{a_r}` for every `ε > 0`, so `κ = 0` since `a_r > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `∫⁻ ‖∇^⊥ζ_i‖^{r'}` over the normalized cell is finite for a nice stream. -/
theorem sd_perp_lint_lt_top {c : ℝ} (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    {r' : ℝ} (hr' : 0 < r') (i : Fin 2) :
    ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ r' ∂(Cyl.avgμ c) < ⊤ := by
  obtain ⟨L, hL⟩ := hζ.compact
  have hKc : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous fun p : ℝ × ℝ => ‖perpGrad ζ p i‖ :=
    (pf_perpGrad_continuous ζ hζ.smooth i).norm
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  have hpt : ∀ p ∈ Cyl.cell c, ‖perpGrad ζ p i‖ₑ ^ r' ≤
      (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L).indicator (fun _ => ENNReal.ofReal M ^ r') p := by
    intro p hp
    by_cases hpK : p ∈ Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L
    · rw [indicator_of_mem hpK]
      apply ENNReal.rpow_le_rpow _ hr'.le
      have h1 := hM p hpK
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [indicator_of_notMem hpK]
      have h2 : p.2 ∉ Icc (-L) L := fun h => hpK ⟨⟨hp.1.1, hp.1.2.le⟩, h⟩
      have hLa : L < |p.2| := by
        by_contra hcon
        push_neg at hcon
        exact h2 (abs_le.1 hcon)
      rw [pf_perpGrad_eq_zero ζ L hL p hLa i]
      simp [ENNReal.zero_rpow_of_pos hr']
  have hKm : MeasurableSet (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hcellm : MeasurableSet (Cyl.cell c) := measurableSet_Ico.prod MeasurableSet.univ
  rw [Cyl.lintegral_avgμ]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  calc ∫⁻ p in Cyl.cell c, ‖perpGrad ζ p i‖ₑ ^ r'
      ≤ ∫⁻ p in Cyl.cell c, (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L).indicator
          (fun _ => ENNReal.ofReal M ^ r') p := setLIntegral_mono' hcellm hpt
    _ ≤ ∫⁻ p, (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L).indicator
          (fun _ => ENNReal.ofReal M ^ r') p := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal M ^ r' * volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) :=
          lintegral_indicator_const hKm _
    _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hr'.le ENNReal.ofReal_ne_top) hKc.measure_lt_top

/-- The `∇^⊥` of a heat slice `H(τ,·)` (`τ > 0`) is continuous in the space variable. -/
theorem sd_perp_slice_continuous {H : Coord → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) {τ : ℝ} (hτ : 0 < τ)
    (i : Fin 2) :
    Continuous fun p : ℝ × ℝ => perpGrad (fun z => H (τ, z)) p i := by
  have hc := (perpGradH_continuousOn hH τ i).comp_continuous
    (f := fun p : ℝ × ℝ => ((0 : ℝ), p)) (by fun_prop) (fun p => hτ)
  simpa [Function.comp_def] using hc


/-- Hölder bound for a slice pairing: `‖slicePair σ s‖ ≤ (∫|b(σ)|^r)^{1/r} · Σ_i ‖∇^⊥ζ_i‖_{L^{r'}}`. -/
theorem sd_slice_bound {c r s σ : ℝ} (hc : 0 < c) (hr : 1 < r) {b : CProf} {H : Coord → ℝ}
    {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (hσs : σ < s)
    (hbs : AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c))
    (hBfin : ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) < ⊤)
    (hcon : ∀ i : Fin 2,
      ∫⁻ p, ‖perpGrad (fun z => H (s - σ, z)) p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c) ≤
        ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) :
    ‖slicePair c b H σ s‖ ≤
      ((∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
        ∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
          (1 / (r / (r - 1)))).toReal := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < r / (r - 1) := div_pos hr0 (by linarith)
  have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
  have hτ : 0 < s - σ := sub_pos.2 hσs
  have hF : ∀ p : ℝ × ℝ, ‖∑ i : Fin 2, b (σ, p) i *
      ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)‖ₑ ≤
      ∑ i : Fin 2, ‖b (σ, p) i‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) p i‖ₑ := by
    intro p
    refine (enorm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real]
  have hbi : ∀ i : Fin 2, AEMeasurable (fun p : ℝ × ℝ => ‖b (σ, p) i‖ₑ) (Cyl.avgμ c) := fun i =>
    (((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
      hbs).enorm)
  have hgi : ∀ i : Fin 2, AEMeasurable
      (fun p : ℝ × ℝ => ‖perpGrad (fun z => H (s - σ, z)) p i‖ₑ) (Cyl.avgμ c) := fun i =>
    ((sd_perp_slice_continuous hH hτ i).enorm).aemeasurable
  have hcomp : ∀ (p : ℝ × ℝ) (i : Fin 2), ‖b (σ, p) i‖ₑ ≤ ‖b (σ, p)‖ₑ := by
    intro p i
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ _)
  have hholder : ∀ i : Fin 2,
      ∫⁻ p, ‖b (σ, p) i‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) p i‖ₑ ∂(Cyl.avgμ c) ≤
        (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
          (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) := by
    intro i
    have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq (Cyl.avgμ c) hpq (hbi i) (hgi i)
    refine h1.trans (mul_le_mul' ?_ ?_)
    · exact ENNReal.rpow_le_rpow
        (lintegral_mono fun p => ENNReal.rpow_le_rpow (hcomp p i) hr0.le) (by positivity)
    · exact ENNReal.rpow_le_rpow (hcon i) (by positivity)
  have htot : ∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i *
      ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c) ≤
      (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
        ∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
          (1 / (r / (r - 1))) := by
    calc ∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c)
        ≤ ∫⁻ p, ∑ i : Fin 2, ‖b (σ, p) i‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) p i‖ₑ
            ∂(Cyl.avgμ c) := lintegral_mono hF
      _ = ∑ i : Fin 2, ∫⁻ p, ‖b (σ, p) i‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) p i‖ₑ
            ∂(Cyl.avgμ c) := lintegral_finsetSum' _ fun i _ => (hbi i).mul (hgi i)
      _ ≤ ∑ i : Fin 2, (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
            (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) :=
          Finset.sum_le_sum fun i _ => hholder i
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hfin : (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
      ∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
        (1 / (r / (r - 1))) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hBfin.ne) ?_
    refine (ENNReal.sum_lt_top.2 fun i _ => ?_).ne
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (sd_perp_lint_lt_top hc hζ hr1 i).ne
  calc ‖slicePair c b H σ s‖
      = ‖∫ p, ∑ i : Fin 2, b (σ, p) i * ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)
          ∂(Cyl.avgμ c)‖ := rfl
    _ ≤ (∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i *
          ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c)).toReal := by
          have hnorm := norm_integral_le_lintegral_norm (μ := Cyl.avgμ c)
            (fun p : ℝ × ℝ => ∑ i : Fin 2, b (σ, p) i *
              ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ))
          simpa only [ofReal_norm_eq_enorm] using hnorm
    _ ≤ _ := ENNReal.toReal_mono hfin htot


/-- The constant bound: for every `ε > 0`, `‖κ‖ ≤ ε^{1/r} · D · s^{a_r}` (`a_r = Re μ + (3/r-1)/2`). -/
theorem sd_kappa_bound {c r s : ℝ} (μ : ℂ) (hc : 0 < c) (hr : 1 < r)
    (ha : 0 < μ.re + (3 / r - 1) / 2) {b : CProf} (hb : InHr c r b)
    {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ) {H : Coord → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (hcon : ∀ τ : ℝ, 0 < τ → ∀ i : Fin 2,
      ∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c) ≤
        ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c))
    (κ : ℂ) (hs : 0 < s)
    (hκ : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) s)),
      ((σ : ℝ) : ℂ) ^ μ * slicePair c b H σ s = κ)
    (ε : ℝ) (hε : 0 < ε) :
    ‖κ‖ ≤ ε ^ (1 / r) * ((∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
      (1 / (r / (r - 1)))).toReal * s ^ (μ.re + (3 / r - 1) / 2)) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < r / (r - 1) := div_pos hr0 (by linarith)
  set e : ℝ := r / 2 - 3 / 2 with he
  set a : ℝ := μ.re + (3 / r - 1) / 2 with ha_def
  set Dz : ℝ := (∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
      (1 / (r / (r - 1)))).toReal with hDz
  -- the set where the small-slice quantity is `≤ ε`
  have hS := smallSliceNorm c r b hc hr hb ε s hε hs
  set Sε : Set ℝ := {σ : ℝ | σ ∈ Ioo (0 : ℝ) s ∧
    ENNReal.ofReal (σ ^ e) * ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) ≤ ENNReal.ofReal ε} with hSε
  have hA2 : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) s)),
      AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c) :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      (slice_aestronglyMeasurable hc hb)
  have hall : ∀ᵐ σ ∂volume, σ ∈ Ioo (0 : ℝ) s →
      ((σ : ℝ) : ℂ) ^ μ * slicePair c b H σ s = κ ∧
        AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c) :=
    (ae_restrict_iff' measurableSet_Ioo).1 (hκ.and hA2)
  -- a good point in `Sε`
  obtain ⟨σ, hσS, hσg⟩ : ∃ σ, σ ∈ Sε ∧
      (((σ : ℝ) : ℂ) ^ μ * slicePair c b H σ s = κ ∧
        AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c)) := by
    by_contra hne
    have hae : ∀ᵐ σ ∂volume, σ ∉ Sε := by
      filter_upwards [hall] with σ hσ hσS
      exact hne ⟨σ, hσS, hσ hσS.1⟩
    have h0 := measure_eq_zero_iff_ae_notMem.2 hae
    exact (ne_of_gt hS) h0
  obtain ⟨hσ1, hσ2⟩ := hσg
  have hσ0 : 0 < σ := hσS.1.1
  have hσs : σ < s := hσS.1.2
  have hpos : ENNReal.ofReal (σ ^ e) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hσ0 e)).ne'
  have hBfin : ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hB => ?_
    have hle := hσS.2
    rw [hB, ENNReal.mul_top hpos] at hle
    exact (not_le.2 ENNReal.ofReal_lt_top) hle
  set B := ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) with hBdef
  set β : ℝ := B.toReal with hβdef
  have hBeq : B = ENNReal.ofReal β := (ENNReal.ofReal_toReal hBfin.ne).symm
  have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
  have hβle : σ ^ e * β ≤ ε := by
    have hle : ENNReal.ofReal (σ ^ e) * B ≤ ENNReal.ofReal ε := hσS.2
    rw [hBeq, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hσ0 e).le,
      ENNReal.ofReal_le_ofReal_iff hε.le] at hle
    exact hle
  have hσe : 0 < σ ^ e := Real.rpow_pos_of_pos hσ0 e
  have hβ2 : β ≤ ε / σ ^ e := (le_div_iff₀ hσe).2 (by linarith [mul_comm (σ ^ e) β])
  -- the slice bound
  have hsl := sd_slice_bound hc hr hζ hH hσs hσ2 hBfin
    (fun i => hcon (s - σ) (sub_pos.2 hσs) i)
  have hB1 : B ^ (1 / r) = ENNReal.ofReal (β ^ (1 / r)) := by
    rw [hBeq, ENNReal.ofReal_rpow_of_nonneg hβ0 (by positivity)]
  have hfin : (∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
      (1 / (r / (r - 1)))) ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.2 fun i _ => ?_).ne
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (sd_perp_lint_lt_top hc hζ hr1 i).ne
  have hslice : ‖slicePair c b H σ s‖ ≤ β ^ (1 / r) * Dz := by
    refine hsl.trans (le_of_eq ?_)
    rw [hB1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- the norm of the constant
  have hκn : ‖κ‖ = σ ^ μ.re * ‖slicePair c b H σ s‖ := by
    rw [← hσ1, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hσ0]
  have hDz0 : 0 ≤ Dz := ENNReal.toReal_nonneg
  -- combine
  have hβroot : β ^ (1 / r) ≤ ε ^ (1 / r) / (σ ^ e) ^ (1 / r) := by
    rw [← Real.div_rpow hε.le hσe.le]
    exact Real.rpow_le_rpow hβ0 hβ2 (by positivity)
  have hexp : σ ^ μ.re / (σ ^ e) ^ (1 / r) = σ ^ a := by
    rw [← Real.rpow_mul hσ0.le, ← Real.rpow_sub hσ0, ha_def, he]
    congr 1
    field_simp
    ring
  calc ‖κ‖ = σ ^ μ.re * ‖slicePair c b H σ s‖ := hκn
    _ ≤ σ ^ μ.re * (β ^ (1 / r) * Dz) := by gcongr
    _ ≤ σ ^ μ.re * ((ε ^ (1 / r) / (σ ^ e) ^ (1 / r)) * Dz) := by gcongr
    _ = ε ^ (1 / r) * (Dz * σ ^ a) := by
        rw [← hexp]; field_simp
    _ ≤ ε ^ (1 / r) * (Dz * s ^ a) := by
        gcongr


/-- A nonnegative number bounded by `ε^{1/r} K` for every `ε > 0` vanishes. -/
theorem sd_norm_zero {r K N : ℝ} (hr : 0 < r) (hK0 : 0 ≤ K) (hN : 0 ≤ N)
    (h : ∀ ε : ℝ, 0 < ε → N ≤ ε ^ (1 / r) * K) : N = 0 := by
  by_contra hne
  have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hne)
  set x : ℝ := N / (2 * (K + 1)) with hx
  have hxpos : 0 < x := div_pos hNpos (by linarith)
  have hq : K / (2 * (K + 1)) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have key := h (x ^ r) (Real.rpow_pos_of_pos hxpos r)
  rw [← Real.rpow_mul hxpos.le, mul_one_div_cancel hr.ne', Real.rpow_one] at key
  have hxK : x * K = N * (K / (2 * (K + 1))) := by
    rw [hx]
    field_simp
  have hlt : N * (K / (2 * (K + 1))) < N := mul_lt_of_lt_one_right hNpos hq
  linarith

/-- **Leaf `PartII-b:T11/5/1`** (`SliceDualVanish`): zero entrance of the slice pairing. -/
theorem sliceDualVanish : UnforcedLeray.Short.IIb.SliceDualVanish := by
  intro c r ν μ hc hν hr hr3 ha b hb h0 ζ H hζ hH hcon s hs
  obtain ⟨κ, hκ⟩ := flatDualConstancy c r ν μ b H s hc hν hr hs hb.inHr h0 hH
  have hκ' : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) s)),
      ((σ : ℝ) : ℂ) ^ μ * slicePair c b H σ s = κ := hκ
  have hK0 : 0 ≤ (∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
      (1 / (r / (r - 1)))).toReal * s ^ (μ.re + (3 / r - 1) / 2) :=
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hs.le _)
  have hκ0 : ‖κ‖ = 0 :=
    sd_norm_zero (show (0 : ℝ) < r by linarith) hK0 (norm_nonneg κ)
      (fun ε hε => sd_kappa_bound μ hc hr ha hb.inHr hζ hH.smooth hcon κ hs hκ' ε hε)
  have hκ00 : κ = 0 := norm_eq_zero.1 hκ0
  filter_upwards [hκ', ae_restrict_mem measurableSet_Ioo] with σ hσ hσI
  rw [hκ00] at hσ
  rcases mul_eq_zero.1 hσ with h | h
  · exfalso
    have hn := Complex.norm_cpow_eq_rpow_re_of_pos hσI.1 μ
    rw [h, norm_zero] at hn
    exact (Real.rpow_pos_of_pos hσI.1 _).ne' hn.symm
  · exact h

end UnforcedLeray.Short.IIb
