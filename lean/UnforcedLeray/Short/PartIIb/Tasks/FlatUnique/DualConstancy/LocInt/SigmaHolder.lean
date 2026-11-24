import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1

/-!
# Leaf `PartII-b:T11/2/1/6` (`SigmaHolder`): Hölder in `σ` on compact sets

Pure real analysis.  On `[a, a'] ⊂ (0, s)` with `a > 0`, write
`σ^e A(σ) B(s-σ) = (σ^α A(σ)) · (σ^{e-α} B(s-σ))` with `α = (r/2-5/2)/r`.  The first factor is
controlled by `∫ σ^{r/2-5/2} A^r < ∞`; the second has a bounded weight `σ^{e-α}` and
`B(s-·)^{r/(r-1)}` integrable on `[s-a', s-a]` by reflection.  Hölder with exponents `r` and
`r/(r-1)` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) finishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Helper: the interval version of `SigmaHolder` (`[a, a'] ⊂ (0, s)`, `a > 0`). -/
theorem sigmaHolder_icc (r e s : ℝ) (A B : ℝ → ℝ≥0∞) (hr : 1 < r) (a a' : ℝ) (ha : 0 < a)
    (haa : a ≤ a') (has : a' < s)
    (hA : AEMeasurable A (volume.restrict (Ioi (0 : ℝ))))
    (hB : AEMeasurable B (volume.restrict (Ioi (0 : ℝ))))
    (hAint : ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * A σ ^ r < ⊤)
    (hBint : ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₂ →
      ∫⁻ τ in Icc τ₁ τ₂, B τ ^ (r / (r - 1)) < ⊤) :
    ∫⁻ σ in Icc a a', ENNReal.ofReal (σ ^ e) * A σ * B (s - σ) < ⊤ := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hq0 : 0 < r / (r - 1) := div_pos hr0 hr1
  have hpq : r.HolderConjugate (r / (r - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hr).2 rfl
  have hIpos : Icc a a' ⊆ Ioi (0 : ℝ) := fun σ hσ => lt_of_lt_of_le ha hσ.1
  have hIm : MeasurableSet (Icc a a') := measurableSet_Icc
  have hmono : volume.restrict (Icc a a') ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono hIpos le_rfl
  -- measurability of the two Hölder factors
  have hXm : AEMeasurable (fun σ => ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ)
      (volume.restrict (Icc a a')) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).aemeasurable.mul
      (hA.mono_measure hmono)
  have hQ : Measure.QuasiMeasurePreserving (fun σ : ℝ => s - σ) (volume.restrict (Icc a a'))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hmp : MeasurePreserving (fun σ : ℝ => s - σ) volume volume :=
      Measure.measurePreserving_sub_left volume s
    have hres := hmp.restrict_preimage (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))
    refine (hres.quasiMeasurePreserving).mono_left ?_
    refine Measure.absolutelyContinuous_of_le (Measure.restrict_mono ?_ le_rfl)
    intro σ hσ
    show 0 < s - σ
    linarith [hσ.2]
  have hBc : AEMeasurable (fun σ => B (s - σ)) (volume.restrict (Icc a a')) :=
    hB.comp_quasiMeasurePreserving hQ
  have hYm : AEMeasurable (fun σ => ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ))
      (volume.restrict (Icc a a')) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).aemeasurable.mul hBc
  -- Hölder
  have hH : ∫⁻ σ in Icc a a',
      (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) *
        (ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ))
      ≤ (∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) ^ r) ^ (1 / r) *
        (∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ)) ^
          (r / (r - 1))) ^ (1 / (r / (r - 1))) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq hXm hYm
  -- pointwise factorization of the integrand on `[a, a']`
  have hfac : ∀ σ ∈ Icc a a',
      ENNReal.ofReal (σ ^ e) * A σ * B (s - σ) =
        (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) *
          (ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ)) := by
    intro σ hσ
    have hσp : 0 < σ := lt_of_lt_of_le ha hσ.1
    have hsplit : σ ^ e = σ ^ ((r / 2 - 5 / 2) / r) * σ ^ (e - (r / 2 - 5 / 2) / r) := by
      rw [← Real.rpow_add hσp]
      congr 1
      ring
    rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg hσp.le _)]
    ring
  -- first factor: finiteness from `hAint`
  have hαr : (r / 2 - 5 / 2) / r * r = r / 2 - 5 / 2 := div_mul_cancel₀ _ hr0.ne'
  have hX1 : ∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) ^ r
      ≤ ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * A σ ^ r := by
    calc ∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) ^ r
        ≤ ∫⁻ σ in Ioi (0 : ℝ), (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) ^ r :=
          lintegral_mono_set hIpos
      _ = ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * A σ ^ r := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun σ hσ => ?_)
          have hσp : 0 < σ := hσ
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.ofReal_rpow_of_nonneg
            (Real.rpow_nonneg hσp.le _) hr0.le, ← Real.rpow_mul hσp.le, hαr]
  have hfin1 : ∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) ^ r < ⊤ :=
    lt_of_le_of_lt hX1 hAint
  -- second factor: bounded weight times reflected `B^{r/(r-1)}`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ σ ∈ Icc a a', ‖σ ^ (e - (r / 2 - 5 / 2) / r)‖ ≤ C := by
    have hcont : ContinuousOn (fun σ : ℝ => σ ^ (e - (r / 2 - 5 / 2) / r)) (Icc a a') :=
      ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (lt_of_lt_of_le ha hx.1).ne')
    exact isCompact_Icc.exists_bound_of_continuousOn hcont
  have hbound : ∀ σ ∈ Icc a a',
      ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) ≤ ENNReal.ofReal C := by
    intro σ hσ
    apply ENNReal.ofReal_le_ofReal
    have h := hC σ hσ
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h
  have hY2 : ∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ)) ^
        (r / (r - 1))
      ≤ ENNReal.ofReal C ^ (r / (r - 1)) * ∫⁻ σ in Icc a a', B (s - σ) ^ (r / (r - 1)) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hq0.le
      ENNReal.ofReal_ne_top).ne]
    refine setLIntegral_mono' hIm (fun σ hσ => ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hbound σ hσ) hq0.le) zero_le
  have hR : ∫⁻ σ in Icc a a', B (s - σ) ^ (r / (r - 1))
      = ∫⁻ τ in Icc (s - a') (s - a), B τ ^ (r / (r - 1)) := by
    rw [← lintegral_indicator hIm, ← lintegral_indicator measurableSet_Icc]
    have key : ∀ σ, (Icc a a').indicator (fun σ => B (s - σ) ^ (r / (r - 1))) σ
        = (Icc (s - a') (s - a)).indicator (fun τ => B τ ^ (r / (r - 1))) (s - σ) := by
      intro σ
      by_cases h : σ ∈ Icc a a'
      · have h' : s - σ ∈ Icc (s - a') (s - a) := ⟨by linarith [h.2], by linarith [h.1]⟩
        rw [indicator_of_mem h, indicator_of_mem h']
      · have h' : s - σ ∉ Icc (s - a') (s - a) :=
          fun hh => h ⟨by linarith [hh.2], by linarith [hh.1]⟩
        rw [indicator_of_notMem h, indicator_of_notMem h']
    rw [lintegral_congr key]
    exact lintegral_sub_left_eq_self _ s
  have hfinB : ∫⁻ τ in Icc (s - a') (s - a), B τ ^ (r / (r - 1)) < ⊤ :=
    hBint (s - a') (s - a) (by linarith) (by linarith)
  have hfin2 : ∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ)) ^
        (r / (r - 1)) < ⊤ :=
    lt_of_le_of_lt hY2 (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le
      ENNReal.ofReal_ne_top) (hR ▸ hfinB))
  -- assemble
  calc ∫⁻ σ in Icc a a', ENNReal.ofReal (σ ^ e) * A σ * B (s - σ)
      = ∫⁻ σ in Icc a a', (ENNReal.ofReal (σ ^ ((r / 2 - 5 / 2) / r)) * A σ) *
          (ENNReal.ofReal (σ ^ (e - (r / 2 - 5 / 2) / r)) * B (s - σ)) :=
        setLIntegral_congr_fun hIm (fun σ hσ => hfac σ hσ)
    _ ≤ _ := hH
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hr0.le) hfin1.ne)
        (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hq0.le) hfin2.ne)

/-- Leaf `T11/2/1/6` (pure real analysis, Hölder in `σ`): see `SigmaHolder` in `Sub/PartIIb_T11_2_1`.
A compact `K ⊂ (0, s)` lies in some `[sInf K, sSup K] ⊂ (0, s)`; apply `sigmaHolder_icc`. -/
theorem SigmaHolder_proof : UnforcedLeray.Short.IIb.SigmaHolder := by
  intro r e s A B hr hs hA hB hAint hBint K hK hKs
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hmin : sInf K ∈ K := hK.sInf_mem hne
  have hmax : sSup K ∈ K := hK.sSup_mem hne
  have hsub : K ⊆ Icc (sInf K) (sSup K) := fun σ hσ =>
    ⟨csInf_le hK.bddBelow hσ, le_csSup hK.bddAbove hσ⟩
  have hle : sInf K ≤ sSup K := (hsub hmin).2
  exact lt_of_le_of_lt (lintegral_mono_set hsub)
    (sigmaHolder_icc r e s A B hr (sInf K) (sSup K) (hKs hmin).1 hle (hKs hmax).2 hA hB hAint hBint)

end UnforcedLeray.Short.IIb
