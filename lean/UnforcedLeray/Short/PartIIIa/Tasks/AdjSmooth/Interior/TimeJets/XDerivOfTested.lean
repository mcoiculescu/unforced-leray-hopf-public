import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.CylUniq

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- An `X_{-m,c}` class and an a.e.-equal function have the same pairing with a cylinder test on
the cell (the cell measure is absolutely continuous with respect to Lebesgue on the cell, and
equivalent to it). -/
theorem xd_setIntegral_eq {c m : ℝ} (u : AdjX c m) (v : ℝ × ℝ → ℂ)
    (h : ⇑u =ᵐ[B0579.cellMeasure c (-m)] v) (ψ : ℝ × ℝ → ℝ) :
    ∫ x in B0579.cell c, u x * (ψ x : ℂ) = ∫ x in B0579.cell c, v x * (ψ x : ℂ) := by
  apply integral_congr_ae
  filter_upwards [(B0579.ac_cellMeasure c (-m)).ae_eq h] with x hx
  simp only [hx]

/-- An interval `[[r, r']]` with both ends in an open interval `Ioo a b` lies in `Ioo a b`. -/
theorem xd_uIcc_sub {a b r r' : ℝ} (hr : r ∈ Ioo a b) (hr' : r' ∈ Ioo a b) :
    uIcc r r' ⊆ Ioo a b := by
  intro σ hσ
  rcases Set.mem_uIcc.mp hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le hr.1 h1, lt_of_le_of_lt h2 hr'.2⟩
  · exact ⟨lt_of_lt_of_le hr'.1 h1, lt_of_le_of_lt h2 hr.2⟩

/-- **(2) A continuous tested derivative is the `X_{-m,c}`-derivative** (SP 3060; Pettis and FTC
in `X_{-m,c}`). -/
theorem xDerivOfTested : XDerivOfTested := by
  intro c m a b f f' hc hf hf' hfd hD
  -- zero extensions of the two families outside `Ioo a b`
  obtain ⟨g, hg_in, hg_out⟩ : ∃ g : ℝ → ℝ × ℝ → ℂ, (∀ σ ∈ Ioo a b, g σ = f σ) ∧
      (∀ σ, σ ∉ Ioo a b → g σ = 0) :=
    ⟨fun σ => (Ioo a b).indicator f σ, fun σ h => Set.indicator_of_mem h f,
      fun σ h => by simp [h]⟩
  obtain ⟨g', hg'_in, hg'_out⟩ : ∃ g' : ℝ → ℝ × ℝ → ℂ, (∀ σ ∈ Ioo a b, g' σ = f' σ) ∧
      (∀ σ, σ ∉ Ioo a b → g' σ = 0) :=
    ⟨fun σ => (Ioo a b).indicator f' σ, fun σ h => Set.indicator_of_mem h f',
      fun σ h => by simp [h]⟩
  have hgm : ∀ σ, MemLp (g σ) 2 (B0579.cellMeasure c (-m)) := by
    intro σ
    by_cases h : σ ∈ Ioo a b
    · rw [hg_in σ h]; exact hf σ h
    · rw [hg_out σ h]; exact MemLp.zero
  have hgm' : ∀ σ, MemLp (g' σ) 2 (B0579.cellMeasure c (-m)) := by
    intro σ
    by_cases h : σ ∈ Ioo a b
    · rw [hg'_in σ h]; exact hf' σ h
    · rw [hg'_out σ h]; exact MemLp.zero
  -- the `X_{-m,c}` classes of the zero extensions
  obtain ⟨E, hE⟩ : ∃ E : ℝ → AdjX c m, ∀ σ, ⇑(E σ) =ᵐ[B0579.cellMeasure c (-m)] g σ :=
    ⟨fun σ => (hgm σ).toLp (g σ), fun σ => (hgm σ).coeFn_toLp⟩
  obtain ⟨E', hE'⟩ : ∃ E' : ℝ → AdjX c m, ∀ σ, ⇑(E' σ) =ᵐ[B0579.cellMeasure c (-m)] g' σ :=
    ⟨fun σ => (hgm' σ).toLp (g' σ), fun σ => (hgm' σ).coeFn_toLp⟩
  have hEf : ∀ σ ∈ Ioo a b, ⇑(E σ) =ᵐ[B0579.cellMeasure c (-m)] f σ := fun σ hσ =>
    (hE σ).trans (Filter.Eventually.of_forall (fun x => congrFun (hg_in σ hσ) x))
  have hE'f : ∀ σ ∈ Ioo a b, ⇑(E' σ) =ᵐ[B0579.cellMeasure c (-m)] f' σ := fun σ hσ =>
    (hE' σ).trans (Filter.Eventually.of_forall (fun x => congrFun (hg'_in σ hσ) x))
  -- continuity of `E'` in `X_{-m,c}` on `Ioo a b`
  have hcontE' : ContinuousOn E' (Ioo a b) := by
    intro σ0 hσ0
    unfold ContinuousWithinAt
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun σ => (xNorm c (-m) (f' σ - f' σ0)).toReal) (𝓝[Ioo a b] σ0) (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hfd σ0 hσ0)
      rw [ENNReal.toReal_zero] at h
      exact h
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hE'f σ hσ).sub (hE'f σ0 hσ0)))]
    rfl
  have hcontE'At : ∀ σ ∈ Ioo a b, ContinuousAt E' σ := fun σ hσ =>
    (hcontE' σ hσ).continuousAt (isOpen_Ioo.mem_nhds hσ)
  -- the pairing identity: the increment of `E` is the Bochner integral of `E'`
  have hGI : ∀ r ∈ Ioo a b, ∀ r' ∈ Ioo a b, E r' - E r = ∫ σ in r..r', E' σ := by
    intro r hr r' hr'
    have hint : IntervalIntegrable E' volume r r' :=
      (hcontE'.mono (xd_uIcc_sub hr hr')).intervalIntegrable
    have hV : E r' - E r - ∫ σ in r..r', E' σ = 0 := by
      refine locCylUniq c m hc _ (fun ψ hψ => ?_)
      obtain ⟨_, Lψ, hL⟩ := adjPairing c m hc ψ hψ
      have hLE : ∀ σ ∈ Ioo a b, Lψ (E σ) = ∫ x in B0579.cell c, f σ x * (ψ x : ℂ) := by
        intro σ hσ
        rw [hL]
        exact xd_setIntegral_eq (E σ) (f σ) (hEf σ hσ) ψ
      have hLE' : ∀ σ ∈ Ioo a b, Lψ (E' σ) = ∫ x in B0579.cell c, f' σ x * (ψ x : ℂ) := by
        intro σ hσ
        rw [hL]
        exact xd_setIntegral_eq (E' σ) (f' σ) (hE'f σ hσ) ψ
      have hcontψ : ContinuousOn (fun σ => ∫ x in B0579.cell c, f' σ x * (ψ x : ℂ)) (Ioo a b) :=
        ((Lψ.continuous.comp_continuousOn hcontE').congr
          (fun σ hσ => (hLE' σ hσ).symm))
      have hintψ : IntervalIntegrable (fun σ => ∫ x in B0579.cell c, f' σ x * (ψ x : ℂ))
          volume r r' := (hcontψ.mono (xd_uIcc_sub hr hr')).intervalIntegrable
      have h3 : ∫ σ in r..r', Lψ (E' σ) = ∫ σ in r..r', ∫ x in B0579.cell c, f' σ x * (ψ x : ℂ) :=
        intervalIntegral.integral_congr (fun σ hσ => hLE' σ (xd_uIcc_sub hr hr' hσ))
      have h4 : ∫ σ in r..r', (∫ x in B0579.cell c, f' σ x * (ψ x : ℂ)) =
          (∫ x in B0579.cell c, f r' x * (ψ x : ℂ)) - ∫ x in B0579.cell c, f r x * (ψ x : ℂ) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun σ hσ => hD ψ hψ σ (xd_uIcc_sub hr hr' hσ)) hintψ
      have hLV := hL (E r' - E r - ∫ σ in r..r', E' σ)
      rw [← hLV, map_sub, map_sub, ← ContinuousLinearMap.intervalIntegral_comp_comm Lψ hint,
        h3, h4, hLE r hr, hLE r' hr']
      ring
    exact sub_eq_zero.mp hV
  -- the derivative of the integral at `r`
  unfold HasXDerivOn
  intro r hr
  have hint_r : IntervalIntegrable E' volume r r :=
    (hcontE'.mono (xd_uIcc_sub hr hr)).intervalIntegrable
  have hmeas_r : StronglyMeasurableAtFilter E' (𝓝 r) :=
    (hcontE'.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo) r hr
  have hGI_deriv : HasDerivAt (fun u => ∫ σ in r..u, E' σ) (E' r) r :=
    intervalIntegral.integral_hasDerivAt_right hint_r hmeas_r (hcontE'At r hr)
  have hsl := hasDerivAt_iff_tendsto_slope.mp hGI_deriv
  have hQ : Tendsto (fun r' => (r' - r)⁻¹ • (E r' - E r) - E' r) (𝓝[Ioo a b \ {r}] r) (𝓝 0) := by
    have h1 := hsl.mono_left (nhdsWithin_mono r (fun x (hx : x ∈ Ioo a b \ {r}) => hx.2))
    have h2 := h1.sub_const (E' r)
    rw [sub_self] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    rw [slope_def_module, intervalIntegral.integral_same, sub_zero, ← hGI r hr r' hr'.1]
  have hnorm : Tendsto (fun r' => ‖(r' - r)⁻¹ • (E r' - E r) - E' r‖) (𝓝[Ioo a b \ {r}] r) (𝓝 0) := by
    have := hQ.norm
    simpa using this
  have hofr : Tendsto (fun r' => ENNReal.ofReal ‖(r' - r)⁻¹ • (E r' - E r) - E' r‖)
      (𝓝[Ioo a b \ {r}] r) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hnorm
    simpa using this
  refine hofr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have hae : ⇑((r' - r)⁻¹ • (E r' - E r) - E' r) =ᵐ[B0579.cellMeasure c (-m)]
      (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) := by
    filter_upwards [Lp.coeFn_sub ((r' - r)⁻¹ • (E r' - E r)) (E' r),
      Lp.coeFn_smul ((r' - r)⁻¹) (E r' - E r), Lp.coeFn_sub (E r') (E r),
      hEf r' hr'.1, hEf r hr, hE'f r hr] with x e1 e2 e3 e4 e5 e6
    simp only [e1, e2, e3, e4, e5, e6, Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
  rw [Lp.norm_def]
  unfold xNorm
  rw [eLpNorm_congr_ae hae.symm]
  exact ENNReal.ofReal_toReal (MemLp.eLpNorm_ne_top (Lp.memLp _))

end UnforcedLeray.Short.IIIa
