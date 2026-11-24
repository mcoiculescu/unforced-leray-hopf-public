import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt

/-!
# Part II-b, leaf `PartII-b:T11/2/2/5/2` (`DualMainInfIntegrable`)

Source: `the November 2 reference manuscript` 1923-1927.

With the bridge `h1`, `G = pairC b (dualMain μ χ 1 H s 1)` equals
`-(σ^μ χ'(σ)) · Σᵢ bᵢ ∂^⊥ᵢ H(s-σ,·)`, which vanishes off `tsupport χ ⊆ (0,s)`.
Tonelli (`lintegral_prod_le`) on `ageμ c 0 = (dσ|_{σ>0}) ⊗ avgμ c`, the cell Hölder bound
(as in `DualFPointwise`) and `SigmaHolder` on the compact `tsupport χ` give a finite integral of
`‖G‖ₑ`.  Measurability follows from the slice argument of `DualFMeas`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dualMainInfIntegrable_proof : UnforcedLeray.Short.IIb.DualMainInfIntegrable := by
  intro h1 c r ν μ b H s χ hc hν hr hs hb hH hχ
  obtain ⟨hχc, hχcs, hχsupp⟩ := hχ
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr' : 0 < r / (r - 1) := div_pos hr0 hr1
  have hSf : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  -- the age measure at exponent `0` is a product
  have hm : Axi.ageμ c 0 = (volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c) := by
    unfold Axi.ageμ
    simp only [Real.rpow_zero, ENNReal.ofReal_one, withDensity_const, one_smul]
  -- `χ'` vanishes off `tsupport χ`
  have hz1 : ∀ σ : ℝ, σ ∉ tsupport χ → deriv χ σ = 0 := by
    intro σ hσ
    have hev : χ =ᶠ[𝓝 σ] 0 := notMem_tsupport_iff_eventuallyEq.1 hσ
    rw [hev.deriv_eq]
    simp
  have hz0 : ∀ σ : ℝ, σ ∉ Ioo (0 : ℝ) s → deriv χ σ = 0 :=
    fun σ hσ => hz1 σ (fun h => hσ (hχsupp h))
  -- the integrand as a function on the chart
  obtain ⟨S, hS⟩ : ∃ S : Coord → ℂ, S = fun x => ∑ i : Fin 2, b x i *
      ((perpGrad (fun z => H (s - x.1, z)) x.2 i : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ G : Coord → ℂ, G = fun x =>
      -(((x.1 : ℂ) ^ μ) * ((deriv χ x.1 : ℝ) : ℂ)) * S x := ⟨_, rfl⟩
  have hGeq : ∀ x : Coord, pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x = Gf x := by
    intro x
    by_cases hx : x.1 < s
    · simp only [hGf, hS]
      unfold pairC dualMain
      simp only [Complex.ofReal_one, one_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 c ν (r / (r - 1)) H s hc hν hH x i hx]
      ring
    · have hd : deriv χ x.1 = 0 := hz0 x.1 (fun h => hx h.2)
      simp [pairC, dualMain, hGf, hS, hd]
  have hzero : ∀ x : Coord, x.1 ∉ Ioo (0 : ℝ) s → Gf x = 0 := by
    intro x hx
    simp [hGf, hz0 x.1 hx]
  -- measurability
  have hT : MeasurableSet (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hind : Gf = (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))).indicator Gf := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      exact hzero x (fun h => hx (Set.mk_mem_prod h (Set.mem_univ _)))
  have hMr : (Axi.ageμ c 0).restrict (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) =
      (volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c) := by
    rw [hm, ← Measure.prod_restrict, Measure.restrict_restrict_of_subset Ioo_subset_Ioi_self,
      Measure.restrict_univ]
  have hMr2 : (volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c) =
      (volume.prod (Cyl.avgμ c)).restrict (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hbM : AEStronglyMeasurable b ((volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c)) :=
    b_aestronglyMeasurable_prod hc hb s
  have hSm : AEStronglyMeasurable S ((volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c)) := by
    rw [hS]
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    have h1' : AEStronglyMeasurable (fun q : Coord => b q i)
        ((volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c)) :=
      (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hbM
    have hg : AEStronglyMeasurable (fun q : Coord => perpGrad (fun z => H (s - q.1, z)) q.2 i)
        ((volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c)) := by
      rw [hMr2]
      exact ((perpGradH_continuousOn hH.smooth s i).mono (fun q hq => hq.1.2)).aestronglyMeasurable
        hT
    exact h1'.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hg)
  have hA0 : Measurable (fun x : Coord => -(((x.1 : ℂ) ^ μ) * ((deriv χ x.1 : ℝ) : ℂ))) := by
    have e1 : Measurable (fun x : Coord => (x.1 : ℂ) ^ μ) :=
      (Complex.measurable_ofReal.pow_const μ).comp measurable_fst
    have e2 : Measurable (fun x : Coord => ((deriv χ x.1 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp ((measurable_deriv χ).comp measurable_fst)
    exact (e1.mul e2).neg
  have hGm : AEStronglyMeasurable Gf ((volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c)) := by
    rw [hGf]
    exact hA0.aestronglyMeasurable.mul hSm
  have hGint : AEStronglyMeasurable Gf (Axi.ageμ c 0) := by
    rw [hind]
    exact (aestronglyMeasurable_indicator_iff hT).2 (by rw [hMr]; exact hGm)
  -- constants and integrability data
  have hdc : Continuous (deriv χ) := hχc.continuous_deriv (by simp)
  obtain ⟨Cχ, hCχ⟩ := hdc.bounded_above_of_compact_support hχcs.deriv
  have hCle : ∀ σ : ℝ, ‖((deriv χ σ : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal Cχ := by
    intro σ
    rw [← ofReal_norm, Complex.norm_real]
    exact ENNReal.ofReal_le_ofReal (hCχ σ)
  have hnorm : ∀ σ : ℝ, 0 < σ → ‖((σ : ℂ)) ^ μ‖ₑ = ENNReal.ofReal (σ ^ μ.re) := by
    intro σ hσ
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hσ]
  have hSform : ∀ (σ : ℝ) (p : ℝ × ℝ), S (σ, p) =
      ∑ i : Fin 2, b (σ, p) i * ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ) := by
    intro σ p
    simp only [hS]
  have hA : AEMeasurable (dfA c r b) (volume.restrict (Ioi (0 : ℝ))) :=
    (DualFABMeas_proof c r ν b H hc hν hr hb hH).1
  have hB : AEMeasurable (dfB c (r / (r - 1)) H) (volume.restrict (Ioi (0 : ℝ))) :=
    (DualFABMeas_proof c r ν b H hc hν hr hb hH).2
  have hfin1 := DualFAFinite_proof c r b hc hr hb
  have hfin2 : ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ τ₂ →
      ∫⁻ τ in Icc τ₁ τ₂, dfB c (r / (r - 1)) H τ ^ (r / (r - 1)) < ⊤ :=
    fun τ₁ τ₂ h₁ h₂ => DualFBFinite_proof c r ν H hc hν hr hH τ₁ τ₂ h₁ h₂
  have hKc : IsCompact (tsupport χ) := hχcs.isCompact
  have hKm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hSig : ∫⁻ σ in tsupport χ, ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ *
      dfB c (r / (r - 1)) H (s - σ) < ⊤ :=
    SigmaHolder_proof r μ.re s (dfA c r b) (dfB c (r / (r - 1)) H) hr hs hA hB hfin1 hfin2
      (tsupport χ) hKc hχsupp
  -- the integrand bound `Φ`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ≥0∞, ∀ σ : ℝ, Φ σ = ENNReal.ofReal Cχ * 2 *
      (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) :=
    ⟨fun σ => ENNReal.ofReal Cχ * 2 *
      (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)), fun σ => rfl⟩
  -- pointwise `p`-integral bound on `(0,s)` (cell Hölder, as in `DualFPointwise`)
  have hae : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ p, ‖Gf (σ, p)‖ₑ ∂(Cyl.avgμ c) ≤ (tsupport χ).indicator Φ σ := by
    filter_upwards [slice_aestronglyMeasurable hc hb, ae_restrict_mem measurableSet_Ioi]
      with σ hσb hσpos
    have hσ0 : 0 < σ := hσpos
    by_cases hσK : σ ∈ tsupport χ
    · have hσs : σ < s := (hχsupp hσK).2
      rw [indicator_of_mem hσK, hΦ σ]
      have hGp : ∀ p : ℝ × ℝ, ‖Gf (σ, p)‖ₑ =
          (‖((σ : ℂ)) ^ μ‖ₑ * ‖((deriv χ σ : ℝ) : ℂ)‖ₑ) * ‖S (σ, p)‖ₑ := by
        intro p
        rw [hGf]
        simp only [enorm_mul, enorm_neg]
      have hne : ‖((σ : ℂ)) ^ μ‖ₑ * ‖((deriv χ σ : ℝ) : ℂ)‖ₑ ≠ ⊤ :=
        ENNReal.mul_ne_top (by rw [hnorm σ hσ0]; exact ENNReal.ofReal_ne_top)
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCle σ))
      have hpt : ∫⁻ p, ‖Gf (σ, p)‖ₑ ∂(Cyl.avgμ c) =
          (‖((σ : ℂ)) ^ μ‖ₑ * ‖((deriv χ σ : ℝ) : ℂ)‖ₑ) *
            ∫⁻ p, ‖S (σ, p)‖ₑ ∂(Cyl.avgμ c) := by
        calc ∫⁻ p, ‖Gf (σ, p)‖ₑ ∂(Cyl.avgμ c)
            = ∫⁻ p, (‖((σ : ℂ)) ^ μ‖ₑ * ‖((deriv χ σ : ℝ) : ℂ)‖ₑ) * ‖S (σ, p)‖ₑ ∂(Cyl.avgμ c) :=
              lintegral_congr fun p => hGp p
          _ = _ := lintegral_const_mul' _ _ hne
      have hgc : Continuous (fun p : ℝ × ℝ => perpGrad (fun z => H (s - σ, z)) p) := by
        refine continuous_pi fun i => ?_
        have h1' := perpGradH_continuousOn hH.smooth s i
        have h2' : ContinuousOn (fun p : ℝ × ℝ => (σ, p)) univ :=
          (by fun_prop : Continuous fun p : ℝ × ℝ => (σ, p)).continuousOn
        have h3' := h1'.comp h2' (fun p _ => (show (σ, p).1 < s from hσs))
        exact continuousOn_univ.1 h3'
      have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
      have hpt' : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
      have hq0 : ENNReal.ofReal (r / (r - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 hr').ne'
      have hqt : ENNReal.ofReal (r / (r - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
      have hAeq : dfA c r b σ = (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) := by
        unfold dfA
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt', ENNReal.toReal_ofReal hr0.le]
      have hBeq : dfB c (r / (r - 1)) H (s - σ) =
          (∫⁻ p, ‖perpGrad (fun z => H (s - σ, z)) p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
            (1 / (r / (r - 1))) := by
        unfold dfB
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt, ENNReal.toReal_ofReal hr'.le]
      have hgm : AEMeasurable (fun p : ℝ × ℝ => ‖perpGrad (fun z => H (s - σ, z)) p‖ₑ)
          (Cyl.avgμ c) :=
        hgc.measurable.enorm.aemeasurable
      have hbm : AEMeasurable (fun p : ℝ × ℝ => ‖b (σ, p)‖ₑ) (Cyl.avgμ c) :=
        hσb.enorm
      have hHöl : ∫⁻ p, ‖S (σ, p)‖ₑ ∂(Cyl.avgμ c) ≤
          2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) := by
        calc ∫⁻ p, ‖S (σ, p)‖ₑ ∂(Cyl.avgμ c)
            ≤ ∫⁻ p, 2 * (‖b (σ, p)‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) p‖ₑ) ∂(Cyl.avgμ c) :=
              lintegral_mono fun p => by
                rw [hSform σ p]
                exact dualF_pt_bound (b (σ, p)) (perpGrad (fun z => H (s - σ, z)) p)
          _ = 2 * ∫⁻ p, (‖b (σ, p)‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) p‖ₑ) ∂(Cyl.avgμ c) :=
              lintegral_const_mul' _ _ (by simp)
          _ ≤ 2 * ((∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
                (∫⁻ p, ‖perpGrad (fun z => H (s - σ, z)) p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
                  (1 / (r / (r - 1)))) := by
              gcongr
              exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Cyl.avgμ c) hpq hbm hgm
          _ = 2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) := by rw [hAeq, hBeq]
      rw [hpt]
      have hC1 := hCle σ
      calc (‖((σ : ℂ)) ^ μ‖ₑ * ‖((deriv χ σ : ℝ) : ℂ)‖ₑ) * ∫⁻ p, ‖S (σ, p)‖ₑ ∂(Cyl.avgμ c)
          ≤ (ENNReal.ofReal (σ ^ μ.re) * ENNReal.ofReal Cχ) *
              (2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ))) := by
            rw [hnorm σ hσ0]
            gcongr
        _ = ENNReal.ofReal Cχ * 2 *
            (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) := by ring
    · rw [indicator_of_notMem hσK]
      have hd : deriv χ σ = 0 := hz1 σ hσK
      have hzeroG : ∀ p : ℝ × ℝ, Gf (σ, p) = 0 := by
        intro p
        rw [hGf]
        simp [hd]
      simp [hzeroG]
  -- the integral bound
  have hfinite : ∫⁻ σ in tsupport χ, Φ σ < ⊤ := by
    have h2 : ENNReal.ofReal Cχ * 2 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
    calc ∫⁻ σ in tsupport χ, Φ σ
        = ∫⁻ σ in tsupport χ, ENNReal.ofReal Cχ * 2 *
            (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) :=
          lintegral_congr fun σ => hΦ σ
      _ = ENNReal.ofReal Cχ * 2 * ∫⁻ σ in tsupport χ, ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ *
            dfB c (r / (r - 1)) H (s - σ) := lintegral_const_mul' _ _ h2
      _ < ⊤ := ENNReal.mul_lt_top (by finiteness) hSig
  have hind2 : ∫⁻ σ, (tsupport χ).indicator Φ σ < ⊤ := by
    rw [lintegral_indicator hKm]
    exact hfinite
  have hFinGf : ∫⁻ x, ‖Gf x‖ₑ ∂(Axi.ageμ c 0) < ⊤ := by
    rw [hm]
    calc ∫⁻ x, ‖Gf x‖ₑ ∂((volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c))
        ≤ ∫⁻ σ, ∫⁻ p, ‖Gf (σ, p)‖ₑ ∂(Cyl.avgμ c) ∂(volume.restrict (Ioi (0 : ℝ))) :=
          lintegral_prod_le _
      _ ≤ ∫⁻ σ, (tsupport χ).indicator Φ σ ∂(volume.restrict (Ioi (0 : ℝ))) :=
          lintegral_mono_ae hae
      _ ≤ ∫⁻ σ, (tsupport χ).indicator Φ σ :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ < ⊤ := hind2
  have hGfInt : Integrable Gf (Axi.ageμ c 0) := ⟨hGint, hFinGf⟩
  have hfun : (fun x : Coord => pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x) = Gf :=
    funext hGeq
  rw [hfun]
  exact hGfInt

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualMainInfIntegrable_proof
