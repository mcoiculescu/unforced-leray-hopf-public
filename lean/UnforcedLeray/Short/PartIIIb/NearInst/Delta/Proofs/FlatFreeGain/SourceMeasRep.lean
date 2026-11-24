import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.SourceMeasRep.Helpers

/-!
# `SourceMeasRep` (item `PartIII-b:C/near/delta/7/2`)

Source `the November 2 reference manuscript` 3564-3571: for `m_Z ≥ 0`, `0 < ρ_b ≤ 1`
the meridional block of `𝖦F ∈ Z` has a symmetric measurable representative `Fm` whose `g⁻¹`-conjugate
has `𝒯`-norm at most `‖F‖_Z`. Helper lemmas are in `SourceMeasRep/Helpers.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

theorem sourceMeasRep : SourceMeasRep := by
  intro c mZ ρb γ ν hν hc hmZ hρ hρ1 F
  -- the measures of the components dominate the age measure
  have hle1 : ageμ c (-1 / 2) ≤ z1Measure c mZ := by
    unfold z1Measure
    have h1 : ∀ p : Chart, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) := by
      intro p
      have hw : 1 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
        unfold UnforcedLeray.Short.IIIa.transWeight
        exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _))
          (div_nonneg hmZ (by norm_num))
      exact ENNReal.one_le_ofReal.2 (one_le_pow₀ hw)
    calc ageμ c (-1 / 2) = (ageμ c (-1 / 2)).withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (Filter.Eventually.of_forall fun p => h1 p)
  have hle2 : ageμ c (-1 / 2) ≤ htRhoMeasure c ρb := by
    unfold htRhoMeasure
    refine Measure.le_iff'.2 fun s => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left zero_le
      (ENNReal.one_le_ofReal.2 ((one_le_inv₀ hρ).2 hρ1))
  -- the gain acts a.e. as multiplication by `gainFun`
  have hgL : ∀ (μ : Measure Chart) (x : Lp Ten3 2 μ),
      (gainLp μ γ hν x : Chart → Ten3) =ᵐ[μ] gainFun γ ν • (x : Chart → Ten3) :=
    fun μ x => mulBdd_apply_ae (μ := μ) (gainFun γ ν) (gainFun_measurable γ ν)
      (Real.exp (|γ| / ν)) (gainFun_le hν) x
  have hG1 : ∀ᵐ p ∂z1Measure c mZ, ((gainEquiv c mZ ρb γ hν F).fst : Chart → Ten3) p =
      gainFun γ ν p • ((F.fst : Chart → Ten3) p) := hgL _ F.fst
  have hG2 : ∀ᵐ p ∂htRhoMeasure c ρb, ((gainEquiv c mZ ρb γ hν F).snd : Chart → Ten3) p =
      gainFun γ ν p • ((F.snd : Chart → Ten3) p) := hgL _ F.snd
  have hG1' : ∀ᵐ p ∂ageμ c (-1 / 2), ((gainEquiv c mZ ρb γ hν F).fst : Chart → Ten3) p =
      gainFun γ ν p • ((F.fst : Chart → Ten3) p) :=
    (Measure.absolutelyContinuous_of_le hle1).ae_le hG1
  have hG2' : ∀ᵐ p ∂ageμ c (-1 / 2), ((gainEquiv c mZ ρb γ hν F).snd : Chart → Ten3) p =
      gainFun γ ν p • ((F.snd : Chart → Ten3) p) :=
    (Measure.absolutelyContinuous_of_le hle2).ae_le hG2
  have hsum : ∀ᵐ p ∂ageμ c (-1 / 2), zsum (gainEquiv c mZ ρb γ hν F) p =
      gainFun γ ν p • zsum F p := by
    filter_upwards [hG1', hG2'] with p h1 h2
    show ((gainEquiv c mZ ρb γ hν F).fst : Chart → Ten3) p +
      ((gainEquiv c mZ ρb γ hν F).snd : Chart → Ten3) p =
        gainFun γ ν p • ((F.fst : Chart → Ten3) p + (F.snd : Chart → Ten3) p)
    rw [h1, h2, smul_add]
  have hpos : ∀ᵐ p ∂ageμ c (-1 / 2), 0 < p.1 := by
    filter_upwards [UnforcedLeray.Axi.ae_ageμ_mem hc (-1 / 2)] with p hp
    exact hp.1
  -- a measurable representative of the summed source
  have hAEs : AEStronglyMeasurable (zsum (gainEquiv c mZ ρb γ hν F)) (ageμ c (-1 / 2)) := by
    have h1 := (Lp.aestronglyMeasurable ((gainEquiv c mZ ρb γ hν F).fst)).mono_measure hle1
    have h2 := (Lp.aestronglyMeasurable ((gainEquiv c mZ ρb γ hν F).snd)).mono_measure hle2
    exact h1.add h2
  have htm_sm := hAEs.stronglyMeasurable_mk
  have htm_ae := hAEs.ae_eq_mk
  have hT : Measurable (hAEs.mk (zsum (gainEquiv c mZ ρb γ hν F))) := htm_sm.measurable
  have hcoord : ∀ x : Fin 3 × Fin 3,
      Measurable fun p => (hAEs.mk (zsum (gainEquiv c mZ ρb γ hν F)) p) x := fun x => by
    have hcont : Continuous fun t : Ten3 => t x := by fun_prop
    exact hcont.measurable.comp hT
  refine ⟨merBlockC (hAEs.mk (zsum (gainEquiv c mZ ρb γ hν F))), ?_, ?_, ?_, ?_⟩
  · intro p i j
    simp only [merBlockC]
    fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ, merIdx]
  · intro i j
    simp only [merBlockC]
    fin_cases i <;> fin_cases j <;> simp only [nsSym, symRZ, merIdx] <;>
      first
      | exact Complex.measurable_ofReal.comp (hcoord _)
      | exact Complex.measurable_ofReal.comp (((hcoord _).add (hcoord _)).div_const 2)
  · filter_upwards [htm_ae] with p hp
    exact congrArg (fun T : Ten3 => fun (i j : Fin 2) => ((nsSym T (merIdx i) (merIdx j) : ℝ) : ℂ))
      hp.symm
  · have hconj : ∀ᵐ p ∂ageμ c (-1 / 2), UnforcedLeray.Short.IIIa.gainConj γ ν
        (merBlockC (hAEs.mk (zsum (gainEquiv c mZ ρb γ hν F)))) p =
          fun (i j : Fin 2) => ((nsSym (zsum F p) (merIdx i) (merIdx j) : ℝ) : ℂ) := by
      filter_upwards [htm_ae, hsum, hpos] with p hp hs1 hps
      have hgf : gainFun γ ν p = UnforcedLeray.Short.IIIa.gainG γ ν p.1 := by
        unfold gainFun
        rw [max_eq_left hps.le]
      have hk : UnforcedLeray.Short.IIIa.gainG γ ν p.1 ≠ 0 := by
        unfold UnforcedLeray.Short.IIIa.gainG
        exact (Real.exp_pos _).ne'
      change (UnforcedLeray.Short.IIIa.gainG γ ν p.1)⁻¹ • (fun (i j : Fin 2) =>
        ((nsSym (hAEs.mk (zsum (gainEquiv c mZ ρb γ hν F)) p) (merIdx i) (merIdx j) : ℝ) : ℂ)) =
          fun (i j : Fin 2) => ((nsSym (zsum F p) (merIdx i) (merIdx j) : ℝ) : ℂ)
      rw [← hp, hs1, hgf]
      exact conj_blk _ hk _
    have hF1 : eLpNorm (F.fst : Chart → Ten3) 2 (z1Measure c mZ) = ENNReal.ofReal ‖F.fst‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp _).2.ne]
    have hF2 : eLpNorm (F.snd : Chart → Ten3) 2 (htRhoMeasure c ρb) = ENNReal.ofReal ‖F.snd‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp _).2.ne]
    have hFn : ‖F‖ = ‖F.fst‖ + ‖F.snd‖ := by
      rw [WithLp.prod_norm_eq_add (by norm_num)]
      simp
    have hN1 : AEStronglyMeasurable (fun p => ‖(F.fst : Chart → Ten3) p‖) (ageμ c (-1 / 2)) :=
      ((Lp.aestronglyMeasurable F.fst).mono_measure hle1).norm
    have hN2 : AEStronglyMeasurable (fun p => ‖(F.snd : Chart → Ten3) p‖) (ageμ c (-1 / 2)) :=
      ((Lp.aestronglyMeasurable F.snd).mono_measure hle2).norm
    have b1 : eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) ≤
        ENNReal.ofReal ‖F.fst‖ :=
      calc eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2))
          ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (z1Measure c mZ) :=
            eLpNorm_mono_measure _ hle1
        _ = eLpNorm (F.fst : Chart → Ten3) 2 (z1Measure c mZ) := eLpNorm_norm _
        _ = ENNReal.ofReal ‖F.fst‖ := hF1
    have b2 : eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) ≤
        ENNReal.ofReal ‖F.snd‖ :=
      calc eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2))
          ≤ eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (htRhoMeasure c ρb) :=
            eLpNorm_mono_measure _ hle2
        _ = eLpNorm (F.snd : Chart → Ten3) 2 (htRhoMeasure c ρb) := eLpNorm_norm _
        _ = ENNReal.ofReal ‖F.snd‖ := hF2
    unfold UnforcedLeray.Short.IIIa.tCalNorm
    have hnn : ∀ T : Fin 2 → Fin 2 → ℂ, 0 ≤ UnforcedLeray.Short.IIIa.tnorm2 T :=
      fun T => Real.sqrt_nonneg _
    calc eLpNorm (fun p => UnforcedLeray.Short.IIIa.tnorm2 (UnforcedLeray.Short.IIIa.gainConj γ ν
          (merBlockC (hAEs.mk (zsum (gainEquiv c mZ ρb γ hν F)))) p)) 2 (ageμ c (-1 / 2))
        ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖ + ‖(F.snd : Chart → Ten3) p‖) 2
            (ageμ c (-1 / 2)) := by
          apply eLpNorm_mono_ae
          filter_upwards [hconj] with p hp
          rw [hp, Real.norm_of_nonneg (hnn _),
            Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact (blk_norm_le _).trans (norm_add_le _ _)
      _ ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) +
            eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) :=
          eLpNorm_add_le hN1 hN2 (by norm_num)
      _ ≤ ENNReal.ofReal ‖F.fst‖ + ENNReal.ofReal ‖F.snd‖ := add_le_add b1 b2
      _ = ENNReal.ofReal (‖F.fst‖ + ‖F.snd‖) :=
          (ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)).symm
      _ = ENNReal.ofReal ‖F‖ := by rw [hFn]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
