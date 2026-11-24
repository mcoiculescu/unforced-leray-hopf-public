import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Nonpos.Abstract

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/5` (`StrPairContNonpos`): the junk-representative case `ρb ≤ 0`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

For `ρb ≤ 0`, `gainHTMeasure c ρb γ ν = 0`, so `T.snd = 0` and `strSum T = ⇑T.fst + j₀`, with `j₀`
the (measurable) coercion of the zero element.  The stress integrand is additive, the first part is
integrable and Lipschitz in `L¹(cell)` in terms of `‖T.fst‖` (the `L¹` version of the Cauchy-Schwarz
bound of `stressCSRegion_of`), and `phaseInt_add_cont_of` (Abstract) gives continuity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- The `L¹(cell)` form of the Cauchy-Schwarz bound of `stressCSRegion_of`. -/
theorem stressL1Bound (R c P Y : ℝ) (Φ : ℝ × Space → CVec3) (hR : 0 < R) (hc : 0 < c)
    (hP : P = 2 * c / R) (hY : 0 ≤ Y) (hΦ : IsPhaseTest P Φ)
    (hsupp : ∀ τ y, Y < ‖y‖ → Φ (τ, y) = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Chart → Ten3, Measurable g →
      ∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ ≤
        ENNReal.ofReal K * (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ) := by
  obtain ⟨B, hB0, hBb⟩ := stressPointwise_proof R c P Y Φ hR hc hP hY hΦ hsupp
  obtain ⟨K₁, hK₁0, hK₁⟩ := stressBallLintegral_proof R c P Y hR hc hP hY
  refine ⟨B * K₁, mul_nonneg hB0 hK₁0, fun g hg => ?_⟩
  calc ∫⁻ x in phaseCell P, ‖stressF R c g Φ x‖ₑ
      ≤ ∫⁻ x in phaseCell P, ENNReal.ofReal B * ENNReal.ofReal (stressBall R c Y g x) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hB0, ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hBb g x)
    _ = ENNReal.ofReal B * ∫⁻ x in phaseCell P, ENNReal.ofReal (stressBall R c Y g x) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal K₁ *
          (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ)) := by
        gcongr; exact hK₁ g hg
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hB0]

theorem stressF_sub (R c : ℝ) (g g' : Chart → Ten3) (Φ : ℝ × Space → CVec3) (x : ℝ × Space) :
    stressF R c (g - g') Φ x = stressF R c g Φ x - stressF R c g' Φ x := by
  have h := integrand_add_lin (strPhys R c g') (strPhys R c (g - g')) Φ x
  have e : strPhys R c g' + strPhys R c (g - g') = strPhys R c g := by
    rw [← strPhys_add_lin]; congr 1; abel
  rw [e] at h
  unfold stressF
  rw [h]
  ring

theorem gainHT_eq_zero {c ρb γ ν : ℝ} (hρ : ρb ≤ 0) : gainHTMeasure c ρb γ ν = 0 := by
  unfold gainHTMeasure htRhoMeasure
  have : ENNReal.ofReal ρb⁻¹ = 0 := ENNReal.ofReal_of_nonpos (inv_nonpos.2 hρ)
  simp [this]

theorem strG_snd_zero {c mZ ρb γ ν : ℝ} (hρ : ρb ≤ 0) (T : StrG c mZ ρb γ ν) :
    T.snd = 0 := by
  refine Lp.ext ?_
  rw [Filter.EventuallyEq, ae_eq_bot.2 (gainHT_eq_zero hρ)]
  exact Filter.eventually_bot

theorem strPairContNonpos_core : UnforcedLeray.Short.PartIIIb.Concrete.StrPairContNonpos := by
  intro c mZ ρb γ ν ε hρ hc hν hε Φ hΦ
  obtain ⟨R0, hR0⟩ := hΦ.bounded_support
  set Y : ℝ := max R0 0 with hYdef
  have hY0 : 0 ≤ Y := le_max_right _ _
  have hsupp : ∀ τ y, Y < ‖y‖ → Φ (τ, y) = 0 :=
    fun τ y hy => hR0 τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  set P : ℝ := 2 * ε * c with hPdef
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : P = 2 * c / ε⁻¹ := by rw [hPdef]; field_simp
  obtain ⟨K, hK0, hK⟩ := stressL1Bound ε⁻¹ c P Y Φ hRpos hc hP hY0 hΦ hsupp
  obtain ⟨K2, -, hK2⟩ := stressCSRegion_proved ε⁻¹ c P Y Φ hRpos hc hP hY0 hΦ hsupp
  obtain ⟨Kc, hKtop, -, h1, -, -⟩ := strMeasureCmp_proved c mZ 1 γ ν hν one_pos Y
  set j0 : Chart → Ten3 := ⇑(0 : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) with hj0
  have hstr : ∀ T : StrG c mZ ρb γ ν, strSum T = (T.fst : Chart → Ten3) + j0 := by
    intro T
    funext p
    simp only [strSum, Pi.add_apply]
    rw [strG_snd_zero hρ T]
  have hv : ∀ T : StrG c mZ ρb γ ν, stressPair P (strPhys ε⁻¹ c (strSum T)) Φ =
      phaseInt P (fun z => stressF ε⁻¹ c (T.fst : Chart → Ten3) Φ z + stressF ε⁻¹ c j0 Φ z) := by
    intro T
    unfold stressPair
    rw [hstr T, strPhys_add_lin]
    congr 1
    funext x
    exact integrand_add_lin _ _ _ x
  have hmeasf : ∀ T : StrG c mZ ρb γ ν, Measurable (T.fst : Chart → Ten3) :=
    fun T => (Lp.stronglyMeasurable T.fst).measurable
  have hJ : Measurable (stressF ε⁻¹ c j0 Φ) :=
    stressMeasurable_proof ε⁻¹ c P Φ hRpos hc hP hΦ j0 (Lp.stronglyMeasurable _).measurable
  have hint : ∀ T : StrG c mZ ρb γ ν,
      Integrable (stressF ε⁻¹ c (T.fst : Chart → Ten3) Φ) (volume.restrict (phaseCell P)) :=
    fun T => (hK2 (T.fst : Chart → Ten3) (hmeasf T)
      (lintegral_rpow_two_lt_top_lin (memLp_region_z1_lin hν Y T.fst))).1
  have hs_top : Kc ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hKtop
  have hL : ∀ T T' : StrG c mZ ρb γ ν,
      ∫ z, ‖stressF ε⁻¹ c (T.fst : Chart → Ten3) Φ z - stressF ε⁻¹ c (T'.fst : Chart → Ten3) Φ z‖
        ∂(volume.restrict (phaseCell P)) ≤
      (K * (Kc ^ (1 / (2 : ℝ≥0∞)).toReal).toReal) * dist T T' := by
    intro T T'
    set d : Chart → Ten3 := (T.fst : Chart → Ten3) - (T'.fst : Chart → Ten3) with hd
    have hdm : Measurable d := (hmeasf T).sub (hmeasf T')
    have hfun : (fun z => ‖stressF ε⁻¹ c (T.fst : Chart → Ten3) Φ z -
        stressF ε⁻¹ c (T'.fst : Chart → Ten3) Φ z‖) = fun z => ‖stressF ε⁻¹ c d Φ z‖ := by
      funext z; rw [hd, stressF_sub]
    rw [hfun]
    have hsm : AEStronglyMeasurable (stressF ε⁻¹ c d Φ) (volume.restrict (phaseCell P)) :=
      (stressMeasurable_proof ε⁻¹ c P Φ hRpos hc hP hΦ d hdm).aestronglyMeasurable
    rw [integral_norm_eq_lintegral_enorm hsm]
    -- `L²` comparison of the difference
    have hEq : (∫⁻ p in StrRegion Y, ‖d p‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2)) ^ (1 / 2 : ℝ) =
        eLpNorm d 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat]
    have hf1 : eLpNorm d 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) ≤
        Kc ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm d 2 (gainZ1Measure c mZ γ ν) := by
      have a1 := eLpNorm_le_of_measure_le_smul h1 (f := d) (p := 2)
      have a2 := eLpNorm_mono_measure d (p := 2)
        (Measure.restrict_le_self (μ := gainZ1Measure c mZ γ ν) (s := StrRegion Y))
      exact a1.trans (by rw [smul_eq_mul]; gcongr)
    have hdz : eLpNorm d 2 (gainZ1Measure c mZ γ ν) = ENNReal.ofReal ‖T.fst - T'.fst‖ := by
      have : d =ᵐ[gainZ1Measure c mZ γ ν] ((T.fst - T'.fst : Lp (α := Chart) Ten3 2
          (gainZ1Measure c mZ γ ν)) : Chart → Ten3) := (Lp.coeFn_sub _ _).symm
      rw [eLpNorm_congr_ae this, ← Lp.enorm_def, ofReal_norm_eq_enorm]
    have hlt : ∫⁻ z in phaseCell P, ‖stressF ε⁻¹ c d Φ z‖ₑ ≤
        ENNReal.ofReal K * (Kc ^ (1 / (2 : ℝ≥0∞)).toReal * ENNReal.ofReal ‖T.fst - T'.fst‖) := by
      refine (hK d hdm).trans ?_
      rw [hEq]
      gcongr
      exact hf1.trans (by rw [hdz])
    have hne : ENNReal.ofReal K * (Kc ^ (1 / (2 : ℝ≥0∞)).toReal *
        ENNReal.ofReal ‖T.fst - T'.fst‖) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hs_top ENNReal.ofReal_ne_top)
    have hr := ENNReal.toReal_mono hne hlt
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0,
      ENNReal.toReal_ofReal (norm_nonneg _)] at hr
    have hdist : ‖T.fst - T'.fst‖ ≤ dist T T' := by
      rw [dist_eq_norm, strG_norm_lin]
      have : (T - T').fst = T.fst - T'.fst := rfl
      rw [this]
      exact le_add_of_nonneg_right (norm_nonneg _)
    refine hr.trans ?_
    have h0 : 0 ≤ K * (Kc ^ (1 / (2 : ℝ≥0∞)).toReal).toReal :=
      mul_nonneg hK0 ENNReal.toReal_nonneg
    calc K * ((Kc ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖T.fst - T'.fst‖)
        = (K * (Kc ^ (1 / (2 : ℝ≥0∞)).toReal).toReal) * ‖T.fst - T'.fst‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist h0
  have hmain := phaseInt_add_cont_of (P := P) (fun T : StrG c mZ ρb γ ν =>
    stressF ε⁻¹ c (T.fst : Chart → Ten3) Φ) (stressF ε⁻¹ c j0 Φ) hJ hint _ hL
  have hfe : (fun T : StrG c mZ ρb γ ν => stressPair P (strPhys ε⁻¹ c (strSum T)) Φ) =
      fun T => phaseInt P (fun z => stressF ε⁻¹ c (T.fst : Chart → Ten3) Φ z +
        stressF ε⁻¹ c j0 Φ z) := funext hv
  exact hfe ▸ hmain

end UnforcedLeray.Short.PartIIIb.Concrete

theorem strPairContNonpos_proved : UnforcedLeray.Short.PartIIIb.Concrete.StrPairContNonpos :=
  UnforcedLeray.Short.PartIIIb.Concrete.strPairContNonpos_core
