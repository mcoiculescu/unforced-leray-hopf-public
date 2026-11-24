import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain

/-!
# `PartIII-b:C/near/2/Bound` (`FreeStressPinBound`, source 3541-3552, 1686-1689)

Energy bound for the pin: `‖h‖_H ≤ C ‖F‖_Z`, with `C` depending on `ν, c, m_Z, ρ_b`.  Uses the free
solver `FreeCausalExistsUnique` (hypothesis `hU`, as in `flatFreeGainBound_of`), the velocity bridge
`velNormBridge`, and a source representative for *arbitrary* `ρ_b > 0`
(`sourceMeasRepAny`: the constant picks up `max 1 √ρ_b`; for `ρ_b ≤ 1` this is `sourceMeasRep`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- `sourceMeasRep` for arbitrary `ρ_b > 0` (the second component only costs `√ρ_b`). -/
theorem sourceMeasRepAny (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (hc : 0 < c) (hmZ : 0 ≤ mZ)
    (hρ : 0 < ρb) (F : Zsp c mZ ρb) :
    ∃ Fm : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p i j, Fm p i j = Fm p j i) ∧ (∀ i j, Measurable fun p => Fm p i j) ∧
      Fm =ᵐ[ageμ c (-1 / 2)] merBlockC (zsum (gainEquiv c mZ ρb γ hν F)) ∧
      UnforcedLeray.Short.IIIa.tCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν Fm) ≤
        ENNReal.ofReal (max 1 (Real.sqrt ρb) * ‖F‖) := by
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
  have hEq2 : ageμ c (-1 / 2) = ENNReal.ofReal ρb • htRhoMeasure c ρb := by
    unfold htRhoMeasure
    rw [smul_smul, ← ENNReal.ofReal_mul hρ.le, mul_inv_cancel₀ hρ.ne', ENNReal.ofReal_one, one_smul]
  have hac2 : ageμ c (-1 / 2) ≪ htRhoMeasure c ρb := by
    rw [hEq2]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
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
    hac2.ae_le hG2
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
  have hAEs : AEStronglyMeasurable (zsum (gainEquiv c mZ ρb γ hν F)) (ageμ c (-1 / 2)) := by
    have h1 := (Lp.aestronglyMeasurable ((gainEquiv c mZ ρb γ hν F).fst)).mono_measure hle1
    have h2 := (Lp.aestronglyMeasurable ((gainEquiv c mZ ρb γ hν F).snd)).mono_ac hac2
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
      ((Lp.aestronglyMeasurable F.snd).mono_ac hac2).norm
    have b1 : eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) ≤
        ENNReal.ofReal ‖F.fst‖ :=
      calc eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2))
          ≤ eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (z1Measure c mZ) :=
            eLpNorm_mono_measure _ hle1
        _ = eLpNorm (F.fst : Chart → Ten3) 2 (z1Measure c mZ) := eLpNorm_norm _
        _ = ENNReal.ofReal ‖F.fst‖ := hF1
    have b2 : eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) =
        ENNReal.ofReal (Real.sqrt ρb * ‖F.snd‖) := by
      rw [hEq2, eLpNorm_smul_measure_of_ne_top (by norm_num), eLpNorm_norm, hF2]
      rw [smul_eq_mul, ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow]
      congr 1
      rw [ENNReal.ofReal_rpow_of_nonneg hρ.le ENNReal.toReal_nonneg]
      congr 1
      simp
    have hm1 : (1 : ℝ) ≤ max 1 (Real.sqrt ρb) := le_max_left _ _
    have hm2 : Real.sqrt ρb ≤ max 1 (Real.sqrt ρb) := le_max_right _ _
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
      _ ≤ ENNReal.ofReal ‖F.fst‖ + ENNReal.ofReal (Real.sqrt ρb * ‖F.snd‖) :=
          add_le_add b1 b2.le
      _ = ENNReal.ofReal (‖F.fst‖ + Real.sqrt ρb * ‖F.snd‖) :=
          (ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).symm
      _ ≤ ENNReal.ofReal (max 1 (Real.sqrt ρb) * ‖F‖) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hFn, mul_add]
          have := norm_nonneg F.fst
          have := norm_nonneg F.snd
          nlinarith [mul_le_mul_of_nonneg_right hm1 (norm_nonneg F.fst),
            mul_le_mul_of_nonneg_right hm2 (norm_nonneg F.snd)]

/-- **Target `PartIII-b:C/near/2/Bound`** (`FreeStressPinBound`), from the free solver `hU`. -/
theorem freeStressPinBound_proof (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) :
    FreeStressPinBound := by
  intro P hP Kset hK hKs
  have hadm : UnforcedLeray.Short.IIIa.IsAdmissibleK (Complex.ofReal '' Kset) :=
    ⟨hK.image Complex.continuous_ofReal, by
      rintro _ ⟨x, hx, rfl⟩
      have := hKs hx
      exact ⟨by simpa using this.1, by simpa using this.2⟩⟩
  obtain ⟨ν₀, hν₀, hex⟩ := hU P hP _ hadm
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν hν c hc μ hμ mZ ρb hmZ hρb
  have hνpos : 0 < ν := hν.1
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc' : (ν ^ (-2 : ℝ)) = c := by
    rw [hc, Real.rpow_neg hνpos.le, Real.rpow_two]
  have hexμ := hex ν hν (μ : ℂ) ⟨μ, hμ, rfl⟩
  simp only [hc'] at hexμ
  set γ := P.eigenvalue.re with hγ
  have hk : (1 / 4 : ℝ) ≤ ⨅ μ' : (Complex.ofReal '' Kset), μ'.1.re + 1 / 4 := by
    haveI : Nonempty (Complex.ofReal '' Kset) := ⟨⟨(μ : ℂ), μ, hμ, rfl⟩⟩
    refine le_ciInf fun μ' => ?_
    obtain ⟨x, hx, hxe⟩ := μ'.2
    have := (hKs hx).1
    have h' : μ'.1.re = x := by rw [← hxe]; simp
    rw [h']; linarith
  set E : ℝ := (2 * Real.sqrt ((⨅ μ' : (Complex.ofReal '' Kset), μ'.1.re + 1 / 4) * ν))⁻¹ with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set A : ℝ := ‖((gainEquiv c mZ ρb γ hνpos).symm : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb)‖ with hA
  set B : ℝ := ‖((gainH c γ hνpos : Hsp c ≃L[ℝ] Hsp c) : Hsp c →L[ℝ] Hsp c)‖ with hB
  refine ⟨B * (E * (max 1 (Real.sqrt ρb) * A)), ?_⟩
  intro F h hpin
  obtain ⟨b, G, hbv, hsol⟩ := hpin
  set F0 := (gainEquiv c mZ ρb γ hνpos).symm F with hF0
  obtain ⟨Fm, hsym, hmeas, hae, hnorm⟩ :=
    sourceMeasRepAny c mZ ρb γ ν hνpos hcpos hmZ hρb F0
  have hgF : gainEquiv c mZ ρb γ hνpos F0 = F := (gainEquiv c mZ ρb γ hνpos).apply_symm_apply F
  rw [hgF] at hae
  have hsol' := freeSolAEInvariant c ν (μ : ℂ) hcpos _ Fm b G hsol hae.symm
  have hfin : UnforcedLeray.Short.IIIa.tCalNorm c
      (UnforcedLeray.Short.IIIa.gainConj γ ν Fm) < ⊤ :=
    hnorm.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨b₁, G₁, hsol₁, hH, -, huniq⟩ := hexμ Fm hsym hmeas hfin
  have hbb : b =ᵐ[ageμ c (-3 / 2)] b₁ :=
    (ageMeasureAC c (-3 / 2) hcpos).ae_le (huniq b G hsol')
  have hbb' : UnforcedLeray.Short.IIIa.gainConj γ ν b =ᵐ[ageμ c (-3 / 2)]
      UnforcedLeray.Short.IIIa.gainConj γ ν b₁ := by
    filter_upwards [hbb] with x hx
    simp [UnforcedLeray.Short.IIIa.gainConj, hx]
  have h1 := velNormBridge c γ ν hνpos h b hbv
  have h2 : UnforcedLeray.Short.IIIa.hCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν b) =
      UnforcedLeray.Short.IIIa.hCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν b₁) := by
    unfold UnforcedLeray.Short.IIIa.hCalNorm
    exact eLpNorm_congr_ae (by filter_upwards [hbb'] with x hx; simp [hx])
  have hF0n : ‖F0‖ ≤ A * ‖F‖ :=
    ((gainEquiv c mZ ρb γ hνpos).symm : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb).le_opNorm F
  have h3 : ENNReal.ofReal ‖(gainH c γ hνpos).symm h‖ ≤
      ENNReal.ofReal (E * (max 1 (Real.sqrt ρb) * A * ‖F‖)) := by
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := hH
      _ ≤ ENNReal.ofReal E * ENNReal.ofReal (max 1 (Real.sqrt ρb) * ‖F0‖) := by gcongr
      _ = ENNReal.ofReal (E * (max 1 (Real.sqrt ρb) * ‖F0‖)) := by
          rw [ENNReal.ofReal_mul hE0]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hm : 0 ≤ max 1 (Real.sqrt ρb) := le_trans zero_le_one (le_max_left _ _)
          have := mul_le_mul_of_nonneg_left hF0n hm
          have := mul_le_mul_of_nonneg_left this hE0
          nlinarith
  have h4 : ‖(gainH c γ hνpos).symm h‖ ≤ E * (max 1 (Real.sqrt ρb) * A * ‖F‖) := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).1 h3
    have hm : 0 ≤ max 1 (Real.sqrt ρb) := le_trans zero_le_one (le_max_left _ _)
    have : 0 ≤ A := norm_nonneg _
    positivity
  have h5 : ‖h‖ ≤ B * ‖(gainH c γ hνpos).symm h‖ := by
    have := ((gainH c γ hνpos : Hsp c ≃L[ℝ] Hsp c) : Hsp c →L[ℝ] Hsp c).le_opNorm
      ((gainH c γ hνpos).symm h)
    simpa using this
  calc ‖h‖ ≤ B * ‖(gainH c γ hνpos).symm h‖ := h5
    _ ≤ B * (E * (max 1 (Real.sqrt ρb) * A * ‖F‖)) :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = B * (E * (max 1 (Real.sqrt ρb) * A)) * ‖F‖ := by ring

end UnforcedLeray.Short.PartIIIb.NearInst
#print axioms UnforcedLeray.Short.PartIIIb.NearInst.freeStressPinBound_proof
