import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.SourceMeasRep.Helpers
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.AEInvariant
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.AgeMeasureAC

/-!
# Shared lemma for `PartIII-b:C/near/2/{Exists,Unique}` (source 3564-3571)

`sourceMeasRepFin`: `SourceMeasRep` with finiteness in place of the bound, valid for every
`ρ_b > 0` (the source states `ρ_b ≤ 1`; here only `‖g⁻¹Fm‖_𝒯 < ∞` is needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Blueprint.Planar

theorem sourceMeasRepFin (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (hc : 0 < c) (hmZ : 0 ≤ mZ)
    (hρ : 0 < ρb) (F : Zsp c mZ ρb) :
    ∃ Fm : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p i j, Fm p i j = Fm p j i) ∧ (∀ i j, Measurable fun p => Fm p i j) ∧
      Fm =ᵐ[ageμ c (-1 / 2)] merBlockC (zsum (gainEquiv c mZ ρb γ hν F)) ∧
      UnforcedLeray.Short.IIIa.tCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν Fm) < ⊤ := by
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
  have hageEq : ageμ c (-1 / 2) = ENNReal.ofReal ρb • htRhoMeasure c ρb := by
    unfold htRhoMeasure
    rw [smul_smul, ← ENNReal.ofReal_mul hρ.le, mul_inv_cancel₀ hρ.ne']
    simp
  have hle2 : ageμ c (-1 / 2) ≤ ENNReal.ofReal ρb • htRhoMeasure c ρb := hageEq.le
  have hac2 : ageμ c (-1 / 2) ≪ htRhoMeasure c ρb :=
    Measure.absolutelyContinuous_of_le_smul hle2
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
  -- a measurable representative of the summed source
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
    have hF1 : eLpNorm (F.fst : Chart → Ten3) 2 (z1Measure c mZ) < ⊤ := (Lp.memLp _).2
    have hF2 : eLpNorm (F.snd : Chart → Ten3) 2 (htRhoMeasure c ρb) < ⊤ := (Lp.memLp _).2
    have hN1 : AEStronglyMeasurable (fun p => ‖(F.fst : Chart → Ten3) p‖) (ageμ c (-1 / 2)) :=
      ((Lp.aestronglyMeasurable F.fst).mono_measure hle1).norm
    have hN2 : AEStronglyMeasurable (fun p => ‖(F.snd : Chart → Ten3) p‖) (ageμ c (-1 / 2)) :=
      ((Lp.aestronglyMeasurable F.snd).mono_ac hac2).norm
    have b1 : eLpNorm (fun p => ‖(F.fst : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) < ⊤ :=
      lt_of_le_of_lt
        ((eLpNorm_mono_measure _ hle1).trans_eq (eLpNorm_norm _)) hF1
    have b2 : eLpNorm (fun p => ‖(F.snd : Chart → Ten3) p‖) 2 (ageμ c (-1 / 2)) < ⊤ := by
      rw [hageEq, eLpNorm_smul_measure_of_ne_top (by norm_num)]
      refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity)
        ENNReal.ofReal_ne_top) ?_
      rw [eLpNorm_norm]
      exact hF2
    unfold UnforcedLeray.Short.IIIa.tCalNorm
    have hnn : ∀ T : Fin 2 → Fin 2 → ℂ, 0 ≤ UnforcedLeray.Short.IIIa.tnorm2 T :=
      fun T => Real.sqrt_nonneg _
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (eLpNorm_add_le hN1 hN2 (by norm_num))
      (ENNReal.add_lt_top.2 ⟨b1, b2⟩))
    apply eLpNorm_mono_ae
    filter_upwards [hconj] with p hp
    simp only [Pi.add_apply]
    rw [hp, Real.norm_of_nonneg (hnn _),
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact (blk_norm_le _).trans (norm_add_le _ _)

end UnforcedLeray.Short.PartIIIb.NearInst
