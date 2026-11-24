import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.FlatIntegrandBound

/-!
# Integrability of the tested forced integrand (organizer task `PartIII-b:C/flatset/col/7/3/5`)

Source `the November 2 reference manuscript` 1684-1689.
The `b`-part (`F = 0`, `vel = 0`) is integrable by `IIIa.flatIntegrandBound` at `ν = 1, 2`
(the integrand is affine in `ν`, so every `ν` follows); the body-force part `∑ f_i Φ_i`, with
`f = s⁻¹ velC h` a.e., is integrable by the `fib_key` comparison `L²(ageμ) → L¹` on `fibK1`.
`volCyl ≪ ageμ` transfers the a.e. identities to `volume.restrict (Ioi 0 × cell)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest flatDt flatLap)
open UnforcedLeray.Short.PartIIa (IsMeridTest PepsC T0flat solenoidalHC pdS pdQ pdEta)

theorem weakPairIntegrable : WeakPairIntegrable := by
  intro c ν μ hc Φ hΦ f h vR h' B _hh' _hB hhf
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  set SS : Set (ℝ × (ℝ × ℝ)) := Ioi (0 : ℝ) ×ˢ B0579.cell c with hSSdef
  have hSSm : MeasurableSet SS := measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hac : (volume : Measure (ℝ × (ℝ × ℝ))).restrict SS ≪ ageμ c (-3 / 2) :=
    volCyl_ac_ageμ hc (-3 / 2)
  set W : Set (ℝ × (ℝ × ℝ)) := UnforcedLeray.Short.IIIa.fibK1 c s1 s2 R with hWdef
  have hWm : MeasurableSet W := UnforcedLeray.Short.IIIa.fibK1_measurable c s1 s2 R
  set K : Set (ℝ × (ℝ × ℝ)) := Icc s1 s2 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hWK : ∀ p, p ∈ W → p ∈ K := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := (UnforcedLeray.Short.IIIa.fibK1_mem).1 hp
    exact ⟨h1, ⟨h2.1, h2.2.le⟩, h3⟩
  -- measurable representatives of the two L² classes
  set vm := (Lp.aestronglyMeasurable vR).mk ⇑vR with hvm
  set hm := (Lp.aestronglyMeasurable h).mk ⇑h with hhm
  have hvm_meas : Measurable vm := (Lp.aestronglyMeasurable vR).stronglyMeasurable_mk.measurable
  have hhm_meas : Measurable hm := (Lp.aestronglyMeasurable h).stronglyMeasurable_mk.measurable
  have hvm_ae : (⇑vR) =ᵐ[ageμ c (-3 / 2)] vm := (Lp.aestronglyMeasurable vR).ae_eq_mk
  have hhm_ae : (⇑h) =ᵐ[ageμ c (-3 / 2)] hm := (Lp.aestronglyMeasurable h).ae_eq_mk
  -- transfer the a.e. statements from `ageμ` to `volume.restrict SS`
  have hvm_S : ∀ᵐ p ∂(volume.restrict SS), vR p = vm p := hac.ae_le hvm_ae
  have hhm_S : ∀ᵐ p ∂(volume.restrict SS), h p = hm p := hac.ae_le hhm_ae
  have hf_S : ∀ᵐ p ∂(volume.restrict SS), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i :=
    hac.ae_le hhf
  have hvel_S : ∀ᵐ p ∂(volume.restrict SS), ∀ i, NearInst.velC vR p i = NearInst.velC vm p i := by
    filter_upwards [hvm_S] with p hp i
    simp only [NearInst.velC, hp]
  have hkey : ∀ᵐ p ∂(volume.restrict SS), ∀ i, f p i = ((p.1 : ℂ))⁻¹ * NearInst.velC hm p i := by
    filter_upwards [hf_S, hhm_S, ae_restrict_mem hSSm] with p hfp hhp hpS i
    have hp1 : (p.1 : ℂ) ≠ 0 := by
      have : 0 < p.1 := Set.mem_Ioi.1 (Set.mem_prod.1 hpS).1
      exact_mod_cast this.ne'
    have hvh : NearInst.velC h p i = NearInst.velC hm p i := by
      simp only [NearInst.velC, hhp]
    rw [← hvh, hfp i, ← mul_assoc, inv_mul_cancel₀ hp1, one_mul]
  -- norms
  have hvnorm : ∀ x : EuclideanSpace ℝ (Fin 2),
      UnforcedLeray.Short.IIIa.vnorm2 (fun i => ((x i : ℝ) : ℂ)) = ‖x‖ := by
    intro x
    unfold UnforcedLeray.Short.IIIa.vnorm2
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the b-part, for every ν' > 0
  have hBpart : ∀ ν' : ℝ, 0 < ν' →
      IntegrableOn (UnforcedLeray.Short.IIIa.flatIntegrand ν' (μ : ℂ) (fun _ _ _ => 0)
        (fun _ _ _ => 0) (NearInst.velC vm) Φ) SS := by
    intro ν' hν'
    obtain ⟨C, _, hC⟩ := UnforcedLeray.Short.IIIa.flatIntegrandBound c ν' 0 (μ : ℂ) hc hν' Φ hΦ
    have hb : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => NearInst.velC vm p i := by
      intro i
      exact Complex.measurable_ofReal.comp
        ((EuclideanSpace.proj i).continuous.measurable.comp hvm_meas)
    have ht : UnforcedLeray.Short.IIIa.tCalNorm c
        (UnforcedLeray.Short.IIIa.gainConj 0 ν' (fun _ _ _ => (0 : ℂ))) < ⊤ := by
      simp [UnforcedLeray.Short.IIIa.tCalNorm, UnforcedLeray.Short.IIIa.gainConj,
        UnforcedLeray.Short.IIIa.tnorm2]
    have hh : UnforcedLeray.Short.IIIa.hCalNorm c
        (UnforcedLeray.Short.IIIa.gainConj 0 ν' (NearInst.velC vm)) < ⊤ := by
      have e1 : UnforcedLeray.Short.IIIa.gainConj 0 ν' (NearInst.velC vm) = NearInst.velC vm := by
        funext p
        simp [UnforcedLeray.Short.IIIa.gainConj, UnforcedLeray.Short.IIIa.gainG]
      rw [e1]
      unfold UnforcedLeray.Short.IIIa.hCalNorm
      have e2 : (fun p => UnforcedLeray.Short.IIIa.vnorm2 (NearInst.velC vm p)) =
          fun p => ‖vm p‖ := by
        funext p
        unfold NearInst.velC
        exact hvnorm (vm p)
      rw [e2]
      have hcongr : eLpNorm (fun p => ‖vm p‖) 2 (ageμ c (-3 / 2)) =
          eLpNorm (fun p => ‖vR p‖) 2 (ageμ c (-3 / 2)) :=
        eLpNorm_congr_ae (by filter_upwards [hvm_ae] with p hp; simp only [hp])
      rw [hcongr]
      exact (Lp.memLp vR).norm.eLpNorm_lt_top
    have hC' := hC (fun _ _ _ => 0) (NearInst.velC vm) (fun i j => measurable_const) hb ht hh
    exact hC'.1
  -- the b-part with the true velocity class `vR`, for every ν' > 0
  have hFl : ∀ ν' : ℝ, 0 < ν' →
      IntegrableOn (UnforcedLeray.Short.IIIa.flatIntegrand ν' (μ : ℂ) (fun _ _ _ => 0)
        (fun _ _ _ => 0) (NearInst.velC vR) Φ) SS := by
    intro ν' hν'
    refine (hBpart ν' hν').congr ?_
    filter_upwards [hvel_S] with p hp
    simp only [UnforcedLeray.Short.IIIa.flatIntegrand, hp]
  -- body-force part
  set G : ℝ × (ℝ × ℝ) → ℂ := fun p => ∑ i : Fin 2, f p i * (Φ p.1 p.2 i : ℂ) with hGdef
  have hcont : ∀ i : Fin 2, Continuous fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i :=
    fun i => (hΦ.smooth i).continuous
  obtain ⟨M0, hM0, hb0⟩ := UnforcedLeray.Short.IIIa.fib_bound hKc (hcont 0)
  obtain ⟨M1, hM1, hb1⟩ := UnforcedLeray.Short.IIIa.fib_bound hKc (hcont 1)
  have hBnn : 0 ≤ M0 + M1 := add_nonneg hM0 hM1
  have hPhiB : ∀ p ∈ W, ∀ i : Fin 2, ‖Φ p.1 p.2 i‖ ≤ M0 + M1 := by
    intro p hp i
    have hpK := hWK p hp
    rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with rfl | rfl
    · exact (hb0 p hpK).trans (by linarith)
    · exact (hb1 p hpK).trans (by linarith)
  have hzeroOff : ∀ p : ℝ × (ℝ × ℝ), p ∈ SS → p ∉ W → ∀ i : Fin 2, Φ p.1 p.2 i = 0 := by
    intro p hpS hpW i
    apply hsupp p.1 p.2 i
    by_contra hcon
    push_neg at hcon
    apply hpW
    have hq : -(c / 2) ≤ p.2.1 ∧ p.2.1 < c / 2 := by
      have := (Set.mem_prod.1 hpS).2
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at this
      exact this
    exact (UnforcedLeray.Short.IIIa.fibK1_mem).2 ⟨⟨hcon.1, hcon.2.1⟩, hq, abs_le.1 hcon.2.2⟩
  -- pointwise size of the body-force term on `W`
  have hterm : ∀ (p : ℝ × (ℝ × ℝ)) (i : Fin 2), p ∈ W → p ∈ SS →
      f p i = ((p.1 : ℂ))⁻¹ * NearInst.velC hm p i →
      ‖f p i * (Φ p.1 p.2 i : ℂ)‖ ≤ ‖hm p‖ / s1 * (M0 + M1) := by
    intro p i hpW hpS hfi
    have hx : s1 ≤ p.1 := ((UnforcedLeray.Short.IIIa.fibK1_mem).1 hpW).1.1
    have hx0 : 0 < p.1 := lt_of_lt_of_le hs1 hx
    have hn1 : ‖(p.1 : ℂ)‖ = p.1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hv : ‖NearInst.velC hm p i‖ ≤ ‖hm p‖ := by
      unfold NearInst.velC
      rw [Complex.norm_real]
      exact PiLp.norm_apply_le (hm p) i
    have hΦb : ‖(Φ p.1 p.2 i : ℂ)‖ ≤ M0 + M1 := by
      rw [Complex.norm_real]
      exact hPhiB p hpW i
    have hA : ‖NearInst.velC hm p i‖ * ‖(Φ p.1 p.2 i : ℂ)‖ ≤ ‖hm p‖ * (M0 + M1) :=
      mul_le_mul hv hΦb (norm_nonneg _) (norm_nonneg _)
    have hinv : (p.1)⁻¹ ≤ s1⁻¹ := inv_anti₀ hs1 hx
    calc ‖f p i * (Φ p.1 p.2 i : ℂ)‖
        = (p.1)⁻¹ * (‖NearInst.velC hm p i‖ * ‖(Φ p.1 p.2 i : ℂ)‖) := by
          rw [norm_mul, hfi, norm_mul, norm_inv, hn1]
          ring
      _ ≤ s1⁻¹ * (‖hm p‖ * (M0 + M1)) :=
          mul_le_mul hinv hA (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (inv_nonneg.2 hs1.le)
      _ = ‖hm p‖ / s1 * (M0 + M1) := by ring
  -- the body-force integrand is dominated by `(2 (M0+M1)/s1) · 1_W ‖hm‖`
  set wh : ℝ × (ℝ × ℝ) → ℝ := fun p => ‖hm p‖ with hwh
  have hwh_meas : Measurable wh := hhm_meas.norm
  have hfinite : eLpNorm wh 2 (ageμ c (-3 / 2)) < ⊤ := by
    have hcongr : eLpNorm wh 2 (ageμ c (-3 / 2)) = eLpNorm (fun p => ‖h p‖) 2 (ageμ c (-3 / 2)) :=
      eLpNorm_congr_ae (by filter_upwards [hhm_ae] with p hp; simp only [wh, hp])
    rw [hcongr]
    exact (Lp.memLp h).norm.eLpNorm_lt_top
  obtain ⟨Cf, hCf_top, hCf⟩ := UnforcedLeray.Short.IIIa.fib_key (s1 := s1) (s2 := s2) (R := R)
    hc hs1 (-3 / 2) (by norm_num)
  have hWint : Integrable wh (volume.restrict W) := by
    refine ⟨hwh_meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hmain := hCf wh hwh_meas (fun p => norm_nonneg _)
    have hlt : ∫⁻ p in W, ENNReal.ofReal (wh p) < ⊤ :=
      lt_of_le_of_lt hmain (ENNReal.mul_ne_top hCf_top hfinite.ne).lt_top
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun a => ?_)) hlt
    show ‖‖hm a‖‖ₑ = ENNReal.ofReal (wh a)
    rw [Real.enorm_eq_ofReal (norm_nonneg _)]
  have hWind : Integrable (W.indicator wh) volume :=
    (integrable_indicator_iff hWm).2 hWint
  have hgInt : Integrable (fun p => (2 * (M0 + M1) / s1) * W.indicator wh p)
      (volume.restrict SS) :=
    (hWind.const_mul (2 * (M0 + M1) / s1)).restrict
  have hGbound : ∀ᵐ p ∂(volume.restrict SS), ‖G p‖ ≤ (2 * (M0 + M1) / s1) * W.indicator wh p := by
    filter_upwards [ae_restrict_mem hSSm, hkey] with p hpS hk
    by_cases hpW : p ∈ W
    · rw [Set.indicator_of_mem hpW]
      have hsum : ‖G p‖ ≤ ∑ i : Fin 2, ‖f p i * (Φ p.1 p.2 i : ℂ)‖ := norm_sum_le _ _
      have hper : ∀ i : Fin 2, ‖f p i * (Φ p.1 p.2 i : ℂ)‖ ≤ ‖hm p‖ / s1 * (M0 + M1) :=
        fun i => hterm p i hpW hpS (hk i)
      calc ‖G p‖ ≤ ∑ i : Fin 2, ‖f p i * (Φ p.1 p.2 i : ℂ)‖ := hsum
        _ ≤ ∑ _i : Fin 2, ‖hm p‖ / s1 * (M0 + M1) := Finset.sum_le_sum fun i _ => hper i
        _ = (2 * (M0 + M1) / s1) * wh p := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hwh]
          push_cast
          ring
    · have hz : ∀ i : Fin 2, Φ p.1 p.2 i = 0 := fun i => hzeroOff p hpS hpW i
      rw [Set.indicator_of_notMem hpW]
      have : G p = 0 := by
        simp only [hGdef, hz]
        simp
      rw [this]
      simp
  -- measurability of the body-force integrand
  have hv : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => NearInst.velC hm p i := by
    intro i
    exact Complex.measurable_ofReal.comp ((EuclideanSpace.proj i).continuous.measurable.comp hhm_meas)
  have hGm_meas : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, ((p.1 : ℂ))⁻¹ * NearInst.velC hm p i * (Φ p.1 p.2 i : ℂ)) := by
    apply Finset.measurable_sum
    intro i _
    apply Measurable.mul
    · apply Measurable.mul
      · exact (Complex.measurable_ofReal.comp measurable_fst).inv
      · exact hv i
    · exact Complex.measurable_ofReal.comp (hcont i).measurable
  have hGmeas : AEStronglyMeasurable G (volume.restrict SS) := by
    refine AEStronglyMeasurable.congr hGm_meas.aestronglyMeasurable ?_
    filter_upwards [hkey] with p hk
    simp only [hGdef, hk]
  have hGint : Integrable G (volume.restrict SS) :=
    Integrable.mono' hgInt hGmeas hGbound
  -- algebraic splitting in `ν`
  have hlin : ∀ p : ℝ × (ℝ × ℝ),
      forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC vR) Φ p =
        (2 * UnforcedLeray.Short.IIIa.flatIntegrand 1 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p
          - UnforcedLeray.Short.IIIa.flatIntegrand 2 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p)
        - (ν : ℂ) * (UnforcedLeray.Short.IIIa.flatIntegrand 1 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p
          - UnforcedLeray.Short.IIIa.flatIntegrand 2 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p)
        - ∑ i : Fin 2, f p i * (Φ p.1 p.2 i : ℂ) := by
    intro p
    simp only [forcedIntegrand, UnforcedLeray.Short.IIIa.flatIntegrand, Fin.sum_univ_two]
    push_cast
    ring
  have hfun : forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f (NearInst.velC vR) Φ =
      fun p => (2 * UnforcedLeray.Short.IIIa.flatIntegrand 1 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p
          - UnforcedLeray.Short.IIIa.flatIntegrand 2 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p)
        - (ν : ℂ) * (UnforcedLeray.Short.IIIa.flatIntegrand 1 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p
          - UnforcedLeray.Short.IIIa.flatIntegrand 2 (μ : ℂ) (fun _ _ _ => 0)
            (fun _ _ _ => 0) (NearInst.velC vR) Φ p)
        - G p := funext hlin
  have h1 := hFl 1 one_pos
  have h2 := hFl 2 two_pos
  unfold IntegrableOn
  rw [hfun]
  exact ((((h1.const_mul 2).sub h2).sub ((h1.sub h2).const_mul (ν : ℂ))).sub hGint)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
