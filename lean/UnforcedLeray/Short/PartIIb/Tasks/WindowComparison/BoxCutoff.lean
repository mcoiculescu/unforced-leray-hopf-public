import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G3
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.TestedGradientEnergy
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Tasks.FlatInverse

/-!
# Part II-b, task `PartII-b:G3/1` (`WindowBoxCutoffBound`, SP 2007–2023, 2441–2460)

Source of record: `the November 2 reference manuscript`
(SP), lines 2441–2460:
On the observation box `obsBox σ S L` with `σ = p.ε ^ a`, `S = p.ε ^ (-b)`, and
`L = C_D * (p.c / p.ν + Real.sqrt S + 1)`, construct a smooth observation-box cutoff
`ϑ : ObsCut (σ / 2) (2 * S) (L + 1) Γ` equal to `1` on `obsBox σ S L` with
`Γ = C_Γ * (p.ν ^ 3)⁻¹ * p.ε ^ (-(8 : ℝ) * (a + b))`, and apply the single-box interaction
comparison together with `window_eps_inv_bounds` and `window_gamma_pow_mul_rate` to obtain
`hpIndNorm p.c (obsBox σ S L) (Ke f - K0 f) ≤ C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ (2/539 - N*(a+b)) * ‖f‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. `C^8` derivative bounds for `boxCutoff σ H₁ L₁` -/

private theorem exists_smoothTransition_deriv_bound :
    ∃ M_st : ℝ, 1 ≤ M_st ∧ ∀ l ≤ 8, ∀ x : ℝ, ‖iteratedDeriv l Real.smoothTransition x‖ ≤ M_st := by
  choose M hM using ageJets_bound
  refine ⟨1 + ∑ l ∈ Finset.range 9, |M l|, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.range 9) => abs_nonneg (M l))
    linarith
  · intro l hl x
    have hmem : l ∈ Finset.range 9 := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg (M i)) hmem
    have h1 := hM l x
    have h2 := le_abs_self (M l)
    linarith

private theorem affine_smoothTransition_iteratedFDeriv_le {M_st : ℝ}
    (hM : ∀ l ≤ 8, ∀ x : ℝ, ‖iteratedDeriv l Real.smoothTransition x‖ ≤ M_st)
    (a b : ℝ) {A : ℝ} (hA1 : 1 ≤ A) (ha : |a| ≤ A) {l : ℕ} (hl : l ≤ 8) (t : ℝ) :
    ‖iteratedFDeriv ℝ l (fun s : ℝ => Real.smoothTransition (a * s + b)) t‖ ≤ A ^ 8 * M_st := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hφ : ContDiff ℝ l (fun z : ℝ => Real.smoothTransition (z + b)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)
  have hfun : (fun s : ℝ => Real.smoothTransition (a * s + b)) =
      fun s : ℝ => (fun z : ℝ => Real.smoothTransition (z + b)) (a * s) := rfl
  have hit : iteratedDeriv l (fun z : ℝ => Real.smoothTransition (z + b)) =
      fun z => iteratedDeriv l Real.smoothTransition (z + b) :=
    iteratedDeriv_comp_add_const l Real.smoothTransition b
  rw [hfun, iteratedDeriv_comp_const_mul hφ a, hit, norm_mul, norm_pow, Real.norm_eq_abs]
  have hal : |a| ^ l ≤ A ^ 8 :=
    (pow_le_pow_left₀ (abs_nonneg a) ha l).trans (pow_le_pow_right₀ hA1 hl)
  exact mul_le_mul hal (hM l hl (a * t + b)) (norm_nonneg _) (by positivity)

private def projEtaCLM : Coord →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private theorem norm_projEtaCLM_le : ‖projEtaCLM‖ ≤ 1 := by
  unfold projEtaCLM
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖
      ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
        (ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem norm_iteratedFDeriv_mul_le_8 {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℝ} (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) (x : Coord)
    (hf_bd : ∀ m ≤ 8, ‖iteratedFDeriv ℝ m f x‖ ≤ A)
    (hg_bd : ∀ m ≤ 8, ‖iteratedFDeriv ℝ m g x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 8) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ 2304 * A * B := by
  have hmul := norm_iteratedFDeriv_mul_le hf hg x (n := k) (by exact_mod_cast le_top)
  refine hmul.trans ?_
  have hsum : ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ ≤
      ∑ _i ∈ Finset.range (k + 1), (2 : ℝ) ^ 8 * A * B := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hch : (k.choose i : ℝ) ≤ (2 : ℝ) ^ 8 := by
      have h1 : (k.choose i : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast Nat.choose_le_two_pow k i
      exact h1.trans (pow_le_pow_right₀ (by norm_num) hk)
    have hAB : ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ ≤ A * B :=
      mul_le_mul (hf_bd i (hi_le.trans hk)) (hg_bd (k - i) ((Nat.sub_le k i).trans hk))
        (norm_nonneg _) hA0
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖
        = (k.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖) := by ring
      _ ≤ (2 : ℝ) ^ 8 * (A * B) :=
          mul_le_mul hch hAB (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 8 * A * B := by ring
  refine hsum.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hk9 : ((k + 1 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast (show k + 1 ≤ 9 by omega)
  calc ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ 8 * A * B)
      ≤ 9 * ((2 : ℝ) ^ 8 * A * B) := mul_le_mul_of_nonneg_right hk9 (by positivity)
    _ = 2304 * A * B := by ring

private theorem exists_boxCutoff_iteratedFDeriv_bound :
    ∃ C_cut : ℝ, 1 ≤ C_cut ∧
      ∀ (σ H₁ L₁ : ℝ), 0 < σ → σ ≤ 1 → 1 ≤ H₁ →
        ∀ k ≤ 8, ∀ x : Coord,
          ‖iteratedFDeriv ℝ k (boxCutoff σ H₁ L₁) x‖ ≤ C_cut * (σ⁻¹) ^ 8 := by
  obtain ⟨M_st, hM1, hM⟩ := exists_smoothTransition_deriv_bound
  set C_cut : ℝ := 2304 ^ 3 * 256 * M_st ^ 4
  have hC1 : 1 ≤ C_cut := by
    have : (1 : ℝ) ≤ M_st ^ 4 := one_le_pow₀ hM1
    dsimp [C_cut]
    nlinarith
  refine ⟨C_cut, hC1, ?_⟩
  intro σ H₁ L₁ hσ0 hσ1 hH₁ k hk x
  have hσ_inv1 : 1 ≤ σ⁻¹ := one_le_inv₀ hσ0 |>.mpr hσ1
  have h2σ_inv1 : 1 ≤ 2 * σ⁻¹ := by linarith
  have hH₁0 : 0 < H₁ := lt_of_lt_of_le one_pos hH₁
  have hH₁_inv1 : H₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hH₁
  set f1_1d : ℝ → ℝ := fun s => Real.smoothTransition ((2 * σ⁻¹) * s + (-1))
  set f2_1d : ℝ → ℝ := fun s => Real.smoothTransition ((-H₁⁻¹) * s + 2)
  set e1_1d : ℝ → ℝ := fun η => Real.smoothTransition (1 * η + (L₁ + 1))
  set e2_1d : ℝ → ℝ := fun η => Real.smoothTransition ((-1) * η + (L₁ + 1))
  have hf1_cd : ContDiff ℝ ∞ f1_1d := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hf2_cd : ContDiff ℝ ∞ f2_1d := Real.smoothTransition.contDiff.comp (by fun_prop)
  have he1_cd : ContDiff ℝ ∞ e1_1d := Real.smoothTransition.contDiff.comp (by fun_prop)
  have he2_cd : ContDiff ℝ ∞ e2_1d := Real.smoothTransition.contDiff.comp (by fun_prop)
  set L_s : Coord →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  have hLs_norm : ‖L_s‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)
  have hf1_bd : ∀ m ≤ 8, ‖iteratedFDeriv ℝ m (f1_1d ∘ L_s) x‖ ≤ 256 * M_st * (σ⁻¹) ^ 8 := by
    intro m hm
    refine (cutJets_comp_le hf1_cd L_s hLs_norm m x).trans ?_
    have habs : |2 * σ⁻¹| ≤ 2 * σ⁻¹ := by
      rw [abs_of_pos (by positivity)]
    have h1 := affine_smoothTransition_iteratedFDeriv_le hM (2 * σ⁻¹) (-1) h2σ_inv1 habs hm (L_s x)
    calc ‖iteratedFDeriv ℝ m f1_1d (L_s x)‖
        ≤ (2 * σ⁻¹) ^ 8 * M_st := h1
      _ = 256 * M_st * (σ⁻¹) ^ 8 := by ring
  have hf2_bd : ∀ m ≤ 8, ‖iteratedFDeriv ℝ m (f2_1d ∘ L_s) x‖ ≤ M_st := by
    intro m hm
    refine (cutJets_comp_le hf2_cd L_s hLs_norm m x).trans ?_
    have habs : |-H₁⁻¹| ≤ 1 := by
      rw [abs_neg, abs_of_pos (inv_pos.mpr hH₁0)]
      exact hH₁_inv1
    have h1 := affine_smoothTransition_iteratedFDeriv_le hM (-H₁⁻¹) 2 le_rfl habs hm (L_s x)
    simpa [f2_1d] using h1
  have he1_bd : ∀ m ≤ 8, ‖iteratedFDeriv ℝ m (e1_1d ∘ projEtaCLM) x‖ ≤ M_st := by
    intro m hm
    refine (cutJets_comp_le he1_cd projEtaCLM norm_projEtaCLM_le m x).trans ?_
    have habs : |(1 : ℝ)| ≤ 1 := by norm_num
    have h1 := affine_smoothTransition_iteratedFDeriv_le hM 1 (L₁ + 1) le_rfl habs hm (projEtaCLM x)
    simpa [e1_1d] using h1
  have he2_bd : ∀ m ≤ 8, ‖iteratedFDeriv ℝ m (e2_1d ∘ projEtaCLM) x‖ ≤ M_st := by
    intro m hm
    refine (cutJets_comp_le he2_cd projEtaCLM norm_projEtaCLM_le m x).trans ?_
    have habs : |(-1 : ℝ)| ≤ 1 := by norm_num
    have h1 := affine_smoothTransition_iteratedFDeriv_le hM (-1) (L₁ + 1) le_rfl habs hm (projEtaCLM x)
    simpa [e2_1d] using h1
  have hs_bd : ∀ m ≤ 8,
      ‖iteratedFDeriv ℝ m (fun y : Coord => (f1_1d ∘ L_s) y * (f2_1d ∘ L_s) y) x‖ ≤
        2304 * (256 * M_st * (σ⁻¹) ^ 8) * M_st :=
    fun m hm => norm_iteratedFDeriv_mul_le_8 (hf1_cd.comp L_s.contDiff) (hf2_cd.comp L_s.contDiff)
      (by positivity) (by positivity) x hf1_bd hf2_bd hm
  have he_bd : ∀ m ≤ 8,
      ‖iteratedFDeriv ℝ m (fun y : Coord => (e1_1d ∘ projEtaCLM) y * (e2_1d ∘ projEtaCLM) y) x‖ ≤
        2304 * M_st * M_st :=
    fun m hm => norm_iteratedFDeriv_mul_le_8 (he1_cd.comp projEtaCLM.contDiff)
      (he2_cd.comp projEtaCLM.contDiff) (by positivity) (by positivity) x he1_bd he2_bd hm
  have hbox_eq : boxCutoff σ H₁ L₁ = fun y : Coord =>
      ((f1_1d ∘ L_s) y * (f2_1d ∘ L_s) y) *
        ((e1_1d ∘ projEtaCLM) y * (e2_1d ∘ projEtaCLM) y) := by
    funext y
    unfold boxCutoff sBoxCut etaBoxCut f1_1d f2_1d e1_1d e2_1d L_s projEtaCLM
    simp only [Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_snd']
    have h1 : 2 * y.1 / σ - 1 = 2 * σ⁻¹ * y.1 + -1 := by ring
    have h2 : (2 * H₁ - y.1) / H₁ = -H₁⁻¹ * y.1 + 2 := by
      rw [sub_div, mul_div_cancel_right₀ 2 hH₁0.ne']
      ring
    have h3 : L₁ + 1 + y.2.2 = 1 * y.2.2 + (L₁ + 1) := by ring
    have h4 : L₁ + 1 - y.2.2 = -1 * y.2.2 + (L₁ + 1) := by ring
    rw [h1, h2, h3, h4]
  rw [hbox_eq]
  have htot := norm_iteratedFDeriv_mul_le_8
    ((hf1_cd.comp L_s.contDiff).mul (hf2_cd.comp L_s.contDiff))
    ((he1_cd.comp projEtaCLM.contDiff).mul (he2_cd.comp projEtaCLM.contDiff))
    (by positivity) (by positivity) x hs_bd he_bd hk
  calc ‖iteratedFDeriv ℝ k (fun y : Coord =>
          ((f1_1d ∘ L_s) y * (f2_1d ∘ L_s) y) *
            ((e1_1d ∘ projEtaCLM) y * (e2_1d ∘ projEtaCLM) y)) x‖
      ≤ 2304 * (2304 * (256 * M_st * (σ⁻¹) ^ 8) * M_st) * (2304 * M_st * M_st) := htot
    _ = C_cut * (σ⁻¹) ^ 8 := by dsimp [C_cut]; ring

/-- Package `boxCutoff σ H₁ L₁` as an `ObsCut (σ / 2) (2 * H₁) (L₁ + 1) Γ` whenever
`C_cut * (σ⁻¹) ^ 8 ≤ Γ`. -/
private def mkWindowObsCut {σ H₁ L₁ C_cut Γ : ℝ} (hσ0 : 0 < σ) (hσH₁ : σ ≤ H₁)
    (hbd : ∀ k ≤ 8, ∀ x : Coord, ‖iteratedFDeriv ℝ k (boxCutoff σ H₁ L₁) x‖ ≤ C_cut * (σ⁻¹) ^ 8)
    (hΓ : C_cut * (σ⁻¹) ^ 8 ≤ Γ) :
    ObsCut (σ / 2) (2 * H₁) (L₁ + 1) Γ where
  ϑ := boxCutoff σ H₁ L₁
  smooth := boxCutoff_contDiff σ H₁ L₁
  supp := fun _ hx => boxCutoff_eq_zero_of_notMem hσ0 hσH₁ hx
  bounded := fun k hk x => (hbd k hk x).trans hΓ

/-! ## 2. Window exponent and indicator norm comparison -/

private theorem inv_rpow_pow_eight_le {ε a b : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (_ha : 0 < a) (hb : 0 < b) :
    ((ε ^ a)⁻¹) ^ (8 : ℕ) ≤ ε ^ (-(8 : ℝ) * (a + b)) := by
  rw [← Real.rpow_neg hε0.le, ← Real.rpow_natCast (ε ^ (-a)) 8, ← Real.rpow_mul hε0.le]
  have hexp : -(8 : ℝ) * (a + b) ≤ -a * (8 : ℕ) := by push_cast; linarith
  have hdiff : 0 ≤ -a * (8 : ℕ) - -(8 : ℝ) * (a + b) := sub_nonneg.mpr hexp
  have h1 : ε ^ (-a * (8 : ℕ) - -(8 : ℝ) * (a + b)) ≤ 1 := Real.rpow_le_one hε0.le hε1 hdiff
  calc ε ^ (-a * (8 : ℕ))
      = ε ^ (-a * (8 : ℕ) - -(8 : ℝ) * (a + b) + -(8 : ℝ) * (a + b)) := by ring_nf
    _ = ε ^ (-a * (8 : ℕ) - -(8 : ℝ) * (a + b)) * ε ^ (-(8 : ℝ) * (a + b)) :=
        Real.rpow_add hε0 _ _
    _ ≤ 1 * ε ^ (-(8 : ℝ) * (a + b)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hε0.le _)
    _ = ε ^ (-(8 : ℝ) * (a + b)) := one_mul _

private theorem hpIndNorm_obsBox_le_cutoff_hNorm {c σ S L : ℝ} (hc : 0 < c)
    (hσ : 0 < σ) (hσS : σ ≤ S) (Ke_f K0_f : HpR c) (g_flat : CProf)
    (hK0_ae : toProf c K0_f =ᵐ[hMeas c bgp] g_flat) {M : ℝ} (hM0 : 0 ≤ M)
    (hbd : hNorm c bgp (fun x => (boxCutoff σ S L x : ℂ) • (toProf c Ke_f x - g_flat x)) ≤
      ENNReal.ofReal M) :
    hpIndNorm c (obsBox σ S L) (Ke_f - K0_f) ≤ M := by
  set pE := ENNReal.ofReal bgp
  set μ := hMeas c bgp
  have hptw : ∀ᵐ x ∂μ,
      ‖(obsBox σ S L).indicator ((Ke_f - K0_f : HpR c) : Coord → Axi.Merid) x‖ ≤
        ‖(boxCutoff σ S L x : ℂ) • (toProf c Ke_f x - g_flat x)‖ := by
    filter_upwards [Lp.coeFn_sub Ke_f K0_f, toProf_ae_eq hc Ke_f, toProf_ae_eq hc K0_f,
      hK0_ae] with x hsub hKe_lift hK0_lift hK0_eq
    by_cases hx : x ∈ obsBox σ S L
    · rw [Set.indicator_of_mem hx, boxCutoff_eq_one_of_mem hσ hσS hx, Complex.ofReal_one, one_smul,
        hsub, Pi.sub_apply, hKe_lift, ← hK0_eq, hK0_lift, ← liftM_sub', liftM_norm]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _
  have hmono : eLpNorm ((obsBox σ S L).indicator ((Ke_f - K0_f : HpR c) : Coord → Axi.Merid)) pE μ ≤
      ENNReal.ofReal M :=
    (eLpNorm_mono_ae hptw).trans hbd
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono
  rwa [ENNReal.toReal_ofReal hM0] at htoReal

/-! ## 3. Main theorem: `windowBoxCutoffBound_proof` (`PartII-b:G3/1`) -/

/-- **Proof of `WindowBoxCutoffBound` (`PartII-b:G3/1`, SP 2007–2023, 2441–2460)**. -/
theorem windowBoxCutoffBound_proof : UnforcedLeray.Short.IIb.WindowBoxCutoffBound := by
  obtain ⟨C_cut, hC_cut1, hCut_bd⟩ := exists_boxCutoff_iteratedFDeriv_bound
  intro k_loc C_loc hC_loc N a b ha hb dm dp _hdm C_D hCD1
  set C_Γ : ℝ := C_cut + 4 * C_D + 2
  have hC_Γ_pos : 0 < C_Γ := by dsimp [C_Γ]; linarith
  set C_box : ℝ := C_loc * C_Γ ^ k_loc
  set k_box : ℕ := 3 * k_loc
  refine ⟨C_box, k_box, 1, by positivity, one_pos, ?_⟩
  intro p d hreg hν1 _hP1 hLoc Ke K0 hKe hK0 f σ S L
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hε_pos : 0 < p.ε := p.ε_pos
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hν_pos.le
  obtain ⟨hE1, hσ_inv_le, hS_le, hsqrtS_le⟩ := window_eps_inv_bounds hε_pos hε1 ha hb
  set E : ℝ := p.ε ^ (-(8 : ℝ) * (a + b))
  set V : ℝ := (p.ν ^ 3)⁻¹
  have hV_pos : 0 < V := by dsimp [V]; positivity
  have hE_pos : 0 < E := by dsimp [E]; exact Real.rpow_pos_of_pos hε_pos _
  have hν3_le_one : p.ν ^ 3 ≤ 1 := pow_le_one₀ hν_pos.le hν1
  have hV1 : 1 ≤ V := by
    dsimp [V]
    exact one_le_inv₀ (pow_pos hν_pos 3) |>.mpr hν3_le_one
  have hν_inv_le_V : p.ν⁻¹ ≤ V := by
    dsimp [V]
    rw [inv_le_inv₀ hν_pos (pow_pos hν_pos 3)]
    calc p.ν ^ 3 ≤ p.ν ^ 1 := pow_le_pow_of_le_one hν_pos.le hν1 (by omega)
      _ = p.ν := pow_one p.ν
  have hc_div_ν : p.c / p.ν = V := by
    dsimp [V]
    rw [hreg.c_eq, div_eq_mul_inv, ← mul_inv, ← pow_succ]
  have hVE1 : 1 ≤ V * E := one_le_mul_of_one_le_of_one_le hV1 hE1
  have hV_le_VE : V ≤ V * E := le_mul_of_one_le_right hV_pos.le hE1
  have hE_le_VE : E ≤ V * E := le_mul_of_one_le_left hE_pos.le hV1
  have hσ_pos : 0 < σ := Real.rpow_pos_of_pos hε_pos a
  have hσ1 : σ ≤ 1 := Real.rpow_le_one hε_pos.le hε1 ha.le
  have hS1 : 1 ≤ S := by
    dsimp [S]
    have h1 : p.ε ^ (-b) * p.ε ^ b = 1 := by
      rw [← Real.rpow_add hε_pos, neg_add_cancel, Real.rpow_zero]
    have h2 : p.ε ^ b ≤ 1 := Real.rpow_le_one hε_pos.le hε1 hb.le
    nlinarith [Real.rpow_pos_of_pos hε_pos (-b)]
  have hσS : σ ≤ S := hσ1.trans hS1
  have hσ8_le : (σ⁻¹) ^ 8 ≤ E := inv_rpow_pow_eight_le hε_pos hε1 ha hb
  set Γ : ℝ := C_Γ * V * E
  have hC_Γ1 : 1 ≤ C_Γ := by dsimp [C_Γ]; linarith
  have hΓ1 : 1 ≤ Γ := by
    dsimp [Γ]
    rw [mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hC_Γ1 hVE1
  have hν_le_Γ : p.ν ≤ Γ := hν1.trans hΓ1
  have hν_inv_le_Γ : p.ν⁻¹ ≤ Γ := by
    calc p.ν⁻¹ ≤ V := hν_inv_le_V
      _ ≤ V * E := hV_le_VE
      _ = 1 * (V * E) := (one_mul _).symm
      _ ≤ C_Γ * (V * E) := mul_le_mul_of_nonneg_right hC_Γ1 (by positivity)
      _ = Γ := by dsimp [Γ]; ring
  have hσ2_inv_le_Γ : (σ / 2)⁻¹ ≤ Γ := by
    have h1 : (σ / 2)⁻¹ = 2 * σ⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have h2 : 2 ≤ C_Γ := by dsimp [C_Γ]; linarith
    rw [h1]
    calc 2 * σ⁻¹ ≤ 2 * E := mul_le_mul_of_nonneg_left hσ_inv_le zero_le_two
      _ ≤ 2 * (V * E) := mul_le_mul_of_nonneg_left hE_le_VE zero_le_two
      _ ≤ C_Γ * (V * E) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = Γ := by dsimp [Γ]; ring
  have h2S_le_Γ : 2 * S ≤ Γ := by
    have h2 : 2 ≤ C_Γ := by dsimp [C_Γ]; linarith
    calc 2 * S ≤ 2 * E := mul_le_mul_of_nonneg_left hS_le zero_le_two
      _ ≤ 2 * (V * E) := mul_le_mul_of_nonneg_left hE_le_VE zero_le_two
      _ ≤ C_Γ * (V * E) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = Γ := by dsimp [Γ]; ring
  have hL1_le_Γ : L + 1 ≤ Γ := by
    have hsum : p.c / p.ν + Real.sqrt S + 1 ≤ 3 * (V * E) := by
      rw [hc_div_ν]
      have hsqrt_VE : Real.sqrt S ≤ V * E := hsqrtS_le.trans hE_le_VE
      linarith
    have hL_le : L ≤ 3 * C_D * (V * E) := by
      dsimp [L]
      calc C_D * (p.c / p.ν + Real.sqrt S + 1)
          ≤ C_D * (3 * (V * E)) := mul_le_mul_of_nonneg_left hsum (by linarith)
        _ = 3 * C_D * (V * E) := by ring
    have h1_le : 1 ≤ C_D * (V * E) := one_le_mul_of_one_le_of_one_le hCD1 hVE1
    have h4CD : 4 * C_D ≤ C_Γ := by dsimp [C_Γ]; linarith
    calc L + 1 ≤ 3 * C_D * (V * E) + C_D * (V * E) := add_le_add hL_le h1_le
      _ = (4 * C_D) * (V * E) := by ring
      _ ≤ C_Γ * (V * E) := mul_le_mul_of_nonneg_right h4CD (by positivity)
      _ = Γ := by dsimp [Γ]; ring
  have hCut_le_Γ : C_cut * (σ⁻¹) ^ 8 ≤ Γ := by
    have hC : C_cut ≤ C_Γ := by dsimp [C_Γ]; linarith
    calc C_cut * (σ⁻¹) ^ 8 ≤ C_cut * E := mul_le_mul_of_nonneg_left hσ8_le (by linarith)
      _ ≤ C_cut * (V * E) := mul_le_mul_of_nonneg_left hE_le_VE (by linarith)
      _ ≤ C_Γ * (V * E) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = Γ := by dsimp [Γ]; ring
  let ϑ : ObsCut (σ / 2) (2 * S) (L + 1) Γ :=
    mkWindowObsCut hσ_pos hσS (hCut_bd σ S L hσ_pos hσ1 hS1) hCut_le_Γ
  obtain ⟨bε, hbε_in, hbε_resp, hbε_kout⟩ := hKe f
  obtain ⟨b0, gq0, gη0, hb0_cls, hb0_resp, hgq0, hgη0, hK0_ae⟩ := hK0 f
  have hF_in : InHr p.c bgp (toProf p.c f) := inHr_toProf hc_pos f
  have hgε_in : InHr p.c bgp (toProf p.c (Ke f)) := inHr_toProf hc_pos (Ke f)
  obtain ⟨gq, gη, hgq, hgη, hLoc_bd⟩ :=
    hLoc Γ (σ / 2) (2 * S) (L + 1) hΓ1 hν_le_Γ hν_inv_le_Γ hσ2_inv_le_Γ h2S_le_Γ hL1_le_Γ
      (half_pos hσ_pos) ϑ (toProf p.c f) bε b0 (toProf p.c (Ke f))
      hF_in hbε_in hbε_resp hb0_resp hb0_cls hgε_in hbε_kout
  have hflat_uniq : flatK p.train b0 gq gη =ᵐ[hMeas p.c bgp] flatK p.train b0 gq0 gη0 :=
    F10K0Help.flatK_unique_ae hν_pos hc_pos p.train hF_in hb0_cls hb0_resp hgq hgη
      hb0_cls hb0_resp hgq0 hgη0
  have hK0_ae' : toProf p.c (K0 f) =ᵐ[hMeas p.c bgp] flatK p.train b0 gq gη :=
    hK0_ae.trans hflat_uniq.symm
  have hrate_eq :
      (C_loc * Γ ^ k_loc * p.ε ^ (2 / 539 : ℝ)) * ‖f‖ =
        C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (N : ℝ) * (a + b)) * ‖f‖ := by
    have hV_pow : V ^ k_loc = (p.ν ^ k_box)⁻¹ := by
      dsimp [V, k_box]
      rw [inv_pow, ← pow_mul]
    have hE_rate := window_gamma_pow_mul_rate (a := a) (b := b) hε_pos k_loc
    dsimp only at hE_rate
    calc (C_loc * Γ ^ k_loc * p.ε ^ (2 / 539 : ℝ)) * ‖f‖
        = C_loc * (C_Γ ^ k_loc * V ^ k_loc * E ^ k_loc) * p.ε ^ (2 / 539 : ℝ) * ‖f‖ := by
          dsimp [Γ]
          rw [mul_pow, mul_pow]
      _ = (C_loc * C_Γ ^ k_loc) * V ^ k_loc * (E ^ k_loc * p.ε ^ (2 / 539 : ℝ)) * ‖f‖ := by ring
      _ = C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (N : ℝ) * (a + b)) * ‖f‖ := by
          rw [hV_pow, hE_rate]
  have hF_norm : hNorm p.c bgp (toProf p.c f) = ENNReal.ofReal ‖f‖ := by
    rw [hNorm_toProf hc_pos f, (ofReal_norm f).symm]
  have hM_nonneg :
      0 ≤ C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (N : ℝ) * (a + b)) * ‖f‖ := by
    rw [← hrate_eq]
    positivity
  have hLoc_bd' :
      hNorm p.c bgp (fun x => (boxCutoff σ S L x : ℂ) •
          (toProf p.c (Ke f) x - flatK p.train b0 gq gη x)) ≤
        ENNReal.ofReal
          (C_box * (p.ν ^ k_box)⁻¹ * p.ε ^ ((2 / 539 : ℝ) - (N : ℝ) * (a + b)) * ‖f‖) := by
    change hNorm p.c bgp (fun x => (ϑ.ϑ x : ℂ) •
        (toProf p.c (Ke f) x - flatK p.train b0 gq gη x)) ≤ _
    refine hLoc_bd.trans ?_
    rw [hF_norm, ← ENNReal.ofReal_mul (by positivity), hrate_eq]
  exact hpIndNorm_obsBox_le_cutoff_hNorm hc_pos hσ_pos hσS (Ke f) (K0 f)
    (flatK p.train b0 gq gη) hK0_ae' hM_nonneg hLoc_bd'

end UnforcedLeray.Short.IIb

end
