import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.Anisotropy.StressDefect

/-!
# Part III-a, `PartIII-a:T22/7`: Stress defect and anisotropy (`eq:ct-stress-defect`, `eq:ct-anisotropy`)

Source of record: `the November 2 reference manuscript` (SP), lines 3380-3404.

Proves `ctAnisotropyPair : CTStressDefect ∧ CTAnisotropy` and its projections `ctStressDefect`
and `ctAnisotropy`. Helper sections §1–§4 are factored into
`Anisotropy/{SymAndPlanar,CompactWindow,StressDefect}.lean` under `AnisoSynthAux`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff Interval InnerProductSpace ComplexConjugate SchwartzMap

namespace UnforcedLeray.Short.IIIa

open AnisoSynthAux

/-! ## 5. Unforced quadrupole law, Fubini integration by parts, and `CTAnisotropy` -/

private lemma integrable_inv_jb_plane_aniso {m : ℝ} (hm : 1 < m) :
    Integrable (fun x : ℝ × ℝ => (1 + ‖x‖ ^ 2) ^ (-m)) volume := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by simp
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume)
    (r := 2 * m) (by rw [hd]; linarith)
  convert h using 1
  funext x; congr 1; ring

private lemma cellL1_le_xNorm_aniso {m : ℝ} (hm : 1 < m) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (c : ℝ) (f : ℝ × ℝ → ℂ), MemLp f 2 (B0579.cellMeasure c m) →
      ∫ x in B0579.cell c, ‖f x‖ ≤ K₁ * (xNorm c m f).toReal := by
  set I₀ : ℝ≥0∞ := ∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-m))
  have hI₀_ne : I₀ ≠ ⊤ := (integrable_inv_jb_plane_aniso hm).lintegral_lt_top.ne
  refine ⟨I₀.toReal ^ (1 / 2 : ℝ), by positivity, fun c f hf => ?_⟩
  have hf_int : IntegrableOn f (B0579.cell c) := integrableOn_cell_of_memX hm hf
  have hF : AEMeasurable (fun x : ℝ × ℝ => (ENNReal.ofReal (B0579.jb x ^ m))⁻¹)
      (B0579.cellMeasure c m) :=
    ((B0579.continuous_jb_rpow m).measurable.ennreal_ofReal.inv).aemeasurable
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure c m)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hF hf.aestronglyMeasurable.enorm
  simp only [ENNReal.rpow_two] at hCS
  have hwt_le : ∀ x : ℝ × ℝ,
      ENNReal.ofReal (B0579.jb x ^ m) * ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹) ^ 2 ≤
        ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-m)) := by
    intro x
    have hA : 0 < B0579.jb x ^ m := Real.rpow_pos_of_pos (B0579.jb_pos x) m
    have hq0 : 0 < 1 + ‖x‖ ^ 2 := by positivity
    have hn : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
      rw [Prod.norm_def]
      rcases max_choice ‖x.1‖ ‖x.2‖ with h | h <;> rw [h, Real.norm_eq_abs, sq_abs] <;>
        nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hqjb : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by unfold B0579.jb; linarith
    have hreal : B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹) ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ (-m) := by
      have he : B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹) ^ 2 = (B0579.jb x ^ m)⁻¹ := by
        field_simp [hA.ne']
      rw [he, Real.rpow_neg hq0.le]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hq0.le hqjb (by linarith))
    rw [← ENNReal.ofReal_inv_of_pos hA, ← ENNReal.ofReal_pow (inv_nonneg.2 hA.le),
      ← ENNReal.ofReal_mul hA.le]
    exact ENNReal.ofReal_le_ofReal hreal
  have hsq : ∫⁻ x, ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹) ^ 2 ∂(B0579.cellMeasure c m) ≤ I₀ := by
    rw [CTE.QuadQBoundProof.lintegral_cellMeasure_eq]
    exact (lintegral_mono hwt_le).trans (setLIntegral_le_lintegral _ _)
  have hlint : ∫⁻ x in B0579.cell c, ‖f x‖ₑ ≤ I₀ ^ (1 / 2 : ℝ) * xNorm c m f := by
    rw [CTE.QuadQBoundProof.lintegral_cell_eq c m]
    refine hCS.trans ?_
    rw [← CTE.QuadQBoundProof.eLpNorm_two_eq]
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hsq (by norm_num)) bot_le
  have heq : ENNReal.ofReal (∫ x in B0579.cell c, ‖f x‖) = ∫⁻ x in B0579.cell c, ‖f x‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hf_int.norm (Eventually.of_forall fun _ => norm_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm]
  have hx_ne : xNorm c m f ≠ ⊤ := hf.2.ne
  have hrhs : I₀ ^ (1 / 2 : ℝ) * xNorm c m f =
      ENNReal.ofReal (I₀.toReal ^ (1 / 2 : ℝ) * (xNorm c m f).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hI₀_ne, ENNReal.ofReal_toReal hx_ne]
  rw [← heq, hrhs] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlint

private lemma contDiff_deriv_real_aniso {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (deriv g) := by
  unfold deriv
  exact ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

private lemma isCylTest_of_snd_aniso {c : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hband : ∃ R : ℝ, ∀ y : ℝ, R < |y| → g y = 0) :
    B0579.IsCylTest c (fun x => g x.2) ∧
      (∀ x : ℝ × ℝ, B0579.pd 0 (fun z => g z.2) x = 0) ∧
      (∀ x : ℝ × ℝ, B0579.pd 1 (fun z => g z.2) x = deriv g x.2) := by
  obtain ⟨R, hR⟩ := hband
  have htest : B0579.IsCylTest c (fun x => g x.2) :=
    ⟨hg.comp contDiff_snd, fun _ => rfl, ⟨R, fun x hx => hR x.2 hx⟩⟩
  have hfderiv : ∀ x : ℝ × ℝ,
      HasFDerivAt (fun z : ℝ × ℝ => g z.2)
        (deriv g x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := fun x =>
    ((hg.differentiable (by simp) x.2).hasDerivAt).comp_hasFDerivAt x hasFDerivAt_snd
  refine ⟨htest, fun x => ?_, fun x => ?_⟩
  · unfold B0579.pd; rw [(hfderiv x).fderiv]; simp [B0579.dir]
  · unfold B0579.pd; rw [(hfderiv x).fderiv]; simp [B0579.dir]

private lemma lapP_of_snd_aniso {c : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hband : ∃ R : ℝ, ∀ y : ℝ, R < |y| → g y = 0) :
    B0579.IsCylTest c (fun x => deriv g x.2) ∧
      B0579.IsCylTest c (fun x => deriv (deriv g) x.2) ∧
      ∀ x : ℝ × ℝ, lapP (fun z => g z.2) x = deriv (deriv g) x.2 := by
  obtain ⟨_, hpd0, hpd1⟩ := isCylTest_of_snd_aniso (c := c) hg hband
  obtain ⟨R, hR⟩ := hband
  have hband1 : ∃ R₁ : ℝ, ∀ y : ℝ, R₁ < |y| → deriv g y = 0 := by
    refine ⟨R, fun y hy => ?_⟩
    have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hR z hz
    rw [hev.deriv_eq, deriv_const]
  have hband2 : ∃ R₂ : ℝ, ∀ y : ℝ, R₂ < |y| → deriv (deriv g) y = 0 := by
    obtain ⟨R₁, hR1⟩ := hband1
    refine ⟨R₁, fun y hy => ?_⟩
    have hev : deriv g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hR1 z hz
    rw [hev.deriv_eq, deriv_const]
  have hg1 := contDiff_deriv_real_aniso hg
  have hg2 := contDiff_deriv_real_aniso hg1
  obtain ⟨htest1, _, hpd11⟩ := isCylTest_of_snd_aniso (c := c) hg1 hband1
  obtain ⟨htest2, _, _⟩ := isCylTest_of_snd_aniso (c := c) hg2 hband2
  refine ⟨htest1, htest2, fun x => ?_⟩
  unfold lapP
  have heq0 : B0579.pd 0 (fun z => g z.2) = fun _ => (0 : ℝ) := funext hpd0
  have heq1 : B0579.pd 1 (fun z => g z.2) = fun z => deriv g z.2 := funext hpd1
  rw [heq0, heq1, hpd11 x]
  have h00 : B0579.pd 0 (fun _ : ℝ × ℝ => (0 : ℝ)) x = 0 := by unfold B0579.pd; simp
  rw [h00, zero_add]

private lemma flowIntegrand_snd_identity_aniso {ν c τ : ℝ} (hτ : 0 ≤ τ)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    {om : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hom : MemLp om 2 (volume.restrict (B0579.cell c)))
    (hu : IsBiotSavart c om u)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hband : ∃ R : ℝ, ∀ y : ℝ, R < |y| → g y = 0) :
    ∫ x in B0579.cell c, flowIntegrand tr om u τ (fun z => g z.2) x =
      (ν : ℂ) * (∫ x in B0579.cell c, om x * ((deriv (deriv g) x.2 : ℝ) : ℂ)) +
        ∫ x in B0579.cell c,
          ((tr.v τ x 0 : ℂ) * u x 1 + (tr.v τ x 1 : ℂ) * u x 0) *
            ((deriv (deriv g) x.2 : ℝ) : ℂ) := by
  set φ : ℝ × ℝ → ℝ := fun z => g z.2
  set dg : ℝ × ℝ → ℝ := fun z => deriv g z.2
  set ddg : ℝ × ℝ → ℝ := fun z => deriv (deriv g) z.2
  obtain ⟨hφ, hφ0, hφ1⟩ := isCylTest_of_snd_aniso (c := c) hg hband
  obtain ⟨hdg, hddg, hlap⟩ := lapP_of_snd_aniso (c := c) hg hband
  obtain ⟨_, hdg0, hdg1⟩ := isCylTest_of_snd_aniso (c := c) (contDiff_deriv_real_aniso hg) (by
    obtain ⟨R, hR⟩ := hband
    refine ⟨R, fun y hy => ?_⟩
    have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hR z hz
    rw [hev.deriv_eq, deriv_const])
  set ψ₁ : ℝ × ℝ → ℝ := fun x => V1.vC tr τ 1 x * dg x
  set ψ₂a : ℝ × ℝ → ℝ := fun x => V1.vC tr τ 0 x * dg x
  set ψ₂b : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0238.Ec tr τ x * φ x
  set ψ₂ : ℝ × ℝ → ℝ := fun x => ψ₂a x + ψ₂b x
  have hψ₁ : B0579.IsCylTest c ψ₁ :=
    V1.cylTest_mul_left (V1.vC_contDiff tr hτ 1) (V1.vC_periodic tr hτ 1) hdg
  have hψ₂a : B0579.IsCylTest c ψ₂a :=
    V1.cylTest_mul_left (V1.vC_contDiff tr hτ 0) (V1.vC_periodic tr hτ 0) hdg
  have hψ₂b : B0579.IsCylTest c ψ₂b :=
    V1.cylTest_mul_left (V1.Ec_contDiff tr hτ) (V1.Ec_periodic tr hτ) hφ
  have hψ₂ : B0579.IsCylTest c ψ₂ := V1.cylTest_add hψ₂a hψ₂b
  have hec_test : ∀ j : Fin 2,
      B0579.IsCylTest c (fun x => B0579.pd j (UnforcedLeray.B0238.Ec tr τ) x * φ x) := fun j =>
    V1.cylTest_mul_left (V1.pdE_contDiff tr hτ j)
      (fun x => by
        have hEc_diff : Differentiable ℝ (UnforcedLeray.B0238.Ec tr τ) :=
          (V1.Ec_contDiff tr hτ).differentiable (by simp)
        have hT : UnforcedLeray.B0238.Ec tr τ ∘ (fun y : ℝ × ℝ => (y.1 + c, y.2)) =
            UnforcedLeray.B0238.Ec tr τ := funext (V1.Ec_periodic tr hτ)
        have hS : HasFDerivAt (fun y : ℝ × ℝ => (y.1 + c, y.2))
            (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
          have : (fun y : ℝ × ℝ => (y.1 + c, y.2)) = fun y => y + ((c, 0) : ℝ × ℝ) := by
            funext y; ext <;> simp
          rw [this]; exact (hasFDerivAt_id x).add_const _
        have hc_fd := (hEc_diff (x.1 + c, x.2)).hasFDerivAt.comp x hS
        rw [hT] at hc_fd
        simp only [B0579.pd]; rw [hc_fd.fderiv]; rfl) hφ
  have hint_visc : IntegrableOn (fun x => (ν : ℂ) * (om x * (ddg x : ℂ))) (B0579.cell c) :=
    (CoreDuhamelRepSub.integrableOn_cylTest_mul hddg hom).const_mul _
  have hint_adv : IntegrableOn (fun x => om x * (ψ₁ x : ℂ)) (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul hψ₁ hom
  have hint_ec0 : IntegrableOn
      (fun x => u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul (hec_test 0) (hu.1 0)
  have hint_ec1 : IntegrableOn
      (fun x => u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul (hec_test 1) (hu.1 1)
  have hint_ec : IntegrableOn
      (fun x => u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
        u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      (B0579.cell c) := hint_ec0.add hint_ec1
  have hint_rest : IntegrableOn
      (fun x => om x * (ψ₁ x : ℂ) -
        (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
          u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ)))
      (B0579.cell c) := hint_adv.sub hint_ec
  have hflow_pt : ∀ x : ℝ × ℝ,
      flowIntegrand tr om u τ φ x =
        (ν : ℂ) * (om x * (ddg x : ℂ)) +
          (om x * (ψ₁ x : ℂ) -
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))) := by
    intro x
    unfold flowIntegrand
    rw [hlap x, hφ0 x, hφ1 x]
    dsimp only [ψ₁, V1.vC, dg, ddg, φ]
    push_cast; ring
  rw [integral_congr_ae (Eventually.of_forall hflow_pt),
    integral_add hint_visc hint_rest,
    integral_const_mul, integral_sub hint_adv hint_ec,
    hu.2.2 ψ₁ hψ₁]
  congr 1
  have hint_curl : IntegrableOn
      (fun x => u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ))
      (B0579.cell c) :=
    (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₁.pd 1) (hu.1 0)).sub
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₁.pd 0) (hu.1 1))
  have hint_curl_sub : IntegrableOn
      (fun x => (u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ)) -
        (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
          u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ)))
      (B0579.cell c) := hint_curl.sub hint_ec
  have hint_div : IntegrableOn
      (fun x => u x 0 * (B0579.pd 0 ψ₂ x : ℂ) + u x 1 * (B0579.pd 1 ψ₂ x : ℂ))
      (B0579.cell c) :=
    (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₂.pd 0) (hu.1 0)).add
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₂.pd 1) (hu.1 1))
  have hdiv_zero := hu.2.1 ψ₂ hψ₂
  calc (∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ))) -
          ∫ x in B0579.cell c,
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      = (∫ x in B0579.cell c,
          ((u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ)) -
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ)))) +
          ∫ x in B0579.cell c,
            (u x 0 * (B0579.pd 0 ψ₂ x : ℂ) + u x 1 * (B0579.pd 1 ψ₂ x : ℂ)) := by
        rw [hdiv_zero, add_zero, ← integral_sub hint_curl hint_ec]
    _ = ∫ x in B0579.cell c,
          (((u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ)) -
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))) +
            (u x 0 * (B0579.pd 0 ψ₂ x : ℂ) + u x 1 * (B0579.pd 1 ψ₂ x : ℂ))) := by
        rw [← integral_add hint_curl_sub hint_div]
    _ = ∫ x in B0579.cell c,
          ((tr.v τ x 0 : ℂ) * u x 1 + (tr.v τ x 1 : ℂ) * u x 0) * (ddg x : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have hEc_diff : Differentiable ℝ (UnforcedLeray.B0238.Ec tr τ) :=
          (V1.Ec_contDiff tr hτ).differentiable (by simp)
        have hp10 : B0579.pd 0 ψ₁ x = B0579.pd 0 (V1.vC tr τ 1) x * dg x := by
          rw [V1.pd_mul' (V1.vC_diff tr hτ 1) hdg.differentiable 0 x, hdg0 x, mul_zero, add_zero]
        have hp11 : B0579.pd 1 ψ₁ x =
            B0579.pd 1 (V1.vC tr τ 1) x * dg x + V1.vC tr τ 1 x * ddg x := by
          rw [V1.pd_mul' (V1.vC_diff tr hτ 1) hdg.differentiable 1 x, hdg1 x]
        have hp20 : B0579.pd 0 ψ₂ x =
            B0579.pd 0 (V1.vC tr τ 0) x * dg x +
              B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x := by
          rw [V1.pd_add hψ₂a.differentiable.differentiableAt hψ₂b.differentiable.differentiableAt 0,
            V1.pd_mul' (V1.vC_diff tr hτ 0) hdg.differentiable 0 x,
            V1.pd_mul' hEc_diff hφ.differentiable 0 x, hdg0 x, hφ0 x]
          ring
        have hp21 : B0579.pd 1 ψ₂ x =
            B0579.pd 1 (V1.vC tr τ 0) x * dg x + V1.vC tr τ 0 x * ddg x +
              B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x +
              UnforcedLeray.B0238.Ec tr τ x * dg x := by
          rw [V1.pd_add hψ₂a.differentiable.differentiableAt hψ₂b.differentiable.differentiableAt 1,
            V1.pd_mul' (V1.vC_diff tr hτ 0) hdg.differentiable 1 x,
            V1.pd_mul' hEc_diff hφ.differentiable 1 x, hdg1 x, hφ1 x]
          ring
        have hdiv_v : B0579.pd 0 (V1.vC tr τ 0) x = -B0579.pd 1 (V1.vC tr τ 1) x := by
          linarith [V1.vC_div tr hτ x]
        have hcurl_v : UnforcedLeray.B0238.Ec tr τ x =
            B0579.pd 0 (V1.vC tr τ 1) x - B0579.pd 1 (V1.vC tr τ 0) x :=
          congrFun (V1.Ec_eq tr hτ) x
        dsimp only
        rw [hp10, hp11, hp20, hp21, hdiv_v, hcurl_v]
        dsimp only [V1.vC]
        push_cast; ring

private def psi0Aniso (y : ℝ) : ℝ := y ^ 2 * B0285.chi0 y

private def quadCut1Aniso (n : ℕ) (y : ℝ) : ℝ := y ^ 2 * B0285.chi0 (((n : ℝ) + 1)⁻¹ * y)

private lemma quadCut1Aniso_properties :
    (∀ n : ℕ, ContDiff ℝ ∞ (quadCut1Aniso n)) ∧
    (∀ n : ℕ, ∃ R : ℝ, ∀ y : ℝ, R < |y| → quadCut1Aniso n y = 0) ∧
    (∀ (n : ℕ) (x : ℝ × ℝ), quadCut1Aniso n x.2 = x.2 ^ 2 * B0285.cutT n x) ∧
    (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ (n : ℕ) (y : ℝ), |deriv (deriv (quadCut1Aniso n)) y| ≤ M₂) ∧
    (∀ y : ℝ, ∀ᶠ n : ℕ in atTop, deriv (deriv (quadCut1Aniso n)) y = 2) := by
  have hpsi_smooth : ContDiff ℝ ∞ psi0Aniso := (contDiff_id.pow 2).mul B0285.chi0.contDiff
  have hpsi_supp : ∀ y : ℝ, 2 < |y| → psi0Aniso y = 0 := by
    intro y hy
    unfold psi0Aniso
    have h0 : B0285.chi0 y = 0 := by
      apply B0285.chi0.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]; exact hy.le
    rw [h0, mul_zero]
  have hdpsi_smooth : ContDiff ℝ ∞ (deriv psi0Aniso) := contDiff_deriv_real_aniso hpsi_smooth
  have hddpsi_smooth : ContDiff ℝ ∞ (deriv (deriv psi0Aniso)) :=
    contDiff_deriv_real_aniso hdpsi_smooth
  have hddpsi_supp : ∀ y : ℝ, 2 < |y| → deriv (deriv psi0Aniso) y = 0 := by
    intro y hy
    have hev1 : ∀ z : ℝ, 2 < |z| → deriv psi0Aniso z = 0 := by
      intro z hz
      have hev : psi0Aniso =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hz] with w hw
        exact hpsi_supp w hw
      rw [hev.deriv_eq, deriv_const]
    have hev2 : deriv psi0Aniso =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hev1 z hz
    rw [hev2.deriv_eq, deriv_const]
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hddpsi_smooth.continuous.continuousOn
  set M₂ : ℝ := max M₀ 2
  have hM₂_nn : 0 ≤ M₂ := by positivity
  have hddpsi_bd : ∀ y : ℝ, |deriv (deriv psi0Aniso) y| ≤ M₂ := by
    intro y
    by_cases hy : y ∈ Icc (-2 : ℝ) 2
    · exact (Real.norm_eq_abs _ ▸ hM₀ y hy).trans (le_max_left _ _)
    · have hy' : 2 < |y| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hddpsi_supp y hy', abs_zero]; exact hM₂_nn
  have hddpsi_ball : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv (deriv psi0Aniso) y = 2 := by
    have hval : ∀ z ∈ Ioo (-1 : ℝ) 1, psi0Aniso z = z ^ 2 := by
      intro z hz
      unfold psi0Aniso
      have h1 : B0285.chi0 z = 1 := by
        apply B0285.chi0.one_of_mem_closedBall
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
        exact ⟨hz.1.le, hz.2.le⟩
      rw [h1, mul_one]
    have hdval : ∀ z ∈ Ioo (-1 : ℝ) 1, deriv psi0Aniso z = 2 * z := by
      intro z hz
      have hev : psi0Aniso =ᶠ[𝓝 z] fun w : ℝ => w ^ 2 := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
        exact hval w hw
      rw [hev.deriv_eq,
        ((hasDerivAt_pow 2 z).congr_deriv (by ring : (2 : ℕ) * z ^ (2 - 1) = 2 * z)).deriv]
    intro y hy
    have hev : deriv psi0Aniso =ᶠ[𝓝 y] fun z : ℝ => 2 * z := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact hdval z hz
    rw [hev.deriv_eq, (((hasDerivAt_id' y).const_mul (2 : ℝ)).congr_deriv (mul_one 2)).deriv]
  have hscale_eq : ∀ (n : ℕ) (y : ℝ),
      quadCut1Aniso n y = ((n : ℝ) + 1) ^ 2 * psi0Aniso (((n : ℝ) + 1)⁻¹ * y) := by
    intro n y
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    unfold quadCut1Aniso psi0Aniso; field_simp [hpos.ne']
  have hdd_scale : ∀ (n : ℕ) (y : ℝ),
      deriv (deriv (quadCut1Aniso n)) y = deriv (deriv psi0Aniso) (((n : ℝ) + 1)⁻¹ * y) := by
    intro n y
    set R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by positivity
    have hd1 : deriv (quadCut1Aniso n) = fun z : ℝ => R * deriv psi0Aniso (R⁻¹ * z) := by
      funext z
      have hfn : quadCut1Aniso n = fun w : ℝ => R ^ 2 * psi0Aniso (R⁻¹ * w) := funext (hscale_eq n)
      rw [hfn]
      have h_in : HasDerivAt (fun w : ℝ => R⁻¹ * w) R⁻¹ z :=
        ((hasDerivAt_id' z).const_mul R⁻¹).congr_deriv (mul_one R⁻¹)
      have h_out : HasDerivAt psi0Aniso (deriv psi0Aniso (R⁻¹ * z)) (R⁻¹ * z) :=
        (hpsi_smooth.differentiable (by simp) _).hasDerivAt
      exact (((h_out.comp z h_in).const_mul (R ^ 2)).congr_deriv (by field_simp [hR.ne'])).deriv
    rw [hd1]
    have h_in : HasDerivAt (fun w : ℝ => R⁻¹ * w) R⁻¹ y :=
      ((hasDerivAt_id' y).const_mul R⁻¹).congr_deriv (mul_one R⁻¹)
    have h_out : HasDerivAt (deriv psi0Aniso) (deriv (deriv psi0Aniso) (R⁻¹ * y)) (R⁻¹ * y) :=
      (hdpsi_smooth.differentiable (by simp) _).hasDerivAt
    exact (((h_out.comp y h_in).const_mul R).congr_deriv (by field_simp [hR.ne'])).deriv
  refine ⟨?_, ?_, fun _ _ => rfl, ⟨M₂, hM₂_nn, fun n y => ?_⟩, fun y => ?_⟩
  · intro n
    rw [funext (hscale_eq n)]
    exact contDiff_const.mul (hpsi_smooth.comp (contDiff_const.mul contDiff_id))
  · intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine ⟨2 * ((n : ℝ) + 1), fun y hy => ?_⟩
    rw [hscale_eq n y, hpsi_supp]
    · simp
    · rw [abs_mul, abs_inv, abs_of_pos hpos, lt_inv_mul_iff₀ hpos]; linarith
  · rw [hdd_scale n y]; exact hddpsi_bd _
  · refine (eventually_ge_atTop ⌈|y|⌉₊).mono fun n hn => ?_
    rw [hdd_scale n y]
    apply hddpsi_ball
    have hn' : |y| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have habs : |((n : ℝ) + 1)⁻¹ * y| < 1 := by
      rw [abs_mul, abs_inv, abs_of_pos hpos, inv_mul_lt_iff₀ hpos]; linarith
    exact abs_lt.1 habs

private lemma xNorm_toReal_bounded_on_Icc_aniso {ν c m t s₁ : ℝ} (_hts₁ : t ≤ s₁)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t f w u) :
    ∃ B_w : ℝ, 0 ≤ B_w ∧ ∀ τ ∈ Icc t s₁, (xNorm c m (w τ)).toReal ≤ B_w := by
  have hcont : ContinuousOn (fun τ => (xNorm c m (w τ)).toReal) (Ici t) := by
    intro s hs
    rw [ContinuousWithinAt]
    have hlim : Tendsto (fun s' => (xNorm c m (w s' - w s)).toReal) (𝓝[Ici t] s)
        (𝓝 (0 : ℝ≥0∞).toReal) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hw.strongCont s hs)
    rw [ENNReal.toReal_zero] at hlim
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [self_mem_nhdsWithin, (Metric.tendsto_nhds.1 hlim) ε hε] with s' hs' hd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hd
    rw [Real.dist_eq]
    have hmem_s := hw.memX s hs
    have hmem_s' := hw.memX s' hs'
    have hsub_mem : MemLp (w s' - w s) 2 (B0579.cellMeasure c m) := hmem_s'.sub hmem_s
    have hle1 : (xNorm c m (w s')).toReal - (xNorm c m (w s)).toReal ≤
        (xNorm c m (w s' - w s)).toReal := by
      have heq : w s' = (w s' - w s) + w s := by ext x; simp
      have htri : xNorm c m (w s') ≤ xNorm c m (w s' - w s) + xNorm c m (w s) := by
        unfold xNorm; conv_lhs => rw [heq]
        exact eLpNorm_add_le hsub_mem.1 hmem_s.1 one_le_two
      have htr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsub_mem.2.ne, hmem_s.2.ne⟩) htri
      rw [ENNReal.toReal_add hsub_mem.2.ne hmem_s.2.ne] at htr
      unfold xNorm at *; linarith
    have hle2 : (xNorm c m (w s)).toReal - (xNorm c m (w s')).toReal ≤
        (xNorm c m (w s' - w s)).toReal := by
      have heq : w s = w s' - (w s' - w s) := by ext x; simp
      have htri : xNorm c m (w s) ≤ xNorm c m (w s') + xNorm c m (w s' - w s) := by
        unfold xNorm; conv_lhs => rw [heq]
        exact eLpNorm_sub_le hmem_s'.1 hsub_mem.1 one_le_two
      have htr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmem_s'.2.ne, hsub_mem.2.ne⟩) htri
      rw [ENNReal.toReal_add hmem_s'.2.ne hsub_mem.2.ne] at htr
      unfold xNorm at *; linarith
    exact (abs_sub_le_iff.2 ⟨hle1, hle2⟩).trans_lt hd
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := t) (b := s₁)).exists_bound_of_continuousOn
    (hcont.mono Icc_subset_Ici_self)
  refine ⟨max M₀ 0, le_max_right _ _, fun τ hτ => ?_⟩
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM₀ τ hτ).trans (le_max_left _ _))

private def qScaled (c : ℝ) (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) : ℂ :=
  (1 / (2 * (c : ℂ))) * ∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s x

private def cRaw {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (τ : ℝ) : ℂ :=
  (1 / (c : ℂ)) * ∫ x in B0579.cell c,
    (((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1 + ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0)

private lemma aPlus_eq_cpow_mul_qScaled {ν : ℝ} (hν : 0 < ν) (μ : ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (s : ℝ) :
    aPlus ν μ w s = (s : ℂ) ^ (-μ) * qScaled (ν ^ (-2 : ℝ)) w s := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hc : ((ν ^ (-2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hν _).ne'
  unfold aPlus quadQ qScaled
  push_cast
  field_simp [hpi, hc]
  ring

private lemma pairC_eq_cpow_mul_cRaw {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (τ : ℝ) :
    pairC tr μ (u τ) τ = (τ : ℂ) ^ (-μ) * cRaw tr u τ := by
  unfold pairC cRaw
  have hpt : (fun x : ℝ × ℝ =>
        ((tr.v τ x 0 : ℝ) : ℂ) * ((τ : ℂ) ^ (-μ) * u τ x 1) +
          ((tr.v τ x 1 : ℝ) : ℂ) * ((τ : ℂ) ^ (-μ) * u τ x 0)) =
      fun x => (τ : ℂ) ^ (-μ) *
        (((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1 + ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0) := by
    funext x; ring
  rw [hpt, integral_const_mul]; ring

/-- Unforced quadrupole evolution law on `[s₁, s₂]` (`0 ≤ s₁ ≤ s₂`). -/
private lemma qScaled_sub_eq_integral_cRaw
    {ν c m C_L2 : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c) (hm : 8 < m) (hC_L2 : 0 < C_L2)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hv_bd : ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal C_L2)
    {f : ℝ × ℝ → ℂ} (hf_zc : HasZeroCirculation c f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr 0 f w u)
    (hw_ev : ∀ s : ℝ, IsCentrallyEven (w s))
    {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs12 : s₁ ≤ s₂) :
    qScaled c w s₂ - qScaled c w s₁ = ∫ τ in Ioc s₁ s₂, cRaw tr u τ := by
  have hc_pos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc_pos.ne'
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K₁, hK₁_nn, hCellL1⟩ := cellL1_le_xNorm_aniso (m := m) (by linarith)
  obtain ⟨hg_smooth, hg_band, hg_cut, ⟨M₂, hM₂_nn, hg_dd_bd⟩, hg_dd_ev⟩ := quadCut1Aniso_properties
  have hw_res : IsLinearisedFlow ν c m tr s₁ (w s₁) w u := hw.restart hs₁
  obtain ⟨B_w, hB_w_nn, hB_w⟩ := xNorm_toReal_bounded_on_Icc_aniso hs12 hw_res
  set φ_seq : ℕ → ℝ × ℝ → ℝ := fun n x => quadCut1Aniso n x.2
  have hφ_test : ∀ n : ℕ, B0579.IsCylTest c (φ_seq n) :=
    fun n => (isCylTest_of_snd_aniso (c := c) (hg_smooth n) (hg_band n)).1
  set G_seq : ℕ → ℝ → ℂ := fun n τ =>
    ∫ x in B0579.cell c, flowIntegrand tr (w τ) (u τ) τ (φ_seq n) x
  set M_dom : ℝ := ν * (M₂ * (K₁ * B_w)) + M₂ * (2 * C_L2 * (C_emb * B_w))
  have hG_dom_and_lim : ∀ τ ∈ Icc s₁ s₂,
      (∀ n : ℕ, ‖G_seq n τ‖ ≤ M_dom) ∧
        Tendsto (fun n : ℕ => G_seq n τ) atTop (𝓝 (2 * (c : ℂ) * cRaw tr u τ)) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hs₁.trans hτ.1
    have hw_τ_mem := hw.memX τ hτ0
    have hw_τ_l2 : MemLp (w τ) 2 (volume.restrict (B0579.cell c)) :=
      memLp_vol_of_cellMeasure (by linarith) hw_τ_mem
    have hw_τ_int : IntegrableOn (w τ) (B0579.cell c) :=
      integrableOn_cell_of_memX (by linarith) hw_τ_mem
    have hw_τ_zc : HasZeroCirculation c (w τ) :=
      zeroCirculationPreserved ν c m hc_pos (by linarith) tr 0 f w u hw hf_zc τ hτ0
    have hv_τ_fin : UnforcedLeray.Train.cellL2 c (tr.v τ) < ⊤ :=
      lt_of_le_of_lt (hv_bd τ hτ0) ENNReal.ofReal_lt_top
    have hv0_mem := memLp_train_coord_of_cellL2 hτ0 tr hv_τ_fin 0
    have hv1_mem := memLp_train_coord_of_cellL2 hτ0 tr hv_τ_fin 1
    -- Bound `eLpNorm (u τ · j) 2` via `ctEmbeddings`
    have hemb_τ : velNorm c (u τ) ≤ ENNReal.ofReal C_emb * xNorm c m (w τ) :=
      (le_add_self.trans (hEmb0 c hc1 (w τ) hw_τ_mem hw_τ_zc (hw_ev τ) (u τ)
        (hw.biotSavart τ hτ0))).trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C_emb0 1)) bot_le)
    have hu_toReal : ∀ j : Fin 2,
        (eLpNorm (fun x => u τ x j) 2 (volume.restrict (B0579.cell c))).toReal ≤ C_emb * B_w := by
      intro j
      have hrhs_ne : ENNReal.ofReal C_emb * xNorm c m (w τ) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw_τ_mem.2.ne
      have h1 := ENNReal.toReal_mono hrhs_ne ((eLpNorm_coord_le_velNorm (u τ) j).trans hemb_τ)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_emb.le] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hB_w τ hτ) hC_emb.le)
    set F_v : ℝ × ℝ → ℂ := fun x =>
      ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1 + ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0
    have hFv0_int : IntegrableOn (fun x => ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1) (B0579.cell c) :=
      hv0_mem.1.ofReal.integrable_mul ((hw.biotSavart τ hτ0).1 1)
    have hFv1_int : IntegrableOn (fun x => ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0) (B0579.cell c) :=
      hv1_mem.1.ofReal.integrable_mul ((hw.biotSavart τ hτ0).1 0)
    have hFv_int : IntegrableOn F_v (B0579.cell c) := hFv0_int.add hFv1_int
    have hG_eq : ∀ n : ℕ, G_seq n τ =
        (ν : ℂ) * (∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ) :=
      fun n => flowIntegrand_snd_identity_aniso hτ0 tr hw_τ_l2 (hw.biotSavart τ hτ0)
        (hg_smooth n) (hg_band n)
    constructor
    · intro n
      rw [hG_eq n]
      have hvisc_le :
          ‖(ν : ℂ) *
              ∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ)‖ ≤
            ν * (M₂ * (K₁ * B_w)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν.le]
        refine mul_le_mul_of_nonneg_left ?_ hν.le
        have h1 : ‖∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ)‖ ≤
            ∫ x in B0579.cell c, M₂ * ‖w τ x‖ := by
          refine (norm_integral_le_integral_norm _).trans
            (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hw_τ_int.norm.const_mul M₂) (Eventually.of_forall fun x => ?_))
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)
        rw [integral_const_mul] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left
          ((hCellL1 c (w τ) hw_τ_mem).trans (mul_le_mul_of_nonneg_left (hB_w τ hτ) hK₁_nn))
          hM₂_nn)
      have hadv_le :
          ‖∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ)‖ ≤
            M₂ * (2 * C_L2 * (C_emb * B_w)) := by
        have h1 : ‖∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ)‖ ≤
            M₂ * ∫ x in B0579.cell c,
              (‖((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1‖ + ‖((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0‖) := by
          rw [← integral_const_mul]
          refine (norm_integral_le_integral_norm _).trans
            (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((hFv0_int.norm.add hFv1_int.norm).const_mul M₂) (Eventually.of_forall fun x => ?_))
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact (mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (norm_add_le _ _) hM₂_nn)
        have hcs_pair : ∀ (i j : Fin 2),
            ∫ x in B0579.cell c, ‖((tr.v τ x i : ℝ) : ℂ) * u τ x j‖ ≤
              C_L2 * (C_emb * B_w) := fun i j => by
          let μ_c := volume.restrict (B0579.cell c)
          have hvi := memLp_train_coord_of_cellL2 hτ0 tr hv_τ_fin i
          have huj := (hw.biotSavart τ hτ0).1 j
          have hvi' : MemLp (fun x => tr.v τ x i) (ENNReal.ofReal 2) μ_c := by
            rw [ENNReal.ofReal_ofNat]; exact hvi.1
          have huj' : MemLp (fun x => ‖u τ x j‖) (ENNReal.ofReal 2) μ_c := by
            rw [ENNReal.ofReal_ofNat]; exact huj.norm
          have hle : ∫ x, ‖((tr.v τ x i : ℝ) : ℂ) * u τ x j‖ ∂μ_c ≤
              (eLpNorm (fun x => tr.v τ x i) 2 μ_c).toReal *
                (eLpNorm (fun x => u τ x j) 2 μ_c).toReal := by
            calc ∫ x, ‖((tr.v τ x i : ℝ) : ℂ) * u τ x j‖ ∂μ_c
                = ∫ x, ‖tr.v τ x i‖ * ‖‖u τ x j‖‖ ∂μ_c := by
                  simp only [norm_mul, Complex.norm_real, norm_norm]
              _ ≤ (∫ x, ‖tr.v τ x i‖ ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) *
                    (∫ x, ‖‖u τ x j‖‖ ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) :=
                  integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hvi' huj'
              _ = (eLpNorm (fun x => tr.v τ x i) 2 μ_c).toReal *
                    (eLpNorm (fun x => u τ x j) 2 μ_c).toReal := by
                  simp only [norm_norm]
                  rw [← eLpNorm_two_sq_eq_integral_norm_sq hvi.1,
                    ← eLpNorm_two_sq_eq_integral_norm_sq huj]
          exact hle.trans (mul_le_mul
            (ENNReal.toReal_le_of_le_ofReal hC_L2.le (hvi.2.trans (hv_bd τ hτ0)))
            (hu_toReal j) ENNReal.toReal_nonneg hC_L2.le)
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hM₂_nn)
        rw [integral_add hFv0_int.norm hFv1_int.norm]
        linarith [hcs_pair 0 1, hcs_pair 1 0]
      exact (norm_add_le _ _).trans (add_le_add hvisc_le hadv_le)
    · have hlim_visc : Tendsto
          (fun n : ℕ =>
            ∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ))
          atTop (𝓝 0) := by
        have h1 : Tendsto
            (fun n : ℕ =>
              ∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ))
            atTop (𝓝 (∫ x in B0579.cell c, w τ x * (2 : ℂ))) := by
          refine tendsto_integral_of_dominated_convergence (fun x => M₂ * ‖w τ x‖)
            (fun n => hw_τ_int.aestronglyMeasurable.mul
              (Complex.continuous_ofReal.comp
                (lapP_of_snd_aniso (c := c) (hg_smooth n) (hg_band n)).2.1.continuous).aestronglyMeasurable)
            (hw_τ_int.norm.const_mul M₂)
            (fun n => Eventually.of_forall fun x => ?_)
            (Eventually.of_forall fun x => ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)
          · refine tendsto_const_nhds.congr' ?_
            filter_upwards [hg_dd_ev x.2] with n hn
            rw [hn]; norm_num
        rw [integral_mul_const, hw_τ_zc.2, zero_mul] at h1
        exact h1
      have hlim_adv : Tendsto
          (fun n : ℕ =>
            ∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ))
          atTop (𝓝 (2 * (c : ℂ) * cRaw tr u τ)) := by
        have h1 : Tendsto
            (fun n : ℕ =>
              ∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1Aniso n)) x.2 : ℝ) : ℂ))
            atTop (𝓝 (∫ x in B0579.cell c, F_v x * (2 : ℂ))) := by
          refine tendsto_integral_of_dominated_convergence (fun x => M₂ * ‖F_v x‖)
            (fun n => hFv_int.aestronglyMeasurable.mul
              (Complex.continuous_ofReal.comp
                (lapP_of_snd_aniso (c := c) (hg_smooth n) (hg_band n)).2.1.continuous).aestronglyMeasurable)
            (hFv_int.norm.const_mul M₂)
            (fun n => Eventually.of_forall fun x => ?_)
            (Eventually.of_forall fun x => ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)
          · refine tendsto_const_nhds.congr' ?_
            filter_upwards [hg_dd_ev x.2] with n hn
            rw [hn]; norm_num
        have heq_t : (∫ x in B0579.cell c, F_v x * (2 : ℂ)) = 2 * (c : ℂ) * cRaw tr u τ := by
          rw [integral_mul_const]; unfold cRaw; dsimp only [F_v]
          field_simp [hc_ne]
        rwa [heq_t] at h1
      have hsum := (hlim_visc.const_mul (ν : ℂ)).add hlim_adv
      rw [mul_zero, zero_add] at hsum
      exact hsum.congr fun n => (hG_eq n).symm
  -- Dominated convergence on `s₁..s₂`
  have hlim_time : Tendsto (fun n : ℕ => ∫ τ in s₁..s₂, G_seq n τ) atTop
      (𝓝 (∫ τ in s₁..s₂, 2 * (c : ℂ) * cRaw tr u τ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M_dom)
      (Eventually.of_forall fun n =>
        (hw_res.timeIntegrable (φ_seq n) (hφ_test n) s₂ hs12).def'.aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun τ hτ => ?_)
      intervalIntegrable_const
      (Eventually.of_forall fun τ hτ => ?_)
    · rw [uIoc_of_le hs12] at hτ
      exact (hG_dom_and_lim τ ⟨hτ.1.le, hτ.2⟩).1 n
    · rw [uIoc_of_le hs12] at hτ
      exact (hG_dom_and_lim τ ⟨hτ.1.le, hτ.2⟩).2
  have hw1_mom : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s₁ x) (B0579.cell c) :=
    integrable_eta_sq_of_memX m hm c (w s₁) (hw.memX s₁ hs₁)
  have hw2_mom : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s₂ x) (B0579.cell c) :=
    integrable_eta_sq_of_memX m hm c (w s₂) (hw.memX s₂ (hs₁.trans hs12))
  have hlim_lhs : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, w s₂ x * (φ_seq n x : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s₂ x)) := by
    refine (zcCutoffLimit c _ hw2_mom).congr fun n =>
      integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [φ_seq]; rw [hg_cut n x]; push_cast; ring
  have hlim_init : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, w s₁ x * (φ_seq n x : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s₁ x)) := by
    refine (zcCutoffLimit c _ hw1_mom).congr fun n =>
      integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [φ_seq]; rw [hg_cut n x]; push_cast; ring
  have hlim_rhs : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, w s₂ x * (φ_seq n x : ℂ)) atTop
      (𝓝 ((∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s₁ x) +
        ∫ τ in s₁..s₂, 2 * (c : ℂ) * cRaw tr u τ)) :=
    (hlim_init.add hlim_time).congr fun n => (hw_res.weak (φ_seq n) (hφ_test n) s₂ hs12).symm
  have hmom_id := tendsto_nhds_unique hlim_lhs hlim_rhs
  rw [intervalIntegral.integral_of_le hs12, integral_const_mul] at hmom_id
  unfold qScaled
  have h2c : (2 * (c : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hc_ne
  rw [hmom_id]
  calc (1 / (2 * (c : ℂ))) *
          ((∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s₁ x) +
            2 * (c : ℂ) * ∫ τ in Ioc s₁ s₂, cRaw tr u τ) -
        (1 / (2 * (c : ℂ))) * ∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s₁ x
      = ((1 / (2 * (c : ℂ))) * (2 * (c : ℂ))) * ∫ τ in Ioc s₁ s₂, cRaw tr u τ := by ring
    _ = ∫ τ in Ioc s₁ s₂, cRaw tr u τ := by rw [one_div_mul_cancel h2c, one_mul]

private lemma ofReal_cpow_add_aniso {s : ℝ} (hs : 0 < s) (z₁ z₂ : ℂ) :
    (s : ℂ) ^ (z₁ + z₂) = (s : ℂ) ^ z₁ * (s : ℂ) ^ z₂ :=
  Complex.cpow_add z₁ z₂ (Complex.ofReal_ne_zero.2 hs.ne')

private lemma ofReal_cpow_ofReal_aniso {s : ℝ} (hs : 0 < s) (p : ℝ) :
    (s : ℂ) ^ (p : ℂ) = ((s ^ p : ℝ) : ℂ) :=
  (Complex.ofReal_cpow hs.le p).symm

private lemma integral_Ioc_cpow_weight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (μ : ℂ) :
    IntegrableOn (fun s : ℝ => (μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)) (Ioc a b) ∧
      (∫ s in Ioc a b, (μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)) =
        (a : ℂ) ^ (-μ - 3 / 2) - (b : ℂ) ^ (-μ - 3 / 2) := by
  set z : ℂ := -μ - 3 / 2
  let Ψ : ℝ → ℂ := fun s => -(s : ℂ) ^ z
  let g : ℝ → ℂ := fun s => (μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)
  have hcont : ContinuousOn g (Icc a b) := by
    refine continuousOn_const.mul (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_)
    intro s hs
    exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha hs.1)
  have hderiv : ∀ s ∈ uIcc a b, HasDerivAt Ψ (g s) s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs.1
    have hne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs_pos.ne'
    -- Differentiate `(t : ℂ) ^ z = Complex.exp (((Real.log t : ℝ) : ℂ) * z)` on `Ioi 0`
    let Ψ_exp : ℝ → ℂ := fun t => -Complex.exp (((Real.log t : ℝ) : ℂ) * z)
    have hev_eq : Ψ =ᶠ[𝓝 s] Ψ_exp := by
      filter_upwards [isOpen_Ioi.mem_nhds hs_pos] with t ht
      dsimp only [Ψ, Ψ_exp]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 ht.ne'),
        Complex.ofReal_log ht.le]
    have hd_log : HasDerivAt (fun t : ℝ => ((Real.log t : ℝ) : ℂ) * z)
        (((s⁻¹ : ℝ) : ℂ) * z) s :=
      ((Real.hasDerivAt_log hs_pos.ne').ofReal_comp).mul_const z
    have hd_exp : HasDerivAt Ψ_exp
        (-(Complex.exp (((Real.log s : ℝ) : ℂ) * z) * (((s⁻¹ : ℝ) : ℂ) * z))) s :=
      hd_log.cexp.neg
    refine (hd_exp.congr_of_eventuallyEq hev_eq).congr_deriv ?_
    rw [Complex.ofReal_log hs_pos.le, ← Complex.cpow_def_of_ne_zero hne]
    have hsinv : ((s⁻¹ : ℝ) : ℂ) = (s : ℂ) ^ (-1 : ℂ) := by
      rw [Complex.ofReal_inv, Complex.cpow_neg_one]
    have hsub1 : z + (-1 : ℂ) = -μ - 5 / 2 := by dsimp [z]; ring
    have hmul_z : -z = μ + 3 / 2 := by dsimp [z]; ring
    rw [hsinv]
    calc -((s : ℂ) ^ z * ((s : ℂ) ^ (-1 : ℂ) * z))
        = (-z) * ((s : ℂ) ^ z * (s : ℂ) ^ (-1 : ℂ)) := by ring
      _ = (μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2) := by
          rw [hmul_z, ← ofReal_cpow_add_aniso hs_pos z (-1 : ℂ), hsub1]
  have hiiv : IntervalIntegrable g volume a b := (uIcc_of_le hab ▸ hcont).intervalIntegrable
  have hintOn : IntegrableOn g (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hiiv
  refine ⟨hintOn, ?_⟩
  rw [← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hiiv]
  dsimp [Ψ, z]; ring

/-- Fubini integration by parts on `Ioc u_o T` (`0 < u_o < T`), followed by `T → ∞` via DCT. -/
private lemma integral_pairC_eq_mellin_sub_boundary
    {ν m C_L2 : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ ν ^ (-2 : ℝ)) (hm : 8 < m) (hC_L2 : 0 < C_L2)
    (_P : PlanarData) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hv_bd : ∀ s : ℝ, 0 ≤ s →
      UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤ ENNReal.ofReal C_L2)
    {f : ℝ × ℝ → ℂ} (hf_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f w u)
    (hw_ev : ∀ s : ℝ, IsCentrallyEven (w s))
    {μ : ℂ} (hσ_pos : 0 < μ.re)
    (hint_pairC : IntegrableOn
      (fun τ => pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (onsetAge ν)))
    (hint_aPlus : IntegrableOn
      (fun s => aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (onsetAge ν))) :
    (∫ τ in Ioi (onsetAge ν), pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) =
      (μ + 3 / 2) * iA ν μ w -
        aPlus ν μ w (onsetAge ν) * (((onsetAge ν) ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := lt_of_lt_of_le one_pos hc1
  set u_o : ℝ := onsetAge ν
  have huo_pos : 0 < u_o := Real.rpow_pos_of_pos hν _
  set σ : ℝ := μ.re
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- Measurability of `cRaw` on `Ioi 0`
  have hrc_cRaw : ∀ s₀ : ℝ, 0 < s₀ → ContinuousWithinAt (cRaw tr u) (Ici s₀) s₀ := by
    intro s₀ hs₀
    have h01 := rightContinuous_train_vel_pairing hm hc1 hC_L2 tr hv_bd hf_zc hw hw_ev 0 1 hs₀.le
    have h10 := rightContinuous_train_vel_pairing hm hc1 hC_L2 tr hv_bd hf_zc hw hw_ev 1 0 hs₀.le
    have hfun : EqOn (cRaw tr u) (fun τ => (1 / (c : ℂ)) *
        ((∫ x in B0579.cell c, ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1) +
          ∫ x in B0579.cell c, ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0)) (Ici s₀) := by
      intro τ hτ
      have hτ0 : 0 ≤ τ := hs₀.le.trans hτ
      have hv_fin := lt_of_le_of_lt (hv_bd τ hτ0) ENNReal.ofReal_lt_top
      have i01 : IntegrableOn (fun x => ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1) (B0579.cell c) :=
        (memLp_train_coord_of_cellL2 hτ0 tr hv_fin 0).1.ofReal.integrable_mul
          ((hw.biotSavart τ hτ0).1 1)
      have i10 : IntegrableOn (fun x => ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0) (B0579.cell c) :=
        (memLp_train_coord_of_cellL2 hτ0 tr hv_fin 1).1.ofReal.integrable_mul
          ((hw.biotSavart τ hτ0).1 0)
      dsimp only [c] at i01 i10 ⊢
      unfold cRaw; rw [integral_add i01 i10]
    exact (continuousWithinAt_const.mul (h01.add h10)).congr
      (fun τ hτ => hfun hτ) (hfun (mem_Ici.2 le_rfl))
  let g_c : ℝ → ℂ := fun τ => if 0 < τ then cRaw tr u τ else 0
  have hgc_sm : StronglyMeasurable g_c :=
    stronglyMeasurable_posIndicator_of_rightContinuous hrc_cRaw
  let w_s : ℝ → ℂ := fun s => if 0 < s then (μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2) else 0
  have hws_sm : StronglyMeasurable w_s := by
    have hrc_w : ∀ s₀ : ℝ, 0 < s₀ →
        ContinuousWithinAt (fun s : ℝ => (μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)) (Ici s₀) s₀ :=
      fun s₀ hs₀ => continuousWithinAt_const.mul
        (((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hs₀)).comp
          Complex.continuous_ofReal.continuousAt).continuousWithinAt)
    exact stronglyMeasurable_posIndicator_of_rightContinuous hrc_w
  -- Step 1: Finite-horizon Fubini identity for every `T > u_o`
  have hfubini_T : ∀ {T : ℝ}, u_o < T →
      (∫ τ in Ioc u_o T, cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T : ℂ) ^ (-μ - 3 / 2))) =
        (μ + 3 / 2) * (∫ s in Ioc u_o T, aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) -
          qScaled c w u_o * ((u_o : ℂ) ^ (-μ - 3 / 2) - (T : ℂ) ^ (-μ - 3 / 2)) := by
    intro T hT
    have hT_pos : 0 < T := huo_pos.trans hT
    let μ_I := volume.restrict (Ioc u_o T)
    have hμI_fin : IsFiniteMeasure μ_I := ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
    let H : ℝ × ℝ → ℂ := fun p => if p.1 < p.2 then g_c p.1 * w_s p.2 else 0
    have hH_sm : StronglyMeasurable H :=
      ((hgc_sm.comp_measurable measurable_fst).mul
        (hws_sm.comp_measurable measurable_snd)).piecewise
        (isOpen_lt continuous_fst continuous_snd).measurableSet stronglyMeasurable_const
    -- Uniform bound of `H` on `Ioc u_o T ×ˢ Ioc u_o T`
    obtain ⟨B_w, hB_w_nn, hB_w⟩ := xNorm_toReal_bounded_on_Icc_aniso hT_pos.le hw
    set B_c : ℝ := c⁻¹ * (2 * C_L2 * (C_emb * B_w))
    have hgc_bd : ∀ τ ∈ Ioc u_o T, ‖cRaw tr u τ‖ ≤ B_c := by
      intro τ hτ
      have hτ0 : 0 ≤ τ := (huo_pos.trans hτ.1).le
      have hv_fin := lt_of_le_of_lt (hv_bd τ hτ0) ENNReal.ofReal_lt_top
      have hv0 := memLp_train_coord_of_cellL2 hτ0 tr hv_fin 0
      have hv1 := memLp_train_coord_of_cellL2 hτ0 tr hv_fin 1
      have hw_m := hw.memX τ hτ0
      have hw_zc := zeroCirculationPreserved ν c m hc_pos (by linarith) tr 0 f w u hw hf_zc τ hτ0
      have hemb_τ : velNorm c (u τ) ≤ ENNReal.ofReal C_emb * xNorm c m (w τ) :=
        (le_add_self.trans (hEmb0 c hc1 (w τ) hw_m hw_zc (hw_ev τ) (u τ)
          (hw.biotSavart τ hτ0))).trans
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C_emb0 1)) bot_le)
      have hu_tr : ∀ j : Fin 2,
          (eLpNorm (fun x => u τ x j) 2 (volume.restrict (B0579.cell c))).toReal ≤ C_emb * B_w := by
        intro j
        have hrhs_ne : ENNReal.ofReal C_emb * xNorm c m (w τ) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw_m.2.ne
        have h1 := ENNReal.toReal_mono hrhs_ne ((eLpNorm_coord_le_velNorm (u τ) j).trans hemb_τ)
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_emb.le] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (hB_w τ ⟨hτ0, hτ.2⟩) hC_emb.le)
      have i01 : IntegrableOn (fun x => ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1) (B0579.cell c) :=
        hv0.1.ofReal.integrable_mul ((hw.biotSavart τ hτ0).1 1)
      have i10 : IntegrableOn (fun x => ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0) (B0579.cell c) :=
        hv1.1.ofReal.integrable_mul ((hw.biotSavart τ hτ0).1 0)
      have b01 : ‖∫ x in B0579.cell c, ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1‖ ≤
          C_L2 * (C_emb * B_w) :=
        (norm_integral_mul_le_eLpNorm_two hv0.1 ((hw.biotSavart τ hτ0).1 1)).trans
          (mul_le_mul (ENNReal.toReal_le_of_le_ofReal hC_L2.le (hv0.2.trans (hv_bd τ hτ0)))
            (hu_tr 1) ENNReal.toReal_nonneg hC_L2.le)
      have b10 : ‖∫ x in B0579.cell c, ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0‖ ≤
          C_L2 * (C_emb * B_w) :=
        (norm_integral_mul_le_eLpNorm_two hv1.1 ((hw.biotSavart τ hτ0).1 0)).trans
          (mul_le_mul (ENNReal.toReal_le_of_le_ofReal hC_L2.le (hv1.2.trans (hv_bd τ hτ0)))
            (hu_tr 0) ENNReal.toReal_nonneg hC_L2.le)
      unfold cRaw
      dsimp only [c] at i01 i10 b01 b10 hc_pos B_c ⊢
      rw [integral_add i01 i10, norm_mul, norm_div, norm_one, Complex.norm_real,
        Real.norm_of_nonneg hc_pos.le, one_div]
      calc c⁻¹ * ‖(∫ x in B0579.cell c, ((tr.v τ x 0 : ℝ) : ℂ) * u τ x 1) +
              ∫ x in B0579.cell c, ((tr.v τ x 1 : ℝ) : ℂ) * u τ x 0‖
          ≤ c⁻¹ * (2 * C_L2 * (C_emb * B_w)) :=
            mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith))
              (inv_nonneg.2 hc_pos.le)
        _ = B_c := rfl
    set B_ws : ℝ := ‖μ + 3 / 2‖ * u_o ^ (-σ - 5 / 2)
    have hws_bd : ∀ s ∈ Ioc u_o T, ‖(μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)‖ ≤ B_ws := by
      intro s hs
      have hs_pos : 0 < s := huo_pos.trans hs.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs_pos]
      have hre : (-μ - 5 / 2).re = -σ - 5 / 2 := by simp [σ]
      rw [hre]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos huo_pos hs.1.le (by linarith)) (norm_nonneg _)
    have hH_int : Integrable H (μ_I.prod μ_I) := by
      refine Integrable.mono' (integrable_const (B_c * B_ws)) hH_sm.aestronglyMeasurable ?_
      have hae : ∀ᵐ p ∂(μ_I.prod μ_I), p ∈ Ioc u_o T ×ˢ Ioc u_o T := by
        dsimp only [μ_I]
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      filter_upwards [hae] with p ⟨hp1, hp2⟩
      dsimp only [H]
      split_ifs with hlt
      · have hp1_pos : 0 < p.1 := huo_pos.trans hp1.1
        have hp2_pos : 0 < p.2 := huo_pos.trans hp2.1
        dsimp only [g_c, w_s]
        rw [ite_eq_left hp1_pos, ite_eq_left hp2_pos, norm_mul]
        exact mul_le_mul (hgc_bd p.1 hp1) (hws_bd p.2 hp2) (norm_nonneg _) (by positivity)
      · rw [norm_zero]; positivity
    have hfub : (∫ τ, (∫ s, H (τ, s) ∂μ_I) ∂μ_I) = ∫ s, (∫ τ, H (τ, s) ∂μ_I) ∂μ_I :=
      (MeasureTheory.integral_prod H hH_int).symm.trans (MeasureTheory.integral_prod_symm H hH_int)
    -- Evaluate LHS of `hfub`
    have hlhs_fub : (∫ τ, (∫ s, H (τ, s) ∂μ_I) ∂μ_I) =
        ∫ τ in Ioc u_o T, cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T : ℂ) ^ (-μ - 3 / 2)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
      have hτ_pos : 0 < τ := huo_pos.trans hτ.1
      have hsub : Ioc τ T ⊆ Ioc u_o T := Ioc_subset_Ioc hτ.1.le le_rfl
      have hcongr_s : EqOn (fun s => H (τ, s))
          ((Ioc τ T).indicator (fun s => cRaw tr u τ * ((μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2))))
          (Ioc u_o T) := by
        intro s hs
        have hs_pos : 0 < s := huo_pos.trans hs.1
        dsimp only [H, g_c, w_s]
        by_cases hlt : τ < s
        · have hmem : s ∈ Ioc τ T := ⟨hlt, hs.2⟩
          rw [ite_eq_left hlt, ite_eq_left hτ_pos, ite_eq_left hs_pos, indicator_of_mem hmem]
        · have hnmem : s ∉ Ioc τ T := fun h => hlt h.1
          rw [ite_eq_right hlt, indicator_of_notMem hnmem]
      rw [setIntegral_congr_fun measurableSet_Ioc hcongr_s,
        integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_self_of_subset_left hsub, integral_const_mul,
        (integral_Ioc_cpow_weight hτ_pos hτ.2 μ).2]
    -- Evaluate RHS of `hfub`
    have hrhs_fub : (∫ s, (∫ τ, H (τ, s) ∂μ_I) ∂μ_I) =
        (μ + 3 / 2) * (∫ s in Ioc u_o T, aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) -
          qScaled c w u_o * ((u_o : ℂ) ^ (-μ - 3 / 2) - (T : ℂ) ^ (-μ - 3 / 2)) := by
      have hinner : EqOn (fun s => ∫ τ, H (τ, s) ∂μ_I)
          (fun s => (μ + 3 / 2) * (aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) -
            qScaled c w u_o * ((μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)))
          (Ioc u_o T) := by
        intro s hs
        have hs_pos : 0 < s := huo_pos.trans hs.1
        have hsub : Ioo u_o s ⊆ Ioc u_o T :=
          Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc le_rfl hs.2)
        have hcongr_τ : EqOn (fun τ => H (τ, s))
            ((Ioo u_o s).indicator (fun τ => cRaw tr u τ * ((μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2))))
            (Ioc u_o T) := by
          intro τ hτ
          have hτ_pos : 0 < τ := huo_pos.trans hτ.1
          dsimp only [H, g_c, w_s]
          by_cases hlt : τ < s
          · have hmem : τ ∈ Ioo u_o s := ⟨hτ.1, hlt⟩
            rw [ite_eq_left hlt, ite_eq_left hτ_pos, ite_eq_left hs_pos, indicator_of_mem hmem]
          · have hnmem : τ ∉ Ioo u_o s := fun h => hlt h.2
            rw [ite_eq_right hlt, indicator_of_notMem hnmem]
        dsimp only [μ_I]
        rw [setIntegral_congr_fun measurableSet_Ioc hcongr_τ,
          integral_indicator measurableSet_Ioo,
          Measure.restrict_restrict measurableSet_Ioo,
          inter_eq_self_of_subset_left hsub,
          ← integral_Ioc_eq_integral_Ioo, integral_mul_const,
          ← qScaled_sub_eq_integral_cRaw hν hc1 hm hC_L2 tr hv_bd hf_zc hw hw_ev
            huo_pos.le hs.1.le]
        have hcp : (s : ℂ) ^ (-μ - 5 / 2) = (s : ℂ) ^ (-μ) * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ) := by
          rw [show (-μ - 5 / 2 : ℂ) = -μ + ((-5 / 2 : ℝ) : ℂ) by push_cast; ring,
            ofReal_cpow_add_aniso hs_pos, ofReal_cpow_ofReal_aniso hs_pos]
        rw [hcp, aPlus_eq_cpow_mul_qScaled hν μ w s]
        dsimp only [c]
        ring
      have hi1 : IntegrableOn
          (fun s : ℝ => (μ + 3 / 2) * (aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)))
          (Ioc u_o T) := (hint_aPlus.mono_set Ioc_subset_Ioi_self).const_mul _
      obtain ⟨hw_int, hw_val⟩ := integral_Ioc_cpow_weight huo_pos hT.le μ
      have hi2 : IntegrableOn
          (fun s : ℝ => qScaled c w u_o * ((μ + 3 / 2) * (s : ℂ) ^ (-μ - 5 / 2)))
          (Ioc u_o T) := hw_int.const_mul _
      rw [setIntegral_congr_fun measurableSet_Ioc hinner,
        integral_sub hi1 hi2, integral_const_mul, integral_const_mul, hw_val]
    rw [← hlhs_fub, ← hrhs_fub, hfub]
  -- Step 2: Pass `T_seq n = u_o + n + 1 → ∞` via DCT
  let T_seq : ℕ → ℝ := fun n => u_o + (n : ℝ) + 1
  have hT_gt : ∀ n : ℕ, u_o < T_seq n := fun n => by
    dsimp [T_seq]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hT_pos_n : ∀ n : ℕ, 0 < T_seq n := fun n => huo_pos.trans (hT_gt n)
  have hTn_pow_zero : Tendsto (fun n : ℕ => (T_seq n : ℂ) ^ (-μ - 3 / 2)) atTop (𝓝 0) := by
    have hnorm0 : Tendsto (fun n : ℕ => ‖(T_seq n : ℂ) ^ (-μ - 3 / 2)‖) atTop (𝓝 0) := by
      have h_atTop : Tendsto T_seq atTop atTop := by
        have h1 : Tendsto (fun n : ℕ => u_o + (n : ℝ)) atTop atTop :=
          tendsto_atTop_add_const_left atTop u_o tendsto_natCast_atTop_atTop
        exact tendsto_atTop_add_const_right atTop 1 h1
      have h_rpow : Tendsto (fun x : ℝ => x ^ (-σ - 3 / 2)) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith : 0 < σ + 3 / 2) |>.congr fun x => by
          congr 1; ring
      refine (h_rpow.comp h_atTop).congr fun n => ?_
      dsimp [Function.comp]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hT_pos_n n)]
      simp [σ]
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm0
  -- LHS limit as `n → ∞`
  have hlim_L : Tendsto
      (fun n : ℕ => ∫ τ in Ioc u_o (T_seq n),
        cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)))
      atTop
      (𝓝 (∫ τ in Ioi u_o, pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) := by
    let μ_oi := volume.restrict (Ioi u_o)
    let f_L : ℕ → ℝ → ℂ := fun n => (Ioc u_o (T_seq n)).indicator
      (fun τ => cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)))
    have hfL_eq : ∀ n : ℕ, (∫ τ in Ioc u_o (T_seq n),
          cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2))) =
        ∫ τ, f_L n τ ∂μ_oi := by
      intro n
      dsimp only [f_L, μ_oi]
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_self_of_subset_left Ioc_subset_Ioi_self]
    simp_rw [hfL_eq]
    have hdom_int : Integrable
        (fun τ => 2 * ‖pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖) μ_oi :=
      hint_pairC.norm.const_mul 2
    have hpairC_id : ∀ {τ : ℝ}, 0 < τ →
        cRaw tr u τ * (τ : ℂ) ^ (-μ - 3 / 2) =
          pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
      intro τ hτ
      have hcp : (τ : ℂ) ^ (-μ - 3 / 2) = (τ : ℂ) ^ (-μ) * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
        rw [show (-μ - 3 / 2 : ℂ) = -μ + ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
          ofReal_cpow_add_aniso hτ, ofReal_cpow_ofReal_aniso hτ]
      rw [hcp, pairC_eq_cpow_mul_cRaw]; ring
    refine tendsto_integral_of_dominated_convergence
      (fun τ => 2 * ‖pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖)
      (fun n => ?_) hdom_int (fun n => ?_) ?_
    · refine AEStronglyMeasurable.indicator ?_ measurableSet_Ioc
      refine aestronglyMeasurable_on_subset_Ioi_of_rightContinuous
        (Ioi_subset_Ioi huo_pos.le) measurableSet_Ioi (fun s₀ hs₀ => ?_)
      exact (hrc_cRaw s₀ hs₀).mul
        ((((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hs₀)).comp
          Complex.continuous_ofReal.continuousAt).continuousWithinAt).sub continuousWithinAt_const)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ_oi
      have hτ_pos : 0 < τ := huo_pos.trans hτ_oi
      dsimp only [f_L]
      by_cases hmem : τ ∈ Ioc u_o (T_seq n)
      · rw [indicator_of_mem hmem, norm_mul]
        have hTn_le : ‖(T_seq n : ℂ) ^ (-μ - 3 / 2)‖ ≤ ‖(τ : ℂ) ^ (-μ - 3 / 2)‖ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (hT_pos_n n),
            Complex.norm_cpow_eq_rpow_re_of_pos hτ_pos]
          have hre : (-μ - 3 / 2).re = -σ - 3 / 2 := by simp [σ]
          rw [hre]
          exact Real.rpow_le_rpow_of_nonpos hτ_pos hmem.2 (by linarith)
        have hdiff_le : ‖(τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)‖ ≤
            2 * ‖(τ : ℂ) ^ (-μ - 3 / 2)‖ :=
          (norm_sub_le _ _).trans (by linarith)
        calc ‖cRaw tr u τ‖ * ‖(τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)‖
            ≤ ‖cRaw tr u τ‖ * (2 * ‖(τ : ℂ) ^ (-μ - 3 / 2)‖) :=
              mul_le_mul_of_nonneg_left hdiff_le (norm_nonneg _)
          _ = 2 * ‖cRaw tr u τ * (τ : ℂ) ^ (-μ - 3 / 2)‖ := by rw [norm_mul]; ring
          _ = 2 * ‖pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ := by
              rw [hpairC_id hτ_pos]
      · rw [indicator_of_notMem hmem, norm_zero]; positivity
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ_oi
      have hτ_pos : 0 < τ := huo_pos.trans hτ_oi
      have hlim_pt : Tendsto
          (fun n : ℕ => cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)))
          atTop (𝓝 (pairC tr μ (u τ) τ * ((τ ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) := by
        have h1 : Tendsto
            (fun n : ℕ => cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)))
            atTop (𝓝 (cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - 0))) :=
          tendsto_const_nhds.mul (tendsto_const_nhds.sub hTn_pow_zero)
        rwa [sub_zero, hpairC_id hτ_pos] at h1
      refine hlim_pt.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈τ - u_o⌉₊] with n hn
      have hle : τ ≤ T_seq n := by
        have hceil : τ - u_o ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        dsimp [T_seq]; linarith
      dsimp only [f_L]
      rw [indicator_of_mem (mem_Ioc.2 ⟨hτ_oi, hle⟩)]
  -- RHS limit as `n → ∞`
  have hlim_iA : Tendsto
      (fun n : ℕ => ∫ s in Ioc u_o (T_seq n), aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (iA ν μ w)) := by
    let μ_oi := volume.restrict (Ioi u_o)
    let f_A : ℕ → ℝ → ℂ := fun n => (Ioc u_o (T_seq n)).indicator
      (fun s => aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ))
    have hfA_eq : ∀ n : ℕ, (∫ s in Ioc u_o (T_seq n),
          aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) = ∫ s, f_A n s ∂μ_oi := by
      intro n
      dsimp only [f_A, μ_oi]
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_self_of_subset_left Ioc_subset_Ioi_self]
    simp_rw [hfA_eq]; unfold iA
    refine tendsto_integral_of_dominated_convergence
      (fun s => ‖aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)‖)
      (fun n => hint_aPlus.aestronglyMeasurable.indicator measurableSet_Ioc)
      hint_aPlus.norm
      (fun n => Eventually.of_forall fun s => ?_)
      ?_;
    · dsimp only [f_A]
      by_cases hs : s ∈ Ioc u_o (T_seq n)
      · rw [indicator_of_mem hs]
      · rw [indicator_of_notMem hs, norm_zero]; exact norm_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs_oi
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈s - u_o⌉₊] with n hn
      have hle : s ≤ T_seq n := by
        have hceil : s - u_o ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        dsimp [T_seq]; linarith
      dsimp only [f_A]
      rw [indicator_of_mem (mem_Ioc.2 ⟨hs_oi, hle⟩)]
  have hbd_uo : qScaled c w u_o * (u_o : ℂ) ^ (-μ - 3 / 2) =
      aPlus ν μ w u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
    have hcp : (u_o : ℂ) ^ (-μ - 3 / 2) = (u_o : ℂ) ^ (-μ) * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (-μ - 3 / 2 : ℂ) = -μ + ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
        ofReal_cpow_add_aniso huo_pos, ofReal_cpow_ofReal_aniso huo_pos]
    rw [hcp, aPlus_eq_cpow_mul_qScaled hν μ w u_o]; ring
  have hlim_R : Tendsto
      (fun n : ℕ => ∫ τ in Ioc u_o (T_seq n),
        cRaw tr u τ * ((τ : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)))
      atTop
      (𝓝 ((μ + 3 / 2) * iA ν μ w - aPlus ν μ w u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) := by
    have h1 : Tendsto
        (fun n : ℕ =>
          (μ + 3 / 2) * (∫ s in Ioc u_o (T_seq n), aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) -
            qScaled c w u_o * ((u_o : ℂ) ^ (-μ - 3 / 2) - (T_seq n : ℂ) ^ (-μ - 3 / 2)))
        atTop
        (𝓝 ((μ + 3 / 2) * iA ν μ w - qScaled c w u_o * ((u_o : ℂ) ^ (-μ - 3 / 2) - 0))) :=
      (hlim_iA.const_mul (μ + 3 / 2)).sub
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub hTn_pow_zero))
    rw [sub_zero, hbd_uo] at h1
    exact h1.congr fun n => (hfubini_T (hT_gt n)).symm
  exact tendsto_nhds_unique hlim_L hlim_R

private theorem ctAnisotropy_impl : CTAnisotropy := by
  intro P hP m hm K hK ε hε
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  set γ : ℝ := P.eigenvalue.re
  set κ_re : ℝ := P.kappa.re
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hEmb : ∀ d : ℝ, 1 ≤ d → ∀ f : ℝ × ℝ → ℂ,
      MemLp f 2 (B0579.cellMeasure d m) → HasZeroCirculation d f → IsCentrallyEven f →
        ∀ u, IsBiotSavart d f u →
          ENNReal.ofReal ‖quadQ d f‖ + velNorm d u ≤ ENNReal.ofReal C_emb * xNorm d m f := by
    intro d hd f hf hz hev u hu
    exact (hEmb0 d hd f hf hz hev u hu).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C_emb0 1)) bot_le)
  have hBranch := T22Sub.ctCanonicalBranchProps P hP m hm
  obtain ⟨b₀_br, _, hBr_all⟩ := hBranch.2.2.1
  obtain ⟨b₀_long, hLong_all⟩ := ctLongComparison P hP m hm
  obtain ⟨C_L2, ν_L2, hC_L2, hν_L2, hL2_unif⟩ := train_cellL2_uniform_aniso
  obtain ⟨ν_int, hν_int, hInt_pairs⟩ := integrableOn_each_pair_Ioi_onset P hP m hm K hK
  -- Base cutoff `b_base` for bounding the boundary term at `u_o = onsetAge ν`
  set b_base : ℝ := max 1 (max b₀_br b₀_long)
  have hb_base1 : 1 ≤ b_base := le_max_left _ _
  have hb_base0 : 0 < b_base := lt_of_lt_of_le one_pos hb_base1
  obtain ⟨C_br, hC_br, hBr_est⟩ := hBr_all b_base ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨C_long0, a₁, ν_long, ha₁, hν_long, hLong_est⟩ :=
    hLong_all b_base ((le_max_right _ _).trans (le_max_right _ _))
  set C_long : ℝ := max C_long0 1
  have hC_long : 0 < C_long := lt_of_lt_of_le one_pos (le_max_right _ _)
  set C_Z : ℝ := C_emb * (C_br + 3 * C_long)
  have hC_Z : 0 < C_Z := by dsimp [C_Z]; positivity
  set M_bd : ℕ := ⌈2 - κ_re⌉₊
  set M_exp_bd : ℝ := (M_bd.factorial : ℝ) * (2 / γ) ^ M_bd
  have hM_exp_bd : 0 < M_exp_bd :=
    mul_pos (Nat.cast_pos.2 (Nat.factorial_pos M_bd)) (pow_pos (div_pos two_pos hγ) M_bd)
  -- Exponential decay of `(12 * C_Z * M_exp_bd) * exp (-(γ / 4) * ν^(-1/2))` as `ν → 0⁺`
  have hlim_bd : Tendsto
      (fun ν : ℝ => (12 * C_Z * M_exp_bd) * Real.exp (-((γ / 4) * (ν ^ (1 / 2 : ℝ))⁻¹)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun ν : ℝ => ν ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun ν : ℝ => ν ^ (1 / 2 : ℝ)) :=
          Real.continuous_rpow_const (by norm_num)
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ν hν
        exact Real.rpow_pos_of_pos (mem_Ioi.1 hν) _
    have h2 : Tendsto (fun x : ℝ => (γ / 4) * x⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (h2.comp h1)).const_mul
      (12 * C_Z * M_exp_bd)
    rw [mul_zero] at h3
    exact h3
  have hDef_ev := ctStressDefect_impl P hP m hm K hK (ε / 2) (half_pos hε)
  have hMel_ev := ctMellin P hP m hm K hK 1 one_pos
  set ν_cap : ℝ := min ν_int (min ν_long (min ν_L2 (min (1 / 4) ((9 * b_base ^ 2)⁻¹))))
  have hν_cap : 0 < ν_cap :=
    lt_min hν_int (lt_min hν_long (lt_min hν_L2
      (lt_min (by norm_num) (inv_pos.2 (by positivity)))))
  filter_upwards [Ioc_mem_nhdsGT hν_cap, hDef_ev, hMel_ev,
    (Metric.tendsto_nhds.1 hlim_bd) (ε / 2) (half_pos hε)]
    with ν hν_in hDef hMel hBd_small
  intro tr htr w u hw μ hμ
  have hν_pos : 0 < ν := hν_in.1
  have hν_int_le : ν ≤ ν_int := hν_in.2.trans (min_le_left _ _)
  have hν_long_le : ν ≤ ν_long := hν_in.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_L2_le : ν ≤ ν_L2 :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_qtr : ν ≤ 1 / 4 :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hν_9b2 : ν ≤ (9 * b_base ^ 2)⁻¹ :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  rw [dist_zero_right, Real.norm_of_nonneg (by positivity)] at hBd_small
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  have hc1 : 1 ≤ c := by
    have hle : ((1 / 4 : ℝ) ^ (-2 : ℝ)) ≤ c :=
      Real.rpow_le_rpow_of_nonpos hν_pos hν_qtr (by norm_num)
    have hev : ((1 / 4 : ℝ) ^ (-2 : ℝ)) = 16 := by norm_num
    linarith
  obtain ⟨hprep_mem, hprep_zc, hprep_ev⟩ := hBranch.1 ν ⟨hν_pos, hν1⟩
  obtain ⟨hσ_pos, hσ_lt⟩ := hK.2 μ hμ
  set σ : ℝ := μ.re
  have hscaleA_nn : 0 ≤ scaleA P ν μ := by unfold scaleA; positivity
  -- Integrability on `Ioi (onsetAge ν)`
  obtain ⟨hi_Eta, hi_Q, hi_C⟩ := hInt_pairs ν ⟨hν_pos, hν_int_le⟩ tr htr w u hw μ hμ
  have hInt_aniso : IntegrableOn
      (fun s => (2 * pairQ tr μ (u s) s - pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
      (Ioi (onsetAge ν)) := by
    refine IntegrableOn.congr_fun ((hi_Q.const_mul 2).sub hi_Eta) (fun s _ => ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]; ring
  refine ⟨hInt_aniso, ?_⟩
  -- Symmetrize `(w, u)` to `(w_ev, u_odd)`
  set w_ev : ℝ → ℝ × ℝ → ℂ := symFlowW w
  set u_odd : ℝ → ℝ × ℝ → Fin 2 → ℂ := symFlowU u
  have hw_sym : IsLinearisedFlow ν c m tr 0 (preparedDatum P ν) w_ev u_odd :=
    isLinearisedFlow_sym_aniso (by linarith) tr hprep_mem hprep_ev hw
  have hw_ev_all : ∀ s : ℝ, IsCentrallyEven (w_ev s) := fun s x => by
    unfold w_ev symFlowW; rw [neg_neg]; ring
  have hv_fin : ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤ := fun s hs =>
    lt_of_le_of_lt (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr s hs) ENNReal.ofReal_lt_top
  obtain ⟨hpair_eq, hiA_eq⟩ := symFlow_pairings_and_iA_eq hν_pos hm P tr μ hv_fin hw
  obtain ⟨_, _, hi_C_sym⟩ := hInt_pairs ν ⟨hν_pos, hν_int_le⟩ tr htr w_ev u_odd hw_sym μ hμ
  have hint_aPlus_sym := (hMel tr htr w_ev u_odd hw_sym μ hμ).1
  set u_o : ℝ := onsetAge ν
  have huo_pos : 0 < u_o := Real.rpow_pos_of_pos hν_pos _
  -- Apply Fubini + DCT identity to `(w_ev, u_odd)` and transfer back to `(w, u)`
  have hIBP_sym := integral_pairC_eq_mellin_sub_boundary hν_pos hc1 hm hC_L2 P tr
    (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr) hprep_zc hw_sym hw_ev_all hσ_pos hi_C_sym hint_aPlus_sym
  have hpairC_int_eq :
      (∫ s in Ioi u_o, pairC tr μ (u_odd s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) =
        ∫ s in Ioi u_o, pairC tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun s hs => by
      dsimp only [u_odd]; rw [(hpair_eq s (huo_pos.trans hs).le).2.2.1]
  rw [hpairC_int_eq, hiA_eq] at hIBP_sym
  -- Algebraic decomposition `2 E_q - E_η = -(D_c - 3 R_c) + 3 i C`
  obtain ⟨hInt_def, hBd_def⟩ := hDef tr htr w u hw μ hμ
  have halg_int :
      (∫ s in Ioi u_o,
          (2 * pairQ tr μ (u s) s - pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) =
        -(∫ s in Ioi u_o,
            ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
              3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) +
          (3 * Complex.I) *
            ∫ s in Ioi u_o, pairC tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
    have hpt : (fun s =>
          (2 * pairQ tr μ (u s) s - pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) =
        fun s =>
          -(((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
              3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) +
            (3 * Complex.I) * (pairC tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) := by
      funext s; ring
    have hi1 : IntegrableOn
        (fun s => -(((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
          3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
            ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) (Ioi u_o) := hInt_def.neg
    have hi2 : IntegrableOn
        (fun s => (3 * Complex.I) * (pairC tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)))
        (Ioi u_o) := hi_C.const_mul (3 * Complex.I)
    rw [hpt, integral_add hi1 hi2, integral_neg, integral_const_mul]
  -- Bound the onset boundary term `‖3 * Complex.I * (aPlus ν μ w_ev u_o * u_o^(-3/2))‖ ≤ (ε/2) * scaleA`
  have hBd_uo : ‖(3 * Complex.I) * (aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ))‖ ≤
      (ε / 2) * scaleA P ν μ := by
    set θ_o : ℝ := clockTheta ν u_o
    have ha_uo : 0 < clockA ν u_o := by unfold clockA; positivity
    have hθo_pos : 0 < θ_o := by unfold θ_o clockTheta; positivity
    have hs_θo : clockAge ν θ_o = u_o := T22Sub.clockAge_clockTheta hν_pos ha_uo
    have hθo_eq : θ_o = (ν + ν ^ (1 / 2 : ℝ))⁻¹ := by
      unfold θ_o clockTheta clockA u_o onsetAge
      congr 1
      have hmul : ν * ν ^ (-3 / 2 : ℝ) = ν ^ (-1 / 2 : ℝ) := by
        calc ν * ν ^ (-3 / 2 : ℝ)
            = ν ^ (1 : ℝ) * ν ^ (-3 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = ν ^ ((1 : ℝ) + -3 / 2) := (Real.rpow_add hν_pos 1 (-3 / 2)).symm
          _ = ν ^ (-1 / 2 : ℝ) := by norm_num
      have hmul2 : ν * ν ^ (-1 / 2 : ℝ) = ν ^ (1 / 2 : ℝ) := by
        calc ν * ν ^ (-1 / 2 : ℝ)
            = ν ^ (1 : ℝ) * ν ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = ν ^ ((1 : ℝ) + -1 / 2) := (Real.rpow_add hν_pos 1 (-1 / 2)).symm
          _ = ν ^ (1 / 2 : ℝ) := by norm_num
      rw [hmul, mul_add, mul_one, hmul2]
    have hν_le_sqrt : ν ≤ ν ^ (1 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one ν]
      exact Real.rpow_le_rpow_of_exponent_ge hν_pos hν1 (by norm_num)
    have hθo_ge_half : (2 * ν ^ (1 / 2 : ℝ))⁻¹ ≤ θ_o := by
      rw [hθo_eq]
      exact inv_anti₀ (by positivity) (by linarith)
    have hν_inv_le : ν⁻¹ ≤ 4 * θ_o ^ 2 := by
      have hsq : ((2 * ν ^ (1 / 2 : ℝ))⁻¹) ^ 2 = (4 * ν)⁻¹ := by
        rw [inv_pow, mul_pow, ← Real.rpow_natCast (ν ^ (1 / 2 : ℝ)) 2,
          ← Real.rpow_mul hν_pos.le]
        norm_num
      have hle_sq : ((2 * ν ^ (1 / 2 : ℝ))⁻¹) ^ 2 ≤ θ_o ^ 2 :=
        pow_le_pow_left₀ (by positivity) hθo_ge_half 2
      rw [hsq, mul_inv] at hle_sq
      linarith
    have hsqrt_le : ν ^ (1 / 2 : ℝ) ≤ (3 * b_base)⁻¹ := by
      have h9 : (9 * b_base ^ 2)⁻¹ = ((3 * b_base)⁻¹) ^ (2 : ℝ) := by
        rw [Real.rpow_two, inv_pow]; ring
      calc ν ^ (1 / 2 : ℝ)
          ≤ ((9 * b_base ^ 2)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hν_pos.le hν_9b2 (by norm_num)
        _ = (((3 * b_base)⁻¹) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [h9]
        _ = (3 * b_base)⁻¹ := by
            rw [← Real.rpow_mul (by positivity : 0 ≤ (3 * b_base)⁻¹)]; norm_num
    have hb_le_θo : b_base ≤ θ_o := by
      have h1 : b_base ≤ (2 * (3 * b_base)⁻¹)⁻¹ := by
        have heq : (2 * (3 * b_base)⁻¹)⁻¹ = (3 / 2) * b_base := by
          have := hb_base0.ne'; field_simp
        rw [heq]; linarith
      have h2 : (2 * (3 * b_base)⁻¹)⁻¹ ≤ (2 * ν ^ (1 / 2 : ℝ))⁻¹ :=
        inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hsqrt_le (by norm_num))
      exact h1.trans (h2.trans hθo_ge_half)
    have hθo_le_inv : θ_o ≤ ν⁻¹ := by
      rw [hθo_eq]
      exact inv_anti₀ hν_pos (by linarith [Real.rpow_pos_of_pos hν_pos (1 / 2 : ℝ)])
    have hν3_θo : ν ^ 3 ≤ θ_o := by
      have h1 : ν ^ 3 ≤ 1 := pow_le_one₀ hν_pos.le hν1
      exact h1.trans (hb_base1.trans hb_le_θo)
    obtain ⟨hd_o1, hZo_mem, hZo_zc, hZo_ev, hUZo_bs, _, hQo_eq⟩ :=
      heatColumn_even_props_aniso (P := P) hν_pos hθo_pos hθo_le_inv hν3_θo hm
        hprep_zc hw_sym hw_ev_all
    rw [hs_θo] at hQo_eq
    set d_o : ℝ := dOfTheta ν θ_o
    set Z_o : ℝ × ℝ → ℂ := heatColumn P ν w_ev θ_o
    set V_do : ℝ × ℝ → ℂ := canonicalPeriodized P ν θ_o
    have hVdo_mem := (hBranch.2.1 ν θ_o hν_pos hθo_pos hd_o1).1
    have hBr_o := hBr_est ν ⟨hν_pos, hν1⟩ θ_o hb_le_θo hd_o1
    have hLong_o0 := (hLong_est ν ⟨hν_pos, hν_long_le⟩ tr htr).2 w_ev u_odd hw_sym
      θ_o hb_le_θo hθo_le_inv
    set W_o : ℝ := Real.exp (γ * θ_o) * θ_o ^ κ_re
    have hWo_pos : 0 < W_o := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hθo_pos _)
    have hθo1 : 1 ≤ θ_o := hb_base1.trans hb_le_θo
    have herr_le3 : ν + (ν ^ 3) ^ 2 / θ_o + Real.exp (-a₁ * θ_o / ν ^ 3) ≤ 3 := by
      have hν6 : (ν ^ 3) ^ 2 / θ_o ≤ 1 :=
        (div_le_one hθo_pos).2
          ((pow_le_one₀ (by positivity) (pow_le_one₀ hν_pos.le hν1)).trans hθo1)
      have hexp1 : Real.exp (-a₁ * θ_o / ν ^ 3) ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha₁.le) hθo_pos.le) (by positivity))
      linarith
    have hLong_3 : ENNReal.ofReal W_o * xNorm d_o m (Z_o - V_do) ≤
        ENNReal.ofReal (3 * C_long) := by
      refine hLong_o0.trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : C_long0 ≤ C_long := le_max_left _ _
      have hnn : 0 ≤ ν + (ν ^ 3) ^ 2 / θ_o + Real.exp (-a₁ * θ_o / ν ^ 3) := by positivity
      nlinarith only [h1, hnn, herr_le3, hC_long]
    have hxZo_tri : xNorm d_o m Z_o ≤ xNorm d_o m (Z_o - V_do) + xNorm d_o m V_do := by
      have heq : Z_o = (Z_o - V_do) + V_do := by funext y; simp
      unfold xNorm; conv_lhs => rw [heq]
      exact eLpNorm_add_le (hZo_mem.sub hVdo_mem).1 hVdo_mem.1 one_le_two
    have hWZo : ENNReal.ofReal W_o * xNorm d_o m Z_o ≤ ENNReal.ofReal (C_br + 3 * C_long) := by
      calc ENNReal.ofReal W_o * xNorm d_o m Z_o
          ≤ ENNReal.ofReal W_o * (xNorm d_o m (Z_o - V_do) + xNorm d_o m V_do) :=
            mul_le_mul_of_nonneg_left hxZo_tri bot_le
        _ = ENNReal.ofReal W_o * xNorm d_o m (Z_o - V_do) +
              ENNReal.ofReal W_o * xNorm d_o m V_do := mul_add _ _ _
        _ ≤ ENNReal.ofReal (3 * C_long) + ENNReal.ofReal C_br := add_le_add hLong_3 hBr_o
        _ = ENNReal.ofReal (C_br + 3 * C_long) := by
            rw [← ENNReal.ofReal_add (by positivity) hC_br.le]; congr 1; ring
    have hxZo_bd : xNorm d_o m Z_o ≤
        ENNReal.ofReal ((C_br + 3 * C_long) * Real.exp (-γ * θ_o) * θ_o ^ (-κ_re)) := by
      have hWinv : W_o⁻¹ = Real.exp (-γ * θ_o) * θ_o ^ (-κ_re) := by
        dsimp [W_o]; rw [mul_inv, ← Real.exp_neg, neg_mul, ← Real.rpow_neg hθo_pos.le]
      have hsc := mul_le_mul_of_nonneg_left hWZo (bot_le : 0 ≤ ENNReal.ofReal W_o⁻¹)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hWo_pos.le),
        inv_mul_cancel₀ hWo_pos.ne', ENNReal.ofReal_one, one_mul,
        ← ENNReal.ofReal_mul (inv_nonneg.2 hWo_pos.le), hWinv] at hsc
      exact hsc.trans (le_of_eq (by congr 1; ring))
    have hQZo_bd : ‖quadQ d_o Z_o‖ ≤ C_Z * Real.exp (-γ * θ_o) * θ_o ^ (-κ_re) := by
      have hemb := (le_self_add.trans (hEmb d_o hd_o1 Z_o hZo_mem hZo_zc hZo_ev _ hUZo_bs)).trans
        (mul_le_mul_of_nonneg_left hxZo_bd bot_le)
      rw [← ENNReal.ofReal_mul hC_emb.le,
        show C_emb * ((C_br + 3 * C_long) * Real.exp (-γ * θ_o) * θ_o ^ (-κ_re)) =
          C_Z * Real.exp (-γ * θ_o) * θ_o ^ (-κ_re) by dsimp [C_Z]; ring] at hemb
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hemb
    -- Bound `u_o ^ (-σ - 3 / 2)`
    have huo_pow : u_o ^ (-σ) * u_o ^ (-3 / 2 : ℝ) ≤ ν ^ (3 + 2 * σ) * (4 * θ_o ^ 2) := by
      have h1 : u_o ^ (-σ) * u_o ^ (-3 / 2 : ℝ) = ν ^ ((3 / 2) * σ + 9 / 4) := by
        rw [← Real.rpow_add huo_pos]
        dsimp [u_o]; unfold onsetAge
        rw [← Real.rpow_mul hν_pos.le]; congr 1; ring
      have h2 : ν ^ ((3 / 2) * σ + 9 / 4) = ν ^ (3 + 2 * σ) * ν ^ (-(3 / 4 + σ / 2)) := by
        rw [← Real.rpow_add hν_pos]; congr 1; ring
      have h3 : ν ^ (-(3 / 4 + σ / 2)) ≤ ν⁻¹ := by
        rw [← Real.rpow_neg_one ν]
        exact Real.rpow_le_rpow_of_exponent_ge hν_pos hν1 (by linarith)
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (h3.trans hν_inv_le) (by positivity)
    have hθo_exp : θ_o ^ 2 * θ_o ^ (-κ_re) * Real.exp (-γ * θ_o) ≤
        M_exp_bd * Real.exp (-((γ / 4) * (ν ^ (1 / 2 : ℝ))⁻¹)) := by
      have hcomb : θ_o ^ 2 * θ_o ^ (-κ_re) = θ_o ^ (2 - κ_re) := by
        rw [← Real.rpow_natCast θ_o 2, ← Real.rpow_add hθo_pos]; push_cast; ring_nf
      have h1 := rpow_mul_exp_le_half_exp_aniso hγ hθo1 M_bd (Nat.le_ceil _)
      have h2 : Real.exp (-(γ / 2) * θ_o) ≤ Real.exp (-((γ / 4) * (ν ^ (1 / 2 : ℝ))⁻¹)) := by
        apply Real.exp_le_exp.2
        have : (γ / 4) * (ν ^ (1 / 2 : ℝ))⁻¹ = (γ / 2) * (2 * ν ^ (1 / 2 : ℝ))⁻¹ := by
          rw [mul_inv]; ring
        rw [this]
        linarith only [mul_le_mul_of_nonneg_left hθo_ge_half (by positivity : 0 ≤ γ / 2)]
      rw [hcomb]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hM_exp_bd.le)
    have hpi_le : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
    have hnorm_uo :
        ‖(3 * Complex.I) * (aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ))‖ =
          3 * (Real.pi / 4) * c⁻¹ * (u_o ^ (-σ) * u_o ^ (-3 / 2 : ℝ)) *
            ‖P.gaugeFactor ν‖ * ‖quadQ d_o Z_o‖ := by
      unfold aPlus
      rw [hQo_eq]
      simp only [norm_mul, norm_div, norm_neg, Complex.norm_ofNat, Complex.norm_I,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_cpow_eq_rpow_re_of_pos huo_pos, Complex.neg_re,
        Real.norm_of_nonneg hc_pos.le, Real.norm_of_nonneg (Real.rpow_nonneg huo_pos.le _), c, σ]
      ring
    rw [hnorm_uo]
    calc 3 * (Real.pi / 4) * c⁻¹ * (u_o ^ (-σ) * u_o ^ (-3 / 2 : ℝ)) *
            ‖P.gaugeFactor ν‖ * ‖quadQ d_o Z_o‖
        ≤ 3 * 1 * c⁻¹ * (ν ^ (3 + 2 * σ) * (4 * θ_o ^ 2)) *
            ‖P.gaugeFactor ν‖ * (C_Z * Real.exp (-γ * θ_o) * θ_o ^ (-κ_re)) := by
          have p1 : 3 * (Real.pi / 4) * c⁻¹ * (u_o ^ (-σ) * u_o ^ (-3 / 2 : ℝ)) ≤
              3 * 1 * c⁻¹ * (ν ^ (3 + 2 * σ) * (4 * θ_o ^ 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hc_pos.le))
              huo_pow (by positivity) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right p1 (norm_nonneg _)) hQZo_bd
            (norm_nonneg _) (by positivity)
      _ = 12 * C_Z * scaleA P ν μ * (θ_o ^ 2 * θ_o ^ (-κ_re) * Real.exp (-γ * θ_o)) := by
          unfold scaleA; dsimp [c]; ring
      _ ≤ 12 * C_Z * scaleA P ν μ *
            (M_exp_bd * Real.exp (-((γ / 4) * (ν ^ (1 / 2 : ℝ))⁻¹))) :=
          mul_le_mul_of_nonneg_left hθo_exp (by positivity)
      _ = ((12 * C_Z * M_exp_bd) * Real.exp (-((γ / 4) * (ν ^ (1 / 2 : ℝ))⁻¹))) *
            scaleA P ν μ := by ring
      _ ≤ (ε / 2) * scaleA P ν μ := mul_le_mul_of_nonneg_right hBd_small.le hscaleA_nn
  -- Final assembly
  rw [halg_int, hIBP_sym]
  have hrew_diff :
      (-(∫ s in Ioi u_o,
          ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
            3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
              ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) +
        (3 * Complex.I) *
          ((μ + 3 / 2) * iA ν μ w - aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) -
        3 * Complex.I * (μ + 3 / 2) * iA ν μ w =
      -(∫ s in Ioi u_o,
          ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
            3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
              ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
        (3 * Complex.I) * (aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) := by ring
  rw [hrew_diff]
  calc ‖-(∫ s in Ioi u_o,
            ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
              3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
          (3 * Complex.I) * (aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ))‖
      ≤ ‖∫ s in Ioi u_o,
            ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
              3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ +
          ‖(3 * Complex.I) * (aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ))‖ := by
        simpa [norm_neg] using norm_sub_le
          (-(∫ s in Ioi u_o,
              ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
                3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
                  ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)))
          ((3 * Complex.I) * (aPlus ν μ w_ev u_o * ((u_o ^ (-3 / 2 : ℝ) : ℝ) : ℂ)))
    _ ≤ (ε / 2) * scaleA P ν μ + (ε / 2) * scaleA P ν μ := add_le_add hBd_def hBd_uo
    _ = ε * scaleA P ν μ := by ring

/-! ## Public Theorems (`PartIII-a:T22/7`) -/

/-- Combined stress-defect and anisotropy theorem (`eq:ct-stress-defect`, `eq:ct-anisotropy`). -/
theorem ctAnisotropyPair : CTStressDefect ∧ CTAnisotropy :=
  ⟨ctStressDefect_impl, ctAnisotropy_impl⟩

/-- Stress defect bound (`eq:ct-stress-defect`, SP 3380-3391). -/
theorem ctStressDefect : CTStressDefect := ctAnisotropyPair.1

/-- Anisotropy Mellin identity (`eq:ct-anisotropy`, SP 3392-3401). -/
theorem ctAnisotropy : CTAnisotropy := ctAnisotropyPair.2

end UnforcedLeray.Short.IIIa

end
