import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_2
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.MeridTestDense.MeridProj.CoreAndLift

/-!
# Meridional projection of phase tests (`MeridProjOfPhaseTest`, task `PartII-a:N04/3/3/2/2`)

Source of record: `the November 2 reference manuscript`,
lines 1477–1478 (the outer generator commutes with rotations and reflections fixing the axis, and
`O(2)`-averaging preserves smoothness across the axis while killing swirl) and lines 3289–3352
(exact outer meridional lift `J_ε` and meridional vector generator `A_ε^vec`).

Given a smooth `P`-periodic phase test `ψ` (`P = 2εc`), we construct its `O(2)`-averaged chart
profile `u := meridProjProfile ε ψ`:
1. `isMeridCoreTest_meridProjProfile` (`CoreAndLift.lean`): `u` and `u' := meridProjProfile ε (phaseGen ν ε ψ)`
   are axis-reaching core tests (`IsMeridCoreTest ε c`), hence square-integrable on `measureH c`
   by `meridCoreTestMemLp`;
2. `meridProjProfile_phaseGen` (`CoreAndLift.lean`): `u' = AepsVecC ν ε u` on `{s > 0}`, hence
   `measureH c`-almost everywhere;
3. `adjoint_liftVec_eq_meridProjProfile` (below): angular averaging over `Axi.angμ` and the
   weighted pushforward `B0220.map_cellChart_jDensity` identify `(B0223.liftVec hε hc hP)^* Φ`
   with the `HSpace c MeridC` class of `meridProjProfile ε φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.MeridProjAux

open UnforcedLeray.PhaseSpace

private theorem toCell_measurableEmbedding (P : ℝ) [Fact (0 < P)] :
    MeasurableEmbedding (B0223.toCell P) := by
  have he : MeasurableEmbedding
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Space)
        (AddCircle.measurableEquivIoc P 0)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Space)
        (AddCircle.measurableEquivIoc P 0)).measurableEmbedding
  have h1 : MeasurableEmbedding
      (Prod.map (id : Space → Space)
        (Subtype.val : Ioc (0 : ℝ) (0 + P) → ℝ)) :=
    MeasurableEmbedding.prodMap MeasurableEmbedding.id
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc)
  have h2 := h1.comp he
  have hfun : B0223.toCell P =
      Prod.map (id : Space → Space)
        (Subtype.val : Ioc (0 : ℝ) (0 + P) → ℝ) ∘
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Space)
        (AddCircle.measurableEquivIoc P 0)) := rfl
  rw [hfun]
  exact h2

private theorem setIntegral_Ioc_add_periodic_complex {f : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hf : Function.Periodic f T) (β : ℝ) :
    ∫ α in Ioc 0 T, f (α + β) = ∫ θ in Ioc 0 T, f θ := by
  have h1 : ∫ α in Ioc 0 T, f (α + β) = ∫ θ in Ioc β (β + T), f θ := by
    have := (measurePreserving_add_right (volume : Measure ℝ) β).setIntegral_preimage_emb
      (measurableEmbedding_addRight β) f (Ioc β (β + T))
    rwa [preimage_add_const_Ioc, sub_self, add_sub_cancel_left] at this
  rw [h1]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  have h2 := IsAddFundamentalDomain.setIntegral_eq (isAddFundamentalDomain_Ioc hT β)
    (isAddFundamentalDomain_Ioc hT 0) hf.map_vadd_zmultiples
  rwa [zero_add] at h2

private theorem integral_angμ_add_right_complex {f : ℝ → ℂ}
    (hf : Function.Periodic f (2 * Real.pi)) (β : ℝ) :
    ∫ α, f (α + β) ∂Axi.angμ = ∫ θ, f θ ∂Axi.angμ := by
  simp only [Axi.angμ, integral_smul_measure]
  rw [setIntegral_Ioc_add_periodic_complex Real.two_pi_pos hf β]

private theorem integral_complex_eq_angμ_avg {ε c : ℝ} {G : Space × ℝ → ℂ}
    (hGm : Measurable G) (hG : Integrable G (B0220.physMeasure ε c)) :
    ∫ y, G y ∂B0220.physMeasure ε c =
      ∫ y, (∫ θ, G (B0226.rotPt θ (B0220.radius y.1) (y.1 2), y.2) ∂Axi.angμ)
        ∂B0220.physMeasure ε c := by
  set μ := B0220.physMeasure ε c with hμ
  have : SFinite μ := by
    rw [hμ, B0220.physMeasure]
    infer_instance
  set Ga : ℝ × (Space × ℝ) → ℂ := fun p => G (B0226.rotZ p.1 p.2.1, p.2.2) with hGa
  have hGam : Measurable Ga := hGm.comp B0226.continuous_rotZ_param.measurable
  have hGa_int : Integrable Ga (Axi.angμ.prod μ) := by
    refine ⟨hGam.aestronglyMeasurable, ?_⟩
    change ∫⁻ p, ‖Ga p‖ₑ ∂(Axi.angμ.prod μ) < ⊤
    rw [lintegral_prod _ hGam.enorm.aemeasurable]
    have h1 : ∀ α : ℝ, ∫⁻ y, ‖Ga (α, y)‖ₑ ∂μ = ∫⁻ y, ‖G y‖ₑ ∂μ := fun α =>
      B0226.lintegral_comp_rotZ α ε c (fun y => ‖G y‖ₑ)
    simp_rw [h1]
    rw [lintegral_const, measure_univ, mul_one]
    exact hG.2
  have ha : ∀ α : ℝ, ∫ y, Ga (α, y) ∂μ = ∫ y, G y ∂μ := fun α =>
    (B0226.measurePreserving_rotProd α ε c).integral_comp
      (B0226.rotProd α).measurableEmbedding G
  have hc_shift : ∀ y : Space × ℝ, ∫ α, Ga (α, y) ∂Axi.angμ =
      ∫ θ, G (B0226.rotPt θ (B0220.radius y.1) (y.1 2), y.2) ∂Axi.angμ := by
    intro y
    obtain ⟨β, hβ⟩ := B0226.exists_rotZ_eq y
    simp only [hGa, hβ]
    exact integral_angμ_add_right_complex (B0226.periodic_rotPt_param G y) β
  calc ∫ y, G y ∂μ
      = ∫ _α, (∫ y, G y ∂μ) ∂Axi.angμ := by simp
    _ = ∫ α, (∫ y, Ga (α, y) ∂μ) ∂Axi.angμ := by simp_rw [ha]
    _ = ∫ y, (∫ α, Ga (α, y) ∂Axi.angμ) ∂μ :=
          integral_integral_swap (f := fun α y => Ga (α, y)) hGa_int
    _ = ∫ y, (∫ θ, G (B0226.rotPt θ (B0220.radius y.1) (y.1 2), y.2) ∂Axi.angμ) ∂μ :=
          integral_congr_ae (ae_of_all _ hc_shift)

private theorem measurable_comp_cellChart (ε c : ℝ) {f : B0220.Profile → B0223.MeridC}
    (hf : Measurable f) :
    Measurable fun y : Space × ℝ => f (B0220.cellChart ε c y) :=
  hf.comp (B0220.measurable_cellChart ε c)

private theorem measurable_frameC_comp {w : Space × ℝ → B0223.MeridC} (hw : Measurable w) :
    Measurable fun y : Space × ℝ => B0223.frameC y.1 (w y) := by
  have h0 : Measurable fun y : Space × ℝ => w y 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).measurable.comp hw
  have h1 : Measurable fun y : Space × ℝ => w y 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).measurable.comp hw
  have heq : (fun y : Space × ℝ => B0223.frameC y.1 (w y)) =
      fun y => w y 0 • B0223.unitRC y.1 + w y 1 • B0223.unitZC := rfl
  rw [heq]
  exact (h0.smul (B0223.measurable_unitRC.comp measurable_fst)).add (h1.smul_const _)

private theorem measurable_inner_spaceC {f g : Space × ℝ → B0223.SpaceC}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun y : Space × ℝ => inner ℂ (f y) (g y) := by
  have heq : (fun y : Space × ℝ => inner ℂ (f y) (g y)) =
      (fun p : B0223.SpaceC × B0223.SpaceC => inner ℂ p.1 p.2) ∘ (fun y => (f y, g y)) := rfl
  rw [heq]
  exact (Continuous.inner (𝕜 := ℂ) continuous_fst continuous_snd).measurable.comp (hf.prodMk hg)

/-- **Theorem B (`adjoint_liftVec_eq_meridProjProfile`)**: the Hilbert adjoint of `B0223.liftVec`
maps the `X SpaceC P` class of any phase test `φ` to the `HSpace c MeridC` class of
`meridProjProfile ε φ`. -/
theorem adjoint_liftVec_eq_meridProjProfile {c ε P : ℝ} (hc : 0 < c) (hε : 0 < ε) [Fact (0 < P)]
    (hP : P = 2 * ε * c) {φ : ℝ × Space → CVec3} (hφ : IsPhaseTest P φ)
    (Φ : B0223.X B0223.SpaceC P)
    (hΦ : (Φ : B0223.PSpace P → B0223.SpaceC) =ᵐ[volume]
      fun z => φ ((B0223.toCell P z).2, (B0223.toCell P z).1))
    (U : B0220.HSpace c B0223.MeridC)
    (hU : (U : B0220.Profile → B0223.MeridC) =ᵐ[B0220.measureH c] meridProjProfile ε φ) :
    ContinuousLinearMap.adjoint (B0223.liftVec hε hc hP).toContinuousLinearMap Φ = U := by
  refine ext_inner_left ℂ fun b => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (B0223.liftVec hε hc hP b) Φ = inner ℂ b U
  set G : Space × ℝ → ℂ := fun y =>
    inner ℂ ((B0220.jConst ε * B0220.liftA y.1 : ℝ) •
      B0223.frameC y.1 ((b : B0220.Profile → B0223.MeridC) (B0220.cellChart ε c y)))
      (φ (y.2, y.1))
  have hkey : (fun z : B0223.PSpace P => inner ℂ (B0223.liftVec hε hc hP b z) (Φ z)) =ᵐ[volume]
      fun z => G (B0223.toCell P z) := by
    filter_upwards [B0223.coeFn_liftVec hε hc hP b, hΦ] with z hz1 hz2
    rw [hz1, hz2, smul_smul]
    rfl
  have hGm : Measurable G := by
    have hb_m := measurable_comp_cellChart ε c (Lp.stronglyMeasurable b).measurable
    have hfr_m := measurable_frameC_comp hb_m
    have hv1_m : Measurable fun y : Space × ℝ =>
        (B0220.jConst ε * B0220.liftA y.1 : ℝ) •
          B0223.frameC y.1 ((b : B0220.Profile → B0223.MeridC) (B0220.cellChart ε c y)) := by
      have hk_m : Measurable fun y : Space × ℝ => B0220.jConst ε * B0220.liftA y.1 :=
        (B0220.measurable_liftA.comp measurable_fst).const_mul (B0220.jConst ε)
      exact hk_m.smul hfr_m
    have hv2_m : Measurable fun y : Space × ℝ => (φ (y.2, y.1) : B0223.SpaceC) :=
      (hφ.continuous.comp (continuous_snd.prodMk continuous_fst)).measurable
    exact measurable_inner_spaceC hv1_m hv2_m
  have hG_ps : Integrable (fun z => G (B0223.toCell P z))
      (volume : Measure (B0223.PSpace P)) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (B0223.liftVec hε hc hP b) Φ).congr hkey
  have hG_int : Integrable G (B0220.physMeasure ε c) := by
    rw [B0223.physMeasure_eq hP, ← (B0223.mp_toCell (P := P)).map_eq]
    exact (toCell_measurableEmbedding P).integrable_map_iff.mpr hG_ps
  have hlhs : inner ℂ (B0223.liftVec hε hc hP b) Φ = ∫ y, G y ∂B0220.physMeasure ε c := by
    calc inner ℂ (B0223.liftVec hε hc hP b) Φ
        = ∫ z, inner ℂ (B0223.liftVec hε hc hP b z) (Φ z) := MeasureTheory.L2.inner_def _ _
      _ = ∫ z, G (B0223.toCell P z) := integral_congr_ae hkey
      _ = ∫ y, G y ∂((volume : Measure (B0223.PSpace P)).map (B0223.toCell P)) := by
            rw [(toCell_measurableEmbedding P).integral_map]
      _ = ∫ y, G y ∂((volume : Measure (Space × ℝ)).restrict (univ ×ˢ Ioc 0 P)) := by
            rw [(B0223.mp_toCell (P := P)).map_eq]
      _ = ∫ y, G y ∂B0220.physMeasure ε c := by
            rw [B0223.physMeasure_eq hP]
  set h : B0220.Profile → ℂ := fun p =>
    inner ℂ ((b : B0220.Profile → B0223.MeridC) p) (meridProjProfile ε φ p)
  have hper : ∀ τ' x', φ (τ' + 2 * ε * c, x') = φ (τ', x') := by
    simpa [hP] using hφ.periodic
  have hpt_ae : (fun y : Space × ℝ =>
      ∫ θ, G (B0226.rotPt θ (B0220.radius y.1) (y.1 2), y.2) ∂Axi.angμ) =ᵐ[B0220.physMeasure ε c]
      fun y => ((B0220.jConst ε * B0220.liftA y.1) ^ 2 : ℝ) • h (B0220.cellChart ε c y) := by
    filter_upwards [B0220.ae_physMeasure ε c] with ⟨x, τ⟩ ⟨hr, _hτ⟩
    dsimp only
    set r := B0220.radius x with hr_def
    have hr_pos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
    have hrot_pt : ∀ θ : ℝ, G (B0226.rotPt θ r (x 2), τ) =
        ((B0220.jConst ε * B0220.liftA x : ℝ) : ℂ) *
          inner ℂ ((b : B0220.Profile → B0223.MeridC) (B0220.cellChart ε c (x, τ)))
            (projThetaC θ (φ (τ, B0226.rotPt θ r (x 2)))) := by
      intro θ
      have hrad : B0220.radius (B0226.rotPt θ r (x 2)) = r :=
        B0226.radius_rotPt hr_pos.le θ (x 2)
      have hliftA : B0220.liftA (B0226.rotPt θ r (x 2)) = B0220.liftA x := by
        rw [B0220.liftA, B0220.liftA, hrad, hr_def]
      have hcc : B0220.cellChart ε c (B0226.rotPt θ r (x 2), τ) = B0220.cellChart ε c (x, τ) := by
        simp only [B0220.cellChart, B0220.ageS, B0220.cellQ, B0220.etaCoord, hrad,
          B0226.rotPt_apply_two]
        rw [hr_def]
      dsimp only [G]
      rw [hliftA, hcc, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal,
        inner_frameC_rotPt hr_pos θ (x 2)]
    simp_rw [hrot_pt]
    rw [integral_const_mul]
    have hrot_cont : Continuous fun θ : ℝ => B0226.rotPt θ r (x 2) := by
      have heq : (fun θ : ℝ => B0226.rotPt θ r (x 2)) = fun θ =>
          (r * Real.cos θ) • coordinateVector 0 + (r * Real.sin θ) • coordinateVector 1 +
            x 2 • coordinateVector 2 := funext fun θ => B0226.rotPt_eq_comb θ r (x 2)
      rw [heq]
      fun_prop
    have hf_cont : Continuous fun θ : ℝ => projThetaC θ (φ (τ, B0226.rotPt θ r (x 2))) :=
      continuous_projThetaC_comp (hφ.continuous.comp (continuous_const.prodMk hrot_cont))
    have hf_int : Integrable (fun θ => projThetaC θ (φ (τ, B0226.rotPt θ r (x 2)))) Axi.angμ :=
      integrable_angμ_of_continuous hf_cont
    have hinn_comm : ∫ θ, inner ℂ ((b : B0220.Profile → B0223.MeridC) (B0220.cellChart ε c (x, τ)))
        (projThetaC θ (φ (τ, B0226.rotPt θ r (x 2)))) ∂Axi.angμ =
        inner ℂ ((b : B0220.Profile → B0223.MeridC) (B0220.cellChart ε c (x, τ)))
          (∫ θ, projThetaC θ (φ (τ, B0226.rotPt θ r (x 2))) ∂Axi.angμ) :=
      (innerSL ℂ ((b : B0220.Profile → B0223.MeridC) (B0220.cellChart ε c (x, τ)))).integral_comp_comm
        hf_int
    rw [hinn_comm]
    set q := B0220.chart ε (x, τ)
    have hq1 : 0 < q.1 := by
      show 0 < (r ^ 2)⁻¹
      positivity
    have hsqrt : √(q.1⁻¹) = r := by
      show √(((r ^ 2)⁻¹)⁻¹) = r
      rw [inv_inv, Real.sqrt_sq hr_pos.le]
    have hz_r : ε * q.2.2 * r = x 2 := by
      simp only [q, B0220.chart, B0220.etaCoord, hr_def]
      have hε0 : ε ≠ 0 := hε.ne'
      have hr0 : B0220.radius x ≠ 0 := hr
      field_simp
    have hτ_q : 2 * ε * q.2.1 + Real.log q.1 = τ := by
      simp only [q, B0220.chart, B0220.cellQ, B0220.ageS]
      have hε0 : ε ≠ 0 := hε.ne'
      rw [Real.log_inv, Real.log_pow]
      field_simp
      ring
    have hmp_cc : meridProjProfile ε φ (B0220.cellChart ε c (x, τ)) = meridProjProfile ε φ q :=
      B0220.periodic_reduceIoc_eq (meridProjProfile ε φ) (qPeriodic_meridProjProfile hper)
        (B0220.ageS x) (B0220.cellQ ε x τ) (B0220.etaCoord ε x)
    have hmp_q : meridProjProfile ε φ q =
        ((B0220.jConst ε)⁻¹ * r : ℝ) •
          ∫ θ, projThetaC θ (φ (τ, B0226.rotPt θ r (x 2))) ∂Axi.angμ := by
      simp only [meridProjProfile, hq1, ↓reduceIte, hsqrt, hz_r, hτ_q]
    have hsc : (B0220.jConst ε * B0220.liftA x) ^ 2 * ((B0220.jConst ε)⁻¹ * r) =
        B0220.jConst ε * B0220.liftA x := by
      have hj : B0220.jConst ε ≠ 0 := by
        unfold B0220.jConst
        positivity
      have hr0 : B0220.radius x ≠ 0 := hr
      simp only [B0220.liftA, hr_def]
      field_simp
    dsimp only [h]
    rw [hmp_cc, hmp_q, ← Complex.coe_smul ((B0220.jConst ε)⁻¹ * r) _, inner_smul_right,
      ← Complex.coe_smul ((B0220.jConst ε * B0220.liftA x) ^ 2) _, smul_eq_mul, ← mul_assoc]
    have hscC : (((B0220.jConst ε * B0220.liftA x) ^ 2 : ℝ) : ℂ) *
        (((B0220.jConst ε)⁻¹ * r : ℝ) : ℂ) =
        ((B0220.jConst ε * B0220.liftA x : ℝ) : ℂ) := by
      exact_mod_cast hsc
    rw [hscC]
  -- Push forward from `physMeasure ε c` to `measureH c` via `map_cellChart_jDensity`
  have hh_ae : h =ᵐ[B0220.measureH c]
      fun p => inner ℂ ((b : B0220.Profile → B0223.MeridC) p) ((U : B0220.Profile → B0223.MeridC) p) := by
    filter_upwards [hU] with p hp
    dsimp only [h]
    rw [hp]
  have hh_int : Integrable h (B0220.measureH c) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) b U).congr hh_ae.symm
  set D : Space × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((B0220.jConst ε * B0220.liftA y.1) ^ 2)
  have hDm : Measurable D :=
    ENNReal.measurable_ofReal.comp
      (((B0220.measurable_liftA.comp measurable_fst).const_mul _).pow_const 2)
  have hDlt : ∀ᵐ y ∂B0220.physMeasure ε c, D y < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hpush : ∫ y, ((B0220.jConst ε * B0220.liftA y.1) ^ 2 : ℝ) • h (B0220.cellChart ε c y)
      ∂B0220.physMeasure ε c = ∫ p, h p ∂B0220.measureH c := by
    symm
    calc ∫ p, h p ∂B0220.measureH c
        = ∫ p, h p ∂(((B0220.physMeasure ε c).withDensity D).map (B0220.cellChart ε c)) := by
            rw [B0220.map_cellChart_jDensity hε hc]
      _ = ∫ y, h (B0220.cellChart ε c y) ∂((B0220.physMeasure ε c).withDensity D) := by
            refine integral_map (B0220.measurable_cellChart ε c).aemeasurable ?_
            rw [B0220.map_cellChart_jDensity hε hc]
            exact hh_int.aestronglyMeasurable
      _ = ∫ y, (D y).toReal • h (B0220.cellChart ε c y) ∂B0220.physMeasure ε c :=
            integral_withDensity_eq_integral_toReal_smul hDm hDlt _
      _ = ∫ y, ((B0220.jConst ε * B0220.liftA y.1) ^ 2 : ℝ) • h (B0220.cellChart ε c y)
            ∂B0220.physMeasure ε c := by
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            dsimp only [D]
            rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hlhs, integral_complex_eq_angμ_avg hGm hG_int, integral_congr_ae hpt_ae, hpush,
    integral_congr_ae hh_ae, ← MeasureTheory.L2.inner_def]

end UnforcedLeray.Short.PartIIa.MeridProjAux

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- **Main Theorem (`meridProjOfPhaseTest`, task `PartII-a:N04/3/3/2/2`)**:
the adjoint of `B0223.liftVec` maps the `L²` classes of any phase test `ψ` and of
`phaseGen ν ε ψ` to the `HSpace c MeridC` classes of an axis-reaching meridional core test `u`
and of `AepsVecC ν ε u`. -/
theorem meridProjOfPhaseTest : MeridProjOfPhaseTest := by
  intro ν c ε _hν hc hε P _ hP ψ hψ Ψ Ψ' hΨ hΨ'
  have hPpos : 0 < P := Fact.out
  set u : B0220.Profile → B0223.MeridC := MeridProjAux.meridProjProfile ε ψ
  have hu : IsMeridCoreTest ε c u :=
    MeridProjAux.isMeridCoreTest_meridProjProfile hε hPpos hP hψ
  have hψ' : IsPhaseTest P (phaseGen ν ε ψ) := MeridProjAux.isPhaseTest_phaseGen ν ε hψ
  set u' : B0220.Profile → B0223.MeridC := MeridProjAux.meridProjProfile ε (phaseGen ν ε ψ)
  have hu' : IsMeridCoreTest ε c u' :=
    MeridProjAux.isMeridCoreTest_meridProjProfile hε hPpos hP hψ'
  have hmemU : MemLp u 2 (B0220.measureH c) := meridCoreTestMemLp c ε hc hε u hu
  have hmemAU : MemLp u' 2 (B0220.measureH c) := meridCoreTestMemLp c ε hc hε u' hu'
  set U : B0220.HSpace c B0223.MeridC := hmemU.toLp u
  set AU : B0220.HSpace c B0223.MeridC := hmemAU.toLp u'
  have hU : (U : B0220.Profile → B0223.MeridC) =ᵐ[B0220.measureH c] u := hmemU.coeFn_toLp
  have hAU' : (AU : B0220.Profile → B0223.MeridC) =ᵐ[B0220.measureH c] u' := hmemAU.coeFn_toLp
  have hAU : (AU : B0220.Profile → B0223.MeridC) =ᵐ[B0220.measureH c] AepsVecC ν ε u := by
    filter_upwards [hAU', B0220.ae_cell_measureH c] with p hp1 hp2
    rw [hp1]
    exact MeridProjAux.meridProjProfile_phaseGen ν hε hPpos hP hψ hp2.1
  refine ⟨u, U, AU, hu, hU, hAU, ?_, ?_⟩
  · exact MeridProjAux.adjoint_liftVec_eq_meridProjProfile hc hε hP hψ Ψ hΨ U hU
  · exact MeridProjAux.adjoint_liftVec_eq_meridProjProfile hc hε hP hψ' Ψ' hΨ' AU hAU'

#print axioms meridProjOfPhaseTest

end UnforcedLeray.Short.PartIIa
