import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_9

/-!
# Part III-a, `PartIII-a:T21/3/9/1`: linearity of linearised flows

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Statement `LinFlowComb` is in `Sub/PartIIIa_T21_3_9.lean`. Every field of `IsLinFlowOn` is stable
under `(f, ω, u) ↦ (f₁ + I f₂, ω₁ + I ω₂, u₁ + I u₂)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Real-valued `L²(cellMeasure)` function against a cylinder test (via `X_{-m}` pairing). -/
theorem lfc_integrableOn_re_test {c m : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun x => g x * φ x) (B0579.cell c) := by
  have h := B0579.integrableOn_mul_neg c m (hg.toLp g) (B0579.testLp c (-m) hφ)
  have e1 : ⇑(hg.toLp g) =ᵐ[volume.restrict (B0579.cell c)] g :=
    (B0579.ac_cellMeasure c m).ae_eq (MemLp.coeFn_toLp hg)
  have e2 : ⇑(B0579.testLp c (-m) hφ) =ᵐ[volume.restrict (B0579.cell c)] φ :=
    B0579.coeFn_testLp c (-m) hφ
  refine h.congr_fun_ae ?_
  filter_upwards [e1, e2] with x h1 h2
  simp only [h1, h2]

/-- Complex-valued `L²(cellMeasure)` function against a (real) cylinder test. -/
theorem lfc_integrableOn_cplx_test {c m : ℝ} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure c m))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun x => g x * (φ x : ℂ)) (B0579.cell c) := by
  have h1 := lfc_integrableOn_re_test hg.re hφ
  have h2 := lfc_integrableOn_re_test hg.im hφ
  have h := Integrable.add (Integrable.ofReal h1) (Integrable.const_mul (Integrable.ofReal h2) Complex.I)
  refine h.congr (Eventually.of_forall fun x => ?_)
  show ((RCLike.re (g x) * φ x : ℝ) : ℂ) + Complex.I * ((RCLike.im (g x) * φ x : ℝ) : ℂ)
    = g x * (φ x : ℂ)
  simp only [RCLike.re_to_complex, RCLike.im_to_complex]
  conv_rhs => rw [← Complex.re_add_im (g x)]
  push_cast
  ring

/-- Complex-valued `L²(volume.restrict cell)` function against a cylinder test. -/
theorem lfc_integrableOn_vol_test {c : ℝ} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c)))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun x => g x * (φ x : ℂ)) (B0579.cell c) := by
  obtain ⟨R, hR⟩ := hφ.vanish
  have hφ2 : MemLp φ 2 (volume.restrict (B0579.cell c)) :=
    B0579.memLp_cell_of_continuous hφ.continuous (B0579.isCompact_box c R) hR
  exact hg.integrable_mul hφ2.ofReal

theorem lfc_integral_comb {S : Set (ℝ × ℝ)} (g₁ g₂ : ℝ × ℝ → ℂ)
    (h₁ : IntegrableOn g₁ S) (h₂ : IntegrableOn g₂ S) :
    ∫ x in S, (g₁ x + Complex.I * g₂ x) = (∫ x in S, g₁ x) + Complex.I * ∫ x in S, g₂ x := by
  rw [integral_add h₁ (Integrable.const_mul h₂ Complex.I), integral_const_mul]

theorem lfc_integral_comb_mul {S : Set (ℝ × ℝ)} (g₁ g₂ φ : ℝ × ℝ → ℂ)
    (h₁ : IntegrableOn (fun x => g₁ x * φ x) S) (h₂ : IntegrableOn (fun x => g₂ x * φ x) S) :
    ∫ x in S, (g₁ x + Complex.I * g₂ x) * φ x
      = (∫ x in S, g₁ x * φ x) + Complex.I * ∫ x in S, g₂ x * φ x := by
  have e : ∀ x, (g₁ x + Complex.I * g₂ x) * φ x = g₁ x * φ x + Complex.I * (g₂ x * φ x) :=
    fun x => by ring
  simp only [e]
  exact lfc_integral_comb (fun x => g₁ x * φ x) (fun x => g₂ x * φ x) h₁ h₂

theorem lfc_flowIntegrand_comb {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (a b : ℝ × ℝ → ℂ) (v w : ℝ × ℝ → Fin 2 → ℂ) (r : ℝ) (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    flowIntegrand tr (fun y => a y + Complex.I * b y)
        (fun y j => v y j + Complex.I * w y j) r φ x
      = flowIntegrand tr a v r φ x + Complex.I * flowIntegrand tr b w r φ x := by
  simp only [flowIntegrand]
  ring

theorem lfc_xNorm_comb {c m : ℝ} {a₁ a₂ : ℝ × ℝ → ℂ}
    (ha₁ : MemLp a₁ 2 (B0579.cellMeasure c m)) (ha₂ : MemLp a₂ 2 (B0579.cellMeasure c m)) :
    xNorm c m (fun x => a₁ x + Complex.I * a₂ x) ≤ xNorm c m a₁ + xNorm c m a₂ := by
  unfold xNorm
  have h := eLpNorm_add_le ha₁.aestronglyMeasurable
    (ha₂.aestronglyMeasurable.const_mul Complex.I) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine le_trans h (le_of_eq ?_)
  have hf : (fun x => Complex.I * a₂ x) = Complex.I • a₂ := by
    funext x
    simp [smul_eq_mul]
  have hI : ‖Complex.I‖ₑ = 1 := by
    first
    | simp
    | rw [← ofReal_norm_eq_enorm, Complex.norm_I, ENNReal.ofReal_one]
  rw [hf, eLpNorm_const_smul, hI, one_mul]

theorem linFlowComb : UnforcedLeray.Short.IIIa.Exist.LinFlowComb := by
  intro ν c m tr t T f₁ f₂ ω₁ ω₂ u₁ u₂ h₁ h₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- initial
    filter_upwards [h₁.initial, h₂.initial] with x hx1 hx2
    show ω₁ t x + Complex.I * ω₂ t x = f₁ x + Complex.I * f₂ x
    rw [hx1, hx2]
  · -- memX
    intro s hs
    exact (h₁.memX s hs).add ((h₂.memX s hs).const_mul Complex.I)
  · -- strongCont
    intro s hs
    have hA := h₁.strongCont s hs
    have hB := h₂.strongCont s hs
    have hC := hA.add hB
    rw [add_zero] at hC
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC ?_ ?_
    · exact Eventually.of_forall fun _ => zero_le
    · filter_upwards [self_mem_nhdsWithin] with s' hs'
      have hsplit : (fun y x => ω₁ y x + Complex.I * ω₂ y x) s' -
          (fun y x => ω₁ y x + Complex.I * ω₂ y x) s
          = fun x => (ω₁ s' - ω₁ s) x + Complex.I * (ω₂ s' - ω₂ s) x := by
        funext x
        simp only [Pi.sub_apply]
        ring
      rw [hsplit]
      exact lfc_xNorm_comb ((h₁.memX s' hs').sub (h₁.memX s hs))
        ((h₂.memX s' hs').sub (h₂.memX s hs))
  · -- biotSavart
    intro s hs
    obtain ⟨b1, b2, b3⟩ := h₁.biotSavart s hs
    obtain ⟨d1, d2, d3⟩ := h₂.biotSavart s hs
    unfold IsBiotSavart
    refine ⟨fun j => ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · exact (b1 j).add ((d1 j).const_mul Complex.I)
    · -- zero velocity circulation
      have A1 : IntegrableOn (fun x => u₁ s x 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
        lfc_integrableOn_vol_test (b1 0) (hψ.pd 0)
      have B1 : IntegrableOn (fun x => u₁ s x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
        lfc_integrableOn_vol_test (b1 1) (hψ.pd 1)
      have A2 : IntegrableOn (fun x => u₂ s x 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
        lfc_integrableOn_vol_test (d1 0) (hψ.pd 0)
      have B2 : IntegrableOn (fun x => u₂ s x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
        lfc_integrableOn_vol_test (d1 1) (hψ.pd 1)
      have hI1 : IntegrableOn (fun x => u₁ s x 0 * (B0579.pd 0 ψ x : ℂ)
          + u₁ s x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add A1 B1
      have hI2 : IntegrableOn (fun x => u₂ s x 0 * (B0579.pd 0 ψ x : ℂ)
          + u₂ s x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add A2 B2
      have e : ∀ x, (u₁ s x 0 + Complex.I * u₂ s x 0) * (B0579.pd 0 ψ x : ℂ)
          + (u₁ s x 1 + Complex.I * u₂ s x 1) * (B0579.pd 1 ψ x : ℂ)
          = (u₁ s x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ s x 1 * (B0579.pd 1 ψ x : ℂ))
            + Complex.I * (u₂ s x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ s x 1 * (B0579.pd 1 ψ x : ℂ)) :=
        fun x => by ring
      show ∫ x in B0579.cell c, ((u₁ s x 0 + Complex.I * u₂ s x 0) * (B0579.pd 0 ψ x : ℂ)
          + (u₁ s x 1 + Complex.I * u₂ s x 1) * (B0579.pd 1 ψ x : ℂ)) = 0
      simp only [e]
      rw [lfc_integral_comb _ _ hI1 hI2, b2 ψ hψ, d2 ψ hψ]
      simp
    · -- Biot-Savart curl identity
      have Lw1 : IntegrableOn (fun x => ω₁ s x * (ψ x : ℂ)) (B0579.cell c) :=
        lfc_integrableOn_cplx_test (h₁.memX s hs) hψ
      have Lw2 : IntegrableOn (fun x => ω₂ s x * (ψ x : ℂ)) (B0579.cell c) :=
        lfc_integrableOn_cplx_test (h₂.memX s hs) hψ
      have C1 : IntegrableOn (fun x => u₁ s x 0 * (B0579.pd 1 ψ x : ℂ)
          - u₁ s x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
        Integrable.sub (lfc_integrableOn_vol_test (b1 0) (hψ.pd 1))
          (lfc_integrableOn_vol_test (b1 1) (hψ.pd 0))
      have C2 : IntegrableOn (fun x => u₂ s x 0 * (B0579.pd 1 ψ x : ℂ)
          - u₂ s x 1 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
        Integrable.sub (lfc_integrableOn_vol_test (d1 0) (hψ.pd 1))
          (lfc_integrableOn_vol_test (d1 1) (hψ.pd 0))
      have e : ∀ x, (u₁ s x 0 + Complex.I * u₂ s x 0) * (B0579.pd 1 ψ x : ℂ)
          - (u₁ s x 1 + Complex.I * u₂ s x 1) * (B0579.pd 0 ψ x : ℂ)
          = (u₁ s x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ s x 1 * (B0579.pd 0 ψ x : ℂ))
            + Complex.I * (u₂ s x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ s x 1 * (B0579.pd 0 ψ x : ℂ)) :=
        fun x => by ring
      show ∫ x in B0579.cell c, (ω₁ s x + Complex.I * ω₂ s x) * (ψ x : ℂ)
          = ∫ x in B0579.cell c, ((u₁ s x 0 + Complex.I * u₂ s x 0) * (B0579.pd 1 ψ x : ℂ)
            - (u₁ s x 1 + Complex.I * u₂ s x 1) * (B0579.pd 0 ψ x : ℂ))
      simp only [e]
      rw [lfc_integral_comb_mul _ _ _ Lw1 Lw2, lfc_integral_comb _ _ C1 C2, b3 ψ hψ, d3 ψ hψ]
  · -- integrable
    intro φ hφ r hr
    have h1 := h₁.integrable φ hφ r hr
    have h2 := h₂.integrable φ hφ r hr
    have h := Integrable.add h1 (Integrable.const_mul h2 Complex.I)
    refine IntegrableOn.congr_fun h (fun x _ => ?_) (B0579.measurableSet_cell c)
    exact (lfc_flowIntegrand_comb tr (ω₁ r) (ω₂ r) (u₁ r) (u₂ r) r φ x).symm
  · -- timeIntegrable
    intro φ hφ s hs
    have htT : t ∈ Icc t T := ⟨le_rfl, hs.1.trans hs.2⟩
    have hsub : uIcc t s ⊆ Icc t T := Set.uIcc_subset_Icc htT hs
    have hG : ∀ r ∈ Icc t T,
        (∫ x in B0579.cell c, flowIntegrand tr (fun y => ω₁ r y + Complex.I * ω₂ r y)
            (fun y j => u₁ r y j + Complex.I * u₂ r y j) r φ x)
          = (∫ x in B0579.cell c, flowIntegrand tr (ω₁ r) (u₁ r) r φ x)
            + Complex.I * ∫ x in B0579.cell c, flowIntegrand tr (ω₂ r) (u₂ r) r φ x := by
      intro r hr
      simp only [lfc_flowIntegrand_comb]
      exact lfc_integral_comb _ _ (h₁.integrable φ hφ r hr) (h₂.integrable φ hφ r hr)
    have hint1 := h₁.timeIntegrable φ hφ s hs
    have hint2 := h₂.timeIntegrable φ hφ s hs
    refine intervalIntegrable_iff.2 ?_
    refine (intervalIntegrable_iff.1 (hint1.add (hint2.const_mul Complex.I))).congr_fun
      (fun r hr => ?_) measurableSet_uIoc
    exact (hG r (hsub (uIoc_subset_uIcc hr))).symm
  · -- weak
    intro φ hφ s hs
    have htT : t ∈ Icc t T := ⟨le_rfl, hs.1.trans hs.2⟩
    have hsub : uIcc t s ⊆ Icc t T := Set.uIcc_subset_Icc htT hs
    have hG : ∀ r ∈ Icc t T,
        (∫ x in B0579.cell c, flowIntegrand tr (fun y => ω₁ r y + Complex.I * ω₂ r y)
            (fun y j => u₁ r y j + Complex.I * u₂ r y j) r φ x)
          = (∫ x in B0579.cell c, flowIntegrand tr (ω₁ r) (u₁ r) r φ x)
            + Complex.I * ∫ x in B0579.cell c, flowIntegrand tr (ω₂ r) (u₂ r) r φ x := by
      intro r hr
      simp only [lfc_flowIntegrand_comb]
      exact lfc_integral_comb _ _ (h₁.integrable φ hφ r hr) (h₂.integrable φ hφ r hr)
    have hint1 := h₁.timeIntegrable φ hφ s hs
    have hint2 := h₂.timeIntegrable φ hφ s hs
    have hTI : (∫ r in t..s, ∫ x in B0579.cell c, flowIntegrand tr (fun y => ω₁ r y + Complex.I * ω₂ r y)
            (fun y j => u₁ r y j + Complex.I * u₂ r y j) r φ x)
          = (∫ r in t..s, ∫ x in B0579.cell c, flowIntegrand tr (ω₁ r) (u₁ r) r φ x)
            + Complex.I * ∫ r in t..s, ∫ x in B0579.cell c, flowIntegrand tr (ω₂ r) (u₂ r) r φ x := by
      rw [intervalIntegral.integral_congr (fun r hr => hG r (hsub hr)),
        intervalIntegral.integral_add hint1 (hint2.const_mul Complex.I),
        intervalIntegral.integral_const_mul]
    have hL1 : IntegrableOn (fun x => ω₁ t x * (φ x : ℂ)) (B0579.cell c) :=
      lfc_integrableOn_cplx_test (h₁.memX t htT) hφ
    have hL2 : IntegrableOn (fun x => ω₂ t x * (φ x : ℂ)) (B0579.cell c) :=
      lfc_integrableOn_cplx_test (h₂.memX t htT) hφ
    have hf1 : IntegrableOn (fun x => f₁ x * (φ x : ℂ)) (B0579.cell c) :=
      hL1.congr_fun_ae (by
        filter_upwards [h₁.initial] with x hx
        simp only [hx])
    have hf2 : IntegrableOn (fun x => f₂ x * (φ x : ℂ)) (B0579.cell c) :=
      hL2.congr_fun_ae (by
        filter_upwards [h₂.initial] with x hx
        simp only [hx])
    have hS1 : IntegrableOn (fun x => ω₁ s x * (φ x : ℂ)) (B0579.cell c) :=
      lfc_integrableOn_cplx_test (h₁.memX s hs) hφ
    have hS2 : IntegrableOn (fun x => ω₂ s x * (φ x : ℂ)) (B0579.cell c) :=
      lfc_integrableOn_cplx_test (h₂.memX s hs) hφ
    have hsumL := lfc_integral_comb_mul (ω₁ s) (ω₂ s) (fun x => (φ x : ℂ)) hS1 hS2
    have hfl := lfc_integral_comb_mul f₁ f₂ (fun x => (φ x : ℂ)) hf1 hf2
    have w1 := h₁.weak φ hφ s hs
    have w2 := h₂.weak φ hφ s hs
    show ∫ x in B0579.cell c, (ω₁ s x + Complex.I * ω₂ s x) * (φ x : ℂ)
        = (∫ x in B0579.cell c, (f₁ x + Complex.I * f₂ x) * (φ x : ℂ))
          + ∫ r in t..s, ∫ x in B0579.cell c, flowIntegrand tr (fun y => ω₁ r y + Complex.I * ω₂ r y)
            (fun y j => u₁ r y j + Complex.I * u₂ r y j) r φ x
    rw [hfl, hTI, hsumL, w1, w2]
    ring
