import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeCylDuality.ClassicalAdj
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeCylDuality.ProductRuleFree
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.XNorm

/-!
# `PartIII-a:T21/c3/3/1/1/2/2/2/2`: physical cylinder-data duality (`FreeCylDuality`)

Source `the November 2 reference manuscript` (SP) lines 2937-2958, 3036-3060.

Proves `FreeCylDuality`: for a BUC train `tr`, a regular backward free adjoint flow `φ` on `[t₁, s]`
with terminal datum `g`, and a weak free cylinder flow `om` from `s₁ ∈ [t₁, s]` with cylinder-test
datum `f`, the pairing `∫_{C_c} om(r) φ(r)` is constant on `[s₁, s]`, giving
`∫_{C_c} om(s) g = ∫_{C_c} f φ(s₁)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux

/-- Restriction of a regular backward free adjoint flow from `[t₁, s]` to `[s₁, s]`. -/
lemma isFreeAdjointFlow_mono {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {t₁ s₁ s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hs₁ : t₁ ≤ s₁) (hs₁s : s₁ ≤ s) (hφ : IsFreeAdjointFlow ν c m tr t₁ s g φ) :
    IsFreeAdjointFlow ν c m tr s₁ s g φ where
  terminal := hφ.terminal
  memX := fun r hr => hφ.memX r ⟨hs₁.trans hr.1, hr.2⟩
  strongCont := fun r hr =>
    (hφ.strongCont r ⟨hs₁.trans hr.1, hr.2⟩).mono_left
      (nhdsWithin_mono _ fun r' hr' => ⟨hs₁.trans hr'.1, hr'.2⟩)
  periodic := fun r hr => hφ.periodic r ⟨hs₁.trans hr.1, hr.2⟩
  smooth := fun r hr => hφ.smooth r ⟨hs₁.trans hr.1, hr.2⟩
  jointSmooth := hφ.jointSmooth.mono (prod_mono (fun r hr => ⟨hs₁.trans hr.1, hr.2⟩) subset_rfl)
  memH1 := fun r hr => hφ.memH1 r ⟨hs₁.trans hr.1, hr.2⟩
  strongContH1 := fun r hr k =>
    (hφ.strongContH1 r ⟨hs₁.trans hr.1, hr.2⟩ k).mono_left
      (nhdsWithin_mono _ fun r' hr' => ⟨hs₁.trans hr'.1, hr'.2⟩)
  integrable := fun ψ hψ r hr => hφ.integrable ψ hψ r ⟨hs₁.trans hr.1, hr.2⟩
  timeIntegrable := fun ψ hψ =>
    (hφ.timeIntegrable ψ hψ).mono_set (by
      rw [Set.uIcc_of_le (hs₁.trans hs₁s), Set.uIcc_of_le hs₁s]
      exact Icc_subset_Icc hs₁ le_rfl)
  weak := fun ψ hψ r hr => hφ.weak ψ hψ r ⟨hs₁.trans hr.1, hr.2⟩

/-- For a free cylinder flow and a regular free adjoint flow (`ladChi = 0` on the cell),
`ladRate` equals the cutoff commutator `ladComm` on `(s₁, s)`. -/
lemma free_rate_eq_comm {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {s₁ s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ}
    (hc : 0 < c) (hs₁0 : 0 ≤ s₁)
    (hφ : IsFreeAdjointFlow ν c m tr s₁ s g φ)
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    {R : ℝ} (hR : 0 < R) {ρ : ℝ} (hρ : ρ ∈ Ioo s₁ s) :
    ladRate tr (freeW om) zeroU φ R ρ = ladComm tr (freeW om) φ R ρ := by
  have hρ0 : 0 ≤ ρ := hs₁0.trans hρ.1.le
  have hφs : ContDiff ℝ ∞ (φ ρ) := hφ.smooth ρ (Ioo_subset_Ico_self hρ)
  have hdt : Continuous (ladDt φ ρ) := RateSplitAux.continuous_dt hρ hφ.jointSmooth
  have hχ : ContDiff ℝ ∞ (ladCut R) := ((ladCutProps.choose_spec.2 R hR).1 c).smooth
  have hχC : Continuous (fun x => (ladCut R x : ℂ)) := (RateSplitAux.contDiff_ofReal hχ).continuous
  have hφC : Continuous (φ ρ) := hφs.continuous
  have hpd : ∀ k : Fin 2, Continuous (fun x => (B0579.pd k (ladCut R) x : ℂ)) := fun k =>
    (RateSplitAux.contDiff_ofReal (ForceMemXAux.contDiff_pd hχ k)).continuous
  have hpdφ : ∀ k : Fin 2, Continuous (pdCx k (φ ρ)) := fun k =>
    (RateSplitAux.contDiff_pdCx hφs k).continuous
  have hv : ∀ j : Fin 2, Continuous (fun x => (tr.v ρ x j : ℂ)) := fun j =>
    (RateSplitAux.contDiff_ofReal (RateSplitAux.continuous_v tr hρ0 j)).continuous
  have hlapP : Continuous (fun x => (lapP (ladCut R) x : ℂ)) := by
    unfold lapP
    have h0 := ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 0) 0
    have h1 := ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 1) 1
    exact (RateSplitAux.contDiff_ofReal (h0.add h1)).continuous
  have hwm := freeW_memX hω ρ hρ.1.le
  have hz1 : ∀ x : ℝ × ℝ, 2 * R < |x.2| → ladCut R x = 0 := fun x hx =>
    RateSplitAux.cut_zero hR hx
  set Bp : ℝ × ℝ → ℂ := fun x => (ladCut R x : ℂ) * ladDt φ ρ x
  set Ep : ℝ × ℝ → ℂ := fun x =>
    (ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
      ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
        φ ρ x
  have hBc : Continuous Bp := hχC.mul hdt
  have hEc : Continuous Ep := by
    refine (continuous_const.mul ?_).add ?_
    · refine (continuous_const.mul (((hpd 0).mul (hpdφ 0)).add ((hpd 1).mul (hpdφ 1)))).add
        (hlapP.mul hφC)
    · have : Continuous (fun x => ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
          tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ)) := by
        push_cast
        exact ((hv 0).mul (hpd 0)).add ((hv 1).mul (hpd 1))
      exact this.mul hφC
  have hBs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Bp x = 0 := fun x hx => by simp [Bp, hz1 x hx]
  have hEs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Ep x = 0 := fun x hx => by
    simp [Ep, RateSplitAux.pd_cut_zero hR 0 hx,
      RateSplitAux.pd_cut_zero hR 1 hx, RateSplitAux.lapP_cut_zero hR hx]
  have iB := RateSplitAux.integrableOn_w_mul c m R hwm hBc hBs
  have iE := RateSplitAux.integrableOn_w_mul c m R hwm hEc hEs
  have hpt : ∀ x ∈ B0579.cell c,
      ladFlowCx tr (freeW om ρ) (zeroU ρ) ρ (ladCutPhi φ R ρ) x +
          freeW om ρ x * Bp x = freeW om ρ x * Ep x := by
    intro x hx
    have hchi0 : ladChi tr φ ρ x = 0 := freeAdj_chi_eq_zero hc hs₁0 hφ hρ hx
    have h := RateSplitAux.pointwise_split tr hχ hφs ρ (freeW om ρ x) (zeroU ρ x) x
      (ladDt φ ρ x) (ladChi tr φ ρ x) rfl
    rw [hchi0, mul_zero, mul_zero, zero_add] at h
    unfold ladFlowCx ladForce zeroU
    simp only [zero_mul, add_zero, sub_zero]
    have e : ladCutPhi φ R ρ = fun y => (ladCut R y : ℂ) * φ ρ y := rfl
    rw [e]
    exact h
  have iFl : IntegrableOn (fun x => ladFlowCx tr (freeW om ρ) (zeroU ρ) ρ (ladCutPhi φ R ρ) x)
      (B0579.cell c) := by
    refine (iE.sub iB).congr_fun (fun x hx => ?_) (B0579.measurableSet_cell c)
    simp only [Pi.sub_apply]
    linear_combination -(hpt x hx)
  unfold ladRate ladComm
  rw [← integral_add iFl iB]
  exact setIntegral_congr_fun (B0579.measurableSet_cell c) hpt

/-- Uniform real bound on `[a, b]` for the weighted norm of a strongly continuous family. -/
lemma norm_bdd_on_Icc {c n a b : ℝ} {F : ℝ → ℝ × ℝ → ℂ}
    (hmem : ∀ ρ ∈ Icc a b, MemLp (F ρ) 2 (B0579.cellMeasure c n))
    (hcont : ∀ ρ ∈ Icc a b,
      Tendsto (fun ρ' => xNorm c n (F ρ' - F ρ)) (𝓝[Icc a b] ρ) (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ ∈ Icc a b, (eLpNorm (F ρ) 2 (B0579.cellMeasure c n)).toReal ≤ M := by
  have hmem' : ∀ ρ ∈ Icc a b, MemLp (F ρ) 2 (B0579.cellMeasure c (-(-n))) := by
    simpa only [neg_neg] using hmem
  have hcont' : ∀ ρ ∈ Icc a b,
      Tendsto (fun ρ' => xNorm c (-(-n)) (F ρ' - F ρ)) (𝓝[Icc a b] ρ) (𝓝 0) := by
    simpa only [neg_neg] using hcont
  have hcw : ∀ ρ ∈ Icc a b, ContinuousWithinAt (fun ρ' => xNorm c n (F ρ')) (Icc a b) ρ := by
    intro ρ hρ
    simpa only [neg_neg] using
      xNorm_continuousWithinAt_of_strongCont (m := -n) hmem' hcont' ρ hρ
  have hG : ContinuousOn (fun ρ' => (xNorm c n (F ρ')).toReal) (Icc a b) := by
    intro ρ hρ
    exact ContinuousAt.comp_continuousWithinAt (f := fun ρ' => xNorm c n (F ρ')) (x := ρ)
      (ENNReal.continuousAt_toReal (hmem ρ hρ).2.ne) (hcw ρ hρ)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.image_of_continuousOn hG).bddAbove
  refine ⟨max M₀ 0, le_max_right _ _, fun ρ hρ => ?_⟩
  have hle : (xNorm c n (F ρ)).toReal ≤ M₀ := hM₀ (Set.mem_image_of_mem _ hρ)
  exact hle.trans (le_max_left _ _)

/-- Cell integral of `‖A‖ · ‖B‖` bounded by the product of weighted `L²` norms. -/
lemma int_norm_mul_le {c m : ℝ} {A B : ℝ × ℝ → ℂ}
    (hA : MemLp A 2 (B0579.cellMeasure c m)) (hB : MemLp B 2 (B0579.cellMeasure c (-m))) :
    ∫ x in B0579.cell c, ‖A x‖ * ‖B x‖ ≤
      (eLpNorm A 2 (B0579.cellMeasure c m)).toReal *
        (eLpNorm B 2 (B0579.cellMeasure c (-m))).toReal := by
  have hAn : MemLp (fun x => ((‖A x‖ : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := hA.norm.ofReal
  have hBn : MemLp (fun x => ((‖B x‖ : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) := hB.norm.ofReal
  have hcs := (PairContAux.holder hAn hBn).2
  have heA : eLpNorm (fun x => ((‖A x‖ : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) =
      eLpNorm A 2 (B0579.cellMeasure c m) := by
    rw [← eLpNorm_norm, ← eLpNorm_norm (f := A)]
    congr 1; funext x; simp [Complex.norm_real]
  have heB : eLpNorm (fun x => ((‖B x‖ : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) =
      eLpNorm B 2 (B0579.cellMeasure c (-m)) := by
    rw [← eLpNorm_norm, ← eLpNorm_norm (f := B)]
    congr 1; funext x; simp [Complex.norm_real]
  rw [heA, heB] at hcs
  have heI : ∫ x in B0579.cell c, ((‖A x‖ : ℝ) : ℂ) * ((‖B x‖ : ℝ) : ℂ) =
      ((∫ x in B0579.cell c, ‖A x‖ * ‖B x‖ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext x; push_cast; rfl
  have hnn : 0 ≤ ∫ x in B0579.cell c, ‖A x‖ * ‖B x‖ :=
    integral_nonneg fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [heI, Complex.norm_real, Real.norm_of_nonneg hnn] at hcs
  exact hcs

/-- Uniform `O(R⁻¹)` bound on `ladComm` over `(s₁, r)` (`r < s`). -/
lemma comm_unif_bound {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {s₁ s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ}
    (hs₁0 : 0 ≤ s₁) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hφ : IsFreeAdjointFlow ν c m tr s₁ s g φ)
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om)
    {r : ℝ} (hr : r ∈ Ico s₁ s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo s₁ r,
      ‖ladComm tr (freeW om) φ R ρ‖ ≤ B * R⁻¹ := by
  have hs0 : 0 ≤ s := hs₁0.trans (hr.1.trans hr.2.le)
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  obtain ⟨CV, hCV⟩ := htr.sup_bound hs0
  set C : ℝ := max CV 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hv_le : ∀ ρ ∈ Icc (0 : ℝ) s, ∀ x : ℝ × ℝ, ∀ j : Fin 2, |tr.v ρ x j| ≤ C := by
    intro ρ hρ x j
    have h1 : ‖tr.v ρ x j‖ ≤ ‖tr.v ρ x‖ := PiLp.norm_apply_le (tr.v ρ x) j
    rw [Real.norm_eq_abs] at h1
    exact (h1.trans (hCV ρ hρ x)).trans (le_max_left _ _)
  -- uniform weighted-norm bounds on `Icc s₁ r`
  obtain ⟨Mw, hMw0, hMw⟩ := norm_bdd_on_Icc (c := c) (n := m) (a := s₁) (b := r)
    (fun ρ hρ => freeW_memX hω ρ hρ.1)
    (fun ρ hρ => (freeW_strongCont hω ρ hρ.1).mono_left
      (nhdsWithin_mono _ fun x hx => hx.1))
  obtain ⟨Mφ, hMφ0, hMφ⟩ := norm_bdd_on_Icc (c := c) (n := -m) (a := s₁) (b := r)
    (fun ρ hρ => hφ.memX ρ ⟨hρ.1, hρ.2.trans hr.2.le⟩)
    (fun ρ hρ => (hφ.strongCont ρ ⟨hρ.1, hρ.2.trans hr.2.le⟩).mono_left
      (nhdsWithin_mono _ fun x hx => ⟨hx.1, hx.2.trans hr.2.le⟩))
  obtain ⟨M0, hM00, hM0⟩ := norm_bdd_on_Icc (c := c) (n := -m) (a := s₁) (b := r)
    (F := fun ρ => pdCx 0 (φ ρ))
    (fun ρ hρ => hφ.memH1 ρ ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩ 0)
    (fun ρ hρ => (hφ.strongContH1 ρ ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩ 0).mono_left
      (nhdsWithin_mono _ fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩))
  obtain ⟨M1, hM10, hM1⟩ := norm_bdd_on_Icc (c := c) (n := -m) (a := s₁) (b := r)
    (F := fun ρ => pdCx 1 (φ ρ))
    (fun ρ hρ => hφ.memH1 ρ ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩ 1)
    (fun ρ hρ => (hφ.strongContH1 ρ ⟨hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩ 1).mono_left
      (nhdsWithin_mono _ fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩))
  set B : ℝ := (3 * |ν| * K + 2 * C * K) * (Mw * (Mφ + M0 + M1))
  have hB0 : 0 ≤ B := by positivity
  refine ⟨B, hB0, fun R hR1 ρ hρ => ?_⟩
  have hρI : ρ ∈ Icc s₁ r := ⟨hρ.1.le, hρ.2.le⟩
  have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨hs₁0.trans hρ.1.le, hρ.2.le.trans hr.2.le⟩
  have hρIco : ρ ∈ Ico s₁ s := ⟨hρ.1.le, lt_trans hρ.2 hr.2⟩
  have hR0 : 0 < R := by linarith
  have hq : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have i1 := CommVanishAux.integrableOn_cell_norm_mul c m (freeW_memX hω ρ hρ.1.le)
    (hφ.memX ρ ⟨hρ.1.le, hρIco.2.le⟩)
  have i2 := CommVanishAux.integrableOn_cell_norm_mul c m (freeW_memX hω ρ hρ.1.le)
    (hφ.memH1 ρ hρIco 0)
  have i3 := CommVanishAux.integrableOn_cell_norm_mul c m (freeW_memX hω ρ hρ.1.le)
    (hφ.memH1 ρ hρIco 1)
  have hI : IntegrableOn (fun x =>
      ‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
        ‖freeW om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (B0579.cell c) := (i1.add i2).add i3
  have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖freeW om ρ x * ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
          ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
            tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) * φ ρ x)‖ ≤
        (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          (‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
            ‖freeW om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
    rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
    refine Eventually.of_forall fun x _ => ?_
    have hpd := hK R hR0
    have hp0 : |B0579.pd 0 (ladCut R) x| ≤ K * R⁻¹ := by
      simpa [div_eq_mul_inv] using hpd.2.2.2.2.1 x 0
    have hp1 : |B0579.pd 1 (ladCut R) x| ≤ K * R⁻¹ := by
      simpa [div_eq_mul_inv] using hpd.2.2.2.2.1 x 1
    have hL : |lapP (ladCut R) x| ≤ K * R⁻¹ := by
      have h := hpd.2.2.2.2.2 x
      have e : K / R ^ 2 = K * R⁻¹ * R⁻¹ := by ring
      rw [e] at h
      exact h.trans (mul_le_of_le_one_right (mul_nonneg hK0 hq) hq1)
    have hvv : |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
        tr.v ρ x 1 * B0579.pd 1 (ladCut R) x| ≤ 2 * C * K * R⁻¹ := by
      calc |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x|
          ≤ |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x| +
              |tr.v ρ x 1 * B0579.pd 1 (ladCut R) x| := abs_add_le _ _
        _ = |tr.v ρ x 0| * |B0579.pd 0 (ladCut R) x| +
              |tr.v ρ x 1| * |B0579.pd 1 (ladCut R) x| := by rw [abs_mul, abs_mul]
        _ ≤ C * (K * R⁻¹) + C * (K * R⁻¹) :=
            add_le_add (mul_le_mul (hv_le ρ hρS x 0) hp0 (abs_nonneg _) hC0)
              (mul_le_mul (hv_le ρ hρS x 1) hp1 (abs_nonneg _) hC0)
        _ = 2 * C * K * R⁻¹ := by ring
    have hZ := CommVanishAux.comm_pointwise ν C K R _ _ _ _ hK0 hC0 hq hp0 hp1 hL hvv
      (pdCx 0 (φ ρ) x) (pdCx 1 (φ ρ) x) (φ ρ x)
    rw [norm_mul]
    calc ‖freeW om ρ x‖ * ‖(ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
            (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
            ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
              tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) * φ ρ x‖
        ≤ ‖freeW om ρ x‖ * ((3 * |ν| * K + 2 * C * K) * R⁻¹ *
            (‖φ ρ x‖ + ‖pdCx 0 (φ ρ) x‖ + ‖pdCx 1 (φ ρ) x‖)) :=
          mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
      _ = (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          (‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
            ‖freeW om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by ring
  have hIntLe : ∫ x in B0579.cell c,
      (‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
        ‖freeW om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) ≤ Mw * (Mφ + M0 + M1) := by
    have i12 : IntegrableOn
        (fun x => ‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖)
        (B0579.cell c) := Integrable.add i1 i2
    rw [integral_add i12 i3, integral_add i1 i2]
    have b1 := int_norm_mul_le (freeW_memX hω ρ hρ.1.le) (hφ.memX ρ ⟨hρ.1.le, hρIco.2.le⟩)
    have b2 := int_norm_mul_le (freeW_memX hω ρ hρ.1.le) (hφ.memH1 ρ hρIco 0)
    have b3 := int_norm_mul_le (freeW_memX hω ρ hρ.1.le) (hφ.memH1 ρ hρIco 1)
    have nw := hMw ρ hρI
    have nφ := hMφ ρ hρI
    have n0 := hM0 ρ hρI
    have n1 := hM1 ρ hρI
    have c1 : (eLpNorm (freeW om ρ) 2 (B0579.cellMeasure c m)).toReal *
        (eLpNorm (φ ρ) 2 (B0579.cellMeasure c (-m))).toReal ≤ Mw * Mφ :=
      mul_le_mul nw nφ ENNReal.toReal_nonneg hMw0
    have c2 : (eLpNorm (freeW om ρ) 2 (B0579.cellMeasure c m)).toReal *
        (eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal ≤ Mw * M0 :=
      mul_le_mul nw n0 ENNReal.toReal_nonneg hMw0
    have c3 : (eLpNorm (freeW om ρ) 2 (B0579.cellMeasure c m)).toReal *
        (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal ≤ Mw * M1 :=
      mul_le_mul nw n1 ENNReal.toReal_nonneg hMw0
    linarith [b1, b2, b3, c1, c2, c3]
  unfold ladComm
  calc ‖∫ x in B0579.cell c, freeW om ρ x *
          ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
              (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) +
              (lapP (ladCut R) x : ℂ) * φ ρ x) +
            ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
              tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) * φ ρ x)‖
      ≤ ∫ x in B0579.cell c, (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          (‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
            ‖freeW om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) :=
        norm_integral_le_of_norm_le (hI.const_mul _) hpt
    _ = (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          ∫ x in B0579.cell c,
            (‖freeW om ρ x‖ * ‖φ ρ x‖ + ‖freeW om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
              ‖freeW om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := integral_const_mul _ _
    _ ≤ (3 * |ν| * K + 2 * C * K) * R⁻¹ * (Mw * (Mφ + M0 + M1)) :=
        mul_le_mul_of_nonneg_left hIntLe (by positivity)
    _ = B * R⁻¹ := by simp only [B]; ring

/-- Continuity of the unweighted cell pairing `ladPair c (freeW om) φ` on `[s₁, s]`. -/
lemma free_ladPair_cont {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    {s₁ s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {f : B0579.Plane → ℝ} {om : ℝ → B0579.Plane → ℝ}
    (hφ : IsFreeAdjointFlow ν c m tr s₁ s g φ)
    (hω : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f om) :
    ContinuousOn (ladPair c (freeW om) φ) (Icc s₁ s) := by
  intro ρ hρ
  have hwm : ∀ r' ∈ Icc s₁ s, MemLp (freeW om r') 2 (B0579.cellMeasure c m) :=
    fun r' h => freeW_memX hω r' h.1
  have hφm : ∀ r' ∈ Icc s₁ s, MemLp (φ r') 2 (B0579.cellMeasure c (-m)) :=
    fun r' h => hφ.memX r' h
  have ha : Tendsto (fun r' => (eLpNorm (freeW om r' - freeW om ρ) 2
      (B0579.cellMeasure c m)).toReal) (𝓝[Icc s₁ s] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun r' => xNorm c m (freeW om r' - freeW om ρ)) (𝓝[Icc s₁ s] ρ) (𝓝 0) :=
      (freeW_strongCont hω ρ hρ.1).mono_left (nhdsWithin_mono _ fun x hx => hx.1)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, xNorm] using this
  have hb : Tendsto (fun r' => (eLpNorm (φ r' - φ ρ) 2
      (B0579.cellMeasure c (-m))).toReal) (𝓝[Icc s₁ s] ρ) (𝓝 0) := by
    have h1 := hφ.strongCont ρ hρ
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, xNorm] using this
  unfold ladPair
  exact LadPRPairAux.pairCW (S := Icc s₁ s) hρ (freeW om) φ hwm hφm ha hb

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded

open UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeCylDualityAux

/-- **Physical cylinder-data duality** (`PartIII-a:T21/c3/3/1/1/2/2/2/2`, SP 2937-2958). -/
theorem freeCylDuality (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.FreeCylDuality ν m tr t₁ t₂ := by
  intro _ hν ht₁ _ htr s _ g φ hφ₀ s₁ hs₁ f _ om hω
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hs₁0 : 0 ≤ s₁ := ht₁.trans hs₁.1
  rcases eq_or_lt_of_le hs₁.2 with hss | hs₁s
  · subst hss
    refine integral_congr_ae ?_
    filter_upwards [hω.initial, hφ₀.terminal] with x hx₁ hx₂
    rw [hx₁, hx₂]
  have hφ : IsFreeAdjointFlow ν c m tr s₁ s g φ := isFreeAdjointFlow_mono hs₁.1 hs₁s.le hφ₀
  -- constancy of `ladPair c (freeW om) φ` on `[s₁, s)`
  have hconst : ∀ r ∈ Ico s₁ s,
      ladPair c (freeW om) φ r = ladPair c (freeW om) φ s₁ := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hrt | hrt
    · rw [hrt]
    obtain ⟨B, hB0, hB⟩ := comm_unif_bound hs₁0 htr hφ hω hr
    have hprod : ∀ R : ℝ, 0 < R →
        IntervalIntegrable (fun ρ => ladRate tr (freeW om) zeroU φ R ρ) volume s₁ r ∧
          ladCutPair c R (freeW om) φ r - ladCutPair c R (freeW om) φ s₁ =
            ∫ ρ in s₁..r, ladRate tr (freeW om) zeroU φ R ρ :=
      fun R hR => free_productRule hc hs₁0 hs₁s hω hφ.jointSmooth hφ.periodic hR hr
    have hlimInt : Tendsto (fun R : ℝ => ∫ ρ in s₁..r, ladRate tr (freeW om) zeroU φ R ρ)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun R : ℝ => B * R⁻¹ * |r - s₁|) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.const_mul B).mul_const |r - s₁|
        simpa using this
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
      set gR : ℝ → ℂ := fun ρ =>
        if ρ < r then ladRate tr (freeW om) zeroU φ R ρ else 0
      have hae : ∫ ρ in s₁..r, ladRate tr (freeW om) zeroU φ R ρ = ∫ ρ in s₁..r, gR ρ := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [lad_ae_ne r] with ρ hρr hρI
        rw [Set.uIoc_of_le hr.1] at hρI
        have hlt : ρ < r := lt_of_le_of_ne hρI.2 hρr
        simp [gR, hlt]
      rw [hae]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun ρ hρI => ?_
      rw [Set.uIoc_of_le hr.1] at hρI
      by_cases hlt : ρ < r
      · simp only [gR, hlt, ↓reduceIte]
        have hρIoo : ρ ∈ Ioo s₁ s := ⟨hρI.1, lt_trans hlt hr.2⟩
        rw [free_rate_eq_comm hc hs₁0 hφ hω (by linarith : 0 < R) hρIoo]
        exact hB R hR1 ρ ⟨hρI.1, hlt⟩
      · simp only [gR, hlt, ↓reduceIte, norm_zero]
        exact mul_nonneg hB0 (inv_nonneg.2 (by linarith))
    have hcutr : Tendsto (fun R : ℝ => ladCutPair c R (freeW om) φ r) atTop
        (𝓝 (ladPair c (freeW om) φ r)) :=
      ladCutLimit c m (freeW om r) (φ r) (freeW_memX hω r hr.1) (hφ.memX r ⟨hr.1, hr.2.le⟩)
    have hcuts : Tendsto (fun R : ℝ => ladCutPair c R (freeW om) φ s₁) atTop
        (𝓝 (ladPair c (freeW om) φ s₁)) :=
      ladCutLimit c m (freeW om s₁) (φ s₁) (freeW_memX hω s₁ le_rfl)
        (hφ.memX s₁ ⟨le_rfl, hs₁s.le⟩)
    have hdiff' : Tendsto (fun R : ℝ =>
        ladCutPair c R (freeW om) φ r - ladCutPair c R (freeW om) φ s₁) atTop (𝓝 0) := by
      refine hlimInt.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact ((hprod R hR).2).symm
    exact sub_eq_zero.1 (tendsto_nhds_unique (hcutr.sub hcuts) hdiff')
  -- extend constancy to `s` by continuity
  have hcont := free_ladPair_cont hφ hω
  have hEq : EqOn (ladPair c (freeW om) φ) (fun _ => ladPair c (freeW om) φ s₁) (Icc s₁ s) := by
    have h0 : EqOn (ladPair c (freeW om) φ) (fun _ => ladPair c (freeW om) φ s₁) (Ico s₁ s) :=
      fun r hr => hconst r hr
    refine h0.of_subset_closure hcont continuousOn_const Ico_subset_Icc_self ?_
    rw [closure_Ico hs₁s.ne]
  have hsEq : ladPair c (freeW om) φ s = ladPair c (freeW om) φ s₁ := hEq ⟨hs₁s.le, le_rfl⟩
  have e1 : ∫ x in B0579.cell c, ((om s x : ℝ) : ℂ) * g x = ladPair c (freeW om) φ s := by
    unfold ladPair freeW
    refine integral_congr_ae ?_
    filter_upwards [hφ.terminal] with x hx
    rw [hx]
  have e2 : ladPair c (freeW om) φ s₁ = ∫ x in B0579.cell c, ((f x : ℝ) : ℂ) * φ s₁ x := by
    unfold ladPair freeW
    refine integral_congr_ae ?_
    filter_upwards [hω.initial] with x hx
    rw [hx]
  rw [e1, hsEq, e2]

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded

export UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded (freeCylDuality)
