import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.Local
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.HolderConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Raw
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.VSup
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L2

/-!
# `PartIII-b_C_rep_8_1_5`: decomposition and assembly for `BackgroundSplit` (`PartIII-b:C/rep/8/1/5`)

Source: `the November 2 reference manuscript` lines 5134-5139, 5225-5242,
5272-5289, 5434-5436.

At each regime `L` we split `coefSize L.ν L.U L.pres ≤ Bl + Br` with:
* `Bl = bgBl L = coefSize L.ν L.V (liftP L)` (the transversally localized raw-train and entrance
  part) and `βl = bgBeta (C * L.ν⁻¹ ^ k)`: both the uniform-in-phase young-chart bound and the
  `(s, η)` square-integral bound are proved unconditionally from `D.RepairStanding` in
  `BackgroundSplit.Local` (`bgLocal_eventually`) using `ringChartRules`, `trainMoment`, and `entWPt`.
* `Br = bgBr L M` (the repair velocity and pressure-completion remainder): at every chart point
  `0 < p.1`, `Br` coincides with `(1 + 12 L.ν + M) coefChgDens (L.U τ) (L.V τ) +
  3 presChgDens (L.pres τ) (liftP L τ)`.  Combined with the `Y_{11/4}` bounds `PresFlatAt` and
  `CoefChgAt` and the `Y_{22/3}` response-derivative bound `RespJetGradAt` via `ringHolderConv`
  (`1 + 3/11 + 57/22 = 85/22`), this bounds `remTerm Pl K L μ Br T` in `L²(srcMeasure)`.

We also prove:
* `jetSize_le_act_add_mean`: pointwise control of `jetSize` by `meanJetDens` of `(actX, actY)`
  plus `meanJetDens` of `(mnX, mnY)`, reducing `RespJetGrad` to the actual thin-response bound
  `ActGrad` together with `meanGrad` (already proved in `Pres.MeanGrad`);
* `actJetMeas` and `actJetChartTransfer`: ring-chart `AEStronglyMeasurable` for `jetSize` and
  `meanJetDens (actX, actY)` together with the phase-slice-to-chart `L^{22/3}` transfer for
  `(actX, actY)`;
* `coefChg_of_rhoW1`: reduction of `D.CoefChg` to `D.RhoW1` using the already-proved
  `coefChgMeas`, `coefChgLp`, `rawSupBound`, `vSupBound`, and `nuLeOneRhoNonneg`;
* `backgroundSplit_of`, `backgroundSplit_of_leaves`, and `backgroundSplit_of_actGrad`: assembly of
  `D.BackgroundSplit` from `D.RepairStanding` and the remaining source inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)
open WardEMeasAux

/-! ## 1. The remainder background coefficient `bgBr` -/

/-- The linear combination of `coefChgDens (L.U τ) (L.V τ)` and `presChgDens (L.pres τ) (liftP L τ)`
dominating `coefSize L.ν L.U L.pres - coefSize L.ν L.V (liftP L)` whenever `‖U‖ + ‖V‖ ≤ M`. -/
def bgBrLin (L : ReturnLevel) (M : ℝ) (τ : ℝ) (y : Space) : ℝ :=
  (1 + 12 * L.ν + M) * coefChgDens (L.U τ) (L.V τ) y +
    3 * presChgDens (L.pres τ) (liftP L τ) y

/-- The remainder background coefficient `Br`: equals `bgBrLin L M` wherever `‖U‖ + ‖V‖ ≤ M`
(in particular at every chart point `0 < p.1` under `CoefChgAt`), and `coefSize L.ν L.U L.pres`
otherwise so that `coefSize ≤ bgBl + bgBr` holds at every `(τ, y) : ℝ × Space`. -/
def bgBr (L : ReturnLevel) (M : ℝ) (τ : ℝ) (y : Space) : ℝ :=
  if ‖L.U τ y‖ + ‖L.V τ y‖ ≤ M then
    bgBrLin L M τ y
  else
    coefSize L.ν L.U L.pres τ y

theorem bgBr_split (L : ReturnLevel) (M : ℝ) (τ : ℝ) (y : Space) :
    coefSize L.ν L.U L.pres τ y ≤ bgBl L τ y + bgBr L M τ y := by
  unfold bgBl bgBr bgBrLin
  split_ifs with h
  · have hsub := coefSize_sub_le L.ν_pos.le L.U L.V L.pres (liftP L) τ y
    have h1 : (1 + 12 * L.ν + ‖L.U τ y‖ + ‖L.V τ y‖) * coefChgDens (L.U τ) (L.V τ) y ≤
        (1 + 12 * L.ν + M) * coefChgDens (L.U τ) (L.V τ) y :=
      mul_le_mul_of_nonneg_right (by linarith) (coefChgDens_nonneg _ _ _)
    linarith
  · have h0 := bg_coefSize_nonneg L.ν_pos.le L.V (liftP L) τ y
    linarith

theorem bgBrLin_nonneg (L : ReturnLevel) {M : ℝ} (hM : 0 ≤ M) (τ : ℝ) (y : Space) :
    0 ≤ bgBrLin L M τ y := by
  unfold bgBrLin
  have hν := L.ν_pos.le
  have hc := coefChgDens_nonneg (L.U τ) (L.V τ) y
  have hp := presChgDens_nonneg (L.pres τ) (liftP L τ) y
  positivity

theorem bgBr_nonneg (L : ReturnLevel) {M : ℝ} (hM : 0 ≤ M) (τ : ℝ) (y : Space) :
    0 ≤ bgBr L M τ y := by
  unfold bgBr
  split_ifs
  · exact bgBrLin_nonneg L hM τ y
  · exact bg_coefSize_nonneg L.ν_pos.le L.U L.pres τ y

theorem bgBr_eq_lin_of_pos (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    {C : ℝ} {k : ℕ} (h2 : CoefChgAt Pl K L C k) {p : Chart} (hp : 0 < p.1) :
    ringRead L.ε⁻¹ (bgBr L (C * L.ν⁻¹ ^ k)) p =
      ringRead L.ε⁻¹ (bgBrLin L (C * L.ν⁻¹ ^ k)) p := by
  unfold ringRead bgBr
  have hU := h2.2.2 p hp
  split_ifs with hle
  · rfl
  · exfalso
    exact hle (by linarith [hU, norm_nonneg (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)
      (NearInst.chartY L.ε⁻¹ p))])

theorem remTerm_bgBr_eq_lin (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    {C : ℝ} {k : ℕ} (h2 : CoefChgAt Pl K L C k) (T : LStr Pl K L) (p : Chart) :
    remTerm Pl K L μ (bgBr L (C * L.ν⁻¹ ^ k)) T p =
      (Real.sqrt p.1)⁻¹ * ringRead L.ε⁻¹ (bgBrLin L (C * L.ν⁻¹ ^ k)) p *
        ringRead L.ε⁻¹ (jetSize Pl K L μ T) p := by
  by_cases hp : 0 < p.1
  · unfold remTerm
    have heq := bgBr_eq_lin_of_pos Pl K L h2 hp
    unfold ringRead at heq ⊢
    rw [heq]
  · have hs : (Real.sqrt p.1)⁻¹ = 0 := by
      rw [Real.sqrt_eq_zero'.2 (not_lt.1 hp), inv_zero]
    simp [remTerm, hs]

/-! ## 2. Pointwise comparison of `jetSize` with `meanJetDens` and the `Y_{22/3}` jet leaves -/

/-- Operator norm of `fderiv ℝ f y` is bounded by `gradSize f y = ∑ j, ‖physPd f j y‖`. -/
theorem norm_fderiv_le_gradSize (f : Space → Space) (y : Space) :
    ‖fderiv ℝ f y‖ ≤ gradSize f y := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : fderiv ℝ f y v = ∑ j : Fin 3, v j • physPd f j y := by
    conv_lhs => rw [eq_jet1 (fderiv ℝ f y)]
    exact jet1_apply (fun j => physPd f j y) v
  rw [hv]
  calc ‖∑ j : Fin 3, v j • physPd f j y‖
      ≤ ∑ j : Fin 3, ‖v j • physPd f j y‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, |v j| * ‖physPd f j y‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin 3, ‖v‖ * ‖physPd f j y‖ :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (chgPt_abs_coord_le v j) (norm_nonneg _)
    _ = gradSize f y * ‖v‖ := by
        unfold gradSize
        rw [← Finset.mul_sum, mul_comm]

/-- `jetSize` is bounded by the sum of `meanJetDens` for `(actX, actY)` and `(mnX, mnY)`. -/
theorem jetSize_le_act_add_mean (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L) (τ : ℝ) (y : Space) :
    jetSize Pl K L μ T τ y ≤
      meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ) y +
        meanJetDens (mnX Pl K L μ T τ) (mnY Pl K L μ T τ) y := by
  have h1 := norm_fderiv_le_gradSize (actX Pl K L μ T τ) y
  have h2 := norm_fderiv_le_gradSize (mnX Pl K L μ T τ) y
  unfold gradSize at h1 h2
  unfold jetSize hessData meanJetDens hessSize
  linarith

/-- **The `Y_{22/3}` bound of `jetSize`** (source 5214-5217, 5267-5268, 5282-5289:
`‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22} N₁`). -/
def RespJetGradAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (ringRead L.ε⁻¹ (jetSize Pl K L μ T))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    eLpNorm (ringRead L.ε⁻¹ (jetSize Pl K L μ T)) (22 / 3)
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T

/-- Measurability of `jetSize` in the ring chart. -/
def ActJetMeasAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (ringRead L.ε⁻¹ (jetSize Pl K L μ T))
      (ringPhysμ L.ε⁻¹ (cOf L.ν))

/-- **The `Y_{22/3}` bound of the actual thin Ward response `(actX, actY)`** (source 5214-5217,
5282-5289: `repair:phase-gradient` applied to the old thin source `χ_oT₁`). -/
def ActGradAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ =>
        meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    eLpNorm (ringRead L.ε⁻¹ fun τ =>
        meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ)) (22 / 3)
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T

/-- `ActJetMeasAt`, `ActGradAt`, and `MeanGradAt` give `RespJetGradAt`. -/
theorem respJetGradAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    {C : ℝ} {k : ℕ} (hC : 0 ≤ C) (hm : ActJetMeasAt Pl K L μ)
    (ha : ActGradAt Pl K L μ C k) (hmn : MeanGradAt Pl K L μ C k) :
    RespJetGradAt Pl K L μ (2 * C) k := by
  intro T
  refine ⟨hm T, ?_⟩
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν)
  set ja := ringRead L.ε⁻¹ fun τ => meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ)
  set jm := ringRead L.ε⁻¹ fun τ => meanJetDens (mnX Pl K L μ T τ) (mnY Pl K L μ T τ)
  have hle : ∀ᵐ p ∂μp, ‖ringRead L.ε⁻¹ (jetSize Pl K L μ T) p‖ ≤ ‖(ja + jm) p‖ := by
    refine ae_of_all _ fun p => ?_
    have hj0 : 0 ≤ ringRead L.ε⁻¹ (jetSize Pl K L μ T) p := by
      unfold ringRead
      exact (add_nonneg (cmpData_nonneg Pl K L μ T _ _) (hessData_nonneg Pl K L μ T _ _)).trans
        (cmp_add_hess_le_jet Pl K L μ T _ _)
    have hsum0 : 0 ≤ ja p + jm p :=
      add_nonneg (meanJetDens_nonneg _ _ _) (meanJetDens_nonneg _ _ _)
    rw [Pi.add_apply, Real.norm_of_nonneg hj0, Real.norm_of_nonneg hsum0]
    exact jetSize_le_act_add_mean Pl K L μ T _ _
  have h223 : (1 : ℝ≥0∞) ≤ 22 / 3 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hE0 : 0 ≤ C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ) := by
    have := L.ν_pos; have := L.ε_pos; positivity
  calc eLpNorm (ringRead L.ε⁻¹ (jetSize Pl K L μ T)) (22 / 3) μp
      ≤ eLpNorm (ja + jm) (22 / 3) μp := eLpNorm_mono_ae hle
    _ ≤ eLpNorm ja (22 / 3) μp + eLpNorm jm (22 / 3) μp :=
        eLpNorm_add_le (ha T).1 (hmn T).1 h223
    _ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T +
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T :=
        add_le_add (ha T).2 (hmn T).2
    _ = ENNReal.ofReal (2 * C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T := by
        rw [← add_mul, ← ENNReal.ofReal_add hE0 hE0]
        congr 2
        ring

/-! ## 2b. Chart measurability and slice transfer for `(actX, actY)` and `jetSize` -/

private def bg_rjOff (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space) : ℝ :=
  ‖jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y‖ +
    ∑ j : Fin 3, ‖wemOff (fun t z => physPd (X t) j z) τ y‖ +
    ∑ j : Fin 3, ∑ l : Fin 3, ‖wemOff (fun t z => physPd2 (X t) j l z) τ y‖

private def bg_actJetOff (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space) : ℝ :=
  ‖jet1 fun j => wemOff (fun t z => physPd (X t) j z) τ y‖ +
    ‖jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y‖ +
    ∑ j : Fin 3, ∑ l : Fin 3, ‖wemOff (fun t z => physPd2 (X t) j l z) τ y‖

private lemma bg_rjOff_eq_of_not_mem (X Y : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    bg_rjOff X Y τ y = meanJetDens (X τ) (Y τ) y := by
  unfold bg_rjOff meanJetDens
  have hY : (jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y) = fderiv ℝ (Y τ) y := by
    conv_rhs => rw [eq_jet1 (fderiv ℝ (Y τ) y)]
    congr 1; funext j
    exact wem_off_of_not_mem (F := fun t z => physPd (Y t) j z) hy
  have hX1 : ∀ j : Fin 3, wemOff (fun t z => physPd (X t) j z) τ y = physPd (X τ) j y :=
    fun j => wem_off_of_not_mem (F := fun t z => physPd (X t) j z) hy
  have hX2 : ∀ j l : Fin 3, wemOff (fun t z => physPd2 (X t) j l z) τ y = physPd2 (X τ) j l y :=
    fun j l => wem_off_of_not_mem (F := fun t z => physPd2 (X t) j l z) hy
  simp only [hY, hX1, hX2]

private lemma bg_actJetOff_eq_of_not_mem (X Y : ℝ → Space → Space) (τ : ℝ) {y : Space}
    (hy : y ∉ axis) :
    bg_actJetOff X Y τ y =
      ‖fderiv ℝ (X τ) y‖ + ‖fderiv ℝ (Y τ) y‖ + hessSize (X τ) y := by
  unfold bg_actJetOff hessSize
  have hX : (jet1 fun j => wemOff (fun t z => physPd (X t) j z) τ y) = fderiv ℝ (X τ) y := by
    conv_rhs => rw [eq_jet1 (fderiv ℝ (X τ) y)]
    congr 1; funext j
    exact wem_off_of_not_mem (F := fun t z => physPd (X t) j z) hy
  have hY : (jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y) = fderiv ℝ (Y τ) y := by
    conv_rhs => rw [eq_jet1 (fderiv ℝ (Y τ) y)]
    congr 1; funext j
    exact wem_off_of_not_mem (F := fun t z => physPd (Y t) j z) hy
  have hX2 : ∀ j l : Fin 3, wemOff (fun t z => physPd2 (X t) j l z) τ y = physPd2 (X τ) j l y :=
    fun j l => wem_off_of_not_mem (F := fun t z => physPd2 (X t) j l z) hy
  simp only [hX, hY, hX2]

theorem isOldL2_thinG (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (T : LStr Pl K L) :
    IsOldL2 (cOf L.ν) L.ν (thinG Pl K L T) :=
  wo_isOldL2_rep (wardOldNormLe_of gainMeasureLower) (vr_rhoB_pos Pl K L hC0) hmZ L.ν_pos
    K.hχo (thinPart T)

private lemma bg_off_measurable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hχy : IsStreamCutoff K.χy) (hμ : -(1 / 4 : ℝ) < μ) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (T : LStr Pl K L) :
    (Measurable fun x : ℝ × Space => bg_rjOff (actX Pl K L μ T) (actY Pl K L μ T) x.1 x.2) ∧
    (Measurable fun x : ℝ × Space => bg_actJetOff (actX Pl K L μ T) (actY Pl K L μ T) x.1 x.2) := by
  have hO : IsOpen axisᶜ := isClosed_axis.isOpen_compl
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hχy' : IsYoungCutoff K.χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  have hg : IsOldL2 (cOf L.ν) L.ν (thinG Pl K L T) := isOldL2_thinG Pl K L hC0 hmZ T
  set X := actX Pl K L μ T with hXdef
  set Y := actY Pl K L μ T with hYdef
  have hD := fun τ =>
    wardXDiff_proved L.ν μ L.ε⁻¹ (cOf L.ν) K.χy hχy' hν hR hc hμ (thinG Pl K L T) hg τ
  have hC3 : ∀ τ, ContDiffOn ℝ 3 (X τ) axisᶜ := fun τ => (hD τ).1
  have hXm : Measurable fun x : ℝ × Space => X x.1 x.2 :=
    T8_4.t84_ward_stream hχy' hg.measurable
  have dX : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (X τ) y := fun τ y hy =>
    WardCalc.diffAt_of_contDiffOn hO (hC3 τ) hy
  have dpX : ∀ l : Fin 3, ∀ τ y, y ∉ axis →
      DifferentiableAt ℝ ((fun τ y => physPd (X τ) l y) τ) y := fun l τ y hy =>
    WardCalc.differentiableAt_physPd hO (hC3 τ) hy l
  have dY : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (Y τ) y := by
    intro τ y hy
    have hcd : ContDiffAt ℝ 3 (X τ) y := (hC3 τ).contDiffAt (hO.mem_nhds hy)
    have d1 : DifferentiableAt ℝ (fun y' => deriv (fun t => X t y') τ) y :=
      ((hD τ).2.2).differentiableAt (hO.mem_nhds hy)
    have d2 : DifferentiableAt ℝ (fun y' => fderiv ℝ (X τ) y' y') y :=
      ((hcd.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).clm_apply
        differentiableAt_id
    have d3 : DifferentiableAt ℝ (fun y' => physLap (X τ) y') y := by
      unfold physLap
      exact DifferentiableAt.fun_sum fun j _ =>
        WardCalc.differentiableAt_physPd2 hO (hC3 τ) hy j j
    have d4 : DifferentiableAt ℝ (X τ) y := dX τ y hy
    have hfun : Y τ = fun y' => deriv (fun t => X t y') τ - (1 / 2 : ℝ) • fderiv ℝ (X τ) y' y' -
        L.ν • physLap (X τ) y' + (μ + 1 - 1 / 2) • X τ y' := by
      funext y'
      simp only [hYdef, hXdef, actY, actX, wardY, physDmu]
    rw [hfun]
    exact ((d1.sub (d2.const_smul (1 / 2 : ℝ))).sub (d3.const_smul L.ν)).add
      (d4.const_smul (μ + 1 - 1 / 2))
  have mX : Measurable fun x : ℝ × Space => wemOff X x.1 x.2 := wem_off_meas hXm
  have mpX : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (X τ) j y) x.1 x.2 := fun j => wem_meas_pd mX dX j
  have mp2X : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (X τ) l y) (mpX l) (dpX l) j
  have mdt : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 :=
    wem_meas_deriv_tau hXm fun τ y hy => (hD τ).2.1 y hy
  have mfy : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 :=
    wem_meas_fderiv_apply (V := fun _ y => y) mX measurable_snd dX
  have mY : Measurable fun x : ℝ × Space => wemOff Y x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff Y x.1 x.2) = fun x =>
        wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 -
          (1 / 2 : ℝ) • wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 -
          L.ν • ∑ j : Fin 3, wemOff (fun τ y => physPd2 (X τ) j j y) x.1 x.2 +
          (μ + 1 - 1 / 2) • wemOff X x.1 x.2 := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp [wemOff, hx]
      · simp only [wem_off_of_not_mem hx, hYdef, hXdef, actY, actX, wardY, physDmu, physLap]
    rw [heq]
    exact ((mdt.sub (mfy.const_smul (1 / 2 : ℝ))).sub
      ((Finset.measurable_sum _ fun j _ => mp2X j j).const_smul L.ν)).add
      (mX.const_smul (μ + 1 - 1 / 2))
  have mpY : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (Y τ) j y) x.1 x.2 := fun j => wem_meas_pd mY dY j
  have m1Y : Measurable fun x : ℝ × Space =>
      ‖jet1 fun j => wemOff (fun t z => physPd (Y t) j z) x.1 x.2‖ :=
    (continuous_jet1.measurable.comp (measurable_pi_iff.2 fun j => mpY j)).norm
  have m1X : Measurable fun x : ℝ × Space =>
      ‖jet1 fun j => wemOff (fun t z => physPd (X t) j z) x.1 x.2‖ :=
    (continuous_jet1.measurable.comp (measurable_pi_iff.2 fun j => mpX j)).norm
  have m2 : Measurable fun x : ℝ × Space =>
      ∑ j : Fin 3, ‖wemOff (fun t z => physPd (X t) j z) x.1 x.2‖ :=
    Finset.measurable_sum _ fun j _ => (mpX j).norm
  have m3 : Measurable fun x : ℝ × Space =>
      ∑ j : Fin 3, ∑ l : Fin 3, ‖wemOff (fun t z => physPd2 (X t) j l z) x.1 x.2‖ :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ => (mp2X j l).norm
  exact ⟨(m1Y.add m2).add m3, (m1X.add m1Y).add m3⟩

private lemma bg_ringRead_measurable {R : ℝ} {F : ℝ → Space → ℝ}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2) : Measurable (ringRead R F) := by
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hτ : Measurable fun p : Chart => NearInst.chartTau R p := by
    unfold NearInst.chartTau
    exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have hY : Measurable fun p : Chart => NearInst.chartY R p := by
    unfold NearInst.chartY
    exact T8_4.t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
      (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
      (measurable_const.div hsq) measurable_const
      ((measurable_snd.comp measurable_snd).div hsq)
  exact hF.comp (hτ.prodMk hY)

private lemma bg_wardX_periodic (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) :
    wardX ν μ R c χy g (τ + 2 * c / R) = wardX ν μ R c χy g τ := by
  have hZ : wardX0 ν μ R c g (τ + 2 * c / R) = wardX0 ν μ R c g τ :=
    funext (wardX0_periodic oldPhysPeriodic ν μ R c g τ)
  funext y
  simp only [wardX, wardStreamCut, outPrim, hZ]

/-- Chart measurability and meridional-slice transfer for `meanJetDens (actX ...) (actY ...)`. -/
theorem actJetChartTransfer (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχy : IsStreamCutoff K.χy) (hμ : -(1 / 4 : ℝ) < μ) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (T : LStr Pl K L) :
    AEStronglyMeasurable
      (ringRead L.ε⁻¹ (fun τ => meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ)))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    ∀ B : ℝ≥0∞,
      (∀ τ : ℝ, lqNorm (22 / 3)
        (fun z : Space => ENNReal.ofReal
          (meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ) !₂[ϱ z, 0, z 2])) ≤ B) →
      eLpNorm (ringRead L.ε⁻¹ (fun τ => meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ)))
        (22 / 3) (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ B := by
  set R : ℝ := L.ε⁻¹
  set c : ℝ := cOf L.ν
  set X := actX Pl K L μ T
  set Y := actY Pl K L μ T
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < R := inv_pos.2 L.ε_pos
  have hc : 0 < c := cOf_pos hν
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set g : Chart → ℝ := ringRead R (bg_rjOff X Y) with hgdef
  have hgm : Measurable g :=
    bg_ringRead_measurable (bg_off_measurable hχy hμ hC0 hmZ T).1
  have hge_age : ringRead R (fun τ => meanJetDens (X τ) (Y τ)) =ᵐ[ageμ c (-5 / 2)] g := by
    filter_upwards [ae_ageμ_mem hc (-5 / 2)] with p hp
    have hs : 0 < p.1 := hp.1
    have hy : NearInst.chartY R p ∉ axis := by
      intro h
      have h' : NearInst.chartY R p 0 = 0 ∧ NearInst.chartY R p 1 = 0 := h
      have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
      have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hs).ne'
      exact hne (h1 ▸ h'.1)
    unfold g ringRead
    exact (bg_rjOff_eq_of_not_mem X Y (NearInst.chartTau R p) hy).symm
  have hge : ringRead R (fun τ => meanJetDens (X τ) (Y τ)) =ᵐ[ringPhysμ R c] g := by
    unfold ringPhysμ
    exact Measure.ae_smul_measure hge_age _
  refine ⟨hgm.aestronglyMeasurable.congr hge.symm, ?_⟩
  intro B hB
  set q : ℝ := 22 / 3 with hqdef
  have hq0 : 0 < q := by rw [hqdef]; norm_num
  have hp0 : (22 / 3 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt_top : (22 / 3 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hpR : (22 / 3 : ℝ≥0∞).toReal = q := by
    rw [ENNReal.toReal_div, hqdef]; norm_num
  set G : Chart → ℝ≥0∞ := fun p => ‖g p‖ₑ ^ q with hGdef
  have hGm : Measurable G := hgm.enorm.pow_const q
  have hL : eLpNorm (ringRead R fun τ => meanJetDens (X τ) (Y τ)) (22 / 3) (ringPhysμ R c) =
      (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) ^ (1 / q) := by
    rw [eLpNorm_congr_ae hge, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt_top, hpR,
      ringPhysμ, lintegral_smul_measure]
    rfl
  have hperX : Function.Periodic X (2 * c / R) :=
    fun τ => bg_wardX_periodic L.ν μ R c K.χy (thinG Pl K L T) τ
  have hperY : Function.Periodic Y (2 * c / R) :=
    fun τ => vr_wardY_periodic L.ν μ R c K.χy (thinG Pl K L T) τ
  have hpt : ∀ (τ : ℝ) (z : Space), z ∉ axis →
      G (NearInst.chartOf R c z τ) =
        ENNReal.ofReal (meanJetDens (X τ) (Y τ) !₂[ϱ z, 0, z 2]) ^ q := by
    intro τ z hz
    have hρ : 0 < NearInst.hRad z := by
      have h1 : ϱ z ≠ 0 := fun h => hz ((mem_axis_iff z).2 h)
      exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h1)
    have hmerid_not_axis : (!₂[ϱ z, 0, z 2] : Space) ∉ axis := by
      intro h
      have h' : (!₂[ϱ z, 0, z 2] : Space) 0 = 0 ∧ (!₂[ϱ z, 0, z 2] : Space) 1 = 0 := h
      exact hz ((mem_axis_iff z).2 h'.1)
    have hYo : NearInst.chartY R (NearInst.chartOf R c z τ) = !₂[ϱ z, 0, z 2] :=
      chartYOf_proved R c z τ hR hρ
    have hTo := chartTauOf_proved R c z τ hR.ne'
    have hg_eq : g (NearInst.chartOf R c z τ) = meanJetDens (X τ) (Y τ) !₂[ϱ z, 0, z 2] := by
      show bg_rjOff X Y (NearInst.chartTau R (NearInst.chartOf R c z τ))
          (NearInst.chartY R (NearInst.chartOf R c z τ)) = _
      rw [hYo, bg_rjOff_eq_of_not_mem X Y _ hmerid_not_axis, hTo, hperX.sub_int_mul_eq,
        hperY.sub_int_mul_eq]
    simp only [hGdef, hg_eq]
    congr 1
    rw [← ofReal_norm, Real.norm_of_nonneg (meanJetDens_nonneg (X τ) (Y τ) _)]
  have hslice : ∀ τ : ℝ, ∫⁻ z : Space, G (NearInst.chartOf R c z τ) ≤ B ^ q := by
    intro τ
    have heq : ∫⁻ z : Space, G (NearInst.chartOf R c z τ) =
        ∫⁻ z : Space, ENNReal.ofReal (meanJetDens (X τ) (Y τ) !₂[ϱ z, 0, z 2]) ^ q :=
      lintegral_congr_ae (ae_not_mem_axis.mono fun z hz => hpt τ z hz)
    rw [heq]
    have h1 := ENNReal.rpow_le_rpow (hB τ) hq0.le
    unfold lqNorm at h1
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at h1
    exact h1
  have hCP := chartPhaseLIntegral R c hR hc G hGm
  have hInt : ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
      ∫⁻ p, G p ∂(ageμ c (-5 / 2)) ≤ B ^ q * ENNReal.ofReal (2 * c / R) := by
    rw [← hCP]
    calc ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z : Space, G (NearInst.chartOf R c z τ)
        ≤ ∫⁻ _ in Ioc 0 (2 * c / R), B ^ q := lintegral_mono fun τ => hslice τ
      _ = B ^ q * ENNReal.ofReal (2 * c / R) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hinv : ENNReal.ofReal (2 * c / R)⁻¹ * ENNReal.ofReal (2 * c / R) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos hP0]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hP0).ne' ENNReal.ofReal_ne_top
  have hM : ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2)) ≤ B ^ q := by
    calc ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))
        = (ENNReal.ofReal (2 * c / R)⁻¹ * ENNReal.ofReal (2 * c / R)) *
            (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal (2 * c / R)⁻¹ *
            (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
              ∫⁻ p, G p ∂(ageμ c (-5 / 2))) := by ring
      _ ≤ ENNReal.ofReal (2 * c / R)⁻¹ * (B ^ q * ENNReal.ofReal (2 * c / R)) :=
          mul_le_mul_of_nonneg_left hInt zero_le
      _ = (ENNReal.ofReal (2 * c / R)⁻¹ * ENNReal.ofReal (2 * c / R)) * B ^ q := by ring
      _ = B ^ q := by rw [hinv, one_mul]
  rw [hL]
  calc (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) ^ (1 / q)
      ≤ (B ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hM (by positivity)
    _ = B := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

/-- Ring-chart measurability of `jetSize` at one regime. -/
theorem actJetMeasAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχy : IsStreamCutoff K.χy) (hμ : -(1 / 4 : ℝ) < μ) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) :
    ActJetMeasAt Pl K L μ := by
  intro T
  set R : ℝ := L.ε⁻¹
  set c : ℝ := cOf L.ν
  set X := actX Pl K L μ T
  set Y := actY Pl K L μ T
  set MX := mnX Pl K L μ T 0
  set MY := mnY Pl K L μ T 0
  have hR : 0 < R := inv_pos.2 L.ε_pos
  have hc : 0 < c := cOf_pos L.ν_pos
  have hact_m : Measurable (ringRead R (bg_actJetOff X Y)) :=
    bg_ringRead_measurable (bg_off_measurable hχy hμ hC0 hmZ T).2
  have hmn_dens : Measurable (fun y : Space =>
      ‖fderiv ℝ MX y‖ + ‖fderiv ℝ MY y‖ + hessSize MX y) := by
    have h1 : Measurable fun y => ‖fderiv ℝ MX y‖ := (measurable_fderiv ℝ MX).norm
    have h2 : Measurable fun y => ‖fderiv ℝ MY y‖ := (measurable_fderiv ℝ MY).norm
    have h3 : Measurable fun y => hessSize MX y :=
      Finset.measurable_fun_sum _ fun j _ => Finset.measurable_fun_sum _ fun l _ =>
        (measurable_fderiv_apply_const ℝ (fun y' => physPd MX l y') (coordinateVector j)).norm
    exact (h1.add h2).add h3
  have hmn_m : Measurable (fun p : Chart =>
      ‖fderiv ℝ MX (NearInst.chartY R p)‖ + ‖fderiv ℝ MY (NearInst.chartY R p)‖ +
        hessSize MX (NearInst.chartY R p)) :=
    hmn_dens.comp (mg_measurable_chartY R)
  set g : Chart → ℝ := fun p =>
    ringRead R (bg_actJetOff X Y) p +
      (‖fderiv ℝ MX (NearInst.chartY R p)‖ + ‖fderiv ℝ MY (NearInst.chartY R p)‖ +
        hessSize MX (NearInst.chartY R p))
  have hgm : Measurable g := hact_m.add hmn_m
  have hge_age : ringRead R (jetSize Pl K L μ T) =ᵐ[ageμ c (-5 / 2)] g := by
    filter_upwards [ae_ageμ_mem hc (-5 / 2)] with p hp
    have hs : 0 < p.1 := hp.1
    have hy : NearInst.chartY R p ∉ axis := by
      intro h
      have h' : NearInst.chartY R p 0 = 0 ∧ NearInst.chartY R p 1 = 0 := h
      have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
      have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hs).ne'
      exact hne (h1 ▸ h'.1)
    show jetSize Pl K L μ T (NearInst.chartTau R p) (NearInst.chartY R p) =
      bg_actJetOff X Y (NearInst.chartTau R p) (NearInst.chartY R p) +
        (‖fderiv ℝ MX (NearInst.chartY R p)‖ + ‖fderiv ℝ MY (NearInst.chartY R p)‖ +
          hessSize MX (NearInst.chartY R p))
    rw [bg_actJetOff_eq_of_not_mem X Y (NearInst.chartTau R p) hy]
    have hMX : mnX Pl K L μ T (NearInst.chartTau R p) = MX := rfl
    have hMY : mnY Pl K L μ T (NearInst.chartTau R p) = MY := rfl
    unfold jetSize hessData X Y
    rw [hMX, hMY]
    ring
  have hge : ringRead R (jetSize Pl K L μ T) =ᵐ[ringPhysμ R c] g := by
    unfold ringPhysμ
    exact Measure.ae_smul_measure hge_age _
  exact hgm.aestronglyMeasurable.congr hge.symm

/-! ## 3. Hölder bound for `remTerm` and regime assembly `backgroundSplitAt_of` -/

lemma aestronglyMeasurable_src_of_ringPhys {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {f : Chart → ℝ}
    (hf : AEStronglyMeasurable f (ringPhysμ R c)) :
    AEStronglyMeasurable f (srcMeasure c) :=
  hf.stronglyMeasurable_mk.aestronglyMeasurable.congr
    (Filter.EventuallyEq.symm (holderConv_ae_src hR hc hf.ae_eq_mk))

lemma coefOf_coord0_norm (R : ℝ) (g : ℝ → Space → ℝ) (hg : ∀ τ y, 0 ≤ g τ y) (p : Chart) :
    ‖coefOf R (fun τ y => (g τ y) • coordinateVector (0 : Fin 3)) p‖ =
      (Real.sqrt p.1)⁻¹ * ringRead R g p := by
  set x := ringRead R g p
  have hx0 : 0 ≤ x := hg _ _
  have h0 : ((g (NearInst.chartTau R p) (NearInst.chartY R p)) •
      coordinateVector (0 : Fin 3)) 0 = x := by
    simp [x, ringRead, coordinateVector]
  have h2 : ((g (NearInst.chartTau R p) (NearInst.chartY R p)) •
      coordinateVector (0 : Fin 3)) 2 = 0 := by
    simp [coordinateVector]
  unfold coefOf
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), h0, h2]
  congr 1
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs,
    sq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.sqrt_sq hx0

/-- **Remainder `L²(srcMeasure)` bound at one regime** from `PresFlatAt`, `CoefChgAt`, and
`RespJetGradAt` via `ringHolderConv`. -/
theorem remTerm_bound_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    {C : ℝ} {k : ℕ} (hC : 0 ≤ C) (hν1 : L.ν ≤ 1)
    (h1 : PresFlatAt K L C k) (h2 : CoefChgAt Pl K L C k)
    (h3 : RespJetGradAt Pl K L μ C k) (T : LStr Pl K L) :
    AEStronglyMeasurable (remTerm Pl K L μ (bgBr L (C * L.ν⁻¹ ^ k)) T) (srcMeasure (cOf L.ν)) ∧
      eLpNorm (remTerm Pl K L μ (bgBr L (C * L.ν⁻¹ ^ k)) T) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal ((16 + C) * C ^ 2 * L.ν⁻¹ ^ (3 * k) *
          (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  set P := L.ν⁻¹ ^ k
  set M := C * P
  have hP1 : 1 ≤ P := one_le_pow₀ hνinv1
  have hM0 : 0 ≤ M := by positivity
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν)
  set μs := srcMeasure (cOf L.ν)
  set fc := ringRead L.ε⁻¹ fun τ => coefChgDens (L.U τ) (L.V τ)
  set fp := ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (liftP L τ)
  set a := bgBrLin L M
  set b := jetSize Pl K L μ T
  have hra : ringRead L.ε⁻¹ a = (1 + 12 * L.ν + M) • fc + (3 : ℝ) • fp := by
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hma : AEStronglyMeasurable (ringRead L.ε⁻¹ a) μp := by
    rw [hra]
    exact (h2.1.const_smul (1 + 12 * L.ν + M)).add (h1.1.const_smul 3)
  have hmb : AEStronglyMeasurable (ringRead L.ε⁻¹ b) μp := (h3 T).1
  have hrem_eq : remTerm Pl K L μ (bgBr L M) T =
      fun p => (Real.sqrt p.1)⁻¹ * ringRead L.ε⁻¹ a p * ringRead L.ε⁻¹ b p := by
    funext p
    exact remTerm_bgBr_eq_lin Pl K L μ h2 T p
  refine ⟨?_, ?_⟩
  · rw [hrem_eq]
    have hms : Measurable fun p : Chart => (Real.sqrt p.1)⁻¹ :=
      (Real.continuous_sqrt.measurable.comp measurable_fst).inv
    exact (hms.aestronglyMeasurable.mul
      (aestronglyMeasurable_src_of_ringPhys hR hc hma)).mul
      (aestronglyMeasurable_src_of_ringPhys hR hc hmb)
  · set F : ℝ → Space → Space := fun τ y => (a τ y * b τ y) • coordinateVector (0 : Fin 3)
    have hab0 : ∀ τ y, 0 ≤ a τ y * b τ y := fun τ y =>
      mul_nonneg (bgBrLin_nonneg L hM0 τ y)
        ((add_nonneg (cmpData_nonneg Pl K L μ T τ y) (hessData_nonneg Pl K L μ T τ y)).trans
          (cmp_add_hess_le_jet Pl K L μ T τ y))
    have hnorm_eq : ∀ p : Chart,
        ‖remTerm Pl K L μ (bgBr L M) T p‖ = ‖coefOf L.ε⁻¹ F p‖ := by
      intro p
      have h1' := coefOf_coord0_norm L.ε⁻¹ (fun τ y => a τ y * b τ y) hab0 p
      have h2' := remTerm_bgBr_eq_lin Pl K L μ h2 T p
      have hr0 : 0 ≤ remTerm Pl K L μ (bgBr L M) T p :=
        remTerm_nonneg Pl K L μ (bgBr_nonneg L hM0) T p
      rw [Real.norm_of_nonneg hr0, h2', h1']
      unfold ringRead
      ring
    have heLp : eLpNorm (remTerm Pl K L μ (bgBr L M) T) 2 μs = eLpNorm (coefOf L.ε⁻¹ F) 2 μs :=
      eLpNorm_congr_norm_ae (ae_of_all _ hnorm_eq)
    rw [heLp]
    have hpw : ∀ p : Chart, 0 < p.1 →
        ‖F (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
          ringRead L.ε⁻¹ a p * ringRead L.ε⁻¹ b p := by
      intro p _
      unfold F ringRead
      rw [norm_smul, norm_coordinateVector_sj, mul_one,
        Real.norm_of_nonneg (hab0 _ _)]
    have hconv := ringHolderConv L.ε⁻¹ (cOf L.ν) hR hc F a b hma hmb hpw
    have h114 : (1 : ℝ≥0∞) ≤ 11 / 4 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hA0 : 0 ≤ 1 + 12 * L.ν + M := by positivity
    have hna : eLpNorm (ringRead L.ε⁻¹ a) (11 / 4) μp ≤
        ENNReal.ofReal ((4 + 12 * L.ν + M) * (M * rhoRep K L)) := by
      have hρ0 : 0 ≤ rhoRep K L := rhoRep_nonneg K L
      have hMR0 : 0 ≤ M * rhoRep K L := by positivity
      rw [hra]
      calc eLpNorm ((1 + 12 * L.ν + M) • fc + (3 : ℝ) • fp) (11 / 4) μp
          ≤ eLpNorm ((1 + 12 * L.ν + M) • fc) (11 / 4) μp +
              eLpNorm ((3 : ℝ) • fp) (11 / 4) μp :=
            eLpNorm_add_le (h2.1.const_smul _) (h1.1.const_smul _) h114
        _ ≤ ENNReal.ofReal (1 + 12 * L.ν + M) * ENNReal.ofReal (M * rhoRep K L) +
              ENNReal.ofReal 3 * ENNReal.ofReal (M * rhoRep K L) := by
            rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal hA0,
              Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 3)]
            exact add_le_add (mul_le_mul' le_rfl h2.2.1) (mul_le_mul' le_rfl h1.2)
        _ = ENNReal.ofReal ((4 + 12 * L.ν + M) * (M * rhoRep K L)) := by
            rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
    have hεpow : L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) = L.ε ^ (85 / 22 : ℝ) := by
      rw [show (85 / 22 : ℝ) = 1 + 3 / 11 + 57 / 22 by norm_num, Real.rpow_add hε,
        Real.rpow_add hε, Real.rpow_one]
    have hfac : 4 + 12 * L.ν + M ≤ (16 + C) * P := by
      have : 4 + 12 * L.ν ≤ 16 * P := by linarith
      linarith
    have hreal : L.ε * ((4 + 12 * L.ν + M) * (M * rhoRep K L)) * (M * L.ε ^ (57 / 22 : ℝ)) ≤
        (16 + C) * C ^ 2 * L.ν⁻¹ ^ (3 * k) *
          (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
      have hE0 : 0 ≤ M ^ 2 * (L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) *
          Real.exp (K.m0 / L.ν)) := by positivity
      calc L.ε * ((4 + 12 * L.ν + M) * (M * rhoRep K L)) * (M * L.ε ^ (57 / 22 : ℝ))
          = (4 + 12 * L.ν + M) * (M ^ 2 * (L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) *
              Real.exp (K.m0 / L.ν))) := by
            rw [rhoRep]; ring
        _ ≤ ((16 + C) * P) * (M ^ 2 * (L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) *
              Real.exp (K.m0 / L.ν))) :=
            mul_le_mul_of_nonneg_right hfac hE0
        _ = (16 + C) * C ^ 2 * L.ν⁻¹ ^ (3 * k) *
              (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
            rw [← hεpow]
            simp only [M, P]
            ring
    have hρ0 : 0 ≤ rhoRep K L := rhoRep_nonneg K L
    calc eLpNorm (coefOf L.ε⁻¹ F) 2 μs
        ≤ ENNReal.ofReal L.ε⁻¹⁻¹ * eLpNorm (ringRead L.ε⁻¹ a) (11 / 4) μp *
            eLpNorm (ringRead L.ε⁻¹ b) (22 / 3) μp := hconv
      _ ≤ ENNReal.ofReal L.ε * ENNReal.ofReal ((4 + 12 * L.ν + M) * (M * rhoRep K L)) *
            (ENNReal.ofReal (M * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T) := by
          rw [inv_inv]
          exact mul_le_mul' (mul_le_mul' le_rfl hna) (h3 T).2
      _ = ENNReal.ofReal (L.ε * ((4 + 12 * L.ν + M) * (M * rhoRep K L)) *
            (M * L.ε ^ (57 / 22 : ℝ))) * oldN1 Pl K L T := by
          rw [← ENNReal.ofReal_mul hε.le, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((16 + C) * C ^ 2 * L.ν⁻¹ ^ (3 * k) *
            (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T := by
          gcongr

/-- **Regime-level assembly of `BackgroundSplitAt`** from the localized bound (`bgBl`, `bgBeta`) and
the three remainder bounds (`PresFlatAt`, `CoefChgAt`, `RespJetGradAt`). -/
theorem backgroundSplitAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    {Cl C : ℝ} {kl k : ℕ} (hC : 0 ≤ C) (hν1 : L.ν ≤ 1)
    (hloc1 : ∀ (τ : ℝ) (p : Chart), 0 < p.1 → p.1 ≤ 1 / L.ν →
      bgBl L τ (NearInst.chartY L.ε⁻¹ p) ≤ bgBeta (Cl * L.ν⁻¹ ^ kl) p.1 p.2.2)
    (hloc2 : ∫⁻ s in Ioc (0 : ℝ) (1 / L.ν), ∫⁻ η : ℝ,
        ENNReal.ofReal (s ^ (5 / 2 : ℝ) * bgBeta (Cl * L.ν⁻¹ ^ kl) s η ^ 2) ≤
      ENNReal.ofReal (4 * Cl ^ 2 * L.ν⁻¹ ^ (2 * kl + 4)))
    (h1 : PresFlatAt K L C k) (h2 : CoefChgAt Pl K L C k)
    (h3 : RespJetGradAt Pl K L μ C k) :
    BackgroundSplitAt Pl K L μ (4 * Cl ^ 2 + (16 + C) * C ^ 2) (max (2 * kl + 4) (3 * k)) := by
  have hν : 0 < L.ν := L.ν_pos
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  set C' := 4 * Cl ^ 2 + (16 + C) * C ^ 2
  set k' := max (2 * kl + 4) (3 * k)
  have hM0 : 0 ≤ C * L.ν⁻¹ ^ k := by positivity
  refine ⟨bgBl L, bgBr L (C * L.ν⁻¹ ^ k), bgBeta (Cl * L.ν⁻¹ ^ kl),
    bgBr_split L (C * L.ν⁻¹ ^ k), bgBr_nonneg L hM0, hloc1, ?_, fun T => ?_⟩
  · refine hloc2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hP : L.ν⁻¹ ^ (2 * kl + 4) ≤ L.ν⁻¹ ^ k' := pow_le_pow_right₀ hνinv1 (le_max_left _ _)
    have hC_le : 4 * Cl ^ 2 ≤ C' := by simp only [C']; linarith [ mul_nonneg (by positivity : (0:ℝ) ≤ 16 + C) (sq_nonneg C) ]
    exact mul_le_mul hC_le hP (by positivity) (by positivity)
  · obtain ⟨hm, hb⟩ := remTerm_bound_of Pl K L μ hC hν1 h1 h2 h3 T
    refine ⟨hm, hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)⟩
    have hP : L.ν⁻¹ ^ (3 * k) ≤ L.ν⁻¹ ^ k' := pow_le_pow_right₀ hνinv1 (le_max_right _ _)
    have hC_le : (16 + C) * C ^ 2 ≤ C' := by simp only [C']; linarith [sq_nonneg Cl]
    have hE0 : 0 ≤ L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) := by
      have := L.ε_pos; positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hC_le hP (by positivity) (by positivity)) hE0

/-! ## 4. Sequence-level hypotheses and assembly of `SeqData.BackgroundSplit` -/

namespace SeqData

variable (D : SeqData)

/-- Sequence-level `Y_{22/3}` bound of `jetSize`. -/
def RespJetGrad : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RespJetGradAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence-level ring-chart measurability of `jetSize`. -/
def ActJetMeas : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ActJetMeasAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence-level `Y_{22/3}` bound of the actual thin Ward response `(actX, actY)`. -/
def ActGrad : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ActGradAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-- Sequence-level ring-chart measurability of `jetSize`, proved from `RepairStanding`. -/
theorem actJetMeas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ActJetMeas := by
  have hev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  filter_upwards [hev] with n hμn z hz
  have hμ : -(1 / 4 : ℝ) < D.mu n z := by
    have := (hμn z hz).1
    linarith [hst.sigma_pos]
  exact actJetMeasAt_of D.Pl D.K (D.level n) (D.mu n z) hst.chiY hμ hst.C0_pos hmZ

/-- Reduction of `D.CoefChg` to `D.RhoW1` using the already-proved `coefChgMeas`, `coefChgLp`,
`rawSupBound`, `vSupBound`, and `nuLeOneRhoNonneg`. -/
theorem coefChg_of_rhoW1 (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h : D.RhoW1) : D.CoefChg :=
  coefChg_of D hst (coefChgMeas D hst)
    (coefChgQuant_of D (coefChgLp D hst)
      (coefChgSup_of D hst (rawSupBound D hst) h (vSupBound D hst))
      (nuLeOneRhoNonneg D hst))

/-- Reduction of `D.RespJetGrad` to `D.ActJetMeas` and `D.ActGrad` using the already-proved
`meanGrad D hst`. -/
theorem respJetGrad_of_act (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hm : D.ActJetMeas) (ha : D.ActGrad) : D.RespJetGrad := by
  obtain ⟨C1, k1, ha'⟩ := ha
  obtain ⟨C2, k2, hmn'⟩ := meanGrad D hst
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C := max (max C1 C2) 0
  set k := max k1 k2
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨2 * C, k, ?_⟩
  filter_upwards [hm, ha', hmn', hle1] with n hm_n ha_n hmn_n hle1_n z hz
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν1 : (D.level n).ν ≤ 1 := hle1_n.1
  have hF0 : 0 ≤ (D.level n).ε ^ (57 / 22 : ℝ) := by positivity
  have ha_z : ActGradAt D.Pl D.K (D.level n) (D.mu n z) C k := fun T =>
    ⟨(ha_n z hz T).1, bound_mono hν hν1 hF0
      ((le_max_left C1 C2).trans (le_max_left _ _)) hC0 (le_max_left k1 k2) (ha_n z hz T).2⟩
  have hmn_z : MeanGradAt D.Pl D.K (D.level n) (D.mu n z) C k := fun T =>
    ⟨(hmn_n z hz T).1, bound_mono hν hν1 hF0
      ((le_max_right C1 C2).trans (le_max_left _ _)) hC0 (le_max_right k1 k2) (hmn_n z hz T).2⟩
  exact respJetGradAt_of D.Pl D.K (D.level n) (D.mu n z) hC0 (hm_n z hz) ha_z hmn_z

/-- **Sequence-level assembly of `D.BackgroundSplit`** from `D.RepairStanding` (which proves the
localized part via `bgLocal_eventually`) and the remainder bounds `D.PresFlat`, `D.CoefChg`, and
`D.RespJetGrad`. -/
theorem backgroundSplit_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.PresFlat) (h2 : D.CoefChg) (h3 : D.RespJetGrad) : D.BackgroundSplit := by
  obtain ⟨Cl, kl, _, hloc⟩ := bgLocal_eventually D hst
  obtain ⟨C1, k1, h1'⟩ := h1
  obtain ⟨C2, k2, h2'⟩ := h2
  obtain ⟨C3, k3, h3'⟩ := h3
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C := max (max (max C1 C2) C3) 0
  set k := max (max k1 k2) k3
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨4 * Cl ^ 2 + (16 + C) * C ^ 2, max (2 * kl + 4) (3 * k), ?_⟩
  filter_upwards [hloc, h1', h2', h3', hle1] with n hloc_n h1_n h2_n h3_n hle1_n z hz
  set L := D.level n
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hν1 : L.ν ≤ 1 := hle1_n.1
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hρ0 : 0 ≤ rhoRep D.K L := rhoRep_nonneg D.K L
  have hmono : ∀ (Ca : ℝ) (ka : ℕ), Ca ≤ C → ka ≤ k → Ca * L.ν⁻¹ ^ ka ≤ C * L.ν⁻¹ ^ k := by
    intro Ca ka hCa hka
    calc Ca * L.ν⁻¹ ^ ka ≤ C * L.ν⁻¹ ^ ka :=
          mul_le_mul_of_nonneg_right hCa (by positivity)
      _ ≤ C * L.ν⁻¹ ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hνinv1 hka) hC0
  have h1_m : PresFlatAt D.K L C k := by
    refine ⟨h1_n.1, h1_n.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_right
      (hmono C1 k1 (((le_max_left C1 C2).trans (le_max_left _ _)).trans (le_max_left _ _))
        ((le_max_left k1 k2).trans (le_max_left _ _))) hρ0
  have h2_m : CoefChgAt D.Pl D.K L C k := by
    refine ⟨h2_n.1, h2_n.2.1.trans (ENNReal.ofReal_le_ofReal ?_), fun p hp =>
      (h2_n.2.2 p hp).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (hmono C2 k2 (((le_max_right C1 C2).trans (le_max_left _ _)).trans (le_max_left _ _))
          ((le_max_right k1 k2).trans (le_max_left _ _))) hρ0
    · exact hmono C2 k2 (((le_max_right C1 C2).trans (le_max_left _ _)).trans (le_max_left _ _))
        ((le_max_right k1 k2).trans (le_max_left _ _))
  have h3_m : RespJetGradAt D.Pl D.K L (D.mu n z) C k := fun T => by
    refine ⟨(h3_n z hz T).1, ?_⟩
    exact bound_mono hν hν1 (by positivity)
      ((le_max_right _ C3).trans (le_max_left _ _)) hC0 (le_max_right _ k3) (h3_n z hz T).2
  exact backgroundSplitAt_of D.Pl D.K L (D.mu n z) hC0 hν1 hloc_n.1 hloc_n.2 h1_m h2_m h3_m

/-- **Sequence-level assembly of `D.BackgroundSplit` from the finest remaining leaves**
(`D.PresFlat`, `D.RhoW1`, `D.ActJetMeas`, `D.ActGrad`), plugging in all already-proved theorems
(`bgLocal_eventually`, `coefChg_of_rhoW1`, `meanGrad`). -/
theorem backgroundSplit_of_leaves (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.PresFlat) (h2 : D.RhoW1) (hm : D.ActJetMeas) (ha : D.ActGrad) :
    D.BackgroundSplit :=
  backgroundSplit_of D hst h1 (coefChg_of_rhoW1 D hst h2) (respJetGrad_of_act D hst hm ha)

/-- **Sequence-level assembly of `D.BackgroundSplit` from `D.PresFlat`, `D.RhoW1`, and `D.ActGrad`**
(with `D.ActJetMeas` discharged by `actJetMeas D hst`). -/
theorem backgroundSplit_of_actGrad (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.PresFlat) (h2 : D.RhoW1) (ha : D.ActGrad) :
    D.BackgroundSplit :=
  backgroundSplit_of_leaves D hst h1 h2 (actJetMeas D hst) ha

end UnforcedLeray.Short.PartIIIb.Concrete
