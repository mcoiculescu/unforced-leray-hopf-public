import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf3.Dual
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf3.Kernel
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1a
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1b
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1c
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.Pullback
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_3
import UnforcedLeray.Units.B0610

/-!
# Leaf (c) of `PartIII-a:T21/c3/3/1/1`: the interaction bound from the adjoint localized bound

Source `the November 2 reference manuscript` lines 2863-2865 (the interaction
`-(K_d W)·∇E_mov` of the moving operator), 2953-2958 (the adjoint localized bound gives
`‖(K_d W)·∇E_mov‖_{X_{m,d}} ≤ C_loc ‖W‖_{X_{m,d}}`).

Fix an age `r` and `W ∈ X_{m,d}` (WLOG strongly measurable: `kerVelCx` only sees `W` a.e. on the
cell).  For a bounded measurable `Φ` vanishing for `|η|` large, put `G_k = Φ ∂_kE_mov`:
* Fubini (`fubini_ker`): `∫ L_int(W) Φ = -∫ W · K_dᵀG`;
* `K_dᵀG = χ` a.e. (`cellUnique`), where `χ` is the adjoint of `LocalizedHyp`: both are
  band-integrable and pair equally with every cylinder test `ψ`, since `K_dψ` is the kernel
  Biot-Savart velocity of `ψ` (`kerVelFarField0`, `kerVelDivFree0`, `kerVelCurl0`) and
  `∫ K_dᵀG ψ = ∫ G · K_dψ` (`kerAdjFubini0`);
* weighted Hölder: `|∫ W χ| ≤ ‖W‖_{X_m} ‖χ‖_{X_{-m}} ≤ C_loc ‖W‖_{X_m} ‖Φ‖_{X_{-m}}`.
Duality against such `Φ` (`xNorm_le_of_pairing`) gives the bound; measurability is from
`stronglyMeasurable_kerVelCx`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

open UnforcedLeray.Short.IIIa

namespace Leaf3Aux

theorem dd_pos {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 < dd ν r := by
  show 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  unfold cellLen
  have ha : 0 < clockA ν r := by
    unfold clockA
    have := mul_nonneg hν.le hr
    linarith
  exact div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha)

/-- **The pairing bound at a fixed age**: `|∫ L_int(W) Φ| ≤ C ‖W‖_{X_m} ‖Φ‖_{X_{-m}}` for
bounded measurable `Φ` vanishing for `|η| > R` (SP 2953-2958). -/
theorem pairing_bound {ν m C : ℝ} (hm : 8 < m) (hν : 0 < ν) (hC : 0 ≤ C)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {r : ℝ} (hr : 0 ≤ r)
    (hLoc : ∀ Φ : ℝ × ℝ → ℂ, MemLp Φ 2 (B0579.cellMeasure (dd ν r) (-m)) →
      ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC (dd ν r) j χ (gχ j)) ∧
        h1Norm (dd ν r) m χ gχ ≤ ENNReal.ofReal C * xNorm (dd ν r) (-m) Φ ∧
        xNorm (dd ν r) (-m) χ ≤ ENNReal.ofReal C * xNorm (dd ν r) (-m) Φ ∧
        ∀ ψ uψ, B0579.IsCylTest (dd ν r) ψ → IsKernelBiotSavart (dd ν r) ψ uψ →
          ∫ y in B0579.cell (dd ν r), χ y * (ψ y : ℂ) =
            ∫ y in B0579.cell (dd ν r),
              Φ y * ((uψ y 0 * B0579.pd 0 (movingTrainE tr r) y +
                uψ y 1 * B0579.pd 1 (movingTrainE tr r) y : ℝ) : ℂ))
    {W : ℝ × ℝ → ℂ} (hW : MemLp W 2 (B0579.cellMeasure (dd ν r) m))
    (Φ : ℝ × ℝ → ℂ) (hΦs : StronglyMeasurable Φ) (B R : ℝ) (hB : ∀ y, ‖Φ y‖ ≤ B)
    (hR : ∀ y, R < |y.2| → Φ y = 0) :
    ‖∫ y in B0579.cell (dd ν r), interactionTerm tr r W y * Φ y‖ ≤
      C * (xNorm (dd ν r) m W).toReal * (xNorm (dd ν r) (-m) Φ).toReal := by
  set d := dd ν r with hd_def
  have hd : 0 < d := dd_pos hν hr
  have hm' : 1 / 2 < m := by linarith
  set gE : Fin 2 → ℝ × ℝ → ℝ := fun k y => movingTrainGradE tr r y k with hgE
  have hgEc : ∀ k, Continuous (gE k) := fun k =>
    EulerErrorSub.continuous_movingTrainGradE tr hr k
  -- the cutoff and the bounds
  obtain ⟨ψ₀, hψ₀, hψ₀nn, hψ₀one⟩ := exists_band_cutoff d R
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨Mg, hMg⟩ := (B0579.isCompact_box d R).exists_bound_of_continuousOn
    (f := fun y => ‖gE 0 y‖ + ‖gE 1 y‖)
    (((hgEc 0).norm.add (hgEc 1).norm).continuousOn)
  set Mg' := max Mg 0 with hMg'
  have hgEb : ∀ k, ∀ y ∈ B0579.box d R, ‖gE k y‖ ≤ Mg' := by
    intro k y hy
    have h := hMg y hy
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at h
    have h0 : ‖gE 0 y‖ ≤ Mg := by linarith [norm_nonneg (gE 1 y)]
    have h1 : ‖gE 1 y‖ ≤ Mg := by linarith [norm_nonneg (gE 0 y)]
    refine le_trans ?_ (le_max_left _ _)
    match k with
    | 0 => exact h0
    | 1 => exact h1
  set M := B * Mg' with hM
  have hM0 : 0 ≤ M := mul_nonneg hB0 (le_max_right _ _)
  set G : Fin 2 → ℝ × ℝ → ℂ := fun k y => Φ y * ((gE k y : ℝ) : ℂ) with hG
  have hGs : ∀ k, StronglyMeasurable (G k) := fun k =>
    hΦs.mul (Complex.continuous_ofReal.comp (hgEc k)).stronglyMeasurable
  have hGb : ∀ k, ∀ x ∈ B0579.cell d, ‖G k x‖ ≤ M * |ψ₀ x| := by
    intro k x hx
    by_cases hx2 : |x.2| ≤ R
    · rw [hψ₀one x hx2, abs_one, mul_one, hG]
      dsimp only
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hB x) (hgEb k x (B0579.mem_box_of_mem_cell hx hx2)) (norm_nonneg _) hB0
    · rw [hG]
      dsimp only
      rw [hR x (lt_of_not_ge hx2), zero_mul, norm_zero]
      exact mul_nonneg hM0 (abs_nonneg _)
  -- `Φ ∈ X_{-m}`
  obtain ⟨Bψ, -, hBψ, -⟩ := AdjFubiniAux.test_facts hd hψ₀
  have hΦL2 : MemLp Φ 2 (B0579.cellMeasure d (-m)) := by
    have hg : MemLp (fun y => B * ψ₀ y) 2 (B0579.cellMeasure d (-m)) :=
      (B0610.memLp_neg_of_bounded hm' hψ₀.continuous hBψ).const_mul B
    refine hg.of_le hΦs.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    by_cases hy : |y.2| ≤ R
    · rw [hψ₀one y hy, mul_one, Real.norm_of_nonneg hB0]
      exact hB y
    · rw [hR y (lt_of_not_ge hy), norm_zero]
      exact norm_nonneg _
  have hΦfin : xNorm d (-m) Φ ≠ ⊤ := hΦL2.eLpNorm_ne_top
  -- the adjoint `χ`
  obtain ⟨χ, gχ, hweak, hh1, hχx, hpairχ⟩ := hLoc Φ hΦL2
  have hh1ne : h1Norm d m χ gχ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦfin) hh1
  have hband := weakFieldBandInt m d χ gχ hd hweak hh1ne
  have hχband : ∀ R' : ℝ, IntegrableOn χ (AdjE1.bandSet d R') := fun R' => (hband R').1
  have hχm : AEStronglyMeasurable χ (volume.restrict (B0579.cell d)) := by
    have hU : (⋃ n : ℕ, AdjE1.bandSet d n) = B0579.cell d := by
      ext x
      simp only [mem_iUnion, AdjE1.bandSet, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨n, hx, -⟩
        exact hx
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge |x.2|
        exact ⟨n, hx, hn⟩
    rw [← hU]
    exact aestronglyMeasurable_iUnion_iff.2 fun n => (hχband n).aestronglyMeasurable
  have hχfin : xNorm d (-m) χ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦfin) hχx
  have hχL2 : MemLp χ 2 (B0579.cellMeasure d (-m)) :=
    ⟨hχm.mono_ac (B0579.cellMeasure_ac d (-m)), hχfin.lt_top⟩
  -- integrability of `G` and the band-integrability of `K_dᵀG`
  obtain ⟨R₀, hR₀⟩ := hψ₀.band
  have hψ₀int : IntegrableOn ψ₀ (B0579.cell d) :=
    B0579.integrableOn_cell_of_continuous hψ₀.continuous (B0579.isCompact_box d R₀)
      (fun x hx hxK => hR₀ x (lt_of_not_ge fun h => hxK (B0579.mem_box_of_mem_cell hx h)))
  have hGint : ∀ k, IntegrableOn (G k) (B0579.cell d) := by
    intro k
    refine Integrable.mono' (hψ₀int.abs.const_mul M) (hGs k).aestronglyMeasurable ?_
    exact (ae_restrict_iff' (B0579.measurableSet_cell d)).2
      (Eventually.of_forall fun x hx => hGb k x hx)
  have hkerAdj : ∀ z, kerAdj d G z =
      (∫ x in B0579.cell d, G 0 x * ((kerD d (x - z) 0 : ℝ) : ℂ)) +
        ∫ x in B0579.cell d, G 1 x * ((kerD d (x - z) 1 : ℝ) : ℂ) := by
    intro z
    unfold kerAdj
    simp only [Fin.sum_univ_two]
    exact integral_add
      (integrable_ker_left hd hM0 hψ₀ (hGs 0).aestronglyMeasurable (hGb 0) z 0)
      (integrable_ker_left hd hM0 hψ₀ (hGs 1).aestronglyMeasurable (hGb 1) z 1)
  have hAband : ∀ R' : ℝ, IntegrableOn (kerAdj d G) (AdjE1.bandSet d R') := by
    intro R'
    have hs : volume (AdjE1.bandSet d R') < ⊤ :=
      lt_of_le_of_lt (measure_mono fun x hx => B0579.mem_box_of_mem_cell hx.1 hx.2)
        (B0579.isCompact_box d R').measure_lt_top
    rw [show kerAdj d G = fun z => (∫ x in B0579.cell d, G 0 x * ((kerD d (x - z) 0 : ℝ) : ℂ)) +
        ∫ x in B0579.cell d, G 1 x * ((kerD d (x - z) 1 : ℝ) : ℂ) from funext hkerAdj]
    exact (integrableOn_kerInt hd hM0 hψ₀ (hGs 0) (hGb 0) 0 hs).add
      (integrableOn_kerInt hd hM0 hψ₀ (hGs 1) (hGb 1) 1 hs)
  -- `K_dᵀG = χ` a.e. on the cell
  have hann : ∀ ψ, B0579.IsCylTest d ψ →
      ∫ x in B0579.cell d, (kerAdj d G - χ) x * (ψ x : ℂ) = 0 := by
    intro ψ hψ
    obtain ⟨hAψint, hAψ⟩ := kerAdjFubini0 d hd G hGint ψ hψ
    have hχψint := bandMulTest d χ ψ hd hχband hψ
    rw [AdjE1.int_sub_mul d _ _ ψ hAψint hχψint, hAψ]
    have hBS : IsKernelBiotSavart d ψ (kerVel d ψ) :=
      ⟨fun j => AdjE1.kerVelFarField0 d hd ψ hψ j,
        fun φ hφ => AdjE1.kerVelDivFree0 d hd ψ hψ φ hφ,
        fun φ hφ => AdjE1.kerVelCurl0 d hd ψ hψ φ hφ⟩
    rw [hpairχ ψ (kerVel d ψ) hψ hBS, sub_eq_zero]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν hr, Fin.sum_univ_two,
      hG, hgE]
    push_cast
    ring
  have hAχ : kerAdj d G =ᵐ[volume.restrict (B0579.cell d)] χ := by
    have h0 := cellUnique d (kerAdj d G - χ) hd (fun R' => (hAband R').sub (hχband R')) hann
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  -- Fubini: `∫ L_int(W) Φ = -∫ W K_dᵀG`
  have hone : MemLp (fun _ : ℝ × ℝ => (1 : ℂ)) 2 (B0579.cellMeasure d (-m)) := by
    have := (B0610.memLp_one_neg (c := d) hm').ofReal (K := ℂ)
    simpa using this
  have hW1 : IntegrableOn W (B0579.cell d) := by
    have := (PairContAux.holder hW hone).1
    simpa using this
  have F0 := fubini_ker hd hM0 hψ₀ (hGs 0).aestronglyMeasurable (hGb 0) hW1 0
  have F1 := fubini_ker hd hM0 hψ₀ (hGs 1).aestronglyMeasurable (hGb 1) hW1 1
  have hfub : ∫ y in B0579.cell d, interactionTerm tr r W y * Φ y =
      -∫ z in B0579.cell d, W z * kerAdj d G z := by
    have e1 : (fun y => interactionTerm tr r W y * Φ y) = fun y =>
        -((G 0 y * ∫ z in B0579.cell d, W z * ((kerD d (y - z) 0 : ℝ) : ℂ)) +
          G 1 y * ∫ z in B0579.cell d, W z * ((kerD d (y - z) 1 : ℝ) : ℂ)) := by
      funext y
      simp only [interactionTerm, kerVelCx, hG, hgE]
      ring
    have e2 : (fun z => W z * kerAdj d G z) = fun z =>
        (W z * ∫ y in B0579.cell d, G 0 y * ((kerD d (y - z) 0 : ℝ) : ℂ)) +
          W z * ∫ y in B0579.cell d, G 1 y * ((kerD d (y - z) 1 : ℝ) : ℂ) := by
      funext z
      rw [hkerAdj z, mul_add]
    rw [e1, e2, integral_neg, integral_add F0.1 F1.1, integral_add F0.2.1 F1.2.1, F0.2.2, F1.2.2]
  have hWχ : ∫ z in B0579.cell d, W z * kerAdj d G z = ∫ z in B0579.cell d, W z * χ z :=
    integral_congr_ae (by filter_upwards [hAχ] with z hz; rw [hz])
  -- weighted Hölder
  have hhol := (PairContAux.holder hW hχL2).2
  have hχr : (xNorm d (-m) χ).toReal ≤ C * (xNorm d (-m) Φ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦfin) hχx
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at this
  rw [hfub, norm_neg, hWχ]
  calc ‖∫ z in B0579.cell d, W z * χ z‖
      ≤ (xNorm d m W).toReal * (xNorm d (-m) χ).toReal := hhol
    _ ≤ (xNorm d m W).toReal * (C * (xNorm d (-m) Φ).toReal) :=
        mul_le_mul_of_nonneg_left hχr ENNReal.toReal_nonneg
    _ = C * (xNorm d m W).toReal * (xNorm d (-m) Φ).toReal := by ring

end Leaf3Aux

/-- **Leaf (c)** (SP 2953-2958): the adjoint localized bound `LocalizedHyp` implies the interaction
bound `‖(K_d W)·∇E_mov‖_{X_{m,d}} ≤ C_loc ‖W‖_{X_{m,d}}` on all of `X_{m,d}`. -/
theorem locInteractionBound (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ C_loc : ℝ) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.LocInteractionBound ν m tr t₁ t₂ C_loc := by
  intro hm hν ht₁ _h12 hC hLoc r hr W hW
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  set d := dd ν r with hd_def
  -- a strongly measurable representative of `W`
  set W' := hW.1.mk W with hW'
  have hW's : StronglyMeasurable W' := hW.1.stronglyMeasurable_mk
  have hae : W =ᵐ[B0579.cellMeasure d m] W' := hW.1.ae_eq_mk
  have haev : W =ᵐ[volume.restrict (B0579.cell d)] W' :=
    (B0579.ac_cellMeasure d m).ae_le hae
  have hIT : interactionTerm tr r W = interactionTerm tr r W' := by
    funext y
    have hk : ∀ k, kerVelCx (dd ν r) W y k = kerVelCx (dd ν r) W' y k := fun k =>
      integral_congr_ae (by filter_upwards [haev] with z hz; rw [hz])
    simp only [interactionTerm, hk]
  have hxW : xNorm d m W = xNorm d m W' := eLpNorm_congr_ae hae
  have hW'L : MemLp W' 2 (B0579.cellMeasure d m) := hW.ae_eq hae
  rw [hIT, hxW]
  have hFs : StronglyMeasurable (interactionTerm tr r W') := by
    have h0 := EulerErrorSub.stronglyMeasurable_kerVelCx (dd ν r) hW's 0
    have h1 := EulerErrorSub.stronglyMeasurable_kerVelCx (dd ν r) hW's 1
    have g0 : StronglyMeasurable (fun y => ((movingTrainGradE tr r y 0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (EulerErrorSub.continuous_movingTrainGradE tr hr0 0)).stronglyMeasurable
    have g1 : StronglyMeasurable (fun y => ((movingTrainGradE tr r y 1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (EulerErrorSub.continuous_movingTrainGradE tr hr0 1)).stronglyMeasurable
    exact ((h0.mul g0).add (h1.mul g1)).neg
  refine ⟨hFs.aestronglyMeasurable, ?_⟩
  have hfin : xNorm d m W' ≠ ⊤ := hW'L.eLpNorm_ne_top
  have hA0 : 0 ≤ C_loc * (xNorm d m W').toReal := mul_nonneg hC ENNReal.toReal_nonneg
  have hmain := Leaf3Aux.xNorm_le_of_pairing (d := d) (m := m)
    (A := C_loc * (xNorm d m W').toReal) (by linarith) hA0 hFs
    (fun Φ hΦs B R hB hR =>
      Leaf3Aux.pairing_bound hm hν hC tr hr0 (fun Φ' hΦ' => hLoc r hr Φ' hΦ') hW'L Φ hΦs B R
        hB hR)
  rwa [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hfin] at hmain

end UnforcedLeray.Short.IIIa.ComplFreeRateSub

#print axioms UnforcedLeray.Short.IIIa.ComplFreeRateSub.locInteractionBound
