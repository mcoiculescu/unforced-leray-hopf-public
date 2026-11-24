import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.CurlDuality
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2

/-!
# `PartIII-a:T19/2/3/2/2`: `coreSourceNegBound` (SP 3456-3480)

The `Z^{-1}_{9,c}` bound of the source functional `coreSrcFun`, by the same Cauchy-Schwarz and
weight split as `negNorm_le_of_advStretch_pairing`, using clause 1 of `CDualClause`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CurlDualityAux

lemma coreSrc_cs (a0 a1 g0 g1 : ℂ) :
    ‖a1 * g0 - a0 * g1‖ ≤ vnorm2 ![a0, a1] * vnorm2 ![g0, g1] := by
  have hx : ‖a1 * g0 - a0 * g1‖ ≤ ‖a1‖ * ‖g0‖ + ‖a0‖ * ‖g1‖ := by
    calc ‖a1 * g0 - a0 * g1‖ ≤ ‖a1 * g0‖ + ‖a0 * g1‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have hsq : (‖a1‖ * ‖g0‖ + ‖a0‖ * ‖g1‖) ^ 2 ≤
      (‖a0‖ ^ 2 + ‖a1‖ ^ 2) * (‖g0‖ ^ 2 + ‖g1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a0‖ * ‖g0‖ - ‖a1‖ * ‖g1‖)]
  have hv : ∀ p q : ℂ, vnorm2 ![p, q] = Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    intro p q
    simp [vnorm2, Fin.sum_univ_two]
  rw [hv, hv, ← Real.sqrt_mul (by positivity)]
  refine hx.trans (Real.le_sqrt_of_sq_le hsq)

lemma coreSrc_pair_le (c : ℝ) (v : ℝ × ℝ → Fin 2 → ℝ) (u : ℝ × ℝ → Fin 2 → ℂ)
    (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    ENNReal.ofReal ‖coreSrcFun c (advStretch v u G) g‖ ≤
      ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) := by
  unfold coreSrcFun
  rw [ofReal_norm_eq_enorm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono fun x => ?_
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal ?_
  have := coreSrc_cs (advStretch v u G x 0) (advStretch v u G x 1) (g 0 x) (g 1 x)
  have e1 : (![advStretch v u G x 0, advStretch v u G x 1] : Fin 2 → ℂ) = advStretch v u G x := by
    ext i; fin_cases i <;> rfl
  have e2 : (![g 0 x, g 1 x] : Fin 2 → ℂ) = fun j => g j x := by
    ext i; fin_cases i <;> rfl
  rwa [e1, e2] at this

theorem coreSrcNorm_le_aux {c A_m C : ℝ} (hc : 0 < c) (hAm : 0 ≤ A_m)
    {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun x => u x i) (hG : ∀ i j, Measurable fun x => G x i j)
    (h1 : (∫⁻ x in B0579.cell c,
            ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
          (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * A_m) *
            ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
              (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ))) :
    coreSrcNorm c 9 (advStretch v u G) ≤
      ENNReal.ofReal (C * A_m) *
        ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) := by
  unfold coreSrcNorm
  refine iSup₂_le fun φ g => iSup₂_le fun hg hh1 => ?_
  set F₁ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x))
  set F₂ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (B0579.bracket x ^ (-9 : ℝ) * vnorm2 (fun j => g j x))
  have hF₁ : AEMeasurable F₁ (volume.restrict (B0579.cell c)) := by
    have hm_br : Measurable fun x : ℝ × ℝ => B0579.bracket x ^ (9 : ℝ) :=
      ((B0579.continuous_jb.sqrt).rpow_const (fun _ => Or.inr (by norm_num))).measurable
    have hm_adv : Measurable fun x : ℝ × ℝ => vnorm2 (advStretch v u G x) :=
      causalLin_measurable_vnorm2 (measurable_advStretch hv hu hG)
    exact (hm_br.mul hm_adv).ennreal_ofReal.aemeasurable
  have hgm : ∀ j : Fin 2, AEStronglyMeasurable (g j) (volume.restrict (B0579.cell c)) :=
    fun j => aestronglyMeasurable_of_hasWeakCellDerivC (hg j)
  have hF₂ : AEMeasurable F₂ (volume.restrict (B0579.cell c)) := by
    have hm_br : AEMeasurable (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ))
        (volume.restrict (B0579.cell c)) := by
      have heq : (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ)) =
          fun x => B0579.jb x ^ (-9 / 2 : ℝ) := funext (B0579.bracket_rpow (-9))
      rw [heq]
      exact (B0579.continuous_jb_rpow (-9 / 2)).measurable.aemeasurable
    have hm_g : AEMeasurable (fun x : ℝ × ℝ => vnorm2 (fun j => g j x))
        (volume.restrict (B0579.cell c)) := by
      unfold vnorm2
      refine Real.continuous_sqrt.measurable.comp_aemeasurable ?_
      rw [show (fun x : ℝ × ℝ => ∑ i : Fin 2, ‖g i x‖ ^ 2) =
          fun x => ‖g 0 x‖ ^ 2 + ‖g 1 x‖ ^ 2 from funext fun _ => Fin.sum_univ_two _]
      exact (((hgm 0).norm.aemeasurable.pow_const 2).add ((hgm 1).norm.aemeasurable.pow_const 2))
    exact (hm_br.mul hm_g).ennreal_ofReal
  have hprod_eq : ∀ x,
      ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) = F₁ x * F₂ x := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr_mul : B0579.bracket x ^ (9 : ℝ) * B0579.bracket x ^ (-9 : ℝ) = 1 := by
      rw [← Real.rpow_add hbr_pos, add_neg_cancel, Real.rpow_zero]
    dsimp [F₁, F₂]
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _))]
    congr 1
    calc vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)
        = (B0579.bracket x ^ (9 : ℝ) * B0579.bracket x ^ (-9 : ℝ)) *
            (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) := by
          rw [hbr_mul, one_mul]
      _ = B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) *
            (B0579.bracket x ^ (-9 : ℝ) * vnorm2 (fun j => g j x)) := by ring
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (B0579.cell c))
    Real.HolderConjugate.two_two hF₁ hF₂
  have hF₁_sq : ∀ x, F₁ x ^ (2 : ℝ) =
      ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2) := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr18 : B0579.bracket x ^ (18 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (B0579.bracket x ^ (9 : ℝ)) 2, ← Real.rpow_mul hbr_pos.le]
      norm_num
    dsimp [F₁]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)),
      mul_pow, hbr18]
  have hF₂_sq : ∀ x, F₂ x ^ (2 : ℝ) =
      ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 0 x‖ ^ 2) +
        ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 1 x‖ ^ 2) := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr_neg18 : (B0579.bracket x ^ (-9 : ℝ)) ^ 2 = B0579.jb x ^ (-9 : ℝ) := by
      rw [B0579.bracket_rpow (-9), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (B0579.jb_pos x).le]
      congr 1
      norm_num
    have hv_sq : vnorm2 (fun j => g j x) ^ 2 = ‖g 0 x‖ ^ 2 + ‖g 1 x‖ ^ 2 := by
      unfold vnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_two]
    dsimp [F₂]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)),
      mul_pow, hbr_neg18, hv_sq, mul_add,
      ENNReal.ofReal_add
        (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
        (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))]
  have hF₂_int : (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
    have hm0 : AEMeasurable
        (fun x : ℝ × ℝ => ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 0 x‖ ^ 2))
        (volume.restrict (B0579.cell c)) :=
      ((B0579.continuous_jb_rpow (-9)).measurable.aemeasurable.mul
        ((hgm 0).norm.aemeasurable.pow_const 2)).ennreal_ofReal
    have hint_eq : ∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ) =
        ∑ j : Fin 2, xNorm c (-9) (g j) ^ 2 := by
      simp_rw [hF₂_sq]
      rw [lintegral_add_left' hm0, ← xNorm_neg_nine_sq_eq c (g 0),
        ← xNorm_neg_nine_sq_eq c (g 1), Fin.sum_univ_two]
    rw [hint_eq]
    calc (∑ j : Fin 2, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ)
        ≤ (xNorm c (-9) φ ^ 2 + ∑ j : Fin 2, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_add_self (by norm_num)
      _ = h1Norm c 9 φ g := rfl
      _ ≤ 1 := hh1
  calc ENNReal.ofReal ‖coreSrcFun c (advStretch v u G) g‖
      ≤ ∫⁻ x in B0579.cell c,
          ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) :=
        coreSrc_pair_le c v u G g
    _ = ∫⁻ x in B0579.cell c, (F₁ * F₂) x := lintegral_congr hprod_eq
    _ ≤ (∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hCS
    _ ≤ (∫⁻ x in B0579.cell c,
          ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) * 1 := by
        simp_rw [hF₁_sq]
        exact mul_le_mul_of_nonneg_left hF₂_int bot_le
    _ = (∫⁻ x in B0579.cell c,
          ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) := mul_one _
    _ ≤ _ := h1

/-- The coordinate map of the Euclidean plane vector. -/
abbrev evE : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)

lemma norm_evE_le (y : EuclideanSpace ℝ (Fin 2)) : ‖evE y‖ ≤ ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact PiLp.norm_apply_le y i

lemma trainVel_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {t : ℝ} (ht : 0 < t) :
    trainVel tr t = fun x => evE (tr.v t x) := by
  funext x i; simp [trainVel, ht.le, evE]

/-- `tr.v t` is `C¹` for `t > 0`. -/
lemma contDiff_trainV {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 1 (tr.v t) := by
  have h := tr.isTrain.smooth_v.of_le (m := 1) (by exact_mod_cast le_top)
  have hg : ContDiff ℝ 1 (fun x : ℝ × ℝ => ((t, x) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have := h.comp hg.contDiffOn (s := univ) (fun x _ => ⟨ht.le, trivial⟩)
  exact contDiffOn_univ.1 this

lemma contDiff_trainVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 1 (trainVel tr t) := by
  rw [trainVel_eq tr ht]
  exact evE.contDiff.comp (contDiff_trainV tr ht)

theorem coreSourceNegBound : UnforcedLeray.Short.IIIa.CoreSourceNegBound := by
  intro C_dual hC0 hdual P hP K hK b hb ν hν tr μ A_m F b₀ G₀ b_sol G_sol hd
  obtain ⟨hbuc, hμ, hAm, hbd, hsym, hmeas, htc, hfree, hsol⟩ := hd
  refine Filter.Eventually.of_forall fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hv := contDiff_trainVel tr ht0
  have hvb : ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)), B0579.bracket x ^ (9 : ℝ) *
      (‖trainVel tr t x‖ + ‖fderiv ℝ (trainVel tr t) x‖) ≤ A_m := by
    intro x hx
    have hb := hbd t ⟨ht0, ht.2.le⟩ x hx
    have hdf : DifferentiableAt ℝ (tr.v t) x :=
      ((contDiff_trainV tr ht0).differentiable (by norm_num)) x
    have hfd : fderiv ℝ (trainVel tr t) x =
        (evE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ)).comp (fderiv ℝ (tr.v t) x) := by
      rw [trainVel_eq tr ht0]
      exact evE.comp_fderiv (f := tr.v t) (x := x)
    have hop : ‖(evE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ)).comp (fderiv ℝ (tr.v t) x)‖
        ≤ ‖fderiv ℝ (tr.v t) x‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
      calc ‖(evE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ)) (fderiv ℝ (tr.v t) x y)‖
          ≤ ‖fderiv ℝ (tr.v t) x y‖ := norm_evE_le _
        _ ≤ ‖fderiv ℝ (tr.v t) x‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    have hn : ‖trainVel tr t x‖ ≤ ‖tr.v t x‖ := by
      rw [trainVel_eq tr ht0]; exact norm_evE_le _
    rw [hfd]
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hn hop) (Real.rpow_nonneg
      (Real.sqrt_nonneg _) _)) hb
  have hu : ∀ i, Measurable fun x : ℝ × ℝ => gainConj P.eigenvalue.re ν b₀ (t, x) i := by
    intro i
    simp only [gainConj, Pi.smul_apply]
    exact ((hfree.measurable i).comp measurable_prodMk_left).const_smul _
  have hG : ∀ i j, Measurable fun x : ℝ × ℝ => gainConj P.eigenvalue.re ν G₀ (t, x) i j := by
    intro i j
    simp only [gainConj, Pi.smul_apply]
    exact ((hfree.gradMeasurable i j).comp measurable_prodMk_left).const_smul _
  have h1 := (hdual (ν ^ (-2 : ℝ)) A_m hc hAm (trainVel tr t) hv hvb
    (fun x => gainConj P.eigenvalue.re ν b₀ (t, x))
    (fun x => gainConj P.eigenvalue.re ν G₀ (t, x)) hu hG).1
  exact coreSrcNorm_le_aux hc hAm hv hu hG h1

end UnforcedLeray.Short.IIIa

end
