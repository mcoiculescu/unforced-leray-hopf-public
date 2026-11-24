import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.BasicReg
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Transfer
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_9

/-!
# `PartIII-a:T21/2/2/3/5/3/2`: integrability of the rescaled cross term (SP 3044-3047, 3060-3073)

Source of record: `the November 2 reference manuscript` (SP) lines 3044-3047 and
3060-3073. On the moving cell `C_d`, `d = c/√a` with `a = clockA ν (revAge ν s ζ)`, the function
`w Re(conj ∂_kΦ · ψ_k)` is integrable, where `ψ_k = psiK`:
* `w|∂_kΦ|²` is integrable (`MovRegLow.int1`, from `movAdjBasicReg`);
* `w|ψ_k|² = (a√a)² · w|∂_k∂_rφ(√a ·)|²` is integrable by `transfer_weight_int`, using the
  `X_{-m,c}` membership of `∂_k∂_rφ` (`IsAdjointFlow.higherCont`);
* `|w Re(conj u · v)| ≤ w(|u|² + |v|²)`, and the integrand is continuous (joint smoothness of
  `∂_k∂_rφ` on the open strip, `continuousOn_adjSpatial`), so `intOn_of_abs_le` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem e1PsiInt (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjE1.E1PsiInt m := by
  intro ν tr t s φ ζ hζ k
  have hreg : MovRegLow m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvPhi ν φ s ζ) :=
    movAdjBasicReg m hm ν tr t s φ ζ hζ
  obtain ⟨hr, ha⟩ := adjFlowAt_age hζ
  obtain ⟨G, _, hF⟩ := hζ.2.2.2.1
  have hν : 0 < ν := hζ.1
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hm0 : 0 ≤ m := by linarith
  have hsq : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.2 ha
  have hr' : revAge ν s ζ ∈ Ico t s := Ioo_subset_Ico_self hr
  have hmv : mvLen ν (ν ^ (-2 : ℝ)) s ζ =
      (ν ^ (-2 : ℝ)) / Real.sqrt (clockA ν (revAge ν s ζ)) := rfl
  -- `∂_k∂_rφ(r, ·)` lies in `X_{-m,c}` (`higherCont`, `w = [k]`)
  have hg : MemLp (pdCx k (adjDt t s φ (revAge ν s ζ))) 2
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    ((hF.higherCont _ hr' [k]).2 (by simp)).1
  -- joint continuity of `∂_k∂_rφ` on the strip, restricted to the slice at the age `r`
  have hj : ContDiffOn ℝ ∞ (jF φ) (Ioo t s ×ˢ univ) :=
    hF.jointSmooth.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
  have hcont := continuousOn_adjSpatial hj [k] (by simp)
  have hx : Continuous (fun x : ℝ × ℝ => pdCx k (adjDt t s φ (revAge ν s ζ)) x) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hat : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => adjSpatial [k] (adjDt t s φ p.1) p.2)
        (revAge ν s ζ, x) :=
      hcont.continuousAt (IsOpen.mem_nhds (isOpen_strip t s) ⟨hr, mem_univ x⟩)
    exact hat.comp (f := fun x : ℝ × ℝ => ((revAge ν s ζ, x) : ℝ × (ℝ × ℝ)))
      (continuous_const.prodMk continuous_id).continuousAt
  have hgc : Continuous (fun y : ℝ × ℝ =>
      pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)) :=
    hx.comp (continuous_const_smul _)
  have hpsic : Continuous (fun y : ℝ × ℝ => psiK ν t s φ ζ k y) := by
    unfold psiK
    exact (continuous_const.neg).mul hgc
  have hu : Continuous (fun y : ℝ × ℝ => pdCx k (mvPhi ν φ s ζ) y) :=
    pdCx_cont hreg.smooth k
  -- (i) `w|∂_kΦ|²` is integrable on the moving cell
  have hA : IntegrableOn (fun y : ℝ × ℝ => periodicWeight (-m) (ν ^ (-2 : ℝ) /
      Real.sqrt (clockA ν (revAge ν s ζ))) y * ‖pdCx k (mvPhi ν φ s ζ) y‖ ^ 2)
      (B0579.cell (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν (revAge ν s ζ)))) := hreg.int1 k
  -- (ii) `w|ψ_k|²` is integrable on the moving cell, by transfer of `∂_k∂_rφ ∈ X_{-m,c}`
  have hpsi_norm : ∀ y : ℝ × ℝ, ‖psiK ν t s φ ζ k y‖ ^ 2 =
      (clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ))) ^ 2 *
        ‖pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)‖ ^ 2 := by
    intro y
    unfold psiK
    rw [neg_mul, norm_neg]
    exact norm_sq_real_const_mul _ _
  have hB : IntegrableOn (fun y : ℝ × ℝ => periodicWeight (-m) (ν ^ (-2 : ℝ) /
      Real.sqrt (clockA ν (revAge ν s ζ))) y * ‖psiK ν t s φ ζ k y‖ ^ 2)
      (B0579.cell (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν (revAge ν s ζ)))) := by
    have h := (transfer_weight_int m (ν ^ (-2 : ℝ)) (Real.sqrt (clockA ν (revAge ν s ζ)))
      hm0 hc hsq _ hg).const_mul
      ((clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ))) ^ 2)
    refine IntegrableOn.congr_fun h (fun y _ => ?_) (B0579.measurableSet_cell _)
    rw [hpsi_norm y]
    ring
  -- the cross term: continuous and dominated by `w(|∂_kΦ|² + |ψ_k|²)`
  have hw : Continuous (fun y : ℝ × ℝ => periodicWeight (-m) (ν ^ (-2 : ℝ) /
      Real.sqrt (clockA ν (revAge ν s ζ))) y) := (pw_contDiff _ _).continuous
  have hf : Continuous (fun y : ℝ × ℝ => periodicWeight (-m) (ν ^ (-2 : ℝ) /
      Real.sqrt (clockA ν (revAge ν s ζ))) y *
      ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re) :=
    hw.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hu).mul hpsic))
  rw [hmv]
  refine intOn_of_abs_le (B0579.measurableSet_cell _) (hA.add hB) hf ?_
  intro y _
  have hw0 : 0 < periodicWeight (-m) (ν ^ (-2 : ℝ) /
      Real.sqrt (clockA ν (revAge ν s ζ))) y := pw_pos _ _ y
  have h1 := abs_re_conj_le (pdCx k (mvPhi ν φ s ζ) y) (psiK ν t s φ ζ k y)
  have h2 : ‖pdCx k (mvPhi ν φ s ζ) y‖ * ‖psiK ν t s φ ζ k y‖ ≤
      ‖pdCx k (mvPhi ν φ s ζ) y‖ ^ 2 + ‖psiK ν t s φ ζ k y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖pdCx k (mvPhi ν φ s ζ) y‖ - ‖psiK ν t s φ ζ k y‖),
      sq_nonneg ‖pdCx k (mvPhi ν φ s ζ) y‖, sq_nonneg ‖psiK ν t s φ ζ k y‖]
  calc |periodicWeight (-m) (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν (revAge ν s ζ))) y *
        ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re|
      = periodicWeight (-m) (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν (revAge ν s ζ))) y *
        |((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re| := by
        rw [abs_mul, abs_of_pos hw0]
    _ ≤ periodicWeight (-m) (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν (revAge ν s ζ))) y *
        (‖pdCx k (mvPhi ν φ s ζ) y‖ ^ 2 + ‖psiK ν t s φ ζ k y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hw0.le
    _ = periodicWeight (-m) (ν ^ (-2 : ℝ) / Real.sqrt (clockA ν (revAge ν s ζ))) y *
          ‖pdCx k (mvPhi ν φ s ζ) y‖ ^ 2 + periodicWeight (-m) (ν ^ (-2 : ℝ) /
          Real.sqrt (clockA ν (revAge ν s ζ))) y * ‖psiK ν t s φ ζ k y‖ ^ 2 := by ring

end UnforcedLeray.Short.IIIa.AdjE1
