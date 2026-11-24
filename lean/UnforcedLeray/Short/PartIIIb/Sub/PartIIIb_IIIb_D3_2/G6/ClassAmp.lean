import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flat_1
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.FpmInvSubExp
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.FpmInvBound
import UnforcedLeray.Short.PartIIIb.Proofs.Flat.BclassAeBound

/-!
# `PartIII-b:IIIb-D3/2/G6/1`: the window-uniform class amplitude `ClassAmpWindow`

Source of record: `the November 2 reference manuscript`, lines 4624-4626 and
proof lines 4643-4661 (majorant lines 4659-4661).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

open ConcreteYF ConcreteYF.FlatAmp

private theorem majorant_le_add {lo hi x : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) (b : ℝ) {t : ℝ}
    (ht : 0 < t) :
    majorant x b t ≤ majorant lo b t + majorant hi b t := by
  have hlo_nn : 0 ≤ majorant lo b t := majorant_nonneg lo b t ht.le
  have hhi_nn : 0 ≤ majorant hi b t := majorant_nonneg hi b t ht.le
  have hfac_nn : 0 ≤ (1 + t + t ^ 2) * Real.exp (-b * t) := by positivity
  rcases le_or_gt t 1 with ht1 | ht1
  · have hpow : t ^ (x + 3 / 2) ≤ t ^ (lo + 3 / 2) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
    have hle : majorant x b t ≤ majorant lo b t := by
      unfold majorant
      calc t ^ (x + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-b * t)
          = t ^ (x + 3 / 2) * ((1 + t + t ^ 2) * Real.exp (-b * t)) := by ring
        _ ≤ t ^ (lo + 3 / 2) * ((1 + t + t ^ 2) * Real.exp (-b * t)) :=
            mul_le_mul_of_nonneg_right hpow hfac_nn
        _ = t ^ (lo + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-b * t) := by ring
    linarith
  · have hpow : t ^ (x + 3 / 2) ≤ t ^ (hi + 3 / 2) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have hle : majorant x b t ≤ majorant hi b t := by
      unfold majorant
      calc t ^ (x + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-b * t)
          = t ^ (x + 3 / 2) * ((1 + t + t ^ 2) * Real.exp (-b * t)) := by ring
        _ ≤ t ^ (hi + 3 / 2) * ((1 + t + t ^ 2) * Real.exp (-b * t)) :=
            mul_le_mul_of_nonneg_right hpow hfac_nn
        _ = t ^ (hi + 3 / 2) * (1 + t + t ^ 2) * Real.exp (-b * t) := by ring
    linarith

/-- `PartIII-b:IIIb-D3/2/G6/1`: window-uniform class amplitude estimate. -/
theorem classAmpWindow : FlatUnif.G6.ClassAmpWindow := by
  intro S ν μ lam κ ell a lo hi hlam ha0 halt hlo hνpos hνlim hce hmeas hwin hG
  obtain ⟨CS, hCS⟩ := fpmInvSubExp lam κ hlam
  obtain ⟨CF, hCF⟩ := fpmInvBound lam κ hlam
  have h3 : BclassAeBound := bclassAeBound
  obtain ⟨CG, NG, hCG⟩ := hG
  have hb : 0 < lam.re / 3 - a := by linarith
  set b : ℝ := lam.re / 3 - a
  have hMajLo : IntegrableOn (majorant lo b) (Ioi 0) :=
    majorant_integrableOn lo b (by linarith) hb
  have hMajHi : IntegrableOn (majorant hi b) (Ioi 0) :=
    majorant_integrableOn hi b (by
      obtain ⟨N0, hN0⟩ := eventually_atTop.1 hwin
      have hmem := hN0 N0 le_rfl 0 ⟨by norm_num, by norm_num⟩
      linarith [hmem.1, hmem.2]) hb
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hνlim.eventually (gt_mem_nhds one_pos))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hce.and (hmeas.and hwin))
  have hC00 : 0 ≤ 3 * |CF| * |CG| + |CS| * ‖ell‖ := by positivity
  refine ⟨(3 * |CF| * |CG| + |CS| * ‖ell‖) *
      ((∫ t in Ioi (0 : ℝ), majorant lo b t) + ∫ t in Ioi (0 : ℝ), majorant hi b t),
    max NG (max N1 N2), fun n hn z hz B hB => ?_⟩
  have hnG : NG ≤ n := le_trans (le_max_left _ _) hn
  have hn12 : max N1 N2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : ν n < 1 := hN1 n (le_trans (le_max_left _ _) hn12)
  obtain ⟨hc_eq, ⟨hpH, hpHb, hpR⟩, hwin_n⟩ := hN2 n (le_trans (le_max_right _ _) hn12)
  have hμz : μ n z ∈ Icc lo hi := hwin_n z hz
  have hμ_pos : 0 < μ n z := lt_of_lt_of_le hlo hμz.1
  have hMajInt : IntegrableOn (majorant (μ n z) b) (Ioi 0) :=
    majorant_integrableOn (μ n z) b (by linarith) hb
  have hν : 0 < ν n := hνpos n
  have hK : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hc4 : (S n).c⁻¹ ^ 2 = ν n ^ 4 := by
    rw [hc_eq]
    simp only [inv_pow, inv_inv]
    ring
  have hν4 : ν n ^ 4 ≤ ν n := by
    have h3' : ν n ^ 3 ≤ 1 := pow_le_one₀ hν.le hn1.le
    nlinarith
  obtain ⟨hBm, -, -, hBsupp, -⟩ := id hB
  have hBd : Measurable (fun t => Bd (B t)) := ((hBm 0 0).sub (hBm 2 2)).div_const 2
  have hBe : Measurable (fun t => Be (B t)) := ((hBm 0 2).add (hBm 2 0)).div_const 2
  have hBb : Measurable (fun t => Bbeta (B t)) := ((hBm 0 0).add (hBm 2 2)).div_const 2
  have hmA := measurable_ampIntegrand (S n) lam κ (ν n) (μ n z) B hBd hBe hBb hpH hpHb hpR
  have hmZ := measurable_zeroIntegrand lam ell (μ n z) B hBd hBe
  have hmE : Measurable (fun t => ampIntegrand (S n) lam κ (ν n) (μ n z) B t -
      zeroIntegrand lam ell (μ n z) B t) := hmA.fun_sub hmZ
  have hA : (S n).aNuC lam κ (μ n z : ℂ) (ν n) B =
      ∫ t in Ioc 0 (1.1 / ν n), ampIntegrand (S n) lam κ (ν n) (μ n z) B t := rfl
  have hZ := aZero_eq lam ell (μ n z) (ν n) B hBsupp
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (h3 a (ν n) B hB)
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))), t ∈ Ioc (0 : ℝ) (1.1 / ν n) :=
    ae_restrict_mem measurableSet_Ioc
  have hEb : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))),
      ‖ampIntegrand (S n) lam κ (ν n) (μ n z) B t - zeroIntegrand lam ell (μ n z) B t‖ ≤
        (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B * majorant (μ n z) b t := by
    filter_upwards [hae, hmem] with t hm ht
    obtain ⟨hGH, hGHb, hGR⟩ := hCG n hnG t ⟨ht.1.le, ht.2⟩
    rw [hc4] at hGH hGHb hGR
    exact pointwise_error (S n) lam κ ell (μ n z) a (ν n) t (bNorm a B) CF CS CG B
      hν hν4 ht.1 hK hm (hCF (ν n) hν t ⟨ht.1.le, ht.2⟩) (hCS (ν n) hν t ⟨ht.1.le, ht.2⟩)
      hGH hGHb hGR
  have hgb : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))),
      ‖zeroIntegrand lam ell (μ n z) B t‖ ≤ ‖ell‖ * bNorm a B * majorant (μ n z) b t := by
    filter_upwards [hae, hmem] with t hm ht
    exact pointwise_zero lam ell (μ n z) a t (bNorm a B) B hlam ht.1 hK hm
  have hMajIoc : Integrable (majorant (μ n z) b)
      (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) :=
    hMajInt.mono_set Ioc_subset_Ioi_self
  have hZI : Integrable (zeroIntegrand lam ell (μ n z) B)
      (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) :=
    Integrable.mono' (hMajIoc.const_mul (‖ell‖ * bNorm a B)) hmZ.aestronglyMeasurable hgb
  have hEI : Integrable (fun t => ampIntegrand (S n) lam κ (ν n) (μ n z) B t -
      zeroIntegrand lam ell (μ n z) B t) (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) :=
    Integrable.mono' (hMajIoc.const_mul ((3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B))
      hmE.aestronglyMeasurable hEb
  have hAI : Integrable (ampIntegrand (S n) lam κ (ν n) (μ n z) B)
      (volume.restrict (Ioc (0 : ℝ) (1.1 / ν n))) := by
    refine (hEI.add hZI).congr (Eventually.of_forall (fun t => ?_))
    simp
  have hIntLe : ∫ t in Ioi (0 : ℝ), majorant (μ n z) b t ≤
      (∫ t in Ioi (0 : ℝ), majorant lo b t) + ∫ t in Ioi (0 : ℝ), majorant hi b t := by
    rw [← integral_add hMajLo hMajHi]
    exact setIntegral_mono_on hMajInt (hMajLo.add hMajHi) measurableSet_Ioi
      (fun t ht => majorant_le_add hμz.1 hμz.2 b ht)
  rw [hA, hZ, ← integral_sub hAI hZI]
  calc ‖∫ t in Ioc 0 (1.1 / ν n),
        (ampIntegrand (S n) lam κ (ν n) (μ n z) B t - zeroIntegrand lam ell (μ n z) B t)‖
      ≤ ∫ t in Ioc 0 (1.1 / ν n),
        (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B * majorant (μ n z) b t :=
        norm_integral_le_of_norm_le (hMajIoc.const_mul _) hEb
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B *
        ∫ t in Ioc 0 (1.1 / ν n), majorant (μ n z) b t := integral_const_mul _ _
    _ ≤ (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B *
        ∫ t in Ioi 0, majorant (μ n z) b t := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hC00 hν.le) hK)
        exact setIntegral_mono_set hMajInt
          (ae_restrict_of_forall_mem measurableSet_Ioi
            (fun t ht => majorant_nonneg (μ n z) _ t (le_of_lt (mem_Ioi.mp ht))))
          (LE.le.eventuallyLE Ioc_subset_Ioi_self)
    _ ≤ (3 * |CF| * |CG| + |CS| * ‖ell‖) * ν n * bNorm a B *
        ((∫ t in Ioi (0 : ℝ), majorant lo b t) + ∫ t in Ioi (0 : ℝ), majorant hi b t) :=
        mul_le_mul_of_nonneg_left hIntLe (mul_nonneg (mul_nonneg hC00 hν.le) hK)
    _ = (3 * |CF| * |CG| + |CS| * ‖ell‖) *
        ((∫ t in Ioi (0 : ℝ), majorant lo b t) + ∫ t in Ioi (0 : ℝ), majorant hi b t) *
        ν n * bNorm a B := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
