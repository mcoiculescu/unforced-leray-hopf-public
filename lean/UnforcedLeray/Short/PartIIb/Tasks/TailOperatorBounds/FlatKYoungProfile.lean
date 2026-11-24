import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainVelSmooth
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.Helpers.YoungTrain

/-!
# `PartII-b:G2/3/2`: young bound for the flat interaction profile (SP 2436-2445)
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb
namespace YoungHelp

theorem vQ_zero : vQ 0 = vQ0 := by
  funext x; simp [vQ, vQ0]

theorem dQ_zero : dQ 0 = dZero := by
  funext x; simp [dQ, dZero]

end YoungHelp
end UnforcedLeray.Short.IIb

theorem flatKYoungProfile_proof : UnforcedLeray.Short.IIb.FlatKYoungProfile := by
  open UnforcedLeray.Short.IIb UnforcedLeray.Cons.C03.Concrete in
  intro dm dp hdm Cf hCf
  obtain ⟨Cb, kb, νb, hCb, hνb, HT⟩ := YoungHelp.train_young_bound dm dp hdm
  refine ⟨12 * Cb * Cf, kb + 1, min νb 1, by positivity, lt_min hνb one_pos, ?_⟩
  intro p d hreg hν hF F b gq gη hFin hb hresp hgq hgη σ hσ hσ1
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hc : 0 < p.c := by rw [hreg.c_eq]; positivity
  obtain ⟨b0, hb0cls, -, hb0gb, huniq⟩ := hF F hFin
  have hbb0 : b =ᵐ[hMeas p.c bgp] b0 := huniq b hb hresp
  have hgb : GraphBound p.ν p.c bgp 0 Cf F b :=
    graphBoundCongrPer p.ν p.c bgp Cf F b b0 hc hb.inHr.periodic hb0cls.inHr.periodic hbb0 hb0gb
  obtain ⟨Sb, Qb, Eb, -, h2, h3, hn⟩ := hgb
  rw [YoungHelp.vQ_zero, YoungHelp.dQ_zero] at h2
  have eq1 : gq =ᵐ[hMeas p.c bgp] Qb := hasWeakVec_unique_ae hc hgq h2
  have eq2 : gη =ᵐ[hMeas p.c bgp] Eb := hasWeakVec_unique_ae hc hgη h3
  obtain ⟨Sb', Qb', Eb', -, hq', he', -, hQin, hEin⟩ := hb.deriv
  have eq1' : gq =ᵐ[hMeas p.c bgp] Qb' := hasWeakVec_unique_ae hc hgq hq'
  have eq2' : gη =ᵐ[hMeas p.c bgp] Eb' := hasWeakVec_unique_ae hc hgη he'
  have m1 : AEStronglyMeasurable (sqrtS gq) (hMeas p.c bgp) :=
    hQin.meas.congr (sqrtS_congr_ae eq1'.symm)
  have m2 : AEStronglyMeasurable (sqrtS gη) (hMeas p.c bgp) :=
    hEin.meas.congr (sqrtS_congr_ae eq2'.symm)
  have m0 : AEStronglyMeasurable b (hMeas p.c bgp) := hb.inHr.meas
  -- norm bounds from the graph bound
  set N := hNorm p.c bgp F with hN
  have hn1 : hNorm p.c bgp b ≤ ENNReal.ofReal Cf * N :=
    le_trans (le_trans le_self_add le_self_add) hn
  have hn2 : ENNReal.ofReal (Real.sqrt p.ν) * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))
      ≤ ENNReal.ofReal Cf * N := le_trans le_add_self hn
  have hsq : p.ν ≤ Real.sqrt p.ν := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hinv : ENNReal.ofReal p.ν⁻¹ * ENNReal.ofReal p.ν = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hνpos.le), inv_mul_cancel₀ hνpos.ne']
    simp
  have hk1 : 1 ≤ p.ν⁻¹ := one_le_inv_iff₀.mpr ⟨hνpos, hν1⟩
  have hsum : ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))
      ≤ ENNReal.ofReal Cf * N :=
    le_trans (by gcongr) hn2
  have hsum2 : hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb) ≤
      ENNReal.ofReal (Cf * p.ν⁻¹) * N := by
    calc _ = ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal p.ν *
          (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal Cf * N) := by gcongr
      _ = ENNReal.ofReal (Cf * p.ν⁻¹) * N := by
          rw [ENNReal.ofReal_mul hCf.le]; ring
  have hQ : hNorm p.c bgp (sqrtS gq) ≤ ENNReal.ofReal (Cf * p.ν⁻¹) * N := by
    have : hNorm p.c bgp (sqrtS gq) = hNorm p.c bgp (sqrtS Qb) :=
      eLpNorm_congr_ae (sqrtS_congr_ae eq1)
    rw [this]; exact le_trans le_self_add hsum2
  have hE : hNorm p.c bgp (sqrtS gη) ≤ ENNReal.ofReal (Cf * p.ν⁻¹) * N := by
    have : hNorm p.c bgp (sqrtS gη) = hNorm p.c bgp (sqrtS Eb) :=
      eLpNorm_congr_ae (sqrtS_congr_ae eq2)
    rw [this]; exact le_trans le_add_self hsum2
  have hB0 : hNorm p.c bgp b ≤ ENNReal.ofReal (Cf * p.ν⁻¹) * N :=
    hn1.trans (by gcongr; exact le_mul_of_one_le_right hCf.le hk1)
  -- pointwise bound
  set B : ℝ := Cb * (p.ν ^ kb)⁻¹ with hBdef
  have hBnn : 0 ≤ B := by positivity
  have hsv := trainVelSmooth_proof p d dm dp hreg
  have hpt : ∀ᵐ x ∂(hMeas p.c bgp),
      ‖(youngAgeSet σ).indicator (flatK p.train b gq gη) x‖ ≤
        4 * B * Real.sqrt σ * (‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖) := by
    filter_upwards [ageμ_ae_pos p.c (bgp / 2 - 5 / 2)] with x hx0
    have hRHS : 0 ≤ 4 * B * Real.sqrt σ * (‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖) := by positivity
    by_cases hxy : x ∈ youngAgeSet σ
    · rw [Set.indicator_of_mem hxy]
      have hxσ : x.1 < σ := hxy
      have hx1 : x.1 ≤ 1 := by linarith
      obtain ⟨t1, t2, t3⟩ := HT p d hreg (hν.trans (min_le_left _ _)) x hx0 hx1
      have hK := YoungHelp.flatK_norm_le p.train hsv b gq gη x hx0 B t1 t2 t3
      have hs1 : x.1 ≤ Real.sqrt σ := by
        apply Real.le_sqrt_of_sq_le; nlinarith
      have hs2 : Real.sqrt x.1 ≤ Real.sqrt σ := Real.sqrt_le_sqrt hxσ.le
      have hsx : Real.sqrt x.1 * Real.sqrt x.1 = x.1 := Real.mul_self_sqrt hx0.le
      have nS : ∀ g : CProf, ‖sqrtS g x‖ = Real.sqrt x.1 * ‖g x‖ := by
        intro g
        simp [sqrtS, norm_smul, Real.sqrt_nonneg]
      have ga : x.1 * ‖gq x‖ ≤ Real.sqrt σ * ‖sqrtS gq x‖ := by
        have e : x.1 * ‖gq x‖ = Real.sqrt x.1 * (Real.sqrt x.1 * ‖gq x‖) := by
          rw [← mul_assoc, hsx]
        rw [e, nS]
        exact mul_le_mul_of_nonneg_right hs2 (mul_nonneg (Real.sqrt_nonneg x.1) (norm_nonneg _))
      have gb : x.1 * ‖gη x‖ ≤ Real.sqrt σ * ‖sqrtS gη x‖ := by
        have e : x.1 * ‖gη x‖ = Real.sqrt x.1 * (Real.sqrt x.1 * ‖gη x‖) := by
          rw [← mul_assoc, hsx]
        rw [e, nS]
        exact mul_le_mul_of_nonneg_right hs2 (mul_nonneg (Real.sqrt_nonneg x.1) (norm_nonneg _))
      have gc : x.1 * ‖b x‖ ≤ Real.sqrt σ * ‖b x‖ :=
        mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      have key : x.1 * (‖gq x‖ + ‖gη x‖ + 2 * ‖b x‖) ≤
          2 * (Real.sqrt σ * (‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖)) := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg σ) (norm_nonneg (sqrtS gq x)),
          mul_nonneg (Real.sqrt_nonneg σ) (norm_nonneg (sqrtS gη x)),
          mul_nonneg (Real.sqrt_nonneg σ) (norm_nonneg (b x))]
      calc ‖flatK p.train b gq gη x‖ ≤ 2 * (x.1 * B * (‖gq x‖ + ‖gη x‖ + 2 * ‖b x‖)) := hK
        _ = 2 * B * (x.1 * (‖gq x‖ + ‖gη x‖ + 2 * ‖b x‖)) := by ring
        _ ≤ 2 * B * (2 * (Real.sqrt σ * (‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖))) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hxy]
      simpa using hRHS
  -- assemble
  have hmono := eLpNorm_mono_ae_real (p := ENNReal.ofReal bgp) hpt
  have hu : AEStronglyMeasurable (fun x => ‖sqrtS gq x‖) (hMeas p.c bgp) := m1.norm
  have hv : AEStronglyMeasurable (fun x => ‖sqrtS gη x‖) (hMeas p.c bgp) := m2.norm
  have hw : AEStronglyMeasurable (fun x => ‖b x‖) (hMeas p.c bgp) := m0.norm
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num [bgp])
  have htri : eLpNorm (fun x => ‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖) (ENNReal.ofReal bgp)
      (hMeas p.c bgp) ≤ hNorm p.c bgp (sqrtS gq) + hNorm p.c bgp (sqrtS gη) + hNorm p.c bgp b := by
    have h1 := eLpNorm_add_le (hu.add hv) hw hp1 (μ := hMeas p.c bgp)
    have h2 := eLpNorm_add_le hu hv hp1 (μ := hMeas p.c bgp)
    have e1 : eLpNorm (fun x => ‖sqrtS gq x‖) (ENNReal.ofReal bgp) (hMeas p.c bgp) =
        hNorm p.c bgp (sqrtS gq) := eLpNorm_norm _
    have e2 : eLpNorm (fun x => ‖sqrtS gη x‖) (ENNReal.ofReal bgp) (hMeas p.c bgp) =
        hNorm p.c bgp (sqrtS gη) := eLpNorm_norm _
    have e3 : eLpNorm (fun x => ‖b x‖) (ENNReal.ofReal bgp) (hMeas p.c bgp) =
        hNorm p.c bgp b := eLpNorm_norm _
    rw [e3] at h1
    rw [e1, e2] at h2
    exact h1.trans (add_le_add h2 le_rfl)
  have ha : 0 ≤ 4 * B * Real.sqrt σ := by positivity
  have hsc : eLpNorm (fun x => 4 * B * Real.sqrt σ * (‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖))
      (ENNReal.ofReal bgp) (hMeas p.c bgp) =
      ENNReal.ofReal (4 * B * Real.sqrt σ) *
        eLpNorm (fun x => ‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖) (ENNReal.ofReal bgp)
          (hMeas p.c bgp) := by
    rw [show (fun x => 4 * B * Real.sqrt σ * (‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖)) =
      (4 * B * Real.sqrt σ) • (fun x => ‖sqrtS gq x‖ + ‖sqrtS gη x‖ + ‖b x‖) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal ha]
  have h3 : hNorm p.c bgp (sqrtS gq) + hNorm p.c bgp (sqrtS gη) + hNorm p.c bgp b ≤
      ENNReal.ofReal (3 * (Cf * p.ν⁻¹)) * N := by
    calc _ ≤ ENNReal.ofReal (Cf * p.ν⁻¹) * N + ENNReal.ofReal (Cf * p.ν⁻¹) * N +
          ENNReal.ofReal (Cf * p.ν⁻¹) * N := by gcongr
      _ = _ := by
        have h3' : ENNReal.ofReal (3 * (Cf * p.ν⁻¹)) = 3 * ENNReal.ofReal (Cf * p.ν⁻¹) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]; norm_num
        rw [h3']; ring
  have hcoef : 4 * B * Real.sqrt σ * (3 * (Cf * p.ν⁻¹)) =
      12 * Cb * Cf * (p.ν ^ (kb + 1))⁻¹ * Real.sqrt σ := by
    rw [hBdef, pow_succ]; field_simp
    ring
  show eLpNorm _ _ _ ≤ _
  calc _ ≤ _ := hmono
    _ = _ := hsc
    _ ≤ ENNReal.ofReal (4 * B * Real.sqrt σ) * (hNorm p.c bgp (sqrtS gq) +
          hNorm p.c bgp (sqrtS gη) + hNorm p.c bgp b) := by gcongr
    _ ≤ ENNReal.ofReal (4 * B * Real.sqrt σ) * (ENNReal.ofReal (3 * (Cf * p.ν⁻¹)) * N) := by
        gcongr
    _ = ENNReal.ofReal (12 * Cb * Cf * (p.ν ^ (kb + 1))⁻¹ * Real.sqrt σ) * N := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha, hcoef]
