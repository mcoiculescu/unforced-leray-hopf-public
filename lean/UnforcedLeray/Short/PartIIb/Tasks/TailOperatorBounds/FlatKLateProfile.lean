import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction.FreeInteraction
import UnforcedLeray.Short.PartIIb.Tasks.FlatInverse

/-!
# `PartII-b:G2/3/3`: late bound for the flat interaction profile (SP 2436-2445)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open FreeInteractionAux

theorem flatKLateProfile_proof : UnforcedLeray.Short.IIb.FlatKLateProfile := by
  intro dm dp hdm Cfl hCfl
  obtain ⟨Ct, kt, νt, hCt, hνt, Ht⟩ := trainVel_tail_bound
  refine ⟨3 * Cfl * Ct, kt + 1, min νt 1, by positivity, lt_min hνt one_pos, ?_⟩
  intro p d hb hν hgr F b gq gη hF hbc hresp hgq hgη S hS
  have hνpos : 0 < p.ν := p.ν_pos
  have hνt' : p.ν ≤ νt := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hc : 0 < p.c := by rw [hb.c_eq]; positivity
  have hS0 : 0 < S := lt_of_lt_of_le one_pos hS
  obtain ⟨b', hb'c, hb'r, hb'g, hb'u⟩ := hgr F hF
  have hbb : b =ᵐ[hMeas p.c bgp] b' := hb'u b hbc hresp
  have hb_vol : ∀ᵐ x : Coord, 0 < x.1 → b x = b' x :=
    CongrHelp.ae_volume_of_ageμ hc hbc.inHr.periodic hb'c.inHr.periodic hbb
  obtain ⟨Sb, Qb, Eb, _, hQ, hE, hbd⟩ := hb'g
  have hv : vQ 0 = vQ0 := by funext x; simp [vQ, vQ0]
  have hd : dQ 0 = dZero := by funext x; simp [dQ, dZero]
  rw [hv, hd] at hQ
  have hQb : HasWeakVec vQ0 dZero b Qb :=
    hasWeakVec_congr hb_vol (Eventually.of_forall fun _ _ => rfl) hQ
  have hEb : HasWeakVec vEta dZero b Eb :=
    hasWeakVec_congr hb_vol (Eventually.of_forall fun _ _ => rfl) hE
  obtain ⟨Sb', Qb', Eb', _, hQ', hE', _, hq', hη'⟩ := hbc.deriv
  have hQQ : Qb =ᵐ[hMeas p.c bgp] Qb' := hasWeakVec_unique_ae hc hQb hQ'
  have hEE : Eb =ᵐ[hMeas p.c bgp] Eb' := hasWeakVec_unique_ae hc hEb hE'
  have hgQ : gq =ᵐ[hMeas p.c bgp] Qb' := hasWeakVec_unique_ae hc hgq hQ'
  have hgE : gη =ᵐ[hMeas p.c bgp] Eb' := hasWeakVec_unique_ae hc hgη hE'
  have hnQ : hNorm p.c bgp (sqrtS Qb) = hNorm p.c bgp (sqrtS Qb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae hQQ)
  have hnE : hNorm p.c bgp (sqrtS Eb) = hNorm p.c bgp (sqrtS Eb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae hEE)
  have hnb : hNorm p.c bgp b' = hNorm p.c bgp b := eLpNorm_congr_ae hbb.symm
  have hbd' : hNorm p.c bgp b + ENNReal.ofReal (Real.sqrt p.ν) *
      (hNorm p.c bgp (sqrtS Qb') + hNorm p.c bgp (sqrtS Eb')) ≤
      ENNReal.ofReal Cfl * hNorm p.c bgp F := by
    rw [← hnQ, ← hnE, ← hnb]
    refine le_trans ?_ hbd
    calc _ ≤ hNorm p.c bgp b' + ENNReal.ofReal (Real.sqrt p.ν) *
          (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) + hNorm p.c bgp Sb := le_self_add
      _ = _ := add_right_comm _ _ _
  have hKae : flatK p.train b gq gη =ᵐ[hMeas p.c bgp] flatK p.train b Qb' Eb' := by
    filter_upwards [hgQ, hgE] with x h1 h2
    simp only [flatK, h1, h2]
  set U : ℝ := Ct * (p.ν ^ kt)⁻¹ with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hSr : 0 ≤ S ^ (-1 / 2 : ℝ) := by positivity
  have h1 := eLpNorm_restrict_flatK_le hc p.train b Qb' Eb' hbc.inHr hq' hη'
    (lateAgeSet S) (measurableSet_lateAgeSet S)
    (A₁ := U * S ^ (-1 / 2 : ℝ)) (A₂ := 2 * U * S ^ (-1 / 2 : ℝ))
    (by positivity) (by positivity)
    (fun x hx hx0 => by
      have hxS : S < x.1 := hx
      have hx1 : 1 ≤ x.1 := hS.trans hxS.le
      obtain ⟨h1, h2, h3⟩ := Ht p d dm dp hb hνt' x hx1
      have hV0 : 0 ≤ U * x.1 ^ (-1 : ℝ) := by positivity
      have hD0 : 0 ≤ U * x.1 ^ (-(3 / 2) : ℝ) := by positivity
      have := norm_flatK_le_of_vel_grad p.train b Qb' Eb' hx0 hV0 hD0
        (by simpa [hUdef, mul_assoc] using h1) (by simpa [hUdef, mul_assoc] using h2)
        (by simpa [hUdef, mul_assoc] using h3)
      refine this.trans ?_
      have hr : x.1 ^ (-1 / 2 : ℝ) ≤ S ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hS0 hxS.le (by norm_num)
      have e1 : U * x.1 ^ (-1 : ℝ) * Real.sqrt x.1 = U * x.1 ^ (-1 / 2 : ℝ) := by
        rw [mul_assoc, rpow_neg_one_mul_sqrt hx0]
      have e2 : 2 * (U * x.1 ^ (-(3 / 2) : ℝ)) * x.1 = 2 * U * x.1 ^ (-1 / 2 : ℝ) := by
        rw [← rpow_neg_three_halves_mul hx0]; ring
      rw [e1, e2]
      have n1 := norm_nonneg (sqrtS Qb' x)
      have n2 := norm_nonneg (sqrtS Eb' x)
      have n3 := norm_nonneg (b x)
      have g1 : U * x.1 ^ (-1 / 2 : ℝ) ≤ U * S ^ (-1 / 2 : ℝ) := by gcongr
      have g2 : 2 * U * x.1 ^ (-1 / 2 : ℝ) ≤ 2 * U * S ^ (-1 / 2 : ℝ) := by gcongr
      gcongr)
  have h2 := h1.trans (enn_combine hνpos (by positivity) (by positivity) hCfl.le hbd')
  have hreal : Cfl * (U * S ^ (-1 / 2 : ℝ) * p.ν ^ (-1 / 2 : ℝ) + 2 * U * S ^ (-1 / 2 : ℝ)) ≤
      3 * Cfl * Ct * (p.ν ^ (kt + 1))⁻¹ * S ^ (-(1 / 2 : ℝ)) := by
    have hneg : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [hneg]
    have hp1 : p.ν ^ (-1 / 2 : ℝ) ≤ p.ν⁻¹ := by
      have : p.ν ^ (-1 / 2 : ℝ) ≤ p.ν ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hνpos hν1 (by norm_num)
      simpa [Real.rpow_neg_one] using this
    have hp2 : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν1⟩
    have hpow : (p.ν ^ (kt + 1))⁻¹ = (p.ν ^ kt)⁻¹ * p.ν⁻¹ := by
      rw [pow_succ, mul_inv]
    rw [hpow]
    have hk : 0 ≤ (p.ν ^ kt)⁻¹ := by positivity
    have : U * S ^ (-1 / 2 : ℝ) * p.ν ^ (-1 / 2 : ℝ) + 2 * U * S ^ (-1 / 2 : ℝ) ≤
        3 * Ct * ((p.ν ^ kt)⁻¹ * p.ν⁻¹) * S ^ (-1 / 2 : ℝ) := by
      rw [hUdef]
      have : Ct * (p.ν ^ kt)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) + 2) ≤
          Ct * (p.ν ^ kt)⁻¹ * (3 * p.ν⁻¹) := by
        gcongr; linarith
      nlinarith [mul_le_mul_of_nonneg_right this hSr]
    nlinarith [mul_le_mul_of_nonneg_left this hCfl.le]
  have hind : eLpNorm ((lateAgeSet S).indicator (flatK p.train b gq gη)) (ENNReal.ofReal bgp)
      (hMeas p.c bgp) = eLpNorm (flatK p.train b Qb' Eb') (ENNReal.ofReal bgp)
      ((hMeas p.c bgp).restrict (lateAgeSet S)) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_lateAgeSet S)]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hKae] with x hx
    by_cases hxS : x ∈ lateAgeSet S <;> simp [Set.indicator, hxS, hx]
  have hfin := ENNReal.ofReal_le_ofReal hreal
  change eLpNorm _ _ _ ≤ _
  rw [hind]
  refine h2.trans ?_
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _

end UnforcedLeray.Short.IIb

end
