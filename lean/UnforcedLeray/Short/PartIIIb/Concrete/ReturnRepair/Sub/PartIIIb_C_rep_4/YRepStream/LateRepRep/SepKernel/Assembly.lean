import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/org` (d): `FarRepRepUng` and `LateSepKernel` from the leaves

Source `the November 2 reference manuscript` 5303-5306, 5323-5339, 5134-5139,
3902-3920.

`farRepRepUng_of`: on a box repair source, the receiver conversion (c) `RepRecvConv`
(`P_νε^{25/22}e^{m₀/(2ν)}`), the lift identity `SopSubIsFarSeq` (`Sop - SNop = Sf`,
`IsFarMaskG`: output a.e. `farOut f`) and the separated kernel (a) `FarVelYoungBox`
(`(1-e^{-δ/2})^{-35/11}ε^{35/11}S^{35/22}`) give the bound; the extension (b2) `FarRepExtend`
passes to every repair source.  Exponents: `25/22 + 35/11 = 95/22`, `S^{35/22} = ε^{-35b/22} ≤
ε^{-2b}` (`ε ≤ 1`), so `k₀ = 2` (chosen before the sequence).

`lateSepKernel_of_leaves`: `LateSepKernel` (`LateRepRep/Props.lean`) from the same four facts
(with `lateSepKernel_of_farRepRepUng`, `Props.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ε^{25/22}·ε^{35/11}·S^{35/22} ≤ ε^{-2b}ε^{95/22}` for `S = ε^{-b}`, `0 < ε ≤ 1`, `b ≥ 0`
(source 5332: the polynomial `P_νS^k`). -/
theorem lrr_kernel_const {ε b S : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 ≤ b)
    (hS : S = ε ^ (-b)) :
    ε ^ (25 / 22 : ℝ) * (ε ^ (35 / 11 : ℝ) * S ^ (35 / 22 : ℝ)) ≤
      ε ^ (-(((2 : ℕ) : ℝ) * b)) * ε ^ (95 / 22 : ℝ) := by
  subst hS
  rw [← Real.rpow_mul hε.le, ← mul_assoc, ← Real.rpow_add hε]
  have h1 : (25 / 22 : ℝ) + 35 / 11 = 95 / 22 := by norm_num
  rw [h1, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε.le _)
  refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
  push_cast
  nlinarith

/-- **`FarRepRepUng` from the leaves** (source 5303-5306, 5323-5339, 5134-5139, 3902-3920). -/
theorem farRepRepUng_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hR : SopSubIsFarSeq Pl σ₀ mZ dm dp) (ha : FarVelYoungBox) (hc : RepRecvConv dm dp)
    (hX : FarRepExtend) : FarRepRepUng Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D hP hσ hZ hst => ?_⟩
  obtain ⟨Ca, hCa, ha'⟩ := ha
  obtain ⟨Cc, kc, hCc, ec⟩ := hc D hst
  have hδ1 : 0 ≤ 1 - Real.exp (-D.K.δ / 2) := by
    have h := Real.exp_lt_exp.2 (show -D.K.δ / 2 < 0 by linarith [hst.δ_pos])
    rw [Real.exp_zero] at h
    linarith
  have hcδ : 0 ≤ (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ)) := Real.rpow_nonneg hδ1 _
  have hC0 : 0 ≤ Cc * (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ))) :=
    mul_nonneg hCc (mul_nonneg hCa hcδ)
  refine ⟨Cc * (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ))), kc, hC0, ?_⟩
  filter_upwards [hR D hP hσ hZ hst, ec, inv_seq_large D hst.dm_pos hst.omega_ne hst.sigma_pos
    hst.sigma_lt hst.actual] with n hRn hcn hL
  intro z hz T
  obtain ⟨Sf, hSf, hEq⟩ := hRn z hz
  obtain ⟨-, -, hε1, hμ⟩ := hL
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hε1' : (D.level n).ε ≤ 1 := hε1
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hc0 : 0 < cOf (D.level n).ν := cOf_pos hν
  have hμ' : -(1 / 4) < D.mu n z := by
    have h1 := (hμ z hz).1
    have h2 := hst.sigma_pos
    linarith
  have hS : 0 < (D.level n).Scut D.K := by
    unfold ReturnLevel.Scut; exact Real.rpow_pos_of_pos hε _
  have hKc0 : 0 ≤ Cc * (D.level n).ν⁻¹ ^ kc * (D.level n).ε ^ (25 / 22 : ℝ) *
      Real.exp (D.K.m0 / 2 / (D.level n).ν) := by positivity
  have hbox : ∀ (T' : LStr D.Pl D.K (D.level n)) (f : Chart → Ten3), NearInst.IsBoxTensor f →
      strSum (repPart T') =ᵐ[ageμ (cOf (D.level n).ν) (-1 / 2)] f →
      htUng (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
          ((multOp D.Pl D.K (D.level n) (Sf (repPart T'))).snd : Chart → Ten3) ≤
        (ENNReal.ofReal (Cc * (D.level n).ν⁻¹ ^ kc * (D.level n).ε ^ (25 / 22 : ℝ) *
            Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
          ENNReal.ofReal (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ)) *
            (D.level n).ε ^ (35 / 11 : ℝ) * ((D.level n).Scut D.K) ^ (35 / 22 : ℝ))) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) := by
    intro T' f hf hsum
    have h1 := hcn (Sf (repPart T'))
    have h2 := hSf (repPart T') f hf hsum
    have h3 := ha' (D.level n).ε (cOf (D.level n).ν) (D.level n).ν D.K.δ ((D.level n).Scut D.K)
      (D.mu n z) hε hc0 hν hst.δ_pos hS hμ' f hf
      ((Sf (repPart T') : LVel D.Pl (D.level n)) : Chart → Merid)
      (Lp.stronglyMeasurable _).measurable h2
    rw [mul_assoc]
    exact h1.trans (mul_le_mul' le_rfl h3)
  have hext := hX D.Pl D.K (D.level n) hst.C0_pos Sf _ hbox T
  rw [hEq]
  refine hext.trans (mul_le_mul' ?_ le_rfl)
  rw [← ENNReal.ofReal_mul hKc0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hk := lrr_kernel_const hε hε1' hst.b_pos.le
    (rfl : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b))
  have hA0 : 0 ≤ Cc * (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ))) *
      (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν) := by
    have := Real.exp_pos (D.K.m0 / 2 / (D.level n).ν)
    have : 0 ≤ (D.level n).ν⁻¹ ^ kc := by positivity
    positivity
  calc (Cc * (D.level n).ν⁻¹ ^ kc * (D.level n).ε ^ (25 / 22 : ℝ) *
          Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
        (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ)) *
          (D.level n).ε ^ (35 / 11 : ℝ) * ((D.level n).Scut D.K) ^ (35 / 22 : ℝ))
      = (Cc * (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ))) *
          (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
        ((D.level n).ε ^ (25 / 22 : ℝ) *
          ((D.level n).ε ^ (35 / 11 : ℝ) * ((D.level n).Scut D.K) ^ (35 / 22 : ℝ))) := by ring
    _ ≤ (Cc * (Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(35 / 11 : ℝ))) *
          (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
        ((D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) * (D.level n).ε ^ (95 / 22 : ℝ)) :=
          mul_le_mul_of_nonneg_left hk hA0
    _ = _ := by ring

/-- **`LateSepKernel` from the leaves** (source 5303-5306, 5318, 5323-5339, 5134-5139,
3902-3920): the realization `SopSubIsFarSeq` (task `PartIII-b:C/rep/5/1/1/1`), the separated
kernel `FarVelYoungBox`, the receiver conversion `RepRecvConv` and the extension `FarRepExtend`. -/
theorem lateSepKernel_of_leaves (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hR : SopSubIsFarSeq Pl σ₀ mZ dm dp) (ha : FarVelYoungBox) (hc : RepRecvConv dm dp)
    (hX : FarRepExtend) : LateSepKernel Pl σ₀ mZ dm dp :=
  lateSepKernel_of_farRepRepUng Pl σ₀ mZ dm dp (farRepRepUng_of Pl σ₀ mZ dm dp hR ha hc hX)

end UnforcedLeray.Short.PartIIIb.Concrete
