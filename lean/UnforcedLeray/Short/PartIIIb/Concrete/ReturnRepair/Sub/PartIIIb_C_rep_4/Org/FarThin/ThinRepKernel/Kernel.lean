import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.ThinRepKernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.ThinLiftZ1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.FarVelYoungBoxL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HW
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HU
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq

/-!
# `PartIII-b:C/rep/4/1/org/5/1`: the ungained thin-to-repair far kernel

Source `the November 2 reference manuscript` 5303-5311 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`), 5323-5339 (thin source → scaled repair receiver `ε^{49/22}e^{m₀/(2ν)}`,
"the thin-to-repair entry uses the order-four kernel from `L²` to `L^{22/3}`, with off-diagonal
norm `D^{-23/11}`, followed by `√ρ`"), 3631-3650 (`sep:young`), 3902-3912, 2693-2706, 2683-2697
(`‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`, `Z₁`), 5134-5139.

Route (all pieces proved):

* **far part** `Sop - SNop = Sf` with `IsFarMaskG` at every standing level: `concreteBase_isNearSplit`
  with `stressMapWeakSolC`, `stressPairAE`, `freeWeakUniquenessAll` and the near operators of
  `hst.pins` (the argument of `sopSubIsFarSeq_of` with `NearOpsExistC` replaced by `RegimePins.near`);
* **(A)** box tensors: `farVelYoungBoxL2` (`sep:young`, `p = 2`, `q = 22/3`, `D^{-23/11}`, output cut
  `S`) and `repRecvConv` (`r_b ⊗ v + v ⊗ r_b`, Hölder `1/2 = 4/11 + 3/22`, `√ρ_b`), with the
  source lift `thinLiftZ1` (`‖𝒩_TT₁‖_{L²L²} ≤ √π ε⁻¹ ‖T₁‖_{Z₁}`);
* **(C)** completion: `FarBridge.farBridge_le_mono` with the closed receiver `htUng ∘ (M_U ·)₂`
  (`RecvClosed.lintegral_comp`) and the source norm `phaseL2Lr`, nonincreasing under truncation.

Exponents: `ε^{25/22}·(ε^{23/11}S^{23/22})·ε⁻¹ ≤ ε^{-2b}ε^{49/22}`, so `k₀ = 2`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace FarThinKernel

/-- **The far mask part of `Sop - SNop`, at every standing level** (source 3888-3920, 5785): the
argument of `sopSubIsFarSeq_of` with the near operators supplied by the pins of `RepairStanding`. -/
theorem far_part (dm dp : ℝ) (D : SeqData) (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ Sf : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
        IsFarMaskG (D.level n).ε⁻¹ (D.mu n z) D.K.δ ((D.level n).Scut D.K) Sf ∧
          Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z) = Sf := by
  filter_upwards [hst.pins, hst.near,
    inv_seq_large D hst.dm_pos hst.omega_ne hst.sigma_pos hst.sigma_lt hst.actual] with
    n hp hnear hlarge z hz
  obtain ⟨-, hP, -, hμ⟩ := hlarge
  have hμ' : -(1 / 4) < D.mu n z := by linarith [(hμ z hz).1, hst.sigma_pos]
  have hν := retNu_pos D.Pl D.σ₀ n
  have hs := concreteBase_isNearSplit UnforcedLeray.Short.PartIIIb.stressMapWeakSolC
    NearInst.stressPairAE
    (UnforcedLeray.Short.PartIIIb.freeWeakUniquenessAll _ _ _ _ _
      (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (retNu_pos D.Pl D.σ₀ n) (retEps_pos D.coeff_ne n) hP
      (by linarith))
    hP hμ' (by linarith [hst.mZ_gt]) (inv_rhoB_pos hst.C0_pos) (hp z hz).near (hnear z hz)
  obtain ⟨Sf, hSf, hsn⟩ := hs
  refine ⟨Sf, hSf, ?_⟩
  have e1 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).S
      = Sop D.Pl D.K (D.level n) (D.mu n z) := rfl
  have e2 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).SN
      = SNop D.Pl D.K (D.level n) (D.mu n z) := rfl
  rw [e1, e2] at hsn
  rw [hsn, sub_sub_cancel]

end FarThinKernel

/-- **The ungained thin-to-repair far kernel** (source 5323-5339, 3631-3650, 5303-5311), `k₀ = 2`. -/
theorem farThinRepKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) :
    FarThinRepKernel Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨Ca, hCa, hY'⟩ := farVelYoungBoxL2
  obtain ⟨Cc, kc, hCc, ec⟩ := repRecvConv dm dp D hst
  have hκ0 : 0 < 1 - Real.exp (-D.K.δ / 2) := by
    have h := Real.exp_lt_exp.2 (show -D.K.δ / 2 < 0 by linarith [hst.δ_pos])
    rw [Real.exp_zero] at h
    linarith
  have hmZ0 : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  refine ⟨Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi,
    kc, by positivity, ?_⟩
  filter_upwards [FarThinKernel.far_part dm dp D hst, ec,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with
    n hfar hcn hmu hle z hz T
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hε1 : (D.level n).ε ≤ 1 := hle.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hS : 0 < (D.level n).Scut D.K := Real.rpow_pos_of_pos hε _
  have hρ : 0 < (D.level n).ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hμ : -(1 / 4) < D.mu n z := by
    have := (hmu z hz).1
    linarith [hst.sigma_pos]
  obtain ⟨Sf, hSf, hFS⟩ := hfar z hz
  set Bc : ℝ := Cc * (D.level n).ν⁻¹ ^ kc * (D.level n).ε ^ (25 / 22 : ℝ) *
    Real.exp (D.K.m0 / 2 / (D.level n).ν) with hBc
  set By : ℝ := Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) *
    (D.level n).ε ^ (23 / 11 : ℝ) * (D.level n).Scut D.K ^ (23 / 22 : ℝ) with hBy
  have hBc0 : 0 ≤ Bc := by positivity
  have hBy0 : 0 ≤ By := by positivity
  -- the closed receiver
  have hac : htRhoMeasure (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K) ≪
      gainHTMeasure (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
        (D.level n).ν :=
    Measure.ae_le_iff_absolutelyContinuous.1 (NearInst.ae_gainHTMeasure _ _ _ _).ge
  have hcl : FarBridge.RecvClosed (fun v : LVel D.Pl (D.level n) =>
      htUng (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
        ((multOp D.Pl D.K (D.level n) v).snd : Chart → Ten3)) :=
    FarBridge.RecvClosed.lintegral_comp (q := 2) hac two_pos
      (FarBridge.continuous_strSnd.comp (multOp D.Pl D.K (D.level n)).continuous)
  -- the bridge
  have hfT := LateThinRep.ltr_strSum_thinPart hρ T
  have hmeas : Measurable (T.fst : Chart → Ten3) := (Lp.stronglyMeasurable _).measurable
  have hbr := FarBridge.farBridge_le_mono hρ hSf hcl hmeas hfT
    (Q := fun g => phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) 2
      (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) g))
    (fun W _ => FarBridge.phaseL2Lr_indicator_le _ _ _ _ (by norm_num) _ _)
    (B := ENNReal.ofReal (Bc * By)) (by
      intro v g hg hv
      have c2 := hcn v
      have c3 := hY' (D.level n).ε (cOf (D.level n).ν) (D.level n).ν D.K.δ
        ((D.level n).Scut D.K) (D.mu n z) hε hc hν hst.δ_pos hS hμ g hg (v : Chart → Merid)
        (Lp.stronglyMeasurable v).measurable hv
      have c2' : htUng (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
          ((multOp D.Pl D.K (D.level n) v).snd : Chart → Ten3) ≤
          ENNReal.ofReal Bc * UnforcedLeray.Short.IIIa.ltauLq (2 * (D.level n).ε *
            cOf (D.level n).ν) (22 / 3)
            (fun τ y => ‖velPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) v (τ, y)‖ₑ) := c2
      refine c2'.trans ?_
      rw [ENNReal.ofReal_mul hBc0, mul_assoc (ENNReal.ofReal Bc)]
      exact mul_le_mul_of_nonneg_left c3 zero_le)
  have hF : Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z) = Sf :=
    hFS
  rw [hF]
  refine hbr.trans ?_
  -- the source lift
  have hl := thinLiftZ1 (D.level n).ε (cOf (D.level n).ν) D.K.mZ hε hc hmZ0 (T.fst : Chart → Ten3)
    hmeas
  have hX : 0 ≤ Real.sqrt Real.pi * (D.level n).ε⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left hl zero_le).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hBc0 hBy0)]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hK := LateThinRep.ltr_eps_const hε hε1 hst.b_pos.le (rfl : (D.level n).Scut D.K = _)
  have hνi : 0 ≤ (D.level n).ν⁻¹ := inv_nonneg.2 hν.le
  have hP0 : 0 ≤ Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi *
      (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν) := by positivity
  calc Bc * By * (Real.sqrt Real.pi * (D.level n).ε⁻¹)
      = (Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi *
          (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
          ((D.level n).ε ^ (25 / 22 : ℝ) * ((D.level n).ε ^ (23 / 11 : ℝ) *
            (D.level n).Scut D.K ^ (23 / 22 : ℝ)) * (D.level n).ε⁻¹) := by
        rw [hBc, hBy]; ring
    _ ≤ (Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi *
          (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
          ((D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) * (D.level n).ε ^ (49 / 22 : ℝ)) := by
        gcongr
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
