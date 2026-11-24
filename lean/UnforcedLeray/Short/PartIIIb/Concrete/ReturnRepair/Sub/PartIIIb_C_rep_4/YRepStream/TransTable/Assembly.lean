import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.Props

/-!
# `PartIII-b:C/rep/4/4/1/org/3/org` (c): the repair-source transition table from its leaves

Source `the November 2 reference manuscript` 5312-5341 (both transitions, their
support `0.8/ν < s < 1/ν`, the late-output gain `e^{-4γ/(9ν)}`, the repair-source row of the table
`ε^{63/22}e^{m₀/ν}` / `ε^{79/22}e^{3m₀/(2ν)}` with the factor `G(w)|N_ν|e^{-4γ/(9ν)}`), 5169-5176
(`repair:source` `F_r ≤ P_νρR|N_ν|G(w)`), 4171-4214 (the Ward fields), 2697-2713 (the split stress
norm), 5607 (order of choice).

`transRepTable_of` proves `TransRepTable` (`YRepStream/Trans.lean`) with the `S`-degree `k₁ = 0`
(chosen before everything: both transitions live on the bounded window `s ≤ 1/ν`, so no power of
`S = ε^{-b}` is needed) from:

* `OldRepIsRep` (`Sub/PartIII-b_C_rep_5_2_2TransOrg.lean`; `g₁ = 0`, `g₂ = repSrcTen w`), with
  `tt_reps_ae`, `tt_oldPhys_ae`, `sepWCongrAE`: for any representatives the transition field is
  `sepTrans` of the separated representative `T` of `RepairSepBridge` (proved);
* `TransVanishOff` (proved): the field vanishes at ages `s < 0.8/ν`, so does `M_Uv` (exact
  multiplier, `concreteBase_isExactMultiplier`), and the gain transfers `lrt_gainZ1_le`,
  `tt_gainHT_le` give the factor `e^{-4γ/(9ν)}` (5318);
* `TransSepDom` (`|sepTrans| ≤ P_ν transMaj`) and `tt_pt_le`, `tt_L2_le`: the ungained receivers
  are at most `2P_ν` times the chart majorants `multMaj R V transMaj`, `multMaj R r_b transMaj`;
* `TransMajThin`, `TransMajRep` (`TransTable/Props.lean`): `P_νε^{79/22}‖T‖` and
  `P_νε^{95/22}e^{m₀/(2ν)}‖T‖`, `‖T‖ = ‖T‖_{L²_τL^{22/19}} ≤ F_r` (`RepairSepBridge`);
* `repairSource` (proved): `F_r ≤ P_νρR|N_ν|G(w)`; then `ε^{79/22}ρR = ε^{63/22}e^{m₀/ν}` and
  `ε^{95/22}e^{m₀/(2ν)}ρR = ε^{79/22}e^{3m₀/(2ν)}` (`tt_exp_thin`, `tt_exp_rep`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ε^{79/22}·ρ·ε⁻¹ = ε^{63/22}e^{m₀/ν}` (source 5337-5338, `ρ = ε^{3/11}e^{m₀/ν}`). -/
theorem tt_exp_thin {ε ν m0 : ℝ} (hε : 0 < ε) :
    ε ^ (79 / 22 : ℝ) * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν)) * ε⁻¹ =
      ε ^ (63 / 22 : ℝ) * Real.exp (m0 / ν) := by
  have e : ε ^ (63 / 22 : ℝ) = ε ^ (79 / 22 : ℝ) * ε ^ (3 / 11 : ℝ) * ε⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε]; norm_num
  rw [e]; ring

/-- `ε^{95/22}e^{m₀/(2ν)}·ρ·ε⁻¹ = ε^{79/22}e^{3m₀/(2ν)}` (source 5338-5339). -/
theorem tt_exp_rep {ε ν m0 : ℝ} (hε : 0 < ε) :
    ε ^ (95 / 22 : ℝ) * Real.exp (m0 / 2 / ν) * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν)) * ε⁻¹ =
      ε ^ (79 / 22 : ℝ) * Real.exp (3 * m0 / 2 / ν) := by
  have e : ε ^ (79 / 22 : ℝ) = ε ^ (95 / 22 : ℝ) * ε ^ (3 / 11 : ℝ) * ε⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε]; norm_num
  have e2 : Real.exp (3 * m0 / 2 / ν) = Real.exp (m0 / 2 / ν) * Real.exp (m0 / ν) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e, e2]; ring

/-- **The repair-source transition table at one level** (source 5312-5341, 5169-5176), with
`k₁ = 0`. -/
theorem tt_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hC0 : 0 < K.C0) (hγ : 0 ≤ gRate Pl) (hmZ : 0 ≤ K.mZ)
    (hν1 : L.ν ≤ 1) (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hI : OldRepIsRep) (hV : TransVanishOff) (hB : RepairSepBridge)
    {Cd : ℝ} {kd : ℕ} (hCd : 0 ≤ Cd)
    (hDom : ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T →
      SepMoment (2 * L.ε * cOf L.ν) T → IsAxiSource T → ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
        ‖sepTrans L.ν μ L.ε⁻¹ K.χy T τ y‖ₑ ≤
          ENNReal.ofReal (Cd * L.ν⁻¹ ^ kd) * transMaj L.ν L.ε⁻¹ (IIIa.srcNorm T) τ y)
    {Ct : ℝ} {kt : ℕ} (hCt : 0 ≤ Ct)
    (hThin : ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T →
      SepMoment (2 * L.ε * cOf L.ν) T → IsAxiSource T →
      z1Maj (cOf L.ν) K.mZ (multMaj L.ε⁻¹ L.V (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm T))) ≤
        ENNReal.ofReal (Ct * L.ν⁻¹ ^ kt * L.ε ^ (79 / 22 : ℝ)) *
          IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T))
    {Cr : ℝ} {kr : ℕ} (hCr : 0 ≤ Cr)
    (hRep : ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T →
      SepMoment (2 * L.ε * cOf L.ν) T → IsAxiSource T →
      htMaj (cOf L.ν) (L.ρb Pl K) (multMaj L.ε⁻¹ L.rb (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm T))) ≤
        ENNReal.ofReal (Cr * L.ν⁻¹ ^ kr * L.ε ^ (95 / 22 : ℝ) * Real.exp (K.m0 / 2 / L.ν)) *
          IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T))
    {Cs : ℝ} {ks : ℕ} (hSrc : RepairSourceAt Pl K L Cs ks) :
    TransRepTableAt Pl K L μ 0 (2 * Cd * (Ct + Cr) * |Cs|) (kd + (kt + kr) + ks) := by
  intro w g₁ g₂ hg v hv
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hR0 : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hι0 : 0 ≤ L.ν⁻¹ := inv_nonneg.2 hν.le
  have hι : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hρb : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 := (L.params Pl).ν_pos
    have h2 := (L.params Pl).ε_pos
    exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos h1 _))) (Real.exp_pos _))
      (Real.rpow_pos_of_pos h2 _)
  obtain ⟨T, hTS, hTM, hTA, hTW, hTN⟩ := hB (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo
    K.hχo hc hρb hmZ hν hε (multOp Pl K L w)
  -- the transition field of any representatives is that of the separated source `T`
  have hae := tt_oldPhys_ae hR0 hc (tt_reps_ae hI Pl K L hρb w hg)
  have hF : transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂) = sepTrans L.ν μ L.ε⁻¹ K.χy T := by
    rw [transField_eq_sepTrans]
    refine sepTrans_congr (fun μ' y τ => ?_)
    rw [← hTW μ' y τ]
    exact sepWCongrAE L.ν μ' _ _ hae y τ
  have hcoef : (v : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) := by
    rw [← hF]; exact hv
  -- support: ages `s ≥ 0.8/ν`
  have hvan : ∀ p : Chart, 0 < p.1 → L.ν * p.1 < 4 / 5 →
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p = 0 := by
    intro p hp hlt
    have hy : 0 < ϱ (NearInst.chartY L.ε⁻¹ p) := by
      rw [ϱ_chartY hR0 hp]; positivity
    refine coefOf_eq_zero_of ?_
    exact hV L.ν μ L.ε⁻¹ K.χy hχ hν hR0 T _ _ hy (Or.inl (by rw [age_chartY hR0 hp]; exact hlt))
  have h3a : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)), (v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p ∧ 0 < p.1 := by
    rw [← NearInst.ae_bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
    exact Filter.Eventually.and hcoef (bodyMeasure_ae_pos _ _ _)
  have h3b : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ), (v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p ∧ 0 < p.1 :=
    (NearInst.CoeffMult.z1_ac hc K.mZ).ae_le h3a
  have h3h : ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)), (v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p ∧ 0 < p.1 := by
    rw [NearInst.ae_htRhoMeasure hρb, ← NearInst.ae_z1Measure _ K.mZ]; exact h3b
  have h3z : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν), (v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p ∧ 0 < p.1 := by
    rw [NearInst.ae_gainZ1Measure]; exact h3b
  have h3g : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν), (v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p ∧ 0 < p.1 := by
    rw [NearInst.ae_gainHTMeasure]; exact h3h
  -- the exact multiplier
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have m1 : ((multOp Pl K L v).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
      (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((v : Chart → Merid) p)) :=
    (hEx v).1
  have m2 : ((multOp Pl K L v).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν)
      (L.ρb Pl K) (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) ((v : Chart → Merid) p)) :=
    (hEx v).2
  have hlt : ∀ p : Chart, p.1 < 4 / 5 / L.ν → L.ν * p.1 < 4 / 5 := by
    intro p hp; rw [mul_comm]; exact (lt_div_iff₀ hν).1 hp
  have s1 : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν), p.1 < 4 / 5 / L.ν →
      ((multOp Pl K L v).fst : Chart → Ten3) p = 0 := by
    filter_upwards [m1, h3z] with p e1 e2 hp
    rw [e1, e2.1, hvan p e2.2 (hlt p hp)]
    exact tt_ten3_symOuter_zero _
  have s2 : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν), p.1 < 4 / 5 / L.ν →
      ((multOp Pl K L v).snd : Chart → Ten3) p = 0 := by
    filter_upwards [m2, h3g] with p e1 e2 hp
    rw [e1, e2.1, hvan p e2.2 (hlt p hp)]
    exact tt_ten3_symOuter_zero _
  -- the late-output gain (5318)
  have hE0 : 0 ≤ Real.exp (-(4 * gRate Pl / 9) / L.ν) := (Real.exp_pos _).le
  have G1 := lrt_gainZ1_le hE0 (fun p hp => lrt_ginv_late hγ hν p hp) (multOp Pl K L v).fst s1
  have G2 := tt_gainHT_le hE0 (fun p hp => lrt_ginv_late hγ hν p hp) (multOp Pl K L v).snd s2
  -- the ungained receivers below the chart majorants
  have hK0 : 0 ≤ Cd * L.ν⁻¹ ^ kd := mul_nonneg hCd (pow_nonneg hι0 _)
  have Z1 : z1Ung (cOf L.ν) K.mZ ((multOp Pl K L v).fst : Chart → Ten3) ≤
      ENNReal.ofReal (2 * (Cd * L.ν⁻¹ ^ kd)) *
        z1Maj (cOf L.ν) K.mZ (multMaj L.ε⁻¹ L.V (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm T))) := by
    unfold z1Ung z1Maj
    refine tt_L2_le (z1Measure (cOf L.ν) K.mZ) ?_
    have m1z : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ), ((multOp Pl K L v).fst : Chart → Ten3) p =
        NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((v : Chart → Merid) p)) := by
      rw [← NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]; exact m1
    filter_upwards [m1z, h3b] with p e1 e2
    rw [e1, e2.1]
    exact tt_pt_le _ _ _ p hK0
      (hDom T hTS hTM hTA _ _ (by rw [ϱ_chartY hR0 e2.2]; exact div_pos hR0 (Real.sqrt_pos.2 e2.2)))
  have H1 : htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L v).snd : Chart → Ten3) ≤
      ENNReal.ofReal (2 * (Cd * L.ν⁻¹ ^ kd)) *
        htMaj (cOf L.ν) (L.ρb Pl K) (multMaj L.ε⁻¹ L.rb
          (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm T))) := by
    unfold htUng htMaj
    refine tt_L2_le (htRhoMeasure (cOf L.ν) (L.ρb Pl K)) ?_
    have m2z : ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)),
        ((multOp Pl K L v).snd : Chart → Ten3) p =
        NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) ((v : Chart → Merid) p)) := by
      rw [← NearInst.ae_gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]; exact m2
    filter_upwards [m2z, h3h] with p e1 e2
    rw [e1, e2.1]
    exact tt_pt_le _ _ _ p hK0
      (hDom T hTS hTM hTA _ _ (by rw [ϱ_chartY hR0 e2.2]; exact div_pos hR0 (Real.sqrt_pos.2 e2.2)))
  -- `repair:source` (5169-5176)
  have hρ : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hN : 0 ≤ gaugeN Pl L := norm_nonneg _
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hX : 0 ≤ |Cs| * L.ν⁻¹ ^ ks * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖ := by positivity
  have Lb : IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) ≤
      ENNReal.ofReal (|Cs| * L.ν⁻¹ ^ ks * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by
    refine hTN.trans ((hSrc w).trans (ENNReal.ofReal_le_ofReal ?_))
    have h0 : 0 ≤ L.ν⁻¹ ^ ks * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖ := by positivity
    have h := mul_le_mul_of_nonneg_right (le_abs_self Cs) h0
    calc Cs * L.ν⁻¹ ^ ks * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖
        = Cs * (L.ν⁻¹ ^ ks * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by ring
      _ ≤ |Cs| * (L.ν⁻¹ ^ ks * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := h
      _ = _ := by ring
  have he2 : 0 ≤ 2 * (Cd * L.ν⁻¹ ^ kd) := mul_nonneg zero_le_two hK0
  have ha := tt_chain G1 Z1 (hThin T hTS hTM hTA) Lb hE0 he2
    (mul_nonneg (mul_nonneg hCt (pow_nonneg hι0 _)) (Real.rpow_nonneg hε.le _)) hX
  have hb := tt_chain G2 H1 (hRep T hTS hTM hTA) Lb hE0 he2
    (mul_nonneg (mul_nonneg (mul_nonneg hCr (pow_nonneg hι0 _)) (Real.rpow_nonneg hε.le _))
      (Real.exp_pos _).le) hX
  -- bookkeeping
  set E := Real.exp (-(4 * gRate Pl / 9) / L.ν) with hEdef
  set A1 := L.ε ^ (63 / 22 : ℝ) * Real.exp (K.m0 / L.ν) with hA1def
  set A2 := L.ε ^ (79 / 22 : ℝ) * Real.exp (3 * K.m0 / 2 / L.ν) with hA2def
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  set Q := E * (2 * (Cd * L.ν⁻¹ ^ kd)) * (|Cs| * L.ν⁻¹ ^ ks * gaugeN Pl L * ‖w‖) with hQdef
  have hQ : 0 ≤ Q := by positivity
  have ha' : ‖(multOp Pl K L v).fst‖ ≤ Q * (Ct * L.ν⁻¹ ^ kt * A1) := by
    refine ha.trans_eq ?_
    rw [hQdef, hA1def, ← tt_exp_thin hε]
    unfold rhoRep
    ring
  have hb' : ‖(multOp Pl K L v).snd‖ ≤ Q * (Cr * L.ν⁻¹ ^ kr * A2) := by
    refine hb.trans_eq ?_
    rw [hQdef, hA2def, ← tt_exp_rep hε]
    unfold rhoRep
    ring
  have pt : L.ν⁻¹ ^ kt ≤ L.ν⁻¹ ^ (kt + kr) := pow_le_pow_right₀ hι (Nat.le_add_right _ _)
  have pr : L.ν⁻¹ ^ kr ≤ L.ν⁻¹ ^ (kt + kr) := pow_le_pow_right₀ hι (Nat.le_add_left _ _)
  have hsum : Ct * L.ν⁻¹ ^ kt * A1 + Cr * L.ν⁻¹ ^ kr * A2 ≤
      (Ct + Cr) * L.ν⁻¹ ^ (kt + kr) * (A1 + A2) := by
    have h1 : Ct * L.ν⁻¹ ^ kt * A1 ≤ Ct * L.ν⁻¹ ^ (kt + kr) * A1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pt hCt) hA1
    have h2 : Cr * L.ν⁻¹ ^ kr * A2 ≤ Cr * L.ν⁻¹ ^ (kt + kr) * A2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pr hCr) hA2
    have h3 : 0 ≤ Ct * L.ν⁻¹ ^ (kt + kr) * A2 := by positivity
    have h4 : 0 ≤ Cr * L.ν⁻¹ ^ (kt + kr) * A1 := by positivity
    have e : (Ct + Cr) * L.ν⁻¹ ^ (kt + kr) * (A1 + A2) =
        Ct * L.ν⁻¹ ^ (kt + kr) * A1 + Cr * L.ν⁻¹ ^ (kt + kr) * A2 +
          (Ct * L.ν⁻¹ ^ (kt + kr) * A2 + Cr * L.ν⁻¹ ^ (kt + kr) * A1) := by ring
    rw [e]; linarith
  rw [WithLp.prod_norm_eq_of_L1]
  calc ‖(multOp Pl K L v).fst‖ + ‖(multOp Pl K L v).snd‖
      ≤ Q * (Ct * L.ν⁻¹ ^ kt * A1) + Q * (Cr * L.ν⁻¹ ^ kr * A2) := add_le_add ha' hb'
    _ = Q * (Ct * L.ν⁻¹ ^ kt * A1 + Cr * L.ν⁻¹ ^ kr * A2) := by ring
    _ ≤ Q * ((Ct + Cr) * L.ν⁻¹ ^ (kt + kr) * (A1 + A2)) := mul_le_mul_of_nonneg_left hsum hQ
    _ = _ := by
      rw [hQdef]
      simp only [Nat.cast_zero, zero_mul, neg_zero, Real.rpow_zero, pow_add]
      ring

/-- **The repair-source transition table** (source 5312-5341, 5169-5176, 5607) from its leaves:
`OldRepIsRep`, `TransVanishOff` (proved), `RepairSepBridge` (proved), `TransSepDom`, `TransMajThin`,
`TransMajRep`; the `S`-degree is `k₁ = 0`. -/
theorem transRepTable_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hI : OldRepIsRep)
    (hV : TransVanishOff) (hB : RepairSepBridge) (hD : TransSepDom)
    (hT : TransMajThin dm dp) (hR : TransMajRep dm dp) : TransRepTable Pl σ₀ mZ dm dp := by
  refine ⟨0, fun D _ _ _ hst => ?_⟩
  have hσ' : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨Cd, kd, hCd, hDd⟩ := hD (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ' D.K.χy hst.chiY
  obtain ⟨Ct, kt, hCt, hTt⟩ := hT D hst
  obtain ⟨Cr, kr, hCr, hRr⟩ := hR D hst
  obtain ⟨Cs, ks, hS⟩ := repairSource D hst
  refine ⟨2 * Cd * (Ct + Cr) * |Cs|, kd + (kt + kr) + ks, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hev1, hev2, hst.pins, hst.near, hTt, hRr, hS] with
    n e1 e2 pins near ht hr hs z hz
  have hν := (D.level n).ν_pos
  have hε := (D.level n).ε_pos
  have hR1 : 1 ≤ (D.level n).ε⁻¹ := (one_le_inv₀ hε).2 e2.2
  have hPp : 0 < 2 * (D.level n).ε * cOf (D.level n).ν := by
    have := cOf_pos hν; positivity
  exact tt_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hst.C0_pos hst.gamma_pos.le
    (by linarith [hst.mZ_gt]) e2.1 (near z hz) (pins z hz).split hI hV hB hCd
    (fun T hTS hTM hTA τ y hy => hDd _ _ _ _ hν e2.1 hR1 hPp (e1 z hz) T hTS hTM hTA τ y hy)
    hCt ht hCr hr hs

end UnforcedLeray.Short.PartIIIb.Concrete
