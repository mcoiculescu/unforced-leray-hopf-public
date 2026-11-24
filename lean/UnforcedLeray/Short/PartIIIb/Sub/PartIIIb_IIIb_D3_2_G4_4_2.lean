import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.GBAdmissible
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.DatumNorm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_3
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.PlanarReferenceExists

/-!
# `PartIII-b:IIIb-D3/2/G4/4/2`: integrable majorant of the upper piece (`UpperMaj D`)

Source `the November 2 reference manuscript`: `I_T` 4584-4592; split at
`u_o = ν^{-3/2}` 4668-4690; absolute moments 4637-4693.

On the unbounded upper range `s ≥ u_o = ν^{-3/2}`, the `s ^ (-3/2)` factor in `ITdens` is integrable
on `(u_o / 2, ∞)` (`integrableOn_Ioi_rpow_of_lt`), while uniform-in-`s` control of the cell readout
`cellInt (2 M_{zz} - M_{rr})` on `[u_o, ∞)` requires large-age bounds on the train velocity and the
linearised evolution `FI.ev.U s (1.1 / ν)` (not bundled in `FlatInstData`, whose `locBdd` only
covers compact intervals `[0, T]`; see `TrainGrowth.lean`).

We establish two unconditional reduction paths to the leaf propositions in the task graph:
1. `upperMaj_of_trainGrowth` and `upperMaj_of_leaves`: from `TrainEnergyUnif` (`PartI.TrainL2Decay`)
   and `TrainFlowKinetic` (`IIIa.FullClockLongForward` and `TFKLongAll`), using the late-age Duhamel
   formula `xiDLate` (`ξ_B(s) = (T/s)^μ 𝒰(s,T) ξ_B(T)` for `s ≥ T = 1.1/ν`), real homogeneity of
   `kcLp`, and the cell Cauchy-Schwarz bound `slice_gen` (`abs_cellInt_symOuter_le`).
2. `upperMaj_of_oldAnisoLeaves`: from the `G3` old-anisotropy leaf propositions
   `G3.DuhamelDecomp D`, `G3.OldReadoutLinear D`, `G3.LaterOutputRem D`, and `G3.BareColUnit D`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF FlatSettingInst

private lemma abs_entry_le_frob_upper (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)

private lemma abs_two_zz_sub_rr_le_three_frob_upper (A : Mat3) :
    |2 * A 2 2 - A 0 0| ≤ 3 * frob A := by
  have h22 := abs_entry_le_frob_upper A 2 2
  have h00 := abs_entry_le_frob_upper A 0 0
  have htri : |2 * A 2 2 - A 0 0| ≤ |2 * A 2 2| + |A 0 0| := abs_sub _ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
  linarith

private lemma integral_avgμ_eq_cellInt_upper {c : ℝ} (hc : 0 ≤ c) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(UnforcedLeray.Cyl.avgμ c) = cellInt c F := by
  rw [UnforcedLeray.Cyl.integral_avgμ hc F, cellInt, smul_eq_mul]
  congr 1
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c) := by
    rw [UnforcedLeray.Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  rw [hmeas]

private lemma abs_cellInt_symOuter_le_upper {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (y : Xmc c m)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal E) :
    |cellInt c (fun x =>
      2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 0 0)| ≤
      6 * c⁻¹ * E * ‖kcLp y‖ := by
  set F : ℝ × ℝ → ℝ := fun x =>
    2 * IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 2 2 -
      IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x) 0 0
  have hRHS0 : 0 ≤ 6 * c⁻¹ * E * ‖kcLp y‖ := by positivity
  rw [← integral_avgμ_eq_cellInt_upper hc.le F, ← Real.norm_eq_abs]
  by_cases hInt : Integrable F (UnforcedLeray.Cyl.avgμ c)
  · have h1 : ‖∫ x, F x ∂(UnforcedLeray.Cyl.avgμ c)‖ ≤ ∫ x, ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) :=
      norm_integral_le_integral_norm F
    have h2 : ENNReal.ofReal (∫ x, ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c)) =
        ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) :=
      ofReal_integral_eq_lintegral_ofReal hInt.norm (ae_of_all _ fun _ => norm_nonneg _)
    have hpt : ∀ x, ENNReal.ofReal ‖F x‖ ≤
        ENNReal.ofReal 3 * ENNReal.ofReal (frob
          (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x))) := by
      intro x
      rw [Real.norm_eq_abs, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (abs_two_zz_sub_rr_le_three_frob_upper _)
    have h3 : ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal (6 * c⁻¹ * E * ‖kcLp y‖) := by
      calc ∫⁻ x, ENNReal.ofReal ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c)
          ≤ ∫⁻ x, ENNReal.ofReal 3 * ENNReal.ofReal (frob
              (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x)))
              ∂(UnforcedLeray.Cyl.avgμ c) := lintegral_mono hpt
        _ = ENNReal.ofReal 3 * ∫⁻ x, ENNReal.ofReal (frob
              (IIIa.symOuter (NearInst.trainMer tr (s, x)) (kcMer y x)))
              ∂(UnforcedLeray.Cyl.avgμ c) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal 3 * (2 * ENNReal.ofReal c⁻¹ *
              UnforcedLeray.Train.cellL2 c (tr.v s) * ENNReal.ofReal ‖kcLp y‖) := by
            gcongr
            exact slice_gen m tr s y
        _ ≤ ENNReal.ofReal 3 * (2 * ENNReal.ofReal c⁻¹ *
              ENNReal.ofReal E * ENNReal.ofReal ‖kcLp y‖) := by
            gcongr
        _ = ENNReal.ofReal (6 * c⁻¹ * E * ‖kcLp y‖) := by
            have e : 6 * c⁻¹ * E * ‖kcLp y‖ = 3 * (2 * c⁻¹ * E * ‖kcLp y‖) := by ring
            rw [e, ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    have h4 : ∫ x, ‖F x‖ ∂(UnforcedLeray.Cyl.avgμ c) ≤ 6 * c⁻¹ * E * ‖kcLp y‖ :=
      (ENNReal.ofReal_le_ofReal_iff hRHS0).1 (h2 ▸ h3)
    exact h1.trans h4
  · rw [integral_undef hInt, norm_zero]
    exact hRHS0

private lemma kcLp_smul_real {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (r : ℝ) (ξ : Xmc c m) :
    kcLp ((r : ℂ) • ξ) = r • kcLp ξ := by
  have hm : 1 ≤ m := one_le_of_fact
  have hsm : ∫ x in B0579.cell c, (r • reX ξ.1) x = 0 := by
    rw [← kcMerLinear_reX_smul]
    exact reX_circ ((r : ℂ) • ξ)
  calc kcLp ((r : ℂ) • ξ)
      = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
          (reX ((r : ℂ) • ξ).1) (reX_circ ((r : ℂ) • ξ)) := rfl
    _ = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
          (r • reX ξ.1) hsm :=
        kcMerLinear_rbs_congr hm (kcMerLinear_reX_smul r ξ)
    _ = r • UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm (reX ξ.1)
          (reX_circ ξ) :=
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart_smul hm r
          (reX ξ.1) (reX_circ ξ) hsm
    _ = r • kcLp ξ := rfl

private lemma integrableOn_duhIntegrand_of_bclass {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {μ a : ℝ} (hμ : 0 ≤ μ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (DuhIntegrand FI μ B T) (Ioc 0 T) := by
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    FI.src.H_cont.continuousOn
  obtain ⟨Cr, hCr⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    FI.src.R_cont.continuousOn
  set Csrc : ℝ := |Ch| + |Cr|
  have hCsrc0 : 0 ≤ Csrc := by positivity
  obtain ⟨Cs, hCs⟩ := FI.ev.locBdd T
  have hCs0 : 0 ≤ Cs := (norm_nonneg (FI.ev.U 0 0)).trans (hCs 0 0 le_rfl le_rfl hT.le)
  have haeB : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)),
      matNorm (B t) ≤ bNorm a B * (Real.exp (a * t) * t ^ (3 / 2 : ℝ)) :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (bclassAeBound a ν B hB)
  have hbN0 : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  set K : ℝ := T ^ μ * (Cs * (3 * Csrc * (bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ)))))
  have hd : AEStronglyMeasurable (fun t : ℝ => Bd (B t)) (volume.restrict (Ioc 0 T)) :=
    (((hB.1 0 0).sub (hB.1 2 2)).div_const 2).aestronglyMeasurable
  have he : AEStronglyMeasurable (fun t : ℝ => Be (B t)) (volume.restrict (Ioc 0 T)) :=
    (((hB.1 0 2).add (hB.1 2 0)).div_const 2).aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun t : ℝ => Bbeta (B t)) (volume.restrict (Ioc 0 T)) :=
    (((hB.1 0 0).add (hB.1 2 2)).div_const 2).aestronglyMeasurable
  refine IntegrableOn.of_bound measure_Ioc_lt_top (duhIntegrand_aesm FI μ B T hd he hb) K ?_
  filter_upwards [haeB, ae_restrict_mem measurableSet_Ioc] with t htB ht
  unfold DuhIntegrand
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hg1 : ‖gBD FI B t‖ ≤ 3 * Csrc * matNorm (B t) := by
    refine gBPointwise (actualFlatSetting FI (fun _ => 0) 0) T Csrc (fun r hr => ?_) B t htIcc
    have hHr : ‖FI.src.H r‖ ≤ Csrc :=
      (hCh r hr).trans ((le_abs_self _).trans (by linarith [abs_nonneg Cr]))
    have hRr : ‖FI.src.R r‖ ≤ Csrc :=
      (hCr r hr).trans ((le_abs_self _).trans (by linarith [abs_nonneg Ch]))
    change ‖FI.src.H r‖ ≤ Csrc ∧ ‖conjX (FI.src.H r)‖ ≤ Csrc ∧ ‖FI.src.R r‖ ≤ Csrc
    rw [norm_conjX]
    exact ⟨hHr, hHr, hRr⟩
  have hexp : Real.exp (a * t) ≤ Real.exp (|a| * T) := by
    apply Real.exp_le_exp.2
    calc a * t ≤ |a| * t := mul_le_mul_of_nonneg_right (le_abs_self a) ht.1.le
      _ ≤ |a| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg a)
  have ht32 : t ^ (3 / 2 : ℝ) ≤ T ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ht.1.le ht.2 (by norm_num)
  have htμ : t ^ μ ≤ T ^ μ :=
    Real.rpow_le_rpow ht.1.le ht.2 hμ
  have hB_le : matNorm (B t) ≤ bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ)) :=
    htB.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hexp ht32 (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le) hbN0)
  have hg2 : ‖gBD FI B t‖ ≤
      3 * Csrc * (bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ))) :=
    hg1.trans (mul_le_mul_of_nonneg_left hB_le (by positivity))
  have hU : ‖FI.ev.U T t (gBD FI B t)‖ ≤
      Cs * (3 * Csrc * (bNorm a B * (Real.exp (|a| * T) * T ^ (3 / 2 : ℝ)))) :=
    ((FI.ev.U T t).le_opNorm _).trans
      (mul_le_mul (hCs T t ht.1.le ht.2 le_rfl) hg2 (norm_nonneg _) hCs0)
  exact mul_le_mul htμ hU (norm_nonneg _) (Real.rpow_nonneg hT.le _)

/-- **Reduction 1 (`TrainGrowth` path)**: `UpperMaj D` follows from uniform train energy
(`TrainEnergyUnif`) and the kinetic bound on the train evolution (`TrainFlowKinetic`). -/
theorem upperMaj_of_trainGrowth (D : SeqData)
    (hE : TrainEnergyUnif) (hK : ∀ (m : ℝ) [Fact (1 < m)], TrainFlowKinetic m) :
    UpperMaj D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨ν₁, hν₁, hK'⟩ := hK m hm
  obtain ⟨ν₂, hν₂, E, hE'⟩ := hE
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hν_ev : ∀ᶠ n : ℕ in atTop, nu D n < min (min ν₁ ν₂) (1 / 4) :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually
      (gt_mem_nhds (lt_min (lt_min hν₁ hν₂) (by norm_num)))
  filter_upwards [hS, hmu_ev, hν_ev] with n ⟨FI, hSn⟩ hmu_z hν_lt
  intro z hz B hB
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hν₁' : nu D n ≤ ν₁ :=
    (hν_lt.le.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hν₂' : nu D n ≤ ν₂ :=
    (hν_lt.le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hν4 : nu D n ≤ 1 / 4 := hν_lt.le.trans (min_le_right _ _)
  have hμ0 : 0 ≤ D.mu n z := by
    have := (hmu_z z hz).1
    linarith [hst.sigma_pos]
  have hc0 : 0 < cOf (nu D n) := cOf_pos hν
  have : Fact (0 < cOf (nu D n)) := ⟨hc0⟩
  obtain ⟨Ck, hCk⟩ := hK' κ (nu D n) hν hν₁' (D.train n) (D.train_buc n) FI
  set E' : ℝ := max E 0
  set Ck' : ℝ := max Ck 0
  have hE'0 : 0 ≤ E' := le_max_right _ _
  have hCk'0 : 0 ≤ Ck' := le_max_right _ _
  set T : ℝ := 11 / 10 / nu D n
  have hTpos : 0 < T := by positivity
  set w : Xmc (cOf (nu D n)) m := xiD FI (D.mu n z : ℂ) B T
  set uo : ℝ := nu D n ^ (-(3 / 2 : ℝ))
  have huo_pos : 0 < uo := Real.rpow_pos_of_pos hν _
  have hTuo : T ≤ uo := by
    have hT2 : T ≤ 2 / nu D n := div_le_div_of_nonneg_right (by norm_num) hν.le
    exact hT2.trans (G3.two_div_le_uo hν hν4)
  have hBz : ∀ t, T < t → B t = 0 := by
    intro t ht
    have ht' : (1.1 : ℝ) / nu D n < t := by
      show (1.1 : ℝ) / nu D n < t
      have : (1.1 : ℝ) = 11 / 10 := by norm_num
      rw [this]
      exact ht
    exact hB.2.2.2.1 t (fun h => not_lt.2 h.2.le ht')
  have hIT : IntegrableOn (DuhIntegrand FI (D.mu n z) B T) (Ioc 0 T) :=
    integrableOn_duhIntegrand_of_bclass FI hμ0 hB hTpos
  set Cmaj : ℝ := 6 * (cOf (nu D n))⁻¹ * E' * (Ck' * ‖w‖)
  have hCmaj0 : 0 ≤ Cmaj := by positivity
  have ha0 : 0 < uo / 2 := half_pos huo_pos
  have hsub : Ioi (uo / 2) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ha0.le
  refine ⟨Set.indicator (Ioi (uo / 2)) (fun s => Cmaj * s ^ (-(3 / 2 : ℝ))), ?_, ?_⟩
  · rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.2 hsub]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) ha0).const_mul Cmaj
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    by_cases hu : nu D n ^ (-(3 / 2 : ℝ)) ≤ s
    · have hs_mem : s ∈ Ioi (uo / 2) := mem_Ioi.2 (lt_of_lt_of_le (half_lt_self huo_pos) hu)
      have hTs : T ≤ s := hTuo.trans hu
      have hlate : xiD FI (D.mu n z : ℂ) B s =
          ((s : ℂ) ^ (-(D.mu n z : ℂ)) * (T : ℂ) ^ (D.mu n z : ℂ)) • FI.ev.U s T w :=
        xiDLate m κ (nu D n) (D.mu n z) hν (D.train n) FI B T s hTpos hTs hBz hIT
      set ρ : ℝ := s ^ (-D.mu n z) * T ^ D.mu n z
      have hρ_eq : (s : ℂ) ^ (-(D.mu n z : ℂ)) * (T : ℂ) ^ (D.mu n z : ℂ) = (ρ : ℂ) := by
        simp only [ρ, Complex.ofReal_mul, Complex.ofReal_cpow hs0.le,
          Complex.ofReal_cpow hTpos.le, Complex.ofReal_neg]
      have hρ0 : 0 ≤ ρ :=
        mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hTpos.le _)
      have hρ1 : ρ ≤ 1 := by
        simp only [ρ]
        rw [Real.rpow_neg hs0.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hs0 _), mul_one]
        exact Real.rpow_le_rpow hTpos.le hTs hμ0
      have hkc_norm : ‖kcLp (xiD FI (D.mu n z : ℂ) B s)‖ ≤ Ck' * ‖w‖ := by
        rw [hlate, hρ_eq, kcLp_smul_real, norm_smul, Real.norm_of_nonneg hρ0]
        calc ρ * ‖kcLp (FI.ev.U s T w)‖
            ≤ 1 * ‖kcLp (FI.ev.U s T w)‖ :=
              mul_le_mul_of_nonneg_right hρ1 (norm_nonneg _)
          _ = ‖kcLp (FI.ev.U s T w)‖ := one_mul _
          _ ≤ Ck * ‖w‖ := hCk s hTs w
          _ ≤ Ck' * ‖w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      have hcellL2 : UnforcedLeray.Train.cellL2 (cOf (nu D n)) ((D.train n).v s) ≤
          ENNReal.ofReal E' :=
        (hE' (nu D n) hν hν₂' (D.train n) (D.train_buc n) s hs0.le).trans
          (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      have hcell : |cellInt (cOf (nu D n)) (fun x =>
          2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
            (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 2 2 -
          IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
            (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 0 0)| ≤ Cmaj := by
        exact (abs_cellInt_symOuter_le_upper hc0 (D.train n) s
          (xiD FI (D.mu n z : ℂ) B s) hE'0 hcellL2).trans
          (mul_le_mul_of_nonneg_left hkc_norm (by positivity))
      have key : upperPiece D S n z B s =
          (S n).ITdens (fun s => (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s)) s := by
        unfold upperPiece FlatSetting.ITdens
        simp [hu]
      rw [key, indicator_of_mem hs_mem, hSn, Real.norm_eq_abs]
      change |D.K.χo (nu D n * s) * s ^ (-(3 / 2 : ℝ)) *
        cellInt (cOf (nu D n)) (fun x =>
          2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
            (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 2 2 -
          IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
            (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 0 0)| ≤
        Cmaj * s ^ (-(3 / 2 : ℝ))
      have hχ_abs : |D.K.χo (nu D n * s)| ≤ 1 := by
        rcases D.K.hχo.range (nu D n * s) with ⟨h0, h1⟩
        rw [abs_of_nonneg h0]
        exact h1
      have hpow0 : 0 ≤ s ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
      rw [abs_mul, abs_mul, abs_of_nonneg hpow0]
      calc |D.K.χo (nu D n * s)| * s ^ (-(3 / 2 : ℝ)) *
            |cellInt (cOf (nu D n)) (fun x =>
              2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
                (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 2 2 -
              IIIa.symOuter (NearInst.trainMer (D.train n) (s, x))
                (kcMer (xiD FI (D.mu n z : ℂ) B s) x) 0 0)|
          ≤ 1 * s ^ (-(3 / 2 : ℝ)) * Cmaj := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hχ_abs hpow0) hcell
              (abs_nonneg _) (mul_nonneg zero_le_one hpow0)
        _ = Cmaj * s ^ (-(3 / 2 : ℝ)) := by ring
    · have key0 : upperPiece D S n z B s = 0 := by
        unfold upperPiece FlatSetting.ITdens
        simp [hu, cellInt]
      rw [key0, norm_zero]
      exact Set.indicator_nonneg (fun r hr =>
        mul_nonneg hCmaj0 (Real.rpow_nonneg (ha0.trans hr).le _)) s

/-- **Reduction 1b (to the three unproved leaf propositions in the `TrainGrowth` subtree)**:
`UpperMaj D` from `PartI.TrainL2Decay`, `IIIa.FullClockLongForward`, and `TFKLongAll`. -/
theorem upperMaj_of_leaves (D : SeqData)
    (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hLong : ∀ (m : ℝ) [Fact (1 < m)], TFKLongAll m) :
    UpperMaj D :=
  upperMaj_of_trainGrowth D (trainEnergyUnif_of hL2) fun m _ =>
    trainFlowKinetic_of m
      (tfkShortAll_of m hLF NearInst.Delta.planarReferenceExists (tfkKcEmbed m) (tfkDatumNorm m))
      (hLong m)

/-- **Reduction 2 (`G3` old-anisotropy path)**: `UpperMaj D` follows from the `G3` leaves
`DuhamelDecomp`, `OldReadoutLinear`, `LaterOutputRem`, and `BareColUnit`. -/
theorem upperMaj_of_oldAnisoLeaves (D : SeqData)
    (hDuh : G3.DuhamelDecomp D) (hLin : G3.OldReadoutLinear D)
    (hRem : G3.LaterOutputRem D) (hU : G3.BareColUnit D) :
    UpperMaj D := by
  have hBare := G3.bareColAniso_of_unit D hLin hU
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨_, _, Nduh, _, _, hNduh⟩ := hDuh dm dp hst κ hκ m hm S hS
  obtain ⟨Nlin, hNlin⟩ := hLin dm dp hst κ hκ m hm S hS
  obtain ⟨_, Nrem, _, hNrem⟩ := hRem dm dp hst κ hκ m hm S hS
  obtain ⟨_, _, Nbare, _, _, _, hNbare⟩ := hBare dm dp hst κ hκ m hm S hS
  have hν_ev : ∀ᶠ n : ℕ in atTop, nu D n < 1 / 4 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [eventually_ge_atTop Nduh, eventually_ge_atTop Nlin,
    eventually_ge_atTop Nrem, eventually_ge_atTop Nbare, hν_ev] with
    n hnduh hnlin hnrem hnbare hν4
  intro z hz B hB
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have huo : 2 / nu D n ≤ nu D n ^ (-(3 / 2 : ℝ)) := G3.two_div_le_uo hν hν4.le
  obtain ⟨hxi_eq, _, _⟩ := hNduh n hnduh z hz B hB
  set aPlus := (S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B
  set rH := G3.duhRemH D (S n) n z B
  obtain ⟨hint_bare, _⟩ := hNbare n hnbare z hz aPlus
  obtain ⟨hint_rem, _⟩ := hNrem n hnrem z hz rH
  have hdens_split : upperPiece D S n z B =
      fun s => G3.itOldDens (S n) (nu D n) (G3.xiBare (S n) (D.mu n z) aPlus) s +
        G3.itOldDens (S n) (nu D n) (G3.xiFromH (S n) (nu D n) (D.mu n z) rH) s := by
    funext s
    unfold upperPiece G3.itOldDens FlatSetting.ITdens
    by_cases hs : nu D n ^ (-(3 / 2 : ℝ)) ≤ s
    · simp only [ite_eq_left_iff.2 fun h => (h hs).elim]
      rw [hxi_eq s (le_trans huo hs), (hNlin n hnlin s _ _ 0).1]
      ring
    · simp only [ite_eq_right_iff.2 fun h => (hs h).elim, cellInt, Matrix.zero_apply,
        mul_zero, sub_self, integral_zero, add_zero]
  have hint : Integrable (upperPiece D S n z B) (volume.restrict (Ioi (0 : ℝ))) := by
    rw [hdens_split]
    exact hint_bare.add hint_rem
  refine ⟨fun s => ‖upperPiece D S n z B s‖, hint.norm, Eventually.of_forall fun _ => le_rfl⟩

alias flatUpperMaj_of_trainGrowth := upperMaj_of_trainGrowth
alias flatUpperMaj_of_leaves := upperMaj_of_leaves
alias flatUpperMaj_of_oldAnisoLeaves := upperMaj_of_oldAnisoLeaves

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
