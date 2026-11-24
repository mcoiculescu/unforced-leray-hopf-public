import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.TrainGrowth

/-!
# Old absolute stress of the train evolution from the end of the source band

Source of record: `the November 2 reference manuscript`, lines 4677-4694 and
3277-3289.  Task `PartIII-b:C/asrc/kflat/1/2/2`.

The bound is the combination of the uniform train energy (`TrainEnergyUnif`), the Cauchy-Schwarz
readout on one cell (`SymOuterSliceProp`) and the kinetic bound (`TrainFlowKinetic`), integrated
against the finite weight `∫_{1.2/ν}^∞ u^{-3/2} du`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

theorem trainOldStressBound_of (m : ℝ) [Fact (1 < m)] (hE : TrainEnergyUnif) (hSl : SymOuterSliceProp m) (hK : TrainFlowKinetic m) : TrainOldStressBound m := by
  intro hm
  obtain ⟨ν₁, hν₁, hK'⟩ := hK hm
  obtain ⟨ν₂, hν₂, E, hE'⟩ := hE
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro κ ν hν hνs tr htr FI
  have hν₁' : ν ≤ ν₁ := le_trans hνs (min_le_left _ _)
  have hν₂' : ν ≤ ν₂ := le_trans hνs (min_le_right _ _)
  haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  obtain ⟨Ck, hCk⟩ := hK' κ ν hν hν₁' tr htr FI
  have hc : 0 < (cOf ν)⁻¹ := inv_pos.2 (cOf_pos hν)
  have ha0 : 0 < 6 / 5 / ν := div_pos (by norm_num) hν
  set a : ℝ := 6 / 5 / ν with ha_def
  set E' : ℝ := max E 0 with hE'_def
  set Ck' : ℝ := max Ck 0 with hCk'_def
  have hE'nn : 0 ≤ E' := le_max_right _ _
  have hCk'nn : 0 ≤ Ck' := le_max_right _ _
  set J : ℝ := ∫ u in Ioi a, u ^ (-(3 / 2 : ℝ)) with hJ_def
  have hJint : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha0
  have hJnn' : 0 ≤ᵐ[volume.restrict (Ioi a)] (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun u hu => Real.rpow_nonneg (ha0.trans (Set.mem_Ioi.mp hu)).le _)
  have hJnn : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi
    (fun u hu => Real.rpow_nonneg (ha0.trans (Set.mem_Ioi.mp hu)).le _)
  have hL : ∫⁻ u in Ioi a, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) = ENNReal.ofReal J :=
    (ofReal_integral_eq_lintegral_ofReal hJint hJnn').symm
  refine ⟨2 * (cOf ν)⁻¹ * E' * Ck' * J, fun w => ?_⟩
  have hpt : ∀ u ∈ Ioi a,
      ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * frob (UnforcedLeray.Short.IIIa.symOuter
          (NearInst.trainMer tr (u, x)) (kcMer (FI.ev.U u (11 / 10 / ν) w) x)))
        ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤
      ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) *
        (2 * ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal E' * ENNReal.ofReal (Ck' * ‖w‖)) := by
    intro u hu
    have hu0 : 0 < u := ha0.trans (Set.mem_Ioi.mp hu)
    have hT : 11 / 10 / ν ≤ u := by
      have h1 : 11 / 10 / ν ≤ 6 / 5 / ν := by
        apply div_le_div_of_nonneg_right _ hν.le
        norm_num
      exact h1.trans (Set.mem_Ioi.mp hu).le
    have hsplit : ∀ x : ℝ × ℝ, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * frob (UnforcedLeray.Short.IIIa.symOuter
          (NearInst.trainMer tr (u, x)) (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) =
        ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal (frob (UnforcedLeray.Short.IIIa.symOuter
          (NearInst.trainMer tr (u, x)) (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) :=
      fun x => ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _)
    simp_rw [hsplit]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    have h1 : UnforcedLeray.Train.cellL2 (cOf ν) (tr.v u) ≤ ENNReal.ofReal E' :=
      (hE' ν hν hν₂' tr htr u hu0.le).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have h2 : ENNReal.ofReal ‖kcLp (FI.ev.U u (11 / 10 / ν) w)‖ ≤ ENNReal.ofReal (Ck' * ‖w‖) :=
      ENNReal.ofReal_le_ofReal ((hCk u hT w).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    exact (hSl ν hν tr u (FI.ev.U u (11 / 10 / ν) w)).trans (by gcongr)
  have hK_ne : (2 * ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal E' * ENNReal.ofReal (Ck' * ‖w‖)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  calc ∫⁻ u in Ioi a, ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * frob (UnforcedLeray.Short.IIIa.symOuter
          (NearInst.trainMer tr (u, x)) (kcMer (FI.ev.U u (11 / 10 / ν) w) x)))
        ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ u in Ioi a, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ))) *
          (2 * ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal E' * ENNReal.ofReal (Ck' * ‖w‖)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ u in Ioi a, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)))) *
          (2 * ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal E' * ENNReal.ofReal (Ck' * ‖w‖)) :=
        lintegral_mul_const' _ _ hK_ne
    _ = ENNReal.ofReal (2 * (cOf ν)⁻¹ * E' * Ck' * J * ‖w‖) := by
        rw [hL]
        have hX : 0 ≤ Ck' * ‖w‖ := mul_nonneg hCk'nn (norm_nonneg _)
        have hY : 0 ≤ 2 * (cOf ν)⁻¹ * E' := mul_nonneg (mul_nonneg (by norm_num) hc.le) hE'nn
        have hZ : 0 ≤ J * (2 * (cOf ν)⁻¹ * E') := mul_nonneg hJnn hY
        have e : 2 * (cOf ν)⁻¹ * E' * Ck' * J * ‖w‖ = (J * (2 * (cOf ν)⁻¹ * E')) * (Ck' * ‖w‖) := by
          ring
        rw [e, ENNReal.ofReal_mul hZ, ENNReal.ofReal_mul hJnn,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (cOf ν)⁻¹),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
