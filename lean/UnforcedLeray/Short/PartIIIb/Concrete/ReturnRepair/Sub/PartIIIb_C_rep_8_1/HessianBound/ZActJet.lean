import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Tools
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.ThinSrc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStep.PointMass
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.SepX0Dom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4

/-!
# `ZActJet`: phase `L²` bounds of the separated jet `(X₀, ∇X₀, ∇²X₀, Ψ_{X₀})`

Helper for `HessianBound` (`PartIII-b:C/rep/8/1/2`), source
`the November 2 reference manuscript`
lines 5404-5413, 5438-5448, 4178-4184, 3640-3648, 3669-3701.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open GeomXAsm

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Phase `L²` bounds of the separated jet `(X₀, ∇X₀, ∇²X₀, Ψ_{X₀})` at young receivers**
(source 5404-5413, 4178-4184, 5445-5447). -/
def ZActJetAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    ∃ B₀ B₁ B₂ B₃ : ℝ → ℝ≥0∞, Measurable B₀ ∧ Measurable B₁ ∧ Measurable B₂ ∧ Measurable B₃ ∧
      (∀ q : ℝ, ENNReal.ofReal ‖zAct Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
          (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖ ≤ B₀ q) ∧
      (∀ q : ℝ, ENNReal.ofReal (gradSize (zAct Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
          (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤ B₁ q) ∧
      (∀ q : ℝ, ENNReal.ofReal (hessSize (zAct Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
          (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤ B₂ q) ∧
      (∀ q : ℝ, ENNReal.ofReal |outPrim (zAct Pl K L μ T) (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
          (L.ε⁻¹ / Real.sqrt s) (η / Real.sqrt s)| ≤ B₃ q) ∧
      cellN (cOf L.ν) B₀ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 2 * s ^ 2)) * oldN1 Pl K L T ∧
      cellN (cOf L.ν) B₁ ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 3 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T ∧
      cellN (cOf L.ν) B₂ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T ∧
      cellN (cOf L.ν) B₃ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * s) * oldN1 Pl K L T

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `ZActJetAt` (under the standing hypotheses). -/
def ZActJetSeq (dm dp : ℝ) : Prop :=
  D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ZActJetAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

namespace ZActJetAux

theorem norm_coordVec (j : Fin 3) : ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector]

theorem gradSize_le_iteratedFDeriv (f : Space → Space) (y : Space) :
    gradSize f y ≤ 3 * ‖iteratedFDeriv ℝ 1 f y‖ := by
  have e : ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ := by rw [norm_iteratedFDeriv_one]
  have hj : ∀ j : Fin 3, ‖physPd f j y‖ ≤ ‖iteratedFDeriv ℝ 1 f y‖ := by
    intro j
    rw [← e]
    unfold physPd
    calc ‖fderiv ℝ f y (coordinateVector j)‖
        ≤ ‖fderiv ℝ f y‖ * ‖coordinateVector j‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f y‖ := by rw [norm_coordVec, mul_one]
  unfold gradSize
  calc ∑ j : Fin 3, ‖physPd f j y‖
      ≤ ∑ _ : Fin 3, ‖iteratedFDeriv ℝ 1 f y‖ := Finset.sum_le_sum fun j _ => hj j
    _ = 3 * ‖iteratedFDeriv ℝ 1 f y‖ := by simp

theorem hessSize_le_iteratedFDeriv {U : Set Space} (hU : IsOpen U) {f : Space → Space}
    (hf : ContDiffOn ℝ 2 f U) {y : Space} (hy : y ∈ U) :
    hessSize f y ≤ 9 * ‖iteratedFDeriv ℝ 2 f y‖ := by
  have hc : ContDiffAt ℝ 2 f y := (hf.contDiffWithinAt hy).contDiffAt (hU.mem_nhds hy)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e : ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  have hjl : ∀ j l : Fin 3, ‖physPd2 f j l y‖ ≤ ‖iteratedFDeriv ℝ 2 f y‖ := by
    intro j l
    have hclm := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector l) y)
    have hpd : physPd2 f j l y =
        fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector l) := by
      unfold physPd2 physPd
      rw [hclm.fderiv]
      simp
    rw [hpd, ← e]
    calc ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector l)‖
        ≤ ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j)‖ * ‖coordinateVector l‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ * ‖coordinateVector j‖ * ‖coordinateVector l‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by rw [norm_coordVec, norm_coordVec, mul_one, mul_one]
  unfold hessSize
  calc ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 f j l y‖
      ≤ ∑ _ : Fin 3, ∑ _ : Fin 3, ‖iteratedFDeriv ℝ 2 f y‖ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hjl j l
    _ = 9 * ‖iteratedFDeriv ℝ 2 f y‖ := by simp; ring

theorem measurable_Kint {g : ℝ → Space → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    Measurable (PmStep.Kint g) := by
  have hh : Measurable (fun q : (ℝ × ℝ) × Space => g (q.1.2 + 2 * Real.log q.1.1) q.2) := by
    refine hg.comp (Measurable.prodMk ?_ measurable_snd)
    exact (measurable_snd.comp measurable_fst).add
      (measurable_const.mul (measurable_fst.comp measurable_fst).log)
  have hF : Measurable (Function.uncurry fun (l τ : ℝ) =>
      ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
    hh.lintegral_prod_right' (ν := (volume : Measure Space))
  unfold PmStep.Kint
  exact (hF.comp measurable_swap).lintegral_prod_right'

theorem periodic_Kint {P : ℝ} {g : ℝ → Space → ℝ≥0∞} (hper : ∀ τ z, g (τ + P) z = g τ z) :
    Function.Periodic (PmStep.Kint g) P := by
  intro τ
  unfold PmStep.Kint
  refine lintegral_congr fun l => lintegral_congr fun z => ?_
  have : τ + P + 2 * Real.log l = (τ + 2 * Real.log l) + P := by ring
  rw [this, hper]

theorem cellN_chartTau_le (ε c s η : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (B : ℝ → ℝ≥0∞) (hBm : Measurable B) (hBp : Function.Periodic B (2 * ε * c)) :
    cellN c (fun q => B (NearInst.chartTau ε⁻¹ (s, (q, η)))) ≤ IIIa.ltauAt (2 * ε * c) B := by
  have hP : 0 < 2 * ε * c := by positivity
  have htau : ∀ q, NearInst.chartTau ε⁻¹ (s, (q, η)) = 2 * ε * q + Real.log s := by
    intro q; unfold NearInst.chartTau; rw [div_inv_eq_mul]; ring
  unfold cellN IIIa.ltauAt
  rw [lintegral_cellμ]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  simp only [htau]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    PhasePrim.lintegral_affine (2 * ε) (Real.log s) (-c / 2) (c / 2) (by positivity)
      (fun τ => B τ ^ 2) (hBm.pow_const 2)]
  have hper : Function.Periodic (fun τ => B τ ^ 2) (2 * ε * c) := fun τ => by simp only [hBp τ]
  have e1 : ∫⁻ τ in Ico (2 * ε * (-c / 2) + Real.log s) (2 * ε * (c / 2) + Real.log s),
      B τ ^ 2 = ∫⁻ τ in Ioc (2 * ε * (-c / 2) + Real.log s)
        ((2 * ε * (-c / 2) + Real.log s) + 2 * ε * c), B τ ^ 2 := by
    rw [show (2 * ε * (-c / 2) + Real.log s) + 2 * ε * c = 2 * ε * (c / 2) + Real.log s by ring]
    exact setLIntegral_congr Ico_ae_eq_Ioc
  have e2 := PhasePrim.lintegral_periodic hP hper (2 * ε * (-c / 2) + Real.log s) 0
  rw [zero_add] at e2
  rw [e1, e2]
  have e3 : ∀ τ, B τ ^ (2 : ℝ) = B τ ^ 2 := fun τ => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [e3]
  rw [← mul_assoc]
  apply le_of_eq
  congr 1
  rw [ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hc.le]
  congr 2
  ring

theorem ltauAt_srcNorm_thinSource_le {ε c ρo : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hF : FarLeafOrg.ThinHyp c ρo F) :
    ∫⁻ z : Space, IIIa.ltauAt (2 * ε * c) (fun τ => IIIa.srcNorm (IIIa.thinSource ε F) τ z) ≤
      ENNReal.ofReal (ε⁻¹ ^ 2) * IIIa.thinMoment c F := by
  have hpoint : ∀ z : Space,
      IIIa.ltauAt (2 * ε * c) (fun τ => IIIa.srcNorm (IIIa.thinSource ε F) τ z) ≤
        (fun w : (ℝ × ℝ) × ℝ =>
          ((ENNReal.ofReal c)⁻¹ * ∫⁻ q in Ioc 0 c,
            ENNReal.ofReal (IIIa.tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ))
          ((ε * z 0, ε * z 1), z 2) := by
    intro z
    dsimp only
    set qz := FarLeafOrg.q0 ε 0 z with hqz
    have htau : ∀ τ, IIIa.srcNorm (IIIa.thinSource ε F) τ z =
        ENNReal.ofReal (IIIa.tensorNorm (F (ε * z 0, ε * z 1) (z 2) ((2 * ε)⁻¹ * τ + qz))) := by
      intro τ
      rw [hqz]
      unfold IIIa.srcNorm IIIa.thinSource FarLeafOrg.q0
      congr 3
      field_simp
      ring
    set B : ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (IIIa.tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))
    have hBm : Measurable B := ENNReal.measurable_ofReal.comp (FarLeafOrg.tn_meas_phase hF _ _)
    have hBp : Function.Periodic (fun q => B q ^ 2) c := fun q => by
      simp only [B, hF.per]
    unfold IIIa.ltauAt
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    simp only [htau]
    have e0 : ∀ τ, ENNReal.ofReal (IIIa.tensorNorm
        (F (ε * z 0, ε * z 1) (z 2) ((2 * ε)⁻¹ * τ + qz))) ^ (2 : ℝ) =
        B ((2 * ε)⁻¹ * τ + qz) ^ 2 := fun τ => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    simp only [e0]
    have eI : ∫⁻ τ in Ioc 0 (2 * ε * c), B ((2 * ε)⁻¹ * τ + qz) ^ 2 =
        ∫⁻ τ in Ico 0 (2 * ε * c), B ((2 * ε)⁻¹ * τ + qz) ^ 2 :=
      setLIntegral_congr Ico_ae_eq_Ioc.symm
    rw [eI, PhasePrim.lintegral_affine (2 * ε)⁻¹ qz 0 (2 * ε * c) (by positivity)
      (fun q => B q ^ 2) (hBm.pow_const 2)]
    have e1 : (2 * ε)⁻¹ * 0 + qz = qz := by ring
    have e2 : (2 * ε)⁻¹ * (2 * ε * c) + qz = qz + c := by field_simp; ring
    rw [e1, e2, setLIntegral_congr Ico_ae_eq_Ioc]
    have e3 := PhasePrim.lintegral_periodic hc hBp qz 0
    rw [zero_add] at e3
    rw [e3, ← mul_assoc]
    have e4 : ∀ q, B q ^ 2 = ENNReal.ofReal (IIIa.tensorNorm (F (ε * z 0, ε * z 1) (z 2) q) ^ 2) := by
      intro q
      have h0 : 0 ≤ IIIa.tensorNorm (F (ε * z 0, ε * z 1) (z 2) q) := by
        unfold IIIa.tensorNorm; positivity
      exact (ENNReal.ofReal_pow h0 2).symm
    simp only [e4]
    apply le_of_eq
    congr 1
    rw [inv_inv, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ε),
      ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top),
      mul_right_comm, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
  calc ∫⁻ z : Space, IIIa.ltauAt (2 * ε * c) (fun τ => IIIa.srcNorm (IIIa.thinSource ε F) τ z)
      ≤ ∫⁻ z : Space, (fun w : (ℝ × ℝ) × ℝ =>
          ((ENNReal.ofReal c)⁻¹ * ∫⁻ q in Ioc 0 c,
            ENNReal.ofReal (IIIa.tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ))
          ((ε * z 0, ε * z 1), z 2) := lintegral_mono hpoint
    _ = ENNReal.ofReal (ε⁻¹) ^ 2 * ∫⁻ w : (ℝ × ℝ) × ℝ,
          ((ENNReal.ofReal c)⁻¹ * ∫⁻ q in Ioc 0 c,
            ENNReal.ofReal (IIIa.tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [FarLeafOrg.lintegral_space_scale hε (fun w : (ℝ × ℝ) × ℝ =>
          ((ENNReal.ofReal c)⁻¹ * ∫⁻ q in Ioc 0 c,
            ENNReal.ofReal (IIIa.tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ))]
    _ ≤ ENNReal.ofReal (ε⁻¹ ^ 2) * IIIa.thinMoment c F := by
        rw [← ENNReal.ofReal_pow (by positivity)]
        refine mul_le_mul' le_rfl ?_
        unfold IIIa.thinMoment
        refine lintegral_mono fun w => ?_
        have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + |w.2|) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg w.2])
        conv_lhs => rw [← one_mul (((ENNReal.ofReal c)⁻¹ * _) ^ (1 / 2 : ℝ))]
        rw [ENNReal.ofReal_inv_of_pos hc,
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (by positivity))]
        exact mul_le_mul' h1 le_rfl

theorem ltauAt_Kint_oldCutSrc_le (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    IIIa.ltauAt (2 * L.ε * cOf L.ν)
      (PmStep.Kint (IIIa.srcNorm
        (oldCutSrc L.ε⁻¹ (cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (thinG Pl K L T)))) ≤
      ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  set g := thinG Pl K L T
  have hgm : Measurable g :=
    (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
  set F := PhasePrim.cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) g
  have hFH : FarLeafOrg.ThinHyp (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) F :=
    ⟨PhasePrim.cutLift_measurable _ _ g hgm, PhasePrim.cutLift_periodic _ _ hc.ne' g,
      fun x' Y q h => PhasePrim.cutLift_support _ _ g x' Y q h⟩
  have hS_eq : oldCutSrc L.ε⁻¹ (cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) g =
      IIIa.thinSource L.ε F :=
    funext fun τ => funext fun z => (PhasePrim.thinSource_cutLift L.ε (cOf L.ν) _ hε g τ z).symm
  rw [hS_eq]
  have hS := FarLeafOrg.thin_isSep hε hFH
  have hP : 0 < 2 * L.ε * cOf L.ν := by positivity
  have hper : ∀ τ z, IIIa.srcNorm (IIIa.thinSource L.ε F) (τ + 2 * L.ε * cOf L.ν) z =
      IIIa.srcNorm (IIIa.thinSource L.ε F) τ z := fun τ z => by
    unfold IIIa.srcNorm; rw [hS.periodic]
  have hSm : Measurable (Function.uncurry (IIIa.srcNorm (IIIa.thinSource L.ε F))) :=
    srcNorm_measurable hS
  calc IIIa.ltauAt (2 * L.ε * cOf L.ν) (PmStep.Kint (IIIa.srcNorm (IIIa.thinSource L.ε F)))
      ≤ ∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν)
          (fun τ => IIIa.srcNorm (IIIa.thinSource L.ε F) τ z) :=
        PmStep.ltauAt_Kint_le hP hSm hper
    _ ≤ ENNReal.ofReal (L.ε⁻¹ ^ 2) * IIIa.thinMoment (cOf L.ν) F :=
        ltauAt_srcNorm_thinSource_le hε hc hFH
    _ ≤ ENNReal.ofReal (L.ε⁻¹ ^ 2) *
          (ENNReal.ofReal Real.pi *
            IIIa.firstMoment (cOf L.ν) 0 (fun p => Ten3.toMatrix (g p))) :=
        mul_le_mul' le_rfl (PhasePrim.thinMoment_cutLift_le _ _ hc g hgm)
    _ = ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
        rw [PhasePrim.firstMoment_thinG Pl K L hC0 T, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), mul_comm (L.ε⁻¹ ^ 2) Real.pi]

/-- Pointwise domination of `iteratedFDeriv ℝ j (sepX0 ν μ T τ)` (`j ≤ 2`) by `Kint`. -/
theorem sepX0_iteratedFDeriv_le :
    ∃ C_W : ℝ, 0 < C_W ∧ ∀ (ν μ rOut rIn P : ℝ), 0 < ν → 0 ≤ μ → μ ≤ 1 →
      0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
      ∀ j : ℕ, j ≤ 2 →
        ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ ≤
          ENNReal.ofReal (C_W * (rIn - rOut) ^ (-4 - (j : ℝ))) *
            PmStep.Kint (IIIa.srcNorm T) τ := by
  classical
  obtain ⟨A0, hA0, hW0⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 0
  obtain ⟨A1, hA1, hW1⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 1
  obtain ⟨A2, hA2, hW2⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 2
  set C_W : ℝ := ‖reL‖ * (2 * A0 + 2 * A1 + 2 * A2) + 1
  have hCW : 0 < C_W := by
    have := mul_nonneg (norm_nonneg reL) (by linarith : (0 : ℝ) ≤ 2 * A0 + 2 * A1 + 2 * A2)
    linarith
  refine ⟨C_W, hCW, ?_⟩
  intro ν μ rOut rIn P hν hμ0 _hμ1 hrO hrr hP T hT hM τ y hry j hj
  have hD : 0 < rIn - rOut := sub_pos.2 hrr
  have hcoef : 0 < C_W * (rIn - rOut) ^ (-4 - (j : ℝ)) :=
    mul_pos hCW (Real.rpow_pos_of_pos hD _)
  have hcoef_ne : ENNReal.ofReal (C_W * (rIn - rOut) ^ (-4 - (j : ℝ))) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hcoef
  by_cases hK : PmStep.Kint (IIIa.srcNorm T) τ = ⊤
  · rw [hK, ENNReal.mul_top hcoef_ne]; exact le_top
  have hm1re : -(1 / 4) < ((μ : ℂ)).re := by simp; linarith
  have hm2re : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hy : y ∈ {y : Space | rOut < ϱ y} := lt_of_lt_of_le hrr hry
  have hWa : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
      hm1re hrO hP hT hM τ i)
  have hWb : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν
      hm2re hrO hP hT hM τ i)
  have hder : ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ ≤
      ENNReal.ofReal ‖reL‖ * (IIIa.wDerivNorm ν (μ : ℂ) T j τ y +
        IIIa.wDerivNorm ν ((μ : ℂ) + 1) T j τ y) := by
    rw [sepX0_eq_reL]
    exact iteratedFDeriv_reL_le hU hWa hWb hj hy
  have hS0_le := PmStep.sepDom_zero_le 0 hD (IIIa.srcNorm T) τ y
  have hS0_lt : IIIa.sepDom 0 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt hS0_le (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hK))
  have hb1 : (0 : ℝ) ≤ 2 * ((μ : ℂ)).re + 2 := by simp; linarith
  have hb2 : (0 : ℝ) ≤ 2 * ((μ : ℂ) + 1).re + 2 := by simp; linarith
  have hf1 : IIIa.sepDom (2 * ((μ : ℂ)).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt (sepDom_anti_a' hb1 0 _ _ _ _) hS0_lt
  have hf2 : IIIa.sepDom (2 * ((μ : ℂ) + 1).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y < ⊤ :=
    lt_of_le_of_lt (sepDom_anti_a' hb2 0 _ _ _ _) hS0_lt
  have hri : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hry
  have hSj : IIIa.wDerivNorm ν (μ : ℂ) T j τ y + IIIa.wDerivNorm ν ((μ : ℂ) + 1) T j τ y ≤
      ENNReal.ofReal (2 * A0 + 2 * A1 + 2 * A2) *
        IIIa.sepDom 0 j (rIn - rOut) (IIIa.srcNorm T) τ y := by
    have hd1 := sepDom_anti_a' hb1 j (rIn - rOut) (IIIa.srcNorm T) τ y
    have hd2 := sepDom_anti_a' hb2 j (rIn - rOut) (IIIa.srcNorm T) τ y
    interval_cases j
    · have wa := (hW0 ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hri hf1).trans
        (mul_le_mul' le_rfl hd1)
      have wb := (hW0 ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP T hT τ y hri hf2).trans
        (mul_le_mul' le_rfl hd2)
      calc _ ≤ ENNReal.ofReal A0 * _ + ENNReal.ofReal A0 * _ := add_le_add wa wb
        _ = (ENNReal.ofReal A0 + ENNReal.ofReal A0) * _ := (add_mul _ _ _).symm
        _ ≤ _ := mul_le_mul' (by
          rw [← ENNReal.ofReal_add hA0 hA0]
          exact ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
    · have wa := (hW1 ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hri hf1).trans
        (mul_le_mul' le_rfl hd1)
      have wb := (hW1 ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP T hT τ y hri hf2).trans
        (mul_le_mul' le_rfl hd2)
      calc _ ≤ ENNReal.ofReal A1 * _ + ENNReal.ofReal A1 * _ := add_le_add wa wb
        _ = (ENNReal.ofReal A1 + ENNReal.ofReal A1) * _ := (add_mul _ _ _).symm
        _ ≤ _ := mul_le_mul' (by
          rw [← ENNReal.ofReal_add hA1 hA1]
          exact ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
    · have wa := (hW2 ν hν (μ : ℂ) hm1re rOut rIn P hrO hrr hP T hT τ y hri hf1).trans
        (mul_le_mul' le_rfl hd1)
      have wb := (hW2 ν hν ((μ : ℂ) + 1) hm2re rOut rIn P hrO hrr hP T hT τ y hri hf2).trans
        (mul_le_mul' le_rfl hd2)
      calc _ ≤ ENNReal.ofReal A2 * _ + ENNReal.ofReal A2 * _ := add_le_add wa wb
        _ = (ENNReal.ofReal A2 + ENNReal.ofReal A2) * _ := (add_mul _ _ _).symm
        _ ≤ _ := mul_le_mul' (by
          rw [← ENNReal.ofReal_add hA2 hA2]
          exact ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
  calc ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ₑ
      ≤ ENNReal.ofReal ‖reL‖ * (ENNReal.ofReal (2 * A0 + 2 * A1 + 2 * A2) *
          IIIa.sepDom 0 j (rIn - rOut) (IIIa.srcNorm T) τ y) :=
        hder.trans (mul_le_mul' le_rfl hSj)
    _ ≤ ENNReal.ofReal C_W * IIIa.sepDom 0 j (rIn - rOut) (IIIa.srcNorm T) τ y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg reL)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
    _ ≤ ENNReal.ofReal C_W *
          (ENNReal.ofReal ((rIn - rOut) ^ (-4 - (j : ℝ))) * PmStep.Kint (IIIa.srcNorm T) τ) :=
        mul_le_mul' le_rfl (PmStep.sepDom_zero_le j hD (IIIa.srcNorm T) τ y)
    _ = ENNReal.ofReal (C_W * (rIn - rOut) ^ (-4 - (j : ℝ))) * PmStep.Kint (IIIa.srcNorm T) τ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCW.le]

theorem rpow_neg_nat {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ (-(m : ℝ)) = (r⁻¹) ^ m := by
  rw [Real.rpow_neg hr.le, Real.rpow_natCast, inv_pow]

theorem srcNorm_eq_zero_of_zero {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {τ : ℝ} {z : Space}
    (h : T τ z = 0) : IIIa.srcNorm T τ z = 0 := by
  simp [IIIa.srcNorm, h, IIIa.tensorNorm]

theorem cellN_mul_Φ_le {c R a b C ν : ℝ} {Φ : ℝ → ℝ≥0∞} {N : ℝ≥0∞}
    (ha : 0 ≤ a) (hab : a * (Real.pi * R ^ 2) ≤ C * b)
    (hΦ : cellN c Φ ≤ ENNReal.ofReal (Real.pi * R ^ 2) * N) :
    cellN c (fun q => ENNReal.ofReal a * Φ q) ≤ ENNReal.ofReal (C * ν⁻¹ ^ 0 * b) * N := by
  rw [cellN_const_mul _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl hΦ).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha, pow_zero, mul_one]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hab) le_rfl

theorem zAct_sepSrc (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) (T : LStr Pl K L) :
    ∃ S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) S ∧
      SepMoment (2 * L.ε * cOf L.ν) S ∧
      zAct Pl K L μ T = sepX0 L.ν μ S ∧
      IIIa.ltauAt (2 * L.ε * cOf L.ν) (PmStep.Kint (IIIa.srcNorm S)) ≤
        ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  set g := thinG Pl K L T
  have hρb : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  have hgm : Measurable g :=
    (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
  have hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith only [hmZ]) hν _
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → g p = 0 :=
    ZRegAux.strSum_zero_young _ _ _ _ _ K.hχo hρb _
  set rOut : ℝ := L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)
  set S := oldCutSrc L.ε⁻¹ (cOf L.ν) rOut g
  have hP_eq : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hS : IIIa.IsSepSource (2 * L.ε * cOf L.ν) rOut S := by
    rw [hP_eq]
    exact ⟨oldCutMeasurable L.ε⁻¹ (cOf L.ν) rOut g hgm,
      fun τ z => by unfold S oldCutSrc; rw [oldPhysPeriodic L.ε⁻¹ (cOf L.ν) g τ z],
      fun τ z hz => by unfold S oldCutSrc; exact ite_eq_right_iff.2 fun h => absurd hz (not_lt.2 h)⟩
  have hM : SepMoment (2 * L.ε * cOf L.ν) S := by
    rw [hP_eq]
    exact oldCutMoment L.ε⁻¹ (cOf L.ν) rOut g hR hc hgm hmom
  have hEq : ∀ (μ' : ℂ) (y' : Space) (τ : ℝ),
      IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) g) y' τ = IIIa.sepW L.ν μ' S y' τ :=
    fun μ' y' τ =>
      (sepWCongrAE L.ν μ' _ _ (PhasePrim.oldCut_ae (cOf L.ν) L.ν L.ε hc hν hε g hz) y' τ).symm
  have hzAct_eq : zAct Pl K L μ T = sepX0 L.ν μ S := by
    funext τ y'
    exact ZRegAux.wardX0_eq_T' (μ := μ) hEq τ y'
  exact ⟨S, hS, hM, hzAct_eq, ltauAt_Kint_oldCutSrc_le Pl K L hC0 T⟩

/-- Radius and power bounds at a young chart point `s ∈ (0, 1 / ν]`, `r = ε⁻¹ / √s`,
`rOut = ε⁻¹ * √(5 ν / 6)`, with `s₀ = √(5 / 6)`. -/
private theorem young_r_bounds {ν ε s : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hs : s ∈ Ioc 0 (1 / ν)) :
    let s₀ := Real.sqrt (5 / 6)
    let r := ε⁻¹ / Real.sqrt s
    let rOut := ε⁻¹ * Real.sqrt (5 * ν / 6)
    0 < r ∧ rOut ≤ s₀ * r ∧ rOut < r ∧
      (r - rOut) ^ (-4 - (0 : ℝ)) ≤ (1 - s₀) ^ (-4 : ℝ) * (ε ^ 4 * s ^ 2) ∧
      (r - rOut) ^ (-4 - (1 : ℝ)) ≤ (1 - s₀) ^ (-5 : ℝ) * (ε ^ 5 * s ^ (5 / 2 : ℝ)) ∧
      (r - rOut) ^ (-4 - (2 : ℝ)) ≤ (1 - s₀) ^ (-6 : ℝ) * (ε ^ 6 * s ^ 3) ∧
      r ^ (-2 : ℝ) = ε ^ 2 * s := by
  intro s₀ r rOut
  have hs₀0 : 0 ≤ s₀ := Real.sqrt_nonneg _
  have hs₀1 : s₀ < 1 := by change Real.sqrt (5 / 6) < 1; rw [Real.sqrt_lt' one_pos]; norm_num
  have hκ : 0 < 1 - s₀ := sub_pos.2 hs₀1
  have hs0 : 0 < s := hs.1
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hr : 0 < r := div_pos hR hss
  have hrinv : r⁻¹ = ε * Real.sqrt s := by
    change (ε⁻¹ / Real.sqrt s)⁻¹ = ε * Real.sqrt s
    rw [inv_div, div_inv_eq_mul, mul_comm]
  have hRν : ε⁻¹ * Real.sqrt ν ≤ r := by
    change ε⁻¹ * Real.sqrt ν ≤ ε⁻¹ / Real.sqrt s
    have h1 : Real.sqrt s ≤ 1 / Real.sqrt ν := by
      rw [← Real.sqrt_one, ← Real.sqrt_div zero_le_one]
      exact Real.sqrt_le_sqrt hs.2
    rw [le_div_iff₀ hss]
    calc ε⁻¹ * Real.sqrt ν * Real.sqrt s
        ≤ ε⁻¹ * Real.sqrt ν * (1 / Real.sqrt ν) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hR.le (Real.sqrt_nonneg ν))
      _ = ε⁻¹ := by field_simp [(Real.sqrt_pos.2 hν).ne']
  have hrOut_eq : rOut = s₀ * (ε⁻¹ * Real.sqrt ν) := by
    change ε⁻¹ * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * (ε⁻¹ * Real.sqrt ν)
    rw [show 5 * ν / 6 = (5 / 6) * ν by ring, Real.sqrt_mul (by norm_num)]
    ring
  have hrOut_le : rOut ≤ s₀ * r := by
    rw [hrOut_eq]
    exact mul_le_mul_of_nonneg_left hRν hs₀0
  have hrr : rOut < r := lt_of_le_of_lt hrOut_le (by nlinarith only [hs₀1, hr])
  have hD_ge : (1 - s₀) * r ≤ r - rOut := by linarith only [hrOut_le]
  have hD_pos : 0 < (1 - s₀) * r := mul_pos hκ hr
  have hr4 : (r - rOut) ^ (-4 - (0 : ℝ)) ≤ (1 - s₀) ^ (-4 : ℝ) * (ε ^ 4 * s ^ 2) := by
    have h1 : (r - rOut) ^ (-4 : ℝ) ≤ ((1 - s₀) * r) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hD_pos hD_ge (by norm_num)
    have h2 : ((1 - s₀) * r) ^ (-4 : ℝ) = (1 - s₀) ^ (-4 : ℝ) * (r⁻¹) ^ 4 := by
      rw [Real.mul_rpow hκ.le hr.le]
      congr 1
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, rpow_neg_nat hr 4]
    have h3 : (r⁻¹) ^ 4 = ε ^ 4 * s ^ 2 := by
      rw [hrinv, mul_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul (Real.sqrt s), Real.sq_sqrt hs0.le]
    rw [show (-4 : ℝ) - (0 : ℝ) = -4 by norm_num, ← h3, ← h2]
    exact h1
  have hr5 : (r - rOut) ^ (-4 - (1 : ℝ)) ≤ (1 - s₀) ^ (-5 : ℝ) * (ε ^ 5 * s ^ (5 / 2 : ℝ)) := by
    have h1 : (r - rOut) ^ (-5 : ℝ) ≤ ((1 - s₀) * r) ^ (-5 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hD_pos hD_ge (by norm_num)
    have h2 : ((1 - s₀) * r) ^ (-5 : ℝ) = (1 - s₀) ^ (-5 : ℝ) * (r⁻¹) ^ 5 := by
      rw [Real.mul_rpow hκ.le hr.le]
      congr 1
      rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, rpow_neg_nat hr 5]
    have h3 : (r⁻¹) ^ 5 = ε ^ 5 * s ^ (5 / 2 : ℝ) := by
      rw [hrinv, mul_pow, GeomXAsm.sqrt_pow_five hs0.le]
    rw [show (-4 : ℝ) - (1 : ℝ) = -5 by norm_num, ← h3, ← h2]
    exact h1
  have hr6 : (r - rOut) ^ (-4 - (2 : ℝ)) ≤ (1 - s₀) ^ (-6 : ℝ) * (ε ^ 6 * s ^ 3) := by
    have h1 : (r - rOut) ^ (-6 : ℝ) ≤ ((1 - s₀) * r) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hD_pos hD_ge (by norm_num)
    have h2 : ((1 - s₀) * r) ^ (-6 : ℝ) = (1 - s₀) ^ (-6 : ℝ) * (r⁻¹) ^ 6 := by
      rw [Real.mul_rpow hκ.le hr.le]
      congr 1
      rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, rpow_neg_nat hr 6]
    have h3 : (r⁻¹) ^ 6 = ε ^ 6 * s ^ 3 := by
      rw [hrinv, mul_pow, show (6 : ℕ) = 2 * 3 by rfl, pow_mul (Real.sqrt s), Real.sq_sqrt hs0.le]
    rw [show (-4 : ℝ) - (2 : ℝ) = -6 by norm_num, ← h3, ← h2]
    exact h1
  have hr2 : r ^ (-2 : ℝ) = ε ^ 2 * s := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_nat hr 2, hrinv, mul_pow,
      Real.sq_sqrt hs0.le]
  exact ⟨hr, hrOut_le, hrr, hr4, hr5, hr6, hr2⟩

/-- Opaque phase majorant `Φ` along `q ↦ chartTau (ε⁻¹) (s, (q, η))` for a separated source `S`. -/
private theorem exists_chart_majorant (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (T : LStr Pl K L) (s η : ℝ) {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hS : IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) S)
    (hK0_ltau : IIIa.ltauAt (2 * L.ε * cOf L.ν) (PmStep.Kint (IIIa.srcNorm S)) ≤
      ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T) :
    ∃ Φ : ℝ → ℝ≥0∞,
      (∀ q, PmStep.Kint (IIIa.srcNorm S) (NearInst.chartTau L.ε⁻¹ (s, (q, η))) = Φ q) ∧
      Measurable Φ ∧
      cellN (cOf L.ν) Φ ≤ ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
  have hK0m : Measurable (PmStep.Kint (IIIa.srcNorm S)) := measurable_Kint (srcNorm_measurable hS)
  have hK0p : Function.Periodic (PmStep.Kint (IIIa.srcNorm S)) (2 * L.ε * cOf L.ν) :=
    periodic_Kint fun τ z => by unfold IIIa.srcNorm; rw [hS.periodic]
  refine ⟨fun q => PmStep.Kint (IIIa.srcNorm S) (NearInst.chartTau L.ε⁻¹ (s, (q, η))),
    fun _ => rfl, hK0m.comp (GeomXAsm.continuous_chartTau_q L.ε⁻¹ s η).measurable, ?_⟩
  exact (cellN_chartTau_le L.ε (cOf L.ν) s η L.ε_pos (cOf_pos L.ν_pos) _ hK0m hK0p).trans hK0_ltau

theorem sepX0_cd {ν μ P r0 : ℝ} {T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ r0) (hP : 0 < P)
    (hS : IIIa.IsSepSource P r0 T') (hM : SepMoment P T') (τ : ℝ) :
    ContDiffOn ℝ 2 (sepX0 ν μ T' τ) {y : Space | r0 < ϱ y} := by
  have hW := sepWSmoothOn_of IIIa.sepKernelBounds
  have hA := hW ν (μ : ℂ) r0 P T' hν (by simpa using hμ) hr0 hP hS hM τ
  have hB := hW ν ((μ : ℂ) + 1) r0 P T' hν (by simp; linarith) hr0 hP hS hM τ
  refine contDiffOn_piLp' 2 fun i => ?_
  exact Complex.reCLM.contDiff.comp_contDiffOn ((hA i).sub (hB i))

set_option maxHeartbeats 400000 in
theorem zActJetAt_uniform : ∃ (C : ℝ), 0 ≤ C ∧
    ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ),
      0 ≤ μ → μ ≤ 1 → 0 < K.C0 → 3 / 2 < K.mZ →
        ZActJetAt Pl K L μ C 0 := by
  obtain ⟨C_W, hCW, hJet⟩ := sepX0_iteratedFDeriv_le
  obtain ⟨C_O, hCO, hOut⟩ :=
    (outPrimPointwise_of IIIa.sepWDominated IIIa.sepKernelBounds : OutPrimPointwise) 0 1
      (by norm_num)
  set s₀ : ℝ := Real.sqrt (5 / 6) with hs₀_def
  have hs₀0 : 0 ≤ s₀ := Real.sqrt_nonneg _
  have hs₀1 : s₀ < 1 := by rw [hs₀_def, Real.sqrt_lt' one_pos]; norm_num
  have hκ : 0 < 1 - s₀ := sub_pos.2 hs₀1
  set κ₀ : ℝ := (1 - s₀) ^ (-4 : ℝ)
  set κ₁ : ℝ := (1 - s₀) ^ (-5 : ℝ)
  set κ₂ : ℝ := (1 - s₀) ^ (-6 : ℝ)
  have hκ₀ : 0 < κ₀ := Real.rpow_pos_of_pos hκ _
  have hκ₁ : 0 < κ₁ := Real.rpow_pos_of_pos hκ _
  have hκ₂ : 0 < κ₂ := Real.rpow_pos_of_pos hκ _
  set c₀ : ℝ := C_W * κ₀
  set c₁ : ℝ := 3 * (C_W * κ₁)
  set c₂ : ℝ := 9 * (C_W * κ₂)
  set c₃ : ℝ := (2 * C_O + 1) * (κ₀ * (1 / 2))
  have hc₀ : 0 ≤ c₀ := by positivity
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hc₃ : 0 ≤ c₃ := by positivity
  set C : ℝ := (c₀ + c₁ + c₂ + c₃) * Real.pi
  refine ⟨C, by positivity, ?_⟩
  intro Pl K L μ hμ0 hμ1 hC0 hmZ T s hs η
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hs0 : 0 < s := hs.1
  set R : ℝ := L.ε⁻¹
  set r : ℝ := R / Real.sqrt s
  set rOut : ℝ := R * Real.sqrt (5 * L.ν / 6)
  have hrO : 0 ≤ rOut := by positivity
  obtain ⟨hr, hrOut_le, hrr, hr4, hr5, hr6, hr2⟩ := young_r_bounds hν hε hs
  -- Separated source S and opaque majorant Φ
  set P : ℝ := 2 * L.ε * cOf L.ν
  have hP : 0 < P := by positivity
  obtain ⟨S, hS, hM, hzAct_eq, hK0_ltau⟩ := zAct_sepSrc Pl K L μ hC0 hmZ T
  obtain ⟨Φ, hΦ_eq, hΦm, hΦ_cell⟩ := exists_chart_majorant Pl K L T s η hS hK0_ltau
  -- Receiver point y
  set y : Space := NearInst.chartY R (s, (0, η)) with hy_def
  have hyq : ∀ q, NearInst.chartY R (s, (q, η)) = y := fun _ => rfl
  have hϱy : ϱ y = r := by
    rw [hy_def, GeomXAsm.chartY_eq_hpt, GeomXAsm.ϱ_hpt hr.le]
  have hU : IsOpen {y' : Space | rOut < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  have hyU : y ∈ {y' : Space | rOut < ϱ y'} := by show rOut < ϱ y; rw [hϱy]; exact hrr
  have hCD : ∀ τ, ContDiffOn ℝ 2 (sepX0 L.ν μ S τ) {y' : Space | rOut < ϱ y'} :=
    fun τ => sepX0_cd hν (by linarith only [hμ0]) hrO hP hS hM τ
  -- Define B₀, B₁, B₂, B₃
  refine ⟨fun q => ENNReal.ofReal (c₀ * (L.ε ^ 4 * s ^ 2)) * Φ q,
    fun q => ENNReal.ofReal (c₁ * (L.ε ^ 5 * s ^ (5 / 2 : ℝ))) * Φ q,
    fun q => ENNReal.ofReal (c₂ * (L.ε ^ 6 * s ^ 3)) * Φ q,
    fun q => ENNReal.ofReal (c₃ * (L.ε ^ 2 * s)) * Φ q,
    measurable_const.mul hΦm, measurable_const.mul hΦm,
    measurable_const.mul hΦm, measurable_const.mul hΦm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Pointwise B₀
    intro q
    rw [hyq, hzAct_eq,
      ← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) (x := y),
      ofReal_norm]
    refine (hJet L.ν μ rOut r P hν hμ0 hμ1 hrO hrr hP S hS hM _ y hϱy.symm.le 0 (by norm_num)).trans ?_
    rw [hΦ_eq]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hr4' : (r - rOut) ^ (-4 - ((0 : ℕ) : ℝ)) ≤ (1 - s₀) ^ (-4 : ℝ) * (L.ε ^ 4 * s ^ 2) := by
      rw [Nat.cast_zero]; exact hr4
    calc C_W * (r - rOut) ^ (-4 - ((0 : ℕ) : ℝ))
        ≤ C_W * ((1 - s₀) ^ (-4 : ℝ) * (L.ε ^ 4 * s ^ 2)) := mul_le_mul_of_nonneg_left hr4' hCW.le
      _ = c₀ * (L.ε ^ 4 * s ^ 2) := by ring
  · -- Pointwise B₁
    intro q
    rw [hyq, hzAct_eq]
    have h1 := gradSize_le_iteratedFDeriv (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y
    have hJ := hJet L.ν μ rOut r P hν hμ0 hμ1 hrO hrr hP S hS hM
      (NearInst.chartTau R (s, (q, η))) y hϱy.symm.le 1 (by norm_num)
    rw [hΦ_eq] at hJ
    calc ENNReal.ofReal (gradSize (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y)
        ≤ ENNReal.ofReal (3 * ‖iteratedFDeriv ℝ 1 (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y‖) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal 3 * ‖iteratedFDeriv ℝ 1 (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y‖ₑ := by
          rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm]
      _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal (C_W * (r - rOut) ^ (-4 - ((1 : ℕ) : ℝ))) * Φ q) :=
          mul_le_mul' le_rfl hJ
      _ ≤ ENNReal.ofReal (c₁ * (L.ε ^ 5 * s ^ (5 / 2 : ℝ))) * Φ q := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hr5' : (r - rOut) ^ (-4 - ((1 : ℕ) : ℝ)) ≤ (1 - s₀) ^ (-5 : ℝ) * (L.ε ^ 5 * s ^ (5 / 2 : ℝ)) := by
            rw [Nat.cast_one]; exact hr5
          calc 3 * (C_W * (r - rOut) ^ (-4 - ((1 : ℕ) : ℝ)))
              = (3 * C_W) * (r - rOut) ^ (-4 - ((1 : ℕ) : ℝ)) := by ring
            _ ≤ (3 * C_W) * ((1 - s₀) ^ (-5 : ℝ) * (L.ε ^ 5 * s ^ (5 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hr5' (by positivity)
            _ = c₁ * (L.ε ^ 5 * s ^ (5 / 2 : ℝ)) := by ring
  · -- Pointwise B₂
    intro q
    rw [hyq, hzAct_eq]
    have h2 := hessSize_le_iteratedFDeriv hU (hCD (NearInst.chartTau R (s, (q, η)))) hyU
    have hJ := hJet L.ν μ rOut r P hν hμ0 hμ1 hrO hrr hP S hS hM
      (NearInst.chartTau R (s, (q, η))) y hϱy.symm.le 2 (by norm_num)
    rw [hΦ_eq] at hJ
    calc ENNReal.ofReal (hessSize (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y)
        ≤ ENNReal.ofReal (9 * ‖iteratedFDeriv ℝ 2 (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y‖) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal 9 * ‖iteratedFDeriv ℝ 2 (sepX0 L.ν μ S (NearInst.chartTau R (s, (q, η)))) y‖ₑ := by
          rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm]
      _ ≤ ENNReal.ofReal 9 * (ENNReal.ofReal (C_W * (r - rOut) ^ (-4 - ((2 : ℕ) : ℝ))) * Φ q) :=
          mul_le_mul' le_rfl hJ
      _ ≤ ENNReal.ofReal (c₂ * (L.ε ^ 6 * s ^ 3)) * Φ q := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hr6' : (r - rOut) ^ (-4 - ((2 : ℕ) : ℝ)) ≤ (1 - s₀) ^ (-6 : ℝ) * (L.ε ^ 6 * s ^ 3) := by
            rw [Nat.cast_ofNat]; exact hr6
          calc 9 * (C_W * (r - rOut) ^ (-4 - ((2 : ℕ) : ℝ)))
              = (9 * C_W) * (r - rOut) ^ (-4 - ((2 : ℕ) : ℝ)) := by ring
            _ ≤ (9 * C_W) * ((1 - s₀) ^ (-6 : ℝ) * (L.ε ^ 6 * s ^ 3)) :=
              mul_le_mul_of_nonneg_left hr6' (by positivity)
            _ = c₂ * (L.ε ^ 6 * s ^ 3) := by ring
  · -- Pointwise B₃
    intro q
    rw [hzAct_eq]
    have hOX := (hOut L.ν μ rOut r P hν ⟨hμ0, hμ1⟩ hrO hrr hP S hS
      (NearInst.chartTau R (s, (q, η))) r (η / Real.sqrt s) le_rfl).2
    have hμ_ge : (0 : ℝ) ≤ 2 * μ + 2 := by linarith only [hμ0]
    have hgs : ∀ τ (z : Space), s₀ * r < ϱ z → IIIa.srcNorm S τ z = 0 := by
      intro τ z hz
      exact srcNorm_eq_zero_of_zero (hS.support τ z (lt_of_le_of_lt hrOut_le hz))
    have hOM := PmStep.outMaj_zero_le (D := r - rOut) hs₀0 hs₀1 hr le_rfl (IIIa.srcNorm S) hgs
      (NearInst.chartTau R (s, (q, η))) (η / Real.sqrt s)
    rw [hΦ_eq] at hOM
    calc ENNReal.ofReal |outPrim (sepX0 L.ν μ S) (NearInst.chartTau R (s, (q, η))) r (η / Real.sqrt s)|
        ≤ ENNReal.ofReal C_O * (2 * outMaj 0 (r - rOut) (IIIa.srcNorm S)
            (NearInst.chartTau R (s, (q, η))) r (η / Real.sqrt s)) :=
          hOX.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (outMaj_anti_a hμ_ge _ _ _ _ _)))
      _ ≤ ENNReal.ofReal (2 * C_O + 1) * outMaj 0 (r - rOut) (IIIa.srcNorm S)
            (NearInst.chartTau R (s, (q, η))) r (η / Real.sqrt s) := by
          rw [← mul_assoc, show ENNReal.ofReal C_O * 2 = ENNReal.ofReal (2 * C_O) by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm]]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith only [])) le_rfl
      _ ≤ ENNReal.ofReal (2 * C_O + 1) *
            (ENNReal.ofReal (κ₀ * (1 / 2) * r ^ (-2 : ℝ)) * Φ q) :=
          mul_le_mul' le_rfl hOM
      _ = ENNReal.ofReal (c₃ * (L.ε ^ 2 * s)) * Φ q := by
          rw [hr2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  · -- cellN B₀
    refine cellN_mul_Φ_le (by positivity) ?_ hΦ_cell
    have he : L.ε ^ 4 * R ^ 2 = L.ε ^ 2 := by
      change L.ε ^ 4 * (L.ε⁻¹) ^ 2 = L.ε ^ 2; field_simp [hε.ne']
    have hle : c₀ * Real.pi ≤ C := by
      have : c₀ ≤ c₀ + c₁ + c₂ + c₃ := by linarith only [hc₁, hc₂, hc₃]
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
    calc c₀ * (L.ε ^ 4 * s ^ 2) * (Real.pi * R ^ 2)
        = (c₀ * Real.pi) * ((L.ε ^ 4 * R ^ 2) * s ^ 2) := by ring
      _ = (c₀ * Real.pi) * (L.ε ^ 2 * s ^ 2) := by rw [he]
      _ ≤ C * (L.ε ^ 2 * s ^ 2) := mul_le_mul_of_nonneg_right hle (by positivity)
  · -- cellN B₁
    refine cellN_mul_Φ_le (by positivity) ?_ hΦ_cell
    have he : L.ε ^ 5 * R ^ 2 = L.ε ^ 3 := by
      change L.ε ^ 5 * (L.ε⁻¹) ^ 2 = L.ε ^ 3; field_simp [hε.ne']
    have hle : c₁ * Real.pi ≤ C := by
      have : c₁ ≤ c₀ + c₁ + c₂ + c₃ := by linarith only [hc₀, hc₂, hc₃]
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
    calc c₁ * (L.ε ^ 5 * s ^ (5 / 2 : ℝ)) * (Real.pi * R ^ 2)
        = (c₁ * Real.pi) * ((L.ε ^ 5 * R ^ 2) * s ^ (5 / 2 : ℝ)) := by ring
      _ = (c₁ * Real.pi) * (L.ε ^ 3 * s ^ (5 / 2 : ℝ)) := by rw [he]
      _ ≤ C * (L.ε ^ 3 * s ^ (5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hle (by positivity)
  · -- cellN B₂
    refine cellN_mul_Φ_le (by positivity) ?_ hΦ_cell
    have he : L.ε ^ 6 * R ^ 2 = L.ε ^ 4 := by
      change L.ε ^ 6 * (L.ε⁻¹) ^ 2 = L.ε ^ 4; field_simp [hε.ne']
    have hle : c₂ * Real.pi ≤ C := by
      have : c₂ ≤ c₀ + c₁ + c₂ + c₃ := by linarith only [hc₀, hc₁, hc₃]
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
    calc c₂ * (L.ε ^ 6 * s ^ 3) * (Real.pi * R ^ 2)
        = (c₂ * Real.pi) * ((L.ε ^ 6 * R ^ 2) * s ^ 3) := by ring
      _ = (c₂ * Real.pi) * (L.ε ^ 4 * s ^ 3) := by rw [he]
      _ ≤ C * (L.ε ^ 4 * s ^ 3) := mul_le_mul_of_nonneg_right hle (by positivity)
  · -- cellN B₃
    refine cellN_mul_Φ_le (by positivity) ?_ hΦ_cell
    have he : L.ε ^ 2 * R ^ 2 = 1 := by
      change L.ε ^ 2 * (L.ε⁻¹) ^ 2 = 1; field_simp [hε.ne']
    have hle : c₃ * Real.pi ≤ C := by
      have : c₃ ≤ c₀ + c₁ + c₂ + c₃ := by linarith only [hc₀, hc₁, hc₂]
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
    calc c₃ * (L.ε ^ 2 * s) * (Real.pi * R ^ 2)
        = (c₃ * Real.pi) * ((L.ε ^ 2 * R ^ 2) * s) := by ring
      _ = (c₃ * Real.pi) * s := by rw [he, one_mul]
      _ ≤ C * s := mul_le_mul_of_nonneg_right hle hs0.le

end ZActJetAux

open ZActJetAux in
theorem zActJetSeq (D : SeqData) (dm dp : ℝ) : D.ZActJetSeq dm dp := by
  intro hst
  obtain ⟨C, _hC, hU⟩ := zActJetAt_uniform
  refine ⟨C, 0, ?_⟩
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY] with n hL z hz
  have hLz := hL z hz
  exact hU D.Pl D.K (D.level n) (D.mu n z) hLz.mu_pos.le (by linarith [hLz.mu_lt])
    hst.C0_pos hst.mZ_gt

end UnforcedLeray.Short.PartIIIb.Concrete
end
