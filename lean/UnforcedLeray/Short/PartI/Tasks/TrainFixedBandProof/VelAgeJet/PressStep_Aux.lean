import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Sub.PartI_T22_1
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.T25_3_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.PressureStep_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.QcDiv_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.AdvDiff_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.PcTwoMulM_Aux

/-!
# `Short/PartI/Tasks/TrainFixedBandProof/VelAgeJet/PressStep.lean` — Task `PartI:T25/1/3`

Source of record: `the November 2 reference manuscript`, lines 318–336, 468–478,
541–551.

Proves `trainFixedBandPressStep_proof : TrainFixedBandPressStep`:
assuming the strong induction hypothesis `∀ r ≤ ℓ, TrainFixedBandVelOrderUnweighted r`, for every
`ρ > 1/2`, `Sg > 0`, and spatial order `j : ℕ`, the pressure-gradient difference age-jet
`ageJet ℓ j dp s` (`dp r z = Train.gradS (fun w => tr.p r w - pc ν c r w) z`) satisfies the
unweighted fixed-band estimate on `0 < s ≤ Sg / ν` in both `wCellL2 c 0` and `wSupNorm 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI.VelAgeJetAux
open UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width jap jet cellL2 wCellL2 toVec toVec_zero toVec_one)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm vcSmooth_proof vb_ageJet_sub)

namespace PartI_T25_PressStep

/-! ### 1. Unconditional upstream tail assembly -/



/-! ### 2. Weighted `wSupNorm` extraction and `wCellL2 c 0` upgrade -/

private theorem sqrt_jap_mul_norm_le_of_wSupNorm_le {E : Type*} [NormedAddCommGroup E]
    (m : ℕ) {f : Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (h : wSupNorm m f ≤ ENNReal.ofReal B) (z : Plane) :
    Real.sqrt (jap m z) * ‖f z‖ ≤ B := by
  have hz : ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap m w)) * ‖f w‖ₑ) z).trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hz

private theorem norm_le_of_wSupNorm_zero_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (h : wSupNorm 0 f ≤ ENNReal.ofReal B) (z : Plane) :
    ‖f z‖ ≤ B := by
  have h1 := sqrt_jap_mul_norm_le_of_wSupNorm_le 0 hB h z
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rwa [hj0, one_mul] at h1

private theorem wSupNorm_zero_le_of_norm_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (h : ∀ z : Plane, ‖f z‖ ≤ B) :
    wSupNorm 0 f ≤ ENNReal.ofReal B := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h z)

private theorem wCellL2_zero_le_of_weight4_and_sup {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c A B : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (f : Plane → E)
    (h4 : ∀ z : Plane, (1 + z.2 ^ 2) ^ 2 * ‖f z‖ ≤ A)
    (h0 : ∀ z : Plane, ‖f z‖ ≤ B) :
    wCellL2 c 0 f ≤ ENNReal.ofReal (Real.sqrt (c * ((A * B) * Real.pi))) := by
  set M : ℝ := Real.sqrt (A * B)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hpt : ∀ z : Plane, Real.sqrt (jap 0 z) * ‖f z‖ ≤ M * (1 + z.2 ^ 2)⁻¹ := by
    intro z
    have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
    rw [hj0, one_mul]
    have h1z : 0 < 1 + z.2 ^ 2 := by positivity
    have hsq : ((1 + z.2 ^ 2) * ‖f z‖) ^ 2 ≤ A * B := by
      calc ((1 + z.2 ^ 2) * ‖f z‖) ^ 2
          = ((1 + z.2 ^ 2) ^ 2 * ‖f z‖) * ‖f z‖ := by ring
        _ ≤ A * B := mul_le_mul (h4 z) (h0 z) (norm_nonneg _) hA
    have hle : (1 + z.2 ^ 2) * ‖f z‖ ≤ M := by
      dsimp [M]
      exact (Real.le_sqrt (by positivity) (mul_nonneg hA hB)).2 hsq
    calc ‖f z‖
        = ((1 + z.2 ^ 2) * ‖f z‖) * (1 + z.2 ^ 2)⁻¹ := by field_simp [h1z.ne']
      _ ≤ M * (1 + z.2 ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hle (inv_nonneg.2 h1z.le)
  have hL2 := wCellL2_le_of_inv_one_add_sq hc hM 0 f hpt
  have hM2 : M ^ 2 = A * B := Real.sq_sqrt (mul_nonneg hA hB)
  rwa [hM2] at hL2

/-! ### 3. Divergence and Laplacian identities for `P = tr.p - pc` -/

private theorem contDiff_slice_vec {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (F r) :=
  contDiffOn_univ.1 (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => mem_UU hr))

private theorem div_add_vec {A B : Plane → Vec}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (z : Plane) :
    Cyl.divergence (fun w => A w + B w) z = Cyl.divergence A z + Cyl.divergence B z := by
  have hA0 : ContDiff ℝ ∞ (fun w => A w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hA
  have hB0 : ContDiff ℝ ∞ (fun w => B w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hB
  have hA1 : ContDiff ℝ ∞ (fun w => A w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hA
  have hB1 : ContDiff ℝ ∞ (fun w => B w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hB
  have hq : Cyl.partialQ (fun w => (A w + B w) 0) z =
      Cyl.partialQ (fun w => A w 0) z + Cyl.partialQ (fun w => B w 0) z := by
    have hfun : (fun w => (A w + B w) 0) = fun w => A w 0 + B w 0 :=
      funext fun w => by simp [PiLp.add_apply]
    rw [hfun]
    exact PartI_T20_1.partialQ_add hA0 hB0 z
  have he : Cyl.partialEta (fun w => (A w + B w) 1) z =
      Cyl.partialEta (fun w => A w 1) z + Cyl.partialEta (fun w => B w 1) z := by
    have hfun : (fun w => (A w + B w) 1) = fun w => A w 1 + B w 1 :=
      funext fun w => by simp [PiLp.add_apply]
    rw [hfun]
    exact PartI_T20_1.partialEta_add hA1 hB1 z
  unfold Cyl.divergence
  rw [hq, he]
  ring

private theorem div_sub_vec {A B : Plane → Vec}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (z : Plane) :
    Cyl.divergence (fun w => A w - B w) z = Cyl.divergence A z - Cyl.divergence B z := by
  have hA0 : ContDiff ℝ ∞ (fun w => A w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hA
  have hB0 : ContDiff ℝ ∞ (fun w => B w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hB
  have hA1 : ContDiff ℝ ∞ (fun w => A w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hA
  have hB1 : ContDiff ℝ ∞ (fun w => B w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hB
  have hq : Cyl.partialQ (fun w => (A w - B w) 0) z =
      Cyl.partialQ (fun w => A w 0) z - Cyl.partialQ (fun w => B w 0) z := by
    have hfun : (fun w => (A w - B w) 0) = fun w => A w 0 - B w 0 :=
      funext fun w => by simp [PiLp.sub_apply]
    rw [hfun]
    exact PartI_T20_1.derivWord_sub hA0 hB0 [true] z
  have he : Cyl.partialEta (fun w => (A w - B w) 1) z =
      Cyl.partialEta (fun w => A w 1) z - Cyl.partialEta (fun w => B w 1) z := by
    have hfun : (fun w => (A w - B w) 1) = fun w => A w 1 - B w 1 :=
      funext fun w => by simp [PiLp.sub_apply]
    rw [hfun]
    exact PartI_T20_1.derivWord_sub hA1 hB1 [false] z
  unfold Cyl.divergence
  rw [hq, he]
  ring

private theorem div_smul_vecLaplacian_eq_zero {u : Plane → Vec}
    (hu : ContDiff ℝ ∞ u) (hdiv : ∀ w : Plane, Cyl.divergence u w = 0)
    (ν : ℝ) (z : Plane) :
    Cyl.divergence (fun w => ν • Train.vecLaplacian u w) z = 0 := by
  have hu0 : ContDiff ℝ ∞ (fun w => u w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hu1 : ContDiff ℝ ∞ (fun w => u w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hq_smul : Cyl.partialQ (fun w => (ν • Train.vecLaplacian u w) 0) z =
      ν * Cyl.partialQ (Train.lapS (fun w => u w 0)) z := by
    have hfun : (fun q => (ν • Train.vecLaplacian u (q, z.2)) 0) =
        fun q => ν * Train.lapS (fun w => u w 0) (q, z.2) := by
      funext q
      simp [Train.vecLaplacian, Train.toVec_zero]
    show deriv (fun q => (ν • Train.vecLaplacian u (q, z.2)) 0) z.1 = _
    rw [hfun, deriv_const_mul_field ν]
    rfl
  have he_smul : Cyl.partialEta (fun w => (ν • Train.vecLaplacian u w) 1) z =
      ν * Cyl.partialEta (Train.lapS (fun w => u w 1)) z := by
    have hfun : (fun e => (ν • Train.vecLaplacian u (z.1, e)) 1) =
        fun e => ν * Train.lapS (fun w => u w 1) (z.1, e) := by
      funext e
      simp [Train.vecLaplacian, Train.toVec_one]
    show deriv (fun e => (ν • Train.vecLaplacian u (z.1, e)) 1) z.2 = _
    rw [hfun, deriv_const_mul_field ν]
    rfl
  have hcomm0 : Cyl.partialQ (Train.lapS (fun w => u w 0)) z =
      Train.lapS (Cyl.partialQ (fun w => u w 0)) z :=
    (PartI_T20_1.derivWord_lapS_comm hu0 [true] z).symm
  have hcomm1 : Cyl.partialEta (Train.lapS (fun w => u w 1)) z =
      Train.lapS (Cyl.partialEta (fun w => u w 1)) z :=
    (PartI_T20_1.derivWord_lapS_comm hu1 [false] z).symm
  have hQ0 : ContDiff ℝ ∞ (Cyl.partialQ (fun w => u w 0)) :=
    B0151.contDiff_derivWord hu0 [true]
  have hE1 : ContDiff ℝ ∞ (Cyl.partialEta (fun w => u w 1)) :=
    B0151.contDiff_derivWord hu1 [false]
  have hlap_add : Train.lapS (Cyl.partialQ (fun w => u w 0)) z +
      Train.lapS (Cyl.partialEta (fun w => u w 1)) z =
      Train.lapS (Cyl.divergence u) z := by
    unfold Train.lapS Cyl.divergence
    have h1 := (PartI_T20_1.derivWord_add hQ0 hE1 [true, true] z).symm
    have h2 := (PartI_T20_1.derivWord_add hQ0 hE1 [false, false] z).symm
    change B0151.derivWord [true, true] (Cyl.partialQ (fun w => u w 0)) z +
        B0151.derivWord [false, false] (Cyl.partialQ (fun w => u w 0)) z +
        (B0151.derivWord [true, true] (Cyl.partialEta (fun w => u w 1)) z +
          B0151.derivWord [false, false] (Cyl.partialEta (fun w => u w 1)) z) =
      B0151.derivWord [true, true]
          (fun w => Cyl.partialQ (fun y => u y 0) w + Cyl.partialEta (fun y => u y 1) w) z +
        B0151.derivWord [false, false]
          (fun w => Cyl.partialQ (fun y => u y 0) w + Cyl.partialEta (fun y => u y 1) w) z
    linarith [h1, h2]
  have hdiv_fun : Cyl.divergence u = fun _ => (0 : ℝ) := funext hdiv
  have hlap_zero : Train.lapS (fun _ : Plane => (0 : ℝ)) z = 0 := by
    show deriv (fun q => deriv (fun _ : ℝ => (0 : ℝ)) q) z.1 +
      deriv (fun e => deriv (fun _ : ℝ => (0 : ℝ)) e) z.2 = 0
    simp [deriv_const]
  unfold Cyl.divergence
  rw [hq_smul, he_smul, hcomm0, hcomm1, ← mul_add, hlap_add, hdiv_fun, hlap_zero, mul_zero]

private theorem deriv_vec_apply {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {r : ℝ} (hr : 0 < r) (w : Plane) (k : Fin 2) :
    deriv (fun t => F t w) r k = deriv (fun t => F t w k) r := by
  have hd : DifferentiableAt ℝ (fun t => F t w) r :=
    (UnforcedLeray.Short.IIb.hasDerivAt_slice hF hr w).differentiableAt
  exact (((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt r hd.hasDerivAt).deriv.symm

private theorem div_deriv_slice_eq_zero {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2))
    (hdiv : ∀ t : ℝ, 0 < t → ∀ w : Plane, Cyl.divergence (F t) w = 0)
    {r : ℝ} (hr : 0 < r) (z : Plane) :
    Cyl.divergence (fun w => deriv (fun t => F t w) r) z = 0 := by
  have hF0 : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hF
  have hF1 : PartI_T20.SmR (fun x : ℝ × Plane => F x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hF
  have hq_eq : (fun w => deriv (fun t => F t w) r 0) =
      fun w => iteratedDeriv 1 (fun t => F t w 0) r := by
    funext w
    rw [deriv_vec_apply hF hr w 0, iteratedDeriv_one]
  have he_eq : (fun w => deriv (fun t => F t w) r 1) =
      fun w => iteratedDeriv 1 (fun t => F t w 1) r := by
    funext w
    rw [deriv_vec_apply hF hr w 1, iteratedDeriv_one]
  have hq_comm := (PartI_T20.iteratedDeriv_partialQ_eq (F := fun t w => F t w 0) hF0 1 hr z).symm
  have he_comm := (PartI_T20.iteratedDeriv_partialEta_eq (F := fun t w => F t w 1) hF1 1 hr z).symm
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => F x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun t w => F t w 0) hF0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => F x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun t w => F t w 1) hF1
  have hdQ : DifferentiableAt ℝ (fun t => Cyl.partialQ (fun w => F t w 0) z) r :=
    (hasDerivAt_sliceS hQ0 hr z).differentiableAt
  have hdE : DifferentiableAt ℝ (fun t => Cyl.partialEta (fun w => F t w 1) z) r :=
    (hasDerivAt_sliceS hE1 hr z).differentiableAt
  unfold Cyl.divergence
  rw [hq_eq, he_eq, hq_comm, he_comm, iteratedDeriv_one, iteratedDeriv_one, ← deriv_add hdQ hdE]
  change deriv (fun t => Cyl.partialQ (fun w => F t w 0) z +
    Cyl.partialEta (fun w => F t w 1) z) r = 0
  have hev : (fun t => Cyl.partialQ (fun w => F t w 0) z +
      Cyl.partialEta (fun w => F t w 1) z) =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht using hdiv t ht z
  rw [hev.deriv_eq, deriv_const]

/-- Pointwise Laplacian identity for `P r w = tr.p r w - pc ν c r w` on `r > 0`:
`Train.lapS (P r) z = -Cyl.divergence (advDiff r + qcDiv r) z`. -/
private theorem lapS_P_eq_neg_div_rhs {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hν : 0 < ν) (hc : 0 < c) {r : ℝ} (hr : 0 < r) (z : Plane) :
    Train.lapS (fun w => tr.p r w - pc ν c r w) z =
      -Cyl.divergence (fun w =>
        (Train.advection (tr.v r) w - Train.advection (Vc ν c r) w) +
          Train.matDiv (Train.Qc ν c r) w) z := by
  let dv : ℝ → Plane → Vec := fun t w => tr.v t w - Vc ν c t w
  let G₁ : ℝ → Plane → Vec := fun t w => ν • Train.vecLaplacian (dv t) w
  let G₂ : ℝ → Plane → Vec := fun t w => deriv (fun s => dv s w) t
  let G₃ : ℝ → Plane → Vec := fun t w => Train.advection (tr.v t) w - Train.advection (Vc ν c t) w
  let G₄ : ℝ → Plane → Vec := fun t w => Train.matDiv (Train.Qc ν c t) w
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc
  have hsm_dv : Sm (fun x : ℝ × Plane => dv x.1 x.2) := hsm_v.sub hsm_Vc
  have hcd_dv : ContDiff ℝ ∞ (dv r) := contDiff_slice_vec (F := dv) hsm_dv hr
  have hcd₁ : ContDiff ℝ ∞ (G₁ r) :=
    contDiff_slice_vec (F := G₁) (PartI_T25_1.sm_smul_vecLaplacian hsm_dv ν) hr
  have hcd₂ : ContDiff ℝ ∞ (G₂ r) :=
    contDiff_slice_vec (F := G₂) (PartI_T25_3.sm_deriv_slice hsm_dv) hr
  have hcd₃ : ContDiff ℝ ∞ (G₃ r) :=
    contDiff_slice_vec (F := G₃)
      ((PartI_T25_1.sm_advection hsm_v).sub (PartI_T25_1.sm_advection hsm_Vc)) hr
  have hcd₄ : ContDiff ℝ ∞ (G₄ r) :=
    contDiff_slice_vec (F := G₄) (trainFixedBandQcDivAgeJet_proof.1 ν c hν hc) hr
  have hdiv_dv : ∀ t : ℝ, 0 < t → ∀ w : Plane, Cyl.divergence (dv t) w = 0 := by
    intro t ht w
    have hcd_vt : ContDiff ℝ ∞ (tr.v t) := contDiff_slice_vec (F := tr.v) hsm_v ht
    have hcd_Vct : ContDiff ℝ ∞ (Vc ν c t) := contDiff_slice_vec (F := Vc ν c) hsm_Vc ht
    rw [div_sub_vec hcd_vt hcd_Vct w, tr.isTrain.solenoidal t ht.le w,
      UnforcedLeray.Train.Vc_div hν hc.ne' ht.le w, sub_self]
  have hlap_eq_div : Train.lapS (fun w => tr.p r w - pc ν c r w) z =
      Cyl.divergence (Train.gradS (fun w => tr.p r w - pc ν c r w)) z := by
    simp [Cyl.divergence, Train.gradS, Train.lapS, toVec_zero, toVec_one]
  have hdp_fun : Train.gradS (fun w => tr.p r w - pc ν c r w) =
      fun w => (G₁ r w - G₂ r w) - (G₃ r w + G₄ r w) := by
    funext w
    rw [PartI_T25_3.dp_eq_error_rhs tr hν hc.ne' hr w]
    ext k
    simp only [G₁, G₂, G₃, G₄, dv, PiLp.sub_apply, PiLp.add_apply]
    ring
  rw [hlap_eq_div, hdp_fun, div_sub_vec (hcd₁.sub hcd₂) (hcd₃.add hcd₄) z,
    div_sub_vec hcd₁ hcd₂ z, div_smul_vecLaplacian_eq_zero hcd_dv (hdiv_dv r hr) ν z,
    div_deriv_slice_eq_zero hsm_dv hdiv_dv hr z, sub_zero, zero_sub]

private theorem smR_divergence {G : ℝ → Plane → Vec}
    (hG : Sm (fun x : ℝ × Plane => G x.1 x.2)) :
    PartI_T20.SmR (fun x : ℝ × Plane => Cyl.divergence (G x.1) x.2) := by
  have hG0 : PartI_T20.SmR (fun x : ℝ × Plane => G x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hG1 : PartI_T20.SmR (fun x : ℝ × Plane => G x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  exact (PartI_T20.smR_partialQ (F := fun r w => G r w 0) hG0).add
    (PartI_T20.smR_partialEta (F := fun r w => G r w 1) hG1)

private theorem norm_ageJet_divergence_le {G : ℝ → Plane → Vec}
    (hG : Sm (fun x : ℝ × Plane => G x.1 x.2))
    (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ k (fun r w => Cyl.divergence (G r) w) s z‖ ≤
      2 * ‖ageJet ℓ (k + 1) G s z‖ := by
  have hG0 : PartI_T20.SmR (fun x : ℝ × Plane => G x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hG1 : PartI_T20.SmR (fun x : ℝ × Plane => G x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => G x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => G r w 0) hG0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => G x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => G r w 1) hG1
  have hadd := PartI_T20.ageJet_add
    (fun r w => Cyl.partialQ (fun y => G r y 0) w)
    (fun r w => Cyl.partialEta (fun y => G r y 1) w)
    hQ0 hE1 hs ℓ k z
  have hfun : (fun r w => Cyl.divergence (G r) w) =
      fun r w => Cyl.partialQ (fun y => G r y 0) w + Cyl.partialEta (fun y => G r y 1) w := rfl
  have hb0 : ‖ageJet ℓ k (fun r w => Cyl.partialQ (fun y => G r y 0) w) s z‖ ≤
      ‖ageJet ℓ (k + 1) G s z‖ :=
    (PartI_T20.norm_ageJet_partialQ_le (F := fun r w => G r w 0) hG0 ℓ k hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hG 0 ℓ (k + 1) hs z)
  have hb1 : ‖ageJet ℓ k (fun r w => Cyl.partialEta (fun y => G r y 1) w) s z‖ ≤
      ‖ageJet ℓ (k + 1) G s z‖ :=
    (PartI_T20.norm_ageJet_partialEta_le (F := fun r w => G r w 1) hG1 ℓ k hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hG 1 ℓ (k + 1) hs z)
  rw [hfun, hadd]
  have htri := norm_add_le
    (ageJet ℓ k (fun r w => Cyl.partialQ (fun y => G r y 0) w) s z)
    (ageJet ℓ k (fun r w => Cyl.partialEta (fun y => G r y 1) w) s z)
  linarith

/-! ### 4. Horizontal mean identity and bound for `B0151.derivWord w P_ℓ` -/

private theorem hmean_add_cont (c : ℝ) {f g : Plane → ℝ}
    (hf : Continuous f) (hg : Continuous g) (η : ℝ) :
    hmean c (fun z => f z + g z) η = hmean c f η + hmean c g η := by
  unfold hmean
  have hfi : IntegrableOn (fun q => f (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hf.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have hgi : IntegrableOn (fun q => g (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hg.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  rw [integral_add hfi hgi, smul_add]

private theorem hmean_sub_cont (c : ℝ) {f g : Plane → ℝ}
    (hf : Continuous f) (hg : Continuous g) (η : ℝ) :
    hmean c (fun z => f z - g z) η = hmean c f η - hmean c g η := by
  unfold hmean
  have hfi : IntegrableOn (fun q => f (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hf.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have hgi : IntegrableOn (fun q => g (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hg.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  rw [integral_sub hfi hgi, smul_sub]

private theorem isPeriodic_advection {c : ℝ} {u : Plane → Vec}
    (hper : Cyl.IsPeriodic c u) : Cyl.IsPeriodic c (Train.advection u) := by
  intro z
  have hp0 : Cyl.IsPeriodic c (fun w => u w 0) := fun w => congrArg (fun v : Vec => v 0) (hper w)
  have hp1 : Cyl.IsPeriodic c (fun w => u w 1) := fun w => congrArg (fun v : Vec => v 1) (hper w)
  have hu0 : u (z.1 + c, z.2) 0 = u z 0 := hp0 z
  have hu1 : u (z.1 + c, z.2) 1 = u z 1 := hp1 z
  have hq0 : Cyl.partialQ (fun w => u w 0) (z.1 + c, z.2) = Cyl.partialQ (fun w => u w 0) z :=
    PartI_T20_1.isPeriodic_derivWord hp0 [true] z
  have he0 : Cyl.partialEta (fun w => u w 0) (z.1 + c, z.2) = Cyl.partialEta (fun w => u w 0) z :=
    PartI_T20_1.isPeriodic_derivWord hp0 [false] z
  have hq1 : Cyl.partialQ (fun w => u w 1) (z.1 + c, z.2) = Cyl.partialQ (fun w => u w 1) z :=
    PartI_T20_1.isPeriodic_derivWord hp1 [true] z
  have he1 : Cyl.partialEta (fun w => u w 1) (z.1 + c, z.2) = Cyl.partialEta (fun w => u w 1) z :=
    PartI_T20_1.isPeriodic_derivWord hp1 [false] z
  change Train.advection u (z.1 + c, z.2) = Train.advection u z
  unfold Train.advection
  rw [hu0, hu1, hq0, he0, hq1, he1]

/-- For `r > 0`, the horizontal mean of `Cyl.partialEta (tr.p r - pc ν c r)` equals the negative
horizontal mean of the vertical component of `advDiff r + qcDiv r`. -/
private theorem hmean_partialEta_P_eq {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    hmean c (Cyl.partialEta (fun w => tr.p r w - pc ν c r w)) η =
      -hmean c (fun w =>
        ((Train.advection (tr.v r) w - Train.advection (Vc ν c r) w) +
          Train.matDiv (Train.Qc ν c r) w) 1) η := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : PartI_T20.SmR (fun x : ℝ × Plane => pc ν c x.1 x.2) :=
    PartI_T25_3.smS_pc hν hc
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc
  have hp_cd : ContDiff ℝ ∞ (tr.p r) := PartI_T20.contDiff_slice_of_smR hsm_p hr
  have hpc_cd : ContDiff ℝ ∞ (pc ν c r) := PartI_T20.contDiff_slice_of_smR hsm_pc hr
  have hv_cd : ContDiff ℝ ∞ (tr.v r) := contDiff_slice_vec (F := tr.v) hsm_v hr
  have hv0_cd : ContDiff ℝ ∞ (fun w => tr.v r w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_cd
  have hv1_cd : ContDiff ℝ ∞ (fun w => tr.v r w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_cd
  have hsq_cd : ContDiff ℝ ∞ (fun w => tr.v r w 1 ^ 2) := hv1_cd.pow 2
  have hp_per : Cyl.IsPeriodic c (tr.p r) := tr.isTrain.periodic_p r hr.le
  have hsq_per : Cyl.IsPeriodic c (fun w => tr.v r w 1 ^ 2) := fun z =>
    congrArg (fun v : Vec => v 1 ^ 2) (tr.isTrain.periodic_v r hr.le z)
  have hsub_eta : Cyl.partialEta (fun w => tr.p r w - pc ν c r w) =
      fun w => Cyl.partialEta (tr.p r) w - Cyl.partialEta (pc ν c r) w :=
    funext fun w => PartI_T20_1.derivWord_sub hp_cd hpc_cd [false] w
  have h1 : hmean c (Cyl.partialEta (fun w => tr.p r w - pc ν c r w)) η =
      hmean c (Cyl.partialEta (tr.p r)) η - hmean c (Cyl.partialEta (pc ν c r)) η := by
    rw [hsub_eta]
    exact hmean_sub_cont c (f := Cyl.partialEta (tr.p r)) (g := Cyl.partialEta (pc ν c r))
      (B0151.contDiff_derivWord hp_cd [false]).continuous
      (B0151.contDiff_derivWord hpc_cd [false]).continuous η
  have h2 : hmean c (Cyl.partialEta (tr.p r)) η =
      -hmean c (Cyl.partialEta (fun w => tr.v r w 1 ^ 2)) η :=
    PartI_T20_1.hmean_derivWord_neg_eq hc hp_cd hsq_cd hp_per hsq_per
      (PartI_T20_1.train_hmean_p_eq_neg_v1_sq hν hc1 tr htr hr) [false] η
  have hadv_v_eq : (fun w => Train.advection (tr.v r) w 1) =
      fun w => Cyl.partialQ (fun y => tr.v r y 0 * tr.v r y 1) w +
        Cyl.partialEta (fun y => tr.v r y 1 ^ 2) w := by
    funext w
    have hd0 : Differentiable ℝ (fun y => tr.v r y 0) := hv0_cd.differentiable (by simp)
    have hd1 : Differentiable ℝ (fun y => tr.v r y 1) := hv1_cd.differentiable (by simp)
    have hQ := mm_partialQ_mul hd0 hd1 w
    have hE := mm_partialEta_mul hd1 hd1 w
    have hsq_fn : (fun y : Plane => tr.v r y 1 ^ 2) = fun y => tr.v r y 1 * tr.v r y 1 :=
      funext fun _ => sq _
    have hdiv : Cyl.partialQ (fun y => tr.v r y 0) w +
        Cyl.partialEta (fun y => tr.v r y 1) w = 0 := tr.isTrain.solenoidal r hr.le w
    rw [hsq_fn, hQ, hE]
    simp only [Train.advection, toVec_one]
    linear_combination -(tr.v r w 1) * hdiv
  have hprod_cd : ContDiff ℝ ∞ (fun y => tr.v r y 0 * tr.v r y 1) := hv0_cd.mul hv1_cd
  have hprod_per : Cyl.IsPeriodic c (fun y => tr.v r y 0 * tr.v r y 1) := fun z => by
    simp only [tr.isTrain.periodic_v r hr.le z]
  have h3 : hmean c (fun w => Train.advection (tr.v r) w 1) η =
      hmean c (Cyl.partialEta (fun y => tr.v r y 1 ^ 2)) η := by
    rw [hadv_v_eq, hmean_add_cont c
      (f := Cyl.partialQ (fun y => tr.v r y 0 * tr.v r y 1))
      (g := Cyl.partialEta (fun y => tr.v r y 1 ^ 2))
      (B0151.contDiff_derivWord hprod_cd [true]).continuous
      (B0151.contDiff_derivWord hsq_cd [false]).continuous η,
      PartI_T20_1.hmean_partialQ_zero hc (hprod_cd.of_le (by simp)) hprod_per η, zero_add]
  have hpc_eta_eq : Cyl.partialEta (pc ν c r) =
      fun w => Train.matDiv (Train.Qc ν c r) w 1 - Train.advection (Vc ν c r) w 1 := by
    funext w
    have h := congrArg (fun v : Vec => v 1) (PartI_T25_3.gradS_pc_eq hν hc.ne' hr.le w)
    simpa [Train.gradS, toVec_one, PiLp.sub_apply] using h
  have hqc1_cd : ContDiff ℝ ∞ (fun w => Train.matDiv (Train.Qc ν c r) w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp
      (contDiff_slice_vec (F := fun t w => Train.matDiv (Train.Qc ν c t) w)
        (trainFixedBandQcDivAgeJet_proof.1 ν c hν hc) hr)
  have hadv_Vc1_cd : ContDiff ℝ ∞ (fun w => Train.advection (Vc ν c r) w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp
      (contDiff_slice_vec (F := fun t w => Train.advection (Vc ν c t) w)
        (PartI_T25_1.sm_advection hsm_Vc) hr)
  have hadv_v1_cd : ContDiff ℝ ∞ (fun w => Train.advection (tr.v r) w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp
      (contDiff_slice_vec (F := fun t w => Train.advection (tr.v t) w)
        (PartI_T25_1.sm_advection hsm_v) hr)
  have hqc1_cont : Continuous (fun w => Train.matDiv (Train.Qc ν c r) w 1) := hqc1_cd.continuous
  have hadv_Vc1_cont : Continuous (fun w => Train.advection (Vc ν c r) w 1) := hadv_Vc1_cd.continuous
  have hadv_v1_cont : Continuous (fun w => Train.advection (tr.v r) w 1) := hadv_v1_cd.continuous
  have h4 : hmean c (Cyl.partialEta (pc ν c r)) η =
      hmean c (fun w => Train.matDiv (Train.Qc ν c r) w 1) η -
        hmean c (fun w => Train.advection (Vc ν c r) w 1) η := by
    rw [hpc_eta_eq]
    exact hmean_sub_cont c hqc1_cont hadv_Vc1_cont η
  have h5 : hmean c (fun w =>
        ((Train.advection (tr.v r) w - Train.advection (Vc ν c r) w) +
          Train.matDiv (Train.Qc ν c r) w) 1) η =
      (hmean c (fun w => Train.advection (tr.v r) w 1) η -
        hmean c (fun w => Train.advection (Vc ν c r) w 1) η) +
        hmean c (fun w => Train.matDiv (Train.Qc ν c r) w 1) η := by
    have hfun : (fun w =>
        ((Train.advection (tr.v r) w - Train.advection (Vc ν c r) w) +
          Train.matDiv (Train.Qc ν c r) w) 1) =
        fun w => (Train.advection (tr.v r) w 1 - Train.advection (Vc ν c r) w 1) +
          Train.matDiv (Train.Qc ν c r) w 1 :=
      funext fun w => by
        rw [PiLp.add_apply, PiLp.sub_apply]
    have hdiff_cont : Continuous (fun w =>
        Train.advection (tr.v r) w 1 - Train.advection (Vc ν c r) w 1) :=
      hadv_v1_cont.sub hadv_Vc1_cont
    rw [hfun, hmean_add_cont c hdiff_cont hqc1_cont η,
      hmean_sub_cont c hadv_v1_cont hadv_Vc1_cont η]
  linarith [h1, h2, h3, h4, h5]

/-- Horizontal-mean bound for word derivatives `B0151.derivWord w P_ℓ` of length `j + 1`. -/
private theorem abs_hmean_derivWord_P_le {ν c M_R : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMR : 0 ≤ M_R)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ j : ℕ) {w : List Bool} (hw : w.length = j + 1) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hR_bd : ∀ y : Plane,
      ‖ageJet ℓ j (fun r w' =>
        (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
          Train.matDiv (Train.Qc ν c r) w') s y‖ ≤ M_R) :
    |hmean c (B0151.derivWord w
      (fun z' => iteratedDeriv ℓ (fun r => tr.p r z' - pc ν c r z') s)) z.2| ≤ M_R := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let P : ℝ → Plane → ℝ := fun r w' => tr.p r w' - pc ν c r w'
  let F_rhs : ℝ → Plane → Vec := fun r w' =>
    (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
      Train.matDiv (Train.Qc ν c r) w'
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : PartI_T20.SmR (fun x : ℝ × Plane => pc ν c x.1 x.2) :=
    PartI_T25_3.smS_pc hν hc
  have hsm_P : PartI_T20.SmR (fun x : ℝ × Plane => P x.1 x.2) := hsm_p.sub hsm_pc
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => P r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_P ℓ hs
  have hP_per : Cyl.IsPeriodic c P_ℓ := by
    refine PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
    dsimp [P]
    rw [tr.isTrain.periodic_p r hr.le z', UnforcedLeray.Train.pc_periodic ν c r z']
  rcases w with _ | ⟨b, w'⟩
  · cases hw
  · have hw' : w'.length = j := Nat.succ.inj hw
    cases b
    · -- `b = false`: `B0151.derivWord (false :: w') P_ℓ = B0151.derivWord w' (Cyl.partialEta P_ℓ)`
      have hcomm : B0151.derivWord (false :: w') P_ℓ = B0151.derivWord w' (Cyl.partialEta P_ℓ) :=
        PartI_T20_1.derivWord_partialEta_comm hP_sm w'
      rw [hcomm]
      have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
        tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
      have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc
      have hsm_rhs : Sm (fun x : ℝ × Plane => F_rhs x.1 x.2) :=
        ((PartI_T25_1.sm_advection hsm_v).sub (PartI_T25_1.sm_advection hsm_Vc)).add
          (trainFixedBandQcDivAgeJet_proof.1 ν c hν hc)
      have hsm_rhs1 : PartI_T20.SmR (fun x : ℝ × Plane => F_rhs x.1 x.2 1) :=
        (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_rhs
      have hsm_etaP : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (P x.1) x.2) :=
        PartI_T20.smR_partialEta (F := P) hsm_P
      let E_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => Cyl.partialEta (P r) z') s
      let G_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => F_rhs r z' 1) s
      have hE_eq : Cyl.partialEta P_ℓ = E_ℓ :=
        funext fun z' => (PartI_T20.iteratedDeriv_partialEta_eq hsm_P ℓ hs z').symm
      rw [hE_eq]
      have hE_sm : ContDiff ℝ ∞ E_ℓ :=
        PartI_T20_1.contDiff_iteratedDeriv_slice (F := fun r z' => Cyl.partialEta (P r) z')
          hsm_etaP ℓ hs
      have hG_sm : ContDiff ℝ ∞ G_ℓ :=
        PartI_T20_1.contDiff_iteratedDeriv_slice (F := fun r z' => F_rhs r z' 1) hsm_rhs1 ℓ hs
      have hE_per : Cyl.IsPeriodic c E_ℓ := by
        rw [← hE_eq]
        exact PartI_T20_1.isPeriodic_derivWord hP_per [false]
      have hG_per : Cyl.IsPeriodic c G_ℓ := by
        refine PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
        have hper_v := tr.isTrain.periodic_v r hr.le
        have hper_Vc := UnforcedLeray.Train.Vc_periodic ν c r
        have hper_adv_v := isPeriodic_advection hper_v z'
        have hper_adv_Vc := isPeriodic_advection hper_Vc z'
        have hper_qc : Train.matDiv (Train.Qc ν c r) (z'.1 + c, z'.2) =
            Train.matDiv (Train.Qc ν c r) z' := by
          have h1 := PartI_T25_3.gradS_pc_eq hν hc.ne' hr.le (z'.1 + c, z'.2)
          have h2 := PartI_T25_3.gradS_pc_eq hν hc.ne' hr.le z'
          have hper_gpc : Train.gradS (pc ν c r) (z'.1 + c, z'.2) = Train.gradS (pc ν c r) z' := by
            ext m
            fin_cases m
            · simp only [Train.gradS]
              exact PartI_T20_1.isPeriodic_derivWord (UnforcedLeray.Train.pc_periodic ν c r) [true] z'
            · simp only [Train.gradS]
              exact PartI_T20_1.isPeriodic_derivWord (UnforcedLeray.Train.pc_periodic ν c r) [false] z'
          ext m
          have hm1 := congrArg (fun v : Vec => v m) h1
          have hm2 := congrArg (fun v : Vec => v m) h2
          have hm_gpc := congrArg (fun v : Vec => v m) hper_gpc
          have hm_adv := congrArg (fun v : Vec => v m) hper_adv_Vc
          simp only [PiLp.sub_apply] at hm1 hm2
          linarith
        dsimp [F_rhs]
        rw [hper_adv_v, hper_adv_Vc, hper_qc]
      have hmean_eq : ∀ η : ℝ, hmean c E_ℓ η = -hmean c G_ℓ η := by
        intro η
        rw [← PartI_T20_1.iteratedDeriv_hmean_eq hc (F := fun r z' => Cyl.partialEta (P r) z')
            hsm_etaP ℓ hs η,
          ← PartI_T20_1.iteratedDeriv_hmean_eq hc (F := fun r z' => F_rhs r z' 1)
            hsm_rhs1 ℓ hs η,
          ← iteratedDeriv_neg]
        have hev : (fun r => hmean c (Cyl.partialEta (P r)) η) =ᶠ[𝓝 s]
            fun r => -hmean c (fun z' => F_rhs r z' 1) η := by
          filter_upwards [Ioi_mem_nhds hs] with r hr using
            hmean_partialEta_P_eq hν hc1 tr htr hr η
        exact hev.iteratedDeriv_eq ℓ
      have hword_eq :=
        PartI_T20_1.hmean_derivWord_neg_eq hc hE_sm hG_sm hE_per hG_per hmean_eq w' z.2
      rw [hword_eq, abs_neg]
      refine cylpHmeanAbsLe hc (fun y => ?_) z.2
      calc |B0151.derivWord w' G_ℓ y|
          ≤ ‖ageJet ℓ j (fun r z' => F_rhs r z' 1) s y‖ :=
            PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => F_rhs r z' 1)
              hsm_rhs1 ℓ j hw' hs y
        _ ≤ ‖ageJet ℓ j F_rhs s y‖ :=
            PartI_T20.norm_ageJet_vec_proj_le hsm_rhs 1 ℓ j hs y
        _ ≤ M_R := hR_bd y
    · -- `b = true`: `B0151.derivWord (true :: w') P_ℓ = Cyl.partialQ (B0151.derivWord w' P_ℓ)`
      have hwf : ContDiff ℝ 1 (B0151.derivWord w' P_ℓ) :=
        (B0151.contDiff_derivWord hP_sm w').of_le (by simp)
      have hpf : Cyl.IsPeriodic c (B0151.derivWord w' P_ℓ) :=
        PartI_T20_1.isPeriodic_derivWord hP_per w'
      change |hmean c (Cyl.partialQ (B0151.derivWord w' P_ℓ)) z.2| ≤ M_R
      rw [PartI_T20_1.hmean_partialQ_zero hc hwf hpf z.2, abs_zero]
      exact hMR

/-! ### 5. Oscillating-part bound and pointwise `dp` bound -/

private theorem abs_lapS_derivWord_P_le {ν c M_R : ℝ}
    (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hR_bd : ‖ageJet ℓ (k + 1) (fun r w' =>
      (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
        Train.matDiv (Train.Qc ν c r) w') s z‖ ≤ M_R) :
    |Train.lapS (B0151.derivWord w
      (fun z' => iteratedDeriv ℓ (fun r => tr.p r z' - pc ν c r z') s)) z| ≤
      2 * M_R := by
  let P : ℝ → Plane → ℝ := fun r w' => tr.p r w' - pc ν c r w'
  let F_rhs : ℝ → Plane → Vec := fun r w' =>
    (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
      Train.matDiv (Train.Qc ν c r) w'
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : PartI_T20.SmR (fun x : ℝ × Plane => pc ν c x.1 x.2) :=
    PartI_T25_3.smS_pc hν hc
  have hsm_P : PartI_T20.SmR (fun x : ℝ × Plane => P x.1 x.2) := hsm_p.sub hsm_pc
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc
  have hsm_rhs : Sm (fun x : ℝ × Plane => F_rhs x.1 x.2) :=
    ((PartI_T25_1.sm_advection hsm_v).sub (PartI_T25_1.sm_advection hsm_Vc)).add
      (trainFixedBandQcDivAgeJet_proof.1 ν c hν hc)
  have hsm_div : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.divergence (F_rhs x.1) x.2) :=
    smR_divergence hsm_rhs
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => P r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_P ℓ hs
  have hlap_P : Train.lapS P_ℓ =
      fun z' => -iteratedDeriv ℓ (fun r => Cyl.divergence (F_rhs r) z') s := by
    funext z'
    have h1 := PartI_T20.iteratedDeriv_mul_lapS_eq hsm_P 1 ℓ hs z'
    simp only [one_mul] at h1
    rw [← h1, ← iteratedDeriv_neg]
    have hev : (fun r => Train.lapS (P r) z') =ᶠ[𝓝 s]
        fun r => -Cyl.divergence (F_rhs r) z' := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using lapS_P_eq_neg_div_rhs tr hν hc hr z'
    exact hev.iteratedDeriv_eq ℓ
  rw [PartI_T20_1.derivWord_lapS_comm hP_sm w z, hlap_P, PartI_T20_1.derivWord_neg _ w z, abs_neg]
  calc |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => Cyl.divergence (F_rhs r) z') s) z|
      ≤ ‖ageJet ℓ k (fun r z' => Cyl.divergence (F_rhs r) z') s z‖ :=
        PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet
          (F := fun r z' => Cyl.divergence (F_rhs r) z') hsm_div ℓ k hw hs z
    _ ≤ 2 * ‖ageJet ℓ (k + 1) F_rhs s z‖ :=
        norm_ageJet_divergence_le hsm_rhs ℓ k hs z
    _ ≤ 2 * M_R := mul_le_mul_of_nonneg_left hR_bd zero_le_two

private theorem abs_osc_derivWord_P_le {ν c M_R L_P : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hMR : 0 ≤ M_R)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hP_grad : ∀ y : Plane, ‖ageJet ℓ (k + 1) (fun r w' => tr.p r w' - pc ν c r w') s y‖ ≤ L_P)
    (hR_bd : ∀ y : Plane,
      ‖ageJet ℓ (k + 1) (fun r w' =>
        (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
          Train.matDiv (Train.Qc ν c r) w') s y‖ ≤ M_R) :
    let Q_s : Plane → ℝ :=
      B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z' - pc ν c r z') s)
    |Q_s z - hmean c Q_s z.2| ≤
      ((2 * M_R) * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  intro Q_s
  let P : ℝ → Plane → ℝ := fun r w' => tr.p r w' - pc ν c r w'
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : PartI_T20.SmR (fun x : ℝ × Plane => pc ν c x.1 x.2) :=
    PartI_T25_3.smS_pc hν hc
  have hsm_P : PartI_T20.SmR (fun x : ℝ × Plane => P x.1 x.2) := hsm_p.sub hsm_pc
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => P r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_P ℓ hs
  have hQ_C2 : ContDiff ℝ 2 Q_s := (B0151.contDiff_derivWord hP_sm w).of_le (by simp)
  have hP_per : Cyl.IsPeriodic c P_ℓ := by
    refine PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
    dsimp [P]
    rw [tr.isTrain.periodic_p r hr.le z', UnforcedLeray.Train.pc_periodic ν c r z']
  have hQ_per : Cyl.IsPeriodic c Q_s := PartI_T20_1.isPeriodic_derivWord hP_per w
  have hgrad : ∃ L : ℝ, ∀ y : Plane, |Cyl.partialQ Q_s y| ≤ L ∧ |Cyl.partialEta Q_s y| ≤ L := by
    refine ⟨L_P, fun y => ⟨?_, ?_⟩⟩
    · have hlen_t : (true :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (true :: w) P_ℓ y| ≤ L_P
      exact (PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_P ℓ (k + 1) hlen_t hs y).trans
        (hP_grad y)
    · have hlen_f : (false :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (false :: w) P_ℓ y| ≤ L_P
      exact (PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_P ℓ (k + 1) hlen_f hs y).trans
        (hP_grad y)
  have hlap : ∀ y : Plane, |Train.lapS Q_s y| ≤ 2 * M_R := fun y =>
    abs_lapS_derivWord_P_le hν hc tr ℓ k hw hs y (hR_bd y)
  exact PartI_T20_1.oscLinear_explicit hc (by positivity) hQ_C2 hQ_per hgrad hlap z

/-- Pointwise bound on `ageJet ℓ j dp s z` from `M_R` bounds on `advDiff + qcDiv` at orders `j` and
`j + 2` and a qualitative bound `L_P` on `ageJet ℓ (j + 2) (tr.p - pc) s`. -/
private theorem norm_ageJet_dp_le_of_rhs {ν c C_R CS_R b_R L_P : ℝ} {N_R : ℕ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hCR : 0 < C_R)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s)
    (hP_grad : ∀ y : Plane, ‖ageJet ℓ (j + 2) (fun r w' => tr.p r w' - pc ν c r w') s y‖ ≤ L_P)
    (hR_j : ∀ y : Plane,
      ‖ageJet ℓ j (fun r w' =>
        (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
          Train.matDiv (Train.Qc ν c r) w') s y‖ ≤
        polyP C_R N_R ν c * Real.exp (CS_R / ν - b_R * c ^ 2))
    (hR_j2 : ∀ y : Plane,
      ‖ageJet ℓ (j + 2) (fun r w' =>
        (Train.advection (tr.v r) w' - Train.advection (Vc ν c r) w') +
          Train.matDiv (Train.Qc ν c r) w') s y‖ ≤
        polyP C_R N_R ν c * Real.exp (CS_R / ν - b_R * c ^ 2))
    (z : Plane) :
    let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
    let C_sup : ℝ := 2 * (2 : ℝ) ^ (2 * (j + 1)) * C_R * (1 + (2 / (2 * Real.pi ^ 2)) * S_zeta)
    ‖ageJet ℓ j (fun r w => Train.gradS (fun u => tr.p r u - pc ν c r u) w) s z‖ ≤
      polyP C_sup (N_R + 2) ν c * Real.exp (CS_R / ν - b_R * c ^ 2) := by
  intro S_zeta C_sup
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ X := by dsimp [X]; linarith
  have hcX : c ≤ X := by dsimp [X]; linarith
  let P : ℝ → Plane → ℝ := fun r w => tr.p r w - pc ν c r w
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : SmS (fun x : ℝ × Plane => pc ν c x.1 x.2) := PartI_T25_3.smS_pc hν hc
  have hsm_P : SmS (fun x : ℝ × Plane => P x.1 x.2) := hsm_p.sub hsm_pc
  let M_R : ℝ := polyP C_R N_R ν c * Real.exp (CS_R / ν - b_R * c ^ 2)
  have hMR_nn : 0 ≤ M_R := by dsimp [M_R]; unfold polyP; positivity
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => P r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_P ℓ hs
  let B_word : ℝ := M_R * (1 + (2 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta)
  have hBword_nn : 0 ≤ B_word := by dsimp [B_word]; positivity
  have hword_bd : ∀ w ∈ wordsOfLength (j + 1), |B0151.derivWord w P_ℓ z| ≤ B_word := by
    intro w hw
    have hlen : w.length = j + 1 := by
      unfold wordsOfLength at hw
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
      simp
    have hmean_bd := abs_hmean_derivWord_P_le hν hc1 hMR_nn tr htr ℓ j hlen hs z hR_j
    have hosc_bd := abs_osc_derivWord_P_le hν hc hMR_nn tr ℓ (j + 1) hlen hs z hP_grad hR_j2
    have htri : |B0151.derivWord w P_ℓ z| ≤
        |B0151.derivWord w P_ℓ z - hmean c (B0151.derivWord w P_ℓ) z.2| +
          |hmean c (B0151.derivWord w P_ℓ) z.2| := by
      have := abs_add_le (B0151.derivWord w P_ℓ z - hmean c (B0151.derivWord w P_ℓ) z.2)
        (hmean c (B0151.derivWord w P_ℓ) z.2)
      rwa [sub_add_cancel] at this
    calc |B0151.derivWord w P_ℓ z|
        ≤ ((2 * M_R) * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta + M_R :=
          htri.trans (add_le_add hosc_bd hmean_bd)
      _ = B_word := by dsimp [B_word]; ring
  have hjet_word := (cylJetWord_proof P_ℓ hP_sm (j + 1) z).2
  have hcard_nat : (wordsOfLength (j + 1)).card ≤ 2 ^ (j + 1) := by
    unfold wordsOfLength
    exact Finset.card_image_le.trans (by simp)
  have hcard : ((wordsOfLength (j + 1)).card : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    exact_mod_cast hcard_nat
  have hP_jet : ‖ageJet ℓ (j + 1) P s z‖ ≤ (2 : ℝ) ^ (j + 1) * B_word := by
    change ‖iteratedFDeriv ℝ (j + 1) P_ℓ z‖ ≤ _
    calc ‖iteratedFDeriv ℝ (j + 1) P_ℓ z‖
        ≤ ∑ w ∈ wordsOfLength (j + 1), |B0151.derivWord w P_ℓ z| := hjet_word
      _ ≤ ∑ _w ∈ wordsOfLength (j + 1), B_word := Finset.sum_le_sum fun w hw => hword_bd w hw
      _ = ((wordsOfLength (j + 1)).card : ℝ) * B_word := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ (j + 1) * B_word := mul_le_mul_of_nonneg_right hcard hBword_nn
  have hgrad_le := norm_ageJet_gradS_le hsm_P ℓ j hs z
  have hc2_le : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc.le hcX 2
  have h1_le_X2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ h1X
  have hfactor : 1 + (2 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta ≤
      (1 + (2 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2 := by
    have h1 : (2 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta =
        (2 / (2 * Real.pi ^ 2)) * S_zeta * c ^ 2 := by ring
    rw [h1]
    have h2 : (2 / (2 * Real.pi ^ 2)) * S_zeta * c ^ 2 ≤
        (2 / (2 * Real.pi ^ 2)) * S_zeta * X ^ 2 :=
      mul_le_mul_of_nonneg_left hc2_le (by positivity)
    nlinarith
  calc ‖ageJet ℓ j (fun r w => Train.gradS (P r) w) s z‖
      ≤ 2 * ‖ageJet ℓ (j + 1) P s z‖ := hgrad_le
    _ ≤ 2 * ((2 : ℝ) ^ (j + 1) * B_word) := mul_le_mul_of_nonneg_left hP_jet zero_le_two
    _ = 2 * (2 : ℝ) ^ (j + 1) * M_R *
          (1 + (2 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta) := by
        dsimp [B_word]; ring
    _ ≤ 2 * (2 : ℝ) ^ (2 * (j + 1)) * M_R *
          (1 + (2 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta) := by
        have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (2 * (j + 1)) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hnn : 0 ≤ M_R * (1 + (2 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta) := by positivity
        nlinarith
    _ ≤ 2 * (2 : ℝ) ^ (2 * (j + 1)) * M_R *
          ((1 + (2 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = polyP C_sup (N_R + 2) ν c * Real.exp (CS_R / ν - b_R * c ^ 2) := by
        dsimp [M_R, C_sup, X]
        unfold polyP
        rw [pow_add]
        ring

private theorem sqrt_c_polyP_exp_le {C_wt C_sup CS_R b_R ν c : ℝ} {N_wt N_sup : ℕ}
    (hCwt : 0 < C_wt) (hCsup : 0 < C_sup) (hCS : 0 ≤ CS_R) (hb : 0 < b_R)
    (hν : 0 < ν) (hc : 0 < c) :
    let C_out : ℝ := C_sup + (C_wt + C_sup + 1) * (Real.pi + 1)
    let N_out : ℕ := max N_wt N_sup + 1
    let E_out : ℝ := Real.exp (CS_R / ν - (b_R / 2) * c ^ 2)
    Real.sqrt (c * ((polyP C_wt N_wt ν c *
      (polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2))) * Real.pi)) ≤
      polyP C_out N_out ν c * E_out ∧
    polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2) ≤
      polyP C_out N_out ν c * E_out := by
  intro C_out N_out E_out
  set X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ X := by dsimp [X]; linarith
  have hcX : c ≤ X := by dsimp [X]; linarith
  have hE_sq : Real.exp (CS_R / ν - b_R * c ^ 2) ≤ E_out ^ 2 := by
    dsimp [E_out]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hdiv_nn : 0 ≤ CS_R / ν := div_nonneg hCS hν.le
    linarith
  have hE_le : Real.exp (CS_R / ν - b_R * c ^ 2) ≤ E_out := by
    dsimp [E_out]
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg c, hb.le]
  set N_m : ℕ := max N_wt N_sup
  have hA_le : polyP C_wt N_wt ν c ≤ C_wt * X ^ N_m := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (le_max_left _ _)) hCwt.le
  have hB_le : polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2) ≤
      C_sup * X ^ N_m * E_out ^ 2 := by
    unfold polyP
    have hP : C_sup * X ^ N_sup ≤ C_sup * X ^ N_m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (le_max_right _ _)) hCsup.le
    exact mul_le_mul hP hE_sq (Real.exp_nonneg _) (by positivity)
  have hc_le : c ≤ X ^ 2 := by nlinarith
  have hpi_le : Real.pi ≤ (Real.pi + 1) ^ 2 := by nlinarith [Real.pi_pos]
  have hprod_C : C_wt * C_sup ≤ (C_wt + C_sup + 1) ^ 2 := by nlinarith [hCwt.le, hCsup.le]
  have hsq : c * ((polyP C_wt N_wt ν c *
      (polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2))) * Real.pi) ≤
      ((C_wt + C_sup + 1) * (Real.pi + 1) * X ^ N_out * E_out) ^ 2 := by
    have hA_nn : 0 ≤ polyP C_wt N_wt ν c := by
      unfold polyP; positivity
    have hB_nn : 0 ≤ polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2) := by
      unfold polyP; positivity
    calc c * ((polyP C_wt N_wt ν c *
            (polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2))) * Real.pi)
        ≤ X ^ 2 * (((C_wt * X ^ N_m) * (C_sup * X ^ N_m * E_out ^ 2)) *
            (Real.pi + 1) ^ 2) := by
          apply mul_le_mul hc_le _ (by positivity) (by positivity)
          apply mul_le_mul _ hpi_le Real.pi_pos.le (by positivity)
          exact mul_le_mul hA_le hB_le hB_nn (by positivity)
      _ = (C_wt * C_sup) * (Real.pi + 1) ^ 2 * (X ^ (N_m + 1)) ^ 2 * E_out ^ 2 := by
          rw [pow_add, pow_one]
          ring
      _ ≤ (C_wt + C_sup + 1) ^ 2 * (Real.pi + 1) ^ 2 * (X ^ N_out) ^ 2 * E_out ^ 2 := by
          have hC2 : C_wt * C_sup * (Real.pi + 1) ^ 2 ≤
              (C_wt + C_sup + 1) ^ 2 * (Real.pi + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hprod_C (by positivity)
          have hX_eq : X ^ (N_m + 1) = X ^ N_out := rfl
          rw [hX_eq]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC2 (by positivity)) (by positivity)
      _ = ((C_wt + C_sup + 1) * (Real.pi + 1) * X ^ N_out * E_out) ^ 2 := by ring
  have h1 : Real.sqrt (c * ((polyP C_wt N_wt ν c *
      (polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2))) * Real.pi)) ≤
      (C_wt + C_sup + 1) * (Real.pi + 1) * X ^ N_out * E_out :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩
  refine ⟨h1.trans ?_, ?_⟩
  · dsimp [C_out]
    unfold polyP
    have hC_le : (C_wt + C_sup + 1) * (Real.pi + 1) ≤
        C_sup + (C_wt + C_sup + 1) * (Real.pi + 1) := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC_le (by positivity)) (Real.exp_nonneg _)
  · dsimp [C_out, N_out]
    unfold polyP
    have hC_add_nn : 0 ≤ (C_wt + C_sup + 1) * (Real.pi + 1) := by positivity
    have hC_le : C_sup ≤ C_sup + (C_wt + C_sup + 1) * (Real.pi + 1) := by linarith
    have hN_le : N_sup ≤ max N_wt N_sup + 1 := (le_max_right _ _).trans (Nat.le_succ _)
    have hP_le : C_sup * X ^ N_sup ≤
        (C_sup + (C_wt + C_sup + 1) * (Real.pi + 1)) * X ^ (max N_wt N_sup + 1) :=
      mul_le_mul hC_le (pow_le_pow_right₀ h1X hN_le) (by positivity) (by positivity)
    exact mul_le_mul hP_le hE_le (Real.exp_nonneg _) (by positivity)

end PartI_T25_PressStep

/-! ### 6. Main theorem: `trainFixedBandPressStep_proof : TrainFixedBandPressStep` -/

/-- **Proof of `TrainFixedBandPressStep` (`PartI:T25/1/3`)**. -/
theorem trainFixedBandPressStep_of_tails (hTails : TrainStreamVelocityPressureTails) : TrainFixedBandPressStep := by
  intro ℓ hIH ρ hρ Sg hSg j
  obtain ⟨C_a0, N_a0, CS_a0, b_a0, ν_a0, hCa0, hba0, hνa0, hAdv0⟩ :=
    trainFixedBandAdvDiffStep_proof ℓ hIH ρ hρ Sg hSg j
  obtain ⟨C_a2, N_a2, CS_a2, b_a2, ν_a2, hCa2, hba2, hνa2, hAdv2⟩ :=
    trainFixedBandAdvDiffStep_proof ℓ hIH ρ hρ Sg hSg (j + 2)
  obtain ⟨C_q0, N_q0, CS_q0, b_q0, ν_q0, hCq0, hbq0, hνq0, hQc0⟩ :=
    trainFixedBandQcDivAgeJet_proof.2 ρ hρ Sg hSg ℓ j
  obtain ⟨C_q2, N_q2, CS_q2, b_q2, ν_q2, hCq2, hbq2, hνq2, hQc2⟩ :=
    trainFixedBandQcDivAgeJet_proof.2 ρ hρ Sg hSg ℓ (j + 2)
  obtain ⟨C_p0, N_p0, ν_p0, hCp0, hνp0, hTp0⟩ :=
    hTails.2.2 ρ hρ 0 ℓ (j + 2)
  obtain ⟨C_p4, N_p4, ν_p4, hCp4, hνp4, hTp4⟩ :=
    hTails.2.2 ρ hρ 4 ℓ (j + 1)
  obtain ⟨K_pc0, hKpc0, hpc0⟩ := PcTwoMulMAux.pcJointJetSg Sg hSg 0 (ℓ + (j + 2))
  obtain ⟨K_pc2, hKpc2, hpc2⟩ := PcTwoMulMAux.pcJointJetSg Sg hSg 2 (ℓ + (j + 1))
  obtain ⟨ν_per, hνper, hνper1, hper⟩ :=
    trainPeriodAsymptotics_proof ρ hρ (1 + Sg) (by positivity)
  let C_R : ℝ := max (C_a0 + C_q0) (C_a2 + C_q2)
  let N_R : ℕ := max (max N_a0 N_q0) (max N_a2 N_q2)
  let CS_R : ℝ := max (max (max CS_a0 CS_q0) (max CS_a2 CS_q2)) 0
  let b_R : ℝ := min (min b_a0 b_q0) (min b_a2 b_q2)
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let C_sup : ℝ := 2 * (2 : ℝ) ^ (2 * (j + 1)) * C_R * (1 + (2 / (2 * Real.pi ^ 2)) * S_zeta)
  let N_sup : ℕ := N_R + 2
  let C_wt : ℝ := 2 * (C_p4 * (1 + Sg) ^ N_p4) + 2 * (K_pc2 + 1)
  let N_wt : ℕ := 2 * N_p4
  let C_out : ℝ := C_sup + (C_wt + C_sup + 1) * (Real.pi + 1)
  let N_out : ℕ := max N_wt N_sup + 1
  let CS_out : ℝ := CS_R
  let b_out : ℝ := b_R / 2
  let ν_out : ℝ :=
    min (min (min ν_a0 ν_a2) (min ν_q0 ν_q2)) (min (min ν_p0 ν_p4) ν_per)
  have hCR_pos : 0 < C_R := lt_max_of_lt_left (add_pos hCa0 hCq0)
  have hCsup_pos : 0 < C_sup := by dsimp [C_sup]; positivity
  have hCwt_pos : 0 < C_wt := by dsimp [C_wt]; positivity
  have hCout_pos : 0 < C_out := by dsimp [C_out]; positivity
  have hbR_pos : 0 < b_R := lt_min (lt_min hba0 hbq0) (lt_min hba2 hbq2)
  have hbout_pos : 0 < b_out := half_pos hbR_pos
  have hνout_pos : 0 < ν_out :=
    lt_min (lt_min (lt_min hνa0 hνa2) (lt_min hνq0 hνq2)) (lt_min (lt_min hνp0 hνp4) hνper)
  refine ⟨C_out, N_out, CS_out, b_out, ν_out, hCout_pos, hbout_pos, hνout_pos, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν_left := hν_le.trans (min_le_left _ _)
  have hν_right := hν_le.trans (min_le_right _ _)
  have hν_a0 : ν ≤ ν_a0 := hν_left.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_a2 : ν ≤ ν_a2 := hν_left.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_q0 : ν ≤ ν_q0 := hν_left.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_q2 : ν ≤ ν_q2 := hν_left.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν_p0 : ν ≤ ν_p0 := hν_right.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_p4 : ν ≤ ν_p4 := hν_right.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_per : ν ≤ ν_per := hν_right.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hν_per.trans hνper1
  obtain ⟨hc1, hνc2⟩ := hper ν hν hν_per
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := zero_lt_one.trans_le hc1
  have hSg_c2 : 1 + Sg ≤ c ^ 2 := by
    calc 1 + Sg ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  let X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ X := by dsimp [X]; linarith
  let P : ℝ → Plane → ℝ := fun r w => tr.p r w - pc ν c r w
  let dp : ℝ → Plane → Vec := fun r z => Train.gradS (P r) z
  let F_adv : ℝ → Plane → Vec := fun r w => Train.advection (tr.v r) w - Train.advection (Vc ν c r) w
  let F_qc : ℝ → Plane → Vec := fun r w => Train.matDiv (Train.Qc ν c r) w
  let F_rhs : ℝ → Plane → Vec := fun r w => F_adv r w + F_qc r w
  have hsm_p : SmS (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_pc : SmS (fun x : ℝ × Plane => pc ν c x.1 x.2) := PartI_T25_3.smS_pc hν hc_pos
  have hsm_P : SmS (fun x : ℝ × Plane => P x.1 x.2) := hsm_p.sub hsm_pc
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc_pos
  have hsm_adv : Sm (fun x : ℝ × Plane => F_adv x.1 x.2) :=
    (PartI_T25_1.sm_advection hsm_v).sub (PartI_T25_1.sm_advection hsm_Vc)
  have hsm_qc : Sm (fun x : ℝ × Plane => F_qc x.1 x.2) :=
    trainFixedBandQcDivAgeJet_proof.1 ν c hν hc_pos
  -- Pointwise bounds on `F_rhs` at spatial orders `j` and `j + 2`
  let M_R : ℝ := polyP C_R N_R ν c * Real.exp (CS_R / ν - b_R * c ^ 2)
  have hR_j : ∀ y : Plane, ‖ageJet ℓ j F_rhs s y‖ ≤ M_R := by
    intro y
    have hadd := PartI_T20.ageJet_add F_adv F_qc hsm_adv hsm_qc hs ℓ j y
    have ha := PartI_T25_PressStep.norm_le_of_wSupNorm_zero_le
      (by unfold polyP; positivity) ((hAdv0 ν hν hν_a0 tr htr s hs hs_le).2) y
    have hq := PartI_T25_PressStep.norm_le_of_wSupNorm_zero_le
      (by unfold polyP; positivity) ((hQc0 ν hν hν_q0 s hs hs_le).2) y
    have ha' := ha.trans (PartI_T25_3.polyP_exp_mono
      (C' := C_a0) (N' := N_R) (CS' := CS_R) (bS' := b_R)
      le_rfl hCa0.le ((le_max_left N_a0 N_q0).trans (le_max_left _ _))
      (((le_max_left CS_a0 CS_q0).trans (le_max_left _ _)).trans (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_left b_a0 b_q0)) hν hc_pos.le)
    have hq' := hq.trans (PartI_T25_3.polyP_exp_mono
      (C' := C_q0) (N' := N_R) (CS' := CS_R) (bS' := b_R)
      le_rfl hCq0.le ((le_max_right N_a0 N_q0).trans (le_max_left _ _))
      (((le_max_right CS_a0 CS_q0).trans (le_max_left _ _)).trans (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_right b_a0 b_q0)) hν hc_pos.le)
    have hsum : (polyP C_a0 N_R ν c + polyP C_q0 N_R ν c) * Real.exp (CS_R / ν - b_R * c ^ 2) ≤
        M_R := by
      dsimp [M_R]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      unfold polyP
      have hC_le : C_a0 + C_q0 ≤ C_R := le_max_left _ _
      calc C_a0 * X ^ N_R + C_q0 * X ^ N_R
          = (C_a0 + C_q0) * X ^ N_R := by ring
        _ ≤ C_R * X ^ N_R := mul_le_mul_of_nonneg_right hC_le (by positivity)
    change ‖ageJet ℓ j (fun r w => F_adv r w + F_qc r w) s y‖ ≤ M_R
    rw [hadd]
    have htri := norm_add_le (ageJet ℓ j F_adv s y) (ageJet ℓ j F_qc s y)
    linarith
  have hR_j2 : ∀ y : Plane, ‖ageJet ℓ (j + 2) F_rhs s y‖ ≤ M_R := by
    intro y
    have hadd := PartI_T20.ageJet_add F_adv F_qc hsm_adv hsm_qc hs ℓ (j + 2) y
    have ha := PartI_T25_PressStep.norm_le_of_wSupNorm_zero_le
      (by unfold polyP; positivity) ((hAdv2 ν hν hν_a2 tr htr s hs hs_le).2) y
    have hq := PartI_T25_PressStep.norm_le_of_wSupNorm_zero_le
      (by unfold polyP; positivity) ((hQc2 ν hν hν_q2 s hs hs_le).2) y
    have ha' := ha.trans (PartI_T25_3.polyP_exp_mono
      (C' := C_a2) (N' := N_R) (CS' := CS_R) (bS' := b_R)
      le_rfl hCa2.le ((le_max_left N_a2 N_q2).trans (le_max_right _ _))
      (((le_max_left CS_a2 CS_q2).trans (le_max_right _ _)).trans (le_max_left _ _))
      ((min_le_right _ _).trans (min_le_left b_a2 b_q2)) hν hc_pos.le)
    have hq' := hq.trans (PartI_T25_3.polyP_exp_mono
      (C' := C_q2) (N' := N_R) (CS' := CS_R) (bS' := b_R)
      le_rfl hCq2.le ((le_max_right N_a2 N_q2).trans (le_max_right _ _))
      (((le_max_right CS_a2 CS_q2).trans (le_max_right _ _)).trans (le_max_left _ _))
      ((min_le_right _ _).trans (min_le_right b_a2 b_q2)) hν hc_pos.le)
    have hsum : (polyP C_a2 N_R ν c + polyP C_q2 N_R ν c) * Real.exp (CS_R / ν - b_R * c ^ 2) ≤
        M_R := by
      dsimp [M_R]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      unfold polyP
      have hC_le : C_a2 + C_q2 ≤ C_R := le_max_right _ _
      calc C_a2 * X ^ N_R + C_q2 * X ^ N_R
          = (C_a2 + C_q2) * X ^ N_R := by ring
        _ ≤ C_R * X ^ N_R := mul_le_mul_of_nonneg_right hC_le (by positivity)
    change ‖ageJet ℓ (j + 2) (fun r w => F_adv r w + F_qc r w) s y‖ ≤ M_R
    rw [hadd]
    have htri := norm_add_le (ageJet ℓ (j + 2) F_adv s y) (ageJet ℓ (j + 2) F_qc s y)
    linarith
  -- Qualitative gradient bound `L_P` on `ageJet ℓ (j + 2) P s`
  let L_P : ℝ := polyPS C_p0 N_p0 ν c s + K_pc0
  have hP_grad : ∀ y : Plane, ‖ageJet ℓ (j + 2) P s y‖ ≤ L_P := by
    intro y
    have hsub := PartI_T22.ageJet_sub tr.p (pc ν c) hsm_p hsm_pc hs ℓ (j + 2) y
    have hp_y : ‖ageJet ℓ (j + 2) tr.p s y‖ ≤ polyPS C_p0 N_p0 ν c s :=
      PartI_T25_PressStep.norm_le_of_wSupNorm_zero_le (by unfold polyPS; positivity)
        ((hTp0 ν hν hν_p0 tr htr s hs).2.2.2.2.2) y
    have hpc_y : ‖ageJet ℓ (j + 2) (pc ν c) s y‖ ≤ K_pc0 := by
      have hA := PcTwoMulMAux.alj_main ℓ (pc ν c) hsm_pc (j + 2) hs y
      have hJ := hpc0 ν c hν hν1 hc_pos hSg_c2 (s, y) hs hs_le
      rw [pow_zero, one_mul] at hJ
      exact hA.trans hJ
    change ‖ageJet ℓ (j + 2) (fun r w => tr.p r w - pc ν c r w) s y‖ ≤ L_P
    rw [hsub]
    exact (norm_sub_le _ _).trans (add_le_add hp_y hpc_y)
  -- Unweighted pointwise bound on `ageJet ℓ j dp s`
  let B_sup : ℝ := polyP C_sup N_sup ν c * Real.exp (CS_R / ν - b_R * c ^ 2)
  have hBsup_nn : 0 ≤ B_sup := by dsimp [B_sup]; unfold polyP; positivity
  have hdp_sup_pt : ∀ z : Plane, ‖ageJet ℓ j dp s z‖ ≤ B_sup := fun z =>
    PartI_T25_PressStep.norm_ageJet_dp_le_of_rhs hν hc1 hCR_pos tr htr ℓ j hs hP_grad hR_j hR_j2 z
  -- Weight-4 polynomial bound on `ageJet ℓ j dp s`
  let A_wt : ℝ := polyP C_wt N_wt ν c
  have hAwt_nn : 0 ≤ A_wt := by dsimp [A_wt]; unfold polyP; positivity
  have hdp_wt4_pt : ∀ z : Plane, (1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ j dp s z‖ ≤ A_wt := by
    intro z
    have hsub := PartI_T22.ageJet_sub tr.p (pc ν c) hsm_p hsm_pc hs ℓ (j + 1) z
    have hgrad_le := norm_ageJet_gradS_le hsm_P ℓ j hs z
    have hdp_le : ‖ageJet ℓ j dp s z‖ ≤
        2 * ‖ageJet ℓ (j + 1) tr.p s z‖ + 2 * ‖ageJet ℓ (j + 1) (pc ν c) s z‖ := by
      have hP_le : ‖ageJet ℓ (j + 1) P s z‖ ≤
          ‖ageJet ℓ (j + 1) tr.p s z‖ + ‖ageJet ℓ (j + 1) (pc ν c) s z‖ := by
        change ‖ageJet ℓ (j + 1) (fun r w => tr.p r w - pc ν c r w) s z‖ ≤ _
        rw [hsub]
        exact norm_sub_le _ _
      linarith
    have hjap4 : Real.sqrt (jap 4 z) = (1 + z.2 ^ 2) ^ 2 := by
      have hsq : jap 4 z = ((1 + z.2 ^ 2) ^ 2) ^ 2 := by
        unfold jap; ring
      rw [hsq, Real.sqrt_sq (by positivity)]
    have hp4 : (1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ (j + 1) tr.p s z‖ ≤
        polyP (C_p4 * (1 + Sg) ^ N_p4) (2 * N_p4) ν c := by
      have h1 := PartI_T25_PressStep.sqrt_jap_mul_norm_le_of_wSupNorm_le 4
        (by unfold polyPS; positivity) ((hTp4 ν hν hν_p4 tr htr s hs).2.2.2.2.2) z
      rw [hjap4] at h1
      exact h1.trans (PartI_T25.polyPS_le_polyP_of_le_div_nu N_p4 hCp4.le hSg.le hν hc_pos.le
        hs.le hs_le)
    have hpc4 : (1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ (j + 1) (pc ν c) s z‖ ≤
        polyP (K_pc2 + 1) (2 * N_p4) ν c := by
      have hA := PcTwoMulMAux.alj_main ℓ (pc ν c) hsm_pc (j + 1) hs z
      have hJ := hpc2 ν c hν hν1 hc_pos hSg_c2 (s, z) hs hs_le
      have hle : (1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ (j + 1) (pc ν c) s z‖ ≤ K_pc2 + 1 := by
        calc (1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ (j + 1) (pc ν c) s z‖
            ≤ (1 + z.2 ^ 2) ^ 2 *
                ‖iteratedFDeriv ℝ (ℓ + (j + 1)) (fun x : ℝ × Plane => pc ν c x.1 x.2) (s, z)‖ :=
              mul_le_mul_of_nonneg_left hA (by positivity)
          _ ≤ K_pc2 := hJ
          _ ≤ K_pc2 + 1 := by linarith
      refine hle.trans ?_
      unfold polyP
      have hpow1 : (1 : ℝ) ≤ X ^ (2 * N_p4) := one_le_pow₀ h1X
      calc K_pc2 + 1
          = (K_pc2 + 1) * 1 := (mul_one _).symm
        _ ≤ (K_pc2 + 1) * X ^ (2 * N_p4) := mul_le_mul_of_nonneg_left hpow1 (by positivity)
    calc (1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ j dp s z‖
        ≤ (1 + z.2 ^ 2) ^ 2 *
            (2 * ‖ageJet ℓ (j + 1) tr.p s z‖ + 2 * ‖ageJet ℓ (j + 1) (pc ν c) s z‖) :=
          mul_le_mul_of_nonneg_left hdp_le (by positivity)
      _ = 2 * ((1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ (j + 1) tr.p s z‖) +
            2 * ((1 + z.2 ^ 2) ^ 2 * ‖ageJet ℓ (j + 1) (pc ν c) s z‖) := by ring
      _ ≤ 2 * polyP (C_p4 * (1 + Sg) ^ N_p4) (2 * N_p4) ν c +
            2 * polyP (K_pc2 + 1) (2 * N_p4) ν c :=
          add_le_add (mul_le_mul_of_nonneg_left hp4 zero_le_two)
            (mul_le_mul_of_nonneg_left hpc4 zero_le_two)
      _ = A_wt := by
          dsimp [A_wt, C_wt, N_wt]
          unfold polyP
          ring
  -- Final assembly of `wCellL2 c 0` and `wSupNorm 0`
  have hL2_raw := PartI_T25_PressStep.wCellL2_zero_le_of_weight4_and_sup
    hc_pos.le hAwt_nn hBsup_nn (ageJet ℓ j dp s) hdp_wt4_pt hdp_sup_pt
  have hSup_raw := PartI_T25_PressStep.wSupNorm_zero_le_of_norm_le hdp_sup_pt
  obtain ⟨hsqrt_le, hSup_le⟩ := PartI_T25_PressStep.sqrt_c_polyP_exp_le
    (N_wt := N_wt) (N_sup := N_sup) hCwt_pos hCsup_pos (le_max_right _ _) hbR_pos hν hc_pos
  dsimp only
  exact ⟨hL2_raw.trans (ENNReal.ofReal_le_ofReal hsqrt_le),
    hSup_raw.trans (ENNReal.ofReal_le_ofReal hSup_le)⟩

namespace VelAgeJet

/-- Proof of `TrainFixedBandPressStep` (`PartI:T25/1/3`). -/
theorem trainFixedBandPressStep_of_tails (hTails : TrainStreamVelocityPressureTails) : TrainFixedBandPressStep :=
  UnforcedLeray.Short.PartI.VelAgeJetAux.trainFixedBandPressStep_of_tails hTails

end VelAgeJet

end UnforcedLeray.Short.PartI.VelAgeJetAux

end
