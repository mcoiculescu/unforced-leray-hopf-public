import UnforcedLeray.Short.PartI.Sub.PartI_T22_1
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.PressureStep

/-!
# `PartI:T22/1`: Post-overlap (`ℓ = 0`) stream fluctuation and pressure decay

Source of record: `the November 2 reference manuscript`, lines 439-446, 499-503,
515-522.

This module completes the unconditional proof of
`trainPostOverlapStreamPressureZero_proof : TrainStreamVelocityPressureTails → OverlapFluctuationDecay → TrainOverlap → TrainPostOverlapStreamPressureZero`
by proving the unweighted post-overlap pressure jet bound `trainPostOverlapPressureSupZero_proof : TrainPostOverlapPressureSupZero`
and combining it with `trainPostOverlapStreamPressureZero_of_sup` from
`UnforcedLeray.Short.PartI.Sub.PartI_T22_1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet cellL2 wCellL2 jap)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm)

namespace PartI_T22_1_Proof

/-- Pointwise extraction of `‖f z‖ ≤ B` from `wSupNorm 0 f ≤ ENNReal.ofReal B` (`0 ≤ B`). -/
private theorem norm_le_of_wSupNorm_zero_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (h : wSupNorm 0 f ≤ ENNReal.ofReal B) (z : Plane) :
    ‖f z‖ ≤ B := by
  have hz : ENNReal.ofReal (Real.sqrt (jap 0 z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap 0 w)) * ‖f w‖ₑ) z).trans h
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hz

/-- Pointwise bound `∀ z, ‖f z‖ ≤ B` implies `wSupNorm 0 f ≤ ENNReal.ofReal B`. -/
private theorem wSupNorm_zero_le_of_norm_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (h : ∀ z : Plane, ‖f z‖ ≤ B) :
    wSupNorm 0 f ≤ ENNReal.ofReal B := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  have hj0 : Real.sqrt (jap 0 z) = 1 := by simp [jap]
  rw [hj0, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h z)

/-- Since the vertical mean velocity vanishes (`trainMeanV2`), the vertical component of `tr.v r`
coincides with the vertical component of the fluctuation `hfluct c (tr.v r)` for all `r > 0`. -/
private theorem hfluct_v_one_eq {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r) (z : Plane) :
    hfluct c (tr.v r) z 1 = tr.v r z 1 := by
  have hvc : Continuous (tr.v r) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun w => ⟨hr.le, mem_univ w⟩)
  have hm1 := PartI_T22.hmean_apply_vec' c hvc z.2 1
  have hv2_0 : hmean c (fun w => tr.v r w 1) z.2 = 0 := trainMeanV2 ν c hν hc tr r hr z.2
  show (tr.v r z - hmean c (tr.v r) z.2) 1 = tr.v r z 1
  rw [PiLp.sub_apply, hm1, hv2_0, sub_zero]

/-- Equality of `ageJet r k` on the vertical velocity component and its horizontal fluctuation. -/
private theorem ageJet_v_one_eq_hfluct {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (r k : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet r k (fun t w => tr.v t w 1) s z =
      ageJet r k (fun t w => hfluct c (tr.v t) w 1) s z := by
  have hslice : (fun w : Plane => iteratedDeriv r (fun t => tr.v t w 1) s) =
      fun w : Plane => iteratedDeriv r (fun t => hfluct c (tr.v t) w 1) s := by
    funext w
    have hev : (fun t => tr.v t w 1) =ᶠ[𝓝 s] (fun t => hfluct c (tr.v t) w 1) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using (hfluct_v_one_eq hν hc tr ht w).symm
    exact hev.iteratedDeriv_eq r
  unfold ageJet
  rw [hslice]

/-- Since `hmean c (tr.v r) z.2` depends only on `z.2`, its `q`-partial vanishes, so
`Cyl.partialQ` of component `m` of `tr.v r` coincides with `Cyl.partialQ` of `hfluct c (tr.v r)`. -/
private theorem partialQ_v_eq_hfluct {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (m : Fin 2) (r : ℝ) (z : Plane) :
    Cyl.partialQ (fun y => tr.v r y m) z =
      Cyl.partialQ (fun y => hfluct c (tr.v r) y m) z := by
  obtain ⟨x, y⟩ := z
  show deriv (fun q => tr.v r (q, y) m) x =
    deriv (fun q => (tr.v r (q, y) - hmean c (tr.v r) y) m) x
  have hfun : (fun q => (tr.v r (q, y) - hmean c (tr.v r) y) m) =
      fun q => tr.v r (q, y) m - (hmean c (tr.v r) y) m :=
    funext fun q => by simp [PiLp.sub_apply]
  rw [hfun, deriv_sub_const]

/-- Bilinear spacetime Leibniz bound for `poissonSource (tr.v r)` retaining a fluctuation factor
`M_F` on every term. -/
private theorem norm_ageJet_poissonSource_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_F)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s z‖ ≤ M_V) :
    ‖ageJet ℓ j (fun r w => poissonSource (tr.v r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M_F * M_V := by
  let V : ℝ → Plane → Vec := tr.v
  let VF : ℝ → Plane → Vec := fun t => hfluct c (tr.v t)
  have hV : Sm (fun x : ℝ × Plane => V x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hVF : Sm (fun x : ℝ × Plane => VF x.1 x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_vf0 : PartI_T20.SmR (fun x : ℝ × Plane => VF x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hVF
  have hsm_vf1 : PartI_T20.SmR (fun x : ℝ × Plane => VF x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hVF
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 1) hsm_v1
  let P₁ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 0) w * Cyl.partialQ (fun y => V r y 0) w
  let P₂ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 0) w
  let P₃ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialEta (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 1) w
  have hsm₁ : PartI_T20.SmR (fun x : ℝ × Plane => P₁ x.1 x.2) := hQ0.mul hQ0
  have hsm₂ : PartI_T20.SmR (fun x : ℝ × Plane => P₂ x.1 x.2) := hQ1.mul hE0
  have hsm₃ : PartI_T20.SmR (fun x : ℝ × Plane => P₃ x.1 x.2) := hE1.mul hE1
  have hfun : (fun r w => poissonSource (V r) w) =
      fun r w => (P₁ r w + (P₂ r w + P₂ r w)) + P₃ r w := by
    funext r w
    unfold poissonSource
    dsimp [P₁, P₂, P₃]
    ring
  have hadd1 := PartI_T20.ageJet_add (fun r w => P₁ r w + (P₂ r w + P₂ r w)) P₃
    (hsm₁.add (hsm₂.add hsm₂)) hsm₃ hs ℓ j z
  have hadd2 := PartI_T20.ageJet_add P₁ (fun r w => P₂ r w + P₂ r w)
    hsm₁ (hsm₂.add hsm₂) hs ℓ j z
  have hadd3 := PartI_T20.ageJet_add P₂ P₂ hsm₂ hsm₂ hs ℓ j z
  have hQ0_eq : (fun t w => Cyl.partialQ (fun y => V t y 0) w) =
      fun t w => Cyl.partialQ (fun y => VF t y 0) w :=
    funext fun t => funext fun w => partialQ_v_eq_hfluct tr 0 t w
  have hQ1_eq : (fun t w => Cyl.partialQ (fun y => V t y 1) w) =
      fun t w => Cyl.partialQ (fun y => VF t y 1) w :=
    funext fun t => funext fun w => partialQ_v_eq_hfluct tr 1 t w
  have hQ0_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M_F := by
    intro r hr i hi
    rw [hQ0_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => VF t w 0) hsm_vf0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hVF 0 r (i + 1) hs z)).trans (hF_bd r hr (i + 1) (by omega))
  have hQ1_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 1) w) s z‖ ≤ M_F := by
    intro r hr i hi
    rw [hQ1_eq]
    exact ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => VF t w 1) hsm_vf1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hVF 1 r (i + 1) hs z)).trans (hF_bd r hr (i + 1) (by omega))
  have hE1_F_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M_F := by
    intro r hr i hi
    calc ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖
        ≤ ‖ageJet r (i + 1) (fun t w => V t w 1) s z‖ :=
          PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z
      _ = ‖ageJet r (i + 1) (fun t w => VF t w 1) s z‖ := by
          rw [ageJet_v_one_eq_hfluct hν hc tr r (i + 1) hs z]
      _ ≤ ‖ageJet r (i + 1) VF s z‖ :=
          PartI_T20.norm_ageJet_vec_proj_le hVF 1 r (i + 1) hs z
      _ ≤ M_F := hF_bd r hr (i + 1) (by omega)
  have hQ0_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hE0_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 0) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hE1_V_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M_V := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hV_bd r hr (i + 1) (by omega))
  have hb₁ := PartI_T20.norm_ageJet_mul_le hQ0 hQ0 ℓ j hs hMF hMV z hQ0_F_bd hQ0_V_bd
  have hb₂ := PartI_T20.norm_ageJet_mul_le hQ1 hE0 ℓ j hs hMF hMV z hQ1_F_bd hE0_V_bd
  have hb₃ := PartI_T20.norm_ageJet_mul_le hE1 hE1 ℓ j hs hMF hMV z hE1_F_bd hE1_V_bd
  rw [hfun, hadd1, hadd2, hadd3]
  have htri1 := norm_add_le
    (ageJet ℓ j P₁ s z + (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)) (ageJet ℓ j P₃ s z)
  have htri2 := norm_add_le (ageJet ℓ j P₁ s z) (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)
  have htri3 := norm_add_le (ageJet ℓ j P₂ s z) (ageJet ℓ j P₂ s z)
  linarith

/-- Horizontal-mean bound for word derivatives of the age-iterated pressure slice retaining a
fluctuation factor `M_F`. -/
private theorem abs_hmean_derivWord_p_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (ℓ k : ℕ) {w : List Bool} (hw : w.length = k) {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s w'‖ ≤ M_F)
    (hV_bd : ∀ w' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k, ‖ageJet r i tr.v s w'‖ ≤ M_V) :
    |hmean c (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z.2| ≤
      (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hVF : Sm (fun x : ℝ × Plane => hfluct c (tr.v x.1) x.2) :=
    PartI_T22.contDiffOn_hfluct_v hc tr
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hsm_v
  have hsm_sq : PartI_T20.SmR (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) := by
    have : (fun x : ℝ × Plane => tr.v x.1 x.2 1 ^ 2) =
        fun x : ℝ × Plane => tr.v x.1 x.2 1 * tr.v x.1 x.2 1 :=
      funext fun _ => sq _
    rw [this]
    exact hsm_v1.mul hsm_v1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  let G_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.v r z' 1 ^ 2) s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hG_sm : ContDiff ℝ ∞ G_ℓ :=
    PartI_T20_1.contDiff_iteratedDeriv_slice (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs
  have hP_per : Cyl.IsPeriodic c P_ℓ :=
    PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs
  have hG_per : Cyl.IsPeriodic c G_ℓ := by
    refine PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr z' => ?_) ℓ hs
    exact congrArg (fun v : Vec => v 1 ^ 2) (tr.isTrain.periodic_v r hr.le z')
  have hmean_eq : ∀ η : ℝ, hmean c P_ℓ η = -hmean c G_ℓ η := by
    intro η
    rw [← PartI_T20_1.iteratedDeriv_hmean_eq hc hsm_p ℓ hs η,
      ← PartI_T20_1.iteratedDeriv_hmean_eq hc (F := fun r z' => tr.v r z' 1 ^ 2) hsm_sq ℓ hs η,
      ← iteratedDeriv_neg]
    have hev : (fun r => hmean c (tr.p r) η) =ᶠ[𝓝 s]
        fun r => -hmean c (fun z' : Plane => tr.v r z' 1 ^ 2) η := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using
        PartI_T20_1.train_hmean_p_eq_neg_v1_sq hν hc1 tr htr hr η
    exact hev.iteratedDeriv_eq ℓ
  have hword_eq := PartI_T20_1.hmean_derivWord_neg_eq hc hP_sm hG_sm hP_per hG_per hmean_eq w z.2
  rw [hword_eq, abs_neg]
  refine cylpHmeanAbsLe hc (fun w' => ?_) z.2
  have hsq_fn : (fun r (z' : Plane) => tr.v r z' 1 ^ 2) =
      fun r z' => tr.v r z' 1 * tr.v r z' 1 := by
    funext r z'; exact sq _
  calc |B0151.derivWord w G_ℓ w'|
      ≤ ‖ageJet ℓ k (fun r z' => tr.v r z' 1 ^ 2) s w'‖ :=
        PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => tr.v r z' 1 ^ 2)
          hsm_sq ℓ k hw hs w'
    _ = ‖ageJet ℓ k (fun r z' => tr.v r z' 1 * tr.v r z' 1) s w'‖ := by rw [hsq_fn]
    _ ≤ (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
        refine PartI_T20.norm_ageJet_mul_le
          (A := fun r z' => tr.v r z' 1) (B := fun r z' => tr.v r z' 1)
          hsm_v1 hsm_v1 ℓ k hs hMF hMV w' (fun r hr i hi => ?_) (fun r hr i hi => ?_)
        · rw [ageJet_v_one_eq_hfluct hν hc tr r i hs w']
          exact (PartI_T20.norm_ageJet_vec_proj_le hVF 1 r i hs w').trans (hF_bd w' r hr i hi)
        · exact (PartI_T20.norm_ageJet_vec_proj_le hsm_v 1 r i hs w').trans (hV_bd w' r hr i hi)

/-- Laplacian bound for word derivatives of the age-iterated pressure slice retaining a
fluctuation factor `M_F`. -/
private theorem abs_lapS_derivWord_p_fluct_le {ν c M_F M_V : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hF_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i (fun t => hfluct c (tr.v t)) s z‖ ≤ M_F)
    (hV_bd : ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z‖ ≤ M_V) :
    |Train.lapS (B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)) z| ≤
      4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hsm_src : PartI_T20.SmR (fun x : ℝ × Plane => poissonSource (tr.v x.1) x.2) :=
    PartI_T20_1.smR_poissonSource hsm_v
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hlap_P : Train.lapS P_ℓ =
      fun z' => -iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') s := by
    funext z'
    have h1 := PartI_T20.iteratedDeriv_mul_lapS_eq hsm_p 1 ℓ hs z'
    simp only [one_mul] at h1
    rw [← h1, ← iteratedDeriv_neg]
    have hev : (fun r => Train.lapS (tr.p r) z') =ᶠ[𝓝 s]
        fun r => -poissonSource (tr.v r) z' := by
      filter_upwards [Ioi_mem_nhds hs] with r (hr : 0 < r)
      exact slicePoisson ν c (r + 1) tr.v tr.p hν hc1 (by linarith)
        (trainSol_isClassicalOn tr (r + 1)) r ⟨hr.le, by linarith⟩ z'
    exact hev.iteratedDeriv_eq ℓ
  rw [PartI_T20_1.derivWord_lapS_comm hP_sm w z, hlap_P, PartI_T20_1.derivWord_neg _ w z, abs_neg]
  calc |B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => poissonSource (tr.v r) z') s) z|
      ≤ ‖ageJet ℓ k (fun r z' => poissonSource (tr.v r) z') s z‖ :=
        PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet (F := fun r z' => poissonSource (tr.v r) z')
          hsm_src ℓ k hw hs z
    _ ≤ 4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V :=
        norm_ageJet_poissonSource_fluct_le hν hc hMF hMV tr ℓ k hs z hF_bd hV_bd

/-- Oscillating-part bound for `B0151.derivWord w P_ℓ` from a qualitative bound `L_p` on
`ageJet ℓ (k + 1) tr.p s` and the bilinear Laplacian bound `K_src = 4 * 2^(ℓ + k) * M_F * M_V`. -/
private theorem abs_osc_derivWord_p_fluct_le {ν c M_F M_V L_p : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (hMF : 0 ≤ M_F) (hMV : 0 ≤ M_V)
    (tr : B0140.TrainSol ν c) (ℓ k : ℕ) {w : List Bool} (hw : w.length = k)
    {s : ℝ} (hs : 0 < s) (z : Plane)
    (hp_grad : ∀ z' : Plane, ‖ageJet ℓ (k + 1) tr.p s z'‖ ≤ L_p)
    (hF_bd : ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s z'‖ ≤ M_F)
    (hV_bd : ∀ z' : Plane, ∀ r ≤ ℓ, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z'‖ ≤ M_V) :
    let Q_s : Plane → ℝ := B0151.derivWord w (fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s)
    let K_src : ℝ := 4 * (2 : ℝ) ^ (ℓ + k) * M_F * M_V
    |Q_s z - hmean c Q_s z.2| ≤
      (K_src * c ^ 2 / (2 * Real.pi ^ 2)) * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  intro Q_s K_src
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hK_nn : 0 ≤ K_src := by dsimp [K_src]; positivity
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_ℓ : Plane → ℝ := fun z' => iteratedDeriv ℓ (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_ℓ := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p ℓ hs
  have hQ_C2 : ContDiff ℝ 2 Q_s := (B0151.contDiff_derivWord hP_sm w).of_le (by simp)
  have hQ_per : Cyl.IsPeriodic c Q_s :=
    PartI_T20_1.isPeriodic_derivWord
      (PartI_T20_1.isPeriodic_iteratedDeriv (fun r hr => tr.isTrain.periodic_p r hr.le) ℓ hs) w
  have hgrad : ∃ L : ℝ, ∀ y : Plane, |Cyl.partialQ Q_s y| ≤ L ∧ |Cyl.partialEta Q_s y| ≤ L := by
    refine ⟨L_p, fun y => ⟨?_, ?_⟩⟩
    · have hlen_t : (true :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (true :: w) P_ℓ y| ≤ L_p
      exact (PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ (k + 1) hlen_t hs y).trans
        (hp_grad y)
    · have hlen_f : (false :: w).length = k + 1 := by simp [hw]
      change |B0151.derivWord (false :: w) P_ℓ y| ≤ L_p
      exact (PartI_T20_1.abs_derivWord_iteratedDeriv_le_ageJet hsm_p ℓ (k + 1) hlen_f hs y).trans
        (hp_grad y)
  have hlap : ∀ y : Plane, |Train.lapS Q_s y| ≤ K_src := fun y =>
    abs_lapS_derivWord_p_fluct_le hν hc1 hMF hMV tr ℓ k hw hs y (hF_bd y) (hV_bd y)
  exact PartI_T20_1.oscLinear_explicit hc hK_nn hQ_C2 hQ_per hgrad hlap z

/-- Uniform spatial post-overlap velocity fluctuation sup bound across all `i ≤ K` at `ℓ = 0`. -/
private theorem uniform_postOverlap_velFluct_sup (hVel0 : TrainPostOverlapVelZero)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    ∀ K : ℕ, ∃ C_F : ℝ, ∃ N_F : ℕ, ∃ lam_F ν_F : ℝ,
      0 < C_F ∧ 0 < lam_F ∧ 0 < ν_F ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν_F →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → B0146.overlapAge ν (trainPeriod ρ ν) ≤ s →
            ∀ z : Plane, ∀ i ≤ K,
              let c := trainPeriod ρ ν
              ‖ageJet 0 i (fun r => hfluct c (tr.v r)) s z‖ ≤
                polyP C_F N_F ν c * Real.exp (-(lam_F * ν * s / c ^ 2))
  | 0 => by
    obtain ⟨C_F, N_F, lam_F, ν_F, hC_F, hlam_F, hν_F, h0⟩ := hVel0 ρ hρ 0
    refine ⟨C_F, N_F, lam_F, ν_F, hC_F, hlam_F, hν_F, ?_⟩
    intro ν hν hν_le tr htr s hs hsc z i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    let c := trainPeriod ρ ν
    have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
    have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hB_nn : 0 ≤ polyP C_F N_F ν c * Real.exp (-(lam_F * ν * s / c ^ 2)) := by
      unfold polyP; positivity
    exact norm_le_of_wSupNorm_zero_le hB_nn (h0 ν hν hν_le tr htr s hs hsc).2 z
  | K + 1 => by
    obtain ⟨C₁, N₁, lam₁, ν₁, hC₁, hlam₁, hν₁, hIH⟩ :=
      uniform_postOverlap_velFluct_sup hVel0 hρ K
    obtain ⟨C₂, N₂, lam₂, ν₂, hC₂, hlam₂, hν₂, hK1⟩ := hVel0 ρ hρ (K + 1)
    refine ⟨max C₁ C₂, max N₁ N₂, min lam₁ lam₂, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr s hs hsc z i hi
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
    have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have h1X : 1 ≤ 1 + c + ν⁻¹ := by linarith
    rcases Nat.of_le_succ hi with hiK | rfl
    · have h1 := hIH ν hν hν₁_le tr htr s hs hsc z i hiK
      refine h1.trans (mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by unfold polyP; positivity))
      · unfold polyP
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
          (by positivity) (by positivity)
      · apply Real.exp_le_exp.2
        apply neg_le_neg
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (min_le_left _ _) hν.le) hs.le) (sq_nonneg c)
    · have hB₂_nn : 0 ≤ polyP C₂ N₂ ν c * Real.exp (-(lam₂ * ν * s / c ^ 2)) := by
        unfold polyP; positivity
      have h2 := norm_le_of_wSupNorm_zero_le hB₂_nn (hK1 ν hν hν₂_le tr htr s hs hsc).2 z
      refine h2.trans (mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by unfold polyP; positivity))
      · unfold polyP
        exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
          (by positivity) (by positivity)
      · apply Real.exp_le_exp.2
        apply neg_le_neg
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (min_le_right _ _) hν.le) hs.le) (sq_nonneg c)

end PartI_T22_1_Proof

/-- **Unconditional proof of `TrainPostOverlapPressureSupZero`:**
for `s ≥ overlapAge ν c`, bounds `wSupNorm 0 (ageJet 0 k tr.p s)` by
`ENNReal.ofReal (polyP C_p N_p ν c * Real.exp (-(lam_F * ν * s / c ^ 2)))`. -/
theorem trainPostOverlapPressureSupZero_proof : TrainPostOverlapPressureSupZero := by
  intro hTails hFD hOv ρ hρ k
  obtain ⟨C_F, N_F, lam_F, ν_F, hCF, hlamF, hνF, hF_rect⟩ :=
    PartI_T22_1_Proof.uniform_postOverlap_velFluct_sup
      (trainPostOverlapVelZero_of hFD) hρ (k + 1)
  obtain ⟨C_V, N_V, ν_V, hCV, hνV, hV_rect⟩ :=
    PartI_T20.uniform_velocity_sup_spatial hρ (trainVelocityAgeJetSupBoundAt_zero hOv) (k + 1)
  obtain ⟨C_P1, N_P1, ν_P1, hCP1, hνP1, hT_p⟩ := hTails.2.2 ρ hρ 0 0 (k + 1)
  let S_zeta : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hS_nn : 0 ≤ S_zeta := tsum_nonneg fun _ => by positivity
  let C_p : ℝ :=
    (2 : ℝ) ^ (2 * k) * (C_F * C_V) * (1 + (4 / (2 * Real.pi ^ 2)) * S_zeta)
  let N_p : ℕ := N_F + N_V + 2
  let ν₀ : ℝ := min ν_F (min ν_V (min ν_P1 1))
  have hCp : 0 < C_p := by dsimp [C_p]; positivity
  have hν₀ : 0 < ν₀ := lt_min hνF (lt_min hνV (lt_min hνP1 zero_lt_one))
  refine ⟨C_p, N_p, lam_F, ν₀, hCp, hlamF, hν₀, ?_⟩
  intro ν hν hν_le tr htr s hs hsc
  have hν_F : ν ≤ ν_F := hν_le.trans (min_le_left _ _)
  have hν_V : ν ≤ ν_V := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_P1 : ν ≤ ν_P1 :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν1 : ν ≤ 1 :=
    hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let c := trainPeriod ρ ν
  have hc1 : 1 ≤ c := by
    unfold c trainPeriod
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  let X : ℝ := 1 + c + ν⁻¹
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1X : 1 ≤ X := by dsimp [X]; linarith
  have hcX : c ≤ X := by dsimp [X]; linarith
  let E_s : ℝ := Real.exp (-(lam_F * ν * s / c ^ 2))
  let M_F : ℝ := polyP C_F N_F ν c * E_s
  let M_V : ℝ := polyP C_V N_V ν c
  let L_p : ℝ := polyPS C_P1 N_P1 ν c s
  have hMF : 0 ≤ M_F := by dsimp [M_F, E_s, polyP]; positivity
  have hMV : 0 ≤ M_V := by dsimp [M_V, polyP]; positivity
  have hLp_nn : 0 ≤ L_p := by dsimp [L_p, polyPS]; positivity
  have hF_bd : ∀ z' : Plane, ∀ r ≤ 0, ∀ i ≤ k + 1,
      ‖ageJet r i (fun t => hfluct c (tr.v t)) s z'‖ ≤ M_F := by
    intro z' r hr i hi
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact hF_rect ν hν hν_F tr htr s hs hsc z' i hi
  have hV_bd : ∀ z' : Plane, ∀ r ≤ 0, ∀ i ≤ k + 1, ‖ageJet r i tr.v s z'‖ ≤ M_V := by
    intro z' r hr i hi
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact hV_rect ν hν hν_V tr htr s hs z' i hi
  have hp_grad : ∀ z' : Plane, ‖ageJet 0 (k + 1) tr.p s z'‖ ≤ L_p := by
    intro z'
    have hsup := (hT_p ν hν hν_P1 tr htr s hs).2.2.2.2.2
    exact PartI_T22_1_Proof.norm_le_of_wSupNorm_zero_le hLp_nn hsup z'
  refine PartI_T22_1_Proof.wSupNorm_zero_le_of_norm_le fun z => ?_
  have hsm_p : PartI_T20.SmR (fun x : ℝ × Plane => tr.p x.1 x.2) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let P_0 : Plane → ℝ := fun z' => iteratedDeriv 0 (fun r => tr.p r z') s
  have hP_sm : ContDiff ℝ ∞ P_0 := PartI_T20_1.contDiff_iteratedDeriv_slice hsm_p 0 hs
  let B_word : ℝ :=
    (2 : ℝ) ^ k * M_F * M_V * (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta)
  have hword_bd : ∀ w ∈ wordsOfLength k, |B0151.derivWord w P_0 z| ≤ B_word := by
    intro w hw
    have hlen : w.length = k := by
      unfold wordsOfLength at hw
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hw
      simp
    have hmean_bd := PartI_T22_1_Proof.abs_hmean_derivWord_p_fluct_le
      hν hc1 hMF hMV tr htr 0 k hlen hs z
      (fun w' r hr i hi => hF_bd w' r hr i (by omega))
      (fun w' r hr i hi => hV_bd w' r hr i (by omega))
    have hosc_bd := PartI_T22_1_Proof.abs_osc_derivWord_p_fluct_le
      hν hc1 hMF hMV tr 0 k hlen hs z hp_grad hF_bd hV_bd
    have htri : |B0151.derivWord w P_0 z| ≤
        |B0151.derivWord w P_0 z - hmean c (B0151.derivWord w P_0) z.2| +
          |hmean c (B0151.derivWord w P_0) z.2| := by
      have := abs_add_le (B0151.derivWord w P_0 z - hmean c (B0151.derivWord w P_0) z.2)
        (hmean c (B0151.derivWord w P_0) z.2)
      rwa [sub_add_cancel] at this
    calc |B0151.derivWord w P_0 z|
        ≤ (4 * (2 : ℝ) ^ (0 + k) * M_F * M_V * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta +
            (2 : ℝ) ^ (0 + k) * M_F * M_V :=
          htri.trans (add_le_add hosc_bd hmean_bd)
      _ = B_word := by dsimp [B_word]; rw [ zero_add ]; ring
  have hjet_word := (cylJetWord_proof P_0 hP_sm k z).2
  have hcard_nat : (wordsOfLength k).card ≤ 2 ^ k := by
    unfold wordsOfLength
    exact Finset.card_image_le.trans (by simp)
  have hcard : ((wordsOfLength k).card : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hcard_nat
  have hB_nn : 0 ≤ B_word := by dsimp [B_word]; positivity
  have hjet_le : ‖ageJet 0 k tr.p s z‖ ≤ (2 : ℝ) ^ k * B_word := by
    change ‖iteratedFDeriv ℝ k P_0 z‖ ≤ _
    calc ‖iteratedFDeriv ℝ k P_0 z‖
        ≤ ∑ w ∈ wordsOfLength k, |B0151.derivWord w P_0 z| := hjet_word
      _ ≤ ∑ _w ∈ wordsOfLength k, B_word := Finset.sum_le_sum fun w hw => hword_bd w hw
      _ = ((wordsOfLength k).card : ℝ) * B_word := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ k * B_word := mul_le_mul_of_nonneg_right hcard hB_nn
  refine hjet_le.trans ?_
  have hc2_le : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0 hcX 2
  have h1_le_X2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ h1X
  have hfactor : 1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta ≤
      (1 + (4 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2 := by
    have h1 : (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta =
        (4 / (2 * Real.pi ^ 2)) * S_zeta * c ^ 2 := by ring
    rw [h1]
    have h2 : (4 / (2 * Real.pi ^ 2)) * S_zeta * c ^ 2 ≤
        (4 / (2 * Real.pi ^ 2)) * S_zeta * X ^ 2 :=
      mul_le_mul_of_nonneg_left hc2_le (by positivity)
    nlinarith
  calc (2 : ℝ) ^ k * B_word
      = (2 : ℝ) ^ (2 * k) * (M_F * M_V) *
          (1 + (4 * c ^ 2 / (2 * Real.pi ^ 2)) * S_zeta) := by
        dsimp [B_word]
        rw [show 2 * k = k + k by omega, pow_add]
        ring
    _ ≤ (2 : ℝ) ^ (2 * k) * (M_F * M_V) *
          ((1 + (4 / (2 * Real.pi ^ 2)) * S_zeta) * X ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = polyP C_p N_p ν c * E_s := by
        dsimp [M_F, M_V, C_p, N_p, X]
        unfold polyP
        rw [pow_add, pow_add]
        ring

/-- **Post-overlap (`ℓ = 0`) stream fluctuation and pressure decay (`PartI:T22/1`)**:
combines `trainPostOverlapStreamPressureZero_of_sup` and `trainPostOverlapPressureSupZero_proof`. -/
theorem trainPostOverlapStreamPressureZero_proof
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : OverlapFluctuationDecay)
    (hOv : TrainOverlap) :
    TrainPostOverlapStreamPressureZero :=
  trainPostOverlapStreamPressureZero_of_sup trainPostOverlapPressureSupZero_proof hTails hFD hOv

end UnforcedLeray.Short.PartI

end
