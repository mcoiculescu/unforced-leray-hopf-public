import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Sub.PartI_T25_3
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1

/-!
# `TrainFixedBandAdvDiffStep` (`PartI:T25/1/2`, helper for `PartI:T25/3/2`)

Source of record: `the November 2 reference manuscript`, lines 326-336, 468-478,
541-551.

Proves `TrainFixedBandAdvDiffStep`: given `∀ r ≤ ℓ, TrainFixedBandVelOrderUnweighted r`, on
`0 < s ≤ Sg / ν`, `ageJet ℓ j advDiff s` for
`advDiff r z = Train.advection (tr.v r) z - Train.advection (Vc ν c r) z` satisfies the unweighted
(`m = 0`) fixed-band exponential bound in `wCellL2 c 0` and `wSupNorm 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm vcSmooth_proof vcAgeJetLe_proof)

namespace PartI_T25_AdvDiff

/-! ### 1. Pointwise / `wSupNorm 0` and `wCellL2 c 0` subadditivity helpers -/

theorem norm_le_of_wSupNorm_zero_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (hB : 0 ≤ B) (h : wSupNorm 0 f ≤ ENNReal.ofReal B) (z : Plane) :
    ‖f z‖ ≤ B := by
  have hz : ENNReal.ofReal (Real.sqrt (jap 0 z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap 0 w)) * ‖f w‖ₑ) z).trans h
  simp only [jap, pow_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul, ← ofReal_norm] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hz

theorem wSupNorm_zero_le_of_forall_norm_le {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {B : ℝ} (h : ∀ z : Plane, ‖f z‖ ≤ B) :
    wSupNorm 0 f ≤ ENNReal.ofReal B := by
  unfold wSupNorm
  refine iSup_le fun z => ?_
  simp only [jap, pow_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h z)

theorem wCellL2_add_le_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (m : ℕ) {f g : Plane → E} (hf : Continuous f) (hg : Continuous g) :
    wCellL2 c m (fun z => f z + g z) ≤ wCellL2 c m f + wCellL2 c m g := by
  unfold wCellL2
  have hadd : (fun z : Plane => Real.sqrt (jap m z) • (f z + g z)) =
      (fun z : Plane => Real.sqrt (jap m z) • f z) +
        (fun z : Plane => Real.sqrt (jap m z) • g z) := by
    funext z
    simp [smul_add]
  have hjap : Continuous (fun z : Plane => Real.sqrt (jap m z)) := by
    unfold jap
    fun_prop
  rw [hadd]
  exact eLpNorm_add_le (hjap.smul hf).aestronglyMeasurable
    (hjap.smul hg).aestronglyMeasurable (by norm_num)

theorem wCellL2_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (m : ℕ) (f : Plane → E) :
    wCellL2 c m (fun z => ‖f z‖) ≤ wCellL2 c m f := by
  have h := PartI_T25.wCellL2_le_of_pointwise c m (K := 1) zero_le_one
    (fun z => ‖f z‖) f (fun z => by simp)
  simpa using h

/-! ### 2. Bilinear advection operator `advBil` and spacetime Leibniz bound -/

/-- Bilinear transport form `(u · ∇) v` on `Plane`. -/
def advBil (u v : Plane → Vec) (w : Plane) : Vec :=
  Train.toVec
    (u w 0 * Cyl.partialQ (fun x => v x 0) w + u w 1 * Cyl.partialEta (fun x => v x 0) w,
     u w 0 * Cyl.partialQ (fun x => v x 1) w + u w 1 * Cyl.partialEta (fun x => v x 1) w)

theorem advBil_apply (u v : Plane → Vec) (w : Plane) (k : Fin 2) :
    advBil u v w k =
      u w 0 * Cyl.partialQ (fun x => v x k) w + u w 1 * Cyl.partialEta (fun x => v x k) w := by
  fin_cases k <;> simp [advBil, Train.toVec_zero, Train.toVec_one]

theorem sm_advBil {U V : ℝ → Plane → Vec}
    (hU : Sm (fun x : ℝ × Plane => U x.1 x.2))
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) :
    Sm (fun x : ℝ × Plane => advBil (U x.1) (V x.1) x.2) := by
  have hU0 : PartI_T20.SmR (fun x : ℝ × Plane => U x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hU
  have hU1 : PartI_T20.SmR (fun x : ℝ × Plane => U x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hU
  have hV0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hV1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hQ0 := PartI_T20.smR_partialQ (F := fun r w => V r w 0) hV0
  have hE0 := PartI_T20.smR_partialEta (F := fun r w => V r w 0) hV0
  have hQ1 := PartI_T20.smR_partialQ (F := fun r w => V r w 1) hV1
  have hE1 := PartI_T20.smR_partialEta (F := fun r w => V r w 1) hV1
  have hpair : ContDiffOn ℝ ∞ (fun x : ℝ × Plane =>
      (U x.1 x.2 0 * Cyl.partialQ (fun y => V x.1 y 0) x.2 +
        U x.1 x.2 1 * Cyl.partialEta (fun y => V x.1 y 0) x.2,
       U x.1 x.2 0 * Cyl.partialQ (fun y => V x.1 y 1) x.2 +
        U x.1 x.2 1 * Cyl.partialEta (fun y => V x.1 y 1) x.2)) UU :=
    ((hU0.mul hQ0).add (hU1.mul hE0)).prodMk ((hU0.mul hQ1).add (hU1.mul hE1))
  exact (Train.toVecL : (ℝ × ℝ) →L[ℝ] Vec).contDiff.comp_contDiffOn hpair

theorem norm_ageJet_advBil_comp_le {U V : ℝ → Plane → Vec}
    (hU : Sm (fun x : ℝ × Plane => U x.1 x.2))
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2)
    (ℓ j : ℕ) {s M_U M_V : ℝ} (hs : 0 < s) (hMU : 0 ≤ M_U) (hMV : 0 ≤ M_V) (z : Plane)
    (hbdU : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i U s z‖ ≤ M_U)
    (hbdV : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i V s z‖ ≤ M_V) :
    ‖ageJet ℓ j (fun r w => advBil (U r) (V r) w k) s z‖ ≤
      2 * (2 : ℝ) ^ (ℓ + j) * M_U * M_V := by
  have hsm_u0 : PartI_T20.SmR (fun x : ℝ × Plane => U x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hU
  have hsm_u1 : PartI_T20.SmR (fun x : ℝ × Plane => U x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hU
  have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => V x.1 y k) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w k) hsm_vk
  have hsm_E : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => V x.1 y k) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w k) hsm_vk
  let A₀ : ℝ → Plane → ℝ := fun r w => U r w 0 * Cyl.partialQ (fun y => V r y k) w
  let A₁ : ℝ → Plane → ℝ := fun r w => U r w 1 * Cyl.partialEta (fun y => V r y k) w
  have hfun : (fun r w => advBil (U r) (V r) w k) = fun r w => A₀ r w + A₁ r w :=
    funext fun r => funext fun w => advBil_apply (U r) (V r) w k
  rw [hfun, PartI_T20.ageJet_add A₀ A₁ (hsm_u0.mul hsm_Q) (hsm_u1.mul hsm_E) hs ℓ j z]
  have hb₀ : ‖ageJet ℓ j A₀ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_U * M_V := by
    refine PartI_T20.norm_ageJet_mul_le hsm_u0 hsm_Q ℓ j hs hMU hMV z
      (fun r hr i hi => (PartI_T20.norm_ageJet_vec_proj_le hU 0 r i hs z).trans
        (hbdU r hr i (by omega)))
      (fun r hr i hi =>
        ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w k) hsm_vk r i hs z).trans
          (PartI_T20.norm_ageJet_vec_proj_le hV k r (i + 1) hs z)).trans
        (hbdV r hr (i + 1) (by omega)))
  have hb₁ : ‖ageJet ℓ j A₁ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M_U * M_V := by
    refine PartI_T20.norm_ageJet_mul_le hsm_u1 hsm_E ℓ j hs hMU hMV z
      (fun r hr i hi => (PartI_T20.norm_ageJet_vec_proj_le hU 1 r i hs z).trans
        (hbdU r hr i (by omega)))
      (fun r hr i hi =>
        ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w k) hsm_vk r i hs z).trans
          (PartI_T20.norm_ageJet_vec_proj_le hV k r (i + 1) hs z)).trans
        (hbdV r hr (i + 1) (by omega)))
  calc ‖ageJet ℓ j A₀ s z + ageJet ℓ j A₁ s z‖
      ≤ ‖ageJet ℓ j A₀ s z‖ + ‖ageJet ℓ j A₁ s z‖ := norm_add_le _ _
    _ ≤ (2 : ℝ) ^ (ℓ + j) * M_U * M_V + (2 : ℝ) ^ (ℓ + j) * M_U * M_V := add_le_add hb₀ hb₁
    _ = 2 * (2 : ℝ) ^ (ℓ + j) * M_U * M_V := by ring

theorem norm_ageJet_advBil_le {U V : ℝ → Plane → Vec}
    (hU : Sm (fun x : ℝ × Plane => U x.1 x.2))
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s M_U M_V : ℝ} (hs : 0 < s) (hMU : 0 ≤ M_U) (hMV : 0 ≤ M_V) (z : Plane)
    (hbdU : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i U s z‖ ≤ M_U)
    (hbdV : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i V s z‖ ≤ M_V) :
    ‖ageJet ℓ j (fun r w => advBil (U r) (V r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M_U * M_V := by
  have hsm_bil : Sm (fun x : ℝ × Plane => advBil (U x.1) (V x.1) x.2) := sm_advBil hU hV
  have hvec := PartI_T20_1.norm_ageJet_vec_le_add_proj
    (V := fun r w => advBil (U r) (V r) w) hsm_bil ℓ j hs z
  have h0 := norm_ageJet_advBil_comp_le hU hV 0 ℓ j hs hMU hMV z hbdU hbdV
  have h1 := norm_ageJet_advBil_comp_le hU hV 1 ℓ j hs hMU hMV z hbdU hbdV
  linarith

theorem advection_sub_eq_advBil {U V : ℝ → Plane → Vec}
    (hU : Sm (fun x : ℝ × Plane => U x.1 x.2))
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    {r : ℝ} (hr : 0 < r) (w : Plane) :
    Train.advection (U r) w - Train.advection (V r) w =
      advBil (fun x => U r x - V r x) (U r) w +
        advBil (V r) (fun x => U r x - V r x) w := by
  have hu : ContDiff ℝ ∞ (U r) := PartI_T25_1.contDiff_slice_of_sm hU hr
  have hv : ContDiff ℝ ∞ (V r) := PartI_T25_1.contDiff_slice_of_sm hV hr
  have hcomp_u : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x : Plane => U r x k) := fun k =>
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hcomp_v : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x : Plane => V r x k) := fun k =>
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hv
  have hQ : ∀ k : Fin 2,
      Cyl.partialQ (fun x => U r x k - V r x k) w =
        Cyl.partialQ (fun x => U r x k) w - Cyl.partialQ (fun x => V r x k) w := fun k =>
    TrainErrorEquation.partialQ_sub_eq
      (TrainErrorEquation.lineQ_of_contDiff (hcomp_u k))
      (TrainErrorEquation.lineQ_of_contDiff (hcomp_v k)) w
  have hE : ∀ k : Fin 2,
      Cyl.partialEta (fun x => U r x k - V r x k) w =
        Cyl.partialEta (fun x => U r x k) w - Cyl.partialEta (fun x => V r x k) w := fun k =>
    TrainErrorEquation.partialEta_sub_eq
      (TrainErrorEquation.lineE_of_contDiff (hcomp_u k))
      (TrainErrorEquation.lineE_of_contDiff (hcomp_v k)) w
  ext k
  simp only [PiLp.sub_apply, PiLp.add_apply, PartI_T20_1.advection_apply_eq, advBil_apply]
  rw [hQ k, hE k]
  ring

theorem ageJet_add_vec (F G : ℝ → Plane → Vec)
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2))
    (hG : Sm (fun x : ℝ × Plane => G x.1 x.2))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (w : Plane) :
    ageJet ℓ j (fun r v => F r v + G r v) s w =
      ageJet ℓ j F s w + ageJet ℓ j G s w := by
  have hadd : ∀ v : Plane, iteratedDeriv ℓ (fun r => F r v + G r v) s =
      iteratedDeriv ℓ (fun r => F r v) s + iteratedDeriv ℓ (fun r => G r v) s := fun v =>
    iteratedDeriv_add
      (UnforcedLeray.Short.IIb.vb_slice_smooth_at F hF hs v ℓ)
      (UnforcedLeray.Short.IIb.vb_slice_smooth_at G hG hs v ℓ)
  have hjet : (fun v : Plane => iteratedDeriv ℓ (fun r => F r v + G r v) s) =
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) +
        (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) :=
    funext hadd
  have hA : ContDiffAt ℝ j
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w :=
    UnforcedLeray.Short.IIb.vb_slice_contDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ j hs w
  have hB : ContDiffAt ℝ j
      (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w :=
    UnforcedLeray.Short.IIb.vb_slice_contDiffAt (fun x : ℝ × Plane => G x.1 x.2) hG ℓ j hs w
  unfold ageJet Train.jet
  show iteratedFDeriv ℝ j
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v + G r v) s) w =
    iteratedFDeriv ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w +
      iteratedFDeriv ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w
  rw [hjet, iteratedFDeriv_add_apply hA hB]

theorem ageJet_advection_sub_eq {U V : ℝ → Plane → Vec}
    (hU : Sm (fun x : ℝ × Plane => U x.1 x.2))
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ageJet ℓ j (fun r w => Train.advection (U r) w - Train.advection (V r) w) s z =
      ageJet ℓ j (fun r w => advBil (fun x => U r x - V r x) (U r) w) s z +
        ageJet ℓ j (fun r w => advBil (V r) (fun x => U r x - V r x) w) s z := by
  let D : ℝ → Plane → Vec := fun r x => U r x - V r x
  have hD : Sm (fun x : ℝ × Plane => D x.1 x.2) := hU.sub hV
  have hstep : ageJet ℓ j (fun r w => Train.advection (U r) w - Train.advection (V r) w) s =
      ageJet ℓ j (fun r w => advBil (D r) (U r) w + advBil (V r) (D r) w) s := by
    unfold ageJet
    congr 1
    funext w
    have hev : (fun r => Train.advection (U r) w - Train.advection (V r) w) =ᶠ[nhds s]
        fun r => advBil (D r) (U r) w + advBil (V r) (D r) w := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using advection_sub_eq_advBil hU hV hr w
    exact hev.iteratedDeriv_eq ℓ
  rw [hstep]
  exact ageJet_add_vec
    (fun r w => advBil (D r) (U r) w) (fun r w => advBil (V r) (D r) w)
    (sm_advBil hD hU) (sm_advBil hV hD) hs ℓ j z

/-! ### 3. Rectangle norm sum and uniform bounds for `Vc` and `dv` -/

/-- Sum of `‖ageJet r i F s z‖` over the rectangle `r ≤ L`, `i ≤ K`. -/
def rectNormSum (L K : ℕ) (F : ℝ → Plane → Vec) (s : ℝ) (z : Plane) : ℝ :=
  ∑ r ∈ Finset.range (L + 1), ∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖

theorem rectNormSum_nonneg (L K : ℕ) (F : ℝ → Plane → Vec) (s : ℝ) (z : Plane) :
    0 ≤ rectNormSum L K F s z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_rectNormSum {L K r i : ℕ} (hr : r ≤ L) (hi : i ≤ K)
    (F : ℝ → Plane → Vec) (s : ℝ) (z : Plane) :
    ‖ageJet r i F s z‖ ≤ rectNormSum L K F s z := by
  unfold rectNormSum
  have hi_mem : i ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have hr_mem : r ∈ Finset.range (L + 1) := Finset.mem_range.mpr (by omega)
  have h1 : ‖ageJet r i F s z‖ ≤ ∑ k ∈ Finset.range (K + 1), ‖ageJet r k F s z‖ :=
    Finset.single_le_sum (f := fun k => ‖ageJet r k F s z‖) (fun _ _ => norm_nonneg _) hi_mem
  have h2 : ∑ k ∈ Finset.range (K + 1), ‖ageJet r k F s z‖ ≤
      ∑ m ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (K + 1), ‖ageJet m k F s z‖ :=
    Finset.single_le_sum (f := fun m => ∑ k ∈ Finset.range (K + 1), ‖ageJet m k F s z‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hr_mem
  exact h1.trans h2

theorem rectNormSum_le_of_forall {L K : ℕ} {F : ℝ → Plane → Vec} {s B : ℝ}
    (z : Plane) (h : ∀ r ≤ L, ∀ i ≤ K, ‖ageJet r i F s z‖ ≤ B) :
    rectNormSum L K F s z ≤ ((L + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) * B := by
  unfold rectNormSum
  calc ∑ r ∈ Finset.range (L + 1), ∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖
      ≤ ∑ _r ∈ Finset.range (L + 1), ∑ _i ∈ Finset.range (K + 1), B := by
        refine Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun i hi => ?_
        exact h r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
          i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = ((L + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) * B := by
        simp [mul_assoc]

theorem continuous_rowNormSum (r K : ℕ) {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {s : ℝ} (hs : 0 < s) :
    Continuous (fun z : Plane => ∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖) :=
  continuous_finsetSum _ fun i _ => (continuous_ageJet_of_contDiffOn F hF r i hs).norm

theorem continuous_rectNormSum (L K : ℕ) {F : ℝ → Plane → Vec}
    (hF : Sm (fun x : ℝ × Plane => F x.1 x.2)) {s : ℝ} (hs : 0 < s) :
    Continuous (rectNormSum L K F s) :=
  continuous_finsetSum _ fun r _ => continuous_rowNormSum r K hF hs

theorem wCellL2_rowNormSum_le (c : ℝ) (r : ℕ) :
    ∀ (K : ℕ) {F : ℝ → Plane → Vec} (_hF : Sm (fun x : ℝ × Plane => F x.1 x.2))
      {s B : ℝ} (_hs : 0 < s) (_hB : 0 ≤ B)
      (_h : ∀ i ≤ K, wCellL2 c 0 (ageJet r i F s) ≤ ENNReal.ofReal B),
      wCellL2 c 0 (fun z : Plane => ∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖) ≤
        ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * B)
  | 0, F, _, s, B, _, _, h => by
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_one, one_mul]
    exact (wCellL2_norm_le c 0 (ageJet r 0 F s)).trans (h 0 le_rfl)
  | K + 1, F, hF, s, B, hs, hB, h => by
    have hfun : (fun z : Plane => ∑ i ∈ Finset.range (K + 1 + 1), ‖ageJet r i F s z‖) =
        fun z : Plane =>
          (∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖) + ‖ageJet r (K + 1) F s z‖ := by
      funext z
      exact Finset.sum_range_succ _ (K + 1)
    rw [hfun]
    have htri := wCellL2_add_le_of_continuous c 0
      (continuous_rowNormSum r K hF hs)
      (continuous_ageJet_of_contDiffOn F hF r (K + 1) hs).norm
    have h1 := wCellL2_rowNormSum_le c r K hF hs hB (fun i hi => h i (by omega))
    have h2 := (wCellL2_norm_le c 0 (ageJet r (K + 1) F s)).trans (h (K + 1) le_rfl)
    calc wCellL2 c 0 (fun z : Plane =>
          (∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖) + ‖ageJet r (K + 1) F s z‖)
        ≤ wCellL2 c 0 (fun z : Plane => ∑ i ∈ Finset.range (K + 1), ‖ageJet r i F s z‖) +
            wCellL2 c 0 (fun z : Plane => ‖ageJet r (K + 1) F s z‖) := htri
      _ ≤ ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * B) + ENNReal.ofReal B := add_le_add h1 h2
      _ = ENNReal.ofReal (((K + 1 + 1 : ℕ) : ℝ) * B) := by
          rw [← ENNReal.ofReal_add (by positivity) hB]
          congr 1
          push_cast
          ring

theorem wCellL2_rectNormSum_le (c : ℝ) :
    ∀ (L K : ℕ) {F : ℝ → Plane → Vec} (_hF : Sm (fun x : ℝ × Plane => F x.1 x.2))
      {s B : ℝ} (_hs : 0 < s) (_hB : 0 ≤ B)
      (_h : ∀ r ≤ L, ∀ i ≤ K, wCellL2 c 0 (ageJet r i F s) ≤ ENNReal.ofReal B),
      wCellL2 c 0 (rectNormSum L K F s) ≤
        ENNReal.ofReal (((L + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) * B)
  | 0, K, F, hF, s, B, hs, hB, h => by
    unfold rectNormSum
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_one, one_mul]
    exact wCellL2_rowNormSum_le c 0 K hF hs hB (fun i hi => h 0 le_rfl i hi)
  | L + 1, K, F, hF, s, B, hs, hB, h => by
    have hfun : rectNormSum (L + 1) K F s = fun z : Plane =>
        rectNormSum L K F s z + ∑ i ∈ Finset.range (K + 1), ‖ageJet (L + 1) i F s z‖ := by
      funext z
      unfold rectNormSum
      exact Finset.sum_range_succ _ (L + 1)
    rw [hfun]
    have htri := wCellL2_add_le_of_continuous c 0
      (continuous_rectNormSum L K hF hs)
      (continuous_rowNormSum (L + 1) K hF hs)
    have h1 := wCellL2_rectNormSum_le c L K hF hs hB (fun r hr i hi => h r (by omega) i hi)
    have h2 := wCellL2_rowNormSum_le c (L + 1) K hF hs hB (fun i hi => h (L + 1) le_rfl i hi)
    calc wCellL2 c 0 (fun z : Plane =>
          rectNormSum L K F s z + ∑ i ∈ Finset.range (K + 1), ‖ageJet (L + 1) i F s z‖)
        ≤ wCellL2 c 0 (rectNormSum L K F s) +
            wCellL2 c 0 (fun z : Plane => ∑ i ∈ Finset.range (K + 1), ‖ageJet (L + 1) i F s z‖) := htri
      _ ≤ ENNReal.ofReal (((L + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) * B) +
            ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * B) := add_le_add h1 h2
      _ = ENNReal.ofReal (((L + 1 + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) * B) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring

/-- Pointwise bound on `ageJet r i (Vc ν c) s z` for a single `(r, i)`. -/
theorem vc_ageJet_single_bound (r i : ℕ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → width ν s ≤ c ^ 2 →
        ∀ z : Plane, ‖ageJet r i (Vc ν c) s z‖ ≤ M := by
  obtain ⟨K_age, hK_age_nn, hAge⟩ := vcAgeJetLe_proof r i
  obtain ⟨C_V, hC_V_pos, hJet⟩ := UnforcedLeray.Short.IIb.vcSpatialJetBound_proof (i + 2 * r)
  refine ⟨K_age * C_V + 1, by positivity, fun {ν c s} hν hν1 hc hs hw z => ?_⟩
  have h1 := hAge ν c hν hc s hs z
  have h2 := hJet ν c s hν hc hs.le hw z
  have hν_pow : ν ^ r ≤ 1 := pow_le_one₀ hν.le hν1
  calc ‖ageJet r i (Vc ν c) s z‖
      ≤ ν ^ r * K_age * ‖jet (i + 2 * r) (Vc ν c s) z‖ := h1
    _ ≤ 1 * K_age * C_V := by
        have hK : ν ^ r * K_age ≤ 1 * K_age := mul_le_mul_of_nonneg_right hν_pow hK_age_nn
        exact mul_le_mul hK h2 (norm_nonneg _) (by positivity)
    _ ≤ K_age * C_V + 1 := by linarith

theorem vc_ageJet_row_bound (r : ℕ) :
    ∀ K : ℕ, ∃ M : ℝ, 0 < M ∧
      ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → width ν s ≤ c ^ 2 →
        ∀ z : Plane, ∀ i ≤ K, ‖ageJet r i (Vc ν c) s z‖ ≤ M
  | 0 => by
    obtain ⟨M, hM, hb⟩ := vc_ageJet_single_bound r 0
    refine ⟨M, hM, fun hν hν1 hc hs hw z i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact hb hν hν1 hc hs hw z
  | K + 1 => by
    obtain ⟨M₁, hM₁, hb₁⟩ := vc_ageJet_row_bound r K
    obtain ⟨M₂, hM₂, hb₂⟩ := vc_ageJet_single_bound r (K + 1)
    refine ⟨max M₁ M₂, lt_max_of_lt_left hM₁, fun hν hν1 hc hs hw z i hi => ?_⟩
    rcases Nat.of_le_succ hi with hiK | rfl
    · exact (hb₁ hν hν1 hc hs hw z i hiK).trans (le_max_left _ _)
    · exact (hb₂ hν hν1 hc hs hw z).trans (le_max_right _ _)

theorem vc_ageJet_rect_bound :
    ∀ L K : ℕ, ∃ M : ℝ, 0 < M ∧
      ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → width ν s ≤ c ^ 2 →
        ∀ z : Plane, ∀ r ≤ L, ∀ i ≤ K, ‖ageJet r i (Vc ν c) s z‖ ≤ M
  | 0, K => by
    obtain ⟨M, hM, hb⟩ := vc_ageJet_row_bound 0 K
    refine ⟨M, hM, fun hν hν1 hc hs hw z r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact hb hν hν1 hc hs hw z i hi
  | L + 1, K => by
    obtain ⟨M₁, hM₁, hb₁⟩ := vc_ageJet_rect_bound L K
    obtain ⟨M₂, hM₂, hb₂⟩ := vc_ageJet_row_bound (L + 1) K
    refine ⟨max M₁ M₂, lt_max_of_lt_left hM₁, fun hν hν1 hc hs hw z r hr i hi => ?_⟩
    rcases Nat.of_le_succ hr with hrL | rfl
    · exact (hb₁ hν hν1 hc hs hw z r hrL i hi).trans (le_max_left _ _)
    · exact (hb₂ hν hν1 hc hs hw z i hi).trans (le_max_right _ _)

/-- Uniform fixed-band bound for `ageJet r i dv s` across a row `i ≤ K` at fixed age order `r`. -/
theorem dv_ageJet_row_bound (r : ℕ) (hr : TrainFixedBandVelOrderUnweighted r)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) :
    ∀ K : ℕ,
      ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
              let c := trainPeriod ρ ν
              let dv : ℝ → Plane → Vec := fun t z => tr.v t z - Vc ν c t z
              ∀ i ≤ K,
                wCellL2 c 0 (ageJet r i dv s) ≤
                  ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
                wSupNorm 0 (ageJet r i dv s) ≤
                  ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))
  | 0 => by
    obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, h0⟩ := hr ρ hρ Sg hSg 0
    refine ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, fun ν hν hν_le tr htr s hs hs_le i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact h0 ν hν hν_le tr htr s hs hs_le
  | K + 1 => by
    obtain ⟨C₁, N₁, CS₁, bS₁, ν₁, hC₁, hbS₁, hν₁, h₁⟩ := dv_ageJet_row_bound r hr ρ hρ Sg hSg K
    obtain ⟨C₂, N₂, CS₂, bS₂, ν₂, hC₂, hbS₂, hν₂, h₂⟩ := hr ρ hρ Sg hSg (K + 1)
    refine ⟨max C₁ C₂, max N₁ N₂, max CS₁ CS₂, min bS₁ bS₂, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, lt_min hbS₁ hbS₂, lt_min hν₁ hν₂,
      fun ν hν hν_le tr htr s hs hs_le i hi => ?_⟩
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc_pos : 0 < c := by
      dsimp [c]; unfold trainPeriod; exact Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hi with hiK | rfl
    · obtain ⟨hL2, hSup⟩ := h₁ ν hν hν₁_le tr htr s hs hs_le i hiK
      have hmono := PartI_T25_3.polyP_exp_mono (le_max_left C₁ C₂) (by positivity)
        (le_max_left N₁ N₂) (le_max_left CS₁ CS₂) (min_le_left bS₁ bS₂) hν hc_pos.le
      exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hmono),
        hSup.trans (ENNReal.ofReal_le_ofReal hmono)⟩
    · obtain ⟨hL2, hSup⟩ := h₂ ν hν hν₂_le tr htr s hs hs_le
      have hmono := PartI_T25_3.polyP_exp_mono (le_max_right C₁ C₂) (by positivity)
        (le_max_right N₁ N₂) (le_max_right CS₁ CS₂) (min_le_right bS₁ bS₂) hν hc_pos.le
      exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hmono),
        hSup.trans (ENNReal.ofReal_le_ofReal hmono)⟩

/-- Uniform fixed-band bound for `ageJet r i dv s` across the rectangle `r ≤ L`, `i ≤ K`. -/
theorem dv_ageJet_rect_bound (ρ : ℝ) (hρ : 1 / 2 < ρ) (Sg : ℝ) (hSg : 0 < Sg) (K : ℕ) :
    ∀ (L : ℕ), (∀ r ≤ L, TrainFixedBandVelOrderUnweighted r) →
      ∃ C : ℝ, ∃ N : ℕ, ∃ CS bS ν₀ : ℝ, 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
        ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
          ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
            ∀ s : ℝ, 0 < s → s ≤ Sg / ν →
              let c := trainPeriod ρ ν
              let dv : ℝ → Plane → Vec := fun t z => tr.v t z - Vc ν c t z
              ∀ r ≤ L, ∀ i ≤ K,
                wCellL2 c 0 (ageJet r i dv s) ≤
                  ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2)) ∧
                wSupNorm 0 (ageJet r i dv s) ≤
                  ENNReal.ofReal (polyP C N ν c * Real.exp (CS / ν - bS * c ^ 2))
  | 0, hIH => by
    obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, h0⟩ :=
      dv_ageJet_row_bound 0 (hIH 0 le_rfl) ρ hρ Sg hSg K
    refine ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, fun ν hν hν_le tr htr s hs hs_le r hr i hi => ?_⟩
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    exact h0 ν hν hν_le tr htr s hs hs_le i hi
  | L + 1, hIH => by
    obtain ⟨C₁, N₁, CS₁, bS₁, ν₁, hC₁, hbS₁, hν₁, h₁⟩ :=
      dv_ageJet_rect_bound ρ hρ Sg hSg K L (fun r hr => hIH r (by omega))
    obtain ⟨C₂, N₂, CS₂, bS₂, ν₂, hC₂, hbS₂, hν₂, h₂⟩ :=
      dv_ageJet_row_bound (L + 1) (hIH (L + 1) le_rfl) ρ hρ Sg hSg K
    refine ⟨max C₁ C₂, max N₁ N₂, max CS₁ CS₂, min bS₁ bS₂, min ν₁ ν₂,
      lt_max_of_lt_left hC₁, lt_min hbS₁ hbS₂, lt_min hν₁ hν₂,
      fun ν hν hν_le tr htr s hs hs_le r hr i hi => ?_⟩
    have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc_pos : 0 < c := by
      dsimp [c]; unfold trainPeriod; exact Real.rpow_pos_of_pos hν _
    rcases Nat.of_le_succ hr with hrL | rfl
    · obtain ⟨hL2, hSup⟩ := h₁ ν hν hν₁_le tr htr s hs hs_le r hrL i hi
      have hmono := PartI_T25_3.polyP_exp_mono (le_max_left C₁ C₂) (by positivity)
        (le_max_left N₁ N₂) (le_max_left CS₁ CS₂) (min_le_left bS₁ bS₂) hν hc_pos.le
      exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hmono),
        hSup.trans (ENNReal.ofReal_le_ofReal hmono)⟩
    · obtain ⟨hL2, hSup⟩ := h₂ ν hν hν₂_le tr htr s hs hs_le i hi
      have hmono := PartI_T25_3.polyP_exp_mono (le_max_right C₁ C₂) (by positivity)
        (le_max_right N₁ N₂) (le_max_right CS₁ CS₂) (min_le_right bS₁ bS₂) hν hc_pos.le
      exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hmono),
        hSup.trans (ENNReal.ofReal_le_ofReal hmono)⟩

end PartI_T25_AdvDiff

/-- Unconditional proof of `TrainFixedBandAdvDiffStep` (`PartI:T25/1/2`). -/
theorem trainFixedBandAdvDiffStep_proof : TrainFixedBandAdvDiffStep := by
  intro ℓ hIH ρ hρ Sg hSg j
  obtain ⟨C₁, N₁, CS₁, bS₁, ν₁, hC₁, hbS₁, hν₁, hdv_rect⟩ :=
    PartI_T25_AdvDiff.dv_ageJet_rect_bound ρ hρ Sg hSg (j + 1) ℓ hIH
  obtain ⟨M_Vc, hM_Vc, hVc_rect⟩ := PartI_T25_AdvDiff.vc_ageJet_rect_bound ℓ (j + 1)
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ (1 + Sg) (by positivity)
  let R_card : ℝ := ((ℓ + 1 : ℕ) : ℝ) * ((j + 1 + 1 : ℕ) : ℝ)
  have hR_pos : 0 < R_card := by dsimp [R_card]; positivity
  let C_out : ℝ := 8 * (2 : ℝ) ^ (ℓ + j) * R_card * ((C₁ + M_Vc) * C₁)
  let N_out : ℕ := 2 * N₁
  let CS_out : ℝ := max CS₁ 0 + CS₁
  refine ⟨C_out, N_out, CS_out, bS₁, min ν₁ νp, by positivity, hbS₁, lt_min hν₁ hνp, ?_⟩
  intro ν hν hν_le tr htr s hs hs_le
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hνp_le : ν ≤ νp := hν_le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hνp_le.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hνp_le
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := zero_lt_one.trans_le hc1
  have hw_le_Sg : width ν s ≤ 1 + Sg := by
    unfold width
    have hνs : ν * s ≤ Sg := by
      have := mul_le_mul_of_nonneg_left hs_le hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    linarith
  have hSg_c2 : 1 + Sg ≤ c ^ 2 := by
    calc 1 + Sg ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  have hw_le_c2 : width ν s ≤ c ^ 2 := hw_le_Sg.trans hSg_c2
  let dv : ℝ → Plane → Vec := fun r z => tr.v r z - Vc ν c r z
  let advDiff : ℝ → Plane → Vec := fun r z =>
    Train.advection (tr.v r) z - Train.advection (Vc ν c r) z
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  have hsm_Vc : Sm (fun x : ℝ × Plane => Vc ν c x.1 x.2) := vcSmooth_proof ν c hν hc_pos
  have hsm_dv : Sm (fun x : ℝ × Plane => dv x.1 x.2) := hsm_v.sub hsm_Vc
  let E_dv : ℝ := polyP C₁ N₁ ν c * Real.exp (CS₁ / ν - bS₁ * c ^ 2)
  have hE_dv_pos : 0 < E_dv := by
    dsimp [E_dv]; unfold polyP; positivity
  have hdv_L2 : ∀ r ≤ ℓ, ∀ i ≤ j + 1, wCellL2 c 0 (ageJet r i dv s) ≤ ENNReal.ofReal E_dv :=
    fun r hr i hi => (hdv_rect ν hν hν₁_le tr htr s hs hs_le r hr i hi).1
  have hdv_pt : ∀ z : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i dv s z‖ ≤ E_dv :=
    fun z r hr i hi => PartI_T25_AdvDiff.norm_le_of_wSupNorm_zero_le hE_dv_pos.le
      (hdv_rect ν hν hν₁_le tr htr s hs hs_le r hr i hi).2 z
  have hVc_pt : ∀ z : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i (Vc ν c) s z‖ ≤ M_Vc :=
    fun z r hr i hi => hVc_rect hν hν1 hc_pos hs hw_le_c2 z r hr i hi
  let M_bg : ℝ := E_dv + M_Vc
  have hM_bg_pos : 0 < M_bg := add_pos hE_dv_pos hM_Vc
  have hv_pt : ∀ z : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i tr.v s z‖ ≤ M_bg := by
    intro z r hr i hi
    have hsub := UnforcedLeray.Short.IIb.vb_ageJet_sub tr.v (Vc ν c) hsm_v hsm_Vc hs r i z
    have heq : ageJet r i tr.v s z = ageJet r i dv s z + ageJet r i (Vc ν c) s z := by
      dsimp [dv]
      rw [hsub, sub_add_cancel]
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (hdv_pt z r hr i hi) (hVc_pt z r hr i hi))
  have hVc_pt' : ∀ z : Plane, ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i (Vc ν c) s z‖ ≤ M_bg :=
    fun z r hr i hi => (hVc_pt z r hr i hi).trans (by dsimp [M_bg]; linarith [hE_dv_pos.le])
  let K_bil : ℝ := 8 * (2 : ℝ) ^ (ℓ + j) * M_bg
  have hK_bil_nn : 0 ≤ K_bil := by dsimp [K_bil]; positivity
  have hpt_rect : ∀ z : Plane,
      ‖ageJet ℓ j advDiff s z‖ ≤
        K_bil * ‖PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z‖ := by
    intro z
    have hrect_nn := PartI_T25_AdvDiff.rectNormSum_nonneg ℓ (j + 1) dv s z
    have hbd_dv : ∀ r ≤ ℓ, ∀ i ≤ j + 1,
        ‖ageJet r i dv s z‖ ≤ PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z :=
      fun r hr i hi => PartI_T25_AdvDiff.le_rectNormSum hr hi dv s z
    have h1 := PartI_T25_AdvDiff.norm_ageJet_advBil_le hsm_dv hsm_v ℓ j hs hrect_nn hM_bg_pos.le z
      hbd_dv (hv_pt z)
    have h2 := PartI_T25_AdvDiff.norm_ageJet_advBil_le hsm_Vc hsm_dv ℓ j hs hM_bg_pos.le hrect_nn z
      (hVc_pt' z) hbd_dv
    have hdecomp := PartI_T25_AdvDiff.ageJet_advection_sub_eq hsm_v hsm_Vc ℓ j hs z
    change ‖ageJet ℓ j (fun r w => Train.advection (tr.v r) w - Train.advection (Vc ν c r) w) s z‖ ≤ _
    rw [hdecomp, Real.norm_of_nonneg hrect_nn]
    calc ‖ageJet ℓ j (fun r w => PartI_T25_AdvDiff.advBil (dv r) (tr.v r) w) s z +
          ageJet ℓ j (fun r w => PartI_T25_AdvDiff.advBil (Vc ν c r) (dv r) w) s z‖
        ≤ ‖ageJet ℓ j (fun r w => PartI_T25_AdvDiff.advBil (dv r) (tr.v r) w) s z‖ +
            ‖ageJet ℓ j (fun r w => PartI_T25_AdvDiff.advBil (Vc ν c r) (dv r) w) s z‖ :=
          norm_add_le _ _
      _ ≤ 4 * (2 : ℝ) ^ (ℓ + j) * PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z * M_bg +
            4 * (2 : ℝ) ^ (ℓ + j) * M_bg * PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z :=
          add_le_add h1 h2
      _ = K_bil * PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z := by dsimp [K_bil]; ring
  have habsorb : K_bil * (R_card * E_dv) ≤
      polyP C_out N_out ν c * Real.exp (CS_out / ν - bS₁ * c ^ 2) := by
    let X : ℝ := 1 + c + ν⁻¹
    have hν_inv_nn : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have hX1 : 1 ≤ X := by dsimp [X]; linarith
    have hXN1 : 1 ≤ X ^ N₁ := one_le_pow₀ hX1
    let E_max : ℝ := Real.exp (max CS₁ 0 / ν)
    have hE_max_ge1 : 1 ≤ E_max :=
      Real.one_le_exp (div_nonneg (le_max_right _ _) hν.le)
    have hE_dv_le_max : Real.exp (CS₁ / ν - bS₁ * c ^ 2) ≤ E_max := by
      dsimp [E_max]
      apply Real.exp_le_exp.mpr
      have h1 : CS₁ / ν ≤ max CS₁ 0 / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      have h2 : 0 ≤ bS₁ * c ^ 2 := by positivity
      linarith
    have hM_bg_le : M_bg ≤ (C₁ + M_Vc) * X ^ N₁ * E_max := by
      have h1 : E_dv ≤ C₁ * X ^ N₁ * E_max := by
        dsimp [E_dv]; unfold polyP
        exact mul_le_mul_of_nonneg_left hE_dv_le_max (by positivity)
      have h2 : M_Vc ≤ M_Vc * X ^ N₁ * E_max := by
        calc M_Vc = M_Vc * 1 * 1 := by ring
          _ ≤ M_Vc * X ^ N₁ * E_max := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hXN1 hM_Vc.le) hE_max_ge1
                zero_le_one (by positivity)
      dsimp [M_bg]
      linarith
    have hexp_mul : E_max * Real.exp (CS₁ / ν - bS₁ * c ^ 2) =
        Real.exp (CS_out / ν - bS₁ * c ^ 2) := by
      dsimp [E_max, CS_out]
      rw [← Real.exp_add]
      congr 1
      ring
    calc K_bil * (R_card * E_dv)
        = 8 * (2 : ℝ) ^ (ℓ + j) * R_card * M_bg * E_dv := by dsimp [K_bil]; ring
      _ ≤ 8 * (2 : ℝ) ^ (ℓ + j) * R_card * ((C₁ + M_Vc) * X ^ N₁ * E_max) * E_dv := by
          apply mul_le_mul_of_nonneg_right _ hE_dv_pos.le
          exact mul_le_mul_of_nonneg_left hM_bg_le (by positivity)
      _ = C_out * X ^ N_out * (E_max * Real.exp (CS₁ / ν - bS₁ * c ^ 2)) := by
          dsimp [C_out, N_out, E_dv]
          unfold polyP
          rw [two_mul, pow_add]
          ring
      _ = polyP C_out N_out ν c * Real.exp (CS_out / ν - bS₁ * c ^ 2) := by
          rw [hexp_mul]
          rfl
  have hL2_dom := PartI_T25.wCellL2_le_of_pointwise c 0 hK_bil_nn
    (ageJet ℓ j advDiff s) (PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s) hpt_rect
  have hL2_rect := PartI_T25_AdvDiff.wCellL2_rectNormSum_le c ℓ (j + 1) hsm_dv hs hE_dv_pos.le hdv_L2
  refine ⟨?_, ?_⟩
  · calc wCellL2 c 0 (ageJet ℓ j advDiff s)
        ≤ ENNReal.ofReal K_bil * wCellL2 c 0 (PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s) :=
          hL2_dom
      _ ≤ ENNReal.ofReal K_bil * ENNReal.ofReal (R_card * E_dv) := by gcongr
      _ = ENNReal.ofReal (K_bil * (R_card * E_dv)) := by
          rw [← ENNReal.ofReal_mul hK_bil_nn]
      _ ≤ ENNReal.ofReal (polyP C_out N_out ν c * Real.exp (CS_out / ν - bS₁ * c ^ 2)) :=
          ENNReal.ofReal_le_ofReal habsorb
  · refine PartI_T25_AdvDiff.wSupNorm_zero_le_of_forall_norm_le fun z => ?_
    have hrect_le := PartI_T25_AdvDiff.rectNormSum_le_of_forall z (hdv_pt z)
    have hrect_nn := PartI_T25_AdvDiff.rectNormSum_nonneg ℓ (j + 1) dv s z
    calc ‖ageJet ℓ j advDiff s z‖
        ≤ K_bil * ‖PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z‖ := hpt_rect z
      _ = K_bil * PartI_T25_AdvDiff.rectNormSum ℓ (j + 1) dv s z := by
          rw [Real.norm_of_nonneg hrect_nn]
      _ ≤ K_bil * (R_card * E_dv) :=
          mul_le_mul_of_nonneg_left hrect_le hK_bil_nn
      _ ≤ polyP C_out N_out ν c * Real.exp (CS_out / ν - bS₁ * c ^ 2) := habsorb

end UnforcedLeray.Short.PartI
