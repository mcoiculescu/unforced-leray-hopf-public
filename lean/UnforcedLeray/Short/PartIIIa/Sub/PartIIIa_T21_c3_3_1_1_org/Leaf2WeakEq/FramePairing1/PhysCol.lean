import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairingDefs
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Residual
import UnforcedLeray.Short.PartIIIa.T06_ScalingJa
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit

/-!
# Physical-variable periodized frame columns and rate identity

Helper for `PartIII-a:T21/c3/3/1/1/2/2/3/c/1` (`FramePairingFTC`, SP 2905-2925, 2937-2958).
Expresses the rescaled periodized growing mode `J_{a(q)} (perE κ (dd ν q) j)` on the fixed
physical cell `C_{ν⁻²}` via `LamJetInf.perPhys`, proves joint `C^∞` smoothness, computes its
backward free-adjoint operator `(∂_q - ν Δ + v · ∇)`, relates cell pairings between moving and
physical coordinates, and establishes uniform `X_{m,c}` bounds on `[0, s]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.FramePairing1Aux

/-! ## 1. `Good` regularity and physical column definition -/

/-- Seed growing modes `κ.e j` belong to `LamJetInf.Good`. -/
theorem good_e {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    LamJetInf.Good (κ.e j) := by
  have ⟨hsm, hdec⟩ := OscillatorForceSub.seed_e_smooth_decay hκ
  refine ⟨hsm j, fun k => ?_⟩
  obtain ⟨C₁, hC₁, hb₁⟩ := hdec j k
  obtain ⟨C₂, hC₂, hb₂⟩ := LamJetInf.pow_mul_exp_le (k + 2)
  refine ⟨C₁ * 2 ^ (k + 2) * C₂, by positivity, fun z => ?_⟩
  set s : ℝ := (z.1 ^ 2 + z.2 ^ 2) / 2
  have hs0 : 0 ≤ s := by positivity
  have hz_le : ‖z‖ ≤ s + 1 := by
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs]
      simp only [s]
      nlinarith [sq_abs z.1, sq_nonneg (|z.1| - 1), sq_nonneg z.2]
    · rw [Real.norm_eq_abs]
      simp only [s]
      nlinarith [sq_abs z.2, sq_nonneg (|z.2| - 1), sq_nonneg z.1]
  have h1z : 1 + ‖z‖ ≤ 2 * (1 + s) := by linarith
  have hpow : (1 + ‖z‖) ^ (k + 2) ≤ 2 ^ (k + 2) * (1 + s) ^ (k + 2) := by
    calc (1 + ‖z‖) ^ (k + 2) ≤ (2 * (1 + s)) ^ (k + 2) :=
          pow_le_pow_left₀ (by positivity) h1z (k + 2)
      _ = 2 ^ (k + 2) * (1 + s) ^ (k + 2) := mul_pow _ _ _
  have hexp_eq : -(z.1 ^ 2 + z.2 ^ 2) / 8 = (-1 / 4) * s := by
    simp only [s]; ring
  have hk0 : ‖iteratedFDeriv ℝ k (κ.e j) z‖ ≤ C₁ * Real.exp ((-1 / 4) * s) := by
    have h := hb₁ z
    rw [hexp_eq] at h
    refine (le_mul_of_one_le_left (norm_nonneg _) ?_).trans h
    linarith [norm_nonneg z]
  calc ‖iteratedFDeriv ℝ k (κ.e j) z‖ * (1 + ‖z‖) ^ (k + 2)
      ≤ (C₁ * Real.exp ((-1 / 4) * s)) * (2 ^ (k + 2) * (1 + s) ^ (k + 2)) :=
        mul_le_mul hk0 hpow (by positivity) (by positivity)
    _ = C₁ * 2 ^ (k + 2) * ((1 + s) ^ (k + 2) * Real.exp ((-1 / 4) * s)) := by ring
    _ ≤ C₁ * 2 ^ (k + 2) * C₂ :=
        mul_le_mul_of_nonneg_left (hb₂ s hs0) (by positivity)

/-- Physical-variable periodized frame column `J_{a(q)} (perE κ (dd ν q) j)` on `C_{ν⁻²}`. -/
def physFrameE (κ : PlanarFrameKernels) (ν q : ℝ) (j : Fin 2) (x : ℝ × ℝ) : ℂ :=
  (((clockA ν q)⁻¹ : ℝ) : ℂ) ^ 3 * LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (κ.e j) (q, x)

/-- Physical-variable free-adjoint rate `(∂_q - ν Δ + v(q)·∇) (physFrameE κ ν q j)`. -/
def physFrameERate (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (q : ℝ) (j : Fin 2) (x : ℝ × ℝ) : ℂ :=
  ladDt (fun q' x' => physFrameE κ ν q' j x') q x -
    (ν : ℂ) * ladLapCx (physFrameE κ ν q j) x +
    ladTransport tr q (physFrameE κ ν q j) x

/-- Pointwise relation between `LamJetInf.perPhys` and `perSum (dd ν q)`. -/
theorem perPhys_eq_clockA_mul_perSum (ν q : ℝ) (L : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) L (q, x) =
      ((clockA ν q : ℝ) : ℂ) *
        perSum (dd ν q) L (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) := by
  unfold LamJetInf.perPhys perSum physAdj dd cellLen
  dsimp only
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  congr 2
  ext <;> simp [add_div, mul_div_assoc]

/-- `physFrameE` agrees pointwise with `Jscale (clockA ν q) (perE κ (dd ν q) j)`. -/
theorem physFrameE_eq_jscale_perE (κ : PlanarFrameKernels) {ν q : ℝ} (ha : 0 < clockA ν q)
    (j : Fin 2) (x : ℝ × ℝ) :
    physFrameE κ ν q j x = Jscale (clockA ν q) (perE κ (dd ν q) j) x := by
  unfold physFrameE Jscale perE
  rw [perPhys_eq_clockA_mul_perSum ν q]
  have hrpow : (clockA ν q) ^ (-2 : ℝ) = ((clockA ν q)⁻¹) ^ 3 * clockA ν q := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    field_simp [ha.ne']
  rw [hrpow]
  push_cast
  ring

/-- Horizontal `ν⁻²`-periodicity of `physFrameE`. -/
theorem physFrameE_periodic (κ : PlanarFrameKernels) (ν q : ℝ) (j : Fin 2) (x : ℝ × ℝ) :
    physFrameE κ ν q j (x.1 + ν ^ (-2 : ℝ), x.2) = physFrameE κ ν q j x := by
  unfold physFrameE LamJetInf.perPhys perSum
  dsimp only
  congr 1
  rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  ext <;> (simp; try ring)

/-- Joint `C^∞` smoothness of `(q, x) ↦ physFrameE κ ν q j x` on `LamJetInf.physU ν`. -/
theorem contDiffOn_physFrameE_physU {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν : ℝ} (hν : 0 < ν) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameE κ ν p.1 j p.2) (LamJetInf.physU ν) := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν _).ne'
  have hP : ContDiffOn ℝ ∞ (LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (κ.e j)) (LamJetInf.physU ν) :=
    LamJetInf.contDiffOn_perPhys hν hc (good_e hκ j)
  have hA : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => clockA ν p.1) (LamJetInf.physU ν) :=
    ((CutFTCSmooth.contDiff_clockA ν).comp contDiff_fst).contDiffOn
  have hAinv : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (clockA ν p.1)⁻¹) (LamJetInf.physU ν) :=
    hA.inv fun _ hp => ne_of_gt hp
  have hfac : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => (((clockA ν p.1)⁻¹ : ℝ) : ℂ) ^ 3) (LamJetInf.physU ν) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hAinv).pow 3
  exact hfac.mul hP

/-- Joint `C^∞` smoothness on `Ico t₁ S ×ˢ univ` for `0 ≤ t₁`. -/
theorem contDiffOn_physFrameE {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν t₁ S : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameE κ ν p.1 j p.2)
      (Ico t₁ S ×ˢ univ) := by
  refine (contDiffOn_physFrameE_physU hκ hν j).mono fun p hp => ?_
  show 0 < clockA ν p.1
  have h0 : 0 ≤ p.1 := ht₁.trans hp.1.1
  unfold clockA
  nlinarith

/-- Spatial `C^∞` smoothness of a slice `physFrameE κ ν q j` when `0 < clockA ν q`. -/
theorem contDiff_physFrameE_slice {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν q) (j : Fin 2) :
    ContDiff ℝ ∞ (physFrameE κ ν q j) := by
  have h := (contDiffOn_physFrameE_physU hκ hν j).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun _ => ha)
  exact h

/-! ## 2. Exact derivatives and PDE rate identity -/

/-- First spatial partial derivative of `LamJetInf.perPhys` for a `Good` kernel. -/
theorem pdCx_perPhys_eq {ν : ℝ} (hν : 0 < ν) {L : ℝ × ℝ → ℂ} (hL : LamJetInf.Good L)
    {q : ℝ} (ha : 0 < clockA ν q) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (fun y => LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) L (q, y)) x =
      ((Real.sqrt (clockA ν q) * (clockA ν q)⁻¹ : ℝ) : ℂ) *
        LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (pdCx k L) (q, x) := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν _).ne'
  have hF := (LamJetInf.hasFDerivAt_perPhys hν hc hL (p₀ := (q, x)) ha).1
  have hcomp := hF.comp x ((hasFDerivAt_const q x).prodMk (hasFDerivAt_id x))
  unfold pdCx
  change fderiv ℝ (LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) L ∘ Prod.mk q) x (B0579.dir k) = _
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, ← hF.fderiv]
  have happ := LamJetInf.fderiv_perPhys_apply hν hc hL (p := (q, x)) ha (0, B0579.dir k)
  simpa [pdCx] using happ

/-- First spatial partial derivative of `physFrameE`. -/
theorem pdCx_physFrameE_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν q) (j k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (physFrameE κ ν q j) x =
      (((clockA ν q)⁻¹ ^ 3 * Real.sqrt (clockA ν q) : ℝ) : ℂ) *
        perSum (dd ν q) (pdCx k (κ.e j))
          (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν _).ne'
  have hL := good_e hκ j
  have hdiff : DifferentiableAt ℝ
      (fun y => LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (κ.e j) (q, y)) x :=
    ((LamJetInf.hasFDerivAt_perPhys hν hc hL (p₀ := (q, x)) ha).1.comp x
      ((hasFDerivAt_const q x).prodMk (hasFDerivAt_id x))).differentiableAt
  unfold physFrameE
  have hm := RateSplitAux.pdCx_mul k
    (differentiableAt_const ((((clockA ν q)⁻¹ : ℝ) : ℂ) ^ 3)) hdiff
  have hc0 : pdCx k (fun _ : ℝ × ℝ => (((clockA ν q)⁻¹ : ℝ) : ℂ) ^ 3) x = 0 := by
    unfold pdCx; simp
  rw [hm, hc0, zero_mul, zero_add, pdCx_perPhys_eq hν hL ha k x,
    perPhys_eq_clockA_mul_perSum ν q]
  have ha0 : (clockA ν q : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

/-- Second spatial partial derivative of `physFrameE`. -/
theorem pdCx2_physFrameE_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν q) (j k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (pdCx k (physFrameE κ ν q j)) x =
      (((clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) *
        perSum (dd ν q) (pdCx k (pdCx k (κ.e j)))
          (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν _).ne'
  have hL := good_e hκ j
  have hLk : LamJetInf.Good (pdCx k (κ.e j)) := hL.fderiv_apply (B0579.dir k)
  have h1 : pdCx k (physFrameE κ ν q j) = fun y =>
      ((((clockA ν q)⁻¹ : ℝ) : ℂ) ^ 3 *
        ((Real.sqrt (clockA ν q) * (clockA ν q)⁻¹ : ℝ) : ℂ)) *
        LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (pdCx k (κ.e j)) (q, y) := by
    funext y
    rw [pdCx_physFrameE_eq hκ hν ha j k y, perPhys_eq_clockA_mul_perSum ν q]
    have ha0 : (clockA ν q : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  rw [h1]
  have hdiff : DifferentiableAt ℝ
      (fun y => LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (pdCx k (κ.e j)) (q, y)) x :=
    ((LamJetInf.hasFDerivAt_perPhys hν hc hLk (p₀ := (q, x)) ha).1.comp x
      ((hasFDerivAt_const q x).prodMk (hasFDerivAt_id x))).differentiableAt
  have hm := RateSplitAux.pdCx_mul k
    (differentiableAt_const ((((clockA ν q)⁻¹ : ℝ) : ℂ) ^ 3 *
      ((Real.sqrt (clockA ν q) * (clockA ν q)⁻¹ : ℝ) : ℂ))) hdiff
  have hc0 : pdCx k (fun _ : ℝ × ℝ =>
      (((clockA ν q)⁻¹ : ℝ) : ℂ) ^ 3 *
        ((Real.sqrt (clockA ν q) * (clockA ν q)⁻¹ : ℝ) : ℂ)) x = 0 := by
    unfold pdCx; simp
  rw [hm, hc0, zero_mul, zero_add, pdCx_perPhys_eq hν hLk ha k x,
    perPhys_eq_clockA_mul_perSum ν q]
  have hsq : Real.sqrt (clockA ν q) * Real.sqrt (clockA ν q) = clockA ν q :=
    Real.mul_self_sqrt ha.le
  have ha0 : (clockA ν q : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hsqC : ((Real.sqrt (clockA ν q) : ℝ) : ℂ) * ((Real.sqrt (clockA ν q) : ℝ) : ℂ) =
      (clockA ν q : ℂ) := by exact_mod_cast hsq
  push_cast
  calc (((clockA ν q : ℂ)⁻¹ ^ 3 * (((Real.sqrt (clockA ν q) : ℝ) : ℂ) * (clockA ν q : ℂ)⁻¹)) *
        ((((Real.sqrt (clockA ν q) : ℝ) : ℂ) * (clockA ν q : ℂ)⁻¹) *
          ((clockA ν q : ℂ) * perSum (dd ν q) (pdCx k (pdCx k (κ.e j)))
            (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)))))
      = (clockA ν q : ℂ)⁻¹ ^ 3 *
          ((((Real.sqrt (clockA ν q) : ℝ) : ℂ) * ((Real.sqrt (clockA ν q) : ℝ) : ℂ)) *
            (clockA ν q : ℂ)⁻¹ * (clockA ν q : ℂ)⁻¹ * (clockA ν q : ℂ)) *
          perSum (dd ν q) (pdCx k (pdCx k (κ.e j)))
            (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) := by ring
    _ = (clockA ν q : ℂ)⁻¹ ^ 3 *
          perSum (dd ν q) (pdCx k (pdCx k (κ.e j)))
            (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) := by
          rw [hsqC]
          field_simp

/-- Time derivative of `q ↦ physFrameE κ ν q j x` for `0 < clockA ν q`. -/
theorem hasDerivAt_physFrameE {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν q) (j : Fin 2) (x : ℝ × ℝ) :
    HasDerivAt (fun q' => physFrameE κ ν q' j x)
      (((ν * (clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) *
        (-(3 : ℂ) * perSum (dd ν q) (κ.e j)
            (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) +
          perSum (dd ν q) (LamJetInf.eulerK (κ.e j))
            (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)))) q := by
  have hc : ν ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hν _).ne'
  have hL := good_e hκ j
  have hdA : HasDerivAt (clockA ν) ν q := FrameAmplSub.hasDerivAt_clockA ν q
  have hdAinv : HasDerivAt (fun q' => (clockA ν q')⁻¹) (-ν / (clockA ν q) ^ 2) q :=
    hdA.inv ha.ne'
  have hdC : HasDerivAt (fun q' => (((clockA ν q')⁻¹ : ℝ) : ℂ))
      (((-ν / (clockA ν q) ^ 2 : ℝ) : ℂ)) q :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt q hdAinv)
  have hdPow : HasDerivAt (fun q' => (((clockA ν q')⁻¹ : ℝ) : ℂ) ^ 3)
      (((3 : ℕ) : ℂ) * (((clockA ν q)⁻¹ : ℝ) : ℂ) ^ (3 - 1) *
        ((-ν / (clockA ν q) ^ 2 : ℝ) : ℂ)) q :=
    hdC.pow 3
  have hF := (LamJetInf.hasFDerivAt_perPhys hν hc hL (p₀ := (q, x)) ha).1
  have hdι : HasDerivAt (fun q' : ℝ => (q', x)) (1, (0 : ℝ × ℝ)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q x)
  have hdP : HasDerivAt (fun q' => LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (κ.e j) (q', x))
      (((ν * 1 * (clockA ν q)⁻¹ : ℝ) : ℂ) *
        LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) (LamJetInf.eulerK (κ.e j)) (q, x)) q := by
    refine (hF.comp_hasDerivAt q hdι).congr_deriv ?_
    rw [hF.fderiv.symm, LamJetInf.fderiv_perPhys_apply hν hc hL (p := (q, x)) ha (1, (0 : ℝ × ℝ))]
    simp [LamJetInf.perPhys, perSum, physAdj]
  refine (hdPow.mul hdP).congr_deriv ?_
  rw [perPhys_eq_clockA_mul_perSum ν q, perPhys_eq_clockA_mul_perSum ν q]
  have ha0 : (clockA ν q : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

/-- Summability of `n ↦ L (y.1 + n * d, y.2)` for `LamJetInf.Good L` and `d ≠ 0`. -/
lemma summable_perSum_of_good {d : ℝ} (hd : d ≠ 0) {L : ℝ × ℝ → ℂ} (hL : LamJetInf.Good L)
    (y : ℝ × ℝ) : Summable (fun n : ℤ => L (y.1 + n * d, y.2)) := by
  obtain ⟨C, _, hC⟩ := hL.norm_le
  refine Summable.of_norm_bounded ((LamJetInf.summable_inv_sq_shift hd y.1).mul_left C) fun n => ?_
  have h1 := hC (y.1 + n * d, y.2)
  have hle : 1 + |y.1 + n * d| ≤ 1 + ‖(y.1 + n * d, y.2)‖ := by
    have : |y.1 + n * d| ≤ ‖(y.1 + n * d, y.2)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_fst_le (y.1 + n * d, y.2)
    linarith
  have hp1 : 0 < (1 + |y.1 + n * d|) ^ 2 := by positivity
  have hp2 : (1 + |y.1 + n * d|) ^ 2 ≤ (1 + ‖(y.1 + n * d, y.2)‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  rw [← div_eq_mul_inv, le_div_iff₀ hp1]
  exact (mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)).trans h1

/-- Heat + drift identity: `(∂_q - ν Δ)(physFrameE) = -a⁻² J_a(movOscRes)` for `q ≥ 0`. -/
theorem heat_part_physFrameE_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q : ℝ} (hν : 0 < ν) (hq : 0 ≤ q) (j : Fin 2) (x : ℝ × ℝ) :
    ladDt (fun q' x' => physFrameE κ ν q' j x') q x -
        (ν : ℂ) * ladLapCx (physFrameE κ ν q j) x =
      -((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
          Jscale (clockA ν q) (movOscRes κ ν q j) x) := by
  have ha1 : 1 ≤ clockA ν q := one_le_clockA hν.le hq
  have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one ha1
  have hd : 0 < dd ν q := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha)
  have hdt := ladDt_eq_of_hasDerivAt (hasDerivAt_physFrameE hκ hν ha j x)
  unfold ladLapCx
  rw [hdt, pdCx2_physFrameE_eq hκ hν ha j 0 x, pdCx2_physFrameE_eq hκ hν ha j 1 x]
  set y : ℝ × ℝ := (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q))
  have hL := good_e hκ j
  have hs_e := summable_perSum_of_good hd.ne' hL y
  have hs_eu := summable_perSum_of_good hd.ne' hL.eulerK y
  have hs_d0 : Summable (fun n : ℤ => pdCx 0 (pdCx 0 (κ.e j)) (y.1 + n * dd ν q, y.2)) :=
    summable_perSum_of_good hd.ne'
      ((hL.fderiv_apply (B0579.dir 0)).fderiv_apply (B0579.dir 0)) y
  have hs_d1 : Summable (fun n : ℤ => pdCx 1 (pdCx 1 (κ.e j)) (y.1 + n * dd ν q, y.2)) :=
    summable_perSum_of_good hd.ne'
      ((hL.fderiv_apply (B0579.dir 1)).fderiv_apply (B0579.dir 1)) y
  have hosc := OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν hq j y
  unfold Jscale
  rw [show (x.1 / Real.sqrt (clockA ν q), x.2 / Real.sqrt (clockA ν q)) = y from rfl, hosc]
  -- Pointwise identity `-3 L + eulerK L - (∂₀² L + ∂₁² L) = -movD L`
  have hker : ∀ z : ℝ × ℝ,
      -(3 : ℂ) * κ.e j z + LamJetInf.eulerK (κ.e j) z -
        (pdCx 0 (pdCx 0 (κ.e j)) z + pdCx 1 (pdCx 1 (κ.e j)) z) =
      -movD (κ.e j) z := by
    intro z
    have hz_decomp : z = z.1 • B0579.dir 0 + z.2 • B0579.dir 1 := by
      ext <;> simp [B0579.dir]
    have hdir : fderiv ℝ (κ.e j) z z =
        ((z.1 : ℝ) : ℂ) * pdCx 0 (κ.e j) z + ((z.2 : ℝ) : ℂ) * pdCx 1 (κ.e j) z := by
      have happ := congrArg (fderiv ℝ (κ.e j) z) hz_decomp
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
        ContinuousLinearMap.map_smul] at happ
      rw [happ]
      simp [pdCx, Complex.real_smul]
    unfold LamJetInf.eulerK movD ladLapCx
    rw [hdir]
    ring
  have htsum : -(3 : ℂ) * perSum (dd ν q) (κ.e j) y +
      perSum (dd ν q) (LamJetInf.eulerK (κ.e j)) y -
      (perSum (dd ν q) (pdCx 0 (pdCx 0 (κ.e j))) y +
        perSum (dd ν q) (pdCx 1 (pdCx 1 (κ.e j))) y) =
      -perSum (dd ν q) (movD (κ.e j)) y := by
    unfold perSum
    rw [← tsum_mul_left, ← (hs_e.mul_left _).tsum_add hs_eu, ← hs_d0.tsum_add hs_d1,
      ← ((hs_e.mul_left _).add hs_eu).tsum_sub (hs_d0.add hs_d1), ← tsum_neg]
    exact tsum_congr fun n => hker (y.1 + n * dd ν q, y.2)
  have hcoef : ν * (clockA ν q)⁻¹ ^ 3 =
      (clockA ν q) ^ (-2 : ℝ) * ((clockA ν q) ^ (-2 : ℝ) * (clockTheta ν q)⁻¹) := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    unfold clockTheta
    rw [inv_inv]
    field_simp [ha.ne']
  have hcoefC : ((ν * (clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) =
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * (clockTheta ν q : ℂ)⁻¹) := by
    have := congrArg (Complex.ofReal) hcoef
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv] using this
  have hsplit : ((ν * (clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) *
        (-(3 : ℂ) * perSum (dd ν q) (κ.e j) y +
          perSum (dd ν q) (LamJetInf.eulerK (κ.e j)) y) -
      (ν : ℂ) * ((((clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) * perSum (dd ν q) (pdCx 0 (pdCx 0 (κ.e j))) y +
        (((clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) * perSum (dd ν q) (pdCx 1 (pdCx 1 (κ.e j))) y) =
      ((ν * (clockA ν q)⁻¹ ^ 3 : ℝ) : ℂ) *
        (-(3 : ℂ) * perSum (dd ν q) (κ.e j) y +
          perSum (dd ν q) (LamJetInf.eulerK (κ.e j)) y -
          (perSum (dd ν q) (pdCx 0 (pdCx 0 (κ.e j))) y +
            perSum (dd ν q) (pdCx 1 (pdCx 1 (κ.e j))) y)) := by
    push_cast; ring
  rw [hsplit, htsum, hcoefC]
  ring

/-- Transport identity: `(v(q)·∇)(physFrameE) = a⁻² J_a(V(q)·∇ E_j)`. -/
theorem transport_part_physFrameE_eq {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν q : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν q)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2) (x : ℝ × ℝ) :
    ladTransport tr q (physFrameE κ ν q j) x =
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        Jscale (clockA ν q)
          (fun y => ((movingTrainV tr q y 0 : ℝ) : ℂ) * pdCx 0 (perE κ (dd ν q) j) y +
            ((movingTrainV tr q y 1 : ℝ) : ℂ) * pdCx 1 (perE κ (dd ν q) j) y) x := by
  have hd : 0 < dd ν q := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha)
  have hsq : 0 < Real.sqrt (clockA ν q) := Real.sqrt_pos.2 ha
  unfold ladTransport Jscale movingTrainV
  dsimp only
  rw [pdCx_physFrameE_eq hκ hν ha j 0 x, pdCx_physFrameE_eq hκ hν ha j 1 x,
    EulerErrorTail.pdCx_perE_eq hκ hd j 0, EulerErrorTail.pdCx_perE_eq hκ hd j 1]
  have hx1 : Real.sqrt (clockA ν q) * (x.1 / Real.sqrt (clockA ν q)) = x.1 :=
    mul_div_cancel₀ x.1 hsq.ne'
  have hx2 : Real.sqrt (clockA ν q) * (x.2 / Real.sqrt (clockA ν q)) = x.2 :=
    mul_div_cancel₀ x.2 hsq.ne'
  rw [hx1, hx2]
  have hexp : (clockA ν q)⁻¹ ^ 3 * Real.sqrt (clockA ν q) =
      (clockA ν q) ^ (-2 : ℝ) * (clockA ν q) ^ (-2 : ℝ) * (clockA ν q) ^ (3 / 2 : ℝ) := by
    have h32 : (clockA ν q) ^ (3 / 2 : ℝ) = clockA ν q * Real.sqrt (clockA ν q) := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by ring, Real.rpow_add ha, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [h32, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    field_simp [ha.ne']
  have hexpC : (((clockA ν q)⁻¹ ^ 3 * Real.sqrt (clockA ν q) : ℝ) : ℂ) =
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * (((clockA ν q) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    have := congrArg Complex.ofReal hexp
    simpa only [Complex.ofReal_mul] using this
  rw [hexpC, Prod.mk.eta]
  push_cast
  ring

/-- Moving-frame residual cancellation:
`interactionTerm E_j - (movOscRes_j + movEulerRes_j + λ_j E_j) = -movOscRes_j + V·∇E_j`. -/
theorem moving_frame_residual_eq (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (q : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    interactionTerm tr q (perE κ (dd ν q) j) y -
        (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
          modeEigen P j * perE κ (dd ν q) j y) =
      -movOscRes κ ν q j y +
        (((movingTrainV tr q y 0 : ℝ) : ℂ) * pdCx 0 (perE κ (dd ν q) j) y +
          ((movingTrainV tr q y 1 : ℝ) : ℂ) * pdCx 1 (perE κ (dd ν q) j) y) := by
  unfold interactionTerm movEulerRes movL dd
  ring

/-- Full PDE rate identity: `physFrameERate` is `a(q)⁻² J_{a(q)}` of the moving mode residual. -/
theorem physFrameERate_eq_jscale {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν q : ℝ} (hν : 0 < ν) (hq : 0 ≤ q)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2) (x : ℝ × ℝ) :
    physFrameERate κ tr q j x =
      (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) *
        Jscale (clockA ν q)
          (fun y => interactionTerm tr q (perE κ (dd ν q) j) y -
            (movOscRes κ ν q j y + movEulerRes κ P tr q j y +
              modeEigen P j * perE κ (dd ν q) j y)) x := by
  have ha : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hq)
  unfold physFrameERate
  rw [heat_part_physFrameE_eq hκ hν hq j x, transport_part_physFrameE_eq hκ hν ha tr j x]
  simp only [moving_frame_residual_eq κ P tr q j]
  unfold Jscale
  ring

/-! ## 3. Moving-to-physical cell pairing and uniform `X_{m,c}` bounds -/

/-- `J_a⁻¹ (J_a W) = W` for `a > 0`. -/
theorem jscaleInv_jscale {a : ℝ} (ha : 0 < a) (W : ℝ × ℝ → ℂ) :
    JscaleInv a (Jscale a W) = W := by
  funext y
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have h1 : a ^ 2 * a ^ (-2 : ℝ) = 1 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero 2 ha.ne')
  unfold JscaleInv Jscale
  rw [mul_div_cancel_left₀ y.1 hs, mul_div_cancel_left₀ y.2 hs, ← mul_assoc,
    ← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

/-- `physAdj (clockA ν q) (movingPhi ν φ q) = φ q` for `0 < clockA ν q`. -/
theorem physAdj_movingPhi {ν q : ℝ} (ha : 0 < clockA ν q) (φ : ℝ → ℝ × ℝ → ℂ) :
    physAdj (clockA ν q) (movingPhi ν φ q) = φ q := by
  funext x
  have hs : Real.sqrt (clockA ν q) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  unfold physAdj movingPhi
  rw [mul_div_cancel₀ x.1 hs, mul_div_cancel₀ x.2 hs, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]

/-- Cell pairing change of variables between `dd ν q` and `ν ^ (-2 : ℝ)`. -/
theorem cell_pair_jscale_movingPhi {ν q : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν q)
    (W : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) :
    ∫ y in B0579.cell (dd ν q), W y * movingPhi ν φ q y =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), Jscale (clockA ν q) W x * φ q x := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hcov := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν q) hc ha (Jscale (clockA ν q) W)
    (movingPhi ν φ q)
  simpa only [dd, jscaleInv_jscale ha W, physAdj_movingPhi ha φ] using hcov

/-- Rescaled periodized Gaussian-decaying kernel is uniformly bounded in `X_{m,c}`. -/
lemma xNorm_jscale_perSum_of_gauss {m : ℝ} (hm : 0 ≤ m) {g : ℝ × ℝ → ℂ} (hg_cont : Continuous g)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hg : ∀ y : ℝ × ℝ, ‖g y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {a d : ℝ}, 1 ≤ a → 1 ≤ d →
      MemLp (Jscale a (perSum d g)) 2 (B0579.cellMeasure (d * Real.sqrt a) m) ∧
        xNorm (d * Real.sqrt a) m (Jscale a (perSum d g)) ≤
          ENNReal.ofReal (a ^ ((m - 3) / 2) * B) := by
  obtain ⟨M, hM0, hM⟩ := OscillatorForceSub.perSum_pointwise_of_gauss hC0 hg
  obtain ⟨K_m, hKm0, hKm⟩ := xNorm_le_of_gauss hm
  refine ⟨M * K_m, mul_nonneg hM0 hKm0, fun {a d} ha1 hd1 => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hper_cont : Continuous (perSum d g) :=
    FrameCont.perSum_continuous hg_cont
      (fun z => (hg z).trans (by
        have htw := FrameCont.exp_le_translate_weight z.1 z.2
        calc C * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
            ≤ C * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left htw hC0
          _ = (16 * C) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hd0.ne'
  have hJ_cont : Continuous (Jscale a (perSum d g)) := by
    unfold Jscale
    exact continuous_const.mul (hper_cont.comp
      ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  have hxd : xNorm d m (perSum d g) ≤ ENNReal.ofReal (M * K_m) :=
    hKm d M (perSum d g) hM0 (hM d hd1)
  have hsc := scalingJa m hm a d ha1 hd0 (perSum d g) hper_cont.measurable
  have hbound : xNorm (d * Real.sqrt a) m (Jscale a (perSum d g)) ≤
      ENNReal.ofReal (a ^ ((m - 3) / 2) * (M * K_m)) := by
    calc xNorm (d * Real.sqrt a) m (Jscale a (perSum d g))
        ≤ ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m (perSum d g) := hsc
      _ ≤ ENNReal.ofReal (a ^ ((m - 3) / 2)) * ENNReal.ofReal (M * K_m) :=
          mul_le_mul_of_nonneg_left hxd zero_le
      _ = ENNReal.ofReal (a ^ ((m - 3) / 2) * (M * K_m)) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _)).symm
  exact ⟨⟨hJ_cont.aestronglyMeasurable, lt_of_le_of_lt hbound ENNReal.ofReal_lt_top⟩, hbound⟩

private lemma memLp_and_xNorm_add3 {c m : ℝ} {f g h : ℝ × ℝ → ℂ} {Bf Bg Bh : ℝ}
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hBh : 0 ≤ Bh)
    (hf : MemLp f 2 (B0579.cellMeasure c m)) (hnf : xNorm c m f ≤ ENNReal.ofReal Bf)
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hng : xNorm c m g ≤ ENNReal.ofReal Bg)
    (hh : MemLp h 2 (B0579.cellMeasure c m)) (hnh : xNorm c m h ≤ ENNReal.ofReal Bh) :
    MemLp ((f + g) + h) 2 (B0579.cellMeasure c m) ∧
      xNorm c m ((f + g) + h) ≤ ENNReal.ofReal (Bf + Bg + Bh) := by
  refine ⟨(hf.add hg).add hh, ?_⟩
  unfold xNorm at hnf hng hnh ⊢
  calc eLpNorm ((f + g) + h) 2 (B0579.cellMeasure c m)
      ≤ eLpNorm (f + g) 2 (B0579.cellMeasure c m) +
          eLpNorm h 2 (B0579.cellMeasure c m) :=
        eLpNorm_add_le (hf.add hg).1 hh.1 one_le_two
    _ ≤ (eLpNorm f 2 (B0579.cellMeasure c m) +
          eLpNorm g 2 (B0579.cellMeasure c m)) +
          eLpNorm h 2 (B0579.cellMeasure c m) :=
        add_le_add (eLpNorm_add_le (p := 2) hf.1 hg.1 one_le_two) le_rfl
    _ ≤ (ENNReal.ofReal Bf + ENNReal.ofReal Bg) + ENNReal.ofReal Bh :=
        add_le_add (add_le_add hnf hng) hnh
    _ = ENNReal.ofReal (Bf + Bg + Bh) := by
        rw [← ENNReal.ofReal_add hBf hBg, ← ENNReal.ofReal_add (add_nonneg hBf hBg) hBh]

set_option maxHeartbeats 800000 in
/-- Uniform `X_{m, ν⁻²}` bounds on `Icc 0 s` for `physFrameE`, `pdCx k physFrameE`, and
`physFrameERate` when `ν ∈ Ioc 0 1` and `1 ≤ b ≤ clockTheta ν s`. -/
theorem physFrameE_uniform_xNorm {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {m b ν s C_tr : ℝ} (hm : 8 < m) (hb : 1 ≤ b) (hν : ν ∈ Ioc 0 1) (hs : 0 ≤ s)
    (hbs : b ≤ clockTheta ν s)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} (hBdd : LadTrainBdd tr m s C_tr) :
    ∃ M_col : ℝ, 0 ≤ M_col ∧ ∀ q ∈ Icc (0 : ℝ) s, ∀ j : Fin 2,
      (MemLp (physFrameE κ ν q j) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
        xNorm (ν ^ (-2 : ℝ)) m (physFrameE κ ν q j) ≤ ENNReal.ofReal M_col) ∧
      (∀ k : Fin 2,
        MemLp (pdCx k (physFrameE κ ν q j)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
          xNorm (ν ^ (-2 : ℝ)) m (pdCx k (physFrameE κ ν q j)) ≤ ENNReal.ofReal M_col) ∧
      (MemLp (physFrameERate κ tr q j) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
        xNorm (ν ^ (-2 : ℝ)) m (physFrameERate κ tr q j) ≤ ENNReal.ofReal M_col) := by
  have hm0 : 0 ≤ m := by linarith
  have hm3 : 0 ≤ (m - 3) / 2 := by linarith
  have hsm_e := (OscillatorForceSub.seed_e_smooth_decay hκ).1
  obtain ⟨C_e, hCe0, hseed⟩ := EulerErrorTail.seed_bounds hκ
  -- Per-mode Gaussian bounds
  have he_b : ∀ j : Fin 2, ∃ B : ℝ, 0 ≤ B ∧ ∀ {a d : ℝ}, 1 ≤ a → 1 ≤ d →
      MemLp (Jscale a (perSum d (κ.e j))) 2 (B0579.cellMeasure (d * Real.sqrt a) m) ∧
        xNorm (d * Real.sqrt a) m (Jscale a (perSum d (κ.e j))) ≤
          ENNReal.ofReal (a ^ ((m - 3) / 2) * B) :=
    fun j => xNorm_jscale_perSum_of_gauss hm0 (hsm_e j).continuous hCe0
      (fun y => (hseed j y).1)
  have hpd_b : ∀ (j k : Fin 2), ∃ B : ℝ, 0 ≤ B ∧ ∀ {a d : ℝ}, 1 ≤ a → 1 ≤ d →
      MemLp (Jscale a (perSum d (pdCx k (κ.e j)))) 2 (B0579.cellMeasure (d * Real.sqrt a) m) ∧
        xNorm (d * Real.sqrt a) m (Jscale a (perSum d (pdCx k (κ.e j)))) ≤
          ENNReal.ofReal (a ^ ((m - 3) / 2) * B) :=
    fun j k => xNorm_jscale_perSum_of_gauss hm0
      (RateSplitAux.contDiff_pdCx (hsm_e j) k).continuous hCe0 (fun y => (hseed j y).2 k)
  have hD_b : ∀ j : Fin 2, ∃ B : ℝ, 0 ≤ B ∧ ∀ {a d : ℝ}, 1 ≤ a → 1 ≤ d →
      MemLp (Jscale a (perSum d (movD (κ.e j)))) 2 (B0579.cellMeasure (d * Real.sqrt a) m) ∧
        xNorm (d * Real.sqrt a) m (Jscale a (perSum d (movD (κ.e j)))) ≤
          ENNReal.ofReal (a ^ ((m - 3) / 2) * B) := fun j => by
    obtain ⟨hcontD, C_D, hCD0, hCD⟩ := OscillatorForceSub.movD_seed_decay hκ j
    exact xNorm_jscale_perSum_of_gauss hm0 hcontD hCD0 hCD
  choose Be hBe0 hBe using he_b
  choose Bpd hBpd0 hBpd using fun p : Fin 2 × Fin 2 => hpd_b p.1 p.2
  choose BD hBD0 hBD using hD_b
  set B₀ : ℝ := Be 0 + Be 1 + Bpd (0, 0) + Bpd (0, 1) + Bpd (1, 0) + Bpd (1, 1) + BD 0 + BD 1
  have hB₀ : 0 ≤ B₀ := by
    have := hBe0 0; have := hBe0 1
    have := hBpd0 (0, 0); have := hBpd0 (0, 1); have := hBpd0 (1, 0); have := hBpd0 (1, 1)
    have := hBD0 0; have := hBD0 1
    linarith
  set A_s : ℝ := (clockA ν s) ^ ((m - 3) / 2)
  have hAs0 : 0 ≤ A_s := Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one (one_le_clockA hν.1.le hs)).le _
  set M_base : ℝ := A_s * B₀
  set c_tr : ℝ := |C_tr|
  have hc_tr0 : 0 ≤ c_tr := abs_nonneg C_tr
  set M_col : ℝ := M_base + c_tr * M_base + c_tr * M_base
  refine ⟨M_col, by positivity, fun q hq j => ?_⟩
  have ha1 : 1 ≤ clockA ν q := one_le_clockA hν.1.le hq.1
  have ha0 : 0 < clockA ν q := lt_of_lt_of_le zero_lt_one ha1
  have has : clockA ν q ≤ clockA ν s := by
    unfold clockA; nlinarith [hν.1, hq.2]
  have hA_le : (clockA ν q) ^ ((m - 3) / 2) ≤ A_s :=
    Real.rpow_le_rpow ha0.le has hm3
  have hθ_le : clockTheta ν s ≤ clockTheta ν q := by
    unfold clockTheta
    exact inv_anti₀ (mul_pos hν.1 ha0) (mul_le_mul_of_nonneg_left has hν.1.le)
  have hθ1 : 1 ≤ clockTheta ν q := hb.trans (hbs.trans hθ_le)
  have hd1 : 1 ≤ dd ν q :=
    ComplCouplingSub.one_le_cellLen_of_theta hν.1 hν.2 hq.1 hθ1
  have hdc : dd ν q * Real.sqrt (clockA ν q) = ν ^ (-2 : ℝ) :=
    div_mul_cancel₀ _ (Real.sqrt_pos.2 ha0).ne'
  have hMbase0 : 0 ≤ M_base := mul_nonneg hAs0 hB₀
  have hMcol_ge : M_base ≤ M_col := by
    have : 0 ≤ c_tr * M_base := mul_nonneg hc_tr0 hMbase0
    linarith
  -- 1. `physFrameE`
  have hE_eq : physFrameE κ ν q j = Jscale (clockA ν q) (perSum (dd ν q) (κ.e j)) :=
    funext (physFrameE_eq_jscale_perE κ ha0 j)
  have hBe_j : Be j ≤ B₀ := by
    fin_cases j
    · change Be 0 ≤ B₀
      linarith [hBe0 1, hBpd0 (0, 0), hBpd0 (0, 1), hBpd0 (1, 0), hBpd0 (1, 1), hBD0 0, hBD0 1]
    · change Be 1 ≤ B₀
      linarith [hBe0 0, hBpd0 (0, 0), hBpd0 (0, 1), hBpd0 (1, 0), hBpd0 (1, 1), hBD0 0, hBD0 1]
  have hE_mem_norm : MemLp (physFrameE κ ν q j) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      xNorm (ν ^ (-2 : ℝ)) m (physFrameE κ ν q j) ≤ ENNReal.ofReal M_base := by
    obtain ⟨hm_e, hn_e⟩ := hBe j ha1 hd1
    rw [hdc, ← hE_eq] at hm_e hn_e
    refine ⟨hm_e, hn_e.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul hA_le hBe_j (hBe0 j) hAs0
  -- 2. `pdCx k (physFrameE)`
  have hpd_mem_norm : ∀ k : Fin 2,
      MemLp (pdCx k (physFrameE κ ν q j)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
        xNorm (ν ^ (-2 : ℝ)) m (pdCx k (physFrameE κ ν q j)) ≤ ENNReal.ofReal M_base := by
    intro k
    obtain ⟨hm_p, hn_p⟩ := hBpd (j, k) ha1 hd1
    rw [hdc] at hm_p hn_p
    have hBpd_jk : Bpd (j, k) ≤ B₀ := by
      fin_cases j <;> fin_cases k
      · change Bpd (0, 0) ≤ B₀
        linarith [hBe0 0, hBe0 1, hBpd0 (0, 1), hBpd0 (1, 0), hBpd0 (1, 1), hBD0 0, hBD0 1]
      · change Bpd (0, 1) ≤ B₀
        linarith [hBe0 0, hBe0 1, hBpd0 (0, 0), hBpd0 (1, 0), hBpd0 (1, 1), hBD0 0, hBD0 1]
      · change Bpd (1, 0) ≤ B₀
        linarith [hBe0 0, hBe0 1, hBpd0 (0, 0), hBpd0 (0, 1), hBpd0 (1, 1), hBD0 0, hBD0 1]
      · change Bpd (1, 1) ≤ B₀
        linarith [hBe0 0, hBe0 1, hBpd0 (0, 0), hBpd0 (0, 1), hBpd0 (1, 0), hBD0 0, hBD0 1]
    have hsq1 : 1 ≤ Real.sqrt (clockA ν q) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt ha1
    have hfac_le : |(clockA ν q)⁻¹ ^ 3 * Real.sqrt (clockA ν q)| ≤ (clockA ν q) ^ (-2 : ℝ) := by
      have hpos : 0 < (clockA ν q)⁻¹ ^ 3 * Real.sqrt (clockA ν q) := by positivity
      rw [abs_of_pos hpos, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha0.le,
        Real.rpow_natCast]
      have hsq2 : Real.sqrt (clockA ν q) * Real.sqrt (clockA ν q) = clockA ν q :=
        Real.mul_self_sqrt ha0.le
      have hle1 : (clockA ν q)⁻¹ * Real.sqrt (clockA ν q) ≤ 1 := by
        rw [inv_mul_le_iff₀ ha0, mul_one]
        nlinarith [hsq1, hsq2]
      calc (clockA ν q)⁻¹ ^ 3 * Real.sqrt (clockA ν q)
          = ((clockA ν q) ^ 2)⁻¹ * ((clockA ν q)⁻¹ * Real.sqrt (clockA ν q)) := by
            field_simp [ha0.ne']
        _ ≤ ((clockA ν q) ^ 2)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = ((clockA ν q) ^ 2)⁻¹ := mul_one _
    have hpt_le : ∀ x : ℝ × ℝ, ‖pdCx k (physFrameE κ ν q j) x‖ ≤
        ‖Jscale (clockA ν q) (perSum (dd ν q) (pdCx k (κ.e j))) x‖ := by
      intro x
      rw [pdCx_physFrameE_eq hκ hν.1 ha0 j k x]
      unfold Jscale
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _)]
      exact mul_le_mul_of_nonneg_right hfac_le (norm_nonneg _)
    have hcont_pd : Continuous (pdCx k (physFrameE κ ν q j)) :=
      (RateSplitAux.contDiff_pdCx (contDiff_physFrameE_slice hκ hν.1 ha0 j) k).continuous
    have hm_pd : MemLp (pdCx k (physFrameE κ ν q j)) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
      hm_p.mono hcont_pd.aestronglyMeasurable (Eventually.of_forall hpt_le)
    have hn_pd : xNorm (ν ^ (-2 : ℝ)) m (pdCx k (physFrameE κ ν q j)) ≤ ENNReal.ofReal M_base := by
      refine (eLpNorm_mono hpt_le).trans (hn_p.trans (ENNReal.ofReal_le_ofReal ?_))
      exact mul_le_mul hA_le hBpd_jk (hBpd0 (j, k)) hAs0
    exact ⟨hm_pd, hn_pd⟩
  -- 3. `physFrameERate`
  have hRate_mem_norm : MemLp (physFrameERate κ tr q j) 2
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      xNorm (ν ^ (-2 : ℝ)) m (physFrameERate κ tr q j) ≤ ENNReal.ofReal M_col := by
    obtain ⟨hm_D, hn_D⟩ := hBD j ha1 hd1
    rw [hdc] at hm_D hn_D
    have hBD_j : BD j ≤ B₀ := by
      fin_cases j
      · change BD 0 ≤ B₀
        linarith [hBe0 0, hBe0 1, hBpd0 (0, 0), hBpd0 (0, 1), hBpd0 (1, 0), hBpd0 (1, 1), hBD0 1]
      · change BD 1 ≤ B₀
        linarith [hBe0 0, hBe0 1, hBpd0 (0, 0), hBpd0 (0, 1), hBpd0 (1, 0), hBpd0 (1, 1), hBD0 0]
    set heatPart : ℝ × ℝ → ℂ := fun x =>
      ladDt (fun q' x' => physFrameE κ ν q' j x') q x -
        (ν : ℂ) * ladLapCx (physFrameE κ ν q j) x
    have hEq : heatPart = fun x =>
        -((((clockA ν q) ^ (-2 : ℝ) * (clockTheta ν q)⁻¹ : ℝ) : ℂ) *
          Jscale (clockA ν q) (perSum (dd ν q) (movD (κ.e j))) x) := by
      funext x
      change ladDt _ q x - _ = _
      rw [heat_part_physFrameE_eq hκ hν.1 hq.1 j x]
      unfold Jscale dd
      rw [OscillatorForceSub.movOscRes_eq_perSum_movD hκ hν.1 hq.1 j]
      push_cast; ring
    have hheat_le : ∀ x : ℝ × ℝ,
        ‖heatPart x‖ ≤ ‖Jscale (clockA ν q) (perSum (dd ν q) (movD (κ.e j))) x‖ := by
      intro x
      rw [congrFun hEq x, norm_neg, norm_mul, Complex.norm_of_nonneg (mul_nonneg
        (Real.rpow_nonneg ha0.le _) (inv_nonneg.2 (lt_of_lt_of_le zero_lt_one hθ1).le))]
      have ha_le1 : (clockA ν q) ^ (-2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
      have hθ_le1 : (clockTheta ν q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ1
      have h1 : (clockA ν q) ^ (-2 : ℝ) * (clockTheta ν q)⁻¹ ≤ 1 := by
        nlinarith [Real.rpow_nonneg ha0.le (-2 : ℝ), inv_nonneg.2 (lt_of_lt_of_le zero_lt_one hθ1).le]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    have hcont_heat : Continuous heatPart := by
      rw [hEq]
      obtain ⟨hcontD, C_D, hCD0, hCD⟩ := OscillatorForceSub.movD_seed_decay hκ j
      have hd0 : 0 < dd ν q := lt_of_lt_of_le zero_lt_one hd1
      have hperD : Continuous (perSum (dd ν q) (movD (κ.e j))) :=
        FrameCont.perSum_continuous hcontD
          (fun z => (hCD z).trans (by
            have htw := FrameCont.exp_le_translate_weight z.1 z.2
            calc C_D * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
                ≤ C_D * (16 * (1 + |z.1|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left htw hCD0
              _ = (16 * C_D) * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring)) hd0.ne'
      unfold Jscale
      exact (continuous_const.mul (continuous_const.mul (hperD.comp
        ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _))))).neg
    have hm_heat : MemLp heatPart 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
      hm_D.mono hcont_heat.aestronglyMeasurable (Eventually.of_forall hheat_le)
    have hn_heat : xNorm (ν ^ (-2 : ℝ)) m heatPart ≤ ENNReal.ofReal M_base := by
      refine (eLpNorm_mono hheat_le).trans (hn_D.trans (ENNReal.ofReal_le_ofReal ?_))
      exact mul_le_mul hA_le hBD_j (hBD0 j) hAs0
    -- Bound each transport coordinate `(tr.v q x k) * pdCx k (physFrameE)` on `cellMeasure`
    have htr_k : ∀ k : Fin 2,
        MemLp (fun x => ((tr.v q x k : ℝ) : ℂ) * pdCx k (physFrameE κ ν q j) x) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
        xNorm (ν ^ (-2 : ℝ)) m
            (fun x => ((tr.v q x k : ℝ) : ℂ) * pdCx k (physFrameE κ ν q j) x) ≤
          ENNReal.ofReal (c_tr * M_base) := by
      intro k
      have hv_cont : Continuous (fun x : ℝ × ℝ => tr.v q x k) := by
        have hvS : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ici 0 ×ˢ univ) :=
          tr.isTrain.smooth_v.continuousOn
        have hslice : ContinuousOn (fun x : ℝ × ℝ => tr.v q x) univ :=
          hvS.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun _ _ => ⟨hq.1, mem_univ _⟩)
        exact ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous).comp
          (continuousOn_univ.1 hslice)
      set fk : ℝ × ℝ → ℂ := fun x => ((tr.v q x k : ℝ) : ℂ) * pdCx k (physFrameE κ ν q j) x
      set gk : ℝ × ℝ → ℂ := (c_tr : ℂ) • pdCx k (physFrameE κ ν q j)
      have hcont_k : Continuous fk :=
        (Complex.continuous_ofReal.comp hv_cont).mul
          (RateSplitAux.contDiff_pdCx (contDiff_physFrameE_slice hκ hν.1 ha0 j) k).continuous
      have hcell_ae : ∀ᵐ x ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m),
          x ∈ B0579.cell (ν ^ (-2 : ℝ)) :=
        (B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) m).ae_le
          (ae_restrict_mem (B0579.measurableSet_cell _))
      have hae_k : ∀ᵐ x ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m), ‖fk x‖ ≤ ‖gk x‖ := by
        filter_upwards [hcell_ae] with x hx
        simp only [fk, gk, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_of_nonneg hc_tr0]
        exact mul_le_mul_of_nonneg_right
          (((hBdd q hq x hx).1 k).trans (le_abs_self C_tr)) (norm_nonneg _)
      have hc_mem : MemLp gk 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
        (hpd_mem_norm k).1.const_smul (c_tr : ℂ)
      have hm_k := hc_mem.mono hcont_k.aestronglyMeasurable hae_k
      have hn_k : xNorm (ν ^ (-2 : ℝ)) m fk ≤ ENNReal.ofReal (c_tr * M_base) := by
        unfold xNorm
        calc eLpNorm fk 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m)
            ≤ eLpNorm gk 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := eLpNorm_mono_ae hae_k
          _ ≤ ‖(c_tr : ℂ)‖ₑ * xNorm (ν ^ (-2 : ℝ)) m (pdCx k (physFrameE κ ν q j)) :=
              eLpNorm_const_smul_le
          _ ≤ ENNReal.ofReal c_tr * ENNReal.ofReal M_base := by
              rw [T06.enorm_ofReal_cast hc_tr0]
              exact mul_le_mul_of_nonneg_left (hpd_mem_norm k).2 zero_le
          _ = ENNReal.ofReal (c_tr * M_base) :=
              (ENNReal.ofReal_mul hc_tr0).symm
      exact ⟨hm_k, hn_k⟩
    have hm0_tr := htr_k 0
    have hm1_tr := htr_k 1
    have hRate_eq : physFrameERate κ tr q j =
        (heatPart + fun x => ((tr.v q x 0 : ℝ) : ℂ) * pdCx 0 (physFrameE κ ν q j) x) +
          fun x => ((tr.v q x 1 : ℝ) : ℂ) * pdCx 1 (physFrameE κ ν q j) x := by
      funext x; unfold physFrameERate heatPart ladTransport; simp [Pi.add_apply]; ring
    rw [hRate_eq]
    exact memLp_and_xNorm_add3 hMbase0 (mul_nonneg hc_tr0 hMbase0) (mul_nonneg hc_tr0 hMbase0)
      hm_heat hn_heat hm0_tr.1 hm0_tr.2 hm1_tr.1 hm1_tr.2
  exact ⟨⟨hE_mem_norm.1, hE_mem_norm.2.trans (ENNReal.ofReal_le_ofReal hMcol_ge)⟩,
    fun k => ⟨(hpd_mem_norm k).1, (hpd_mem_norm k).2.trans (ENNReal.ofReal_le_ofReal hMcol_ge)⟩,
    hRate_mem_norm⟩

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.FramePairing1Aux
