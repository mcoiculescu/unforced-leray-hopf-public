import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.SepPsiOscFar.IterOscBound

/-!
# Sub-leaf 5 (`SepPsiOscFar`, task `PartIII-b:C/rep/8/1/1/2/5/1/1/4`)

Source `the November 2 reference manuscript`
lines 4178-4215, 5400-5432.

Proves `YBPhase.sepPsiOscFar : YBPhase.SepPsiOscFar`: on the transition annulus
`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`, the outward stream primitive commutator difference
`fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) (ε⁻¹ • xo) - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) (ε⁻¹ • xo)`
for `Z₁ = srcX0 ν μ (thinSource ε F)` and
`Z₂ = srcX0 ν μ (thinSource ε (meanLift (phaseMean c F)))` has a measurable `(2 * ε * c)`-periodic
phase majorant `B` with
`ltauAt (2 * ε * c) B ≤ ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * |xo'| ^ (-5)) * thinMoment c F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open UnforcedLeray.Short.IIIa
open YBComm PhasePrim FarLeafOrg GeomXAsm GeomXAsm.RayFTCAux GeomXAsm.RayPrimAux
open SepPsiOscFarAux

/-- Outward ray integral bound from a pointwise `ρ ^ (-4 - j)` bound on `Ioi r`. -/
private theorem rayInt_le_of_hpt_le {r₁ B : ℝ} {W : ℝ → Space → Space}
    (hW : ValidPsiFieldWith r₁ B W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ)
    {j : ℕ} (hj : j ≤ 3) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ ρ, r ≤ ρ → ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖ ≤ K * ρ ^ (-4 - (j : ℝ))) :
    rayInt (W 0) j r z ≤ K * r ^ (-2 - (j : ℝ)) := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hint_lhs : IntegrableOn (fun ρ : ℝ => ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) (Ioi r) :=
    integrableOn_ray_iteratedFDeriv hW hr₁ hr z hj
  have hlt1 : -3 - (j : ℝ) < -1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hint_rhs : IntegrableOn (fun ρ : ℝ => K * ρ ^ (-3 - (j : ℝ))) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt hlt1 hr0).const_mul K
  have hae : (fun ρ : ℝ => ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) ≤ᵐ[volume.restrict (Ioi r)]
      fun ρ : ℝ => K * ρ ^ (-3 - (j : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    calc ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖
        ≤ ρ * (K * ρ ^ (-4 - (j : ℝ))) :=
          mul_le_mul_of_nonneg_left (hbd ρ (le_of_lt hρ)) hρ0.le
      _ = K * (ρ ^ (1 : ℝ) * ρ ^ (-4 - (j : ℝ))) := by rw [Real.rpow_one]; ring
      _ = K * ρ ^ (-3 - (j : ℝ)) := by
          rw [← Real.rpow_add hρ0]
          congr 2; ring
  have h1 : rayInt (W 0) j r z ≤ ∫ ρ in Ioi r, K * ρ ^ (-3 - (j : ℝ)) :=
    integral_mono_ae hint_lhs hint_rhs hae
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt1 hr0] at h1
  have hexp : -3 - (j : ℝ) + 1 = -2 - (j : ℝ) := by ring
  rw [hexp] at h1
  have hdiv_le : -r ^ (-2 - (j : ℝ)) / (-2 - (j : ℝ)) ≤ r ^ (-2 - (j : ℝ)) := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hd : 0 < 2 + (j : ℝ) := by linarith
    have h_eq : -r ^ (-2 - (j : ℝ)) / (-2 - (j : ℝ)) = r ^ (-2 - (j : ℝ)) / (2 + (j : ℝ)) := by
      have : -2 - (j : ℝ) = -(2 + (j : ℝ)) := by ring
      rw [this, neg_div_neg_eq]
    rw [h_eq, div_le_iff₀ hd]
    have hrp : 0 ≤ r ^ (-2 - (j : ℝ)) := Real.rpow_nonneg hr0.le _
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left hdiv_le hK)

/-- Combined transition-annulus oscillation bound for the 7-term `ptNorm`/`rayInt` sum. -/
private theorem sum7_le {s r_y K M : ℝ} {ΔZ : Space → Space} {z_y : ℝ}
    (hs0 : 0 < s) (hr0 : 0 < r_y) (hK0 : 0 ≤ K) (hM1 : 1 ≤ M)
    (hs_le : s ≤ 2 * r_y ^ (-1 : ℝ)) (hsr_le : s * r_y⁻¹ ≤ M)
    (hP0 : ptNorm ΔZ 0 r_y z_y ≤ K * r_y ^ (-4 : ℝ))
    (hP1 : ptNorm ΔZ 1 r_y z_y ≤ K * r_y ^ (-5 : ℝ))
    (hP2 : ptNorm ΔZ 2 r_y z_y ≤ K * r_y ^ (-6 : ℝ))
    (hI0 : rayInt ΔZ 0 r_y z_y ≤ K * r_y ^ (-2 : ℝ))
    (hI1 : rayInt ΔZ 1 r_y z_y ≤ K * r_y ^ (-3 : ℝ))
    (hI2 : rayInt ΔZ 2 r_y z_y ≤ K * r_y ^ (-4 : ℝ))
    (hI3 : rayInt ΔZ 3 r_y z_y ≤ K * r_y ^ (-5 : ℝ)) :
    s * ptNorm ΔZ 0 r_y z_y +
      ptNorm ΔZ 1 r_y z_y +
      s * ptNorm ΔZ 2 r_y z_y +
      s ^ 3 * rayInt ΔZ 0 r_y z_y +
      s ^ 2 * rayInt ΔZ 1 r_y z_y +
      s * rayInt ΔZ 2 r_y z_y +
      rayInt ΔZ 3 r_y z_y ≤
      19 * K * M * r_y ^ (-5 : ℝ) := by
  have hrp_nn : ∀ a : ℝ, 0 ≤ r_y ^ a := fun a => Real.rpow_nonneg hr0.le a
  -- Term 1: s * ptNorm 0 ≤ 2 * K * M * r_y ^ (-5)
  have ht1 : s * ptNorm ΔZ 0 r_y z_y ≤ 2 * K * M * r_y ^ (-5 : ℝ) := by
    have hp : r_y ^ (-1 : ℝ) * r_y ^ (-4 : ℝ) = r_y ^ (-5 : ℝ) := by
      rw [← Real.rpow_add hr0]; norm_num
    calc s * ptNorm ΔZ 0 r_y z_y
        ≤ s * (K * r_y ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left hP0 hs0.le
      _ ≤ (2 * r_y ^ (-1 : ℝ)) * (K * r_y ^ (-4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hs_le (mul_nonneg hK0 (hrp_nn _))
      _ = 2 * K * 1 * (r_y ^ (-1 : ℝ) * r_y ^ (-4 : ℝ)) := by ring
      _ ≤ 2 * K * M * r_y ^ (-5 : ℝ) := by rw [hp]; gcongr
  -- Term 2: ptNorm 1 ≤ K * M * r_y ^ (-5)
  have ht2 : ptNorm ΔZ 1 r_y z_y ≤ K * M * r_y ^ (-5 : ℝ) := by
    calc ptNorm ΔZ 1 r_y z_y ≤ K * 1 * r_y ^ (-5 : ℝ) := by rw [mul_one]; exact hP1
      _ ≤ K * M * r_y ^ (-5 : ℝ) := by gcongr
  -- Term 3: s * ptNorm 2 ≤ K * M * r_y ^ (-5)
  have ht3 : s * ptNorm ΔZ 2 r_y z_y ≤ K * M * r_y ^ (-5 : ℝ) := by
    have hp : r_y ^ (-6 : ℝ) = r_y⁻¹ * r_y ^ (-5 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hr0]; norm_num
    calc s * ptNorm ΔZ 2 r_y z_y
        ≤ s * (K * r_y ^ (-6 : ℝ)) := mul_le_mul_of_nonneg_left hP2 hs0.le
      _ = K * (s * r_y⁻¹) * r_y ^ (-5 : ℝ) := by rw [hp]; ring
      _ ≤ K * M * r_y ^ (-5 : ℝ) := by gcongr
  -- Term 4: s ^ 3 * rayInt 0 ≤ 8 * K * M * r_y ^ (-5)
  have ht4 : s ^ 3 * rayInt ΔZ 0 r_y z_y ≤ 8 * K * M * r_y ^ (-5 : ℝ) := by
    have hs3 : s ^ 3 ≤ (2 * r_y ^ (-1 : ℝ)) ^ 3 := pow_le_pow_left₀ hs0.le hs_le 3
    have hp : (r_y ^ (-1 : ℝ)) ^ 3 * r_y ^ (-2 : ℝ) = r_y ^ (-5 : ℝ) := by
      rw [← Real.rpow_natCast (r_y ^ (-1 : ℝ)) 3, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      norm_num
    calc s ^ 3 * rayInt ΔZ 0 r_y z_y
        ≤ s ^ 3 * (K * r_y ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left hI0 (by positivity)
      _ ≤ (2 * r_y ^ (-1 : ℝ)) ^ 3 * (K * r_y ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hs3 (mul_nonneg hK0 (hrp_nn _))
      _ = 8 * K * 1 * ((r_y ^ (-1 : ℝ)) ^ 3 * r_y ^ (-2 : ℝ)) := by ring
      _ ≤ 8 * K * M * r_y ^ (-5 : ℝ) := by rw [hp]; gcongr
  -- Term 5: s ^ 2 * rayInt 1 ≤ 4 * K * M * r_y ^ (-5)
  have ht5 : s ^ 2 * rayInt ΔZ 1 r_y z_y ≤ 4 * K * M * r_y ^ (-5 : ℝ) := by
    have hs2 : s ^ 2 ≤ (2 * r_y ^ (-1 : ℝ)) ^ 2 := pow_le_pow_left₀ hs0.le hs_le 2
    have hp : (r_y ^ (-1 : ℝ)) ^ 2 * r_y ^ (-3 : ℝ) = r_y ^ (-5 : ℝ) := by
      rw [← Real.rpow_natCast (r_y ^ (-1 : ℝ)) 2, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      norm_num
    calc s ^ 2 * rayInt ΔZ 1 r_y z_y
        ≤ s ^ 2 * (K * r_y ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hI1 (by positivity)
      _ ≤ (2 * r_y ^ (-1 : ℝ)) ^ 2 * (K * r_y ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hs2 (mul_nonneg hK0 (hrp_nn _))
      _ = 4 * K * 1 * ((r_y ^ (-1 : ℝ)) ^ 2 * r_y ^ (-3 : ℝ)) := by ring
      _ ≤ 4 * K * M * r_y ^ (-5 : ℝ) := by rw [hp]; gcongr
  -- Term 6: s * rayInt 2 ≤ 2 * K * M * r_y ^ (-5)
  have ht6 : s * rayInt ΔZ 2 r_y z_y ≤ 2 * K * M * r_y ^ (-5 : ℝ) := by
    have hp : r_y ^ (-1 : ℝ) * r_y ^ (-4 : ℝ) = r_y ^ (-5 : ℝ) := by
      rw [← Real.rpow_add hr0]; norm_num
    calc s * rayInt ΔZ 2 r_y z_y
        ≤ s * (K * r_y ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left hI2 hs0.le
      _ ≤ (2 * r_y ^ (-1 : ℝ)) * (K * r_y ^ (-4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hs_le (mul_nonneg hK0 (hrp_nn _))
      _ = 2 * K * 1 * (r_y ^ (-1 : ℝ) * r_y ^ (-4 : ℝ)) := by ring
      _ ≤ 2 * K * M * r_y ^ (-5 : ℝ) := by rw [hp]; gcongr
  -- Term 7: rayInt 3 ≤ K * M * r_y ^ (-5)
  have ht7 : rayInt ΔZ 3 r_y z_y ≤ K * M * r_y ^ (-5 : ℝ) := by
    calc rayInt ΔZ 3 r_y z_y ≤ K * 1 * r_y ^ (-5 : ℝ) := by rw [mul_one]; exact hI3
      _ ≤ K * M * r_y ^ (-5 : ℝ) := by gcongr
  linarith

/-- **Sub-leaf 5 (`SepPsiOscFar`, task `PartIII-b:C/rep/8/1/1/2/5/1/1/4`)**:
outward stream-primitive phase-primitive oscillation bound for `commPsi` on the transition annulus
(source 4178-4215, 5400-5432). -/
theorem sepPsiOscFar : SepPsiOscFar := by
  intro χy hχ
  obtain ⟨C_φ, hCφ0, hPhi⟩ := fderiv_commPsi_sub_le hχ
  obtain ⟨C₀, k₀, hC₀, hOsc0⟩ := iterFDeriv_srcX0_osc_hpt_le 0
  obtain ⟨C₁, k₁, hC₁, hOsc1⟩ := iterFDeriv_srcX0_osc_hpt_le 1
  obtain ⟨C₂, k₂, hC₂, hOsc2⟩ := iterFDeriv_srcX0_osc_hpt_le 2
  obtain ⟨C₃, k₃, hC₃, hOsc3⟩ := iterFDeriv_srcX0_osc_hpt_le 3
  set C_osc : ℝ := C₀ + C₁ + C₂ + C₃
  set k_osc : ℕ := max (max k₀ k₁) (max k₂ k₃)
  refine ⟨19 * C_φ * C_osc, k_osc + 1, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hxo1 hxo2
  set ρo := Real.sqrt (5 * ν / 6)
  have hρo0 : 0 ≤ ρo := Real.sqrt_nonneg _
  have hth : ThinHyp c ρo F := ⟨hFm, hFp, hFs⟩
  obtain ⟨hm1, _⟩ := IIIa.sepMomentSplit c hc F hFm
  have hN1 : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfin hm1
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hFm
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hFs x' Y _ h]
  have hth1 : ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  set M : ℝ := 1 + ν⁻¹ + c
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    change 1 ≤ 1 + ν⁻¹ + c
    linarith
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hr_ge : Real.sqrt ν ≤ r := Real.sqrt_le_sqrt hxo1
  have hr0 : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hr_ge
  set y : Space := ε⁻¹ • xo
  set r_y : ℝ := ϱ y
  set z_y : ℝ := y 2
  set s : ℝ := (ε⁻¹ * Real.sqrt ν)⁻¹
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hr_y_eq : r_y = ε⁻¹ * r := by
    change ϱ (ε⁻¹ • xo) = ε⁻¹ * r
    rw [ϱ_smul, abs_of_pos (inv_pos.2 hε)]
    rfl
  have hr_y0 : 0 < r_y := by rw [hr_y_eq]; positivity
  have hr_y_in : ε⁻¹ * Real.sqrt ν ≤ r_y := by
    rw [hr_y_eq]
    exact mul_le_mul_of_nonneg_left hr_ge (inv_nonneg.2 hε.le)
  have hr₁_lt : (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) < r_y := by
    have : 0 < ε⁻¹ * Real.sqrt ν := by positivity
    linarith
  have hr₁0 : 0 < (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) := by positivity
  -- Bounds on s and s * r_y⁻¹
  have hr_le_2 : r ≤ 2 * Real.sqrt ν := by
    have hsq : xo 0 ^ 2 + xo 1 ^ 2 ≤ (2 * Real.sqrt ν) ^ 2 := by
      calc xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 := hxo2
        _ ≤ 4 * ν := by linarith
        _ = 2 ^ 2 * (Real.sqrt ν) ^ 2 := by rw [Real.sq_sqrt hν.le]; ring
        _ = (2 * Real.sqrt ν) ^ 2 := by ring
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
  have hs_le : s ≤ 2 * r_y ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, le_mul_inv_iff₀ hr_y0, mul_comm]
    have hr_y_le : r_y ≤ 2 * (ε⁻¹ * Real.sqrt ν) := by
      rw [hr_y_eq]
      calc ε⁻¹ * r ≤ ε⁻¹ * (2 * Real.sqrt ν) :=
            mul_le_mul_of_nonneg_left hr_le_2 (inv_nonneg.2 hε.le)
        _ = 2 * (ε⁻¹ * Real.sqrt ν) := by ring
    calc r_y * s ≤ (2 * (ε⁻¹ * Real.sqrt ν)) * (ε⁻¹ * Real.sqrt ν)⁻¹ :=
          mul_le_mul_of_nonneg_right hr_y_le hs0.le
      _ = 2 * ((ε⁻¹ * Real.sqrt ν) * (ε⁻¹ * Real.sqrt ν)⁻¹) := by ring
      _ = 2 := by rw [mul_inv_cancel₀ (by positivity), mul_one]
  have hsr_le : s * r_y⁻¹ ≤ M := by
    have hR1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
    have h1 : Real.sqrt ν ≤ ε⁻¹ * Real.sqrt ν := by
      calc Real.sqrt ν = 1 * Real.sqrt ν := (one_mul _).symm
        _ ≤ ε⁻¹ * Real.sqrt ν := mul_le_mul_of_nonneg_right hR1 (Real.sqrt_nonneg _)
    have hs_inv : s ≤ (Real.sqrt ν)⁻¹ := inv_anti₀ (Real.sqrt_pos.2 hν) h1
    have hr_inv : r_y⁻¹ ≤ (Real.sqrt ν)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 hν) (h1.trans hr_y_in)
    have hprod : (Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹ = ν⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hν.le]
    have hle : s * r_y⁻¹ ≤ ν⁻¹ := by
      rw [← hprod]
      exact mul_le_mul hs_inv hr_inv (inv_nonneg.2 hr_y0.le) (inv_nonneg.2 (Real.sqrt_nonneg _))
    change s * r_y⁻¹ ≤ 1 + ν⁻¹ + c
    linarith
  set N : ℝ := (IIIa.thinMoment c F).toReal
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set K : ℝ := C_osc * M ^ k_osc * ε⁻¹ * N
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ≥0∞ :=
    ENNReal.ofReal (19 * C_φ * C_osc * M ^ (k_osc + 1) * ε ^ 4 * r ^ (-5 : ℝ)) *
      IIIa.thinMoment c F
  refine ⟨fun _ => a, measurable_const, fun _ => rfl, ?_, ?_⟩
  · refine Eventually.of_forall fun τ => ?_
    set Z₁ := srcX0 ν μ (IIIa.thinSource ε F)
    set Z₂ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))
    set ΔZ : Space → Space := fun w => Z₁ τ w - Z₂ τ w
    have hμ_gt : -(1 / 4) < μ := by linarith
    obtain ⟨B₁, hV1⟩ := thin_validPsiFieldWith hν hμ_gt hε hc hρo0 le_rfl hth hFfin τ
    obtain ⟨B₂, hV2⟩ := thin_validPsiFieldWith hν hμ_gt hε hc hρo0 le_rfl hth1 hN1 τ
    have hVΔ : ValidPsiFieldWith ((23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)) (B₁ + B₂)
        (fun _ => ΔZ) := ValidPsiFieldWith.sub hV1 hV2
    -- Uniform oscillation bounds along outward ray ρ ≥ r_y ≥ ε⁻¹ * √ν
    have hk0 : k₀ ≤ k_osc := le_trans (le_max_left k₀ k₁) (le_max_left _ _)
    have hk1 : k₁ ≤ k_osc := le_trans (le_max_right k₀ k₁) (le_max_left _ _)
    have hk2 : k₂ ≤ k_osc := le_trans (le_max_left k₂ k₃) (le_max_right _ _)
    have hk3 : k₃ ≤ k_osc := le_trans (le_max_right k₂ k₃) (le_max_right _ _)
    have hbd0 : ∀ ρ, r_y ≤ ρ →
        ‖iteratedFDeriv ℝ 0 ΔZ (hpt ρ z_y)‖ ≤ K * ρ ^ (-4 - ((0 : ℕ) : ℝ)) := by
      intro ρ hρ
      have hρ_in : ε⁻¹ * Real.sqrt ν ≤ ρ := hr_y_in.trans hρ
      have hρ0 : 0 < ρ := lt_of_lt_of_le hr_y0 hρ
      have h := hOsc0 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hth hFfin ρ z_y τ hρ_in
      have hC : C₀ ≤ C_osc := by dsimp [C_osc]; linarith
      have hM : M ^ k₀ ≤ M ^ k_osc := pow_le_pow_right₀ hM1 hk0
      calc ‖iteratedFDeriv ℝ 0 ΔZ (hpt ρ z_y)‖
          ≤ C₀ * M ^ k₀ * ε⁻¹ * ρ ^ (-4 - ((0 : ℕ) : ℝ)) * N := h
        _ ≤ C_osc * M ^ k_osc * ε⁻¹ * ρ ^ (-4 - ((0 : ℕ) : ℝ)) * N := by gcongr
        _ = K * ρ ^ (-4 - ((0 : ℕ) : ℝ)) := by dsimp [K]; ring
    have hbd1 : ∀ ρ, r_y ≤ ρ →
        ‖iteratedFDeriv ℝ 1 ΔZ (hpt ρ z_y)‖ ≤ K * ρ ^ (-4 - ((1 : ℕ) : ℝ)) := by
      intro ρ hρ
      have hρ_in : ε⁻¹ * Real.sqrt ν ≤ ρ := hr_y_in.trans hρ
      have hρ0 : 0 < ρ := lt_of_lt_of_le hr_y0 hρ
      have h := hOsc1 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hth hFfin ρ z_y τ hρ_in
      have hC : C₁ ≤ C_osc := by dsimp [C_osc]; linarith
      have hM : M ^ k₁ ≤ M ^ k_osc := pow_le_pow_right₀ hM1 hk1
      calc ‖iteratedFDeriv ℝ 1 ΔZ (hpt ρ z_y)‖
          ≤ C₁ * M ^ k₁ * ε⁻¹ * ρ ^ (-4 - ((1 : ℕ) : ℝ)) * N := h
        _ ≤ C_osc * M ^ k_osc * ε⁻¹ * ρ ^ (-4 - ((1 : ℕ) : ℝ)) * N := by gcongr
        _ = K * ρ ^ (-4 - ((1 : ℕ) : ℝ)) := by dsimp [K]; ring
    have hbd2 : ∀ ρ, r_y ≤ ρ →
        ‖iteratedFDeriv ℝ 2 ΔZ (hpt ρ z_y)‖ ≤ K * ρ ^ (-4 - ((2 : ℕ) : ℝ)) := by
      intro ρ hρ
      have hρ_in : ε⁻¹ * Real.sqrt ν ≤ ρ := hr_y_in.trans hρ
      have hρ0 : 0 < ρ := lt_of_lt_of_le hr_y0 hρ
      have h := hOsc2 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hth hFfin ρ z_y τ hρ_in
      have hC : C₂ ≤ C_osc := by dsimp [C_osc]; linarith
      have hM : M ^ k₂ ≤ M ^ k_osc := pow_le_pow_right₀ hM1 hk2
      calc ‖iteratedFDeriv ℝ 2 ΔZ (hpt ρ z_y)‖
          ≤ C₂ * M ^ k₂ * ε⁻¹ * ρ ^ (-4 - ((2 : ℕ) : ℝ)) * N := h
        _ ≤ C_osc * M ^ k_osc * ε⁻¹ * ρ ^ (-4 - ((2 : ℕ) : ℝ)) * N := by gcongr
        _ = K * ρ ^ (-4 - ((2 : ℕ) : ℝ)) := by dsimp [K]; ring
    have hbd3 : ∀ ρ, r_y ≤ ρ →
        ‖iteratedFDeriv ℝ 3 ΔZ (hpt ρ z_y)‖ ≤ K * ρ ^ (-4 - ((3 : ℕ) : ℝ)) := by
      intro ρ hρ
      have hρ_in : ε⁻¹ * Real.sqrt ν ≤ ρ := hr_y_in.trans hρ
      have hρ0 : 0 < ρ := lt_of_lt_of_le hr_y0 hρ
      have h := hOsc3 ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hth hFfin ρ z_y τ hρ_in
      have hC : C₃ ≤ C_osc := by dsimp [C_osc]; linarith
      have hM : M ^ k₃ ≤ M ^ k_osc := pow_le_pow_right₀ hM1 hk3
      calc ‖iteratedFDeriv ℝ 3 ΔZ (hpt ρ z_y)‖
          ≤ C₃ * M ^ k₃ * ε⁻¹ * ρ ^ (-4 - ((3 : ℕ) : ℝ)) * N := h
        _ ≤ C_osc * M ^ k_osc * ε⁻¹ * ρ ^ (-4 - ((3 : ℕ) : ℝ)) * N := by gcongr
        _ = K * ρ ^ (-4 - ((3 : ℕ) : ℝ)) := by dsimp [K]; ring
    -- Pointwise and ray integral bounds at r_y
    have hP0 : ptNorm ΔZ 0 r_y z_y ≤ K * r_y ^ (-4 : ℝ) := by
      simpa [ptNorm] using hbd0 r_y le_rfl
    have hP1 : ptNorm ΔZ 1 r_y z_y ≤ K * r_y ^ (-5 : ℝ) := by
      simpa [ptNorm, show (-4 : ℝ) - 1 = -5 by norm_num] using hbd1 r_y le_rfl
    have hP2 : ptNorm ΔZ 2 r_y z_y ≤ K * r_y ^ (-6 : ℝ) := by
      simpa [ptNorm, show (-4 : ℝ) - 2 = -6 by norm_num] using hbd2 r_y le_rfl
    have hI0 : rayInt ΔZ 0 r_y z_y ≤ K * r_y ^ (-2 : ℝ) := by
      simpa using rayInt_le_of_hpt_le hVΔ hr₁0 hr₁_lt z_y (by norm_num) hK0 hbd0
    have hI1 : rayInt ΔZ 1 r_y z_y ≤ K * r_y ^ (-3 : ℝ) := by
      simpa [show (-2 : ℝ) - 1 = -3 by norm_num] using
        rayInt_le_of_hpt_le hVΔ hr₁0 hr₁_lt z_y (by norm_num) hK0 hbd1
    have hI2 : rayInt ΔZ 2 r_y z_y ≤ K * r_y ^ (-4 : ℝ) := by
      simpa [show (-2 : ℝ) - 2 = -4 by norm_num] using
        rayInt_le_of_hpt_le hVΔ hr₁0 hr₁_lt z_y (by norm_num) hK0 hbd2
    have hI3 : rayInt ΔZ 3 r_y z_y ≤ K * r_y ^ (-5 : ℝ) := by
      simpa [show (-2 : ℝ) - 3 = -5 by norm_num] using
        rayInt_le_of_hpt_le hVΔ hr₁0 hr₁_lt z_y (by norm_num) hK0 hbd3
    have hsum7 := sum7_le hs0 hr_y0 hK0 hM1 hs_le hsr_le hP0 hP1 hP2 hI0 hI1 hI2 hI3
    have hraw := hPhi ν μ ε c ρo F hν hν1 hμ_gt hε hε1 hc hρo0 le_rfl hth hFfin xo hxo1 hxo2 τ
    have hε_rpow : ε⁻¹ * r_y ^ (-5 : ℝ) = ε ^ 4 * r ^ (-5 : ℝ) := by
      have hr_y_div : r_y = r / ε := by
        rw [hr_y_eq]
        ring
      rw [hr_y_div, Real.div_rpow hr0.le hε.le]
      have h5 : ε ^ (-5 : ℝ) = (ε ^ 5)⁻¹ := by
        rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hε.le, Real.rpow_natCast]
      rw [h5, div_inv_eq_mul]
      have : ε ≠ 0 := hε.ne'
      field_simp
    have h_real :
        ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖ ≤
          (19 * C_φ * C_osc * M ^ (k_osc + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * N := by
      calc ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖
          ≤ C_φ * (19 * K * M * r_y ^ (-5 : ℝ)) :=
            hraw.trans (mul_le_mul_of_nonneg_left hsum7 hCφ0)
        _ = 19 * C_φ * C_osc * (M ^ k_osc * M) * (ε⁻¹ * r_y ^ (-5 : ℝ)) * N := by
            dsimp [K]; clear_value C_osc M r_y r N; ring
        _ = (19 * C_φ * C_osc * M ^ (k_osc + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * N := by
            rw [← pow_succ, hε_rpow]; clear_value C_osc M r N; ring
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal h_real).trans ?_
    have hcoeff_nn : 0 ≤ 19 * C_φ * C_osc * M ^ (k_osc + 1) * ε ^ 4 * r ^ (-5 : ℝ) := by
      have : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr0.le _
      positivity
    rw [ENNReal.ofReal_mul hcoeff_nn, ENNReal.ofReal_toReal hFfin]
  · have hP : 0 < 2 * ε * c := by positivity
    exact (IIIa.ltauAt_const (2 * ε * c) hP a).le

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

end
