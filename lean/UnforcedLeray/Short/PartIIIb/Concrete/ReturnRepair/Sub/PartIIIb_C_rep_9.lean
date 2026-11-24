import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.SrcPairing

/-!
# `PartIII-b:C/rep/9`: `repair:actual-affine-remainder` reduced to three leaves

Source `the November 2 reference manuscript` 5507-5525 (and the final subtraction
5694).  `R⁻¹‖𝔯_{A_T}‖ ≤ P_ν(ε + δ_base + δ_U) M(A_T)` for every bound of `δ_U` at the level
(Lemma `ret:physical-affine`, 5001-5016, `RABoundExists`), `δ_U ≤ P_ν ρ` for large `n` (5094
"`δ_U ≤ P_νρ` from the background bounds", with `short-bg:strong` 2538-2541, `RhoW1`), and
`M(A_T) ≤ P_ν ε³ N` (`repair:actual-jet`, 5400-5413, `χ_f A_T = A_T`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf (source 5400-5413, 4741-4745): `M(A_T) ≤ P_ν ε³ N` along the sequence, where
`M = affM` and `A_T = 𝓛T` (`χ_f A_T = A_T`, 5396-5398). -/
def SeqData.AffMJet (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ENNReal.ofReal (affM (retNu D.Pl D.σ₀ n) D.K.χf
          (affIota D.K.as (LjOp D.Pl D.K (D.level n) (D.mu n z) T))) ≤
        ENNReal.ofReal (C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k * (retEps D.Pl D.σ₀ n) ^ 3) *
          oldN1 D.Pl D.K (D.level n) T

/-- Leaf (source 5007-5008, 5049-5050, 5094; `short-bg:strong` 2538-2541): for large `n`,
`P_ν ρ = Cν^{-k}ε^{3/11}e^{m₀/ν}` (`rhoRep`, 5138) bounds `δ_U = ‖U - U_raw‖_{W^{1,∞}}` at level
`n` (`IsW1InfBoundAt`).  It is eventual: `RepairStanding` constrains the data of `D` only at large
`n`. -/
def SeqData.RhoW1 (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    D.IsW1InfBoundAt n (C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k * rhoRep D.K (D.level n))

theorem affRem_real (C Cj Cd ν ε δ ρ d : ℝ) (k kj kd : ℕ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hd0 : 0 ≤ d) (hd : d ≤ Cd * ν⁻¹ ^ kd * ρ) :
    |C| * ν⁻¹ ^ k * (ε + δ + d) * (|Cj| * ν⁻¹ ^ kj * ε ^ 3) ≤
      |C| * |Cj| * (1 + |Cd|) * ν⁻¹ ^ (k + kj + kd) * ε ^ 3 * (ε + ρ + δ) := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hP : 1 ≤ ν⁻¹ ^ kd := one_le_pow₀ h1
  have hP0 : 0 ≤ ν⁻¹ ^ k := by positivity
  have hPj0 : 0 ≤ ν⁻¹ ^ kj := by positivity
  have hPd0 : 0 ≤ ν⁻¹ ^ kd := by positivity
  have hd' : d ≤ |Cd| * ν⁻¹ ^ kd * ρ :=
    hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hPd0) hρ)
  have hS : ε + δ + d ≤ (1 + |Cd|) * ν⁻¹ ^ kd * (ε + ρ + δ) := by
    have a1 : ε ≤ ν⁻¹ ^ kd * ε := by nlinarith
    have a2 : δ ≤ ν⁻¹ ^ kd * δ := by nlinarith
    have a3 : |Cd| * ν⁻¹ ^ kd * ρ ≤ |Cd| * ν⁻¹ ^ kd * ρ := le_rfl
    nlinarith [mul_nonneg (abs_nonneg Cd) (mul_nonneg hPd0 hρ),
      mul_nonneg (abs_nonneg Cd) (mul_nonneg hPd0 hε.le),
      mul_nonneg (abs_nonneg Cd) (mul_nonneg hPd0 hδ)]
  have hpow : ν⁻¹ ^ (k + kj + kd) = ν⁻¹ ^ k * ν⁻¹ ^ kj * ν⁻¹ ^ kd := by
    rw [pow_add, pow_add]
  rw [hpow]
  have hE : 0 ≤ ε ^ 3 := by positivity
  have hfac : 0 ≤ |C| * ν⁻¹ ^ k * (|Cj| * ν⁻¹ ^ kj * ε ^ 3) := by positivity
  calc |C| * ν⁻¹ ^ k * (ε + δ + d) * (|Cj| * ν⁻¹ ^ kj * ε ^ 3)
      = (|C| * ν⁻¹ ^ k * (|Cj| * ν⁻¹ ^ kj * ε ^ 3)) * (ε + δ + d) := by ring
    _ ≤ (|C| * ν⁻¹ ^ k * (|Cj| * ν⁻¹ ^ kj * ε ^ 3)) *
          ((1 + |Cd|) * ν⁻¹ ^ kd * (ε + ρ + δ)) := mul_le_mul_of_nonneg_left hS hfac
    _ = _ := by ring

theorem affineRemainder_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hex : RABoundExists D dm dp) (hW : D.RhoW1) (hJ : D.AffMJet) : D.AffineRemainder := by
  obtain ⟨Csig, bsig, C, k, N, hb, hr⟩ := hex hst.actual
  obtain ⟨Cj, kj, hJ⟩ := hJ
  obtain ⟨Cd, kd, hW⟩ := hW
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  refine ⟨|C| * |Cj| * (1 + |Cd|), k + kj + kd, Csig, bsig, hb, ?_⟩
  filter_upwards [eventually_ge_atTop N, hJ, hW, hν1] with n hn hJn hWn hν z hz
  generalize hdU : Cd * (retNu D.Pl D.σ₀ n)⁻¹ ^ kd * rhoRep D.K (D.level n) = dUn at hWn
  have hdn : dUn ≤ Cd * (retNu D.Pl D.σ₀ n)⁻¹ ^ kd * rhoRep D.K (D.level n) := hdU.symm.le
  unfold AffineRemainderAt
  intro T
  obtain ⟨r, hpin, hbd⟩ := hr n hn z hz
  have hre : rAOp D.Pl D.K (D.level n) (D.mu n z) = r :=
    isRAOp_unique srcPairingNondeg (cOf_pos (retNu_pos _ _ _)) (retEps_pos D.coeff_ne n)
      (rAOp_spec ⟨r, hpin⟩) hpin
  rw [hre]
  have h1 := hbd dUn hWn (LjOp D.Pl D.K (D.level n) (D.mu n z) T)
  have hJT := hJn z hz T
  have hνp : 0 < retNu D.Pl D.σ₀ n := retNu_pos _ _ _
  have hεp : 0 < retEps D.Pl D.σ₀ n := retEps_pos D.coeff_ne n
  have hδ : 0 ≤ deltaBase Csig bsig (retNu D.Pl D.σ₀ n) := (Real.exp_pos _).le
  have hρ : 0 ≤ rhoRep D.K (D.level n) :=
    mul_nonneg (Real.rpow_pos_of_pos hεp _).le (Real.exp_pos _).le
  have hd0 : 0 ≤ dUn := (norm_nonneg _).trans (hWn 0 0).1
  have hM := affM_nonneg (retNu D.Pl D.σ₀ n) D.K.χf
    (affIota D.K.as (LjOp D.Pl D.K (D.level n) (D.mu n z) T))
  set a := affM (retNu D.Pl D.σ₀ n) D.K.χf
    (affIota D.K.as (LjOp D.Pl D.K (D.level n) (D.mu n z) T)) with ha
  set ν := retNu D.Pl D.σ₀ n with hνdef
  set ε := retEps D.Pl D.σ₀ n with hεdef
  set δ := deltaBase Csig bsig ν with hδdef
  have hSn : 0 ≤ ε + δ + dUn := by positivity
  have hP0 : 0 ≤ ν⁻¹ ^ k := by positivity
  have h2 : ‖r (LjOp D.Pl D.K (D.level n) (D.mu n z) T)‖ ≤ |C| * ν⁻¹ ^ k * (ε + δ + dUn) * a :=
    h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) hP0) hSn) hM)
  have hXn : 0 ≤ |C| * ν⁻¹ ^ k * (ε + δ + dUn) := by positivity
  have hJ2 : ENNReal.ofReal a ≤ ENNReal.ofReal (|Cj| * ν⁻¹ ^ kj * ε ^ 3) *
      oldN1 D.Pl D.K (D.level n) T :=
    hJT.trans (by
      gcongr
      exact le_abs_self _)
  have hreal := affRem_real C Cj Cd ν ε δ (rhoRep D.K (D.level n)) dUn k kj kd hνp hν
    hεp hδ hρ hd0 hdn
  calc ENNReal.ofReal ‖r (LjOp D.Pl D.K (D.level n) (D.mu n z) T)‖
      ≤ ENNReal.ofReal (|C| * ν⁻¹ ^ k * (ε + δ + dUn) * a) := ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (|C| * ν⁻¹ ^ k * (ε + δ + dUn)) * ENNReal.ofReal a :=
        ENNReal.ofReal_mul hXn
    _ ≤ ENNReal.ofReal (|C| * ν⁻¹ ^ k * (ε + δ + dUn)) *
          (ENNReal.ofReal (|Cj| * ν⁻¹ ^ kj * ε ^ 3) * oldN1 D.Pl D.K (D.level n) T) :=
        by gcongr
    _ = ENNReal.ofReal (|C| * ν⁻¹ ^ k * (ε + δ + dUn) * (|Cj| * ν⁻¹ ^ kj * ε ^ 3)) *
          oldN1 D.Pl D.K (D.level n) T := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hXn]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

end UnforcedLeray.Short.PartIIIb.Concrete
