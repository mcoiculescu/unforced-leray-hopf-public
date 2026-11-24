import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9

/-!
# `PartIII-b:C/rep/9/3`: `M(A_T) ≤ P_ν ε³ N` from the actual jet

Source `the November 2 reference manuscript` 5396-5413 (`χ_f A_T = A_T`, the jet
bound `repair:actual-jet`), and 4741-4745, 4955-4962 (the norm `affM`).  The actual jet
`ActualJet` (`PartIII-b:C/rep/6`) gives, for `A_T = 𝓛T`, the jet bounds with the old moment `N`
and `A_T(s) = 0` for `s ≥ 1/ν`.  The cutoff `χ_f` equals one on `s ≤ 1/ν`, so `χ_f A_T = A_T`,
and `M(A_T)` is a supremum of `7` jet terms, each bounded by `C ν^{-k} ε³ N`.  The constant is
taken as `7 (|C| + 1)` so that it is positive, which is needed for the case `N = ∞`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `χ_f A = A` when `A` vanishes on `[1/ν, ∞)` (source 5396-5398: `χ_f` is one for `s ≤ 1/ν`). -/
theorem rep9_3_ay_eq {ν : ℝ} (hν : 0 < ν) {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) (A : ℝ → Mat3)
    (hA : ∀ s : ℝ, 1 / ν ≤ s → A s = 0) : Ay ν χ A = A := by
  funext s
  unfold Ay
  by_cases hs : s ≤ 1 / ν
  · have h1 : ν * s ≤ 1 := by
      rw [mul_comm]
      exact (le_div_iff₀ hν).1 hs
    rw [hχ.one (ν * s) h1, one_smul]
  · rw [hA s (not_le.1 hs).le, smul_zero]

/-- The leaf `𝓛` of the pinned regime: the pinned `Lj` of `RegimePins.lj` is the operator
`LjOp` (the Hilbert choice in its definition). -/
theorem rep9_3_ljOp_spec (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (h : ∃ Lj : LStr Pl K L →L[ℝ] AffSp K.as, ∀ T, affIota K.as (Lj T) =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) (T : LStr Pl K L) :
    affIota K.as (LjOp Pl K L μ T) =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T :=
  (Classical.epsilon_spec h) T

/-- The supremum defining `affM` is at most `7 c m` when every jet term is at most `c s^{5/2} m`
(source 4955-4962). -/
theorem rep9_3_affM_le (ν : ℝ) (hν : 0 < ν) {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) (A : ℝ → Mat3)
    (hA : ∀ s : ℝ, 1 / ν ≤ s → A s = 0) (c m : ℝ)
    (hbd : ∀ j : ℕ, j ≤ 6 → ∀ s : ℝ, 0 < s → frob (sDerivIter j A s) ≤ c * s ^ (5 / 2 : ℝ) * m) :
    affM ν χ A ≤ 7 * c * m := by
  unfold affM
  rw [rep9_3_ay_eq hν hχ A hA]
  refine csSup_le ((Set.nonempty_Ioc.2 (div_pos (by norm_num) hν)).image _) ?_
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hs0, -⟩ := hs
  show s ^ (-(5 / 2 : ℝ)) * affSum 6 A s ≤ 7 * c * m
  have hsp : s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs0]
    norm_num
  have hsum : affSum 6 A s ≤ 7 * (c * s ^ (5 / 2 : ℝ) * m) := by
    unfold affSum
    calc ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j A s)
        ≤ ∑ j ∈ Finset.range (6 + 1), c * s ^ (5 / 2 : ℝ) * m :=
          Finset.sum_le_sum fun j hj =>
            hbd j (by have := Finset.mem_range.1 hj; omega) s hs0
      _ = 7 * (c * s ^ (5 / 2 : ℝ) * m) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  calc s ^ (-(5 / 2 : ℝ)) * affSum 6 A s
      ≤ s ^ (-(5 / 2 : ℝ)) * (7 * (c * s ^ (5 / 2 : ℝ) * m)) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hs0.le _)
    _ = 7 * c * m * (s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ)) := by ring
    _ = 7 * c * m := by rw [hsp, mul_one]

/-- The real/ENNReal core: the jet bound with a finite old moment `N = ofReal m` gives
`ofReal (M(A)) ≤ ofReal(7(|C|+1)ν^{-k}ε³) · ofReal m`. -/
theorem rep9_3_key (ν ε C : ℝ) (k : ℕ) (hν : 0 < ν) (hε : 0 < ε) {χ : ℝ → ℝ}
    (hχ : IsSourceCutoffC χ) (A : ℝ → Mat3) (hA : ∀ s : ℝ, 1 / ν ≤ s → A s = 0) (m : ℝ)
    (hm0 : 0 ≤ m)
    (hfr : ∀ j : ℕ, j ≤ 6 → ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (frob (sDerivIter j A s)) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ)) * ENNReal.ofReal m) :
    ENNReal.ofReal (affM ν χ A) ≤
      ENNReal.ofReal (7 * (|C| + 1) * ν⁻¹ ^ k * ε ^ 3) * ENNReal.ofReal m := by
  have hqk : 0 ≤ ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν.le) k
  have hcnn : 0 ≤ |C| * ν⁻¹ ^ k * ε ^ 3 :=
    mul_nonneg (mul_nonneg (abs_nonneg C) hqk) (pow_nonneg hε.le 3)
  have hc7 : 0 ≤ 7 * (|C| + 1) * ν⁻¹ ^ k * ε ^ 3 :=
    mul_nonneg (mul_nonneg (by positivity) hqk) (pow_nonneg hε.le 3)
  have hbd : ∀ j : ℕ, j ≤ 6 → ∀ s : ℝ, 0 < s →
      frob (sDerivIter j A s) ≤ |C| * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ) * m := by
    intro j hj s hs
    have h1 := hfr j hj s hs
    have hqs : 0 ≤ ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ) :=
      mul_nonneg (mul_nonneg hqk (pow_nonneg hε.le 3)) (Real.rpow_nonneg hs.le _)
    have hpos : 0 ≤ |C| * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ) :=
      mul_nonneg hcnn (Real.rpow_nonneg hs.le _)
    have hCle : C * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ) ≤
        |C| * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self C) hqs
      simpa only [mul_assoc] using this
    have h2 : ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ)) ≤
        ENNReal.ofReal (|C| * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ)) :=
      ENNReal.ofReal_le_ofReal hCle
    have h3 : ENNReal.ofReal (frob (sDerivIter j A s)) ≤
        ENNReal.ofReal (|C| * ν⁻¹ ^ k * ε ^ 3 * s ^ (5 / 2 : ℝ) * m) := by
      rw [ENNReal.ofReal_mul hpos]
      exact h1.trans (by gcongr)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hpos hm0)).1 h3
  rw [← ENNReal.ofReal_mul hc7]
  apply ENNReal.ofReal_le_ofReal
  have hreal := rep9_3_affM_le ν hν hχ A hA _ m hbd
  have hqm : 0 ≤ ν⁻¹ ^ k * ε ^ 3 * m :=
    mul_nonneg (mul_nonneg hqk (pow_nonneg hε.le 3)) hm0
  nlinarith [hreal, hqm, abs_nonneg C]

/-- **`PartIII-b:C/rep/9/3`** (`repair:actual-jet` through `affM`, source 5396-5413): under the
repair standing and the actual jet, `M(A_T) ≤ P_ν ε³ N` along the sequence, where
`A_T = 𝓛T` and `N = N₁(χ_oT₁)`. -/
theorem affMJet_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (hAJ : D.ActualJet) :
    D.AffMJet := by
  obtain ⟨C, k, hJ⟩ := hAJ
  refine ⟨7 * (|C| + 1), k, ?_⟩
  filter_upwards [hJ, hst.pins] with n hJn hpn
  intro z hz T
  obtain ⟨hfr, hzero⟩ := hJn z hz T
  have hν : 0 < retNu D.Pl D.σ₀ n := retNu_pos D.Pl D.σ₀ n
  have hε : 0 < retEps D.Pl D.σ₀ n := retEps_pos D.coeff_ne n
  rw [rep9_3_ljOp_spec D.Pl D.K (D.level n) (D.mu n z) (hpn z hz).lj T]
  by_cases htop : oldN1 D.Pl D.K (D.level n) T = ⊤
  · have hc0 : 0 < 7 * (|C| + 1) * (retNu D.Pl D.σ₀ n)⁻¹ ^ k * (retEps D.Pl D.σ₀ n) ^ 3 :=
      mul_pos (mul_pos (by positivity) (pow_pos (inv_pos.2 hν) k)) (pow_pos hε 3)
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc0).ne']
    exact le_top
  · obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 ≤ m ∧ oldN1 D.Pl D.K (D.level n) T = ENNReal.ofReal m :=
      ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
    rw [hm] at hfr ⊢
    exact rep9_3_key (retNu D.Pl D.σ₀ n) (retEps D.Pl D.σ₀ n) C k hν hε hst.chiF _ hzero m hm0
      hfr

end UnforcedLeray.Short.PartIIIb.Concrete
