import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4

/-!
# Decomposition of `coefChgQuant` (task `PartIII-b:C/rep/8/2/pres/4/2`)

Source `the November 2 reference manuscript`
5287-5289, 2669, 2697-2713, 5134-5139, 2715-2725, 5007-5008.  `CoefChgQuant` is the `Y_{11/4}`
bound of the change together with the pointwise sup bound, with common constants.  Here they are
split into two statements with separate constants, merged using `ν ≤ 1` and `0 ≤ ρ`.
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `Y_{11/4}` bound of `U - U_raw` and its two derivatives in ring-chart form (source
5287-5289, 2669, 2697-2713, 5134-5139: `U - U_raw = r_b + E_εα_bg`, `r_b` from `RepairDerivBound`
and `ExactSplitII.energy` via `phaseAvg_ringChart`; the entrance part from the ball bound on `α`
and the inlet columns). -/
def CoefChgLp (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    eLpNorm (ringRead (D.level n).ε⁻¹ fun τ =>
        coefChgDens ((D.level n).U τ) ((D.level n).V τ)) (11 / 4)
        (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n))

/-- The pointwise bound `|U| + |U_raw| ≤ C ν⁻ᵏ` at chart points (source 2715-2725:
`sup √s W|v| ≤ P_ν`; 5007-5008). -/
def CoefChgSup (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ p : Chart, 0 < p.1 →
      ‖(D.level n).U (NearInst.chartTau (D.level n).ε⁻¹ p) (NearInst.chartY (D.level n).ε⁻¹ p)‖ +
          ‖(D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ p) (NearInst.chartY (D.level n).ε⁻¹ p)‖ +
          ‖rawU D.Pl (D.level n) (NearInst.chartTau (D.level n).ε⁻¹ p)
            (NearInst.chartY (D.level n).ε⁻¹ p)‖ ≤ C * (D.level n).ν⁻¹ ^ k

/-- `ν_n ≤ 1` and `ρ_n ≥ 0` for large `n` (needed to merge the two exponents). -/
def NuLeOneRhoNonneg (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 ∧ 0 ≤ rhoRep D.K (D.level n)

theorem coefChgQuant_of (D : SeqData) (h1 : CoefChgLp D) (h2 : CoefChgSup D)
    (h3 : NuLeOneRhoNonneg D) : CoefChgQuant D := by
  obtain ⟨C1, k1, hA⟩ := h1
  obtain ⟨C2, k2, hB⟩ := h2
  refine ⟨max (max C1 C2) 0, max k1 k2, ?_⟩
  filter_upwards [hA, hB, h3] with n hA hB hν
  obtain ⟨hν1, hρ⟩ := hν
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have ha : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν1⟩
  set a := (D.level n).ν⁻¹ with hadef
  have hmono : ∀ C : ℝ, ∀ k : ℕ, C ≤ max (max C1 C2) 0 → k ≤ max k1 k2 →
      C * a ^ k ≤ max (max C1 C2) 0 * a ^ (max k1 k2) := by
    intro C k hC hk
    have h0 : 0 ≤ max (max C1 C2) 0 := le_max_right _ _
    have hapos : 0 < a := by linarith
    have hak : a ^ k ≤ a ^ (max k1 k2) := pow_le_pow_right₀ ha hk
    calc C * a ^ k ≤ max C 0 * a ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (max C1 C2) 0 * a ^ k :=
          mul_le_mul_of_nonneg_right (max_le hC h0) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hak h0
  refine ⟨hA.trans (ENNReal.ofReal_le_ofReal ?_), fun p hp => (hB p hp).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (hmono C1 k1 ((le_max_left _ _).trans (le_max_left _ _)) (le_max_left _ _)) hρ
  · exact hmono C2 k2 ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)

end UnforcedLeray.Short.PartIIIb.Concrete
