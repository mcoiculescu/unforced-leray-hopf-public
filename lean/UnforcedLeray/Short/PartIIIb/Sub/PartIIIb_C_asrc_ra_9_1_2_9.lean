import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks

/-!
# `PartIII-b:C/asrc/ra/9/1/2/9` : `LatCellBound` from the `h^p` and `ψ^p` cell bounds

Source of record: `the November 2 reference manuscript`, lines 5063-5071, 5076-5079,
5034-5039, 4979-4980.  The two halves (`h^p_A` words, `ψ^p_A` words) are separate Gaussian-summation
estimates; the constants are merged by `max`/`min`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Cell `L²` bound of the words applied to `h^p_A` (source 5063-5071, 5076-5079). -/
def LatCellHp (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ w ∈ budgetWords,
        ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * ‖wordW w (hpM ν χf A) (s, x)‖) ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
          ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k * affM ν χf A * s ^ (5 / 2 : ℝ)) ^ 2)

/-- Cell `L²` bound of the words applied to `ψ^p_A` (source 5063-5071, 5076-5079). -/
def LatCellPsi (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ w ∈ budgetWords,
        ∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * |wordW w (psiM ν χf A) (s, x)|) ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
          ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k * affM ν χf A * s ^ (5 / 2 : ℝ)) ^ 2)

private lemma mono_aux (C1 C k1 k : ℝ) (ν M s : ℝ) (kk1 kk : ℕ) (hC1 : 0 ≤ C1) (hCC : C1 ≤ C)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hk : kk1 ≤ kk) :
    ENNReal.ofReal ((C1 * ν⁻¹ ^ kk1 * M * s) ^ 2) ≤ ENNReal.ofReal ((C * ν⁻¹ ^ kk * M * s) ^ 2) := by
  apply ENNReal.ofReal_le_ofReal
  apply sq_le_sq.mpr
  have h1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.mpr hν1
  have hp : ν⁻¹ ^ kk1 ≤ ν⁻¹ ^ kk := pow_le_pow_right₀ h1 hk
  have hp0 : 0 ≤ ν⁻¹ ^ kk1 := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
  rw [abs_of_nonneg hC1, abs_of_nonneg (hC1.trans hCC), abs_of_nonneg hp0,
    abs_of_nonneg (hp0.trans hp)]
  have : 0 ≤ C := hC1.trans hCC
  have := abs_nonneg M
  have := abs_nonneg s
  gcongr

theorem latCellBound_of (as : ℝ) (χf : ℝ → ℝ) (h1 : LatCellHp as χf) (h2 : LatCellPsi as χf) :
    LatCellBound as χf := by
  intro hχ
  obtain ⟨C1, k1, n1, hC1, hn1, H1⟩ := h1 hχ
  obtain ⟨C2, k2, n2, hC2, hn2, H2⟩ := h2 hχ
  refine ⟨max C1 C2, max k1 k2, min (min n1 n2) 1, by positivity, fun ν hν hνle A hA s hs hs1 w hw => ?_⟩
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνn1 : ν ≤ n1 := hνle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνn2 : ν ≤ n2 := hνle.trans ((min_le_left _ _).trans (min_le_right _ _))
  constructor
  · refine (H1 ν hν hνn1 A hA s hs hs1 w hw).trans ?_
    have := mono_aux C1 (max C1 C2) 0 0 ν (affM ν χf A) (s ^ (5 / 2 : ℝ)) k1 (max k1 k2) hC1
      (le_max_left _ _) hν hν1 (le_max_left _ _)
    simpa [mul_assoc] using this
  · refine (H2 ν hν hνn2 A hA s hs hs1 w hw).trans ?_
    have := mono_aux C2 (max C1 C2) 0 0 ν (affM ν χf A) (s ^ (5 / 2 : ℝ)) k2 (max k1 k2) hC2
      (le_max_right _ _) hν hν1 (le_max_right _ _)
    simpa [mul_assoc] using this

end UnforcedLeray.Short.PartIIIb.Concrete
