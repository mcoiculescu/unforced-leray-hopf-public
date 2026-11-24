import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/1/5` (`VcJetSup`): decomposition

Source of record: `the November 2 reference manuscript` line 2205 (`V_c`),
255-258 (polynomial convention).

Age derivatives of `Vc` are spatial: `Vc` solves the vector heat equation `∂ₛ Vc = ν Δ Vc`
(`Train.Vc_heat`), so `∂ₛ^ℓ D^j Vc = ν^ℓ D^j Δ^ℓ Vc`, and `Δ^ℓ` costs `2ℓ` spatial derivatives
(`VcAgeJetLe`, which uses joint smoothness `VcSmooth`).  The spatial jets are bounded by
`Train.Vc_bounds` (`VcSpatialJetBound`).  Proved here: `vcJetSup_of`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartI UnforcedLeray.Train

/-- **Age jets through the heat equation** (SP 2205; needs `VcSmooth`, i.e. the target of task
`PartII-b:G4/3/6/1/4`): for `ν, c > 0` and `s > 0`,
`∂_s^ℓ D^j Vc = ν^ℓ D^j Δ^ℓ Vc` (iterating `Train.Vc_heat`, `Lib/Train/PeriodizedVortex.lean:192`),
hence `‖ageJet ℓ j Vc s z‖ ≤ ν^ℓ K ‖D^{j+2ℓ} Vc(s) (z)‖` with `K` depending only on `ℓ, j`
(`Δ = ∂_q² + ∂_η²` is a sum of two second derivatives along unit vectors of `Plane = ℝ × ℝ`, so
`K = 2^ℓ` works). -/
def VcAgeJetLe : Prop :=
  ∀ ℓ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ s : ℝ, 0 < s →
    ∀ z : UnforcedLeray.Cyl.Plane,
      ‖ageJet ℓ j (fun r w => Vc ν c r w) s z‖ ≤
        ν ^ ℓ * K * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖

/-- **Spatial jets of `Vc`** (`Train.Vc_bounds`, `Lib/Train/VortexBounds.lean:40`, whose word
derivatives `B0151.derivWord` are the coordinate partials of the iterated Fréchet derivative, so
`‖D^j Vc‖ ≤ 2^j max_words`): for each `j`, `‖D^j Vc ν c s z‖ ≤ C` whenever `ν > 0`, `c > 0`,
`s ≥ 0`, `1 ≤ 1 + νs ≤ c²`. -/
def VcSpatialJetBound : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → width ν s ≤ c ^ 2 →
    ∀ z : UnforcedLeray.Cyl.Plane, ‖jet j (Vc ν c s) z‖ ≤ C

/-- **`VcJetSup` from the two jet facts.** -/
theorem vcJetSup_of (h1 : VcAgeJetLe) (h2 : VcSpatialJetBound) : VcJetSup := by
  intro Sig hSig ℓ j
  obtain ⟨K, hK, hKb⟩ := h1 ℓ j
  obtain ⟨C, hC, hCb⟩ := h2 (j + 2 * ℓ)
  refine ⟨K * C + 1, 0, 1 / (2 + Sig), by positivity, by positivity, ?_⟩
  intro ν hν hνle s hs hsS z
  have hSig2 : 0 < 2 + Sig := by linarith
  have hν1 : ν ≤ 1 := by
    refine hνle.trans ?_
    rw [div_le_one hSig2]; linarith
  have hνS : ν * (2 + Sig) ≤ 1 := by
    have := (le_div_iff₀ hSig2).1 hνle
    simpa using this
  have hw : width ν s ≤ ((ν ^ 2)⁻¹) ^ 2 := by
    have h1 : ν * s ≤ Sig := by
      have := mul_le_mul_of_nonneg_left hsS hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    have h2 : (2 + Sig) ≤ ν⁻¹ := by
      rw [le_inv_comm₀ hSig2 hν]
      exact hνle.trans (by rw [one_div])
    have h3 : ν⁻¹ ≤ ((ν ^ 2)⁻¹) ^ 2 := by
      have hi : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
      calc ν⁻¹ = ν⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ ν⁻¹ ^ 4 := pow_le_pow_right₀ hi (by norm_num)
        _ = ((ν ^ 2)⁻¹) ^ 2 := by rw [inv_pow, inv_pow, ← pow_mul]
    unfold width
    linarith
  have hc : 0 < (ν ^ 2)⁻¹ := by positivity
  have ha := hKb ν ((ν ^ 2)⁻¹) hν hc s hs z
  have hb := hCb ν ((ν ^ 2)⁻¹) s hν hc hs.le hw z
  calc ‖ageJet ℓ j (fun r w => Vc ν ((ν ^ 2)⁻¹) r w) s z‖
      ≤ ν ^ ℓ * K * ‖jet (j + 2 * ℓ) (Vc ν ((ν ^ 2)⁻¹) s) z‖ := ha
    _ ≤ 1 * K * C := by
        have hνl : ν ^ ℓ ≤ 1 := pow_le_one₀ hν.le hν1
        gcongr
    _ ≤ (K * C + 1) * (ν ^ 0)⁻¹ := by simp
