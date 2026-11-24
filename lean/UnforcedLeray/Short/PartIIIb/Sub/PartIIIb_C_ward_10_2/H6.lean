import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H5

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (6): the primitive of `X₀` is dominated by the
cylinder majorant

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3697,
4178-4186: `|Ψ_{X₀}(r,z)| ≤ ∫_r^∞ ρ|X₀| dρ`, `|X₀| ≤ |W_μ| + |W_{μ+1}|`, `sep:resolvent` /
`sep:kernel` for each, and the radial integral of the order-four kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w2Dom_mono_a (k : Space → ℝ≥0∞) {a a' : ℝ} (h : a ≤ a') (g : ℝ → Space → ℝ≥0∞) (τ : ℝ)
    (y : Space) : w2Dom k a' g τ y ≤ w2Dom k a g τ y := by
  unfold w2Dom
  refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hl.1 hl.2.le h)) le_rfl

theorem w2_enorm_sepWre {ν : ℝ} (m : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) :
    ‖sepWre ν m T τ y‖ₑ ≤ ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 0 τ y := by
  unfold IIIa.wDerivNorm
  have e : ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y‖ₑ =
      ENNReal.ofReal ‖IIIa.sepW ν (m : ℂ) T y τ‖ := by
    rw [← ofReal_norm, norm_iteratedFDeriv_zero]
  rw [e, ← ofReal_norm (sepWre ν m T τ y), ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (w10_norm0V m T τ y)

/-- Unconditional pointwise domination of `W_m` by the dilation integral. -/
theorem w2_wdom : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν : ℝ), 0 < ν → ∀ m : ℝ, -(1 / 4) < m →
    ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
    ∀ T, IIIa.IsSepSource P rOut T → ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
      IIIa.wDerivNorm ν (m : ℂ) T 0 τ y ≤
        ENNReal.ofReal C0 * IIIa.sepDom (2 * m + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y := by
  obtain ⟨C0, hC0, h⟩ := IIIa.sepWDominated IIIa.sepKernelBounds 0
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro ν hν m hm rOut rIn P hr hlt hP T hT τ y hy
  by_cases htop : IIIa.sepDom (2 * (m : ℂ).re + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y = ⊤
  · have : IIIa.sepDom (2 * m + 2) 0 (rIn - rOut) (IIIa.srcNorm T) τ y = ⊤ := by
      simpa using htop
    rw [this, ENNReal.mul_top (by simp; linarith)]
    exact le_top
  · have := h ν hν (m : ℂ) (by simpa using hm) rOut rIn P hr hlt hP T hT τ y hy
      (lt_top_iff_ne_top.2 htop)
    refine this.trans ?_
    simp only [Complex.ofReal_re]
    gcongr
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete
end
