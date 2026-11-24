import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/2/org/3/3`: the constants are uniform along the sequence

Source `the November 2 reference manuscript` 3631-3633 (`sep:young`: "`K`
compact in `Re μ > -1/4`", constants independent of `ν, D, P`), 3669-3674 (`sep:thin-global`:
`R ≥ 1`, `P_ν = Cν^{-k}`), 5928-5950 (`ν_n, ε_n → 0`; the window `μ_n(z) = σ₀ + z/(2|log ν_n|)`,
`σ₀ ∈ (0, 1/4)`).

For large `n`: `ν_n ≤ 1`, `ε_n ≤ 1` (so `R = ε_n⁻¹ ≥ 1`), and every `μ_n(z)`, `z ∈ [-1, 1]`, lies
in the fixed compact `K = [σ₀/2, (σ₀ + 1/4)/2] ⊂ ℂ` on which `Re μ > -1/4`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The window is a fixed compact set** (source 3631-3633, 5928-5950). -/
theorem annulus_window {dm dp : ℝ} (D : SeqData) (hst : D.RepairStanding dm dp) :
    ∃ Kc : Set ℂ, IsCompact Kc ∧ (∀ μ ∈ Kc, -(1 / 4) < μ.re) ∧
      ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 ∧ (D.level n).ε ≤ 1 ∧
        ∀ z ∈ Icc (-1 : ℝ) 1, ((D.mu n z : ℝ) : ℂ) ∈ Kc := by
  refine ⟨(fun x : ℝ => (x : ℂ)) '' Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2),
    isCompact_Icc.image Complex.continuous_ofReal, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hst.sigma_pos
    simp only [Complex.ofReal_re]
    linarith [hx.1]
  · filter_upwards [mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt,
      retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos D.coeff_ne]
      with n hμ hνε
    exact ⟨hνε.1, hνε.2, fun z hz => ⟨D.mu n z, hμ z hz, rfl⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
