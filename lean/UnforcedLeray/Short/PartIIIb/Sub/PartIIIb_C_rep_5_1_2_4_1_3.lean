import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3`: the chart bin bound of the Ward `Y` majorant

Source `the November 2 reference manuscript` 5585-5593.

`WardYMajBinCore` is the analytic content with explicit constants, free of `ν`, `ε` (it is stated for
the ring parameter `R = ε⁻¹` and the cell length `c`): the constant is `C₀(δ) (1 + c/R) R^{-3/2} s_j^{5/4}`.
The factor `1 + c/R` comes from the periodic fold of the phase `q` (the `l`-integral of the majorant
sweeps the phase by `R log l`, see the task spec); in the sequence `c = ν⁻²`, `R = ε⁻¹`, `ε ≤ 1`.

`wardYMajBinSeq_of` derives the sequence statement `WardYMajBinSeq` from the core.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Core of the bin bound** (source 5585-5593).  For `0 < δ < log(12/11)`, `h = δ/4`, there is `C₀`
such that for all `R, c > 0`, every output bin `j` (upper age `s_j = S e^{-hj}`) and every measurable
chart source `g` (no vanishing hypothesis: the radial gap `ϱ z < θ ϱ y`, `θ = e^{-δ/2}`, built into
`wardYKerMaj` forces the source age `t' > e^δ s > e^{δ-h} s_j` for every output `y` in the bin):
`‖wardYChartMaj‖_{L²(bin, ageμ c (-3/2))} ≤ C₀ (1 + c/R) R^{-3/2} s_j^{5/4} · N₀(e^{δ-h}s_j)`. -/
def WardYMajBinCore : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < Real.log (12 / 11) → ∃ C0 : ℝ, ∀ (R c S : ℝ), 0 < R → 0 < c →
    ∀ (j : ℕ) (g : Chart → Ten3), Measurable g →
      (∫⁻ p in binSet S (δ / 4) j,
          wardYChartMaj R c (Real.exp (-(δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C0 * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) *
          ageMass c (Real.exp (δ - δ / 4) * binUpper S (δ / 4) j) g

/-- `WardYMajBin` for `0 < ν ≤ 1`, `0 < ε ≤ 1`, `c = ν⁻²` from the core. -/
theorem wardYMajBin_of_core (hcore : WardYMajBinCore) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < Real.log (12 / 11)) :
    ∃ (C : ℝ) (k : ℕ), ∀ ν ε S : ℝ, 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 ≤ S →
      WardYMajBin ν ε (cOf ν) δ (δ / 4) S C k := by
  obtain ⟨C0, hC0⟩ := hcore δ hδ hδ'
  refine ⟨2 * |C0|, 2, fun ν ε S hν hν1 hε hε1 hS => ?_⟩
  intro _ _ hc _ _ hh j g hg _
  have hc0 : 0 < cOf ν := by unfold cOf; positivity
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have h := hC0 ε⁻¹ (cOf ν) S hR hc0 j g hg
  rw [hh]
  refine h.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have e1 : ε⁻¹ ^ (-(3 / 2 : ℝ)) = ε ^ (3 / 2 : ℝ) := by
    rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le, neg_neg]
  rw [e1]
  have hcR : cOf ν / ε⁻¹ ≤ ν⁻¹ ^ 2 := by
    unfold cOf
    rw [div_inv_eq_mul, ← inv_pow]
    have : (ν ^ 2)⁻¹ * ε ≤ (ν ^ 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
    simpa using this
  have h1 : (1 : ℝ) ≤ ν⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ hν |>.2 hν1)
  have hfac : 1 + cOf ν / ε⁻¹ ≤ 2 * ν⁻¹ ^ 2 := by linarith
  have hB : 0 ≤ binUpper S (δ / 4) j ^ (5 / 4 : ℝ) := by
    unfold binUpper; exact Real.rpow_nonneg (mul_nonneg hS (Real.exp_pos _).le) _
  have hE : 0 ≤ ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hε.le _
  have hP : 0 ≤ ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ) := mul_nonneg hE hB
  have hk : C0 * (1 + cOf ν / ε⁻¹) ≤ 2 * |C0| * ν⁻¹ ^ 2 := by
    calc C0 * (1 + cOf ν / ε⁻¹) ≤ |C0| * (1 + cOf ν / ε⁻¹) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C0| * (2 * ν⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ = 2 * |C0| * ν⁻¹ ^ 2 := by ring
  calc C0 * (1 + cOf ν / ε⁻¹) * ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)
      = (C0 * (1 + cOf ν / ε⁻¹)) * (ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) := by ring
    _ ≤ (2 * |C0| * ν⁻¹ ^ 2) * (ε ^ (3 / 2 : ℝ) * binUpper S (δ / 4) j ^ (5 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hk hP
    _ = _ := by ring

/-- **Target**: `wardYMajBinSeq`, from the core. -/
theorem wardYMajBinSeq_of (D : SeqData) {dm dp : ℝ} (hcore : WardYMajBinCore) :
    D.WardYMajBinSeq dm dp := by
  intro hst
  obtain ⟨C, k, hCk⟩ := wardYMajBin_of_core hcore hst.δ_pos hst.δ_lt
  refine ⟨C, k, ?_⟩
  have hle : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 ∧ retEps D.Pl D.σ₀ n ≤ 1 :=
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hle] with n hn
  have hS : 0 ≤ (D.level n).Scut D.K := by
    unfold ReturnLevel.Scut
    exact Real.rpow_nonneg (D.level n).ε_pos.le _
  exact hCk (D.level n).ν (D.level n).ε _ (D.level n).ν_pos hn.1 (D.level n).ε_pos hn.2 hS

end UnforcedLeray.Short.PartIIIb.Concrete

end
