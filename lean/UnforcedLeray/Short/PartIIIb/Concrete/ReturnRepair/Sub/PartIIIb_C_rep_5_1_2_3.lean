import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardYoungPointwise

/-!
# `PartIII-b:C/rep/5/1/2/3`: the stream transition `Y` on thin sources is supported below `S`

Source `the November 2 reference manuscript` lines 4161-4166 (young stream cutoff
`χ_y` vanishes for `s ≥ 1/ν`), 3905-3912, 5594-5600.
For large `n`, `1 / ν_n ≤ S_n = ε_n^{-b}`; by `IsWardTriple` (from `RegimePins.ward`) and
`wardYoungPointwise`, `(wardOps ..).1 (thinPart T)` vanishes a.e. above `S_n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `1/ν ≤ e^{a/ν}` for `ν ≤ a²/2`, `a = b d₋` (the output cut `S = ε^{-b}` exceeds `1/ν`). -/
private theorem inv_le_exp_of_small {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a) (h : ν ≤ a ^ 2 / 2) :
    1 / ν ≤ Real.exp (a / ν) := by
  have hx : 0 ≤ a / ν := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 1 / ν ≤ (a / ν) ^ 2 / 2 := by
    rw [div_pow, div_div, div_le_div_iff₀ hν (by positivity)]
    nlinarith [sq_nonneg ν]
  linarith [sq_nonneg (a / ν)]

/-- The output cut is at least `1/ν` on an actual level of small viscosity. -/
private theorem scut_ge_inv (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) {dm dp : ℝ}
    (hb : 0 < K.b)
    (hreg : UnforcedLeray.Short.IIb.BgRegime (L.params Pl) (-L.ν * Real.log L.ε) dm dp)
    (hν : L.ν ≤ (K.b * dm) ^ 2 / 2) : 1 / L.ν ≤ L.Scut K := by
  have hν0 : 0 < L.ν := L.ν_pos
  have hdm : 0 < dm := hreg.dm_pos
  have hdle := hreg.dm_le
  have hε : L.ε = Real.exp (-(-L.ν * Real.log L.ε) / L.ν) := hreg.eps_eq
  set d := -L.ν * Real.log L.ε with hd
  have hS : L.Scut K = Real.exp (K.b * d / L.ν) := by
    unfold ReturnLevel.Scut
    rw [Real.rpow_def_of_pos L.ε_pos]
    have : Real.log L.ε = -d / L.ν := by
      conv_lhs => rw [hε]
      rw [Real.log_exp]
    rw [this]
    congr 1
    ring
  rw [hS]
  refine (inv_le_exp_of_small hν0 (mul_pos hb hdm) hν).trans (Real.exp_le_exp.2 ?_)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdle hb.le) hν0.le

theorem wardOutSupported (D : SeqData) {dm dp : ℝ} (h : D.RepairStanding dm dp) :
    D.OutSupported wardThinFam := by
  have hapos : 0 < (D.K.b * dm) ^ 2 / 2 := by
    have := h.b_pos
    have := h.dm_pos
    positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ (D.K.b * dm) ^ 2 / 2 :=
    Filter.Tendsto.eventually_le_const hapos (retNu_tendsto D.σ₀ h.omega_ne)
  have hχ : IsYoungCutoff D.K.χy :=
    ⟨h.chiY.smooth, h.chiY.one, h.chiY.zero, h.chiY.range⟩
  filter_upwards [h.actual, h.pins, hsmall] with n hact hpins hs z hz T
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 (D.level n).ε_pos
  have hS : 1 / (D.level n).ν ≤ (D.level n).Scut D.K :=
    scut_ge_inv D.Pl D.K (D.level n) h.b_pos hact.regime hs
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy
      (D.level n).U (D.level n).pres := Classical.epsilon_spec (hpins z hz).ward
  have hY := (hW (thinPart T) _ _ EventuallyEq.rfl EventuallyEq.rfl).1
  have hpt := wardYoungPointwise (ν := (D.level n).ν) (μ := D.mu n z) (R := (D.level n).ε⁻¹)
    (c := cOf (D.level n).ν) (D.level n).U hν hR hχ
  filter_upwards [hY] with p hp hpS
  change ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T) : Chart → Merid) p = 0
  rw [hp]
  refine (hpt _ p ?_).1
  have h1 : 1 < p.1 * (D.level n).ν := (div_lt_iff₀ hν).1 (lt_of_le_of_lt hS hpS)
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
