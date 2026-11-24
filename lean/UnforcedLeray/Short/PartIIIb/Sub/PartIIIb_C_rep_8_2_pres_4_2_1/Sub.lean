import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9

/-!
# Decomposition of `coefChgSup` (task `PartIII-b:C/rep/8/2/pres/4/2/1`)

Source `the November 2 reference manuscript`
2715-2725 (`sup √s W|v| ≤ P_ν`), 5007-5008 (`δ_U = ‖U - U_raw‖_{W^{1,∞}}`), 5134-5139.

`|U| + |V| + |U_raw| ≤ 2|U_raw| + |U - U_raw| + |V|`.  The first is the sup bound of the raw background
(`RawSupBound`, source 2715-2725 and background (2.15)), the third is the sup bound of `V = U_raw + E_εα`
(`VSupBound`, source 2389-2390, 2719-2725), the second is `RhoW1` (`δ_U ≤ P_νρ`, task
`PartIII-b:C/rep/9/2`) together with `ρ ≤ 1` (proved below from the regime).
-/

open Filter Set Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Sup bound of the raw background** (source 2715-2725: `sup √s W|v| ≤ P_ν` with `W ≥ 1` and
`U_raw = √s(v₁e_r + (v₂ + εH)e_z)`, 2076-2077; background (2.15) `‖U_raw‖_{W^{2,∞}} ≤ P_ν`):
for large `n`, `|U_raw(τ, y)| ≤ Cν^{-k}` at every phase and point. -/
def RawSupBound (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ (τ : ℝ) (y : Space),
    ‖rawU D.Pl (D.level n) τ y‖ ≤ C * (D.level n).ν⁻¹ ^ k

/-- **Sup bound of the entrance background `V = U_raw + E_εα`** (source 2389-2390:
`‖E_εα‖_{W^{j,∞}} ≤ P_ν|α|`, `|α| ≤ P_ν e^{m₀/ν}ε ≤ P_ν`; with `RawSupBound`, 2715-2725): for
large `n`, `|V(τ, y)| ≤ Cν^{-k}` at every phase and point. -/
def VSupBound (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ (τ : ℝ) (y : Space),
    ‖(D.level n).V τ y‖ ≤ C * (D.level n).ν⁻¹ ^ k

/-- `ρ = ε^{3/11}e^{m₀/ν} ≤ 1` at a regime level with `m₀ ≤ 3d₋/11` (`ε = e^{-d/ν}`, `d ≥ d₋`). -/
theorem rhoRep_le_one {K : ReturnConsts} {L : ReturnLevel} {d dm : ℝ}
    (hε : L.ε = Real.exp (-d / L.ν)) (hd : dm ≤ d) (hm : K.m0 ≤ 3 * dm / 11) :
    rhoRep K L ≤ 1 := by
  have hν := L.ν_pos
  unfold rhoRep
  rw [hε, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_one_iff]
  have : -d / L.ν * (3 / 11) + K.m0 / L.ν = (K.m0 - 3 * d / 11) / L.ν := by
    field_simp; ring
  rw [this]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le

/-- `ρ ≤ 1` for large `n` under the repair standing. -/
theorem rhoRep_le_one_eventually (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, rhoRep D.K (D.level n) ≤ 1 := by
  filter_upwards [hst.actual] with n hn
  have h := hn.regime
  exact rhoRep_le_one (d := _) h.eps_eq h.dm_le (by have := hst.m0_ball; have := hst.m0_pos; linarith)

theorem coefChgSup_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : RawSupBound D) (h2 : D.RhoW1) (h3 : VSupBound D) : CoefChgSup D := by
  obtain ⟨C1, k1, hA⟩ := h1
  obtain ⟨C2, k2, hB⟩ := h2
  obtain ⟨C3, k3, hC⟩ := h3
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  refine ⟨2 * |C1| + |C2| + |C3|, max k1 (max k2 k3), ?_⟩
  filter_upwards [hA, hB, hC, hν1, rhoRep_le_one_eventually D hst] with n hA hB hC hν hρ p _
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have ha : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν⟩
  set a := (D.level n).ν⁻¹ with hadef
  have hρ0 : 0 ≤ rhoRep D.K (D.level n) := by
    unfold rhoRep
    exact mul_nonneg (Real.rpow_nonneg (D.level n).ε_pos.le _) (Real.exp_pos _).le
  have hapos : 0 < a := by linarith
  set τ := NearInst.chartTau (D.level n).ε⁻¹ p
  set y := NearInst.chartY (D.level n).ε⁻¹ p
  have hr : ‖rawU D.Pl (D.level n) τ y‖ ≤ |C1| * a ^ (max k1 (max k2 k3)) := by
    refine (hA τ y).trans ?_
    calc C1 * a ^ k1 ≤ |C1| * a ^ k1 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C1| * a ^ (max k1 (max k2 k3)) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (le_max_left _ _)) (abs_nonneg _)
  have hd : ‖(D.level n).U τ y - rawU D.Pl (D.level n) τ y‖ ≤ |C2| * a ^ (max k1 (max k2 k3)) := by
    have h0 := (hB τ y).1
    have e : ((D.level n).params D.Pl).raw τ y = rawU D.Pl (D.level n) τ y := rfl
    rw [e] at h0
    refine h0.trans ?_
    have hk : a ^ k2 ≤ a ^ (max k1 (max k2 k3)) := pow_le_pow_right₀ ha ((le_max_left k2 k3).trans (le_max_right _ _))
    calc C2 * a ^ k2 * rhoRep D.K (D.level n) ≤ |C2| * a ^ k2 * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hρ hρ0
            (by positivity)
      _ ≤ |C2| * a ^ (max k1 (max k2 k3)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  have hU : ‖(D.level n).U τ y‖ ≤ ‖rawU D.Pl (D.level n) τ y‖ +
      ‖(D.level n).U τ y - rawU D.Pl (D.level n) τ y‖ := by
    calc ‖(D.level n).U τ y‖ = ‖rawU D.Pl (D.level n) τ y +
          ((D.level n).U τ y - rawU D.Pl (D.level n) τ y)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have hV : ‖(D.level n).V τ y‖ ≤ |C3| * a ^ (max k1 (max k2 k3)) := by
    refine (hC τ y).trans ?_
    calc C3 * a ^ k3 ≤ |C3| * a ^ k3 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C3| * a ^ (max k1 (max k2 k3)) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ ha ((le_max_right k2 k3).trans (le_max_right _ _))) (abs_nonneg _)
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
