import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_5
import UnforcedLeray.Units.B0147
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.StressDivLocal.BSBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.StressDivLocal.GaussCell

/-!
# Part I, task `PartI:T08/4/1/1/5/4` (`QcJetLocalL2`)

Source `the November 2 reference manuscript` lines 326-335 and 2217-2234.

Take `ε = 1`. For `r > 0` with `|r - s| < 1`, the width `a = heatWidth ν r` lies in `[1, a₂]`
with `a₂ = 1 + ν (s + 1)`. The word derivative of `Q_c^{kl}` is `λ⁶ λ^|w| H₁(λc, λx)` with
`H₁` a member of `BS`, and `qcJet_BS_bound_loc` gives a transverse Gaussian bound uniform in
`L ≥ c/√a₂`. Then `qcJet_gauss_cell` gives the `L²(cell)` bound, with `K` independent of `r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem qcJetLocalL2_proof : UnforcedLeray.Short.PartI.QcJetLocalL2 := by
  intro ν c hν hc s hs w k l
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := hc0.ne'
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℝ, a2 = 1 + ν * (s + 1) := ⟨_, rfl⟩
  have ha2p : 0 < a2 := by
    have := mul_pos hν (by linarith : (0 : ℝ) < s + 1)
    rw [ha2]; linarith
  have hsa2 : 0 < Real.sqrt a2 := Real.sqrt_pos.mpr ha2p
  obtain ⟨H₁, hH₁, hw⟩ := (UnforcedLeray.B0147.BS.pair (UnforcedLeray.B0147.GP_U k)
    (UnforcedLeray.B0147.GP_U l)).deriv_word w
  have hL₀ : 0 < c * (Real.sqrt a2)⁻¹ := mul_pos hc0 (inv_pos.mpr hsa2)
  obtain ⟨C, γ, hC, hγ, hb⟩ := qcJet_BS_bound_loc hH₁ hL₀
  have hb2 : 0 < γ / a2 := div_pos hγ ha2p
  refine ⟨1, one_pos, ∫ z : Plane in UnforcedLeray.Cyl.cell c,
      (C * Real.exp (-((γ / a2) * z.2 ^ 2))) ^ 2, fun r hr hrs => ?_⟩
  have hrs' := abs_lt.mp hrs
  have hrlt : r < s + 1 := by linarith [hrs'.2]
  have hnr : ν * r ≤ ν * (s + 1) := mul_le_mul_of_nonneg_left hrlt.le hν.le
  set a := UnforcedLeray.B0113.heatWidth ν r with ha_def
  have hadef : a = 1 + ν * r := rfl
  have hrw : 1 ≤ a := by
    rw [hadef]; have := mul_pos hν hr; linarith
  have hra : a ≤ a2 := by rw [hadef, ha2]; linarith
  have ha : 0 < a := by linarith
  have hl : 0 < UnforcedLeray.B0147.lam a := UnforcedLeray.B0147.lam_pos ha
  have hl1 : UnforcedLeray.B0147.lam a ≤ 1 := by
    unfold UnforcedLeray.B0147.lam
    apply inv_le_one_of_one_le₀
    rw [Real.one_le_sqrt]; exact hrw
  have hlsq : UnforcedLeray.B0147.lam a ^ 2 = a⁻¹ := UnforcedLeray.B0147.lam_sq ha
  have hLne : UnforcedLeray.B0147.lam a * c ≠ 0 := (mul_pos hl hc0).ne'
  have hLL : c * (Real.sqrt a2)⁻¹ ≤ UnforcedLeray.B0147.lam a * c := by
    have h1 : (Real.sqrt a2)⁻¹ ≤ UnforcedLeray.B0147.lam a :=
      inv_anti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hra)
    calc c * (Real.sqrt a2)⁻¹ ≤ c * UnforcedLeray.B0147.lam a :=
          mul_le_mul_of_nonneg_left h1 hc0.le
      _ = UnforcedLeray.B0147.lam a * c := mul_comm _ _
  have hF_eq : UnforcedLeray.B0151.derivWord w
      (fun x => UnforcedLeray.B0146.crossStress ν c r x k l) = fun x =>
        UnforcedLeray.B0147.lam a ^ 6 * UnforcedLeray.B0147.lam a ^ w.length *
          H₁ (UnforcedLeray.B0147.lam a * c)
            (UnforcedLeray.B0147.lam a * x.1, UnforcedLeray.B0147.lam a * x.2) :=
    UnforcedLeray.B0147.derivWord_cross (ν := ν) (c := c) (s := r) hcne ha k l w hw
  have hpt : ∀ z : Plane, |UnforcedLeray.B0147.lam a ^ 6 * UnforcedLeray.B0147.lam a ^ w.length *
      H₁ (UnforcedLeray.B0147.lam a * c)
        (UnforcedLeray.B0147.lam a * z.1, UnforcedLeray.B0147.lam a * z.2)| ≤
      C * Real.exp (-((γ / a2) * z.2 ^ 2)) := by
    intro z
    have hp6 : UnforcedLeray.B0147.lam a ^ 6 ≤ 1 := pow_le_one₀ hl.le hl1
    have hpw : UnforcedLeray.B0147.lam a ^ w.length ≤ 1 := pow_le_one₀ hl.le hl1
    have hp : UnforcedLeray.B0147.lam a ^ 6 * UnforcedLeray.B0147.lam a ^ w.length ≤ 1 := by
      calc UnforcedLeray.B0147.lam a ^ 6 * UnforcedLeray.B0147.lam a ^ w.length ≤ 1 * 1 :=
            mul_le_mul hp6 hpw (pow_nonneg hl.le _) zero_le_one
        _ = 1 := one_mul 1
    have hp0 : 0 ≤ UnforcedLeray.B0147.lam a ^ 6 * UnforcedLeray.B0147.lam a ^ w.length :=
      mul_nonneg (pow_nonneg hl.le _) (pow_nonneg hl.le _)
    have hHb : |H₁ (UnforcedLeray.B0147.lam a * c)
        (UnforcedLeray.B0147.lam a * z.1, UnforcedLeray.B0147.lam a * z.2)| ≤
        C * Real.exp (-(γ * (UnforcedLeray.B0147.lam a * z.2) ^ 2)) :=
      hb (UnforcedLeray.B0147.lam a * c) hLL
        (UnforcedLeray.B0147.lam a * z.1, UnforcedLeray.B0147.lam a * z.2)
    have e1 : γ * (UnforcedLeray.B0147.lam a * z.2) ^ 2 = γ * a⁻¹ * z.2 ^ 2 := by
      rw [mul_pow, hlsq]; ring
    have hinv : a2⁻¹ ≤ a⁻¹ := inv_anti₀ ha hra
    have hcmp : γ * a2⁻¹ * z.2 ^ 2 ≤ γ * a⁻¹ * z.2 ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hγ.le) (sq_nonneg _)
    have hexp : Real.exp (-(γ * (UnforcedLeray.B0147.lam a * z.2) ^ 2)) ≤
        Real.exp (-((γ / a2) * z.2 ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [e1, div_eq_mul_inv]
      exact neg_le_neg hcmp
    rw [abs_mul, abs_of_nonneg hp0]
    calc UnforcedLeray.B0147.lam a ^ 6 * UnforcedLeray.B0147.lam a ^ w.length *
          |H₁ (UnforcedLeray.B0147.lam a * c)
            (UnforcedLeray.B0147.lam a * z.1, UnforcedLeray.B0147.lam a * z.2)|
        ≤ 1 * |H₁ (UnforcedLeray.B0147.lam a * c)
            (UnforcedLeray.B0147.lam a * z.1, UnforcedLeray.B0147.lam a * z.2)| :=
          mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = |H₁ (UnforcedLeray.B0147.lam a * c)
            (UnforcedLeray.B0147.lam a * z.1, UnforcedLeray.B0147.lam a * z.2)| := one_mul _
      _ ≤ C * Real.exp (-(γ * (UnforcedLeray.B0147.lam a * z.2) ^ 2)) := hHb
      _ ≤ C * Real.exp (-((γ / a2) * z.2 ^ 2)) := mul_le_mul_of_nonneg_left hexp hC
  have hcont : Continuous (fun x : Plane => UnforcedLeray.B0147.lam a ^ 6 *
      UnforcedLeray.B0147.lam a ^ w.length *
        H₁ (UnforcedLeray.B0147.lam a * c)
          (UnforcedLeray.B0147.lam a * x.1, UnforcedLeray.B0147.lam a * x.2)) :=
    continuous_const.mul ((hH₁.continuous hLne).comp
      (f := fun x : Plane => (UnforcedLeray.B0147.lam a * x.1, UnforcedLeray.B0147.lam a * x.2))
      (by fun_prop))
  have hG := qcJet_gauss_cell (c := c) (A := C) (b := γ / a2) hb2 hcont hpt
  have eQ : (fun x => UnforcedLeray.Train.Qc ν c r x k l) =
      fun x => UnforcedLeray.B0146.crossStress ν c r x k l := by
    rw [UnforcedLeray.Train.Qc_fun_eq]
  rw [eQ, hF_eq]
  exact hG

end UnforcedLeray.Short.PartI
