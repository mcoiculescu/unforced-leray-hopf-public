import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3

/-!
# Part III-a, `PartIII-a:T21/2/3/2`: the change of variables `x = √a y` (SP 3036-3037)

`∫_{C_{c/√a}} (J_a⁻¹F) G = ∫_{C_c} F (physAdj a G)`: the substitution `x = √a • y` maps the cell
`C_{c/√a}` onto `C_c` with Jacobian `a` (`integral_comp_smul` on the plane, `finrank = 2`).
No integrability hypothesis is needed: both sides vanish for non-integrable data.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem pairingCoV : PairingCoV := by
  intro c a hc ha F G
  set s : ℝ := Real.sqrt a with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hsq : s ^ 2 = a := Real.sq_sqrt ha.le
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd : cellLen c a = c / s := rfl
  -- the integrand of the right-hand side, extended by zero off the cell `C_c`
  set H : ℝ × ℝ → ℂ := (B0579.cell c).indicator (fun x => F x * physAdj a G x) with hH_def
  -- membership: `s • y ∈ C_c ↔ y ∈ C_{c/s}`
  have hmem : ∀ y : ℝ × ℝ, s • y ∈ B0579.cell c ↔ y ∈ B0579.cell (c / s) := by
    intro y
    simp only [B0579.cell, Set.mem_prod, Set.mem_univ, and_true, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, Set.mem_Ico]
    have e : c / 2 = (c / s / 2) * s := by field_simp
    have e' : -(c / 2) = -(c / s / 2) * s := by rw [e]; ring
    rw [e', e]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  -- pointwise identity
  have hpt : ∀ y : ℝ × ℝ, (a : ℂ) * H (s • y) =
      (B0579.cell (c / s)).indicator (fun y => JscaleInv a F y * G y) y := by
    intro y
    by_cases hy : y ∈ B0579.cell (c / s)
    · have hx : s • y ∈ B0579.cell c := (hmem y).2 hy
      have e : s • y = (s * y.1, s * y.2) := by ext <;> simp [smul_eq_mul]
      have e1 : (s * y.1) / s = y.1 := by field_simp
      have e2 : (s * y.2) / s = y.2 := by field_simp
      rw [hH_def, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      unfold physAdj JscaleInv
      rw [e, e1, e2]
      rw [show ((a ^ 2 : ℝ) : ℂ) = (a : ℂ) ^ 2 by push_cast; ring]
      push_cast
      ring
    · have hx : s • y ∉ B0579.cell c := fun h => hy ((hmem y).1 h)
      rw [hH_def, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
      simp
  -- the scaling identity on the plane
  have hfr : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have key : ∫ x, H (s • x) = |((s ^ Module.finrank ℝ (ℝ × ℝ))⁻¹)| • ∫ x, H x :=
    MeasureTheory.Measure.integral_comp_smul volume H s
  rw [hfr, hsq, abs_of_pos (inv_pos.mpr ha)] at key
  calc ∫ y in B0579.cell (cellLen c a), JscaleInv a F y * G y
      = ∫ y, (B0579.cell (c / s)).indicator (fun y => JscaleInv a F y * G y) y :=
        (integral_indicator (B0579.measurableSet_cell _)).symm
    _ = ∫ y, (a : ℂ) * H (s • y) := by
        congr 1; funext y; exact (hpt y).symm
    _ = (a : ℂ) * ∫ y, H (s • y) := integral_const_mul _ _
    _ = (a : ℂ) * ((a⁻¹ : ℝ) • ∫ x, H x) := by rw [key]
    _ = ∫ x, H x := by
        rw [Complex.real_smul]
        push_cast
        field_simp
    _ = ∫ x in B0579.cell c, F x * physAdj a G x :=
        integral_indicator (B0579.measurableSet_cell c)

end UnforcedLeray.Short.IIIa
