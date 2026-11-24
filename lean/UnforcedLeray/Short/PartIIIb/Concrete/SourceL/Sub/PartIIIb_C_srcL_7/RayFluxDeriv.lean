import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rayFluxDeriv : RayFluxDeriv := by
  intro Z y ρ hr hZd hG hdiv
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℝ, u0 = y 0 / cylR y := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ, u1 = y 1 / cylR y := ⟨_, rfl⟩
  have hpyth : u0 ^ 2 + u1 ^ 2 = 1 := by
    have h2 : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := cylR_sq_sum y
    have hne : cylR y ≠ 0 := hr.ne'
    rw [hu0, hu1, div_pow, div_pow, ← add_div, ← h2, div_self (pow_ne_zero 2 hne)]
  have hp0 : rayPt y ρ 0 = ρ * u0 := by simp [rayPt, hu0]
  have hp1 : rayPt y ρ 1 = ρ * u1 := by simp [rayPt, hu1]
  have hray : HasDerivAt (rayPt y) ![u0, u1, 0] ρ := by
    have hf : rayPt y = fun x => ![x * u0, x * u1, y 2] := by
      funext x
      simp [rayPt, hu0, hu1]
    rw [hf]
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using (hasDerivAt_id ρ).mul_const u0
    · simpa using (hasDerivAt_id ρ).mul_const u1
    · simpa using hasDerivAt_const ρ (y 2)
  have hF : rayFlux Z y = fun x => x * (u0 * Z (rayPt y x) 0 + u1 * Z (rayPt y x) 1) := by
    funext x
    unfold rayFlux
    rw [hu0, hu1]
  have hZd' : HasFDerivAt Z (fderiv ℝ Z (rayPt y ρ)) (rayPt y ρ) := hZd.hasFDerivAt
  have hcomp : HasDerivAt (fun x => Z (rayPt y x)) (fderiv ℝ Z (rayPt y ρ) ![u0, u1, 0]) ρ :=
    hZd'.comp_hasDerivAt ρ hray
  have hc0 := hasDerivAt_pi.1 hcomp 0
  have hc1 := hasDerivAt_pi.1 hcomp 1
  have hprod := (hasDerivAt_id' ρ).mul ((hc0.const_mul u0).add (hc1.const_mul u1))
  set A := fderiv ℝ Z (rayPt y ρ) with hA
  have hlin : ∀ a b c : ℝ,
      A ![a, b, c] = a • A (Pi.single 0 1) + b • A (Pi.single 1 1) + c • A (Pi.single 2 1) := by
    intro a b c
    have hv : (![a, b, c] : Vec3) =
        a • (Pi.single 0 1 : Vec3) + b • (Pi.single 1 1 : Vec3) + c • (Pi.single 2 1 : Vec3) := by
      funext i
      fin_cases i <;> simp
    rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
  have hD0 : A ![u0, u1, 0] 0 = u0 * A (Pi.single 0 1) 0 + u1 * A (Pi.single 1 1) 0 := by
    rw [hlin]
    simp
  have hD1 : A ![u0, u1, 0] 1 = u0 * A (Pi.single 0 1) 1 + u1 * A (Pi.single 1 1) 1 := by
    rw [hlin]
    simp
  have hGc := hG
  rw [hlin] at hGc
  have g0 := congrFun hGc 0
  have g1 := congrFun hGc 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one] at g0 g1
  simp only [hp0, hp1] at g0 g1
  have hdiv' : A (Pi.single 0 1) 0 + A (Pi.single 1 1) 1 + A (Pi.single 2 1) 2 = 0 := by
    rw [Fin.sum_univ_three] at hdiv
    exact hdiv
  rw [hF]
  refine hprod.congr_deriv ?_
  rw [hD0, hD1]
  simp only [Pi.add_apply]
  linear_combination (-u0) * g1 + u1 * g0 + ρ * hdiv' +
    ρ * (A (Pi.single 0 1) 0 + A (Pi.single 1 1) 1) * hpyth

end UnforcedLeray.Short.PartIIIb.Concrete
