import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_1
import UnforcedLeray.Units.B0424.Calc

/-!


`adjTest χ τ₀ φ c = cmb c̃ m̃ b̃ φ · e_c` with `c̃(τ) = e^{-3t/2} χ(t)`, `m̃(τ) = 1 - e^{-t}`,
`b̃(τ) = e^{-t/2}`, `t = τ₀ - τ`. The forward operator `L₀ = T₀ - νΔ - ½` acts on `s e_c` by
`(μ̄ + L₀)(s e_c) = (μ̄ s + ∂_τ s - ½ y·∇s - νΔs - ½ s) e_c`, and the chain rule of
`Units/B0424/Calc.lean` (`fderiv_cmb_time`, `fderiv_cmb_space`, `sLap_cmb`) gives the stated
scalar: the `y·∇` terms cancel, `Δ_y` contributes `e^{-t}`, `∂_τ` contributes `-e^{-t}φ_θ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.B0424

/-- The forward operator on a scalar times a constant vector:
`L₀ (s e) = (∂_τ s - ½ ∑ yⱼ ∂ⱼ s - νΔs - ½ s) e`. -/
theorem adj_L0_smul_e {S : ℝ × Space → ℝ} (hS : ContDiff ℝ ∞ S) (ν : ℝ) (e : CVec3)
    (p : ℝ × Space) :
    B0411.L0 ν (fun q => S q • e) p =
      (dτ S p - (1 / 2 : ℝ) * (∑ j : Fin 3, p.2 j * sD j (S : PS 3 → ℝ) p) -
        ν * sLap (S : PS 3 → ℝ) p - (1 / 2 : ℝ) * S p) • e := by
  have hdt : dτ (fun q => S q • e) p = dτ S p • e := by
    simp only [dτ]
    rw [fderiv_smul_e hS]
  have hrad : radialT (fun q => S q • e) p = (∑ j : Fin 3, p.2 j * sD j (S : PS 3 → ℝ) p) • e := by
    simp only [radialT]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dy_smul_e hS, smul_smul]
  have hl : lapT (fun q => S q • e) p = sLap (S : PS 3 → ℝ) p • e := lapT_smul_e hS e p
  simp only [B0411.L0, B0411.T0, hdt, hrad, hl]
  module

/-- The complex scalar and the real scalar multiples of a constant vector agree. -/
theorem adj_coe_smul (r : ℝ) (e : CVec3) : (r : ℂ) • e = r • e := by
  ext i
  simp [Complex.real_smul]

/-- A linear split of the derivative along `(a, b • y)`. -/
theorem adj_lin (φ : PS 3 → ℝ) (X : PS 3) (a b' : ℝ) (y : Space) :
    fderiv ℝ φ X (a, b' • y) = a * tD φ X + b' * fderiv ℝ φ X (0, y) := by
  have h : ((a, b' • y) : ℝ × Space) = a • ((1 : ℝ), (0 : Space)) + b' • ((0 : ℝ), y) := by
    ext <;> simp
  simp only [h, map_add, map_smul, smul_eq_mul]
  rfl

/-- The time derivative of `cmb`. -/
theorem adj_cmb_time {c m b : ℝ → ℝ} {c' m' b' : ℝ} {φ : PS 3 → ℝ} (hφs : ContDiff ℝ ∞ φ)
    (hc : ContDiff ℝ ∞ c) (hm : ContDiff ℝ ∞ m) (hb : ContDiff ℝ ∞ b) (p : ℝ × Space)
    (hcd : HasDerivAt c c' p.1) (hmd : HasDerivAt m m' p.1) (hbd : HasDerivAt b b' p.1) :
    dτ (B0424.cmb c m b φ) p = c' * φ (m p.1, b p.1 • p.2) + c p.1 *
      (m' * tD φ (m p.1, b p.1 • p.2) + b' * fderiv ℝ φ (m p.1, b p.1 • p.2) (0, p.2)) := by
  have hd : DifferentiableAt ℝ (B0424.cmb c m b φ) p :=
    ((B0424.contDiff_cmb hφs hc hm hb).differentiable (by simp)) p
  have hΨd : DifferentiableAt ℝ φ (m p.1, b p.1 • p.2) := (hφs.differentiable (by simp)) _
  show fderiv ℝ (B0424.cmb c m b φ) p (1, 0) = _
  rw [B0424.fderiv_cmb_time hd hΨd hcd hmd hbd, adj_lin]

/-- The radial sum of `cmb`. -/
theorem adj_cmb_space {c m b : ℝ → ℝ} {φ : PS 3 → ℝ} (hφs : ContDiff ℝ ∞ φ)
    (hc : ContDiff ℝ ∞ c) (hm : ContDiff ℝ ∞ m) (hb : ContDiff ℝ ∞ b) (p : ℝ × Space) :
    (∑ j : Fin 3, p.2 j * sD j (B0424.cmb c m b φ) p) =
      c p.1 * b p.1 * fderiv ℝ φ (m p.1, b p.1 • p.2) (0, p.2) := by
  have hd : DifferentiableAt ℝ (B0424.cmb c m b φ) p :=
    ((B0424.contDiff_cmb hφs hc hm hb).differentiable (by simp)) p
  have hΨd : DifferentiableAt ℝ φ (m p.1, b p.1 • p.2) := (hφs.differentiable (by simp)) _
  have hs : ∀ j : Fin 3, sD j (B0424.cmb c m b φ) p =
      c p.1 * (b p.1 * fderiv ℝ φ (m p.1, b p.1 • p.2) (0, coordinateVector j)) :=
    fun j => B0424.fderiv_cmb_space hd hΨd _
  have e1 : ∀ j : Fin 3, p.2 j * (c p.1 * (b p.1 *
      fderiv ℝ φ (m p.1, b p.1 • p.2) (0, coordinateVector j))) =
      (c p.1 * b p.1) * (p.2 j * fderiv ℝ φ (m p.1, b p.1 • p.2) (0, coordinateVector j)) :=
    fun j => by ring
  simp only [hs, e1]
  rw [← Finset.mul_sum, sum_mul_fderiv_coord]

theorem adjTestCalc : AdjTestCalc := by
  intro ν μ χ hχ τ₀ φ hφ c p
  have hφs : ContDiff ℝ ∞ φ := hφ.1
  have hχs : ContDiff ℝ ∞ χ := hχ.smooth
  have ht : ContDiff ℝ ∞ (fun τ : ℝ => τ₀ - τ) := contDiff_const.sub contDiff_id
  have hc : ContDiff ℝ ∞ (fun τ : ℝ => Real.exp (-(3 * (τ₀ - τ) / 2)) * χ (τ₀ - τ)) :=
    (Real.contDiff_exp.comp
      (((contDiff_const.mul ht : ContDiff ℝ ∞ (fun τ : ℝ => (3 : ℝ) * (τ₀ - τ))).div_const 2).neg)).mul
      (hχs.comp ht)
  have hm : ContDiff ℝ ∞ (fun τ : ℝ => 1 - Real.exp (-(τ₀ - τ))) :=
    contDiff_const.sub (Real.contDiff_exp.comp ht.neg)
  have hb : ContDiff ℝ ∞ (fun τ : ℝ => Real.exp (-(τ₀ - τ) / 2)) :=
    Real.contDiff_exp.comp (ht.neg.div_const 2)
  have hτ : HasDerivAt (fun τ : ℝ => τ₀ - τ) (-1) p.1 := (hasDerivAt_id' p.1).const_sub τ₀
  have hτn : HasDerivAt (fun τ : ℝ => -(τ₀ - τ)) 1 p.1 := (hτ.neg).congr_deriv (by ring)
  have hu : HasDerivAt (fun τ : ℝ => -(3 * (τ₀ - τ) / 2)) (3 / 2) p.1 :=
    ((hτ.const_mul (3 : ℝ)).div_const 2).neg.congr_deriv (by ring)
  have hcd : HasDerivAt (fun τ : ℝ => Real.exp (-(3 * (τ₀ - τ) / 2)) * χ (τ₀ - τ))
      (Real.exp (-(3 * (τ₀ - p.1) / 2)) * (3 / 2) * χ (τ₀ - p.1) +
        Real.exp (-(3 * (τ₀ - p.1) / 2)) * (deriv χ (τ₀ - p.1) * (-1))) p.1 := by
    have h2 : HasDerivAt (fun τ : ℝ => χ (τ₀ - τ)) (deriv χ (τ₀ - p.1) * (-1)) p.1 :=
      ((hχs.differentiable (by simp)) (τ₀ - p.1)).hasDerivAt.comp p.1 hτ
    exact hu.exp.mul h2
  have hmd : HasDerivAt (fun τ : ℝ => 1 - Real.exp (-(τ₀ - τ)))
      (-(Real.exp (-(τ₀ - p.1)))) p.1 :=
    ((hτn.exp).const_sub 1).congr_deriv (by ring)
  have hbd : HasDerivAt (fun τ : ℝ => Real.exp (-(τ₀ - τ) / 2))
      (Real.exp (-(τ₀ - p.1) / 2) * (1 / 2)) p.1 :=
    ((hτn.div_const 2).exp).congr_deriv (by ring)
  have hS := B0424.contDiff_cmb hφs hc hm hb
  have hdτ := adj_cmb_time hφs hc hm hb p hcd hmd hbd
  have hsp := adj_cmb_space hφs hc hm hb p
  have hl := B0424.sLap_cmb hφs hc hm hb p
  have hsq : Real.exp (-(τ₀ - p.1) / 2) ^ 2 = Real.exp (-(τ₀ - p.1)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hA : adjTest χ τ₀ φ c = fun q => B0424.cmb (fun τ : ℝ => Real.exp (-(3 * (τ₀ - τ) / 2)) *
      χ (τ₀ - τ)) (fun τ : ℝ => 1 - Real.exp (-(τ₀ - τ))) (fun τ : ℝ => Real.exp (-(τ₀ - τ) / 2))
      φ q • EuclideanSpace.single c (1 : ℂ) := by
    funext q
    exact adj_coe_smul _ _
  rw [hA, Pi.add_apply, Pi.smul_apply, adj_L0_smul_e hS ν (EuclideanSpace.single c (1 : ℂ)) p,
    hdτ, hsp, hl, hsq]
  simp only [← adj_coe_smul, smul_smul, ← add_smul]
  congr 1
  simp only [B0424.cmb]
  push_cast
  ring

end UnforcedLeray.Short.PartIIa
