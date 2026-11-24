import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise.Commutator.CpdMul

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/3/2` (`commFormula`): the exact Leibniz formula for the
commutator with the cutoff `φ(η/L)`.

Source: `the November 2 reference manuscript` lines 1923-1927.
Real rescaled cutoff derivatives are `fmlR φ L k t = L⁻¹^k * iteratedDeriv k φ t`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Real rescaled cutoff derivative `L⁻¹^k φ^{(k)}(t)`. -/
def fmlR (φ : ℝ → ℝ) (L : ℝ) (k : ℕ) (t : ℝ) : ℝ := L⁻¹ ^ k * iteratedDeriv k φ t

theorem fml_perp0 (ψ : Coord → ℂ) (z : Coord) : perpC ψ z 0 = cpdC 2 ψ z := rfl

theorem fml_perp1 (ψ : Coord → ℂ) (z : Coord) : perpC ψ z 1 = -cpdC 1 ψ z := rfl

theorem fmlR_one (φ : ℝ → ℝ) (L t : ℝ) : fmlR φ L 1 t = L⁻¹ * deriv φ t := by
  simp [fmlR, iteratedDeriv_one]

theorem fmlR_deriv (φ : ℝ → ℝ) (L : ℝ) (k : ℕ) (t : ℝ) :
    L⁻¹ * deriv (fmlR φ L k) t = fmlR φ L (k + 1) t := by
  unfold fmlR
  simp only [deriv_const_mul_field', iteratedDeriv_succ]
  ring

theorem fml_iter_smooth (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k φ)
  | 0 => by
    rw [iteratedDeriv_zero]
    exact hφ
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp (fml_iter_smooth φ hφ k)).2

@[fun_prop]
theorem fmlR_smooth (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (fmlR φ L k) := by
  unfold fmlR
  exact contDiff_const.mul (fml_iter_smooth φ hφ k)

@[fun_prop]
theorem fml_R_pt_smooth (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (fun y : Coord => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    ((fmlR_smooth φ hφ L k).comp ((contDiff_snd.comp contDiff_snd).div_const L))

@[fun_prop]
theorem fml_phi_pt_smooth (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) :
    ContDiff ℝ ∞ (fun y : Coord => ((φ (y.2.2 / L) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hφ.comp ((contDiff_snd.comp contDiff_snd).div_const L))

@[fun_prop]
theorem fml_cpd_smooth (j : Fin 3) (G : Coord → ℂ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (cpdC j G) := by
  unfold cpdC
  exact (hG.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

theorem fml_cpd_add (j : Fin 3) (A B : Coord → ℂ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    cpdC j (fun y => A y + B y) = fun y => cpdC j A y + cpdC j B y := by
  funext y
  unfold cpdC
  rw [show (fun z => A z + B z) = A + B from rfl,
    fderiv_add (hA.differentiable (by simp) y) (hB.differentiable (by simp) y)] <;> rfl

theorem fml_cpd_neg (j : Fin 3) (G : Coord → ℂ) :
    cpdC j (fun y => -G y) = fun y => -cpdC j G y := by
  funext y
  unfold cpdC
  rw [show (fun z => -G z) = -G from rfl, fderiv_neg] <;> rfl

theorem fml_phi0 (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (G : Coord → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    cpdC 0 (fun y : Coord => ((φ (y.2.2 / L) : ℝ) : ℂ) * G y) =
      fun y => ((φ (y.2.2 / L) : ℝ) : ℂ) * cpdC 0 G y := by
  rw [commCpdMul φ hφ L G hG 0]
  funext y
  simp [eq_false (show ¬ ((0 : Fin 3) = 2) by decide)]

theorem fml_phi1 (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (G : Coord → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    cpdC 1 (fun y : Coord => ((φ (y.2.2 / L) : ℝ) : ℂ) * G y) =
      fun y => ((φ (y.2.2 / L) : ℝ) : ℂ) * cpdC 1 G y := by
  rw [commCpdMul φ hφ L G hG 1]
  funext y
  simp [eq_false (show ¬ ((1 : Fin 3) = 2) by decide)]

theorem fml_phi2 (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (G : Coord → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    cpdC 2 (fun y : Coord => ((φ (y.2.2 / L) : ℝ) : ℂ) * G y) =
      fun y => ((φ (y.2.2 / L) : ℝ) : ℂ) * cpdC 2 G y +
        ((fmlR φ L 1 (y.2.2 / L) : ℝ) : ℂ) * G y := by
  rw [commCpdMul φ hφ L G hG 2]
  funext y
  rw [if_pos (rfl : (2 : Fin 3) = 2), fmlR_one]

theorem fml_R0 (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (k : ℕ) (G : Coord → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    cpdC 0 (fun y : Coord => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ) * G y) =
      fun y => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ) * cpdC 0 G y := by
  rw [commCpdMul (fmlR φ L k) (fmlR_smooth φ hφ L k) L G hG 0]
  funext y
  simp [eq_false (show ¬ ((0 : Fin 3) = 2) by decide)]

theorem fml_R1 (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (k : ℕ) (G : Coord → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    cpdC 1 (fun y : Coord => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ) * G y) =
      fun y => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ) * cpdC 1 G y := by
  rw [commCpdMul (fmlR φ L k) (fmlR_smooth φ hφ L k) L G hG 1]
  funext y
  simp [eq_false (show ¬ ((1 : Fin 3) = 2) by decide)]

theorem fml_R2 (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ) (k : ℕ) (G : Coord → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    cpdC 2 (fun y : Coord => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ) * G y) =
      fun y => ((fmlR φ L k (y.2.2 / L) : ℝ) : ℂ) * cpdC 2 G y +
        ((fmlR φ L (k + 1) (y.2.2 / L) : ℝ) : ℂ) * G y := by
  rw [commCpdMul (fmlR φ L k) (fmlR_smooth φ hφ L k) L G hG 2]
  funext y
  rw [if_pos (rfl : (2 : Fin 3) = 2), fmlR_deriv]

set_option maxHeartbeats 1000000 in
theorem fml_comp0 (ν : ℝ) (μ : ℂ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ)
    (Ψ : Coord → ℂ) (hΨ : ContDiff ℝ ∞ Ψ) (x : Coord) :
    flatTransposeC ν μ (perpC (fun y => ((φ (y.2.2 / L) : ℝ) : ℂ) * Ψ y)) x 0 -
          ((φ (x.2.2 / L) : ℝ) : ℂ) * flatTransposeC ν μ (perpC Ψ) x 0 =
        (μ - 1) * ((fmlR φ L 1 (x.2.2 / L) : ℝ) : ℂ) * Ψ x -
          (x.1 : ℂ) * ((fmlR φ L 1 (x.2.2 / L) : ℝ) : ℂ) * cpdC 0 Ψ x -
          (ν : ℂ) * (x.1 : ℂ) * (((fmlR φ L 1 (x.2.2 / L) : ℝ) : ℂ) * cpdC 1 (cpdC 1 Ψ) x +
            ((fmlR φ L 3 (x.2.2 / L) : ℝ) : ℂ) * Ψ x +
            3 * ((fmlR φ L 2 (x.2.2 / L) : ℝ) : ℂ) * cpdC 2 Ψ x +
            3 * ((fmlR φ L 1 (x.2.2 / L) : ℝ) : ℂ) * cpdC 2 (cpdC 2 Ψ) x) := by
  simp (disch := fun_prop) only [flatTransposeC, fml_perp0, fml_perp1,
    fml_phi0 φ hφ L, fml_phi1 φ hφ L, fml_phi2 φ hφ L, fml_R0 φ hφ L, fml_R1 φ hφ L,
    fml_R2 φ hφ L, fml_cpd_add, fml_cpd_neg,
    show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) + 1 = 3 from rfl]
  ring

set_option maxHeartbeats 1000000 in
theorem fml_comp1 (ν : ℝ) (μ : ℂ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (L : ℝ)
    (Ψ : Coord → ℂ) (hΨ : ContDiff ℝ ∞ Ψ) (x : Coord) :
    flatTransposeC ν μ (perpC (fun y => ((φ (y.2.2 / L) : ℝ) : ℂ) * Ψ y)) x 1 -
          ((φ (x.2.2 / L) : ℝ) : ℂ) * flatTransposeC ν μ (perpC Ψ) x 1 =
        (ν : ℂ) * (x.1 : ℂ) * (2 * ((fmlR φ L 1 (x.2.2 / L) : ℝ) : ℂ) * cpdC 2 (cpdC 1 Ψ) x +
          ((fmlR φ L 2 (x.2.2 / L) : ℝ) : ℂ) * cpdC 1 Ψ x) := by
  simp (disch := fun_prop) only [flatTransposeC, fml_perp0, fml_perp1,
    fml_phi0 φ hφ L, fml_phi1 φ hφ L, fml_phi2 φ hφ L, fml_R0 φ hφ L, fml_R1 φ hφ L,
    fml_R2 φ hφ L, fml_cpd_add, fml_cpd_neg,
    show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) + 1 = 3 from rfl]
  ring

theorem commFormula : UnforcedLeray.Short.IIb.CommFormula := by
  unfold CommFormula
  intro ν μ φ hφ L _hL Ψ hΨ x
  exact ⟨fml_comp0 ν μ φ hφ L Ψ hΨ x, fml_comp1 ν μ φ hφ L Ψ hΨ x⟩
