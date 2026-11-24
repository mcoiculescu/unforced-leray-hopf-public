import UnforcedLeray.Lib.Cylinder.Seam
import UnforcedLeray.Lib.Cylinder.WeightDerivs

/-!
# The weighted diffusion energy for the smooth periodic weight (INF13, CY05)


§5 CY05 (`re_weighted_laplacian_le_smooth`).

`paper/main.tex` lines 4569-4578 (unit B0271): Sobolev norms on the physical cylinder use
"a smooth periodic weight, uniformly comparable to `(1+q²+η²)^m`, whose fixed derivative
ratios are bounded independently of `c`".  For this weight there is no seam term
(`weighted_laplacian_smooth`), and `Δ(ρw^m) ≤ C_m ρw^m` with `C_m` independent of the period
`c ≥ 1` (`laplacian_rpow_ρw_le`), so
`2∫_cell Δw w ρw^m ≤ -2∫_cell |∇w|² ρw^m + C_m ∫_cell w² ρw^m` (`weighted_laplacian_le_smooth`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real

namespace UnforcedLeray.Cyl

theorem second_partial_eq {p : Plane → ℝ} (hp : ContDiff ℝ 2 p) (v z : Plane) :
    fderiv ℝ (fun z => fderiv ℝ p z v) z v = iteratedFDeriv ℝ 2 p z ![v, v] := by
  have hfd : Differentiable ℝ (fderiv ℝ p) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [fderiv_clm_apply (hfd z) (differentiableAt_const v), iteratedFDeriv_two_apply]
  simp

theorem abs_partialQ_partialQ_le {p : Plane → ℝ} (hp : ContDiff ℝ 2 p) (z : Plane) :
    |partialQ (partialQ p) z| ≤ ‖iteratedFDeriv ℝ 2 p z‖ := by
  have hw := C2.of_contDiff hp
  have h1 : partialQ p = fun z => fderiv ℝ p z (1, 0) := funext (partialQ_eq_fderiv hw.diff)
  rw [partialQ_eq_fderiv hw.diffQ, h1, second_partial_eq hp, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [Fin.prod_univ_two, Prod.norm_def]

theorem abs_partialEta_partialEta_le {p : Plane → ℝ} (hp : ContDiff ℝ 2 p) (z : Plane) :
    |partialEta (partialEta p) z| ≤ ‖iteratedFDeriv ℝ 2 p z‖ := by
  have hw := C2.of_contDiff hp
  have h1 : partialEta p = fun z => fderiv ℝ p z (0, 1) := funext (partialEta_eq_fderiv hw.diff)
  rw [partialEta_eq_fderiv hw.diffEta, h1, second_partial_eq hp, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [Fin.prod_univ_two, Prod.norm_def]

theorem laplacian_le_norm_iteratedFDeriv {p : Plane → ℝ} (hp : ContDiff ℝ 2 p) (z : Plane) :
    laplacian p z ≤ 2 * ‖iteratedFDeriv ℝ 2 p z‖ := by
  have h1 := abs_partialQ_partialQ_le hp z
  have h2 := abs_partialEta_partialEta_le hp z
  rw [laplacian]
  linarith [le_abs_self (partialQ (partialQ p) z), le_abs_self (partialEta (partialEta p) z)]

/-- `Δ(ρw^m) ≤ C_m ρw^m` with `C_m` independent of the period `ℓ ≥ 1` (B0271). -/
theorem laplacian_rpow_ρw_le (m : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ z : Plane,
      laplacian (fun z => ρw ℓ z ^ m) z ≤ C * ρw ℓ z ^ m := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_rpow_ρw_le 2 m
  refine ⟨2 * C, by positivity, fun ℓ hℓ z => ?_⟩
  have h1 := laplacian_le_norm_iteratedFDeriv (contDiff_rpow_ρw ℓ m) z
  have h2 := hC ℓ hℓ z
  nlinarith

/-- **Weighted diffusion energy, smooth periodic weight** (CY05
`re_weighted_laplacian_le_smooth`, real form; B0271, tex 4569-4578).  There is `C_m`,
independent of the period `c ≥ 1`, such that for every real `C²`, `c`-periodic `w` with compact
support in `η`, `2∫_cell Δw w ρw^m ≤ -2∫_cell |∇w|² ρw^m + C_m ∫_cell w² ρw^m`. -/
theorem weighted_laplacian_le_smooth (m : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ (R : ℝ) (w : Plane → ℝ), ContDiff ℝ 2 w →
      IsPeriodic c w → VanishesOutside R w →
      2 * (∫ z in cell c, laplacian w z * w z * ρw c z ^ m) ≤
        -2 * (∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * ρw c z ^ m)
          + C * ∫ z in cell c, w z ^ 2 * ρw c z ^ m := by
  obtain ⟨C, hC0, hC⟩ := laplacian_rpow_ρw_le m
  refine ⟨C, hC0, fun c hc R w hw hper hR => ?_⟩
  rw [weighted_laplacian_smooth (by linarith) hw hper hR]
  have hw2 := C2.of_contDiff hw
  have hp2 : C2 (fun z => ρw c z ^ m) := C2.of_contDiff (contDiff_rpow_ρw c m)
  have c0 := hw2.cont
  have d0 := hp2.cont; have d3 := hp2.contQQ; have d4 := hp2.contEtaEta
  have iA : IntegrableOn (fun z => w z ^ 2 * laplacian (fun z => ρw c z ^ m) z) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz])
      (by simp only [laplacian]; fun_prop) c
  have iB : IntegrableOn (fun z => C * (w z ^ 2 * ρw c z ^ m)) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  have e : ∫ z in cell c, C * (w z ^ 2 * ρw c z ^ m) = C * ∫ z in cell c, w z ^ 2 * ρw c z ^ m :=
    integral_const_mul _ _
  have : ∫ z in cell c, w z ^ 2 * laplacian (fun z => ρw c z ^ m) z ≤
      ∫ z in cell c, C * (w z ^ 2 * ρw c z ^ m) :=
    setIntegral_mono iA iB fun z => by
      have := hC c hc z
      have h2 := sq_nonneg (w z)
      nlinarith
  linarith

end UnforcedLeray.Cyl
