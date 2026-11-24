import UnforcedLeray.Lib.HeatR3.Line
import UnforcedLeray.Lib.HeatR3.Bounded

/-!
# Anisotropic factorization of the heat kernel and weighted line kernels (INF04 T12, INF05 T19,
part)


`kernel_factor` (used for B0740, B0300, B0572: tex 9188–9247, 5335–5348, 9272–9284), and the
pointwise kernel bound at the start of **T19** (B0180, B0181: tex 2795–2801).

Main results:
* `horiz`, `norm_sq_eq_horiz`: `|x|² = |x_h|² + x₃²`;
* `kernel_factor`: `G^{(3)}_θ(x) = G^{(2)}_θ(x_h) G^{(1)}_θ(x₃)` (`θ > 0`);
* `abs_pow_mul_iteratedDeriv_lineGauss_le` (T19):
  `|η|^m |∂^b G_θ(η)| ≤ C θ^{(m-b)/2} G_{4θ}(η)` for `θ > 0`, uniformly in `θ`;
* `eLpNorm_pow_mul_iteratedDeriv_lineGauss_le`: the weighted `L^p` bound
  `‖η^m ∂^b G_θ‖_{L^p} ≤ C θ^{(m-b)/2} ‖G_{4θ}‖_{L^p}`.

Not proved here: the mixed-norm and transverse bounds `eLpNorm_average_mixed`,
`norm_iteratedFDeriv_average_le_transverse` (they need the Fubini splitting `ℝ³ = ℝ² × ℝ`).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The horizontal part `x_h = (x₀, x₁)` of `x ∈ ℝ³`. -/
def horiz (x : Space) : Euc 2 := WithLp.toLp 2 fun i : Fin 2 => x (Fin.castSucc i)

theorem norm_sq_eq_horiz (x : Space) : ‖x‖ ^ 2 = ‖horiz x‖ ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  simp only [horiz, Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ, Fin.sum_univ_zero,
    PiLp.toLp_apply]
  simp [Fin.castSucc]
  ring

/-- **INF04 T12 `kernel_factor`.** `G^{(3)}_θ(x) = G^{(2)}_θ(x_h) · G^{(1)}_θ(x₃)` for `θ > 0`. -/
theorem kernel_factor {θ : ℝ} (hθ : 0 < θ) (x : Space) :
    kernel θ x = gaussKernel 2 θ (horiz x) * lineGauss θ (x 2) := by
  rw [← Gaussian.gaussKernel_three_eq, Gaussian.gaussKernel, Gaussian.gaussKernel, lineGauss,
    norm_sq_eq_horiz]
  have hA : 0 < 4 * π * θ := by positivity
  have h1 : (4 * π * θ) ^ (-((3 : ℕ) : ℝ) / 2) =
      (4 * π * θ) ^ (-((2 : ℕ) : ℝ) / 2) * (4 * π * θ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hA]; norm_num
  rw [h1]
  have h2 : Real.exp (-(‖horiz x‖ ^ 2 + x 2 ^ 2) / (4 * θ)) =
      Real.exp (-‖horiz x‖ ^ 2 / (4 * θ)) * Real.exp (-x 2 ^ 2 / (4 * θ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]; ring

/-! ### Weighted line kernels (T19) -/

/-- **INF05 T19, pointwise kernel bound.** `|η|^m |∂^b G_θ(η)| ≤ C θ^{(m-b)/2} G_{4θ}(η)` for
`θ > 0`, with `C = C(m, b)` (the manuscript's `|η^m∂^bG_θ| ≤ Cθ^{(m-b-1)/2}G_{2θ}` up to the
harmless change `2θ ↦ 4θ` of the comparison kernel; B0180, B0181). -/
theorem abs_pow_mul_iteratedDeriv_lineGauss_le (m b : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {θ : ℝ}, 0 < θ → ∀ η : ℝ,
      |η| ^ m * ‖iteratedDeriv b (lineGauss θ) η‖ ≤
        C * θ ^ (((m : ℝ) - b) / 2) * lineGauss (4 * θ) η := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le 1 b
  obtain ⟨C₂, hC₂0, hC₂⟩ := Gaussian.rpow_mul_exp_le (m : ℝ) (by positivity)
  refine ⟨C₁ * C₂ * 2 ^ (m : ℝ) * (16 * π) ^ ((1 : ℝ) / 2), by positivity, fun {θ} hθ η => ?_⟩
  rw [norm_iteratedDeriv_lineGauss]
  have hK := hC₁ hθ (lineIso η)
  rw [norm_lineIso] at hK
  have hE := hC₂ |η| (2 * θ) (abs_nonneg η) (by positivity)
  have he : -|η| ^ 2 / (4 * (2 * θ)) = -|η| ^ 2 / (8 * θ) := by ring
  have he2 : -|η| ^ 2 / (8 * (2 * θ)) = -η ^ 2 / (4 * (4 * θ)) := by rw [sq_abs]; ring
  rw [he, he2] at hE
  have hm : |η| ^ m = |η| ^ (m : ℝ) := (Real.rpow_natCast _ _).symm
  rw [hm]
  have hG : lineGauss (4 * θ) η =
      (16 * π) ^ (-(1 : ℝ) / 2) * θ ^ (-(1 : ℝ) / 2) * Real.exp (-η ^ 2 / (4 * (4 * θ))) := by
    rw [lineGauss, show 4 * π * (4 * θ) = (16 * π) * θ by ring,
      Real.mul_rpow (by positivity) hθ.le]
  rw [hG]
  have hpow : (2 * θ) ^ ((m : ℝ) / 2) = 2 ^ ((m : ℝ) / 2) * θ ^ ((m : ℝ) / 2) :=
    Real.mul_rpow (by norm_num) hθ.le
  have h2m : (2 : ℝ) ^ ((m : ℝ) / 2) ≤ 2 ^ (m : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
  have hθexp : θ ^ (-((((1 : ℕ) : ℝ) + b) / 2)) * θ ^ ((m : ℝ) / 2) =
      θ ^ (((m : ℝ) - b) / 2) * θ ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hθ, ← Real.rpow_add hθ]; congr 1; push_cast; ring
  have h16 : (16 * π) ^ ((1 : ℝ) / 2) * (16 * π) ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  calc |η| ^ (m : ℝ) * ‖iteratedFDeriv ℝ b (gaussKernel 1 θ) (lineIso η)‖
      ≤ |η| ^ (m : ℝ) * (C₁ * θ ^ (-((((1 : ℕ) : ℝ) + b) / 2)) *
          Real.exp (-|η| ^ 2 / (8 * θ))) := by gcongr
    _ = C₁ * θ ^ (-((((1 : ℕ) : ℝ) + b) / 2)) *
          (|η| ^ (m : ℝ) * Real.exp (-|η| ^ 2 / (8 * θ))) := by ring
    _ ≤ C₁ * θ ^ (-((((1 : ℕ) : ℝ) + b) / 2)) *
          (C₂ * (2 * θ) ^ ((m : ℝ) / 2) * Real.exp (-η ^ 2 / (4 * (4 * θ)))) := by gcongr
    _ = C₁ * C₂ * 2 ^ ((m : ℝ) / 2) * (θ ^ (-((((1 : ℕ) : ℝ) + b) / 2)) * θ ^ ((m : ℝ) / 2)) *
          Real.exp (-η ^ 2 / (4 * (4 * θ))) := by rw [hpow]; ring
    _ ≤ C₁ * C₂ * 2 ^ (m : ℝ) * (θ ^ (-((((1 : ℕ) : ℝ) + b) / 2)) * θ ^ ((m : ℝ) / 2)) *
          Real.exp (-η ^ 2 / (4 * (4 * θ))) := by gcongr
    _ = C₁ * C₂ * 2 ^ (m : ℝ) * ((16 * π) ^ ((1 : ℝ) / 2) * (16 * π) ^ (-(1 : ℝ) / 2)) *
          θ ^ (((m : ℝ) - b) / 2) * θ ^ (-(1 : ℝ) / 2) * Real.exp (-η ^ 2 / (4 * (4 * θ))) := by
        rw [hθexp, h16]; ring
    _ = C₁ * C₂ * 2 ^ (m : ℝ) * (16 * π) ^ ((1 : ℝ) / 2) * θ ^ (((m : ℝ) - b) / 2) *
          ((16 * π) ^ (-(1 : ℝ) / 2) * θ ^ (-(1 : ℝ) / 2) *
            Real.exp (-η ^ 2 / (4 * (4 * θ)))) := by ring

/-- **INF05 T19, weighted `L^p` bound.** `‖η^m ∂^b G_θ‖_{L^p} ≤ C θ^{(m-b)/2} ‖G_{4θ}‖_{L^p}`
for `θ > 0` and every `p` (combine with `eLpNorm_iteratedDeriv_lineGauss` at `k = 0` for the
power of `θ`). -/
theorem eLpNorm_pow_mul_iteratedDeriv_lineGauss_le (m b : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {θ : ℝ}, 0 < θ → ∀ p : ℝ≥0∞,
      eLpNorm (fun η => η ^ m * iteratedDeriv b (lineGauss θ) η) p volume ≤
        ENNReal.ofReal (C * θ ^ (((m : ℝ) - b) / 2)) * eLpNorm (lineGauss (4 * θ)) p volume := by
  obtain ⟨C, hC0, hC⟩ := abs_pow_mul_iteratedDeriv_lineGauss_le m b
  refine ⟨C, hC0, fun {θ} hθ p => ?_⟩
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun η => ?_) p
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg
    (lineGauss_nonneg (by positivity) η)]
  exact hC hθ η

end UnforcedLeray.Heat
