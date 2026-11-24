import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivOf

/-!
# `PlaneGaussDtLap` reduced to two coordinate integration-by-parts facts
(task `PartIII-b:C/flatset/col/7/3/2/1/2/5`)

Source `the November 2 reference manuscript` 1650-1656 (`A₀ = -S + νsΔ_{q,η}`,
`T₀(t)* = e^{-t/2} e^{νs(eᵗ-1)Δ} f(seᵗ)`).  On `ℝ²`,
`∂_θG_θ(y) = (y₀²/(4θ²) - 1/(2θ) + y₁²/(4θ²) - 1/(2θ)) G_θ(y)` and each summand is
`∂_i²G_θ`; two integrations by parts per coordinate move `∂_i²` to the test function.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)

/-- Coordinate `0` (the `q`-direction) of `PlaneGaussDtLap`: with `a₀(y) = y₀²/(4θ²) - 1/(2θ)`
(so `a₀G_θ = ∂_{y₀}²G_θ`, source 1650-1656), for a smooth meridional test `ζ`, `θ > 0`:
both `a₀G_θ • ζ(σ, x - ι y)` and `G_θ • ∂_q²ζ(σ, x - ι y)` are integrable on `ℝ²` and their
integrals agree (two integrations by parts in `y₀`; `∂_{y₀}[ζ(σ,x-ιy)] = -∂_qζ`). -/
def PlaneGaussIbpQ : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (ζ : UnforcedLeray.B0220.Profile → MeridC), IsMeridTest c ζ →
    ∀ (θ σ : ℝ), 0 < θ → ∀ x : ℝ × ℝ,
      MeasureTheory.Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        (((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) •
          ζ (σ, x - UnforcedLeray.B0224.planeι y)) ∧
      MeasureTheory.Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          pdQ (pdQ ζ) (σ, x - UnforcedLeray.B0224.planeι y)) ∧
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
          (((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) •
            ζ (σ, x - UnforcedLeray.B0224.planeι y) =
        ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          pdQ (pdQ ζ) (σ, x - UnforcedLeray.B0224.planeι y)

/-- Coordinate `1` (the `η`-direction) of `PlaneGaussDtLap`, as `PlaneGaussIbpQ` with `y₁`,
`∂_η²ζ` (source 1650-1656). -/
def PlaneGaussIbpEta : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (ζ : UnforcedLeray.B0220.Profile → MeridC), IsMeridTest c ζ →
    ∀ (θ σ : ℝ), 0 < θ → ∀ x : ℝ × ℝ,
      MeasureTheory.Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        (((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) •
          ζ (σ, x - UnforcedLeray.B0224.planeι y)) ∧
      MeasureTheory.Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          pdEta (pdEta ζ) (σ, x - UnforcedLeray.B0224.planeι y)) ∧
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
          (((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) •
            ζ (σ, x - UnforcedLeray.B0224.planeι y) =
        ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          pdEta (pdEta ζ) (σ, x - UnforcedLeray.B0224.planeι y)

/-- `∂_θG_θ = ∂_{y₀}²G_θ + ∂_{y₁}²G_θ` on `ℝ²` (explicit coefficients). -/
theorem gaussDt_two_eq_sum (θ : ℝ) (y : UnforcedLeray.Gaussian.Euc 2) :
    UnforcedLeray.Heat.gaussDt 2 θ y =
      (((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) +
      (((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) := by
  unfold UnforcedLeray.Heat.gaussDt
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- **Reduction of `PlaneGaussDtLap`** to the two coordinate integration-by-parts identities. -/
theorem plane_gaussDt_lap_of (h0 : PlaneGaussIbpQ) (h1 : PlaneGaussIbpEta) :
    PlaneGaussDtLap := by
  intro c hc ζ hζ θ σ hθ x
  obtain ⟨i0, j0, e0⟩ := h0 c hc ζ hζ θ σ hθ x
  obtain ⟨i1, j1, e1⟩ := h1 c hc ζ hζ θ σ hθ x
  have hL : (fun y : UnforcedLeray.Gaussian.Euc 2 => UnforcedLeray.Heat.gaussDt 2 θ y •
      ζ (σ, x - UnforcedLeray.B0224.planeι y)) = fun y =>
      (((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) •
          ζ (σ, x - UnforcedLeray.B0224.planeι y) +
      (((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y) •
          ζ (σ, x - UnforcedLeray.B0224.planeι y) := by
    funext y
    rw [gaussDt_two_eq_sum, add_smul]
  have hR : (fun y : UnforcedLeray.Gaussian.Euc 2 => UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          (pdQ (pdQ ζ) (σ, x - UnforcedLeray.B0224.planeι y) +
            pdEta (pdEta ζ) (σ, x - UnforcedLeray.B0224.planeι y))) = fun y =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          pdQ (pdQ ζ) (σ, x - UnforcedLeray.B0224.planeι y) +
      UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          pdEta (pdEta ζ) (σ, x - UnforcedLeray.B0224.planeι y) := by
    funext y
    rw [smul_add]
  rw [hL, hR, integral_add i0 i1, integral_add j0 j1, e0, e1]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
