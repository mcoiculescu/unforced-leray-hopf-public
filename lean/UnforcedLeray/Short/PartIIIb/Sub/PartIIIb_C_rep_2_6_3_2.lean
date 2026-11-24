import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3

/-!
# Decomposition of `SepX0TauDeriv` (`PartIII-b:C/rep/2/6/3/2`)

Source `the November 2 reference manuscript`
lines 3603-3626, 4171-4200.  By `SepX0KerInt` (valid for every `t`), `sepX0 ·` is `Re kerInt Kd`
componentwise; the whole analytic content is the `τ`-derivative of the complex kernel integral
(`Kd 0 = 0`, so no boundary term), isolated as `KerIntKdDeriv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `Kd(0) = 0` (source 4171-4200): both `Gker` have the factor `exp 0 = 1` and the same
`heatLerayK 0` term. -/
theorem kd_zero (ν μ : ℝ) (y z : Space) (i j k : Fin 3) : Kd ν μ 0 y z i j k = 0 := by
  simp [Kd, Gker]

/-- **Differentiation of the kernel integral in `τ`** (source 4171-4200, 3800-3807): for a
separated source with `SepData`, off the old disk,
`∂_τ kerInt T Kd = kerInt T (∂_h Kd)` (no instantaneous term since `Kd 0 = 0`).  Proof idea:
`kerInt T Kd t = -∫_{s ≤ t} ∫ Kd(t-s) y z : T(s,z)`; extend `Kd` by `0` to `h<0` (continuous at
`0` by `kd_zero`); the difference quotient converges pointwise to `kdDh` and is dominated by an
envelope from the Lipschitz bound of `Kd` in `h` for `h > 0` (kernel bounds `SepKernelBounds`
for `D²∇K`, `|y - e^{-h/2}z| ≥ ϱ y - rOut` on the support) against `|T|` (`SepMoment`,
periodicity); use `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
def KerIntKdDeriv : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
      HasDerivAt (fun t => kerInt T (Kd ν μ) t y i) (kerInt T (kdDh ν μ) τ y i) τ

/-- `SepX0TauDeriv` from `SepX0KerInt` and `KerIntKdDeriv` (real parts, componentwise). -/
theorem sepX0TauDeriv_of (h1 : SepX0KerInt) (h2 : KerIntKdDeriv) : SepX0TauDeriv := by
  intro ν μ rOut P T hD τ y hy
  have hfun : (fun t => sepX0 ν μ T t y) =
      fun t => WithLp.toLp 2 fun i => (kerInt T (Kd ν μ) t y i).re := by
    funext t; exact h1 ν μ rOut P T hD t y hy
  rw [hfun]
  have hc : ∀ i : Fin 3, HasDerivAt (fun t => (kerInt T (Kd ν μ) t y i).re)
      (kerInt T (kdDh ν μ) τ y i).re τ := fun i =>
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ (h2 ν μ rOut P T hD τ y hy i))
  have hp : HasDerivAt (fun t => fun i : Fin 3 => (kerInt T (Kd ν μ) t y i).re)
      (fun i : Fin 3 => (kerInt T (kdDh ν μ) τ y i).re) τ := hasDerivAt_pi.2 hc
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ hp)

end UnforcedLeray.Short.PartIIIb.Concrete
