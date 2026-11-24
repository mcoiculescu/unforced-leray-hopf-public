import UnforcedLeray.Short.PartIIIa.Sub.T20_4

/-!
# Part III-a, task `PartIII-a:T20/4/1`: the Fourier shape of the modes of a test field

Proves `CTE.TestModeFourier` (statement in `Sub/T20_4.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3240 (the Fourier coefficients
in `q` of a cylinder test field).

Proof. `B0583.modes_testLp` identifies `(modes (ψ e_j))_k` with the Schwartz function
`tSchwartz c k hψ j η = z(η) e_j`, `z = √c c⁻¹ sc c k ψ` (`sSchwartz`, a scalar Schwartz function).
Physical side: `coeFn_toLp` and `coeFn_compLpL`. Fourier side: `SchwartzMap.toLp_fourier_eq`,
`SchwartzMap.fourier_coe` and `integral_smul_const` (the Fourier integral of `z(η) • e_j`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CTE

/-- The scalar profile `z(η) = √c c⁻¹ sc c k φ η` of the `k`-th mode of a test field. -/
def scalarMode (c : ℝ) (k : ℤ) (φ : B0579.Plane → ℝ) (η : ℝ) : ℂ :=
  (Real.sqrt c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * B0583.sc c k φ η)

theorem contDiff_scalarMode {c : ℝ} (hc : 0 ≤ c) (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (scalarMode c k φ) :=
  contDiff_const.mul (contDiff_const.mul (B0583.contDiff_sc hc k hφ))

theorem hasCompactSupport_scalarMode {c : ℝ} (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) : HasCompactSupport (scalarMode c k φ) :=
  ((B0583.hasCompactSupport_sc k hφ).mul_left).mul_left

def sSchwartz (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_scalarMode k hφ).toSchwartzMap (contDiff_scalarMode hc.out.le k hφ.smooth)

theorem tSchwartz_eq (c : ℝ) [Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) (η : ℝ) :
    B0583.tSchwartz c k hφ j η =
      sSchwartz c k hφ η • (EuclideanSpace.single j (1 : ℂ) : B0581.Vel) := rfl

theorem testModeFourier : TestModeFourier := by
  intro c hc k ψ hψ
  refine ⟨(sSchwartz c k hψ).toLp 2, fun j => ?_, fun j => ?_⟩
  · rw [B0583.modes_testLp]
    refine Lp.ext ?_
    filter_upwards [(B0583.tSchwartz c k hψ j).coeFn_toLp 2,
      ContinuousLinearMap.coeFn_compLpL (embedJ j) ((sSchwartz c k hψ).toLp 2),
      (sSchwartz c k hψ).coeFn_toLp 2] with η h1 h2 h3
    rw [h1, h2, h3, embedJ_apply]
    rfl
  · rw [B0583.modes_testLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    filter_upwards [(𝓕 (B0583.tSchwartz c k hψ j)).coeFn_toLp 2,
      (𝓕 (sSchwartz c k hψ)).coeFn_toLp 2] with ξ h1 h2
    rw [h1, h2, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    have : (B0583.tSchwartz c k hψ j : ℝ → B0581.Vel) =
        fun η => (sSchwartz c k hψ : ℝ → ℂ) η • (EuclideanSpace.single j (1 : ℂ) : B0581.Vel) :=
      funext fun η => tSchwartz_eq c k hψ j η
    rw [this, Real.fourier_real_eq, Real.fourier_real_eq]
    rw [← integral_smul_const]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_assoc]

end CTE

end UnforcedLeray.Short.IIIa
