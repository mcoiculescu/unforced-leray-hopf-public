import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1

/-!
# `PartII-a:N01/9/1/3/3/2/1/1` (decomposition): `PlaneHeatGradSmoothing`

Source `the November 2 reference manuscript`
lines 3373-3383, 1684-1689.  `∂_j e^{θΔ} f = (∂_j K_θ) ∗ f`, `‖∂_j K_θ‖_{L¹(ℝ²)} = C θ^{-1/2}`,
Young on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- **(K1)** (tex 3373-3383) The gradient of the planar Gaussian is in `L¹(ℝ²)` with norm
`≤ C θ^{-1/2}` (scaling `x = √θ y`), `C` universal. -/
def GaussGradL1 : Prop :=
  ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → ∀ j : Fin 2,
    Integrable (fun y : Euc 2 => fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))) ∧
    ∫ y : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))‖ ≤
      C * θ ^ (-(1 / 2 : ℝ))

/-- **(K2)** (tex 3373-3383) Integration by parts: for `C¹` bounded `f` with bounded derivative,
`e^{θΔ}∂_j f (x) = ∫ (∂_j K_θ)(y) f(x - y) dy`. -/
def PlaneHeatGradIBP : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ f : ℝ × ℝ → ℂ, ContDiff ℝ 1 f → (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) →
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ f x‖ ≤ M) → ∀ j : Fin 2, ∀ x : ℝ × ℝ,
      UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ f y (UnforcedLeray.B0579.dir j)) x =
        ∫ y : Euc 2, fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ)) •
          f (x - UnforcedLeray.B0224.planeι y)

/-- **(K3)** (tex 1650-1658, 3379-3383) Young on the cell for an `L¹` kernel and continuous
`c`-periodic data (the Gaussian case is `PlaneHeatCellContract`). -/
def CellYoungKernel : Prop :=
  ∀ c : ℝ, 0 < c → ∀ k : Euc 2 → ℝ, Integrable k → ∀ u : ℝ × ℝ → ℂ, Continuous u →
    (∀ x : ℝ × ℝ, u (x.1 + c, x.2) = u x) →
    ∫⁻ x in UnforcedLeray.B0579.cell c,
        ‖∫ y : Euc 2, k y • u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 ≤
      (∫⁻ y : Euc 2, ‖k y‖ₑ) ^ 2 * ∫⁻ x in UnforcedLeray.B0579.cell c, ‖u x‖ₑ ^ 2

theorem planeHeatGradSmoothing_of (h1 : GaussGradL1) (h2 : PlaneHeatGradIBP) (h3 : CellYoungKernel) :
    PlaneHeatGradSmoothing := by
  obtain ⟨C, hC⟩ := h1
  refine ⟨C, ?_⟩
  intro θ c hθ hc f hf hper hb hd j
  obtain ⟨hint, hnorm⟩ := hC θ hθ j
  set k : Euc 2 → ℝ := fun y => fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ)) with hk
  have hY := h3 c hc k hint f hf.continuous hper
  have hrew : (∫⁻ x in UnforcedLeray.B0579.cell c,
      ‖UnforcedLeray.B0224.planeHeat θ
        (fun y => fderiv ℝ f y (UnforcedLeray.B0579.dir j)) x‖ₑ ^ 2) =
      ∫⁻ x in UnforcedLeray.B0579.cell c,
        ‖∫ y : Euc 2, k y • f (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 := by
    refine lintegral_congr fun x => ?_
    rw [h2 θ hθ f hf hb hd j x]
  have hA : (∫⁻ y : Euc 2, ‖k y‖ₑ) ≤ ENNReal.ofReal (C * θ ^ (-(1 / 2 : ℝ))) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact ENNReal.ofReal_le_ofReal hnorm
  rw [hrew]
  calc _ ≤ ((∫⁻ y : Euc 2, ‖k y‖ₑ) ^ 2 * ∫⁻ x in UnforcedLeray.B0579.cell c, ‖f x‖ₑ ^ 2) ^
          (1 / 2 : ℝ) := by gcongr
    _ = (∫⁻ y : Euc 2, ‖k y‖ₑ) *
          (∫⁻ x in UnforcedLeray.B0579.cell c, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
    _ ≤ _ := by gcongr

end UnforcedLeray.Short.PartIIa.N01
