import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel

/-!
# `DuhamelSliceBound` from the sup bound and the `x`-gradient bound of the Duhamel integral

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2)

/-- Sup bound of each component of the Duhamel integral on a slice `s > 0` (source 1684-1689):
`|planeHeat θ u| ≤ sup |u|` (Gaussian probability density) and the finite `σ`-integral with
`(σ/s)^μ` bounded on `[s₀, min s s₁]`. -/
def DuhamelSupBound : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ s : ℝ, 0 < s →
    ∃ C : ℝ, ∀ (x : ℝ × ℝ) (i : Fin 2), ‖duhamel ν μ G (s, x) i‖ ≤ C

/-- Bound of the `x`-Fréchet derivative of each component of the Duhamel integral on a slice
`s > 0` (source 1684-1689): `∂_x` commutes with `planeHeat` and with the `σ`-integral,
`|D planeHeat θ u| ≤ sup |Du|`, `Du = ∂_x G` bounded by `IsDriving` (`n = 1`). -/
def DuhamelFderivBound : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ s : ℝ, 0 < s →
    ∃ C : ℝ, ∀ (x : ℝ × ℝ) (i : Fin 2),
      ‖fderiv ℝ (fun y : ℝ × ℝ => duhamel ν μ G (s, y) i) x‖ ≤ C

theorem duhamelSliceBound_of (h1 : DuhamelSupBound) (h2 : DuhamelFderivBound) :
    DuhamelSliceBound := by
  intro c ν μ G hG hν s hs
  obtain ⟨C1, hC1⟩ := h1 c ν μ G hG hν s hs
  obtain ⟨C2, hC2⟩ := h2 c ν μ G hG hν s hs
  set M : ℝ := max (max C1 C2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have h1M : C1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have h2M : C2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨2 * M, fun x => ⟨?_, fun i j => ?_⟩⟩
  · unfold vnorm2
    apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    simp only [Fin.sum_univ_two]
    have a0 := (hC1 x 0).trans h1M
    have a1 := (hC1 x 1).trans h1M
    have n0 := norm_nonneg (duhamel ν μ G (s, x) 0)
    have n1 := norm_nonneg (duhamel ν μ G (s, x) 1)
    nlinarith
  · unfold cellGrad
    have hd := (fderiv ℝ (fun y : ℝ × ℝ => duhamel ν μ G (s, y) i) x).le_opNorm
      (B0579.dir j)
    have hdir : ‖B0579.dir j‖ ≤ 1 := by
      fin_cases j <;> simp [B0579.dir, Prod.norm_def]
    have := hC2 x i
    have hn := norm_nonneg (fderiv ℝ (fun y : ℝ × ℝ => duhamel ν μ G (s, y) i) x)
    calc _ ≤ ‖fderiv ℝ (fun y : ℝ × ℝ => duhamel ν μ G (s, y) i) x‖ * ‖B0579.dir j‖ := hd
      _ ≤ ‖fderiv ℝ (fun y : ℝ × ℝ => duhamel ν μ G (s, y) i) x‖ * 1 :=
          mul_le_mul_of_nonneg_left hdir hn
      _ ≤ 2 * M := by nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
