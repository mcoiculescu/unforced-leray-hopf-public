import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_org

/-!
# `SFCHeatGrad` from gradient commutation and Gaussian Jensen
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/2`)

Source `the November 2 reference manuscript`
1650-1656, 3426-3430.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- Gradient commutation (source 3426-3430): for smooth bounded `q`-periodic `f` with finite cell
`L²` gradient, `∂_j e^{θΔ} f = e^{θΔ} ∂_j f` (differentiation under the Gaussian integral; the
bounded-derivative route is not available, use the L² hypothesis, e.g. Cauchy-Schwarz in `η` against
the Gaussian, or integrate by parts against the kernel). -/
def SFCHeatCommute : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 ≤ θ → ∀ f : ℝ × ℝ → ℂ, ContDiff ℝ ∞ f →
    (∀ q η, f (q + c, η) = f (q, η)) → (∃ C : ℝ, ∀ x : ℝ × ℝ, ‖f x‖ ≤ C) →
    ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal ((‖fderiv ℝ f x (B0579.dir 0)‖ ^ 2 + ‖fderiv ℝ f x (B0579.dir 1)‖ ^ 2)) < ⊤ →
    ∀ (x : ℝ × ℝ) (j : Fin 2), fderiv ℝ (UnforcedLeray.B0224.planeHeat θ f) x (B0579.dir j) =
      UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ f y (B0579.dir j)) x

/-- Gaussian Jensen on the cell strip (source 3426-3430): for continuous `q`-periodic
`h₀ h₁ : ℝ×ℝ → ℂ`, `θ ≥ 0`,
`∫_{strip} |e^{θΔ}h₀|²+|e^{θΔ}h₁|² ≤ ∫_{strip} |h₀|²+|h₁|²`
(Gaussian is a probability density; Minkowski/Jensen; strip measure is shift invariant in `η` and,
by periodicity, in `q`).  Trivial when the right side is infinite. -/
def SFCHeatJensen : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 ≤ θ → ∀ h₀ h₁ : ℝ × ℝ → ℂ, Continuous h₀ → Continuous h₁ →
    (∀ q η, h₀ (q + c, η) = h₀ (q, η)) → (∀ q η, h₁ (q + c, η) = h₁ (q, η)) →
      ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (‖UnforcedLeray.B0224.planeHeat θ h₀ x‖ ^ 2 +
          ‖UnforcedLeray.B0224.planeHeat θ h₁ x‖ ^ 2)
      ≤ ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (‖h₀ x‖ ^ 2 + ‖h₁ x‖ ^ 2)

theorem tnorm2_row_sq (a : Fin 2 → ℂ) :
    tnorm2 (fun i j => a j * (if i = 0 then 1 else 0)) ^ 2 = ‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

theorem sfcHeatGrad_of (hC : SFCHeatCommute) (hJ : SFCHeatJensen) : SFCHeatGrad := by
  intro c θ hc hθ f hf hper hbd
  simp only [tnorm2_row_sq]
  by_cases hfin : ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (‖fderiv ℝ f x (B0579.dir 0)‖ ^ 2 + ‖fderiv ℝ f x (B0579.dir 1)‖ ^ 2) < ⊤
  · have hcm := hC c θ hc hθ f hf hper hbd hfin
    have hd : ∀ j : Fin 2, Continuous fun y => fderiv ℝ f y (B0579.dir j) := fun j =>
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hdper : ∀ j : Fin 2, ∀ q η, fderiv ℝ f (q + c, η) (B0579.dir j) = fderiv ℝ f (q, η) (B0579.dir j) := by
      intro j q η
      have h1 : (fun y : ℝ × ℝ => f (y + (c, 0))) = f := funext fun y => by
        have := hper y.1 y.2
        rcases y with ⟨a, b⟩
        simpa using this
      have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := (q, η)) (c, 0)
      rw [h1] at h2
      have h3 : ((q, η) + (c, 0) : ℝ × ℝ) = (q + c, η) := by simp
      rw [h3] at h2
      rw [← h2]
    have := hJ c θ hc hθ _ _ (hd 0) (hd 1) (hdper 0) (hdper 1)
    refine le_of_eq_of_le ?_ this
    refine setLIntegral_congr_fun (measurableSet_Ico.prod MeasurableSet.univ) (fun x _ => ?_)
    rw [hcm x 0, hcm x 1]
  · have h : _ = (⊤ : ENNReal) := top_le_iff.mp (not_lt.mp hfin)
    rw [h]; exact le_top

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
