import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2

/-!
# `SFCHeatCommute` from directional differentiability and differentiability

Source `the November 2 reference manuscript`
3426-3430 (`∂_j e^{θΔ} f = e^{θΔ} ∂_j f`, derivative under the Gaussian integral).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Hypotheses of `SFCHeatCommute` on `f` (source 3426-3430). -/
def SFCCommuteHyp (c : ℝ) (f : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ q η, f (q + c, η) = f (q, η)) ∧ (∃ C : ℝ, ∀ x : ℝ × ℝ, ‖f x‖ ≤ C) ∧
    ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal ((‖fderiv ℝ f x (B0579.dir 0)‖ ^ 2 + ‖fderiv ℝ f x (B0579.dir 1)‖ ^ 2)) < ⊤

/-- Directional derivative under the Gaussian integral (source 3426-3430): dominated convergence
with majorant `G_θ(y) · ∫₀¹ |∂_j f(z + s t e_j - y)| ds`, integrable by Cauchy-Schwarz against the
Gaussian and `q`-periodicity of `∂_j f` (so Gaussian-weighted `L²` is bounded by the cell `L²`
times a uniform bound on the periodic sum of Gaussians; `IsFundamentalDomain.lintegral_eq_tsum`). -/
def SFCHeatHasDerivDir : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 < θ → ∀ f : ℝ × ℝ → ℂ, SFCCommuteHyp c f →
    ∀ (z : ℝ × ℝ) (j : Fin 2),
      HasDerivAt (fun t : ℝ => UnforcedLeray.B0224.planeHeat θ f (z + t • B0579.dir j))
        (UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ f y (B0579.dir j)) z) 0

/-- `e^{θΔ} f` is Fréchet differentiable under the same hypotheses (continuity of the two
partials, i.e. continuity of `e^{θΔ} ∂_j f` — continuity of translations in the Gaussian-weighted
periodic `L²` norm — plus existence of the partials from `SFCHeatHasDerivDir`). -/
def SFCHeatDifferentiable : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 < θ → ∀ f : ℝ × ℝ → ℂ, SFCCommuteHyp c f →
    ∀ z : ℝ × ℝ, DifferentiableAt ℝ (UnforcedLeray.B0224.planeHeat θ f) z

theorem sfcHeatCommute_of (h1 : SFCHeatHasDerivDir) (h2 : SFCHeatDifferentiable) :
    SFCHeatCommute := by
  intro c θ hc hθ f hf hper hbd hfin x j
  by_cases hpos : 0 < θ
  · have hyp : SFCCommuteHyp c f := ⟨hf, hper, hbd, hfin⟩
    have hd := h2 c θ hc hpos f hyp x
    have hD := h1 c θ hc hpos f hyp x j
    have hline : HasDerivAt (fun t : ℝ => x + t • B0579.dir j) (B0579.dir j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (B0579.dir j)).const_add x
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact hcomp.unique hD
  · have hθ0 : θ ≤ 0 := not_lt.1 hpos
    rw [UnforcedLeray.B0224.planeHeat_of_nonpos hθ0, UnforcedLeray.B0224.planeHeat_of_nonpos hθ0]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
