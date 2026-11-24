import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1

/-!
# `SFCHeatHasDerivDir`: decomposition

Source `the November 2 reference manuscript`
3426-3430 (`∂_j e^{θΔ} f = e^{θΔ} ∂_j f`, derivative under the Gaussian integral).

The hypotheses give no global bound on `∇f`, so dominated convergence with majorant `|∂_j f|` fails;
instead the derivative is moved onto the Gaussian by the substitution `y ↦ y + t e_j`
(`SFCGaussShiftDeriv`, which needs only `f` bounded), and then back onto `f` by one integration by
parts (`SFCGaussIBP`), whose integrability hypothesis is the Gaussian-weighted periodic bound
(`SFCGaussPeriodicBound` and `SFCGaussWeightedInt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The `j`-th unit vector of `Euc 2` (`planeι (sfcE j) = B0579.dir j`). -/
def sfcE (j : Fin 2) : Euc 2 := EuclideanSpace.single j (1 : ℝ)

/-- **Lemma 1 (Gaussian-weighted periodic bound, source 3426-3430).** For a `c`-periodic measurable
`φ : ℝ × ℝ → ℝ≥0∞` there is a finite `K` (depending on `c, θ`) with
`∫⁻ y, G_θ(y) φ(w - y) ≤ K ∫⁻_{strip c} φ` for all `w`
(`IsFundamentalDomain.lintegral_eq_tsum` over the translates of the strip by `(c, 0)`, and the
periodic sum of Gaussians is uniformly bounded; cf. `B0224.lintegral_strip_comp_sub`). -/
def SFCGaussPeriodicBound : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 < θ → ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ φ : ℝ × ℝ → ℝ≥0∞, Measurable φ →
    UnforcedLeray.Cyl.IsPeriodic c φ → ∀ w : ℝ × ℝ,
      ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (w - UnforcedLeray.B0224.planeι y) ≤
        K * ∫⁻ x in UnforcedLeray.B0224.strip c, φ x

/-- **Lemma 2 (integrability against the Gaussian).** Under `SFCCommuteHyp`, for every `z` and `j`
the function `y ↦ G_θ(y) • ∂_j f(z - y)` is integrable on `Euc 2` (apply Lemma 1 to
`φ = ‖∂_j f‖ₑ²`, which is periodic because `f` is, with finite strip integral by the hypothesis
`∫⁻ over Ico (-c/2) (c/2) × univ`, converted by `B0224.restrict_strip`; then Cauchy-Schwarz
against the probability density `G_θ`, as in the calc at the end of the cylinder-heat section of
`Units/B0224/PlaneHeat.lean`, near line 150). -/
def SFCGaussWeightedInt : Prop :=
  ∀ (c θ : ℝ), 0 < c → 0 < θ → ∀ f : ℝ × ℝ → ℂ, SFCCommuteHyp c f → ∀ (z : ℝ × ℝ) (j : Fin 2),
    Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • fderiv ℝ f (z - UnforcedLeray.B0224.planeι y) (B0579.dir j))

/-- **Lemma 3 (derivative moved onto the Gaussian).** For bounded continuous `f`, the substitution
`y ↦ y + t e_j` gives `planeHeat θ f (z + t e_j) = ∫ G_θ(y + t e_j) f(z - y) dy`, and
differentiating under the integral (majorant `sup_{|t|≤1} |∂_j G_θ(y + t e_j)| · ‖f‖_∞`, integrable
since `∇G_θ` has Gaussian decay: `Gaussian.memLp_iteratedFDeriv_gaussKernel`) yields the derivative
`∫ (∂_{e_j} G_θ)(y) f(z - y) dy`. -/
def SFCGaussShiftDeriv : Prop :=
  ∀ (θ : ℝ), 0 < θ → ∀ f : ℝ × ℝ → ℂ, Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
    ∀ (z : ℝ × ℝ) (j : Fin 2),
      HasDerivAt (fun t : ℝ => UnforcedLeray.B0224.planeHeat θ f (z + t • B0579.dir j))
        (∫ y : Euc 2, fderiv ℝ (gaussKernel 2 θ) y (sfcE j) •
          f (z - UnforcedLeray.B0224.planeι y)) 0

/-- **Lemma 4 (integration by parts).** For `f` smooth and bounded with
`y ↦ G_θ(y) • ∂_j f(z - y)` integrable:
`∫ (∂_{e_j} G_θ)(y) f(z - y) dy = ∫ G_θ(y) ∂_j f(z - y) dy`
(`d/dy_j [G_θ(y) f(z - y)] = ∂G_θ f - G_θ ∂_j f(z - y)`, integral of a derivative of an integrable
function with integrable derivative vanishes: Mathlib
`integral_bilinear_fderiv_eq_neg_fderiv_of_integrable` or its `smul` variant; `planeι (sfcE j) =
B0579.dir j`). -/
def SFCGaussIBP : Prop :=
  ∀ (θ : ℝ), 0 < θ → ∀ f : ℝ × ℝ → ℂ, ContDiff ℝ ∞ f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
    ∀ (z : ℝ × ℝ) (j : Fin 2),
      Integrable (fun y : Euc 2 =>
        gaussKernel 2 θ y • fderiv ℝ f (z - UnforcedLeray.B0224.planeι y) (B0579.dir j)) →
      ∫ y : Euc 2, fderiv ℝ (gaussKernel 2 θ) y (sfcE j) • f (z - UnforcedLeray.B0224.planeι y) =
        ∫ y : Euc 2, gaussKernel 2 θ y •
          fderiv ℝ f (z - UnforcedLeray.B0224.planeι y) (B0579.dir j)

/-- `SFCHeatHasDerivDir` from the four lemmas. -/
theorem sfcHeatHasDerivDir_of (h2 : SFCGaussWeightedInt)
    (h3 : SFCGaussShiftDeriv) (h4 : SFCGaussIBP) : SFCHeatHasDerivDir := by
  intro c θ hc hθ f hyp z j
  obtain ⟨hf, hper, hbd, hfin⟩ := hyp
  have hD := h3 θ hθ f hf.continuous hbd z j
  have hI := h4 θ hθ f hf hbd z j (h2 c θ hc hθ f ⟨hf, hper, hbd, hfin⟩ z j)
  rw [hI] at hD
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  exact hD

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
