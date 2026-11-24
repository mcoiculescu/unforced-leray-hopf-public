import UnforcedLeray.Loc.Hyp.ModeIdentification.Drift

/-!
# H-ModeId helpers: the mode at almost every phase as an `X`-field

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 172–185 and 308–312; blueprint units B1007, B1009).

* `LaplacianH1Regularity`: the elliptic statement "`f, Δf ∈ L²` gives `f ∈ H¹` with the
  weak `H¹` Laplacian `Δf`" on `ℝ³` (the manuscript's "`H²` from `‖f‖₂ + ‖Δf‖₂`", INF11). It is
  proved in `Regularity.lean` (`laplacianH1Regularity`).
* `ae_phase`: given that statement, at almost every phase `τ` the mode `b_*(τ)` is the value of
  an `X = H¹_div` field `b̃` whose weak Laplacian is `lapB(τ)`, and the mode equation holds in
  `L²` with the coefficient map of L1:
  `driftB(τ) - ½b_*(τ) = h lapB(τ) - σ b_*(τ) + 𝓑_*(τ) b̃`.
  The coupling is identified with `𝓑_*(τ) b̃` by the literal characterization `B_weak` of
  `IsCoefficients`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph

/-- **Elliptic `H¹` regularity on `ℝ³`** (the manuscript's "`H²` from `‖f‖₂ + ‖Δf‖₂`",
tex lines 308–312, B1009; INF11): if `f, g ∈ L²(ℝ³;ℝ³)` and `⟨f, Δφ⟩ = ⟨g, φ⟩` for every vector
test `φ`, then `f ∈ H¹` and `g` is its weak `H¹` Laplacian. -/
def LaplacianH1Regularity : Prop :=
  ∀ f g : L2Space, (∀ φ : Space → Space, IsVectorTest φ →
      inner ℝ f (toL2 (testLap φ)) = inner ℝ g (toL2 φ)) →
    ∃ F : H1, F.value = f ∧ HasWeakLaplacian F g

variable {D : BackgroundData} {c : Coefficients}

/-- An `H¹` field with solenoidal value is an element of `X`. -/
def toX (F : H1) (hF : F.value ∈ Leray.solenoidalSubspace) : X := ⟨F, hF⟩

theorem toX_toH1 (F : H1) (hF : F.value ∈ Leray.solenoidalSubspace) : (toX F hF).toH1 = F := rfl

theorem toL2_mem_solenoidal {f : SpatialField} (hf : MemLp f 2 volume) (hs : IsSolenoidal f) :
    toL2 f ∈ Leray.solenoidalSubspace := by
  rw [Leray.mem_solenoidalSubspace_iff]
  exact Leray.solenoidal_congr_ae hs (coeFn_toL2 hf).symm

/-- **The mode at a.e. phase** (B1007, B1009): at almost every phase `τ`, `b_*(τ) ∈ L²`, and there
is `b̃ ∈ X` with value `b_*(τ)`, weak Laplacian `lapB(τ)` and
`driftB(τ) - ½b_*(τ) = h lapB(τ) - σ b_*(τ) + 𝓑_*(τ) b̃` in `L²`. -/
theorem ae_phase (hR : LaplacianH1Regularity) (hD : IsUnstableBackground D)
    (hc : IsCoefficients D c) :
    ∀ᵐ τ, MemLp (D.bstar τ) 2 volume ∧ ∃ bt : X, Xclass bt = toL2 (D.bstar τ) ∧
      HasWeakLaplacian bt.toH1 (toL2 (D.lapB τ)) ∧
      toL2 (D.driftB τ) - (1 / 2 : ℝ) • toL2 (D.bstar τ) =
        D.h • toL2 (D.lapB τ) - D.σ • toL2 (D.bstar τ) + Lclass (c.B τ bt) := by
  have hT := hD.1.period_pos
  have hg := hD.2.graph
  filter_upwards [Y2.ae_memLp hT hg.value, hg.value.solenoidal, ae_laplacian hD, ae_mode hD]
    with τ hm hs hlap hmode
  refine ⟨hm, ?_⟩
  obtain ⟨F, hFv, hFL⟩ := hR _ _ hlap
  have hsol : F.value ∈ Leray.solenoidalSubspace := by
    rw [hFv]
    exact toL2_mem_solenoidal hm hs
  refine ⟨toX F hsol, hFv, hFL, ?_⟩
  -- the coupling is `𝓑_*(τ) b̃`
  have hBw := hc.B_weak τ (toX F hsol)
  have hval : Xval (toX F hsol) =ᵐ[volume] D.bstar τ := by
    have : Xval (toX F hsol) = ((toL2 (D.bstar τ) : L2Space) : SpatialField) := by
      unfold Xval Xclass
      rw [toX_toH1, hFv]
    rw [this]
    exact coeFn_toL2 hm
  have hcol : ∀ j, symTensorColumns (D.Ustar τ) (Xval (toX F hsol)) j =ᵐ[volume]
      symTensorColumns (D.Ustar τ) (D.bstar τ) j := by
    intro j
    filter_upwards [hval] with y hy
    simp only [symTensorColumns, hy]
  have hpair : ∀ φ, IsVectorTest φ →
      lerayDivPairing (symTensorColumns (D.Ustar τ) (D.bstar τ)) φ =
        -inner ℝ (Lclass (c.B τ (toX F hsol))) (toL2 φ) := by
    intro φ hφ
    rw [← L13.lerayDivPairing_congr hBw.1 hcol φ, hBw.2 φ hφ, neg_neg]
  have hzero : (D.σ - 1 / 2) • toL2 (D.bstar τ) + toL2 (D.driftB τ) - D.h • toL2 (D.lapB τ) -
      Lclass (c.B τ (toX F hsol)) = 0 := by
    apply L13.eq_zero_of_forall_vectorTest
    intro φ hφ
    have := hmode φ hφ
    rw [hpair φ hφ] at this
    rw [inner_sub_left, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left]
    linarith
  linear_combination (norm := module) hzero

end UnforcedLeray.Blueprint.ModeId
