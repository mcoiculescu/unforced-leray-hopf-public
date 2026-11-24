import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Units.B0121.Spectral
import UnforcedLeray.Units.B0121.Planar

/-!
# Part I, task `PartI:S10a`: the seed mode lies in every power domain `X_{G,j}` (decomposition)

Source of record: `the November 2 reference manuscript`, lines 619-623 and
913-929 (the Gaussian derivative bounds of `q` make `U_G q` Schwartz, hence `q ∈ 𝒟(D^j)` for all
`j`).

`SeedModeRegularity` (proved: `seedModeRegularity_proof`) gives a smooth representative `h'` of
the profile with Gaussian derivative bounds.  Two leaves remain: the identification of the planar
function of `q` with `seedPlanar h'`, and the criterion that a planar function with Gaussian
derivative bounds lies in every `X_{G,j}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

/-- **Leaf 1** (planar representation; source lines 619-623): if the profile `h'` agrees with
`h` almost everywhere on `(0,∞)`, the planar function `B0121.planar (hh.toLp h)`
(= `h(r) e^{2iϑ}`, `angularTwoField`) equals `seedPlanar h' = Ang.ofProfile 2 h'` almost
everywhere on `ℝ × ℝ` (through `Complex.equivRealProd.symm`).  Sketch: both are
`profile(‖z‖) e^{2i arg z}`; polar coordinates carry null sets of `(0,∞)` to null sets of `ℝ²`
(`polarCoord` is measure preserving up to the weight `r`). -/
def SeedPlanarBridge : Prop :=
  ∀ (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (h' : ℝ → ℂ),
    h' =ᵐ[volume.restrict (Ioi (0 : ℝ))] h →
      B0121.planar (hh.toLp h) =ᵐ[volume]
        fun z : ℝ × ℝ => seedPlanar h' (Complex.equivRealProd.symm z)

/-- **Leaf 2** (Gaussian-class functions are in every power domain; source lines 913-929): if
the planar function of `q ∈ X_G` is a smooth `F` all of whose derivatives are bounded by a
polynomial times `e^{-|y|²/4}`, then `q ∈ X_{G,j}` for every `j`.  Sketch: by
`B0121.mem_XGj_iff_weakDerivs` it suffices to give weak derivatives `∂^α q ∈ L²(G⁻¹ dy)` for
`|α| ≤ j`; take the classical derivatives (weak = classical for `C^∞`,
`B0121.WeakDeriv`), and `|∂^α F|² e^{|y|²/4} ≤ C (1+|y|)^{2N} e^{-|y|²/4}` is integrable. -/
def GaussianSmoothMemXGj : Prop :=
  ∀ (q : B0010.XG) (F : ℂ → ℂ), ContDiff ℝ ∞ F →
    (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ k F y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) →
    B0121.planar q =ᵐ[volume] (fun z : ℝ × ℝ => F (Complex.equivRealProd.symm z)) →
      ∀ j : ℕ, q ∈ B0121.XGj j

/-- **`PartI:S10a` from the two leaves**. -/
theorem seed_mode_mem_XGj_of (hreg : SeedModeRegularity) (h1 : SeedPlanarBridge)
    (h2 : GaussianSmoothMemXGj) {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) (j : ℕ) : q ∈ B0121.XGj j := by
  have hh : MemLp (⇑q) 2 B0010.xGMeasure := Lp.memLp q
  have hq : hh.toLp (⇑q) = q := Lp.toLp_coeFn q hh
  rw [← hq] at hI
  obtain ⟨_, _, h', hae, hcd, hder, -⟩ := hreg lam (⇑q) hh l hI
  have hpl := h1 (⇑q) hh h' hae
  rw [hq] at hpl
  exact h2 q (seedPlanar h') hcd hder (by simpa using hpl) j

end UnforcedLeray.Short.PartI
