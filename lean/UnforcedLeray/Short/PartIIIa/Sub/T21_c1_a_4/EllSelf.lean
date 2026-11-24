import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Of

/-!
# `PartIII-a:T21/c1/a/4/3`: `seedEll h h = 1`

Source: `the November 2 reference manuscript` lines 603-610.
Proves `SeedEllSelf` (defined in `Of.lean`).  Uses `l f = seedEll h f` on `X_G`
(`SeedFunctional`), `ell_q : l q = 1` (`IsSeedXG`), and the fact that the `X_G` representative
`hh.toLp h` agrees with `h` almost everywhere on `(0, ∞)` (`xGMeasure` is
`volume.restrict (Ioi 0)` with the strictly positive density `xGDensity`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa.SeedEllSelfAux

/-- On `(0, ∞)`, the `X_G` representative of `h` agrees with `h` almost everywhere
(Lebesgue measure restricted to `(0, ∞)`). -/
lemma ae_toLp_eq (h : ℝ → ℂ) (hh : MemLp h 2 UnforcedLeray.B0010.xGMeasure) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), (hh.toLp h : ℝ → ℂ) r = h r := by
  have hgood : ∀ᵐ x ∂UnforcedLeray.B0010.xGMeasure, (hh.toLp h : ℝ → ℂ) x = h x :=
    MemLp.coeFn_toLp hh
  unfold UnforcedLeray.B0010.xGMeasure at hgood
  have h1 := (ae_withDensity_iff
    (UnforcedLeray.B0010.measurable_xGDensity.coe_nnreal_ennreal)).1 hgood
  have hw : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ((UnforcedLeray.B0010.xGDensity r : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hpos : (0 : ℝ) < (UnforcedLeray.B0010.xGDensity r : ℝ) := by
      rw [UnforcedLeray.B0010.coe_xGDensity hr]
      exact mul_pos (inv_pos.2 (UnforcedLeray.B0010.radialGaussianWeight_pos r)) hr
    exact ENNReal.coe_ne_zero.2 (fun h0 => by rw [h0] at hpos; simp at hpos)
  filter_upwards [h1, hw] with r h1r hwr
  exact h1r hwr

theorem seedEll_toLp_eq (h : ℝ → ℂ) (hh : MemLp h 2 UnforcedLeray.B0010.xGMeasure) :
    UnforcedLeray.Short.PartI.seedEll h (hh.toLp h : ℝ → ℂ) =
      UnforcedLeray.Short.PartI.seedEll h h := by
  unfold UnforcedLeray.Short.PartI.seedEll
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_toLp_eq h hh] with r hr
  rw [hr]

end UnforcedLeray.Short.IIIa.SeedEllSelfAux

theorem seedEllSelf_proof : UnforcedLeray.Short.IIIa.SeedEllSelf := by
  unfold UnforcedLeray.Short.IIIa.SeedEllSelf
  intro hSF lam h hh ℓ hIS
  have e1 := (hSF lam h hh ℓ hIS).2.2.2.1 (hh.toLp h)
  rw [hIS.ell_q] at e1
  rw [UnforcedLeray.Short.IIIa.SeedEllSelfAux.seedEll_toLp_eq h hh] at e1
  exact e1.symm
