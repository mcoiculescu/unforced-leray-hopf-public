import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_of
import UnforcedLeray.Lib.LerayLp.Helmholtz
import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# `PartII-b:T10/org/2/3/4`: `FundLemmaC` (fundamental lemma for `L^q(ℝ³;ℂ³)`)

Source `the November 2 reference manuscript` (SP solenoidal separation step).
Route: for a real smooth compactly supported `g` and coordinate `j`, the test field
`F = g • e_j` gives `∫ g · w_j = 0`. Each coordinate `w_j` is locally integrable (it is the image
of `w ∈ L^q` under the continuous coordinate functional), so
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` makes `w_j = 0` a.e. for every `j`, and the
`Lp` element `w` is zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp

/-- Each coordinate of an `L^q(ℝ³;ℂ³)` field is locally integrable (`q ≥ 1`). -/
theorem fundLemmaC_coord_locInt (q : ℝ≥0∞) [Fact (1 ≤ q)] (w : Lp CVec3 q (volume : Measure Space))
    (j : Fin 3) : LocallyIntegrable (fun x => w x j) (volume : Measure Space) := by
  have hm := (Lp.memLp ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).compLpL q
    (volume : Measure Space) w)).locallyIntegrable (Fact.out : 1 ≤ q)
  exact hm.congr (((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).coeFn_compLpL
    (μ := (volume : Measure Space)) (p := q) w).mono fun x hx => by
      rw [hx]; rfl)

/-- Pointwise value of the test pairing: `⟨g • e_j, w⟩ = g · w_j`. -/
theorem fundLemmaC_dot (j : Fin 3) (r : ℝ) (z : CVec3) :
    dotL (r • (EuclideanSpace.single j (1 : ℂ) : CVec3)) z = (r : ℂ) * z j := by
  simp [dotL_apply, EuclideanSpace.single_apply, Fin.sum_univ_three]

theorem fundLemmaC_proof : UnforcedLeray.Short.IIb.FundLemmaC := by
  intro q _ w hw
  have hcomp : ∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure Space), w x j = 0 := by
    intro j
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (fundLemmaC_coord_locInt q w j)
      (fun g hg hgc => ?_)
    set v : CVec3 := EuclideanSpace.single j (1 : ℂ) with hv
    set F : Space → CVec3 := fun x => g x • v with hFdef
    have hFc : ContDiff ℝ ∞ F := hg.smul contDiff_const
    have hFs : HasCompactSupport F := hgc.smul_right
    have hFcont : Continuous F := hFc.continuous
    have hFm : MemLp F (conjExp q) (volume : Measure Space) :=
      hFcont.memLp_of_hasCompactSupport hFs
    have hz := hw F hFc hFs hFm
    have e : ∫ y, dotL ((hFm.toLp F) y) (w y) = ∫ y, g y • w y j := by
      refine integral_congr_ae ?_
      filter_upwards [hFm.coeFn_toLp] with y hy
      rw [hy, hFdef]
      simp only
      rw [fundLemmaC_dot]
      simp [Complex.real_smul]
    rw [innerPair_apply, e] at hz
    exact hz
  have hall : ∀ᵐ x ∂(volume : Measure Space), ∀ j : Fin 3, w x j = 0 := ae_all_iff.2 hcomp
  apply Lp.ext
  filter_upwards [hall, Lp.coeFn_zero CVec3 q (volume : Measure Space)] with x hx h0
  rw [h0]
  ext i
  simp [hx i]

end UnforcedLeray.Short.IIb
