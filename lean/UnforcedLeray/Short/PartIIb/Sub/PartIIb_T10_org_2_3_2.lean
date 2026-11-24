import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_of
import UnforcedLeray.Units.B0414.Orthogonal
import UnforcedLeray.Lib.LerayLp.Duality
import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# `PartII-b:T10/org/2/3/2`: `LerayCSymm` (complex symmetry of `𝐏` for general `1 < p < ∞`)

Source `the November 2 reference manuscript` (SP 2519-2524, B0414).
Generalizes `LerayCTranspose` (`Tasks/RawResidualFamily/LerayOnForce/CTranspose.lean`) from
`q0E` to general `p`. Route: split both fields into real and imaginary parts (`lerayC_apply`,
`B0414.reV_lerayC`, `B0414.imV_lerayC`), expand the bilinear `innerPair` into four real pairings,
and apply `RieszLp.integral_inner_lerayLp_symm` to each.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.B0414

/-- The bilinear dot product of two real images is the complex image of the real inner product. -/
theorem lerayCS_dotL_ofReV (u v : Space) :
    dotL (ofReV u) (ofReV v) = ((inner ℝ u v : ℝ) : ℂ) := by
  simp [dotL_apply, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three, ofReV_apply]
  ring

/-- Pairing of two real-image elements: the complex pairing is the cast of the real pairing. -/
theorem lerayCS_innerPair_ofReV (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (b : Lp Space (conjExp q) (volume : Measure Space))
    (a : Lp Space q (volume : Measure Space)) :
    innerPair q ((ofReV.compLpL (conjExp q) volume) b) ((ofReV.compLpL q volume) a) =
      ((∫ x, inner ℝ (b x) (a x) : ℝ) : ℂ) := by
  rw [innerPair_apply]
  have hae : ∀ᵐ x ∂(volume : Measure Space),
      dotL (((ofReV.compLpL (conjExp q) volume) b) x) (((ofReV.compLpL q volume) a) x) =
        ((inner ℝ (b x) (a x) : ℝ) : ℂ) := by
    filter_upwards [ofReV.coeFn_compLpL (μ := volume) (p := conjExp q) b,
      ofReV.coeFn_compLpL (μ := volume) (p := q) a] with x h1 h2
    rw [h1, h2, lerayCS_dotL_ofReV]
  rw [integral_congr_ae hae]
  exact integral_ofReal

/-- Decomposition of an `L^r` field into its real and imaginary parts. -/
theorem lerayCS_decomp (r : ℝ≥0∞) [Fact (1 ≤ r)] (g : Lp CVec3 r (volume : Measure Space)) :
    g = (ofReV.compLpL r volume) ((reV.compLpL r volume) g) +
      Complex.I • (ofReV.compLpL r volume) ((imV.compLpL r volume) g) := by
  rw [I_smul_ofReV_compLpL]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofReV.compLpL r volume (reV.compLpL r volume g))
      (ofImV.compLpL r volume (imV.compLpL r volume g)),
    ofReV.coeFn_compLpL (μ := volume) (p := r) (reV.compLpL r volume g),
    ofImV.coeFn_compLpL (μ := volume) (p := r) (imV.compLpL r volume g),
    reV.coeFn_compLpL (μ := volume) (p := r) g,
    imV.coeFn_compLpL (μ := volume) (p := r) g] with x h0 h1 h2 h3 h4
  rw [h0, Pi.add_apply, h1, h2, h3, h4]
  exact (ofReV_reV_add_ofImV_imV (g x)).symm

/-- `innerPair` is `ℂ`-bilinear: it expands into four real pairings of real and imaginary parts. -/
theorem lerayCS_expand (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (g : Lp CVec3 (conjExp q) (volume : Measure Space)) (h : Lp CVec3 q (volume : Measure Space)) :
    innerPair q g h =
      ((∫ x, inner ℝ ((reV.compLpL (conjExp q) volume) g x)
        ((reV.compLpL q volume) h x) : ℝ) : ℂ) +
      Complex.I * ((∫ x, inner ℝ ((reV.compLpL (conjExp q) volume) g x)
        ((imV.compLpL q volume) h x) : ℝ) : ℂ) +
      Complex.I * ((∫ x, inner ℝ ((imV.compLpL (conjExp q) volume) g x)
        ((reV.compLpL q volume) h x) : ℝ) : ℂ) +
      Complex.I * (Complex.I * ((∫ x, inner ℝ ((imV.compLpL (conjExp q) volume) g x)
        ((imV.compLpL q volume) h x) : ℝ) : ℂ)) := by
  conv_lhs => rw [lerayCS_decomp (conjExp q) g, lerayCS_decomp q h]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, lerayCS_innerPair_ofReV]
  ring

/-- Real symmetry of the Leray projection under the `L^p`–`L^{p'}` pairing. -/
theorem lerayCS_real_symm (p : ℝ≥0∞) [Fact (1 ≤ p)] (h1 : 1 < p) (h2 : p ≠ ⊤)
    (h1' : 1 < conjExp p) (h2' : conjExp p ≠ ⊤)
    (a : Lp Space p (volume : Measure Space))
    (b : Lp Space (conjExp p) (volume : Measure Space)) :
    ∫ x, inner ℝ (b x) (lerayLp p h1 h2 a x) =
      ∫ x, inner ℝ (lerayLp (conjExp p) h1' h2' b x) (a x) :=
  calc ∫ x, inner ℝ (b x) (lerayLp p h1 h2 a x)
      = ∫ x, inner ℝ (lerayLp p h1 h2 a x) (b x) := by
        congr 1; funext x; exact real_inner_comm _ _
    _ = ∫ x, inner ℝ (a x) (lerayLp (conjExp p) h1' h2' b x) :=
        UnforcedLeray.RieszLp.integral_inner_lerayLp_symm h1 h2 h1' h2' a b
    _ = ∫ x, inner ℝ (lerayLp (conjExp p) h1' h2' b x) (a x) := by
        congr 1; funext x; exact real_inner_comm _ _

/-- **Leaf `PartII-b:T10/org/2/3/2`: complex symmetry of `𝐏`** (`1 < p < ∞`). -/
theorem lerayCSymm_proof : UnforcedLeray.Short.IIb.LerayCSymm := by
  intro p _ h1 h2 h1' h2' G F
  rw [lerayCS_expand p G (lerayC p h1 h2 F), lerayCS_expand p (lerayC (conjExp p) h1' h2' G) F]
  simp only [reV_lerayC, imV_lerayC, lerayCS_real_symm p h1 h2 h1' h2']

end UnforcedLeray.Short.IIb
