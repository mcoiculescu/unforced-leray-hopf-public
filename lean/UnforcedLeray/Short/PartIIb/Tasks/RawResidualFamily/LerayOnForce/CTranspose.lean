import UnforcedLeray.Short.PartIIb.Sub.R1_3

/-!
# `LerayCTranspose`: the complex transpose of the spatial Leray projection

Target `UnforcedLeray.Short.IIb.LerayCTranspose` (`Sub/R1_3.lean`). Source:
`the November 2 reference manuscript` lines 2519-2524 (`paper/main.tex` 7336-7344).

Route: `innerPair q0E` is `ℂ`-bilinear, so each side expands into four real pairings of the real
and imaginary parts (`lerayCT_expand`). The real and imaginary parts of `lerayC F` are
`𝔓(Re F)` and `𝔓(Im F)` (`B0414.reV_lerayC`, `B0414.imV_lerayC`). Each real pairing is symmetric
by `RieszLp.integral_inner_lerayLp_symm` (`lerayCT_real_symm`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
  UnforcedLeray.B0412

/-- The bilinear dot product of two real images is the complex image of the real inner product. -/
theorem lerayCT_dotL_ofReV (u v : Space) :
    dotL (ofReV u) (ofReV v) = ((inner ℝ u v : ℝ) : ℂ) := by
  simp [dotL_apply, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three, ofReV_apply]
  ring

/-- Pairing of two real-image elements: the complex pairing is the cast of the real pairing. -/
theorem lerayCT_innerPair_ofReV (q : ℝ≥0∞) [Fact (1 ≤ q)]
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
    rw [h1, h2, lerayCT_dotL_ofReV]
  rw [integral_congr_ae hae]
  exact integral_ofReal

/-- Decomposition of an `L^r` field into its real and imaginary parts. -/
theorem lerayCT_decomp (r : ℝ≥0∞) [Fact (1 ≤ r)] (g : Lp CVec3 r (volume : Measure Space)) :
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
theorem lerayCT_expand (q : ℝ≥0∞) [Fact (1 ≤ q)]
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
  conv_lhs => rw [lerayCT_decomp (conjExp q) g, lerayCT_decomp q h]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, lerayCT_innerPair_ofReV]
  ring

/-- Real symmetry of the Leray projection under the `L^{q₀}`–`L^{q₀'}` pairing. -/
theorem lerayCT_real_symm (a : Lp Space q0E (volume : Measure Space))
    (b : Lp Space (conjExp q0E) (volume : Measure Space)) :
    ∫ x, inner ℝ (b x) (lerayLp q0E one_lt_q0E q0E_ne_top a x) =
      ∫ x, inner ℝ (lerayLp (conjExp q0E) one_lt_conjExp_q0E conjExp_q0E_ne_top b x) (a x) :=
  (UnforcedLeray.RieszLp.integral_inner_lerayLp_symm one_lt_conjExp_q0E conjExp_q0E_ne_top
    one_lt_q0E q0E_ne_top b a).symm

/-- **Leaf `PartII-b:R1/3/1`: the complex transpose of the spatial Leray projection**
(SP 2519-2524, `paper/main.tex` 7336-7344, B0414). -/
theorem lerayCTranspose : UnforcedLeray.Short.IIb.LerayCTranspose := by
  unfold LerayCTranspose
  intro G F
  have e1 := innerPair_apply G (lerayC q0E one_lt_q0E q0E_ne_top F)
  have e2 := innerPair_apply (lerayC (conjExp q0E) one_lt_conjExp_q0E conjExp_q0E_ne_top G) F
  rw [← e1, ← e2, lerayCT_expand q0E G (lerayC q0E one_lt_q0E q0E_ne_top F),
    lerayCT_expand q0E (lerayC (conjExp q0E) one_lt_conjExp_q0E conjExp_q0E_ne_top G) F]
  simp only [UnforcedLeray.B0414.reV_lerayC, UnforcedLeray.B0414.imV_lerayC, lerayCT_real_symm]

end UnforcedLeray.Short.IIb
