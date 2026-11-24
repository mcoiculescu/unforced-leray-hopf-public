import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!
# Leaf A2: the radial oscillator on a Gaussian-polynomial profile

Proves `UnforcedLeray.Short.Spine.OscProfOde` (`Sub/SP_CAN4_4_1.lean`): for every polynomial `p`
and `r > 0`, `oscillatorD (profFun p) r = profFun (lag p) r`.

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140.

Method. Write `Q_p(s) = qp p s = p(s) e^{-s/4}`, so `profFun p r = r * r * Q_p(r²)`. With
`Q₁ = p' - p/4` and `Q₂ = Q₁' - Q₁/4` (so `Q_p' = Q_{Q₁}` and `Q_p'' = Q_{Q₂}`), the chain rule
gives, for all real `r`,
  `f' = 2r Q_p + 2r³ Q₁`,  `f'' = 2 Q_p + 10 r² Q₁ + 4 r⁴ Q₂`  (`f = profFun p`),
and the radial form `f'' + f'/r - 4f/r² + (r/2) f' + 2f` collapses to
`r² (4 r² Q₂ + (12 + r²) Q₁ + 3 Q_p)`, which is `r² Q_{lag p}(r²)` by `bracket_qp`.

The file adds no declarations beyond the helpers and the main theorem, and no proof escapes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- The map `x ↦ (x : ℂ)` has derivative `1`. -/
theorem oscProf_hasDerivAt_ofReal (r : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r := by
  simpa using (hasDerivAt_id r).ofReal_comp

/-- The real map `x ↦ x ^ 2` has derivative `2 r`. -/
theorem oscProf_hasDerivAt_sq (r : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
  simpa using hasDerivAt_pow 2 r

/-- Chain rule for `x ↦ qp q (x²)` (`qp q` has derivative `qp (q' - q/4)`). -/
theorem oscProf_hasDerivAt_qp_sq (q : ℂ[X]) (r : ℝ) :
    HasDerivAt (fun x : ℝ => UnforcedLeray.B0094.qp q (x ^ 2))
      (UnforcedLeray.B0094.qp (Polynomial.derivative q - (1 / 4 : ℂ) • q) (r ^ 2) *
        (2 * (r : ℂ))) r := by
  have h := (UnforcedLeray.B0094.hasDerivAt_qp q (r ^ 2)).scomp r (oscProf_hasDerivAt_sq r)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- `profFun p x = x * x * qp p (x²)` for every real `x`. -/
theorem oscProf_profFun_eq (p : ℂ[X]) (x : ℝ) :
    UnforcedLeray.B0094.profFun p x =
      (x : ℂ) * (x : ℂ) * UnforcedLeray.B0094.qp p (x ^ 2) := by
  simp only [UnforcedLeray.B0094.profFun, UnforcedLeray.B0094.gauss, UnforcedLeray.B0094.qp]
  push_cast
  ring

/-- First derivative of `profFun p` at every real point. -/
theorem oscProf_hasDerivAt_profFun (p : ℂ[X]) (r : ℝ) :
    HasDerivAt (UnforcedLeray.B0094.profFun p)
      (2 * (r : ℂ) * UnforcedLeray.B0094.qp p (r ^ 2) +
        2 * ((r : ℂ) * (r : ℂ) * (r : ℂ)) *
          UnforcedLeray.B0094.qp (Polynomial.derivative p - (1 / 4 : ℂ) • p) (r ^ 2)) r := by
  have hf : UnforcedLeray.B0094.profFun p =
      fun x : ℝ => (x : ℂ) * (x : ℂ) * UnforcedLeray.B0094.qp p (x ^ 2) := by
    funext x
    exact oscProf_profFun_eq p x
  rw [hf]
  have h := ((oscProf_hasDerivAt_ofReal r).mul (oscProf_hasDerivAt_ofReal r)).mul
    (oscProf_hasDerivAt_qp_sq p r)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- The first derivative of `profFun p`, as a function. -/
theorem oscProf_deriv_profFun (p : ℂ[X]) :
    deriv (UnforcedLeray.B0094.profFun p) = fun x : ℝ =>
      2 * (x : ℂ) * UnforcedLeray.B0094.qp p (x ^ 2) +
        2 * ((x : ℂ) * (x : ℂ) * (x : ℂ)) *
          UnforcedLeray.B0094.qp (Polynomial.derivative p - (1 / 4 : ℂ) • p) (x ^ 2) := by
  funext x
  exact (oscProf_hasDerivAt_profFun p x).deriv

/-- Derivative of the first-derivative expression (product and chain rules). -/
theorem oscProf_hasDerivAt_g1 (p : ℂ[X]) (r : ℝ) :
    HasDerivAt (fun x : ℝ =>
        2 * (x : ℂ) * UnforcedLeray.B0094.qp p (x ^ 2) +
          2 * ((x : ℂ) * (x : ℂ) * (x : ℂ)) *
            UnforcedLeray.B0094.qp (Polynomial.derivative p - (1 / 4 : ℂ) • p) (x ^ 2))
      (2 * UnforcedLeray.B0094.qp p (r ^ 2) +
        10 * ((r : ℂ) * (r : ℂ)) *
          UnforcedLeray.B0094.qp (Polynomial.derivative p - (1 / 4 : ℂ) • p) (r ^ 2) +
        4 * ((r : ℂ) * (r : ℂ) * (r : ℂ) * (r : ℂ)) *
          UnforcedLeray.B0094.qp (Polynomial.derivative (Polynomial.derivative p -
              (1 / 4 : ℂ) • p) - (1 / 4 : ℂ) • (Polynomial.derivative p - (1 / 4 : ℂ) • p))
            (r ^ 2)) r := by
  have h1 := ((oscProf_hasDerivAt_ofReal r).const_mul 2).mul (oscProf_hasDerivAt_qp_sq p r)
  have h2 := ((((oscProf_hasDerivAt_ofReal r).mul (oscProf_hasDerivAt_ofReal r)).mul
      (oscProf_hasDerivAt_ofReal r)).const_mul 2).mul
    (oscProf_hasDerivAt_qp_sq (Polynomial.derivative p - (1 / 4 : ℂ) • p) r)
  refine (h1.add h2).congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- The second derivative of `profFun p`, as a function. -/
theorem oscProf_deriv_deriv_profFun (p : ℂ[X]) :
    deriv (deriv (UnforcedLeray.B0094.profFun p)) = fun x : ℝ =>
      2 * UnforcedLeray.B0094.qp p (x ^ 2) +
        10 * ((x : ℂ) * (x : ℂ)) *
          UnforcedLeray.B0094.qp (Polynomial.derivative p - (1 / 4 : ℂ) • p) (x ^ 2) +
        4 * ((x : ℂ) * (x : ℂ) * (x : ℂ) * (x : ℂ)) *
          UnforcedLeray.B0094.qp (Polynomial.derivative (Polynomial.derivative p -
              (1 / 4 : ℂ) • p) - (1 / 4 : ℂ) • (Polynomial.derivative p - (1 / 4 : ℂ) • p))
            (x ^ 2) := by
  rw [oscProf_deriv_profFun p]
  funext x
  exact (oscProf_hasDerivAt_g1 p x).deriv

/-- **Leaf A2** (`OscProfOde`): the radial oscillator on a profile is the profile of the
lag operator, for every polynomial `p` and every `r > 0`. -/
theorem oscProfOde_proof : UnforcedLeray.Short.Spine.OscProfOde := by
  unfold UnforcedLeray.Short.Spine.OscProfOde
  intro p r hr
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hb := UnforcedLeray.B0094.bracket_qp p (r ^ 2)
  push_cast at hb
  unfold Blueprint.Planar.oscillatorD
  rw [congrFun (oscProf_deriv_deriv_profFun p) r, congrFun (oscProf_deriv_profFun p) r,
    oscProf_profFun_eq p r, oscProf_profFun_eq (UnforcedLeray.B0094.lag p) r, ← hb]
  field_simp
  ring

end UnforcedLeray.Short.Spine
