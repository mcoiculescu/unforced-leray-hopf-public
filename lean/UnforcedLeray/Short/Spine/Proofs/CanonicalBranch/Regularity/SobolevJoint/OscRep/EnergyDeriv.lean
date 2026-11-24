import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1

/-!


Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140 (the radial operator `D f = f'' + f'/r - 4f/r^2 + (r/2) f' + 2f` and the weight
`w = 4 π e^{r²/4} r`).

Proof: product rule for `F = w χ² Re(conj φ · φ')`. The eigenvalue equation in second-order
form `φ'' = c₁ φ' + c₀ φ` (`OscOde.deriv2`, with `c₁ = -(1/r + r/2)`, `c₀ = 4/r² - 2 - n`)
and the identity `w' = -w c₁` cancel the `φ'` terms, leaving
`χ² w |φ'|² + χ² w c₀ |φ|² + 2 w χ χ' Re(conj φ · φ')`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

namespace OscEnergyDerivAux

/-- `Re (conj z · z) = |z|²`. -/
theorem re_conj_mul_self (z : ℂ) : ((starRingEnd ℂ z) * z).re = ‖z‖ ^ 2 := by
  first
  | (rw [Complex.conj_mul']; exact Complex.ofReal_re _)
  | (rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re])
  | (rw [Complex.conj_mul']; simp)
  | (simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]; ring)

/-- Real part of `conj p · (a q + b p)` for real coefficients `a, b`. -/
theorem re_conj_mul_lin (p q : ℂ) (a b : ℝ) :
    ((starRingEnd ℂ p) * ((a : ℂ) * q + (b : ℂ) * p)).re =
      a * ((starRingEnd ℂ p) * q).re + b * ‖p‖ ^ 2 := by
  have h : (starRingEnd ℂ p) * ((a : ℂ) * q + (b : ℂ) * p) =
      (a : ℂ) * ((starRingEnd ℂ p) * q) + (b : ℂ) * ((starRingEnd ℂ p) * p) := by
    ring
  rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, re_conj_mul_self]

/-- Derivative of the weight `w = 4π e^{r²/4} r`. -/
theorem hasDerivAt_oscWeight (r : ℝ) :
    HasDerivAt oscWeight (4 * Real.pi * (Real.exp (r ^ 2 / 4) * (r / 2)) * r +
      4 * Real.pi * Real.exp (r ^ 2 / 4) * 1) r := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 4) (r / 2) r :=
    ((hasDerivAt_pow 2 r).div_const 4).congr_deriv (by norm_num <;> ring)
  have h2 : HasDerivAt (fun s : ℝ => 4 * Real.pi * Real.exp (s ^ 2 / 4))
      (4 * Real.pi * (Real.exp (r ^ 2 / 4) * (r / 2))) r :=
    (h1.exp).const_mul (4 * Real.pi)
  have h3 := h2.mul (hasDerivAt_id' r)
  exact h3

end OscEnergyDerivAux

open OscEnergyDerivAux in
/-- The derivative of the weighted cutoff energy flux; this is the Prop `OscEnergyDeriv`. -/
theorem oscEnergyDeriv_proof : OscEnergyDeriv := by
  unfold OscEnergyDeriv
  intro n φ χ hφ hχ r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
    first
    | simp
    | decide
  have hmem : Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds (Set.mem_Ioi.2 hr)
  -- smoothness of `φ` and `φ'` at `r > 0`
  have hφc : ContDiffAt ℝ ∞ φ r := hφ.1.contDiffAt hmem
  have hφd : HasDerivAt φ (deriv φ r) r := (hφc.differentiableAt hne).hasDerivAt
  have hq_cd : ContDiffOn ℝ ∞ (deriv φ) (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hφ.1).2
  have hqc : ContDiffAt ℝ ∞ (deriv φ) r := hq_cd.contDiffAt hmem
  have hqd : HasDerivAt (deriv φ) (deriv (deriv φ) r) r :=
    (hqc.differentiableAt hne).hasDerivAt
  -- smoothness of `χ`
  have hχd : HasDerivAt χ (deriv χ r) r := ((hχ.differentiable hne) r).hasDerivAt
  -- conjugate of `φ`
  have hconj : HasDerivAt (fun s => starRingEnd ℂ (φ s)) (starRingEnd ℂ (deriv φ r)) r := by
    have h := hφd.star
    first
    | exact h
    | simpa [Complex.star_def] using h
  -- the complex product `conj φ · φ'`
  have hG : HasDerivAt (fun s => starRingEnd ℂ (φ s) * deriv φ s)
      (starRingEnd ℂ (deriv φ r) * deriv φ r + starRingEnd ℂ (φ r) * deriv (deriv φ) r) r :=
    hconj.mul hqd
  -- its real part
  have hR : HasDerivAt (fun s => (starRingEnd ℂ (φ s) * deriv φ s).re)
      ((starRingEnd ℂ (deriv φ r) * deriv φ r +
        starRingEnd ℂ (φ r) * deriv (deriv φ) r).re) r := by
    have h := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt r hG
    first
    | exact h
    | simpa using h
  have hχ2 : HasDerivAt (fun s => χ s ^ 2) (2 * χ r * deriv χ r) r :=
    (hχd.pow 2).congr_deriv (by norm_num)
  have hW := hasDerivAt_oscWeight r
  have hF := (hW.mul hχ2).mul hR
  -- second-order form of the eigenvalue equation, with real coefficients
  have hq2 : deriv (deriv φ) r = ((-(1 / r + r / 2) : ℝ) : ℂ) * deriv φ r +
      ((4 / r ^ 2 - 2 - (n : ℝ) : ℝ) : ℂ) * φ r :=
    OscOde.deriv2 hφ hr
  have hRe : (starRingEnd ℂ (deriv φ r) * deriv φ r +
      starRingEnd ℂ (φ r) * deriv (deriv φ) r).re =
      ‖deriv φ r‖ ^ 2 + (-(1 / r + r / 2)) * (starRingEnd ℂ (φ r) * deriv φ r).re +
        (4 / r ^ 2 - 2 - (n : ℝ)) * ‖φ r‖ ^ 2 := by
    rw [hq2, Complex.add_re, re_conj_mul_self, re_conj_mul_lin]
    ring
  refine hF.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.pow_apply]
  rw [hRe]
  unfold oscWeight
  first
  | (field_simp; ring)
  | (push_cast; field_simp; ring)
  | (norm_num; field_simp; ring)
  | (simp; field_simp; ring)

end UnforcedLeray.Short.Spine
