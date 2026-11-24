import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Of

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : leaf (L4) `BrkDerivSClosed`

Source of record: `the November 2 reference manuscript` (73 pages), 4957-4958 (the
time derivative `∂_s = ν∂_a` at fixed `x`), 4963 (`a = 1 + νs`, `G = a⁻² e^{-|y|²/(4a)}`), 4973 (the
closed form `b_j = G·bkP`).

With `b_j(s, x) = G(a(s), y)·P(A^y(s), a(s), y)` (`y = x_j` fixed, `a' = ν`, `(A^y)' = M'`), the product
rule gives `∂_s b_j = G·(bkP M' a y + ν·bkPa M a y)`, where `bkPa` absorbs the derivative of `G`
and of the `(2a)⁻¹` factor of `bkP`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Components of `bkP` -/

/-- First component of `bkP M a y`, expanded (`Jy = (-y₂, y₁)`). -/
lemma bkL4_fst (M : Mat3) (a : ℝ) (y : ℝ × ℝ) :
    (bkP M a y).1 = M 0 0 * (-y.2) + M 0 2 * y.1 + (M 2 0 * y.1 + M 2 2 * y.2)
      + ((y.1 * (M 0 0 * y.1 + M 0 2 * y.2) + y.2 * (M 2 0 * y.1 + M 2 2 * y.2)) / (2 * a))
        * (-y.2) := by
  simp only [bkP, merApply, Jrot, bkDot, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
  ring

/-- Second component of `bkP M a y`, expanded. -/
lemma bkL4_snd (M : Mat3) (a : ℝ) (y : ℝ × ℝ) :
    (bkP M a y).2 = M 2 0 * (-y.2) + M 2 2 * y.1 - (M 0 0 * y.1 + M 0 2 * y.2)
      + ((y.1 * (M 0 0 * y.1 + M 0 2 * y.2) + y.2 * (M 2 0 * y.1 + M 2 2 * y.2)) / (2 * a))
        * y.1 := by
  simp only [bkP, merApply, Jrot, bkDot, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]

/-! ## 2. Real-valued derivatives of the components -/

/-- Derivative of the first component along a path with entries `p ·` and `a`. -/
lemma bkL4_P1 (p00 p02 p20 p22 a : ℝ → ℝ) (d00 d02 d20 d22 ν s y1 y2 : ℝ)
    (h00 : HasDerivAt p00 d00 s) (h02 : HasDerivAt p02 d02 s)
    (h20 : HasDerivAt p20 d20 s) (h22 : HasDerivAt p22 d22 s)
    (ha : HasDerivAt a ν s) (hpos : a s ≠ 0) :
    HasDerivAt (fun t => p00 t * (-y2) + p02 t * y1 + (p20 t * y1 + p22 t * y2)
        + ((y1 * (p00 t * y1 + p02 t * y2) + y2 * (p20 t * y1 + p22 t * y2)) / (2 * a t))
          * (-y2))
      (d00 * (-y2) + d02 * y1 + (d20 * y1 + d22 * y2)
        + ((y1 * (d00 * y1 + d02 * y2) + y2 * (d20 * y1 + d22 * y2)) / (2 * a s)
          - (y1 * (p00 s * y1 + p02 s * y2) + y2 * (p20 s * y1 + p22 s * y2)) * ν / (2 * a s ^ 2))
          * (-y2)) s := by
  have hN : HasDerivAt (fun t => y1 * (p00 t * y1 + p02 t * y2) + y2 * (p20 t * y1 + p22 t * y2))
      (y1 * (d00 * y1 + d02 * y2) + y2 * (d20 * y1 + d22 * y2)) s :=
    ((((h00.mul_const y1).add (h02.mul_const y2)).const_mul y1).add
      (((h20.mul_const y1).add (h22.mul_const y2)).const_mul y2))
  have h2a : HasDerivAt (fun t => 2 * a t) (2 * ν) s := ha.const_mul 2
  have hD : HasDerivAt
      (fun t => (y1 * (p00 t * y1 + p02 t * y2) + y2 * (p20 t * y1 + p22 t * y2)) / (2 * a t))
      (((y1 * (d00 * y1 + d02 * y2) + y2 * (d20 * y1 + d22 * y2)) * (2 * a s)
          - (y1 * (p00 s * y1 + p02 s * y2) + y2 * (p20 s * y1 + p22 s * y2)) * (2 * ν))
        / (2 * a s) ^ 2) s :=
    hN.div h2a (mul_ne_zero two_ne_zero hpos)
  have hL : HasDerivAt (fun t => p00 t * (-y2) + p02 t * y1 + (p20 t * y1 + p22 t * y2))
      (d00 * (-y2) + d02 * y1 + (d20 * y1 + d22 * y2)) s :=
    ((h00.mul_const (-y2)).add (h02.mul_const y1)).add ((h20.mul_const y1).add (h22.mul_const y2))
  refine (hL.add (hD.mul_const (-y2))).congr_deriv ?_
  field_simp

/-- Derivative of the second component along a path with entries `p ·` and `a`. -/
lemma bkL4_P2 (p00 p02 p20 p22 a : ℝ → ℝ) (d00 d02 d20 d22 ν s y1 y2 : ℝ)
    (h00 : HasDerivAt p00 d00 s) (h02 : HasDerivAt p02 d02 s)
    (h20 : HasDerivAt p20 d20 s) (h22 : HasDerivAt p22 d22 s)
    (ha : HasDerivAt a ν s) (hpos : a s ≠ 0) :
    HasDerivAt (fun t => p20 t * (-y2) + p22 t * y1 - (p00 t * y1 + p02 t * y2)
        + ((y1 * (p00 t * y1 + p02 t * y2) + y2 * (p20 t * y1 + p22 t * y2)) / (2 * a t))
          * y1)
      (d20 * (-y2) + d22 * y1 - (d00 * y1 + d02 * y2)
        + ((y1 * (d00 * y1 + d02 * y2) + y2 * (d20 * y1 + d22 * y2)) / (2 * a s)
          - (y1 * (p00 s * y1 + p02 s * y2) + y2 * (p20 s * y1 + p22 s * y2)) * ν / (2 * a s ^ 2))
          * y1) s := by
  have hN : HasDerivAt (fun t => y1 * (p00 t * y1 + p02 t * y2) + y2 * (p20 t * y1 + p22 t * y2))
      (y1 * (d00 * y1 + d02 * y2) + y2 * (d20 * y1 + d22 * y2)) s :=
    ((((h00.mul_const y1).add (h02.mul_const y2)).const_mul y1).add
      (((h20.mul_const y1).add (h22.mul_const y2)).const_mul y2))
  have h2a : HasDerivAt (fun t => 2 * a t) (2 * ν) s := ha.const_mul 2
  have hD : HasDerivAt
      (fun t => (y1 * (p00 t * y1 + p02 t * y2) + y2 * (p20 t * y1 + p22 t * y2)) / (2 * a t))
      (((y1 * (d00 * y1 + d02 * y2) + y2 * (d20 * y1 + d22 * y2)) * (2 * a s)
          - (y1 * (p00 s * y1 + p02 s * y2) + y2 * (p20 s * y1 + p22 s * y2)) * (2 * ν))
        / (2 * a s) ^ 2) s :=
    hN.div h2a (mul_ne_zero two_ne_zero hpos)
  have hL : HasDerivAt (fun t => p20 t * (-y2) + p22 t * y1 - (p00 t * y1 + p02 t * y2))
      (d20 * (-y2) + d22 * y1 - (d00 * y1 + d02 * y2)) s :=
    ((h20.mul_const (-y2)).add (h22.mul_const y1)).sub ((h00.mul_const y1).add (h02.mul_const y2))
  refine (hL.add (hD.mul_const y1)).congr_deriv ?_
  field_simp

/-! ## 3. The vector-valued derivative of `bkP` along a path of matrices -/

/-- `s ↦ bkP (f s) (a s) y` with `f' = M'` and `a' = ν`:
derivative `bkP M' a y - (ν·(y·My)/(2a²))·Jy` (`My = merApply (f s) y`). -/
lemma bkL4_P (f : ℝ → Mat3) (M' : Mat3) (a : ℝ → ℝ) (ν s : ℝ) (y : ℝ × ℝ)
    (hf : HasDerivAt f M' s) (ha : HasDerivAt a ν s) (hpos : 0 < a s) :
    HasDerivAt (fun t => bkP (f t) (a t) y)
      (bkP M' (a s) y - (ν * bkDot y (merApply (f s) y) / (2 * a s ^ 2)) • Jrot y) s := by
  have h00 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hf 0) 0
  have h02 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hf 0) 2
  have h20 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hf 2) 0
  have h22 := hasDerivAt_pi.mp (hasDerivAt_pi.mp hf 2) 2
  have hne : a s ≠ 0 := hpos.ne'
  have c1 := bkL4_P1 (fun t => f t 0 0) (fun t => f t 0 2) (fun t => f t 2 0)
    (fun t => f t 2 2) a (M' 0 0) (M' 0 2) (M' 2 0) (M' 2 2) ν s y.1 y.2 h00 h02 h20 h22 ha hne
  have c2 := bkL4_P2 (fun t => f t 0 0) (fun t => f t 0 2) (fun t => f t 2 0)
    (fun t => f t 2 2) a (M' 0 0) (M' 0 2) (M' 2 0) (M' 2 2) ν s y.1 y.2 h00 h02 h20 h22 ha hne
  have e : (fun t => bkP (f t) (a t) y) = fun t =>
      (f t 0 0 * (-y.2) + f t 0 2 * y.1 + (f t 2 0 * y.1 + f t 2 2 * y.2)
          + ((y.1 * (f t 0 0 * y.1 + f t 0 2 * y.2) + y.2 * (f t 2 0 * y.1 + f t 2 2 * y.2))
              / (2 * a t)) * (-y.2),
        f t 2 0 * (-y.2) + f t 2 2 * y.1 - (f t 0 0 * y.1 + f t 0 2 * y.2)
          + ((y.1 * (f t 0 0 * y.1 + f t 0 2 * y.2) + y.2 * (f t 2 0 * y.1 + f t 2 2 * y.2))
              / (2 * a t)) * y.1) := by
    funext t
    ext
    · exact bkL4_fst _ _ _
    · exact bkL4_snd _ _ _
  rw [e]
  refine (c1.prodMk c2).congr_deriv ?_
  ext
  · simp only [bkP, merApply, Jrot, bkDot, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [bkP, merApply, Jrot, bkDot, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    ring

/-! ## 4. The Gaussian factor `G(a(s), y)` -/

/-- `s ↦ G(a(s), y)` with `a' = ν`: derivative `G·ν·(-2/a + |y|²/(4a²))`. -/
lemma bkL4_G (y : ℝ × ℝ) (a : ℝ → ℝ) (ν s : ℝ) (ha : HasDerivAt a ν s) (hpos : 0 < a s) :
    HasDerivAt (fun t => bkG (a t) y)
      (bkG (a s) y * (ν * (-2 / a s + sq2 y / (4 * a s ^ 2)))) s := by
  have hne : a s ≠ 0 := hpos.ne'
  have hsq : HasDerivAt (fun t => a t ^ 2) (ν * a s + a s * ν) s := by
    have e : (fun t => a t ^ 2) = fun t => a t * a t := funext fun t => sq (a t)
    rw [e]
    exact ha.mul ha
  have hinv : HasDerivAt (fun t => (a t ^ 2)⁻¹) (-(ν * a s + a s * ν) / (a s ^ 2) ^ 2) s :=
    hsq.inv (pow_ne_zero 2 hne)
  have hden : HasDerivAt (fun t => 4 * a t) (4 * ν) s := ha.const_mul 4
  have hdiv : HasDerivAt (fun t => -(sq2 y) / (4 * a t))
      ((0 * (4 * a s) - -(sq2 y) * (4 * ν)) / (4 * a s) ^ 2) s :=
    (hasDerivAt_const s (-(sq2 y))).div hden (mul_ne_zero four_ne_zero hne)
  have hprod := hinv.mul hdiv.exp
  refine hprod.congr_deriv ?_
  unfold bkG
  field_simp
  ring

/-! ## 5. The leaf (L4) -/

/-- **(L4)** The `s`-derivative of the bracket at fixed `x` (source 4957-4958, 4963, 4973):
`∂_s b_j = G·(bkP M' a y + ν·bkPa M a y)` with `a = 1 + νs`. -/
theorem brkDerivSClosed : BrkDerivSClosed := by
  intro ν χ A s j x M' ha hM
  have hA : HasDerivAt (fun t => ageA ν t) ν s := by
    unfold ageA
    have h := ((hasDerivAt_id s).const_mul ν).const_add 1
    simpa using h
  have hpos : 0 < ageA ν s := ha
  have e : (fun s' => brk ν χ A s' j x)
      = fun s' => bkG (ageA ν s') (xj ν j x) • bkP (Ay ν χ A s') (ageA ν s') (xj ν j x) :=
    funext fun s' => brkClosed ν χ A s' j x
  rw [e]
  have hG := bkL4_G (xj ν j x) (fun t => ageA ν t) ν s hA hpos
  have hP := bkL4_P (Ay ν χ A) M' (fun t => ageA ν t) ν s (xj ν j x) hM hA hpos
  refine (hG.smul hP).congr_deriv ?_
  unfold bkPa
  ext
  · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
