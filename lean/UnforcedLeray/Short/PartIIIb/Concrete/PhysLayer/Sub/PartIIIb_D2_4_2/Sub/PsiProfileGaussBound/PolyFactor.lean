import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.GaussFactor.ChartBounds

/-!
# Leaf P of `PsiProfileGaussBound` (task `PartIII-b:IIIb-D2/4/2/1/3/2`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
`psiPoly = (-2 a⁻¹)(tr M - c₁(y, M y)/(4a)...)` with `M = χ(νs)A(s)` is a quadratic polynomial in
`y` whose coefficients are `C²` functions of `s` on `(0,∞)` (`A` is `C⁶`, `χ` is `C^∞`).  It is
assembled in the polynomial-growth class `PB` of `ChartBounds.lean` from the coordinates `y₁, y₂`
and the `s`-functions `a⁻¹, (4a)⁻¹, χ(νs)A_{ij}(s)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiPolyFactor_proof (as : ℝ) (χf : ℝ → ℝ) : PsiPolyFactor as χf := by
  intro hχ ν hν A hA s0 hs0
  have hainv : ContDiffOn ℝ 2 (fun s : ℝ => (ageA ν s)⁻¹) (Ioi 0) := by
    have h1 : ContDiffOn ℝ 2 (fun s : ℝ => ageA ν s) (Ioi 0) := by
      unfold ageA
      exact (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
    refine h1.inv (fun s hs => ?_)
    have h : (0 : ℝ) < s := hs
    unfold ageA
    positivity
  have hbinv : ContDiffOn ℝ 2 (fun s : ℝ => (4 * ageA ν s)⁻¹) (Ioi 0) := by
    have h4 : ContDiffOn ℝ 2 (fun s : ℝ => 4 * ageA ν s) (Ioi 0) := by
      unfold ageA
      exact (contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffOn
    refine h4.inv (fun s hs => ?_)
    have h : (0 : ℝ) < s := hs
    unfold ageA
    positivity
  have hχs : ContDiff ℝ 2 (fun s : ℝ => χf (ν * s)) :=
    (hχ.smooth.comp (contDiff_const.mul contDiff_id)).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hA2 : ∀ i j : Fin 3, ContDiffOn ℝ 2 (fun s : ℝ => A s i j) (Ioi (0 : ℝ)) :=
    fun i j => ((contDiffOn_pi.1 (contDiffOn_pi.1 hA.smooth i)) j).of_le
      (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 6))
  have hE : ∀ i j : Fin 3, PB s0 (fun p : Chart => χf (ν * p.1) * A p.1 i j) :=
    fun i j => PB.sfun hs0 (φ := fun s => χf (ν * s) * A s i j)
      (hχs.contDiffOn.mul (hA2 i j))
  have E00 := hE 0 0
  have E02 := hE 0 2
  have E20 := hE 2 0
  have E22 := hE 2 2
  have Ai := PB.sfun hs0 hainv
  have Bi := PB.sfun hs0 hbinv
  have t1 := (PB.const (s0 := s0) (-2)).mul hs0 Ai
  have t2 := E00.add hs0 E22
  have l1 := (PB.const (s0 := s0) 2).mul hs0 (PB.y1 (s0 := s0))
  have l2 := (PB.const (s0 := s0) 2).mul hs0 (PB.y2 (s0 := s0))
  have m1 := (E00.mul hs0 (PB.y1 (s0 := s0))).add hs0 (E02.mul hs0 (PB.y2 (s0 := s0)))
  have m2 := (E20.mul hs0 (PB.y1 (s0 := s0))).add hs0 (E22.mul hs0 (PB.y2 (s0 := s0)))
  have q1 := (l1.mul hs0 m1).add hs0 (l2.mul hs0 m2)
  have t3 := (q1.neg hs0).mul hs0 Bi
  have all := t1.mul hs0 (t2.sub hs0 t3)
  have hP : PB s0 (psiPoly ν χf A) := by
    refine all.congr (fun p => ?_)
    simp only [psiPoly, Ay, merTrace, merApply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  exact hP

end UnforcedLeray.Short.PartIIIb.Concrete
