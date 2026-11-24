import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/inst/9/4/1`: joint continuity of one `f_A` lattice term on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 4963-4970, 5063-5079.
Route: the explicit line-derivative formula `gp_fderiv_Vj` expresses
`fderiv ℝ (Vj ν s j) x w` as a sum of two scalar-times-`Jrot` terms whose coefficients are built
from `(ageA ν s ^ 2)⁻¹`, `exp(-|x_j|²/(4 ageA ν s))` and `ageA ν s = 1 + ν s > 0` on `s > 0`,
and whose vector arguments are `w = merApply B (x_j)` and `x_j`.  Each piece is continuous in
`q = (s, (x, B))` on `{0 < q.1}`, so the lattice term `faTerm ν j` is continuous there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem faTermContOn : FAtermContOn := by
  intro ν hν j
  set U : Set (ℝ × (ℝ × ℝ) × Mat3) := {q | 0 < q.1} with hUdef
  -- the age `a = 1 + ν s` is positive on `U`
  have hA : ∀ q ∈ U, 0 < ageA ν q.1 := by
    intro q hq
    have hs : 0 < q.1 := hq
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hAc : Continuous (fun q : ℝ × (ℝ × ℝ) × Mat3 => ageA ν q.1) := by
    unfold ageA; fun_prop
  have hKc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => (ageA ν q.1 ^ 2)⁻¹) U :=
    ContinuousOn.inv₀ (hAc.pow 2).continuousOn (fun q hq => pow_ne_zero 2 (hA q hq).ne')
  have hsq : Continuous (fun q : ℝ × (ℝ × ℝ) × Mat3 => -(sq2 (xj ν j q.2.1))) := by
    unfold sq2 xj; fun_prop
  have hden : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => 4 * ageA ν q.1) U :=
    continuousOn_const.mul hAc.continuousOn
  have hEc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      Real.exp (-(sq2 (xj ν j q.2.1)) / (4 * ageA ν q.1))) U :=
    ContinuousOn.rexp (ContinuousOn.div hsq.continuousOn hden
      (fun q hq => (mul_pos (by norm_num) (hA q hq)).ne'))
  have hxU : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => xj ν j q.2.1) U := by
    have : Continuous (fun q : ℝ × (ℝ × ℝ) × Mat3 => xj ν j q.2.1) := by
      unfold xj cOf; fun_prop
    exact this.continuousOn
  have hmer : Continuous (fun p : Mat3 × (ℝ × ℝ) => merApply p.1 p.2) := by
    unfold merApply; fun_prop
  have hBq : Continuous (fun q : ℝ × (ℝ × ℝ) × Mat3 => q.2.2) := by fun_prop
  have hvc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => merApply q.2.2 (xj ν j q.2.1)) U :=
    hmer.comp_continuousOn (hBq.continuousOn.prodMk hxU)
  have hJ : Continuous Jrot := by
    unfold Jrot; fun_prop
  have hJx : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => Jrot (xj ν j q.2.1)) U :=
    hJ.comp_continuousOn hxU
  have hJv : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      Jrot (merApply q.2.2 (xj ν j q.2.1))) U :=
    hJ.comp_continuousOn hvc
  -- the numerator `-(2 y·v)` of the second coefficient
  have hnum : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      -(2 * (xj ν j q.2.1).1 * (merApply q.2.2 (xj ν j q.2.1)).1
        + 2 * (xj ν j q.2.1).2 * (merApply q.2.2 (xj ν j q.2.1)).2)) U := by
    have a1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => (xj ν j q.2.1).1) U :=
      continuous_fst.comp_continuousOn hxU
    have a2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => (xj ν j q.2.1).2) U :=
      continuous_snd.comp_continuousOn hxU
    have b1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
        (merApply q.2.2 (xj ν j q.2.1)).1) U :=
      continuous_fst.comp_continuousOn hvc
    have b2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
        (merApply q.2.2 (xj ν j q.2.1)).2) U :=
      continuous_snd.comp_continuousOn hvc
    exact (((continuousOn_const.mul a1).mul b1).add ((continuousOn_const.mul a2).mul b2)).neg
  have hcoef2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      (ageA ν q.1 ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j q.2.1)) / (4 * ageA ν q.1)) *
        (-(2 * (xj ν j q.2.1).1 * (merApply q.2.2 (xj ν j q.2.1)).1
          + 2 * (xj ν j q.2.1).2 * (merApply q.2.2 (xj ν j q.2.1)).2) / (4 * ageA ν q.1)))) U :=
    hKc.mul (hEc.mul (hnum.div hden (fun q hq => (mul_pos (by norm_num) (hA q hq)).ne')))
  have hexplicit : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      ((ageA ν q.1 ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j q.2.1)) / (4 * ageA ν q.1))) •
          Jrot (merApply q.2.2 (xj ν j q.2.1)) +
        ((ageA ν q.1 ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j q.2.1)) / (4 * ageA ν q.1)) *
            (-(2 * (xj ν j q.2.1).1 * (merApply q.2.2 (xj ν j q.2.1)).1
              + 2 * (xj ν j q.2.1).2 * (merApply q.2.2 (xj ν j q.2.1)).2) / (4 * ageA ν q.1)))) •
          Jrot (xj ν j q.2.1)) U :=
    ((hKc.mul hEc).smul hJv).add (hcoef2.smul hJx)
  have hD : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      fderiv ℝ (Vj ν q.1 j) q.2.1 (merApply q.2.2 (xj ν j q.2.1))) U :=
    hexplicit.congr (fun q _ => gp_fderiv_Vj ν q.1 j q.2.1 _)
  -- the embedded derivative term
  have hemb : Continuous emb := by
    unfold emb; fun_prop
  have hDc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 =>
      emb (fderiv ℝ (Vj ν q.1 j) q.2.1 (merApply q.2.2 (xj ν j q.2.1)))) U :=
    hemb.comp_continuousOn hD
  -- the vector `Vj` and the matrix-vector term
  have hVc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => Vj ν q.1 j q.2.1) U :=
    (hKc.mul hEc).smul hJx
  have hmvc : Continuous (fun p : Mat3 × Vec3 => mv p.1 p.2) := by
    unfold mv; fun_prop
  have hmvU : ContinuousOn (fun q : ℝ × (ℝ × ℝ) × Mat3 => mv q.2.2 (emb (Vj ν q.1 j q.2.1))) U :=
    hmvc.comp_continuousOn (hBq.continuousOn.prodMk (hemb.comp_continuousOn hVc))
  unfold faTerm
  exact hDc.add hmvU

end UnforcedLeray.Short.PartIIIb.Concrete
