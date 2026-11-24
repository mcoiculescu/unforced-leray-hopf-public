import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/flatset/col/2`, leaf 2: joint continuity of one lattice term on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 4976, 4594-4596.
Route: the explicit line-derivative formula `gp_fderiv_Vj` expresses
`fderiv ℝ (Vj ν s j) x w` as a sum of two scalar-times-`Jrot` terms whose scalar coefficients are
built from `(ageA ν s ^ 2)⁻¹`, `exp(-|x_j|²/(4 ageA))`, `ageA = 1 + ν s > 0` on `s > 0`, and whose
vector arguments are `w = merApply (B s) (x_j)`, `x_j`.  Each piece is continuous in `(s, x)` on
`Ioi 0 ×ˢ univ` (`B` continuous there), so the `j`-th term is continuous there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatTermCont : FlatTermCont := by
  intro ν hν j B hB
  set U : Set Chart := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) with hUdef
  -- the age `a = 1 + ν s` is positive on `U`
  have hA : ∀ p : Chart, p ∈ U → 0 < ageA ν p.1 := by
    intro p hp
    have hs : 0 < p.1 := hp.1
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hAc : Continuous (fun p : Chart => ageA ν p.1) := by
    unfold ageA; fun_prop
  have hKc : ContinuousOn (fun p : Chart => (ageA ν p.1 ^ 2)⁻¹) U :=
    ContinuousOn.inv₀ (hAc.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hA p hp).ne')
  have hsq : Continuous (fun p : Chart => -(sq2 (xj ν j p.2))) := by
    unfold sq2 xj; fun_prop
  have hden : ContinuousOn (fun p : Chart => 4 * ageA ν p.1) U :=
    continuousOn_const.mul hAc.continuousOn
  have hEc : ContinuousOn (fun p : Chart => Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))) U :=
    ContinuousOn.rexp (ContinuousOn.div hsq.continuousOn hden
      (fun p hp => (mul_pos (by norm_num) (hA p hp)).ne'))
  have hBU : ContinuousOn (fun p : Chart => B p.1) U :=
    hB.comp continuousOn_fst (fun p hp => hp.1)
  have hxU : ContinuousOn (fun p : Chart => xj ν j p.2) U := by
    have : Continuous (fun p : Chart => xj ν j p.2) := by
      unfold xj cOf; fun_prop
    exact this.continuousOn
  have hmer : Continuous (fun q : Mat3 × (ℝ × ℝ) => merApply q.1 q.2) := by
    unfold merApply; fun_prop
  have hvc : ContinuousOn (fun p : Chart => merApply (B p.1) (xj ν j p.2)) U :=
    hmer.comp_continuousOn (hBU.prodMk hxU)
  have hJ : Continuous Jrot := by
    unfold Jrot; fun_prop
  have hJx : ContinuousOn (fun p : Chart => Jrot (xj ν j p.2)) U :=
    hJ.comp_continuousOn hxU
  have hJv : ContinuousOn (fun p : Chart => Jrot (merApply (B p.1) (xj ν j p.2))) U :=
    hJ.comp_continuousOn hvc
  -- the numerator `-(2 y·v)` of the second coefficient
  have hnum : ContinuousOn (fun p : Chart =>
      -(2 * (xj ν j p.2).1 * (merApply (B p.1) (xj ν j p.2)).1
        + 2 * (xj ν j p.2).2 * (merApply (B p.1) (xj ν j p.2)).2)) U := by
    have a1 : ContinuousOn (fun p : Chart => (xj ν j p.2).1) U :=
      continuous_fst.comp_continuousOn hxU
    have a2 : ContinuousOn (fun p : Chart => (xj ν j p.2).2) U :=
      continuous_snd.comp_continuousOn hxU
    have b1 : ContinuousOn (fun p : Chart => (merApply (B p.1) (xj ν j p.2)).1) U :=
      continuous_fst.comp_continuousOn hvc
    have b2 : ContinuousOn (fun p : Chart => (merApply (B p.1) (xj ν j p.2)).2) U :=
      continuous_snd.comp_continuousOn hvc
    exact (((continuousOn_const.mul a1).mul b1).add ((continuousOn_const.mul a2).mul b2)).neg
  have hcoef2 : ContinuousOn (fun p : Chart =>
      (ageA ν p.1 ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) *
        (-(2 * (xj ν j p.2).1 * (merApply (B p.1) (xj ν j p.2)).1
          + 2 * (xj ν j p.2).2 * (merApply (B p.1) (xj ν j p.2)).2) / (4 * ageA ν p.1)))) U :=
    hKc.mul (hEc.mul (hnum.div hden (fun p hp => (mul_pos (by norm_num) (hA p hp)).ne')))
  have hexplicit : ContinuousOn (fun p : Chart =>
      ((ageA ν p.1 ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))) •
          Jrot (merApply (B p.1) (xj ν j p.2)) +
        ((ageA ν p.1 ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) *
            (-(2 * (xj ν j p.2).1 * (merApply (B p.1) (xj ν j p.2)).1
              + 2 * (xj ν j p.2).2 * (merApply (B p.1) (xj ν j p.2)).2) / (4 * ageA ν p.1)))) •
          Jrot (xj ν j p.2)) U :=
    ((hKc.mul hEc).smul hJv).add (hcoef2.smul hJx)
  have hD : ContinuousOn (fun p : Chart =>
      fderiv ℝ (Vj ν p.1 j) p.2 (merApply (B p.1) (xj ν j p.2))) U :=
    hexplicit.congr (fun p _ => gp_fderiv_Vj ν p.1 j p.2 _)
  -- the embedded derivative term
  have hemb : Continuous emb := by
    unfold emb; fun_prop
  have hDc : ContinuousOn (fun p : Chart =>
      emb (fderiv ℝ (Vj ν p.1 j) p.2 (merApply (B p.1) (xj ν j p.2)))) U :=
    hemb.comp_continuousOn hD
  -- the vector `Vj` and the matrix-vector term
  have hVc : ContinuousOn (fun p : Chart => Vj ν p.1 j p.2) U :=
    ((hKc.mul hEc).smul hJx)
  have hmvc : Continuous (fun q : Mat3 × Vec3 => mv q.1 q.2) := by
    unfold mv; fun_prop
  have hmvU : ContinuousOn (fun p : Chart => mv (B p.1) (emb (Vj ν p.1 j p.2))) U :=
    hmvc.comp_continuousOn (hBU.prodMk (hemb.comp_continuousOn hVc))
  exact hDc.add hmvU

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
