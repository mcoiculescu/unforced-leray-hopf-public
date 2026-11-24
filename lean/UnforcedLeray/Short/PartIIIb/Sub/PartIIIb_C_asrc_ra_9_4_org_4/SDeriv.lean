import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/2` : the `s`-derivative of one lattice term along a path

Source `the November 2 reference manuscript`
lines 4966-4968 and 5024.  Calculus of `psiT(s, M(s), y)` in `s`, with `M'(s) = D`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiTSDeriv : PsiTSDeriv := by
  intro ν Mf D s ha hM y
  have ha' : ageA ν s ≠ 0 := ha.ne'
  have h0 : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id' s
  have hA : HasDerivAt (fun t : ℝ => ageA ν t) ν s := by
    unfold ageA
    exact ((h0.const_mul ν).const_add 1).congr_deriv (by ring)
  have hE : ∀ i j : Fin 3, HasDerivAt (fun t => Mf t i j) (D i j) s :=
    fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 hM i) j
  have hQ : HasDerivAt (fun t => qM (Mf t) y) (qM D y) s := by
    have e1 : HasDerivAt (fun t => Mf t 0 0 * y.1 + Mf t 0 2 * y.2)
        (D 0 0 * y.1 + D 0 2 * y.2) s :=
      ((hE 0 0).mul_const y.1).add ((hE 0 2).mul_const y.2)
    have e2 : HasDerivAt (fun t => Mf t 2 0 * y.1 + Mf t 2 2 * y.2)
        (D 2 0 * y.1 + D 2 2 * y.2) s :=
      ((hE 2 0).mul_const y.1).add ((hE 2 2).mul_const y.2)
    have e3 := (e1.const_mul y.1).add (e2.const_mul y.2)
    simp only [qM, merApply]
    exact e3.congr_deriv (by ring)
  have hpow : HasDerivAt (fun t : ℝ => ageA ν t ^ 4) (4 * ageA ν s ^ 3 * ν) s :=
    (hA.pow 4).congr_deriv (by norm_num)
  have hinv : HasDerivAt (fun t : ℝ => (ageA ν t ^ 4)⁻¹)
      (-(4 * ageA ν s ^ 3 * ν) / (ageA ν s ^ 4) ^ 2) s :=
    hpow.inv (pow_ne_zero 4 ha')
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(sq2 y) / (2 * ageA ν t)))
      (Real.exp (-(sq2 y) / (2 * ageA ν s)) *
        ((0 * (2 * ageA ν s) - -(sq2 y) * (2 * ν)) / (2 * ageA ν s) ^ 2)) s := by
    have hd : HasDerivAt (fun t : ℝ => 2 * ageA ν t) (2 * ν) s := hA.const_mul 2
    exact (((hasDerivAt_const s (-(sq2 y))).div hd (mul_ne_zero two_ne_zero ha')).exp)
  show HasDerivAt (fun t : ℝ => Real.exp (-(sq2 y) / (2 * ageA ν t)) *
      ((ageA ν t ^ 4)⁻¹ * qM (Mf t) y)) (psiTS ν s (Mf s) D y) s
  refine (hexp.mul (hinv.mul hQ)).congr_deriv ?_
  unfold psiTS
  simp only [Pi.mul_apply]
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
