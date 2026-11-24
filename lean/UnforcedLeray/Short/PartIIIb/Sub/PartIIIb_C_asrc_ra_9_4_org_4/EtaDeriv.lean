import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/1` : the `η`-derivative of one lattice term

Source `the November 2 reference manuscript`
lines 4966-4968 and 5024.  Calculus of `psiT` in the `η`-variable.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiTEtaDeriv : PsiTEtaDeriv := by
  intro ν s ha M q η
  have hA : ageA ν s ≠ 0 := ha.ne'
  have h0 : HasDerivAt (fun x : ℝ => x) 1 η := hasDerivAt_id' η
  have hsq : HasDerivAt (fun η' : ℝ => q ^ 2 + η' ^ 2) (2 * η) η :=
    ((h0.pow 2).const_add (q ^ 2)).congr_deriv (by norm_num)
  have hE : HasDerivAt (fun η' : ℝ => -(q ^ 2 + η' ^ 2) / (2 * ageA ν s))
      (-(2 * η) / (2 * ageA ν s)) η :=
    hsq.neg.div_const (2 * ageA ν s)
  have hP : HasDerivAt
      (fun η' : ℝ => q * (M 0 0 * q + M 0 2 * η') + η' * (M 2 0 * q + M 2 2 * η'))
      (q * M 0 2 + (M 2 0 * q + M 2 2 * η) + η * M 2 2) η := by
    have h1 : HasDerivAt (fun η' : ℝ => M 0 0 * q + M 0 2 * η') (M 0 2) η :=
      ((h0.const_mul (M 0 2)).const_add (M 0 0 * q)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun η' : ℝ => M 2 0 * q + M 2 2 * η') (M 2 2) η :=
      ((h0.const_mul (M 2 2)).const_add (M 2 0 * q)).congr_deriv (by ring)
    exact ((h1.const_mul q).add (h0.mul h2)).congr_deriv (by ring)
  have hD : HasDerivAt
      (fun η' : ℝ => (ageA ν s ^ 4)⁻¹ *
        (q * (M 0 0 * q + M 0 2 * η') + η' * (M 2 0 * q + M 2 2 * η')))
      ((ageA ν s ^ 4)⁻¹ * (q * M 0 2 + (M 2 0 * q + M 2 2 * η) + η * M 2 2)) η :=
    hP.const_mul _
  have hall := hE.exp.mul hD
  have hfun : (fun η' : ℝ => psiT ν s M (q, η')) = fun η' : ℝ =>
      Real.exp (-(q ^ 2 + η' ^ 2) / (2 * ageA ν s)) *
        ((ageA ν s ^ 4)⁻¹ * (q * (M 0 0 * q + M 0 2 * η') + η' * (M 2 0 * q + M 2 2 * η'))) := by
    funext η'
    simp only [psiT, qM, merApply, sq2]
  rw [hfun]
  refine hall.congr_deriv ?_
  simp only [psiTEta, qM, merApply, sq2]
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
