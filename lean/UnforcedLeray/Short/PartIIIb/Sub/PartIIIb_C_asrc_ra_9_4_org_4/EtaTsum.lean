import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/6` leaf: `η`-differentiation of the lattice sum of `Ψ_A`

Source `the November 2 reference manuscript`
line 4978: the sum and its `η`-derivative converge by Gaussian decay, the majorant
`K₄ |M| 5200 e^{-(q-jc)²/18}` being uniform in `η`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiAEtaTsum : PsiAEtaTsum := by
  intro hD hV hE ν s hν hs hνs M x
  obtain ⟨K3, hK3, B3⟩ := hV
  obtain ⟨K4, hK4, B4⟩ := hE
  have hνs' : ν * s ≤ 5 / 2 := by linarith
  have ha : 0 < ageA ν s := lt_of_lt_of_le one_pos (pdc_ageA_ge_one hν.le hs.le)
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hsum : Summable (fun j : ℤ =>
      K4 * frob M * (5200 * Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2))) :=
    ((gp_gauss_summable x.1 (1 / 18) (cOf ν) (by norm_num) hc).mul_left 5200).mul_left
      (K4 * frob M)
  have hg0 : Summable (fun j : ℤ => psiT ν s M (xj ν j (x.1, x.2))) :=
    Summable.of_norm_bounded ((pdc_genv_summable hν x).mul_left (K3 * frob M)) (fun j => by
      rw [Real.norm_eq_abs]
      exact B3 ν s hν hs.le hνs' M (xj ν j x))
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun (j : ℤ) (η : ℝ) => psiT ν s M (xj ν j (x.1, η)))
    (g' := fun (j : ℤ) (η : ℝ) => psiTEta ν s M (xj ν j (x.1, η)))
    (u := fun j : ℤ => K4 * frob M * (5200 * Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2)))
    (t := univ) hsum isOpen_univ isPreconnected_univ
    (fun j η _ => hD ν s ha M (x.1 - (j : ℝ) * cOf ν) η)
    (fun j η _ => by
      rw [Real.norm_eq_abs]
      have h1 := (B4 ν s hν hs.le hνs' M (xj ν j (x.1, η))).1
      have h2 := pdc_genvT_le ν j (x.1, η)
      have h3 : 0 ≤ K4 * frob M := mul_nonneg hK4 (pdc_frob_nonneg M)
      calc |psiTEta ν s M (xj ν j (x.1, η))|
          ≤ K4 * frob M * genvT (xj ν j (x.1, η)) := h1
        _ ≤ K4 * frob M * (5200 * Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 h3)
    (mem_univ x.2) hg0 (mem_univ x.2)
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
