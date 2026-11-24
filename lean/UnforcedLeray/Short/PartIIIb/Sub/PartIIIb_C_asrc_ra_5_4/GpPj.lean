import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpExp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpBilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54OfS

/-!
# `PartIII-b:C/asrc/ra/5/4/12` : the `j = 0` term `p_0` is in `GP54 2`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`p_0(s, x) = -a⁻³ exp(-|x|²/(2a))` is the product of the Gaussian `exp(-|x|²/(2a))`
(class `GP54 2`) with the function `-a⁻³` of `s` alone (class `PS54`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_pj (ν : ℝ) (hν : 0 < ν) (n : ℕ) : GP54 2 ν n (fun p : ℝ × (ℝ × ℝ) => pj ν p.1 0 p.2) := by
  have hf : GP54 2 ν n (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (2 * ageA ν p.1))) :=
    gp54_exp 2 ν (by norm_num) hν n
  have hpos : ∀ s : ℝ, 0 < s → 0 < ageA ν s := fun s hs => by
    unfold ageA; nlinarith [mul_pos hν hs]
  have h1 : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun s : ℝ => ageA ν s ^ 3) (Ioi (0 : ℝ)) := by
    unfold ageA; fun_prop
  have h2 := h1.inv (fun s hs => pow_ne_zero 3 (hpos s (Set.mem_Ioi.mp hs)).ne')
  have hh : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun s : ℝ => -(ageA ν s ^ 3)⁻¹) (Ioi (0 : ℝ)) :=
    h2.neg
  have hg : PS54 n (fun p : ℝ × (ℝ × ℝ) => -(ageA ν p.1 ^ 3)⁻¹) :=
    ps54_of_s n (fun s : ℝ => -(ageA ν s ^ 3)⁻¹) hh
  have key := gp54_bilin (ContinuousLinearMap.mul ℝ ℝ) 2 ν n _ _ hf hg
  have e : (fun p : ℝ × (ℝ × ℝ) => pj ν p.1 0 p.2) =
      fun p : ℝ × (ℝ × ℝ) => (ContinuousLinearMap.mul ℝ ℝ)
        (Real.exp (-(sq2 p.2) / (2 * ageA ν p.1))) (-(ageA ν p.1 ^ 3)⁻¹) := by
    funext p
    simp only [ContinuousLinearMap.mul_apply', pj, xj_zero]
    ring
  rw [e]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
