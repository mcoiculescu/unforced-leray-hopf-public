import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpExp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpBilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54OfS

/-!
# `PartIII-b:C/asrc/ra/5/4/13` : the `j = 0` term `ψ_0` is in `GP54 4`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`ψ_0(s, x) = -2 a⁻¹ exp(-|x|²/(4a))` is the product of the Gaussian `exp(-|x|²/(4a))`
(class `GP54 4`) with the function `-2 a⁻¹` of `s` alone (class `PS54`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_psij (ν : ℝ) (hν : 0 < ν) (n : ℕ) : GP54 4 ν n (fun p : ℝ × (ℝ × ℝ) => psij ν p.1 0 p.2) := by
  have hf : GP54 4 ν n (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) :=
    gp54_exp 4 ν (by norm_num) hν n
  have hpos : ∀ s : ℝ, 0 < s → 0 < ageA ν s := fun s hs => by
    unfold ageA; nlinarith [mul_pos hν hs]
  have h1 : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun s : ℝ => ageA ν s) (Ioi (0 : ℝ)) := by
    unfold ageA; fun_prop
  have h2 := h1.inv (fun s hs => (hpos s (Set.mem_Ioi.mp hs)).ne')
  have hh : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun s : ℝ => -2 * (ageA ν s)⁻¹) (Ioi (0 : ℝ)) :=
    contDiffOn_const.mul h2
  have hg : PS54 n (fun p : ℝ × (ℝ × ℝ) => -2 * (ageA ν p.1)⁻¹) :=
    ps54_of_s n (fun s : ℝ => -2 * (ageA ν s)⁻¹) hh
  have key := gp54_bilin (ContinuousLinearMap.mul ℝ ℝ) 4 ν n _ _ hf hg
  have e : (fun p : ℝ × (ℝ × ℝ) => psij ν p.1 0 p.2) =
      fun p : ℝ × (ℝ × ℝ) => (ContinuousLinearMap.mul ℝ ℝ)
        (Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) (-2 * (ageA ν p.1)⁻¹) := by
    funext p
    simp only [ContinuousLinearMap.mul_apply', psij, xj_zero]
    ring
  rw [e]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
