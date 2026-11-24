import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpExp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpBilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54OfS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Snd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpVj.Ps54Clm

/-!
# `PartIII-b:C/asrc/ra/5/4/11` : the `j = 0` term `V_0` is in `GP54 4`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`V_0(s, x) = (a⁻² exp(-|x|²/(4a))) • J x`: the Gaussian `exp(-|x|²/(4a))` times `a⁻²`
(class `GP54 4` via `gp54_bilin`), then scaled by the vector `J x` (class `PS54` via `ps54_clm`
applied to the projection `p ↦ p.2`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_Vj (ν : ℝ) (hν : 0 < ν) (n : ℕ) : GP54 4 ν n (fun p : ℝ × (ℝ × ℝ) => Vj ν p.1 0 p.2) := by
  have hf : GP54 4 ν n (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) :=
    gp54_exp 4 ν (by norm_num) hν n
  have hpos : ∀ s : ℝ, 0 < s → 0 < ageA ν s := fun s hs => by
    unfold ageA; nlinarith [mul_pos hν hs]
  have h1 : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun s : ℝ => ageA ν s ^ 2) (Ioi (0 : ℝ)) := by
    unfold ageA; fun_prop
  have h2 := h1.inv (fun s hs => pow_ne_zero 2 (hpos s (Set.mem_Ioi.mp hs)).ne')
  have hg1 : PS54 n (fun p : ℝ × (ℝ × ℝ) => (ageA ν p.1 ^ 2)⁻¹) :=
    ps54_of_s n (fun s : ℝ => (ageA ν s ^ 2)⁻¹) h2
  have hA : GP54 4 ν n (fun p : ℝ × (ℝ × ℝ) => (ContinuousLinearMap.mul ℝ ℝ)
      (Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) ((ageA ν p.1 ^ 2)⁻¹)) :=
    gp54_bilin (ContinuousLinearMap.mul ℝ ℝ) 4 ν n _ _ hf hg1
  have hJ : PS54 n (fun p : ℝ × (ℝ × ℝ) => Jrot p.2) := by
    have e : (fun p : ℝ × (ℝ × ℝ) => Jrot p.2) =
        fun p : ℝ × (ℝ × ℝ) => ((-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
          (ContinuousLinearMap.fst ℝ ℝ ℝ)) p.2 := by
      funext p
      simp [Jrot]
    rw [e]
    exact ps54_clm ((-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))
      n (fun p : ℝ × (ℝ × ℝ) => p.2) (ps54_snd n)
  have hB : GP54 4 ν n (fun p : ℝ × (ℝ × ℝ) => (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) ((ContinuousLinearMap.mul ℝ ℝ)
      (Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) ((ageA ν p.1 ^ 2)⁻¹)) (Jrot p.2)) :=
    gp54_bilin (ContinuousLinearMap.lsmul ℝ ℝ) 4 ν n _ _ hA hJ
  have e2 : (fun p : ℝ × (ℝ × ℝ) => Vj ν p.1 0 p.2) =
      fun p : ℝ × (ℝ × ℝ) => (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) ((ContinuousLinearMap.mul ℝ ℝ)
        (Real.exp (-(sq2 p.2) / (4 * ageA ν p.1))) ((ageA ν p.1 ^ 2)⁻¹)) (Jrot p.2) := by
    funext p
    simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', Vj, xj_zero]
    congr 1
    ring
  rw [e2]
  exact hB

end UnforcedLeray.Short.PartIIIb.Concrete
