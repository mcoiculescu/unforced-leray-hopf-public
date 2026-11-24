import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5

/-!
# `PartIII-b:C/asrc/ra/5/5` : lattice-sum form of `hpA` (source 4963-4973)

`V_j(s,x) = V_0(s, x_j)` and `DV_j(s)(x) = DV_0(s)(x_j)` since `x_j = x + (-(jc), 0)` is a
translation, so `hpA = ∑_j G(s, x_j)` with `G = GhpA`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma hpASum_xj_zero (ν : ℝ) (z : ℝ × ℝ) : xj ν 0 z = z := by
  simp [xj]

lemma hpASum_xj_add (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    xj ν j x = x + (-(j * cOf ν), 0) := by
  ext <;> simp [xj, sub_eq_add_neg]

lemma hpASum_Vj_shift (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    Vj ν s j x = Vj ν s 0 (xj ν j x) := by
  unfold Vj
  rw [hpASum_xj_zero]

lemma hpASum_Vj_comp (ν s : ℝ) (j : ℤ) :
    Vj ν s j = fun x => Vj ν s 0 (x + (-(j * cOf ν), 0)) := by
  funext x
  rw [hpASum_Vj_shift, hpASum_xj_add]

lemma hpASum_fderiv (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) x = fderiv ℝ (Vj ν s 0) (xj ν j x) := by
  rw [hpASum_Vj_comp, fderiv_comp_add_right, hpASum_xj_add]

theorem hpASum_proof : HpASum := by
  intro ν χ A
  funext p
  unfold hpA
  refine tsum_congr fun j => ?_
  rw [hpASum_Vj_shift, hpASum_fderiv]
  unfold GhpA
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
