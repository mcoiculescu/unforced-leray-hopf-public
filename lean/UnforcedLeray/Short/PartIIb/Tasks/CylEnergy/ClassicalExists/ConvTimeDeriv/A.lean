import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatTimeDeriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatLapTransfer

/-!


`∂_a H_a g = Σ_i (∂_iK_a) * ∂_i g` for `g ∈ C¹`, `a > 0`. Source:
`the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
Route: `HeatTimeDeriv` gives `∂_a H_a g (x) = ∫ ΔK_a(x-y) g(y) dy`; one integration by parts per
coordinate (`HLT.ibp_conv`, the `C¹` half of `HLT.step_gen`) moves one derivative onto `g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CTDA

lemma heatKd_eq_pd {a : ℝ} (ha : 0 < a) (i : Fin 2) (z : Pl) :
    heatKd i a z = B0579.pd i (heatK a) z := by
  fin_cases i
  · show heatKd 0 a z = B0579.pd 0 (heatK a) z
    rw [HTD.pd0_heatK ha]; simp [heatKd]
  · show heatKd 1 a z = B0579.pd 1 (heatK a) z
    rw [HTD.pd1_heatK ha]; simp [heatKd]

lemma coordStep (j : Fin 2) {B : ℝ} {g : Pl → ℝ} (hg : ContDiff ℝ 1 g) (hW : WB B g)
    (hW1 : WB B (B0579.pd j g)) {a : ℝ} (x : Pl)
    (hKd : Differentiable ℝ (B0579.pd j (heatK a)))
    (hKi1 : Integrable (fun z : Pl => B0579.pd j (heatK a) z))
    (hKi2 : Integrable (fun z : Pl => B0579.pd j (B0579.pd j (heatK a)) z)) :
    ∫ z : Pl, B0579.pd j (heatK a) z * B0579.pd j g (x - z)
      = ∫ z : Pl, B0579.pd j (B0579.pd j (heatK a)) z * g (x - z) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous g := hg.continuous
  have hpgc : Continuous (B0579.pd j g) := by
    unfold B0579.pd
    exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cg : Continuous (fun z : Pl => g (x - z)) := hgc.comp (continuous_const.sub continuous_id)
  have cpg : Continuous (fun z : Pl => B0579.pd j g (x - z)) :=
    hpgc.comp (continuous_const.sub continuous_id)
  have hbg : ∀ z : Pl, |g (x - z)| ≤ B := fun z => abs_le_of_WB_aux hW (x - z)
  have hbpg : ∀ z : Pl, |B0579.pd j g (x - z)| ≤ B := fun z => abs_le_of_WB_aux hW1 (x - z)
  exact HLT.ibp_conv hKd hgd x (B0579.dir j)
    (HLT.int_mul_bdd hKi2 cg hbg) (HLT.int_mul_bdd hKi1 cpg hbpg) (HLT.int_mul_bdd hKi1 cg hbg)

end CTDA

open CTDA in
/-- **`PartII-b:T22/1/11/1`** `∂_a H_a g = Σ_i (∂_iK_a) * ∂_i g` for `g ∈ C¹`. -/
theorem convTD_A : UnforcedLeray.Short.IIb.CylPDE.ConvTD_A := by
  intro B g hg hW hW1 a ha x
  have hbase := heatTimeDeriv B g hg.continuous hW a ha x
  have hgc : Continuous g := hg.continuous
  have cg : Continuous (fun z : Pl => g (x - z)) := hgc.comp (continuous_const.sub continuous_id)
  have hbg : ∀ z : Pl, |g (x - z)| ≤ B := fun z => abs_le_of_WB_aux hW (x - z)
  have j0 : Integrable (fun z : Pl => B0579.pd 0 (B0579.pd 0 (heatK a)) z * g (x - z)) :=
    HLT.int_mul_bdd (HLT.facts0 ha).2.2 cg hbg
  have j1 : Integrable (fun z : Pl => B0579.pd 1 (B0579.pd 1 (heatK a)) z * g (x - z)) :=
    HLT.int_mul_bdd (HLT.facts1 ha).2.2 cg hbg
  have s0 := coordStep 0 hg hW (hW1 0) x (HLT.facts0 ha).1 (HLT.facts0 ha).2.1
    (HLT.facts0 ha).2.2
  have s1 := coordStep 1 hg hW (hW1 1) x (HLT.facts1 ha).1 (HLT.facts1 ha).2.1
    (HLT.facts1 ha).2.2
  have hsd : ∀ i : Fin 2, heatSGd i a (B0579.pd i g) x =
      ∫ z : Pl, B0579.pd i (heatK a) z * B0579.pd i g (x - z) := by
    intro i
    unfold heatSGd
    have h2 := integral_sub_left_eq_self
      (fun w : Pl => heatKd i a (x - w) * B0579.pd i g w) volume x
    simp only [sub_sub_cancel] at h2
    rw [← h2]
    congr 1
    funext z
    rw [heatKd_eq_pd ha]
  have hsum : (∑ i : Fin 2, heatSGd i a (B0579.pd i g) x)
      = ∫ y : Pl, lapP (heatK a) (x - y) * g y := by
    rw [Fin.sum_univ_two, hsd 0, hsd 1, s0, s1, ← integral_add j0 j1]
    have h2 := integral_sub_left_eq_self (fun w : Pl => lapP (heatK a) (x - w) * g w) volume x
    simp only [sub_sub_cancel] at h2
    rw [← h2]
    congr 1
    funext z
    beta_reduce
    unfold lapP
    ring
  rw [hsum]
  exact hbase

end UnforcedLeray.Short.IIb.CylPDE
