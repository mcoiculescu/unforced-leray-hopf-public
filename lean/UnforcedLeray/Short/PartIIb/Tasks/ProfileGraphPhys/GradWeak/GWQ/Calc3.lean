import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Calc2

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: the divergence of the radial tests
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem sum_dy_tst {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) {x : ℝ × Space} (hy : x.2 ∉ Axi.axis) :
    ∑ j : Fin 3, dy j (tst c ε a φ i j) x =
      (ctLift c ε a φ x * (Axi.ϱ x.2)⁻¹ +
        ((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) *
            fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 0 1) +
          (x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) *
            fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 1 1))) •
        realCL (Evec i x.2) := by
  obtain ⟨D, hD, hD0⟩ := exists_EvD i hy
  rw [Finset.sum_congr rfl (fun j _ => dy_tst hc hε hφ i j D hy hD), Finset.sum_add_distrib]
  have h1 : ∑ j : Fin 3, (Axi.eR x.2 j * ctLift c ε a φ x) • realCL (D (EuclideanSpace.single j 1))
      = 0 := by
    have : ∑ j : Fin 3, (Axi.eR x.2 j * ctLift c ε a φ x) • realCL (D (EuclideanSpace.single j 1))
        = realCL (D (ctLift c ε a φ x • ∑ j : Fin 3, Axi.eR x.2 j • (EuclideanSpace.single j (1:ℝ) : Space))) := by
      simp only [Finset.smul_sum, map_sum, map_smul, smul_smul, mul_comm]
    rw [this, eR_sum, map_smul, hD0]
    simp
  rw [h1, zero_add, ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, eRD_div hy]
  simp only [Fin.sum_univ_three, Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two, zero_mul,
    add_zero]
  show _ = _
  have : Axi.ϱ x.2 = Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) := rfl
  rw [this]
  ring

end UnforcedLeray.Short.IIb.GWQ
