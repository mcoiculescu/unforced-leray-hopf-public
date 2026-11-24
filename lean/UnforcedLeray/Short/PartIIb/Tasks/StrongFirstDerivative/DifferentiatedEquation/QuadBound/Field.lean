import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP

/-!
# The differentiated quadratic field: pointwise and `L^{q₀}` bounds (helper for `PartII-b:S1/1/2`)

Source `the November 2 reference manuscript`, lines
2528-2534: with `u = e + w`, the field `F_i = -∑_k ∂_j∂_k(u_k u_i)` (`GEQuadField`) satisfies
`|F| ≤ ∑_k (2|D²u||u| + |D_ku|² + |D_ju|²)`, and `|D_ku|² ≤ 2|D_ke|² + 2|D_kw|²`; together with
`‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}` every term is in `Y_p`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.QuadBoundSub

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params rep)
open UnforcedLeray.Short.PartIIIb.Concrete (GEQDu GEQDdu GEQuadField)

/-- `GEQuadField` as a vector sum. -/
theorem quadField_eq (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3)
    (x : ℝ × UnforcedLeray.Space) :
    GEQuadField p z g h j x = -∑ k : Fin 3,
      ((GEQDdu p z g h k j x k) • p.uOf z x + (GEQDu p z g k x k) • GEQDu p z g j x +
        (GEQDu p z g j x k) • GEQDu p z g k x + (p.uOf z x k) • GEQDdu p z g h k j x) := by
  ext i
  simp [GEQuadField, Finset.sum_apply, smul_eq_mul]

theorem norm_coord_le' (v : UnforcedLeray.PhaseSpace.CVec3) (k : Fin 3) : ‖v k‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v k

/-- Pointwise bound of the differentiated quadratic field. -/
theorem norm_quadField_le (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3)
    (x : ℝ × UnforcedLeray.Space) :
    ‖GEQuadField p z g h j x‖ ≤ ∑ k : Fin 3,
      (2 * (‖GEQDdu p z g h k j x‖ * ‖p.uOf z x‖) + ‖GEQDu p z g k x‖ ^ 2 +
        ‖GEQDu p z g j x‖ ^ 2) := by
  rw [quadField_eq, norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  set D := GEQDdu p z g h k j x
  set u := p.uOf z x
  set a := GEQDu p z g k x
  set b := GEQDu p z g j x
  have e1 : ‖(D k) • u‖ ≤ ‖D‖ * ‖u‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (norm_coord_le' D k) (norm_nonneg _)
  have e2 : ‖(a k) • b‖ ≤ ‖a‖ * ‖b‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (norm_coord_le' a k) (norm_nonneg _)
  have e3 : ‖(b k) • a‖ ≤ ‖b‖ * ‖a‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (norm_coord_le' b k) (norm_nonneg _)
  have e4 : ‖(u k) • D‖ ≤ ‖u‖ * ‖D‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (norm_coord_le' u k) (norm_nonneg _)
  have hab : 2 * (‖a‖ * ‖b‖) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc ‖(D k) • u + (a k) • b + (b k) • a + (u k) • D‖
      ≤ ‖(D k) • u‖ + ‖(a k) • b‖ + ‖(b k) • a‖ + ‖(u k) • D‖ := norm_add₄_le
    _ ≤ ‖D‖ * ‖u‖ + ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ + ‖u‖ * ‖D‖ := by gcongr
    _ ≤ 2 * (‖D‖ * ‖u‖) + ‖a‖ ^ 2 + ‖b‖ ^ 2 := by nlinarith

/-- `|D_k u|² ≤ 2 L |D_k e| + 2 |D_k w|²` when `|D_k e| ≤ L`. -/
theorem norm_Du_sq_le (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (k : Fin 3) (x : ℝ × UnforcedLeray.Space) {L : ℝ}
    (hL : ‖dy k (p.eFun (p.coord z)) x‖ ≤ L) :
    ‖GEQDu p z g k x‖ ^ 2 ≤
      2 * L * ‖dy k (p.eFun (p.coord z)) x‖ + 2 * ‖rep (g k) x.1 x.2‖ ^ 2 := by
  have h1 : ‖GEQDu p z g k x‖ ≤ ‖dy k (p.eFun (p.coord z)) x‖ + ‖rep (g k) x.1 x.2‖ :=
    norm_add_le _ _
  have h0 : 0 ≤ ‖GEQDu p z g k x‖ := norm_nonneg _
  have ha : 0 ≤ ‖dy k (p.eFun (p.coord z)) x‖ := norm_nonneg _
  have hb : 0 ≤ ‖rep (g k) x.1 x.2‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖dy k (p.eFun (p.coord z)) x‖ - ‖rep (g k) x.1 x.2‖)]

/-- `|D²u| ≤ |D²e| + |D²w|`. -/
theorem norm_Ddu_le (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (k j : Fin 3)
    (x : ℝ × UnforcedLeray.Space) :
    ‖GEQDdu p z g h k j x‖ ≤ ‖dy k (dy j (p.eFun (p.coord z))) x‖ + ‖rep (h k j) x.1 x.2‖ :=
  norm_add_le _ _

end UnforcedLeray.Short.IIb.QuadBoundSub
