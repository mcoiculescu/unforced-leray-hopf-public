import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Assemble
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Vanish

/-!
# Pointwise derivative bounds of the real ring lift: shared reductions

Source `the November 2 reference manuscript`
lines 2385-2387, 2562-2564.  Passage from the jets of `Nv R b τ` (`nv_jets`) to the
`dy`-derivatives of `(τ, y) ↦ realC (Nv R b τ y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.PhaseSpace

/-- `realC` as a real-linear map. -/
def realCL : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

theorem realCL_apply (x : Space) : realCL x = UnforcedLeray.B0412.realC x := rfl

theorem norm_realC (x : Space) : ‖UnforcedLeray.B0412.realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [UnforcedLeray.B0412.realC_apply, Complex.norm_real]

theorem norm_realCL_le : ‖realCL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [realCL_apply, norm_realC, one_mul]

theorem iter_realC_le {f : Space → Space} (hf : ContDiff ℝ ∞ f) (n : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ n (fun z => UnforcedLeray.B0412.realC (f z)) y‖ ≤
      ‖iteratedFDeriv ℝ n f y‖ := by
  have h := realCL.norm_iteratedFDeriv_comp_left (f := f) (x := y) (N := ∞) (n := n)
    hf.contDiffAt (by exact_mod_cast le_top)
  have h2 : ‖realCL‖ * ‖iteratedFDeriv ℝ n f y‖ ≤ ‖iteratedFDeriv ℝ n f y‖ := by
    calc ‖realCL‖ * ‖iteratedFDeriv ℝ n f y‖ ≤ 1 * ‖iteratedFDeriv ℝ n f y‖ :=
          mul_le_mul_of_nonneg_right norm_realCL_le (norm_nonneg _)
      _ = _ := one_mul _
  exact le_trans h h2

theorem dy_eq_zero {Φ : ℝ × Space → CVec3} {p : ℝ × Space} (h : ∀ᶠ q in 𝓝 p, Φ q = 0)
    (j : Fin 3) : dy j Φ p = 0 := by
  have h' : Φ =ᶠ[𝓝 p] fun _ => (0 : CVec3) := h
  simp [dy, h'.fderiv_eq]

theorem dydy_eq_zero {Φ : ℝ × Space → CVec3} {p : ℝ × Space} (h : ∀ᶠ q in 𝓝 p, Φ q = 0)
    (j k : Fin 3) : dy j (dy k Φ) p = 0 :=
  dy_eq_zero (h.eventually_nhds.mono fun q hq => dy_eq_zero hq k) j

theorem sqrt_age_eq_at {R : ℝ} (hR : 0 < R) (y : Space) :
    √(Axi.age R y) = R * (Axi.ϱ y)⁻¹ := congrFun (sqrt_age_eq hR) y

theorem age_rpow_three_halves {R : ℝ} (hR : 0 < R) (y : Space) :
    Axi.age R y ^ (3 / 2 : ℝ) = R ^ 3 * ((Axi.ϱ y)⁻¹) ^ 3 := by
  have h0 : 0 ≤ Axi.age R y := by rw [age_eq_sq]; positivity
  have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [e, Real.rpow_add' h0 (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow,
    sqrt_age_eq_at hR, age_eq_sq]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
