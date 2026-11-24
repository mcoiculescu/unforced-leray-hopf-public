import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!


Source: `the November 2 reference manuscript` lines 2085-2093 (the train drift and
its derivatives are bounded) together with 327-336 (`‖D^j V_c‖_∞ ≤ C_j a^{-(3+j)/2}` for
`1 ≤ a ≤ c²`).  The condition `a ≤ c²` is removed for a bounded range of `a`: if `m c ≥ √a`,
the `c`-periodization is the sum of `m` translates of the `m c`-periodization.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `c`-periodization splits into `m` translates of the `m c`-periodization. -/
theorem Vc_split (ν c s : ℝ) (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) (m : ℕ) [NeZero m]
    (z : ℝ × ℝ) :
    Train.Vc ν c s z = ∑ j : Fin m, Train.Vc ν (m * c) s (z.1 - (j : ℕ) * c, z.2) := by
  simp only [Train.Vc, Gaussian.periodize]
  have hsum := Train.summable_isoV hν hc.ne' hs z
  let E : Fin m × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv m).symm
  have hE : ∀ p : Fin m × ℤ, E p = p.2 * m + ((p.1 : ℕ) : ℤ) := fun p => by
    simp [E, Int.divModEquiv]
  have hs' : Summable (fun p : Fin m × ℤ =>
      Train.isoV ν s (z.1 - (E p : ℝ) * c, z.2)) := (E.summable_iff (f := fun n : ℤ =>
        Train.isoV ν s (z.1 - (n : ℝ) * c, z.2))).2 hsum
  have h1 := (E.tsum_eq (fun n : ℤ => Train.isoV ν s (z.1 - (n : ℝ) * c, z.2))).symm
  have h2 := hs'.tsum_prod' (fun j => hs'.prod_factor j)
  rw [h1, h2, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine tsum_congr fun k => ?_
  congr 2
  rw [hE]
  push_cast
  ring

/-- Uniform bounds on all iterated derivatives of `V_c(s)` for a bounded range of `ν s`,
for every period `c > 0`. -/
theorem Vc_iter_bound (ν c Smax : ℝ) (hν : 0 < ν) (hc : 0 < c) (hS : 0 ≤ Smax) (k : ℕ) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → ν * s ≤ Smax → ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ k (Train.Vc ν c s) z‖ ≤ M := by
  obtain ⟨Cg, hCg⟩ := (UnforcedLeray.Short.Spine.vcRegularity_proof).2 k
  set m : ℕ := ⌈Real.sqrt (1 + Smax) / c⌉₊ + 1 with hm
  have : NeZero m := ⟨by omega⟩
  have hmc : Real.sqrt (1 + Smax) ≤ (m : ℝ) * c := by
    have h1 : Real.sqrt (1 + Smax) / c ≤ (⌈Real.sqrt (1 + Smax) / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) = (⌈Real.sqrt (1 + Smax) / c⌉₊ : ℝ) + 1 := by rw [hm]; push_cast; ring
    rw [div_le_iff₀ hc] at h1
    nlinarith
  have hmc2 : 1 + Smax ≤ ((m : ℝ) * c) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt (1 + Smax) := Real.sqrt_nonneg _
    have := pow_le_pow_left₀ h0 hmc 2
    rwa [Real.sq_sqrt (by linarith)] at this
  refine ⟨(m : ℝ) * |Cg|, fun s hs hνs z => ?_⟩
  have ha1 : 1 ≤ B0113.heatWidth ν s := by
    unfold B0113.heatWidth; nlinarith [mul_nonneg hν.le hs]
  have ha2 : B0113.heatWidth ν s ≤ ((m : ℝ) * c) ^ 2 := by
    unfold B0113.heatWidth; linarith
  have hmcpos : 0 < (m : ℝ) * c := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
    positivity
  have hcd : ContDiff ℝ ∞ (Train.Vc ν (m * c) s) :=
    Short.Spine.vcReg_contDiff_Vc hmcpos (Short.Spine.vcReg_width_pos hν hs)
  have hfun : Train.Vc ν c s = fun z => ∑ j : Fin m,
      (fun w => Train.Vc ν (m * c) s (w + (-((j : ℕ) * c), 0))) z := by
    funext z
    rw [Vc_split ν c s hν hc hs m z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ext <;> simp [sub_eq_add_neg]
  have hcdj : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      ContDiff ℝ k (fun w => Train.Vc ν (m * c) s (w + (-((j : ℕ) * c), 0))) := fun j _ =>
    (hcd.comp (contDiff_id.add contDiff_const)).of_le (mod_cast le_top)
  have hit := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (u := Finset.univ) hcdj) z
  rw [hfun]
  rw [hit]
  simp only [Finset.sum_apply]
  have hbd : ∀ j : Fin m, ‖iteratedFDeriv ℝ k
      (fun w => Train.Vc ν (m * c) s (w + (-((j : ℕ) * c), 0))) z‖ ≤ |Cg| := by
    intro j
    rw [iteratedFDeriv_comp_add_right]
    refine (hCg ν (m * c) s hmcpos ha1 ha2 _).trans ?_
    have hp : B0113.heatWidth ν s ^ (-((3 + (k : ℝ)) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1 (by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith [show 0 ≤ (3 + (k : ℝ)) / 2 by positivity])
    have hp0 : 0 ≤ B0113.heatWidth ν s ^ (-((3 + (k : ℝ)) / 2)) :=
      Real.rpow_nonneg (by linarith) _
    calc Cg * B0113.heatWidth ν s ^ (-((3 + (k : ℝ)) / 2))
        ≤ |Cg| * B0113.heatWidth ν s ^ (-((3 + (k : ℝ)) / 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hp0
      _ ≤ |Cg| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = |Cg| := mul_one _
  calc ‖∑ j : Fin m, iteratedFDeriv ℝ k
        (fun w => Train.Vc ν (m * c) s (w + (-((j : ℕ) * c), 0))) z‖
      ≤ ∑ j : Fin m, ‖iteratedFDeriv ℝ k
        (fun w => Train.Vc ν (m * c) s (w + (-((j : ℕ) * c), 0))) z‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, |Cg| := Finset.sum_le_sum fun j _ => hbd j
    _ = (m : ℝ) * |Cg| := by simp

end UnforcedLeray.Short.IIb
