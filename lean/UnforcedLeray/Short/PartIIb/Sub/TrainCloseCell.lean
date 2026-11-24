import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Part II-b: the train comparison on the cell gives the bound on the plane

Source: `the November 2 reference manuscript` lines 2074-2076 (the weighted space
`X_{m,c} = L²(C_c, (1+q²+η²)^m)` on the centered cell) and 2085-2093 (the train comparison
`‖v_c - V_c^p‖ + ‖E_c - E_c^p‖ ≤ δ_c` in a fixed finite weighted derivative budget).

`TrainClose tr Σ δ` (`StatementsMixed.lean`) bounds `‖D^j(v - V_c^p)‖ ⟨x⟩⁸` by `δ` for `x` in the
centered cell `B0579.cell c` only. The train velocity `v` and the periodized heat vortex `V_c^p` are
both `c`-periodic in `q` (`IsTrain.periodic_v`, `Train.Vc_periodic`), so every point of the plane is
an integer translate in `q` of a point of the cell, and the derivatives of the difference are
translation invariant. Since `⟨x⟩⁸ = jb x ^ 4 ≥ 1`, this gives `‖D^j(v - V_c^p)(x)‖ ≤ δ` for every
`x` in the plane (`TrainClose.plane_bound`), with the order `0` and order `1` forms
`TrainClose.norm_sub_le`, `TrainClose.norm_fderiv_sub_le`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIb

/-- Wrapping into the centered cell: `qwrap c q = q - ⌊(q + c/2)/c⌋ c ∈ [-c/2, c/2)`. -/
theorem qwrap_mem_Ico {c : ℝ} (hc : 0 < c) (q : ℝ) : qwrap c q ∈ Ico (-(c / 2)) (c / 2) := by
  unfold qwrap
  set n : ℤ := ⌊(q + c / 2) / c⌋ with hn
  have h1 : (n : ℝ) ≤ (q + c / 2) / c := Int.floor_le _
  have h2 : (q + c / 2) / c < (n : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  constructor
  · nlinarith
  · nlinarith

/-- The difference `v - V_c^p` of a train and the periodized heat vortex at an age `s ≥ 0` is
invariant under integer translations in `q` by multiples of `c`. -/
theorem trainDiff_sub_int_mul {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (n : ℤ)
    (z : B0579.Plane) :
    tr.v s (z.1 - n * c, z.2) - Train.Vc ν c s (z.1 - n * c, z.2) =
      tr.v s z - Train.Vc ν c s z := by
  have hper : Function.Periodic
      (fun q : ℝ => tr.v s (q, z.2) - Train.Vc ν c s (q, z.2)) c := by
    intro q
    simp only
    rw [tr.isTrain.periodic_v s hs (q, z.2), Train.Vc_periodic ν c s (q, z.2)]
  exact hper.sub_int_mul_eq n

/-- The iterated derivatives of `v - V_c^p` are invariant under the same translations. -/
theorem iteratedFDeriv_trainDiff_sub_int_mul {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) (n : ℤ) (j : ℕ) (x : B0579.Plane) :
    iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) (x.1 - n * c, x.2) =
      iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x := by
  set a : B0579.Plane := (-(n * c), 0) with ha
  have hfun : (fun z : B0579.Plane => tr.v s (z + a) - Train.Vc ν c s (z + a)) =
      fun z => tr.v s z - Train.Vc ν c s z := by
    funext z
    have hz : z + a = (z.1 - n * c, z.2) := by
      rw [ha]
      ext <;> simp [sub_eq_add_neg]
    rw [hz]
    exact trainDiff_sub_int_mul tr hs n z
  have hx : x + a = (x.1 - n * c, x.2) := by
    rw [ha]
    ext <;> simp [sub_eq_add_neg]
  have key := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun z : B0579.Plane => tr.v s z - Train.Vc ν c s z) j a x
  rw [hfun, hx] at key
  exact key.symm

/-- **The cell bound gives the plane bound.** If `TrainClose tr Σ δ` (weighted bound on the
centered cell), then `‖D^j(v - V_c^p)(x)‖ ≤ δ` for `j ≤ 4`, `0 ≤ s ≤ Σ/ν` and every `x` in the
plane (SP 2074-2076, 2085-2093; periodicity in `q` and `⟨x⟩⁸ ≥ 1`). -/
theorem TrainClose.plane_bound {ν c : ℝ} (hc : 0 < c) {tr : B0140.TrainSol ν c} {Sg δ : ℝ}
    (h : TrainClose tr Sg δ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Sg / ν) (x : B0579.Plane)
    {j : ℕ} (hj : j ≤ 4) :
    ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x‖ ≤ δ := by
  set n : ℤ := ⌊(x.1 + c / 2) / c⌋ with hn
  have hmem : ((x.1 - n * c, x.2) : B0579.Plane) ∈ B0579.cell c := by
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    have := qwrap_mem_Ico hc x.1
    unfold qwrap at this
    rw [← hn] at this
    rwa [mul_comm] at this
  have hb := h s hs0 hs1 _ hmem j hj
  rw [iteratedFDeriv_trainDiff_sub_int_mul tr hs0 n j x] at hb
  have hjb : 1 ≤ B0579.jb (x.1 - n * c, x.2) := by
    unfold B0579.jb
    nlinarith [sq_nonneg (x.1 - n * c), sq_nonneg x.2]
  have h4 : 1 ≤ B0579.jb (x.1 - n * c, x.2) ^ 4 := one_le_pow₀ hjb
  have hnn := norm_nonneg
    (iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x)
  nlinarith [mul_le_mul_of_nonneg_left h4 hnn]

/-- Order `0` of `TrainClose.plane_bound`: `‖v(s, x) - V_c^p(s, x)‖ ≤ δ` on the plane. -/
theorem TrainClose.norm_sub_le {ν c : ℝ} (hc : 0 < c) {tr : B0140.TrainSol ν c} {Sg δ : ℝ}
    (h : TrainClose tr Sg δ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Sg / ν) (x : B0579.Plane) :
    ‖tr.v s x - Train.Vc ν c s x‖ ≤ δ := by
  have hb := h.plane_bound hc hs0 hs1 x (j := 0) (Nat.zero_le 4)
  rwa [norm_iteratedFDeriv_zero] at hb

/-- Order `1` of `TrainClose.plane_bound`: `‖D(v - V_c^p)(s, x)‖ ≤ δ` on the plane. -/
theorem TrainClose.norm_fderiv_sub_le {ν c : ℝ} (hc : 0 < c) {tr : B0140.TrainSol ν c}
    {Sg δ : ℝ} (h : TrainClose tr Sg δ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Sg / ν)
    (x : B0579.Plane) :
    ‖fderiv ℝ (fun z => tr.v s z - Train.Vc ν c s z) x‖ ≤ δ := by
  have hb := h.plane_bound hc hs0 hs1 x (j := 1) (by norm_num)
  rwa [norm_iteratedFDeriv_one] at hb

/-- Componentwise order `0`: `|v_k(s, x) - (V_c^p)_k(s, x)| ≤ δ` on the plane. -/
theorem TrainClose.abs_sub_le {ν c : ℝ} (hc : 0 < c) {tr : B0140.TrainSol ν c} {Sg δ : ℝ}
    (h : TrainClose tr Sg δ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Sg / ν) (x : B0579.Plane)
    (k : Fin 2) :
    |tr.v s x k - Train.Vc ν c s x k| ≤ δ := by
  have h1 := PiLp.norm_apply_le (tr.v s x - Train.Vc ν c s x) k
  rw [PiLp.sub_apply, Real.norm_eq_abs] at h1
  exact h1.trans (h.norm_sub_le hc hs0 hs1 x)

end UnforcedLeray.Short.IIb
