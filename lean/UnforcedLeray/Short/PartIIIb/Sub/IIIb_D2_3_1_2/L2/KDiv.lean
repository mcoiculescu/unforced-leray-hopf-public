import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L2.Ode
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2

/-!
# `∑_i ∂_i K_{ij} = 0` (`PartIII-b:IIIb-D2/3/1/2/2`)

Source 3600-3610 (`sep:kernel`).  With `q = |x|²/4` and `Ψ = ∫_t^∞ (4πa)^{-3/2}e^{-r/a}da`,
`heatTail t = Ψ(q)`, `∂_i∂_j heatTail = Ψ''(q) x_i x_j/4 + Ψ'(q) δ_ij/2`; the ODE
`rΨ''' + (5/2)Ψ'' = (4πt)^{-3/2} t⁻¹ e^{-r/t}` (Ode.lean) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short

/-- `x ↦ |x|²/4` has derivative `(1/2) ⟨x, ·⟩`. -/
lemma kd_hq (x : Space) :
    HasFDerivAt (fun y : Space => ‖y‖ ^ 2 / 4) ((1 / 2 : ℝ) • innerSL ℝ x) x := by
  have h0 : HasFDerivAt (fun y : Space => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := h0.mul_const (1 / 4 : ℝ)
  have e : (fun y : Space => ‖y‖ ^ 2 / 4) = fun y : Space => ‖y‖ ^ 2 * (1 / 4 : ℝ) := by
    funext y; ring
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

lemma kd_hPsi (t : ℝ) (ht : 0 < t) (k : ℕ) (x : Space) :
    HasFDerivAt (fun y : Space => L2hkPsi t k (‖y‖ ^ 2 / 4))
      (L2hkPsi t (k + 1) (‖x‖ ^ 2 / 4) • ((1 / 2 : ℝ) • innerSL ℝ x)) x :=
  (L2_psi_hasDeriv t ht k _).comp_hasFDerivAt x (kd_hq x)

lemma kd_heatTail (t : ℝ) : IIIa.heatTail t = fun x : Space => L2hkPsi t 0 (‖x‖ ^ 2 / 4) := by
  funext x
  unfold IIIa.heatTail L2hkPsi
  congr 1
  funext a
  unfold IIIa.heatG L2hkG
  have e : -‖x‖ ^ 2 / (4 * a) = -(‖x‖ ^ 2 / 4) / a := by ring
  simp only [pow_zero, one_mul]
  rw [e]

lemma kd_inner (x : Space) (j : Fin 3) : inner ℝ x (coordinateVector j) = x j := by
  unfold coordinateVector
  simp [EuclideanSpace.inner_single_right]

lemma kd_fderiv_heatTail (t : ℝ) (ht : 0 < t) (j : Fin 3) :
    (fun y : Space => fderiv ℝ (IIIa.heatTail t) y (coordinateVector j)) =
      fun y : Space => L2hkPsi t 1 (‖y‖ ^ 2 / 4) * (y j / 2) := by
  funext y
  rw [kd_heatTail, (kd_hPsi t ht 0 y).fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, kd_inner]
  ring

/-- Explicit `∂_i∂_j` of the tail. -/
lemma kd_part2 (t : ℝ) (ht : 0 < t) (i j : Fin 3) (x : Space) :
    IIIa.part2 (IIIa.heatTail t) i j x =
      L2hkPsi t 1 (‖x‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
        (x j / 2) * (L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (x i / 2)) := by
  unfold IIIa.part2
  rw [kd_fderiv_heatTail t ht j]
  have hg : HasFDerivAt (fun y : Space => L2hkPsi t 1 (‖y‖ ^ 2 / 4) * (y j / 2))
      (L2hkPsi t 1 (‖x‖ ^ 2 / 4) • ((1 / 2 : ℝ) • (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) +
        (x j / 2) • (L2hkPsi t 2 (‖x‖ ^ 2 / 4) • ((1 / 2 : ℝ) • innerSL ℝ x))) x := by
    have h2 : HasFDerivAt (fun y : Space => y j / 2)
        ((1 / 2 : ℝ) • (EuclideanSpace.proj j : Space →L[ℝ] ℝ)) x := by
      have : HasFDerivAt (fun y : Space => y j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) x :=
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
      have e : (fun y : Space => y j / 2) = fun y : Space => y j * (1 / 2 : ℝ) := by
        funext y; ring
      rw [e]
      exact (this.mul_const (1 / 2 : ℝ)).congr_fderiv (by ext v; simp)
    exact (kd_hPsi t ht 1 x).mul h2
  rw [hg.fderiv]
  have e1 : (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (coordinateVector i) =
      if i = j then 1 else 0 := by
    simp only [coordinateVector]
    simp [PiLp.single_apply, eq_comm]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, kd_inner, e1]
  ring

lemma kd_hG (t : ℝ) (x : Space) :
    HasFDerivAt (fun y : Space => IIIa.heatG t y)
      (IIIa.heatG t x • ((-1 / (4 * t) : ℝ) • (2 • innerSL ℝ x))) x := by
  have h0 : HasFDerivAt (fun y : Space => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h1 := (h0.mul_const (-1 / (4 * t) : ℝ)).exp.const_mul ((4 * Real.pi * t) ^ (-3 / 2 : ℝ))
  have e : IIIa.heatG t = fun y : Space => (4 * Real.pi * t) ^ (-3 / 2 : ℝ) *
      Real.exp (‖y‖ ^ 2 * (-1 / (4 * t) : ℝ)) := by
    funext y
    unfold IIIa.heatG
    congr 2
    ring
  rw [e]
  refine h1.congr_fderiv ?_
  ext v
  simp [IIIa.heatG]
  ring_nf

lemma kd_dG (t : ℝ) (x : Space) (i : Fin 3) :
    fderiv ℝ (fun y : Space => IIIa.heatG t y) x (coordinateVector i) =
      IIIa.heatG t x * (-(x i) / (2 * t)) := by
  rw [(kd_hG t x).fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, kd_inner, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma kd_proj (i j : Fin 3) :
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (coordinateVector i) = if i = j then 1 else 0 := by
  simp only [coordinateVector]
  simp [PiLp.single_apply, eq_comm]

lemma kd_hp (k : Fin 3) (x : Space) : HasFDerivAt (fun y : Space => y k / 2)
    ((1 / 2 : ℝ) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ)) x := by
  have : HasFDerivAt (fun y : Space => y k) (EuclideanSpace.proj k : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt
  have e : (fun y : Space => y k / 2) = fun y : Space => y k * (1 / 2 : ℝ) := by
    funext y; ring
  rw [e]
  exact (this.mul_const (1 / 2 : ℝ)).congr_fderiv (by ext v; simp)

lemma kd_dP (t : ℝ) (ht : 0 < t) (i j : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
        (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2))) x (coordinateVector i) =
      L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (x i / 2) * ((if i = j then 1 else 0) / 2) +
        ((x j / 2) * (L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (1 / 2) +
            (x i / 2) * (L2hkPsi t 3 (‖x‖ ^ 2 / 4) * (x i / 2))) +
          (L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (x i / 2)) * ((if i = j then 1 else 0) / 2)) := by
  have hA : HasFDerivAt (fun y : Space => L2hkPsi t 1 (‖y‖ ^ 2 / 4))
      (L2hkPsi t 2 (‖x‖ ^ 2 / 4) • ((1 / 2 : ℝ) • innerSL ℝ x)) x := kd_hPsi t ht 1 x
  have hB : HasFDerivAt (fun y : Space => L2hkPsi t 2 (‖y‖ ^ 2 / 4))
      (L2hkPsi t 3 (‖x‖ ^ 2 / 4) • ((1 / 2 : ℝ) • innerSL ℝ x)) x := kd_hPsi t ht 2 x
  have hp : ∀ k : Fin 3, HasFDerivAt (fun y : Space => y k / 2)
      ((1 / 2 : ℝ) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ)) x := fun k => kd_hp k x
  have h := (hA.mul_const ((if i = j then (1:ℝ) else 0) / 2)).add ((hp j).mul (hB.mul (hp i)))
  have h' : HasFDerivAt (fun y : Space => L2hkPsi t 1 (‖y‖ ^ 2 / 4) *
      ((if i = j then 1 else 0) / 2) + (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2))) _ x := h
  rw [h'.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, kd_inner, kd_proj,
    Pi.mul_apply, if_true]
  ring

lemma kd_K_eq (t : ℝ) (ht : 0 < t) (i j : Fin 3) :
    (fun y : Space => IIIa.heatLerayK t i j y) = fun y : Space =>
      (if i = j then IIIa.heatG t y else 0) +
        (L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
          (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2))) := by
  funext y
  unfold IIIa.heatLerayK
  rw [kd_part2 t ht]

lemma kd_dK (t : ℝ) (ht : 0 < t) (i j : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => IIIa.heatLerayK t i j y) x (coordinateVector i) =
      (if i = j then IIIa.heatG t x * (-(x i) / (2 * t)) else 0) +
      (L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (x i / 2) * ((if i = j then 1 else 0) / 2) +
        ((x j / 2) * (L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (1 / 2) +
            (x i / 2) * (L2hkPsi t 3 (‖x‖ ^ 2 / 4) * (x i / 2))) +
          (L2hkPsi t 2 (‖x‖ ^ 2 / 4) * (x i / 2)) * ((if i = j then 1 else 0) / 2))) := by
  rw [kd_K_eq t ht]
  have hP : DifferentiableAt ℝ (fun y : Space => L2hkPsi t 1 (‖y‖ ^ 2 / 4) *
      ((if i = j then 1 else 0) / 2) + (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2))) x := by
    have hA := (kd_hPsi t ht 1 x).differentiableAt
    have hB := (kd_hPsi t ht 2 x).differentiableAt
    have hpj := (kd_hp j x).differentiableAt
    have hpi := (kd_hp i x).differentiableAt
    exact (hA.mul_const _).add (hpj.mul (hB.mul hpi))
  by_cases h : i = j
  · have e : (fun y : Space => (if i = j then IIIa.heatG t y else 0) +
        (L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
          (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2)))) = fun y : Space =>
        IIIa.heatG t y +
        (L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
          (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2))) := by
      funext y; rw [if_pos h]
    rw [e]
    have hG := (kd_hG t x).differentiableAt
    have hs' := hG.hasFDerivAt.add hP.hasFDerivAt
    have hs'' : HasFDerivAt (fun y : Space => IIIa.heatG t y +
        (L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
          (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2)))) _ x := hs'
    rw [hs''.fderiv]
    simp only [add_apply]
    rw [← hP.hasFDerivAt.fderiv, ← hG.hasFDerivAt.fderiv, kd_dG, kd_dP t ht]
    have eG : (if i = j then IIIa.heatG t x * (-(x i) / (2 * t)) else 0) =
        IIIa.heatG t x * (-(x i) / (2 * t)) := if_pos h
    rw [eG]
  · have e : (fun y : Space => (if i = j then IIIa.heatG t y else 0) +
        (L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
          (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2)))) = fun y : Space =>
        (L2hkPsi t 1 (‖y‖ ^ 2 / 4) * ((if i = j then 1 else 0) / 2) +
          (y j / 2) * (L2hkPsi t 2 (‖y‖ ^ 2 / 4) * (y i / 2))) := by
      funext y; rw [if_neg h, zero_add]
    rw [e, kd_dP t ht]
    have eG : (if i = j then IIIa.heatG t x * (-(x i) / (2 * t)) else 0) = 0 := if_neg h
    rw [eG, zero_add]

lemma kd_norm_sq (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

/-- **Divergence-free kernel** (3600-3610): `∑_i ∂_i K_{ij} = 0` for `t > 0`. -/
theorem kd_divfree (t : ℝ) (ht : 0 < t) (j : Fin 3) (x : Space) :
    ∑ i : Fin 3, fderiv ℝ (fun y : Space => IIIa.heatLerayK t i j y) x (coordinateVector i) = 0 := by
  have hode := psi_ode_deriv t ht (‖x‖ ^ 2 / 4)
  have hG : IIIa.heatG t x = (4 * Real.pi * t) ^ (-3 / 2 : ℝ) * Real.exp (-(‖x‖ ^ 2 / 4) / t) := by
    unfold IIIa.heatG
    congr 2
    ring
  have hn := kd_norm_sq x
  simp only [kd_dK t ht, Fin.sum_univ_three]
  rw [hG]
  fin_cases j
  · simp
    linear_combination (x 0 / 2) * hode - (x 0 * L2hkPsi t 3 (‖x‖ ^ 2 / 4) / 8) * hn
  · simp
    linear_combination (x 1 / 2) * hode - (x 1 * L2hkPsi t 3 (‖x‖ ^ 2 / 4) / 8) * hn
  · simp
    linear_combination (x 2 / 2) * hode - (x 2 * L2hkPsi t 3 (‖x‖ ^ 2 / 4) / 8) * hn

end UnforcedLeray.Short.PartIIIb.Concrete
