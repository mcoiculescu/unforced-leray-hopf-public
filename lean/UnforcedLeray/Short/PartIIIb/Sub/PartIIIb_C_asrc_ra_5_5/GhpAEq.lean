import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5

/-!
# `PartIII-b:C/asrc/ra/5/5` : explicit form of the `j = 0` summand (source 4963-4968)

`V_0(s,y) = a⁻² e^{-|y|²/(4a)} J y` (`x_0 = y`), so the summand
`G = A^y_mer V_0 - DV_0[A^y_mer y]` equals `e^{-|y|²/(4a)} • PhpA`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The rotation `J` as a continuous linear map. -/
def ghpAEqJ : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

lemma ghpAEqJ_apply (x : ℝ × ℝ) : ghpAEqJ x = Jrot x := by
  simp [ghpAEqJ, Jrot]

lemma ghpAEq_Vj0 (ν s : ℝ) (y : ℝ × ℝ) :
    Vj ν s 0 y = ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * ageA ν s))) • Jrot y := by
  have hx : xj ν 0 y = y := by simp [xj]
  unfold Vj
  rw [hx]

lemma ghpAEq_Vj0_fun (ν s : ℝ) :
    Vj ν s 0 = fun y : ℝ × ℝ =>
      ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * ageA ν s))) • ghpAEqJ y := by
  funext y
  rw [ghpAEqJ_apply, ghpAEq_Vj0]

lemma ghpAEq_fderiv (ν s : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (Vj ν s 0) y v =
      ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * ageA ν s))) • Jrot v
        + (((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * ageA ν s)))
            * (-((y.1 * v.1 + y.2 * v.2) / (2 * ageA ν s)))) • Jrot y := by
  have hsq_eq : (fun z : ℝ × ℝ => sq2 z) = fun z => z.1 * z.1 + z.2 * z.2 := by
    funext z
    simp [sq2, sq]
  have f1 : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
    hasFDerivAt_fst
  have f2 : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    hasFDerivAt_snd
  have hsq : HasFDerivAt (fun z : ℝ × ℝ => sq2 z)
      ((2 * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    rw [hsq_eq]
    refine ((f1.mul f1).add (f2.mul f2)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun w => ?_
    simp
    ring
  have hh : HasFDerivAt (fun z : ℝ × ℝ => -(sq2 z) / (4 * ageA ν s))
      ((-(4 * ageA ν s)⁻¹) • ((2 * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) y := by
    have hfun : (fun z : ℝ × ℝ => -(sq2 z) / (4 * ageA ν s))
        = fun z => (-(4 * ageA ν s)⁻¹) * sq2 z := by
      funext z
      ring
    rw [hfun]
    exact hsq.const_mul _
  have hc := (hh.exp).const_mul ((ageA ν s ^ 2)⁻¹)
  have hF := hc.smul (ghpAEqJ.hasFDerivAt (x := y))
  rw [ghpAEq_Vj0_fun]
  change fderiv ℝ (((fun z : ℝ × ℝ => (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 z) / (4 * ageA ν s)))
    • (ghpAEqJ : ℝ × ℝ → ℝ × ℝ))) y v = _
  rw [hF.fderiv]
  have hfst : ∀ w : ℝ × ℝ, ContinuousLinearMap.fst ℝ ℝ ℝ w = w.1 := fun w => rfl
  have hsnd : ∀ w : ℝ × ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ w = w.2 := fun w => rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ghpAEqJ_apply, smul_eq_mul, hfst, hsnd]
  rw [add_right_inj]
  congr 1
  ring

theorem ghpA_eq_proof : GhpA_eq := by
  intro ν χ A p
  unfold GhpA PhpA
  rw [ghpAEq_Vj0, ghpAEq_fderiv]
  refine Prod.ext ?_ ?_ <;> simp [merApply, Jrot] <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
