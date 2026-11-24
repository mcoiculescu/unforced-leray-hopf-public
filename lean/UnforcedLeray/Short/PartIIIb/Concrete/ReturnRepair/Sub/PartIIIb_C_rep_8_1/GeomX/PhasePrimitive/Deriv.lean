import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Moment

/-!
# `D_yX₀` in terms of `D_yW_μ`, `D_yW_{μ+1}` (helper for `GeomX.PhasePrimitive`)

Source `the November 2 reference manuscript`
lines 4171 (`X₀ = W_μ - W_{μ+1}`, real Cartesian components), 3604-3621 (`W_μ` is smooth off
the source disk).

`wardX0 = Φ ∘ (W_μ - W_{μ+1})` with `Φ v = (Re v_i)_i` of norm `≤ 2`, so at a point where the four
complex responses are differentiable
`‖D zAct - D zMid‖ ≤ 2(‖DW_μ(g) - DW_μ(ḡ)‖ + ‖DW_{μ+1}(g) - DW_{μ+1}(ḡ)‖)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PhasePrim

/-- The real part, componentwise, as a map to `Space`. -/
def reMap : (Fin 3 → ℂ) →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

theorem reMap_apply (v : Fin 3 → ℂ) : reMap v = WithLp.toLp 2 (fun i => (v i).re) := rfl

theorem norm_reMap_le (v : Fin 3 → ℂ) : ‖reMap v‖ ≤ 2 * ‖v‖ := by
  rw [reMap_apply, EuclideanSpace.norm_eq]
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  rw [show 2 * ‖v‖ = Real.sqrt ((2 * ‖v‖) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have hi : ∀ i, ‖(WithLp.toLp 2 (fun i => (v i).re) : Space) i‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have h1 : ‖(WithLp.toLp 2 (fun i => (v i).re) : Space) i‖ ≤ ‖v‖ := by
      show ‖(v i).re‖ ≤ ‖v‖
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (norm_le_pi_norm v i)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖(WithLp.toLp 2 (fun i => (v i).re) : Space) i‖ ^ 2
      ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * ‖v‖ ^ 2 := by simp
    _ ≤ (2 * ‖v‖) ^ 2 := by nlinarith [sq_nonneg ‖v‖]

theorem opNorm_reMap_le : ‖reMap‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) norm_reMap_le

theorem fderiv_wardX0 (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y)
    (hB : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) y) :
    fderiv ℝ (wardX0 ν μ R c g τ) y =
      reMap.comp (fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y -
        fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) y) := by
  have hw : wardX0 ν μ R c g τ = fun y => reMap
      ((fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y -
        (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) y) := by
    funext y
    rfl
  rw [hw]
  exact (reMap.hasFDerivAt.comp y (hA.hasFDerivAt.sub hB.hasFDerivAt)).fderiv

/-- **The phase part through the complex responses.** -/
theorem dX0_le (ν μ R c : ℝ) (g g' : Chart → Ten3) (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y)
    (hB : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) y)
    (hA' : DifferentiableAt ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g') y τ) y)
    (hB' : DifferentiableAt ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g') y τ) y) :
    ‖fderiv ℝ (wardX0 ν μ R c g τ) y - fderiv ℝ (wardX0 ν μ R c g' τ) y‖ ≤
      2 * (‖fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y -
            fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g') y τ) y‖ +
          ‖fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) y -
            fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g') y τ) y‖) := by
  rw [fderiv_wardX0 ν μ R c g τ y hA hB, fderiv_wardX0 ν μ R c g' τ y hA' hB',
    ← ContinuousLinearMap.comp_sub]
  set a := fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ) y
  set b := fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ) y
  set a' := fderiv ℝ (fun y => IIIa.sepW ν (μ : ℂ) (oldPhys R c g') y τ) y
  set b' := fderiv ℝ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g') y τ) y
  have e : a - b - (a' - b') = (a - a') - (b - b') := by abel
  rw [e]
  calc ‖reMap.comp ((a - a') - (b - b'))‖ ≤ ‖reMap‖ * ‖(a - a') - (b - b')‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (‖a - a'‖ + ‖b - b'‖) :=
        mul_le_mul opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)

/-- `W_μ(oldPhys G)` is differentiable off the old cylinder (`sep:resolvent` + `sep:kernel`). -/
theorem sepW_diff (c ν ε : ℝ) (μ : ℂ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hμ : -(1 / 4) < μ.re) (G : Chart → Ten3) (hGm : Measurable G)
    (hmom : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤)
    (hz : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → G p = 0) (τ : ℝ) (y : Space)
    (hy : ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y) :
    DifferentiableAt ℝ (fun y => IIIa.sepW ν μ (oldPhys ε⁻¹ c G) y τ) y := by
  obtain ⟨P, T', hP, hS, hM, hE⟩ := ZRegAux.sepSrc_of_chart c ν ε hc hν hε G hGm hmom hz
  have hW := sepWSmoothOn_of IIIa.sepKernelBounds ν μ _ P T' hν hμ (by positivity) hP hS hM τ
  have hopen : IsOpen {y : Space | ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y} :=
    isOpen_lt continuous_const continuous_ϱ
  have e : (fun y => IIIa.sepW ν μ (oldPhys ε⁻¹ c G) y τ) = fun y => IIIa.sepW ν μ T' y τ :=
    funext fun y => hE μ y τ
  rw [e, differentiableAt_pi]
  intro i
  exact ((hW i).differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hy)

end PhasePrim

end UnforcedLeray.Short.PartIIIb.Concrete
