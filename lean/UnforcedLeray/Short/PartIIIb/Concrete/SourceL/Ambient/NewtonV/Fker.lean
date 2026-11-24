import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV.Vec

/-!
# The parametric integrand of the zero-width Newton field (helper of `Ambient/NewtonV.lean`)

Source 4776-4782, 4870-4900.  For `a = (t, x')`,
`Fker a y = (-2 t^{2μ+2}) · Lmat (Σ_M x') (D3t (y - t (x',0)))`.  This file proves the pointwise
facts: derivative formula, `C^∞` on `{|y|² > 11ν/12}` for `t ∈ (0,1]`, and the norm bound
`‖∂^n Fker a (y)‖ ≤ K_n |Σ_M(x')|_F |y|^{-4-n}`.
-/

set_option autoImplicit false

noncomputable section

open Set UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonVGeom

/-- The coefficient operator `T ↦ -2 t^{2μ+2} Lmat(Σ_M(x')) T`. -/
def gOp (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (a : ℝ × (ℝ × ℝ)) : T3 →L[ℝ] Vec3 :=
  (-2 * a.1 ^ (2 * μ + 2)) • Lmat (sigmaM c ν χo M a.2)

/-- The integrand of `newtonV` over `a = (t, x')`. -/
def Fker (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (a : ℝ × (ℝ × ℝ)) (y : Vec3) : Vec3 :=
  gOp c ν μ χo M a (D3t (y - a.1 • embPlane a.2))

theorem gOp_eq_zero {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) {a : ℝ × (ℝ × ℝ)} (hx : ¬ a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6) :
    gOp c ν μ χo M a = 0 := by
  unfold gOp
  rw [sigmaM_support (c := c) hν hχ M a.2 (by linarith [not_le.1 hx]), Lmat_zero, smul_zero]

theorem norm_gOp_le {c ν μ : ℝ} {χo : ℝ → ℝ} (hμ : 0 ≤ μ) (M : Chart → Mat3)
    {a : ℝ × (ℝ × ℝ)} (ht0 : 0 ≤ a.1) (ht1 : a.1 ≤ 1) :
    ‖gOp c ν μ χo M a‖ ≤ 18 * frob (sigmaM c ν χo M a.2) := by
  unfold gOp
  have hp : a.1 ^ (2 * μ + 2) ≤ 1 := Real.rpow_le_one ht0 ht1 (by linarith)
  have hp0 : 0 ≤ a.1 ^ (2 * μ + 2) := Real.rpow_nonneg ht0 _
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  calc ‖(-2 * a.1 ^ (2 * μ + 2)) • Lmat (sigmaM c ν χo M a.2)‖
      = |(-2 * a.1 ^ (2 * μ + 2))| * ‖Lmat (sigmaM c ν χo M a.2)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * (9 * frob (sigmaM c ν χo M a.2)) := by
        refine mul_le_mul ?_ (norm_Lmat _) (norm_nonneg _) (by norm_num)
        rw [abs_mul, abs_neg, abs_two, abs_of_nonneg hp0]
        nlinarith
    _ = 18 * frob (sigmaM c ν χo M a.2) := by ring

theorem iter_Fker (n : ℕ) {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) {a : ℝ × (ℝ × ℝ)} (ht0 : 0 ≤ a.1) (ht1 : a.1 ≤ 1) {y : Vec3}
    (hy : ν * (11 / 12) < eucSq y) :
    iteratedFDeriv ℝ n (Fker c ν μ χo M a) y =
      (gOp c ν μ χo M a).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2)) y) := by
  by_cases h : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6
  · have hz := shift_ne_zero hν ht0 ht1 hy h
    have hcd : ContDiffAt ℝ NewtonD3.ii (fun x => D3t (x - a.1 • embPlane a.2)) y :=
      (D3t_contDiffAt hz).comp y (contDiffAt_id.sub contDiffAt_const)
    exact ContinuousLinearMap.iteratedFDeriv_comp_left (gOp c ν μ χo M a) hcd
      (by unfold NewtonD3.ii; exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))
  · have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M h
    have hF : Fker c ν μ χo M a = fun _ => 0 := by
      funext x; simp [Fker, h0]
    rw [hF, h0]
    ext m
    simp

theorem contDiffOn_Fker {c ν μ : ℝ} {χo : ℝ → ℝ} (hν : 0 < ν) (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3) {a : ℝ × (ℝ × ℝ)} (ht0 : 0 ≤ a.1) (ht1 : a.1 ≤ 1) :
    ContDiffOn ℝ NewtonD3.ii (Fker c ν μ χo M a) {w | ν * (11 / 12) < eucSq w} := by
  by_cases h : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6
  · intro y hy
    have hz := shift_ne_zero hν ht0 ht1 hy h
    have hcd : ContDiffAt ℝ NewtonD3.ii (fun x => D3t (x - a.1 • embPlane a.2)) y :=
      (D3t_contDiffAt hz).comp y (contDiffAt_id.sub contDiffAt_const)
    exact (hcd.continuousLinearMap_comp (gOp c ν μ χo M a)).contDiffWithinAt
  · have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M h
    have hF : Fker c ν μ χo M a = fun _ => 0 := by
      funext x; simp [Fker, h0]
    rw [hF]
    exact contDiffOn_const

theorem Fker_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3),
    0 < ν → IsOutwardCutoff χo → 0 ≤ μ → ∀ (a : ℝ × (ℝ × ℝ)), 0 ≤ a.1 → a.1 ≤ 1 →
    ∀ y : Vec3, ν * (11 / 12) < eucSq y →
    ‖iteratedFDeriv ℝ n (Fker c ν μ χo M a) y‖ ≤
      K * frob (sigmaM c ν χo M a.2) * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) := by
  obtain ⟨K, hK0, hK⟩ := D3t_shift_bound n
  refine ⟨18 * K, by positivity, ?_⟩
  intro c ν μ χo M hν hχ hμ a ht0 ht1 y hy
  have hp : 0 ≤ (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hf := frob_nonneg' (sigmaM c ν χo M a.2)
  rw [iter_Fker n hν hχ M ht0 ht1 hy]
  by_cases h : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ 5 * ν / 6
  · refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h1 := norm_gOp_le (c := c) (ν := ν) (χo := χo) hμ M ht0 ht1
    have h2 := hK ν a.1 y a.2 hν ht0 ht1 hy h
    calc ‖gOp c ν μ χo M a‖ * ‖iteratedFDeriv ℝ n (fun x => D3t (x - a.1 • embPlane a.2)) y‖
        ≤ (18 * frob (sigmaM c ν χo M a.2)) * (K * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 18 * K * frob (sigmaM c ν χo M a.2) * (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - n) := by ring
  · have h0 := gOp_eq_zero (c := c) (μ := μ) hν hχ M h
    have hz : ∀ φ : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec3) T3,
        (0 : T3 →L[ℝ] Vec3).compContinuousMultilinearMap φ = 0 := fun φ => by ext m; simp
    rw [h0, hz, norm_zero]
    positivity

end NewtonVGeom

end UnforcedLeray.Short.PartIIIb.Concrete
