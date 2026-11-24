import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.Liouville
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Part II-b, task `PartII-b:G4/2/3/4/6`: Cauchy estimates for a planar holomorphic function

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

The map `L(x) = x₁ - i x₂` is real-linear `ℝ × ℝ → ℂ` with `‖L‖ ≤ 2` and `L(z.re, -z.im) = z`.
Composition with `L` on the open preimage of the disc is a real-analytic chart, so the
`j`-th Fréchet derivative of `g ∘ L` at `(z.re, -z.im)` is the `j`-th complex derivative of `g`
composed with `j` copies of `L`. Cauchy's estimate bounds the latter by `j! B / r^j`.
A = `2^j j!`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace UnforcedLeray.Short.IIb

/-- **`cauchy_planar`** (SP 2349-2358): derivatives of order `j` of `x ↦ g(x₁ - i x₂)` at
`(z.re, -z.im)` are bounded by `2^j j! B / r^j`, when `g` is holomorphic on the closed disc of
radius `r` about `z` and `|g| ≤ B` there. -/
theorem cauchy_planar (j : ℕ) : ∃ A : ℝ, ∀ (g : ℂ → ℂ) (r B : ℝ) (z : ℂ), 0 < r →
    DifferentiableOn ℂ g (Metric.closedBall z r) → (∀ w ∈ Metric.closedBall z r, ‖g w‖ ≤ B) →
    ‖iteratedFDeriv ℝ j (fun x : ℝ × ℝ => g ((x.1 : ℂ) - (x.2 : ℂ) * Complex.I)) (z.re, -z.im)‖
      ≤ A * B / r ^ j := by
  refine ⟨2 ^ j * (j.factorial : ℝ), fun g r B z hr hd hB => ?_⟩
  -- the real-linear map `L x = x₁ - i x₂` with norm at most `2`
  have hL : ∃ L : (ℝ × ℝ) →L[ℝ] ℂ, (∀ x, L x = (x.1 : ℂ) - (x.2 : ℂ) * Complex.I) ∧ ‖L‖ ≤ 2 := by
    let Llin : (ℝ × ℝ) →ₗ[ℝ] ℂ :=
      { toFun := fun x => (x.1 : ℂ) - (x.2 : ℂ) * Complex.I
        map_add' := fun x y => by
          simp only [Prod.fst_add, Prod.snd_add]
          push_cast
          ring
        map_smul' := fun a x => by
          simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Complex.real_smul,
            smul_eq_mul, Complex.ofReal_mul]
          ring }
    have hb : ∀ x, ‖Llin x‖ ≤ 2 * ‖x‖ := by
      intro x
      show ‖(x.1 : ℂ) - (x.2 : ℂ) * Complex.I‖ ≤ 2 * ‖x‖
      have h1 : ‖(x.1 : ℂ)‖ ≤ ‖x‖ := by
        rw [Complex.norm_real]
        exact norm_fst_le x
      have h2 : ‖(x.2 : ℂ)‖ ≤ ‖x‖ := by
        rw [Complex.norm_real]
        exact norm_snd_le x
      calc ‖(x.1 : ℂ) - (x.2 : ℂ) * Complex.I‖
          ≤ ‖(x.1 : ℂ)‖ + ‖(x.2 : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ = ‖(x.1 : ℂ)‖ + ‖(x.2 : ℂ)‖ := by rw [norm_mul, Complex.norm_I, mul_one]
        _ ≤ 2 * ‖x‖ := by linarith
    refine ⟨Llin.mkContinuous 2 hb, fun x => rfl, ?_⟩
    exact LinearMap.mkContinuous_norm_le _ (by norm_num) hb
  obtain ⟨L, hLapp, hL2⟩ := hL
  have hfun : (fun x : ℝ × ℝ => g ((x.1 : ℂ) - (x.2 : ℂ) * Complex.I)) = g ∘ L := by
    funext x
    rw [Function.comp_apply, hLapp]
  have hLx0 : L (z.re, -z.im) = z := by
    rw [hLapp]
    apply Complex.ext <;> simp
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB z (Metric.mem_closedBall_self hr.le))
  rw [hfun]
  have hball : DifferentiableOn ℂ g (Metric.ball z r) := hd.mono Metric.ball_subset_closedBall
  have hcd : ContDiffOn ℂ ⊤ g (Metric.ball z r) := DifferentiableOn.contDiffOn (n := ⊤) hball Metric.isOpen_ball
  have hcdR : ContDiffOn ℝ ⊤ g (Metric.ball z r) := ContDiffOn.restrict_scalars (𝕜 := ℝ) hcd
  have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hW : IsOpen (L ⁻¹' Metric.ball z r) := Metric.isOpen_ball.preimage L.continuous
  have hx0W : (z.re, -z.im) ∈ L ⁻¹' Metric.ball z r := by
    show L (z.re, -z.im) ∈ Metric.ball z r
    rw [hLx0]
    exact hzball
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (f := g) L hcdR
    Metric.isOpen_ball.uniqueDiffOn hW.uniqueDiffOn (x := (z.re, -z.im))
    (by rw [hLx0]; exact hzball) (i := j) le_top
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g ∘ L) j hW hx0W
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) j Metric.isOpen_ball hzball
  rw [← e1, hcomp, hLx0, e2]
  -- the norm of the composition
  have hnorm1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j g z) (fun _ : Fin j => L)
  have hprod : ∏ _i : Fin j, ‖L‖ ≤ 2 ^ j := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hL2 j
  -- real and complex norms of the `j`-th derivative agree (`g` is holomorphic)
  have hres : ‖iteratedFDeriv ℝ j g z‖ = ‖iteratedFDeriv ℂ j g z‖ := by
    have h := ((hcd.contDiffAt (Metric.isOpen_ball.mem_nhds hzball)).of_le le_top).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ) (n := j)
    rw [← h, Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  have hcomplex : ‖iteratedFDeriv ℂ j g z‖ = ‖iteratedDeriv j g z‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  -- Cauchy's estimate on the disc
  have hcau : ‖iteratedDeriv j g z‖ ≤ (j.factorial : ℝ) * B / r ^ j := by
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    · refine ⟨hball, ?_⟩
      rw [closure_ball z hr.ne']
      exact hd.continuousOn
    · intro w hw
      exact hB w (Metric.sphere_subset_closedBall hw)
  have h3 : ‖iteratedFDeriv ℝ j g z‖ ≤ (j.factorial : ℝ) * B / r ^ j := by
    rw [hres, hcomplex]
    exact hcau
  have hprod0 : 0 ≤ ∏ _i : Fin j, ‖L‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hbound0 : 0 ≤ (j.factorial : ℝ) * B / r ^ j :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hB0) (pow_nonneg hr.le _)
  calc ‖(iteratedFDeriv ℝ j g z).compContinuousLinearMap (fun _ : Fin j => L)‖
      ≤ ‖iteratedFDeriv ℝ j g z‖ * ∏ _i : Fin j, ‖L‖ := hnorm1
    _ ≤ ((j.factorial : ℝ) * B / r ^ j) * 2 ^ j :=
        mul_le_mul h3 hprod hprod0 hbound0
    _ = 2 ^ j * (j.factorial : ℝ) * B / r ^ j := by ring

end UnforcedLeray.Short.IIb
