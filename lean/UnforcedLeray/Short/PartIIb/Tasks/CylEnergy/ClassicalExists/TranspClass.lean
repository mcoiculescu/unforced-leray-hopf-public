import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

/-!


Source of record: `the November 2 reference manuscript`, lines 2074-2093 (the cylinder
equation `ω_s = (νΔ - v·∇ + A) ω`) and 2103-2105 (smoothing). The statement is `TranspClass`
(`Sub/T22_1/Stages.lean`): for `CylCoeff c T v` and `0 ≤ s ≤ T` there is `K ≥ 0` such that for every
`u` of class `C²` with `W2(u σ) cosh ≤ b σ` on `[s, T]`, the transport term `transp v u` is an `FReg`
integrand and `WB (K b r)` holds for it and for its plane derivatives.

Proof. Take `K = M + M1`, where `M` bounds `‖v‖` and `M1` bounds `‖Dv‖` (`CylCoeff`). The product rule
(`pd_transp_eq`) writes `∂_j (v·∇u)` as a sum of `(∂_j v)·∇u` and `v·∇(∂_j ∇u)`; each term is bounded
by `(M + M1) W2(u)`, which the hypothesis caps by `b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- Product rule for the transport term: `∂_j (v·∇u) = (∂_j v)·∇u + v·∇(∂_j u)`. -/
theorem pd_transp_eq (v : ℝ → Pl → UnforcedLeray.Train.Vec) (u : ℝ → Pl → ℝ) (r : ℝ)
    (hv : ContDiff ℝ 1 (v r)) (hu : ContDiff ℝ 2 (u r)) (j : Fin 2) (y : Pl) :
    B0579.pd j (transp v u r) y =
      fderiv ℝ (v r) y (B0579.dir j) 0 * B0579.pd 0 (u r) y +
      fderiv ℝ (v r) y (B0579.dir j) 1 * B0579.pd 1 (u r) y +
      v r y 0 * B0579.pd j (B0579.pd 0 (u r)) y +
      v r y 1 * B0579.pd j (B0579.pd 1 (u r)) y := by
  have hdv : DifferentiableAt ℝ (v r) y := hv.differentiable one_ne_zero y
  have hdu : ∀ k : Fin 2, DifferentiableAt ℝ (B0579.pd k (u r)) y := by
    intro k
    have h1 : ContDiff ℝ 1 (fderiv ℝ (u r)) := hu.fderiv_right (by norm_num)
    have h2 : ContDiff ℝ 1 (fun z => fderiv ℝ (u r) z (B0579.dir k)) :=
      h1.clm_apply contDiff_const
    exact (h2.differentiable one_ne_zero) y
  have hA0 := (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) (v r y) 0).comp y hdv.hasFDerivAt
  have hA1 := (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) (v r y) 1).comp y hdv.hasFDerivAt
  have H : HasFDerivAt (fun z => v r z 0 * B0579.pd 0 (u r) z + v r z 1 * B0579.pd 1 (u r) z) _ y :=
    (hA0.mul (hdu 0).hasFDerivAt).add (hA1.mul (hdu 1).hasFDerivAt)
  rw [show B0579.pd j (transp v u r) y =
      fderiv ℝ (fun z => v r z 0 * B0579.pd 0 (u r) z + v r z 1 * B0579.pd 1 (u r) z) y
        (B0579.dir j) from rfl, H.fderiv,
    show B0579.pd j (B0579.pd 0 (u r)) y = fderiv ℝ (B0579.pd 0 (u r)) y (B0579.dir j) from rfl,
    show B0579.pd j (B0579.pd 1 (u r)) y = fderiv ℝ (B0579.pd 1 (u r)) y (B0579.dir j) from rfl]
  simp [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Function.comp_apply]
  ring

/-- Bound for a four-term sum `A0 p0 + A1 p1 + v0 q0 + v1 q1`. -/
theorem abs_comb4 (A0 A1 v0 v1 p0 p1 q0 q1 W M M1 : ℝ) (hM : 0 ≤ M) (hM1 : 0 ≤ M1)
    (hA0 : |A0| ≤ M1) (hA1 : |A1| ≤ M1) (hv0 : |v0| ≤ M) (hv1 : |v1| ≤ M)
    (hp : |p0| + |p1| ≤ W) (hq : |q0| + |q1| ≤ W) :
    |A0 * p0 + A1 * p1 + v0 * q0 + v1 * q1| ≤ (M + M1) * W := by
  have e0 : |A0 * p0| ≤ M1 * |p0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hA0 (abs_nonneg _)
  have e1 : |A1 * p1| ≤ M1 * |p1| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hA1 (abs_nonneg _)
  have e2 : |v0 * q0| ≤ M * |q0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv0 (abs_nonneg _)
  have e3 : |v1 * q1| ≤ M * |q1| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv1 (abs_nonneg _)
  have f1 : M1 * |p0| + M1 * |p1| ≤ M1 * W := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hp hM1
  have f2 : M * |q0| + M * |q1| ≤ M * W := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hq hM
  have g1 := abs_add_le (A0 * p0 + A1 * p1 + v0 * q0) (v1 * q1)
  have g2 := abs_add_le (A0 * p0 + A1 * p1) (v0 * q0)
  have g3 := abs_add_le (A0 * p0) (A1 * p1)
  rw [add_mul]
  linarith

/-- Bound for a two-term sum `v0 p0 + v1 p1`. -/
theorem abs_comb2 (v0 v1 p0 p1 W M : ℝ) (hM : 0 ≤ M)
    (hv0 : |v0| ≤ M) (hv1 : |v1| ≤ M) (hp : |p0| + |p1| ≤ W) :
    |v0 * p0 + v1 * p1| ≤ M * W := by
  have e0 : |v0 * p0| ≤ M * |p0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv0 (abs_nonneg _)
  have e1 : |v1 * p1| ≤ M * |p1| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hv1 (abs_nonneg _)
  have f1 : M * |p0| + M * |p1| ≤ M * W := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hp hM
  have g1 := abs_add_le (v0 * p0) (v1 * p1)
  linarith

/-- **`T22/1/13`.** The transport term `v·∇u` is an `FReg` integrand in the weighted class. -/
theorem transpClass : UnforcedLeray.Short.IIb.CylPDE.TranspClass := by
  intro c s T v hC hs hsT
  have hT0 : 0 ≤ T := hs.trans hsT
  obtain ⟨M, hM⟩ := hC.bdd
  obtain ⟨M1, hM1⟩ := hC.dbdd
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hT0⟩ 0)
  have hM10 : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 0 ⟨le_rfl, hT0⟩ 0)
  refine ⟨M + M1, by linarith, ?_⟩
  intro u b hc2 hcont0 hcont1 hcont2 hbound
  have hIcc : Icc s T ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1, hr.2⟩
  have hv : ∀ r ∈ Icc s T, ContDiff ℝ 1 (v r) := fun r hr => hC.slice r (hIcc hr)
  have hvb : ∀ r ∈ Icc s T, ∀ y : Pl, ∀ k : Fin 2, |v r y k| ≤ M := by
    intro r hr y k
    calc |v r y k| = ‖v r y k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v r y‖ := PiLp.norm_apply_le _ k
      _ ≤ M := hM r (hIcc hr) y
  have hdvb : ∀ r ∈ Icc s T, ∀ y : Pl, ∀ j k : Fin 2,
      |fderiv ℝ (v r) y (B0579.dir j) k| ≤ M1 := by
    intro r hr y j k
    have h3 : ‖B0579.dir j‖ ≤ 1 := by
      fin_cases j <;> simp [B0579.dir, Prod.norm_def]
    have h4 : ‖fderiv ℝ (v r) y‖ ≤ M1 := hM1 r (hIcc hr) y
    calc |fderiv ℝ (v r) y (B0579.dir j) k|
        = ‖fderiv ℝ (v r) y (B0579.dir j) k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (v r) y (B0579.dir j)‖ := PiLp.norm_apply_le _ k
      _ ≤ ‖fderiv ℝ (v r) y‖ * ‖B0579.dir j‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M1 * 1 := mul_le_mul h4 h3 (norm_nonneg _) (le_trans (norm_nonneg _) h4)
      _ = M1 := mul_one _
  have hWa : ∀ g : Pl → ℝ, ∀ x : Pl, |B0579.pd 0 g x| + |B0579.pd 1 g x| ≤ W2 g x := by
    intro g x
    unfold W2
    linarith [abs_nonneg (g x), abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x),
      abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x), abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x),
      abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)]
  have hWb : ∀ g : Pl → ℝ, ∀ x : Pl, ∀ j : Fin 2,
      |B0579.pd j (B0579.pd 0 g) x| + |B0579.pd j (B0579.pd 1 g) x| ≤ W2 g x := by
    intro g x j
    unfold W2
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
    · linarith [abs_nonneg (g x), abs_nonneg (B0579.pd 0 g x), abs_nonneg (B0579.pd 1 g x),
        abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x),
        abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)]
    · linarith [abs_nonneg (g x), abs_nonneg (B0579.pd 0 g x), abs_nonneg (B0579.pd 1 g x),
        abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x),
        abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)]
  have hW0 : ∀ g : Pl → ℝ, ∀ x : Pl, 0 ≤ W2 g x := by
    intro g x
    unfold W2
    positivity
  have hTr : ∀ r ∈ Icc s T, ∀ y : Pl, |transp v u r y| ≤ (M + M1) * W2 (u r) y := by
    intro r hr y
    have h1 := abs_comb2 (v r y 0) (v r y 1) (B0579.pd 0 (u r) y) (B0579.pd 1 (u r) y)
      (W2 (u r) y) M hM0 (hvb r hr y 0) (hvb r hr y 1) (hWa (u r) y)
    have hW := hW0 (u r) y
    exact le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) hW)
  have hPd : ∀ r ∈ Icc s T, ∀ y : Pl, ∀ j : Fin 2,
      |B0579.pd j (transp v u r) y| ≤ (M + M1) * W2 (u r) y := by
    intro r hr y j
    rw [pd_transp_eq v u r (hv r hr) (hc2 r hr) j y]
    exact abs_comb4 _ _ _ _ _ _ _ _ _ _ _ hM0 hM10 (hdvb r hr y j 0) (hdvb r hr y j 1)
      (hvb r hr y 0) (hvb r hr y 1) (hWa (u r) y) (hWb (u r) y j)
  have hWBgen : ∀ (g : Pl → ℝ) (r : ℝ), r ∈ Icc s T →
      (∀ x : Pl, |g x| ≤ (M + M1) * W2 (u r) x) → WB ((M + M1) * b r) g := by
    intro g r hr hg x
    calc |g x| * Real.cosh x.2 ≤ ((M + M1) * W2 (u r) x) * Real.cosh x.2 :=
          mul_le_mul_of_nonneg_right (hg x) ((Real.cosh_pos _).le)
      _ = (M + M1) * (W2 (u r) x * Real.cosh x.2) := by ring
      _ ≤ (M + M1) * b r := mul_le_mul_of_nonneg_left (hbound r hr x) (by linarith)
  have hcv : ContinuousOn (fun z : ℝ × Pl => v z.1 z.2) (Icc s T ×ˢ univ) :=
    hC.cont.mono (Set.prod_mono hIcc (subset_refl _))
  have hcdv : ContinuousOn (fun z : ℝ × Pl => fderiv ℝ (v z.1) z.2) (Icc s T ×ˢ univ) :=
    hC.dcont.mono (Set.prod_mono hIcc (subset_refl _))
  have hcomp : ∀ k : Fin 2, ContinuousOn (fun z : ℝ × Pl => v z.1 z.2 k) (Icc s T ×ˢ univ) :=
    fun k => (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k).comp_continuousOn hcv
  have hcontT : ContinuousOn (fun z : ℝ × Pl => transp v u z.1 z.2) (Icc s T ×ˢ univ) :=
    ((hcomp 0).mul (hcont1 0)).add ((hcomp 1).mul (hcont1 1))
  have hpdC : ∀ r ∈ Icc s T, ∀ k : Fin 2, ContDiff ℝ 1 (B0579.pd k (u r)) := by
    intro r hr k
    have h1 : ContDiff ℝ 1 (fderiv ℝ (u r)) := (hc2 r hr).fderiv_right (by norm_num)
    exact h1.clm_apply contDiff_const
  have hcontdT : ∀ j : Fin 2,
      ContinuousOn (fun z : ℝ × Pl => B0579.pd j (transp v u z.1) z.2) (Icc s T ×ˢ univ) := by
    intro j
    have hD : ∀ k : Fin 2, ContinuousOn
        (fun z : ℝ × Pl => fderiv ℝ (v z.1) z.2 (B0579.dir j) k) (Icc s T ×ˢ univ) := fun k =>
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k).comp_continuousOn
        ((ContinuousLinearMap.apply ℝ _ (B0579.dir j)).continuous.comp_continuousOn hcdv)
    have hformula : ContinuousOn (fun z : ℝ × Pl =>
        fderiv ℝ (v z.1) z.2 (B0579.dir j) 0 * B0579.pd 0 (u z.1) z.2 +
        fderiv ℝ (v z.1) z.2 (B0579.dir j) 1 * B0579.pd 1 (u z.1) z.2 +
        v z.1 z.2 0 * B0579.pd j (B0579.pd 0 (u z.1)) z.2 +
        v z.1 z.2 1 * B0579.pd j (B0579.pd 1 (u z.1)) z.2) (Icc s T ×ˢ univ) :=
      ((((hD 0).mul (hcont1 0)).add ((hD 1).mul (hcont1 1))).add
        ((hcomp 0).mul (hcont2 j 0))).add ((hcomp 1).mul (hcont2 j 1))
    exact hformula.congr (fun z hz => pd_transp_eq v u z.1 (hv z.1 hz.1) (hc2 z.1 hz.1) j z.2)
  refine ⟨⟨hcontT, fun r hr => ?_, hcontdT⟩, ?_⟩
  · exact (((contDiff_piLp 2).1 (hv r hr) 0).mul (hpdC r hr 0)).add
      (((contDiff_piLp 2).1 (hv r hr) 1).mul (hpdC r hr 1))
  · intro r hr
    refine ⟨hWBgen (transp v u r) r hr (fun y => hTr r hr y), fun j => ?_⟩
    exact hWBgen (B0579.pd j (transp v u r)) r hr (fun y => hPd r hr y j)

end CylPDE

end UnforcedLeray.Short.IIb
