import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1/2`: decomposition of `HeatGaussSplit`

Source `the November 2 reference manuscript`, lines 261-288 (Gaussian average of
the second-order Taylor expansion: moments `1, 0, 2hδ_ij`).  Leaves:
* `HGMoments`: the six Gaussian moments of the planar heat kernel and their integrability;
* `HGIterExpand`: coordinate expansion of `iterD [w] f` and `iterD [w, w] f`.

`heatGaussSplit_of` assembles `HeatGaussSplit` (boundedness of `f`, integrability, linearity of
the integral are proved here).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Leaf (Gaussian moments; lines 261-288).** For `h > 0` and `K = heatKernel2 h`, the functions
`K, K w₁, K w₂, K w₁², K w₂², K w₁ w₂` are integrable with integrals `1, 0, 0, 2h, 2h, 0`.
Route: `K(w) = G_h(w₁) G_h(w₂)` (`B0284.heatKernel2`, `B0191.heatKernel 1 h`), `integral_prod_mul`,
one-dimensional moments from `integral_rpow_mul_exp_neg_mul_rpow` (cf. `HeatGaussCubeAux` in
`Tasks/.../GeneratorZero/Taylor/GaussCube.lean`), odd moments vanish by `integral_comp_neg`. -/
def HGMoments : Prop :=
  ∀ h : ℝ, 0 < h →
    Integrable (fun w : Plane => B0284.heatKernel2 h w) ∧
    Integrable (fun w : Plane => B0284.heatKernel2 h w * w.1) ∧
    Integrable (fun w : Plane => B0284.heatKernel2 h w * w.2) ∧
    Integrable (fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.1)) ∧
    Integrable (fun w : Plane => B0284.heatKernel2 h w * (w.2 * w.2)) ∧
    Integrable (fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.2)) ∧
    (∫ w : Plane, B0284.heatKernel2 h w = 1) ∧
    (∫ w : Plane, B0284.heatKernel2 h w * w.1 = 0) ∧
    (∫ w : Plane, B0284.heatKernel2 h w * w.2 = 0) ∧
    (∫ w : Plane, B0284.heatKernel2 h w * (w.1 * w.1) = 2 * h) ∧
    (∫ w : Plane, B0284.heatKernel2 h w * (w.2 * w.2) = 2 * h) ∧
    (∫ w : Plane, B0284.heatKernel2 h w * (w.1 * w.2) = 0)

/-- **Leaf (coordinate expansion of `iterD`; lines 261-288).** For cylinder-smooth `f`,
`∂_w f = w₁ ∂₁ f + w₂ ∂₂ f` and `∂_w² f = w₁² ∂₁∂₁ f + w₁w₂ (∂₁∂₂ f + ∂₂∂₁ f) + w₂² ∂₂∂₂ f`
(linearity of `fderiv f y` in `w`, then differentiate again; `Sob.iterD_cons`, `fderiv` of
`fun y => a • g y + b • k y`; no symmetry of second derivatives needed). -/
def HGIterExpand : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (f : Plane → Cyl.Vec2) (_hf : Sob.IsCylSmooth c f) (x w : Plane),
    Sob.iterD [w] f x
        = w.1 • Sob.iterD [((1:ℝ), (0:ℝ))] f x + w.2 • Sob.iterD [((0:ℝ), (1:ℝ))] f x ∧
    Sob.iterD [w, w] f x
        = (w.1 * w.1) • Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f x
          + (w.1 * w.2) • (Sob.iterD [((1:ℝ), (0:ℝ)), ((0:ℝ), (1:ℝ))] f x
              + Sob.iterD [((0:ℝ), (1:ℝ)), ((1:ℝ), (0:ℝ))] f x)
          + (w.2 * w.2) • Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f x

namespace HGSplitAux

theorem bdd_of_periodic_support {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c R : ℝ} (hc : 0 < c) {u : Plane → G} (hcont : Continuous u)
    (hper : ∀ z : Plane, u (z + (c, 0)) = u z)
    (hR : ∀ z : Plane, R < |z.2| → u z = 0) :
    ∃ M : ℝ, ∀ z : Plane, ‖u z‖ ≤ M := by
  have hK : IsCompact (Icc (0:ℝ) c ×ˢ Icc (-(max R 0)) (max R 0)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hη : max R 0 < |z.2|
  · have hz : u z = 0 := hR z (lt_of_le_of_lt (le_max_left _ _) hη)
    rw [hz, norm_zero]
    exact le_max_right _ _
  · have hη' : z.2 ∈ Icc (-(max R 0)) (max R 0) := abs_le.mp (not_lt.mp hη)
    have hq : Function.Periodic (fun q : ℝ => u (q, z.2)) c := fun q => by
      simpa [Prod.mk_add_mk] using hper (q, z.2)
    obtain ⟨y, hy, hyeq⟩ := hq.exists_mem_Ico₀ hc z.1
    have hyK : ((y, z.2) : Plane) ∈ Icc (0:ℝ) c ×ˢ Icc (-(max R 0)) (max R 0) :=
      ⟨⟨hy.1, hy.2.le⟩, hη'⟩
    have h1 : ‖u z‖ ≤ C := by
      have e : u z = u (y, z.2) := hyeq
      rw [e]
      exact hC _ hyK
    exact le_trans h1 (le_max_left _ _)

theorem cylSmooth_bdd {c : ℝ} (hc : 0 < c) {f : Plane → Cyl.Vec2} (hf : Sob.IsCylSmooth c f) :
    ∃ M : ℝ, ∀ z : Plane, ‖f z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hf.bounded
  exact bdd_of_periodic_support hc hf.smooth.continuous hf.periodic hR

theorem continuous_heatKernel2 (h : ℝ) : Continuous (fun w : Plane => B0284.heatKernel2 h w) := by
  unfold B0284.heatKernel2 B0191.heatKernel
  fun_prop

theorem integral_comb7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F0 F1 F2 F3 F4 F5 F6 : Plane → E)
    (h0 : Integrable F0) (h1 : Integrable F1) (h2 : Integrable F2) (h3 : Integrable F3)
    (h4 : Integrable F4) (h5 : Integrable F5) (h6 : Integrable F6) :
    ∫ w, (F0 w - F1 w + F2 w + F3 w - F4 w - F5 w - F6 w)
      = (∫ w, F0 w) - (∫ w, F1 w) + (∫ w, F2 w) + (∫ w, F3 w) - (∫ w, F4 w) - (∫ w, F5 w)
        - (∫ w, F6 w) := by
  have a1 : Integrable (fun w => F0 w - F1 w) := h0.sub h1
  have a2 : Integrable (fun w => F0 w - F1 w + F2 w) := a1.add h2
  have a3 : Integrable (fun w => F0 w - F1 w + F2 w + F3 w) := a2.add h3
  have a4 : Integrable (fun w => F0 w - F1 w + F2 w + F3 w - F4 w) := a3.sub h4
  have a5 : Integrable (fun w => F0 w - F1 w + F2 w + F3 w - F4 w - F5 w) := a4.sub h5
  rw [integral_sub a5 h6, integral_sub a4 h5, integral_sub a3 h4, integral_add a2 h3,
    integral_add a1 h2, integral_sub h0 h1]

end HGSplitAux

open HGSplitAux in
theorem heatGaussSplit_of (hM : HGMoments) (hE : HGIterExpand) : HeatGaussSplit := by
  intro c hc f hf h hh x
  obtain ⟨i0, i1, i2, i11, i22, i12, m0, m1, m2, m11, m22, m12⟩ := hM h hh
  obtain ⟨M, hMb⟩ := cylSmooth_bdd hc hf
  set K : Plane → ℝ := fun w => B0284.heatKernel2 h w with hKdef
  have hKc : Continuous K := continuous_heatKernel2 h
  have hK0 : ∀ w, 0 ≤ K w := fun w => B0284.heatKernel2_nonneg hh w
  have hfc : Continuous (fun w : Plane => f (x - w)) := hf.smooth.continuous.comp (by fun_prop)
  have iF : Integrable (fun w : Plane => K w • f (x - w)) := by
    refine Integrable.mono' (i0.mul_const M) ?_ (ae_of_all _ fun w => ?_)
    · exact (hKc.smul hfc).aestronglyMeasurable
    · rw [norm_smul, Real.norm_of_nonneg (hK0 w)]
      exact mul_le_mul_of_nonneg_left (hMb _) (hK0 w)
  set a := Sob.iterD [((1:ℝ), (0:ℝ))] f x
  set b := Sob.iterD [((0:ℝ), (1:ℝ))] f x
  set A11 := Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f x
  set A12 := Sob.iterD [((1:ℝ), (0:ℝ)), ((0:ℝ), (1:ℝ))] f x
  set A21 := Sob.iterD [((0:ℝ), (1:ℝ)), ((1:ℝ), (0:ℝ))] f x
  set A22 := Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f x
  have hpt : ∀ w : Plane, B0284.heatKernel2 h w • heatTaylorR f x w
      = K w • f (x - w) - K w • f x + (K w * w.1) • a + (K w * w.2) • b
        - (K w * (w.1 * w.1)) • ((1 / 2 : ℝ) • A11)
        - (K w * (w.1 * w.2)) • ((1 / 2 : ℝ) • (A12 + A21))
        - (K w * (w.2 * w.2)) • ((1 / 2 : ℝ) • A22) := by
    intro w
    obtain ⟨e1, e2⟩ := hE c hc f hf x w
    unfold heatTaylorR
    rw [e1, e2]
    simp only [hKdef, smul_add, smul_sub, smul_smul, mul_comm, mul_left_comm]
    module
  have iC : Integrable (fun w : Plane => K w • f x) := i0.smul_const _
  have i1' := i1.smul_const a
  have i2' := i2.smul_const b
  have i11' := i11.smul_const ((1 / 2 : ℝ) • A11)
  have i12' := i12.smul_const ((1 / 2 : ℝ) • (A12 + A21))
  have i22' := i22.smul_const ((1 / 2 : ℝ) • A22)
  have hI : Integrable (fun w : Plane => B0284.heatKernel2 h w • heatTaylorR f x w) := by
    have : (fun w : Plane => B0284.heatKernel2 h w • heatTaylorR f x w)
        = fun w => K w • f (x - w) - K w • f x + (K w * w.1) • a + (K w * w.2) • b
        - (K w * (w.1 * w.1)) • ((1 / 2 : ℝ) • A11)
        - (K w * (w.1 * w.2)) • ((1 / 2 : ℝ) • (A12 + A21))
        - (K w * (w.2 * w.2)) • ((1 / 2 : ℝ) • A22) := funext hpt
    rw [this]
    exact ((((((iF.sub iC).add i1').add i2').sub i11').sub i12').sub i22')
  refine ⟨hI, ?_⟩
  have hint : ∫ w : Plane, B0284.heatKernel2 h w • heatTaylorR f x w
      = HeatCylinder.heatVecConvolution h f x - f x
        - (1 / 2 : ℝ) • ((2 * h) • A11) - (1 / 2 : ℝ) • ((2 * h) • A22) := by
    rw [show (fun w : Plane => B0284.heatKernel2 h w • heatTaylorR f x w)
        = fun w => K w • f (x - w) - K w • f x + (K w * w.1) • a + (K w * w.2) • b
        - (K w * (w.1 * w.1)) • ((1 / 2 : ℝ) • A11)
        - (K w * (w.1 * w.2)) • ((1 / 2 : ℝ) • (A12 + A21))
        - (K w * (w.2 * w.2)) • ((1 / 2 : ℝ) • A22) from funext hpt]
    rw [integral_comb7 _ _ _ _ _ _ _ iF iC i1' i2' i11' i12' i22']
    rw [integral_smul_const, integral_smul_const, integral_smul_const, integral_smul_const,
      integral_smul_const, integral_smul_const]
    have hconv : HeatCylinder.heatVecConvolution h f x = ∫ w : Plane, K w • f (x - w) := rfl
    rw [hconv, m1, m2, m11, m12, m22, m0]
    simp only [zero_smul, add_zero, one_smul]
    module
  rw [hint]
  module

end UnforcedLeray.Short.PartI
