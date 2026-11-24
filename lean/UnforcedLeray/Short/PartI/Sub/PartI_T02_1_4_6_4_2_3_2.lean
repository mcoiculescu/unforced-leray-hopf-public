import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/3/2` (`LeafParamIntCH`), decomposition

Source of record: `the November 2 reference manuscript` (centered heat semigroup,
age derivative of the shift pairing; the shift pairing of a smooth periodic `η`-compactly
supported test against an `L²(cell)` field is a smooth bounded function of the shift, with the
planar Laplacian falling on the test).

Note: `G ∈ L²(cell)` does not give `G ∈ L¹(cell)` (the cell `[-c/2, c/2) × ℝ` has infinite
measure); the domination in the leaf `LeafParamIntHasFDerivCH` must be local in the shift,
using the `η`-support of the test (for `‖x - x₀‖ ≤ 1` the integrand lives in the strip
`|η - x₀.2| ≤ R + 1`, where `G` is `L¹` by Cauchy-Schwarz).

`leafParamIntCH_of` proves `LeafParamIntCH` from five leaves.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The parameter integral `v ↦ ∫_cell ⟪ψ(z - v), G z⟫ dz`. -/
def paramIntCH (c : ℝ) (ψ : Plane → Vec) (G : Cyl.L2v c) : Plane → ℝ :=
  fun v => ∫ z in Cyl.cell c, inner ℝ (ψ (z - v)) (((G : Cyl.L2v c) : Plane → Vec) z)

/-- **Leaf (partials of a test)**: the classical partials `∂_q ψ`, `∂_η ψ` of a cell test are cell
tests (smooth, periodic, `η`-compactly supported). -/
def LeafCellTestPartialCH : Prop :=
  ∀ (c : ℝ) (ψ : Plane → Vec), IsCellTest c ψ →
    IsCellTest c (Cyl.partialQ ψ) ∧ IsCellTest c (Cyl.partialEta ψ)

/-- **Leaf (integrability)**: for a cell test `ψ` and `G ∈ L²(cell)`, the integrand
`z ↦ ⟪ψ(z - x), G z⟫` is integrable on the cell (Cauchy-Schwarz: both factors are `L²`; `ψ(· - x)`
is a cell test, hence in `L²(cell)` by `Cyl.memLp_of_vanishes`). -/
def LeafParamIntIntegrableCH : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (ψ : Plane → Vec) (G : Cyl.L2v c), IsCellTest c ψ → ∀ x : Plane,
    Integrable (fun z : Plane => inner ℝ (ψ (z - x)) (((G : Cyl.L2v c) : Plane → Vec) z))
      (Cyl.cellμ c)

/-- **Leaf (uniform bound)**: the parameter integral is bounded in the shift (it equals the shift
pairing `⟪τ_x ψL, G⟫`, of norm `≤ ‖ψL‖ ‖G‖` since the planar shift is an isometry of `L²(cell)`;
library `leafShiftRepCH_proof`, `HeatCylinder.planeShiftL2CLM`). -/
def LeafParamIntBoundedCH : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (ψ : Plane → Vec) (G : Cyl.L2v c), IsCellTest c ψ →
    ∃ M : ℝ, ∀ x, ‖paramIntCH c ψ G x‖ ≤ M

/-- **Leaf (differentiation under the integral)**: the parameter integral is Fréchet
differentiable with derivative `d ↦ -d.1 ∫⟪∂_qψ(z - x), G⟫ - d.2 ∫⟪∂_ηψ(z - x), G⟫`.  Proof:
`hasFDerivAt_integral_of_dominated_of_fderiv_le` (ParametricIntegral.lean:210) on the ball of
radius `1` about `x`, with local dominating function
`M₁ · ‖G z‖ · 1_{|z.2 - x.2| ≤ R + 1}` (`M₁` bounds `‖fderiv ψ‖`, which is bounded because it
is periodic and `η`-compactly supported), integrable on the cell by Cauchy-Schwarz. -/
def LeafParamIntHasFDerivCH : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (ψ : Plane → Vec) (G : Cyl.L2v c), IsCellTest c ψ → ∀ x : Plane,
    HasFDerivAt (paramIntCH c ψ G)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (-(paramIntCH c (Cyl.partialQ ψ) G x)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-(paramIntCH c (Cyl.partialEta ψ) G x))) x

/-- **Leaf (Laplacian as partials)**: for a cell test, the vector Laplacian is
`∂_q ∂_q ψ + ∂_η ∂_η ψ` (componentwise partials of a smooth map; `Train.lapS`, `Train.vecLaplacian`
in `Lib/Train/Ops.lean`). -/
def LeafVecLaplacianPartialsCH : Prop :=
  ∀ (c : ℝ) (ψ : Plane → Vec), IsCellTest c ψ →
    Train.vecLaplacian ψ = fun z => Cyl.partialQ (Cyl.partialQ ψ) z + Cyl.partialEta (Cyl.partialEta ψ) z


section Proof

variable {c : ℝ} {ψ : Plane → Vec} {G : Cyl.L2v c}

/-- The derivative continuous linear map of `paramIntCH`, from its two partial parameter integrals. -/
def dParam (a b : ℝ) : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (-a) + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (-b)

theorem dParam_apply (a b : ℝ) (d : Plane) : dParam a b d = -(d.1 * a) - d.2 * b := by
  simp [dParam]; ring

theorem norm_dParam_le (a b : ℝ) : ‖dParam a b‖ ≤ |a| + |b| := by
  unfold dParam
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [ContinuousLinearMap.norm_smulRight_apply, norm_neg, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg a) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  · rw [ContinuousLinearMap.norm_smulRight_apply, norm_neg, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg b) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)


theorem leafParamIntCH_of (h1 : LeafCellTestPartialCH) (h2 : LeafParamIntIntegrableCH)
    (h3 : LeafParamIntBoundedCH) (h4 : LeafParamIntHasFDerivCH)
    (h5 : LeafVecLaplacianPartialsCH) : LeafParamIntCH := by
  intro c hc ψ G hψ
  -- derivative formula
  have hD : ∀ φ : Plane → Vec, IsCellTest c φ → ∀ x,
      fderiv ℝ (paramIntCH c φ G) x =
        dParam (paramIntCH c (Cyl.partialQ φ) G x) (paramIntCH c (Cyl.partialEta φ) G x) :=
    fun φ hφ x => (h4 c hc φ G hφ x).fderiv
  -- smoothness of finite order
  have hcd : ∀ n : ℕ, ∀ φ : Plane → Vec, IsCellTest c φ → ContDiff ℝ n (paramIntCH c φ G) := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      have hc0 : Continuous (paramIntCH c φ G) :=
        continuous_iff_continuousAt.2 (fun x => (h4 c hc φ G hφ x).differentiableAt.continuousAt)
      simpa using (contDiff_zero (𝕜 := ℝ)).2 hc0
    | succ n ih =>
      intro φ hφ
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun x => dParam (paramIntCH c (Cyl.partialQ φ) G x)
        (paramIntCH c (Cyl.partialEta φ) G x), ?_, fun x => h4 c hc φ G hφ x⟩
      have ha := ih _ (h1 c φ hφ).1
      have hb := ih _ (h1 c φ hφ).2
      have e : (fun x => dParam (paramIntCH c (Cyl.partialQ φ) G x)
          (paramIntCH c (Cyl.partialEta φ) G x)) = fun x =>
          (ContinuousLinearMap.smulRightL ℝ Plane ℝ (-(ContinuousLinearMap.fst ℝ ℝ ℝ))
            (paramIntCH c (Cyl.partialQ φ) G x)) +
          (ContinuousLinearMap.smulRightL ℝ Plane ℝ (-(ContinuousLinearMap.snd ℝ ℝ ℝ))
            (paramIntCH c (Cyl.partialEta φ) G x)) := by
        funext x
        refine ContinuousLinearMap.ext fun d => ?_
        simp [dParam]
      rw [e]
      exact ((ContinuousLinearMap.smulRightL ℝ Plane ℝ
          (-(ContinuousLinearMap.fst ℝ ℝ ℝ))).contDiff.comp ha).add
        ((ContinuousLinearMap.smulRightL ℝ Plane ℝ
          (-(ContinuousLinearMap.snd ℝ ℝ ℝ))).contDiff.comp hb)
  -- bound on the first derivative, for every cell test
  have hB1 : ∀ φ : Plane → Vec, IsCellTest c φ → ∃ M : ℝ, ∀ x, ‖fderiv ℝ (paramIntCH c φ G) x‖ ≤ M := by
    intro φ hφ
    obtain ⟨M1, hM1⟩ := h3 c hc _ G (h1 c φ hφ).1
    obtain ⟨M2, hM2⟩ := h3 c hc _ G (h1 c φ hφ).2
    refine ⟨M1 + M2, fun x => ?_⟩
    rw [hD φ hφ x]
    refine (norm_dParam_le _ _).trans (add_le_add ?_ ?_)
    · simpa using hM1 x
    · simpa using hM2 x
  -- the first partials of the parameter integral
  have hfst : ∀ φ : Plane → Vec, IsCellTest c φ → ∀ y,
      fderiv ℝ (paramIntCH c φ G) y (1, 0) = -(paramIntCH c (Cyl.partialQ φ) G y) := by
    intro φ hφ y
    rw [hD φ hφ y, dParam_apply]; simp
  have hsnd : ∀ φ : Plane → Vec, IsCellTest c φ → ∀ y,
      fderiv ℝ (paramIntCH c φ G) y (0, 1) = -(paramIntCH c (Cyl.partialEta φ) G y) := by
    intro φ hφ y
    rw [hD φ hφ y, dParam_apply]; simp

  -- partial derivatives of the parameter integral
  have hpq : ∀ φ : Plane → Vec, IsCellTest c φ → ∀ z : Plane,
      Cyl.partialQ (paramIntCH c φ G) z = -(paramIntCH c (Cyl.partialQ φ) G z) := by
    intro φ hφ z
    have h := (h4 c hc φ G hφ z).comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    have h' : HasDerivAt (fun q : ℝ => paramIntCH c φ G (q, z.2))
        (-(paramIntCH c (Cyl.partialQ φ) G z)) z.1 := by
      refine h.congr_deriv ?_
      simp
    exact h'.deriv
  have hpe : ∀ φ : Plane → Vec, IsCellTest c φ → ∀ z : Plane,
      Cyl.partialEta (paramIntCH c φ G) z = -(paramIntCH c (Cyl.partialEta φ) G z) := by
    intro φ hφ z
    have h := (h4 c hc φ G hφ z).comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
    have h' : HasDerivAt (fun q : ℝ => paramIntCH c φ G (z.1, q))
        (-(paramIntCH c (Cyl.partialEta φ) G z)) z.2 := by
      refine h.congr_deriv ?_
      simp
    exact h'.deriv
  have hnegQ : ∀ (f : Plane → ℝ) (z : Plane),
      Cyl.partialQ (fun y => -(f y)) z = -(Cyl.partialQ f z) := by
    intro f z; simp [Cyl.partialQ]
  have hnegE : ∀ (f : Plane → ℝ) (z : Plane),
      Cyl.partialEta (fun y => -(f y)) z = -(Cyl.partialEta f z) := by
    intro f z; simp [Cyl.partialEta]
  have hqq : ∀ z, Cyl.partialQ (Cyl.partialQ (paramIntCH c ψ G)) z =
      paramIntCH c (Cyl.partialQ (Cyl.partialQ ψ)) G z := by
    intro z
    have e : Cyl.partialQ (paramIntCH c ψ G) = fun y => -(paramIntCH c (Cyl.partialQ ψ) G y) :=
      funext (hpq ψ hψ)
    rw [e, hnegQ, hpq _ (h1 c ψ hψ).1, neg_neg]
  have hee : ∀ z, Cyl.partialEta (Cyl.partialEta (paramIntCH c ψ G)) z =
      paramIntCH c (Cyl.partialEta (Cyl.partialEta ψ)) G z := by
    intro z
    have e : Cyl.partialEta (paramIntCH c ψ G) =
        fun y => -(paramIntCH c (Cyl.partialEta ψ) G y) := funext (hpe ψ hψ)
    rw [e, hnegE, hpe _ (h1 c ψ hψ).2, neg_neg]
  refine ⟨contDiff_infty.2 (fun n => hcd n ψ hψ), h3 c hc ψ G hψ, hB1 ψ hψ, ?_, ?_, ?_⟩
  · have e : (fun y => fderiv ℝ (paramIntCH c ψ G) y (1, 0)) =
        fun y => -(paramIntCH c (Cyl.partialQ ψ) G y) := funext (hfst ψ hψ)
    show ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (paramIntCH c ψ G) y (1, 0)) x‖ ≤ M
    rw [e]
    obtain ⟨M, hM⟩ := hB1 _ (h1 c ψ hψ).1
    refine ⟨M, fun x => ?_⟩
    rw [fderiv_fun_neg, norm_neg]; exact hM x
  · have e : (fun y => fderiv ℝ (paramIntCH c ψ G) y (0, 1)) =
        fun y => -(paramIntCH c (Cyl.partialEta ψ) G y) := funext (hsnd ψ hψ)
    show ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (paramIntCH c ψ G) y (0, 1)) x‖ ≤ M
    rw [e]
    obtain ⟨M, hM⟩ := hB1 _ (h1 c ψ hψ).2
    refine ⟨M, fun x => ?_⟩
    rw [fderiv_fun_neg, norm_neg]; exact hM x
  · intro w
    show Train.lapS (paramIntCH c ψ G) w = _
    have hq := (h1 c ψ hψ).1
    have he := (h1 c ψ hψ).2
    have i1 := h1 c _ hq
    have i2 := h1 c _ he
    unfold Train.lapS
    rw [hqq, hee]
    unfold paramIntCH
    rw [h5 c ψ hψ]
    simp only [inner_add_left]
    exact (integral_add (h2 c hc _ G i1.1 w) (h2 c hc _ G i2.2 w)).symm

end Proof

end UnforcedLeray.Short.PartI
