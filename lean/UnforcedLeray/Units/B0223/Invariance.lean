import UnforcedLeray.Units.B0223.Resolvent

/-!
# B0223 helper: the outer semigroup preserves axisymmetric scalar fields

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3341–3366 ("these are the
conjugates of `νε²Δ_x + x·∇/2 + 1/2 - ∂_τ`", "conjugated to `H` by `J_ε`").

We prove the named hypothesis `LiftInvariant` of `B0223/Resolvent.lean` for the scalar lift:
`S_ε(t)` maps every lift `J_ε b` to a lift `J_ε b'`. Route:

* `AxInv u`: `u(x, τ)` depends on `x` only through `(r, z)` (pointwise, everywhere).
* The lift representative `a b(s, q, η)` is `AxInv` (the chart depends on `x` only through
  `r` and `z`), and `AxInv` is preserved by the phase shift, by the dilation and by the
  Gaussian average (`heatConv_axInv`): for each `x` the reflection `rotTo x` (an isometry of
  `ℝ³` fixing `e₃`, preserving `r` and `z`, with `rotTo x (r, 0, z) = x`, Mathlib's
  `reflection_sub`) and the rotation invariance of the Gaussian (`gaussKernel_isometry`).
* An `L²` field equal a.e. to a measurable `B(r, z, τ)` is a lift (`exists_liftSc_eq`, the
  complex periodic analogue of B0220 `range_J`, with B0220's inverse chart `invChart`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace
open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.B0223

open UnforcedLeray.B0220 UnforcedLeray.Infra

/-! ### Meridional geometry of `ℝ³` -/

/-- The point `(r, 0, w)` of the meridional half-plane. -/
def axisVec (r w : ℝ) : Space := r • EuclideanSpace.single 0 1 + w • EuclideanSpace.single 2 1

theorem axisVec_apply (r w : ℝ) :
    axisVec r w 0 = r ∧ axisVec r w 1 = 0 ∧ axisVec r w 2 = w := by
  simp [axisVec]

theorem continuous_axisVec : Continuous fun p : ℝ × ℝ => axisVec p.1 p.2 :=
  (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem radius_axisVec {r : ℝ} (hr : 0 ≤ r) (w : ℝ) : radius (axisVec r w) = r := by
  obtain ⟨h0, h1, -⟩ := axisVec_apply r w
  rw [radius, h0, h1]
  simp [Real.sqrt_sq hr]

/-- `‖y‖² = r² + z²`. -/
theorem norm_sq_eq_radius (y : Space) : ‖y‖ ^ 2 = radius y ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, radius, Real.sq_sqrt (by positivity)]

/-- `(r, 0, z)` for `x = (r cos φ, r sin φ, z)`. -/
def axisPt (x : Space) : Space := axisVec (radius x) (x 2)

theorem radius_axisPt (x : Space) : radius (axisPt x) = radius x :=
  radius_axisVec (Real.sqrt_nonneg _) _

theorem axisPt_two (x : Space) : axisPt x 2 = x 2 := (axisVec_apply _ _).2.2

theorem norm_axisPt (x : Space) : ‖axisPt x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_radius, norm_sq_eq_radius,
    radius_axisPt, axisPt_two]

/-- An isometry of `ℝ³` taking `(r, 0, z)` to `x` and preserving `r` and `z`: the reflection in
the plane orthogonal to `(r, 0, z) - x`. -/
def rotTo (x : Space) : Space ≃ₗᵢ[ℝ] Space := Submodule.reflection (ℝ ∙ (axisPt x - x))ᗮ

theorem rotTo_axisPt (x : Space) : rotTo x (axisPt x) = x :=
  Submodule.reflection_sub (norm_axisPt x)

theorem rotTo_e3 (x : Space) :
    rotTo x (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1 := by
  refine Submodule.reflection_mem_subspace_eq_self ?_
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_single_right]
  simp [axisPt_two]

theorem coord2_eq_inner (y : Space) : y 2 = ⟪EuclideanSpace.single 2 (1 : ℝ), y⟫ := by
  rw [EuclideanSpace.inner_single_left]
  simp

theorem rotTo_two (x y : Space) : rotTo x y 2 = y 2 := by
  rw [coord2_eq_inner, coord2_eq_inner y]
  conv_lhs => rw [← rotTo_e3 x]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem radius_rotTo (x y : Space) : radius (rotTo x y) = radius y := by
  have h1 := norm_sq_eq_radius (rotTo x y)
  have h2 := norm_sq_eq_radius y
  rw [LinearIsometryEquiv.norm_map, rotTo_two] at h1
  have h : radius (rotTo x y) ^ 2 = radius y ^ 2 := by linarith
  exact (pow_left_inj₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).1 h

theorem radius_smul (a : ℝ) (y : Space) : radius (a • y) = |a| * radius y := by
  simp only [radius, PiLp.smul_apply, smul_eq_mul]
  rw [show (a * y 0) ^ 2 + (a * y 1) ^ 2 = a ^ 2 * (y 0 ^ 2 + y 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-! ### Fields depending on `x` only through `(r, z)` -/

variable {P : ℝ} [Fact (0 < P)]

/-- `u(x, τ)` depends on `x` only through `r` and `z` (everywhere). -/
def AxInv {F : Type*} (u : PSpace P → F) : Prop :=
  ∀ y y' : Space, radius y = radius y' → y 2 = y' 2 → ∀ θ : AddCircle P, u (y, θ) = u (y', θ)

theorem AxInv.eq_axisPt {F : Type*} {u : PSpace P → F} (hu : AxInv u) (x : Space)
    (θ : AddCircle P) : u (x, θ) = u (axisPt x, θ) :=
  hu _ _ (radius_axisPt x).symm (axisPt_two x).symm θ

theorem AxInv.shift {F : Type*} {u : PSpace P → F} (hu : AxInv u) (t : ℝ) :
    AxInv fun w : PSpace P => u (w.1, w.2 - (t : AddCircle P)) :=
  fun y y' hr hz θ => hu y y' hr hz _

theorem AxInv.dil {F : Type*} [AddCommGroup F] [Module ℝ F] {u : PSpace P → F} (hu : AxInv u)
    (k a : ℝ) : AxInv fun z : PSpace P => k • u (a • z.1, z.2) := by
  intro y y' hr hz θ
  have h2 : (a • y) 2 = (a • y') 2 := by simp [hz]
  simp only
  rw [hu (a • y) (a • y') (by rw [radius_smul, radius_smul, hr]) h2 θ]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **The Gaussian average preserves `AxInv`** (rotation invariance of the heat kernel). -/
theorem heatConv_axInv {u : PSpace P → E} (hu : AxInv u) (θ : ℝ) :
    AxInv (Heat.heatConv (ιx P) θ u) := by
  have key : ∀ (x : Space) (φ : AddCircle P),
      Heat.heatConv (ιx P) θ u (x, φ) = Heat.heatConv (ιx P) θ u (axisPt x, φ) := by
    intro x φ
    set g := rotTo x
    have hmp := g.measurePreserving
    have hemb := g.toHomeomorph.measurableEmbedding
    conv_lhs => rw [← rotTo_axisPt x]
    simp only [Heat.heatConv, ιx_apply, Prod.mk_sub_mk, sub_zero]
    rw [← hmp.integral_comp hemb]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [show (g w : Euc 3) = g w from rfl, Gaussian.gaussKernel_isometry g θ w, ← map_sub]
    exact congrArg _ (hu _ _ (radius_rotTo x _) (rotTo_two x _) φ)
  intro y y' hr hz φ
  rw [key y, key y']
  simp only [axisPt, hr, hz]

theorem measurable_heatConv {u : PSpace P → E} (hu : Measurable u) (θ : ℝ) :
    Measurable (Heat.heatConv (ιx P) θ u) := by
  have h : StronglyMeasurable (Function.uncurry fun (z : PSpace P) (y : Euc 3) =>
      gaussKernel 3 θ y • u (z - ιx P y)) :=
    (((Gaussian.continuous_gaussKernel θ).measurable.comp measurable_snd).smul
      (hu.comp (measurable_fst.sub (continuous_ιx.measurable.comp measurable_snd)))).stronglyMeasurable
  exact h.integral_prod_right.measurable

/-! ### Fields of `(r, z, τ)` are lifts -/

variable {ε c : ℝ}

theorem ae_offAxis (hP : P = 2 * ε * c) :
    ∀ᵐ z ∂(volume : Measure (PSpace P)),
      radius (toCell P z).1 ≠ 0 ∧ (toCell P z).2 ∈ Ioc 0 (2 * ε * c) := by
  have h := ae_physMeasure ε c
  rw [physMeasure_eq hP] at h
  exact (mp_toCell (P := P)).quasiMeasurePreserving.ae h

/-- **An `L²` field equal a.e. to a measurable `B(r, z, τ)` is a lift** `J_ε b` (the complex
periodic analogue of B0220 `range_J`). -/
theorem exists_liftSc_eq (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {B : ℝ × ℝ × ℝ → E} (hB : Measurable B) {F : X E P}
    (hF : (F : PSpace P → E) =ᵐ[volume] fun z => B (radius z.1, z.1 2, (toCell P z).2)) :
    ∃ b : HSpace c E, liftSc hε hc hP b = F := by
  set W := liftScWC (E := E) hε hc hP with hW
  set b₀ : Profile → E := fun p =>
    (√(2 * Real.pi) * ε * invR p) • B (invR p, invZ ε p, invTau ε c p) with hb₀
  have hb₀m : Measurable b₀ :=
    (measurable_invR.const_mul _).smul
      (hB.comp (measurable_invR.prodMk ((measurable_invZ ε).prodMk (measurable_invTau ε c))))
  have hpt : W.compFun b₀ =ᵐ[volume] fun z => B (radius z.1, z.1 2, (toCell P z).2) := by
    filter_upwards [ae_offAxis hP] with z ⟨hr, hτ⟩
    obtain ⟨h1, h2, h3⟩ := invChart hε hc hr hτ
    have hk : √(2 * Real.pi) * ε * radius (toCell P z).1 * (jConst ε * liftA z.1) = 1 := by
      have hr' : radius z.1 ≠ 0 := hr
      have : √(2 * Real.pi) ≠ 0 := by positivity
      change √(2 * Real.pi) * ε * radius z.1 * (jConst ε * liftA z.1) = 1
      simp only [jConst, liftA]
      field_simp
    simp only [WeightedComp.compFun, hW, liftScWC, LinearMap.smul_apply, LinearMap.id_apply, hb₀]
    rw [h1, h2, h3, smul_smul, mul_comm, hk, one_smul]
    rfl
  have hb₀L : MemLp b₀ 2 (measureH c) :=
    ⟨hb₀m.aestronglyMeasurable, by
      rw [← W.eLpNorm_compFun hb₀m, eLpNorm_congr_ae (hpt.trans hF.symm)]
      exact Lp.eLpNorm_lt_top F⟩
  refine ⟨hb₀L.toLp b₀, Lp.ext ?_⟩
  exact (W.coeFn_toLI_toLp hb₀L).trans (hpt.trans hF.symm)

theorem cellChart_congr {y y' : Space} (hr : radius y = radius y') (hz : y 2 = y' 2) (τ : ℝ) :
    cellChart ε c (y, τ) = cellChart ε c (y', τ) := by
  simp only [cellChart, ageS, cellQ, etaCoord, hr, hz]

/-- The lift representative `a b(s, q, η)` depends on `x` only through `(r, z)`. -/
theorem liftRep_axInv (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (b : Profile → E) :
    AxInv ((liftScWC (E := E) hε hc hP).compFun b) := by
  intro y y' hr hz θ
  change (jConst ε * liftA y) • b (cellChart ε c (y, (toCell P (y, θ)).2)) =
    (jConst ε * liftA y') • b (cellChart ε c (y', (toCell P (y', θ)).2))
  have hτ : (toCell P (y, θ)).2 = (toCell P (y', θ)).2 := rfl
  rw [hτ, cellChart_congr hr hz, liftA, liftA, hr]

/-! ### The invariance -/

/-- **`S_ε(t)` maps lifts to lifts** (scalar case): the named hypothesis `LiftInvariant` holds
for the outer semigroup and the complex scalar lift, `ν, ε, c > 0`, `P = 2εc`. -/
theorem liftInvariant_sc {h : ℝ} (hh : 0 < h) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    LiftInvariant (outerSemigroup (E := E) (P := P) h hh.le) (liftSc hε hc hP) := by
  intro t ht b
  rcases ht.eq_or_lt with h0 | ht'
  · refine ⟨b, ?_⟩
    rw [← h0, outerSemigroup_T, Sop_zero]
    rfl
  obtain ⟨Jrep, hJrep⟩ : ∃ f : PSpace P → E,
      f = (liftScWC (E := E) hε hc hP).compFun (b : Profile → E) := ⟨_, rfl⟩
  have hJ : (liftSc hε hc hP b : PSpace P → E) =ᵐ[volume] Jrep := by
    rw [hJrep]; exact (liftScWC hε hc hP).coeFn_toLI b
  have hrep := Sop_rep' hh ht' hJ
  obtain ⟨U, hUdef⟩ : ∃ U : PSpace P → E,
      U = fun w => Jrep (w.1, w.2 - (t : AddCircle P)) := ⟨_, rfl⟩
  have hUinv : AxInv U := by
    rw [hUdef, hJrep]; exact (liftRep_axInv hε hc hP _).shift t
  have hUm : Measurable U := by
    rw [hUdef, hJrep]
    exact ((liftScWC hε hc hP).measurable_compFun (Lp.stronglyMeasurable b).measurable).comp
      (measurable_fst.prodMk (measurable_snd.sub_const _))
  obtain ⟨R, hRdef⟩ : ∃ R : PSpace P → E, R = fun z => Real.exp (t / 2) •
      Heat.heatConv (ιx P) (h * (Real.exp t - 1)) U (Real.exp (t / 2) • z.1, z.2) := ⟨_, rfl⟩
  have hRinv : AxInv R := by
    rw [hRdef]; exact (heatConv_axInv hUinv _).dil _ _
  have hRm : Measurable R := by
    have hm1 : Measurable fun z : PSpace P => ((Real.exp (t / 2) • z.1, z.2) : PSpace P) :=
      by fun_prop
    have hm2 : Measurable fun z : PSpace P =>
        Heat.heatConv (ιx P) (h * (Real.exp t - 1)) U (Real.exp (t / 2) • z.1, z.2) :=
      (measurable_heatConv hUm (h * (Real.exp t - 1))).comp hm1
    rw [hRdef]
    exact hm2.const_smul (Real.exp (t / 2))
  have hrep' : ((outerSemigroup (E := E) (P := P) h hh.le).T t (liftSc hε hc hP b) :
      PSpace P → E) =ᵐ[volume] R := by
    rw [hRdef, hUdef]; exact hrep
  have hBm : Measurable fun p : ℝ × ℝ × ℝ => R (axisVec p.1 p.2.1, (p.2.2 : AddCircle P)) :=
    hRm.comp ((continuous_axisVec.measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (AddCircle.measurable_mk'.comp (measurable_snd.comp measurable_snd)))
  have hRB : ∀ z : PSpace P,
      R z = R (axisVec (radius z.1) (z.1 2), (((toCell P z).2 : ℝ) : AddCircle P)) := by
    intro z
    have hcoe : (((toCell P z).2 : ℝ) : AddCircle P) = z.2 := AddCircle.coe_equivIoc
    rw [hcoe]
    exact hRinv.eq_axisPt z.1 z.2
  obtain ⟨b', hb'⟩ := exists_liftSc_eq hε hc hP hBm (hrep'.trans (Eventually.of_forall hRB))
  exact ⟨b', hb'.symm⟩

end UnforcedLeray.B0223
