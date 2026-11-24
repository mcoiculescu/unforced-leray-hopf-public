import UnforcedLeray.Units.B0226.Pairing
import UnforcedLeray.Units.B0226.Distrib
import UnforcedLeray.Units.B0226.Divergence
import UnforcedLeray.Units.B0226.AxisTests

/-!
# B0226: the conjugated Leray projections `P_ε`, `P_0` and the exact solenoidal condition

Blueprint unit B0226 (`unlabeled:3396`), `paper/main.tex` lines 3394–3402
(§`sec:st18-2436`), on the spaces of B0220 (tex lines 3279–3314):

> Let `P_ε = J_ε⁻¹ P_3D J_ε` and let `P_0` be the cylinder Leray projection on `(b_r, b_z)`.
> The exact solenoidal condition is `D_ε b_r + ∂_η b_z = 0`, `D_ε = ∂_q − εK`.

Objects (files `B0226/Defs.lean`, `B0226/Chain.lean`, `B0226/Pairing.lean`):

* `P3D ε c`: the `L²` Leray projection on `ℝ³ × period`, the orthogonal projection of
  `L²(dx dτ)` (one period `2εc`) onto the fields with `div_x V = 0` in the sense of
  distributions (`physSolenoidal`, `mem_physSolenoidal_iff`).
* `solenoidalH ε c`: the profiles `b ∈ H` with `D_ε b_r + ∂_η b_z = 0` in the sense of
  distributions on the cylinder (`mem_solenoidalH_iff`; Lebesgue-pairing form in
  `mem_solenoidalH_iff_distrib`, file `B0226/Distrib.lean`).
* `P0 c`: the flat cylinder Leray projection on `(b_r, b_z)`, the orthogonal projection onto
  `{∂_q b_r + ∂_η b_z = 0}` (`solenoidalH 0 c`).
* `Peps hε hc = J_ε† P3D J_ε` (this file). Since `J_ε` is an isometry, `J_ε† J_ε = 1`
  (`adjoint_J_apply_J`) and `J_ε†` is the inverse of `J_ε` on its range, the axisymmetric
  meridional fields (B0220 `range_J`). Unconditionally `P_ε` is self-adjoint with
  `‖P_ε‖ ≤ 1` (`isSelfAdjoint_Peps`, `norm_Peps_le`).

Claims:

* (pointwise, unconditional; proof outline of B0226) For a profile `b` differentiable at
  `chart(x,τ)` and `x` off the axis, `div U(x,τ) = (εr²)⁻¹ (D_ε b_r + ∂_η b_z)(chart(x,τ))`
  (`divergence_fieldU`, `divergence_fieldU_eq_zero_iff`, file `B0226/Divergence.lean`).
* (⇒, unconditional) If `U = a (b_r e_r + b_z e_z)` is distributionally divergence free on
  `ℝ³ × period`, then `D_ε b_r + ∂_η b_z = 0` (`solenoidalH_of_divFree_fieldU`,
  `solenoidalH_of_J_mem`). Proof: pair with the physical tests `Φ ∘ chart` and change
  variables (`inner_J_physGrad`).
* (⇔, unconditional for `ε > 0`, `c > 0`): `U` is divergence free iff
  `D_ε b_r + ∂_η b_z = 0` (`divFree_fieldU_iff`, `divFree_fieldU_iff_distrib`,
  `J_mem_physSolenoidal_iff`); `P_3D` preserves the no-swirl axisymmetric class
  (`P3D_preserves_meridional`), `J_ε P_ε = P_3D J_ε`, i.e. `P_ε = J_ε⁻¹ P_3D J_ε` (`J_Peps`,
  `Peps_eq_Jequiv_symm`), and `P_ε` is the orthogonal projection of `H` onto
  `{D_ε b_r + ∂_η b_z = 0}` (`Peps_eq_starProjection`, `Peps_idem`).

The (⇐) direction rests on `axisTestReduction` (statement `AxisTestReduction ε c`): an
axisymmetric no-swirl `L²` field whose divergence vanishes against the axisymmetric tests
`Φ ∘ chart` has zero divergence against every test of `ℝ³ × period`. It is proved in
`B0226/AxisTests.lean` (`mem_physSolenoidal_of_meridional`) from the removability of the axis
(`B0226/AxisCutoff.lean`, `mem_physSolenoidal_of_offAxis`) and angular averaging
(`B0226/Rotation.lean`, `integral_eq_rotPt_average`): the blueprint's "pair with axisymmetric
test functions" in the proof outline of B0226 (scoping note

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-! ### Axisymmetric tests suffice -/

/-- **Axis removability and angular averaging (INF23).** For every axisymmetric meridional
(no swirl) field `V ∈ L²(dx dτ)` over one period: if `∫∫ V · ∇ₓ(Φ ∘ chart) dx dτ = 0` for every
profile test `Φ` (these are the axisymmetric tests of `ℝ³ × period` vanishing near the axis and
for large `|x|`), then `div_x V = 0` against every test of `ℝ³ × period` (tex lines 3394–3402
and the proof outline of blueprint unit B0226: "pair with axisymmetric test functions").
Proved for `ε > 0`, `c > 0` in `axisTestReduction`. -/
def AxisTestReduction (ε c : ℝ) : Prop :=
  ∀ V ∈ meridionalSubspace ε c,
    (∀ Φ : Profile → ℝ, IsProfileTest c Φ →
      ∫ y, ⟪V y, gradX (fun y => Φ (chart ε y)) y⟫_ℝ ∂physMeasure ε c = 0) →
    V ∈ physSolenoidal ε c

/-- `AxisTestReduction ε c` holds for `ε > 0`, `c > 0` (`mem_physSolenoidal_of_meridional`,
file `B0226/AxisTests.lean`: the cutoff `χ((x₀² + x₁²)/t)` removes the axis because
`∫_{x₀² + x₁² ≤ 2t} |V|² → 0` while `‖∇χ‖_{L²}` stays bounded on the support of a test, and the
angular average reduces a test vanishing near the axis to the axisymmetric tests `Φ_θ ∘ chart`). -/
theorem axisTestReduction {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : AxisTestReduction ε c :=
  fun _ hV hΦ => mem_physSolenoidal_of_meridional hε hc hV hΦ

/-! ### The exact solenoidal condition -/

theorem J_mem_meridional {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    J hε hc b ∈ meridionalSubspace ε c := by
  rw [← range_J hε hc]
  exact LinearMap.mem_range_self _ b

/-- (⇒) If the lift `J_ε b` is divergence free on `ℝ³ × period`, then
`D_ε b_r + ∂_η b_z = 0` (unconditional). -/
theorem solenoidalH_of_J_mem {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {b : HSpace c Merid}
    (h : J hε hc b ∈ physSolenoidal ε c) : b ∈ solenoidalH ε c := by
  rw [solenoidalH, mem_orthogonal_span_range]
  intro Φ
  have h1 := (mem_orthogonal_span_range _ _).1 h (physTestOfProfile hε.ne' Φ)
  rw [inner_J_physGrad hε hc] at h1
  exact (mul_eq_zero.1 h1).resolve_left (jFactor_ne_zero hε)

/-- (⇐) `D_ε b_r + ∂_η b_z = 0` makes `J_ε b` divergence free (via `axisTestReduction`). -/
theorem J_mem_of_solenoidalH {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {b : HSpace c Merid} (hb : b ∈ solenoidalH ε c) :
    J hε hc b ∈ physSolenoidal ε c := by
  refine axisTestReduction hε hc _ (J_mem_meridional hε hc b) fun Φ hΦ => ?_
  have h1 := inner_physGrad (J hε hc b) (physTestOfProfile hε.ne' ⟨Φ, hΦ⟩)
  rw [inner_J_physGrad hε hc, (mem_orthogonal_span_range _ _).1 hb ⟨Φ, hΦ⟩, mul_zero] at h1
  exact h1.symm

/-- **The exact solenoidal condition** (tex lines 3398–3400): `J_ε b` is divergence free on
`ℝ³ × period` iff `D_ε b_r + ∂_η b_z = 0`. -/
theorem J_mem_physSolenoidal_iff {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) :
    J hε hc b ∈ physSolenoidal ε c ↔ b ∈ solenoidalH ε c :=
  ⟨solenoidalH_of_J_mem hε hc, J_mem_of_solenoidalH hε hc⟩

/-- Distributional divergence zero on `ℝ³ × period`, with convergent pairings (the convention of
`Statement.IsSolenoidal`, at the test functions `IsPhysTest` of `ℝ³ × period`). -/
def IsDivFreeOnPeriod (ε c : ℝ) (U : Space × ℝ → Space) : Prop :=
  ∀ φ : PhysTest ε c,
    Integrable (fun y => ⟪U y, gradX φ.1 y⟫_ℝ) (physMeasure ε c) ∧
      ∫ y, ⟪U y, gradX φ.1 y⟫_ℝ ∂physMeasure ε c = 0

/-- `U = a (b_r e_r + b_z e_z)` (B0220 `fieldU`, tex line 3292) is divergence free iff its
normalized lift `J_ε b = c_J U` is. -/
theorem divFree_fieldU_iff_J_mem {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    IsDivFreeOnPeriod ε c (fieldU ε (periodize c b)) ↔ J hε hc b ∈ physSolenoidal ε c := by
  have hk : jConst ε ≠ 0 := (jConst_pos hε).ne'
  have hU : ∀ φ : PhysTest ε c, (fun y => ⟪fieldU ε (periodize c b) y, gradX φ.1 y⟫_ℝ)
      =ᵐ[physMeasure ε c] fun y => (jConst ε)⁻¹ * ⟪J hε hc b y, physGrad ε c φ y⟫_ℝ := by
    intro φ
    filter_upwards [coeFn_J hε hc b, coeFn_physGrad ε c φ] with y h1 h2
    rw [h1, h2, real_inner_smul_left]
    unfold jConst at hk ⊢
    field_simp
  rw [mem_physSolenoidal_iff]
  constructor
  · intro h φ
    have h1 := (h φ).2
    rw [integral_congr_ae (hU φ), integral_const_mul] at h1
    rw [← inner_physGrad]
    exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero hk)
  · intro h φ
    refine ⟨((L2.integrable_inner (J hε hc b) (physGrad ε c φ)).const_mul _).congr
      (hU φ).symm, ?_⟩
    rw [integral_congr_ae (hU φ), integral_const_mul, ← L2.inner_def, inner_physGrad, h φ,
      mul_zero]

/-- (⇒, unconditional) If `U = a (b_r e_r + b_z e_z)` is distributionally divergence free on
`ℝ³ × period`, then `D_ε b_r + ∂_η b_z = 0`. -/
theorem solenoidalH_of_divFree_fieldU {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {b : HSpace c Merid}
    (h : IsDivFreeOnPeriod ε c (fieldU ε (periodize c b))) : b ∈ solenoidalH ε c :=
  solenoidalH_of_J_mem hε hc ((divFree_fieldU_iff_J_mem hε hc b).1 h)

/-- **B0226, the exact solenoidal condition** (tex lines 3398–3400): `U = a (b_r e_r + b_z e_z)`
is distributionally divergence free on `ℝ³ × period` iff `D_ε b_r + ∂_η b_z = 0`,
`D_ε = ∂_q − εK`. -/
theorem divFree_fieldU_iff {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) :
    IsDivFreeOnPeriod ε c (fieldU ε (periodize c b)) ↔ b ∈ solenoidalH ε c :=
  (divFree_fieldU_iff_J_mem hε hc b).trans (J_mem_physSolenoidal_iff hε hc b)

/-- **B0226, the exact solenoidal condition with the Lebesgue pairing**:
`U = a (b_r e_r + b_z e_z)` is distributionally divergence free on
`ℝ³ × period` iff `⟨D_ε b_r + ∂_η b_z, Ψ⟩ = 0` for every test `Ψ` of the cylinder
(`divDistrib`, file `B0226/Distrib.lean`). -/
theorem divFree_fieldU_iff_distrib {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) :
    IsDivFreeOnPeriod ε c (fieldU ε (periodize c b)) ↔
      ∀ Ψ : ProfileTest c, divDistrib ε c b Ψ.1 = 0 :=
  (divFree_fieldU_iff hε hc b).trans (mem_solenoidalH_iff_distrib b)

/-! ### `P_3D` commutes with `J_ε` -/

/-- The lifts of `(solenoidalH)ᗮ`, the closure of the profile gradients, are physical
gradients. -/
theorem J_mem_orthogonal_of_mem_orthogonal {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {r : HSpace c Merid} (hr : r ∈ (solenoidalH ε c)ᗮ) :
    J hε hc r ∈ (physSolenoidal ε c)ᗮ := by
  let T : Submodule ℝ (HSpace c Merid) :=
    (physSolenoidal ε c)ᗮ.comap (J hε hc).toLinearMap
  have hT : IsClosed (T : Set (HSpace c Merid)) :=
    (Submodule.isClosed_orthogonal _).preimage (J hε hc).continuous
  have hspan : Submodule.span ℝ (Set.range (profileGradH ε c)) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨Φ, rfl⟩
    exact J_profileGradH_mem_orthogonal hε hc Φ
  have hle : (solenoidalH ε c)ᗮ ≤ T := by
    rw [solenoidalH, Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.topologicalClosure_minimal _ hspan hT
  exact hle hr

/-- `P_3D J_ε b = J_ε Π b` with `Π` the orthogonal projection of `H`
onto `{D_ε b_r + ∂_η b_z = 0}`. -/
theorem P3D_J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) :
    P3D ε c (J hε hc b) = J hε hc ((solenoidalH ε c).starProjection b) := by
  unfold P3D
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (J_mem_of_solenoidalH hε hc (Submodule.starProjection_apply_mem _ b)) fun w hw => ?_
  rw [← map_sub]
  exact (Submodule.mem_orthogonal' _ _).1
    (J_mem_orthogonal_of_mem_orthogonal hε hc (Submodule.sub_starProjection_mem_orthogonal b))
    w hw

/-- `P_3D` preserves the axisymmetric class without swirl (tex lines 3249–3250, blueprint
statement of B0226). -/
theorem P3D_preserves_meridional {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {V : PhysL2 ε c} (hV : V ∈ meridionalSubspace ε c) :
    P3D ε c V ∈ meridionalSubspace ε c := by
  rw [← range_J hε hc] at hV
  obtain ⟨b, rfl⟩ := hV
  change P3D ε c (J hε hc b) ∈ _
  rw [P3D_J hε hc]
  exact J_mem_meridional hε hc _

/-! ### The conjugated projection `P_ε` -/

/-- `P_ε = J_ε† P_3D J_ε` on `H` (tex line 3396). `J_ε†` inverts `J_ε` on its range
(`adjoint_J_apply_J`) and `P_3D` preserves that range (`P3D_preserves_meridional`), so this is
`J_ε⁻¹ P_3D J_ε` (`J_Peps`, `Peps_eq_Jequiv_symm`). -/
def Peps {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : HSpace c Merid →L[ℝ] HSpace c Merid :=
  ContinuousLinearMap.adjoint (J hε hc).toContinuousLinearMap ∘L P3D ε c ∘L
    (J hε hc).toContinuousLinearMap

theorem adjoint_J_comp_J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ContinuousLinearMap.adjoint (J hε hc).toContinuousLinearMap ∘L
      (J hε hc).toContinuousLinearMap = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 fun b => (J hε hc).norm_map b

/-- `J_ε† J_ε = 1`: the adjoint inverts the isometry `J_ε` on its range. -/
theorem adjoint_J_apply_J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    ContinuousLinearMap.adjoint (J hε hc).toContinuousLinearMap (J hε hc b) = b := by
  exact ContinuousLinearMap.ext_iff.1 (adjoint_J_comp_J hε hc) b

theorem Peps_apply {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    Peps hε hc b =
      ContinuousLinearMap.adjoint (J hε hc).toContinuousLinearMap (P3D ε c (J hε hc b)) :=
  rfl

/-- `P_ε` is self-adjoint on `H`. -/
theorem isSelfAdjoint_Peps {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : IsSelfAdjoint (Peps hε hc) :=
  (isSelfAdjoint_starProjection (physSolenoidal ε c)).adjoint_conj _

/-- `‖P_ε‖ ≤ 1`. -/
theorem norm_Peps_le {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : ‖Peps hε hc‖ ≤ 1 := by
  have hJ : ‖(J hε hc).toContinuousLinearMap‖ ≤ 1 := (J hε hc).norm_toContinuousLinearMap_le
  have hJa : ‖ContinuousLinearMap.adjoint (J hε hc).toContinuousLinearMap‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hJ
  calc ‖Peps hε hc‖ ≤ ‖ContinuousLinearMap.adjoint (J hε hc).toContinuousLinearMap‖ *
        (‖P3D ε c‖ * ‖(J hε hc).toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by
        gcongr
        exact norm_P3D_le ε c
    _ = 1 := by norm_num

/-- `J_ε P_ε = P_3D J_ε`, i.e. `P_ε = J_ε⁻¹ P_3D J_ε` (tex line 3396). -/
theorem J_Peps {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) : J hε hc (Peps hε hc b) = P3D ε c (J hε hc b) := by
  rw [Peps_apply, P3D_J hε hc, adjoint_J_apply_J]

/-- `P_ε = J_ε⁻¹ P_3D J_ε` literally, with `J_ε⁻¹` the inverse of the unitary
`J_ε : H ≃ meridional fields` (B0220 `Jequiv`). -/
theorem Peps_eq_Jequiv_symm {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) :
    Peps hε hc b = (Jequiv hε hc).symm
      ⟨P3D ε c (J hε hc b), P3D_preserves_meridional hε hc (J_mem_meridional hε hc b)⟩ := by
  apply (Jequiv hε hc).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext1
  rw [Jequiv_apply, J_Peps hε hc]

/-- **`P_ε` is the orthogonal projection of `H` onto the exact solenoidal subspace
`{D_ε b_r + ∂_η b_z = 0}`** (tex lines 3396–3400). -/
theorem Peps_eq_starProjection {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    Peps hε hc = (solenoidalH ε c).starProjection := by
  ext1 b
  rw [Peps_apply, P3D_J hε hc, adjoint_J_apply_J]

/-- `P_ε` is idempotent. -/
theorem Peps_idem {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (b : HSpace c Merid) : Peps hε hc (Peps hε hc b) = Peps hε hc b := by
  rw [Peps_eq_starProjection hε hc]
  exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ b)

end UnforcedLeray.B0226
