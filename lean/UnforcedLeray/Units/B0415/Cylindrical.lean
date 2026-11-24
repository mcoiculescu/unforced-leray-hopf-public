import UnforcedLeray.Units.B0415.Group
import UnforcedLeray.Lib.Axisymmetric.Tensor

/-!
# Unit B0415, helper: cylindrical components of `J`, no swirl, and invariant tensors
(claims (i) and (ii))

Blueprint unit `B0415` (`eq:free-stress-2`, `paper/main.tex` lines 7353–7358):

> In cylindrical components, `J` preserves the radial and axial components and reverses the
> azimuthal component, so these are the `𝒪`-invariant fields: axisymmetric without swirl.
> Tensors transform by pushforward in both indices; invariant tensors have no entry with
> exactly one azimuthal index.

Frame `(e_r, e_φ, e_z)` = `(Axi.eR, Axi.eΦ, Axi.e3)` (`Lib/Axisymmetric/Cylindrical.lean`); the
pushforward of a vector field is `Blueprint.rotateField g f = g f(g⁻¹·)`.

* `radial_J`, `axial_J`, `azimuthal_J`: `(Jf)_r(y) = f_r(σy)`, `(Jf)_z(y) = f_z(σy)`,
  `(Jf)_φ(y) = −f_φ(σy)` for every field and every point (`σ = Axi.reflY`, `σ⁻¹ = σ`);
  `radial_rot`, `axial_rot`, `azimuthal_rot`: a rotation `R_θ` transports all three;
* `ae_azimuthal_eq_zero`, `ae_eq_meridional`: a measurable `𝒪`-invariant field has no swirl
  and is `A_r(ϱ, y₃) e_r + A_z(ϱ, y₃) e_z` a.e. (from `Axi.ae_aziC_eq_zero`,
  `Axi.ae_eq_avgLift`, `Lib/AxisymmetricB/Average.lean`);
* `pushTensor g T = g T(g⁻¹·) g⁻¹` (pushforward in both indices), `IsInvariantTensor`,
  `pushTensor_outer` (`u ⊗ v` transforms by pushforward of both factors),
  `isInvariantTensor_outer`, and `ae_isMeridTensor`: the frame entries `⟨e_a, T e_b⟩` of a
  measurable invariant tensor field satisfy `Axi.IsMeridTensor` (no entry with exactly one
  azimuthal index) a.e.

Junk values: on the axis Lean's `e_r`, `e_φ` are `0`; the component identities hold at every
point (both sides vanish on the axis), and the a.e. statements discard the null axis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.B0415

open UnforcedLeray.Axi (rotZ reflY eR eΦ e3 mer fixesAxis_rotZ fixesAxis_reflY)
open UnforcedLeray.Blueprint (rotateField)

/-! ### Cylindrical components under `J` and `R_θ` -/

theorem reflY_symm : reflY.symm = reflY := LinearIsometryEquiv.ext fun _ => rfl

theorem reflY_reflY (y : Space) : reflY (reflY y) = y := Axi.reflFun_reflFun y

theorem fixesAxis_symm {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) : FixesAxis g.symm := by
  unfold FixesAxis at hg ⊢
  rw [LinearIsometryEquiv.symm_apply_eq, hg]

theorem eR_symm {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (y : Space) :
    eR (g.symm y) = g.symm (eR y) :=
  Axi.eR_map (fixesAxis_symm hg) y

/-- **(i), radial component.** `(Jf)_r(y) = f_r(σ y)`: `J` preserves the radial component. -/
theorem radial_J (f : Space → Space) (y : Space) :
    inner ℝ (rotateField reflY f y) (eR y) = inner ℝ (f (reflY y)) (eR (reflY y)) := by
  have h : eR y = reflY (eR (reflY y)) := by
    rw [← Axi.eR_map fixesAxis_reflY, reflY_reflY]
  rw [Blueprint.L12.rotateField_apply, reflY_symm, h, LinearIsometryEquiv.inner_map_map]

/-- **(i), axial component.** `(Jf)_z(y) = f_z(σ y)`: `J` preserves the axial component. -/
theorem axial_J (f : Space → Space) (y : Space) :
    rotateField reflY f y 2 = f (reflY y) 2 := by
  rw [Blueprint.L12.rotateField_apply, Axi.apply_two_map fixesAxis_reflY, reflY_symm]

/-- **(i), azimuthal component.** `(Jf)_φ(y) = −f_φ(σ y)`: `J` reverses the azimuthal
component. -/
theorem azimuthal_J (f : Space → Space) (y : Space) :
    inner ℝ (rotateField reflY f y) (eΦ y) = -inner ℝ (f (reflY y)) (eΦ (reflY y)) := by
  have h : eΦ y = -reflY (eΦ (reflY y)) := by
    have := Axi.eΦ_reflY (reflY y)
    rwa [reflY_reflY] at this
  rw [Blueprint.L12.rotateField_apply, reflY_symm, h, inner_neg_right,
    LinearIsometryEquiv.inner_map_map]

/-- A rotation `R_θ` about the axis transports the radial component. -/
theorem radial_rot (θ : ℝ) (f : Space → Space) (y : Space) :
    inner ℝ (rotateField (rotZ θ) f y) (eR y) =
      inner ℝ (f ((rotZ θ).symm y)) (eR ((rotZ θ).symm y)) := by
  rw [Blueprint.L12.rotateField_apply, eR_symm (fixesAxis_rotZ θ)]
  conv_rhs => rw [← (rotZ θ).inner_map_map, LinearIsometryEquiv.apply_symm_apply]

/-- A rotation `R_θ` about the axis transports the axial component. -/
theorem axial_rot (θ : ℝ) (f : Space → Space) (y : Space) :
    rotateField (rotZ θ) f y 2 = f ((rotZ θ).symm y) 2 := by
  rw [Blueprint.L12.rotateField_apply, Axi.apply_two_map (fixesAxis_rotZ θ)]

/-- A rotation `R_θ` about the axis transports the azimuthal component. -/
theorem azimuthal_rot (θ : ℝ) (f : Space → Space) (y : Space) :
    inner ℝ (rotateField (rotZ θ) f y) (eΦ y) =
      inner ℝ (f ((rotZ θ).symm y)) (eΦ ((rotZ θ).symm y)) := by
  have h : eΦ ((rotZ θ).symm y) = (rotZ θ).symm (eΦ y) := by
    have := Axi.eΦ_rotZ θ ((rotZ θ).symm y)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [LinearIsometryEquiv.eq_symm_apply, ← this]
  rw [Blueprint.L12.rotateField_apply, h]
  conv_rhs => rw [← (rotZ θ).inner_map_map, LinearIsometryEquiv.apply_symm_apply]

/-! ### `𝒪`-invariant fields have no swirl -/

/-- Transfer of an a.e. statement on `dirac () ⊗ dy` to `dy`. -/
theorem ae_of_ae_dirac_prod {p : Unit × Space → Prop}
    (h : ∀ᵐ x ∂(Measure.dirac ()).prod (volume : Measure Space), p x) :
    ∀ᵐ y ∂(volume : Measure Space), p ((), y) := by
  rw [Measure.dirac_prod] at h
  exact ae_of_ae_map measurable_prodMk_left.aemeasurable h

/-- **No swirl.** A measurable `𝒪`-invariant field (`Statement.IsAxisymmetricNoSwirl`) has
vanishing azimuthal component a.e. (tex 7355–7356, the reflection argument). -/
theorem ae_azimuthal_eq_zero {f : Space → Space} (hf : Measurable f)
    (hsym : IsAxisymmetricNoSwirl f) : ∀ᵐ y, inner ℝ (f y) (eΦ y) = 0 := by
  have hW : Measurable fun x : Unit × Space => f x.2 := hf.comp measurable_snd
  have h := Axi.ae_aziC_eq_zero (μ := Measure.dirac ()) hW (ae_of_all _ fun _ => hsym)
  exact ae_of_ae_dirac_prod h

/-- **Axisymmetric without swirl, meridional form.** A measurable `𝒪`-invariant field is
`A_r(ϱ, y₃) e_r(y) + A_z(ϱ, y₃) e_z` a.e., with measurable meridional components. -/
theorem ae_eq_meridional {f : Space → Space} (hf : Measurable f)
    (hsym : IsAxisymmetricNoSwirl f) :
    ∃ Ar Az : ℝ × ℝ → ℝ, Measurable Ar ∧ Measurable Az ∧
      f =ᵐ[volume] fun y => Ar (mer y) • eR y + Az (mer y) • e3 := by
  have hW : Measurable fun x : Unit × Space => f x.2 := hf.comp measurable_snd
  have h := Axi.ae_eq_avgLift (μ := Measure.dirac ()) hW (ae_of_all _ fun _ => hsym)
  refine ⟨fun p => Axi.avgR (fun x : Unit × Space => f x.2) ((), p),
    fun p => Axi.avgZ (fun x : Unit × Space => f x.2) ((), p),
    (Axi.measurable_avgR hW).comp measurable_prodMk_left,
    (Axi.measurable_avgZ hW).comp measurable_prodMk_left, ?_⟩
  exact ae_of_ae_dirac_prod h

/-! ### Tensors -/

/-- **Pushforward of a tensor field in both indices** (tex 7356):
`(g·T)(x) = g ∘ T(g⁻¹x) ∘ g⁻¹`. -/
def pushTensor (g : Space ≃ₗᵢ[ℝ] Space) (T : Space → Space →L[ℝ] Space) (x : Space) :
    Space →L[ℝ] Space :=
  (g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
    ((T (g.symm x)).comp (g.symm.toContinuousLinearEquiv : Space →L[ℝ] Space))

theorem pushTensor_apply (g : Space ≃ₗᵢ[ℝ] Space) (T : Space → Space →L[ℝ] Space)
    (x v : Space) : pushTensor g T x v = g (T (g.symm x) (g.symm v)) := rfl

/-- An **invariant tensor field**: `g·T = T` a.e. for every `g ∈ 𝒪`. -/
def IsInvariantTensor (T : Space → Space →L[ℝ] Space) : Prop :=
  ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → pushTensor g T =ᵐ[volume] T

/-- The tensor product `a ⊗ b`, `(a ⊗ b) w = ⟨b, w⟩ a`. -/
def outer (a b : Space) : Space →L[ℝ] Space := (innerSL ℝ b).smulRight a

theorem outer_apply (a b w : Space) : outer a b w = inner ℝ b w • a := rfl

/-- **Tensors transform by pushforward in both indices** (tex 7356): the pushforward of
`u ⊗ v` is `(g·u) ⊗ (g·v)`. -/
theorem pushTensor_outer (g : Space ≃ₗᵢ[ℝ] Space) (u v : Space → Space) :
    pushTensor g (fun x => outer (u x) (v x)) =
      fun x => outer (rotateField g u x) (rotateField g v x) := by
  funext x
  ext1 w
  rw [pushTensor_apply, outer_apply, outer_apply, map_smul, Blueprint.L12.rotateField_apply,
    Blueprint.L12.rotateField_apply, ← LinearIsometryEquiv.inner_map_map g,
    LinearIsometryEquiv.apply_symm_apply]

/-- The tensor product of two `𝒪`-invariant fields is an invariant tensor. -/
theorem isInvariantTensor_outer {u v : Space → Space} (hu : IsAxisymmetricNoSwirl u)
    (hv : IsAxisymmetricNoSwirl v) : IsInvariantTensor fun x => outer (u x) (v x) := by
  intro g hg
  rw [pushTensor_outer]
  filter_upwards [hu g hg, hv g hg] with x h1 h2
  rw [Blueprint.L12.rotateField_apply, Blueprint.L12.rotateField_apply, h1, h2]

/-- An `𝒪`-equivariant frame vector applied to an invariant tensor gives an invariant field. -/
theorem isAxisymmetricNoSwirl_apply {T : Space → Space →L[ℝ] Space} (hT : IsInvariantTensor T)
    {e : Space → Space} (he : ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → ∀ y, e (g y) = g (e y)) :
    IsAxisymmetricNoSwirl fun y => T y (e y) := by
  intro g hg
  filter_upwards [hT g hg] with x hx
  rw [← hx, pushTensor_apply, he g.symm (fixesAxis_symm hg) x]

theorem adjoint_isometry (g : Space ≃ₗᵢ[ℝ] Space) :
    ContinuousLinearMap.adjoint (g.toContinuousLinearEquiv : Space →L[ℝ] Space) =
      (g.symm.toContinuousLinearEquiv : Space →L[ℝ] Space) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
  change inner ℝ (g.symm x) y = inner ℝ x (g y)
  exact Blueprint.L12.inner_symm_left g x y

theorem adjoint_pushTensor (g : Space ≃ₗᵢ[ℝ] Space) (T : Space → Space →L[ℝ] Space)
    (x : Space) : ContinuousLinearMap.adjoint (pushTensor g T x) =
      pushTensor g (fun y => ContinuousLinearMap.adjoint (T y)) x := by
  rw [pushTensor, pushTensor, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_isometry, ← LinearIsometryEquiv.symm_symm g, adjoint_isometry,
    LinearIsometryEquiv.symm_symm, ContinuousLinearMap.comp_assoc]

/-- The transpose of an invariant tensor is invariant. -/
theorem IsInvariantTensor.adjoint {T : Space → Space →L[ℝ] Space} (hT : IsInvariantTensor T) :
    IsInvariantTensor fun y => ContinuousLinearMap.adjoint (T y) := by
  intro g hg
  filter_upwards [hT g hg] with x hx
  rw [← adjoint_pushTensor, hx]

/-- The frame entries `T_{ab}(y) = ⟨e_a(y), T(y) e_b(y)⟩` in the order `(r, φ, z)`. -/
def frameEntries (T : Space → Space →L[ℝ] Space) (y : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun a b => inner ℝ (Axi.frame y a) (T y (Axi.frame y b))

theorem measurable_clm_apply {T : Space → Space →L[ℝ] Space} (hT : Measurable T)
    {e : Space → Space} (he : Measurable e) : Measurable fun y => T y (e y) := by
  have hc : Continuous fun p : (Space →L[ℝ] Space) × Space => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  exact hc.measurable.comp (hT.prodMk he)

theorem eR_equivariant (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (y : Space) :
    eR (g y) = g (eR y) := Axi.eR_map hg y

theorem e3_equivariant (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (_y : Space) :
    (fun _ : Space => e3) (g _y) = g ((fun _ : Space => e3) _y) := hg.symm

/-- **(ii) Invariant tensors have no entry with exactly one azimuthal index** (tex 7356–7357):
for a measurable tensor field `T` with `g·T = T` a.e. for every `g ∈ 𝒪`, the frame entries
`T_{rφ}, T_{φr}, T_{φz}, T_{zφ}` vanish a.e. -/
theorem ae_isMeridTensor {T : Space → Space →L[ℝ] Space} (hT : Measurable T)
    (hinv : IsInvariantTensor T) : ∀ᵐ y, Axi.IsMeridTensor (frameEntries T y) := by
  have hTa : Measurable fun y => ContinuousLinearMap.adjoint (T y) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous.measurable.comp hT
  have he3 : Measurable fun _ : Space => e3 := measurable_const
  have h1 := ae_azimuthal_eq_zero (measurable_clm_apply hTa Axi.measurable_eR')
    (isAxisymmetricNoSwirl_apply hinv.adjoint eR_equivariant)
  have h2 := ae_azimuthal_eq_zero (measurable_clm_apply hT Axi.measurable_eR')
    (isAxisymmetricNoSwirl_apply hinv eR_equivariant)
  have h3 := ae_azimuthal_eq_zero (measurable_clm_apply hT he3)
    (isAxisymmetricNoSwirl_apply hinv e3_equivariant)
  have h4 := ae_azimuthal_eq_zero (measurable_clm_apply hTa he3)
    (isAxisymmetricNoSwirl_apply hinv.adjoint e3_equivariant)
  filter_upwards [h1, h2, h3, h4] with y e1 e2 e3' e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · change inner ℝ (eR y) (T y (eΦ y)) = 0
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact e1
  · change inner ℝ (eΦ y) (T y (eR y)) = 0
    rw [real_inner_comm]
    exact e2
  · change inner ℝ (eΦ y) (T y e3) = 0
    rw [real_inner_comm]
    exact e3'
  · change inner ℝ e3 (T y (eΦ y)) = 0
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact e4

end UnforcedLeray.B0415
