import UnforcedLeray.Lib.Axisymmetric.Measure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# AX04 (rotation averaging): an 𝒪-invariant field is a meridional lift almost everywhere


§5 Layer 3, target AX04 (`range_Jv`), risk 4 of §6 ("rotation averaging with Fubini over
`(θ, y)` and the reflection argument for the `e_φ` component"). Blueprint units served: B0417
(`eq:m4-free-spaces`, tex 7272–7297: `J_v` unitary onto the axisymmetric-no-swirl subspace),
B0482 (tex 7920–7949: the azimuthal velocity vanishes). The group `𝒪` and the reflection
argument are tex 112–116 ("a reflection in a plane containing the axis reverses the azimuthal
component"). Adapted from the planar template of the NonUniqueEuler formalization,
`NonUniqueEuler/lean/NonUniqueEuler/P/Infra/Polar/AngularAverage.lean` (lines 52–96:
the normalized angle measure, the measure-preserving rotation of the product, and
`ae_eq_angAvg_of_isRadial`, lines 157–182), here with a parameter `t` (the phase time), in
three dimensions and for vector fields.

* `rotZ θ`, `reflY`: the rotation by `θ` about `e₃` and the reflection `y₁ ↦ −y₁`, members of
  `𝒪` (`fixesAxis_rotZ`, `fixesAxis_reflY`);
* `angμ = (2π)⁻¹ dφ|_{(0, 2π]}` (a probability measure) and `measurePreserving_rotPar`:
  `((t, y), φ) ↦ (t, R_φ y)` preserves `(μ ⊗ dy) ⊗ angμ → μ ⊗ dy`;
* `angAvg F (t, ρ, z) = ∫ F(t, ρ cos φ, ρ sin φ, z) dangμ(φ)`, `measurable_angAvg`;
* `ae_eq_angAvg`: a measurable `F` that is a.e. invariant under each rotation separately is
  a.e. equal to its angular average, a function of `(t, ϱ, y₃)`;
* `ae_eq_avgLift` (**main result**): if `W(t, ·)` is axisymmetric without swirl
  (`Statement.IsAxisymmetricNoSwirl`, a.e. invariance for each `g ∈ 𝒪`) for `μ`-a.e. `t`, then
  `W(t, y) = A_r(t, ϱ, y₃) e_r + A_z(t, ϱ, y₃) e_z` for `μ ⊗ dy`-a.e. `(t, y)`, with the
  averaged components `avgR W`, `avgZ W`. The azimuthal component vanishes by the reflection.

Junk values: on the axis `e_r = e_φ = 0` in Lean; the axis is a null set (`ae_not_mem_axis`)
and every a.e. statement below discards it. The averages are Bochner integrals of real
functions; at points where `φ ↦ F(t, …)` is not integrable Lean's value is `0`, and such
points form a null set in every use (they are excluded by the a.e. identity
`F(t, R_φ y) = F(t, y)` for a.e. `φ`, which makes the integrand constant).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

/-! ### Rotations about the axis and the reflection `y₁ ↦ −y₁` -/

/-- The rotation by `θ` about the `e₃` axis, as a function. -/
def rotFun (θ : ℝ) (y : Space) : Space :=
  !₂[Real.cos θ * y 0 - Real.sin θ * y 1, Real.sin θ * y 0 + Real.cos θ * y 1, y 2]

@[simp] theorem rotFun_apply_zero (θ : ℝ) (y : Space) :
    rotFun θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 := rfl
@[simp] theorem rotFun_apply_one (θ : ℝ) (y : Space) :
    rotFun θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 := rfl
@[simp] theorem rotFun_apply_two (θ : ℝ) (y : Space) : rotFun θ y 2 = y 2 := rfl

/-- The rotation about the axis is linear. -/
def rotL (θ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := rotFun θ
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rotFun] <;> ring
  map_smul' k x := by
    ext i
    fin_cases i <;> simp [rotFun] <;> ring

theorem norm_rotFun (θ : ℝ) (y : Space) : ‖rotFun θ y‖ = ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three, rotFun_apply_zero,
    rotFun_apply_one, rotFun_apply_two]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.cos_sq_add_sin_sq θ

theorem rotFun_neg_rotFun (θ : ℝ) (y : Space) : rotFun (-θ) (rotFun θ y) = y := by
  ext i
  fin_cases i
  · show Real.cos (-θ) * (Real.cos θ * y 0 - Real.sin θ * y 1) -
        Real.sin (-θ) * (Real.sin θ * y 0 + Real.cos θ * y 1) = y 0
    rw [Real.cos_neg, Real.sin_neg]
    linear_combination (y 0) * Real.cos_sq_add_sin_sq θ
  · show Real.sin (-θ) * (Real.cos θ * y 0 - Real.sin θ * y 1) +
        Real.cos (-θ) * (Real.sin θ * y 0 + Real.cos θ * y 1) = y 1
    rw [Real.cos_neg, Real.sin_neg]
    linear_combination (y 1) * Real.cos_sq_add_sin_sq θ
  · rfl

/-- **The rotation `R_θ ∈ 𝒪`** by the angle `θ` about `e₃`. -/
def rotZ (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotFun θ
  invFun := rotFun (-θ)
  map_add' := (rotL θ).map_add
  map_smul' := (rotL θ).map_smul
  left_inv := rotFun_neg_rotFun θ
  right_inv y := by simpa using rotFun_neg_rotFun (-θ) y
  norm_map' := norm_rotFun θ

@[simp] theorem rotZ_apply (θ : ℝ) (y : Space) : rotZ θ y = rotFun θ y := rfl

/-- The reflection `(y₀, y₁, y₂) ↦ (y₀, −y₁, y₂)` in the plane `{y₁ = 0}`, as a function. -/
def reflFun (y : Space) : Space := !₂[y 0, -y 1, y 2]

@[simp] theorem reflFun_apply_zero (y : Space) : reflFun y 0 = y 0 := rfl
@[simp] theorem reflFun_apply_one (y : Space) : reflFun y 1 = -y 1 := rfl
@[simp] theorem reflFun_apply_two (y : Space) : reflFun y 2 = y 2 := rfl

/-- The reflection is linear. -/
def reflL : Space →ₗ[ℝ] Space where
  toFun := reflFun
  map_add' x y := by
    ext i
    fin_cases i <;> simp [reflFun]; ring
  map_smul' k x := by
    ext i
    fin_cases i <;> simp [reflFun]

theorem norm_reflFun (y : Space) : ‖reflFun y‖ = ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three, reflFun_apply_zero,
    reflFun_apply_one, reflFun_apply_two]
  ring

theorem reflFun_reflFun (y : Space) : reflFun (reflFun y) = y := by
  ext i
  fin_cases i <;> simp [reflFun]

/-- **The reflection `σ ∈ 𝒪`** in the plane `{y₁ = 0}`, which contains the axis. -/
def reflY : Space ≃ₗᵢ[ℝ] Space where
  toFun := reflFun
  invFun := reflFun
  map_add' := reflL.map_add
  map_smul' := reflL.map_smul
  left_inv := reflFun_reflFun
  right_inv := reflFun_reflFun
  norm_map' := norm_reflFun

@[simp] theorem reflY_apply (y : Space) : reflY y = reflFun y := rfl

theorem fixesAxis_rotZ (θ : ℝ) : FixesAxis (rotZ θ) := by
  unfold FixesAxis
  ext i
  fin_cases i <;> simp [rotFun, coordinateVector]

theorem fixesAxis_reflY : FixesAxis reflY := by
  unfold FixesAxis
  ext i
  fin_cases i <;> simp [reflFun, coordinateVector]

/-! ### Elements of `𝒪` and the frame -/

section Frame

variable {g : Space ≃ₗᵢ[ℝ] Space}

theorem apply_two_map (hg : FixesAxis g) (v : Space) : (g v) 2 = v 2 := by
  have h := symm_apply_two g hg (g v)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

theorem ϱ_map (hg : FixesAxis g) (y : Space) : ϱ (g y) = ϱ y := by
  have h := ϱ_symm_apply g hg (g y)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

theorem mer_map (hg : FixesAxis g) (y : Space) : mer (g y) = mer y := by
  simp only [mer, ϱ_map hg, apply_two_map hg]

theorem eR_map (hg : FixesAxis g) (y : Space) : eR (g y) = g (eR y) := by
  have h := map_eR_symm g hg (g y)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

end Frame

theorem eΦ_rotZ (θ : ℝ) (y : Space) : eΦ (rotZ θ y) = rotZ θ (eΦ y) := by
  have hρ : ϱ (rotZ θ y) = ϱ y := ϱ_map (fixesAxis_rotZ θ) y
  rw [eΦ, eΦ, hρ]
  ext i
  fin_cases i <;> (simp [rotFun]; try ring_nf; try simp)

theorem eΦ_reflY (y : Space) : eΦ (reflY y) = -reflY (eΦ y) := by
  have hρ : ϱ (reflY y) = ϱ y := ϱ_map fixesAxis_reflY y
  rw [eΦ, eΦ, hρ]
  ext i
  fin_cases i <;> simp [reflFun]

theorem inner_eR_apply (v y : Space) : inner ℝ v (eR y) = (v 0 * y 0 + v 1 * y 1) / ϱ y := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, eR_apply_zero, eR_apply_one, eR_apply_two,
    RCLike.inner_apply, conj_trivial]
  ring

theorem inner_eΦ_apply (v y : Space) : inner ℝ v (eΦ y) = (v 1 * y 0 - v 0 * y 1) / ϱ y := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, eΦ_apply_zero, eΦ_apply_one, eΦ_apply_two,
    RCLike.inner_apply, conj_trivial]
  ring

/-- Off the axis `(e_r, e_φ, e_z)` is an orthonormal frame:
`v = (v·e_r) e_r + (v·e_φ) e_φ + v_z e_z`. -/
theorem eq_frame_decomp {y : Space} (hy : y ∉ axis) (v : Space) :
    v = inner ℝ v (eR y) • eR y + inner ℝ v (eΦ y) • eΦ y + v 2 • e3 := by
  have h1 : (y 0 ^ 2 + y 1 ^ 2) / ϱ y ^ 2 = 1 := by
    rw [← ϱ_sq, div_self (pow_ne_zero 2 (ϱ_ne_zero hy))]
  rw [inner_eR_apply, inner_eΦ_apply]
  ext i
  fin_cases i
  · have e : (v 0 * y 0 + v 1 * y 1) / ϱ y * (y 0 / ϱ y) +
        (v 1 * y 0 - v 0 * y 1) / ϱ y * (-y 1 / ϱ y) = v 0 * ((y 0 ^ 2 + y 1 ^ 2) / ϱ y ^ 2) := by
      ring
    simp [e, h1]
  · have e : (v 0 * y 0 + v 1 * y 1) / ϱ y * (y 1 / ϱ y) +
        (v 1 * y 0 - v 0 * y 1) / ϱ y * (y 0 / ϱ y) = v 1 * ((y 0 ^ 2 + y 1 ^ 2) / ϱ y ^ 2) := by
      ring
    simp [e, h1]
  · simp

/-! ### Polar form of a point -/

theorem norm_complex_mk (y : Space) : ‖(⟨y 0, y 1⟩ : ℂ)‖ = ϱ y := by
  rw [Complex.norm_def, Complex.normSq_mk, ϱ]
  congr 1
  ring

/-- Every point is `cylMap ((ϱ y, α), y₃)` for its polar angle `α`. -/
theorem cylMap_polar (y : Space) : cylMap ((ϱ y, Complex.arg ⟨y 0, y 1⟩), y 2) = y := by
  have hc := Complex.norm_mul_cos_arg (⟨y 0, y 1⟩ : ℂ)
  have hs := Complex.norm_mul_sin_arg (⟨y 0, y 1⟩ : ℂ)
  rw [norm_complex_mk] at hc hs
  ext i
  fin_cases i
  · exact hc
  · exact hs
  · rfl

theorem rotFun_cylMap (θ r φ z : ℝ) : rotFun θ (cylMap ((r, φ), z)) = cylMap ((r, φ + θ), z) := by
  ext i
  fin_cases i <;> simp [rotFun, cylMap, Real.cos_add, Real.sin_add] <;> ring

/-! ### The normalized angle measure -/

/-- The normalized angle measure `(2π)⁻¹ dφ` on `(0, 2π]`. -/
def angμ : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc 0 (2 * π))

instance isProbabilityMeasure_angμ : IsProbabilityMeasure angμ := by
  constructor
  simp only [angμ, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [pi_pos]) ENNReal.ofReal_ne_top

theorem integral_angμ (f : ℝ → ℝ) :
    ∫ φ, f φ ∂angμ = (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, f φ := by
  rw [angμ, integral_smul_measure, intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Shift invariance of the angle average of a `2π`-periodic function. -/
theorem integral_angμ_add {g : ℝ → ℝ} (hg : Function.Periodic g (2 * π)) (α : ℝ) :
    ∫ φ, g (α + φ) ∂angμ = ∫ φ, g φ ∂angμ := by
  rw [integral_angμ, integral_angμ, intervalIntegral.integral_comp_add_left, add_zero]
  congr 1
  simpa using hg.intervalIntegral_add_eq α 0

/-! ### Rotating the product -/

theorem continuous_rotFun : Continuous fun q : ℝ × Space => rotFun q.1 q.2 := by
  unfold rotFun
  fun_prop

theorem measurable_rotFun : Measurable fun q : ℝ × Space => rotFun q.1 q.2 :=
  continuous_rotFun.measurable

/-- Measurability of `a ↦ R_{f a} (g a)` (stated through an explicit composition: unifying the
composite with the lambda form directly makes the elaborator unfold the rotation). -/
theorem measurable_rotFun_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ} {g : α → Space}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => rotFun (f a) (g a) := by
  have h : (fun a => rotFun (f a) (g a)) =
      (fun q : ℝ × Space => rotFun q.1 q.2) ∘ (fun a => (f a, g a)) := rfl
  rw [h]
  exact measurable_rotFun.comp (hf.prodMk hg)

variable {T : Type*} [MeasurableSpace T]

theorem measurable_rotPar :
    Measurable fun p : (T × Space) × ℝ => (p.1.1, rotZ p.2 p.1.2) := by
  have h1 : Measurable fun p : (T × Space) × ℝ => p.1.1 := measurable_fst.comp measurable_fst
  have h3 : Measurable fun p : (T × Space) × ℝ => rotFun p.2 p.1.2 :=
    measurable_rotFun_comp measurable_snd (measurable_snd.comp measurable_fst)
  exact h1.prodMk h3

/-- `((t, y), φ) ↦ (t, R_φ y)` maps `(μ ⊗ dy) ⊗ angμ` to `μ ⊗ dy`. -/
theorem measurePreserving_rotPar (μ : Measure T) [SFinite μ] :
    MeasurePreserving (fun p : (T × Space) × ℝ => (p.1.1, rotZ p.2 p.1.2))
      ((μ.prod volume).prod angμ) (μ.prod volume) := by
  refine ⟨measurable_rotPar, ?_⟩
  ext s hs
  rw [Measure.map_apply measurable_rotPar hs, Measure.prod_apply_symm (measurable_rotPar hs)]
  have h : ∀ φ : ℝ, (μ.prod volume) ((fun x : T × Space => (x, φ)) ⁻¹'
      ((fun p : (T × Space) × ℝ => (p.1.1, rotZ p.2 p.1.2)) ⁻¹' s)) = (μ.prod volume) s :=
    fun φ => ((MeasurePreserving.id μ).prod (rotZ φ).measurePreserving).measure_preimage
      hs.nullMeasurableSet
  rw [lintegral_congr h, lintegral_const, measure_univ, mul_one]

/-! ### The angular average -/

/-- The angular average `A F (t, ρ, z) = ∫ F(t, ρ cos φ, ρ sin φ, z) dangμ(φ)`. -/
def angAvg (F : T × Space → ℝ) (p : T × (ℝ × ℝ)) : ℝ :=
  ∫ φ, F (p.1, cylMap ((p.2.1, φ), p.2.2)) ∂angμ

theorem measurable_angAvg {F : T × Space → ℝ} (hF : Measurable F) : Measurable (angAvg F) := by
  have hm : Measurable fun q : (T × (ℝ × ℝ)) × ℝ => F (q.1.1, cylMap ((q.1.2.1, q.2), q.1.2.2)) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_cylMap.comp
      (((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace T] in
/-- The average over the orbit through `y`, read at the meridional point `(ϱ y, y₃)`. -/
theorem angAvg_mer (F : T × Space → ℝ) (t : T) (y : Space) :
    angAvg F (t, mer y) = ∫ φ, F (t, rotZ φ y) ∂angμ := by
  obtain ⟨α, hα⟩ : ∃ α, cylMap ((ϱ y, α), y 2) = y := ⟨_, cylMap_polar y⟩
  have hper : Function.Periodic (fun φ => F (t, cylMap ((ϱ y, φ), y 2))) (2 * π) := by
    intro φ
    simp only [cylMap, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have h1 : ∀ φ, rotZ φ y = cylMap ((ϱ y, α + φ), y 2) := by
    intro φ
    have h := rotFun_cylMap φ (ϱ y) α (y 2)
    rw [hα] at h
    rw [rotZ_apply, h]
  simp_rw [h1]
  exact (integral_angμ_add hper α).symm

/-- **Angular averaging.** A measurable `F` which, for each angle `θ` separately, is a.e.
invariant under `(t, y) ↦ (t, R_θ y)` is a.e. equal to its angular average at `(t, ϱ y, y₃)`
(Fubini over `(θ, (t, y))`; template `AngularAverage.lean:157`). -/
theorem ae_eq_angAvg {μ : Measure T} [SFinite μ] {F : T × Space → ℝ} (hF : Measurable F)
    (hrot : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, F (x.1, rotZ θ x.2) = F x) :
    ∀ᵐ x ∂μ.prod volume, F x = angAvg F (x.1, mer x.2) := by
  have hmeas : MeasurableSet {q : (T × Space) × ℝ | F (q.1.1, rotZ q.2 q.1.2) = F q.1} :=
    measurableSet_eq_fun (hF.comp measurable_rotPar) (hF.comp measurable_fst)
  have hswap : ∀ᵐ x ∂μ.prod volume, ∀ᵐ φ ∂angμ, F (x.1, rotZ φ x.2) = F x :=
    (Measure.ae_ae_comm (p := fun x φ => F (x.1, rotZ φ x.2) = F x) hmeas).2 (ae_of_all _ hrot)
  filter_upwards [hswap] with x hx
  rw [angAvg_mer, integral_congr_ae hx]
  simp

/-! ### Invariant vector fields -/

/-- For `μ`-a.e. `t` let `W(t, ·)` be 𝒪-invariant; then `W(t, g y) = g W(t, y)` for
`μ ⊗ dy`-a.e. `(t, y)`, for each `g ∈ 𝒪`. -/
theorem ae_map_comm {μ : Measure T} [SFinite μ] {W : T × Space → Space} (hW : Measurable W)
    (hsym : ∀ᵐ t ∂μ, IsAxisymmetricNoSwirl fun y => W (t, y))
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) :
    ∀ᵐ x ∂μ.prod volume, W (x.1, g x.2) = g (W x) := by
  have hgm : Measurable g := g.continuous.measurable
  have hS : MeasurableSet {x : T × Space | W (x.1, g x.2) = g (W x)} :=
    measurableSet_eq_fun (hW.comp (measurable_fst.prodMk (hgm.comp measurable_snd)))
      (hgm.comp hW)
  rw [Measure.ae_prod_iff_ae_ae hS]
  filter_upwards [hsym] with t ht
  have h := g.measurePreserving.quasiMeasurePreserving.ae_eq_comp (ht g hg)
  filter_upwards [h] with y hy
  simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply] at hy
  exact hy.symm

/-- The radial component `W·e_r`. -/
def radC (W : T × Space → Space) (x : T × Space) : ℝ := inner ℝ (W x) (eR x.2)

/-- The azimuthal component `W·e_φ`. -/
def aziC (W : T × Space → Space) (x : T × Space) : ℝ := inner ℝ (W x) (eΦ x.2)

/-- The axial component `W_z`. -/
def axC (W : T × Space → Space) (x : T × Space) : ℝ := W x 2

/-- The averaged radial component `A_r(t, ρ, z)`. -/
def avgR (W : T × Space → Space) : T × (ℝ × ℝ) → ℝ := angAvg (radC W)

/-- The averaged axial component `A_z(t, ρ, z)`. -/
def avgZ (W : T × Space → Space) : T × (ℝ × ℝ) → ℝ := angAvg (axC W)

theorem measurable_eΦ : Measurable eΦ := by
  have h : Continuous fun y : Space => !₂[-y 1, y 0, (0 : ℝ)] := by fun_prop
  exact measurable_ϱ.inv.smul h.measurable

theorem measurable_eR' : Measurable eR := by
  have h : Continuous fun y : Space => hor y := contDiff_hor (k := 0) |>.continuous
  exact measurable_ϱ.inv.smul h.measurable

theorem measurable_radC {W : T × Space → Space} (hW : Measurable W) : Measurable (radC W) :=
  hW.inner (measurable_eR'.comp measurable_snd)

theorem measurable_aziC {W : T × Space → Space} (hW : Measurable W) : Measurable (aziC W) :=
  hW.inner (measurable_eΦ.comp measurable_snd)

theorem measurable_axC {W : T × Space → Space} (hW : Measurable W) : Measurable (axC W) :=
  (measurable_coord 2).comp hW

theorem measurable_avgR {W : T × Space → Space} (hW : Measurable W) : Measurable (avgR W) :=
  measurable_angAvg (measurable_radC hW)

theorem measurable_avgZ {W : T × Space → Space} (hW : Measurable W) : Measurable (avgZ W) :=
  measurable_angAvg (measurable_axC hW)

/-- **No swirl** (tex 112–116, the reflection argument): the azimuthal component of an
𝒪-invariant field vanishes a.e. -/
theorem ae_aziC_eq_zero {μ : Measure T} [SFinite μ] {W : T × Space → Space} (hW : Measurable W)
    (hsym : ∀ᵐ t ∂μ, IsAxisymmetricNoSwirl fun y => W (t, y)) :
    ∀ᵐ x ∂μ.prod volume, aziC W x = 0 := by
  have hrot : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, aziC W (x.1, rotZ θ x.2) = aziC W x := by
    intro θ
    filter_upwards [ae_map_comm hW hsym (fixesAxis_rotZ θ)] with x hx
    simp only [aziC]
    rw [hx, eΦ_rotZ, LinearIsometryEquiv.inner_map_map]
  have havg := ae_eq_angAvg (measurable_aziC hW) hrot
  have hmp : MeasurePreserving (Prod.map id reflY) (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).prod reflY.measurePreserving
  have havg' := hmp.quasiMeasurePreserving.ae havg
  filter_upwards [havg, havg', ae_map_comm hW hsym fixesAxis_reflY] with x h1 h2 h3
  change aziC W (x.1, reflY x.2) = angAvg (aziC W) (x.1, mer (reflY x.2)) at h2
  have h4 : aziC W (x.1, reflY x.2) = -aziC W x := by
    simp only [aziC]
    rw [h3, eΦ_reflY, inner_neg_right, LinearIsometryEquiv.inner_map_map]
  rw [mer_map fixesAxis_reflY, ← h1, h4] at h2
  linarith

/-- **AX04, rotation averaging** (B0417, tex 7276–7280; B0482, tex 7920–7949; tex 112–116).
If for `μ`-a.e. `t` the slice `W(t, ·)` is axisymmetric without swirl
(`Statement.IsAxisymmetricNoSwirl`: a.e. invariance for each `g ∈ 𝒪` separately), then
`W(t, y) = A_r(t, ϱ, y₃) e_r(y) + A_z(t, ϱ, y₃) e_z` for `μ ⊗ dy`-a.e. `(t, y)`, with the
angular averages `A_r = avgR W` of `W·e_r` and `A_z = avgZ W` of `W_z`. -/
theorem ae_eq_avgLift {μ : Measure T} [SFinite μ] {W : T × Space → Space} (hW : Measurable W)
    (hsym : ∀ᵐ t ∂μ, IsAxisymmetricNoSwirl fun y => W (t, y)) :
    W =ᵐ[μ.prod volume] fun x => avgR W (x.1, mer x.2) • eR x.2 + avgZ W (x.1, mer x.2) • e3 := by
  have hR : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, radC W (x.1, rotZ θ x.2) = radC W x := by
    intro θ
    filter_upwards [ae_map_comm hW hsym (fixesAxis_rotZ θ)] with x hx
    simp only [radC]
    rw [hx, eR_map (fixesAxis_rotZ θ), LinearIsometryEquiv.inner_map_map]
  have hZ : ∀ θ : ℝ, ∀ᵐ x ∂μ.prod volume, axC W (x.1, rotZ θ x.2) = axC W x := by
    intro θ
    filter_upwards [ae_map_comm hW hsym (fixesAxis_rotZ θ)] with x hx
    simp only [axC]
    rw [hx, apply_two_map (fixesAxis_rotZ θ)]
  filter_upwards [ae_eq_angAvg (measurable_radC hW) hR, ae_eq_angAvg (measurable_axC hW) hZ,
    ae_aziC_eq_zero hW hsym, Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis]
    with x h1 h2 h3 h4
  simp only [avgR, avgZ]
  rw [← h1, ← h2]
  conv_lhs => rw [eq_frame_decomp h4 (W x)]
  simp only [aziC] at h3
  rw [h3, zero_smul, add_zero]
  rfl

end UnforcedLeray.Axi
