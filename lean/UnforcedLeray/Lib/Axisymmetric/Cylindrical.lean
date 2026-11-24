import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
import UnforcedLeray.Statement

/-!
# AX01: cylindrical frame and the meridional lift on `ℝ³`


§5 Layer 3, target AX01 (`Axi/Cylindrical.lean`); Wave 1 block 1E of
`scoping/README.md`. Blueprint units served: B0184 (`eq:st18-t00187`, tex 2837–2850),
B0185 (`eq:st18-t00188/189`, tex 2851–2865), B0186 (`eq:m3-ring-lift`, tex 2070–2098),
B0226 (tex 3394–3402), B0485 (tex 7981–8002).

Physical space is the library's `Space = EuclideanSpace ℝ (Fin 3)` (`UnforcedLeray.Statement`).
For `y ∈ Space` we write `ϱ y = √(y₀² + y₁²)` for the distance to the axis
`{y₀ = y₁ = 0}`, `e_r = ϱ⁻¹ (y₀, y₁, 0)`, `e_φ = ϱ⁻¹ (−y₁, y₀, 0)` and `e_z = e₃`.
A meridional profile `b : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)`, `b(ρ, z) = (b_r, b_z)`, lifts
to the axisymmetric field without swirl `liftMer b = b_r(ϱ, y₃) e_r + b_z(ϱ, y₃) e_z`
(tex 2073–2077: `U_raw = √s [v₁ e_r + (v₂ + εH) e_z]` is of this form).

Junk values. On the axis `ϱ = 0`, and Lean's `0⁻¹ = 0` makes `e_r = e_φ = 0` there; every
differential identity below is stated off the axis (`y ∉ axis`), where the frame is the
manuscript's. The equivariance `isAxisymmetricNoSwirl_liftMer` holds at every point,
including the axis. Meridional vectors use `EuclideanSpace ℝ (Fin 2)` (Euclidean norm),
not `ℝ × ℝ` (sup norm); the profile domain `ℝ × ℝ` carries no norm in any statement.

Main results:
* `isAxisymmetricNoSwirl_liftMer`: the lift is 𝒪-invariant (tex 112–116), pointwise;
* `contDiffOn_liftMer`: `C^k` profiles on `{ρ > 0}` give `C^k` fields off the axis;
* `hasFDerivAt_liftMer`, `fderiv_liftMer_apply`: the full derivative off the axis;
* `divergence_liftMer`: `div (b_r e_r + b_z e_z) = ∂_ρ b_r + b_r/ρ + ∂_z b_z`;
* `curl_liftMer`: `curl (b_r e_r + b_z e_z) = (∂_z b_r − ∂_ρ b_z) e_φ`;
* `advection_liftMer`: `(u·∇)w` for two lifts is the lift of `u_r ∂_ρ w + u_z ∂_z w`
  (no hoop term without swirl);
* `norm_liftMer`: `‖liftMer b y‖ = ‖b(ϱ y, y₃)‖` off the axis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- Meridional vectors `(v_r, v_z)`, with the Euclidean norm. -/
abbrev Merid := EuclideanSpace ℝ (Fin 2)

/-- The axial unit vector `e_z = e₃`. -/
abbrev e3 : Space := coordinateVector 2

/-- Distance to the axis, `ϱ(y) = √(y₀² + y₁²)`. -/
def ϱ (y : Space) : ℝ := √(y 0 ^ 2 + y 1 ^ 2)

/-- The symmetry axis `{y₀ = y₁ = 0}`. -/
def axis : Set Space := {y | y 0 = 0 ∧ y 1 = 0}

/-- Horizontal part `(y₀, y₁, 0)` of `y`. -/
def hor (y : Space) : Space := !₂[y 0, y 1, 0]

/-- The radial unit vector `e_r = ϱ⁻¹ (y₀, y₁, 0)`; its Lean value on the axis is `0`. -/
def eR (y : Space) : Space := (ϱ y)⁻¹ • hor y

/-- The azimuthal unit vector `e_φ = ϱ⁻¹ (−y₁, y₀, 0)`; its Lean value on the axis is `0`. -/
def eΦ (y : Space) : Space := (ϱ y)⁻¹ • !₂[-y 1, y 0, 0]

/-- The meridional coordinates `(ρ, z) = (ϱ(y), y₃)` of `y`. -/
def mer (y : Space) : ℝ × ℝ := (ϱ y, y 2)

/-- The meridional lift `b ↦ b_r(ϱ, y₃) e_r + b_z(ϱ, y₃) e_z` (tex 2073–2077, 3294–3295). -/
def liftMer (b : ℝ × ℝ → Merid) (y : Space) : Space :=
  (b (mer y)) 0 • eR y + (b (mer y)) 1 • e3

/-- Profile partial derivative `∂_ρ b = Db(p)(1, 0)`. -/
def dρ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (b : ℝ × ℝ → F) (p : ℝ × ℝ) : F :=
  fderiv ℝ b p (1, 0)

/-- Profile partial derivative `∂_z b = Db(p)(0, 1)`. -/
def dz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (b : ℝ × ℝ → F) (p : ℝ × ℝ) : F :=
  fderiv ℝ b p (0, 1)

/-- Cartesian divergence `∑ᵢ ∂ᵢ fᵢ` (the convention of `Statement.spatialDivergence`). -/
def divergence (f : Space → Space) (y : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ f y (coordinateVector i)) i

/-- Cartesian partial derivative `∂ᵢ fⱼ`. -/
def pd (f : Space → Space) (i j : Fin 3) (y : Space) : ℝ :=
  (fderiv ℝ f y (coordinateVector i)) j

/-- Cartesian curl `(∂₁f₂ − ∂₂f₁, ∂₂f₀ − ∂₀f₂, ∂₀f₁ − ∂₁f₀)`. -/
def curl (f : Space → Space) (y : Space) : Space :=
  !₂[pd f 1 2 y - pd f 2 1 y, pd f 2 0 y - pd f 0 2 y, pd f 0 1 y - pd f 1 0 y]

/-- Advection `(u·∇)w (y) = Dw(y) u(y)`. -/
def advection (u w : Space → Space) (y : Space) : Space := fderiv ℝ w y (u y)

/-! ### Coordinates -/

@[simp] theorem e3_apply (i : Fin 3) : e3 i = if i = 2 then 1 else 0 := by
  simp only [e3, coordinateVector, PiLp.single_apply]

@[simp] theorem hor_apply_zero (y : Space) : hor y 0 = y 0 := rfl
@[simp] theorem hor_apply_one (y : Space) : hor y 1 = y 1 := rfl
@[simp] theorem hor_apply_two (y : Space) : hor y 2 = 0 := rfl

theorem hor_eq (y : Space) : hor y = y - y 2 • e3 := by
  ext i
  fin_cases i <;> simp [hor]

@[simp] theorem eR_apply_zero (y : Space) : eR y 0 = y 0 / ϱ y := by
  simp [eR, div_eq_inv_mul]
@[simp] theorem eR_apply_one (y : Space) : eR y 1 = y 1 / ϱ y := by
  simp [eR, div_eq_inv_mul]
@[simp] theorem eR_apply_two (y : Space) : eR y 2 = 0 := by
  simp [eR]

@[simp] theorem eΦ_apply_zero (y : Space) : eΦ y 0 = -y 1 / ϱ y := by
  simp [eΦ, div_eq_inv_mul]
@[simp] theorem eΦ_apply_one (y : Space) : eΦ y 1 = y 0 / ϱ y := by
  simp [eΦ, div_eq_inv_mul]
@[simp] theorem eΦ_apply_two (y : Space) : eΦ y 2 = 0 := by
  simp [eΦ]

theorem ϱ_nonneg (y : Space) : 0 ≤ ϱ y := Real.sqrt_nonneg _

theorem ϱ_sq (y : Space) : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)

theorem mem_axis_iff (y : Space) : y ∈ axis ↔ ϱ y = 0 := by
  constructor
  · rintro ⟨h0, h1⟩
    simp [ϱ, h0, h1]
  · intro h
    have h2 : y 0 ^ 2 + y 1 ^ 2 = 0 := by rw [← ϱ_sq, h]; ring
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact ⟨h0, h1⟩

theorem ϱ_pos {y : Space} (hy : y ∉ axis) : 0 < ϱ y :=
  lt_of_le_of_ne (ϱ_nonneg y) (fun h => hy ((mem_axis_iff y).2 h.symm))

theorem ϱ_ne_zero {y : Space} (hy : y ∉ axis) : ϱ y ≠ 0 := (ϱ_pos hy).ne'

theorem continuous_ϱ : Continuous ϱ := by
  unfold ϱ
  fun_prop

theorem isClosed_axis : IsClosed axis := by
  have : axis = ϱ ⁻¹' {0} := by
    ext y
    simp [mem_axis_iff]
  rw [this]
  exact isClosed_singleton.preimage continuous_ϱ

theorem isOpen_compl_axis : IsOpen axisᶜ := isClosed_axis.isOpen_compl

theorem norm_sq_eq_ϱ_sq_add (y : Space) : ‖y‖ ^ 2 = ϱ y ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, ϱ_sq]

/-- The frame `(e_r, e_z)` is orthonormal off the axis. -/
theorem norm_eR {y : Space} (hy : y ∉ axis) : ‖eR y‖ = 1 := by
  have hρ := ϱ_pos hy
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three]
  simp only [eR_apply_zero, eR_apply_one, eR_apply_two]
  field_simp
  rw [ϱ_sq]
  ring

theorem inner_eR_e3 (y : Space) : inner ℝ (eR y) e3 = 0 := by
  simp [PiLp.inner_apply]

theorem inner_eR_eΦ (y : Space) : inner ℝ (eR y) (eΦ y) = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, eR_apply_zero, eR_apply_one, eR_apply_two,
    eΦ_apply_zero, eΦ_apply_one, eΦ_apply_two, RCLike.inner_apply, conj_trivial]
  ring

/-- The horizontal part is `ϱ e_r`. -/
theorem hor_eq_smul_eR {y : Space} (hy : y ∉ axis) : hor y = ϱ y • eR y := by
  rw [eR, smul_smul, mul_inv_cancel₀ (ϱ_ne_zero hy), one_smul]

/-- `y = ϱ e_r + y₃ e_z`. -/
theorem eq_ϱ_eR_add {y : Space} (hy : y ∉ axis) : y = ϱ y • eR y + y 2 • e3 := by
  rw [← hor_eq_smul_eR hy, hor_eq, sub_add_cancel]

theorem coordinateVector_apply (i j : Fin 3) :
    coordinateVector i j = if j = i then 1 else 0 := by
  simp only [coordinateVector, PiLp.single_apply]

/-- `(y₀/ϱ)² + (y₁/ϱ)² = 1` off the axis. -/
theorem eR_sq_sum {y : Space} (hy : y ∉ axis) : (y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 = 1 := by
  rw [div_pow, div_pow, ← add_div, ← ϱ_sq, div_self (pow_ne_zero 2 (ϱ_ne_zero hy))]

/-! ### Equivariance under the group 𝒪 (tex 112–116) -/

theorem inner_e3_left (v : Space) : inner ℝ e3 v = v 2 := by
  simp [e3, coordinateVector, EuclideanSpace.inner_single_left]

section Equivariance

variable (g : Space ≃ₗᵢ[ℝ] Space)

theorem symm_apply_two (hg : FixesAxis g) (x : Space) : (g.symm x) 2 = x 2 := by
  rw [← inner_e3_left, ← inner_e3_left]
  calc inner ℝ e3 (g.symm x) = inner ℝ (g e3) (g (g.symm x)) := (g.inner_map_map _ _).symm
    _ = inner ℝ e3 x := by
      rw [show g e3 = e3 from hg, g.apply_symm_apply]

theorem ϱ_symm_apply (hg : FixesAxis g) (x : Space) : ϱ (g.symm x) = ϱ x := by
  have h1 := norm_sq_eq_ϱ_sq_add (g.symm x)
  have h2 := norm_sq_eq_ϱ_sq_add x
  rw [LinearIsometryEquiv.norm_map, symm_apply_two g hg] at h1
  have h3 : ϱ (g.symm x) ^ 2 = ϱ x ^ 2 := by linarith
  exact (sq_eq_sq₀ (ϱ_nonneg _) (ϱ_nonneg _)).1 h3

theorem mer_symm_apply (hg : FixesAxis g) (x : Space) : mer (g.symm x) = mer x := by
  simp only [mer, ϱ_symm_apply g hg, symm_apply_two g hg]

theorem map_hor_symm (hg : FixesAxis g) (x : Space) : g (hor (g.symm x)) = hor x := by
  rw [hor_eq, hor_eq, map_sub, map_smul, g.apply_symm_apply, symm_apply_two g hg,
    show g e3 = e3 from hg]

theorem map_eR_symm (hg : FixesAxis g) (x : Space) : g (eR (g.symm x)) = eR x := by
  rw [eR, map_smul, map_hor_symm g hg, ϱ_symm_apply g hg, eR]

/-- Pointwise 𝒪-equivariance of the lift: `g (liftMer b (g⁻¹ x)) = liftMer b x`. -/
theorem liftMer_equivariant (b : ℝ × ℝ → Merid) (hg : FixesAxis g) (x : Space) :
    g (liftMer b (g.symm x)) = liftMer b x := by
  rw [liftMer, map_add, map_smul, map_smul, mer_symm_apply g hg, map_eR_symm g hg,
    show g e3 = e3 from hg, liftMer]

end Equivariance

/-- **AX01 `isAxisymmetricNoSwirl_liftMer`.** Every meridional lift is axisymmetric without
swirl in the sense of `Statement.IsAxisymmetricNoSwirl` (𝒪-invariance, tex 112–116); the
invariance even holds at every point. -/
theorem isAxisymmetricNoSwirl_liftMer (b : ℝ × ℝ → Merid) :
    IsAxisymmetricNoSwirl (liftMer b) := fun g hg =>
  ae_of_all _ fun x => liftMer_equivariant g b hg x

/-! ### Smoothness off the axis -/

theorem contDiffOn_ϱ {k : WithTop ℕ∞} : ContDiffOn ℝ k ϱ axisᶜ := by
  have hsq : ContDiff ℝ k (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  exact hsq.contDiffOn.sqrt fun y hy => by
    rw [← ϱ_sq]; exact pow_ne_zero 2 (ϱ_ne_zero hy)

theorem contDiff_hor {k : WithTop ℕ∞} : ContDiff ℝ k hor := by
  have h : hor = fun y : Space => y - y 2 • e3 := funext hor_eq
  rw [h]
  have h2 : ContDiff ℝ k (fun y : Space => y 2) := by fun_prop
  exact contDiff_id.sub (h2.smul contDiff_const)

theorem contDiffOn_eR {k : WithTop ℕ∞} : ContDiffOn ℝ k eR axisᶜ :=
  (contDiffOn_ϱ.inv fun _ hy => ϱ_ne_zero hy).smul contDiff_hor.contDiffOn

theorem contDiffOn_mer {k : WithTop ℕ∞} : ContDiffOn ℝ k mer axisᶜ := by
  have h2 : ContDiff ℝ k (fun y : Space => y 2) := by fun_prop
  exact contDiffOn_ϱ.prodMk h2.contDiffOn

theorem mapsTo_mer : MapsTo mer axisᶜ (Ioi 0 ×ˢ univ) := fun _ hy => ⟨ϱ_pos hy, trivial⟩

/-- **AX01 `contDiffOn_liftMer`.** A profile of class `C^k` on `{ρ > 0}` lifts to a field of
class `C^k` off the axis. -/
theorem contDiffOn_liftMer {k : WithTop ℕ∞} {b : ℝ × ℝ → Merid}
    (hb : ContDiffOn ℝ k b (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ k (liftMer b) axisᶜ := by
  have hbm : ContDiffOn ℝ k (fun y => b (mer y)) axisᶜ := hb.comp contDiffOn_mer mapsTo_mer
  have hb0 : ContDiffOn ℝ k (fun y => b (mer y) 0) axisᶜ :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbm
  have hb1 : ContDiffOn ℝ k (fun y => b (mer y) 1) axisᶜ :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbm
  exact (hb0.smul contDiffOn_eR).add (hb1.smul contDiffOn_const)

/-! ### First derivatives off the axis -/

/-- `Dϱ(y) v = (y₀ v₀ + y₁ v₁)/ϱ = ⟪e_r, v⟫`. -/
def ϱD (y : Space) : Space →L[ℝ] ℝ :=
  (ϱ y)⁻¹ • (y 0 • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) +
    y 1 • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ))

theorem ϱD_apply (y v : Space) : ϱD y v = (y 0 * v 0 + y 1 * v 1) / ϱ y := by
  simp only [ϱD, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]
  ring

theorem hasFDerivAt_ϱ {y : Space} (hy : y ∉ axis) : HasFDerivAt ϱ (ϱD y) y := by
  have h0 : HasFDerivAt (fun x : Space => x 0)
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun x : Space => x 1)
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hne : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    rw [← ϱ_sq]; exact pow_ne_zero 2 (ϱ_ne_zero hy)
  have h := ((h0.pow 2).add (h1.pow 2)).sqrt hne
  have hρ : √(y 0 ^ 2 + y 1 ^ 2) = ϱ y := rfl
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hρ0 := ϱ_ne_zero hy
  rw [ϱD_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, Pi.add_apply, hρ, nsmul_eq_mul]
  field_simp
  ring

/-- The meridional chart `y ↦ (ϱ, y₃)` and its derivative `v ↦ (⟪e_r, v⟫, v₃)`. -/
def merD (y : Space) : Space →L[ℝ] ℝ × ℝ :=
  (ϱD y).prod (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)

theorem merD_apply (y v : Space) : merD y v = (ϱD y v, v 2) := rfl

theorem hasFDerivAt_mer {y : Space} (hy : y ∉ axis) : HasFDerivAt mer (merD y) y :=
  (hasFDerivAt_ϱ hy).prodMk (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt

/-- The horizontal projection as a continuous linear map. -/
def horL : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space -
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight e3

theorem horL_apply (v : Space) : horL v = hor v := by
  rw [hor_eq]
  simp [horL]

/-- `De_r(y) v = ϱ⁻¹ (hor v − ⟪e_r, v⟫ e_r)`. -/
def eRD (y : Space) : Space →L[ℝ] Space :=
  (ϱ y)⁻¹ • (horL - (ϱD y).smulRight (eR y))

theorem eRD_apply (y v : Space) : eRD y v = (ϱ y)⁻¹ • (hor v - ϱD y v • eR y) := by
  simp [eRD, horL_apply]

theorem eRD_apply_coord (y v : Space) (j : Fin 3) :
    eRD y v j = (ϱ y)⁻¹ * (hor v j - ϱD y v * eR y j) := by
  rw [eRD_apply]
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

theorem hasFDerivAt_eR {y : Space} (hy : y ∉ axis) : HasFDerivAt eR (eRD y) y := by
  have hρ0 := ϱ_ne_zero hy
  have hinv : HasFDerivAt (fun x => (ϱ x)⁻¹) ((-(ϱ y ^ 2)⁻¹) • ϱD y) y :=
    (hasDerivAt_inv hρ0).comp_hasFDerivAt y (hasFDerivAt_ϱ hy)
  have hhor : HasFDerivAt hor horL y := by
    have h : hor = fun x => horL x := funext fun x => (horL_apply x).symm
    rw [h]
    exact horL.hasFDerivAt
  have h := hinv.fun_smul hhor
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  ext j
  rw [eRD_apply_coord]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    horL_apply, eR, ϱD_apply]
  field_simp
  ring

/-- The derivative of the lift off the axis. -/
def liftMerD (b : ℝ × ℝ → Merid) (y : Space) : Space →L[ℝ] Space :=
  (b (mer y) 0) • eRD y +
    ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).comp
      ((fderiv ℝ b (mer y)).comp (merD y))).smulRight (eR y) +
    ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).comp
      ((fderiv ℝ b (mer y)).comp (merD y))).smulRight e3

theorem hasFDerivAt_liftMer {b : ℝ × ℝ → Merid} {y : Space} (hy : y ∉ axis)
    (hb : DifferentiableAt ℝ b (mer y)) : HasFDerivAt (liftMer b) (liftMerD b y) y := by
  have hbm : HasFDerivAt (fun x => b (mer x)) ((fderiv ℝ b (mer y)).comp (merD y)) y :=
    hb.hasFDerivAt.comp y (hasFDerivAt_mer hy)
  have hb0 := (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hbm
  have hb1 := (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hbm
  have h := (hb0.fun_smul (hasFDerivAt_eR hy)).add (hb1.fun_smul (hasFDerivAt_const e3 y))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [liftMerD]

/-- Linearity of a derivative on `ℝ × ℝ`: `L(a, c) = a L(1,0) + c L(0,1)`. -/
theorem clm_pair {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℝ × ℝ →L[ℝ] F)
    (a c : ℝ) : L (a, c) = a • L (1, 0) + c • L (0, 1) := by
  have h : ((a, c) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (1 : ℝ)) := by simp
  rw [h, map_add, map_smul, map_smul]

/-- Components of the derivative of the lift:
`D(liftMer b)(y) v = b_r De_r(v) + (⟪e_r,v⟫ ∂_ρ b_r + v₃ ∂_z b_r) e_r
+ (⟪e_r,v⟫ ∂_ρ b_z + v₃ ∂_z b_z) e_z`. -/
theorem liftMerD_apply_coord (b : ℝ × ℝ → Merid) (y v : Space) (j : Fin 3) :
    liftMerD b y v j = b (mer y) 0 * eRD y v j +
      (ϱD y v * dρ b (mer y) 0 + v 2 * dz b (mer y) 0) * eR y j +
      (ϱD y v * dρ b (mer y) 1 + v 2 * dz b (mer y) 1) * e3 j := by
  simp only [liftMerD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, merD_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.coe_proj]
  rw [clm_pair (fderiv ℝ b (mer y)) (ϱD y v) (v 2)]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, dρ, dz]

theorem fderiv_liftMer_coord {b : ℝ × ℝ → Merid} {y : Space} (hy : y ∉ axis)
    (hb : DifferentiableAt ℝ b (mer y)) (v : Space) (j : Fin 3) :
    fderiv ℝ (liftMer b) y v j = b (mer y) 0 * eRD y v j +
      (ϱD y v * dρ b (mer y) 0 + v 2 * dz b (mer y) 0) * eR y j +
      (ϱD y v * dρ b (mer y) 1 + v 2 * dz b (mer y) 1) * e3 j := by
  rw [(hasFDerivAt_liftMer hy hb).fderiv, liftMerD_apply_coord]

/-- **AX01 `divergence_liftMer`** (B0185, tex 2851–2865; B0226, tex 3394–3402). Off the axis,
`div (b_r e_r + b_z e_z) = ∂_ρ b_r + b_r/ρ + ∂_z b_z` at `(ρ, z) = (ϱ y, y₃)`, for a profile
differentiable there. -/
theorem divergence_liftMer {b : ℝ × ℝ → Merid} {y : Space} (hy : y ∉ axis)
    (hb : DifferentiableAt ℝ b (mer y)) :
    divergence (liftMer b) y =
      dρ b (mer y) 0 + b (mer y) 0 / ϱ y + dz b (mer y) 1 := by
  have hac := eR_sq_sum hy
  simp only [divergence, Fin.sum_univ_three, fderiv_liftMer_coord hy hb, eRD_apply_coord,
    ϱD_apply, hor_apply_zero, hor_apply_one, hor_apply_two, eR_apply_zero, eR_apply_one,
    eR_apply_two, e3_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true,
    ite_false, ↓reduceIte]
  linear_combination (dρ b (mer y) 0 - b (mer y) 0 / ϱ y) * hac

/-- **AX01 `curl_liftMer`** (B0485, tex 7981–8002). Off the axis,
`curl (b_r e_r + b_z e_z) = (∂_z b_r − ∂_ρ b_z) e_φ`. -/
theorem curl_liftMer {b : ℝ × ℝ → Merid} {y : Space} (hy : y ∉ axis)
    (hb : DifferentiableAt ℝ b (mer y)) :
    curl (liftMer b) y = (dz b (mer y) 0 - dρ b (mer y) 1) • eΦ y := by
  ext i
  fin_cases i <;>
  · simp only [curl, pd, fderiv_liftMer_coord hy hb, eRD_apply_coord,
      ϱD_apply, hor_apply_zero, hor_apply_one, hor_apply_two, eR_apply_zero, eR_apply_one,
      eR_apply_two, e3_apply, coordinateVector_apply, Fin.isValue, Fin.reduceEq, ite_true,
      ite_false, ↓reduceIte, PiLp.smul_apply, smul_eq_mul, eΦ_apply_zero, eΦ_apply_one,
      eΦ_apply_two, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp
    ring

/-- The meridional advection `u_r ∂_ρ w + u_z ∂_z w` of profiles. -/
def merAdv (b d : ℝ × ℝ → Merid) (p : ℝ × ℝ) : Merid :=
  b p 0 • dρ d p + b p 1 • dz d p

/-- **AX01 `advection_liftMer`.** Off the axis, `(u·∇)w` for the lifts `u = liftMer b`,
`w = liftMer d` is the lift of `u_r ∂_ρ w + u_z ∂_z w`. Without swirl there is no hoop
term: the frame derivative `De_r(u) = ϱ⁻¹(hor u − ⟪e_r,u⟫ e_r)` vanishes for meridional `u`. -/
theorem advection_liftMer (b : ℝ × ℝ → Merid) {d : ℝ × ℝ → Merid} {y : Space}
    (hy : y ∉ axis) (hd : DifferentiableAt ℝ d (mer y)) :
    advection (liftMer b) (liftMer d) y = liftMer (merAdv b d) y := by
  have hac := eR_sq_sum hy
  ext j
  rw [advection, fderiv_liftMer_coord hy hd, eRD_apply_coord]
  fin_cases j <;>
  · simp only [liftMer, merAdv, ϱD_apply, hor_apply_zero, hor_apply_one, hor_apply_two,
      eR_apply_zero, eR_apply_one, eR_apply_two, e3_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Fin.isValue, Fin.reduceEq, ite_true, ite_false, ↓reduceIte,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    first
    | linear_combination (b (mer y) 0 * (y 0 / ϱ y) *
        (dρ d (mer y) 0 - d (mer y) 0 / ϱ y)) * hac
    | linear_combination (b (mer y) 0 * (y 1 / ϱ y) *
        (dρ d (mer y) 0 - d (mer y) 0 / ϱ y)) * hac
    | linear_combination (b (mer y) 0 * dρ d (mer y) 1) * hac

/-- **AX01 `norm_liftMer`.** Off the axis the lift preserves the Euclidean norm:
`‖liftMer b y‖ = ‖b(ϱ y, y₃)‖`. -/
theorem norm_liftMer (b : ℝ × ℝ → Merid) {y : Space} (hy : y ∉ axis) :
    ‖liftMer b y‖ = ‖b (mer y)‖ := by
  have hac := eR_sq_sum hy
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [liftMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, eR_apply_zero,
    eR_apply_one, eR_apply_two, e3_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    ↓reduceIte]
  linear_combination (b (mer y) 0) ^ 2 * hac

end UnforcedLeray.Axi
