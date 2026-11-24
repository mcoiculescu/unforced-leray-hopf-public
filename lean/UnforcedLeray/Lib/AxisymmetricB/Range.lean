import UnforcedLeray.Lib.AxisymmetricB.Jv
import UnforcedLeray.Lib.AxisymmetricB.Stream

/-!
# AX04 (range, one inclusion): the image of `J_v` is axisymmetric, without swirl, `P`-periodic


§5 Layer 3, target AX04 (`range_Jv`), the inclusion `range J_v ⊆ {U | U(τ) ∈ 𝒪-invariant}`.
Blueprint units served: B0417 (`eq:m4-free-spaces`, tex 7272–7297: `J_v` unitary "onto the
axisymmetric-no-swirl subspace" of the period-averaged `Y₂`), B0482 (tex 7920–7949: azimuthal
velocity vanishes), B1005 (`eq:st18-t00770`, tex 13693–13701: zero azimuthal component,
`P`-periodic in `τ`).

* `Nv_eq_liftMer`: `N_v b(τ, ·)` is the meridional lift of `√(R²/ρ²) b(merChart R τ ·)`;
* `isAxisymmetricNoSwirl_Nv`: every slice of a ring lift is 𝒪-invariant (pointwise);
* `Jv_mem_axisymmetric`: `J_v b` has a representative whose every phase slice is axisymmetric
  without swirl and which is `P`-periodic in `τ`.

The reverse inclusion (every such element of the phase space is a lift) and `JvEquiv` are not
built here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- The ring lift at phase time `τ` is the meridional lift of `√(R²/ρ²) b(merChart R τ ·)`. -/
theorem Nv_eq_liftMer (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) :
    Nv R b τ = liftMer (fun p => √(R ^ 2 / p.1 ^ 2) • b (merChart R τ p)) := by
  funext y
  rw [Nv, liftMer_eq_frameL, map_smul, chart_eq_merChart]
  rfl

/-- Every slice of a ring lift is axisymmetric without swirl (B0482, tex 7920–7949), in the
sense of `Statement.IsAxisymmetricNoSwirl`. -/
theorem isAxisymmetricNoSwirl_Nv (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) :
    IsAxisymmetricNoSwirl (Nv R b τ) := by
  rw [Nv_eq_liftMer]
  exact isAxisymmetricNoSwirl_liftMer _

theorem liftFun_slice_eq (R c : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) :
    (fun y => liftFun R c b (τ, y)) =
      liftMer (fun p => (√π * R)⁻¹ • (√(R ^ 2 / p.1 ^ 2) • perExt c b (merChart R τ p))) := by
  funext y
  simp only [liftFun]
  rw [Nv_eq_liftMer, liftMer_eq_frameL, liftMer_eq_frameL]
  simp only [map_smul]

theorem isAxisymmetricNoSwirl_liftFun (R c : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) :
    IsAxisymmetricNoSwirl (fun y => liftFun R c b (τ, y)) := by
  rw [liftFun_slice_eq]
  exact isAxisymmetricNoSwirl_liftMer _

theorem liftFun_add_period {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) (y : Space) :
    liftFun R c b (τ + P, y) = liftFun R c b (τ, y) := by
  simp only [liftFun]
  rw [Nv_dss hR.ne' hP (perExt_periodic hc.ne' b) τ]

/-- **AX04 `range_Jv`, inclusion `⊆`** (B0417, tex 7276–7280; B1005, tex 13693–13701). Every
`J_v b` has a representative that is `P`-periodic in `τ` and whose phase slices are all
axisymmetric without swirl. -/
theorem Jv_mem_axisymmetric {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Lp Merid 2 (ageμ c (-3 / 2))) :
    ∃ U : ℝ × Space → Space, ⇑(Jv hR hc hP b) =ᵐ[phaseμ P] U ∧
      (∀ τ, IsAxisymmetricNoSwirl (fun y => U (τ, y))) ∧ ∀ τ y, U (τ + P, y) = U (τ, y) :=
  ⟨liftFun R c b, coeFn_Jv hR hc hP b, isAxisymmetricNoSwirl_liftFun R c b,
    liftFun_add_period hR hc hP b⟩

end UnforcedLeray.Axi
