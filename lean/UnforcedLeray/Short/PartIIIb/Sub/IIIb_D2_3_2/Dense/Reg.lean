import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3
import UnforcedLeray.Lib.Axisymmetric.Measure

/-!
# The regularized Ward fields (source 4161-4186, 4271-4282)

Source of record: `the November 2 reference manuscript`.

**Axis junk of the raw fields.**  In Lean `age R y = R²/ϱ² = 0` on the axis, so the young cutoff
`χ_y(ν·age) = χ_y(0) = 1` there and `wardX = 𝒞_y X₀` equals `X₀` on the axis, whereas for
`0 < ϱ ≤ R√ν` (`ν·age ≥ 1`) it vanishes (`wardX_eq_zero_of_sq_le`): `wardX` is discontinuous at
the axis and the `fderiv`s inside `wardY`, `wardH`, `wardE` are junk there.  The source defines
the cutoff field "by zero where `χ_y = 0`" (4182-4183), in particular on the axis.

`wardXr` is that field: `wardX` off the axis, `0` on it.  `wardYr`, `wardHr`, `wardEr` are
`Y = D_{μ+1}X`, `h = [U, X]` and the residual `Ẽ_μ` (4171-4173, 4276-4282) of `X = wardXr`, by the
formulas of `wardY`, `wardH`, `wardE`.  The axis is closed, so the regularized and the raw fields
agree off the axis with all their derivatives (`wardYr_eq_of_not_mem`, `wardHr_eq_of_not_mem`,
`wardEr_eq_of_not_mem`), and their chart coefficients agree everywhere (`coefOf_congr_offAxis`:
`coefOf R F` reads `F` at `chartY R p`, which is off the axis for `s > 0`, and is `0` for `s ≤ 0`).
The phase pairings see the fields only off the axis (`pairF_congr_offAxis'`,
`stressPair_congr_offAxis`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## 1. The regularized fields -/

/-- The regularized Ward displacement `X = 𝒞_yX₀` (source 4171, 4180-4186): `wardX` off the axis
and `0` on it (the source's "define it by zero where `χ_y = 0`", 4182-4183). -/
def wardXr (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) : Space → Space :=
  axisᶜ.indicator (wardX ν μ R c χy g τ)

/-- `Y = D_{μ+1}X` of the regularized displacement (source 4171). -/
def wardYr (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) : ℝ → Space → Space :=
  physDmu ν (μ + 1) (wardXr ν μ R c χy g)

/-- `h = [U, X] = U·∇X - X·∇U` of the regularized displacement (source 4171-4173). -/
def wardHr (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (g : Chart → Ten3) (τ : ℝ)
    (y : Space) : Space :=
  fderiv ℝ (wardXr ν μ R c χy g τ) y (U τ y) - fderiv ℝ (U τ) y (wardXr ν μ R c χy g τ y)

/-- The full unprojected residual `Ẽ_μ = 2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX + DXᵀ)∇p` of the
regularized displacement (source 4276-4282). -/
def wardEr (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  (2 : ℝ) • fderiv ℝ (wardYr ν μ R c χy g τ) y (U τ y) -
      (2 * ν) • physCdiff (U τ) (wardXr ν μ R c χy g τ) y +
    physUUD2 (U τ) (wardXr ν μ R c χy g τ) y - physDXp (wardXr ν μ R c χy g τ) (p τ) y

/-! ## 2. Local operators only see a neighbourhood -/

section Local

variable {f₁ f₂ : Space → Space} {y : Space}

theorem physPd_congr_nhds (h : f₁ =ᶠ[𝓝 y] f₂) (j : Fin 3) : physPd f₁ j y = physPd f₂ j y := by
  unfold physPd
  rw [h.fderiv_eq]

theorem physPd_eventuallyEq (h : f₁ =ᶠ[𝓝 y] f₂) (j : Fin 3) :
    (fun y' => physPd f₁ j y') =ᶠ[𝓝 y] fun y' => physPd f₂ j y' := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y' hy'
  unfold physPd
  rw [hy']

theorem physPd2_congr_nhds (h : f₁ =ᶠ[𝓝 y] f₂) (j l : Fin 3) :
    physPd2 f₁ j l y = physPd2 f₂ j l y := by
  unfold physPd2
  exact physPd_congr_nhds (physPd_eventuallyEq h l) j

theorem physLap_congr_nhds (h : f₁ =ᶠ[𝓝 y] f₂) : physLap f₁ y = physLap f₂ y := by
  unfold physLap
  simp only [physPd2_congr_nhds h]

theorem physCdiff_congr_nhds (U : Space → Space) (h : f₁ =ᶠ[𝓝 y] f₂) :
    physCdiff U f₁ y = physCdiff U f₂ y := by
  unfold physCdiff
  simp only [physPd_congr_nhds h, physPd2_congr_nhds h]

theorem physUUD2_congr_nhds (U : Space → Space) (h : f₁ =ᶠ[𝓝 y] f₂) :
    physUUD2 U f₁ y = physUUD2 U f₂ y := by
  unfold physUUD2
  simp only [physPd2_congr_nhds h]

theorem physDXp_congr_nhds (q : Space → ℝ) (h : f₁ =ᶠ[𝓝 y] f₂) :
    physDXp f₁ q y = physDXp f₂ q y := by
  unfold physDXp
  simp only [physPd_congr_nhds h]

end Local

theorem physDmu_congr_nhds {ν μ : ℝ} {X₁ X₂ : ℝ → Space → Space} {y : Space}
    (h : ∀ t, X₁ t =ᶠ[𝓝 y] X₂ t) (τ : ℝ) : physDmu ν μ X₁ τ y = physDmu ν μ X₂ τ y := by
  unfold physDmu
  have h0 : (fun t => X₁ t y) = fun t => X₂ t y := funext fun t => (h t).eq_of_nhds
  rw [h0, (h τ).fderiv_eq, physLap_congr_nhds (h τ), (h τ).eq_of_nhds]

/-! ## 3. Regularized = raw off the axis -/

section Agree

variable (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3)

theorem wardXr_of_not_mem (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    wardXr ν μ R c χy g τ y = wardX ν μ R c χy g τ y :=
  Set.indicator_of_mem (show y ∈ axisᶜ from hy) _

theorem wardXr_of_mem (τ : ℝ) {y : Space} (hy : y ∈ axis) : wardXr ν μ R c χy g τ y = 0 :=
  Set.indicator_of_notMem (show y ∉ axisᶜ from fun h => h hy) _

theorem wardXr_eventuallyEq (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    wardXr ν μ R c χy g τ =ᶠ[𝓝 y] wardX ν μ R c χy g τ := by
  filter_upwards [isOpen_compl_axis.mem_nhds hy] with y' hy'
  exact Set.indicator_of_mem hy' _

theorem wardYr_eq_of_not_mem (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    wardYr ν μ R c χy g τ y = wardY ν μ R c χy g τ y :=
  physDmu_congr_nhds (fun t => wardXr_eventuallyEq ν μ R c χy g t hy) τ

theorem wardYr_eventuallyEq (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    wardYr ν μ R c χy g τ =ᶠ[𝓝 y] wardY ν μ R c χy g τ := by
  filter_upwards [isOpen_compl_axis.mem_nhds hy] with y' hy'
  exact wardYr_eq_of_not_mem ν μ R c χy g τ hy'

theorem wardHr_eq_of_not_mem (U : ℝ → SpatialField) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    wardHr ν μ R c χy U g τ y = wardH ν μ R c χy U g τ y := by
  unfold wardHr wardH
  rw [(wardXr_eventuallyEq ν μ R c χy g τ hy).fderiv_eq, wardXr_of_not_mem ν μ R c χy g τ hy]

theorem wardEr_eq_of_not_mem (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (τ : ℝ) {y : Space}
    (hy : y ∉ axis) : wardEr ν μ R c χy U p g τ y = wardE ν μ R c χy U p g τ y := by
  have hX := wardXr_eventuallyEq ν μ R c χy g τ hy
  unfold wardEr wardE
  rw [(wardYr_eventuallyEq ν μ R c χy g τ hy).fderiv_eq, physCdiff_congr_nhds _ hX,
    physUUD2_congr_nhds _ hX, physDXp_congr_nhds _ hX]

end Agree

/-! ## 4. Chart coefficients and pairings only see the fields off the axis -/

theorem chartY_not_mem_axis {R : ℝ} (hR : R ≠ 0) {p : Chart} (hp : 0 < p.1) :
    NearInst.chartY R p ∉ axis := by
  intro h
  have h0 : NearInst.chartY R p 0 = 0 := h.1
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  rw [h1, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hR h0
  · exact hs h0

/-- `coefOf R F` depends only on `F` off the axis (`R ≠ 0`). -/
theorem coefOf_congr_offAxis {R : ℝ} (hR : R ≠ 0) {F G : ℝ → Space → Space}
    (h : ∀ τ y, y ∉ axis → F τ y = G τ y) : coefOf R F = coefOf R G := by
  funext p
  unfold coefOf
  by_cases hp : 0 < p.1
  · rw [h _ _ (chartY_not_mem_axis hR hp)]
  · have h0 : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    simp [h0]

section Coef

variable {ν μ R c : ℝ} (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
  (g : Chart → Ten3)

theorem coefOf_wardH_reg (hR : R ≠ 0) :
    coefOf R (wardH ν μ R c χy U g) = coefOf R (wardHr ν μ R c χy U g) :=
  coefOf_congr_offAxis hR fun τ _ hy => (wardHr_eq_of_not_mem ν μ R c χy g U τ hy).symm

theorem coefOf_wardE_reg (hR : R ≠ 0) :
    coefOf R (wardE ν μ R c χy U p g) = coefOf R (wardEr ν μ R c χy U p g) :=
  coefOf_congr_offAxis hR fun τ _ hy => (wardEr_eq_of_not_mem ν μ R c χy g U p τ hy).symm

theorem coefOf_wardY_reg (hR : R ≠ 0) :
    coefOf R (wardY ν μ R c χy g) = coefOf R (wardYr ν μ R c χy g) :=
  coefOf_congr_offAxis hR fun τ _ hy => (wardYr_eq_of_not_mem ν μ R c χy g τ hy).symm

theorem coefOf_wardYH_reg (hR : R ≠ 0) :
    coefOf R (fun τ y => wardY ν μ R c χy g τ y + wardH ν μ R c χy U g τ y) =
      coefOf R (fun τ y => wardYr ν μ R c χy g τ y + wardHr ν μ R c χy U g τ y) :=
  coefOf_congr_offAxis hR fun τ _ hy => by
    rw [wardYr_eq_of_not_mem ν μ R c χy g τ hy, wardHr_eq_of_not_mem ν μ R c χy g U τ hy]

end Coef

/-- A phase pairing sees its field only off the axis (`ℝ × axis` is null). -/
theorem pairF_congr_offAxis' {P : ℝ} (Φ u v : ℝ × Space → CVec3)
    (h : ∀ τ y, y ∉ axis → u (τ, y) = v (τ, y)) : pairF P Φ u = pairF P Φ v := by
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  refine integral_congr_ae ?_
  filter_upwards [ae_not_mem_axis] with y hy
  simp only [h t y hy]

/-- The stress pairing sees its tensor only off the axis. -/
theorem stressPair_congr_offAxis {P : ℝ} (Tp Tp' : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ × Space → CVec3) (h : ∀ τ y, y ∉ axis → Tp (τ, y) = Tp' (τ, y)) :
    stressPair P Tp Φ = stressPair P Tp' Φ := by
  unfold stressPair phaseInt
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  refine integral_congr_ae ?_
  filter_upwards [ae_not_mem_axis] with y hy
  simp only [h t y hy]

/-! ## 5. The raw displacement vanishes near the axis -/

/-- The young cutoff profile has zero derivative on `[1, ∞)` (it vanishes there and is `≥ 0`, so
each such point is a minimum). -/
theorem IsYoungCutoff.deriv_eq_zero {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) {t : ℝ} (ht : 1 ≤ t) :
    deriv χ t = 0 := by
  have hmin : IsLocalMin χ t := Eventually.of_forall fun s => by
    rw [hχ.zero t ht]
    exact (hχ.range s).1
  exact hmin.deriv_eq_zero

/-- For `0 < ϱ ≤ R√ν` (`ν·age ≥ 1`) the young cutoff and its derivative vanish, so the raw
displacement is `0` there (source 4164-4166, 4182-4183). -/
theorem wardX_eq_zero_of_sq_le {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (g : Chart → Ten3) (τ : ℝ) {y : Space} (hy : y ∉ axis) (hr : ϱ y ^ 2 ≤ ν * R ^ 2) :
    wardX ν μ R c χy g τ y = 0 := by
  have hpos : 0 < ϱ y ^ 2 := pow_pos (ϱ_pos hy) 2
  have ht : 1 ≤ ν * age R y := by
    unfold age
    rw [← mul_div_assoc, le_div_iff₀ hpos, one_mul]
    exact hr
  unfold wardX wardStreamCut
  rw [hχy.zero _ ht, IsYoungCutoff.deriv_eq_zero hχy ht]
  simp

/-- The regularized displacement vanishes on the closed cylinder `ϱ ≤ R√ν` (axis included). -/
theorem wardXr_eq_zero_of_sq_le {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (g : Chart → Ten3) (τ : ℝ) {y : Space} (hr : ϱ y ^ 2 ≤ ν * R ^ 2) :
    wardXr ν μ R c χy g τ y = 0 := by
  by_cases hy : y ∈ axis
  · exact wardXr_of_mem ν μ R c χy g τ hy
  · rw [wardXr_of_not_mem ν μ R c χy g τ hy]
    exact wardX_eq_zero_of_sq_le hχy g τ hy hr

end UnforcedLeray.Short.PartIIIb.Concrete
