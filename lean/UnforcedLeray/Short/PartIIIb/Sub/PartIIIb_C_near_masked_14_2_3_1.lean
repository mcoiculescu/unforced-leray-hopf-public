import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3

/-!
# Decomposition of `FarOutChange` (`PartIII-b:C/near/masked/14/2/3/1`; source 3996-4011, 3604-3610, 2683)

Source: `the November 2 reference manuscript`.

`FarOutChange` follows from: the pointwise identity `farSliceOut = cartSliceOut ∘ chart` (proved),
the `2c/R`-periodicity of the lift norm in the phase (proved), the axisymmetry of the lift norm and
of the Cartesian slice, joint measurability, and one general change-of-variables statement
`OutChangeVar` (age/cell measure to `ℝ³ × one period`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The chart-to-Cartesian identity of the slice (proved below). -/
lemma farSliceOut_eq_cart (R c δ S l : ℝ) (f : Chart → Ten3) (hR : 0 < R) (x : Chart)
    (hs : 0 < x.1) :
    farSliceOut R c δ S f l x =
      cartSliceOut R δ S l (liftNorm R c f (chartTau R x + 2 * Real.log l)) (chartY R x) := by
  have h2 : (chartY R x) 0 ^ 2 + (chartY R x) 1 ^ 2 = R ^ 2 / x.1 := by
    simp only [chartY]
    show (R / Real.sqrt x.1) ^ 2 + 0 ^ 2 = _
    rw [div_pow, Real.sq_sqrt hs.le]; ring
  have h3 : R ^ 2 / (R ^ 2 / x.1) = x.1 := by
    field_simp
  unfold farSliceOut farSlice cartSliceOut liftNorm
  rw [h2, h3]

/-- The Cartesian lift is `2c/R`-periodic in the phase (floor reduction in `chartOf`). -/
lemma liftNorm_periodic (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3) (τ : ℝ)
    (z : Space) : liftNorm R c f (τ + 2 * c / R) z = liftNorm R c f τ z := by
  have key : chartOf R c z (τ + 2 * c / R) = chartOf R c z τ := by
    unfold chartOf
    have e : R * Real.log (hRad z / R) + R * (τ + 2 * c / R) / 2
        = (R * Real.log (hRad z / R) + R * τ / 2) + c := by
      field_simp
      ring
    rw [e]
    have e2 : (R * Real.log (hRad z / R) + R * τ / 2 + c) / c + 1 / 2
        = ((R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2) + 1 := by
      field_simp
      ring
    rw [e2, Int.floor_add_one]
    push_cast
    ext <;> simp <;> ring
  unfold liftNorm cartLift
  rw [key]

/-- Axisymmetry of the lift norm: it depends on `z` only through `(z₀² + z₁², z₂)`. -/
def LiftAxisym : Prop :=
  ∀ (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z z' : Space),
    z 0 ^ 2 + z 1 ^ 2 = z' 0 ^ 2 + z' 1 ^ 2 → z 2 = z' 2 →
      liftNorm R c f τ z = liftNorm R c f τ z'

/-- Axisymmetry of the Cartesian slice (rotation invariance of Lebesgue measure on `ℝ³` in the first
two coordinates): for `g` depending only on `(z₀² + z₁², z₂)`, `cartSliceOut … g y` depends only on
`(y₀² + y₁², y₂)`. -/
def SliceAxisym : Prop :=
  ∀ (R δ S l : ℝ) (g : Space → ℝ),
    (∀ z z' : Space, z 0 ^ 2 + z 1 ^ 2 = z' 0 ^ 2 + z' 1 ^ 2 → z 2 = z' 2 → g z = g z') →
    ∀ y y' : Space, y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 →
      cartSliceOut R δ S l g y = cartSliceOut R δ S l g y'

/-- Joint measurability in `(τ, y)` of the squared slice of the shifted lift norm. -/
def SliceJointMeas : Prop :=
  ∀ (R c δ S l : ℝ) (f : Chart → Ten3), IsBoxTensor f →
    Measurable (Function.uncurry fun (τ : ℝ) (y : Space) =>
      (cartSliceOut R δ S l (liftNorm R c f (τ + 2 * Real.log l)) y) ^ (2 : ℝ))

/-- RETIRED: `OutChangeVar` (exponent `-3/2`, arbitrary `Q`) is false as stated; nothing new depends
on it. Use `OutChangeVarExp` and `farOutChange_of_exp` in `PartIII-b_C_near_masked_14_2_3_1_4.lean`.

**Change of variables** (source 2683,3604-3610, 3996-4011): for `Q(τ, y)` jointly measurable,
`2c/R`-periodic in `τ` and axisymmetric in `y`, with `x = (s,(q,η))`, `τ = 2q/R + log s`,
`y = (R/√s, 0, η/√s)`:
`∫ Q(τ(x), y(x)) d ageμ c (-3/2) ≤ K₁ ∫_{τ ∈ (0, 2c/R]} ∫_{ℝ³} Q(τ, y) dy dτ`, `K₁` depending on
`R, c` only. (Proof: `Axi.lintegral_ageμ`; periodic shift invariance in `q`; `s^{-5/2} ds dη =
2R^{-2} y₁ dy₁ dy₃`; polar coordinates in `(y₀,y₁)`.) -/
def OutChangeVar : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c →
    ∃ K₁ : ℝ≥0∞, K₁ ≠ ⊤ ∧ ∀ Q : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry Q) →
      (∀ τ y, Q (τ + 2 * c / R) y = Q τ y) →
      (∀ τ y y', y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 → Q τ y = Q τ y') →
        ∫⁻ x, Q (chartTau R x) (chartY R x) ∂(ageμ c (-3 / 2)) ≤
          K₁ * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ∫⁻ y : Space, Q τ y

theorem farOutChange_of (h1 : LiftAxisym) (h2 : SliceAxisym) (h3 : SliceJointMeas)
    (h4 : OutChangeVar) : FarOutChange := by
  intro R c δ S hR hc hδ hS
  obtain ⟨K₁, hK₁, hK⟩ := h4 R c hR hc
  refine ⟨K₁, hK₁, fun f hf l hl => ?_⟩
  set Q : ℝ → Space → ℝ≥0∞ := fun τ y =>
    (cartSliceOut R δ S l (liftNorm R c f (τ + 2 * Real.log l)) y) ^ (2 : ℝ) with hQ
  have hae : ∀ᵐ x ∂(ageμ c (-3 / 2)), 0 < x.1 := by
    filter_upwards [ae_ageμ_mem hc (-3 / 2)] with x hx using hx.1
  have hEq : ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) =
      ∫⁻ x, Q (chartTau R x) (chartY R x) ∂(ageμ c (-3 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hQ]
    rw [farSliceOut_eq_cart R c δ S l f hR x hx]
  rw [hEq]
  refine (hK Q (h3 R c δ S l f hf) ?_ ?_).trans le_rfl
  · intro τ y
    simp only [hQ]
    have : τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R := by ring
    rw [this]
    have : liftNorm R c f ((τ + 2 * Real.log l) + 2 * c / R) = liftNorm R c f (τ + 2 * Real.log l) :=
      funext (liftNorm_periodic R c hR hc f _)
    rw [this]
  · intro τ y y' hy hy2
    simp only [hQ]
    rw [h2 R δ S l _ (fun z z' a b => h1 R c f _ z z' a b) y y' hy hy2]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
