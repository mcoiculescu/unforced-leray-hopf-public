import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1

/-!
# Repair of `OutChangeVar` (`PartIII-b:C/near/masked/14/2/3/1/4`; source 3996-4011, 3604-3610, 2683)

Source: `the November 2 reference manuscript`.

`OutChangeVar` (age measure `s^{-3/2}`, arbitrary periodic axisymmetric `Q`) is false: the change of
variables `y = (R/√s, 0, η/√s)` has Jacobian `dy = π R² s^{-5/2} ds dη` (azimuth integrated), so
only the exponent `-5/2` converts exactly to `ℝ³`.  Counterexample for `-3/2`: `Q` the indicator of
`{ε ≤ ρ ≤ 2ε, |y₂| ≤ 1}` (`τ`-independent); the left side is `2 log 4` for every `ε` while the right
side is `K₁ (2c/R) 6π ε² → 0`.

The slice `farSliceOut` carries the extra factor `s^{-1/2}` (squared: `s^{-1}`) and is supported in
`s < S`, so the `-3/2` integral of `Q = (cartSliceOut …)^2` is at most `S` times its `-5/2` integral.
This file states the exact `-5/2` change of variables `OutChangeVarExp` and proves
`FarOutChange` from it (`farOutChange_of_exp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **Change of variables with the Jacobian weight** (source 2683, 3604-3610, 3996-4011): for
`Q(τ, y)` jointly measurable, `2c/R`-periodic in `τ` and axisymmetric in `y`, with
`x = (s,(q,η))`, `τ = 2q/R + log s`, `y = (R/√s, 0, η/√s)`:
`∫ Q(τ(x), y(x)) d ageμ c (-5/2) = (2π R c)⁻¹ ∫_{τ ∈ (0, 2c/R]} ∫_{ℝ³} Q(τ, y) dy dτ`
(stated as `≤ K₁ ·` with `K₁` depending on `R, c` only).  Proof: `Axi.lintegral_ageμ`; the `q`-integral
of the `2c/R`-periodic `τ = 2q/R + log s` is `R/2` times the period integral; then
`s^{-5/2} ds dη = (2/R²) ρ dρ dy₂` with `ρ = R/√s`, `y₂ = η/√s`; polar coordinates in `(y₀,y₁)`
(axisymmetry). -/
def OutChangeVarExp : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c →
    ∃ K₁ : ℝ≥0∞, K₁ ≠ ⊤ ∧ ∀ Q : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry Q) →
      (∀ τ y, Q (τ + 2 * c / R) y = Q τ y) →
      (∀ τ y y', y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 → Q τ y = Q τ y') →
        ∫⁻ x, Q (chartTau R x) (chartY R x) ∂(ageμ c (-5 / 2)) ≤
          K₁ * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ∫⁻ y : Space, Q τ y

lemma measurable_chartTau (R : ℝ) : Measurable (chartTau R) := by
  unfold chartTau
  fun_prop

lemma measurable_chartY (R : ℝ) : Measurable (chartY R) := by
  unfold chartY
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
  refine measurable_pi_lambda _ fun i => ?_
  fin_cases i <;> simp <;> fun_prop

lemma chartY_sq (R : ℝ) (p : Chart) (hs : 0 < p.1) :
    (chartY R p) 0 ^ 2 + (chartY R p) 1 ^ 2 = R ^ 2 / p.1 := by
  simp only [chartY]
  show (R / Real.sqrt p.1) ^ 2 + 0 ^ 2 = _
  rw [div_pow, Real.sq_sqrt hs.le]; ring

/-- Age comparison: for `Q` supported in `age < S`, the `s^{-3/2}` integral is at most `S` times
the `s^{-5/2}` integral. -/
lemma lintegral_age_compare (R c S : ℝ) (hR : 0 < R) (hc : 0 < c) (hS : 0 < S) (Q : ℝ → Space → ℝ≥0∞)
    (hmeas : Measurable fun x : Chart => Q (chartTau R x) (chartY R x))
    (hsupp : ∀ τ y, Q τ y ≠ 0 → R ^ 2 / (y 0 ^ 2 + y 1 ^ 2) < S) :
    ∫⁻ x, Q (chartTau R x) (chartY R x) ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal S * ∫⁻ x, Q (chartTau R x) (chartY R x) ∂(ageμ c (-5 / 2)) := by
  rw [lintegral_ageμ hc _ hmeas, lintegral_ageμ hc _ hmeas,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  have hmeasSet : MeasurableSet (Ioi (0 : ℝ) ×ˢ qCell c) :=
    (measurableSet_Ioi (a := (0 : ℝ))).prod (by rw [qCell_eq_cell]; exact Cyl.measurableSet_cell c)
  have hmem : ∀ᵐ p ∂((volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ qCell c)),
      p ∈ Ioi (0 : ℝ) ×ˢ qCell c := ae_restrict_mem hmeasSet
  filter_upwards [hmem] with p hp
  have hs : 0 < p.1 := hp.1
  by_cases h0 : Q (chartTau R p) (chartY R p) = 0
  · rw [h0]; simp
  · have hlt := hsupp _ _ h0
    rw [chartY_sq R p hs] at hlt
    have h3' : R ^ 2 / (R ^ 2 / p.1) = p.1 := by
      field_simp
    rw [h3'] at hlt
    have hw : ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) ≤
        ENNReal.ofReal S * ENNReal.ofReal (c⁻¹ * p.1 ^ (-5 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul hS.le]
      apply ENNReal.ofReal_le_ofReal
      have e : p.1 ^ (-3 / 2 : ℝ) = p.1 * p.1 ^ (-5 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hs.le (by norm_num)]; norm_num
      rw [e]
      have hp5 : 0 ≤ p.1 ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
      have : p.1 * p.1 ^ (-5 / 2 : ℝ) ≤ S * p.1 ^ (-5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hlt.le hp5
      have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      calc c⁻¹ * (p.1 * p.1 ^ (-5 / 2 : ℝ)) ≤ c⁻¹ * (S * p.1 ^ (-5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left this hci
        _ = S * (c⁻¹ * p.1 ^ (-5 / 2 : ℝ)) := by ring
    calc ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * Q (chartTau R p) (chartY R p)
        ≤ (ENNReal.ofReal S * ENNReal.ofReal (c⁻¹ * p.1 ^ (-5 / 2 : ℝ))) *
            Q (chartTau R p) (chartY R p) := mul_le_mul' hw le_rfl
      _ = _ := by rw [mul_assoc]

lemma chain_le (L I K J S' : ℝ≥0∞) (h1 : L ≤ S' * I) (h2 : I ≤ K * J) : L ≤ S' * K * J := by
  rw [mul_assoc]; exact h1.trans (by gcongr)

theorem farOutChange_of_exp (h1 : LiftAxisym) (h2 : SliceAxisym) (h3 : SliceJointMeas)
    (h4 : OutChangeVarExp) : FarOutChange := by
  intro R c δ S hR hc hδ hS
  obtain ⟨K₁, hK₁, hK⟩ := h4 R c hR hc
  refine ⟨ENNReal.ofReal S * K₁, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK₁, fun f hf l hl => ?_⟩
  set Q : ℝ → Space → ℝ≥0∞ := fun τ y =>
    (cartSliceOut R δ S l (liftNorm R c f (τ + 2 * Real.log l)) y) ^ (2 : ℝ) with hQ
  have hQm : Measurable (Function.uncurry Q) := h3 R c δ S l f hf
  have hae : ∀ᵐ x ∂(ageμ c (-3 / 2)), 0 < x.1 := by
    filter_upwards [ae_ageμ_mem hc (-3 / 2)] with x hx using hx.1
  have hEq : ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) =
      ∫⁻ x, Q (chartTau R x) (chartY R x) ∂(ageμ c (-3 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hQ]
    rw [farSliceOut_eq_cart R c δ S l f hR x hx]
  have hcart : (∫⁻ τ in Ioc (0 : ℝ) (2 * c / R),
      cartOut R δ S l (liftNorm R c f (τ + 2 * Real.log l))) =
      ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ∫⁻ y : Space, Q τ y :=
    lintegral_congr fun τ => rfl
  rw [hEq, hcart]
  clear_value Q
  have hmeas : Measurable fun x : Chart => Q (chartTau R x) (chartY R x) :=
    hQm.comp ((measurable_chartTau R).prodMk (measurable_chartY R))
  have hsupp : ∀ τ y, Q τ y ≠ 0 → R ^ 2 / (y 0 ^ 2 + y 1 ^ 2) < S := by
    intro τ y hne
    by_contra hnot
    apply hne
    have : cartSliceOut R δ S l (liftNorm R c f (τ + 2 * Real.log l)) y = 0 := by
      unfold cartSliceOut; simp [hnot]
    rw [hQ]
    show (cartSliceOut R δ S l (liftNorm R c f (τ + 2 * Real.log l)) y) ^ (2 : ℝ) = 0
    rw [this]; simp
  have hcmp := lintegral_age_compare R c S hR hc hS Q hmeas hsupp
  have hper : ∀ τ y, Q (τ + 2 * c / R) y = Q τ y := by
    intro τ y
    simp only [hQ]
    have : τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R := by ring
    rw [this]
    have : liftNorm R c f ((τ + 2 * Real.log l) + 2 * c / R) = liftNorm R c f (τ + 2 * Real.log l) :=
      funext (liftNorm_periodic R c hR hc f _)
    rw [this]
  have hax : ∀ τ y y', y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 → Q τ y = Q τ y' := by
    intro τ y y' hy hy2
    simp only [hQ]
    rw [h2 R δ S l _ (fun z z' a b => h1 R c f _ z z' a b) y y' hy hy2]
  exact chain_le _ _ _ _ _ hcmp (hK Q hQm hper hax)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
