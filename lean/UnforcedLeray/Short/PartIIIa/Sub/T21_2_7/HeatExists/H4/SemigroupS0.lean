import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1
import UnforcedLeray.Units.B0289.Semigroup

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/4/1`: (H4.1) the Gaussian semigroup law on the cell

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050.  Statement: `HeatExists/Leaves.lean` (`AdjHeatSemigroupS0`).

Route: for `w ∈ X_{-m,c}` with periodic lift `f̃ = perRep c w`, the inner function
`e^{νbΔ} f̃` is its own periodic lift (`perRep_adjKerOp`), so `e^{νaΔ} e^{νbΔ} f̃` is the iterated
integral `∫ G_{νa}(x-y) ∫ G_{νb}(y-z) f̃(z) dz dy`.  Tonelli bounds the absolute double integral by
`∫ G_{ν(a+b)}(x-z) |f̃(z)| dz`, finite for a.e. `x` by the Young bound at `a+b`
(`ae_integrable_adjKerOp`), and Fubini with the semigroup identity `G_{νa} ∗ G_{νb} = G_{ν(a+b)}`
(`B0289`) gives `e^{ν(a+b)Δ} f̃`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Bochner form of the planar Gaussian semigroup law, in the order of `adjKerOp`. -/
theorem heatKernel2_conv_plane {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x z : ℝ × ℝ) :
    ∫ y : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 α (x - y) *
        UnforcedLeray.B0284.heatKernel2 β (y - z) =
      UnforcedLeray.B0284.heatKernel2 (α + β) (x - z) := by
  have h := UnforcedLeray.B0289.integral_heatKernel2_conv hβ hα (x - z)
  rw [add_comm α β, ← h]
  have hsub : ∀ y : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 α (x - y) *
        UnforcedLeray.B0284.heatKernel2 β (y - z) =
      (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 β ((x - z) - w) *
        UnforcedLeray.B0284.heatKernel2 α w) (x - y) := by
    intro y
    simp only [sub_sub_sub_cancel_left]
    ring
  simp_rw [hsub]
  exact integral_sub_left_eq_self
    (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 β ((x - z) - w) *
      UnforcedLeray.B0284.heatKernel2 α w) volume x

/-- Lower-integral form of the planar Gaussian semigroup law, for the adjoint heat kernels. -/
theorem lintegral_adjHeatKer_conv {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (x z : ℝ × ℝ) :
    ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a (x - y)) *
        ENNReal.ofReal (adjHeatKer ν b (y - z)) =
      ENNReal.ofReal (adjHeatKer ν (a + b) (x - z)) := by
  have h := UnforcedLeray.B0289.lintegral_heatKernel2_conv ha hb (x - z)
  unfold adjHeatKer
  rw [mul_add]
  refine (lintegral_congr fun y => ?_).trans
    ((lintegral_sub_left_eq_self (fun w : ℝ × ℝ => ENNReal.ofReal
      (UnforcedLeray.B0284.heatKernel2 (ν * a) w) * ENNReal.ofReal
      (UnforcedLeray.B0284.heatKernel2 (ν * b) ((x - z) - w))) x).trans ?_)
  · rw [show (x - z) - (x - y) = y - z by abel]
  · exact h

/-- The real cast of a nonnegative real has enorm its `ofReal`. -/
theorem enorm_ofReal_cast_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← Real.enorm_eq_ofReal hr, enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

/-- The double integral of `e^{νaΔ}(e^{νbΔ} g)` swaps to `e^{ν(a+b)Δ} g` at a point `x` where
the integral of `G_{ν(a+b)}(x - ·) g` converges absolutely. -/
theorem adjKer_double_swap {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (x : ℝ × ℝ)
    (g : ℝ × ℝ → ℂ) (hg : Measurable g)
    (hfin : Integrable (fun z => (adjHeatKer ν (a + b) (x - z) : ℂ) * g z)) :
    ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
        ∫ z : ℝ × ℝ, (adjHeatKer ν b (y - z) : ℂ) * g z =
      ∫ z : ℝ × ℝ, (adjHeatKer ν (a + b) (x - z) : ℂ) * g z := by
  have hpos : 0 < ν * (a + b) := by rw [mul_add]; linarith
  have hA : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (adjHeatKer ν a (x - p.1) : ℂ)) :=
    (Complex.continuous_ofReal.comp ((continuous_adjHeatKer ν a).comp
      (continuous_const.sub continuous_fst))).measurable
  have hB : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (adjHeatKer ν b (p.1 - p.2) : ℂ)) :=
    (Complex.continuous_ofReal.comp ((continuous_adjHeatKer ν b).comp
      (continuous_fst.sub continuous_snd))).measurable
  have hF : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (adjHeatKer ν a (x - p.1) : ℂ) * ((adjHeatKer ν b (p.1 - p.2) : ℂ) * g p.2)) :=
    hA.mul (hB.mul (hg.comp measurable_snd))
  -- the pointwise `z`-section of the absolute integral
  have hinner : ∀ z : ℝ × ℝ,
      ∫⁻ y : ℝ × ℝ, ‖(adjHeatKer ν a (x - y) : ℂ) *
        ((adjHeatKer ν b (y - z) : ℂ) * g z)‖ₑ = ‖(adjHeatKer ν (a + b) (x - z) : ℂ) * g z‖ₑ := by
    intro z
    have hγ0 : 0 ≤ adjHeatKer ν (a + b) (x - z) :=
      UnforcedLeray.B0284.heatKernel2_nonneg hpos (x - z)
    calc ∫⁻ y : ℝ × ℝ, ‖(adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatKer ν b (y - z) : ℂ) * g z)‖ₑ
        = ∫⁻ y : ℝ × ℝ, (ENNReal.ofReal (adjHeatKer ν a (x - y)) *
            ENNReal.ofReal (adjHeatKer ν b (y - z))) * ‖g z‖ₑ := by
          refine lintegral_congr fun y => ?_
          have hA0 : 0 ≤ adjHeatKer ν a (x - y) :=
            UnforcedLeray.B0284.heatKernel2_nonneg ha (x - y)
          have hB0 : 0 ≤ adjHeatKer ν b (y - z) :=
            UnforcedLeray.B0284.heatKernel2_nonneg hb (y - z)
          rw [enorm_mul, enorm_mul, enorm_ofReal_cast_nonneg hA0, enorm_ofReal_cast_nonneg hB0]
          ring
      _ = (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a (x - y)) *
            ENNReal.ofReal (adjHeatKer ν b (y - z))) * ‖g z‖ₑ :=
          lintegral_mul_const' _ _ enorm_ne_top
      _ = ENNReal.ofReal (adjHeatKer ν (a + b) (x - z)) * ‖g z‖ₑ := by
          rw [lintegral_adjHeatKer_conv ha hb]
      _ = ‖(adjHeatKer ν (a + b) (x - z) : ℂ) * g z‖ₑ := by
          rw [enorm_mul, enorm_ofReal_cast_nonneg hγ0]
  -- integrability on the product, by Tonelli
  have hint : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (adjHeatKer ν a (x - p.1) : ℂ) * ((adjHeatKer ν b (p.1 - p.2) : ℂ) * g p.2))
      ((volume : Measure (ℝ × ℝ)).prod volume) := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod_symm _ hF.enorm.aemeasurable]
    simp only [hinner]
    exact hfin.2
  calc ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
          ∫ z : ℝ × ℝ, (adjHeatKer ν b (y - z) : ℂ) * g z
      = ∫ y : ℝ × ℝ, ∫ z : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatKer ν b (y - z) : ℂ) * g z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ z : ℝ × ℝ, ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatKer ν b (y - z) : ℂ) * g z) :=
        integral_integral_swap (f := fun y z : ℝ × ℝ => (adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatKer ν b (y - z) : ℂ) * g z)) hint
    _ = ∫ z : ℝ × ℝ, (adjHeatKer ν (a + b) (x - z) : ℂ) * g z := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hbochner : ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
            (adjHeatKer ν b (y - z) : ℂ) = (adjHeatKer ν (a + b) (x - z) : ℂ) := by
          simp only [← Complex.ofReal_mul]
          rw [integral_complex_ofReal]
          congr 1
          unfold adjHeatKer
          rw [mul_add]
          exact heatKernel2_conv_plane ha hb x z
        calc ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
              ((adjHeatKer ν b (y - z) : ℂ) * g z)
            = ∫ y : ℝ × ℝ, ((adjHeatKer ν a (x - y) : ℂ) *
                (adjHeatKer ν b (y - z) : ℂ)) * g z := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              ring
          _ = (∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
                (adjHeatKer ν b (y - z) : ℂ)) * g z := integral_mul_const _ _
          _ = (adjHeatKer ν (a + b) (x - z) : ℂ) * g z := by rw [hbochner]

theorem adjHeatSemigroupS0 (m : ℝ) (hm : 8 < m) : AdjHeatSemigroupS0 m := by
  intro ν c hν hc a b ha hb hab w
  obtain ⟨M₀, -, hY⟩ := adjHeatS0Young m hm ν c hν hc
  have hτ : a + b ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, hab⟩
  have hI := ae_integrable_adjKerOp hc (continuous_adjHeatKer ν (a + b)) (hY (a + b) hτ) w
  have hmeasg : Measurable (perRep c ⇑w) :=
    (stronglyMeasurable_perRep hc (Lp.stronglyMeasurable w)).measurable
  have hpos_a : 0 < ν * a := mul_pos hν ha
  have hpos_b : 0 < ν * b := mul_pos hν hb
  filter_upwards [hI] with x hx
  have hg : perRep c (adjS0Fun ν c b ⇑w) = adjS0Fun ν c b ⇑w :=
    perRep_adjKerOp hc (adjHeatKer ν b) ⇑w
  show ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) * perRep c (adjS0Fun ν c b ⇑w) y =
    ∫ z : ℝ × ℝ, (adjHeatKer ν (a + b) (x - z) : ℂ) * perRep c ⇑w z
  rw [hg]
  exact adjKer_double_swap hpos_a hpos_b x (perRep c ⇑w) hmeasg hx

end UnforcedLeray.Short.IIIa
