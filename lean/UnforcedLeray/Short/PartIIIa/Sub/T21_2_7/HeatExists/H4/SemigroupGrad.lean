import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.KerYoungMoment
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.HeatMoment
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H2.GradMoment
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H4.SemigroupS0
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelGradientConvolution

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/4/2`: (H4.2) `e^{νaΔ} ∂_j e^{νbΔ} = ∂_j e^{ν(a+b)Δ}`

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050.  Statement: `HeatExists/Leaves.lean` (`AdjHeatSemigroupGrad`).

Route as `adjHeatSemigroupS0`: the absolute kernel `K = G_{νa} ∗ |∂_j G_{νb}|`
(`gradAbsKer`) is continuous with axial moment `≤ 2^{m/2}` times the product of the moments
(Peetre), hence has a Young bound; Tonelli bounds the absolute double integral by
`∫ K(x - z) |f̃(z)| dz`, finite for a.e. `x`; Fubini and
`G_{νa} ∗ ∂_j G_{νb} = ∂_j G_{ν(a+b)}` (`integral_heatKernel2_gradHeatKernel2_conv_fst/_snd`)
finish.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The absolute kernel `K = G_{νa} ∗ |∂_j G_{νb}|`. -/
def gradAbsKer (ν a b : ℝ) (j : Fin 2) (u : ℝ × ℝ) : ℝ :=
  ∫ y : ℝ × ℝ, adjHeatKer ν a (u - y) * |adjHeatGradKer ν b j y|

theorem adjHeatKer_le {ν a : ℝ} (h : 0 < ν * a) (x : ℝ × ℝ) :
    adjHeatKer ν a x ≤ (4 * Real.pi * (ν * a))⁻¹ := by
  rw [adjHeatKer_eq h.le]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)

theorem integrable_adjHeatGradKer {ν b : ℝ} (hb : 0 < ν * b) (j : Fin 2) :
    Integrable (adjHeatGradKer ν b j) := by
  have h := adjGrad_kerAxialMoment_le hb (le_refl (0 : ℝ)) j
  refine ⟨(continuous_adjHeatGradKer ν b j).aestronglyMeasurable, ?_⟩
  have h1 : ∫⁻ z, ‖adjHeatGradKer ν b j z‖ₑ ≤ kerAxialMoment 0 (adjHeatGradKer ν b j) := by
    unfold kerAxialMoment; simp
  exact lt_of_le_of_lt h1 (h.trans_lt ENNReal.ofReal_lt_top)

theorem integrable_gradAbs_integrand {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (j : Fin 2)
    (u : ℝ × ℝ) :
    Integrable (fun y : ℝ × ℝ => adjHeatKer ν a (u - y) * |adjHeatGradKer ν b j y|) := by
  refine Integrable.bdd_mul (c := (4 * Real.pi * (ν * a))⁻¹)
    (integrable_adjHeatGradKer hb j).abs ?_ ?_
  · exact (((continuous_adjHeatKer ν a).comp (continuous_const.sub continuous_id))
      ).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (adjHeatKer_nonneg ha _)]
    exact adjHeatKer_le ha _

theorem continuous_gradAbsKer {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (j : Fin 2) :
    Continuous (gradAbsKer ν a b j) := by
  unfold gradAbsKer
  refine continuous_of_dominated (bound := fun y => (4 * Real.pi * (ν * a))⁻¹ *
    |adjHeatGradKer ν b j y|) ?_ ?_ ?_ ?_
  · intro u
    exact (integrable_gradAbs_integrand ha hb j u).aestronglyMeasurable
  · intro u
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (adjHeatKer_nonneg ha _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right (adjHeatKer_le ha _) (abs_nonneg _)
  · exact ((integrable_adjHeatGradKer hb j).abs).const_mul _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((continuous_adjHeatKer ν a).comp (continuous_id.sub continuous_const)).mul
      continuous_const

theorem gradAbsKer_nonneg {ν a b : ℝ} (ha : 0 < ν * a) (j : Fin 2) (u : ℝ × ℝ) :
    0 ≤ gradAbsKer ν a b j u :=
  integral_nonneg fun y => mul_nonneg (adjHeatKer_nonneg ha _) (abs_nonneg _)

theorem ofReal_gradAbsKer {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (j : Fin 2)
    (u : ℝ × ℝ) :
    ENNReal.ofReal (gradAbsKer ν a b j u) =
      ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a (u - y)) *
        ENNReal.ofReal |adjHeatGradKer ν b j y| := by
  unfold gradAbsKer
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_gradAbs_integrand ha hb j u)
    (Filter.Eventually.of_forall fun y =>
      mul_nonneg (adjHeatKer_nonneg ha _) (abs_nonneg _))]
  refine lintegral_congr fun y => ?_
  exact ENNReal.ofReal_mul (adjHeatKer_nonneg ha _)

/-- Peetre's inequality for the axial weight. -/
theorem axialWeight_peetre {m : ℝ} (hm : 0 ≤ m) (s t : ℝ) :
    (1 + (s + t) ^ 2) ^ (m / 2) ≤
      (2 : ℝ) ^ (m / 2) * (1 + s ^ 2) ^ (m / 2) * (1 + t ^ 2) ^ (m / 2) := by
  have hm2 : 0 ≤ m / 2 := div_nonneg hm (by norm_num)
  have h : 1 + (s + t) ^ 2 ≤ 2 * (1 + s ^ 2) * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (s - t), sq_nonneg (s * t)]
  calc (1 + (s + t) ^ 2) ^ (m / 2) ≤ (2 * (1 + s ^ 2) * (1 + t ^ 2)) ^ (m / 2) :=
        Real.rpow_le_rpow (by positivity) h hm2
    _ = _ := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * (1 + s ^ 2)) (by positivity),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]

theorem gradAbsKer_moment {m : ℝ} (hm : 0 ≤ m) {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b)
    (j : Fin 2) :
    kerAxialMoment m (gradAbsKer ν a b j) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * kerAxialMoment m (adjHeatKer ν a) *
        kerAxialMoment m (adjHeatGradKer ν b j) := by
  set W : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 + t ^ 2) ^ (m / 2)) with hW
  have hWm : Measurable W := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Measurable.pow_const (by fun_prop) _)
  have hGm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (adjHeatKer ν a z)) :=
    ENNReal.measurable_ofReal.comp (continuous_adjHeatKer ν a).measurable
  have hhm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal |adjHeatGradKer ν b j z|) :=
    ENNReal.measurable_ofReal.comp (continuous_adjHeatGradKer ν b j).abs.measurable
  have hKe : ∀ u, ‖gradAbsKer ν a b j u‖ₑ = ENNReal.ofReal (gradAbsKer ν a b j u) :=
    fun u => Real.enorm_eq_ofReal (gradAbsKer_nonneg ha j u)
  have hGe : ∀ z, ‖adjHeatKer ν a z‖ₑ = ENNReal.ofReal (adjHeatKer ν a z) :=
    fun z => Real.enorm_eq_ofReal (adjHeatKer_nonneg ha z)
  have hhe : ∀ z, ‖adjHeatGradKer ν b j z‖ₑ = ENNReal.ofReal |adjHeatGradKer ν b j z| :=
    fun z => Real.enorm_eq_ofReal_abs _
  unfold kerAxialMoment
  simp only [hKe, hGe, hhe, ofReal_gradAbsKer ha hb j]
  have step1 : ∀ u : ℝ × ℝ,
      (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a (u - y)) *
        ENNReal.ofReal |adjHeatGradKer ν b j y|) * ENNReal.ofReal ((1 + u.2 ^ 2) ^ (m / 2)) ≤
      ∫⁻ y : ℝ × ℝ, ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        ((ENNReal.ofReal (adjHeatKer ν a (u - y)) * ENNReal.ofReal ((1 + (u - y).2 ^ 2) ^ (m / 2))) *
         (ENNReal.ofReal |adjHeatGradKer ν b j y| * ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2)))) := by
    intro u
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    have hp := axialWeight_peetre hm (u.2 - y.2) y.2
    rw [sub_add_cancel] at hp
    have hp' : ENNReal.ofReal ((1 + u.2 ^ 2) ^ (m / 2)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * ENNReal.ofReal ((1 + (u - y).2 ^ 2) ^ (m / 2)) *
          ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by simpa using hp)
    calc ENNReal.ofReal (adjHeatKer ν a (u - y)) * ENNReal.ofReal |adjHeatGradKer ν b j y| *
          ENNReal.ofReal ((1 + u.2 ^ 2) ^ (m / 2))
        ≤ ENNReal.ofReal (adjHeatKer ν a (u - y)) * ENNReal.ofReal |adjHeatGradKer ν b j y| *
          (ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) * ENNReal.ofReal ((1 + (u - y).2 ^ 2) ^ (m / 2)) *
          ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2))) := by gcongr
      _ = _ := by ring
  calc ∫⁻ u : ℝ × ℝ, (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a (u - y)) *
        ENNReal.ofReal |adjHeatGradKer ν b j y|) * ENNReal.ofReal ((1 + u.2 ^ 2) ^ (m / 2))
      ≤ ∫⁻ u : ℝ × ℝ, ∫⁻ y : ℝ × ℝ, ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        ((ENNReal.ofReal (adjHeatKer ν a (u - y)) * ENNReal.ofReal ((1 + (u - y).2 ^ 2) ^ (m / 2))) *
         (ENNReal.ofReal |adjHeatGradKer ν b j y| * ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2)))) :=
        lintegral_mono step1
    _ = ∫⁻ y : ℝ × ℝ, ∫⁻ u : ℝ × ℝ, ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
        ((ENNReal.ofReal (adjHeatKer ν a (u - y)) * ENNReal.ofReal ((1 + (u - y).2 ^ 2) ^ (m / 2))) *
         (ENNReal.ofReal |adjHeatGradKer ν b j y| * ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2)))) := by
        refine lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        show Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          ((ENNReal.ofReal (adjHeatKer ν a (p.1 - p.2)) *
            ENNReal.ofReal ((1 + (p.1 - p.2).2 ^ 2) ^ (m / 2))) *
          (ENNReal.ofReal |adjHeatGradKer ν b j p.2| * ENNReal.ofReal ((1 + p.2.2 ^ 2) ^ (m / 2)))))
        exact measurable_const.mul (((hGm.comp (measurable_fst.sub measurable_snd)).mul
          (hWm.comp (measurable_snd.comp (measurable_fst.sub measurable_snd)))).mul
          ((hhm.comp measurable_snd).mul (hWm.comp (measurable_snd.comp measurable_snd))))
    _ = ∫⁻ y : ℝ × ℝ, ENNReal.ofReal ((2 : ℝ) ^ (m / 2)) *
          ((∫⁻ v : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a v) *
            ENNReal.ofReal ((1 + v.2 ^ 2) ^ (m / 2))) *
          (ENNReal.ofReal |adjHeatGradKer ν b j y| * ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2)))) := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mul_const']
        · rw [lintegral_sub_right_eq_self (fun v : ℝ × ℝ =>
            ENNReal.ofReal (adjHeatKer ν a v) * ENNReal.ofReal ((1 + v.2 ^ 2) ^ (m / 2))) y]
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    _ = _ := by
        have hmeas : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal |adjHeatGradKer ν b j y| *
            ENNReal.ofReal ((1 + y.2 ^ 2) ^ (m / 2))) := hhm.mul (hWm.comp measurable_snd)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmeas]
        ring

theorem gradAbsKer_young {m : ℝ} (hm : 0 ≤ m) {c ν a b : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (ha : a ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (j : Fin 2) :
    ∃ M : ℝ, KerYoung c m (gradAbsKer ν a b j) M := by
  obtain ⟨A1, hA1, h1⟩ := adjHeatMoment ν m hν hm
  obtain ⟨A2, hA2, h2⟩ := adjHeatGradMoment ν m hν hm
  have hνa : 0 < ν * a := mul_pos hν ha.1
  have hνb : 0 < ν * b := mul_pos hν hb.1
  have hbp : 0 ≤ b ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hb.1.le _
  have hA : 0 ≤ (2 : ℝ) ^ (m / 2) * A1 * (A2 * b ^ (-(1 / 2 : ℝ))) := by positivity
  refine ⟨_, adjKerYoungMoment c m hc hm _ (continuous_gradAbsKer hνa hνb j) _ hA ?_⟩
  refine (gradAbsKer_moment hm hνa hνb j).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  gcongr
  · exact h1 a ha
  · exact h2 b hb j

/-- Bochner form of the gradient convolution law, in the order of the double integral. -/
theorem adjGradConv_plane {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (j : Fin 2)
    (x z : ℝ × ℝ) :
    ∫ y : ℝ × ℝ, adjHeatKer ν a (x - y) * adjHeatGradKer ν b j (y - z) =
      adjHeatGradKer ν (a + b) j (x - z) := by
  have key : ∀ F : ℝ × ℝ → ℝ,
      (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * a) ((x - z) - w) * F w) =
      ∫ y : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * a) (x - y) * F (y - z) := by
    intro F
    rw [← integral_sub_right_eq_self (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 (ν * a) ((x - z) - w) * F w) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_sub_cancel_right]
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  have hsum : ν * (a + b) = ν * a + ν * b := by ring
  rcases hj with rfl | rfl
  · have h := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integral_heatKernel2_gradHeatKernel2_conv_fst
      ha hb (x - z)
    have h2 := key (fun w => (UnforcedLeray.B0296.gradHeatKernel2 (ν * b) w).1)
    simp only [adjHeatGradKer, adjHeatKer, if_true, hsum]
    rw [← h2]; exact h
  · have h := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integral_heatKernel2_gradHeatKernel2_conv_snd
      ha hb (x - z)
    have h2 := key (fun w => (UnforcedLeray.B0296.gradHeatKernel2 (ν * b) w).2)
    simp only [adjHeatGradKer, adjHeatKer, hsum]
    simp only [show ((1 : Fin 2) = 0) = False by decide, if_false]
    rw [← h2]; exact h

theorem enorm_ofReal_cast_abs (r : ℝ) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs]

/-- The double integral of `e^{νaΔ}(∂_j e^{νbΔ} g)` swaps to `∂_j e^{ν(a+b)Δ} g` at a point `x`
where the integral of `K(x - ·) |g|` converges. -/
theorem adjGrad_double_swap {ν a b : ℝ} (ha : 0 < ν * a) (hb : 0 < ν * b) (j : Fin 2)
    (x : ℝ × ℝ) (g : ℝ × ℝ → ℂ) (hg : Measurable g)
    (hfin : Integrable (fun z => (gradAbsKer ν a b j (x - z) : ℂ) * g z)) :
    ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
        ∫ z : ℝ × ℝ, (adjHeatGradKer ν b j (y - z) : ℂ) * g z =
      ∫ z : ℝ × ℝ, (adjHeatGradKer ν (a + b) j (x - z) : ℂ) * g z := by
  have hA : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (adjHeatKer ν a (x - p.1) : ℂ)) :=
    (Complex.continuous_ofReal.comp ((continuous_adjHeatKer ν a).comp
      (continuous_const.sub continuous_fst))).measurable
  have hB : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (adjHeatGradKer ν b j (p.1 - p.2) : ℂ)) :=
    (Complex.continuous_ofReal.comp ((continuous_adjHeatGradKer ν b j).comp
      (continuous_fst.sub continuous_snd))).measurable
  have hF : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (adjHeatKer ν a (x - p.1) : ℂ) * ((adjHeatGradKer ν b j (p.1 - p.2) : ℂ) * g p.2)) :=
    hA.mul (hB.mul (hg.comp measurable_snd))
  have hinner : ∀ z : ℝ × ℝ,
      ∫⁻ y : ℝ × ℝ, ‖(adjHeatKer ν a (x - y) : ℂ) *
        ((adjHeatGradKer ν b j (y - z) : ℂ) * g z)‖ₑ =
        ‖(gradAbsKer ν a b j (x - z) : ℂ) * g z‖ₑ := by
    intro z
    have hK0 := gradAbsKer_nonneg (b := b) ha j (x - z)
    calc ∫⁻ y : ℝ × ℝ, ‖(adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatGradKer ν b j (y - z) : ℂ) * g z)‖ₑ
        = ∫⁻ y : ℝ × ℝ, (ENNReal.ofReal (adjHeatKer ν a (x - y)) *
            ENNReal.ofReal |adjHeatGradKer ν b j (y - z)|) * ‖g z‖ₑ := by
          refine lintegral_congr fun y => ?_
          have hA0 : 0 ≤ adjHeatKer ν a (x - y) := adjHeatKer_nonneg ha _
          rw [enorm_mul, enorm_mul, enorm_ofReal_cast_nonneg hA0, enorm_ofReal_cast_abs]
          ring
      _ = (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (adjHeatKer ν a (x - y)) *
            ENNReal.ofReal |adjHeatGradKer ν b j (y - z)|) * ‖g z‖ₑ :=
          lintegral_mul_const' _ _ enorm_ne_top
      _ = ENNReal.ofReal (gradAbsKer ν a b j (x - z)) * ‖g z‖ₑ := by
          congr 1
          rw [ofReal_gradAbsKer ha hb j (x - z)]
          rw [← lintegral_sub_right_eq_self (fun w : ℝ × ℝ =>
            ENNReal.ofReal (adjHeatKer ν a ((x - z) - w)) *
              ENNReal.ofReal |adjHeatGradKer ν b j w|) z]
          refine lintegral_congr fun y => ?_
          simp only [sub_sub_sub_cancel_right]
      _ = ‖(gradAbsKer ν a b j (x - z) : ℂ) * g z‖ₑ := by
          rw [enorm_mul, enorm_ofReal_cast_nonneg hK0]
  have hint : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (adjHeatKer ν a (x - p.1) : ℂ) * ((adjHeatGradKer ν b j (p.1 - p.2) : ℂ) * g p.2))
      ((volume : Measure (ℝ × ℝ)).prod volume) := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod_symm _ hF.enorm.aemeasurable]
    simp only [hinner]
    exact hfin.2
  calc ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
          ∫ z : ℝ × ℝ, (adjHeatGradKer ν b j (y - z) : ℂ) * g z
      = ∫ y : ℝ × ℝ, ∫ z : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatGradKer ν b j (y - z) : ℂ) * g z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ z : ℝ × ℝ, ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatGradKer ν b j (y - z) : ℂ) * g z) :=
        integral_integral_swap (f := fun y z : ℝ × ℝ => (adjHeatKer ν a (x - y) : ℂ) *
          ((adjHeatGradKer ν b j (y - z) : ℂ) * g z)) hint
    _ = ∫ z : ℝ × ℝ, (adjHeatGradKer ν (a + b) j (x - z) : ℂ) * g z := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hbochner : ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
            (adjHeatGradKer ν b j (y - z) : ℂ) =
            (adjHeatGradKer ν (a + b) j (x - z) : ℂ) := by
          simp only [← Complex.ofReal_mul]
          rw [integral_complex_ofReal]
          congr 1
          exact adjGradConv_plane ha hb j x z
        calc ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
              ((adjHeatGradKer ν b j (y - z) : ℂ) * g z)
            = ∫ y : ℝ × ℝ, ((adjHeatKer ν a (x - y) : ℂ) *
                (adjHeatGradKer ν b j (y - z) : ℂ)) * g z := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              ring
          _ = (∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
                (adjHeatGradKer ν b j (y - z) : ℂ)) * g z := integral_mul_const _ _
          _ = (adjHeatGradKer ν (a + b) j (x - z) : ℂ) * g z := by rw [hbochner]

theorem adjHeatSemigroupGrad (m : ℝ) (hm : 8 < m) : AdjHeatSemigroupGrad m := by
  intro ν c hν hc a b ha hb hab j w
  have hm0 : 0 ≤ m := by linarith
  have haI : a ∈ Ioc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  have hbI : b ∈ Ioc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  obtain ⟨M, hY⟩ := gradAbsKer_young hm0 (c := c) hν hc haI hbI j
  have hpos_a : 0 < ν * a := mul_pos hν ha
  have hpos_b : 0 < ν * b := mul_pos hν hb
  have hI := ae_integrable_adjKerOp hc (continuous_gradAbsKer hpos_a hpos_b j) hY w
  have hmeasg : Measurable (perRep c ⇑w) :=
    (stronglyMeasurable_perRep hc (Lp.stronglyMeasurable w)).measurable
  filter_upwards [hI] with x hx
  have hg : perRep c (adjKerOp c (adjHeatGradKer ν b j) ⇑w) =
      adjKerOp c (adjHeatGradKer ν b j) ⇑w :=
    perRep_adjKerOp hc (adjHeatGradKer ν b j) ⇑w
  show ∫ y : ℝ × ℝ, (adjHeatKer ν a (x - y) : ℂ) *
      perRep c (adjKerOp c (adjHeatGradKer ν b j) ⇑w) y =
    ∫ z : ℝ × ℝ, (adjHeatGradKer ν (a + b) j (x - z) : ℂ) * perRep c ⇑w z
  rw [hg]
  exact adjGrad_double_swap hpos_a hpos_b j x (perRep c ⇑w) hmeasg hx

end UnforcedLeray.Short.IIIa
