import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.ParamCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRCont

/-!


Integrability on `[s, τ]` of `r ↦ ∂_iK_{ν(τ-r)} * ∂_iF(r)(x)`. Source:
`the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
Route: for `a > 0` the scaled representation `heatSGd i a g x = (-1/(2√a)) ∫ w_i K_1(w) g(x-√a w)`
(`DPC.heatSGd_pos_eq`) factors the integrand as `κ(r) J(r)`, with `κ` continuous on `(s, τ)` and `J`
jointly continuous by dominated continuity (domination `|w_i| K_1(w) B`, `CC.abs_coord_int`). The
pointwise bound `2 e^{ν(T-s)} B (1 + (ν(τ-r))^{-1/2})` (`HeatWBounds`) is integrable on `(s, τ)`
by `Gronwall.intervalIntegrable_kernel`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CTDG

lemma scaled_deriv {a : ℝ} (ha : 0 < a) (i : Fin 2) (g : Pl → ℝ) (x : Pl) :
    heatSGd i a g x = (-1 / (2 * Real.sqrt a)) *
      ∫ w : Pl, ![w.1, w.2] i * heatK 1 w * g (x - Real.sqrt a • w) := by
  rw [DPC.heatSGd_pos_eq ha i g x, ← integral_const_mul]
  congr 1
  funext w
  ring

lemma pd_slice {s T : ℝ} {F : ℝ → Pl → ℝ} (hF : FReg s T F) (i : Fin 2) {r : ℝ}
    (hr : r ∈ Icc s T) : Continuous (fun y : Pl => B0579.pd i (F r) y) := by
  have h : ContinuousOn ((fun z : ℝ × Pl => B0579.pd i (F z.1) z.2) ∘ (fun y : Pl => (r, y)))
      univ :=
    (hF.contdF i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨hr, mem_univ _⟩)
  exact continuousOn_univ.1 h

end CTDG

open CTDG in
/-- **`PartII-b:T22/1/11/4/1`** Integrability of the limit integrands on `[s, τ]`. -/
theorem convTD_Quot_gint : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Quot_GInt := by
  intro ν s T hν hsT B F hF hb τ hτ x i
  have hsτ : s ≤ τ := hτ.1
  have hs0 : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  have hB0 : 0 ≤ B := by
    have h0 := (hb s hs0).1 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  -- integrable dominator on (s, τ)
  have hker : IntegrableOn (fun r : ℝ => (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) (Ioo s τ) := by
    have h1 := (UnforcedLeray.Gronwall.intervalIntegrable_kernel τ s τ).const_mul
      (ν ^ (-(1 / 2 : ℝ)))
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hsτ] at h1
    refine h1.congr_fun ?_ measurableSet_Ioo
    intro r hr
    have hr' : 0 ≤ τ - r := sub_nonneg.2 hr.2.le
    beta_reduce
    rw [Real.mul_rpow hν.le hr']
  have hD : IntegrableOn
      (fun r : ℝ => 2 * Real.exp (ν * (T - s)) * B * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))))
      (Ioo s τ) := by
    have hc1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo s τ) :=
      integrableOn_const measure_Ioo_lt_top.ne
    exact (hc1.add hker).const_mul _
  -- pointwise bound
  have hbd : ∀ r ∈ Ioo s τ, ‖heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x‖ ≤
      2 * Real.exp (ν * (T - s)) * B * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) := by
    intro r hr
    have hrI : r ∈ Icc s T := ⟨hr.1.le, hr.2.le.trans hτ.2⟩
    have ha : 0 < ν * (τ - r) := mul_pos hν (by linarith [hr.2])
    have h := (heatWBounds B (B0579.pd i (F r)) ((hb r hrI).2 i)).2 _ ha i x
    rw [Real.norm_eq_abs]
    have hc : 1 ≤ Real.cosh x.2 := Real.one_le_cosh _
    have hE : Real.exp (ν * (τ - r)) ≤ Real.exp (ν * (T - s)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hr.1, hτ.2]) hν.le)
    have hpos : 0 ≤ (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B :=
      mul_nonneg (by linarith [Real.rpow_nonneg ha.le (-(1 / 2 : ℝ))]) hB0
    have key : Real.exp (ν * (τ - r)) * ((1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B)
        ≤ Real.exp (ν * (T - s)) * ((1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B) :=
      mul_le_mul_of_nonneg_right hE hpos
    have habs : |heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x|
        ≤ |heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x| * Real.cosh x.2 :=
      le_mul_of_one_le_right (abs_nonneg _) hc
    calc |heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x|
        ≤ |heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x| * Real.cosh x.2 := habs
      _ ≤ 2 * Real.exp (ν * (τ - r)) * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B := h
      _ = 2 * (Real.exp (ν * (τ - r)) * ((1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B)) := by ring
      _ ≤ 2 * (Real.exp (ν * (T - s)) * ((1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) * B)) := by
          linarith [key]
      _ = 2 * Real.exp (ν * (T - s)) * B * (1 + (ν * (τ - r)) ^ (-(1 / 2 : ℝ))) := by ring
  -- the factor κ(r) = -1/(2√(ν(τ-r))) is continuous on (s, τ)
  have hsq : Continuous (fun r : ℝ => Real.sqrt (ν * (τ - r))) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).sqrt
  have hκc : ContinuousOn (fun r : ℝ => (-1 / (2 * Real.sqrt (ν * (τ - r))))) (Ioo s τ) := by
    refine ContinuousOn.div continuousOn_const ((hsq.const_mul 2).continuousOn) ?_
    intro r hr
    exact (mul_pos two_pos (Real.sqrt_pos.2 (mul_pos hν (by linarith [hr.2])))).ne'
  -- the factor J(r) = ∫ w_i K_1(w) ∂_iF(r)(x - √(ν(τ-r)) w) dw is continuous on (s, τ)
  have hJc : ContinuousOn (fun r : ℝ => ∫ w : Pl, ![w.1, w.2] i * heatK 1 w *
      B0579.pd i (F r) (x - Real.sqrt (ν * (τ - r)) • w)) (Ioo s τ) := by
    refine continuousOn_of_dominated (bound := fun w : Pl => |![w.1, w.2] i| * heatK 1 w * B)
      ?_ ?_ ?_ ?_
    · intro r hr
      have hrI : r ∈ Icc s T := ⟨hr.1.le, hr.2.le.trans hτ.2⟩
      have hc : Continuous (fun w : Pl =>
          B0579.pd i (F r) (x - Real.sqrt (ν * (τ - r)) • w)) :=
        (pd_slice hF i hrI).comp (continuous_const.sub
          ((hsq.comp continuous_const).smul continuous_id))
      exact (((UnforcedLeray.Short.IIb.CylPDE.CC.hv_coord i).mul
        HC.heatK1_continuous).mul hc).aestronglyMeasurable
    · intro r hr
      have hrI : r ∈ Icc s T := ⟨hr.1.le, hr.2.le.trans hτ.2⟩
      refine ae_of_all _ fun w => ?_
      have hK1 : 0 < heatK 1 w := (heatKernelMoments 1 one_pos).1 w
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hK1]
      exact mul_le_mul_of_nonneg_left (HC.gbound ((hb r hrI).2 i) _)
        (mul_nonneg (abs_nonneg _) hK1.le)
    · exact (UnforcedLeray.Short.IIb.CylPDE.CC.abs_coord_int i).mul_const B
    · refine ae_of_all _ fun w => ?_
      refine continuousOn_const.mul ?_
      have hmap : ContinuousOn (fun r : ℝ =>
          ((r, x - Real.sqrt (ν * (τ - r)) • w) : ℝ × Pl)) (Ioo s τ) :=
        (continuous_id.prodMk (continuous_const.sub (hsq.smul continuous_const))).continuousOn
      exact (hF.contdF i).comp hmap
        (fun r hr => ⟨⟨hr.1.le, hr.2.le.trans hτ.2⟩, mem_univ _⟩)
  -- the integrand is κ · J on (s, τ), hence continuous there
  have hfc : ContinuousOn (fun r : ℝ => heatSGd i (ν * (τ - r)) (B0579.pd i (F r)) x)
      (Ioo s τ) := by
    refine (hκc.mul hJc).congr ?_
    intro r hr
    exact scaled_deriv (mul_pos hν (by linarith [hr.2])) i _ x
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hsτ]
  refine Integrable.mono' hD (hfc.aestronglyMeasurable measurableSet_Ioo) ?_
  exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr => hbd r hr)

end UnforcedLeray.Short.IIb.CylPDE
