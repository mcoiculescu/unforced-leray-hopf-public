import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.lineInterpPer

/-!
# Part II-b, task `PartII-b:T13/1/5/4` (`CgiAprioriQ`): the `q`-direction a priori leaf

Source of record: `the November 2 reference manuscript` lines 1932-1935.
For fixed `(s, η)` the line `q ↦ w (s, (q, η))` is `C²` and `c`-periodic, so the one-dimensional
periodic interpolation `lineInterpPer_proof` applies on the cell `Ico (-c/2) (c/2)`. Raising to
the `r`-th power, integrating over `(s, η)` (Minkowski on `ℝ × ℝ`) and using that the `c⁻¹`
normalisation of `cylMeas c` cancels on both sides gives the constant `C` of `LineInterpPer`,
independent of `c`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace CgiQ

theorem eLpNorm_ofReal_eq {α : Type*} [MeasurableSpace α] (r : ℝ) (hr : 0 < r)
    (f : α → ℂ) (μ : Measure α) :
    eLpNorm f (ENNReal.ofReal r) μ = (∫⁻ t, ‖f t‖ₑ ^ r ∂μ) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr.le]

theorem inv_rpow_rpow {r : ℝ} (hr : 0 < r) (x : ℝ≥0∞) : (x ^ (1 / r)) ^ r = x := by
  rw [one_div]; exact ENNReal.rpow_inv_rpow hr.ne' x

theorem rpow_rpow_inv_r {r : ℝ} (hr : 0 < r) (x : ℝ≥0∞) : (x ^ r) ^ (1 / r) = x := by
  rw [one_div]; exact ENNReal.rpow_rpow_inv hr.ne' x

theorem diff_of {F : Coord → ℂ} (hF : ContDiff ℝ ∞ F) : Differentiable ℝ F :=
  hF.differentiable (by simp)

theorem cdv_contDiff (F : Coord → ℂ) (hF : ContDiff ℝ ∞ F) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j F) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := ContDiff.fderiv_right (m := ∞) hF (by simp)
  exact h1.clm_apply contDiff_const

theorem slice_hasDerivAt (F : Coord → ℂ) (hF : Differentiable ℝ F) (s η t : ℝ) :
    HasDerivAt (fun t => F (s, (t, η))) (cdv 1 F (s, (t, η))) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((s, (t, η)) : Coord)) (cdir 1) t := by
    have h := (hasDerivAt_const t s).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t η))
    exact h
  exact (hF (s, (t, η))).hasFDerivAt.comp_hasDerivAt t h1

theorem slice_periodic {c r : ℝ} {w : Coord → ℂ} (hw : CgiNice c r w) (s η : ℝ) :
    ∀ t, (fun t => w (s, (t, η))) (t + c) = (fun t => w (s, (t, η))) t :=
  fun t => hw.periodic (s, (t, η))

theorem slice_contDiff {c r : ℝ} {w : Coord → ℂ} (hw : CgiNice c r w) (s η : ℝ) :
    ContDiff ℝ 2 (fun t => w (s, (t, η))) := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => ((s, (t, η)) : Coord)) :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  exact (hw.smooth.comp hp).of_le (by simp)

theorem deriv_slice {w : Coord → ℂ} (hw : ContDiff ℝ ∞ w) (s η : ℝ) :
    deriv (fun t => w (s, (t, η))) = fun t => cdv 1 w (s, (t, η)) := by
  funext t
  exact (slice_hasDerivAt w (diff_of hw) s η t).deriv

theorem deriv_deriv_slice {w : Coord → ℂ} (hw : ContDiff ℝ ∞ w) (s η : ℝ) :
    deriv (deriv (fun t => w (s, (t, η)))) = fun t => cdv 1 (cdv 1 w) (s, (t, η)) := by
  rw [deriv_slice hw s η]
  funext t
  exact (slice_hasDerivAt (cdv 1 w) (diff_of (cdv_contDiff w hw 1)) s η t).deriv

/-- Slice `L^r` power on the `q`-cell at fixed `(s, η)`. -/
def slQ (c r : ℝ) (G : Coord → ℂ) (s η : ℝ) : ℝ≥0∞ :=
  ∫⁻ q in Ico (-c / 2) (c / 2), ‖G (s, (q, η))‖ₑ ^ r

/-- The iterated slice integral `∫ ds ∫ dη ∫_cell`. -/
def MQ (c r : ℝ) (G : Coord → ℂ) : ℝ≥0∞ := ∫⁻ s, ∫⁻ η, slQ c r G s η

/-- The plane measure on `(s, η)`. -/
abbrev planeMeas : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)

theorem slQ_measurable {c r : ℝ} {G : Coord → ℂ} (hG : Continuous G) :
    Measurable (fun z : ℝ × ℝ => slQ c r G z.1 z.2) := by
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => G (p.1.1, (p.2, p.1.2))) :=
    hG.comp (by fun_prop)
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ => ‖G (p.1.1, (p.2, p.1.2))‖ₑ ^ r) :=
    (hc.measurable.enorm).pow_const r
  exact hm.lintegral_prod_right'

theorem cylNorm_eq {c r : ℝ} (hr : 0 < r) (G : Coord → ℂ) (hG : Continuous G) :
    cylNorm c r G = (ENNReal.ofReal c⁻¹ * MQ c r G) ^ (1 / r) := by
  have hm : Measurable (fun x : Coord => ‖G x‖ₑ ^ r) :=
    (hG.measurable.enorm).pow_const r
  have key : ∀ s : ℝ, ∫⁻ z, ‖G (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ η, slQ c r G s η := by
    intro s
    have hf : Measurable (fun z : ℝ × ℝ => ‖G (s, z)‖ₑ ^ r) :=
      (hG.comp (by fun_prop : Continuous fun z : ℝ × ℝ => (s, z))).measurable.enorm.pow_const r
    have hf' : Measurable (fun p : ℝ × ℝ => ‖G (s, (p.1, p.2))‖ₑ ^ r) :=
      (hG.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (s, (p.1, p.2)))).measurable.enorm.pow_const r
    calc ∫⁻ z, ‖G (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)
        = ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖G (s, z)‖ₑ ^ r :=
          UnforcedLeray.Cyl.lintegral_avgμ (fun z : ℝ × ℝ => ‖G (s, z)‖ₑ ^ r)
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, ‖G (s, (q, η))‖ₑ ^ r := by
          rw [UnforcedLeray.Cyl.lintegral_cell_eq hf.aemeasurable]
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ η, slQ c r G s η := by
          congr 1
          exact lintegral_lintegral_swap (f := fun q η : ℝ => ‖G (s, (q, η))‖ₑ ^ r)
            hf'.aemeasurable
  have hcyl : ∫⁻ t, ‖G t‖ₑ ^ r ∂(cylMeas c) =
      ∫⁻ s, ∫⁻ z, ‖G (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) := by
    unfold cylMeas
    exact lintegral_prod (fun x : Coord => ‖G x‖ₑ ^ r) hm.aemeasurable
  show eLpNorm G (ENNReal.ofReal r) (cylMeas c) = _
  rw [eLpNorm_ofReal_eq r hr]
  congr 1
  unfold MQ
  rw [hcyl]
  simp only [key]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Minkowski on `ℝ × ℝ` for the slice powers, with the constant of the slice inequality. -/
theorem mq_bound {c r : ℝ} (hr : 1 < r) {G1 G2 Gw : Coord → ℂ}
    (h1 : Continuous G1) (h2 : Continuous G2) (hw : Continuous Gw) {K a b : ℝ≥0∞}
    (hslice : ∀ s η : ℝ, slQ c r G1 s η ^ (1 / r) ≤
      K * (a * slQ c r Gw s η ^ (1 / r) + b * slQ c r G2 s η ^ (1 / r))) :
    MQ c r G1 ^ (1 / r) ≤ K * (a * MQ c r Gw ^ (1 / r) + b * MQ c r G2 ^ (1 / r)) := by
  have hr0 : 0 < r := by linarith
  have hone : 0 ≤ 1 / r := one_div_nonneg.mpr hr0.le
  have hM : ∀ G : Coord → ℂ, Continuous G →
      MQ c r G = ∫⁻ z, slQ c r G z.1 z.2 ∂planeMeas := by
    intro G hG
    exact (lintegral_prod (fun z : ℝ × ℝ => slQ c r G z.1 z.2)
      (slQ_measurable hG).aemeasurable).symm
  rw [hM G1 h1, hM G2 h2, hM Gw hw]
  have hfwm : Measurable (fun z : ℝ × ℝ => slQ c r Gw z.1 z.2) := slQ_measurable hw
  have hf2m : Measurable (fun z : ℝ × ℝ => slQ c r G2 z.1 z.2) := slQ_measurable h2
  have hXm : Measurable (fun z : ℝ × ℝ => a * slQ c r Gw z.1 z.2 ^ (1 / r)) :=
    (hfwm.pow_const _).const_mul a
  have hYm : Measurable (fun z : ℝ × ℝ => b * slQ c r G2 z.1 z.2 ^ (1 / r)) :=
    (hf2m.pow_const _).const_mul b
  have hpt : ∀ z : ℝ × ℝ, slQ c r G1 z.1 z.2 ≤
      K ^ r * (a * slQ c r Gw z.1 z.2 ^ (1 / r) + b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r := by
    intro z
    have h' := ENNReal.rpow_le_rpow (hslice z.1 z.2) hr0.le
    rw [inv_rpow_rpow hr0, ENNReal.mul_rpow_of_nonneg _ _ hr0.le] at h'
    exact h'
  have hmeasJ : Measurable (fun z : ℝ × ℝ =>
      (a * slQ c r Gw z.1 z.2 ^ (1 / r) + b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r) :=
    ((hXm.add hYm)).pow_const r
  have hint : ∫⁻ z, slQ c r G1 z.1 z.2 ∂planeMeas ≤
      K ^ r * ∫⁻ z, (a * slQ c r Gw z.1 z.2 ^ (1 / r) + b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r
        ∂planeMeas := by
    rw [← lintegral_const_mul _ hmeasJ]
    exact lintegral_mono hpt
  have hMin := ENNReal.lintegral_Lp_add_le (μ := planeMeas) (p := r)
    (f := fun z : ℝ × ℝ => a * slQ c r Gw z.1 z.2 ^ (1 / r))
    (g := fun z : ℝ × ℝ => b * slQ c r G2 z.1 z.2 ^ (1 / r))
    hXm.aemeasurable hYm.aemeasurable hr.le
  simp only [Pi.add_apply] at hMin
  have hXint : ∫⁻ z, (a * slQ c r Gw z.1 z.2 ^ (1 / r)) ^ r ∂planeMeas =
      a ^ r * ∫⁻ z, slQ c r Gw z.1 z.2 ∂planeMeas := by
    have e : ∀ z : ℝ × ℝ, (a * slQ c r Gw z.1 z.2 ^ (1 / r)) ^ r =
        a ^ r * slQ c r Gw z.1 z.2 := by
      intro z
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, inv_rpow_rpow hr0]
    simp_rw [e]
    exact lintegral_const_mul _ hfwm
  have hYint : ∫⁻ z, (b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r ∂planeMeas =
      b ^ r * ∫⁻ z, slQ c r G2 z.1 z.2 ∂planeMeas := by
    have e : ∀ z : ℝ × ℝ, (b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r =
        b ^ r * slQ c r G2 z.1 z.2 := by
      intro z
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, inv_rpow_rpow hr0]
    simp_rw [e]
    exact lintegral_const_mul _ hf2m
  have hX1 : (a ^ r * ∫⁻ z, slQ c r Gw z.1 z.2 ∂planeMeas) ^ (1 / r) =
      a * (∫⁻ z, slQ c r Gw z.1 z.2 ∂planeMeas) ^ (1 / r) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hone, rpow_rpow_inv_r hr0]
  have hY1 : (b ^ r * ∫⁻ z, slQ c r G2 z.1 z.2 ∂planeMeas) ^ (1 / r) =
      b * (∫⁻ z, slQ c r G2 z.1 z.2 ∂planeMeas) ^ (1 / r) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hone, rpow_rpow_inv_r hr0]
  calc (∫⁻ z, slQ c r G1 z.1 z.2 ∂planeMeas) ^ (1 / r)
      ≤ (K ^ r * ∫⁻ z, (a * slQ c r Gw z.1 z.2 ^ (1 / r) + b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r
          ∂planeMeas) ^ (1 / r) := ENNReal.rpow_le_rpow hint hone
    _ = K * (∫⁻ z, (a * slQ c r Gw z.1 z.2 ^ (1 / r) + b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r
          ∂planeMeas) ^ (1 / r) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hone, rpow_rpow_inv_r hr0]
    _ ≤ K * ((∫⁻ z, (a * slQ c r Gw z.1 z.2 ^ (1 / r)) ^ r ∂planeMeas) ^ (1 / r) +
          (∫⁻ z, (b * slQ c r G2 z.1 z.2 ^ (1 / r)) ^ r ∂planeMeas) ^ (1 / r)) :=
          mul_le_mul_of_nonneg_left hMin zero_le
    _ = K * (a * (∫⁻ z, slQ c r Gw z.1 z.2 ∂planeMeas) ^ (1 / r) +
          b * (∫⁻ z, slQ c r G2 z.1 z.2 ∂planeMeas) ^ (1 / r)) := by
          rw [hXint, hYint, hX1, hY1]

end CgiQ

/-- **Leaf (A, `q` direction).** The `q`-derivative of a nice `w` is controlled by the interpolation
inequality along each `q`-line, integrated over `(s, η)`. -/
theorem cgiAprioriQ_proof : UnforcedLeray.Short.IIb.CgiAprioriQ := by
  unfold UnforcedLeray.Short.IIb.CgiAprioriQ
  intro r hr
  obtain ⟨C0, hC0, hL⟩ := lineInterpPer_proof r hr
  have hr0 : 0 < r := by linarith
  refine ⟨C0, hC0, fun c hc w hw lam hlam => ?_⟩
  have hwS : ContDiff ℝ ∞ w := hw.smooth
  have hF1 : ContDiff ℝ ∞ (cdv 1 w) := CgiQ.cdv_contDiff w hwS 1
  have hF2 : ContDiff ℝ ∞ (cdv 1 (cdv 1 w)) := CgiQ.cdv_contDiff _ hF1 1
  have hslice : ∀ s η : ℝ, CgiQ.slQ c r (cdv 1 w) s η ^ (1 / r) ≤
      ENNReal.ofReal C0 * (ENNReal.ofReal lam⁻¹ * CgiQ.slQ c r w s η ^ (1 / r) +
        ENNReal.ofReal lam * CgiQ.slQ c r (cdv 1 (cdv 1 w)) s η ^ (1 / r)) := by
    intro s η
    have h := hL c hc (fun t => w (s, (t, η))) (CgiQ.slice_contDiff hw s η)
      (CgiQ.slice_periodic hw s η) lam hlam
    rw [CgiQ.deriv_deriv_slice hwS s η, CgiQ.deriv_slice hwS s η] at h
    simp only [CgiQ.eLpNorm_ofReal_eq r hr0] at h
    exact h
  have hmain := CgiQ.mq_bound hr hF1.continuous hF2.continuous hwS.continuous hslice
  rw [CgiQ.cylNorm_eq hr0 _ hF1.continuous, CgiQ.cylNorm_eq hr0 _ hwS.continuous,
    CgiQ.cylNorm_eq hr0 _ hF2.continuous]
  have h1r : 0 ≤ 1 / r := one_div_nonneg.mpr hr0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1r, ENNReal.mul_rpow_of_nonneg _ _ h1r,
    ENNReal.mul_rpow_of_nonneg _ _ h1r]
  refine (mul_le_mul_of_nonneg_left hmain zero_le).trans (le_of_eq ?_)
  ring

end UnforcedLeray.Short.IIb
