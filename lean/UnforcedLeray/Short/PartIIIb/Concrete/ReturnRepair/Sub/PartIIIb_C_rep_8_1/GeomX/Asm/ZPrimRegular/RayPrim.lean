import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.RayFTC
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `PartIII-b:C/rep/8/1/1/1/asm/4`: the deterministic half of `ZPrimRegular`

Source `shorter-proof-2026-11-02.tex` lines 4178-4186.  Ray decay `|Z| ≤ K ρ⁻⁴`, `|DZ| ≤ K ρ⁻⁵`
on a neighbourhood of the ray, together with differentiability, give `PrimData`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace GeomXAsm

namespace RayPrimAux

open RayFTCAux

/-- Decay and differentiability of `Z τ` on `[r₀, ∞) × (z - δ, z + δ)` of the half plane. -/
def RayDecay (Z : ℝ → Space → Space) (τ r₀ z δ K : ℝ) : Prop :=
  (∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ, |z' - z| < δ → DifferentiableAt ℝ (Z τ) (hpt ρ z')) ∧
  (∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ, |z' - z| < δ → ‖Z τ (hpt ρ z')‖ ≤ K * ρ ^ (-4 : ℝ)) ∧
  (∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ, |z' - z| < δ →
    ‖fderiv ℝ (Z τ) (hpt ρ z')‖ ≤ K * ρ ^ (-5 : ℝ))

theorem hasDerivAt_hpt_z (ρ t : ℝ) : HasDerivAt (fun s => hpt ρ s) (coordinateVector 2) t := by
  have h' : (fun s => hpt ρ s) = fun s : ℝ => ρ • (coordinateVector 0 : Space) + s • (coordinateVector 2 : Space) :=
    funext fun s => hpt_eq_lin ρ s
  rw [h']
  have h : HasDerivAt (fun s : ℝ => ρ • (coordinateVector 0 : Space) + s • (coordinateVector 2 : Space))
      ((1 : ℝ) • (coordinateVector 2 : Space)) t :=
    ((hasDerivAt_id t).smul_const (coordinateVector 2 : Space)).const_add _
  simpa using h

theorem continuous_hpt_pair : Continuous fun p : ℝ × ℝ => hpt p.1 p.2 := by
  have h' : (fun p : ℝ × ℝ => hpt p.1 p.2) =
      fun p : ℝ × ℝ => p.1 • (coordinateVector 0 : Space) + p.2 • (coordinateVector 2 : Space) :=
    funext fun p => hpt_eq_lin p.1 p.2
  rw [h']
  fun_prop

/-- `f ρ z' = ρ Z_z(ρ,0,z')`. -/
def fR (Z : ℝ → Space → Space) (τ : ℝ) (ρ z' : ℝ) : ℝ := ρ * Z τ (hpt ρ z') 2

/-- `g ρ z' = ρ ∂_z Z_z(ρ,0,z')`. -/
def gR (Z : ℝ → Space → Space) (τ : ℝ) (ρ z' : ℝ) : ℝ :=
  ρ * fderiv ℝ (Z τ) (hpt ρ z') (coordinateVector 2) 2

theorem rpow_mul_rpow (ρ : ℝ) (hρ : 0 < ρ) (a : ℝ) : ρ * ρ ^ a = ρ ^ (a + 1) := by
  rw [Real.rpow_add hρ, Real.rpow_one, mul_comm]

variable {Z : ℝ → Space → Space} {τ r₀ z δ K : ℝ}

theorem fR_bound (h : RayDecay Z τ r₀ z δ K) {ρ z' : ℝ} (hρ : r₀ ≤ ρ) (hr₀ : 0 < r₀)
    (hz : |z' - z| < δ) : ‖fR Z τ ρ z'‖ ≤ K * ρ ^ (-3 : ℝ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
  have h1 := h.2.1 ρ hρ z' hz
  have h2 : |Z τ (hpt ρ z') 2| ≤ ‖Z τ (hpt ρ z')‖ := by
    have := PiLp.norm_apply_le (Z τ (hpt ρ z')) 2
    rwa [Real.norm_eq_abs] at this
  unfold fR
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
  calc ρ * |Z τ (hpt ρ z') 2| ≤ ρ * (K * ρ ^ (-4 : ℝ)) := by gcongr; exact h2.trans h1
    _ = K * ρ ^ (-3 : ℝ) := by
        rw [← mul_assoc, mul_comm ρ K, mul_assoc, rpow_mul_rpow ρ hρ0]; norm_num

theorem gR_bound (h : RayDecay Z τ r₀ z δ K) {ρ z' : ℝ} (hρ : r₀ ≤ ρ) (hr₀ : 0 < r₀)
    (hz : |z' - z| < δ) : ‖gR Z τ ρ z'‖ ≤ K * ρ ^ (-4 : ℝ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
  have h1 := h.2.2 ρ hρ z' hz
  have h2 : |fderiv ℝ (Z τ) (hpt ρ z') (coordinateVector 2) 2| ≤
      ‖fderiv ℝ (Z τ) (hpt ρ z')‖ := by
    have := PiLp.norm_apply_le (fderiv ℝ (Z τ) (hpt ρ z') (coordinateVector 2)) 2
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc ‖fderiv ℝ (Z τ) (hpt ρ z') (coordinateVector 2)‖
        ≤ ‖fderiv ℝ (Z τ) (hpt ρ z')‖ * ‖(coordinateVector 2 : Space)‖ :=
          (fderiv ℝ (Z τ) (hpt ρ z')).le_opNorm _
      _ = _ := by rw [norm_e, mul_one]
  unfold gR
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
  calc ρ * |fderiv ℝ (Z τ) (hpt ρ z') (coordinateVector 2) 2| ≤ ρ * (K * ρ ^ (-5 : ℝ)) := by
        gcongr; exact h2.trans h1
    _ = K * ρ ^ (-4 : ℝ) := by
        rw [← mul_assoc, mul_comm ρ K, mul_assoc, rpow_mul_rpow ρ hρ0]; norm_num

theorem continuousOn_fR (h : RayDecay Z τ r₀ z δ K) {z' : ℝ} (hz : |z' - z| < δ) :
    ContinuousOn (fun ρ => fR Z τ ρ z') (Ici r₀) := by
  intro ρ hρ
  have hc : ContinuousAt (fun ρ => Z τ (hpt ρ z')) ρ :=
    ContinuousAt.comp (g := Z τ) (f := fun ρ => hpt ρ z') (h.1 ρ hρ z' hz).continuousAt
      (continuous_hpt' z').continuousAt
  have : ContinuousAt (fun ρ => fR Z τ ρ z') ρ := by
    unfold fR
    exact continuousAt_id.mul
      (((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.continuousAt).comp hc)
  exact this.continuousWithinAt

theorem integrableOn_fR (h : RayDecay Z τ r₀ z δ K) (hr₀ : 0 < r₀) {a z' : ℝ} (ha : r₀ ≤ a)
    (hz : |z' - z| < δ) : IntegrableOn (fun ρ => fR Z τ ρ z') (Ioi a) := by
  have hint : IntegrableOn (fun ρ : ℝ => K * ρ ^ (-3 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le hr₀ ha)).const_mul K
  refine Integrable.mono' hint ?_ ?_
  · exact ((continuousOn_fR h hz).mono (fun x hx => le_trans ha (le_of_lt hx))).aestronglyMeasurable
      measurableSet_Ioi
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun ρ hρ =>
      fR_bound h (le_trans ha (le_of_lt hρ)) hr₀ hz)

theorem measurable_gR (Z : ℝ → Space → Space) (τ z' : ℝ) :
    Measurable fun ρ => gR Z τ ρ z' := by
  unfold gR
  have hA : Measurable fun t : ℝ => fderiv ℝ (Z τ) (hpt t z') :=
    (measurable_fderiv (𝕜 := ℝ) (f := Z τ)).comp (measurable_hpt' z')
  have hB : Measurable fun t : ℝ => fderiv ℝ (Z τ) (hpt t z') (coordinateVector 2) 2 :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable).comp
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector 2)).continuous.measurable.comp hA)
  exact measurable_id.mul hB

theorem integrableOn_gR (h : RayDecay Z τ r₀ z δ K) (hr₀ : 0 < r₀) {a z' : ℝ} (ha : r₀ ≤ a)
    (hz : |z' - z| < δ) : IntegrableOn (fun ρ => gR Z τ ρ z') (Ioi a) := by
  have hint : IntegrableOn (fun ρ : ℝ => K * ρ ^ (-4 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le hr₀ ha)).const_mul K
  refine Integrable.mono' hint (measurable_gR Z τ z').aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun ρ hρ =>
      gR_bound h (le_trans ha (le_of_lt hρ)) hr₀ hz)

theorem hasDerivAt_fR (h : RayDecay Z τ r₀ z δ K) {ρ z' : ℝ} (hρ : r₀ ≤ ρ) (hz : |z' - z| < δ) :
    HasDerivAt (fun t => fR Z τ ρ t) (gR Z τ ρ z') z' := by
  have h1 := ((h.1 ρ hρ z' hz).hasFDerivAt).comp_hasDerivAt z' (hasDerivAt_hpt_z ρ z')
  have h2 := ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt z' h1
  have h3 := h2.const_mul ρ
  exact h3

theorem hasDerivAt_F (h : RayDecay Z τ r₀ z δ K) (hr₀ : 0 < r₀) (hδ : 0 < δ) {r : ℝ}
    (hr : r₀ ≤ r) :
    HasDerivAt (fun z' => ∫ ρ in Ioi r, fR Z τ ρ z') (∫ ρ in Ioi r, gR Z τ ρ z) z := by
  have hz0 : |z - z| < δ := by simpa using hδ
  have hbd : IntegrableOn (fun ρ : ℝ => K * ρ ^ (-4 : ℝ)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le hr₀ hr)).const_mul K
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi r))
    (F := fun z' ρ => fR Z τ ρ z') (F' := fun z' ρ => gR Z τ ρ z') (x₀ := z)
    (s := ball z δ) (bound := fun ρ => K * ρ ^ (-4 : ℝ)) (ball_mem_nhds z hδ)
    (Filter.eventually_of_mem (ball_mem_nhds z hδ) fun x hx =>
      (integrableOn_fR h hr₀ hr (by simpa [Real.dist_eq] using hx)).aestronglyMeasurable)
    (integrableOn_fR h hr₀ hr hz0) (measurable_gR Z τ z).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun ρ hρ x hx =>
      gR_bound h (le_trans hr (le_of_lt hρ)) hr₀ (by simpa [Real.dist_eq] using hx))) hbd
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun ρ hρ x hx =>
      hasDerivAt_fR h (le_trans hr (le_of_lt hρ)) (by simpa [Real.dist_eq] using hx)))
  exact this.2

/-- `∫_{(a,∞)} - ∫_{(b,∞)} = ∫_a^b`. -/
theorem S_sub (h : RayDecay Z τ r₀ z δ K) (hr₀ : 0 < r₀) {a b z' : ℝ} (ha : r₀ ≤ a)
    (hb : r₀ ≤ b) (hz : |z' - z| < δ) :
    (∫ ρ in Ioi a, fR Z τ ρ z') - ∫ ρ in Ioi b, fR Z τ ρ z' =
      ∫ ρ in a..b, fR Z τ ρ z' := by
  have key : ∀ {a b : ℝ}, r₀ ≤ a → a ≤ b →
      (∫ ρ in Ioi a, fR Z τ ρ z') - ∫ ρ in Ioi b, fR Z τ ρ z' =
        ∫ ρ in a..b, fR Z τ ρ z' := by
    intro a b ha hab
    have hI := integrableOn_fR h hr₀ ha hz
    rw [intervalIntegral.integral_of_le hab]
    have hU := setIntegral_union (μ := volume) (f := fun ρ => fR Z τ ρ z') (s := Ioc a b) (t := Ioi b)
      (Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx') measurableSet_Ioi
      (hI.mono_set Set.Ioc_subset_Ioi_self) (hI.mono_set (Set.Ioi_subset_Ioi hab))
    rw [Set.Ioc_union_Ioi_eq_Ioi hab] at hU
    rw [hU]; ring
  rcases le_total a b with hab | hab
  · exact key ha hab
  · have := key hb hab
    rw [intervalIntegral.integral_symm]
    linarith

theorem continuousAt_fR_pair (h : RayDecay Z τ r₀ z δ K) (hδ : 0 < δ) {r : ℝ} (hr : r₀ ≤ r) :
    ContinuousAt (fun p : ℝ × ℝ => fR Z τ p.1 p.2) (r, z) := by
  have hz0 : |z - z| < δ := by simpa using hδ
  have hc : ContinuousAt (fun p : ℝ × ℝ => Z τ (hpt p.1 p.2)) (r, z) :=
    ContinuousAt.comp (g := Z τ) (f := fun p : ℝ × ℝ => hpt p.1 p.2)
      (h.1 r hr z hz0).continuousAt continuous_hpt_pair.continuousAt
  unfold fR
  exact continuousAt_fst.mul
    (((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.continuousAt).comp hc)

theorem hasFDerivAt_H (h : RayDecay Z τ r₀ z δ K) (hr₀ : 0 < r₀) (hδ : 0 < δ) {r : ℝ}
    (hr : r₀ < r) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ ρ in r..p.1, fR Z τ ρ p.2)
      ((fR Z τ r z) • ContinuousLinearMap.fst ℝ ℝ ℝ) (r, z) := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hcont := continuousAt_fR_pair h hδ hr.le
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ξ, hξ, hξ'⟩ := hcont c hc
  filter_upwards [Metric.ball_mem_nhds (r, z) (lt_min hξ (lt_min hδ (sub_pos.2 hr)))] with p hp
  rw [Metric.mem_ball, lt_min_iff, lt_min_iff] at hp
  obtain ⟨hpξ, hpδ, hpr⟩ := hp
  have d1 : |p.1 - r| ≤ dist p (r, z) := by
    rw [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have d2 : |p.2 - z| ≤ dist p (r, z) := by
    rw [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
  have hz' : |p.2 - z| < δ := lt_of_le_of_lt d2 hpδ
  have hp1 : r₀ ≤ p.1 := by
    have := (abs_lt.1 (lt_of_le_of_lt d1 hpr)).1
    linarith
  have hsub : uIcc r p.1 ⊆ Ici r₀ := by
    intro x hx
    rcases (Set.mem_uIcc.1 hx) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact le_trans hr.le h1
    · exact le_trans hp1 h1
  have hint : IntervalIntegrable (fun ρ => fR Z τ ρ p.2) volume r p.1 :=
    ((continuousOn_fR h hz').mono hsub).intervalIntegrable
  have hkey : (∫ ρ in r..p.1, fR Z τ ρ p.2) - (p.1 - r) * fR Z τ r z =
      ∫ ρ in r..p.1, (fR Z τ ρ p.2 - fR Z τ r z) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  have hbd : ‖∫ ρ in r..p.1, (fR Z τ ρ p.2 - fR Z τ r z)‖ ≤ c * |p.1 - r| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have hx' : |x - r| ≤ |p.1 - r| := by
      rcases Set.mem_uIoc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have hd : dist (x, p.2) (r, z) < ξ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · exact lt_of_le_of_lt (hx'.trans d1) hpξ
      · exact lt_of_le_of_lt d2 hpξ
    have := hξ' hd
    rw [Real.dist_eq] at this
    exact le_of_lt (by simpa [Real.norm_eq_abs] using this)
  have hH0 : ∫ ρ in r..r, fR Z τ ρ z = 0 := intervalIntegral.integral_same
  simp only [hH0, sub_zero, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    Prod.fst_sub, smul_eq_mul]
  rw [mul_comm (fR Z τ r z), hkey]
  refine hbd.trans ?_
  have : |p.1 - r| ≤ ‖p - (r, z)‖ := by
    have := norm_fst_le (p - (r, z))
    simpa [Real.norm_eq_abs] using this
  exact mul_le_mul_of_nonneg_left this hc.le

theorem primData_of_decay (h : RayDecay Z τ r₀ z δ K) (hr₀ : 0 < r₀) (hδ : 0 < δ) {r : ℝ}
    (hr : r₀ < r) : PrimData Z τ r z := by
  have hz0 : |z - z| < δ := by simpa using hδ
  refine ⟨integrableOn_fR h hr₀ hr.le hz0, integrableOn_gR h hr₀ hr.le hz0, ?_⟩
  have hF := (hasDerivAt_F h hr₀ hδ hr.le).comp_hasFDerivAt (f := fun p : ℝ × ℝ => p.2) (r, z)
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hH := hasFDerivAt_H h hr₀ hδ hr
  have hΨ := hF.neg.add hH
  have hev : (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2) =ᶠ[𝓝 (r, z)]
      fun p : ℝ × ℝ => -((fun z' => ∫ ρ in Ioi r, fR Z τ ρ z') ∘ (fun p : ℝ × ℝ => p.2)) p +
        ∫ ρ in r..p.1, fR Z τ ρ p.2 := by
    have hn : {p : ℝ × ℝ | |p.1 - r| < r - r₀ ∧ |p.2 - z| < δ} ∈ 𝓝 (r, z) := by
      have h1 : IsOpen {p : ℝ × ℝ | |p.1 - r| < r - r₀ ∧ |p.2 - z| < δ} :=
        (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const).inter
          (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const)
      exact h1.mem_nhds ⟨by simpa using sub_pos.2 hr, by simpa using hδ⟩
    filter_upwards [hn] with p hp
    have hp1 : r₀ ≤ p.1 := by
      have := (abs_lt.1 hp.1).1
      linarith
    have := S_sub h hr₀ (a := r) (b := p.1) hr.le hp1 hp.2
    simp only [Function.comp]
    unfold outPrim
    have e : (fun ρ => ρ * Z τ !₂[ρ, 0, p.2] 2) = fun ρ => fR Z τ ρ p.2 := rfl
    rw [e]
    linarith
  refine (hΨ.congr_of_eventuallyEq hev).congr_fderiv ?_
  ext1 <;> simp [primDz, gR, fR]

end RayPrimAux

end GeomXAsm

end UnforcedLeray.Short.PartIIIb.Concrete
