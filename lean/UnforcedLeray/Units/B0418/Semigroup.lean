import UnforcedLeray.Units.B0418.Continuity

/-!
# B0418 helper: the free similarity semigroup `S_ν(r)` on `L^p`, `1 ≤ p < ∞`

Blueprint unit B0418, `eq:free-stress-7`, `paper/main.tex` lines 7411--7427:
`S_ν(r)h(y) = e^{r/2} [e^{ν(e^r-1)Δ} h](e^{r/2} y)`, `r ≥ 0`.
The operator is the library's `AncientLocalization.freeEvolution ν r`
(`lean/UnforcedLeray/Analysis/AncientLocalization/FreeEvolution.lean`), which is reused,
not redefined. This file proves, on every `L^p`, `1 ≤ p < ∞`:

* the semigroup law `S(r₁) S(r₂) = S(r₁ + r₂)` pointwise (intertwining `D_λ H_t = H_{t/λ²} D_λ`
  plus the heat semigroup law), and `S(0) = id`;
* linearity and the `L^p` bound `‖S(r)h‖_p ≤ e^{-γ r} ‖h‖_p`, `γ = (3/p - 1)/2`
  (the dilation Jacobian; this is the content later recorded as B0419);
* strong continuity on `[0, ∞)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0418

open UnforcedLeray.AncientLocalization

variable {p : ℝ≥0∞}

/-- The heat time `ν(e^r - 1)` inside `S_ν(r)`. -/
abbrev heatTime (ν r : ℝ) : ℝ := ν * (Real.exp r - 1)

theorem heatTime_nonneg {ν r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r) : 0 ≤ heatTime ν r :=
  mul_nonneg hν (by linarith [Real.one_le_exp hr])

/-- The literal formula `eq:free-stress-7` for `freeEvolution`. -/
theorem freeEvolution_apply (ν r : ℝ) (h : SpatialField) (y : Space) :
    freeEvolution ν r h y =
      Real.exp (r / 2) • Heat.flow h (ν * (Real.exp r - 1)) (Real.exp (r / 2) • y) := rfl

theorem freeEvolution_eq_smul (ν r : ℝ) (h : SpatialField) :
    freeEvolution ν r h = Real.exp (r / 2) •
      fun y => Heat.flow h (ν * (Real.exp r - 1)) (Real.exp (r / 2) • y) := rfl

/-- `S_ν(r)` preserves `L^p`. -/
theorem freeEvolution_memLp (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField}
    (hh : MemLp h p volume) (ν r : ℝ) : MemLp (freeEvolution ν r h) p volume :=
  SpatialScaling.memLp_spatialScale (flow_memLp hp1 hp hh _) _ (Real.exp_pos _).ne'

/-- Linearity of `S_ν(r)` on `L^p` (subtraction). -/
theorem freeEvolution_sub (hp1 : 1 ≤ p) (hp : p ≠ ∞) {u v : SpatialField}
    (hu : MemLp u p volume) (hv : MemLp v p volume) (ν r : ℝ) :
    freeEvolution ν r (u - v) = freeEvolution ν r u - freeEvolution ν r v := by
  funext y
  simp only [freeEvolution_apply, Pi.sub_apply]
  rw [flow_sub hp1 hp hu hv, Pi.sub_apply, smul_sub]

/-- Homogeneity of `S_ν(r)`. -/
theorem freeEvolution_smul (c : ℝ) (ν r : ℝ) (u : SpatialField) :
    freeEvolution ν r (c • u) = c • freeEvolution ν r u := by
  funext y
  simp only [freeEvolution_apply, Pi.smul_apply]
  rw [flow_smul, Pi.smul_apply, smul_comm]

/-- Additivity of `S_ν(r)` on `L^p`. -/
theorem freeEvolution_add_fun (hp1 : 1 ≤ p) (hp : p ≠ ∞) {u v : SpatialField}
    (hu : MemLp u p volume) (hv : MemLp v p volume) (ν r : ℝ) :
    freeEvolution ν r (u + v) = freeEvolution ν r u + freeEvolution ν r v := by
  have h1 := freeEvolution_sub hp1 hp (hu.add hv) hv ν r
  rw [add_sub_cancel_right] at h1
  rw [h1, sub_add_cancel]

/-- The semigroup law `S_ν(r₁) S_ν(r₂) = S_ν(r₁ + r₂)` on `L^p`, at every point. -/
theorem freeEvolution_add {ν : ℝ} (hν : 0 ≤ ν) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField} (hh : MemLp h p volume) :
    freeEvolution ν r₁ (freeEvolution ν r₂ h) = freeEvolution ν (r₁ + r₂) h := by
  have hsq : Real.exp (r₂ / 2) ^ 2 = Real.exp r₂ := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have htime : Real.exp (r₂ / 2) ^ 2 * (ν * (Real.exp r₁ - 1)) + ν * (Real.exp r₂ - 1) =
      ν * (Real.exp (r₁ + r₂) - 1) := by
    rw [hsq, Real.exp_add]
    ring
  have hscal : Real.exp (r₂ / 2) * Real.exp (r₁ / 2) = Real.exp ((r₁ + r₂) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₁ : 0 ≤ Real.exp (r₂ / 2) ^ 2 * (ν * (Real.exp r₁ - 1)) :=
    mul_nonneg (sq_nonneg _) (heatTime_nonneg hν hr₁)
  funext y
  rw [freeEvolution_apply, freeEvolution_eq_smul ν r₂, flow_smul,
    flow_comp_smul (Real.exp_pos _), flow_add_time h₁ (heatTime_nonneg hν hr₂) hp1 hp hh,
    htime, freeEvolution_apply]
  simp only [Pi.smul_apply, smul_smul]
  rw [mul_comm (Real.exp (r₁ / 2)) (Real.exp (r₂ / 2)), hscal]

/-- `S_ν(0) = id`. -/
theorem freeEvolution_zero' (ν : ℝ) (h : SpatialField) : freeEvolution ν 0 h = h :=
  freeEvolution_zero ν h

/-! ### `L^p` bounds -/

/-- Exact `L^p` transport of `spatialScale`. -/
theorem eLpNorm_spatialScale_Lp (hp : p ≠ ∞) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    (f : SpatialField) :
    eLpNorm (SpatialScaling.spatialScale a b f) p volume =
      ‖a‖ₑ * ((ENNReal.ofReal |(b ^ 3)⁻¹|) ^ (1 / p).toReal * eLpNorm f p volume) := by
  change eLpNorm (a • fun x => f (b • x)) p volume = _
  rw [eLpNorm_const_smul, eLpNorm_comp_dilation hp hb]

/-- For a dilation by `b ≥ 1` the Jacobian factor is at most one. -/
theorem eLpNorm_spatialScale_le (hp : p ≠ ∞) (a : ℝ) {b : ℝ} (hb : 1 ≤ b)
    (f : SpatialField) :
    eLpNorm (SpatialScaling.spatialScale a b f) p volume ≤ ‖a‖ₑ * eLpNorm f p volume := by
  rw [eLpNorm_spatialScale_Lp hp a (by positivity : b ≠ 0)]
  gcongr
  calc (ENNReal.ofReal |(b ^ 3)⁻¹|) ^ (1 / p).toReal * eLpNorm f p volume
      ≤ 1 * eLpNorm f p volume := by
        gcongr
        apply ENNReal.rpow_le_one _ ENNReal.toReal_nonneg
        rw [ENNReal.ofReal_le_one, abs_of_pos (by positivity)]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ hb)
    _ = eLpNorm f p volume := one_mul _

/-- The decay exponent `γ_p = (3/p - 1)/2` of `eq:free-stress-8` (tex line 7368). -/
def gammaExp (p : ℝ≥0∞) : ℝ := (3 / p.toReal - 1) / 2

/-- Exact `L^p` bound `‖S_ν(r)h‖_p ≤ e^{-γ_p r} ‖h‖_p` (heat contraction and Jacobian). -/
theorem eLpNorm_freeEvolution_le (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField}
    (hh : MemLp h p volume) (ν r : ℝ) :
    eLpNorm (freeEvolution ν r h) p volume ≤
      ENNReal.ofReal (Real.exp (-gammaExp p * r)) * eLpNorm h p volume := by
  unfold freeEvolution similarityDilation
  rw [eLpNorm_spatialScale_Lp hp _ (Real.exp_pos _).ne', ← mul_assoc]
  have hc : ‖Real.exp (r / 2)‖ₑ * (ENNReal.ofReal |(Real.exp (r / 2) ^ 3)⁻¹|) ^ (1 / p).toReal =
      ENNReal.ofReal (Real.exp (-gammaExp p * r)) := by
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, abs_of_pos (by positivity),
      ← Real.exp_nat_mul, ← Real.exp_neg,
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    rw [gammaExp, ENNReal.toReal_div, ENNReal.toReal_one]
    push_cast
    ring
  rw [hc]
  gcongr
  exact eLpNorm_flow_le hp1 hp hh _

/-- The crude bound `‖S_ν(r)u‖_p ≤ e^{r/2} ‖u‖_p` for `r ≥ 0`. -/
theorem eLpNorm_freeEvolution_le_exp (hp : p ≠ ∞) (hp1 : 1 ≤ p) {u : SpatialField}
    (hu : MemLp u p volume) (ν : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    eLpNorm (freeEvolution ν r u) p volume ≤
      ENNReal.ofReal (Real.exp (r / 2)) * eLpNorm u p volume := by
  unfold freeEvolution similarityDilation
  refine (eLpNorm_spatialScale_le hp _ (Real.one_le_exp (by linarith)) _).trans ?_
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  gcongr
  exact eLpNorm_flow_le hp1 hp hu _

/-! ### Strong continuity -/

/-- Right continuity of `S_ν` at `r = 0` in `L^p`. -/
theorem tendsto_freeEvolution_sub_self {ν : ℝ} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {h : SpatialField} (hh : MemLp h p volume) :
    Tendsto (fun r => eLpNorm (freeEvolution ν r h - h) p volume) (𝓝[≥] 0) (𝓝 0) := by
  let lam : ℝ → ℝ := fun r => Real.exp (r / 2)
  have hlam : Tendsto lam (𝓝[≥] 0) (𝓝 1) := by
    have hc : Continuous lam := Real.continuous_exp.comp (continuous_id.div_const 2)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
    simpa [lam] using this
  have htau : Tendsto (fun r => ν * (Real.exp r - 1)) (𝓝[≥] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ν * (Real.exp r - 1)) :=
      continuous_const.mul (Real.continuous_exp.sub continuous_const)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
    simpa using this
  -- the three pieces
  have hA : Tendsto (fun r => ENNReal.ofReal (lam r) *
      eLpNorm (Heat.flow h (ν * (Real.exp r - 1)) - h) p volume) (𝓝[≥] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r => ENNReal.ofReal (lam r)) (𝓝[≥] 0) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.tendsto 1).comp hlam
      rw [ENNReal.ofReal_one] at this
      exact this
    have h2 := (tendsto_flow_sub hp1 hp hh).comp htau
    have := ENNReal.Tendsto.mul h1 (Or.inr ENNReal.zero_ne_top) h2 (Or.inr ENNReal.one_ne_top)
    simpa using this
  have hB : Tendsto (fun r => ENNReal.ofReal (lam r - 1) * eLpNorm h p volume)
      (𝓝[≥] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r => ENNReal.ofReal (lam r - 1)) (𝓝[≥] 0) (𝓝 0) := by
      have h0 : Tendsto (fun r => lam r - 1) (𝓝[≥] 0) (𝓝 0) := by
        simpa using hlam.sub_const 1
      have := (ENNReal.continuous_ofReal.tendsto 0).comp h0
      rw [ENNReal.ofReal_zero] at this
      exact this
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hh.2.ne)
    simpa using this
  have hC : Tendsto (fun r => eLpNorm (fun x => h (lam r • x) - h x) p volume)
      (𝓝[≥] 0) (𝓝 0) := (tendsto_dilation hp1 hp hh).comp hlam
  have hsum := hA.add (hB.add hC)
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) ≤ r := hr
  have hl1 : 1 ≤ lam r := Real.one_le_exp (by linarith)
  set F := Heat.flow h (ν * (Real.exp r - 1)) with hF
  have hFm : MemLp F p volume := flow_memLp hp1 hp hh _
  have hdec : freeEvolution ν r h - h =
      SpatialScaling.spatialScale (lam r) (lam r) (F - h) +
        (SpatialScaling.spatialScale (lam r - 1) (lam r) h +
          fun x => h (lam r • x) - h x) := by
    funext x
    simp only [freeEvolution_apply, SpatialScaling.spatialScale, Pi.add_apply, Pi.sub_apply,
      lam, ← hF, smul_sub, sub_smul, one_smul]
    abel
  have hm1 : AEStronglyMeasurable (SpatialScaling.spatialScale (lam r) (lam r) (F - h)) volume :=
    (SpatialScaling.memLp_spatialScale (hFm.sub hh) _ (by positivity)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (SpatialScaling.spatialScale (lam r - 1) (lam r) h) volume :=
    (SpatialScaling.memLp_spatialScale hh _ (by positivity)).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => h (lam r • x) - h x) volume :=
    (SpatialScaling.memLp_comp_dilation hh (by positivity)).aestronglyMeasurable.sub
      hh.aestronglyMeasurable
  rw [hdec]
  calc eLpNorm (SpatialScaling.spatialScale (lam r) (lam r) (F - h) +
        (SpatialScaling.spatialScale (lam r - 1) (lam r) h +
          fun x => h (lam r • x) - h x)) p volume
      ≤ eLpNorm (SpatialScaling.spatialScale (lam r) (lam r) (F - h)) p volume +
          (eLpNorm (SpatialScaling.spatialScale (lam r - 1) (lam r) h) p volume +
            eLpNorm (fun x => h (lam r • x) - h x) p volume) := by
        refine (eLpNorm_add_le hm1 (hm2.add hm3) hp1).trans ?_
        gcongr
        exact eLpNorm_add_le hm2 hm3 hp1
    _ ≤ ENNReal.ofReal (lam r) * eLpNorm (F - h) p volume +
          (ENNReal.ofReal (lam r - 1) * eLpNorm h p volume +
            eLpNorm (fun x => h (lam r • x) - h x) p volume) := by
        gcongr
        · refine (eLpNorm_spatialScale_le hp _ hl1 _).trans_eq ?_
          rw [Real.enorm_eq_ofReal (by positivity)]
        · refine (eLpNorm_spatialScale_le hp _ hl1 _).trans_eq ?_
          rw [Real.enorm_eq_ofReal (by linarith)]

/-- Increment bound: `‖S(r)h - S(r₀)h‖_p ≤ e^{r₀/2} ‖S(|r - r₀|)h - h‖_p` for `r, r₀ ≥ 0`. -/
theorem eLpNorm_freeEvolution_sub_le {ν : ℝ} (hν : 0 ≤ ν) (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {h : SpatialField} (hh : MemLp h p volume) {r r₀ : ℝ} (hr : 0 ≤ r) (hr₀ : 0 ≤ r₀) :
    eLpNorm (freeEvolution ν r h - freeEvolution ν r₀ h) p volume ≤
      ENNReal.ofReal (Real.exp (r₀ / 2)) *
        eLpNorm (freeEvolution ν |r - r₀| h - h) p volume := by
  rcases le_total r r₀ with hle | hle
  · have hd : 0 ≤ r₀ - r := by linarith
    have habs : |r - r₀| = r₀ - r := by
      rw [abs_of_nonpos (by linarith : r - r₀ ≤ 0)]
      ring
    have hdm : MemLp (freeEvolution ν (r₀ - r) h) p volume := freeEvolution_memLp hp1 hp hh ν _
    have hS : freeEvolution ν r₀ h = freeEvolution ν r (freeEvolution ν (r₀ - r) h) := by
      rw [freeEvolution_add hν hr hd hp1 hp hh, add_sub_cancel]
    have hlin : freeEvolution ν r h - freeEvolution ν r₀ h =
        freeEvolution ν r (h - freeEvolution ν (r₀ - r) h) := by
      rw [hS, freeEvolution_sub hp1 hp hh hdm]
    have hn : eLpNorm (h - freeEvolution ν (r₀ - r) h) p volume =
        eLpNorm (freeEvolution ν (r₀ - r) h - h) p volume := eLpNorm_sub_comm _ _ _ _
    calc eLpNorm (freeEvolution ν r h - freeEvolution ν r₀ h) p volume
        = eLpNorm (freeEvolution ν r (h - freeEvolution ν (r₀ - r) h)) p volume := by rw [hlin]
      _ ≤ ENNReal.ofReal (Real.exp (r / 2)) *
            eLpNorm (h - freeEvolution ν (r₀ - r) h) p volume :=
          eLpNorm_freeEvolution_le_exp hp hp1 (hh.sub hdm) ν hr
      _ ≤ ENNReal.ofReal (Real.exp (r₀ / 2)) *
            eLpNorm (freeEvolution ν |r - r₀| h - h) p volume := by
          rw [hn, habs]
          gcongr
  · have hd : 0 ≤ r - r₀ := by linarith
    have habs : |r - r₀| = r - r₀ := abs_of_nonneg hd
    have hdm : MemLp (freeEvolution ν (r - r₀) h) p volume := freeEvolution_memLp hp1 hp hh ν _
    have hS : freeEvolution ν r h = freeEvolution ν r₀ (freeEvolution ν (r - r₀) h) := by
      rw [freeEvolution_add hν hr₀ hd hp1 hp hh, add_sub_cancel]
    have hlin : freeEvolution ν r h - freeEvolution ν r₀ h =
        freeEvolution ν r₀ (freeEvolution ν (r - r₀) h - h) := by
      rw [hS, freeEvolution_sub hp1 hp hdm hh]
    rw [hlin, habs]
    exact eLpNorm_freeEvolution_le_exp hp hp1 (hdm.sub hh) ν hr₀

/-- Strong continuity of `r ↦ S_ν(r)h` on `[0, ∞)` in `L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_freeEvolution {ν : ℝ} (hν : 0 ≤ ν) (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {h : SpatialField} (hh : MemLp h p volume) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    Tendsto (fun r => eLpNorm (freeEvolution ν r h - freeEvolution ν r₀ h) p volume)
      (𝓝[Ici 0] r₀) (𝓝 0) := by
  have habs : Tendsto (fun r : ℝ => |r - r₀|) (𝓝[Ici 0] r₀) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun r => Set.mem_Ici.mpr (abs_nonneg _))⟩
    have hc : Continuous (fun r : ℝ => |r - r₀|) := (continuous_id.sub continuous_const).abs
    have := (hc.tendsto r₀).mono_left (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
    simpa using this
  have h2 := ENNReal.Tendsto.const_mul ((tendsto_freeEvolution_sub_self (ν := ν) hp1 hp hh).comp
    habs) (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (Real.exp (r₀ / 2)))
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact eLpNorm_freeEvolution_sub_le hν hp1 hp hh hr hr₀

end UnforcedLeray.B0418
