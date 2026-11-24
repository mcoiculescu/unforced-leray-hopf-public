import UnforcedLeray.Units.B0428.Slice
import UnforcedLeray.Units.B0411

/-!
# Unit B0428 (`eq:free-stress-19`): spatial elliptic interpolation in `Y_q`

Blueprint unit `B0428`, label `eq:free-stress-19`, `paper/main.tex` lines 7541–7548
(§`sec:st18-9105`, "Core, uniqueness, and exact domain"), within the source range 7268–8686.
The blueprint lists no unit dependencies; it is consumed by B0429 (tex 3591–3621), B0431
(`eq:free-stress-6`, tex 7402–7406), B0432 (`eq:free-background-b-3`, tex 3637–3639) and B0433
(tex 7550–7576).

**Statement (tex 7542–7548).** "Spatial elliptic interpolation gives `∇w ∈ Y_q` whenever
`w, Δw ∈ Y_q`, and `‖∇w‖_{Y_q} ≤ C_q ‖w‖_{Y_q}^{1/2} ‖Δw‖_{Y_q}^{1/2}`." Here (tex 7306–7317)
`Y_q = L^q(ℝ/Pℤ; L^q(ℝ³))` with the normalised phase measure, and `1 < q < ∞` (the range of the
section's theorem, tex 7365 and 7405–7406: "the latter gradient estimate also holds for every
`1 < q < ∞`"); `C_q` is independent of `P` and `ν` (tex 7385).

**Formalization.**
* `Y_q` is `PhaseSpace.Yq P q` (decision D2 of

  "`Δw ∈ Y_q` in distributions" is `HasPhaseOp lapT w L` (`L ∈ Y_q`, pairings with smooth
  `P`-periodic phase tests of bounded spatial support); "`∂ⱼw = g`" is
  `HasPhaseOp (fun Φ => -dy j Φ) w g`, the convention of `Lib/PhaseSpace` (`extend_dy`,
  `Leibniz`). The gradient `∇w` is the triple `(∂₁w, ∂₂w, ∂₃w) : Fin 3 → Y_q`.
* `exists_phaseDeriv` (one component), `exists_phaseGrad` (all components): for `1 < q < ∞`,
  `P > 0` and `w, L ∈ Y_q` with `L = Δw` in distributions, each `∂ⱼw` exists in `Y_q` and
  `‖∂ⱼw‖_{Y_q} ≤ C ‖w‖_{Y_q}^{1/2} ‖Δw‖_{Y_q}^{1/2}` with the explicit constant
  `gradConst = 2√2 c`, `c = ‖∇G_1‖_{L¹(ℝ³)}` (`cHeat`), independent of `P`, `q`, `ν`.
  The norm of the triple is the maximum of the component norms; `exists_phaseGrad` also bounds
  their sum by `3C‖w‖^{1/2}‖Δw‖^{1/2}`, which dominates the `Y_q` norm of the matrix field `∇w`
  with any pointwise matrix norm up to a fixed factor (the manuscript does not fix the norm,
  and `C_q` is unspecified).
* `phaseDeriv_unique`: the derivatives are determined by `w` (phase tests separate `Y_q`,
  `B0411.hasPhaseOp_unique`).
* `exists_phaseDeriv_graph`: the form used by B0431/B0432, for `w ∈ D_(ν,q)` (B0411) and
  `ν > 0`: `‖∂ⱼw‖ ≤ C ν^{-1/2} ‖w‖^{1/2} ‖νΔw‖^{1/2}`.
* `B0428_spec`: the whole unit with an existential constant.

**Proof (blueprint proof outline; bypass §4.4 of `scoping/INF01-CZ.md`, decision D15).** No
Calderón–Zygmund theory is used. At each phase, the `ℝ³` inequality is heat interpolation
(`Units/B0428/Spatial.lean`, after the drafted `Heat.eLpNorm_fderiv_le_interp`):
`∂ₑv = ∂ₑe^{tΔ}v - ∫_0^t ∂ₑe^{sΔ}Δv ds`, so `‖∂ₑv‖_q ≤ c t^{-1/2}‖v‖_q + 2c t^{1/2}‖Δv‖_q`;
the space-time identity holds in almost every phase (`Units/B0428/Slice.lean`); the phase
derivative is the phasewise one (strongly measurable as an a.e. limit of `∂ₑe^{θₙΔ}w(τ)`).
Integrating the phasewise bound in `τ` (Minkowski in `L^q(dτ)`) gives
`‖∂ⱼw‖_{Y_q} ≤ c t^{-1/2}‖w‖_{Y_q} + 2c t^{1/2}‖Δw‖_{Y_q}` for every `t > 0`, and the scaling
optimisation (`le_two_sqrt_mul_of_forall`) gives the product form.

Hypotheses: exactly the manuscript's (`1 < q < ∞`, `P > 0`; the standing `0 < P ≤ 1`, `ν > 0`
are not needed except `ν > 0` in the graph form). No junk values: no division by a norm, no
`toReal` of a possibly infinite quantity, and the square roots are of nonnegative reals.

Status: the unit is proved in full (relative to the compiled drafts it imports). Theorem A is
not proved in Lean.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0428

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.Heat UnforcedLeray.PhaseSpace

/-! ### The constant and the scaling optimisation -/

/-- The interpolation constant `C = 2√2 c`, `c = ‖∇G_1‖_{L¹(ℝ³)}` (independent of `P`, `q`,
`ν`). -/
def gradConst : ℝ := 2 * Real.sqrt 2 * cHeat

theorem gradConst_nonneg : 0 ≤ gradConst := by
  have := cHeat_nonneg
  unfold gradConst
  positivity

/-- **Scaling optimisation.** If `X ≤ A t^{-1/2} + B t^{1/2}` for all `t > 0` (`A, B ≥ 0`), then
`X ≤ 2√A√B`. -/
theorem le_two_sqrt_mul_of_forall {X A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → X ≤ A * t ^ (-(1 : ℝ) / 2) + B * t ^ (1 / 2 : ℝ)) :
    X ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
  have key : ∀ δ : ℝ, 0 < δ → X ≤ 2 * (Real.sqrt (A + δ) * Real.sqrt (B + δ)) := by
    intro δ hδ
    set a := Real.sqrt (A + δ) with ha_def
    set b := Real.sqrt (B + δ) with hb_def
    have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
    have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
    have ha2 : a ^ 2 = A + δ := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = B + δ := Real.sq_sqrt (by linarith)
    set s := a / b with hs_def
    have hs : 0 < s := div_pos ha hb
    have h1 : (s ^ 2) ^ (1 / 2 : ℝ) = s := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hs.le]
    have h2 : (s ^ 2) ^ (-(1 : ℝ) / 2) = s⁻¹ := by
      rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by positivity), h1]
    have hX := h (s ^ 2) (by positivity)
    rw [h1, h2] at hX
    have e1 : A * s⁻¹ ≤ a * b := by
      rw [hs_def, inv_div, mul_div_assoc', div_le_iff₀ ha]
      have : a * b * a = (A + δ) * b := by rw [← ha2]; ring
      rw [this]
      nlinarith
    have e2 : B * s ≤ a * b := by
      rw [hs_def, mul_div_assoc', div_le_iff₀ hb]
      have : a * b * b = (B + δ) * a := by rw [← hb2]; ring
      rw [this]
      nlinarith
    linarith
  have hcont : Continuous fun δ : ℝ => 2 * (Real.sqrt (A + δ) * Real.sqrt (B + δ)) := by
    fun_prop
  have ht := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)

/-! ### The phasewise derivative -/

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- The phasewise derivative `τ ↦ ∂ⱼ(w(τ)) ∈ L^q(ℝ³; ℂ³)`. -/
def phaseDerivFn (j : Fin 3) (w : Yq P q) : AddCircle P → Lp CVec3 q (volume : Measure Space) :=
  fun τ => gradL (coordinateVector j) (w τ)

theorem aestronglyMeasurable_phaseDerivFn (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) :
    AEStronglyMeasurable (phaseDerivFn j w) (AddCircle.haarAddCircle (T := P)) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n τ => dHeat (θs n) (θs_pos n) (coordinateVector j) (w τ))
    (fun n => (continuous_dHeat (θs_pos n) _).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable w)) ?_
  filter_upwards [ae_isWeakLaplacian hq1 h] with τ hτ
  exact tendsto_gradL hqt hτ _

/-- The phasewise interpolation bound, for every `t > 0`. -/
theorem ae_norm_phaseDerivFn_le (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ‖phaseDerivFn j w τ‖ ≤
      cHeat * t ^ (-(1 : ℝ) / 2) * ‖w τ‖ + 2 * cHeat * t ^ (1 / 2 : ℝ) * ‖L τ‖ := by
  filter_upwards [ae_isWeakLaplacian hq1 h] with τ hτ
  have := norm_gradL_le hqt hτ (coordinateVector j) ht
  rw [Heat.norm_coordinateVector, mul_one, mul_one] at this
  exact this

theorem memLp_phaseDerivFn (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) :
    MemLp (phaseDerivFn j w) q (AddCircle.haarAddCircle (T := P)) := by
  have hR : MemLp (fun τ => cHeat * ‖w τ‖ + 2 * cHeat * ‖L τ‖) q
      (AddCircle.haarAddCircle (T := P)) :=
    ((Lp.memLp w).norm.const_mul cHeat).add ((Lp.memLp L).norm.const_mul (2 * cHeat))
  refine hR.of_le (aestronglyMeasurable_phaseDerivFn hq1 hqt h j) ?_
  filter_upwards [ae_norm_phaseDerivFn_le hq1 hqt h j one_pos] with τ hτ
  have := cHeat_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [Real.one_rpow, mul_one] using hτ

/-- The phase derivative `∂ⱼw ∈ Y_q`. -/
def phaseDeriv (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q} (h : HasPhaseOp lapT w L)
    (j : Fin 3) : Yq P q :=
  (memLp_phaseDerivFn hq1 hqt h j).toLp _

/-- `‖∂ⱼw‖_{Y_q} ≤ c t^{-1/2}‖w‖_{Y_q} + 2c t^{1/2}‖Δw‖_{Y_q}` for every `t > 0`. -/
theorem norm_phaseDeriv_le_t (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) {t : ℝ} (ht : 0 < t) :
    ‖phaseDeriv hq1 hqt h j‖ ≤
      cHeat * t ^ (-(1 : ℝ) / 2) * ‖w‖ + 2 * cHeat * t ^ (1 / 2 : ℝ) * ‖L‖ := by
  set a : ℝ := cHeat * t ^ (-(1 : ℝ) / 2) with ha_def
  set b : ℝ := 2 * cHeat * t ^ (1 / 2 : ℝ) with hb_def
  have ha : 0 ≤ a := by have := cHeat_nonneg; positivity
  have hb : 0 ≤ b := by have := cHeat_nonneg; positivity
  set fw : AddCircle P → ℝ := fun τ => ‖w τ‖
  set fL : AddCircle P → ℝ := fun τ => ‖L τ‖
  have hfw : AEStronglyMeasurable fw (AddCircle.haarAddCircle (T := P)) :=
    (Lp.aestronglyMeasurable w).norm
  have hfL : AEStronglyMeasurable fL (AddCircle.haarAddCircle (T := P)) :=
    (Lp.aestronglyMeasurable L).norm
  have h1 : eLpNorm (phaseDerivFn j w) q AddCircle.haarAddCircle ≤
      eLpNorm (a • fw + b • fL) q AddCircle.haarAddCircle := by
    refine eLpNorm_mono_ae_real ?_
    filter_upwards [ae_norm_phaseDerivFn_le hq1 hqt h j ht] with τ hτ
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fw, fL] using hτ
  have h2 : eLpNorm (a • fw + b • fL) q AddCircle.haarAddCircle ≤
      ENNReal.ofReal a * eLpNorm w q AddCircle.haarAddCircle +
        ENNReal.ofReal b * eLpNorm L q AddCircle.haarAddCircle := by
    refine (eLpNorm_add_le (hfw.const_smul a) (hfL.const_smul b) hq.out).trans (le_of_eq ?_)
    rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm, eLpNorm_norm,
      Real.enorm_eq_ofReal ha, Real.enorm_eq_ofReal hb]
  have hfin : ENNReal.ofReal a * eLpNorm w q AddCircle.haarAddCircle +
      ENNReal.ofReal b * eLpNorm L q AddCircle.haarAddCircle ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top w),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top L)⟩
  rw [phaseDeriv, Lp.norm_toLp, Lp.norm_def, Lp.norm_def]
  calc (eLpNorm (phaseDerivFn j w) q AddCircle.haarAddCircle).toReal
      ≤ (ENNReal.ofReal a * eLpNorm w q AddCircle.haarAddCircle +
          ENNReal.ofReal b * eLpNorm L q AddCircle.haarAddCircle).toReal :=
        ENNReal.toReal_mono hfin (h1.trans h2)
    _ = a * (eLpNorm w q AddCircle.haarAddCircle).toReal +
          b * (eLpNorm L q AddCircle.haarAddCircle).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top w))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top L)),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
          ENNReal.toReal_ofReal hb]

/-- **`‖∂ⱼw‖_{Y_q} ≤ C ‖w‖_{Y_q}^{1/2} ‖Δw‖_{Y_q}^{1/2}`** (scaling optimisation). -/
theorem norm_phaseDeriv_le (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) :
    ‖phaseDeriv hq1 hqt h j‖ ≤ gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) := by
  have hc := cHeat_nonneg
  have hA : 0 ≤ cHeat * ‖w‖ := by positivity
  have hB : 0 ≤ 2 * cHeat * ‖L‖ := by positivity
  have hopt := le_two_sqrt_mul_of_forall hA hB fun t ht => by
    have := norm_phaseDeriv_le_t hq1 hqt h j ht
    calc ‖phaseDeriv hq1 hqt h j‖
        ≤ cHeat * t ^ (-(1 : ℝ) / 2) * ‖w‖ + 2 * cHeat * t ^ (1 / 2 : ℝ) * ‖L‖ := this
      _ = cHeat * ‖w‖ * t ^ (-(1 : ℝ) / 2) + 2 * cHeat * ‖L‖ * t ^ (1 / 2 : ℝ) := by ring
  refine hopt.trans (le_of_eq ?_)
  rw [Real.sqrt_mul hc, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * cHeat),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hcc := Real.mul_self_sqrt hc
  unfold gradConst
  calc 2 * (Real.sqrt cHeat * Real.sqrt ‖w‖ *
        (Real.sqrt 2 * Real.sqrt cHeat * Real.sqrt ‖L‖))
      = 2 * Real.sqrt 2 * (Real.sqrt cHeat * Real.sqrt cHeat) *
          (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) := by ring
    _ = 2 * Real.sqrt 2 * cHeat * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) := by rw [hcc]

omit hP in
/-- At one phase `t` with `Δu = Λ` in `𝒟'(ℝ³)`: `⟪-∂ⱼΦ(t, ·), u⟫ = ⟪Φ(t, ·), ∂ⱼu⟫`. -/
theorem slice_pair (hqt : q ≠ ⊤) {u Λ : Lp CVec3 q (volume : Measure Space)}
    (hWL : IsWeakLaplacian (u : Space → CVec3) (Λ : Space → CVec3)) (j : Fin 3)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (hs : IsSliceTest P (conjExp q) Φ)
    (hs' : IsSliceTest P (conjExp q) (-dy j Φ)) (t : ℝ) :
    innerPair q (sliceMap hs'.2 t) u = innerPair q (sliceMap hs.2 t) (gradL (coordinateVector j) u) := by
  have hΨ : ContDiff ℝ ∞ (fun y : Space => Φ (t, y)) :=
    hΦ.smooth.comp (contDiff_prodMk_right t)
  have hΨ1 : ContDiff ℝ 1 (fun y : Space => Φ (t, y)) := contDiff_infty.1 hΨ 1
  have hΨc : HasCompactSupport (fun y : Space => Φ (t, y)) := hΦ.hasCompactSupport_slice t
  have key := innerPair_gradL hqt hWL (coordinateVector j) hΨ1 hΨc
  have eA : sliceMap hs.2 t =
      (memLp_test hΨ1.continuous hΨc (conjExp q)).toLp (fun y : Space => Φ (t, y)) := rfl
  have eB : sliceMap hs'.2 t =
      -((memLp_fderiv_test hΨ1 hΨc (coordinateVector j) (conjExp q)).toLp
        (fun x => fderiv ℝ (fun y : Space => Φ (t, y)) x (coordinateVector j))) := by
    rw [← MemLp.toLp_neg]
    unfold sliceMap
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply]
    rw [dy_apply_slice (hΦ.smooth.differentiable (by simp)) j t y]
  rw [eA, eB, map_neg, ContinuousLinearMap.neg_apply, key]

/-- The phase derivative is the distributional derivative: `⟪-∂ⱼΦ, w⟫ = ⟪Φ, ∂ⱼw⟫`. -/
theorem hasPhaseOp_phaseDeriv (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) :
    HasPhaseOp (fun Φ => -dy j Φ) w (phaseDeriv hq1 hqt h j) := by
  intro Φ hΦ
  have hΦ' : IsPhaseTest P (-dy j Φ) := (hΦ.dy j).neg
  have hs := hΦ.isSliceTest (conjExp q)
  have hs' := hΦ'.isSliceTest (conjExp q)
  show phasePairing P q (testElem P (conjExp q) (-dy j Φ)) w =
    phasePairing P q (testElem P (conjExp q) Φ) (phaseDeriv hq1 hqt h j)
  rw [phasePairing_apply, phasePairing_apply]
  refine integral_congr_ae ?_
  have e1 := ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space))
    (p := conjExp q) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := P)) (circleSlice hs)
  rw [← testElem_of hs] at e1
  have e2 := ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp q) (volume : Measure Space))
    (p := conjExp q) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := P)) (circleSlice hs')
  rw [← testElem_of hs'] at e2
  have e3 : (phaseDeriv hq1 hqt h j : AddCircle P → Lp CVec3 q (volume : Measure Space))
      =ᵐ[AddCircle.haarAddCircle] phaseDerivFn j w :=
    MemLp.coeFn_toLp (memLp_phaseDerivFn hq1 hqt h j)
  filter_upwards [e1, e2, e3, ae_isWeakLaplacian hq1 h] with τ h1 h2 h3 hτ
  rw [h1, h2, h3]
  obtain ⟨t, rfl⟩ : ∃ t : ℝ, (t : AddCircle P) = τ := QuotientAddGroup.mk_surjective τ
  rw [circleSlice_coe, circleSlice_coe]
  exact slice_pair hqt hτ j hΦ hs hs' t

/-! ### The unit -/

/-- **B0428, one component** (tex 7542–7548). For `1 < q < ∞` and `w, L ∈ Y_q` with `L = Δw`
in distributions, `∂ⱼw ∈ Y_q` and `‖∂ⱼw‖_{Y_q} ≤ C ‖w‖_{Y_q}^{1/2} ‖Δw‖_{Y_q}^{1/2}`. -/
theorem exists_phaseDeriv (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) (j : Fin 3) :
    ∃ g : Yq P q, HasPhaseOp (fun Φ => -dy j Φ) w g ∧
      ‖g‖ ≤ gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) :=
  ⟨phaseDeriv hq1 hqt h j, hasPhaseOp_phaseDeriv hq1 hqt h j, norm_phaseDeriv_le hq1 hqt h j⟩

/-- The distributional derivatives are unique (phase tests separate `Y_q`). -/
theorem phaseDeriv_unique {w g g' : Yq P q} {j : Fin 3}
    (hg : HasPhaseOp (fun Φ => -dy j Φ) w g) (hg' : HasPhaseOp (fun Φ => -dy j Φ) w g') :
    g = g' :=
  B0411.hasPhaseOp_unique hg hg'

/-- **B0428, the gradient** (tex 7542–7548): `∇w = (∂₁w, ∂₂w, ∂₃w) ∈ Y_q³` with
`‖∇w‖ = maxⱼ ‖∂ⱼw‖_{Y_q} ≤ C ‖w‖^{1/2}‖Δw‖^{1/2}` and `∑ⱼ ‖∂ⱼw‖_{Y_q} ≤ 3C ‖w‖^{1/2}‖Δw‖^{1/2}`. -/
theorem exists_phaseGrad (hq1 : 1 < q) (hqt : q ≠ ⊤) {w L : Yq P q}
    (h : HasPhaseOp lapT w L) :
    ∃ g : Fin 3 → Yq P q, (∀ j, HasPhaseOp (fun Φ => -dy j Φ) w (g j)) ∧
      ‖g‖ ≤ gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) ∧
      ∑ j, ‖g j‖ ≤ 3 * (gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖)) := by
  refine ⟨fun j => phaseDeriv hq1 hqt h j, fun j => hasPhaseOp_phaseDeriv hq1 hqt h j, ?_, ?_⟩
  · have h0 : 0 ≤ gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) := by
      have := gradConst_nonneg; positivity
    exact (pi_norm_le_iff_of_nonneg h0).2 fun j => norm_phaseDeriv_le hq1 hqt h j
  · calc ∑ j, ‖phaseDeriv hq1 hqt h j‖
        ≤ ∑ _j : Fin 3, gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖) :=
          Finset.sum_le_sum fun j _ => norm_phaseDeriv_le hq1 hqt h j
      _ = 3 * (gradConst * (Real.sqrt ‖w‖ * Real.sqrt ‖L‖)) := by simp

/-- `νΔw = a` in distributions with `ν ≠ 0` gives `Δw = ν⁻¹a`. -/
theorem hasPhaseOp_lapT_of_nuLapT {ν : ℝ} (hν : ν ≠ 0) {w a : Yq P q}
    (h : HasPhaseOp (nuLapT ν) w a) : HasPhaseOp lapT w (((ν⁻¹ : ℝ) : ℂ) • a) := by
  intro Φ hΦ
  have h1 := h Φ hΦ
  have h2 := phasePair_real_smul (q := q) hΦ.lapT ν w
  rw [nuLapT] at h1
  rw [h1] at h2
  rw [map_smul, smul_eq_mul, h2]
  have hν' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hν
  push_cast
  field_simp

/-- **The graph form** (used by B0431, B0432): for `ν > 0` and `w ∈ D_(ν,q)`,
`‖∂ⱼw‖_{Y_q} ≤ C ν^{-1/2} ‖w‖_{Y_q}^{1/2} ‖νΔw‖_{Y_q}^{1/2}`. -/
theorem exists_phaseDeriv_graph (hq1 : 1 < q) (hqt : q ≠ ⊤) {ν : ℝ} (hν : 0 < ν)
    (w : B0411.D P ν q) (j : Fin 3) :
    ∃ g : Yq P q, HasPhaseOp (fun Φ => -dy j Φ) (w : Yq P q) g ∧
      ‖g‖ ≤ gradConst * (Real.sqrt ν)⁻¹ *
        (Real.sqrt ‖(w : Yq P q)‖ * Real.sqrt ‖B0411.nuLapD w‖) := by
  have hL := hasPhaseOp_lapT_of_nuLapT hν.ne' (B0411.hasPhaseOp_nuLapD w)
  obtain ⟨g, hg, hgn⟩ := exists_phaseDeriv hq1 hqt hL j
  refine ⟨g, hg, hgn.trans (le_of_eq ?_)⟩
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hν),
    Real.sqrt_mul (inv_pos.2 hν).le, Real.sqrt_inv]
  ring

/-- **Unit B0428** (`eq:free-stress-19`, tex 7541–7548), with an existential constant
independent of `P` and `q` (the manuscript's `C_q` may depend on `q`). -/
theorem B0428_spec :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)], 1 < q → q ≠ ⊤ →
      ∀ w L : Yq P q, HasPhaseOp lapT w L →
        ∃ g : Fin 3 → Yq P q, (∀ j, HasPhaseOp (fun Φ => -dy j Φ) w (g j)) ∧
          ‖g‖ ≤ C * ‖w‖ ^ (1 / 2 : ℝ) * ‖L‖ ^ (1 / 2 : ℝ) := by
  refine ⟨gradConst, gradConst_nonneg, fun P _ q _ hq1 hqt w L h => ?_⟩
  obtain ⟨g, hg, hgn, -⟩ := exists_phaseGrad hq1 hqt h
  refine ⟨g, hg, hgn.trans (le_of_eq ?_)⟩
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  ring

end UnforcedLeray.B0428
