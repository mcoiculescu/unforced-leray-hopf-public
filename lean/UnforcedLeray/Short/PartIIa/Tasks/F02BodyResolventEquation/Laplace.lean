import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Units.B0411

/-!
# Part II-a, task `PartII-a:F02`, helper: `(μ + L₀) R_μ f = f` in distributions, from the generator

Repaired copy of the (non-compiling) draft `Units/B0421/Equation.lean`, in the namespace
`UnforcedLeray.Short.PartIIa.F02`. The repairs: the coercion in `tendsto_shift_test`, the renamed
`Set.self_mem_Ici`, two heartbeat limits, and the `convert` in `hasPhaseOp_laplace`. The only
hypothesis left is the named Prop `FreeTestGenerator` (the generator of the free semigroup on
phase tests by duality); it is discharged in `Short/PartII-a/Sub/F02.lean` by the tasks
`PartII-a:F02/1`-`F02/11`. Source of record: `the November 2 reference manuscript`,
lines 1363-1370 (original unit B0421, `paper/main.tex` lines 7441-7445).

Original header of the unit:

Blueprint unit B0421, `paper/main.tex` lines 7441–7445: "Formula `eq:free-stress-9` solves
`(μ + L₀)w = P_σ f` in distributions, by differentiation against smooth periodic spatial tests."
Distributions on `(ℝ/Pℤ) × ℝ³` are pairings with phase tests (`PhaseSpace.IsPhaseTest`,
decision D2), and `(μ + L₀)w = g` in distributions is
`PhaseSpace.HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w g` with `L0T` the transpose of
`L₀ = T₀ − νΔ − ½` (unit B0411, `Units/B0411/Operators.lean`).

The proof differentiates `t ↦ ⟪Φ, 𝒯(t) w⟫` at `t = 0⁺`, where `𝒯(t)g(τ) = S_ν(t)g(τ - t)`
(`Units/B0421/Phase.lean`):

* the phase-translation half is proved here: `⟪Φ, g(· - t)⟫ = ⟪Φ(· + t), g⟫`
  (`phasePair_shiftY_neg`) and `t⁻¹(Φ(· + t) − Φ) → ∂_τΦ` in `Y_{q'}` (`tendsto_shift_test`);
* the half that concerns `S_ν` alone, the generator of `S_ν` acting on tests by duality
  ("using the generator of `S_ν` on the tests (adjoint action)", blueprint proof outline), is the
  named hypothesis `FreeTestGenerator`: `d/dr|₀₊ ⟪Φ, S_ν(r)x⟫ = ⟪AᵗΦ, x⟫` with
  `Aᵗ = νΔ − ½ y·∇ − 1` the transpose of the generator `A = νΔ + ½ y·∇ + ½` of
  `eq:free-stress-7`. The drafted B0418 proves the generator only on `C_c^∞` fields in the forward
  direction; the duality with tests (the explicit adjoint semigroup `S_ν(r)^*` on phase tests,
  bypass BP-C of `scoping/README.md`, INF25 T25.4) is not built.
* `tendsto_weak_generator`: under `FreeTestGenerator`, `d/dt|₀₊ ⟪Φ, 𝒯(t)x⟫ = −⟪L₀ᵗΦ, x⟫`;
* `hasPhaseOp_laplace`: under `FreeTestGenerator`, the Laplace transform `R = ∫_0^∞ e^{-μt}𝒯(t) dt`
  satisfies `(μ + L₀) R h = h` in distributions for every `h ∈ Y_q` (`Re μ > -γ_q`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.Short.PartIIa.F02

open UnforcedLeray.B0421

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0418 (gammaExp)

/-! ### Phase tests: bounds and phase shifts -/

section Tests

variable {P : ℝ} [hP : Fact (0 < P)]

/-- A phase test is bounded. -/
theorem exists_bound_of_phaseTest {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × Space → F} (hΦ : IsPhaseTest P Φ) : ∃ M, 0 ≤ M ∧ ∀ p, ‖Φ p‖ ≤ M := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hK : IsCompact (Icc 0 P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hΦ.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun ⟨τ, y⟩ => ?_⟩
  by_cases hy : R < ‖y‖
  · rw [hR τ y hy, norm_zero]
    exact le_max_right _ _
  · have hPpos : 0 < P := hP.out
    have hper : Function.Periodic (fun s => Φ (s, y)) P := fun s => hΦ.periodic s y
    have hτ' : Φ (toIcoMod hPpos 0 τ, y) = Φ (τ, y) := by
      rw [← self_sub_toIcoDiv_zsmul]
      exact hper.sub_zsmul_eq _
    have hmem : (toIcoMod hPpos 0 τ, y) ∈ Icc 0 P ×ˢ Metric.closedBall (0 : Space) R := by
      refine ⟨?_, ?_⟩
      · have h := toIcoMod_mem_Ico' hPpos τ
        exact ⟨h.1, h.2.le⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hy
    rw [← hτ']
    exact (hM _ hmem).trans (le_max_left _ _)

/-- The phase-shifted test `Φ_t(τ, y) = Φ(τ + t, y)`. -/
def shiftT (t : ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := fun p => Φ (p.1 + t, p.2)

omit hP in
theorem isPhaseTest_shiftT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) :
    IsPhaseTest P (shiftT t Φ) where
  smooth := hΦ.smooth.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  periodic τ y := by
    simp only [shiftT]
    rw [show τ + P + t = (τ + t) + P by ring, hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => hR (τ + t) y hy⟩

/-- `s ↦ Ψ(τ + s, y)` has derivative `∂_τΨ(τ + s, y)`. -/
theorem hasDerivAt_phase {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (τ s : ℝ) (y : Space) :
    HasDerivAt (fun s => Ψ (τ + s, y)) (dτ Ψ (τ + s, y)) s := by
  have hpath : HasDerivAt (fun s : ℝ => ((τ + s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    ((hasDerivAt_id s).const_add τ).prodMk (hasDerivAt_const s y)
  have hd : DifferentiableAt ℝ Ψ (τ + s, y) := (hΨ.differentiable (by simp)) _
  exact hd.hasFDerivAt.comp_hasDerivAt s hpath

/-- Taylor bound for the phase difference quotient: for `t > 0`,
`‖t⁻¹(Φ(τ + t, y) − Φ(τ, y)) − ∂_τΦ(τ, y)‖ ≤ t M₂` with `M₂ ≥ ‖∂_τ²Φ‖`. -/
theorem norm_quotient_le {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) {M₂ : ℝ}
    (hM₂ : ∀ p, ‖dτ (dτ Φ) p‖ ≤ M₂) {t : ℝ} (ht : 0 < t) (τ : ℝ) (y : Space) :
    ‖((t⁻¹ : ℝ) : ℂ) • (Φ (τ + t, y) - Φ (τ, y)) - dτ Φ (τ, y)‖ ≤ t * M₂ := by
  have hd1 : IsPhaseTest P (dτ Φ) := hΦ.dτ
  -- `‖∂_τΦ(τ + s, y) − ∂_τΦ(τ, y)‖ ≤ M₂ s` for `s ∈ [0, t]`
  have hstep : ∀ s ∈ Icc (0 : ℝ) t, ‖dτ Φ (τ + s, y) - dτ Φ (τ, y)‖ ≤ M₂ * s := by
    intro s hs
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => dτ Φ (τ + s, y))
      (f' := fun s => dτ (dτ Φ) (τ + s, y)) (C := M₂) (a := 0) (b := t)
      (fun x _ => (hasDerivAt_phase hd1.smooth τ x y).hasDerivWithinAt)
      (fun x _ => hM₂ _) s hs
    simpa using h
  set f : ℝ → CVec3 := fun s => Φ (τ + s, y) - (s : ℂ) • dτ Φ (τ, y) with hf
  have hderiv : ∀ x ∈ Icc (0 : ℝ) t, HasDerivWithinAt f (dτ Φ (τ + x, y) - dτ Φ (τ, y))
      (Icc 0 t) x := by
    intro x _
    have h1 := hasDerivAt_phase hΦ.smooth τ x y
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) • dτ Φ (τ, y)) ((1 : ℂ) • dτ Φ (τ, y)) x := by
      have := (hasDerivAt_id x).ofReal_comp.smul_const (dτ Φ (τ, y))
      simpa using this
    have h3 := h1.sub h2
    rw [one_smul] at h3
    exact h3.hasDerivWithinAt
  have hbd : ∀ x ∈ Ico (0 : ℝ) t, ‖dτ Φ (τ + x, y) - dτ Φ (τ, y)‖ ≤ M₂ * t := by
    intro x hx
    refine (hstep x ⟨hx.1, hx.2.le⟩).trans ?_
    have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ (0, 0))
    exact mul_le_mul_of_nonneg_left hx.2.le hM₂0
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbd t (right_mem_Icc.2 ht.le)
  have hf0 : f 0 = Φ (τ, y) := by simp [hf]
  have hft : f t - f 0 = (Φ (τ + t, y) - Φ (τ, y)) - (t : ℂ) • dτ Φ (τ, y) := by
    rw [hf0]
    simp only [hf]
    abel
  rw [hft, sub_zero] at hmain
  have hrw : ((t⁻¹ : ℝ) : ℂ) • (Φ (τ + t, y) - Φ (τ, y)) - dτ Φ (τ, y) =
      ((t⁻¹ : ℝ) : ℂ) • ((Φ (τ + t, y) - Φ (τ, y)) - (t : ℂ) • dτ Φ (τ, y)) := by
    rw [smul_sub (((t⁻¹ : ℝ) : ℂ)) (Φ (τ + t, y) - Φ (τ, y)) ((t : ℂ) • dτ Φ (τ, y)), smul_smul,
      ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
  rw [hrw, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]
  calc t⁻¹ * ‖(Φ (τ + t, y) - Φ (τ, y)) - (t : ℂ) • dτ Φ (τ, y)‖ ≤ t⁻¹ * (M₂ * t * t) :=
        mul_le_mul_of_nonneg_left hmain (inv_pos.2 ht).le
    _ = t * M₂ := by field_simp

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- `‖testElem G‖_{Y_r} ≤ |B_R|^{1/r} η` for a slice test supported in `|y| ≤ R` with
`‖G‖ ≤ η`. -/
theorem norm_testElem_le {G : ℝ × Space → CVec3} (hG : IsSliceTest P r G) (R η : ℝ) (hη : 0 ≤ η)
    (hsupp : ∀ τ y, R < ‖y‖ → G (τ, y) = 0) (hb : ∀ τ y, ‖G (τ, y)‖ ≤ η) :
    ‖testElem P r G‖ ≤
      (volume (Metric.closedBall (0 : Space) R) ^ r.toReal⁻¹).toReal * η := by
  set K : ℝ≥0∞ := volume (Metric.closedBall (0 : Space) R) ^ r.toReal⁻¹ with hK
  have hKfin : K ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      measure_closedBall_lt_top.ne
  have hslice : ∀ τ : AddCircle P, ‖circleSlice hG τ‖ ≤ K.toReal * η := by
    intro τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      rw [circleSlice_coe, sliceMap, Lp.norm_toLp]
      have h := eLpNorm_le_of_ball (r := r) (fun y => G (t, y)) R η (hsupp t)
        (fun y _ => hb t y)
      calc (eLpNorm (fun y => G (t, y)) r volume).toReal ≤ (K * ENNReal.ofReal η).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top hKfin ENNReal.ofReal_ne_top) h
        _ = K.toReal * η := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη]
  rw [testElem_of hG]
  have h := Lp.norm_le_of_ae_bound (μ := AddCircle.haarAddCircle (T := P))
    (f := ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r
      AddCircle.haarAddCircle ℂ (circleSlice hG))
    (C := K.toReal * η) (by positivity) (by
      filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 r (volume : Measure Space))
        (p := r) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hG)] with τ hτ
      rw [hτ]
      exact hslice τ)
  have h1 : measureUnivNNReal (AddCircle.haarAddCircle (T := P)) = 1 := by
    simp [measureUnivNNReal]
  rw [h1] at h
  simpa using h

theorem testElem_sub {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ)
    (hΨ : IsSliceTest P r Ψ) : testElem P r (Φ - Ψ) = testElem P r Φ - testElem P r Ψ := by
  have h : Φ - Ψ = Φ + (-1 : ℂ) • Ψ := by
    funext p
    simp [sub_eq_add_neg]
  rw [h, testElem_add hΦ (hΨ.const_smul _), testElem_const_smul hΨ, neg_one_smul, ← sub_eq_add_neg]

set_option maxHeartbeats 1600000 in
/-- The circle slice of the shifted test is the shifted circle slice. -/
theorem circleSlice_shiftT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ)
    (τ : AddCircle P) :
    circleSlice ((isPhaseTest_shiftT hΦ t).isSliceTest r) τ =
      circleSlice (hΦ.isSliceTest r) ((t : AddCircle P) + τ) := by
  induction τ using QuotientAddGroup.induction_on with
  | H s =>
    rw [circleSlice_coe, show (t : AddCircle P) + (s : AddCircle P) = ((t + s : ℝ) : AddCircle P)
      from (AddCircle.coe_add P t s).symm, circleSlice_coe]
    unfold sliceMap
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y => by
      simp only [shiftT]
      rw [add_comm s t])

set_option maxHeartbeats 1600000 in
/-- **Phase translation of tests**: `testElem Φ_t = (testElem Φ)(t + ·)`. -/
theorem testElem_shiftT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (t : ℝ) :
    testElem P r (shiftT t Φ) = shiftY (t : AddCircle P) (testElem P r Φ) := by
  have hs := hΦ.isSliceTest r
  have hs' := (isPhaseTest_shiftT hΦ t).isSliceTest r
  rw [testElem_of hs', testElem_of hs, shiftY_apply]
  apply Lp.ext
  have e1 := ContinuousMap.coeFn_toLp (E := Lp CVec3 r (volume : Measure Space)) (p := r)
    (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs')
  have e2 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (t : AddCircle P))
    (ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r AddCircle.haarAddCircle ℂ
      (circleSlice hs))
  have e3' := ContinuousMap.coeFn_toLp (E := Lp CVec3 r (volume : Measure Space)) (p := r)
    (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)
  have hmp : MeasurePreserving (fun τ : AddCircle P => (t : AddCircle P) +ᵥ τ)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
    measurePreserving_vadd _ _
  have e3 := e3'.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
  filter_upwards [e1, e2, e3] with τ h1 h2 h3
  rw [h1, h2]
  simp only [Function.comp_apply] at h3
  change _ = (ContinuousMap.toLp r AddCircle.haarAddCircle ℂ (circleSlice hs) :
    AddCircle P → Lp CVec3 r (volume : Measure Space)) ((t : AddCircle P) +ᵥ τ)
  rw [h3, circleSlice_shiftT hΦ t τ]
  rfl

/-- **Derivative of phase translation on tests** in `Y_r`:
`t⁻¹((testElem Φ)(t + ·) − testElem Φ) → testElem ∂_τΦ` as `t → 0⁺`. -/
theorem tendsto_shift_test {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (shiftY (t : AddCircle P) (testElem P r Φ) -
      testElem P r Φ)) (𝓝[>] 0) (𝓝 (testElem P r (dτ Φ))) := by
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_of_phaseTest hΦ.dτ.dτ
  obtain ⟨R₁, hR₁⟩ := hΦ.bounded_support
  obtain ⟨R₂, hR₂⟩ := hΦ.dτ.bounded_support
  set R := max R₁ R₂ with hR
  set K : ℝ := (volume (Metric.closedBall (0 : Space) R) ^ r.toReal⁻¹).toReal with hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => K * (t * M₂)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => K * (t * M₂)) (𝓝 0) (𝓝 (K * (0 * M₂))) :=
      (continuous_const.mul (continuous_id.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  -- the difference quotient is a test element
  set G : ℝ × Space → CVec3 :=
    ((t⁻¹ : ℝ) : ℂ) • (shiftT t Φ - Φ) - dτ Φ with hGdef
  have hGt : IsPhaseTest P G := (((isPhaseTest_shiftT hΦ t).sub hΦ).const_smul _).sub hΦ.dτ
  have hrep : (t⁻¹ : ℝ) • (shiftY (t : AddCircle P) (testElem P r Φ) - testElem P r Φ) -
      testElem P r (dτ Φ) = testElem P r G := by
    rw [hGdef, testElem_sub ((((isPhaseTest_shiftT hΦ t).sub hΦ).const_smul _).isSliceTest r)
        (hΦ.dτ.isSliceTest r),
      testElem_const_smul (((isPhaseTest_shiftT hΦ t).sub hΦ).isSliceTest r),
      testElem_sub ((isPhaseTest_shiftT hΦ t).isSliceTest r) (hΦ.isSliceTest r), testElem_shiftT hΦ t]
    exact congrArg (fun z => z - testElem P r (dτ Φ))
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
  rw [hrep]
  refine norm_testElem_le (hGt.isSliceTest r) R (t * M₂) (by positivity) ?_ ?_
  · intro τ y hy
    have h1 : R₁ < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) hy
    have h2 : R₂ < ‖y‖ := lt_of_le_of_lt (le_max_right _ _) hy
    simp only [hGdef, Pi.sub_apply, Pi.smul_apply, shiftT]
    rw [hR₁ _ y h1, hR₁ _ y h1, hR₂ _ y h2]
    simp
  · intro τ y
    have h := norm_quotient_le hΦ hM₂ ht0 τ y
    simpa [hGdef, shiftT] using h

end Tests

/-! ### Pairings and phase translation -/

section Pairing

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

set_option maxHeartbeats 1600000 in
/-- The phase pairing is invariant under a common phase translation. -/
theorem phasePairing_shiftY (σ : AddCircle P) (ψ : Yq P (conjExp q)) (z : Yq P q) :
    phasePairing P q (shiftY σ ψ) (shiftY σ z) = phasePairing P q ψ z := by
  rw [phasePairing_apply, phasePairing_apply, shiftY_apply, shiftY_apply]
  have e1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk σ) ψ
  have e2 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk σ) z
  have h : (fun τ => innerPair q ((DomAddAct.mk σ +ᵥ ψ : Yq P (conjExp q)) τ)
      ((DomAddAct.mk σ +ᵥ z : Yq P q) τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => innerPair q (ψ (σ + τ)) (z (σ + τ)) := by
    filter_upwards [e1, e2] with τ h1 h2
    rw [h1, h2]
    rfl
  rw [integral_congr_ae h]
  exact integral_add_left_eq_self σ (f := fun τ => innerPair q (ψ τ) (z τ))

set_option maxHeartbeats 1600000 in
theorem shiftY_shiftY_neg {r : ℝ≥0∞} [Fact (1 ≤ r)] (t : ℝ) (z : Yq P r) :
    shiftY (t : AddCircle P) (shiftY (-(t : AddCircle P)) z) = z := by
  rw [shiftY_apply, shiftY_apply, vadd_vadd, ← DomAddAct.mk_add, neg_add_cancel]
  exact zero_vadd _ z

/-- `⟪Φ, g(· − t)⟫ = ⟪Φ(· + t), g⟫`, written in `Y_{q'}`. -/
theorem phasePair_shiftY_neg (Φ : ℝ × Space → CVec3) (t : ℝ) (w : Yq P q) :
    phasePair P q Φ (shiftY (-(t : AddCircle P)) w) =
      phasePairing P q (shiftY (t : AddCircle P) (testElem P (conjExp q) Φ)) w := by
  rw [phasePair, ← phasePairing_shiftY (t : AddCircle P) (testElem P (conjExp q) Φ)
    (shiftY (-(t : AddCircle P)) w), shiftY_shiftY_neg]

end Pairing

/-! ### The weak generator and the distributional equation -/

section Generator

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The transpose `Aᵗ = νΔ − ½ y·∇ − 1` of the generator `A = νΔ + ½ y·∇ + ½` of `S_ν`
(`eq:free-stress-7`, tex 7411–7419): `∫ Φ·(½ y·∇h) = −∫ (½ y·∇Φ + (3/2)Φ)·h`. -/
def genT (ν : ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  nuLapT ν Φ - (1 / 2 : ℝ) • radialT Φ - Φ

omit [Fact (0 < P)] in
theorem isPhaseTest_genT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (ν : ℝ) :
    IsPhaseTest P (genT ν Φ) :=
  ((B0411.isPhaseTest_nuLapT hΦ ν).sub (hΦ.radialT.const_smul _)).sub hΦ

/-- `∂_τΦ + AᵗΦ = −L₀ᵗΦ`: the generator of `𝒯(t) = S_ν(t)(· − t)` is `−L₀` in the weak sense. -/
theorem dτ_add_genT (ν : ℝ) (Φ : ℝ × Space → CVec3) :
    dτ Φ + genT ν Φ = -B0411.L0T ν Φ := by
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, genT, B0411.L0T, driftT,
    nuLapT]
  module

/-- **Named hypothesis: the generator of `S_ν` on phase tests, by duality** (the adjoint action
of the free semigroup on tests; blueprint unit B0421's proof outline "using the generator of
`S_ν` on the tests (adjoint action)", tex lines 7441–7443; infrastructure INF14 "semigroup
duality with tests", scoping bypass BP-C / INF25 T25.4, not yet built). For every phase test
`Φ` and every `x ∈ Y_q`, the pairing `r ↦ ⟪Φ, S_ν(r)x⟫` (with `S_ν(r)` acting slice by slice)
has right derivative `⟪AᵗΦ, x⟫` at `r = 0`, `Aᵗ = νΔ − ½ y·∇ − 1` (`genT`).

This is a statement about `S_ν` alone. It holds for `1 < q < ∞` because
`S_ν(r)^*Φ = e^{-r}[e^{ν(1-e^{-r})Δ}Φ](e^{-r/2}·)` is the explicit adjoint and
`r⁻¹(S_ν(r)^*Φ − Φ) → AᵗΦ` in `Y_{q'}` for smooth, periodic tests of bounded support. -/
def FreeTestGenerator (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤) (ν : ℝ) :
    Prop :=
  ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → ∀ x : Yq P q,
    Tendsto (fun r : ℝ => (r⁻¹ : ℝ) • (phasePair P q Φ
        ((freeC hq ν r).compLpL q AddCircle.haarAddCircle x) - phasePair P q Φ x))
      (𝓝[>] 0) (𝓝 (phasePair P q (genT ν Φ) x))

set_option maxHeartbeats 1600000 in
/-- Under `FreeTestGenerator`, the weak generator of `𝒯(t) = S_ν(t)(· − t)` on tests is `−L₀ᵗ`:
`t⁻¹(⟪Φ, 𝒯(t)x⟫ − ⟪Φ, x⟫) → −⟪L₀ᵗΦ, x⟫` as `t → 0⁺`. -/
theorem tendsto_weak_generator (hq : q ≠ ⊤) {ν : ℝ} (hν : 0 ≤ ν)
    (hG : FreeTestGenerator P q hq ν) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (x : Yq P q) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (phasePair P q Φ (phaseT hq ν t x) - phasePair P q Φ x))
      (𝓝[>] 0) (𝓝 (-(phasePair P q (B0411.L0T ν Φ) x))) := by
  set ψ : Yq P (conjExp q) := testElem P (conjExp q) Φ with hψ
  set Sx : ℝ → Yq P q := fun r => (freeC hq ν r).compLpL q AddCircle.haarAddCircle x with hSx
  -- rewrite the quotient
  have hsplit : ∀ t : ℝ, (t⁻¹ : ℝ) • (phasePair P q Φ (phaseT hq ν t x) - phasePair P q Φ x) =
      phasePairing P q ((t⁻¹ : ℝ) • (shiftY (t : AddCircle P) ψ - ψ)) (Sx t) +
        (t⁻¹ : ℝ) • (phasePair P q Φ (Sx t) - phasePair P q Φ x) := by
    intro t
    have hT : phaseT hq ν t x = shiftY (-(t : AddCircle P)) (Sx t) := by
      change (freeC hq ν t).compLpL q AddCircle.haarAddCircle (shiftY (-(t : AddCircle P)) x) = _
      exact compLpL_shiftY _ _ _
    rw [hT, phasePair_shiftY_neg, ContinuousLinearMap.map_smul_of_tower, map_sub,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ← smul_add]
    congr 1
    simp only [phasePair, hψ]
    abel
  simp_rw [hsplit]
  -- the two limits
  have hSx0 : Tendsto Sx (𝓝[>] 0) (𝓝 x) := by
    have h := continuousOn_freeY (P := P) hq hν x 0 Set.self_mem_Ici
    have h0 : (freeC hq ν 0).compLpL q AddCircle.haarAddCircle x = x := by
      rw [freeC_zero, compLpL_one]
    rw [ContinuousWithinAt, h0] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h1 : Tendsto (fun t : ℝ =>
      phasePairing P q ((t⁻¹ : ℝ) • (shiftY (t : AddCircle P) ψ - ψ)) (Sx t)) (𝓝[>] 0)
      (𝓝 (phasePair P q (dτ Φ) x)) := by
    have hd := tendsto_shift_test (r := conjExp q) hΦ
    have hc := ((phasePairing P q).continuous₂.tendsto
      (testElem P (conjExp q) (dτ Φ), x)).comp (hd.prodMk_nhds hSx0)
    exact hc
  have h2 := hG Φ hΦ x
  have hsum := h1.add h2
  have hval : phasePair P q (dτ Φ) x + phasePair P q (genT ν Φ) x =
      -(phasePair P q (B0411.L0T ν Φ) x) := by
    rw [← phasePair_add hΦ.dτ (isPhaseTest_genT hΦ ν), dτ_add_genT,
      phasePair_neg (B0411.isPhaseTest_L0T hΦ ν)]
  rw [hval] at hsum
  exact hsum

/-- **The distributional equation** (tex 7441–7443). Let `S` be the exponentially bounded
semigroup `𝒯` (`phaseSemigroup`) and `Re μ > -γ_q`. Under `FreeTestGenerator`, for every
`h ∈ Y_q` the Laplace transform `w = ∫_0^∞ e^{-μt} 𝒯(t) h dt` solves `(μ + L₀)w = h` in
distributions: `⟪μΦ + L₀ᵗΦ, w⟫ = ⟪Φ, h⟫` for every phase test `Φ`. No regularity of `w`
beyond `w ∈ Y_q` is used. -/
theorem hasPhaseOp_laplace (hq : q ≠ ⊤) {ν : ℝ} (hν : 0 ≤ ν) (hG : FreeTestGenerator P q hq ν)
    (S : Infra.ExpSemigroup (Yq P q)) (hS : ∀ t, S.T t = phaseT hq ν t) {μ : ℂ}
    (hμ : S.ω < μ.re) (h : Yq P q) :
    HasPhaseOp (fun Φ => μ • Φ + B0411.L0T ν Φ) (S.laplace μ h) h := by
  intro Φ hΦ
  set z := S.laplace μ h with hz
  -- the right derivative of `t ↦ ⟪Φ, 𝒯(t) z⟫` from the shift formula
  set I : ℝ → Yq P q := fun t => ∫ r in (0 : ℝ)..t, S.lapInt μ h r with hI
  set g : ℝ → Yq P q := fun t => Complex.exp (μ * t) • (z - I t) with hg
  have hI' : HasDerivWithinAt I (S.lapInt μ h 0) (Ici 0) 0 := by
    have hc := S.continuousOn_lapInt μ h
    exact intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0)
      IntervalIntegrable.refl
      ((hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
      ((hc 0 Set.self_mem_Ici).mono Ioi_subset_Ici_self)
  have hlap0 : S.lapInt μ h 0 = h := by
    simp [Infra.ExpSemigroup.lapInt_def, S.T_zero_apply]
  have hI0 : I 0 = 0 := by simp [hI]
  have hg' : HasDerivWithinAt g (μ • z - h) (Ici 0) 0 := by
    have hexp := (Infra.ExpSemigroup.hasDerivAt_cexp_mul μ 0).hasDerivWithinAt (s := Ici 0)
    have hsub := (hasDerivWithinAt_const (0 : ℝ) (Ici 0) z).sub hI'
    have hprod := hexp.smul hsub
    refine hprod.congr_deriv ?_
    rw [hlap0]
    simp [Pi.sub_apply, hI0]
    abel
  have hG' : HasDerivWithinAt (fun t => phasePair P q Φ (g t)) (phasePair P q Φ (μ • z - h))
      (Ici 0) 0 :=
    ((phasePair P q Φ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hg'
  have hA := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).1
    (hG'.mono Ioi_subset_Ici_self)
  have hg0 : g 0 = z := by simp [hg, hI0]
  have hA' : Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (phasePair P q Φ (phaseT hq ν t z) -
      phasePair P q Φ z)) (𝓝[>] 0) (𝓝 (phasePair P q Φ (μ • z - h))) := by
    refine hA.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [slope_def_module, sub_zero, hg0]
    congr 2
    rw [← hS t, S.T_laplace_apply hμ ht0 h]
    rfl
  have hB := tendsto_weak_generator hq hν hG hΦ z
  have heq := tendsto_nhds_unique hA' hB
  rw [map_sub, map_smul, smul_eq_mul] at heq
  show phasePair P q (μ • Φ + B0411.L0T ν Φ) z = phasePair P q Φ h
  rw [phasePair_add (hΦ.const_smul μ) (B0411.isPhaseTest_L0T hΦ ν), phasePair_const_smul hΦ μ]
  linear_combination heq

end Generator

end UnforcedLeray.Short.PartIIa.F02
