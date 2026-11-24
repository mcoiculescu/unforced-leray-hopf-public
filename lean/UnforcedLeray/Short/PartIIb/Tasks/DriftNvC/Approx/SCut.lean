import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Approx.EtaCut
import UnforcedLeray.Short.PartIIb.Sub.T12_7

/-!
# Part II-b, task `PartII-b:T08/2/1` (`DriftSCutApprox`): the `s`-cutoff

Source of record: `the November 2 reference manuscript`, lines 1898-1915.

Multiply `(b, Sb)` by `χ_n(s) = bump(log s / (n+1))` (zero for `s ≤ 0`).  Then
`S(χ b) = χ Sb + (s χ') b` weakly, the new profiles are supported in `[e^{-2(n+1)}, e^{2(n+1)}]`,
and the errors `(χ_n - 1) b`, `(χ_n - 1) Sb` and `(s χ_n') b` tend to `0` in `H_r`
(dominated convergence on `{s > 0}`, and the uniform bound `|s χ_n'| ≤ M/(n+1)`).
The `s`-dependence of the cutoff is handled by the Leibniz identity for `coordTranspose vS dZero`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace DriftSCutHelp

/-- The smooth bump on `ℝ` (from the `η`-cutoff file). -/
abbrev bmp : ContDiffBump (0 : ℝ) := DriftEtaCutHelp.bump1

lemma bmp_smooth : ContDiff ℝ ∞ (fun y : ℝ => bmp y) := bmp.contDiff

/-- The log-scale bump at scale `k`: `bmp (log s / k)` for `s > 0`, and `0` for `s ≤ 0`. -/
def sBump (k s : ℝ) : ℝ := if 0 < s then bmp (Real.log s / k) else 0

lemma sBump_zero_of_lt {k : ℝ} (hk : 0 < k) {s : ℝ} (h : s < Real.exp (-2 * k)) :
    sBump k s = 0 := by
  unfold sBump
  split_ifs with hs
  · apply bmp.zero_of_le_dist
    have hl : Real.log s < -2 * k := by
      have := Real.log_lt_log hs h
      rwa [Real.log_exp] at this
    have h2 : Real.log s / k < -2 := by
      rw [div_lt_iff₀ hk]; linarith
    show (2 : ℝ) ≤ dist (Real.log s / k) 0
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith
  · rfl

lemma sBump_zero_of_gt {k : ℝ} (hk : 0 < k) {s : ℝ} (h : Real.exp (2 * k) < s) :
    sBump k s = 0 := by
  have hs : 0 < s := lt_trans (Real.exp_pos _) h
  have hl : 2 * k < Real.log s := by
    have := Real.log_lt_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  unfold sBump
  rw [if_pos hs]
  apply bmp.zero_of_le_dist
  have h2 : 2 < Real.log s / k := by
    rw [lt_div_iff₀ hk]; linarith
  show (2 : ℝ) ≤ dist (Real.log s / k) 0
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  linarith

lemma sBump_one {k : ℝ} (hk : 0 < k) {s : ℝ} (hs : 0 < s) (h : |Real.log s| ≤ k) :
    sBump k s = 1 := by
  unfold sBump
  rw [if_pos hs]
  apply bmp.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hk]
  show |Real.log s| / k ≤ 1
  rw [div_le_one hk]
  exact h

lemma sBump_nonneg (k s : ℝ) : 0 ≤ sBump k s := by
  unfold sBump
  split_ifs
  · exact bmp.nonneg
  · exact le_rfl

lemma sBump_le_one (k s : ℝ) : sBump k s ≤ 1 := by
  unfold sBump
  split_ifs
  · exact bmp.le_one
  · exact zero_le_one

lemma sBump_eventually_one {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, sBump ((n : ℝ) + 1) s = 1 := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |Real.log s|]
    with n hn
  exact sBump_one (by positivity) hs (by linarith)

lemma sBump_smooth {k : ℝ} (hk : 0 < k) : ContDiff ℝ ∞ (sBump k) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < Real.exp (-2 * k)
  · have hc0 : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) s := contDiffAt_const
    refine hc0.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with t ht
    exact sBump_zero_of_lt hk ht
  · push_neg at hs
    have hpos : 0 < s := lt_of_lt_of_le (Real.exp_pos _) hs
    have hlog : ContDiffAt ℝ ∞ (fun t : ℝ => Real.log t / k) s :=
      (Real.contDiffAt_log.2 hpos.ne').div_const k
    have hB0 : ContDiffAt ℝ ∞ (fun y : ℝ => bmp y) (Real.log s / k) :=
      bmp_smooth.contDiffAt
    have hb : ContDiffAt ℝ ∞ (fun t : ℝ => bmp (Real.log t / k)) s :=
      ContDiffAt.comp (g := fun y : ℝ => bmp y) (f := fun t : ℝ => Real.log t / k) s hB0 hlog
    refine hb.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hpos] with t ht
    unfold sBump
    rw [if_pos (Set.mem_Ioi.1 ht)]

lemma sBump_hasDerivAt_pos {k : ℝ} (hk : 0 < k) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (sBump k) (deriv (fun y : ℝ => bmp y) (Real.log s / k) * (s⁻¹ / k)) s := by
  have h1 : HasDerivAt (fun t : ℝ => Real.log t / k) (s⁻¹ / k) s :=
    (Real.hasDerivAt_log hs.ne').div_const k
  have hBd : Differentiable ℝ (fun y : ℝ => bmp y) := bmp_smooth.differentiable (by simp)
  have hB : HasDerivAt (fun y : ℝ => bmp y) (deriv (fun y : ℝ => bmp y) (Real.log s / k))
      (Real.log s / k) :=
    (hBd (Real.log s / k)).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => bmp (Real.log t / k))
      (deriv (fun y : ℝ => bmp y) (Real.log s / k) * (s⁻¹ / k)) s :=
    by
      have key : ∀ g : ℝ → ℝ, ∀ a : ℝ, HasDerivAt g a (Real.log s / k) →
          HasDerivAt (fun t : ℝ => g (Real.log t / k)) (a * (s⁻¹ / k)) s := fun g a hg => hg.comp s h1
      exact key (fun y : ℝ => bmp y) _ hB
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with t ht
  unfold sBump
  rw [if_pos (Set.mem_Ioi.1 ht)]

lemma sBump_deriv_zero_of_lt {k : ℝ} (hk : 0 < k) {s : ℝ} (h : s < Real.exp (-2 * k)) :
    deriv (sBump k) s = 0 := by
  have h0 : HasDerivAt (sBump k) 0 s := by
    refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with t ht
    exact sBump_zero_of_lt hk ht
  exact h0.deriv

lemma sBump_deriv_zero_of_gt {k : ℝ} (hk : 0 < k) {s : ℝ} (h : Real.exp (2 * k) < s) :
    deriv (sBump k) s = 0 := by
  have h0 : HasDerivAt (sBump k) 0 s := by
    refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with t ht
    exact sBump_zero_of_gt hk ht
  exact h0.deriv

/-- Uniform bound `|s χ_k'(s)| ≤ M / k`. -/
lemma sBump_deriv_bound_exists :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℝ, 0 < k → ∀ s : ℝ, |s * deriv (sBump k) s| ≤ M * (1 / k) := by
  have hcd : Continuous (deriv (fun y : ℝ => bmp y)) := bmp_smooth.continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv (fun y : ℝ => bmp y)) := bmp.hasCompactSupport.deriv
  obtain ⟨M, hM⟩ := hcd.bounded_above_of_compact_support hcs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun k hk s => ?_⟩
  by_cases h : s < Real.exp (-2 * k)
  · rw [sBump_deriv_zero_of_lt hk h, mul_zero, abs_zero]
    exact mul_nonneg hM0 (one_div_pos.2 hk).le
  · push_neg at h
    have hpos : 0 < s := lt_of_lt_of_le (Real.exp_pos _) h
    have hs0 : s ≠ 0 := hpos.ne'
    rw [(sBump_hasDerivAt_pos hk hpos).deriv]
    have e : s * (deriv (fun y : ℝ => bmp y) (Real.log s / k) * (s⁻¹ / k)) =
        deriv (fun y : ℝ => bmp y) (Real.log s / k) * (1 / k) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (one_div_pos.2 hk)]
    apply mul_le_mul_of_nonneg_right ?_ (one_div_pos.2 hk).le
    have := hM (Real.log s / k)
    rwa [Real.norm_eq_abs] at this

lemma sCut_fderiv {k : ℝ} (hk : 0 < k) (x : Coord) :
    fderiv ℝ (fun y : Coord => sBump k y.1) x (cdir 0) = deriv (sBump k) x.1 := by
  have hd : HasDerivAt (sBump k) (deriv (sBump k) x.1) x.1 :=
    ((sBump_smooth hk).differentiable (by simp) x.1).hasDerivAt
  have h : HasFDerivAt (fun y : Coord => sBump k y.1)
      (deriv (sBump k) x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    hd.comp_hasFDerivAt x hasFDerivAt_fst
  rw [h.fderiv]
  simp [cdir]

lemma sD_continuous {k : ℝ} (hk : 0 < k) :
    Continuous (fun x : Coord => x.1 * deriv (sBump k) x.1) :=
  continuous_fst.mul (((sBump_smooth hk).continuous_deriv (by simp)).comp continuous_fst)

/-- Leibniz rule for the transpose of `vS = s ∂_s` against an `s`-cutoff. -/
lemma coordT_mul_cut {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ) {φ : Coord → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    coordTranspose vS dZero (fun y => χ y * φ y) x =
      χ x * coordTranspose vS dZero φ x - (x.1 * fderiv ℝ χ x (cdir 0)) * φ x := by
  have hχd : DifferentiableAt ℝ χ x := (hχ.differentiable (by simp)) x
  have hA : ContDiff ℝ ∞ (fun y : Coord => y.1 * φ y) := contDiff_fst.mul hφ
  have hAd : DifferentiableAt ℝ (fun y : Coord => y.1 * φ y) x := (hA.differentiable (by simp)) x
  have e : (fun y : Coord => y.1 * (χ y * φ y)) = fun y => χ y * (y.1 * φ y) :=
    funext fun y => by ring
  have hm : fderiv ℝ (fun y : Coord => χ y * (y.1 * φ y)) x =
      χ x • fderiv ℝ (fun y : Coord => y.1 * φ y) x + (x.1 * φ x) • fderiv ℝ χ x :=
    fderiv_mul hχd hAd
  rw [DriftEtaCutHelp.coordTranspose_vS, DriftEtaCutHelp.coordTranspose_vS, e, hm]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Weak first-order Leibniz rule for `χ · u` with `D = s ∂_s χ`. -/
lemma hasWeakFO_leib {χ D : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ) (hbd : ∃ C, ∀ x, ‖χ x‖ ≤ C)
    (hD : ∀ x, D x = x.1 * fderiv ℝ χ x (cdir 0)) (hDc : Continuous D)
    {u g : Coord → ℂ} (hw : HasWeakFO vS dZero u g)
    (hu : ∀ f : Coord → ℂ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ Ioi (0 : ℝ) ×ˢ univ → Integrable (fun x => u x * f x)) :
    HasWeakFO vS dZero (fun x => (χ x : ℂ) * u x)
      (fun x => (χ x : ℂ) * g x + (D x : ℂ) * u x) := by
  obtain ⟨C, hC⟩ := hbd
  have hχc : Continuous χ := hχ.continuous
  have hcC : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχc
  have hDφ : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => u x * ((D x * φ x : ℝ) : ℂ)) := by
    intro φ hφ
    have hcs : HasCompactSupport (fun x => D x * φ x) := hφ.compact.mul_left (f := D)
    refine hu (fun x => ((D x * φ x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (hDc.mul hφ.smooth.continuous)) ?_ ?_
    · exact hcs.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
    · exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) (by simp) _).trans
        ((tsupport_mul_subset_right).trans hφ.supp)
  have hAφ : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => (χ x : ℂ) * (g x * (φ x : ℂ))) := by
    intro φ hφ
    refine Integrable.bdd_mul (c := C) (hw.1 φ hφ).2 hcC.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_real]
    exact hC x
  have hTpt : ∀ φ : Coord → ℝ, IsCoordTest φ → ∀ x,
      coordTranspose vS dZero (fun y => χ y * φ y) x =
        χ x * coordTranspose vS dZero φ x - D x * φ x := by
    intro φ hφ x
    rw [coordT_mul_cut hχ hφ.smooth x, hD x]
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · -- integrability of `(χ u) T φ`
    have h1 := (hw.1 _ (DriftEtaCutHelp.isCoordTest_mul hχ hφ)).1
    refine (h1.add (hDφ φ hφ)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    rw [hTpt φ hφ x]
    push_cast
    ring
  · -- integrability of `(χ g + D u) φ`
    refine ((hAφ φ hφ).add (hDφ φ hφ)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    push_cast
    ring
  · -- the weak identity
    have ht := DriftEtaCutHelp.isCoordTest_mul hχ hφ
    have h1 := (hw.1 _ ht).1
    have hB := hDφ φ hφ
    have eL : ∫ x, ((χ x : ℂ) * g x + (D x : ℂ) * u x) * ((φ x : ℝ) : ℂ) =
        (∫ x, (χ x : ℂ) * (g x * (φ x : ℂ))) + ∫ x, u x * ((D x * φ x : ℝ) : ℂ) := by
      rw [← integral_add (hAφ φ hφ) hB]
      congr 1
      funext x
      push_cast
      ring
    have eR : ∫ x, (χ x : ℂ) * u x * (coordTranspose vS dZero φ x : ℂ) =
        (∫ x, u x * (coordTranspose vS dZero (fun y => χ y * φ y) x : ℂ)) +
          ∫ x, u x * ((D x * φ x : ℝ) : ℂ) := by
      rw [← integral_add h1 hB]
      congr 1
      funext x
      rw [hTpt φ hφ x]
      push_cast
      ring
    have eG : ∫ x, g x * ((χ x * φ x : ℝ) : ℂ) =
        ∫ x, (χ x : ℂ) * (g x * (φ x : ℂ)) := by
      congr 1
      funext x
      push_cast
      ring
    have key := (hw.2 _ ht).symm
    beta_reduce at key
    rw [eL, eR, key, eG]

/-- Componentwise weak identity for the `s`-cut pair. -/
lemma cut_hasWeakVec {c r k : ℝ} (hk : 0 < k) (hc : 0 < c) (hr : 1 < r) {b Sb : CProf}
    (hb : InHr c r b) (hw : HasWeakVec vS dZero b Sb) :
    HasWeakVec vS dZero (fun x => ((sBump k x.1 : ℝ) : ℂ) • b x)
      (fun x => ((sBump k x.1 : ℝ) : ℂ) • Sb x + ((x.1 * deriv (sBump k) x.1 : ℝ) : ℂ) • b x) := by
  intro i
  have hχC : ContDiff ℝ ∞ (fun y : Coord => sBump k y.1) :=
    (sBump_smooth hk).comp contDiff_fst
  have hbd : ∃ C, ∀ x : Coord, ‖(fun y : Coord => sBump k y.1) x‖ ≤ C :=
    ⟨1, fun x => by
      show ‖sBump k x.1‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sBump_nonneg _ _)]
      exact sBump_le_one _ _⟩
  have h := hasWeakFO_leib (χ := fun y : Coord => sBump k y.1)
    (D := fun x : Coord => x.1 * deriv (sBump k) x.1) hχC hbd
    (fun x => by show x.1 * deriv (sBump k) x.1 = _; rw [sCut_fderiv hk])
    (sD_continuous hk) (hw i)
    (fun f hf hf' hs => deqIntegrableMul c r b hc hr hb i f hf hf' hs)
  simpa [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] using h

lemma hNorm_smul_le {c r : ℝ} {χ : Coord → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖χ x‖ ≤ C)
    (f : CProf) :
    hNorm c r (fun x => (χ x : ℂ) • f x) ≤ ‖(C : ℂ)‖ₑ * hNorm c r f := by
  unfold hNorm
  calc eLpNorm (fun x => (χ x : ℂ) • f x) (ENNReal.ofReal r) (hMeas c r)
      ≤ eLpNorm (fun x => (C : ℂ) • f x) (ENNReal.ofReal r) (hMeas c r) := by
        refine eLpNorm_mono (fun x => ?_)
        simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC0]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    _ = ‖(C : ℂ)‖ₑ * eLpNorm f (ENNReal.ofReal r) (hMeas c r) :=
        eLpNorm_const_smul (C : ℂ) f (ENNReal.ofReal r) (hMeas c r)

lemma inHr_smul_bdd {c r : ℝ} {χ : Coord → ℝ} (hχc : Continuous χ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖χ x‖ ≤ C) (hper : ∀ x, χ (qShift c x) = χ x) {b : CProf} (hb : InHr c r b) :
    InHr c r (fun x => (χ x : ℂ) • b x) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hb.periodic] with x hx
    simp only [hper x, hx]
  · exact ((Complex.continuous_ofReal.comp hχc).aestronglyMeasurable (μ := hMeas c r)).smul
      hb.meas
  · refine lt_of_le_of_lt (hNorm_smul_le hC0 hC b) (ENNReal.mul_lt_top ?_ hb.finite)
    simp

lemma hNorm_add_le' {c r : ℝ} (hr : 1 < r) {A B : CProf}
    (hA : AEStronglyMeasurable A (hMeas c r)) (hB : AEStronglyMeasurable B (hMeas c r)) :
    hNorm c r (fun x => A x + B x) ≤ hNorm c r A + hNorm c r B := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  unfold hNorm
  exact eLpNorm_add_le hA hB hr1

lemma inHr_add {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r f) (hg : InHr c r g) :
    InHr c r (fun x => f x + g x) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x h1 h2
    simp only [h1, h2]
  · exact hf.meas.add hg.meas
  · exact lt_of_le_of_lt (hNorm_add_le' hr hf.meas hg.meas)
      (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

/-- The truncation error `(χ_n - 1) f → 0` in `H_r`. -/
lemma tendsto_sCut_sub {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {f : CProf} (hf : InHr c r f) :
    Tendsto (fun n : ℕ => hNorm c r (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x))
      atTop (𝓝 0) := by
  have hrpos : (0 : ℝ) < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hrpos).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hrpos.le
  have hnorm : ∀ n : ℕ, hNorm c r (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x) =
      (∫⁻ x, ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r) := by
    intro n
    unfold hNorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hrt]
  have hcont : ∀ n : ℕ, Continuous (fun x : Coord => (sBump ((n : ℝ) + 1) x.1 : ℂ)) := fun n =>
    Complex.continuous_ofReal.comp
      ((sBump_smooth (by positivity : (0 : ℝ) < (n : ℝ) + 1)).continuous.comp continuous_fst)
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun x => ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r) (hMeas c r) := by
    intro n
    have hg : AEStronglyMeasurable (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x)
        (hMeas c r) :=
      ((hcont n).aestronglyMeasurable.smul hf.meas).sub hf.meas
    exact hg.enorm.pow_const r
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ r ∂(hMeas c r) ≠ ⊤ := by
    have h := hf.finite
    unfold hNorm at h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hrt] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.2 hrpos)).1 h).ne
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r
      ∂(hMeas c r)) atTop (𝓝 0) := by
    have hae : ∀ᵐ x ∂(hMeas c r), 0 < x.1 := by
      unfold hMeas
      filter_upwards [Axi.ae_ageμ_mem hc (r / 2 - 5 / 2)] with x hx
      exact (Set.mem_prod.1 hx).1
    have := tendsto_lintegral_of_dominated_convergence' (μ := hMeas c r)
      (f := fun _ => (0 : ℝ≥0∞))
      (F := fun n x => ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r)
      (fun x => ‖f x‖ₑ ^ r) hmeas ?_ hfin ?_
    · simpa using this
    · intro n
      refine ae_of_all _ fun x => ?_
      have hle : ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ ≤ ‖f x‖ := by
        have e : (sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x =
            (((sBump ((n : ℝ) + 1) x.1 - 1 : ℝ)) : ℂ) • f x := by
          rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [abs_le]
        constructor <;> linarith [sBump_nonneg ((n : ℝ) + 1) x.1, sBump_le_one ((n : ℝ) + 1) x.1]
      calc ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r
          = (ENNReal.ofReal ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖) ^ r := by
            rw [ofReal_norm]
        _ ≤ (ENNReal.ofReal ‖f x‖) ^ r :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) hrpos.le
        _ = ‖f x‖ₑ ^ r := by rw [ofReal_norm]
    · filter_upwards [hae] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [sBump_eventually_one hx] with n hn
      simp [hn, ENNReal.zero_rpow_of_pos hrpos]
  have hpow : Tendsto (fun n : ℕ => (∫⁻ x, ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r
      ∂(hMeas c r)) ^ (1 / r)) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp hlim
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hrpos)] at h
    exact h
  rw [show (fun n : ℕ => hNorm c r (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x)) =
      fun n : ℕ => (∫⁻ x, ‖(sBump ((n : ℝ) + 1) x.1 : ℂ) • f x - f x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r)
      from funext hnorm]
  exact hpow

/-- The derivative term `(s χ_n') f → 0` in `H_r`. -/
lemma tendsto_dterm {c r : ℝ} {f : CProf} (hf : InHr c r f) {M : ℝ} (hM0 : 0 ≤ M)
    (hMb : ∀ k : ℝ, 0 < k → ∀ s : ℝ, |s * deriv (sBump k) s| ≤ M * (1 / k)) :
    Tendsto (fun n : ℕ => hNorm c r (fun x => ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • f x))
      atTop (𝓝 0) := by
  have hC0 : ∀ n : ℕ, 0 ≤ M * (1 / ((n : ℝ) + 1)) := fun n =>
    mul_nonneg hM0 (by positivity)
  have hle : ∀ n : ℕ, hNorm c r (fun x => ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • f x) ≤
      ‖((M * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)‖ₑ * hNorm c r f := fun n =>
    hNorm_smul_le (χ := fun x : Coord => x.1 * deriv (sBump ((n : ℝ) + 1)) x.1) (hC0 n)
      (fun x => by
        show ‖x.1 * deriv (sBump ((n : ℝ) + 1)) x.1‖ ≤ M * (1 / ((n : ℝ) + 1))
        rw [Real.norm_eq_abs]
        exact hMb _ (by positivity) x.1) f
  have h1 : Tendsto (fun n : ℕ => M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul M
  have hlim1 : Tendsto (fun n : ℕ => ‖((M * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)‖ₑ) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal h1
    simp only [ENNReal.ofReal_zero] at h
    refine Tendsto.congr (fun n => ?_) h
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hC0 n)]
  have hlim2 : Tendsto (fun n : ℕ => ‖((M * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)‖ₑ * hNorm c r f)
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hlim1 (Or.inr hf.finite.ne)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2 (fun n => bot_le) hle

end DriftSCutHelp

open DriftSCutHelp in
/-- **Target** `driftSCutApprox_proof` (`PartII-b:T08/2/1`). -/
theorem driftSCutApprox_proof : UnforcedLeray.Short.IIb.DriftSCutApprox := by
  intro c r b Sb hc hr hp ε hε
  obtain ⟨hb, hSb, hw⟩ := hp
  obtain ⟨M, hM0, hMb⟩ := sBump_deriv_bound_exists
  have t1 := tendsto_sCut_sub hc hr hb
  have t2 := tendsto_sCut_sub hc hr hSb
  have t3 := tendsto_dterm hb hM0 hMb
  have t23 := t2.add t3
  rw [add_zero] at t23
  have ev : ∀ᶠ n : ℕ in atTop,
      hNorm c r (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • b x - b x) < ENNReal.ofReal ε ∧
      hNorm c r (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • Sb x - Sb x) +
        hNorm c r (fun x => ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x)
          < ENNReal.ofReal ε :=
    ((tendsto_order.1 t1).2 _ (ENNReal.ofReal_pos.2 hε)).and
      ((tendsto_order.1 t23).2 _ (ENNReal.ofReal_pos.2 hε))
  obtain ⟨n, hn1, hn2⟩ := ev.exists
  have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hχc : Continuous (fun y : Coord => sBump ((n : ℝ) + 1) y.1) :=
    (sBump_smooth hk).continuous.comp continuous_fst
  have hχC : ContDiff ℝ ∞ (fun y : Coord => sBump ((n : ℝ) + 1) y.1) :=
    (sBump_smooth hk).comp contDiff_fst
  have hbd1 : ∀ x : Coord, ‖sBump ((n : ℝ) + 1) x.1‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sBump_nonneg _ _)]
    exact sBump_le_one _ _
  have hbn : InHr c r (fun x => ((sBump ((n : ℝ) + 1) x.1 : ℝ) : ℂ) • b x) :=
    inHr_smul_bdd (c := c) (χ := fun y : Coord => sBump ((n : ℝ) + 1) y.1) hχc zero_le_one
      hbd1 (fun x => rfl) hb
  have hDc : Continuous (fun x : Coord => x.1 * deriv (sBump ((n : ℝ) + 1)) x.1) :=
    sD_continuous hk
  have hCn : 0 ≤ M * (1 / ((n : ℝ) + 1)) := mul_nonneg hM0 (by positivity)
  have hDbd : ∀ x : Coord, ‖x.1 * deriv (sBump ((n : ℝ) + 1)) x.1‖ ≤ M * (1 / ((n : ℝ) + 1)) :=
    fun x => by
      rw [Real.norm_eq_abs]
      exact hMb _ hk x.1
  have hSbn : InHr c r (fun x => ((sBump ((n : ℝ) + 1) x.1 : ℝ) : ℂ) • Sb x +
      ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x) :=
    inHr_add hr
      (inHr_smul_bdd (c := c) (χ := fun y : Coord => sBump ((n : ℝ) + 1) y.1) hχc zero_le_one
        hbd1 (fun x => rfl) hSb)
      (inHr_smul_bdd (c := c) (χ := fun x : Coord => x.1 * deriv (sBump ((n : ℝ) + 1)) x.1)
        hDc hCn hDbd (fun x => rfl) hb)
  have hwn := cut_hasWeakVec hk hc hr hb hw
  have hAm : AEStronglyMeasurable (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • Sb x - Sb x)
      (hMeas c r) :=
    ((Complex.continuous_ofReal.comp hχc).aestronglyMeasurable (μ := hMeas c r)).smul hSb.meas
      |>.sub hSb.meas
  have hBm : AEStronglyMeasurable (fun x => ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x)
      (hMeas c r) :=
    ((Complex.continuous_ofReal.comp hDc).aestronglyMeasurable (μ := hMeas c r)).smul hb.meas
  refine ⟨fun x => ((sBump ((n : ℝ) + 1) x.1 : ℝ) : ℂ) • b x,
    fun x => ((sBump ((n : ℝ) + 1) x.1 : ℝ) : ℂ) • Sb x +
      ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x,
    ⟨⟨hbn, hSbn, hwn⟩, Real.exp (-2 * ((n : ℝ) + 1)), Real.exp (2 * ((n : ℝ) + 1)),
      Real.exp_pos _, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rcases hx with h | h
    · simp [sBump_zero_of_lt hk h]
    · simp [sBump_zero_of_gt hk h]
  · intro x hx
    rcases hx with h | h
    · simp [sBump_zero_of_lt hk h, sBump_deriv_zero_of_lt hk h]
    · simp [sBump_zero_of_gt hk h, sBump_deriv_zero_of_gt hk h]
  · exact hn1
  · have key : hNorm c r (fun x => ((sBump ((n : ℝ) + 1) x.1 : ℝ) : ℂ) • Sb x +
        ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x -
          Sb x) ≤
        hNorm c r (fun x => (sBump ((n : ℝ) + 1) x.1 : ℂ) • Sb x - Sb x) +
          hNorm c r (fun x => ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x) := by
      have e : (fun x => ((sBump ((n : ℝ) + 1) x.1 : ℝ) : ℂ) • Sb x +
          ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x - Sb x) =
          (fun x => ((sBump ((n : ℝ) + 1) x.1 : ℂ) • Sb x - Sb x) +
            ((x.1 * deriv (sBump ((n : ℝ) + 1)) x.1 : ℝ) : ℂ) • b x) := by
        funext x
        abel
      rw [e]
      exact hNorm_add_le' hr hAm hBm
    exact lt_of_le_of_lt key hn2
