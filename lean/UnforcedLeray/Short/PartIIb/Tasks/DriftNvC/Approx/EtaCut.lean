import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_2

/-!
# Part II-b, task `PartII-b:T08/2/2` (`DriftEtaCutApprox`): the `η`-cutoff

Source of record: `the November 2 reference manuscript`, lines 1898-1915.

Multiply `(b, Sb)` by `χ_k(η) = θ(η/(k+1))`, `θ` a smooth bump equal to `1` on `[-1,1]` and
vanishing off `(-2,2)`. The cutoff depends only on `η`, so `vS` (which moves only `s`) does not
see it: `coordTranspose vS dZero (χ φ) = χ · coordTranspose vS dZero φ` and the weak identity
`S(χ b) = χ Sb` holds with no derivative of `χ` in `s`. The truncation error `(χ_k - 1) b → 0`
in `H_r` by dominated convergence (pointwise eventually `χ_k = 1`, dominated by `|b|`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace DriftEtaCutHelp

/-- The smooth bump on `ℝ`: `1` on `[-1, 1]`, `0` off `(-2, 2)`. -/
def bump1 : ContDiffBump (0 : ℝ) :=
  { rIn := 1
    rOut := 2
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }

/-- The `η`-cutoff at scale `k + 1`. -/
def etaCut (k : ℕ) (x : Coord) : ℝ := bump1 (x.2.2 / ((k : ℝ) + 1))

lemma etaCut_nonneg (k : ℕ) (x : Coord) : 0 ≤ etaCut k x :=
  bump1.nonneg

lemma etaCut_le_one (k : ℕ) (x : Coord) : etaCut k x ≤ 1 :=
  bump1.le_one

lemma etaCut_smooth (k : ℕ) : ContDiff ℝ ∞ (etaCut k) := by
  unfold etaCut
  exact bump1.contDiff.comp ((contDiff_snd.comp contDiff_snd).div_const _)

lemma etaCut_cdir0 (k : ℕ) (x : Coord) (t : ℝ) :
    etaCut k (x + t • cdir 0) = etaCut k x := by
  simp [etaCut, cdir]

/-- `χ` vanishes where `|η|` exceeds `2 (k+1)`. -/
lemma etaCut_zero_of (k : ℕ) (x : Coord) (h : 2 * ((k : ℝ) + 1) < |x.2.2|) :
    etaCut k x = 0 := by
  unfold etaCut
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  apply bump1.zero_of_le_dist
  show (2 : ℝ) ≤ dist (x.2.2 / ((k : ℝ) + 1)) 0
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hk, le_div_iff₀ hk]
  linarith

/-- `χ_k = 1` eventually in `k`, at each point. -/
lemma etaCut_eventually_one (x : Coord) : ∀ᶠ k : ℕ in atTop, etaCut k x = 1 := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |x.2.2|] with k hk
  have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold etaCut
  apply bump1.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hk']
  show |x.2.2| / ((k : ℝ) + 1) ≤ 1
  rw [div_le_one hk']
  linarith

/-- The derivative of a function invariant under `x ↦ x + t • cdir 0` vanishes in direction
`cdir 0`. -/
lemma fderiv_cdir0_eq_zero {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hinv : ∀ (x : Coord) (t : ℝ), χ (x + t • cdir 0) = χ x) (x : Coord) :
    fderiv ℝ χ x (cdir 0) = 0 := by
  have hd : HasDerivAt (fun t : ℝ => x + t • cdir 0) (cdir 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (cdir 0)).const_add x
  have hχx : HasFDerivAt χ (fderiv ℝ χ x) x := (hχ.differentiable (by simp) x).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => χ (x + t • cdir 0)) (fderiv ℝ χ x (cdir 0)) 0 :=
    hχx.comp_hasDerivAt_of_eq (0 : ℝ) (by simpa using hd) (by simp)
  have h2 : (fun t : ℝ => χ (x + t • cdir 0)) = fun _ => χ x := funext fun t => hinv x t
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const (0 : ℝ) (χ x))

/-- `coordTranspose vS dZero ψ = -∂_s (s ψ)`. -/
lemma coordTranspose_vS (ψ : Coord → ℝ) (x : Coord) :
    coordTranspose vS dZero ψ x = -(fderiv ℝ (fun y : Coord => y.1 * ψ y) x (cdir 0)) := by
  simp [coordTranspose, vS, dZero, cpd, Fin.sum_univ_three]

/-- The transpose commutes with multiplication by an `s`-independent cutoff. -/
lemma coordTranspose_mul_indep {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hinv : ∀ (x : Coord) (t : ℝ), χ (x + t • cdir 0) = χ x) {φ : Coord → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    coordTranspose vS dZero (fun y => χ y * φ y) x = χ x * coordTranspose vS dZero φ x := by
  have hχd : DifferentiableAt ℝ χ x := (hχ.differentiable (by simp)) x
  have hA : ContDiff ℝ ∞ (fun y : Coord => y.1 * φ y) := contDiff_fst.mul hφ
  have hAd : DifferentiableAt ℝ (fun y : Coord => y.1 * φ y) x :=
    (hA.differentiable (by simp)) x
  have e : (fun y : Coord => y.1 * (χ y * φ y)) = fun y => χ y * (y.1 * φ y) :=
    funext fun y => by ring
  have hm : fderiv ℝ (fun y : Coord => χ y * (y.1 * φ y)) x =
      χ x • fderiv ℝ (fun y : Coord => y.1 * φ y) x + (x.1 * φ x) • fderiv ℝ χ x :=
    fderiv_mul hχd hAd
  rw [coordTranspose_vS, coordTranspose_vS, e, hm]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    fderiv_cdir0_eq_zero hχ hinv x]

lemma isCoordTest_mul {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) : IsCoordTest (fun x => χ x * φ x) := by
  refine ⟨hχ.mul hφ.smooth, ?_, ?_⟩
  · have : HasCompactSupport (χ * φ) := hφ.compact.mul_left
    exact this
  · exact tsupport_mul_subset_right.trans hφ.supp

/-- Weak first-order calculus is stable under multiplication by an `s`-independent cutoff. -/
lemma hasWeakFO_mul {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hinv : ∀ (x : Coord) (t : ℝ), χ (x + t • cdir 0) = χ x) {u g : Coord → ℂ}
    (hw : HasWeakFO vS dZero u g) :
    HasWeakFO vS dZero (fun x => (χ x : ℂ) * u x) (fun x => (χ x : ℂ) * g x) := by
  have hT : ∀ φ : Coord → ℝ, IsCoordTest φ → ∀ x,
      (coordTranspose vS dZero (fun y => χ y * φ y) x : ℂ) =
        (χ x : ℂ) * (coordTranspose vS dZero φ x : ℂ) := by
    intro φ hφ x
    rw [coordTranspose_mul_indep hχ hinv hφ.smooth x]
    push_cast
    ring
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have h := (hw.1 _ (isCoordTest_mul hχ hφ)).1
    refine h.congr (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hT φ hφ x]
    ring
  · have h := (hw.1 _ (isCoordTest_mul hχ hφ)).2
    refine h.congr (ae_of_all _ fun x => ?_)
    dsimp only
    push_cast
    ring
  · have h := hw.2 _ (isCoordTest_mul hχ hφ)
    have e : (fun x => (χ x : ℂ) * g x * (φ x : ℂ)) =
        fun x => g x * (((fun y => χ y * φ y) x : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    rw [e, h]
    congr 1
    funext x
    rw [hT φ hφ x]
    ring

lemma hasWeakVec_mul {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hinv : ∀ (x : Coord) (t : ℝ), χ (x + t • cdir 0) = χ x) {b Sb : CProf}
    (hw : HasWeakVec vS dZero b Sb) :
    HasWeakVec vS dZero (fun x => (χ x : ℂ) • b x) (fun x => (χ x : ℂ) • Sb x) := by
  intro i
  have h := hasWeakFO_mul hχ hinv (hw i)
  simpa [PiLp.smul_apply, smul_eq_mul] using h

/-- Pointwise bound `‖χ z‖ ≤ ‖z‖` for a cutoff with values in `[0, 1]`. -/
lemma norm_smul_cut_le {χ : Coord → ℝ} (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1)
    (x : Coord) (z : CMerid) : ‖(χ x : ℂ) • z‖ ≤ ‖z‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (h0 x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (h1 x)

lemma inHr_mul {c r : ℝ} {χ : Coord → ℝ} (hχc : Continuous χ) (h0 : ∀ x, 0 ≤ χ x)
    (h1 : ∀ x, χ x ≤ 1) (hper : ∀ x, χ (qShift c x) = χ x) {b : CProf} (hb : InHr c r b) :
    InHr c r (fun x => (χ x : ℂ) • b x) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hb.periodic] with x hx
    simp only [hper x, hx]
  · exact ((Complex.continuous_ofReal.comp hχc).aestronglyMeasurable (μ := hMeas c r)).smul
      hb.meas
  · have hle : hNorm c r (fun x => (χ x : ℂ) • b x) ≤ hNorm c r b :=
      eLpNorm_mono fun x => norm_smul_cut_le h0 h1 x (b x)
    exact lt_of_le_of_lt hle hb.finite

/-- The truncation error `(χ_k - 1) b → 0` in `H_r`. -/
lemma tendsto_etaCut_sub {c r : ℝ} (hr : 1 < r) {b : CProf} (hb : InHr c r b) :
    Tendsto (fun k : ℕ => hNorm c r (fun x => (etaCut k x : ℂ) • b x - b x)) atTop (𝓝 0) := by
  have hrpos : (0 : ℝ) < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hrpos).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hrpos.le
  have hnorm : ∀ k : ℕ, hNorm c r (fun x => (etaCut k x : ℂ) • b x - b x) =
      (∫⁻ x, ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r) := by
    intro k
    unfold hNorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hrt]
  have hcont : ∀ k : ℕ, Continuous (fun x => (etaCut k x : ℂ)) := fun k =>
    Complex.continuous_ofReal.comp (etaCut_smooth k).continuous
  have hmeas : ∀ k : ℕ, AEMeasurable (fun x => ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r)
      (hMeas c r) := by
    intro k
    have hg : AEStronglyMeasurable (fun x => (etaCut k x : ℂ) • b x - b x) (hMeas c r) :=
      ((hcont k).aestronglyMeasurable.smul hb.meas).sub hb.meas
    exact (hg.enorm.pow_const r)
  have hfin : ∫⁻ x, ‖b x‖ₑ ^ r ∂(hMeas c r) ≠ ⊤ := by
    have h := hb.finite
    unfold hNorm at h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hrt] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 h).ne
  have hlim : Tendsto (fun k : ℕ => ∫⁻ x, ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r ∂(hMeas c r))
      atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := hMeas c r)
      (f := fun _ => (0 : ℝ≥0∞)) (F := fun k x => ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r)
      (fun x => ‖b x‖ₑ ^ r) hmeas ?_ hfin ?_
    · simpa using this
    · intro k
      refine ae_of_all _ fun x => ?_
      have hle : ‖(etaCut k x : ℂ) • b x - b x‖ ≤ ‖b x‖ := by
        have e : (etaCut k x : ℂ) • b x - b x = (((etaCut k x - 1 : ℝ)) : ℂ) • b x := by
          rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [abs_le]
        constructor <;> linarith [etaCut_nonneg k x, etaCut_le_one k x]
      calc ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r
          = (ENNReal.ofReal ‖(etaCut k x : ℂ) • b x - b x‖) ^ r := by rw [ofReal_norm]
        _ ≤ (ENNReal.ofReal ‖b x‖) ^ r :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) hrpos.le
        _ = ‖b x‖ₑ ^ r := by rw [ofReal_norm]
    · refine ae_of_all _ fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [etaCut_eventually_one x] with k hk
      have hr0 : 0 < r := hrpos
      simp [hk, ENNReal.zero_rpow_of_pos hr0]
  have hpow : Tendsto (fun k : ℕ => (∫⁻ x, ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r ∂(hMeas c r))
      ^ (1 / r)) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp hlim
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at h
    exact h
  rw [show (fun k : ℕ => hNorm c r (fun x => (etaCut k x : ℂ) • b x - b x)) =
      fun k : ℕ => (∫⁻ x, ‖(etaCut k x : ℂ) • b x - b x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r) from
    funext hnorm]
  exact hpow


/-- The `η`-cut pair of a graph pair. -/
lemma driftEtaCut_pair {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {b Sb : CProf} (k : ℕ)
    (hb : InHr c r b) (hSb : InHr c r Sb) (hw : HasWeakVec vS dZero b Sb) :
    InHr c r (fun x => (etaCut k x : ℂ) • b x) ∧ InHr c r (fun x => (etaCut k x : ℂ) • Sb x) ∧
      HasWeakVec vS dZero (fun x => (etaCut k x : ℂ) • b x)
        (fun x => (etaCut k x : ℂ) • Sb x) := by
  refine ⟨inHr_mul (etaCut_smooth k).continuous (etaCut_nonneg k) (etaCut_le_one k)
      (fun x => by simp [etaCut, qShift]) hb,
    inHr_mul (etaCut_smooth k).continuous (etaCut_nonneg k) (etaCut_le_one k)
      (fun x => by simp [etaCut, qShift]) hSb,
    hasWeakVec_mul (etaCut_smooth k) (etaCut_cdir0 k) hw⟩

end DriftEtaCutHelp

open DriftEtaCutHelp in
/-- **Target** `driftEtaCutApprox_proof` (`PartII-b:T08/2/2`). -/
theorem driftEtaCutApprox_proof : UnforcedLeray.Short.IIb.DriftEtaCutApprox := by
  intro c r b Sb hc hr hp ε hε
  obtain ⟨hpair, s0, s1, hs0, hcb, hcS⟩ := hp
  obtain ⟨hb, hSb, hw⟩ := hpair
  have t1 := tendsto_etaCut_sub hr hb
  have t2 := tendsto_etaCut_sub hr hSb
  have ev : ∀ᶠ k : ℕ in atTop,
      hNorm c r (fun x => (etaCut k x : ℂ) • b x - b x) < ENNReal.ofReal ε ∧
      hNorm c r (fun x => (etaCut k x : ℂ) • Sb x - Sb x) < ENNReal.ofReal ε :=
    ((tendsto_order.1 t1).2 _ (ENNReal.ofReal_pos.2 hε)).and
      ((tendsto_order.1 t2).2 _ (ENNReal.ofReal_pos.2 hε))
  obtain ⟨k, hk1, hk2⟩ := ev.exists
  obtain ⟨hb', hSb', hw'⟩ := driftEtaCut_pair hc hr k hb hSb hw
  refine ⟨fun x => (etaCut k x : ℂ) • b x, fun x => (etaCut k x : ℂ) • Sb x,
    ⟨⟨⟨hb', hSb', hw'⟩, s0, s1, hs0, fun x hx => by simp [hcb x hx],
      fun x hx => by simp [hcS x hx]⟩, 2 * ((k : ℝ) + 1),
      fun x hx => by simp [etaCut_zero_of k x hx], fun x hx => by simp [etaCut_zero_of k x hx]⟩,
    hk1, hk2⟩

#print axioms UnforcedLeray.Short.IIb.driftEtaCutApprox_proof

end UnforcedLeray.Short.IIb
