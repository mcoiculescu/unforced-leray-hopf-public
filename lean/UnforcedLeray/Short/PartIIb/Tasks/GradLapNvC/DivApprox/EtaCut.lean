import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_2
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Approx.SCut

/-!
# Part II-b, task `PartII-b:T09/2/2` (`DivEtaCutApprox`): the `η`-cutoff

Source of record: `the November 2 reference manuscript`, lines 1912-1918.

Multiply the triple `(b, Q_ε b, ∂_η b)` by `ψ_k(η) = θ(η/(k+1))`.  The product rule gives
`Q_ε(ψ b) = ψ Q_ε b - ε η (∂_η ψ) b` and `∂_η(ψ b) = ψ ∂_η b + (∂_η ψ) b`.  The `s`-window of
`DivDataS` makes `√s` bounded, so the errors `(ψ-1)√s Q_ε b`, `(ψ-1)√s ∂_η b` tend to `0` by the
existing truncation lemma, and `ε η ∂_η ψ_k √s b`, `∂_η ψ_k √s b` tend to `0` by dominated
convergence (pointwise eventually `0`, uniformly bounded).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace DivEtaCutHelp

open DriftEtaCutHelp DriftSCutHelp

/-! ## The bump and its derivative -/

lemma bump1_smooth : ContDiff ℝ ∞ (fun t : ℝ => bump1 t) := bump1.contDiff

lemma bumpD_cont : Continuous (deriv (fun t : ℝ => bump1 t)) :=
  bump1_smooth.continuous_deriv (by simp)

lemma bumpD_bdd : ∃ M0 : ℝ, ∀ t : ℝ, ‖deriv (fun s : ℝ => bump1 s) t‖ ≤ M0 :=
  bumpD_cont.bounded_above_of_compact_support bump1.hasCompactSupport.deriv

lemma bumpDM_bdd : ∃ M1 : ℝ, ∀ t : ℝ, ‖t * deriv (fun s : ℝ => bump1 s) t‖ ≤ M1 := by
  have hc : Continuous (fun t : ℝ => t * deriv (fun s : ℝ => bump1 s) t) :=
    continuous_id.mul bumpD_cont
  have hs : HasCompactSupport (fun t : ℝ => t * deriv (fun s : ℝ => bump1 s) t) := by
    have h := bump1.hasCompactSupport.deriv
    exact h.mul_left
  exact hc.bounded_above_of_compact_support hs

/-- The derivative of the bump vanishes outside `(-2, 2)`. -/
lemma bumpD_zero_of {y : ℝ} (hy : 2 < |y|) : deriv (fun s : ℝ => bump1 s) y = 0 := by
  have hev : (fun s : ℝ => bump1 s) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with s hs
    apply bump1.zero_of_le_dist
    rw [Real.dist_eq, sub_zero]
    show (2 : ℝ) ≤ |s|
    exact hs.le
  rw [hev.deriv_eq]
  simp

/-- The derivative of the bump vanishes on `(-1, 1)`. -/
lemma bumpD_eq_zero_of_lt {y : ℝ} (hy : |y| < 1) : deriv (fun s : ℝ => bump1 s) y = 0 := by
  have hev : (fun s : ℝ => bump1 s) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hy] with s hs
    apply bump1.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hs.le
  rw [hev.deriv_eq]
  simp

/-! ## The `η`-derivative of the cutoff -/

/-- `∂_η ψ_k` where `ψ_k(x) = bump1(η/(k+1))`. -/
def etaD (k : ℕ) (x : Coord) : ℝ :=
  (1 / ((k : ℝ) + 1)) * deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1))

lemma etaCut_fderiv_apply (k : ℕ) (x w : Coord) :
    fderiv ℝ (etaCut k) x w =
      (1 / ((k : ℝ) + 1)) * deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1)) * w.2.2 := by
  have hd1 : HasDerivAt (fun s : ℝ => s / ((k : ℝ) + 1)) (1 / ((k : ℝ) + 1)) x.2.2 := by
    simpa using (hasDerivAt_id x.2.2).div_const ((k : ℝ) + 1)
  have hd2 : HasDerivAt (fun s : ℝ => bump1 s)
      (deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1))) (x.2.2 / ((k : ℝ) + 1)) :=
    ((bump1_smooth.differentiable (by simp)) _).hasDerivAt
  have hg : HasDerivAt (fun s : ℝ => bump1 (s / ((k : ℝ) + 1)))
      (deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1))) x.2.2 :=
    HasDerivAt.comp (h₂ := fun t : ℝ => bump1 t) (h := fun s : ℝ => s / ((k : ℝ) + 1)) x.2.2
      hd2 hd1
  have hf := (hasFDerivAt_snd (𝕜 := ℝ) (p := x.2)).comp x (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  have h := hg.hasFDerivAt.comp x hf
  have e : etaCut k = (fun s : ℝ => bump1 (s / ((k : ℝ) + 1))) ∘ (Prod.snd ∘ Prod.snd) := rfl
  rw [e, h.fderiv]
  simp [ContinuousLinearMap.smulRight_apply] <;> ring

lemma etaCut_fderiv_eta (k : ℕ) (x : Coord) :
    fderiv ℝ (etaCut k) x (cdir 2) = etaD k x := by
  rw [etaCut_fderiv_apply]
  simp [cdir, etaD]

lemma etaD_cont (k : ℕ) : Continuous (etaD k) :=
  continuous_const.mul (bumpD_cont.comp (((continuous_snd.comp continuous_snd)).div_const _))

lemma etaD_bdd (k : ℕ) (x : Coord) {M0 : ℝ}
    (hM : ∀ t : ℝ, ‖deriv (fun s : ℝ => bump1 s) t‖ ≤ M0) :
    ‖etaD k x‖ ≤ M0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpos : 0 < 1 / ((k : ℝ) + 1) := one_div_pos.2 hk
  have hle : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hk]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hn : ‖(1 / ((k : ℝ) + 1))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact hle
  calc ‖etaD k x‖
      = ‖(1 / ((k : ℝ) + 1))‖ * ‖deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1))‖ := by
        unfold etaD
        rw [norm_mul]
    _ ≤ 1 * M0 := mul_le_mul hn (hM _) (norm_nonneg _) zero_le_one
    _ = M0 := one_mul _

lemma etaD_zero_of (k : ℕ) (x : Coord) (h : 2 * ((k : ℝ) + 1) < |x.2.2|) : etaD k x = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hy : 2 < |x.2.2 / ((k : ℝ) + 1)| := by
    rw [abs_div, abs_of_pos hk, lt_div_iff₀ hk]
    linarith
  unfold etaD
  rw [bumpD_zero_of hy, mul_zero]

lemma etaD_eventually_zero (x : Coord) : ∀ᶠ k : ℕ in atTop, etaD k x = 0 := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |x.2.2|] with k hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hy : |x.2.2 / ((k : ℝ) + 1)| < 1 := by
    rw [abs_div, abs_of_pos hk1, div_lt_one hk1]
    linarith
  unfold etaD
  rw [bumpD_eq_zero_of_lt hy, mul_zero]

/-- `x.2.2 · ∂_η ψ_k` is the function `t ↦ t · bump'(t)` at `t = η/(k+1)`. -/
lemma etaDM_eq (k : ℕ) (x : Coord) :
    x.2.2 * etaD k x = (x.2.2 / ((k : ℝ) + 1)) * deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1)) := by
  unfold etaD
  ring


/-! ## Leibniz rule for a cutoff against `v·∇ + d` -/

/-- The zero-order coefficient produced by moving `v·∇` across the cut `χ`. -/
def cutD (v : Coord → Fin 3 → ℝ) (χ : Coord → ℝ) (x : Coord) : ℝ :=
  ∑ j : Fin 3, v x j * cpd j χ x

lemma coordT_mul_gen {v : Coord → Fin 3 → ℝ} {d χ : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Coord => v y j))
    {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    coordTranspose v d (fun y => χ y * φ y) x =
      χ x * coordTranspose v d φ x - cutD v χ x * φ x := by
  have hχd : DifferentiableAt ℝ χ x := (hχ.differentiable (by simp)) x
  have hterm : ∀ j : Fin 3, cpd j (fun y => v y j * (χ y * φ y)) x =
      χ x * cpd j (fun y => v y j * φ y) x + (v x j * φ x) * cpd j χ x := by
    intro j
    have hA : DifferentiableAt ℝ (fun y : Coord => v y j * φ y) x :=
      (((hv j).mul hφ).differentiable (by simp)) x
    have e : (fun y : Coord => v y j * (χ y * φ y)) = fun y => χ y * (v y j * φ y) :=
      funext fun y => by ring
    unfold cpd
    have hm : fderiv ℝ (fun y : Coord => χ y * (v y j * φ y)) x =
        χ x • fderiv ℝ (fun y : Coord => v y j * φ y) x + (v x j * φ x) • fderiv ℝ χ x :=
      (hχd.hasFDerivAt.mul hA.hasFDerivAt).fderiv
    rw [e, hm]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsum : ∑ j : Fin 3, cpd j (fun y => v y j * (χ y * φ y)) x =
      χ x * ∑ j : Fin 3, cpd j (fun y => v y j * φ y) x
        + (∑ j : Fin 3, v x j * cpd j χ x) * φ x := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [coordTranspose]
  rw [hsum]
  unfold cutD
  ring

lemma hasWeakFO_cut {v : Coord → Fin 3 → ℝ} {d χ : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Coord => v y j))
    (hbd : ∃ C : ℝ, ∀ x, ‖χ x‖ ≤ C) (hDc : Continuous (cutD v χ))
    {u g : Coord → ℂ} (hw : HasWeakFO v d u g)
    (hu : ∀ f : Coord → ℂ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ Ioi (0 : ℝ) ×ˢ univ → Integrable (fun x => u x * f x)) :
    HasWeakFO v d (fun x => (χ x : ℂ) * u x)
      (fun x => (χ x : ℂ) * g x + ((cutD v χ x : ℝ) : ℂ) * u x) := by
  obtain ⟨C, hC⟩ := hbd
  have hχc : Continuous χ := hχ.continuous
  have hcC : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχc
  have hDφ : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => u x * ((cutD v χ x * φ x : ℝ) : ℂ)) := by
    intro φ hφ
    have hcs : HasCompactSupport (fun x => cutD v χ x * φ x) := hφ.compact.mul_left (f := cutD v χ)
    refine hu (fun x => ((cutD v χ x * φ x : ℝ) : ℂ))
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
      coordTranspose v d (fun y => χ y * φ y) x =
        χ x * coordTranspose v d φ x - cutD v χ x * φ x := fun φ hφ x =>
    coordT_mul_gen hχ hv hφ.smooth x
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have h1 := (hw.1 _ (isCoordTest_mul hχ hφ)).1
    refine (h1.add (hDφ φ hφ)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    rw [hTpt φ hφ x]
    push_cast
    ring
  · refine ((hAφ φ hφ).add (hDφ φ hφ)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    push_cast
    ring
  · have ht := isCoordTest_mul hχ hφ
    have h1 := (hw.1 _ ht).1
    have hB := hDφ φ hφ
    have eL : ∫ x, ((χ x : ℂ) * g x + ((cutD v χ x : ℝ) : ℂ) * u x) * ((φ x : ℝ) : ℂ) =
        (∫ x, (χ x : ℂ) * (g x * (φ x : ℂ))) + ∫ x, u x * ((cutD v χ x * φ x : ℝ) : ℂ) := by
      rw [← integral_add (hAφ φ hφ) hB]
      congr 1
      funext x
      push_cast
      ring
    have eR : ∫ x, (χ x : ℂ) * u x * (coordTranspose v d φ x : ℂ) =
        (∫ x, u x * (coordTranspose v d (fun y => χ y * φ y) x : ℂ)) +
          ∫ x, u x * ((cutD v χ x * φ x : ℝ) : ℂ) := by
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

lemma hasWeakVec_cut {c r : ℝ} {v : Coord → Fin 3 → ℝ} {d χ : Coord → ℝ} {b Qb : CProf}
    (hχ : ContDiff ℝ ∞ χ) (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Coord => v y j))
    (hbd : ∃ C : ℝ, ∀ x, ‖χ x‖ ≤ C) (hDc : Continuous (cutD v χ))
    (hc : 0 < c) (hr : 1 < r) (hb : InHr c r b) (hw : HasWeakVec v d b Qb) :
    HasWeakVec v d (fun x => (χ x : ℂ) • b x)
      (fun x => (χ x : ℂ) • Qb x + ((cutD v χ x : ℝ) : ℂ) • b x) := by
  intro i
  have h := hasWeakFO_cut hχ hv hbd hDc (hw i)
    (fun f hf hf' hs => deqIntegrableMul c r b hc hr hb i f hf hf' hs)
  simpa [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] using h

lemma vQ_cd (ε : ℝ) : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Coord => vQ ε y j) := by
  intro j
  fin_cases j <;> simp [vQ] <;> first | exact contDiff_const | fun_prop

lemma vEta_cd : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Coord => vEta y j) := by
  intro j
  fin_cases j <;> simp [vEta] <;> first | exact contDiff_const | fun_prop

/-! ## Values of the cut coefficients -/

lemma cutD_vQ_eq (ε : ℝ) (k : ℕ) (x : Coord) :
    cutD (vQ ε) (etaCut k) x = -ε * x.2.2 * etaD k x := by
  unfold cutD
  simp only [Fin.sum_univ_three, cpd, etaCut_fderiv_apply]
  simp [vQ, cdir, etaD]
  <;> ring

lemma cutD_vEta_eq (k : ℕ) (x : Coord) : cutD vEta (etaCut k) x = etaD k x := by
  unfold cutD
  simp only [Fin.sum_univ_three, cpd, etaCut_fderiv_apply]
  simp [vEta, cdir, etaD]

lemma cutDQ_cont (ε : ℝ) (k : ℕ) : Continuous (fun x : Coord => cutD (vQ ε) (etaCut k) x) := by
  have e : (fun x : Coord => cutD (vQ ε) (etaCut k) x) = fun x => -ε * x.2.2 * etaD k x :=
    funext fun x => cutD_vQ_eq ε k x
  rw [e]
  exact (continuous_const.mul (continuous_snd.comp continuous_snd)).mul (etaD_cont k)

lemma cutDE_cont (k : ℕ) : Continuous (fun x : Coord => cutD vEta (etaCut k) x) := by
  have e : (fun x : Coord => cutD vEta (etaCut k) x) = etaD k :=
    funext fun x => cutD_vEta_eq k x
  rw [e]
  exact etaD_cont k

lemma cutD_vQ_bdd (ε M1 : ℝ) (hM1 : ∀ t : ℝ, ‖t * deriv (fun s : ℝ => bump1 s) t‖ ≤ M1)
    (k : ℕ) (x : Coord) : |cutD (vQ ε) (etaCut k) x| ≤ |ε| * M1 := by
  rw [cutD_vQ_eq]
  have e : -ε * x.2.2 * etaD k x =
      -ε * ((x.2.2 / ((k : ℝ) + 1)) * deriv (fun s : ℝ => bump1 s) (x.2.2 / ((k : ℝ) + 1))) := by
    rw [← etaDM_eq]
    ring
  rw [e, abs_mul, abs_neg]
  have h := hM1 (x.2.2 / ((k : ℝ) + 1))
  rw [Real.norm_eq_abs] at h
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

lemma cutD_vEta_bdd (M0 : ℝ) (hM0 : ∀ t : ℝ, ‖deriv (fun s : ℝ => bump1 s) t‖ ≤ M0)
    (k : ℕ) (x : Coord) : |cutD vEta (etaCut k) x| ≤ M0 := by
  rw [cutD_vEta_eq]
  have h := etaD_bdd k x hM0
  rwa [Real.norm_eq_abs] at h

lemma cutD_vQ_ev (ε : ℝ) (x : Coord) : ∀ᶠ k : ℕ in atTop, cutD (vQ ε) (etaCut k) x = 0 :=
  (etaD_eventually_zero x).mono fun k hk => by rw [cutD_vQ_eq, hk, mul_zero]

lemma cutD_vEta_ev (x : Coord) : ∀ᶠ k : ℕ in atTop, cutD vEta (etaCut k) x = 0 :=
  (etaD_eventually_zero x).mono fun k hk => by rw [cutD_vEta_eq, hk]

/-! ## Multiplication, windows and dominated convergence -/

lemma ecAesm_cut {c r : ℝ} {χ : Coord → ℝ} (hχ : Continuous χ) {f : CProf} (hf : InHr c r f) :
    AEStronglyMeasurable (fun x => (χ x : ℂ) • f x) (hMeas c r) :=
  ((Complex.continuous_ofReal.comp hχ).aestronglyMeasurable (μ := hMeas c r)).smul hf.meas

lemma ecAesm_cut_sub {c r : ℝ} {χ : Coord → ℝ} (hχ : Continuous χ) {f : CProf} (hf : InHr c r f) :
    AEStronglyMeasurable (fun x => (χ x : ℂ) • f x - f x) (hMeas c r) :=
  (ecAesm_cut hχ hf).sub hf.meas

/-- `√s b` is in `H_r` when `b` is supported in a compact `s`-window. -/
lemma ecSqrtInHr {c r s0 s1 : ℝ} {b : CProf} (hcb : SCut s0 s1 b) (hb : InHr c r b) :
    InHr c r (sqrtS b) := by
  have hχc : Continuous (fun x : Coord => min (Real.sqrt x.1) (Real.sqrt s1)) :=
    (Real.continuous_sqrt.comp continuous_fst).min continuous_const
  have hC0 : 0 ≤ Real.sqrt s1 := Real.sqrt_nonneg _
  have hC : ∀ x : Coord, ‖min (Real.sqrt x.1) (Real.sqrt s1)‖ ≤ Real.sqrt s1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.sqrt_nonneg _) hC0)]
    exact min_le_right _ _
  have hper : ∀ x : Coord,
      (fun y : Coord => min (Real.sqrt y.1) (Real.sqrt s1)) (qShift c x) =
        min (Real.sqrt x.1) (Real.sqrt s1) := fun x => rfl
  have e : sqrtS b = fun x => (((min (Real.sqrt x.1) (Real.sqrt s1)) : ℝ) : ℂ) • b x := by
    funext x
    unfold sqrtS
    by_cases hx : x.1 ≤ s1
    · rw [min_eq_left (Real.sqrt_le_sqrt hx)]
    · have h0 : b x = 0 := hcb x (Or.inr (not_le.1 hx))
      rw [h0, smul_zero, smul_zero]
  rw [e]
  exact inHr_smul_bdd hχc hC0 hC hper hb

lemma sqrtS_cut_add (ψ D : Coord → ℝ) (A B : CProf) (x : Coord) :
    sqrtS (fun y => (ψ y : ℂ) • A y + (D y : ℂ) • B y) x =
      (ψ x : ℂ) • sqrtS A x + (D x : ℂ) • sqrtS B x := by
  unfold sqrtS
  module

lemma sqrtS_cut_sub (ψ D : Coord → ℝ) (A B : CProf) (x : Coord) :
    sqrtS (fun y => ((ψ y : ℂ) • A y + (D y : ℂ) • B y) - A y) x =
      ((ψ x : ℂ) • sqrtS A x - sqrtS A x) + (D x : ℂ) • sqrtS B x := by
  unfold sqrtS
  module

/-- Dominated convergence: `g_k f → 0` in `H_r` when `g_k` is continuous, uniformly bounded and
eventually `0` at each point. -/
lemma tendsto_hNorm_cut_zero {c r : ℝ} (hr : 1 < r) {f : CProf} (hf : InHr c r f)
    {g : ℕ → Coord → ℝ} (hg : ∀ k, Continuous (g k)) {C : ℝ} (hC : ∀ k x, |g k x| ≤ C)
    (hlim : ∀ x, ∀ᶠ k : ℕ in atTop, g k x = 0) :
    Tendsto (fun k : ℕ => hNorm c r (fun x => (g k x : ℂ) • f x)) atTop (𝓝 0) := by
  have hrpos : (0 : ℝ) < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hrpos).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hrpos.le
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  have hnorm : ∀ k : ℕ, hNorm c r (fun x => (g k x : ℂ) • f x) =
      (∫⁻ x, ‖(g k x : ℂ) • f x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r) := by
    intro k
    unfold hNorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hrt]
  have hmeas : ∀ k : ℕ, AEMeasurable (fun x => ‖(g k x : ℂ) • f x‖ₑ ^ r) (hMeas c r) := by
    intro k
    exact (ecAesm_cut (hg k) hf).enorm.pow_const r
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ r ∂(hMeas c r) ≠ ⊤ := by
    have h := hf.finite
    unfold hNorm at h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hrt] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 h).ne
  have hK : (ENNReal.ofReal C) ^ r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hrpos.le ENNReal.ofReal_ne_top
  have hG : ∫⁻ x, (ENNReal.ofReal C) ^ r * ‖f x‖ₑ ^ r ∂(hMeas c r) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ hK]
    exact ENNReal.mul_ne_top hK hfin
  have hlim' : Tendsto (fun k : ℕ => ∫⁻ x, ‖(g k x : ℂ) • f x‖ₑ ^ r ∂(hMeas c r))
      atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := hMeas c r)
      (f := fun _ => (0 : ℝ≥0∞)) (F := fun k x => ‖(g k x : ℂ) • f x‖ₑ ^ r)
      (fun x => (ENNReal.ofReal C) ^ r * ‖f x‖ₑ ^ r) hmeas ?_ hG ?_
    · simpa using this
    · intro k
      refine ae_of_all _ fun x => ?_
      have hle : ‖(g k x : ℂ) • f x‖ ≤ C * ‖f x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC k x) (norm_nonneg _)
      calc ‖(g k x : ℂ) • f x‖ₑ ^ r
          = (ENNReal.ofReal (‖(g k x : ℂ) • f x‖)) ^ r := by rw [ofReal_norm]
        _ ≤ (ENNReal.ofReal (C * ‖f x‖)) ^ r :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) hrpos.le
        _ = (ENNReal.ofReal C) ^ r * ‖f x‖ₑ ^ r := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.mul_rpow_of_nonneg _ _ hrpos.le, ofReal_norm]
    · refine ae_of_all _ fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim x] with k hk
      simp [hk, ENNReal.zero_rpow_of_pos hrpos]
  have hpow : Tendsto (fun k : ℕ => (∫⁻ x, ‖(g k x : ℂ) • f x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r))
      atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp hlim'
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at h
    exact h
  rw [show (fun k : ℕ => hNorm c r (fun x => (g k x : ℂ) • f x)) =
      fun k : ℕ => (∫⁻ x, ‖(g k x : ℂ) • f x‖ₑ ^ r ∂(hMeas c r)) ^ (1 / r) from funext hnorm]
  exact hpow

/-! ## The cut triple -/

lemma etaCut_data {c r ε M0 M1 : ℝ} (hc : 0 < c) (hr : 1 < r) (hM0' : 0 ≤ M0) (hM1' : 0 ≤ M1)
    (hM0 : ∀ t : ℝ, ‖deriv (fun s : ℝ => bump1 s) t‖ ≤ M0)
    (hM1 : ∀ t : ℝ, ‖t * deriv (fun s : ℝ => bump1 s) t‖ ≤ M1)
    {b Qb Eb : CProf} (hd : DivData c r ε b Qb Eb) (hsb : InHr c r (sqrtS b)) (k : ℕ) :
    DivData c r ε (fun x => (etaCut k x : ℂ) • b x)
      (fun x => (etaCut k x : ℂ) • Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • b x)
      (fun x => (etaCut k x : ℂ) • Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • b x) := by
  have hχc : Continuous (etaCut k) := (etaCut_smooth k).continuous
  have hχs : ContDiff ℝ ∞ (etaCut k) := etaCut_smooth k
  have hχb : ∃ C : ℝ, ∀ x : Coord, ‖etaCut k x‖ ≤ C := ⟨1, fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (etaCut_nonneg k x)]
    exact etaCut_le_one k x⟩
  have hper1 : ∀ x : Coord, etaCut k (qShift c x) = etaCut k x := fun x => by
    simp [etaCut, qShift]
  have hperQ : ∀ x : Coord, cutD (vQ ε) (etaCut k) (qShift c x) = cutD (vQ ε) (etaCut k) x :=
    fun x => by rw [cutD_vQ_eq, cutD_vQ_eq]; rfl
  have hperE : ∀ x : Coord, cutD vEta (etaCut k) (qShift c x) = cutD vEta (etaCut k) x :=
    fun x => by rw [cutD_vEta_eq, cutD_vEta_eq]; rfl
  have hwQ := hasWeakVec_cut hχs (vQ_cd ε) hχb (cutDQ_cont ε k) hc hr hd.inHr hd.weakQ
  have hwE := hasWeakVec_cut hχs vEta_cd hχb (cutDE_cont k) hc hr hd.inHr hd.weakE
  have inHrB : InHr c r (fun x => (etaCut k x : ℂ) • b x) :=
    inHr_mul hχc (etaCut_nonneg k) (etaCut_le_one k) hper1 hd.inHr
  have hQvec : sqrtS (fun x => (etaCut k x : ℂ) • Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • b x)
      = fun x => (etaCut k x : ℂ) • sqrtS Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • sqrtS b x :=
    funext fun x => sqrtS_cut_add _ _ Qb b x
  have hEvec : sqrtS (fun x => (etaCut k x : ℂ) • Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • b x)
      = fun x => (etaCut k x : ℂ) • sqrtS Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • sqrtS b x :=
    funext fun x => sqrtS_cut_add _ _ Eb b x
  refine ⟨inHrB, hwQ, hwE, ?_, ?_⟩
  · rw [hQvec]
    refine inHr_add hr ?_ ?_
    · exact inHr_mul hχc (etaCut_nonneg k) (etaCut_le_one k) hper1 hd.inQ
    · refine inHr_smul_bdd (cutDQ_cont ε k) (C := |ε| * M1) (mul_nonneg (abs_nonneg ε) hM1')
        (fun x => ?_) hperQ hsb
      rw [Real.norm_eq_abs]
      exact cutD_vQ_bdd ε M1 hM1 k x
  · rw [hEvec]
    refine inHr_add hr ?_ ?_
    · exact inHr_mul hχc (etaCut_nonneg k) (etaCut_le_one k) hper1 hd.inE
    · refine inHr_smul_bdd (cutDE_cont k) (C := M0) hM0' (fun x => ?_) hperE hsb
      rw [Real.norm_eq_abs]
      exact cutD_vEta_bdd M0 hM0 k x

lemma etaCut_window (ε : ℝ) (k : ℕ) {s0 s1 : ℝ} {b Qb Eb : CProf} (hcb : SCut s0 s1 b)
    (hcQ : SCut s0 s1 Qb) (hcE : SCut s0 s1 Eb) :
    SCut s0 s1 (fun x => (etaCut k x : ℂ) • b x) ∧
    SCut s0 s1 (fun x => (etaCut k x : ℂ) • Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • b x) ∧
    SCut s0 s1 (fun x => (etaCut k x : ℂ) • Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • b x) :=
  ⟨fun x hx => by simp [hcb x hx],
   fun x hx => by simp [hcQ x hx, hcb x hx],
   fun x hx => by simp [hcE x hx, hcb x hx]⟩

lemma etaCut_support (ε : ℝ) (k : ℕ) (b Qb Eb : CProf) :
    EtaCut (2 * ((k : ℝ) + 1)) (fun x => (etaCut k x : ℂ) • b x) ∧
    EtaCut (2 * ((k : ℝ) + 1))
      (fun x => (etaCut k x : ℂ) • Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • b x) ∧
    EtaCut (2 * ((k : ℝ) + 1))
      (fun x => (etaCut k x : ℂ) • Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • b x) :=
  ⟨fun x hx => by simp [etaCut_zero_of k x hx],
   fun x hx => by simp [etaCut_zero_of k x hx, cutD_vQ_eq, etaD_zero_of k x hx],
   fun x hx => by simp [etaCut_zero_of k x hx, cutD_vEta_eq, etaD_zero_of k x hx]⟩

end DivEtaCutHelp

open DivEtaCutHelp DriftEtaCutHelp DriftSCutHelp in
/-- **Target** `divEtaCutApprox_proof` (`PartII-b:T09/2/2`). -/
theorem divEtaCutApprox_proof : UnforcedLeray.Short.IIb.DivEtaCutApprox := by
  intro c r ε b Qb Eb hc hε hr hp δ hδ
  obtain ⟨hd, s0, s1, hs0, hcb, hcQ, hcE⟩ := hp
  have hr1 : 1 < r := by linarith
  obtain ⟨M0, hM0⟩ := bumpD_bdd
  obtain ⟨M1, hM1⟩ := bumpDM_bdd
  have hM0' : 0 ≤ M0 := by simpa using (norm_nonneg _).trans (hM0 0)
  have hM1' : 0 ≤ M1 := by simpa using (norm_nonneg _).trans (hM1 0)
  have hsb : InHr c r (sqrtS b) := ecSqrtInHr hcb hd.inHr
  have t1 := tendsto_etaCut_sub hr1 hd.inHr
  have t2 := tendsto_etaCut_sub hr1 hd.inQ
  have t3 := tendsto_etaCut_sub hr1 hd.inE
  have t4 := tendsto_hNorm_cut_zero hr1 hsb (g := fun k x => cutD (vQ ε) (etaCut k) x)
    (fun k => cutDQ_cont ε k) (C := |ε| * M1) (fun k x => cutD_vQ_bdd ε M1 hM1 k x)
    (fun x => cutD_vQ_ev ε x)
  have t5 := tendsto_hNorm_cut_zero hr1 hsb (g := fun k x => cutD vEta (etaCut k) x)
    (fun k => cutDE_cont k) (C := M0) (fun k x => cutD_vEta_bdd M0 hM0 k x)
    (fun x => cutD_vEta_ev x)
  have sumQ : Tendsto (fun k : ℕ =>
      hNorm c r (fun x => (etaCut k x : ℂ) • sqrtS Qb x - sqrtS Qb x) +
        hNorm c r (fun x => ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • sqrtS b x)) atTop (𝓝 0) := by
    have h := t2.add t4
    rwa [add_zero] at h
  have sumE : Tendsto (fun k : ℕ =>
      hNorm c r (fun x => (etaCut k x : ℂ) • sqrtS Eb x - sqrtS Eb x) +
        hNorm c r (fun x => ((cutD vEta (etaCut k) x : ℝ) : ℂ) • sqrtS b x)) atTop (𝓝 0) := by
    have h := t3.add t5
    rwa [add_zero] at h
  have ev : ∀ᶠ k : ℕ in atTop,
      hNorm c r (fun x => (etaCut k x : ℂ) • b x - b x) < ENNReal.ofReal δ ∧
      hNorm c r (fun x => (etaCut k x : ℂ) • sqrtS Qb x - sqrtS Qb x) +
        hNorm c r (fun x => ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • sqrtS b x) < ENNReal.ofReal δ ∧
      hNorm c r (fun x => (etaCut k x : ℂ) • sqrtS Eb x - sqrtS Eb x) +
        hNorm c r (fun x => ((cutD vEta (etaCut k) x : ℝ) : ℂ) • sqrtS b x) < ENNReal.ofReal δ := by
    filter_upwards [(tendsto_order.1 t1).2 _ (ENNReal.ofReal_pos.2 hδ),
      (tendsto_order.1 sumQ).2 _ (ENNReal.ofReal_pos.2 hδ),
      (tendsto_order.1 sumE).2 _ (ENNReal.ofReal_pos.2 hδ)] with k h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨k, hk1, hk2, hk3⟩ := ev.exists
  refine ⟨fun x => (etaCut k x : ℂ) • b x,
    fun x => (etaCut k x : ℂ) • Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • b x,
    fun x => (etaCut k x : ℂ) • Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • b x,
    ⟨⟨etaCut_data hc hr1 hM0' hM1' hM0 hM1 hd hsb k, s0, s1, hs0,
      (etaCut_window ε k hcb hcQ hcE).1, (etaCut_window ε k hcb hcQ hcE).2.1,
      (etaCut_window ε k hcb hcQ hcE).2.2⟩,
      2 * ((k : ℝ) + 1), etaCut_support ε k b Qb Eb⟩, ?_⟩
  refine ⟨hk1, ?_, ?_⟩
  · have eq2 : sqrtS (fun x => ((etaCut k x : ℂ) • Qb x + ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • b x)
        - Qb x) = fun x => ((etaCut k x : ℂ) • sqrtS Qb x - sqrtS Qb x) +
          ((cutD (vQ ε) (etaCut k) x : ℝ) : ℂ) • sqrtS b x :=
      funext fun x => sqrtS_cut_sub _ _ Qb b x
    rw [eq2]
    exact lt_of_le_of_lt (hNorm_add_le' hr1 (ecAesm_cut_sub (etaCut_smooth k).continuous hd.inQ)
      (ecAesm_cut (cutDQ_cont ε k) hsb)) hk2
  · have eq3 : sqrtS (fun x => ((etaCut k x : ℂ) • Eb x + ((cutD vEta (etaCut k) x : ℝ) : ℂ) • b x)
        - Eb x) = fun x => ((etaCut k x : ℂ) • sqrtS Eb x - sqrtS Eb x) +
          ((cutD vEta (etaCut k) x : ℝ) : ℂ) • sqrtS b x :=
      funext fun x => sqrtS_cut_sub _ _ Eb b x
    rw [eq3]
    exact lt_of_le_of_lt (hNorm_add_le' hr1 (ecAesm_cut_sub (etaCut_smooth k).continuous hd.inE)
      (ecAesm_cut (cutDE_cont k) hsb)) hk3

#print axioms UnforcedLeray.Short.IIb.divEtaCutApprox_proof

end UnforcedLeray.Short.IIb
