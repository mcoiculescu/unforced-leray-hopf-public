import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:T02/3`: `VelocityDecayOfEnergy` (leaf of `ClassicalOdd`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the finite-energy
solution; "It is also the finite-energy solution"). The Prop `VelocityDecayOfEnergy` is defined in
`Short/PartI/Sub/T02_3.lean`: a classical solution with bounded derivatives has `v(s) → 0` as
`|η| → ∞` for every `s ∈ [0,T]`.

## Argument (fixed `s`, write `w = v s`)

* `w` is `C^∞`, `‖Dw‖ ≤ B` (so `w` is `B`-Lipschitz) and `‖w‖ ≤ M`.
* `G(η) = ∫_{-c/2}^{c/2} ‖w(q,η)‖² dq` is integrable on `ℝ`: Fubini on the cell, from `finite_energy`.
* (window) by `q`-periodicity with period `c ≥ 2r`: `∫_{q₀-r}^{q₀+r} ‖w(·,η)‖² ≤ G(η)`.
* (slice) on that window `‖w(q,η)‖ ≥ ‖w(q₀,η)‖ - Br`, so `2r(‖w(q₀,η)‖² - 2BrM) ≤ ∫_{q₀-r}^{q₀+r}`.
* (η-average) for `|η - η₀| ≤ r`: `2r‖w(q₀,η₀)‖² - 8Br²M ≤ G(η)`; integrating over `[η₀-r, η₀+r]`
  gives `4r²‖w(q₀,η₀)‖² - 16Br³M ≤ ∫_{η₀-r}^{η₀+r} G`.
* (tail) `∫_{η₀-r}^{η₀+r} G → 0` as `|η₀| → ∞`, since `G` is integrable.

Choosing `r` with `16BrM ≤ ε` and the tail below `r²ε` gives `‖w(q₀,η₀)‖² < ε` for `|η₀|` large.

All helpers are prefixed `vd`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- A slice `v s` of a classical solution, `s ∈ [0,T]`, is `C^∞` on the plane. -/
lemma vd_contDiff_slice {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcl : IsClassicalOn ν c T v p) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (v s) := by
  have h := hcl.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun z _ => (⟨hs, mem_univ z⟩ : (s, z) ∈ Icc 0 T ×ˢ univ))
  exact contDiffOn_univ.1 h

/-- The order-one bound of `HasBoundedDerivsOn` bounds `‖fderiv‖`. -/
lemma vd_fderiv_bound {T : ℝ} {v : ℝ → Plane → Vec} (hb : HasBoundedDerivsOn T v) :
    ∃ B : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, ‖fderiv ℝ (v s) z‖ ≤ B := by
  obtain ⟨B, hB⟩ := hb 1
  refine ⟨B, fun s hs z => ?_⟩
  have e : ‖iteratedFDeriv ℝ 0 (fderiv ℝ (v s)) z‖ = ‖iteratedFDeriv ℝ (0 + 1) (v s) z‖ :=
    norm_iteratedFDeriv_fderiv
  rw [norm_iteratedFDeriv_zero] at e
  rw [e]
  exact hB s hs z

/-- A `B`-bounded derivative makes the plane map `B`-Lipschitz (sup norm on `Plane`). -/
lemma vd_lip {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) {B : ℝ} (hB : ∀ z, ‖fderiv ℝ w z‖ ≤ B)
    (x y : Plane) : ‖w y - w x‖ ≤ B * ‖y - x‖ := by
  have hd : ∀ z ∈ (univ : Set Plane), DifferentiableAt ℝ w z := fun z _ =>
    (hw.differentiable (by simp)) z
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hd (fun z _ => hB z) convex_univ
    (mem_univ x) (mem_univ y)

/-- Sup-norm bound on the plane from coordinate bounds. -/
lemma vd_norm_le {x y : Plane} {r : ℝ} (h1 : |x.1 - y.1| ≤ r) (h2 : |x.2 - y.2| ≤ r) :
    ‖x - y‖ ≤ r := by
  rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  exact max_le (by rw [Real.norm_eq_abs]; exact h1) (by rw [Real.norm_eq_abs]; exact h2)

/-- Elementary square estimate, lower side. -/
lemma vd_sq_lb {x t a M : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hxM : x ≤ M) (ht : 0 ≤ t)
    (hxt : x - a ≤ t) : x ^ 2 - 2 * a * M ≤ t ^ 2 := by
  rcases le_total x a with h | h
  · have hM : 0 ≤ M := le_trans hx hxM
    nlinarith [mul_nonneg ha hM, mul_nonneg hx (sub_nonneg.2 hxM),
      mul_le_mul_of_nonneg_right h hM, sq_nonneg t]
  · have h0 : 0 ≤ x - a := by linarith
    nlinarith [mul_nonneg ha (sub_nonneg.2 hxM), sq_nonneg a,
      mul_nonneg (sub_nonneg.2 hxt) (add_nonneg h0 ht)]

/-- Elementary square estimate, upper side. -/
lemma vd_sq_ub {x t d M : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x) (ht : 0 ≤ t) (hxM : x ≤ M)
    (htM : t ≤ M) (hxt : x - t ≤ d) : x ^ 2 ≤ t ^ 2 + 2 * d * M := by
  have h1 : (x - t) * (x + t) ≤ d * (x + t) := mul_le_mul_of_nonneg_right hxt (by linarith)
  have h2 : d * (x + t) ≤ d * (2 * M) := mul_le_mul_of_nonneg_left (by linarith) hd
  nlinarith [h1, h2]

/-- The one-period integral of the squared slice: `G(η) = ∫_{-c/2}^{c/2} ‖w(q,η)‖² dq`. -/
def vdG (w : Plane → Vec) (c η : ℝ) : ℝ := ∫ q in (-c / 2)..(c / 2), ‖w (q, η)‖ ^ 2

/-- The tail set `{η | n ≤ |η|}`. -/
def vdTailSet (n : ℕ) : Set ℝ := {η : ℝ | (n : ℝ) ≤ |η|}

/-- Continuity of a slice in the `q`-variable. -/
lemma vd_cont_slice {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) (η : ℝ) :
    Continuous (fun q : ℝ => ‖w (q, η)‖ ^ 2) := by
  have h1 : Continuous (fun q : ℝ => ((q, η) : Plane)) := continuous_id.prodMk continuous_const
  exact ((hw.continuous.comp h1).norm).pow 2

/-- Periodic upper bound for a `q`-window of length `2r ≤ c`. -/
lemma vd_window_le {c r q₀ : ℝ} (hc : 1 ≤ c) (hr0 : 0 < r) (hr2 : r ≤ 1 / 2) {f : ℝ → ℝ}
    (hf : Function.Periodic f c) (hcont : Continuous f) (hnn : ∀ q, 0 ≤ f q) :
    ∫ q in (q₀ - r)..(q₀ + r), f q ≤ ∫ q in (-c / 2)..(c / 2), f q := by
  have hmono : ∫ q in (q₀ - r)..(q₀ + r), f q ≤ ∫ q in (q₀ - r)..(q₀ - r + c), f q :=
    intervalIntegral.integral_mono_interval (le_refl _) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun q => hnn q) (hcont.intervalIntegrable _ _)
  have hper := hf.intervalIntegral_add_eq (q₀ - r) (-c / 2)
  have hc2 : -c / 2 + c = c / 2 := by ring
  rw [hc2] at hper
  rw [hper] at hmono
  exact hmono

/-- Pointwise lower bound on a slice average over the `q`-window. -/
lemma vd_slice_lb {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) {B M : ℝ} (hB0 : 0 ≤ B)
    (hBw : ∀ z, ‖fderiv ℝ w z‖ ≤ B) (hMw : ∀ z, ‖w z‖ ≤ M) {r : ℝ} (hr0 : 0 < r)
    (q₀ η : ℝ) :
    2 * r * (‖w (q₀, η)‖ ^ 2 - 2 * (B * r) * M) ≤ ∫ q in (q₀ - r)..(q₀ + r), ‖w (q, η)‖ ^ 2 := by
  have hpt : ∀ q ∈ Icc (q₀ - r) (q₀ + r), ‖w (q₀, η)‖ ^ 2 - 2 * (B * r) * M ≤ ‖w (q, η)‖ ^ 2 := by
    intro q hq
    have hd : ‖((q, η) : Plane) - (q₀, η)‖ ≤ r :=
      vd_norm_le (by dsimp only; rw [abs_le]; constructor <;> linarith [hq.1, hq.2])
        (by dsimp only; rw [sub_self, abs_zero]; exact hr0.le)
    have hl := vd_lip hw hBw (q₀, η) (q, η)
    have hl2 : ‖w (q₀, η)‖ - ‖w (q, η)‖ ≤ ‖w (q, η) - w (q₀, η)‖ := by
      have := norm_sub_norm_le (w (q₀, η)) (w (q, η))
      rwa [norm_sub_rev] at this
    have hBr : B * ‖((q, η) : Plane) - (q₀, η)‖ ≤ B * r := mul_le_mul_of_nonneg_left hd hB0
    exact vd_sq_lb (mul_nonneg hB0 hr0.le) (norm_nonneg _) (hMw _) (norm_nonneg _)
      (by linarith)
  have hcont := vd_cont_slice hw η
  have hint : ∫ q in (q₀ - r)..(q₀ + r), (‖w (q₀, η)‖ ^ 2 - 2 * (B * r) * M) ≤
      ∫ q in (q₀ - r)..(q₀ + r), ‖w (q, η)‖ ^ 2 :=
    intervalIntegral.integral_mono_on (show q₀ - r ≤ q₀ + r by linarith) intervalIntegrable_const
      (hcont.intervalIntegrable _ _) (fun q hq => hpt q hq)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have e : q₀ + r - (q₀ - r) = 2 * r := by ring
  rw [e] at hint
  exact hint

/-- Pointwise bound of the averaged slice energy at `(q₀,η₀)` against `G(η)`, `|η - η₀| ≤ r`. -/
lemma vd_pt {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) {c B M : ℝ} (hc : 1 ≤ c) (hB0 : 0 ≤ B)
    (hBw : ∀ z, ‖fderiv ℝ w z‖ ≤ B) (hMw : ∀ z, ‖w z‖ ≤ M) (hper : Cyl.IsPeriodic c w)
    {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 1 / 2) (q₀ η₀ η : ℝ)
    (hη : η ∈ Icc (η₀ - r) (η₀ + r)) :
    2 * r * ‖w (q₀, η₀)‖ ^ 2 - 8 * B * r ^ 2 * M ≤ vdG w c η := by
  have hsl := vd_slice_lb hw hB0 hBw hMw hr0 q₀ η
  have hper' : Function.Periodic (fun q : ℝ => ‖w (q, η)‖ ^ 2) c := by
    intro q
    have h : w (q + c, η) = w (q, η) := hper (q, η)
    simp only [h]
  have hwin : ∫ q in (q₀ - r)..(q₀ + r), ‖w (q, η)‖ ^ 2 ≤ vdG w c η :=
    vd_window_le hc hr0 hr2 hper' (vd_cont_slice hw η) (fun q => sq_nonneg _)
  have hd1 : ‖((q₀, η₀) : Plane) - (q₀, η)‖ ≤ r :=
    vd_norm_le (by dsimp only; rw [sub_self, abs_zero]; exact hr0.le)
      (by dsimp only; rw [abs_le]; constructor <;> linarith [hη.1, hη.2])
  have hl := vd_lip hw hBw (q₀, η) (q₀, η₀)
  have hl2 : ‖w (q₀, η₀)‖ - ‖w (q₀, η)‖ ≤ ‖w (q₀, η₀) - w (q₀, η)‖ :=
    norm_sub_norm_le _ _
  have hBr : B * ‖((q₀, η₀) : Plane) - (q₀, η)‖ ≤ B * r := mul_le_mul_of_nonneg_left hd1 hB0
  have hx2 : ‖w (q₀, η₀)‖ ^ 2 ≤ ‖w (q₀, η)‖ ^ 2 + 2 * (B * r) * M :=
    vd_sq_ub (mul_nonneg hB0 hr0.le) (norm_nonneg _) (norm_nonneg _) (hMw _) (hMw _)
      (by linarith)
  have h3 := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 2 * r)
  nlinarith [h3, hsl, hwin]

/-- Averaging over `η ∈ [η₀ - r, η₀ + r]`. -/
lemma vd_avg {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) {c B M : ℝ} (hc : 1 ≤ c) (hB0 : 0 ≤ B)
    (hBw : ∀ z, ‖fderiv ℝ w z‖ ≤ B) (hMw : ∀ z, ‖w z‖ ≤ M) (hper : Cyl.IsPeriodic c w)
    (hG : Integrable (vdG w c)) {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 1 / 2) (q₀ η₀ : ℝ) :
    2 * r * (2 * r * ‖w (q₀, η₀)‖ ^ 2 - 8 * B * r ^ 2 * M) ≤
      ∫ η in (η₀ - r)..(η₀ + r), vdG w c η := by
  have hint : ∫ η in (η₀ - r)..(η₀ + r), (2 * r * ‖w (q₀, η₀)‖ ^ 2 - 8 * B * r ^ 2 * M) ≤
      ∫ η in (η₀ - r)..(η₀ + r), vdG w c η :=
    intervalIntegral.integral_mono_on (show η₀ - r ≤ η₀ + r by linarith) intervalIntegrable_const
      hG.intervalIntegrable (fun η hη => vd_pt hw hc hB0 hBw hMw hper hr0 hr2 q₀ η₀ η hη)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have e : η₀ + r - (η₀ - r) = 2 * r := by ring
  rw [e] at hint
  exact hint

/-- The one-period integral `G` is integrable on `ℝ` (Fubini on the cell). -/
lemma vd_G_integrable {w : Plane → Vec} {c : ℝ} (hc : 1 ≤ c)
    (hfin : IntegrableOn (fun z => ‖w z‖ ^ 2) (Cyl.cell c)) : Integrable (vdG w c) := by
  have e : ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))).prod
      ((volume : Measure ℝ).restrict (univ : Set ℝ)) =
      (volume : Measure Plane).restrict (Cyl.cell c) := by
    rw [Measure.prod_restrict]
    rfl
  have h2 : Integrable (fun z : Plane => ‖w z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))).prod
        ((volume : Measure ℝ).restrict (univ : Set ℝ))) := by
    rw [e]
    exact hfin
  have h3 := h2.integral_prod_right
  rw [Measure.restrict_univ] at h3
  have hconv : vdG w c = fun η => ∫ q in Ico (-c / 2) (c / 2), ‖w (q, η)‖ ^ 2 := by
    funext η
    unfold vdG
    rw [intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith),
      integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  rw [hconv]
  exact h3

/-- Tail of an integrable nonnegative function over windows of fixed length. -/
lemma vd_tail {G : ℝ → ℝ} (hG : Integrable G) (hnn : ∀ η, 0 ≤ G η) {r : ℝ} (hr : 0 < r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ η₀ : ℝ, R ≤ |η₀| → ∫ η in (η₀ - r)..(η₀ + r), G η < δ := by
  have hsm : ∀ n : ℕ, MeasurableSet (vdTailSet n) := fun n =>
    measurableSet_le measurable_const continuous_abs.measurable
  have hanti : Antitone vdTailSet := by
    intro a b hab η hη
    have hη' : (b : ℝ) ≤ |η| := hη
    show (a : ℝ) ≤ |η|
    exact le_trans (Nat.cast_le.2 hab) hη'
  have hempty : (⋂ n : ℕ, vdTailSet n) = ∅ := by
    ext η
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall, vdTailSet, mem_setOf_eq]
    obtain ⟨n, hn⟩ := exists_nat_gt |η|
    exact ⟨n, not_le.2 hn⟩
  have htend := tendsto_setIntegral_of_antitone hsm hanti ⟨0, hG.integrableOn⟩
  simp only [hempty, Measure.restrict_empty, integral_zero_measure] at htend
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually (gt_mem_nhds hδ))
  refine ⟨(N : ℝ) + r, fun η₀ hη₀ => ?_⟩
  rw [intervalIntegral.integral_of_le (show η₀ - r ≤ η₀ + r by linarith)]
  have hsub : Ioc (η₀ - r) (η₀ + r) ⊆ vdTailSet N := by
    intro η hη
    have h1 : |η₀ - η| ≤ r := abs_le.2 ⟨by linarith [hη.2], by linarith [hη.1]⟩
    have h2 := abs_sub_abs_le_abs_sub η₀ η
    show (N : ℝ) ≤ |η|
    linarith
  calc ∫ η in Ioc (η₀ - r) (η₀ + r), G η ≤ ∫ η in vdTailSet N, G η :=
        setIntegral_mono_set hG.integrableOn (Filter.Eventually.of_forall hnn) hsub.eventuallyLE
    _ < δ := hN N le_rfl

/-- Choice of the window radius `r`. -/
lemma vd_choose_r {B M ε : ℝ} (hB0 : 0 ≤ B) (hM0 : 0 ≤ M) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 16 * B * r * M ≤ ε := by
  have hpos : 0 < 16 * (B * M + 1) := by nlinarith [mul_nonneg hB0 hM0]
  have hr0 : 0 < min (1 / 2 : ℝ) (ε / (16 * (B * M + 1))) :=
    lt_min (by norm_num) (div_pos hε hpos)
  have h1 : min (1 / 2 : ℝ) (ε / (16 * (B * M + 1))) ≤ ε / (16 * (B * M + 1)) :=
    min_le_right _ _
  have h2 : min (1 / 2 : ℝ) (ε / (16 * (B * M + 1))) * (16 * (B * M + 1)) ≤ ε :=
    (le_div_iff₀ hpos).1 h1
  refine ⟨min (1 / 2 : ℝ) (ε / (16 * (B * M + 1))), hr0, min_le_left _ _, ?_⟩
  nlinarith [h2, hr0, mul_nonneg hB0 hM0]

/-- Uniform smallness of the slice energy at large `|η|`, for fixed `s`. -/
lemma vd_key {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) {c B M : ℝ} (hc : 1 ≤ c) (hB0 : 0 ≤ B)
    (hBw : ∀ z, ‖fderiv ℝ w z‖ ≤ B) (hMw : ∀ z, ‖w z‖ ≤ M) (hper : Cyl.IsPeriodic c w)
    (hfin : IntegrableOn (fun z => ‖w z‖ ^ 2) (Cyl.cell c)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : Plane, R ≤ |z.2| → ‖w z‖ ^ 2 < ε := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMw 0)
  have hG : Integrable (vdG w c) := vd_G_integrable hc hfin
  have hGnn : ∀ η, 0 ≤ vdG w c η := fun η =>
    intervalIntegral.integral_nonneg (show -c / 2 ≤ c / 2 by linarith) (fun q _ => sq_nonneg _)
  obtain ⟨r, hr0, hr2, hrε⟩ := vd_choose_r hB0 hM0 hε
  obtain ⟨R, hR⟩ := vd_tail hG hGnn hr0 (mul_pos (pow_pos hr0 2) hε)
  refine ⟨R, ?_⟩
  rintro ⟨q₀, η₀⟩ hz
  have hav := vd_avg hw hc hB0 hBw hMw hper hG hr0 hr2 q₀ η₀
  have hI : ∫ η in (η₀ - r)..(η₀ + r), vdG w c η < r ^ 2 * ε := hR η₀ hz
  have h3 : r ^ 2 * (16 * B * r * M) ≤ r ^ 2 * ε := mul_le_mul_of_nonneg_left hrε (sq_nonneg r)
  have h4 : 4 * r ^ 2 * ‖w (q₀, η₀)‖ ^ 2 < 2 * r ^ 2 * ε := by nlinarith [hav, hI, h3]
  by_contra hcon
  push_neg at hcon
  have h5 := mul_le_mul_of_nonneg_left hcon (sq_nonneg r)
  nlinarith [mul_pos (pow_pos hr0 2) hε, h4, h5]

/-- **Velocity decay from finite energy** (source lines 276-288): for a classical solution with
bounded derivatives, `v(s) → 0` as `|η| → ∞`, for every `s ∈ [0,T]`. -/
theorem velocityDecayOfEnergy : VelocityDecayOfEnergy := by
  intro ν c T v p hν hc hT hcl hb s hs
  have hc1 : (1 : ℝ) ≤ c := hc
  obtain ⟨B, hB⟩ := vd_fderiv_bound hb
  obtain ⟨M, hM⟩ := exists_sup_bound_of_hasBoundedDerivsOn hb
  have hw : ContDiff ℝ ∞ (v s) := vd_contDiff_slice hcl hs
  have hB0 : (0 : ℝ) ≤ max B 0 := le_max_right _ _
  have hBw : ∀ z, ‖fderiv ℝ (v s) z‖ ≤ max B 0 := fun z => (hB s hs z).trans (le_max_left _ _)
  have hMw : ∀ z, ‖v s z‖ ≤ max M 0 := fun z => (hM s hs z).trans (le_max_left _ _)
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : Plane, R ≤ |z.2| → ‖v s z‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := vd_key hw hc1 hB0 hBw hMw (hcl.periodic_v s hs)
      (hcl.finite_energy s hs) (pow_pos hε 2)
    refine ⟨R, fun z hz => ?_⟩
    have h := hR z hz
    nlinarith [norm_nonneg (v s z)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := hkey ε hε
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨R, fun b hb' a ha => ?_⟩
  have ha' : |a.2| = b := ha
  rw [dist_zero_right]
  exact hR a (by rw [ha']; exact hb')

end UnforcedLeray.Short.PartI
