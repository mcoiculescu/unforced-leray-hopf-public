import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# The comoving chart and its norm bound (INF25 T25.5; blueprint B0447)

Tex lines 7633–7662 (`eq:free-stress-20`, `eq:free-stress-21`), unit B0447. For an
observation point `(τ₀, y₀)` and the unit strip `-1/2 < t < 1/2`, the manuscript sets

  `W(t, z) = w(τ₀ + t, e^{-t/2}(y₀ + √ν z))`,

notes `dz = ν^{-3/2} e^{3t/2} dy` and that a unit interval carries at most `(1 + P)` times the
period average of a nonnegative `P`-periodic function, and concludes

  `‖W‖_{L^q} + ‖W_t‖_{L^q} + ‖Δ_z W‖_{L^q} ≤ C_q ν^{-3/(2q)} ‖w‖_{D_(ν,q)}`.

In the Bochner model of decision D2, `w ∈ Y_q` is a class of maps `ℝ/Pℤ → L^q(ℝ³)`, so
`W(t, ·)` is the composition of the slice `w(τ₀ + t)` with the affine map
`z ↦ e^{-t/2}(y₀ + √ν z)` (`chartPullback`), and the strip norm is the iterated norm
`(∫_{-1/2}^{1/2} ∫_{ℝ³} |W(t, z)|^q dz dt)^{1/q}` (`stripNorm`), which is the `L^q` norm of
the strip whenever `W` is jointly measurable. Both are independent of the chosen
representatives, because the chart is a measure-class preserving bijection.

By (20), `W_t = (T₀w) ∘ chart` and `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart = e^{-t} (νΔw) ∘ chart`.
Those distributional identities are the separate targets `chart_timeDeriv`,
`chart_laplacian` of T25.5 and are not built here. This file proves the norm half
(`chart_norm_le`): for any `w, a, b ∈ Y_q`,

  `‖W‖ + ‖b ∘ chart‖ + ‖e^{-t} a ∘ chart‖ ≤ e^{1/2} (2 e^{3/4})^{1/q} ν^{-3/(2q)} (‖w‖ + ‖a‖ + ‖b‖)`,

uniformly in `(τ₀, y₀)`, for `0 < P ≤ 1`, `ν > 0`, `1 ≤ q < ∞`. Applied to a graph triple
`(w, νΔw, T₀w)` it is (21) with `C_q = e^{1/2}(2e^{3/4})^{1/q}`. The manuscript's
hypothesis `1 < q` is not needed for this bound.

Status: infrastructure only; B0447 also needs (20), which is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.PhaseSpace

/-- The comoving chart `(t, z) ↦ (τ₀ + t, e^{-t/2}(y₀ + √ν z))` of tex 7640. -/
def comovingChart (ν τ₀ : ℝ) (y₀ : Space) (t : ℝ) (z : Space) : ℝ × Space :=
  (τ₀ + t, Real.exp (-t / 2) • (y₀ + Real.sqrt ν • z))

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- The chart pullback `W(t, z) = f(τ₀ + t)(e^{-t/2}(y₀ + √ν z))` of `f ∈ Y_q`. -/
def chartPullback (f : Yq P q) (ν τ₀ : ℝ) (y₀ : Space) (t : ℝ) (z : Space) : CVec3 :=
  (f ((comovingChart ν τ₀ y₀ t z).1 : AddCircle P) : Space → CVec3) (comovingChart ν τ₀ y₀ t z).2

/-- The iterated `L^q` norm on the strip `(-1/2, 1/2) × ℝ³` (Lebesgue measure). -/
def stripNorm (q : ℝ≥0∞) (W : ℝ → Space → CVec3) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), ∫⁻ z, ‖W t z‖ₑ ^ q.toReal) ^ (1 / q.toReal)

/-! ### Change of variables in space -/

theorem map_smul_space {b : ℝ} (hb : b ≠ 0) :
    Measure.map (fun x : Space => b • x) volume = ENNReal.ofReal |(b ^ 3)⁻¹| • volume := by
  simpa [Space, finrank_euclideanSpace] using
    Measure.map_addHaar_smul (volume : Measure Space) hb

/-- `∫ G(b z + c) dz = |b|^{-3} ∫ G` on `ℝ³`. -/
theorem lintegral_comp_affine (G : Space → ℝ≥0∞) {b : ℝ} (hb : b ≠ 0) (c : Space) :
    ∫⁻ z, G (b • z + c) = ENNReal.ofReal |(b ^ 3)⁻¹| * ∫⁻ x, G x := by
  have h1 : ∫⁻ z, G (b • z + c) =
      ∫⁻ x, G (x + c) ∂(Measure.map (fun z : Space => b • z) volume) :=
    ((Homeomorph.smulOfNeZero b hb).measurableEmbedding.lintegral_map
      (fun x => G (x + c))).symm
  rw [h1, map_smul_space hb, lintegral_smul_measure, lintegral_add_right_eq_self, smul_eq_mul]

theorem chart_snd (ν τ₀ : ℝ) (y₀ : Space) (t : ℝ) (z : Space) :
    (comovingChart ν τ₀ y₀ t z).2 =
      (Real.exp (-t / 2) * Real.sqrt ν) • z + Real.exp (-t / 2) • y₀ := by
  simp [comovingChart, smul_add, smul_smul, add_comm]

/-- The Jacobian bound `|b|^{-3} ≤ e^{3/4} ν^{-3/2}` on the strip, `b = e^{-t/2}√ν`. -/
theorem jacobian_le {ν t : ℝ} (hν : 0 < ν) (ht : t < 1 / 2) :
    |((Real.exp (-t / 2) * Real.sqrt ν) ^ 3)⁻¹| ≤
      Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he : 0 < Real.exp (-t / 2) := Real.exp_pos _
  rw [abs_of_pos (by positivity), mul_pow, mul_inv]
  have h1 : (Real.exp (-t / 2) ^ 3)⁻¹ = Real.exp (3 * t / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have h2 : (Real.sqrt ν ^ 3)⁻¹ = ν ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hν.le, Real.rpow_neg hν.le]
    norm_num
  rw [h1, h2]
  have h3 : Real.exp (3 * t / 2) ≤ Real.exp (3 / 4) := Real.exp_le_exp.2 (by linarith)
  exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hν.le _)

/-! ### Unit intervals against the period average -/

/-- Each period interval carries the full circle integral. -/
theorem lintegral_Ioc_period (h : AddCircle P → ℝ≥0∞) (τ₀ b : ℝ) :
    ∫⁻ t in Ioc b (b + P), h ((τ₀ + t : ℝ) : AddCircle P) = ∫⁻ τ, h τ := by
  have h1 := AddCircle.lintegral_preimage (T := P) b (fun τ => h ((τ₀ : AddCircle P) + τ))
  rw [lintegral_add_left_eq_self (μ := (volume : Measure (AddCircle P)))
    h (τ₀ : AddCircle P)] at h1
  rw [← h1]
  rfl

theorem lintegral_Ioc_nat_period (h : AddCircle P → ℝ≥0∞) (τ₀ b : ℝ) (n : ℕ) :
    ∫⁻ t in Ioc b (b + n * P), h ((τ₀ + t : ℝ) : AddCircle P) = n * ∫⁻ τ, h τ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Ioc b (b + ((n + 1 : ℕ) : ℝ) * P) =
        Ioc b (b + n * P) ∪ Ioc (b + n * P) (b + n * P + P) := by
      rw [Ioc_union_Ioc_eq_Ioc]
      · congr 1
        push_cast
        ring
      · have : 0 ≤ (n : ℝ) * P := mul_nonneg (Nat.cast_nonneg n) hP.out.le
        linarith
      · linarith [hP.out]
    rw [hsplit, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), ih,
      lintegral_Ioc_period]
    push_cast
    ring

/-- A unit interval carries at most `(1 + P) ≤ 2` times the period average (tex 7652–7654). -/
theorem lintegral_unit_le (hP1 : P ≤ 1) (h : AddCircle P → ℝ≥0∞) (τ₀ : ℝ) :
    ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), h ((τ₀ + t : ℝ) : AddCircle P) ≤
      2 * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle := by
  have hP0 := hP.out
  set n : ℕ := ⌈1 / P⌉₊ with hn
  have hn1 : 1 ≤ (n : ℝ) * P := by
    have : 1 / P ≤ n := Nat.le_ceil _
    rw [div_le_iff₀ hP0] at this
    linarith
  have hn2 : (n : ℝ) * P ≤ 2 := by
    have : (n : ℝ) < 1 / P + 1 := Nat.ceil_lt_add_one (by positivity)
    have h' : (n : ℝ) * P < (1 / P + 1) * P := mul_lt_mul_of_pos_right this hP0
    rw [add_mul, one_div, inv_mul_cancel₀ hP0.ne'] at h'
    linarith
  have hsub : Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + n * P) := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  calc ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), h ((τ₀ + t : ℝ) : AddCircle P)
      ≤ ∫⁻ t in Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + n * P), h ((τ₀ + t : ℝ) : AddCircle P) :=
        lintegral_mono_set hsub
    _ = n * ∫⁻ τ, h τ := lintegral_Ioc_nat_period h τ₀ _ n
    _ = n * (ENNReal.ofReal P * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle) := by
        rw [AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal ((n : ℝ) * P) * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle := by
        rw [← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ ≤ 2 * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle := by
        gcongr
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact ENNReal.ofReal_le_ofReal hn2

/-! ### The strip estimate -/

theorem lintegral_enorm_rpow_Lp (g : Lp CVec3 q (volume : Measure Space)) (hq' : q ≠ ∞) :
    ∫⁻ x, ‖(g : Space → CVec3) x‖ₑ ^ q.toReal = ‖g‖ₑ ^ q.toReal := by
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (by have := hq.out; positivity) hq'
  rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by have := hq.out; positivity) hq',
    lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0]

theorem lintegral_enorm_rpow_Yq (f : Yq P q) (hq' : q ≠ ∞) :
    ∫⁻ τ, ‖(f : AddCircle P → Lp CVec3 q (volume : Measure Space)) τ‖ₑ ^ q.toReal
      ∂AddCircle.haarAddCircle = ‖f‖ₑ ^ q.toReal := by
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (by have := hq.out; positivity) hq'
  rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by have := hq.out; positivity) hq',
    lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0]

/-- The `q`-th power of the strip norm of `m(t) W(t, z)`, for a weight with `‖m t‖ ≤ K` on
the strip. -/
theorem strip_lintegral_le (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν) (hq' : q ≠ ∞) (f : Yq P q)
    (τ₀ : ℝ) (y₀ : Space) (m : ℝ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hm : ∀ t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), ‖m t‖ ≤ K) :
    ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), ∫⁻ z, ‖m t • chartPullback f ν τ₀ y₀ t z‖ₑ ^ q.toReal ≤
      ENNReal.ofReal (K ^ q.toReal * (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ)))) *
        ‖f‖ₑ ^ q.toReal := by
  set p := q.toReal with hpdef
  have hp0 : 0 < p := ENNReal.toReal_pos (by have := hq.out; positivity) hq'
  set J : ℝ := Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ)) with hJ
  have hJ0 : 0 ≤ J := by positivity
  have hinner : ∀ t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
      ∫⁻ z, ‖m t • chartPullback f ν τ₀ y₀ t z‖ₑ ^ p ≤
        ENNReal.ofReal (K ^ p * J) *
          ‖(f : AddCircle P → Lp CVec3 q (volume : Measure Space))
            ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ p := by
    intro t ht
    have hb : Real.exp (-t / 2) * Real.sqrt ν ≠ 0 :=
      mul_ne_zero (Real.exp_pos _).ne' (Real.sqrt_pos.2 hν).ne'
    set g := (f : AddCircle P → Lp CVec3 q (volume : Measure Space))
      ((τ₀ + t : ℝ) : AddCircle P) with hg
    have hW : ∀ z, chartPullback f ν τ₀ y₀ t z =
        (g : Space → CVec3) ((Real.exp (-t / 2) * Real.sqrt ν) • z + Real.exp (-t / 2) • y₀) := by
      intro z
      simp only [chartPullback, hg]
      rw [chart_snd]
      rfl
    simp_rw [hW, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le enorm_ne_top)]
    rw [lintegral_comp_affine (fun x => ‖(g : Space → CVec3) x‖ₑ ^ p) hb,
      lintegral_enorm_rpow_Lp g hq', ← mul_assoc]
    gcongr
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hm t ht) hp0.le)
    · exact jacobian_le hν ht.2
  calc ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), ∫⁻ z, ‖m t • chartPullback f ν τ₀ y₀ t z‖ₑ ^ p
      ≤ ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), ENNReal.ofReal (K ^ p * J) *
          ‖(f : AddCircle P → Lp CVec3 q (volume : Measure Space))
            ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ p :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall hinner))
    _ = ENNReal.ofReal (K ^ p * J) * ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2),
          ‖(f : AddCircle P → Lp CVec3 q (volume : Measure Space))
            ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K ^ p * J) * (2 * ‖f‖ₑ ^ p) := by
        gcongr
        rw [← lintegral_enorm_rpow_Yq f hq']
        exact lintegral_unit_le hP1
          (fun τ => ‖(f : AddCircle P → Lp CVec3 q (volume : Measure Space)) τ‖ₑ ^ p) τ₀
    _ = ENNReal.ofReal (K ^ p * (2 * J)) * ‖f‖ₑ ^ p := by
        rw [← mul_assoc]
        congr 1
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal (K ^ p * (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ)))) * ‖f‖ₑ ^ p := by
        rw [hJ, mul_assoc 2]

/-- The strip norm of a weighted chart pullback. -/
theorem stripNorm_le (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν) (hq' : q ≠ ∞) (f : Yq P q)
    (τ₀ : ℝ) (y₀ : Space) (m : ℝ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hm : ∀ t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), ‖m t‖ ≤ K) :
    stripNorm q (fun t z => m t • chartPullback f ν τ₀ y₀ t z) ≤
      ENNReal.ofReal (K * (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / q.toReal) *
        ‖f‖) := by
  set p := q.toReal with hpdef
  have hp0 : 0 < p := ENNReal.toReal_pos (by have := hq.out; positivity) hq'
  set A : ℝ := 2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  unfold stripNorm
  calc (∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), ∫⁻ z, ‖m t • chartPullback f ν τ₀ y₀ t z‖ₑ ^ p)
        ^ (1 / p)
      ≤ (ENNReal.ofReal (K ^ p * A) * ‖f‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (strip_lintegral_le hP1 hν hq' f τ₀ y₀ m hK hm) (by positivity)
    _ = ENNReal.ofReal (K * A ^ (1 / p) * ‖f‖) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          Real.mul_rpow (by positivity) hA0, ← Real.rpow_mul hK, mul_one_div_cancel hp0.ne',
          Real.rpow_one, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]

/-- The manuscript's form of the constant: `(2 e^{3/4} ν^{-3/2})^{1/q} = (2e^{3/4})^{1/q} ν^{-3/(2q)}`. -/
theorem chart_const_eq {ν : ℝ} (hν : 0 < ν) (p : ℝ) :
    (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / p) =
      (2 * Real.exp (3 / 4)) ^ (1 / p) * ν ^ (-(3 / (2 * p))) := by
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hν.le _), ← Real.rpow_mul hν.le]
  congr 2
  field_simp

/-- **B0447, (21), norm half.** For `w, a, b ∈ Y_q`, the chart pullbacks of `w`, of `b` (which
is `W_t` when `b = T₀w`) and of `e^{-t} a` (which is `Δ_z W` when `a = νΔw`) satisfy

  `‖W‖ + ‖b ∘ chart‖ + ‖e^{-t} a ∘ chart‖ ≤ C_q ν^{-3/(2q)} (‖w‖ + ‖a‖ + ‖b‖)`

on the strip `(-1/2, 1/2) × ℝ³`, with `C_q = e^{1/2} (2 e^{3/4})^{1/q}`, uniformly in the
observation point `(τ₀, y₀)`, for `0 < P ≤ 1`, `ν > 0` and `1 ≤ q < ∞` (tex 7633–7662). The
bound is in `ℝ≥0∞`, so it also shows that each strip norm is finite. -/
theorem chart_norm_le (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν) (hq' : q ≠ ∞) (w a b : Yq P q)
    (τ₀ : ℝ) (y₀ : Space) :
    stripNorm q (chartPullback w ν τ₀ y₀) + stripNorm q (chartPullback b ν τ₀ y₀) +
        stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback a ν τ₀ y₀ t z) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * (2 * Real.exp (3 / 4)) ^ (1 / q.toReal) *
        ν ^ (-(3 / (2 * q.toReal))) * (‖w‖ + ‖a‖ + ‖b‖)) := by
  set A : ℝ := (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / q.toReal) with hA
  have hA0 : 0 ≤ A := by positivity
  have hone : ∀ f : Yq P q, stripNorm q (chartPullback f ν τ₀ y₀) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * A * ‖f‖) := by
    intro f
    have h := stripNorm_le hP1 hν hq' f τ₀ y₀ (fun _ => (1 : ℂ)) zero_le_one
      (fun _ _ => by simp)
    simp only [one_smul, one_mul] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
    have : 0 ≤ A * ‖f‖ := by positivity
    nlinarith
  have hexp : stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback a ν τ₀ y₀ t z) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * A * ‖a‖) := by
    refine stripNorm_le hP1 hν hq' a τ₀ y₀ (fun t => (Real.exp (-t) : ℂ)) (Real.exp_pos _).le
      fun t ht => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [ht.1])
  calc stripNorm q (chartPullback w ν τ₀ y₀) + stripNorm q (chartPullback b ν τ₀ y₀) +
        stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback a ν τ₀ y₀ t z)
      ≤ ENNReal.ofReal (Real.exp (1 / 2) * A * ‖w‖) +
          ENNReal.ofReal (Real.exp (1 / 2) * A * ‖b‖) +
          ENNReal.ofReal (Real.exp (1 / 2) * A * ‖a‖) := by
        gcongr
        · exact hone w
        · exact hone b
    _ = ENNReal.ofReal (Real.exp (1 / 2) * A * (‖w‖ + ‖a‖ + ‖b‖)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal (Real.exp (1 / 2) * (2 * Real.exp (3 / 4)) ^ (1 / q.toReal) *
          ν ^ (-(3 / (2 * q.toReal))) * (‖w‖ + ‖a‖ + ‖b‖)) := by
        rw [hA, chart_const_eq hν, ← mul_assoc]

end UnforcedLeray.PhaseSpace
