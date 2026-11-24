import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Units.B0424.Chart

/-!


Proves `WindowNorms` of `Short/PartII-a/Sub/F03.lean`. For `1 < r < ∞` and a window cutoff `χ`
there is `K` such that the transformed field `u_c` and force `F_c` lie in `L^r(ℝ × ℝ³)` and
`‖F_c‖_r^r ≤ K^r ∫_{τ₀-2}^{τ₀+2} (‖f‖_r^r + (1+|μ|)^r ‖w‖_r^r)`.
Source of record: `the November 2 reference manuscript`, lines 1431-1441.

Route, with all lower integrals in `ℝ≥0∞`:
* `∫⁻ ‖g‖^r = ∫⁻ e^t ‖g(e^t, x)‖^r` for a field vanishing on `θ ≤ 0` (`lintegral_expChart'`);
* on `|t| < 2` (the cutoff support) the transformed field and force are bounded pointwise by
  `e^{at}` times the representative norms, with `|χ|, |χ'| ≤ M`;
* the spatial dilation (`lintegral_dilChart'`) turns `dx` into `e^{3t/2} dy`, and the slice
  representatives (`lintegral_rep`) turn `∫ dy |W(τ₀+t, y)|^r` into `‖w(τ₀+t)‖_r^r`;
* the window `|t| < 2` becomes `τ ∈ (τ₀-2, τ₀+2)` by translation invariance.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.B0424

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-! ### Exponentials, norms, cutoff -/

theorem wn_exp_le (c t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Real.exp (c * t) ≤ Real.exp (2 * |c|) := by
  apply Real.exp_le_exp.2
  have h1 : c * t ≤ |c * t| := le_abs_self _
  rw [abs_mul] at h1
  have h2 : |t| ≤ 2 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
  have h3 : |c| * |t| ≤ |c| * 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
  linarith

theorem wn_ofReal_exp_mul (a b c : ℝ) (h : a + b = c) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) = ENNReal.ofReal (Real.exp c) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos a).le, ← Real.exp_add, h]

theorem wn_ofReal_exp_rpow (a q : ℝ) (hq : 0 ≤ q) :
    ENNReal.ofReal (Real.exp a) ^ q = ENNReal.ofReal (Real.exp (a * q)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos a).le hq, Real.exp_mul]

theorem wn_weight_exp (e : ℝ) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    ENNReal.ofReal (Real.exp (3 * t / 2)) * ENNReal.ofReal (Real.exp (e * t)) ≤
      ENNReal.ofReal (Real.exp (2 * |3 / 2 + e|)) := by
  rw [wn_ofReal_exp_mul (3 * t / 2) (e * t) ((3 / 2 + e) * t) (by ring)]
  exact ENNReal.ofReal_le_ofReal (wn_exp_le _ t ht)

theorem wn_enorm_real (a : ℝ) : ‖(a : ℂ)‖ₑ = ENNReal.ofReal |a| := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

theorem wn_enorm_real_le (a M : ℝ) (h : ‖a‖ ≤ M) : ‖(a : ℂ)‖ₑ ≤ ENNReal.ofReal M := by
  rw [wn_enorm_real]
  exact ENNReal.ofReal_le_ofReal (by rwa [Real.norm_eq_abs] at h)

theorem wn_comp_norm_le (a b M : ℝ) (μ : ℂ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖(a : ℂ) - μ * (b : ℂ)‖ₑ ≤ ENNReal.ofReal (M * (1 + ‖μ‖)) := by
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have ha' : ‖(a : ℂ)‖ ≤ M := by rwa [Complex.norm_real]
  have hb' : ‖(b : ℂ)‖ ≤ M := by rwa [Complex.norm_real]
  calc ‖(a : ℂ) - μ * (b : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖μ‖ * ‖(b : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ M + ‖μ‖ * M := by gcongr
    _ = M * (1 + ‖μ‖) := by ring

theorem wn_cutoff_bound {χ : ℝ → ℝ} (hχ : WindowCutoff χ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ t, ‖χ t‖ ≤ M) ∧ (∀ t, ‖deriv χ t‖ ≤ M) := by
  obtain ⟨A, hA⟩ := hχ.smooth.continuous.bounded_above_of_compact_support hχ.compact
  obtain ⟨B, hB⟩ := (hχ.smooth.continuous_deriv (by simp)).bounded_above_of_compact_support
    hχ.compact.deriv
  exact ⟨max A B, le_max_of_le_left ((norm_nonneg _).trans (hA 0)),
    fun t => (hA t).trans (le_max_left _ _), fun t => (hB t).trans (le_max_right _ _)⟩

theorem wn_cutoff_zero {χ : ℝ → ℝ} (hχ : WindowCutoff χ) {t : ℝ}
    (ht : t ∉ Ioo (-2 : ℝ) 2) : χ t = 0 ∧ deriv χ t = 0 := by
  have h : t ∉ tsupport χ := fun h' => ht (hχ.support h')
  exact ⟨image_eq_zero_of_notMem_tsupport h, deriv_of_notMem_tsupport h⟩

/-! ### The transformed field and force at `(e^t, x)` -/

theorem wn_windowField_expChart (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3)
    (p : ℝ × Space) :
    windowField χ τ₀ W c (expChart p) =
      ((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ) *
        W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c := by
  simp only [windowField, expChart, Real.log_exp, if_pos (Real.exp_pos p.1)]

theorem wn_windowForce_expChart (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3)
    (c : Fin 3) (p : ℝ × Space) :
    windowForce μ χ τ₀ W Fr c (expChart p) =
      ((Real.exp (-(3 * p.1 / 2)) : ℝ) : ℂ) *
        ((((deriv χ p.1 : ℝ) : ℂ) - μ * ((χ p.1 : ℝ) : ℂ)) *
            W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c +
          ((χ p.1 : ℝ) : ℂ) * Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c) := by
  simp only [windowForce, expChart, Real.log_exp, if_pos (Real.exp_pos p.1)]

/-- Pointwise bound for the transformed force, on `ℝ≥0∞`. -/
theorem wn_force_pointwise {χ : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hMχ : ∀ t, ‖χ t‖ ≤ M)
    (hMd : ∀ t, ‖deriv χ t‖ ≤ M) (hχ : WindowCutoff χ) {q : ℝ} (hq : 0 < q) {C : ℝ≥0∞}
    (hC : ∀ x y : ℝ≥0∞, (x + y) ^ q ≤ C * (x ^ q + y ^ q)) (μ : ℂ) (τ₀ : ℝ)
    (W Fr : ℝ × Space → CVec3) (c : Fin 3) (p : ℝ × Space) :
    ENNReal.ofReal (Real.exp p.1) * ‖windowForce μ χ τ₀ W Fr c (expChart p)‖ₑ ^ q ≤
      (Ioo (-2 : ℝ) 2).indicator
          (fun t => ENNReal.ofReal (Real.exp ((1 - 3 * q / 2) * t)) * C) p.1 *
        (ENNReal.ofReal (M * (1 + ‖μ‖)) ^ q * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q +
          ENNReal.ofReal M ^ q * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q) := by
  by_cases ht : p.1 ∈ Ioo (-2 : ℝ) 2
  · rw [Set.indicator_of_mem ht, wn_windowForce_expChart, enorm_mul, wn_enorm_real,
      abs_of_pos (Real.exp_pos _), ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    have hZ : ‖(((deriv χ p.1 : ℝ) : ℂ) - μ * ((χ p.1 : ℝ) : ℂ)) *
          W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c +
        ((χ p.1 : ℝ) : ℂ) * Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c‖ₑ ≤
        ENNReal.ofReal (M * (1 + ‖μ‖)) * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ +
          ENNReal.ofReal M * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ := by
      refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [enorm_mul]
        exact mul_le_mul' (wn_comp_norm_le _ _ M μ (hMd p.1) (hMχ p.1))
          (PiLp.enorm_apply_le _ _)
      · rw [enorm_mul]
        exact mul_le_mul' (wn_enorm_real_le _ M (hMχ p.1)) (PiLp.enorm_apply_le _ _)
    have hZpow := (ENNReal.rpow_le_rpow hZ hq.le).trans (hC _ _)
    calc _ ≤ ENNReal.ofReal (Real.exp p.1) * (ENNReal.ofReal (Real.exp (-(3 * p.1 / 2))) ^ q *
            (C * ((ENNReal.ofReal (M * (1 + ‖μ‖)) * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ) ^ q +
              (ENNReal.ofReal M * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ) ^ q))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hZpow)
      _ = (ENNReal.ofReal (Real.exp ((1 - 3 * q / 2) * p.1)) * C) *
          (ENNReal.ofReal (M * (1 + ‖μ‖)) ^ q * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q +
            ENNReal.ofReal M ^ q * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
            wn_ofReal_exp_rpow _ _ hq.le,
            ← wn_ofReal_exp_mul p.1 (-(3 * p.1 / 2) * q) ((1 - 3 * q / 2) * p.1) (by ring)]
          ring
  · obtain ⟨h0, hd0⟩ := wn_cutoff_zero hχ ht
    rw [Set.indicator_of_notMem ht, wn_windowForce_expChart, h0, hd0]
    simp [ENNReal.zero_rpow_of_pos hq]

/-- Pointwise bound for the transformed field, on `ℝ≥0∞`. -/
theorem wn_field_pointwise {χ : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hMχ : ∀ t, ‖χ t‖ ≤ M)
    (hχ : WindowCutoff χ) {q : ℝ} (hq : 0 < q) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3)
    (p : ℝ × Space) :
    ENNReal.ofReal (Real.exp p.1) * ‖windowField χ τ₀ W c (expChart p)‖ₑ ^ q ≤
      (Ioo (-2 : ℝ) 2).indicator (fun t => ENNReal.ofReal (Real.exp ((1 - q / 2) * t))) p.1 *
        (ENNReal.ofReal M ^ q * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q) := by
  by_cases ht : p.1 ∈ Ioo (-2 : ℝ) 2
  · rw [Set.indicator_of_mem ht, wn_windowField_expChart]
    have hχM : |χ p.1| ≤ M := by
      have := hMχ p.1
      rwa [Real.norm_eq_abs] at this
    have hu : ‖((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ) *
        W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c‖ₑ ≤
        ENNReal.ofReal (M * Real.exp (-(p.1 / 2))) *
          ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ := by
      rw [enorm_mul, wn_enorm_real, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hχM (Real.exp_pos _).le)) (PiLp.enorm_apply_le _ _)
    have h2nn : (0 : ℝ) ≤ 2 := by norm_num
    calc _ ≤ ENNReal.ofReal (Real.exp p.1) *
            (ENNReal.ofReal (M * Real.exp (-(p.1 / 2))) *
              ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ) ^ q :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hu hq.le)
      _ = ENNReal.ofReal (Real.exp p.1) * (ENNReal.ofReal M ^ q *
            ENNReal.ofReal (Real.exp (-(p.1 / 2))) ^ q *
            ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.ofReal_mul hM0,
            ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      _ = ENNReal.ofReal (Real.exp ((1 - q / 2) * p.1)) *
            (ENNReal.ofReal M ^ q * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q) := by
          rw [wn_ofReal_exp_rpow _ _ hq.le,
            ← wn_ofReal_exp_mul p.1 (-(p.1 / 2) * q) ((1 - q / 2) * p.1) (by ring)]
          ring
  · obtain ⟨h0, -⟩ := wn_cutoff_zero hχ ht
    rw [Set.indicator_of_notMem ht, wn_windowField_expChart, h0]
    simp [ENNReal.zero_rpow_of_pos hq]

/-! ### Lebesgue integrals -/

theorem wn_eLpNorm_rpow {f : PS 3 → ℂ} {s : ℝ} (hs : 0 < s) :
    eLpNorm f (ENNReal.ofReal s) volume ^ s = ∫⁻ p, ‖f p‖ₑ ^ s := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hs.le, one_div, ENNReal.rpow_inv_rpow hs.ne']

theorem wn_memLp {f : PS 3 → ℂ} {s : ℝ} (hs : 0 < s) (hm : AEStronglyMeasurable f volume)
    (hI : ∫⁻ p, ‖f p‖ₑ ^ s < ⊤) : MemLp f (ENNReal.ofReal s) volume := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hs.le]
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hs.le) hI.ne

theorem wn_lintegral_expChart {f : PS 3 → ℂ} {s : ℝ} (hs : 0 < s)
    (hf0 : ∀ p : ℝ × Space, p.1 ≤ 0 → f p = 0) :
    ∫⁻ p, ‖f p‖ₑ ^ s = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) * ‖f (expChart p)‖ₑ ^ s := by
  have hsupp : (fun p => ‖f p‖ₑ ^ s).support ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_contra h
    apply hp
    have hp1 : p.1 ≤ 0 := by
      simp only [mem_prod, mem_Ioi, mem_univ, and_true, not_lt] at h
      exact h
    simp [hf0 p hp1, ENNReal.zero_rpow_of_pos hs]
  calc ∫⁻ p, ‖f p‖ₑ ^ s = ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set Space), ‖f p‖ₑ ^ s :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) * ‖f (expChart p)‖ₑ ^ s :=
        lintegral_expChart' (fun p => ‖f p‖ₑ ^ s)

theorem wn_weight_le {g X : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hg : ∀ t ∈ Ioo (-2 : ℝ) 2, g t ≤ c) (hg0 : ∀ t ∉ Ioo (-2 : ℝ) 2, g t = 0) :
    ∫⁻ t, g t * X t ≤ c * ∫⁻ t, (Ioo (-2 : ℝ) 2).indicator X t := by
  rw [← lintegral_const_mul' c _ hc]
  refine lintegral_mono fun t => ?_
  by_cases ht : t ∈ Ioo (-2 : ℝ) 2
  · rw [Set.indicator_of_mem ht]
    exact mul_le_mul' (hg t ht) le_rfl
  · rw [Set.indicator_of_notMem ht, hg0 t ht]
    simp

theorem wn_weight_ind {φ : ℝ → ℝ≥0∞} {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (hφ : ∀ t ∈ Ioo (-2 : ℝ) 2, ENNReal.ofReal (Real.exp (3 * t / 2)) * φ t ≤ D)
    (X : ℝ → ℝ≥0∞) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * (Ioo (-2 : ℝ) 2).indicator φ t * X t ≤
      D * ∫⁻ t, (Ioo (-2 : ℝ) 2).indicator X t := by
  refine (wn_weight_le (g := fun t => ENNReal.ofReal (Real.exp (3 * t / 2)) *
    (Ioo (-2 : ℝ) 2).indicator φ t) (c := D) hD ?_ ?_ (X := X)).trans le_rfl
  · intro t ht
    simp only [Set.indicator_of_mem ht]
    exact hφ t ht
  · intro t ht
    simp only [Set.indicator_of_notMem ht, mul_zero]

theorem wn_window_transfer (w : Yq P r) (τ₀ : ℝ) :
    ∫⁻ t, (Ioo (-2 : ℝ) 2).indicator (fun t => ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) t =
      ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal := by
  have h1 : ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal =
      ∫⁻ τ, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (fun τ => ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) τ :=
    (lintegral_indicator measurableSet_Ioo _).symm
  rw [h1]
  calc ∫⁻ t, (Ioo (-2 : ℝ) 2).indicator (fun t => ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) t
      = ∫⁻ t, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator
          (fun τ => ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) (τ₀ + t) := by
        refine lintegral_congr fun t => ?_
        by_cases ht : t ∈ Ioo (-2 : ℝ) 2
        · have ht' : τ₀ + t ∈ Ioo (τ₀ - 2) (τ₀ + 2) :=
            ⟨by linarith [ht.1], by linarith [ht.2]⟩
          rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
        · have ht' : τ₀ + t ∉ Ioo (τ₀ - 2) (τ₀ + 2) := fun h =>
            ht ⟨by linarith [h.1], by linarith [h.2]⟩
          rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
    _ = ∫⁻ τ, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator
          (fun τ => ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) τ :=
        lintegral_add_left_eq_self _ τ₀

theorem wn_window_lt_top (hrt : r ≠ ⊤) (w : Yq P r) (τ₀ : ℝ) :
    ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal < ⊤ := by
  rw [← wn_window_transfer w τ₀, lintegral_indicator measurableSet_Ioo]
  exact (lintegral_mono_set Ioo_subset_Icc_self).trans_lt
    (lintegral_window_lt_top hrt w τ₀ (-2) 2)

/-- The dilation and slice identity: `∫ m(t) |W(τ₀+t, e^{-t/2}x)|^r dt dx`. -/
theorem wn_pullback_rep (hrt : r ≠ ⊤) {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W)
    (τ₀ : ℝ) {m : ℝ → ℝ≥0∞} (hm : Measurable m) :
    ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal =
      ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
        ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
  have hm' : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (3 * t / 2)) * m t := by
    fun_prop
  calc ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal
      = ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp (3 * p.1 / 2)) * m p.1 *
          ‖W (τ₀ + p.1, p.2)‖ₑ ^ r.toReal := by
        conv_lhs => rw [lintegral_dilChart']
        refine lintegral_congr fun p => ?_
        simp only [dilChart, rhoD, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          one_smul]
        ring
    _ = ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
          ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal :=
        lintegral_rep hrt hW τ₀ hm'

/-- The pulled-back integral with a constant factor `A`. -/
theorem wn_pullback_mul (hrt : r ≠ ⊤) {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W)
    (τ₀ : ℝ) {m : ℝ → ℝ≥0∞} (hm : Measurable m) {A : ℝ≥0∞} (hA : A ≠ ⊤) :
    ∫⁻ p : ℝ × Space, m p.1 * (A * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal) =
      A * ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
        ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
  calc ∫⁻ p : ℝ × Space, m p.1 * (A * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal)
      = ∫⁻ p : ℝ × Space, A * (m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal) :=
        lintegral_congr fun p => by ring
    _ = A * ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal :=
        lintegral_const_mul' A _ hA
    _ = A * ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
          ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
        rw [wn_pullback_rep hrt hW τ₀ hm]

/-! ### Measurability -/

theorem wn_measurable_pt {W : ℝ × Space → CVec3} (hW : Measurable W) (τ₀ : ℝ) (c : Fin 3) :
    Measurable (fun p : ℝ × Space =>
      W (τ₀ + Real.log p.1, Real.exp (-(Real.log p.1 / 2)) • p.2) c) := by
  have hcomp : Measurable (fun v : CVec3 => v c) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) c).measurable
  have hφ : Measurable (fun p : ℝ × Space =>
      (τ₀ + Real.log p.1, Real.exp (-(Real.log p.1 / 2)) • p.2)) := by
    fun_prop
  exact hcomp.comp (hW.comp hφ)

theorem wn_measurable_windowField {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    {W : ℝ × Space → CVec3} (hW : Measurable W) (c : Fin 3) :
    Measurable (windowField χ τ₀ W c) := by
  have hχm : Measurable χ := hχ.smooth.continuous.measurable
  have hlog : Measurable (fun p : PS 3 => Real.log p.1) := Real.measurable_log.comp measurable_fst
  have hr : Measurable (fun p : PS 3 =>
      ((χ (Real.log p.1) * Real.exp (-(Real.log p.1 / 2)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((hχm.comp hlog).mul (Real.measurable_exp.comp (hlog.div_const 2).neg))
  have hpt := wn_measurable_pt hW τ₀ c
  unfold windowField
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  exact hr.mul hpt

theorem wn_measurable_windowForce (μ : ℂ) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    {W Fr : ℝ × Space → CVec3} (hW : Measurable W) (hFr : Measurable Fr) (c : Fin 3) :
    Measurable (windowForce μ χ τ₀ W Fr c) := by
  have hχm : Measurable χ := hχ.smooth.continuous.measurable
  have hdm : Measurable (deriv χ) := (hχ.smooth.continuous_deriv (by simp)).measurable
  have hlog : Measurable (fun p : PS 3 => Real.log p.1) := Real.measurable_log.comp measurable_fst
  have hχl : Measurable (fun p : PS 3 => χ (Real.log p.1)) := hχm.comp hlog
  have hdl : Measurable (fun p : PS 3 => deriv χ (Real.log p.1)) := hdm.comp hlog
  have hpt := wn_measurable_pt hW τ₀ c
  have hpt' := wn_measurable_pt hFr τ₀ c
  have hexp : Measurable (fun p : PS 3 =>
      ((Real.exp (-(3 * Real.log p.1 / 2)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((hlog.const_mul 3).div_const 2).neg)
  have hA : Measurable (fun p : PS 3 =>
      ((deriv χ (Real.log p.1) : ℝ) : ℂ) - μ * ((χ (Real.log p.1) : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp hdl).sub (measurable_const.mul (Complex.measurable_ofReal.comp hχl))
  have hB : Measurable (fun p : PS 3 => ((χ (Real.log p.1) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hχl
  unfold windowForce
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  exact hexp.mul ((hA.mul hpt).add (hB.mul hpt'))

/-! ### Finiteness of the field -/

theorem wn_field_lt_top {χ : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hMχ : ∀ t, ‖χ t‖ ≤ M)
    (hχ : WindowCutoff χ) (hrt : r ≠ ⊤) (hr0 : 0 < r.toReal) (τ₀ : ℝ) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (c : Fin 3) :
    ∫⁻ p, ‖windowField χ τ₀ W c p‖ₑ ^ r.toReal < ⊤ := by
  have hmU : Measurable ((Ioo (-2 : ℝ) 2).indicator
      (fun t => ENNReal.ofReal (Real.exp ((1 - r.toReal / 2) * t)))) :=
    Measurable.indicator (by fun_prop) measurableSet_Ioo
  rw [wn_lintegral_expChart hr0 (fun p hp => by simp [windowField, not_lt.2 hp])]
  refine lt_of_le_of_lt (lintegral_mono fun p =>
    wn_field_pointwise hM0 hMχ hχ hr0 τ₀ W c p) ?_
  rw [wn_pullback_mul hrt hW τ₀ hmU (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top)]
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr0.le ENNReal.ofReal_ne_top) ?_
  refine lt_of_le_of_lt (wn_weight_ind (φ := fun t => ENNReal.ofReal (Real.exp ((1 - r.toReal / 2) * t)))
    (D := ENNReal.ofReal (Real.exp (2 * |3 / 2 + (1 - r.toReal / 2)|))) ENNReal.ofReal_ne_top
    (fun t ht => wn_weight_exp _ ht) (fun t => ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal)) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [lintegral_indicator measurableSet_Ioo]
  exact (lintegral_mono_set Ioo_subset_Icc_self).trans_lt
    (lintegral_window_lt_top hrt w τ₀ (-2) 2)

/-! ### The main theorem -/

theorem windowNorms : WindowNorms := by
  intro r _ hr1 hrt χ hχ
  have hr : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr1
    simpa using this
  have hr0 : 0 < r.toReal := by linarith
  have hr1' : (1 : ℝ) ≤ r.toReal := hr.le
  obtain ⟨M, hM0, hMχ, hMd⟩ := wn_cutoff_bound hχ
  -- the constant `K`
  have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (r.toReal - 1) := Real.rpow_nonneg (by norm_num) _
  have hX1 : 0 ≤ (2 : ℝ) ^ (r.toReal - 1) * Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|) :=
    mul_nonneg h2nn (Real.exp_pos _).le
  have hX : 0 ≤ (2 : ℝ) ^ (r.toReal - 1) * Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|) *
      M ^ r.toReal := mul_nonneg hX1 (Real.rpow_nonneg hM0 _)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ((2 : ℝ) ^ (r.toReal - 1) *
      Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|) * M ^ r.toReal) ^ (1 / r.toReal) :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Real.rpow_nonneg hX _
  have hKpow : K ^ r.toReal = (2 : ℝ) ^ (r.toReal - 1) *
      Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|) * M ^ r.toReal := by
    rw [hKdef, one_div, Real.rpow_inv_rpow hX hr0.ne']
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ (r.toReal - 1)) = (2 : ℝ≥0∞) ^ (r.toReal - 1) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (x := 2) (p := r.toReal - 1) (by norm_num) (by linarith),
      ENNReal.ofReal_ofNat]
  have hKeq : ENNReal.ofReal K ^ r.toReal =
      ENNReal.ofReal (Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|)) *
        (2 : ℝ≥0∞) ^ (r.toReal - 1) * ENNReal.ofReal M ^ r.toReal := by
    rw [ENNReal.ofReal_rpow_of_nonneg hK0 hr0.le, hKpow, ← h2,
      ENNReal.ofReal_mul hX1, ENNReal.ofReal_mul h2nn, ENNReal.ofReal_rpow_of_nonneg hM0 hr0.le]
    ring
  have hC : ∀ x y : ℝ≥0∞, (x + y) ^ r.toReal ≤
      (2 : ℝ≥0∞) ^ (r.toReal - 1) * (x ^ r.toReal + y ^ r.toReal) :=
    fun x y => ENNReal.rpow_add_le_mul_rpow_add_rpow x y hr1'
  have hBne : ENNReal.ofReal (Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|)) *
      (2 : ℝ≥0∞) ^ (r.toReal - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num))
  refine ⟨K, hK0, ?_⟩
  intro P _ μ f w W Fr hW hFr τ₀ c
  have hWm : Measurable W := hW.meas.measurable
  have hFm : Measurable Fr := hFr.meas.measurable
  -- the field
  have hu_mem : MemLp (windowField χ τ₀ W c) (ENNReal.ofReal r.toReal) volume :=
    wn_memLp hr0 (wn_measurable_windowField hχ τ₀ hWm c).aestronglyMeasurable
      (wn_field_lt_top hM0 hMχ hχ hrt hr0 τ₀ hW c)
  -- the force, abbreviations
  set mF : ℝ → ℝ≥0∞ := (Ioo (-2 : ℝ) 2).indicator (fun t =>
    ENNReal.ofReal (Real.exp ((1 - 3 * r.toReal / 2) * t)) * (2 : ℝ≥0∞) ^ (r.toReal - 1)) with hmF
  set AW : ℝ≥0∞ := ENNReal.ofReal (M * (1 + ‖μ‖)) ^ r.toReal with hAWdef
  set Af : ℝ≥0∞ := ENNReal.ofReal M ^ r.toReal with hAfdef
  set c' : ℝ≥0∞ := ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal with hc'def
  set B' : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * |3 / 2 + (1 - 3 * r.toReal / 2)|)) *
    (2 : ℝ≥0∞) ^ (r.toReal - 1) with hB'def
  set IW : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal with hIWdef
  set IF : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖f (τ : AddCircle P)‖ₑ ^ r.toReal with hIFdef
  have hmF_meas : Measurable mF :=
    Measurable.indicator (by fun_prop) measurableSet_Ioo
  have hAW_ne : AW ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
  have hAf_ne : Af ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
  have hc'_ne : c' ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
  have hAW_split : AW = Af * c' := by
    rw [hAWdef, hAfdef, hc'def, ENNReal.ofReal_mul hM0, ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
  have hwb : ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * mF t *
      ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal ≤ B' * IW := by
    rw [hIWdef, ← wn_window_transfer w τ₀]
    refine wn_weight_ind (φ := fun t => ENNReal.ofReal (Real.exp ((1 - 3 * r.toReal / 2) * t)) *
      (2 : ℝ≥0∞) ^ (r.toReal - 1)) hBne ?_ _
    intro t ht
    rw [← mul_assoc]
    exact mul_le_mul' (wn_weight_exp _ ht) le_rfl
  have hfb : ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * mF t *
      ‖f ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal ≤ B' * IF := by
    rw [hIFdef, ← wn_window_transfer f τ₀]
    refine wn_weight_ind (φ := fun t => ENNReal.ofReal (Real.exp ((1 - 3 * r.toReal / 2) * t)) *
      (2 : ℝ≥0∞) ^ (r.toReal - 1)) hBne ?_ _
    intro t ht
    rw [← mul_assoc]
    exact mul_le_mul' (wn_weight_exp _ ht) le_rfl
  -- measurability and the force bound
  have hF_meas : Measurable (windowForce μ χ τ₀ W Fr c) :=
    wn_measurable_windowForce μ hχ τ₀ hWm hFm c
  have hFzero : ∀ p : ℝ × Space, p.1 ≤ 0 → windowForce μ χ τ₀ W Fr c p = 0 := fun p hp => by
    simp [windowForce, not_lt.2 hp]
  have hφ2 : Measurable (fun p : ℝ × Space => (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)) := by
    fun_prop
  have hVW : Measurable (fun p : ℝ × Space =>
      ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal) :=
    ((hWm.comp hφ2).enorm).pow_const _
  have hmeasA : Measurable (fun p : ℝ × Space =>
      mF p.1 * (AW * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal)) :=
    (hmF_meas.comp measurable_fst).mul (measurable_const.mul hVW)
  have hmain : ∫⁻ p, ‖windowForce μ χ τ₀ W Fr c p‖ₑ ^ r.toReal ≤
      AW * (B' * IW) + Af * (B' * IF) := by
    calc ∫⁻ p, ‖windowForce μ χ τ₀ W Fr c p‖ₑ ^ r.toReal
        = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) *
            ‖windowForce μ χ τ₀ W Fr c (expChart p)‖ₑ ^ r.toReal :=
          wn_lintegral_expChart hr0 hFzero
      _ ≤ ∫⁻ p : ℝ × Space, mF p.1 * (AW * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal +
            Af * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal) :=
          lintegral_mono fun p => wn_force_pointwise hM0 hMχ hMd hχ hr0 hC μ τ₀ W Fr c p
      _ = ∫⁻ p : ℝ × Space, (mF p.1 * (AW * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal) +
            mF p.1 * (Af * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal)) :=
          lintegral_congr fun p => mul_add _ _ _
      _ = (∫⁻ p : ℝ × Space, mF p.1 * (AW * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal)) +
            ∫⁻ p : ℝ × Space, mF p.1 * (Af * ‖Fr (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal) :=
          lintegral_add_left hmeasA _
      _ = AW * (∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * mF t *
            ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) +
          Af * (∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * mF t *
            ‖f ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) := by
          rw [wn_pullback_mul hrt hW τ₀ hmF_meas hAW_ne, wn_pullback_mul hrt hFr τ₀ hmF_meas hAf_ne]
      _ ≤ AW * (B' * IW) + Af * (B' * IF) :=
          add_le_add (mul_le_mul' le_rfl hwb) (mul_le_mul' le_rfl hfb)
  have hmain' : eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ^ r.toReal ≤
      AW * (B' * IW) + Af * (B' * IF) := by
    rw [wn_eLpNorm_rpow hr0]
    exact hmain
  have hIW_lt : IW < ⊤ := wn_window_lt_top hrt w τ₀
  have hIF_lt : IF < ⊤ := wn_window_lt_top hrt f τ₀
  have hfin : AW * (B' * IW) + Af * (B' * IF) < ⊤ :=
    ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hAW_ne)
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBne) hIW_lt),
       ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hAf_ne)
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBne) hIF_lt)⟩
  have hF_lt : eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have h1 := hmain'.trans_lt hfin
    rw [hcon, ENNReal.top_rpow_of_pos hr0] at h1
    exact lt_irrefl _ h1
  -- the bound
  have hbound : eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ^ r.toReal ≤
      ENNReal.ofReal K ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
        (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
          ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by
    refine hmain'.trans ?_
    have hsum : IF + c' * IW ≤ ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
        (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
          ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by
      have h1 : ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
          c' * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal = c' * IW :=
        lintegral_const_mul' c' _ hc'_ne
      rw [← h1]
      exact le_lintegral_add _ _
    calc AW * (B' * IW) + Af * (B' * IF) = ENNReal.ofReal K ^ r.toReal * (IF + c' * IW) := by
          rw [hKeq, hAW_split]
          ring
      _ ≤ ENNReal.ofReal K ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
          (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
            ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) :=
          mul_le_mul' le_rfl hsum
  exact ⟨hu_mem, ⟨hF_meas.aestronglyMeasurable, hF_lt⟩, hbound⟩

end UnforcedLeray.Short.PartIIa
