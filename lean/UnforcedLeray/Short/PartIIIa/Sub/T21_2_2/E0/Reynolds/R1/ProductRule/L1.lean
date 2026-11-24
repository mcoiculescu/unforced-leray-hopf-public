import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.ProductRule.Integ

/-!
# `PartIII-a:T21/2/2/2/2/1/4`, leaf `WPRL1` (L¹ convergence of the slopes)

Source: `the November 2 reference manuscript` (SP) lines 3060-3073.
With `h = r'-r`, `Q = h⁻¹(f r' - f r)`, `E = Q - f'`, `Δ = h⁻¹(w r' - w r)`, `N = ‖f r‖²`,
`N_h = ‖f r'‖²`, the slope minus the derivative is exactly
`(Δ - ∂w) N + Δ (N_h - N) + 2 w Re⟨f, E⟩ + h w ‖Q‖²`.  The four pieces tend to `0` in `L¹`:
`(Δ-∂w)N` by dominated convergence, `Δ(N_h-N)` and `h w‖Q‖²` through `∫⁻ w‖Q‖²` bounded, and
`w Re⟨f,E⟩` by Hölder with respect to `w μ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

theorem wpr_ofReal_bd {E : Type*} [NormedAddCommGroup E] (c w' : ℝ) (hc : 0 ≤ c) (hw : 0 ≤ w')
    (z : E) :
    ENNReal.ofReal (c * (w' * ‖z‖ ^ 2)) = ENNReal.ofReal c * (ENNReal.ofReal w' * ‖z‖ₑ ^ 2) := by
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hw, ENNReal.ofReal_pow (norm_nonneg z),
    ofReal_norm_eq_enorm]

theorem wpr_enorm_add_sq_le {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have hr : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc ‖a + b‖ₑ ^ 2 = ENNReal.ofReal (‖a + b‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    _ ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal hr
    _ = 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
          ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
        norm_num

theorem wpr_pt_id (h a b Nh N I Ip Qs dw : ℝ) (hh : h ≠ 0)
    (hN : Nh = N + 2 * h * I + h ^ 2 * Qs) :
    h⁻¹ * (a * Nh - b * N) - (dw * N + b * (2 * Ip)) =
      (h⁻¹ * (a - b) - dw) * N + h⁻¹ * (a - b) * (Nh - N) + 2 * b * (I - Ip) + h * b * Qs := by
  rw [hN]
  field_simp
  ring

theorem wpr_lintegral_add4 {X : Type*} [MeasurableSpace X] {μ : Measure X} (A B C D : X → ℝ≥0∞)
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) (hC : AEMeasurable C μ) :
    ∫⁻ x, (A x + B x + C x + D x) ∂μ =
      ∫⁻ x, A x ∂μ + ∫⁻ x, B x ∂μ + ∫⁻ x, C x ∂μ + ∫⁻ x, D x ∂μ := by
  have e1 := lintegral_add_left' ((hA.add hB).add hC) D
  have e2 := lintegral_add_left' (hA.add hB) C
  have e3 := lintegral_add_left' hA B
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1, e2, e3]


end UnforcedLeray.Short.IIIa.E0

set_option maxHeartbeats 4000000 in
open UnforcedLeray.Short.IIIa.E0 in
theorem wprL1 : UnforcedLeray.Short.IIIa.E0.WPRL1 := by
  intro μ w f f' r hH
  obtain ⟨hw, hf, ⟨C, δ, hC0, hδ, hball⟩, hd, hT, hf0, hf1⟩ := hH
  have hrb : r ∈ ball r δ := mem_ball_self hδ
  have hw0 : ∀ x, 0 ≤ w r x := fun x => (hball x r hrb).2.1
  have hfr : AEStronglyMeasurable (f r) μ := hf.self_of_nhds
  have hf' : AEStronglyMeasurable f' μ := wpr_aesm_of_hasDerivAt f r hf f' hd
  have hdw : AEMeasurable (fun x => deriv (fun q => w q x) r) μ :=
    (wpr_aesm_of_hasDerivAt (fun q x => w q x) r
      (Filter.Eventually.of_forall fun q => (hw q).aestronglyMeasurable) _
      (fun x => (hball x r hrb).1.hasDerivAt)).aemeasurable
  have hMVT : ∀ x, ∀ r' ∈ ball r δ, |w r' x - w r x| ≤ C * w r x * |r' - r| := by
    intro x r' hr'
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun q => w q x)
      (s := ball r δ) (C := C * w r x) (fun y hy => (hball x y hy).1)
      (fun y hy => by rw [Real.norm_eq_abs]; exact (hball x y hy).2.2.2)
      (convex_ball r δ) hrb hr'
    simpa [Real.norm_eq_abs] using h
  have hΔ : ∀ x, ∀ r' ∈ ball r δ, r' ≠ r → |(r' - r)⁻¹ * (w r' x - w r x)| ≤ C * w r x := by
    intro x r' hb hne
    have hpos : 0 < |r' - r| := abs_pos.2 (sub_ne_zero.2 hne)
    rw [abs_mul, abs_inv]
    calc |r' - r|⁻¹ * |w r' x - w r x| ≤ |r' - r|⁻¹ * (C * w r x * |r' - r|) :=
          mul_le_mul_of_nonneg_left (hMVT x r' hb) (inv_nonneg.2 hpos.le)
      _ = C * w r x := by field_simp
  have hΔlim : ∀ x, Tendsto (fun r' => (r' - r)⁻¹ * (w r' x - w r x)) (𝓝[≠] r)
      (𝓝 (deriv (fun q => w q x) r)) := by
    intro x
    exact Tendsto.congr (fun r' => by simp [slope, smul_eq_mul])
      (hasDerivAt_iff_tendsto_slope.1 (hball x r hrb).1.hasDerivAt)
  have hdwb : ∀ x, |deriv (fun q => w q x) r| ≤ C * w r x := fun x => (hball x r hrb).2.2.2
  have hfev : ∀ᶠ r' in 𝓝[≠] r, AEStronglyMeasurable (f r') μ := nhdsWithin_le_nhds hf
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ≥0∞, K = 2 * 1 + 2 * ∫⁻ x, ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2 ∂μ :=
    ⟨_, rfl⟩
  have hKtop : K ≠ ⊤ := by
    rw [hKdef]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) (by norm_num),
      ENNReal.mul_ne_top (by norm_num) hf1.ne⟩
  -- Step 1: the dominated convergence term `T1 = (Δ - ∂w) N`
  have hT1 : Tendsto (fun r' => ∫⁻ x, ‖((r' - r)⁻¹ * (w r' x - w r x)
      - deriv (fun q => w q x) r) * ‖f r x‖ ^ 2‖ₑ ∂μ) (𝓝[≠] r) (𝓝 0) := by
    have key := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := 𝓝[≠] r)
      (F := fun r' x => ‖((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r)
        * ‖f r x‖ ^ 2‖ₑ)
      (f := fun _ => 0)
      (fun x => ENNReal.ofReal (2 * C) * (ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2)) ?_ ?_ ?_ ?_
    · simpa using key
    · refine Filter.Eventually.of_forall fun r' => ?_
      have hm : AEMeasurable (fun x => (r' - r)⁻¹ * (w r' x - w r x)) μ :=
        (((hw r').sub (hw r)).const_mul _).aemeasurable
      exact ((hm.sub hdw).mul (hfr.norm.pow 2).aemeasurable).enorm
    · filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds r hδ)]
        with r' hne hb
      refine ae_of_all _ fun x => ?_
      have h1 := hΔ x r' hb hne
      have h2 := hdwb x
      have habs : |((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r)
          * ‖f r x‖ ^ 2| ≤ 2 * C * (w r x * ‖f r x‖ ^ 2) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg ‖f r x‖)]
        have h3 : |(r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r| ≤ 2 * C * w r x := by
          calc _ ≤ |(r' - r)⁻¹ * (w r' x - w r x)| + |deriv (fun q => w q x) r| := abs_sub _ _
            _ ≤ C * w r x + C * w r x := add_le_add h1 h2
            _ = 2 * C * w r x := by ring
        nlinarith [sq_nonneg ‖f r x‖, mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖f r x‖)]
      calc ‖((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r) * ‖f r x‖ ^ 2‖ₑ
          = ENNReal.ofReal |((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r)
              * ‖f r x‖ ^ 2| := Real.enorm_eq_ofReal_abs _
        _ ≤ ENNReal.ofReal (2 * C * (w r x * ‖f r x‖ ^ 2)) := ENNReal.ofReal_le_ofReal habs
        _ = ENNReal.ofReal (2 * C) * (ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2) :=
          wpr_ofReal_bd (2 * C) (w r x) (by linarith) (hw0 x) (f r x)
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf0.ne
    · refine ae_of_all _ fun x => ?_
      have h1 := ((hΔlim x).sub_const (deriv (fun q => w q x) r)).mul_const (‖f r x‖ ^ 2)
      simpa using h1.enorm
  -- Step 2: the algebraic identity for the slope minus the derivative
  have hNf : ∀ r' x, r' ≠ r → ‖f r' x‖ ^ 2 = ‖f r x‖ ^ 2
      + 2 * (r' - r) * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x))
      + (r' - r) ^ 2 * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 := by
    intro r' x hne
    have hh : r' - r ≠ 0 := sub_ne_zero.2 hne
    have hfeq : f r' x = f r x + (r' - r) • ((r' - r)⁻¹ • (f r' x - f r x)) := by
      rw [smul_inv_smul₀ hh]; abel
    conv_lhs => rw [hfeq]
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hdec : ∀ r', r' ≠ r → ∀ x,
      ‖(r' - r)⁻¹ • (w r' x * ‖f r' x‖ ^ 2 - w r x * ‖f r x‖ ^ 2)
          - deriv (fun q => w q x * ‖f q x‖ ^ 2) r‖ₑ ≤
        ‖((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r) * ‖f r x‖ ^ 2‖ₑ +
        ‖(r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ +
        ‖2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)‖ₑ +
        ‖(r' - r) * w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2‖ₑ := by
    intro r' hne x
    have hh : r' - r ≠ 0 := sub_ne_zero.2 hne
    have hdd : deriv (fun q => w q x * ‖f q x‖ ^ 2) r =
        deriv (fun q => w q x) r * ‖f r x‖ ^ 2 + w r x * (2 * inner ℝ (f r x) (f' x)) :=
      ((hball x r hrb).1.hasDerivAt.mul (hd x).norm_sq).deriv
    have key := wpr_pt_id (r' - r) (w r' x) (w r x) (‖f r' x‖ ^ 2) (‖f r x‖ ^ 2)
      (inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x))) (inner ℝ (f r x) (f' x))
      (‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2) (deriv (fun q => w q x) r) hh (hNf r' x hne)
    have hid : (r' - r)⁻¹ • (w r' x * ‖f r' x‖ ^ 2 - w r x * ‖f r x‖ ^ 2)
          - deriv (fun q => w q x * ‖f q x‖ ^ 2) r =
        ((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r) * ‖f r x‖ ^ 2 +
        (r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2) +
        2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x) +
        (r' - r) * w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 := by
      rw [hdd, smul_eq_mul, inner_sub_right]
      linear_combination key
    rw [hid]
    exact (enorm_add_le _ _).trans (add_le_add
      ((enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)) le_rfl)
  -- Step 3: bound on `Pq(r') = ∫⁻ w ‖Q‖²`
  have hPq : ∀ᶠ r' in 𝓝[≠] r, ∫⁻ x, ENNReal.ofReal (w r x) *
      ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2 ∂μ ≤ K := by
    filter_upwards [hT.eventually (gt_mem_nhds zero_lt_one), hfev] with r' hEv hfr'
    have hEm : AEMeasurable (fun x => (r' - r)⁻¹ • (f r' x - f r x) - f' x) μ :=
      (((hfr'.sub hfr).const_smul ((r' - r)⁻¹)).sub hf').aemeasurable
    have hpt : ∀ x, ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2 ≤
        2 * (ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2) +
        2 * (ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2) := by
      intro x
      have := wpr_enorm_add_sq_le ((r' - r)⁻¹ • (f r' x - f r x) - f' x) (f' x)
      rw [sub_add_cancel] at this
      calc ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2
          ≤ ENNReal.ofReal (w r x) * (2 * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2
            + 2 * ‖f' x‖ₑ ^ 2) := by gcongr
        _ = _ := by ring
    have hA : AEMeasurable (fun x => 2 * (ENNReal.ofReal (w r x) *
        ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2)) μ :=
      (((hw r).ennreal_ofReal.aemeasurable.mul (hEm.enorm.pow_const 2))).const_mul 2
    calc ∫⁻ x, ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ x, (2 * (ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2)
            + 2 * (ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2)) ∂μ := lintegral_mono hpt
      _ = 2 * ∫⁻ x, ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2 ∂μ
            + 2 * ∫⁻ x, ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2 ∂μ := by
        rw [lintegral_add_left' hA, lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
      _ ≤ 2 * 1 + 2 * ∫⁻ x, ENNReal.ofReal (w r x) * ‖f' x‖ₑ ^ 2 ∂μ := by
        gcongr
      _ = K := hKdef.symm
  -- Step 4: the term `T4 = h w ‖Q‖²`
  have hT4 : ∀ r' x, ‖(r' - r) * w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2‖ₑ =
      ENNReal.ofReal |r' - r| * (ENNReal.ofReal (w r x) *
        ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2) := by
    intro r' x
    rw [← wpr_ofReal_bd |r' - r| (w r x) (abs_nonneg _) (hw0 x), Real.enorm_eq_ofReal_abs,
      mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
  have hJ4eq : ∀ r', ∫⁻ x, ‖(r' - r) * w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2‖ₑ ∂μ =
      ENNReal.ofReal |r' - r| * ∫⁻ x, ENNReal.ofReal (w r x) *
        ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2 ∂μ := by
    intro r'
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun x => hT4 r' x
  have hJ4 : Tendsto (fun r' => ∫⁻ x, ‖(r' - r) * w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2‖ₑ ∂μ)
      (𝓝[≠] r) (𝓝 0) := by
    have hab : Tendsto (fun r' : ℝ => ENNReal.ofReal |r' - r|) (𝓝[≠] r) (𝓝 0) := by
      have hc : Continuous (fun r' : ℝ => |r' - r|) := by fun_prop
      have h1 := ENNReal.tendsto_ofReal ((hc.tendsto r).mono_left (nhdsWithin_le_nhds (s := ({r}ᶜ : Set ℝ))))
      simpa using h1
    have h2 := ENNReal.Tendsto.mul_const hab (Or.inr hKtop)
    rw [zero_mul] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Filter.Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hPq] with r' hP
    rw [hJ4eq r']
    gcongr
  -- Step 5: the term `Δ (N_h - N)`
  have hJ2pt : ∀ r' x, r' ∈ ball r δ → r' ≠ r →
      ‖(r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ ≤
        ENNReal.ofReal (C * |r' - r|) * (ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2) +
        ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2)) *
          (ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2) := by
    intro r' x hb hne
    have hΔb := hΔ x r' hb hne
    have hI := abs_real_inner_le_norm (f r x) ((r' - r)⁻¹ • (f r' x - f r x))
    have hdiff : ‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2 = 2 * (r' - r) *
        inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x))
        + (r' - r) ^ 2 * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 := by
      rw [hNf r' x hne]; ring
    have hNh : |‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2| ≤ |r' - r| * ‖f r x‖ ^ 2
        + (|r' - r| + (r' - r) ^ 2) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 := by
      rw [hdiff]
      have h1 : |2 * (r' - r) * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x))|
          ≤ |r' - r| * (‖f r x‖ ^ 2 + ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2) := by
        rw [abs_mul, abs_mul, abs_two]
        nlinarith [mul_le_mul_of_nonneg_left hI (abs_nonneg (r' - r)),
          mul_nonneg (abs_nonneg (r' - r))
            (sq_nonneg (‖f r x‖ - ‖(r' - r)⁻¹ • (f r' x - f r x)‖))]
      have h2 : |(r' - r) ^ 2 * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2|
          = (r' - r) ^ 2 * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 :=
        abs_of_nonneg (by positivity)
      calc _ ≤ |2 * (r' - r) * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x))|
            + |(r' - r) ^ 2 * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2| :=
            abs_add_le _ _
        _ ≤ |r' - r| * (‖f r x‖ ^ 2 + ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2)
            + (r' - r) ^ 2 * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 := by
            rw [h2]; exact add_le_add h1 le_rfl
        _ = |r' - r| * ‖f r x‖ ^ 2 + (|r' - r| + (r' - r) ^ 2) *
            ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2 := by ring
    have hC0w : 0 ≤ C * w r x := mul_nonneg hC0 (hw0 x)
    calc ‖(r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ
        = ENNReal.ofReal |(r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (C * w r x * (|r' - r| * ‖f r x‖ ^ 2
            + (|r' - r| + (r' - r) ^ 2) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal (by rw [abs_mul]; exact mul_le_mul hΔb hNh (abs_nonneg _) hC0w)
      _ = ENNReal.ofReal (C * |r' - r| * (w r x * ‖f r x‖ ^ 2)) +
          ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2) *
            (w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2)) := by
          rw [← ENNReal.ofReal_add
            (mul_nonneg (mul_nonneg hC0 (abs_nonneg _)) (mul_nonneg (hw0 x) (sq_nonneg _)))
            (mul_nonneg (mul_nonneg hC0 (by positivity)) (mul_nonneg (hw0 x) (sq_nonneg _)))]
          congr 1
          ring
      _ = ENNReal.ofReal (C * |r' - r|) * (ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2) +
          ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2)) *
            (ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2) := by
          rw [wpr_ofReal_bd (C * |r' - r|) (w r x) (mul_nonneg hC0 (abs_nonneg _)) (hw0 x),
            wpr_ofReal_bd (C * (|r' - r| + (r' - r) ^ 2)) (w r x)
              (mul_nonneg hC0 (by positivity)) (hw0 x)]
  have hJ2 : Tendsto (fun r' => ∫⁻ x, ‖(r' - r)⁻¹ * (w r' x - w r x) *
      (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ ∂μ) (𝓝[≠] r) (𝓝 0) := by
    have hc1 : Tendsto (fun r' : ℝ => ENNReal.ofReal (C * |r' - r|)) (𝓝[≠] r) (𝓝 0) := by
      have hc : Continuous (fun r' : ℝ => C * |r' - r|) := by fun_prop
      have h1 := ENNReal.tendsto_ofReal ((hc.tendsto r).mono_left (nhdsWithin_le_nhds (s := ({r}ᶜ : Set ℝ))))
      simpa using h1
    have hc2 : Tendsto (fun r' : ℝ => ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2)))
        (𝓝[≠] r) (𝓝 0) := by
      have hc : Continuous (fun r' : ℝ => C * (|r' - r| + (r' - r) ^ 2)) := by fun_prop
      have h1 := ENNReal.tendsto_ofReal ((hc.tendsto r).mono_left (nhdsWithin_le_nhds (s := ({r}ᶜ : Set ℝ))))
      simpa using h1
    have hM : ∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ ≠ ⊤ := hf0.ne
    have h2 := (ENNReal.Tendsto.mul_const hc1 (Or.inr hM)).add
      (ENNReal.Tendsto.mul_const hc2 (Or.inr hKtop))
    rw [zero_mul, zero_mul, add_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Filter.Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds r hδ), hPq]
      with r' hne hb hP
    have hA : AEMeasurable (fun x => ENNReal.ofReal (C * |r' - r|) *
        (ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2)) μ :=
      ((((hw r).ennreal_ofReal.aemeasurable.mul (hfr.enorm.pow_const 2))).const_mul _)
    calc ∫⁻ x, ‖(r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ ∂μ
        ≤ ∫⁻ x, (ENNReal.ofReal (C * |r' - r|) * (ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2) +
            ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2)) *
              (ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2)) ∂μ :=
          lintegral_mono fun x => hJ2pt r' x hb hne
      _ = ENNReal.ofReal (C * |r' - r|) * ∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ +
          ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2)) * ∫⁻ x, ENNReal.ofReal (w r x) *
            ‖(r' - r)⁻¹ • (f r' x - f r x)‖ₑ ^ 2 ∂μ := by
          rw [lintegral_add_left' hA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (C * |r' - r|) * ∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ +
          ENNReal.ofReal (C * (|r' - r| + (r' - r) ^ 2)) * K := by
          gcongr
  -- Step 6: the Hölder term `2 w Re⟨f, E⟩`
  have hJ3 : Tendsto (fun r' => ∫⁻ x, ‖2 * w r x * inner ℝ (f r x)
      ((r' - r)⁻¹ • (f r' x - f r x) - f' x)‖ₑ ∂μ) (𝓝[≠] r) (𝓝 0) := by
    have hEp := hT.ennrpow_const (1 / 2 : ℝ)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hEp
    have hMh : (∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf0.ne
    have h3 := ENNReal.Tendsto.const_mul (a := (∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ)
      ^ (1 / 2 : ℝ)) hEp (Or.inr hMh)
    have h4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 2) h3 (Or.inr ENNReal.ofReal_ne_top)
    simp only [mul_zero] at h4
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h4
      (Filter.Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hfev] with r' hfr'
    have hEm : AEMeasurable (fun x => (r' - r)⁻¹ • (f r' x - f r x) - f' x) μ :=
      (((hfr'.sub hfr).const_smul ((r' - r)⁻¹)).sub hf').aemeasurable
    have hW : Measurable (fun x => ENNReal.ofReal (w r x)) := (hw r).ennreal_ofReal
    have hFG : AEMeasurable (fun x => ‖f r x‖ₑ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ) μ :=
      hfr.enorm.mul hEm.enorm
    have hFν : AEMeasurable (fun x => ‖f r x‖ₑ)
        (μ.withDensity (fun x => ENNReal.ofReal (w r x))) :=
      hfr.enorm.mono_ac (withDensity_absolutelyContinuous μ _)
    have hGν : AEMeasurable (fun x => ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ)
        (μ.withDensity (fun x => ENNReal.ofReal (w r x))) :=
      hEm.enorm.mono_ac (withDensity_absolutelyContinuous μ _)
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.withDensity (fun x => ENNReal.ofReal (w r x)))
      Real.HolderConjugate.two_two hFν hGν
    have e1 : ∫⁻ x, (‖f r x‖ₑ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ)
        ∂(μ.withDensity (fun x => ENNReal.ofReal (w r x))) =
        ∫⁻ x, ENNReal.ofReal (w r x) * (‖f r x‖ₑ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul₀ hW.aemeasurable hFG
    have e2 : ∫⁻ x, ‖f r x‖ₑ ^ (2 : ℝ) ∂(μ.withDensity (fun x => ENNReal.ofReal (w r x))) =
        ∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ := by
      rw [lintegral_withDensity_eq_lintegral_mul₀ hW.aemeasurable
        (hfr.enorm.pow_const _)]
      simp only [ENNReal.rpow_two, Pi.mul_apply]
    have e3 : ∫⁻ x, ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ (2 : ℝ)
        ∂(μ.withDensity (fun x => ENNReal.ofReal (w r x))) =
        ∫⁻ x, ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2 ∂μ := by
      rw [lintegral_withDensity_eq_lintegral_mul₀ hW.aemeasurable
        (hEm.enorm.pow_const _)]
      simp only [ENNReal.rpow_two, Pi.mul_apply]
    simp only [Pi.mul_apply] at hH
    rw [e1, e2, e3] at hH
    have hT3 : ∫⁻ x, ‖2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)‖ₑ ∂μ ≤
        ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (w r x) *
          (‖f r x‖ₑ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      have hI := abs_real_inner_le_norm (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)
      have hb : |2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)|
          ≤ 2 * w r x * (‖f r x‖ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖) := by
        rw [abs_mul, abs_of_nonneg (by linarith [hw0 x] : (0 : ℝ) ≤ 2 * w r x)]
        exact mul_le_mul_of_nonneg_left hI (by linarith [hw0 x])
      rw [Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)|
          ≤ ENNReal.ofReal (2 * w r x * (‖f r x‖ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖)) :=
            ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal 2 * (ENNReal.ofReal (w r x) *
            (‖f r x‖ₑ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ)) := by
          rw [ENNReal.ofReal_mul (by linarith [hw0 x] : (0 : ℝ) ≤ 2 * w r x),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
          ring
    calc ∫⁻ x, ‖2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)‖ₑ ∂μ
        ≤ ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (w r x) *
          (‖f r x‖ₑ * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ) ∂μ := hT3
      _ ≤ ENNReal.ofReal 2 * ((∫⁻ x, ENNReal.ofReal (w r x) * ‖f r x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, ENNReal.ofReal (w r x) * ‖(r' - r)⁻¹ • (f r' x - f r x) - f' x‖ₑ ^ 2 ∂μ)
            ^ (1 / 2 : ℝ)) := by
          gcongr
  -- Step 7: assemble
  have hbig : ∀ᶠ r' in 𝓝[≠] r, ∫⁻ x, ‖(r' - r)⁻¹ • (w r' x * ‖f r' x‖ ^ 2 - w r x * ‖f r x‖ ^ 2)
      - deriv (fun q => w q x * ‖f q x‖ ^ 2) r‖ₑ ∂μ ≤
      (∫⁻ x, ‖((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r) * ‖f r x‖ ^ 2‖ₑ ∂μ) +
      (∫⁻ x, ‖(r' - r)⁻¹ * (w r' x - w r x) * (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ ∂μ) +
      (∫⁻ x, ‖2 * w r x * inner ℝ (f r x) ((r' - r)⁻¹ • (f r' x - f r x) - f' x)‖ₑ ∂μ) +
      (∫⁻ x, ‖(r' - r) * w r x * ‖(r' - r)⁻¹ • (f r' x - f r x)‖ ^ 2‖ₑ ∂μ) := by
    filter_upwards [eventually_mem_nhdsWithin, hfev] with r' hne hfr'
    have hEsm : AEStronglyMeasurable (fun x => (r' - r)⁻¹ • (f r' x - f r x) - f' x) μ :=
      ((hfr'.sub hfr).const_smul ((r' - r)⁻¹)).sub hf'
    have hm : AEMeasurable (fun x => (r' - r)⁻¹ * (w r' x - w r x)) μ :=
      (((hw r').sub (hw r)).const_mul _).aemeasurable
    have a1 : AEMeasurable (fun x => ‖((r' - r)⁻¹ * (w r' x - w r x) - deriv (fun q => w q x) r)
        * ‖f r x‖ ^ 2‖ₑ) μ := ((hm.sub hdw).mul (hfr.norm.pow 2).aemeasurable).enorm
    have a2 : AEMeasurable (fun x => ‖(r' - r)⁻¹ * (w r' x - w r x) *
        (‖f r' x‖ ^ 2 - ‖f r x‖ ^ 2)‖ₑ) μ :=
      ((hm.mul ((hfr'.norm.pow 2).sub (hfr.norm.pow 2)).aemeasurable)).enorm
    have hX : AEStronglyMeasurable (fun x => inner ℝ (f r x)
        ((r' - r)⁻¹ • (f r' x - f r x) - f' x)) μ :=
      hfr.inner hEsm
    have a3 : AEMeasurable (fun x => ‖2 * w r x * inner ℝ (f r x)
        ((r' - r)⁻¹ • (f r' x - f r x) - f' x)‖ₑ) μ :=
      (((hw r).aestronglyMeasurable.const_mul 2).mul hX).aemeasurable.enorm
    refine (lintegral_mono fun x => hdec r' hne x).trans (le_of_eq ?_)
    exact wpr_lintegral_add4 _ _ _ _ a1 a2 a3
  have hsum := ((hT1.add hJ2).add hJ3).add hJ4
  rw [add_zero, add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  exact hbig
