import UnforcedLeray.Short.PartIIb.Sub.T11_3

/-!
# Part II-b, leaf `PartII-b:T11/3/7` (`HeatConvTail`): Gaussian `η`-tail of the heat flow

Source of record: `the November 2 reference manuscript`, SP 1923-1927 (Gaussian
decay of the heat flow of an `η`-compact datum). The statement is `HeatConvTail` of `Sub/T11_3.lean`.

Proof. Let `g` be a nice stream, `g = 0` on `{|η| ≥ L}` and `|g| ≤ M` (continuity, `c`-periodicity
in `q`, compactness of a cell). Fix `z` and put `a = max 0 (|z.2| - L)`, `θ = ν τ ∈ (0, ν τ₂]`.
The integrand `G_θ(w.1) G_θ(w.2) g(z - w)` vanishes unless `|w.2| ≥ a`, since `g(z - w) = 0` when
`|z.2 - w.2| ≥ L`. For `|t| ≥ a` one has `1 ≤ exp(κ (t² - a²))` with `κ = 1/(8θ)`, hence

  `|∫ G_θ(w.1) G_θ(w.2) g(z - w) dw| ≤ M e^{-κ a²} ∫ G_θ(w.1) G_θ(w.2) e^{κ w.2²} dw`.

The planar integral factorizes and `∫ G_θ(t) e^{κ t²} dt = (4πθ)^{-1/2} (8πθ)^{1/2} = √2`
(`integral_gaussian`), so the bound is `√2 M e^{-a²/(8θ)}`. Since `θ ≤ ν τ₂`,
`e^{-a²/(8θ)} ≤ e^{-a²/(8 ν τ₂)}`, and `√2 ≤ 2` gives the constant `C = 2M`, `L` from `NiceStream`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

/-- The one-dimensional weighted Gaussian integral: `∫ G_θ(t) e^{t²/(8θ)} dt = √2`. -/
theorem heatConvTail_gauss_weight {θ : ℝ} (hθ : 0 < θ) :
    ∫ t : ℝ, UnforcedLeray.B0191.heatKernel 1 θ t * Real.exp ((1 / (8 * θ)) * t ^ 2) =
      Real.sqrt 2 := by
  have hθ' : θ ≠ 0 := hθ.ne'
  have hfun : (fun t : ℝ => UnforcedLeray.B0191.heatKernel 1 θ t *
        Real.exp ((1 / (8 * θ)) * t ^ 2)) =
      fun t : ℝ => (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2) := by
    funext t
    unfold UnforcedLeray.B0191.heatKernel
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hpos : 0 < 4 * Real.pi * 1 * θ := by positivity
  have h8 : Real.pi / (1 / (8 * θ)) = 2 * (4 * Real.pi * 1 * θ) := by
    field_simp
    ring
  have hs : Real.sqrt (4 * Real.pi * 1 * θ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hfun, integral_const_mul, integral_gaussian, h8, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [mul_comm (Real.sqrt 2), ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- The planar weighted integral: `∫ G_θ(w.1) G_θ(w.2) e^{w.2²/(8θ)} dw = √2`. -/
theorem heatConvTail_plane_weight {θ : ℝ} (hθ : 0 < θ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * Real.exp ((1 / (8 * θ)) * w.2 ^ 2) =
      Real.sqrt 2 := by
  have hfun : ∀ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w *
      Real.exp ((1 / (8 * θ)) * w.2 ^ 2) =
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        (UnforcedLeray.B0191.heatKernel 1 θ w.2 * Real.exp ((1 / (8 * θ)) * w.2 ^ 2)) := by
    intro w
    unfold UnforcedLeray.B0284.heatKernel2
    ring
  simp only [hfun]
  calc ∫ w : ℝ × ℝ, UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        (UnforcedLeray.B0191.heatKernel 1 θ w.2 * Real.exp ((1 / (8 * θ)) * w.2 ^ 2))
      = ∫ w, UnforcedLeray.B0191.heatKernel 1 θ w.1 *
          (UnforcedLeray.B0191.heatKernel 1 θ w.2 * Real.exp ((1 / (8 * θ)) * w.2 ^ 2))
          ∂((volume : Measure ℝ).prod volume) := rfl
    _ = (∫ x, UnforcedLeray.B0191.heatKernel 1 θ x) *
          ∫ y, UnforcedLeray.B0191.heatKernel 1 θ y * Real.exp ((1 / (8 * θ)) * y ^ 2) :=
        integral_prod_mul (fun x => UnforcedLeray.B0191.heatKernel 1 θ x)
          (fun y => UnforcedLeray.B0191.heatKernel 1 θ y * Real.exp ((1 / (8 * θ)) * y ^ 2))
    _ = Real.sqrt 2 := by
        rw [UnforcedLeray.B0284.integral_heatKernel_one hθ, heatConvTail_gauss_weight hθ, one_mul]

/-- The weighted planar kernel is integrable (its integral is `√2 ≠ 0`). -/
theorem heatConvTail_plane_integrable {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w * Real.exp ((1 / (8 * θ)) * w.2 ^ 2)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [heatConvTail_plane_weight hθ]
  exact (Real.sqrt_pos.mpr (by norm_num)).ne'

/-- A nice stream is bounded and vanishes for `|η|` large (continuity, `c`-periodicity in `q`,
compactness of one period times a bounded `η`-interval). -/
theorem heatConvTail_bounded {c : ℝ} {g : ℝ × ℝ → ℝ} (hc : 0 < c) (hg : NiceStream c g) :
    ∃ L M : ℝ, 0 ≤ M ∧ (∀ p : ℝ × ℝ, L ≤ |p.2| → g p = 0) ∧ ∀ p : ℝ × ℝ, |g p| ≤ M := by
  obtain ⟨L, hL⟩ := hg.compact
  have hK : IsCompact (Icc (0 : ℝ) c ×ˢ Icc (-L) L) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hg.smooth.continuous.continuousOn
  refine ⟨L, max C₀ 0, le_max_right _ _, hL, fun p => ?_⟩
  by_cases hp : L ≤ |p.2|
  · rw [hL p hp, abs_zero]
    exact le_max_right _ _
  · push_neg at hp
    have hper : Function.Periodic (fun s : ℝ => g (s, p.2)) c := fun s => hg.periodic (s, p.2)
    obtain ⟨y, hy, hgy⟩ := hper.exists_mem_Ico₀ hc p.1
    have hgy' : g p = g (y, p.2) := hgy
    have hab := abs_lt.mp hp
    have hmem : (y, p.2) ∈ Icc (0 : ℝ) c ×ˢ Icc (-L) L :=
      ⟨⟨hy.1, hy.2.le⟩, ⟨hab.1.le, hab.2.le⟩⟩
    have hb := hC₀ (y, p.2) hmem
    rw [hgy', ← Real.norm_eq_abs]
    exact hb.trans (le_max_left _ _)

/-- Core Gaussian tail estimate for one planar convolution with a bounded stream that vanishes
for `|η| ≥ L`. -/
theorem heatConvTail_core {θ M L : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M) {g : ℝ × ℝ → ℝ}
    (hL : ∀ p : ℝ × ℝ, L ≤ |p.2| → g p = 0) (hbd : ∀ p : ℝ × ℝ, |g p| ≤ M) (z : ℝ × ℝ) :
    |∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * g (z - w)| ≤
      M * Real.sqrt 2 * Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) := by
  have hint := heatConvTail_plane_integrable hθ
  have hκ : 0 ≤ 1 / (8 * θ) := div_nonneg (by norm_num) (by linarith)
  have hE0 : 0 ≤ Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) := (Real.exp_pos _).le
  have hpt : ∀ w : ℝ × ℝ, ‖UnforcedLeray.B0284.heatKernel2 θ w * g (z - w)‖ ≤
      M * (Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) *
        (UnforcedLeray.B0284.heatKernel2 θ w * Real.exp ((1 / (8 * θ)) * w.2 ^ 2))) := by
    intro w
    have hK : 0 ≤ UnforcedLeray.B0284.heatKernel2 θ w :=
      UnforcedLeray.B0284.heatKernel2_nonneg hθ w
    have hEw : 0 ≤ Real.exp ((1 / (8 * θ)) * w.2 ^ 2) := (Real.exp_pos _).le
    have hRHS : 0 ≤ M * (Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) *
        (UnforcedLeray.B0284.heatKernel2 θ w * Real.exp ((1 / (8 * θ)) * w.2 ^ 2))) :=
      mul_nonneg hM (mul_nonneg hE0 (mul_nonneg hK hEw))
    by_cases hw : max 0 (|z.2| - L) ≤ |w.2|
    · have ha0 : 0 ≤ max 0 (|z.2| - L) := le_max_left _ _
      have hsq : (max 0 (|z.2| - L)) ^ 2 ≤ w.2 ^ 2 := by
        have h2 := mul_le_mul hw hw ha0 (abs_nonneg _)
        rw [← sq_abs w.2]
        nlinarith [h2]
      have hexp : 1 ≤ Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) *
          Real.exp ((1 / (8 * θ)) * w.2 ^ 2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have hnn : 0 ≤ (1 / (8 * θ)) * (w.2 ^ 2 - (max 0 (|z.2| - L)) ^ 2) :=
          mul_nonneg hκ (by linarith)
        have e : -((max 0 (|z.2| - L)) ^ 2) / (8 * θ) + (1 / (8 * θ)) * w.2 ^ 2 =
            (1 / (8 * θ)) * (w.2 ^ 2 - (max 0 (|z.2| - L)) ^ 2) := by
          ring
        linarith
      have hg' : |g (z - w)| ≤ M := hbd _
      have h3 : UnforcedLeray.B0284.heatKernel2 θ w * |g (z - w)| ≤
          UnforcedLeray.B0284.heatKernel2 θ w * M := mul_le_mul_of_nonneg_left hg' hK
      have h5 : M * 1 ≤ M * (Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) *
          Real.exp ((1 / (8 * θ)) * w.2 ^ 2)) := mul_le_mul_of_nonneg_left hexp hM
      have h6 : UnforcedLeray.B0284.heatKernel2 θ w * (M * 1) ≤
          UnforcedLeray.B0284.heatKernel2 θ w * (M * (Real.exp (-((max 0 (|z.2| - L)) ^ 2) /
            (8 * θ)) * Real.exp ((1 / (8 * θ)) * w.2 ^ 2))) := mul_le_mul_of_nonneg_left h5 hK
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
      nlinarith [h3, h6]
    · push_neg at hw
      have hlt : |w.2| < |z.2| - L := by
        rcases le_total 0 (|z.2| - L) with h | h
        · rw [max_eq_right h] at hw
          exact hw
        · rw [max_eq_left h] at hw
          linarith [abs_nonneg w.2]
      have hg0 : g (z - w) = 0 := by
        apply hL (z - w)
        show L ≤ |z.2 - w.2|
        have := abs_sub_abs_le_abs_sub z.2 w.2
        linarith
      rw [hg0, mul_zero, norm_zero]
      exact hRHS
  have hbint : Integrable (fun w : ℝ × ℝ => M * (Real.exp (-((max 0 (|z.2| - L)) ^ 2) /
      (8 * θ)) * (UnforcedLeray.B0284.heatKernel2 θ w *
        Real.exp ((1 / (8 * θ)) * w.2 ^ 2)))) :=
    (hint.const_mul _).const_mul _
  have h1 := norm_integral_le_of_norm_le hbint (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_const_mul, heatConvTail_plane_weight hθ,
    Real.norm_eq_abs] at h1
  calc |∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * g (z - w)|
      ≤ M * (Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) * Real.sqrt 2) := h1
    _ = M * Real.sqrt 2 * Real.exp (-((max 0 (|z.2| - L)) ^ 2) / (8 * θ)) := by ring

/-- **Leaf `PartII-b:T11/3/7`** (Gaussian `η`-tail of the heat flow of a bounded `η`-compact datum,
`HeatConvTail` of `Sub/T11_3.lean`). -/
theorem heatConvTail : UnforcedLeray.Short.IIb.HeatConvTail := by
  unfold HeatConvTail
  intro c ν g τ₂ hc hν hg hτ₂
  obtain ⟨L, M, hM, hL, hbd⟩ := heatConvTail_bounded hc hg
  refine ⟨2 * M, L, fun x hx0 hxτ => ?_⟩
  have hθ : 0 < ν * x.1 := mul_pos hν hx0
  have hθτ : ν * x.1 ≤ ν * τ₂ := mul_le_mul_of_nonneg_left hxτ hν.le
  unfold heatStreamH
  rw [if_pos hx0]
  refine (heatConvTail_core hθ hM hL hbd x.2).trans ?_
  have hB : 0 < 8 * (ν * x.1) := by linarith
  have hBC : 8 * (ν * x.1) ≤ 8 * ν * τ₂ := by nlinarith
  have hexp : Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * (ν * x.1))) ≤
      Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * ν * τ₂)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) hB hBC)
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hM2 : M * Real.sqrt 2 ≤ 2 * M := by
    have := mul_le_mul_of_nonneg_left hs hM
    linarith
  have hE1 : 0 ≤ Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * (ν * x.1))) :=
    (Real.exp_pos _).le
  calc M * Real.sqrt 2 * Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * (ν * x.1)))
      ≤ (2 * M) * Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * (ν * x.1))) :=
        mul_le_mul_of_nonneg_right hM2 hE1
    _ ≤ (2 * M) * Real.exp (-((max 0 (|x.2.2| - L)) ^ 2) / (8 * ν * τ₂)) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)

end UnforcedLeray.Short.IIb
