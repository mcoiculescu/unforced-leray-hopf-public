import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_5
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# `paramIntSmooth_proved` (PartIII-b:IIIb-D2/3/2/11/2/5, source 4177-4179)

Proves `ParamIntSmooth`: if `G` is `C^∞` on `{ρ > r₀}` and every derivative of `G` is bounded by
`C ρ^{-2}` for `ρ ≥ ρ₀` uniformly on compact sets of `(τ,z)`, then `-∫_{Ioi r} G(τ,ρ,z) dρ` is
`C^∞` on `{r > r₀}`.

Route: translate the lower limit (`∫_{Ioi r} G(ρ) = ∫_{Ioi 0} G(r + t)`), differentiate under the
integral with a dominating majorant `M (1 + |t|)^{-2}`, and induct on the order, using that the
derivative of the shifted integral is the shifted integral of `fderiv G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Derivative-bound package on `{ρ > r₀}`: for every order `n` and compact `K ⊆ (τ,z)`-plane
there are `ρ₀ ≥ 1`, `ρ₀ > r₀`, and `C` with `‖D^n G(τ,ρ,z)‖ ≤ C ρ^{-2}` for `ρ ≥ ρ₀`. -/
def PIS_Bnd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : ℝ × ℝ × ℝ → F) (r₀ : ℝ) :
    Prop :=
  ∀ (n : ℕ) (K : Set (ℝ × ℝ)), IsCompact K →
    ∃ ρ₀ C : ℝ, 1 ≤ ρ₀ ∧ r₀ < ρ₀ ∧
      ∀ τ z : ℝ, (τ, z) ∈ K → ∀ ρ : ℝ, ρ₀ ≤ ρ →
        ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ ≤ C / ρ ^ 2

theorem pis_add_c (x : ℝ × ℝ × ℝ) (t : ℝ) :
    x + ((0 : ℝ), t, (0 : ℝ)) = (x.1, x.2.1 + t, x.2.2) := by
  ext <;> simp

theorem pis_shift_Ioi {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) (s : ℝ) :
    ∫ ρ in Ioi s, g ρ = ∫ t in Ioi (0 : ℝ), g (s + t) := by
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ)) ((Ioi s).indicator g) s
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, ← h]
  congr 1
  ext t
  simp [Set.indicator_apply]

theorem pis_maj {E' : Type} [NormedAddCommGroup E'] (M S s t : ℝ) (c : E') (hM : 0 ≤ M) (hS : |s| ≤ S) (ht : 0 ≤ t)
    (hc : ‖c‖ ≤ M / (1 + |s + t|) ^ 2) :
    ‖c‖ ≤ M * (1 + S) ^ 2 * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hst0 : 0 ≤ |s + t| := abs_nonneg _
  have h0 : t ≤ |s + t| + |s| := by
    have := le_abs_self (s + t)
    have := neg_le_abs s
    linarith
  have h1 : 1 + t ≤ (1 + |s|) * (1 + |s + t|) := by
    nlinarith [mul_nonneg hs0 hst0]
  have hB : 0 < 1 + t := by linarith
  have hA : 0 < 1 + |s + t| := by linarith
  have hsq : (1 + t) ^ 2 ≤ ((1 + |s|) * (1 + |s + t|)) ^ 2 :=
    pow_le_pow_left₀ hB.le h1 2
  have hnt : (1 + ‖t‖) = 1 + t := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht]
  rw [hnt, Real.rpow_neg (by linarith), Real.rpow_two]
  have hS1 : (1 + |s|) ^ 2 ≤ (1 + S) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  calc ‖c‖ ≤ M / (1 + |s + t|) ^ 2 := hc
    _ ≤ M * (1 + |s|) ^ 2 / (1 + t) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : M * (1 + t) ^ 2 ≤ M * ((1 + |s|) * (1 + |s + t|)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hM
      nlinarith [this]
    _ ≤ M * (1 + S) ^ 2 / (1 + t) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hS1 hM
    _ = M * (1 + S) ^ 2 * ((1 + t) ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]

theorem pis_contT {Y : Type} [TopologicalSpace Y] (r₀ : ℝ) (x : ℝ × ℝ × ℝ)
    (hUmapsto : ∀ t : ℝ, 0 < t → x + ((0 : ℝ), t, (0 : ℝ)) ∈ {x : ℝ × ℝ × ℝ | r₀ < x.2.1})
    (ψ : ℝ × ℝ × ℝ → Y) (hψ : ContinuousOn ψ {x : ℝ × ℝ × ℝ | r₀ < x.2.1}) :
    ContinuousOn (fun t : ℝ => ψ (x + ((0 : ℝ), t, (0 : ℝ)))) (Ioi (0 : ℝ)) := by
  have hcomp : ContinuousOn (fun t : ℝ => x + ((0 : ℝ), t, (0 : ℝ))) (Ioi (0 : ℝ)) :=
    (continuous_const.add (by fun_prop)).continuousOn
  exact ContinuousOn.comp hψ hcomp (fun t ht => hUmapsto t ht)

theorem pis_ball_coords (x₀ x : ℝ × ℝ × ℝ) (δ : ℝ) (hx : x ∈ Metric.ball x₀ δ) :
    |x.1 - x₀.1| < δ ∧ |x.2.1 - x₀.2.1| < δ ∧ |x.2.2 - x₀.2.2| < δ := by
  simpa [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] using hx

theorem pis_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ × ℝ → F) (r₀ a : ℝ) (n : ℕ)
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G {x : ℝ × ℝ × ℝ | r₀ < x.2.1})
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hb : ∃ ρ₀ C : ℝ, 1 ≤ ρ₀ ∧ r₀ < ρ₀ ∧ ∀ τ z : ℝ, (τ, z) ∈ K → ∀ ρ : ℝ, ρ₀ ≤ ρ →
        ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ ≤ C / ρ ^ 2)
    (ha : r₀ < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ z : ℝ, (τ, z) ∈ K → ∀ ρ : ℝ, a ≤ ρ →
      ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ ≤ M / (1 + |ρ|) ^ 2 := by
  obtain ⟨ρ₀, C, hρ₁, hρr, hC⟩ := hb
  set b : ℝ := max a ρ₀ with hb_def
  set Kc : Set (ℝ × ℝ × ℝ) :=
    (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2, q.1.2)) '' (K ×ˢ Icc a b) with hKc_def
  have hKc : IsCompact Kc := by
    apply IsCompact.image (hK.prod isCompact_Icc)
    fun_prop
  have hKcU : Kc ⊆ {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := by
    rintro _ ⟨⟨τ, z⟩, ⟨_, hρ⟩, rfl⟩
    show r₀ < _
    exact lt_of_lt_of_le ha hρ.1
  have hcont : ContinuousOn (iteratedFDeriv ℝ n G) {x : ℝ × ℝ × ℝ | r₀ < x.2.1} :=
    ContinuousOn.continuousOn_iteratedFDeriv hG (isOpen_lt continuous_const (by fun_prop))
      (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKcU)
  set R : ℝ := |a| + |b| with hR
  refine ⟨|B| * (1 + R) ^ 2 + 4 * |C|, by positivity, ?_⟩
  intro τ z hτz ρ haρ
  by_cases hle : ρ ≤ b
  · have hmem : (τ, ρ, z) ∈ Kc := ⟨((τ, z), ρ), ⟨hτz, ⟨haρ, hle⟩⟩, rfl⟩
    have hnorm : ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ ≤ |B| :=
      (hB (τ, ρ, z) hmem).trans (le_abs_self B)
    have hρR : |ρ| ≤ R := by
      rw [abs_le]
      constructor
      · have := neg_abs_le a
        have := abs_nonneg b
        have := abs_nonneg a
        linarith
      · have := le_abs_self b
        have := abs_nonneg a
        linarith
    have h2 : (1 + |ρ|) ^ 2 ≤ (1 + R) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ * (1 + |ρ|) ^ 2
        ≤ |B| * (1 + R) ^ 2 :=
          mul_le_mul hnorm h2 (by positivity) (abs_nonneg _)
      _ ≤ |B| * (1 + R) ^ 2 + 4 * |C| := by linarith [abs_nonneg C]
  · have hbρ : b < ρ := not_le.mp hle
    have hρ0 : ρ₀ ≤ ρ := le_trans (le_max_right a ρ₀) hbρ.le
    have hρ1 : 1 ≤ ρ := le_trans hρ₁ hρ0
    have hnorm := hC τ z hτz ρ hρ0
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ)]
    have h3 : C / ρ ^ 2 ≤ 4 * |C| / (1 + ρ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hC1 : C * (1 + ρ) ^ 2 ≤ |C| * (1 + ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      have hC2 : |C| * (1 + ρ) ^ 2 ≤ |C| * (4 * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg C)
      nlinarith [hC1, hC2]
    have h4 : 4 * |C| / (1 + ρ) ^ 2 ≤ (|B| * (1 + R) ^ 2 + 4 * |C|) / (1 + ρ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (abs_nonneg B) (sq_nonneg (1 + R))]
    exact hnorm.trans (h3.trans h4)

theorem pis_core {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ × ℝ → F) (r₀ : ℝ)
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G {x : ℝ × ℝ × ℝ | r₀ < x.2.1})
    (hb : PIS_Bnd G r₀) (x₀ : ℝ × ℝ × ℝ) (hx₀ : r₀ < x₀.2.1) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => -∫ t in Ioi (0 : ℝ), G (x + ((0 : ℝ), t, (0 : ℝ))))
      (-∫ t in Ioi (0 : ℝ), fderiv ℝ G (x₀ + ((0 : ℝ), t, (0 : ℝ)))) x₀ := by
  have hUo : IsOpen {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := isOpen_lt continuous_const (by fun_prop)
  set δ : ℝ := min 1 ((x₀.2.1 - r₀) / 2) with hδ_def
  have hδpos : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ (x₀.2.1 - r₀) / 2 := min_le_right _ _
  set a : ℝ := x₀.2.1 - δ with ha_def
  have ha : r₀ < a := by linarith
  set S : ℝ := |x₀.2.1| + 1 with hS_def
  set K : Set (ℝ × ℝ) := Icc (x₀.1 - 1) (x₀.1 + 1) ×ˢ Icc (x₀.2.2 - 1) (x₀.2.2 + 1) with hK_def
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M0, hM0, hM0b⟩ := pis_bound G r₀ a 0 hG K hK (hb 0 K hK) ha
  obtain ⟨M1, hM1, hM1b⟩ := pis_bound G r₀ a 1 hG K hK (hb 1 K hK) ha
  have hnormfd : ∀ y : ℝ × ℝ × ℝ, ‖fderiv ℝ G y‖ = ‖iteratedFDeriv ℝ 1 G y‖ := by
    intro y
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := G) (x := y) (n := 0)
    simpa using this
  -- majorants on the ball
  have hmemK : ∀ x ∈ Metric.ball x₀ δ, (x.1, x.2.2) ∈ K := by
    intro x hx
    obtain ⟨h1, _, h3⟩ := pis_ball_coords x₀ x δ hx
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hSbound : ∀ x ∈ Metric.ball x₀ δ, |x.2.1| ≤ S := by
    intro x hx
    obtain ⟨_, h2, _⟩ := pis_ball_coords x₀ x δ hx
    have := abs_sub_abs_le_abs_sub x.2.1 x₀.2.1
    have := (abs_lt.mp h2).2
    have := (abs_lt.mp h2).1
    linarith
  have hρa : ∀ x ∈ Metric.ball x₀ δ, ∀ t : ℝ, 0 ≤ t → a ≤ x.2.1 + t := by
    intro x hx t ht
    obtain ⟨_, h2, _⟩ := pis_ball_coords x₀ x δ hx
    have := (abs_lt.mp h2).1
    linarith
  have hmajD : ∀ x ∈ Metric.ball x₀ δ, ∀ t : ℝ, 0 < t →
      ‖fderiv ℝ G (x + ((0 : ℝ), t, (0 : ℝ)))‖ ≤ M1 * (1 + S) ^ 2 * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
    intro x hx t ht
    have hb1 := hM1b x.1 x.2.2 (hmemK x hx) (x.2.1 + t) (hρa x hx t ht.le)
    rw [pis_add_c, hnormfd]
    exact pis_maj M1 S x.2.1 t _ hM1 (hSbound x hx) ht.le hb1
  have hmajF : ∀ x ∈ Metric.ball x₀ δ, ∀ t : ℝ, 0 < t →
      ‖G (x + ((0 : ℝ), t, (0 : ℝ)))‖ ≤ M0 * (1 + S) ^ 2 * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
    intro x hx t ht
    have hb0 := hM0b x.1 x.2.2 (hmemK x hx) (x.2.1 + t) (hρa x hx t ht.le)
    rw [pis_add_c, ← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := G)]
    exact pis_maj M0 S x.2.1 t _ hM0 (hSbound x hx) ht.le hb0
  have hintg : ∀ c : ℝ, Integrable (fun t : ℝ => c * (1 + ‖t‖) ^ (-(2 : ℝ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro c
    have h := integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := 2) (by norm_num)
    exact (h.const_mul c).restrict
  -- continuity of the integrands on (0,∞)
  have hUmapsto : ∀ x ∈ {x : ℝ × ℝ × ℝ | r₀ < x.2.1}, ∀ t : ℝ, 0 < t →
      x + ((0 : ℝ), t, (0 : ℝ)) ∈ {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := by
    intro x hx t ht
    show r₀ < (x + ((0 : ℝ), t, (0 : ℝ))).2.1
    have : (x + ((0 : ℝ), t, (0 : ℝ))).2.1 = x.2.1 + t := by simp
    rw [this]
    have : r₀ < x.2.1 := hx
    linarith
  have hcontT : ∀ x ∈ {x : ℝ × ℝ × ℝ | r₀ < x.2.1}, ∀ {Y : Type} [TopologicalSpace Y]
      (ψ : ℝ × ℝ × ℝ → Y), ContinuousOn ψ {x : ℝ × ℝ × ℝ | r₀ < x.2.1} →
      ContinuousOn (fun t : ℝ => ψ (x + ((0 : ℝ), t, (0 : ℝ)))) (Ioi (0 : ℝ)) :=
    fun x hx Y _ ψ hψ => pis_contT r₀ x (hUmapsto x hx) ψ hψ
  have hGcont : ContinuousOn G {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := hG.continuousOn
  have hn1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hDcont : ContinuousOn (fderiv ℝ G) {x : ℝ × ℝ × ℝ | r₀ < x.2.1} :=
    hG.continuousOn_fderiv_of_isOpen hUo hn1
  have hs : Metric.ball x₀ δ ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ hδpos
  have hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun t : ℝ => G (x + ((0 : ℝ), t, (0 : ℝ))))
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hUo.mem_nhds hx₀] with x hx
    exact (hcontT x hx G hGcont).aestronglyMeasurable measurableSet_Ioi
  have hF_int : Integrable (fun t : ℝ => G (x₀ + ((0 : ℝ), t, (0 : ℝ))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' (hintg (M0 * (1 + S) ^ 2))
      ((hcontT x₀ hx₀ G hGcont).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hmajF x₀ (Metric.mem_ball_self hδpos) t ht
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => fderiv ℝ G (x₀ + ((0 : ℝ), t, (0 : ℝ))))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (hcontT x₀ hx₀ (fderiv ℝ G) hDcont).aestronglyMeasurable measurableSet_Ioi
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Metric.ball x₀ δ,
      ‖fderiv ℝ G (x + ((0 : ℝ), t, (0 : ℝ)))‖ ≤ M1 * (1 + S) ^ 2 * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x hx
    exact hmajD x hx t ht
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Metric.ball x₀ δ,
      HasFDerivAt (fun y : ℝ × ℝ × ℝ => G (y + ((0 : ℝ), t, (0 : ℝ))))
        (fderiv ℝ G (x + ((0 : ℝ), t, (0 : ℝ)))) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x hx
    have hxU : x ∈ {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := by
      obtain ⟨_, h2, _⟩ := pis_ball_coords x₀ x δ hx
      have := (abs_lt.mp h2).1
      show r₀ < x.2.1
      linarith
    have hmem := hUmapsto x hxU t ht
    have hd : DifferentiableAt ℝ G (x + ((0 : ℝ), t, (0 : ℝ))) :=
      (hG.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hmem)
    have hadd : HasFDerivAt (fun y : ℝ × ℝ × ℝ => y + ((0 : ℝ), t, (0 : ℝ)))
        (ContinuousLinearMap.id ℝ (ℝ × ℝ × ℝ)) x := (hasFDerivAt_id x).add_const _
    have h2 := hd.hasFDerivAt.comp x hadd
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y (t : ℝ) => G (y + ((0 : ℝ), t, (0 : ℝ))))
    (F' := fun y (t : ℝ) => fderiv ℝ G (y + ((0 : ℝ), t, (0 : ℝ))))
    (x₀ := x₀) (s := Metric.ball x₀ δ) hs hF_meas hF_int hF'_meas h_bound
    (hintg (M1 * (1 + S) ^ 2)) h_diff
  exact key.neg

theorem pis_ind (n : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ × ℝ → F) (r₀ : ℝ),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G {x : ℝ × ℝ × ℝ | r₀ < x.2.1} →
    PIS_Bnd G r₀ →
    ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => -∫ t in Ioi (0 : ℝ), G (x + ((0 : ℝ), t, (0 : ℝ))))
      {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := by
  induction n with
  | zero =>
    intro F _ _ G r₀ hG hb
    rw [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    exact (pis_core G r₀ hG hb x hx).differentiableAt.continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ G r₀ hG hb
    have hU : IsOpen {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := isOpen_lt continuous_const (by fun_prop)
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (pis_core G r₀ hG hb x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hG' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ G) {x : ℝ × ℝ × ℝ | r₀ < x.2.1} :=
      hG.fderiv_of_isOpen hU (by simp)
    have hb' : PIS_Bnd (fderiv ℝ G) r₀ := by
      intro m K hK
      obtain ⟨ρ₀, C, h1, h2, h3⟩ := hb (m + 1) K hK
      refine ⟨ρ₀, C, h1, h2, fun τ z hτz ρ hρ => ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact h3 τ z hτz ρ hρ
    refine (ih (fderiv ℝ G) r₀ hG' hb').congr ?_
    intro x hx
    exact (pis_core G r₀ hG hb x hx).fderiv

theorem paramIntSmooth_proved : ParamIntSmooth := by
  intro G r₀ hG hb
  have hH := contDiffOn_infty.2 (fun n => pis_ind n G r₀ hG hb)
  refine hH.congr ?_
  intro x _
  show -∫ ρ in Ioi x.2.1, G (x.1, ρ, x.2.2) = -∫ t in Ioi (0 : ℝ), G (x + ((0 : ℝ), t, (0 : ℝ)))
  have hfun : (fun t : ℝ => G (x.1, x.2.1 + t, x.2.2)) =
      (fun t : ℝ => G (x + ((0 : ℝ), t, (0 : ℝ)))) := by
    funext t
    rw [pis_add_c x t]
  have hshift : ∫ ρ in Ioi x.2.1, G (x.1, ρ, x.2.2) =
      ∫ t in Ioi (0 : ℝ), G (x.1, x.2.1 + t, x.2.2) :=
    pis_shift_Ioi (fun ρ : ℝ => G (x.1, ρ, x.2.2)) x.2.1
  rw [hshift, hfun]

end UnforcedLeray.Short.PartIIIb.Concrete
