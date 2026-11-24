import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.WeightGrad

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

set_option maxHeartbeats 800000

namespace CutPointAux

lemma ladCut_diff (R : ℝ) : Differentiable ℝ (ladCut R) := by
  have : ContDiff ℝ ∞ (ladCut R) := by
    unfold ladCut
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  exact this.differentiable (by simp)

lemma jb_rpow_diff (m : ℝ) : Differentiable ℝ (fun y : ℝ × ℝ => B0579.jb y ^ (-m)) := by
  intro x
  have h : DifferentiableAt ℝ B0579.jb x := by
    have : B0579.jb = fun y : ℝ × ℝ => 1 + y.1 ^ 2 + y.2 ^ 2 := by
      funext y; simp [B0579.jb]
    rw [this]; fun_prop
  exact h.rpow_const (Or.inl (B0579.jb_pos x).ne')

/-- (1): the weight derivative bound. -/
lemma pd_cutWeight_le (K₁ m R : ℝ) (hK₁ : 0 ≤ K₁) (hR : 1 ≤ R)
    (hK : ∀ (x : ℝ × ℝ) (j : Fin 2), |B0579.pd j (ladCut R) x| ≤ K₁ / R)
    (x : ℝ × ℝ) (k : Fin 2) :
    |B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x| ≤
      (2 * K₁ + 2 * |m|) * (ladCut R x * B0579.jb x ^ (-m)) := by
  have hfun : (fun y : ℝ × ℝ => ladCut R y ^ 2 * B0579.jb y ^ (-m)) =
      fun y => (ladCut R y * ladCut R y) * B0579.jb y ^ (-m) := by
    funext y; ring
  have hd1 : Differentiable ℝ (fun y => ladCut R y * ladCut R y) :=
    (ladCut_diff R).mul (ladCut_diff R)
  rw [hfun, B0579.pd_mul hd1 (jb_rpow_diff m) k x,
    B0579.pd_mul (ladCut_diff R) (ladCut_diff R) k x]
  have hw : 0 < B0579.jb x ^ (-m) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
  have hwg : |B0579.pd k (fun y => B0579.jb y ^ (-m)) x| ≤ 2 * |m| * B0579.jb x ^ (-m) :=
    adjWeightGrad m x k
  obtain ⟨K, hK0, hKp⟩ := ladCutProps
  obtain ⟨z0, z1, -⟩ := (hKp (max R 1) (by positivity))
  have hz : 0 ≤ ladCut R x ∧ ladCut R x ≤ 1 := by
    have := ladCutProps
    -- directly from the smooth transition
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  obtain ⟨hz0, hz1⟩ := hz
  have hpk : |B0579.pd k (ladCut R) x| ≤ K₁ := by
    refine (hK x k).trans ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set ζ := ladCut R x
  set p := B0579.pd k (ladCut R) x
  set w := B0579.jb x ^ (-m)
  set q := B0579.pd k (fun y => B0579.jb y ^ (-m)) x
  have e1 : |(p * ζ + ζ * p) * w + (ζ * ζ) * q| ≤
      (|p| * ζ + ζ * |p|) * w + (ζ * ζ) * |q| := by
    calc _ ≤ |(p * ζ + ζ * p) * w| + |(ζ * ζ) * q| := abs_add_le _ _
      _ = (|p| * ζ + ζ * |p|) * w + (ζ * ζ) * |q| := by
        simp only [abs_mul, abs_of_nonneg hz0, abs_of_pos hw]
        have : |p * ζ + ζ * p| = 2 * (|p| * ζ) := by
          rw [show p * ζ + ζ * p = 2 * (p * ζ) by ring, abs_mul, abs_mul,
            abs_of_nonneg hz0, abs_two]
        rw [this]; ring
  refine e1.trans ?_
  have hζζ : ζ * ζ ≤ ζ := by nlinarith
  have : (|p| * ζ + ζ * |p|) * w ≤ 2 * K₁ * (ζ * w) := by
    have : |p| * ζ ≤ K₁ * ζ := mul_le_mul_of_nonneg_right hpk hz0
    nlinarith [mul_nonneg hz0 hw.le]
  have h2 : (ζ * ζ) * |q| ≤ ζ * (2 * |m| * w) := by
    have := mul_le_mul hζζ hwg (abs_nonneg _) hz0
    exact this
  nlinarith [mul_nonneg hz0 hw.le]

/-- Young: `2 s p q ≤ ε s p² + s q²/ε`. -/
lemma young (s p q ε : ℝ) (hs : 0 ≤ s) (hε : 0 < ε) :
    2 * (s * (p * q)) ≤ ε * (s * p ^ 2) + (s * q ^ 2) / ε := by
  rw [← sub_nonneg]
  have : ε * (s * p ^ 2) + (s * q ^ 2) / ε - 2 * (s * (p * q)) = s * (ε * p - q) ^ 2 / ε := by
    field_simp; ring
  rw [this]; positivity

lemma re_conj_le (a b : ℂ) : |((starRingEnd ℂ) a * b).re| ≤ ‖a‖ * ‖b‖ := by
  calc _ ≤ ‖(starRingEnd ℂ) a * b‖ := Complex.abs_re_le_norm _
    _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]

/-- The real-variable arithmetic of the Young estimate. -/
lemma core_real (ν CV K₂ ζ w D X G0 G1 Y : ℝ) (hν : 0 < ν) (hCV : 0 ≤ CV) (hK₂ : 0 ≤ K₂)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hw : 0 ≤ w) (hD : 0 ≤ D) (hX : 0 ≤ X) (hG0 : 0 ≤ G0)
    (hG1 : 0 ≤ G1) (hY0 : 0 ≤ Y) (hYsq : Y ^ 2 ≤ 2 * X ^ 2 + 4 * CV ^ 2 * (G0 ^ 2 + G1 ^ 2)) :
    2 * (ζ ^ 2 * w * (D * Y)) + (2 * (K₂ * ζ * w * (G0 * (Y + ν * D))) +
      2 * (K₂ * ζ * w * (G1 * (Y + ν * D)))) ≤
      ν * (ζ ^ 2 * w * D ^ 2) +
        ((4 / ν + 4 * K₂) * (1 + 2 * CV ^ 2) + 8 * ν * K₂ ^ 2 + K₂) *
          (w * X ^ 2 + w * G0 ^ 2 + w * G1 ^ 2) := by
  set s : ℝ := ζ ^ 2 * w with hs
  have hs0 : 0 ≤ s := by positivity
  set K' := (4 / ν + 4 * K₂) * (1 + 2 * CV ^ 2) + 8 * ν * K₂ ^ 2 + K₂ with hK'
  have y1 := young s D Y (ν / 2) hs0 (by positivity)
  have yk : ∀ G : ℝ, 0 ≤ G → 2 * (w * ((ζ * D) * (K₂ * ν * G))) ≤
      (ν / 8) * (s * D ^ 2) + 8 * ν * K₂ ^ 2 * (w * G ^ 2) := by
    intro G hG
    have := young w (ζ * D) (K₂ * ν * G) (ν / 8) hw (by positivity)
    have e : (w * (K₂ * ν * G) ^ 2) / (ν / 8) = 8 * ν * K₂ ^ 2 * (w * G ^ 2) := by
      field_simp
    rw [e] at this
    have e2 : ν / 8 * (w * (ζ * D) ^ 2) = (ν / 8) * (s * D ^ 2) := by rw [hs]; ring
    rw [e2] at this
    exact this
  have y0 := yk G0 hG0
  have y1' := yk G1 hG1
  have zk : ∀ G : ℝ, 0 ≤ G → 2 * (K₂ * ζ * w * (G * Y)) ≤ K₂ * (w * G ^ 2) + K₂ * (w * Y ^ 2) := by
    intro G hG
    have h0 : ζ * (2 * (G * Y)) ≤ 1 * (2 * (G * Y)) :=
      mul_le_mul_of_nonneg_right hζ1 (by positivity)
    have h1 : ζ * (2 * (G * Y)) ≤ G ^ 2 + Y ^ 2 := by
      nlinarith [sq_nonneg (G - Y)]
    have : 0 ≤ K₂ * w := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 this
    have e : 2 * (K₂ * ζ * w * (G * Y)) = K₂ * w * (ζ * (2 * (G * Y))) := by ring
    have e' : K₂ * w * (G ^ 2 + Y ^ 2) = K₂ * (w * G ^ 2) + K₂ * (w * Y ^ 2) := by ring
    linarith
  have z0 := zk G0 hG0
  have z1 := zk G1 hG1
  have sY : s * Y ^ 2 ≤ w * Y ^ 2 := by
    have : ζ ^ 2 ≤ 1 := by nlinarith
    rw [hs]; nlinarith [mul_nonneg hw (sq_nonneg Y)]
  have e1 : (s * Y ^ 2) / (ν / 2) = (2 / ν) * (s * Y ^ 2) := by field_simp
  rw [e1] at y1
  have hc0 : 0 ≤ 2 / ν + 2 * K₂ := by positivity
  have hu : w * Y ^ 2 ≤ 2 * (w * X ^ 2) + 4 * CV ^ 2 * (w * G0 ^ 2 + w * G1 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hYsq hw
    refine this.trans (le_of_eq ?_)
    ring
  have hsu : (2 / ν) * (s * Y ^ 2) ≤ (2 / ν) * (w * Y ^ 2) :=
    mul_le_mul_of_nonneg_left sY (by positivity)
  have T1 : 2 * (s * (D * Y)) + (2 * (K₂ * ζ * w * (G0 * (Y + ν * D))) +
      2 * (K₂ * ζ * w * (G1 * (Y + ν * D)))) ≤
      (3 * ν / 4) * (s * D ^ 2) + (2 / ν) * (s * Y ^ 2) +
        8 * ν * K₂ ^ 2 * (w * G0 ^ 2 + w * G1 ^ 2) + K₂ * (w * G0 ^ 2 + w * G1 ^ 2) +
        2 * (K₂ * (w * Y ^ 2)) := by
    linarith [y0, y1', y1, z0, z1]
  have T2 : (2 / ν) * (s * Y ^ 2) + 2 * (K₂ * (w * Y ^ 2)) ≤
      (2 / ν + 2 * K₂) * (2 * (w * X ^ 2) + 4 * CV ^ 2 * (w * G0 ^ 2 + w * G1 ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hu hc0
    have : (2 / ν + 2 * K₂) * (w * Y ^ 2) = (2 / ν) * (w * Y ^ 2) + 2 * (K₂ * (w * Y ^ 2)) := by
      ring
    linarith
  have T3 : (2 / ν + 2 * K₂) * (2 * (w * X ^ 2) + 4 * CV ^ 2 * (w * G0 ^ 2 + w * G1 ^ 2)) +
      (8 * ν * K₂ ^ 2 * (w * G0 ^ 2 + w * G1 ^ 2) + K₂ * (w * G0 ^ 2 + w * G1 ^ 2)) ≤
      K' * (w * X ^ 2 + w * G0 ^ 2 + w * G1 ^ 2) := by
    have hK'e : K' = 2 * (2 / ν + 2 * K₂) +
        (4 * (2 / ν + 2 * K₂) * CV ^ 2 + 8 * ν * K₂ ^ 2 + K₂) := by
      rw [hK']; ring
    have h1 : 0 ≤ (4 * (2 / ν + 2 * K₂) * CV ^ 2 + 8 * ν * K₂ ^ 2 + K₂) * (w * X ^ 2) := by
      positivity
    have h2 : 0 ≤ (2 * (2 / ν + 2 * K₂)) * (w * G0 ^ 2 + w * G1 ^ 2) := by positivity
    rw [hK'e]
    linarith [h1, h2]
  have e3 : (3 * ν / 4) * (s * D ^ 2) ≤ ν * (s * D ^ 2) := by
    have : 0 ≤ s * D ^ 2 := by positivity
    nlinarith
  have e4 : ζ ^ 2 * w * (D * Y) = s * (D * Y) := by rw [hs]
  have e5 : ζ ^ 2 * w * D ^ 2 = s * D ^ 2 := by rw [hs]
  rw [e4, e5]
  linarith [T1, T2, T3, e3, hsu]

/-- (2): the algebraic Young estimate. -/
lemma cut_pointwise_young (ν CV K₂ ζ χ2 w V0 V1 : ℝ) (hν : 0 < ν) (hCV : 0 ≤ CV)
    (hK₂ : 0 ≤ K₂) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζχ : ζ ≠ 0 → χ2 = 1) (hw : 0 ≤ w)
    (hV0 : |V0| ≤ CV) (hV1 : |V1| ≤ CV) (d0 d1 : ℝ) (hd0 : |d0| ≤ K₂ * ζ * w)
    (hd1 : |d1| ≤ K₂ * ζ * w) (z g0 g1 χv : ℂ) :
    |-(2 * (ζ ^ 2 * (w * ((starRingEnd ℂ) z * (χv - (ν : ℂ) * z -
          ((V0 : ℂ) * g0 + (V1 : ℂ) * g1))).re))) -
        2 * (d0 * ((starRingEnd ℂ) g0 * (χv - (ν : ℂ) * z -
          ((V0 : ℂ) * g0 + (V1 : ℂ) * g1))).re +
          d1 * ((starRingEnd ℂ) g1 * (χv - (ν : ℂ) * z -
          ((V0 : ℂ) * g0 + (V1 : ℂ) * g1))).re) - 2 * ν * (ζ ^ 2 * (w * ‖z‖ ^ 2))| ≤
      ν * (ζ ^ 2 * (w * ‖z‖ ^ 2)) +
        ((4 / ν + 4 * K₂) * (1 + 2 * CV ^ 2) + 8 * ν * K₂ ^ 2 + K₂) *
          (w * ‖χv‖ ^ 2 + χ2 ^ 2 * (w * ‖g0‖ ^ 2) + χ2 ^ 2 * (w * ‖g1‖ ^ 2)) := by
  set K' := (4 / ν + 4 * K₂) * (1 + 2 * CV ^ 2) + 8 * ν * K₂ ^ 2 + K₂ with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hX := norm_nonneg χv
  have hD := norm_nonneg z
  have hG0 := norm_nonneg g0
  have hG1 := norm_nonneg g1
  by_cases hz : ζ = 0
  · have h0 : d0 = 0 := by
      have := hd0; rw [hz] at this; simpa using this
    have h1 : d1 = 0 := by
      have := hd1; rw [hz] at this; simpa using this
    rw [hz, h0, h1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      neg_zero, sub_zero, zero_add, abs_zero]
    have : 0 ≤ w * ‖χv‖ ^ 2 + χ2 ^ 2 * (w * ‖g0‖ ^ 2) + χ2 ^ 2 * (w * ‖g1‖ ^ 2) := by positivity
    positivity
  have hχ2 : χ2 = 1 := hζχ hz
  subst hχ2
  simp only [one_pow, one_mul]
  set Tc : ℂ := (V0 : ℂ) * g0 + (V1 : ℂ) * g1 with hTc
  set T' := ‖Tc‖ with hT'
  have hT'le : T' ≤ CV * (‖g0‖ + ‖g1‖) := by
    calc T' ≤ ‖(V0 : ℂ) * g0‖ + ‖(V1 : ℂ) * g1‖ := norm_add_le _ _
      _ = |V0| * ‖g0‖ + |V1| * ‖g1‖ := by
        simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ CV * ‖g0‖ + CV * ‖g1‖ := by gcongr
      _ = _ := by ring
  have hT'0 : 0 ≤ T' := norm_nonneg _
  have hT'sq : T' ^ 2 ≤ 2 * CV ^ 2 * (‖g0‖ ^ 2 + ‖g1‖ ^ 2) := by
    have h1 : T' ^ 2 ≤ (CV * (‖g0‖ + ‖g1‖)) ^ 2 := pow_le_pow_left₀ hT'0 hT'le 2
    nlinarith [sq_nonneg (‖g0‖ - ‖g1‖), sq_nonneg CV]
  set Y := ‖χv‖ + T' with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYsq : Y ^ 2 ≤ 2 * ‖χv‖ ^ 2 + 4 * CV ^ 2 * (‖g0‖ ^ 2 + ‖g1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖χv‖ - T')]
  set S := ‖g0‖ ^ 2 + ‖g1‖ ^ 2 with hS
  -- decompose
  set F : ℂ := χv - (ν : ℂ) * z - Tc with hF
  have hFn : ‖F‖ ≤ Y + ν * ‖z‖ := by
    have : F = (χv - Tc) - (ν : ℂ) * z := by rw [hF]; ring
    rw [this]
    calc _ ≤ ‖χv - Tc‖ + ‖(ν : ℂ) * z‖ := norm_sub_le _ _
      _ ≤ (‖χv‖ + ‖Tc‖) + ν * ‖z‖ := by
        gcongr
        · exact norm_sub_le _ _
        · simp [norm_mul, Complex.norm_real, abs_of_pos hν]
  have hre : ((starRingEnd ℂ) z * F).re =
      ((starRingEnd ℂ) z * (χv - Tc)).re - ν * ‖z‖ ^ 2 := by
    have : F = (χv - Tc) - (ν : ℂ) * z := by rw [hF]; ring
    rw [this, mul_sub, Complex.sub_re]
    congr 1
    have : (starRingEnd ℂ) z * ((ν : ℂ) * z) = ((ν * ‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [show (starRingEnd ℂ) z * ((ν : ℂ) * z) = (ν : ℂ) * ((starRingEnd ℂ) z * z) by ring,
        Complex.conj_mul']
      push_cast; ring
    rw [this, Complex.ofReal_re]
  set s : ℝ := ζ ^ 2 * w with hs
  have hs0 : 0 ≤ s := by positivity
  set P1 := ((starRingEnd ℂ) z * (χv - Tc)).re with hP1
  have hP1b : |P1| ≤ ‖z‖ * Y := by
    refine (re_conj_le _ _).trans ?_
    gcongr
    exact (norm_sub_le _ _)
  -- the main identity
  have hmain : -(2 * (ζ ^ 2 * (w * ((starRingEnd ℂ) z * F).re))) - 2 * ν * (ζ ^ 2 * (w * ‖z‖ ^ 2))
      = -(2 * (s * P1)) := by
    rw [hre, hs]; ring
  -- bound on d-terms
  have hdk : ∀ (d : ℝ) (g : ℂ), |d| ≤ K₂ * ζ * w →
      |d * ((starRingEnd ℂ) g * F).re| ≤ K₂ * ζ * w * (‖g‖ * (Y + ν * ‖z‖)) := by
    intro d g hd
    rw [abs_mul]
    calc |d| * |((starRingEnd ℂ) g * F).re| ≤ (K₂ * ζ * w) * (‖g‖ * ‖F‖) :=
          mul_le_mul hd ((re_conj_le _ _).trans le_rfl) (abs_nonneg _) (by positivity)
      _ ≤ _ := by gcongr
  have hd0b := hdk d0 g0 hd0
  have hd1b := hdk d1 g1 hd1
  have hE : ζ ^ 2 * (w * ‖z‖ ^ 2) = s * ‖z‖ ^ 2 := by rw [hs]; ring
  -- Young pieces
  have y1 := young s ‖z‖ Y (ν / 2) hs0 (by positivity)
  have yk : ∀ G : ℝ, 0 ≤ G → 2 * (w * ((ζ * ‖z‖) * (K₂ * ν * G))) ≤
      (ν / 8) * (s * ‖z‖ ^ 2) + 8 * ν * K₂ ^ 2 * (w * G ^ 2) := by
    intro G hG
    have := young w (ζ * ‖z‖) (K₂ * ν * G) (ν / 8) hw (by positivity)
    have e : (w * (K₂ * ν * G) ^ 2) / (ν / 8) = 8 * ν * K₂ ^ 2 * (w * G ^ 2) := by
      field_simp
    rw [e] at this
    have e2 : ν / 8 * (w * (ζ * ‖z‖) ^ 2) = (ν / 8) * (s * ‖z‖ ^ 2) := by rw [hs]; ring
    rw [e2] at this
    exact this
  have y0 := yk ‖g0‖ hG0
  have y1' := yk ‖g1‖ hG1
  have zk : ∀ G : ℝ, 0 ≤ G → 2 * (K₂ * ζ * w * (G * Y)) ≤ K₂ * (w * G ^ 2) + K₂ * (w * Y ^ 2) := by
    intro G hG
    have h0 : ζ * (2 * (G * Y)) ≤ 1 * (2 * (G * Y)) :=
      mul_le_mul_of_nonneg_right hζ1 (by positivity)
    have h1 : ζ * (2 * (G * Y)) ≤ G ^ 2 + Y ^ 2 := by
      nlinarith [sq_nonneg (G - Y)]
    have : 0 ≤ K₂ * w := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 this
    have e : 2 * (K₂ * ζ * w * (G * Y)) = K₂ * w * (ζ * (2 * (G * Y))) := by ring
    have e' : K₂ * w * (G ^ 2 + Y ^ 2) = K₂ * (w * G ^ 2) + K₂ * (w * Y ^ 2) := by ring
    linarith
  have z0 := zk ‖g0‖ hG0
  have z1 := zk ‖g1‖ hG1
  have sY : s * Y ^ 2 ≤ w * Y ^ 2 := by
    have : ζ ^ 2 ≤ 1 := by nlinarith
    rw [hs]; nlinarith [mul_nonneg hw (sq_nonneg Y)]
  -- assemble
  have hA : |-(2 * (s * P1))| ≤ 2 * (s * (‖z‖ * Y)) := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hs0]
    nlinarith [mul_le_mul_of_nonneg_left hP1b hs0]
  have hBd : |2 * (d0 * ((starRingEnd ℂ) g0 * F).re + d1 * ((starRingEnd ℂ) g1 * F).re)| ≤
      2 * (K₂ * ζ * w * (‖g0‖ * (Y + ν * ‖z‖))) + 2 * (K₂ * ζ * w * (‖g1‖ * (Y + ν * ‖z‖))) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have := (abs_add_le _ _).trans (add_le_add hd0b hd1b)
    linarith
  -- the final
  have hsplit : -(2 * (ζ ^ 2 * (w * ((starRingEnd ℂ) z * F).re))) -
        2 * (d0 * ((starRingEnd ℂ) g0 * F).re + d1 * ((starRingEnd ℂ) g1 * F).re) -
        2 * ν * (ζ ^ 2 * (w * ‖z‖ ^ 2)) =
      -(2 * (s * P1)) - 2 * (d0 * ((starRingEnd ℂ) g0 * F).re + d1 * ((starRingEnd ℂ) g1 * F).re) := by
    rw [← hmain]; ring
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have hcore : 2 * (s * (‖z‖ * Y)) + (2 * (K₂ * ζ * w * (‖g0‖ * (Y + ν * ‖z‖))) +
      2 * (K₂ * ζ * w * (‖g1‖ * (Y + ν * ‖z‖)))) ≤
      ν * (s * ‖z‖ ^ 2) + K' * (w * ‖χv‖ ^ 2 + w * ‖g0‖ ^ 2 + w * ‖g1‖ ^ 2) := by
    have := core_real ν CV K₂ ζ w ‖z‖ ‖χv‖ ‖g0‖ ‖g1‖ Y hν hCV hK₂ hζ0 hζ1 hw hD hX hG0 hG1 hY0
      (by rw [hS] at hYsq; exact hYsq)
    exact this
  rw [hE]
  linarith [hA, hBd, hcore]

end CutPointAux

open CutPointAux in
theorem cutRatePointwise : UnforcedLeray.Short.IIIa.CutRatePointwise := by
  intro m ν CV hν
  obtain ⟨K₁, hK₁0, hKp⟩ := ladCutProps
  set K₂ : ℝ := 2 * K₁ + 2 * |m| with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨(4 / ν + 4 * K₂) * (1 + 2 * CV ^ 2) + 8 * ν * K₂ ^ 2 + K₂, ?_, ?_⟩
  · have : 0 ≤ CV ^ 2 := sq_nonneg CV
    positivity
  intro c R Φ χ F V hc hR hΦ hV hF x hx
  have hR0 : 0 < R := by linarith
  have hCV : 0 ≤ CV := le_trans (abs_nonneg _) (hV x hx 0)
  have hw : 0 ≤ B0579.jb x ^ (-m) := (Real.rpow_pos_of_pos (B0579.jb_pos x) _).le
  have hz01 : 0 ≤ ladCut R x ∧ ladCut R x ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hζχ : ladCut R x ≠ 0 → ladCut (2 * R) x = 1 := by
    intro hne
    have h2 : x.2 ^ 2 < 2 * R ^ 2 := by
      by_contra h
      exact hne ((hKp R hR0).2.2.2.1 x (not_lt.1 h))
    exact ((hKp (2 * R) (by linarith)).2.2.1 x (by nlinarith))
  have hd : ∀ k : Fin 2, |B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x| ≤
      K₂ * ladCut R x * B0579.jb x ^ (-m) := fun k => by
    have := pd_cutWeight_le K₁ m R hK₁0 hR (fun x j => (hKp R hR0).2.2.2.2.1 x j) x k
    rw [hK₂]; linarith
  have key := cut_pointwise_young ν CV K₂ (ladCut R x) (ladCut (2 * R) x) (B0579.jb x ^ (-m))
    (V x 0) (V x 1) hν hCV hK₂0 hz01.1 hz01.2 hζχ hw (hV x hx 0) (hV x hx 1) _ _ (hd 0) (hd 1)
    (ladLapCx Φ x) (pdCx 0 Φ x) (pdCx 1 Φ x) (χ x)
  have hFx := hF x
  have hA : cutRateIntegrand c m R Φ F x =
      -(2 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (ladLapCx Φ x) *
        (χ x - (ν : ℂ) * ladLapCx Φ x - ((V x 0 : ℂ) * pdCx 0 Φ x + (V x 1 : ℂ) * pdCx 1 Φ x))).re))) -
      2 * (B0579.pd 0 (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx 0 Φ x) * (χ x - (ν : ℂ) * ladLapCx Φ x -
            ((V x 0 : ℂ) * pdCx 0 Φ x + (V x 1 : ℂ) * pdCx 1 Φ x))).re +
        B0579.pd 1 (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx 1 Φ x) * (χ x - (ν : ℂ) * ladLapCx Φ x -
            ((V x 0 : ℂ) * pdCx 0 Φ x + (V x 1 : ℂ) * pdCx 1 Φ x))).re) := by
    unfold cutRateIntegrand
    rw [Fin.sum_univ_two, ← hFx]
  rw [Fin.sum_univ_two]
  have hab := abs_le.1 key
  rw [← hA] at hab
  constructor <;> nlinarith [hab.1, hab.2]

end UnforcedLeray.Short.IIIa
