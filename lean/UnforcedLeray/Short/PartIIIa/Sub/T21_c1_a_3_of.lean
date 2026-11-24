import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a

/-!
# Part III-a, `PartIII-a:T21/c1/a/3`: the dual kernel of the Gaussian seed, decomposed

Source: `the November 2 reference manuscript`, lines 601-610 and 2891-2897.
`seedDualKernel_of` proves `SeedDualKernel` from two source facts:

* `SeedProfileOrderTwo`: a smooth planar mode `h(r)e^{2iϑ}` has `h = O(r²)` at `0`
  (lines 601-610: "the quotient `h/k` is smooth ... `h = O(r²)`");
* `SeedPolarPlane`: polar coordinates on the plane, `∫_{ℝ²} G(|y|) e^{-inϑ} f(y) dy
  = 2π ∫₀^∞ G(r) f_n(r) r dr` (lines 2891-2897).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Sub-Prop 1** (lines 601-610): if the planar mode `h(r)e^{2iϑ}` is smooth, then `h = O(r²)`
on `(0,1]` (Taylor expansion at `0` of the smooth function, which vanishes to first order by
the angular dependence `e^{2iϑ}`). -/
def SeedProfileOrderTwo : Prop :=
  ∀ h : ℝ → ℂ, ContDiff ℝ ∞ (PartI.seedPlanar h) →
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖h r‖ ≤ C * r ^ 2

/-- **Sub-Prop 2** (polar coordinates, lines 2891-2897): for `G` continuous on `(0,∞)` and
bounded near `0`, and `f` smooth with compact support,
`∫_{ℝ²} G(|y|) e^{-inϑ} f(y) dy = 2π ∫₀^∞ G(r) f_n(r) r dr`. -/
def SeedPolarPlane : Prop :=
  ∀ (n : ℤ) (G : ℝ → ℂ), ContinuousOn G (Ioi 0) →
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C) →
    ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y : ℝ × ℝ, G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-n) (planeToC y) * f (planeToC y) =
        (2 * Real.pi : ℂ) *
          ∫ r in Ioi (0 : ℝ), G r * Planar.NUE.Polar.angularSector f n r * (r : ℂ)

lemma strainK_abs_ge_one {r : ℝ} (hr : r ≤ 1) (hr0 : 0 < r) :
    1 ≤ |Blueprint.Planar.strainK r| := by
  unfold Blueprint.Planar.strainK
  have h1 : r ^ 2 ≤ 1 := by nlinarith
  have h2 : (3 : ℝ) / 4 ≤ Real.exp (-(r ^ 2) / 4) := by
    have := Real.add_one_le_exp (-(r ^ 2) / 4)
    linarith
  have h3 : r ^ 2 / 4 - 2 ≤ -(7 / 4) := by linarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_neg (by linarith)]
  nlinarith [Real.exp_pos (-(r ^ 2) / 4)]

lemma norm_angPhase_le (l : ℤ) (x : ℂ) : ‖Planar.NUE.Ang.angPhase l x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    unfold Planar.NUE.Ang.angPhase
    rcases lt_trichotomy l 0 with h | h | h
    · simp [zero_zpow _ h.ne]
    · simp [h]
    · simp [zero_zpow _ h.ne']
  · unfold Planar.NUE.Ang.angPhase
    have : ‖x / (‖x‖ : ℂ)‖ = 1 := by
      rw [norm_div]; simp [hx]
    rw [norm_zpow, this]; simp

lemma norm_planeToC_le (y : ℝ × ℝ) : ‖planeToC y‖ ≤ |y.1| + |y.2| :=
  Complex.norm_le_abs_re_add_abs_im _

lemma abs_fst_le (y : ℝ × ℝ) : |y.1| ≤ ‖planeToC y‖ := Complex.abs_re_le_norm (planeToC y)
lemma abs_snd_le (y : ℝ × ℝ) : |y.2| ≤ ‖planeToC y‖ := Complex.abs_im_le_norm (planeToC y)

/-- Generic assembly of the kernel `κ(y) = c * G(|y|) * phase(y)` : continuity and decay. -/
lemma kernel_props (G : ℝ → ℂ) (c : ℂ) (p : ℝ × ℝ → ℂ)
    (hGc : ContinuousOn G (Ioi 0)) (hG0 : G 0 = 0)
    (hGn : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C * r ^ 2)
    (hGinf : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C / r ^ 2)
    (hpc : ∀ y, planeToC y ≠ 0 → ContinuousAt p y) (hp1 : ∀ y, ‖p y‖ ≤ 1) :
    Continuous (fun y : ℝ × ℝ => c * G ‖planeToC y‖ * p y) ∧
    ∃ C : ℝ, ∀ y : ℝ × ℝ, ‖c * G ‖planeToC y‖ * p y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2 := by
  obtain ⟨C0, hC0⟩ := hGn
  obtain ⟨C1, hC1⟩ := hGinf
  have hpl : Continuous (fun y : ℝ × ℝ => planeToC y) := by
    unfold planeToC
    exact Complex.equivRealProdCLM.symm.continuous
  refine ⟨?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : planeToC y = 0
    · have hn : ‖planeToC y‖ = 0 := by simp [hy]
      -- squeeze to zero
      have hval : c * G ‖planeToC y‖ * p y = 0 := by rw [hn, hG0]; simp
      rw [ContinuousAt, hval]
      have hz : Tendsto (fun y' : ℝ × ℝ => ‖planeToC y'‖) (𝓝 y) (𝓝 0) := by
        have := (continuous_norm.comp hpl).continuousAt (x := y)
        rw [ContinuousAt] at this
        have h' : Tendsto (fun y' : ℝ × ℝ => ‖planeToC y'‖) (𝓝 y) (𝓝 ‖planeToC y‖) := this
        simpa [hn] using h'
      refine squeeze_zero_norm' (a := fun y' : ℝ × ℝ =>
        ‖c‖ * (max |C0| 0 * ‖planeToC y'‖ ^ 2)) ?_ ?_
      · filter_upwards [hz.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with y' hy'
        by_cases h0 : ‖planeToC y'‖ = 0
        · simp [h0, hG0]
        · have hpos : 0 < ‖planeToC y'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          have := hC0 _ hpos hy'.le
          rw [norm_mul, norm_mul]
          calc ‖c‖ * ‖G ‖planeToC y'‖‖ * ‖p y'‖ ≤ ‖c‖ * ‖G ‖planeToC y'‖‖ * 1 := by
                gcongr; exact hp1 y'
            _ ≤ ‖c‖ * (C0 * ‖planeToC y'‖ ^ 2) := by rw [mul_one]; gcongr
            _ ≤ ‖c‖ * (max |C0| 0 * ‖planeToC y'‖ ^ 2) := by
                gcongr; exact (le_abs_self C0).trans (le_max_left _ _)
      · have : Tendsto (fun y' : ℝ × ℝ => ‖c‖ * (max |C0| 0 * ‖planeToC y'‖ ^ 2)) (𝓝 y)
            (𝓝 (‖c‖ * (max |C0| 0 * 0 ^ 2))) :=
          (hz.pow 2).const_mul _ |>.const_mul _
        simpa using this
    · have h1 : ContinuousAt (fun y' : ℝ × ℝ => ‖planeToC y'‖) y :=
        (continuous_norm.comp hpl).continuousAt
      have hpos : 0 < ‖planeToC y‖ := norm_pos_iff.mpr hy
      have h2 : ContinuousAt G ‖planeToC y‖ := hGc.continuousAt (Ioi_mem_nhds hpos)
      have h3 : ContinuousAt (fun y' : ℝ × ℝ => G ‖planeToC y'‖) y :=
        ContinuousAt.comp (g := G) (f := fun y' : ℝ × ℝ => ‖planeToC y'‖) h2 h1
      exact ((continuousAt_const.mul h3).mul (hpc y hy))
  · refine ⟨max (‖c‖ * max |C0| 0 * 9) (‖c‖ * max |C1| 0 * 9), fun y => ?_⟩
    set r := ‖planeToC y‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hs : r ≤ |y.1| + |y.2| := norm_planeToC_le y
    have hs2 : |y.1| + |y.2| ≤ 2 * r := by linarith [abs_fst_le y, abs_snd_le y]
    have hA : 0 < 1 + |y.1| + |y.2| := by positivity
    have hnorm : ‖c * G r * p y‖ ≤ ‖c‖ * ‖G r‖ := by
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖G r‖ * ‖p y‖ ≤ ‖c‖ * ‖G r‖ * 1 := by gcongr; exact hp1 y
        _ = _ := mul_one _
    have key : ‖c‖ * ‖G r‖ * (1 + |y.1| + |y.2|) ^ 2 ≤
        max (‖c‖ * max |C0| 0 * 9) (‖c‖ * max |C1| 0 * 9) := by
      by_cases h1 : r ≤ 1
      · by_cases h0 : r = 0
        · simp [h0, hG0]
          left; positivity
        · have hpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h0)
          have := hC0 r hpos h1
          have hb : (1 + |y.1| + |y.2|) ^ 2 ≤ 9 := by nlinarith [abs_nonneg y.1, abs_nonneg y.2]
          have : ‖G r‖ ≤ max |C0| 0 := by
            have hr2 : r ^ 2 ≤ 1 := by nlinarith
            have h3 : C0 * r ^ 2 ≤ max |C0| 0 := by
              calc C0 * r ^ 2 ≤ |C0| * r ^ 2 := by gcongr; exact le_abs_self C0
                _ ≤ |C0| * 1 := by gcongr
                _ ≤ _ := by rw [mul_one]; exact le_max_left _ _
            linarith
          calc ‖c‖ * ‖G r‖ * (1 + |y.1| + |y.2|) ^ 2 ≤ ‖c‖ * max |C0| 0 * 9 := by
                gcongr
            _ ≤ _ := le_max_left _ _
      · push Not at h1
        have h1' : 1 ≤ r := h1.le
        have hpos : 0 < r := by linarith
        have hb : (1 + |y.1| + |y.2|) ^ 2 ≤ 9 * r ^ 2 := by nlinarith
        have hG : ‖G r‖ * r ^ 2 ≤ max |C1| 0 := by
          have := hC1 r h1'
          have h5 : ‖G r‖ ≤ C1 / r ^ 2 := this
          have h6 : ‖G r‖ * r ^ 2 ≤ C1 := by
            rwa [le_div_iff₀ (by positivity)] at h5
          exact h6.trans ((le_abs_self C1).trans (le_max_left _ _))
        calc ‖c‖ * ‖G r‖ * (1 + |y.1| + |y.2|) ^ 2 ≤ ‖c‖ * ‖G r‖ * (9 * r ^ 2) := by
              gcongr
          _ = ‖c‖ * (‖G r‖ * r ^ 2) * 9 := by ring
          _ ≤ ‖c‖ * max |C1| 0 * 9 := by gcongr
          _ ≤ _ := le_max_right _ _
    calc ‖c * G r * p y‖ ≤ ‖c‖ * ‖G r‖ := hnorm
      _ = ‖c‖ * ‖G r‖ * (1 + |y.1| + |y.2|) ^ 2 * (1 + |y.1| + |y.2|)⁻¹ ^ 2 := by
          field_simp
      _ ≤ _ := by gcongr

lemma angPhase_planeToC_continuousAt (l : ℤ) {y : ℝ × ℝ} (hy : planeToC y ≠ 0) :
    ContinuousAt (fun y' : ℝ × ℝ => Planar.NUE.Ang.angPhase l (planeToC y')) y := by
  have hpl : Continuous (fun y : ℝ × ℝ => planeToC y) := by
    unfold planeToC
    exact Complex.equivRealProdCLM.symm.continuous
  unfold Planar.NUE.Ang.angPhase
  have hn : (‖planeToC y‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hy).ne'
  have h1 : ContinuousAt (fun y' : ℝ × ℝ => planeToC y' / (‖planeToC y'‖ : ℂ)) y := by
    refine hpl.continuousAt.div (Complex.continuous_ofReal.continuousAt.comp
      (continuous_norm.comp hpl).continuousAt) hn
  exact h1.zpow₀ l (Or.inl (div_ne_zero hy hn))

theorem seedDualKernel_of (hord : SeedProfileOrderTwo) (hpol : SeedPolarPlane) :
    SeedDualKernel := by
  intro hSF lam h hh ℓ hS hsm hon
  obtain ⟨hJ, -, -, -, hg⟩ := hSF lam h hh ℓ hS
  obtain ⟨g, hgd, hgk, C1, hC1⟩ := hg hon
  obtain ⟨C0, hC0⟩ := hord h hsm
  set G : ℝ → ℂ := fun r => if 0 < r then g r else 0 with hG
  have hGc : ContinuousOn G (Ioi 0) :=
    hgd.continuousOn.congr (fun r hr => by simp [hG, mem_Ioi.mp hr])
  have hG0 : G 0 = 0 := by simp [hG]
  have hGr : ∀ r : ℝ, 0 < r → G r = g r := fun r hr => by simp [hG, hr]
  have hGn : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C * r ^ 2 := by
    refine ⟨C0, fun r hr hr1 => ?_⟩
    have hk := strainK_abs_ge_one hr1 hr
    have hk0 : Blueprint.Planar.strainK r ≠ 0 := by
      intro h0; rw [h0] at hk; norm_num at hk
    rw [hGr r hr, hgk r hr hk0, norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc ‖h r‖ / |Blueprint.Planar.strainK r| ≤ ‖h r‖ :=
          div_le_self (norm_nonneg _) hk
      _ ≤ _ := hC0 r hr hr1
  have hGinf : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C / r ^ 2 :=
    ⟨C1, fun r hr => by rw [hGr r (by linarith)]; exact hC1 r hr⟩
  have hGnb : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C := by
    obtain ⟨C, hC⟩ := hGn
    refine ⟨|C|, fun r hr hr1 => (hC r hr hr1).trans ?_⟩
    have : r ^ 2 ≤ 1 := by nlinarith
    calc C * r ^ 2 ≤ |C| * r ^ 2 := by gcongr; exact le_abs_self C
      _ ≤ |C| * 1 := by gcongr
      _ = |C| := mul_one _
  -- the conjugate profile
  have hGc' : ContinuousOn (fun r => conj (G r)) (Ioi 0) :=
    Complex.continuous_conj.comp_continuousOn hGc
  have hG0' : conj (G 0) = 0 := by rw [hG0]; simp
  have hGn' : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖conj (G r)‖ ≤ C * r ^ 2 := by
    obtain ⟨C, hC⟩ := hGn
    exact ⟨C, fun r hr hr1 => by rw [Complex.norm_conj]; exact hC r hr hr1⟩
  have hGinf' : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖conj (G r)‖ ≤ C / r ^ 2 := by
    obtain ⟨C, hC⟩ := hGinf
    exact ⟨C, fun r hr => by rw [Complex.norm_conj]; exact hC r hr⟩
  have hGnb' : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖conj (G r)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hGnb
    exact ⟨C, fun r hr hr1 => by rw [Complex.norm_conj]; exact hC r hr hr1⟩
  set c : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) with hc
  have hc2 : c * (2 * Real.pi : ℂ) = (PartI.seedJ h)⁻¹ := by
    have : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this]
    rw [hc]; field_simp
  have hcc : conj c * (2 * Real.pi : ℂ) = conj ((PartI.seedJ h)⁻¹) := by
    have := congrArg (fun z => conj z) hc2
    simpa [map_ofNat] using this
  obtain ⟨hc0, hb0⟩ := kernel_props G c (fun y => Planar.NUE.Ang.angPhase (-2) (planeToC y))
    hGc hG0 hGn hGinf (fun y hy => angPhase_planeToC_continuousAt _ hy)
    (fun y => norm_angPhase_le _ _)
  obtain ⟨hc1, hb1⟩ := kernel_props (fun r => conj (G r)) (conj c)
    (fun y => Planar.NUE.Ang.angPhase 2 (planeToC y)) hGc' hG0' hGn' hGinf'
    (fun y hy => angPhase_planeToC_continuousAt _ hy) (fun y => norm_angPhase_le _ _)
  have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      Blueprint.Planar.strainK r ≠ 0 ∧ 0 < r :=
    (ae_restrict_of_ae PartI.ae_strainK_ne_zero).and (ae_restrict_mem measurableSet_Ioi)
  refine ⟨![fun y => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y),
      fun y => conj c * conj (G ‖planeToC y‖) * Planar.NUE.Ang.angPhase 2 (planeToC y)],
    ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hc0
    · exact hc1
  · obtain ⟨Ca, hCa⟩ := hb0
    obtain ⟨Cb, hCb⟩ := hb1
    refine ⟨max Ca Cb, fun i y => ?_⟩
    have hp : 0 ≤ (1 + |y.1| + |y.2|)⁻¹ ^ 2 := by positivity
    fin_cases i
    · exact (hCa y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
    · exact (hCb y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
  · intro f hf hfc
    constructor
    · have e1 := hpol 2 G hGc hGnb f hf hfc
      have hI : ∫ y : ℝ × ℝ, (![fun y => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y),
          fun y => conj c * conj (G ‖planeToC y‖) * Planar.NUE.Ang.angPhase 2 (planeToC y)] 0 : ℝ × ℝ → ℂ) y
            * f (planeToC y) =
          c * ∫ y : ℝ × ℝ, G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y) * f (planeToC y) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [Matrix.cons_val_zero]; ring
      rw [hI, e1, ← mul_assoc, hc2]
      unfold PartI.seedEll
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with r ⟨hk, hr⟩
      rw [hGr r hr, hgk r hr hk]; ring
    · have e2 := hpol (-2) (fun r => conj (G r)) hGc' hGnb' f hf hfc
      rw [neg_neg] at e2
      have hI : ∫ y : ℝ × ℝ, (![fun y => c * G ‖planeToC y‖ * Planar.NUE.Ang.angPhase (-2) (planeToC y),
          fun y => conj c * conj (G ‖planeToC y‖) * Planar.NUE.Ang.angPhase 2 (planeToC y)] 1 : ℝ × ℝ → ℂ) y
            * f (planeToC y) =
          conj c * ∫ y : ℝ × ℝ, conj (G ‖planeToC y‖) * Planar.NUE.Ang.angPhase 2 (planeToC y) * f (planeToC y) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]; ring
      rw [hI, e2]
      unfold PartI.seedEll
      rw [map_mul, ← integral_conj, ← mul_assoc, ← hcc]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with r ⟨hk, hr⟩
      rw [hGr r hr, hgk r hr hk]
      simp [map_div₀, Complex.conj_ofReal]
      left; ring

end UnforcedLeray.Short.IIIa
