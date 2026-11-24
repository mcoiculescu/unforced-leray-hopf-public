import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Tail
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold.Fubini
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1
import UnforcedLeray.Lib.PlanarSectorsB.SectorSum

/-!
# Decay of the kernel velocity of the periodized seed modes (SP 2876-2881, 2914-2925)

The seed modes `e_j` live in the angular sectors `±2`, so `∫ e_j = 0` and the periodized modes
`E_j = P_d e_j` have zero cell mean.  Hence the periodic Biot-Savart velocity `K_d E_j` has no
mean shear at `|η| = ∞`: splitting the cell at `|z₂| = |y₂|/2`, the far-field expansion of the
kernel (`kerD_far_abs`) gives the exponentially small part, the mean shear is cancelled by the
zero cell mean up to a Gaussian tail, and the near/far kernel bound (`kerNearFar`) controls the
Gaussian tail of `E_j` convolved with the kernel.  The bound is uniform in `d ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace ComplMildGAux

open EulerErrorSub

/-- The seed modes have zero plane integral (angular sectors `±2`). -/
theorem integral_seed_e_eq_zero {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (j : Fin 2) :
    ∫ y, κ.e j y = 0 := by
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, _⟩ := hκ
  have h0 : ∫ y : ℝ × ℝ, PartI.seedPlanar h (planeToC y) = 0 := by
    have hmp := BlockPropagatorSub.measurePreserving_planeToC_volume
    rw [BlockPropagatorSub.planeToC_eq_equiv_symm] at hmp ⊢
    rw [hmp.integral_comp' (fun z => PartI.seedPlanar h z)]
    exact UnforcedLeray.Planar.integral_ofProfile_eq_zero (by norm_num) h
  fin_cases j
  · show ∫ y, κ.e 0 y = 0
    rw [show (fun y => κ.e 0 y) = fun y => PartI.seedPlanar h (planeToC y) from funext he0]
    exact h0
  · show ∫ y, κ.e 1 y = 0
    rw [show (fun y => κ.e 1 y) = fun y => conj (PartI.seedPlanar h (planeToC y)) from
      funext he1, integral_conj, h0, map_zero]

/-- The Gaussian `exp(-|z|²/a)`, `a > 0`, is integrable on the plane. -/
theorem integrable_gauss {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / a)) := by
  have h1 : Integrable (fun t : ℝ => Real.exp (-(1 / a) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine (h1.mul_prod h1).congr (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The seed modes are integrable on the plane. -/
theorem integrable_seed_e (κ : PlanarFrameKernels) (j : Fin 2) : Integrable (κ.e j) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  refine Integrable.mono' ((integrable_gauss (a := 8) (by norm_num)).const_mul C)
    (κ.e_cont j).aestronglyMeasurable (Eventually.of_forall fun z => hC j z)

/-- The periodized seed modes have zero cell integral. -/
theorem integral_cell_perE_eq_zero {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ}
    (hd : 0 < d) (j : Fin 2) : ∫ x in B0579.cell d, perE κ d j x = 0 := by
  rw [show perE κ d j = perSum d (κ.e j) from rfl,
    integral_bcell_perSum (integrable_seed_e κ j) hd]
  exact integral_seed_e_eq_zero hκ j

/-- The cell Gaussian bound of `E_j` extends periodically to a transverse Gaussian bound. -/
theorem perE_norm_le_all {κ : PlanarFrameKernels} {M_E d : ℝ} (hd : 0 < d) {j : Fin 2}
    (hcell : ∀ x ∈ B0579.cell d, ‖perE κ d j x‖ ≤ M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16))
    (hM : 0 ≤ M_E) (z : ℝ × ℝ) :
    ‖perE κ d j z‖ ≤ M_E * Real.exp (-(z.2 ^ 2) / 16) := by
  set n : ℤ := ⌊(z.1 + d / 2) / d⌋ with hn
  have h1 : (n : ℝ) ≤ (z.1 + d / 2) / d := Int.floor_le _
  have h2 : (z.1 + d / 2) / d < n + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hd] at h1
  rw [div_lt_iff₀ hd] at h2
  have hmem : (z.1 + ((-n : ℤ) : ℝ) * d, z.2) ∈ B0579.cell d := by
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true]
    push_cast
    constructor <;> nlinarith
  have hper : perE κ d j (z.1 + ((-n : ℤ) : ℝ) * d, z.2) = perE κ d j z :=
    perSum_int_period d (κ.e j) (-n) z
  rw [← hper]
  refine (hcell _ hmem).trans ?_
  gcongr
  nlinarith [sq_nonneg (z.1 + ((-n : ℤ) : ℝ) * d)]

/-- `farC d ≤ 2` for `d ≥ 1`. -/
theorem farC_le_two {d : ℝ} (hd : 1 ≤ d) : farC d ≤ 2 := by
  unfold farC
  have hd0 : 0 < d := by linarith
  set x := 2 * Real.pi / d with hx
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hx0 : 0 < x := by positivity
  have hxle : x ≤ 2 * Real.pi := by rw [hx]; exact div_le_self (by positivity) hd
  have hexp : Real.exp (-x) * (1 + x) ≤ 1 := by
    have h := Real.add_one_le_exp x
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos x)]
    linarith
  have h1 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-x)]
  have h2 : d * x = 2 * Real.pi := by rw [hx]; field_simp
  have hkey : 1 / 2 ≤ d * (1 - Real.exp (-x)) := by
    have h3 : 1 / 2 ≤ d * (x / (1 + x)) := by
      rw [← mul_div_assoc, h2, le_div_iff₀ (by positivity)]
      nlinarith
    exact h3.trans (by gcongr)
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The mean shear has modulus at most `1/2` for `d ≥ 1`. -/
theorem abs_meanShear_le {d : ℝ} (hd : 1 ≤ d) (y : ℝ × ℝ) (k : Fin 2) :
    |meanShear d 1 y k| ≤ 1 / 2 := by
  have hd0 : 0 < d := by linarith
  unfold meanShear
  split_ifs
  · rw [abs_mul, abs_neg, abs_div, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * d)]
    have hs : |Real.sign y.2| ≤ 1 := by
      rcases Real.sign_apply_eq y.2 with h | h | h <;> simp [h]
    calc 1 / (2 * d) * |Real.sign y.2| ≤ 1 / (2 * d) * 1 := by gcongr
      _ ≤ 1 / 2 := by
        rw [mul_one]
        gcongr
        linarith
  · simp

/-- **Near/far bound for a periodic density** (the argument of `kerVelCx_perE_bound`): for a
`d`-periodic `W` with `|W| ≤ S` and cell `L¹` norm `≤ L`, the convolution with the periodic
kernel is bounded by `C (S + L)`, uniformly in `d ≥ 1`. -/
theorem kerConv_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d → ∀ W : ℝ × ℝ → ℂ,
    (∀ z : ℝ × ℝ, W (z.1 + d, z.2) = W z) → ∀ S L : ℝ, 0 ≤ S → 0 ≤ L →
    (∀ z, ‖W z‖ ≤ S) → (∫⁻ z in B0579.cell d, ‖W z‖ₑ) ≤ ENNReal.ofReal L →
    ∀ (y : ℝ × ℝ) (k : Fin 2),
      (∫⁻ z in B0579.cell d, ‖W z‖ₑ * ‖kerD d (y - z) k‖ₑ) ≤
        ENNReal.ofReal (C * S + C * L) := by
  obtain ⟨C_NF, hCNF_pos, hNF⟩ := kerNearFar
  refine ⟨C_NF, hCNF_pos, fun d hd W hWper S L hS0 hL0 hS hL y k => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨_, hK_per, _, hK_near, hK_far⟩ := hNF d hd
  have hcell_eq : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  set near : Set (ℝ × ℝ) := B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1
  set far : Set (ℝ × ℝ) := B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hmeas_ball : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
  have hmeas_near : MeasurableSet near := hmeas_cell.inter hmeas_ball
  have hmeas_far : MeasurableSet far := hmeas_cell.diff hmeas_ball
  have hWshift : ∀ w : ℝ × ℝ, W (y - (w.1 + d, w.2)) = W (y - w) := by
    intro w
    have harg : ((y - (w.1 + d, w.2)).1 + d, (y - (w.1 + d, w.2)).2) = y - w := by
      ext <;> simp <;> ring
    have hW := hWper (y - (w.1 + d, w.2))
    rw [harg] at hW
    exact hW.symm
  have hG_per : UnforcedLeray.Cyl.IsPeriodic d
      (fun w : ℝ × ℝ => ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ) := by
    intro w
    dsimp only
    rw [hWshift w, hK_per w k]
  have hconv_eq :
      (∫⁻ z in B0579.cell d, ‖W z‖ₑ * ‖kerD d (y - z) k‖ₑ) =
      (∫⁻ w in B0579.cell d, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ) := by
    have h1 : (fun z => ‖W z‖ₑ * ‖kerD d (y - z) k‖ₑ) =
        (fun z => ‖W (y - (y - z))‖ₑ * ‖kerD d (y - z) k‖ₑ) := by
      funext z
      rw [sub_sub_cancel]
    rw [hcell_eq, h1]
    exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hG_per y
  have hnear_le :
      (∫⁻ w in near, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ) ≤ ENNReal.ofReal (C_NF * S) := by
    calc ∫⁻ w in near, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ
        ≤ ∫⁻ w in near, ENNReal.ofReal S * ‖kerD d w k‖ₑ := by
          refine setLIntegral_mono' hmeas_near (fun w _ => ?_)
          have hle : ‖W (y - w)‖ₑ ≤ ENNReal.ofReal S := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hS (y - w))
          gcongr
      _ = ENNReal.ofReal S * ∫⁻ w in near, ‖kerD d w k‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal S * ∫⁻ w in near, ∑ j', ‖kerD d w j'‖ₑ := by
          gcongr with w
          exact Finset.single_le_sum (f := fun j' => ‖kerD d w j'‖ₑ)
            (fun _ _ => bot_le) (Finset.mem_univ k)
      _ ≤ ENNReal.ofReal S * ENNReal.ofReal C_NF := by
          gcongr
      _ = ENNReal.ofReal (C_NF * S) := by
          rw [← ENNReal.ofReal_mul hS0, mul_comm]
  have hfar_le :
      (∫⁻ w in far, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ) ≤ ENNReal.ofReal (C_NF * L) := by
    have hE_per : UnforcedLeray.Cyl.IsPeriodic d (fun z : ℝ × ℝ => ‖W z‖ₑ) := by
      intro z
      dsimp only
      rw [hWper z]
    have hshift_E : (∫⁻ w in B0579.cell d, ‖W (y - w)‖ₑ) =
        (∫⁻ z in B0579.cell d, ‖W z‖ₑ) := by
      rw [hcell_eq]
      exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hE_per y
    calc ∫⁻ w in far, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ
        ≤ ∫⁻ w in far, ‖W (y - w)‖ₑ * ENNReal.ofReal C_NF := by
          refine setLIntegral_mono' hmeas_far (fun w hw => ?_)
          have hle : ‖kerD d w k‖ₑ ≤ ENNReal.ofReal C_NF := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hK_far w hw.1 hw.2 k)
          gcongr
      _ ≤ ∫⁻ w in B0579.cell d, ‖W (y - w)‖ₑ * ENNReal.ofReal C_NF :=
          lintegral_mono_set sdiff_subset
      _ = (∫⁻ w in B0579.cell d, ‖W (y - w)‖ₑ) * ENNReal.ofReal C_NF :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ z in B0579.cell d, ‖W z‖ₑ) * ENNReal.ofReal C_NF := by
          rw [hshift_E]
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal C_NF := by
          gcongr
      _ = ENNReal.ofReal (C_NF * L) := by
          rw [← ENNReal.ofReal_mul hL0, mul_comm]
  calc (∫⁻ z in B0579.cell d, ‖W z‖ₑ * ‖kerD d (y - z) k‖ₑ)
      = ∫⁻ w in B0579.cell d, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ := hconv_eq
    _ = (∫⁻ w in near, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ) +
          (∫⁻ w in far, ‖W (y - w)‖ₑ * ‖kerD d w k‖ₑ) := by
        rw [← lintegral_inter_add_sdiff _ (B0579.cell d) hmeas_ball]
    _ ≤ ENNReal.ofReal (C_NF * S) + ENNReal.ofReal (C_NF * L) := add_le_add hnear_le hfar_le
    _ = ENNReal.ofReal (C_NF * S + C_NF * L) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Cell `L¹` bound from a pointwise integrable bound. -/
theorem lintegral_cell_le_of_integrable {d : ℝ} {g : ℝ × ℝ → ℝ} (hg : Integrable g)
    (hg0 : ∀ z, 0 ≤ g z) {F : ℝ × ℝ → ℂ} (hF : ∀ z ∈ B0579.cell d, ‖F z‖ ≤ g z) :
    (∫⁻ z in B0579.cell d, ‖F z‖ₑ) ≤ ENNReal.ofReal (∫ z, g z) := by
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  calc (∫⁻ z in B0579.cell d, ‖F z‖ₑ)
      ≤ ∫⁻ z in B0579.cell d, ENNReal.ofReal (g z) := by
        refine setLIntegral_mono' hmeas_cell (fun z hz => ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hF z hz)
    _ ≤ ∫⁻ z, ENNReal.ofReal (g z) := setLIntegral_le_lintegral (B0579.cell d) _
    _ = ENNReal.ofReal (∫ z, g z) :=
        (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)).symm

/-- Cell `L¹` bound from a pointwise Gaussian bound. -/
theorem lintegral_cell_le_gauss32 {d A : ℝ} (hA : 0 ≤ A) {F : ℝ × ℝ → ℂ}
    (hF : ∀ z ∈ B0579.cell d, ‖F z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)) :
    (∫⁻ z in B0579.cell d, ‖F z‖ₑ) ≤
      ENNReal.ofReal (A * ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)) := by
  set g : ℝ × ℝ → ℝ := fun z => A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32) with hg_def
  have hint : Integrable g := (integrable_gauss (a := 32) (by norm_num)).const_mul A
  have h := lintegral_cell_le_of_integrable hint (fun z => by positivity) hF
  have heq : (∫ z, g z) = A * ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32) :=
    integral_const_mul A _
  rw [heq] at h
  exact h

/-- The abstract decay estimate for a periodic, Gaussian, zero-mean density `W`. -/
theorem kerVel_decay_abstract {C M_E I_E d R : ℝ} {k : Fin 2} {y : ℝ × ℝ} {W : ℝ × ℝ → ℂ}
    (hC0 : 0 ≤ C) (hME0 : 0 ≤ M_E) (hIE0 : 0 ≤ I_E)
    (hconv : ∀ W' : ℝ × ℝ → ℂ, (∀ z : ℝ × ℝ, W' (z.1 + d, z.2) = W' z) → ∀ S L : ℝ,
      0 ≤ S → 0 ≤ L → (∀ z, ‖W' z‖ ≤ S) → (∫⁻ z in B0579.cell d, ‖W' z‖ₑ) ≤ ENNReal.ofReal L →
      (∫⁻ z in B0579.cell d, ‖W' z‖ₑ * ‖kerD d (y - z) k‖ₑ) ≤
        ENNReal.ofReal (C * S + C * L))
    (hd : 1 ≤ d) (hR1 : 1 < R) (hRy : |y.2| = 2 * R)
    (hWcont : Continuous W) (hWper : ∀ z : ℝ × ℝ, W (z.1 + d, z.2) = W z)
    (hWcell : ∀ x ∈ B0579.cell d, ‖W x‖ ≤ M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16))
    (hWall : ∀ z, ‖W z‖ ≤ M_E * Real.exp (-(z.2 ^ 2) / 16))
    (hWsup : ∀ z, ‖W z‖ ≤ M_E)
    (hIE : (∫⁻ z in B0579.cell d, ‖W z‖ₑ) ≤ ENNReal.ofReal I_E)
    (hW0 : ∫ z in B0579.cell d, W z = 0)
    (hKm : Measurable fun z => kerD d z k) :
    ‖kerVelCx d W y k‖ ≤
      I_E * (2 * Real.exp (-(2 * Real.pi / d) * R)) +
        (C * (M_E * Real.exp (-(R ^ 2) / 16)) +
          C * (M_E * Real.exp (-(R ^ 2) / 32) *
            ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32))) +
        1 / 2 * (M_E * Real.exp (-(R ^ 2) / 32) *
          ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)) := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hRy' : R < |y.2| := by rw [hRy]; linarith
  have hG0 : 0 ≤ ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hsin : MeasurableSet {z : ℝ × ℝ | |z.2| ≤ R} :=
    measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const
  -- the outer part of `W`
  have hWout_per : ∀ z : ℝ × ℝ, ({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) (z.1 + d, z.2) =
      ({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z := by
    intro z
    simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [hWper z]
  have hS0 : 0 ≤ M_E * Real.exp (-(R ^ 2) / 16) := by positivity
  have hL0 : 0 ≤ M_E * Real.exp (-(R ^ 2) / 32) *
      ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32) := by positivity
  have hWout_sup : ∀ z, ‖({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z‖ ≤
      M_E * Real.exp (-(R ^ 2) / 16) := by
    intro z
    by_cases hz : |z.2| ≤ R
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ × ℝ | |z.2| ≤ R}ᶜ from fun h => h hz),
        norm_zero]
      exact hS0
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | |z.2| ≤ R}ᶜ from hz)]
      refine (hWall z).trans ?_
      have hz2 : R < |z.2| := lt_of_not_ge hz
      have hsq : R ^ 2 ≤ z.2 ^ 2 := by
        rw [← sq_abs z.2]
        exact pow_le_pow_left₀ (by linarith) hz2.le 2
      gcongr
  have hWout_L1 : (∫⁻ z in B0579.cell d, ‖({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z‖ₑ) ≤
      ENNReal.ofReal (M_E * Real.exp (-(R ^ 2) / 32) *
        ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)) := by
    refine lintegral_cell_le_gauss32 (by positivity) (fun z hz => ?_)
    by_cases hzs : |z.2| ≤ R
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ × ℝ | |z.2| ≤ R}ᶜ from fun h => h hzs),
        norm_zero]
      positivity
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | |z.2| ≤ R}ᶜ from hzs)]
      refine (hWcell z hz).trans ?_
      have hz2 : R < |z.2| := lt_of_not_ge hzs
      have hsq : R ^ 2 ≤ z.2 ^ 2 := by
        rw [← sq_abs z.2]
        exact pow_le_pow_left₀ (by linarith) hz2.le 2
      rw [mul_assoc, ← Real.exp_add]
      gcongr
      nlinarith [sq_nonneg z.1]
  -- integrability
  have hKmeas : Measurable (fun z : ℝ × ℝ => W z * ((kerD d (y - z) k : ℝ) : ℂ)) :=
    hWcont.measurable.mul (Complex.measurable_ofReal.comp
      (hKm.comp (measurable_const.sub measurable_id)))
  have hKfin : (∫⁻ z in B0579.cell d, ‖W z * ((kerD d (y - z) k : ℝ) : ℂ)‖ₑ) < ⊤ := by
    have h1 := hconv W hWper M_E I_E hME0 hIE0 hWsup hIE
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := C * M_E + C * I_E))
    refine le_of_eq_of_le ?_ h1
    refine lintegral_congr fun z => ?_
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  have hKint : IntegrableOn (fun z : ℝ × ℝ => W z * ((kerD d (y - z) k : ℝ) : ℂ))
      (B0579.cell d) := ⟨hKmeas.aestronglyMeasurable, hKfin⟩
  have hWint : IntegrableOn W (B0579.cell d) :=
    ⟨hWcont.aestronglyMeasurable, lt_of_le_of_lt hIE ENNReal.ofReal_lt_top⟩
  have hWin_int : IntegrableOn ({z : ℝ × ℝ | |z.2| ≤ R}.indicator W) (B0579.cell d) :=
    hWint.indicator hsin
  -- the decomposition
  have hK_eq : kerVelCx d W y k =
      (∫ z in B0579.cell d, (W z * ((kerD d (y - z) k : ℝ) : ℂ) -
        ((meanShear d 1 y k : ℝ) : ℂ) * {z : ℝ × ℝ | |z.2| ≤ R}.indicator W z)) -
        ((meanShear d 1 y k : ℝ) : ℂ) *
          ∫ z in B0579.cell d, ({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z := by
    have e1 : (∫ z in B0579.cell d, (W z * ((kerD d (y - z) k : ℝ) : ℂ) -
        ((meanShear d 1 y k : ℝ) : ℂ) * {z : ℝ × ℝ | |z.2| ≤ R}.indicator W z)) =
        kerVelCx d W y k - ((meanShear d 1 y k : ℝ) : ℂ) *
          ∫ z in B0579.cell d, {z : ℝ × ℝ | |z.2| ≤ R}.indicator W z := by
      rw [integral_sub hKint (hWin_int.const_mul _), integral_const_mul]
      rfl
    have e2 : (∫ z in B0579.cell d, ({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z) =
        (∫ z in B0579.cell d, W z) -
          ∫ z in B0579.cell d, {z : ℝ × ℝ | |z.2| ≤ R}.indicator W z := by
      rw [← integral_sub hWint hWin_int]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Set.indicator_compl, Pi.sub_apply]
    rw [e1, e2, hW0]
    ring
  -- the near-shear part
  have hpt : ∀ z, ‖W z * ((kerD d (y - z) k : ℝ) : ℂ) -
      ((meanShear d 1 y k : ℝ) : ℂ) * {z : ℝ × ℝ | |z.2| ≤ R}.indicator W z‖ₑ ≤
      ‖W z‖ₑ * ENNReal.ofReal (2 * Real.exp (-(2 * Real.pi / d) * R)) +
        ‖({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z‖ₑ * ‖kerD d (y - z) k‖ₑ := by
    intro z
    by_cases hz : |z.2| ≤ R
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | |z.2| ≤ R} from hz)]
      have hfac : W z * ((kerD d (y - z) k : ℝ) : ℂ) - ((meanShear d 1 y k : ℝ) : ℂ) * W z =
          W z * (((kerD d (y - z) k - meanShear d 1 y k : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hfac, enorm_mul]
      refine le_add_right ?_
      gcongr
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      apply ENNReal.ofReal_le_ofReal
      have hmsh : meanShear d 1 (y - z) k = meanShear d 1 y k :=
        meanShear_sub_eq d y z k R hz hRy'
      have hyz : R ≤ |(y - z).2| := by
        simp only [Prod.snd_sub]
        have := abs_sub_abs_le_abs_sub y.2 z.2
        linarith
      have hfar := kerD_far_abs d hd (y - z) (by linarith) k
      rw [hmsh] at hfar
      refine hfar.trans ?_
      have hc : 0 ≤ 2 * Real.pi / d := by positivity
      gcongr
      · exact farC_le_two hd
      · nlinarith
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ × ℝ | |z.2| ≤ R} from hz), mul_zero,
        sub_zero, Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | |z.2| ≤ R}ᶜ from hz), enorm_mul]
      refine le_add_left (le_of_eq ?_)
      congr 1
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  have hb1 : ‖∫ z in B0579.cell d, (W z * ((kerD d (y - z) k : ℝ) : ℂ) -
      ((meanShear d 1 y k : ℝ) : ℂ) * {z : ℝ × ℝ | |z.2| ≤ R}.indicator W z)‖ ≤
      I_E * (2 * Real.exp (-(2 * Real.pi / d) * R)) +
        (C * (M_E * Real.exp (-(R ^ 2) / 16)) +
          C * (M_E * Real.exp (-(R ^ 2) / 32) *
            ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32))) := by
    have hmeasA : Measurable (fun z =>
        ‖W z‖ₑ * ENNReal.ofReal (2 * Real.exp (-(2 * Real.pi / d) * R))) :=
      hWcont.measurable.enorm.mul_const _
    have hlin := (lintegral_mono (μ := volume.restrict (B0579.cell d)) hpt).trans
      ((lintegral_add_left hmeasA _).le.trans (add_le_add
        ((lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).le.trans
          (mul_le_mul_of_nonneg_right hIE zero_le))
        (hconv _ hWout_per _ _ hS0 hL0 hWout_sup hWout_L1)))
    rw [← ENNReal.ofReal_mul hIE0, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hlin
    have h := (enorm_integral_le_lintegral_enorm _).trans hlin
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hb2 : ‖((meanShear d 1 y k : ℝ) : ℂ) *
      ∫ z in B0579.cell d, ({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z‖ ≤
      1 / 2 * (M_E * Real.exp (-(R ^ 2) / 32) *
        ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32)) := by
    rw [norm_mul]
    have hms : ‖((meanShear d 1 y k : ℝ) : ℂ)‖ ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_meanShear_le hd y k
    have hint : ‖∫ z in B0579.cell d, ({z : ℝ × ℝ | |z.2| ≤ R}ᶜ.indicator W) z‖ ≤
        M_E * Real.exp (-(R ^ 2) / 32) * ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32) := by
      have h := (enorm_integral_le_lintegral_enorm _).trans hWout_L1
      rw [← ofReal_norm] at h
      exact (ENNReal.ofReal_le_ofReal_iff hL0).mp h
    exact mul_le_mul hms hint (norm_nonneg _) (by norm_num)
  rw [hK_eq]
  exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)

/-- **Decay of the kernel velocity of the periodized seed modes**: uniformly in `d ≥ 1`, for
`|y₂| > 2`, `|K_d E_j(y)| ≤ Q (e^{-|y₂|/64} + e^{-(2π/d)|y₂|/2})`. -/
theorem kerVelCx_perE_decay {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ d : ℝ, 1 ≤ d → ∀ (j k : Fin 2) (y : ℝ × ℝ), 2 < |y.2| →
      ‖kerVelCx d (perE κ d j) y k‖ ≤
        Q * (Real.exp (-(|y.2| / 2) / 32) +
          Real.exp (-(2 * Real.pi / d) * (|y.2| / 2))) := by
  obtain ⟨C, hC0, hconv⟩ := kerConv_le
  obtain ⟨M_E, hME0, hME⟩ := perE_and_pdCx_gauss_bounds hκ
  obtain ⟨I_E, hIE0, hIE⟩ := lintegral_perE_cell_le hκ
  obtain ⟨C_NF, -, hNF⟩ := kerNearFar
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 32) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨2 * I_E + C * M_E + (C + 1) * (M_E * G), by positivity,
    fun d hd j k y hy => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨hKm, -, -, -, -⟩ := hNF d hd
  obtain ⟨hWcell, hWsup, -⟩ := hME d hd j
  have hWper : ∀ z : ℝ × ℝ, perE κ d j (z.1 + d, z.2) = perE κ d j z := fun z => by
    have := perSum_int_period d (κ.e j) 1 z
    simpa [perE] using this
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |y.2| / 2 := ⟨_, rfl⟩
  have hR1 : 1 < R := by rw [hR]; linarith
  have hRy : |y.2| = 2 * R := by rw [hR]; ring
  have hcore := kerVel_decay_abstract (k := k) (y := y) hC0 hME0 hIE0
    (fun W' hW' S L hS hL hsup hL1 => hconv d hd W' hW' S L hS hL hsup hL1 y k) hd hR1 hRy
    (perE_continuous_aux κ hd0 j) hWper hWcell (perE_norm_le_all hd0 hWcell hME0) hWsup
    (hIE d hd j) (integral_cell_perE_eq_zero hκ hd0 j) (hKm k)
  rw [← hG] at hcore
  rw [← hR]
  refine hcore.trans ?_
  have hA : 0 ≤ Real.exp (-R / 32) := (Real.exp_pos _).le
  have hB : 0 ≤ Real.exp (-(2 * Real.pi / d) * R) := (Real.exp_pos _).le
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hex1 : Real.exp (-(R ^ 2) / 16) ≤ Real.exp (-R / 32) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hex2 : Real.exp (-(R ^ 2) / 32) ≤ Real.exp (-R / 32) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hS' : C * (M_E * Real.exp (-(R ^ 2) / 16)) ≤ C * (M_E * Real.exp (-R / 32)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hex1 hME0) hC0
  have hL' : M_E * Real.exp (-(R ^ 2) / 32) * G ≤ M_E * Real.exp (-R / 32) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex2 hME0) hG0
  have hCL := mul_le_mul_of_nonneg_left hL' hC0
  have hL2 := mul_le_mul_of_nonneg_left hL' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith [mul_nonneg hIE0 hA, mul_nonneg (mul_nonneg hC0 hME0) hB,
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C + 1) (mul_nonneg hME0 hG0)) hB,
    mul_nonneg (mul_nonneg hME0 hG0) hA, mul_nonneg (mul_nonneg hC0 hME0) hA,
    mul_nonneg (mul_nonneg hC0 (mul_nonneg hME0 hG0)) hA]

end ComplMildGAux

end UnforcedLeray.Short.IIIa
