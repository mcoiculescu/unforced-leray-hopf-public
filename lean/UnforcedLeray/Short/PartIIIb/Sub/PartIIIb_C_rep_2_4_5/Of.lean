import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-b:C/rep/2/4/5` : `VertYoungPhase` from the three analytic Props

Source `the November 2 reference manuscript` 3624-3647, 5219-5221 in one dimension.
Minkowski in `λ` is proved here (`vertMinkowski`); the scaled Young inequality for the vertical
kernel is assembled from `VertKernLb`, `Vert1DYoung`, `VertDil` (`vertKernYoungScaled_of`); the phase
sum is `periodicDilationSum_proved`; `vertYoungPhase_of` is the assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lqNorm1_eq_eLpNorm {q : ℝ} (hq : 1 ≤ q) (f : ℝ → ℝ≥0∞) :
    lqNorm1 q f = eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hneT : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hneT, ENNReal.toReal_ofReal hq0.le]
  simp only [lqNorm1, enorm_eq_self]

theorem lqNorm1_const_mul {q : ℝ} (hq : 0 < q) {a : ℝ≥0∞} (ha : a ≠ ⊤) (f : ℝ → ℝ≥0∞) :
    lqNorm1 q (fun y => a * f y) = a * lqNorm1 q f := by
  unfold lqNorm1
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ha),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hq.ne', ENNReal.rpow_one]

theorem ltauAt_lqNorm1_eq (P p : ℝ) (h : ℝ → ℝ → ℝ≥0∞) :
    IIIa.ltauAt P (fun s => lqNorm1 p (h s)) = ltauLq1 P p h := by
  have key : ∀ s, (lqNorm1 p (h s)) ^ (2 : ℝ) = (∫⁻ y, h s y ^ p) ^ (2 / p) := by
    intro s
    unfold lqNorm1
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  unfold IIIa.ltauAt ltauLq1
  simp_rw [key]

/-- **Minkowski in `λ`** (3636-3640) for the vertical dilation integral. -/
theorem vertMinkowski (a rIn D q : ℝ) (hq : 1 ≤ q) (h : ℝ → ℝ → ℝ≥0∞)
    (hh : Measurable (Function.uncurry h)) (τ : ℝ) :
    lqNorm1 q (vertRedH a rIn D h τ) ≤
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
        lqNorm1 q (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hq
  have hpne : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hsk : Measurable (vertKern rIn D) := by
    unfold vertKern
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hH : Measurable fun p : (ℝ × ℝ) × ℝ =>
      vertKern rIn D (p.1.1 - p.1.2 * p.2) * h (τ + 2 * Real.log p.1.2) p.2 := by
    have h1 : Measurable fun p : (ℝ × ℝ) × ℝ => vertKern rIn D (p.1.1 - p.1.2 * p.2) :=
      hsk.comp (measurable_fst.fst.sub (measurable_fst.snd.mul measurable_snd))
    have h2 : Measurable fun p : (ℝ × ℝ) × ℝ => h (τ + 2 * Real.log p.1.2) p.2 :=
      hh.comp ((measurable_const.add (measurable_const.mul
        (Real.measurable_log.comp measurable_fst.snd))).prodMk measurable_snd)
    exact h1.mul h2
  have hA : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ a) :=
    ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)
  have hI : Measurable fun p : ℝ × ℝ =>
      ∫⁻ s : ℝ, vertKern rIn D (p.1 - p.2 * s) * h (τ + 2 * Real.log p.2) s :=
    hH.lintegral_prod_right'
  have hMeas : Measurable (Function.uncurry fun (z : ℝ) (l : ℝ) =>
      ENNReal.ofReal (l ^ a) *
        ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s) := hA.mul hI
  have key : ∀ l : ℝ, eLpNorm (fun z => ENNReal.ofReal (l ^ a) *
      ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s) (ENNReal.ofReal q) volume
      = ENNReal.ofReal (l ^ a) * lqNorm1 q
        (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s) := by
    intro l
    rw [← lqNorm1_eq_eLpNorm hq]
    exact lqNorm1_const_mul hq0 ENNReal.ofReal_ne_top _
  calc lqNorm1 q (vertRedH a rIn D h τ)
      = eLpNorm (fun z => ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
          ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s)
          (ENNReal.ofReal q) volume := by
        rw [lqNorm1_eq_eLpNorm hq]
        rfl
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, eLpNorm (fun z => ENNReal.ofReal (l ^ a) *
          ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s)
          (ENNReal.ofReal q) volume :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hMeas.aemeasurable hp1 hpne
    _ = _ := lintegral_congr key

/-- The scaled Young inequality for the vertical kernel (3624-3645 in one dimension). -/
def VertKernYoungScaled : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D → ∀ l : ℝ, 0 < l → l < 1 →
    ∀ g' : ℝ → ℝ≥0∞, Measurable g' →
      lqNorm1 (22 / 3) (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * g' s) ≤
        ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
          (ENNReal.ofReal (l ^ (-(3 / 22) : ℝ)) * lqNorm1 (22 / 19) g')

theorem vertKernYoungScaled_of (hK : VertKernLb) (hY : Vert1DYoung) (hD : VertDil) :
    VertKernYoungScaled := by
  obtain ⟨c, hc, hKb⟩ := hK
  refine ⟨c + 1, by linarith, ?_⟩
  intro rIn D hrIn hD0 l hl0 hl1 g' hg'
  have hepos : 0 < (c + 1) * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ) := by positivity
  have hlpos : 0 < l ^ (-(3 / 22) : ℝ) := by positivity
  by_cases htop : lqNorm1 (22 / 19) g' = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hlpos).ne',
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hepos).ne']
    exact le_top
  · obtain ⟨hD1, hD2⟩ := hD l hl0
    set S := vertKern rIn D with hS
    set gl : ℝ → ℝ≥0∞ := fun w => g' (l⁻¹ * w) with hgl
    have hglm : Measurable gl := hg'.comp (measurable_const.mul measurable_id)
    have hSm : Measurable S := by
      rw [hS]; unfold vertKern
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    have hSt : ∀ x, S x ≠ ⊤ := fun x => by rw [hS]; unfold vertKern; exact ENNReal.ofReal_ne_top
    have hdil : lqNorm1 (22 / 19) gl = ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) * lqNorm1 (22 / 19) g' :=
      hD2 _ (by norm_num) g'
    have hgltop : lqNorm1 (22 / 19) gl ≠ ⊤ := by
      rw [hdil]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
    have hfun : (fun z => ∫⁻ s : ℝ, S (z - l * s) * g' s) =
        fun z => ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * gl w := funext fun z => hD1 S g' z
    rw [hfun, lqNorm1_const_mul (by norm_num) ENNReal.ofReal_ne_top]
    have hy := hY S gl hSm hSt hglm (11 / 3) (22 / 19) (22 / 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgltop
    have hKb' := hKb rIn D hrIn hD0
    have hid : ENNReal.ofReal (l ^ (-(3 / 22) : ℝ)) =
        ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.rpow_neg_one, ← Real.rpow_add hl0]
      norm_num
    have hle : lqNorm1 (11 / 3) S ≤ ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) := by
      refine hKb'.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (rIn / D) * D ^ (-2 + 3 / 11 : ℝ) := by positivity
      nlinarith
    calc ENNReal.ofReal l⁻¹ * lqNorm1 (22 / 3) (fun z => ∫⁻ w : ℝ, S (z - w) * gl w)
        ≤ ENNReal.ofReal l⁻¹ * (lqNorm1 (11 / 3) S * lqNorm1 (22 / 19) gl) := by gcongr
      _ ≤ ENNReal.ofReal l⁻¹ * (ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
            lqNorm1 (22 / 19) gl) := by gcongr
      _ = _ := by
        rw [hdil, hid]
        ring

theorem vertYoungPhase_of (hK : VertKernLb) (hY : Vert1DYoung) (hD : VertDil) :
    VertYoungPhase := by
  obtain ⟨C1, hC1, hY'⟩ := vertKernYoungScaled_of hK hY hD
  obtain ⟨C2, hC2, hS'⟩ := periodicDilationSum_proved (19 / 22) (by norm_num)
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro a rIn D P ha hD0 hrIn hP hP1 h hhm hper τ
  set G : ℝ → ℝ≥0∞ := fun s => lqNorm1 (22 / 19) (h s) with hG
  have hGm : Measurable G := by
    simp only [hG]
    unfold lqNorm1
    have : Measurable fun s => ∫⁻ y, h s y ^ (22 / 19 : ℝ) := by
      have h1 : Measurable (fun x : ℝ × ℝ => h x.1 x.2 ^ (22 / 19 : ℝ)) := hhm.pow_const _
      exact h1.lintegral_prod_right'
    exact this.pow_const _
  have hGper : ∀ s, G (s + P) = G s := by
    intro s; have h' := funext (hper s); simp only [hG, h']
  have hhτ : ∀ l : ℝ, Measurable (h (τ + 2 * Real.log l)) := fun l =>
    hhm.comp (measurable_const.prodMk measurable_id)
  calc lqNorm1 (22 / 3) (vertRedH a rIn D h τ)
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
          lqNorm1 (22 / 3) (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) *
            h (τ + 2 * Real.log l) s) :=
        vertMinkowski a rIn D (22 / 3) (by norm_num) h hhm τ
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
          (ENNReal.ofReal (l ^ (a - 3 / 22)) * G (τ + 2 * Real.log l)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have h1 := hY' rIn D hrIn hD0 l hl.1 hl.2 _ (hhτ l)
        calc ENNReal.ofReal (l ^ a) * lqNorm1 (22 / 3) (fun z => ∫⁻ s : ℝ,
              vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s)
            ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
              (ENNReal.ofReal (l ^ (-(3 / 22) : ℝ)) * G (τ + 2 * Real.log l))) :=
              mul_le_mul' le_rfl h1
          _ = ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
              (ENNReal.ofReal (l ^ (a - 3 / 22)) * G (τ + 2 * Real.log l)) := by
              have : l ^ (a - 3 / 22) = l ^ a * l ^ (-(3 / 22) : ℝ) := by
                rw [← Real.rpow_add hl.1]; ring_nf
              rw [this, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
              ring
    _ = ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 / 22)) * G (τ + 2 * Real.log l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C1 * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) *
          (ENNReal.ofReal C2 * IIIa.ltauAt P G) := by
        refine mul_le_mul' le_rfl ?_
        exact hS' _ (by linarith) P hP hP1 G hGm hGper τ
    _ = ENNReal.ofReal (C1 * C2 * (rIn / D) * D ^ (-2 + 3 / 11 : ℝ)) * ltauLq1 P (22 / 19) h := by
        rw [← ltauAt_lqNorm1_eq P (22 / 19) h, ← mul_assoc, ← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg hC1 (div_nonneg hrIn.le hD0.le)) (Real.rpow_nonneg hD0.le _))]
        congr 2
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
