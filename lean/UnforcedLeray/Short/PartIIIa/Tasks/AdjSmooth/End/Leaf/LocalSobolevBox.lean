import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.LocalSobolevBox.Step

/-!
# `localSobolevBox` (SP 3060-3061)

Cutoff `ζ = 1` on the ball, `F = ζ G` supported in the box, `F x = ∫∫ ∂₀∂₁F` (double FTC, `Step`),
Leibniz for `∂₀∂₁(ζ G)`, Cauchy-Schwarz on the box.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.LSB

lemma contDiff_adjSpatial (w : List (Fin 2)) {Ψ : ℝ × ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (adjSpatial w Ψ) := by
  induction w with
  | nil => exact hΨ
  | cons k w ih => exact contDiff_pdCx k ih

lemma pdCx_add {f g : ℝ × ℝ → ℂ} (k : Fin 2) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (y : ℝ × ℝ) :
    pdCx k (fun z => f z + g z) y = pdCx k f y + pdCx k g y := by
  have hf' : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
  have hg' : DifferentiableAt ℝ g y := (hg.differentiable (by simp)) y
  unfold pdCx
  rw [fderiv_fun_add hf' hg']
  simp only [add_apply]

lemma leibniz {ζ G : ℝ × ℝ → ℂ} (hζ : ContDiff ℝ ∞ ζ) (hG : ContDiff ℝ ∞ G) (y : ℝ × ℝ) :
    pdCx 0 (pdCx 1 (fun z => ζ z * G z)) y =
      (pdCx 0 (pdCx 1 ζ) y * G y + pdCx 1 ζ y * pdCx 0 G y) +
        (pdCx 0 ζ y * pdCx 1 G y + ζ y * pdCx 0 (pdCx 1 G) y) := by
  have e1 : pdCx 1 (fun z => ζ z * G z) =
      fun z => pdCx 1 ζ z * G z + ζ z * pdCx 1 G z := by
    funext z; exact pdCx_mul 1 hζ hG z
  have hA : ContDiff ℝ ∞ (pdCx 1 ζ) := contDiff_pdCx 1 hζ
  have hB : ContDiff ℝ ∞ (pdCx 1 G) := contDiff_pdCx 1 hG
  rw [e1, pdCx_add 0 (hA.mul hG) (hζ.mul hB), pdCx_mul 0 hA hG, pdCx_mul 0 hζ hB]

lemma enorm_le_ofReal {c : ℂ} {K : ℝ} (h : ‖c‖ ≤ K) : ‖c‖ₑ ≤ ENNReal.ofReal K := by
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h

lemma pointwise {ζ G : ℝ × ℝ → ℂ} (hζ : ContDiff ℝ ∞ ζ) (hG : ContDiff ℝ ∞ G) (K : ℝ)
    (y : ℝ × ℝ) (h0 : ‖ζ y‖ ≤ K) (h1 : ‖pdCx 0 ζ y‖ ≤ K) (h2 : ‖pdCx 1 ζ y‖ ≤ K)
    (h3 : ‖pdCx 0 (pdCx 1 ζ) y‖ ≤ K) :
    ‖pdCx 0 (pdCx 1 (fun z => ζ z * G z)) y‖ₑ ≤ ENNReal.ofReal K *
      (‖adjSpatial [] G y‖ₑ + ‖adjSpatial [0] G y‖ₑ + ‖adjSpatial [1] G y‖ₑ +
        ‖adjSpatial [0, 1] G y‖ₑ) := by
  rw [leibniz hζ hG y]
  have c0 := enorm_le_ofReal h0
  have c1 := enorm_le_ofReal h1
  have c2 := enorm_le_ofReal h2
  have c3 := enorm_le_ofReal h3
  refine (enorm_add_le _ _).trans ?_
  refine (add_le_add (enorm_add_le _ _) (enorm_add_le _ _)).trans ?_
  simp only [enorm_mul]
  show _ ≤ ENNReal.ofReal K * (‖G y‖ₑ + ‖pdCx 0 G y‖ₑ + ‖pdCx 1 G y‖ₑ +
        ‖pdCx 0 (pdCx 1 G) y‖ₑ)
  calc _ ≤ (ENNReal.ofReal K * ‖G y‖ₑ + ENNReal.ofReal K * ‖pdCx 0 G y‖ₑ) +
        (ENNReal.ofReal K * ‖pdCx 1 G y‖ₑ + ENNReal.ofReal K * ‖pdCx 0 (pdCx 1 G) y‖ₑ) := by
        gcongr
    _ = _ := by ring

lemma holder {B : Set (ℝ × ℝ)} (hB : volume B ≠ ⊤) {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    ∫⁻ y in B, ‖f y‖ₑ ≤ volume B ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) *
      eLpNorm f 2 (volume.restrict B) := by
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B) (p := 1) (q := 2)
    (by norm_num) hf.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at this
  rw [mul_comm]; exact this

end UnforcedLeray.Short.IIIa.LSB

namespace UnforcedLeray.Short.IIIa

open LSB in
theorem localSobolevBox : UnforcedLeray.Short.IIIa.LocalSobolevBox := by
  intro M
  by_cases hM : 0 ≤ M
  swap
  · exact ⟨0, le_rfl, fun G _ x hx => absurd hx (by
      push_neg; linarith [norm_nonneg x])⟩
  obtain ⟨ζ, hζ, hz, h1⟩ := cutoff M hM
  set B : Set (ℝ × ℝ) := Metric.closedBall (0 : ℝ × ℝ) (M + 1) with hBdef
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBfin : volume B ≠ ⊤ := (measure_closedBall_lt_top).ne
  have bnd : ∀ f : ℝ × ℝ → ℂ, Continuous f → ∃ C : ℝ, ∀ y ∈ B, ‖f y‖ ≤ C :=
    fun f hf => hBc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨C0, hC0⟩ := bnd ζ hζ.continuous
  obtain ⟨C1, hC1⟩ := bnd (pdCx 0 ζ) (LSB.contDiff_pdCx 0 hζ).continuous
  obtain ⟨C2, hC2⟩ := bnd (pdCx 1 ζ) (LSB.contDiff_pdCx 1 hζ).continuous
  obtain ⟨C3, hC3⟩ := bnd (pdCx 0 (pdCx 1 ζ)) (LSB.contDiff_pdCx 0 (LSB.contDiff_pdCx 1 hζ)).continuous
  set K : ℝ := |C0| + |C1| + |C2| + |C3| with hK
  have hK0 : 0 ≤ K := by positivity
  have hb0 : ∀ y ∈ B, ‖ζ y‖ ≤ K := fun y hy => by
    have := hC0 y hy; have := le_abs_self C0
    have : 0 ≤ |C1| + |C2| + |C3| := by positivity
    linarith
  have hb1 : ∀ y ∈ B, ‖pdCx 0 ζ y‖ ≤ K := fun y hy => by
    have := hC1 y hy; have := le_abs_self C1
    have : 0 ≤ |C0| + |C2| + |C3| := by positivity
    linarith
  have hb2 : ∀ y ∈ B, ‖pdCx 1 ζ y‖ ≤ K := fun y hy => by
    have := hC2 y hy; have := le_abs_self C2
    have : 0 ≤ |C0| + |C1| + |C3| := by positivity
    linarith
  have hb3 : ∀ y ∈ B, ‖pdCx 0 (pdCx 1 ζ) y‖ ≤ K := fun y hy => by
    have := hC3 y hy; have := le_abs_self C3
    have : 0 ≤ |C0| + |C1| + |C2| := by positivity
    linarith
  set e : ℝ := 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal with he
  have he0 : 0 ≤ e := by rw [he]; norm_num
  set V : ℝ≥0∞ := volume B ^ e with hV
  have hVfin : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg he0 hBfin
  have hCfin : ENNReal.ofReal K * V ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin
  refine ⟨(ENNReal.ofReal K * V).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro G hG x hx
  rw [ENNReal.ofReal_toReal hCfin]
  have hF : ContDiff ℝ ∞ (fun z => ζ z * G z) := hζ.mul hG
  have hFz : ∀ y, M + 1 ≤ ‖y‖ → ζ y * G y = 0 := fun y hy => by rw [hz y hy, zero_mul]
  have hs := sup_bound hF M hM hFz x hx
  have hFx : ζ x * G x = G x := by rw [h1 x hx, one_mul]
  rw [hFx] at hs
  rw [ofReal_norm]
  have hmeas : ∀ w : List (Fin 2), Measurable (fun y => ‖adjSpatial w G y‖ₑ) := fun w =>
    ((LSB.contDiff_adjSpatial w hG).continuous.measurable).enorm
  have hcw : ∀ w : List (Fin 2), Continuous (adjSpatial w G) := fun w =>
    (LSB.contDiff_adjSpatial w hG).continuous
  calc ‖G x‖ₑ ≤ _ := hs
    _ ≤ ∫⁻ y in B, ENNReal.ofReal K *
          (‖adjSpatial [] G y‖ₑ + ‖adjSpatial [0] G y‖ₑ + ‖adjSpatial [1] G y‖ₑ +
            ‖adjSpatial [0, 1] G y‖ₑ) :=
        setLIntegral_mono' measurableSet_closedBall fun y hy =>
          pointwise hζ hG K y (hb0 y hy) (hb1 y hy) (hb2 y hy) (hb3 y hy)
    _ = ENNReal.ofReal K * ((∫⁻ y in B, ‖adjSpatial [] G y‖ₑ) + (∫⁻ y in B, ‖adjSpatial [0] G y‖ₑ) +
          (∫⁻ y in B, ‖adjSpatial [1] G y‖ₑ) + (∫⁻ y in B, ‖adjSpatial [0, 1] G y‖ₑ)) := by
        have m2 : Measurable (fun y => ‖adjSpatial [] G y‖ₑ + ‖adjSpatial [0] G y‖ₑ) :=
          (hmeas []).add (hmeas [0])
        have m3 : Measurable (fun y => ‖adjSpatial [] G y‖ₑ + ‖adjSpatial [0] G y‖ₑ +
            ‖adjSpatial [1] G y‖ₑ) := m2.add (hmeas [1])
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left m3,
          lintegral_add_left m2, lintegral_add_left (hmeas [])]
    _ ≤ ENNReal.ofReal K * (V * eLpNorm (adjSpatial [] G) 2 (volume.restrict B) +
          V * eLpNorm (adjSpatial [0] G) 2 (volume.restrict B) +
          V * eLpNorm (adjSpatial [1] G) 2 (volume.restrict B) +
          V * eLpNorm (adjSpatial [0, 1] G) 2 (volume.restrict B)) := by
        gcongr
        · exact holder hBfin (hcw [])
        · exact holder hBfin (hcw [0])
        · exact holder hBfin (hcw [1])
        · exact holder hBfin (hcw [0, 1])
    _ ≤ ENNReal.ofReal K * (V * (wordsLe2.map fun w =>
          eLpNorm (adjSpatial w G) 2 (volume.restrict B)).sum) := by
        have hsum : eLpNorm (adjSpatial [] G) 2 (volume.restrict B) +
            eLpNorm (adjSpatial [0] G) 2 (volume.restrict B) +
            eLpNorm (adjSpatial [1] G) 2 (volume.restrict B) +
            eLpNorm (adjSpatial [0, 1] G) 2 (volume.restrict B) ≤ (wordsLe2.map fun w =>
              eLpNorm (adjSpatial w G) 2 (volume.restrict B)).sum := by
          simp only [wordsLe2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          calc _ ≤ _ + (eLpNorm (adjSpatial [0, 0] G) 2 (volume.restrict B) +
                eLpNorm (adjSpatial [1, 0] G) 2 (volume.restrict B) +
                eLpNorm (adjSpatial [1, 1] G) 2 (volume.restrict B)) := le_self_add
            _ = _ := by simp only [add_zero]; ring
        calc _ = ENNReal.ofReal K * (V * (eLpNorm (adjSpatial [] G) 2 (volume.restrict B) +
            eLpNorm (adjSpatial [0] G) 2 (volume.restrict B) +
            eLpNorm (adjSpatial [1] G) 2 (volume.restrict B) +
            eLpNorm (adjSpatial [0, 1] G) 2 (volume.restrict B))) := by ring
          _ ≤ _ := by gcongr
    _ = _ := by ring

end UnforcedLeray.Short.IIIa
