import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2_1
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.SmoothAe.Smooth.LocalPart
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.SmoothAe.Smooth.FarPart

/-!
# Smoothness of `flatAdjointRep` on `{p | 0 < p.1}` (`Smooth`)

Proves `flatAdjointSmoothProp : UnforcedLeray.Short.PartIIa.N04_2_2_1.SmoothProp` (task
`PartII-a:N04/2/2/1/1`, source lines 1803–1805). Since `IsFlatLerayRep c σ H1 h` provides global
spatial derivative bounds only up to order 4, around each base point `p₀` with `0 < p₀.1` we
decompose `h = h_loc + h_far` via a radial `smoothTransition` cutoff `cutoffAt p₀.2` in the planar
variable `y = (q, η)`:
* `h_loc` is `IsCompactBand σ H1`, so `LocalPart.contDiffOn_flatAdjointRep_of_compactBand` gives
  `ContDiffOn ℝ ∞ (flatAdjointRep ν μ h_loc) {p | 0 < p.1}`;
* `h_far` is continuous, globally bounded, supported in `s ∈ [σ, H1]`, and vanishes on the unit
  planar disk `(y - p₀.2)² ≤ 1`, so `FarPart.contDiffOn_flatAdjointRep_of_far` gives
  `ContDiffOn ℝ ∞ (flatAdjointRep ν μ h_far) (farNhd p₀)`.

Pointwise additivity of `flatAdjointRep ν μ` on `{p | 0 < p.1}` for continuous globally bounded
profiles then yields `ContDiffOn ℝ ∞ (flatAdjointRep ν μ h) (farNhd p₀)`, hence smoothness on
`{p | 0 < p.1}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N04_2_2_1

open UnforcedLeray.Short.PartIIa UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIa.FlatAdjointElemAux
open UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (ptCont_shift ptIntKer)

/-- Planar smooth cutoff centered at `x₀ : ℝ × ℝ`, equal to `1` on `(y - x₀)² ≤ 1` and `0` outside
`(y - x₀)² < 2`. -/
private def cutoffAt (x₀ y : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (2 - ((y.1 - x₀.1) ^ 2 + (y.2 - x₀.2) ^ 2))

private theorem contDiff_cutoffAt (x₀ : ℝ × ℝ) : ContDiff ℝ ∞ (cutoffAt x₀) := by
  unfold cutoffAt
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const (c := (2 : ℝ))).sub
      (((contDiff_fst.sub (contDiff_const (c := x₀.1))).pow 2).add
        ((contDiff_snd.sub (contDiff_const (c := x₀.2))).pow 2)))

private theorem cutoffAt_nonneg (x₀ y : ℝ × ℝ) : 0 ≤ cutoffAt x₀ y :=
  Real.smoothTransition.nonneg _

private theorem cutoffAt_le_one (x₀ y : ℝ × ℝ) : cutoffAt x₀ y ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem cutoffAt_eq_one_of_sq_le_one {x₀ y : ℝ × ℝ}
    (hy : (y.1 - x₀.1) ^ 2 + (y.2 - x₀.2) ^ 2 ≤ 1) :
    cutoffAt x₀ y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutoffAt_eq_zero_of_norm_gt {x₀ y : ℝ × ℝ}
    (hy : ‖x₀.1‖ + ‖x₀.2‖ + 2 < ‖y‖) :
    cutoffAt x₀ y = 0 := by
  rw [Prod.norm_def, lt_max_iff] at hy
  have hnonpos : 2 - ((y.1 - x₀.1) ^ 2 + (y.2 - x₀.2) ^ 2) ≤ 0 := by
    rcases hy with hy1 | hy2
    · have htri : ‖y.1‖ ≤ ‖y.1 - x₀.1‖ + ‖x₀.1‖ := by
        simpa only [sub_add_cancel] using norm_add_le (y.1 - x₀.1) x₀.1
      have hgt2 : 2 < ‖y.1 - x₀.1‖ := by linarith [norm_nonneg x₀.2]
      have hsq : ‖y.1 - x₀.1‖ ^ 2 = (y.1 - x₀.1) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (y.2 - x₀.2)]
    · have htri : ‖y.2‖ ≤ ‖y.2 - x₀.2‖ + ‖x₀.2‖ := by
        simpa only [sub_add_cancel] using norm_add_le (y.2 - x₀.2) x₀.2
      have hgt2 : 2 < ‖y.2 - x₀.2‖ := by linarith [norm_nonneg x₀.1]
      have hsq : ‖y.2 - x₀.2‖ ^ 2 = (y.2 - x₀.2) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (y.1 - x₀.1)]
  exact Real.smoothTransition.zero_of_nonpos hnonpos

/-- Pointwise additivity of `flatAdjointRep ν μ` on `{p | 0 < p.1}` for continuous globally bounded
profiles when `0 < μ.re + 1 / 4`. -/
private theorem flatAdjointRep_add_apply {ν : ℝ} (hν : 0 < ν) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {w₁ w₂ : Profile → MeridC}
    (hw₁_cont : Continuous w₁) (hw₁_bdd : ∃ M₁ : ℝ, ∀ q, ‖w₁ q‖ ≤ M₁)
    (hw₂_cont : Continuous w₂) (hw₂_bdd : ∃ M₂ : ℝ, ∀ q, ‖w₂ q‖ ≤ M₂)
    {p : Profile} (hp : 0 < p.1) :
    flatAdjointRep ν μ (fun q => w₁ q + w₂ q) p =
      flatAdjointRep ν μ w₁ p + flatAdjointRep ν μ w₂ p := by
  have hI₁ : IntegrableOn (fun t : ℝ => flatAdjointSlice ν μ w₁ t p) (Ioi 0) volume := by
    simpa [thetaWeight_zero] using
      integrableOn_thetaWeight_flatAdjointSlice ν hμ 0 hw₁_cont hw₁_bdd p
  have hI₂ : IntegrableOn (fun t : ℝ => flatAdjointSlice ν μ w₂ t p) (Ioi 0) volume := by
    simpa [thetaWeight_zero] using
      integrableOn_thetaWeight_flatAdjointSlice ν hμ 0 hw₂_cont hw₂_bdd p
  obtain ⟨M₁, hM₁⟩ := hw₁_bdd
  obtain ⟨M₂, hM₂⟩ := hw₂_bdd
  simp only [flatAdjointRep, hp, ↓reduceIte]
  have hslice : EqOn (fun t : ℝ => flatAdjointSlice ν μ (fun q => w₁ q + w₂ q) t p)
      (fun t : ℝ => flatAdjointSlice ν μ w₁ t p + flatAdjointSlice ν μ w₂ t p) (Ioi 0) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have hθ : 0 < ν * p.1 * (Real.exp t - 1) :=
      mul_pos (mul_pos hν hp) (sub_pos.2 (Real.one_lt_exp_iff.2 ht_pos))
    have hheat :
        planeHeat (ν * p.1 * (Real.exp t - 1))
          (fun z => w₁ (Real.exp t * p.1, z) + w₂ (Real.exp t * p.1, z)) p.2 =
        planeHeat (ν * p.1 * (Real.exp t - 1)) (fun z => w₁ (Real.exp t * p.1, z)) p.2 +
        planeHeat (ν * p.1 * (Real.exp t - 1)) (fun z => w₂ (Real.exp t * p.1, z)) p.2 := by
      rw [planeHeat_of_pos hθ, planeHeat_of_pos hθ, planeHeat_of_pos hθ, ← integral_add
        (ptIntKer hθ (ptCont_shift hw₁_cont (Real.exp t * p.1) p.2) fun y => hM₁ _)
        (ptIntKer hθ (ptCont_shift hw₂_cont (Real.exp t * p.1) p.2) fun y => hM₂ _)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      exact smul_add _ _ _
    simp only [flatAdjointSlice, hheat, smul_add]
  rw [setIntegral_congr_fun measurableSet_Ioi hslice, integral_add hI₁ hI₂]

/-- **Smoothness of `flatAdjointRep` on `{p | 0 < p.1}` for flat Leray representatives.** -/
theorem flatAdjointSmoothProp : UnforcedLeray.Short.PartIIa.N04_2_2_1.SmoothProp := by
  intro ν c σ H1 γs hν hσ hσH1 hγs μ hμ h hh
  have hμpos : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hμ
  obtain ⟨B, hB⟩ := (isDiffProfile_base hh).bdd_w
  set S : Set Profile := {p : Profile | 0 < p.1}
  suffices h_nhd : ∀ p₀ ∈ S, ContDiffOn ℝ ∞ (flatAdjointRep ν μ h) (farNhd p₀) by
    intro p₀ hp₀
    exact ((h_nhd p₀ hp₀).contDiffAt
      ((isOpen_farNhd p₀).mem_nhds (mem_farNhd hp₀))).contDiffWithinAt
  intro p₀ hp₀
  have hp₀_pos : 0 < p₀.1 := hp₀
  set h_loc : Profile → MeridC := fun q => cutoffAt p₀.2 q.2 • h q
  set h_far : Profile → MeridC := fun q => (1 - cutoffAt p₀.2 q.2) • h q
  have hh_loc_smooth : ContDiff ℝ ∞ h_loc :=
    ((contDiff_cutoffAt p₀.2).comp contDiff_snd).smul hh.smooth
  have hh_loc_band : IsCompactBand σ H1 h_loc := by
    refine ⟨hh_loc_smooth, ?_, ⟨‖p₀.2.1‖ + ‖p₀.2.2‖ + 2, ?_⟩⟩
    · intro q hq
      simp only [h_loc, hh.support_s q hq, smul_zero]
    · intro q hq
      simp only [h_loc, cutoffAt_eq_zero_of_norm_gt hq, zero_smul]
  have hh_far_cont : Continuous h_far :=
    ((continuous_const.sub ((contDiff_cutoffAt p₀.2).continuous.comp continuous_snd))).smul
      hh.smooth.continuous
  have hh_far_supp_s : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → h_far q = 0 := by
    intro q hq
    simp only [h_far, hh.support_s q hq, smul_zero]
  have hh_far_supp_y :
      ∀ q : Profile, (q.2.1 - p₀.2.1) ^ 2 + (q.2.2 - p₀.2.2) ^ 2 ≤ 1 → h_far q = 0 := by
    intro q hq
    simp only [h_far, cutoffAt_eq_one_of_sq_le_one hq, sub_self, zero_smul]
  have hh_loc_bdd : ∃ M₁ : ℝ, ∀ q : Profile, ‖h_loc q‖ ≤ M₁ := hh_loc_band.bdd
  have hh_far_bdd : ∃ M₂ : ℝ, ∀ q : Profile, ‖h_far q‖ ≤ M₂ := by
    refine ⟨max B 0, fun q => ?_⟩
    have hnn : 0 ≤ 1 - cutoffAt p₀.2 q.2 := sub_nonneg.2 (cutoffAt_le_one p₀.2 q.2)
    have hle1 : 1 - cutoffAt p₀.2 q.2 ≤ 1 := sub_le_self 1 (cutoffAt_nonneg p₀.2 q.2)
    rw [norm_smul, Real.norm_of_nonneg hnn]
    calc (1 - cutoffAt p₀.2 q.2) * ‖h q‖
        ≤ 1 * max B 0 :=
          mul_le_mul hle1 ((hB q).trans (le_max_left B 0)) (norm_nonneg _) zero_le_one
      _ = max B 0 := one_mul _
  have h_loc_sm : ContDiffOn ℝ ∞ (flatAdjointRep ν μ h_loc) (farNhd p₀) :=
    (contDiffOn_flatAdjointRep_of_compactBand hν hσ hσH1 hμpos hh_loc_band).mono
      fun p hp => lt_trans (half_pos hp₀_pos) hp.1
  have h_far_sm : ContDiffOn ℝ ∞ (flatAdjointRep ν μ h_far) (farNhd p₀) :=
    contDiffOn_flatAdjointRep_of_far hν hσ μ hp₀_pos hh_far_cont hh_far_supp_s
      hh_far_supp_y hh_far_bdd
  refine (h_loc_sm.add h_far_sm).congr fun p hp => ?_
  have hp_pos : 0 < p.1 := lt_trans (half_pos hp₀_pos) hp.1
  have hsum : h = fun q => h_loc q + h_far q := by
    funext q
    simp only [h_loc, h_far, ← add_smul, add_sub_cancel, one_smul]
  rw [hsum]
  exact flatAdjointRep_add_apply hν hμpos hh_loc_smooth.continuous hh_loc_bdd
    hh_far_cont hh_far_bdd hp_pos

end UnforcedLeray.Short.PartIIa.N04_2_2_1
