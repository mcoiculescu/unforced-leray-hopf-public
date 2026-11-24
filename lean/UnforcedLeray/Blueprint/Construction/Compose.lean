import UnforcedLeray.Blueprint.Construction.Gain

/-!
# Composition of the construction steps

`paper/main.tex`, completion of the construction (lines 13714–13745, blueprint B1033): the
open step propositions of `Construction/Steps.lean` imply `ConstructionClaim`
(`prop:unstable-background`, B1034). Proved here and in `Construction/Gain.lean`, from the
steps only:

* the window lies in `(0, 1/4)` for large `n`, `ε_n > 0`, `P_n > 0` (`Gain.lean`);
* C4 and C5 from C1 and C2 (`stepGainTrace_of`, `stepGainBound_of` in `Gain.lean`);
* the endpoint signs `eq:st18-t00767` from C4, C5 and the uniform return C6, by a `2 × 2`
  determinant perturbation bound and `det(I - K₀) = 1 - tr K₀`
  (`MatrixCrossing.det_one_sub_outerProduct`);
* the real root `σ_n` and a real `0 ≠ β ∈ ker B_full` (`eq:st18-t00768`–`t00769`, first
  line) by `MatrixCrossing.exists_interior_kernel_of_gram_crossing`;
* the zero-entrance mode from the reduced-matrix identification C7
  (`IsReducedMatrix.zeroEntrance`, `Cylinder.lean`);
* `isExactBackground_of_B3Projected`, `isExactBackground_of_B3`: Theorem B3's output (in
  pressure-free form, or literally with the pressure conversion C9) gives the background half
  of the package (the identification of lines 13734–13742);
* `constructionClaim_of_projected_steps` (C1, C2, C3′, C6, C7, C8) and
  `constructionClaim_of_steps` (C1, C2, C3, C6, C7, C8, C9).

(Adapted from `SkeletonDesignA/ConstructionSteps.lean`, `exists_root_kernel`.)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint

open MatrixCrossing

/-! ## The determinant crossing (lines 13653–13679) -/

/-- A `2 × 2` determinant perturbation bound. -/
theorem abs_det_sub_le {A B : Matrix2} {δ M : ℝ}
    (hAB : ∀ i j, |(A - B) i j| ≤ δ) (hB : ∀ i j, |B i j| ≤ M) :
    |A.det - B.det| ≤ 4 * M * δ + 2 * δ * δ := by
  have hp : ∀ x y a b : ℝ, |x| ≤ a → |y| ≤ b → |x * y| ≤ a * b := fun x y a b hx hy => by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  have e : A.det - B.det = B 0 0 * (A - B) 1 1 + (A - B) 0 0 * B 1 1 +
      (A - B) 0 0 * (A - B) 1 1 -
      (B 0 1 * (A - B) 1 0 + (A - B) 0 1 * B 1 0 + (A - B) 0 1 * (A - B) 1 0) := by
    simp only [Matrix.det_fin_two, Matrix.sub_apply]
    ring
  rw [e]
  obtain ⟨l1, u1⟩ := abs_le.mp (hp _ _ _ _ (hB 0 0) (hAB 1 1))
  obtain ⟨l2, u2⟩ := abs_le.mp (hp _ _ _ _ (hAB 0 0) (hB 1 1))
  obtain ⟨l3, u3⟩ := abs_le.mp (hp _ _ _ _ (hAB 0 0) (hAB 1 1))
  obtain ⟨l4, u4⟩ := abs_le.mp (hp _ _ _ _ (hB 0 1) (hAB 1 0))
  obtain ⟨l5, u5⟩ := abs_le.mp (hp _ _ _ _ (hAB 0 1) (hB 1 0))
  obtain ⟨l6, u6⟩ := abs_le.mp (hp _ _ _ _ (hAB 0 1) (hAB 1 0))
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_one_sub_apply_le (K : Matrix2) {M : ℝ} (hK : ∀ i j, |K i j| ≤ M) (i j : Fin 2) :
    |(1 - K) i j| ≤ 1 + M := by
  rw [Matrix.sub_apply]
  have h1 : |(1 : Matrix2) i j| ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  calc |(1 : Matrix2) i j - K i j| ≤ |(1 : Matrix2) i j| + |K i j| := abs_sub _ _
    _ ≤ 1 + M := add_le_add h1 (hK i j)

theorem exp_one_gt_two : 2 < Real.exp 1 := by
  have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  linarith

theorem exp_neg_one_lt_half : Real.exp (-1) < 1 / 2 := by
  have hm : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    simp
  have := exp_one_gt_two
  have := Real.exp_pos (-1)
  nlinarith

/-- `eq:st18-t00767`: for any normalizer `G` with the uniform return of C6,
`det(B_full G) < 0` at `σ₀ - 1/(2ℓ_n)` and `> 0` at `σ₀ + 1/(2ℓ_n)`, for all large `n`. -/
theorem eventually_endpoint_signs {F : ConstructionData} (h4 : StepGainTrace F)
    (h5 : StepGainBound F) {G : ℕ → ℝ → Matrix2}
    (hret : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ σ ∈ F.window n, ∀ i j,
      |(F.Bfull n σ * G n σ - (1 - F.K0 n σ)) i j| ≤ δ) :
    ∀ᶠ n in atTop,
      (F.Bfull n (F.point n (-1)) * G n (F.point n (-1))).det < 0 ∧
        0 < (F.Bfull n (F.point n 1) * G n (F.point n 1)).det := by
  obtain ⟨M, hK⟩ := h5
  set M' : ℝ := 1 + |M| with hM'
  have hM'pos : 0 < M' := by positivity
  set δ : ℝ := 1 / (16 * (2 * M' + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    nlinarith
  have herr : 4 * M' * δ + 2 * δ * δ ≤ 1 / 8 := by
    have h16 : δ * (16 * (2 * M' + 1)) = 1 := by
      rw [hδdef]
      field_simp
    nlinarith
  filter_upwards [hK, hret δ hδpos, h4 (1 / 8) (by norm_num)] with n hKn hretn htr
  have hamem : F.point n (-1) ∈ F.window n := ⟨le_rfl, F.point_le n⟩
  have hbmem : F.point n 1 ∈ F.window n := ⟨F.point_le n, le_rfl⟩
  have hdet : ∀ σ ∈ F.window n,
      |(F.Bfull n σ * G n σ).det - (1 - F.K0 n σ).det| ≤ 1 / 8 := fun σ hσ =>
    (abs_det_sub_le (hretn σ hσ)
      (abs_one_sub_apply_le (F.K0 n σ) (fun i j => (hKn σ hσ i j).trans (le_abs_self M)))).trans
      herr
  have htrace : ∀ σ, (1 - F.K0 n σ).det = 1 - (F.K0 n σ).trace := fun σ =>
    det_one_sub_outerProduct _ _
  have htrm := htr (-1) ⟨le_rfl, by norm_num⟩
  have htrp := htr 1 ⟨by norm_num, le_rfl⟩
  rw [neg_neg] at htrm
  have he := exp_one_gt_two
  have he' := exp_neg_one_lt_half
  have hepos := Real.exp_pos (-1)
  constructor
  · have h1 := hdet _ hamem
    rw [htrace] at h1
    obtain ⟨_, u1⟩ := abs_le.mp h1
    obtain ⟨l2, _⟩ := abs_le.mp htrm
    linarith
  · have h1 := hdet _ hbmem
    rw [htrace] at h1
    obtain ⟨l1, _⟩ := abs_le.mp h1
    obtain ⟨_, u2⟩ := abs_le.mp htrp
    linarith

/-! ## The background half (lines 13714–13725, 13734–13742) -/

/-- C9 turns the literal output of Theorem B3 into its pressure-free form. -/
theorem IsB3Output.toProjected (hconv : PressureProjectionStep) {ν P : ℝ} {a : SpatialField}
    {U : ℝ → SpatialField} {Q : ℝ → SobolevGraph.H2} {p : ℝ → Space → ℝ}
    (hB : IsB3Output ν P a U Q p) : IsB3ProjectedOutput ν P a U Q :=
  { hB.toIsB3Core with
    projected_equation := hconv ν U p hB.background_solenoidal hB.products_L2 hB.pressure_L2
      hB.equation }

theorem StepBackground.toProjected {F : ConstructionData} (hconv : PressureProjectionStep)
    (h3 : StepBackground F) : StepBackgroundProjected F := by
  filter_upwards [h3] with n hn
  exact hn.toProjected hconv

/-- The pressure-free output of Theorem B3 at `(ν, P)` is the background half of the package
for `h = ν`, `𝒯 = P`, `u_dss = a`, `U_* = U`, `r_heat = Q` (lines 13734–13742). -/
theorem isExactBackground_of_B3Projected {ν P : ℝ} {a : SpatialField}
    {U : ℝ → SpatialField} {Q : ℝ → SobolevGraph.H2}
    (hν : 0 < ν) (hP : 0 < P) (hB : IsB3ProjectedOutput ν P a U Q) :
    IsExactBackground ⟨ν, P, a, U, Q⟩ where
  h_pos := hν
  period_pos := hP
  udss_smooth := hB.datum_smooth
  udss_solenoidal := hB.datum_solenoidal
  udss_nonzero := hB.datum_nonzero
  udss_dss := hB.datum_dss
  udss_bounds := hB.datum_bounds
  rheat_continuous := hB.remainder_continuous
  rheat_periodic := hB.remainder_periodic
  Ustar_decomposition := fun τ => by
    filter_upwards [hB.remainder τ] with y hy
    show U τ y = heatProfile ν a τ y + ((Q τ).value : SpatialField) y
    rw [hy, Pi.sub_apply]
    abel
  Ustar_solenoidal := hB.background_solenoidal
  Ustar_periodic := fun τ => by
    show U (τ + P) =ᵐ[volume] U τ
    rw [hB.background_periodic τ]
  Ustar_equation := hB.projected_equation
  udss_symmetric := hB.datum_symmetric
  Ustar_symmetric := hB.background_symmetric

/-- Theorem B3's literal output at `(ν, P)`, with the pressure conversion C9, is the
background half of the package. -/
theorem isExactBackground_of_B3 (hconv : PressureProjectionStep) {ν P : ℝ} {a : SpatialField}
    {U : ℝ → SpatialField} {Q : ℝ → SobolevGraph.H2} {p : ℝ → Space → ℝ}
    (hν : 0 < ν) (hP : 0 < P) (hB : IsB3Output ν P a U Q p) :
    IsExactBackground ⟨ν, P, a, U, Q⟩ :=
  isExactBackground_of_B3Projected hν hP (hB.toProjected hconv)

/-! ## The completion (lines 13714–13745) -/

/-- `prop:unstable-background` from the construction steps with the pressure-free form C3′
of Theorem B3: at one large member `n` of the phase-locked sequence, the root
`σ_n ∈ (0,1/4)`, a real kernel vector of `B_full` (lines 13665–13681), the zero-entrance
mode of the exact correspondence (C7, line 13681), the physical mode on the same background
(C8, lines 13693–13707), and the identification of line 13741. -/
theorem constructionClaim_of_projected_steps (F : ConstructionData)
    (h1 : StepReferenceChoice F) (h2 : StepPhaseLocked F) (h3 : StepBackgroundProjected F)
    (h6 : StepUniformReturn F) (h7 : StepReducedMatrix F) (h8 : StepPhysicalMode) :
    ConstructionClaim := by
  obtain ⟨G, hGwin, hret⟩ := h6
  have hsigns := eventually_endpoint_signs (stepGainTrace_of h1 h2) (stepGainBound_of h1 h2)
    hret
  obtain ⟨n, hs, hsub, hw, hB, hZ⟩ := (hsigns.and
    ((ConstructionData.eventually_window_subset h1 h2).and (hGwin.and (h3.and h7)))).exists
  obtain ⟨hcont, hgram⟩ := hw
  -- the window is a nondegenerate interval
  have hab : F.point n (-1) < F.point n 1 := by
    refine lt_of_le_of_ne (F.point_le n) (fun h => ?_)
    have h' := hs.2
    rw [← h] at h'
    linarith [hs.1]
  -- `eq:st18-t00768`: a real root, and the kernel vector of `t00769`
  obtain ⟨σ, hσ, β, hβ, hBβ⟩ := exists_interior_kernel_of_gram_crossing (F.Bfull n) (G n)
    hab hcont hs.1 hs.2 hgram
  have hσw : σ ∈ F.window n := ⟨hσ.1.le, hσ.2.le⟩
  have hσ0 : 0 < σ := (hsub hσw).1
  have hσ1 : σ < 1 / 4 := (hsub hσw).2
  -- `eq:st18-t00769`: the exact correspondence gives a nonzero zero-entrance mode
  obtain ⟨-, hred⟩ := hZ
  obtain ⟨b, hsol, -, hnz⟩ := (hred σ hσw).zeroEntrance hβ hBβ
  -- `eq:st18-t00633`, `t00770`, `unlabeled:13702`: the mode on the same background
  have hν := h2.1 n
  have hP := ConstructionData.period_pos h1 hν
  have hR : 0 < F.radius n := inv_pos.mpr (ConstructionData.amplitude_pos h1 hν)
  obtain ⟨lapB, driftB, hmode⟩ := h8 (F.backgroundCore n) (F.radius n) σ b hν hP hR hσ0 hσ1
    hB.background_bounded hB.background_periodic hB.background_solenoidal hsol hnz
  -- the background half, and the identification of line 13741
  have hexact : IsExactBackground (F.backgroundCore n) :=
    isExactBackground_of_B3Projected hν hP hB
  exact ⟨_, isUnstableBackground_mk (F.backgroundCore n)
    ⟨σ, cylinderLift (F.radius n) b, lapB, driftB⟩ hexact (hmode.toGrowingMode hσ0 hσ1)⟩

/-- `prop:unstable-background` from the open construction steps C1, C2, C3, C6, C7, C8 and
C9, with Theorem B3's literal equation (2.5) and the pressure conversion C9. (C4 and C5 are
proved from C1 and C2.) -/
theorem constructionClaim_of_steps (F : ConstructionData) (h1 : StepReferenceChoice F)
    (h2 : StepPhaseLocked F) (h3 : StepBackground F) (h6 : StepUniformReturn F)
    (h7 : StepReducedMatrix F) (h8 : StepPhysicalMode) (h9 : PressureProjectionStep) :
    ConstructionClaim :=
  constructionClaim_of_projected_steps F h1 h2 (h3.toProjected h9) h6 h7 h8

/-- The data-dependent open construction steps C1, C2, C3, C6, C7 for one data record, as
one proposition. -/
def ConstructionSteps : Prop :=
  ∃ F : ConstructionData, StepReferenceChoice F ∧ StepPhaseLocked F ∧ StepBackground F ∧
    StepUniformReturn F ∧ StepReducedMatrix F

theorem constructionClaim_of_constructionSteps (h : ConstructionSteps)
    (h8 : StepPhysicalMode) (h9 : PressureProjectionStep) : ConstructionClaim := by
  obtain ⟨F, h1, h2, h3, h6, h7⟩ := h
  exact constructionClaim_of_steps F h1 h2 h3 h6 h7 h8 h9

end UnforcedLeray.Blueprint
