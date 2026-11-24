import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# `PartIII-b:C/rep/4/2/org/3/org`: support and late output of the stream transitions

Source `the November 2 reference manuscript` 5312-5321 ("They are supported on
`0.8/ν < s < 1/ν`"; "On late output, `g(s)⁻¹ ≤ e^{-4γ/(9ν)}`"), 5116 (`g(s) = exp(γs/(1+νs))`).

* (a) `transField_zero_outside`: `transCut` and `transComm` vanish at every `y` with `ϱ y > 0`
  unless `4/5 ≤ ν s ≤ 1`, `s = R²/ϱ²` (the two endpoints are a null set; the source's open
  annulus is contained in this closed one, which is all that a.e. statements use).
* (b) `ginv_le_late`: `g⁻¹ ≤ e^{-4γ/(9ν)}` on `ν s ≥ 4/5`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## (a) support -/

theorem continuous_ϱ : Continuous fun y : Space => ϱ y := by
  unfold ϱ
  have h0 : Continuous fun y : Space => y 0 := (EuclideanSpace.proj (0 : Fin 3)).continuous
  have h1 : Continuous fun y : Space => y 1 := (EuclideanSpace.proj (1 : Fin 3)).continuous
  fun_prop

/-- The open set `{ϱ > 0, ν age < 4/5}`. -/
theorem isOpen_young (ν R : ℝ) :
    IsOpen {y : Space | 0 < ϱ y ∧ ν * R ^ 2 < (4 / 5) * ϱ y ^ 2} :=
  (isOpen_lt continuous_const continuous_ϱ).inter
    (isOpen_lt continuous_const (continuous_const.mul (continuous_ϱ.pow 2)))

/-- The open set `{ϱ > 0, ν age > 1}`. -/
theorem isOpen_oldSide (ν R : ℝ) :
    IsOpen {y : Space | 0 < ϱ y ∧ ϱ y ^ 2 < ν * R ^ 2} :=
  (isOpen_lt continuous_const continuous_ϱ).inter
    (isOpen_lt (continuous_ϱ.pow 2) continuous_const)

theorem nu_age_lt_iff {ν R : ℝ} {y : Space} (hy : 0 < ϱ y) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 < t) :
    ν * age R y < t ↔ ν * R ^ 2 < t * ϱ y ^ 2 := by
  unfold age
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]

theorem lt_nu_age_iff {ν R : ℝ} {y : Space} (hy : 0 < ϱ y) {t : ℝ} :
    t < ν * age R y ↔ t * ϱ y ^ 2 < ν * R ^ 2 := by
  unfold age
  rw [← mul_div_assoc, lt_div_iff₀ (by positivity)]

/-- Near `ν age < 4/5` the stream cutoff is the identity: `χ_y = 1`, `χ_y' = 0`. -/
theorem wardStreamCut_eq_self_young {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (h : ν * age R y < 4 / 5) :
    wardStreamCut ν R χy Z τ y = Z τ y := by
  have h1 : χy (ν * age R y) = 1 := hχ.one _ h.le
  have hev : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with u hu using hχ.one u (le_of_lt hu)
  have h2 : deriv χy (ν * age R y) = 0 := by rw [hev.deriv_eq]; simp
  unfold wardStreamCut
  rw [h1, h2]
  simp

/-- Beyond `ν age > 1` the stream cut vanishes identically. -/
theorem wardStreamCut_eq_zero_old {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (h : 1 < ν * age R y) :
    wardStreamCut ν R χy Z τ y = 0 := by
  obtain ⟨h0, hd⟩ := streamCut_zero_of_gt hχ h
  unfold wardStreamCut
  rw [h0, hd]
  simp

/-- `D_μ` is local: it only reads the field on a neighbourhood of `y`. -/
theorem physDmu_congr_nhds {ν μ : ℝ} {X X' : ℝ → Space → Space} {y : Space}
    (h : ∀ τ, X τ =ᶠ[𝓝 y] X' τ) (τ : ℝ) :
    physDmu ν μ X τ y = physDmu ν μ X' τ y := by
  have hX : ∀ t, X t y = X' t y := fun t => (h t).eq_of_nhds
  have hf : fderiv ℝ (X τ) y = fderiv ℝ (X' τ) y := (h τ).fderiv_eq
  have hf2 : ∀ j : Fin 3, (fun y' => fderiv ℝ (X τ) y' (coordinateVector j)) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ (X' τ) y' (coordinateVector j) := by
    intro j
    filter_upwards [(h τ).eventuallyEq_nhds] with y' hy'
    rw [hy'.fderiv_eq]
  have hlap : physLap (X τ) y = physLap (X' τ) y := by
    unfold physLap physPd2 physPd
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hf2 j).fderiv_eq]
  unfold physDmu
  rw [show (fun t => X t y) = fun t => X' t y from funext hX, hf, hlap, hX τ]


theorem physDmu_zero (ν μ : ℝ) (τ : ℝ) (y : Space) :
    physDmu ν μ (fun _ _ => (0 : Space)) τ y = 0 := by
  unfold physDmu physLap physPd2 physPd
  simp

theorem streamCorr_zero_of {ν R : ℝ} {χy : ℝ → ℝ} (Z : ℝ → Space → Space) (τ : ℝ) (y : Space)
    (hd : deriv χy (ν * age R y) = 0) : streamCorr ν R χy Z τ y = 0 := by
  unfold streamCorr
  rw [hd]
  simp

/-- **(a) support of the two stream transitions** (source 5312-5316: "supported on
`0.8/ν < s < 1/ν`"; `χ_y' = 0` for `νs < 4/5` and `νs > 1`; `χ_y = 1` resp. `0` there and both are
locally constant, so `D_{μ+1}` commutes with `𝒞_y` away from the annulus): at every `y` with
`ϱ y > 0`, outside `4/5 ≤ ν s ≤ 1` (`s = R²/ϱ²`; the endpoints are a null set) both
`transCut` and `transComm` vanish. -/
theorem transField_zero_outside {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (ν μ R c : ℝ)
    (g : Chart → Ten3) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (hout : ν * age R y < 4 / 5 ∨ 1 < ν * age R y) :
    transCut ν μ R c χy g τ y = 0 ∧ transComm ν μ R c χy g τ y = 0 := by
  rcases hout with h | h
  · have hev : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with u hu using hχ.one u (le_of_lt hu)
    refine ⟨streamCorr_zero_of _ _ _ (by rw [hev.deriv_eq]; simp), ?_⟩
    have hn : {y' : Space | 0 < ϱ y' ∧ ν * R ^ 2 < (4 / 5) * ϱ y' ^ 2} ∈ 𝓝 y := by
      refine (isOpen_young ν R).mem_nhds ⟨hy, ?_⟩
      have h' : ν * age R y < 4 / 5 := h
      unfold age at h'
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)] at h'
      exact h'
    have hX : ∀ τ', wardX ν μ R c χy g τ' =ᶠ[𝓝 y] wardX0 ν μ R c g τ' := by
      intro τ'
      filter_upwards [hn] with y' hy'
      have h2 : ν * age R y' < 4 / 5 := by
        unfold age
        rw [← mul_div_assoc, div_lt_iff₀ (by have := hy'.1; positivity)]
        exact hy'.2
      exact wardStreamCut_eq_self_young hχ _ τ' h2
    unfold transComm
    rw [physDmu_congr_nhds (X' := wardX0 ν μ R c g) hX τ,
      wardStreamCut_eq_self_young hχ _ τ h]
    simp
  · have hn : {y' : Space | 0 < ϱ y' ∧ ϱ y' ^ 2 < ν * R ^ 2} ∈ 𝓝 y := by
      refine (isOpen_oldSide ν R).mem_nhds ⟨hy, ?_⟩
      have h' : 1 < ν * age R y := h
      unfold age at h'
      rw [← mul_div_assoc, lt_div_iff₀ (by positivity)] at h'
      linarith
    refine ⟨streamCorr_zero_of _ _ _ ?_, ?_⟩
    · have hev : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h] with u hu using hχ.zero u (le_of_lt hu)
      rw [hev.deriv_eq]; simp
    · have hX : ∀ τ', wardX ν μ R c χy g τ' =ᶠ[𝓝 y] fun _ => (0 : Space) := by
        intro τ'
        filter_upwards [hn] with y' hy'
        have h2 : 1 < ν * age R y' := by
          unfold age
          rw [← mul_div_assoc, lt_div_iff₀ (by have := hy'.1; positivity)]
          linarith [hy'.2]
        exact wardStreamCut_eq_zero_old hχ _ τ' h2
      unfold transComm
      rw [physDmu_congr_nhds (X' := fun _ _ => (0 : Space)) hX τ, physDmu_zero,
        wardStreamCut_eq_zero_old hχ _ τ h]
      simp

/-! ## (b) late output -/

/-- **(b) late output** (source 5317-5321: "`g(s)⁻¹ ≤ e^{-4γ/(9ν)}`" on `s ≥ 0.8/ν`, `g(s) =
exp(γs/(1+νs))`, 5116): for `γ ≥ 0`, `ν > 0` and `4/5 ≤ νs`, `ginv ≤ exp(-(4γ/9)/ν)`. -/
theorem ginv_le_late {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) (hp : 4 / 5 ≤ ν * p.1) :
    ginv γ ν p ≤ Real.exp (-(4 * γ / 9) / ν) := by
  have hs : 0 ≤ p.1 := by
    by_contra h
    push_neg at h
    nlinarith
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  rw [max_eq_left hs, ← Real.exp_neg]
  apply Real.exp_le_exp.2
  have h1 : 0 < 1 + ν * p.1 := by positivity
  have h2 : 4 * γ / 9 / ν ≤ γ * p.1 / (1 + ν * p.1) := by
    rw [div_div, div_le_div_iff₀ (by positivity) h1]
    nlinarith [mul_nonneg hγ (sub_nonneg.2 hp)]
  have : -(4 * γ / 9) / ν = -(4 * γ / 9 / ν) := by ring
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
