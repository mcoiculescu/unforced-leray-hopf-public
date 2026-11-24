import UnforcedLeray.Lib.SobolevB.Density

/-!
# Density of `C_c^∞` in weighted `W^{k,p}(ρ; ℝⁿ)` (INF11 target S4, weighted)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S4, `W.dense_smooth` with a weight). Manuscript uses:
density of `C_c^∞` in `H^j_M` with the weight `⟨y⟩^{2M}` (tex 1238–1243, B0063), smooth
approximation in weighted spaces (tex 13970–13985, B0892).

Every `Sob.Weight` is bounded above and below by positive constants on compact sets
(`Weight.locBdd`). After the cutoff `χ_m` (`W.tendsto_cutoff`, any weight) all components
vanish outside a ball (`W.cutoff_deriv_vanishes`, from `lcoef_eq_zero_of_notMem_tsupport`);
on a fixed compact set the weighted and unweighted `L^p` norms are comparable
(`eLpNorm_wμ_le_of_vanish`, `eLpNorm_le_wμ_of_vanish`), so the unweighted mollifier
convergence `tendsto_eLpNorm_moll_sub` gives convergence of the componentwise mollification
in `W^{k,p}(ρ)` (`W.tendsto_mollifyW`). No growth condition on `ρ` is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

/-! ### Supports of the Leibniz coefficients -/

theorem lcoef_eq_zero_of_notMem_tsupport {n : ℕ} (a : Eucl n → ℝ) (w u : List (Fin n))
    {x : Eucl n} (hx : x ∉ tsupport a) : lcoef a w u x = 0 := by
  induction w generalizing u x with
  | nil =>
    rw [lcoef_nil]
    split_ifs
    · exact image_eq_zero_of_notMem_tsupport hx
    · rfl
  | cons j w ih =>
    rw [lcoef_cons]
    have h1 : fderiv ℝ (lcoef a w u) x = 0 := by
      have hev : lcoef a w u =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hx] with y hy
        exact ih u hy
      rw [hev.fderiv_eq]
      simp
    have h2 : ltail j (lcoef a w) u x = 0 := by
      cases u with
      | nil => rfl
      | cons l u =>
        simp only [ltail]
        split_ifs
        · exact ih u hx
        · rfl
    rw [h1, h2]
    simp

theorem tsupport_cutR_subset {n : ℕ} (m : ℕ) :
    tsupport (cutR (n := n) m) ⊆ closedBall 0 (2 * ((m : ℝ) + 1)) := by
  refine (closure_mono fun x hx => ?_).trans closure_ball_subset_closedBall
  rw [mem_ball_zero_iff]
  by_contra h
  exact hx (cutR_eq_zero (not_lt.mp h))

/-! ### Comparison of weighted and unweighted norms on a compact set -/

section Compare

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

theorem eLpNorm_wμ_le_of_vanish (ρ : Weight (Eucl n)) {K : Set (Eucl n)} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ h : Eucl n → F,
      (∀ᵐ x ∂volume, x ∉ K → h x = 0) →
        eLpNorm h p (wμ volume ρ) ≤ C * eLpNorm h p volume := by
  obtain ⟨a, B, _, hab⟩ := ρ.locBdd K hK
  have hKm : MeasurableSet K := hK.measurableSet
  refine ⟨ENNReal.ofReal B ^ (1 / p).toReal, ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top, fun h hh => ?_⟩
  have hind : h =ᵐ[volume] K.indicator h := by
    filter_upwards [hh] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK, hx hxK]
  have hle : (wμ volume ρ).restrict K ≤ ENNReal.ofReal B • volume.restrict K := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      wμ, withDensity_apply _ (hs.inter hKm)]
    calc ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ≤ ∫⁻ _ in s ∩ K, ENNReal.ofReal B :=
          setLIntegral_mono' (hs.inter hKm) fun x hx => ENNReal.ofReal_le_ofReal (hab x hx.2).2
      _ = ENNReal.ofReal B * volume (s ∩ K) := setLIntegral_const _ _
  rw [eLpNorm_congr_ae ((ae_eq_wμ_iff volume ρ).mpr hind), eLpNorm_congr_ae hind,
    eLpNorm_indicator_eq_eLpNorm_restrict hKm, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  calc eLpNorm h p ((wμ volume ρ).restrict K)
      ≤ eLpNorm h p (ENNReal.ofReal B • volume.restrict K) := eLpNorm_mono_measure _ hle
    _ = ENNReal.ofReal B ^ (1 / p).toReal * eLpNorm h p (volume.restrict K) := by
        rw [eLpNorm_smul_measure_of_ne_top hp]; rfl

theorem eLpNorm_le_wμ_of_vanish (ρ : Weight (Eucl n)) {K : Set (Eucl n)} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ h : Eucl n → F,
      (∀ᵐ x ∂volume, x ∉ K → h x = 0) →
        eLpNorm h p volume ≤ C * eLpNorm h p (wμ volume ρ) := by
  obtain ⟨a, B, ha, hab⟩ := ρ.locBdd K hK
  have hKm : MeasurableSet K := hK.measurableSet
  refine ⟨ENNReal.ofReal a⁻¹ ^ (1 / p).toReal, ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top, fun h hh => ?_⟩
  have hind : h =ᵐ[volume] K.indicator h := by
    filter_upwards [hh] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK, hx hxK]
  have hle : volume.restrict K ≤ ENNReal.ofReal a⁻¹ • (wμ volume ρ).restrict K := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      wμ, withDensity_apply _ (hs.inter hKm)]
    have h1 : ENNReal.ofReal a * volume (s ∩ K) ≤ ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hs.inter hKm) fun x hx => ENNReal.ofReal_le_ofReal (hab x hx.2).1
    calc volume (s ∩ K) = ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * volume (s ∩ K)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) := by gcongr
  rw [eLpNorm_congr_ae ((ae_eq_wμ_iff volume ρ).mpr hind), eLpNorm_congr_ae hind,
    eLpNorm_indicator_eq_eLpNorm_restrict hKm, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  calc eLpNorm h p (volume.restrict K)
      ≤ eLpNorm h p (ENNReal.ofReal a⁻¹ • (wμ volume ρ).restrict K) := eLpNorm_mono_measure _ hle
    _ = ENNReal.ofReal a⁻¹ ^ (1 / p).toReal * eLpNorm h p ((wμ volume ρ).restrict K) := by
        rw [eLpNorm_smul_measure_of_ne_top hp]; rfl

end Compare

/-! ### Mollification of compactly supported elements of weighted `W` -/

section Far

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem moll_eq_zero_far {f : Eucl n → F} {R : ℝ} (hf : ∀ᵐ x ∂volume, x ∉ closedBall 0 R → f x = 0)
    (b : ContDiffBump (0 : Eucl n)) (hb : b.rOut ≤ 1) {x : Eucl n}
    (hx : x ∉ closedBall (0 : Eucl n) (R + 1)) : moll b volume f x = 0 := by
  rw [moll, cv_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hf] with t ht
  by_cases htR : t ∈ closedBall (0 : Eucl n) R
  · have hfar : b.rOut ≤ dist (x - t) 0 := by
      rw [dist_zero_right]
      rw [mem_closedBall_zero_iff] at htR
      rw [mem_closedBall_zero_iff, not_le] at hx
      have := norm_sub_norm_le x t
      linarith
    simp [b.normed_def, b.zero_of_le_dist hfar]
  · simp [ht htR]

end Far

section MollW

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {ρ : Weight (Eucl n)}

instance isFiniteMeasureOnCompacts_wμ (ρ : Weight (Eucl n)) :
    IsFiniteMeasureOnCompacts (wμ volume ρ) :=
  ⟨fun _ hK => wμ_lt_top hK⟩

/-- All components of `y` vanish a.e. outside the ball of radius `R`. -/
def VanishOutside (y : W (wholeSpace n) ρ 𝕜 F k p) (R : ℝ) : Prop :=
  ∀ α : Idx n k, ∀ᵐ x ∂volume, x ∉ closedBall (0 : Eucl n) R →
    W.deriv (wholeSpace n) ρ 𝕜 F k p α y x = 0

theorem W.cutoff_vanishOutside (m : ℕ) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    VanishOutside (W.cutoff m x) (2 * ((m : ℝ) + 1)) := by
  intro α
  have h := (ae_eq_wμ_iff volume ρ).mp (W.coeFn_deriv_mulCoeff (bddDerivs_cutR k m) x α)
  rw [← W.cutoff_apply] at h
  filter_upwards [h] with y hy hyK
  rw [hy]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [lcoef_eq_zero_of_notMem_tsupport _ _ _ fun h => hyK (tsupport_cutR_subset m h), zero_smul]

variable (hp : p ≠ ⊤) (b : ContDiffBump (0 : Eucl n))

theorem W.locallyIntegrable_derivW (y : W (wholeSpace n) ρ 𝕜 F k p) (α : Idx n k) :
    LocallyIntegrable (W.deriv (wholeSpace n) ρ 𝕜 F k p α y) volume :=
  locallyIntegrable_of_memLp (Lp.memLp _)

theorem W.memLp_moll_derivW (y : W (wholeSpace n) ρ 𝕜 F k p) {R : ℝ}
    (hy : VanishOutside y R) (α : Idx n k) :
    MemLp (moll b volume (W.deriv (wholeSpace n) ρ 𝕜 F k p α y)) p (wμ volume ρ) :=
  (contDiff_moll b (W.locallyIntegrable_derivW y α)).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_cv b.hasCompactSupport_normed (isCompact_closedBall 0 R) (hy α))

/-- The componentwise mollification of an element of `W^{k,p}(ρ)` vanishing outside a ball. -/
def W.mollifyW (y : W (wholeSpace n) ρ 𝕜 F k p) {R : ℝ} (hy : VanishOutside y R) :
    W (wholeSpace n) ρ 𝕜 F k p :=
  W.ofFields (fun α => moll b volume (W.deriv (wholeSpace n) ρ 𝕜 F k p α y))
    (W.memLp_moll_derivW b y hy) (fun α => by
      have h := hasWeakDeriv_of_contDiff (μ := volume) (dir := e)
        (contDiff_moll b (W.locallyIntegrable_derivW y Idx.zero)) ((wholeSpace n).word α)
      have e1 := iterDD_cv_of_hasWeakDeriv (μ := volume) (dir := e) (W.hasWeakDeriv y α)
        (b.contDiff_normed (μ := volume)) (b.hasCompactSupport_normed (μ := volume))
        (W.locallyIntegrable_derivW y Idx.zero)
      have h' : HasWeakDeriv (wholeSpaceOf (Eucl n) volume e) ((wholeSpace n).word α)
          (moll b volume (W.deriv (wholeSpace n) ρ 𝕜 F k p Idx.zero y))
          (iterDD ((wholeSpace n).word α)
            (cv volume (b.normed volume) (W.value (wholeSpace n) ρ 𝕜 F k p y))) := h
      rw [e1] at h'
      exact h')

theorem W.coeFn_value_mollifyW (y : W (wholeSpace n) ρ 𝕜 F k p) {R : ℝ} (hy : VanishOutside y R) :
    ⇑(W.value (wholeSpace n) ρ 𝕜 F k p (W.mollifyW b y hy)) =ᵐ[volume]
      moll b volume (W.value (wholeSpace n) ρ 𝕜 F k p y) :=
  (ae_eq_wμ_iff volume ρ).mp (W.memLp_moll_derivW b y hy Idx.zero).coeFn_toLp

omit hp in
/-- **Mollification converges in `W^{k,p}(ρ)`** for elements vanishing outside a ball. -/
theorem W.tendsto_mollifyW (hp : p ≠ ⊤) (y : W (wholeSpace n) ρ 𝕜 F k p) {R : ℝ}
    (hy : VanishOutside y R) :
    Tendsto (fun j => W.mollifyW (shrinkBump n j) y hy) atTop (𝓝 y) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hK : IsCompact (closedBall (0 : Eucl n) (R + 1)) := isCompact_closedBall 0 _
  obtain ⟨C₁, hC₁, h₁⟩ := eLpNorm_wμ_le_of_vanish (F := F) ρ hK hp
  obtain ⟨C₂, hC₂, h₂⟩ := eLpNorm_le_wμ_of_vanish (F := F) ρ hK hp
  refine W.tendsto_of_deriv fun α => ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set g : Eucl n → F := (W.deriv (wholeSpace n) ρ 𝕜 F k p α y : Eucl n → F)
  have hgK : ∀ᵐ x ∂volume, x ∉ closedBall (0 : Eucl n) (R + 1) → g x = 0 := by
    filter_upwards [hy α] with x hx hxK
    exact hx fun h => hxK (closedBall_subset_closedBall (by linarith) h)
  have hgm : MemLp g p volume := by
    refine ⟨(Lp.aestronglyMeasurable _).mono_ac (ac_wμ volume ρ), ?_⟩
    exact (h₂ g hgK).trans_lt (ENNReal.mul_lt_top hC₂.lt_top (Lp.eLpNorm_lt_top _))
  have hconv := tendsto_eLpNorm_moll_sub hp hgm (tendsto_shrinkBump_rOut n)
  have hlim : Tendsto (fun j => C₁ * eLpNorm (g - moll (shrinkBump n j) volume g) p volume)
      atTop (𝓝 (C₁ * 0)) := ENNReal.Tendsto.const_mul hconv (Or.inr hC₁)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun j => zero_le)
    fun j => ?_
  have hrw : eLpNorm (⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α (W.mollifyW (shrinkBump n j) y hy)) -
      g) p (wμ volume ρ) = eLpNorm (g - moll (shrinkBump n j) volume g) p (wμ volume ρ) := by
    rw [eLpNorm_sub_comm]
    refine eLpNorm_congr_ae ?_
    filter_upwards [(W.memLp_moll_derivW (shrinkBump n j) y hy α).coeFn_toLp] with x hx
    exact congrArg (_ - ·) hx
  show eLpNorm (⇑(W.deriv (wholeSpace n) ρ 𝕜 F k p α (W.mollifyW (shrinkBump n j) y hy)) - g) p
    (wμ volume ρ) ≤ _
  rw [hrw]
  refine h₁ _ ?_
  filter_upwards [hgK] with x hx hxK
  rw [Pi.sub_apply, hx hxK,
    moll_eq_zero_far (hy α) _ (by simp [shrinkBump]; exact inv_le_one_of_one_le₀ (by
      linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])) hxK, sub_zero]

end MollW

/-! ### Weighted density -/

section Dense

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Density of `C_c^∞` in `W^{k,p}(ρ; ℝⁿ)` for every weight** (S4, `W.dense_smooth`),
`1 ≤ p < ∞`: the elements whose value is a smooth compactly supported field are dense. -/
theorem W.dense_smooth_weight (ρ : Weight (Eucl n)) (hp : p ≠ ⊤) :
    Dense {x : W (wholeSpace n) ρ 𝕜 F k p | ∃ f : Eucl n → F, ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧ (W.value (wholeSpace n) ρ 𝕜 F k p x : Eucl n → F) =ᵐ[volume] f} := by
  set S := {x : W (wholeSpace n) ρ 𝕜 F k p | ∃ f : Eucl n → F, ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧ (W.value (wholeSpace n) ρ 𝕜 F k p x : Eucl n → F) =ᵐ[volume] f}
  set T := {y : W (wholeSpace n) ρ 𝕜 F k p | ∃ R : ℝ, VanishOutside y R}
  have hTS : T ⊆ closure S := by
    rintro y ⟨R, hy⟩
    refine mem_closure_of_tendsto (W.tendsto_mollifyW hp y hy) (Eventually.of_forall fun j => ?_)
    exact ⟨_, contDiff_moll _ (W.locallyIntegrable_derivW y Idx.zero),
      hasCompactSupport_cv (shrinkBump n j).hasCompactSupport_normed (isCompact_closedBall 0 R)
        (hy Idx.zero),
      W.coeFn_value_mollifyW (shrinkBump n j) y hy⟩
  have hT : ∀ x, x ∈ closure T := by
    intro x
    refine mem_closure_of_tendsto (W.tendsto_cutoff hp x) (Eventually.of_forall fun m => ?_)
    exact ⟨_, W.cutoff_vanishOutside m x⟩
  intro x
  exact closure_minimal hTS isClosed_closure (hT x)

end Dense

end UnforcedLeray.Sob
