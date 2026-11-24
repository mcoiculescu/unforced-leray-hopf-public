import UnforcedLeray.Lib.PhaseSpace.CutoffCalc
import UnforcedLeray.Lib.PhaseSpace.PointSingularity

/-!
# Spatial cutoffs and their multiplier families (helper for INF25 T25.3)

The cutoff `χₙ(y) = ψ(y/(n+1))` with the bump `ψ = 1` on the closed unit ball and `ψ = 0`
outside the ball of radius `2` (`unitBump`, from `PointSingularity.lean`). The commutators
of `∂ⱼ`, `Δ` and `T₀ᵗ` with `χₙ` (`CutoffCalc.lean`) produce the multipliers

* `χₙ − 1`, `(y·∇χₙ)/2`: profiles vanishing on the unit ball, evaluated at `y/(n+1)`;
* `∂ⱼχₙ`, `2∂ⱼχₙ`, `Δχₙ`: bounded profiles times `(n+1)⁻¹` or `(n+1)⁻²`.

Each family is uniformly bounded and tends to zero pointwise (`GoodMult`), which is what
`tendsto_testElem_mulT` needs.

Status: infrastructure only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

/-- A multiplier family: continuous, uniformly bounded, tending to zero pointwise. -/
structure GoodMult (m : ℕ → Space → ℝ) : Prop where
  cont : ∀ n, Continuous (m n)
  bound : ∃ L, ∀ n y, |m n y| ≤ L
  lim : ∀ y, Tendsto (fun n => m n y) atTop (𝓝 0)

/-- The scale `(n + 1)⁻¹`. -/
def cutC (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem cutC_pos (n : ℕ) : 0 < cutC n := by unfold cutC; positivity

theorem cutC_le_one (n : ℕ) : cutC n ≤ 1 := by
  unfold cutC
  exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem tendsto_cutC : Tendsto cutC atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- The cutoff `χₙ(y) = ψ(y/(n+1))`. -/
def cutχ (n : ℕ) (y : Space) : ℝ := unitBump (cutC n • y)

theorem contDiff_unitBump : ContDiff ℝ ∞ (unitBump : Space → ℝ) := unitBump.contDiff

theorem contDiff_cutχ (n : ℕ) : ContDiff ℝ ∞ (cutχ n) :=
  contDiff_unitBump.comp (contDiff_const_smul _)

theorem cutχ_eq_zero (n : ℕ) {y : Space} (hy : 2 * ((n : ℝ) + 1) ≤ ‖y‖) : cutχ n y = 0 :=
  bump_scale_eq_zero (cutC_pos n) (by rwa [cutC, inv_inv])

/-! ### Profiles -/

/-- A profile vanishing on the open unit ball, rescaled, gives a good family. -/
theorem goodMult_of_vanish {b : Space → ℝ} (hb : Continuous b) {B : ℝ} (hB : ∀ z, |b z| ≤ B)
    (hb0 : ∀ z, ‖z‖ < 1 → b z = 0) {s : ℕ → ℝ} {S : ℝ} (hS : ∀ n, |s n| ≤ S) :
    GoodMult fun n y => s n * b (cutC n • y) where
  cont n := continuous_const.mul (hb.comp (continuous_const_smul _))
  bound := ⟨S * B, fun n y => by
    rw [abs_mul]
    exact mul_le_mul (hS n) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hS n))⟩
  lim y := by
    have h1 : Tendsto (fun n => cutC n * ‖y‖) atTop (𝓝 0) := by
      simpa using tendsto_cutC.mul_const ‖y‖
    have hev : ∀ᶠ n in atTop, cutC n * ‖y‖ < 1 := h1.eventually (gt_mem_nhds one_pos)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    rw [hb0 _ (by rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (cutC_pos n)]), mul_zero]

/-- A bounded profile times a vanishing scalar gives a good family. -/
theorem goodMult_of_small {b : Space → ℝ} (hb : Continuous b) {B : ℝ} (hB : ∀ z, |b z| ≤ B)
    {s : ℕ → ℝ} {S : ℝ} (hS : ∀ n, |s n| ≤ S) (hs : Tendsto s atTop (𝓝 0)) :
    GoodMult fun n y => s n * b (cutC n • y) where
  cont n := continuous_const.mul (hb.comp (continuous_const_smul _))
  bound := ⟨S * B, fun n y => by
    rw [abs_mul]
    exact mul_le_mul (hS n) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hS n))⟩
  lim y := by
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    refine squeeze_zero_norm (fun n => ?_) (by simpa using (hs.norm.mul_const B))
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)

theorem bounded_of_compact {b : Space → ℝ} (hb : Continuous b) (hbs : HasCompactSupport b) :
    ∃ B, ∀ z, |b z| ≤ B := by
  obtain ⟨B, hB⟩ := hb.bounded_above_of_compact_support hbs
  exact ⟨B, fun z => by simpa [Real.norm_eq_abs] using hB z⟩

theorem hasCompactSupport_sd {b : Space → ℝ} (hbs : HasCompactSupport b) (j : Fin 3) :
    HasCompactSupport (sd j b) :=
  hbs.fderiv_apply (𝕜 := ℝ) (coordinateVector j)

theorem sd_unitBump_eq_zero {z : Space} (hz : ‖z‖ < 1) (j : Fin 3) :
    sd j (unitBump : Space → ℝ) z = 0 := by
  have hev : (unitBump : Space → ℝ) =ᶠ[𝓝 z] fun _ => 1 := by
    have hopen : IsOpen {y : Space | ‖y‖ < 1} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen.mem_nhds hz] with y hy
    refine unitBump.one_of_mem_closedBall ?_
    simpa [unitBump] using hy.le
  simp [sd, hev.fderiv_eq]

theorem sd_const_mul {h : Space → ℝ} (hh : Differentiable ℝ h) (c : ℝ) (j : Fin 3) :
    sd j (fun y => c * h y) = fun y => c * sd j h y := by
  funext y
  simp [sd, fderiv_const_mul (hh y)]

/-! ### The five multiplier families -/

/-- `χₙ − 1`. -/
theorem goodMult_cutχ_sub_one : GoodMult fun n y => cutχ n y - 1 := by
  have h := goodMult_of_vanish (b := fun z => unitBump z - 1)
    (contDiff_unitBump.continuous.sub continuous_const) (B := 1)
    (fun z => by
      rw [abs_le]
      constructor <;> linarith [unitBump.nonneg' z, (unitBump.le_one : unitBump z ≤ 1)])
    (fun z hz => by
      rw [unitBump.one_of_mem_closedBall (by simpa [unitBump] using hz.le), sub_self])
    (s := fun _ => 1) (S := 1) (fun _ => by simp)
  simpa [cutχ] using h

theorem sd_cutχ (n : ℕ) (j : Fin 3) :
    sd j (cutχ n) = fun y => cutC n * sd j (unitBump : Space → ℝ) (cutC n • y) :=
  sd_comp_smul (contDiff_unitBump.differentiable (by simp)) (cutC n) j

/-- `c ∂ⱼχ` for a fixed real `c`. -/
theorem goodMult_sd_cutχ (j : Fin 3) (c : ℝ) : GoodMult fun n y => c * sd j (cutχ n) y := by
  obtain ⟨B, hB⟩ := bounded_of_compact (contDiff_sd contDiff_unitBump j).continuous
    (hasCompactSupport_sd unitBump.hasCompactSupport j)
  have h := goodMult_of_small (contDiff_sd contDiff_unitBump j).continuous hB
    (s := fun n => c * cutC n) (S := |c|)
    (fun n => by
      rw [abs_mul, abs_of_pos (cutC_pos n)]
      exact mul_le_of_le_one_right (abs_nonneg _) (cutC_le_one n))
    (by simpa using tendsto_cutC.const_mul c)
  simpa [sd_cutχ, mul_assoc] using h

/-- `Δχₙ`. -/
theorem goodMult_lapS_cutχ : GoodMult fun n y => lapS (cutχ n) y := by
  have hb : ContDiff ℝ ∞ (lapS (unitBump : Space → ℝ)) :=
    ContDiff.sum fun j _ => contDiff_sd (contDiff_sd contDiff_unitBump j) j
  have hbs : HasCompactSupport (lapS (unitBump : Space → ℝ)) := by
    have : lapS (unitBump : Space → ℝ) =
        ∑ j : Fin 3, sd j (sd j (unitBump : Space → ℝ)) := by
      funext y
      simp [lapS]
    rw [this]
    exact HasCompactSupport.finset_sum fun j _ =>
      hasCompactSupport_sd (hasCompactSupport_sd unitBump.hasCompactSupport j) j
  obtain ⟨B, hB⟩ := bounded_of_compact hb.continuous hbs
  have h := goodMult_of_small hb.continuous hB (s := fun n => cutC n ^ 2) (S := 1)
    (fun n => by
      rw [abs_pow, abs_of_pos (cutC_pos n)]
      exact pow_le_one₀ (cutC_pos n).le (cutC_le_one n))
    (by simpa using tendsto_cutC.pow 2)
  have hid : ∀ n, lapS (cutχ n) =
      fun y => cutC n ^ 2 * lapS (unitBump : Space → ℝ) (cutC n • y) := by
    intro n
    funext y
    have hj : ∀ j : Fin 3, sd j (sd j (cutχ n)) y =
        cutC n ^ 2 * sd j (sd j (unitBump : Space → ℝ)) (cutC n • y) := by
      intro j
      have hg : Differentiable ℝ (sd j (unitBump : Space → ℝ)) :=
        (contDiff_sd contDiff_unitBump j).differentiable (by simp)
      have hgc : Differentiable ℝ (fun y => sd j (unitBump : Space → ℝ) (cutC n • y)) :=
        hg.comp (differentiable_id.const_smul (cutC n))
      simp only [sd_cutχ, sd_const_mul hgc, sd_comp_smul hg]
      ring
    simp only [lapS, hj, Finset.mul_sum]
  simpa [hid] using h

/-- `(y·∇χₙ)/2`. -/
theorem goodMult_radS_cutχ : GoodMult fun n y => (1 / 2 : ℝ) * radS (cutχ n) y := by
  set b : Space → ℝ := fun z => (1 / 2 : ℝ) * radS (unitBump : Space → ℝ) z with hbdef
  have hcoord : ∀ j : Fin 3, Continuous fun z : Space => z j := fun j =>
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous
  have hb : Continuous b := by
    refine continuous_const.mul ?_
    exact continuous_finset_sum _ fun j _ =>
      (hcoord j).mul (contDiff_sd contDiff_unitBump j).continuous
  have hbs : HasCompactSupport b := by
    refine unitBump.hasCompactSupport.mono' fun z hz => ?_
    by_contra hzt
    apply hz
    simp [hbdef, radS, sd, fderiv_of_notMem_tsupport ℝ hzt]
  obtain ⟨B, hB⟩ := bounded_of_compact hb hbs
  have h := goodMult_of_vanish hb hB
    (fun z hz => by simp [hbdef, radS, sd_unitBump_eq_zero hz])
    (s := fun _ => 1) (S := 1) (fun _ => by simp)
  have hid : ∀ n y, (1 / 2 : ℝ) * radS (cutχ n) y = 1 * b (cutC n • y) := by
    intro n y
    simp only [hbdef, radS, sd_cutχ, PiLp.smul_apply, smul_eq_mul, one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have heq : (fun n y => (1 / 2 : ℝ) * radS (cutχ n) y) = fun n y => 1 * b (cutC n • y) := by
    funext n y
    exact hid n y
  rw [heq]
  exact h

end UnforcedLeray.PhaseSpace
