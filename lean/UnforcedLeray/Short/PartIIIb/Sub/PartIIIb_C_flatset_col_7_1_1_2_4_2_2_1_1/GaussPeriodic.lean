import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Lib.Gaussian.LatticeSum
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `SFCGaussPeriodicBound` (source 3426-3430)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The plane Gaussian density `G_θ(z)` on `ℝ × ℝ`. -/
def gz (θ : ℝ) (z : ℝ × ℝ) : ℝ :=
  (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * θ))

theorem gz_neg (θ : ℝ) (z : ℝ × ℝ) : gz θ (-z) = gz θ z := by
  simp [gz]

theorem gz_continuous (θ : ℝ) : Continuous (gz θ) := by
  unfold gz
  fun_prop

theorem gaussKernel_planeι (θ : ℝ) (y : Euc 2) :
    gaussKernel 2 θ y = gz θ (UnforcedLeray.B0224.planeι y) := by
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  unfold gaussKernel gz
  rw [hn]
  rfl

theorem planeι_measurePreserving :
    MeasurePreserving (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) volume volume := by
  have h := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hfun : (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) =
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ∘ (WithLp.ofLp) := by
    funext y
    rfl
  rw [hfun]
  exact h

/-- Squared distance of a lattice point from the cell: a lower bound `(v + t)² ≥ t²/4` when
`|v| ≤ c/2` and `t = 0` or `|t| ≥ c`. -/
theorem sq_add_ge_quarter {v t c : ℝ} (hc : 0 < c) (hv : |v| ≤ c / 2) (ht : c ≤ |t| ∨ t = 0) :
    t ^ 2 / 4 ≤ (v + t) ^ 2 := by
  rcases ht with ht | ht
  · have hA : |t| - |v| ≤ |v + t| := by
      have h := abs_sub (v + t) v
      rw [add_sub_cancel_left] at h
      linarith
    have hB : 0 ≤ |t| / 2 := by positivity
    have hA' : |t| / 2 ≤ |v + t| := by linarith
    nlinarith [sq_abs t, sq_abs (v + t), mul_self_le_mul_self hB hA']
  · subst ht
    nlinarith [sq_nonneg v]

/-- Lattice Gaussian sum bound (uniform in the shift `u`, with time `θ > 0`, period `c > 0`). -/
theorem lattice_gauss_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (u : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(u + n * c) ^ 2 / (4 * θ))) ∧
      ∑' n : ℤ, Real.exp (-(u + n * c) ^ 2 / (4 * θ)) ≤
        ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2)) := by
  set β : ℝ := c ^ 2 / (16 * θ) with hβ
  have hβpos : 0 < β := by positivity
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hnat : Summable (fun m : ℕ => Real.exp (-(β * ((m : ℤ) : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_)
      (UnforcedLeray.Gaussian.summable_exp_neg_mul_nat hβpos)
    apply Real.exp_le_exp.2
    have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases m.eq_zero_or_pos with h0 | hpos
      · subst h0; simp
      · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
        nlinarith
    have hcast : ((m : ℤ) : ℝ) = (m : ℝ) := by simp
    rw [hcast]
    nlinarith [mul_le_mul_of_nonneg_left hm hβpos.le]
  have hint : Summable (fun m : ℤ => Real.exp (-(β * (m : ℝ) ^ 2))) := by
    apply Summable.of_nat_of_neg
    · exact hnat
    · simpa [neg_sq] using hnat
  -- reduce the shift: `n₀` puts `v = u + n₀ c` in `[-c/2, c/2]`
  set n₀ : ℤ := ⌊-u / c + 1 / 2⌋ with hn₀
  set v : ℝ := u + n₀ * c with hv
  have hf1 : (n₀ : ℝ) ≤ -u / c + 1 / 2 := Int.floor_le _
  have hf2 : -u / c + 1 / 2 < (n₀ : ℝ) + 1 := Int.lt_floor_add_one _
  have hut : -u / c * c = -u := div_mul_cancel₀ _ hc.ne'
  have hv1 : v ≤ c / 2 := by nlinarith
  have hv2 : -(c / 2) ≤ v := by nlinarith
  have hvabs : |v| ≤ c / 2 := abs_le.2 ⟨hv2, hv1⟩
  -- the shifted series is the same series
  have hG : Summable (fun m : ℤ => Real.exp (-(v + m * c) ^ 2 / (4 * θ))) := by
    refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_) hint
    have hq := sq_add_ge_quarter (v := v) (t := (m : ℝ) * c) hc hvabs
      (by
        rcases eq_or_ne m 0 with h0 | h0
        · right; simp [h0]
        · left
          have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
            have : (1 : ℤ) ≤ |m| := Int.one_le_abs h0
            exact_mod_cast this
          rw [abs_mul, abs_of_pos hc]
          nlinarith)
    have e1 : -(v + m * c) ^ 2 / (4 * θ) ≤ -((m * c) ^ 2 / 4) / (4 * θ) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e2 : -((m * c) ^ 2 / 4) / (4 * θ) = -(β * (m : ℝ) ^ 2) := by
      rw [hβ]
      field_simp
      ring
    rw [e2] at e1
    exact Real.exp_le_exp.2 e1
  have hF : Summable (fun n : ℤ => Real.exp (-(u + n * c) ^ 2 / (4 * θ))) := by
    rw [← (Equiv.addRight n₀).summable_iff]
    refine hG.congr (fun m => ?_)
    simp only [Function.comp, Equiv.coe_addRight]
    congr 2
    rw [hv]
    push_cast
    ring
  refine ⟨hF, ?_⟩
  have hre : ∑' n : ℤ, Real.exp (-(u + n * c) ^ 2 / (4 * θ)) =
      ∑' m : ℤ, Real.exp (-(v + m * c) ^ 2 / (4 * θ)) := by
    rw [← (Equiv.addRight n₀).tsum_eq]
    refine tsum_congr (fun m => ?_)
    simp only [Equiv.coe_addRight]
    congr 2
    rw [hv]
    push_cast
    ring
  rw [hre]
  refine Summable.tsum_le_tsum (fun m => ?_) hG hint
  have hq := sq_add_ge_quarter (v := v) (t := (m : ℝ) * c) hc hvabs
    (by
      rcases eq_or_ne m 0 with h0 | h0
      · right; simp [h0]
      · left
        have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
          have : (1 : ℤ) ≤ |m| := Int.one_le_abs h0
          exact_mod_cast this
        rw [abs_mul, abs_of_pos hc]
        nlinarith)
  have e1 : -(v + m * c) ^ 2 / (4 * θ) ≤ -((m * c) ^ 2 / 4) / (4 * θ) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have e2 : -((m * c) ^ 2 / 4) / (4 * θ) = -(β * (m : ℝ) ^ 2) := by
    rw [hβ]
    field_simp
    ring
  rw [e2] at e1
  exact Real.exp_le_exp.2 e1

/-- The periodized plane Gaussian sum, real version. -/
theorem periodic_gz_sum_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (z : ℝ × ℝ) :
    Summable (fun n : ℤ => gz θ (z.1 + n * c, z.2)) ∧
    ∑' n : ℤ, gz θ (z.1 + n * c, z.2) ≤
      (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
        ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2)) := by
  have hC0 : 0 ≤ (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) := by positivity
  obtain ⟨hs, hle⟩ := lattice_gauss_le (u := z.1) hc hθ
  have hterm : ∀ n : ℤ, gz θ (z.1 + n * c, z.2) ≤
      (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-(z.1 + n * c) ^ 2 / (4 * θ)) := by
    intro n
    unfold gz
    try dsimp only
    apply mul_le_mul_of_nonneg_left _ hC0
    apply Real.exp_le_exp.2
    have h2 : 0 ≤ z.2 ^ 2 / (4 * θ) := by positivity
    have h3 : -((z.1 + n * c) ^ 2 + z.2 ^ 2) / (4 * θ) =
        -(z.1 + n * c) ^ 2 / (4 * θ) - z.2 ^ 2 / (4 * θ) := by ring
    rw [h3]
    linarith
  have hgnn : ∀ n : ℤ, 0 ≤ gz θ (z.1 + n * c, z.2) := by
    intro n
    unfold gz
    try dsimp only
    positivity
  have hsumm : Summable (fun n : ℤ => gz θ (z.1 + n * c, z.2)) :=
    Summable.of_nonneg_of_le hgnn hterm (hs.mul_left _)
  refine ⟨hsumm, ?_⟩
  calc ∑' n : ℤ, gz θ (z.1 + n * c, z.2)
      ≤ ∑' n : ℤ, (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
          Real.exp (-(z.1 + n * c) ^ 2 / (4 * θ)) :=
        Summable.tsum_le_tsum hterm hsumm (hs.mul_left _)
    _ = (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
          ∑' n : ℤ, Real.exp (-(z.1 + n * c) ^ 2 / (4 * θ)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hC0

/-- **Lemma 1 (Gaussian-weighted periodic bound, source 3426-3430).** -/
theorem sfcGaussPeriodicBound : SFCGaussPeriodicBound := by
  unfold SFCGaussPeriodicBound
  intro c θ hc hθ
  refine ⟨ENNReal.ofReal ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
      ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2))), ENNReal.ofReal_lt_top, ?_⟩
  intro φ hφm hφp w
  have hgnn : ∀ (z : ℝ × ℝ) (n : ℤ), 0 ≤ gz θ (z.1 + n * c, z.2) := by
    intro z n
    unfold gz
    try dsimp only
    positivity
  have hgmeas : Measurable (gz θ) := (gz_continuous θ).measurable
  have hg : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (gz θ z) * φ (w - z)) :=
    (ENNReal.measurable_ofReal.comp hgmeas).mul (hφm.comp (measurable_const.sub measurable_id))
  -- Step 1: move to the plane
  have e1 : ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (w - UnforcedLeray.B0224.planeι y)
      = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (gz θ z) * φ (w - z) := by
    rw [← planeι_measurePreserving.lintegral_comp hg]
    refine lintegral_congr (fun y => ?_)
    try dsimp only
    rw [gaussKernel_planeι]
  -- Step 2: reflect `z ↦ -z` (the density is even)
  have hneg := (Measure.measurePreserving_neg (volume : Measure (ℝ × ℝ))).lintegral_comp hg
  have e2 : ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (gz θ z) * φ (w - z)
      = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (gz θ z) * φ (w + z) := by
    rw [← hneg]
    refine lintegral_congr (fun z => ?_)
    try dsimp only
    rw [gz_neg, sub_neg_eq_add]
  -- Step 3: unfold along the cell lattice
  have hper : ∀ (n : ℤ) (z : ℝ × ℝ), φ (w + (z.1 + n * c, z.2)) = φ (w + z) := by
    intro n z
    have hw : w + (z.1 + n * c, z.2) = ((w + z).1 + n * c, (w + z).2) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [hw]
    exact hφp.add_int_mul n (w + z)
  have e3 := Cyl.lintegral_eq_tsum_cell (c := c) hc
    (fun z : ℝ × ℝ => ENNReal.ofReal (gz θ z) * φ (w + z))
  try dsimp only at e3
  have hAm : ∀ n : ℤ, Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (gz θ (z.1 + n * c, z.2)) * φ (w + z)) := by
    intro n
    have hsh : Measurable (fun z : ℝ × ℝ => (z.1 + n * c, z.2)) :=
      (measurable_fst.add_const _).prodMk measurable_snd
    exact (ENNReal.measurable_ofReal.comp ((gz_continuous θ).measurable.comp hsh)).mul
      (hφm.comp (measurable_const.add measurable_id))
  have hpt : ∀ z : ℝ × ℝ, ∑' n : ℤ, ENNReal.ofReal (gz θ (z.1 + n * c, z.2)) ≤
      ENNReal.ofReal ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
        ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2))) := by
    intro z
    obtain ⟨hs, hb⟩ := periodic_gz_sum_le hc hθ z
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hgnn z n) hs]
    exact ENNReal.ofReal_le_ofReal hb
  have htr : ∫⁻ z in Cyl.cell c, φ (w + z) = ∫⁻ z in Cyl.cell c, φ z := by
    simp_rw [add_comm w]
    exact Cyl.lintegral_cell_comp_add hc hφp w
  have e4 : ∑' n : ℤ, ∫⁻ z in Cyl.cell c, ENNReal.ofReal (gz θ (z.1 + n * c, z.2)) *
      φ (w + (z.1 + n * c, z.2)) = ∑' n : ℤ, ∫⁻ z in Cyl.cell c,
      ENNReal.ofReal (gz θ (z.1 + n * c, z.2)) * φ (w + z) :=
    tsum_congr (fun n => lintegral_congr (fun z => by rw [hper n z]))
  rw [e1, e2, e3, e4]
  calc ∑' n : ℤ, ∫⁻ z in Cyl.cell c, ENNReal.ofReal (gz θ (z.1 + n * c, z.2)) * φ (w + z)
      = ∫⁻ z in Cyl.cell c, ∑' n : ℤ, ENNReal.ofReal (gz θ (z.1 + n * c, z.2)) * φ (w + z) :=
        (lintegral_tsum (fun n => (hAm n).aemeasurable)).symm
    _ ≤ ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
          ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2))) * φ (w + z) := by
        refine lintegral_mono (fun z => ?_)
        rw [ENNReal.tsum_mul_right]
        gcongr
        exact hpt z
    _ = ENNReal.ofReal ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
          ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2))) *
          ∫⁻ z in Cyl.cell c, φ (w + z) :=
        lintegral_const_mul _ (hφm.comp (measurable_const.add measurable_id))
    _ = ENNReal.ofReal ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
          ∑' m : ℤ, Real.exp (-((c ^ 2 / (16 * θ)) * (m : ℝ) ^ 2))) *
          ∫⁻ x in UnforcedLeray.B0224.strip c, φ x := by
        rw [htr, UnforcedLeray.B0224.lintegral_strip_eq_cell hc hφp]


end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
