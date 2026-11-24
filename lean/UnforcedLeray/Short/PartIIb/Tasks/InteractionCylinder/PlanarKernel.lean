import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1

/-!
# PartII-b:F1/4 — Cylinder vs planar Biot–Savart kernel bound with Gaussian coefficient

Proves `planarKernelBoundStep_proof : PlanarKernelBoundStep` (SP 2117–2131).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## 1. Weighted `L²` and `L¹` estimates on `planeMeasure m` -/

theorem planeMeasure_ac (m : ℝ) : planeMeasure m ≪ volume :=
  withDensity_absolutelyContinuous _ _

theorem volume_ac_planeMeasure (m : ℝ) : (volume : Measure B0579.Plane) ≪ planeMeasure m :=
  withDensity_absolutelyContinuous'
    (B0579.measurable_density m).coe_nnreal_ennreal.aemeasurable
    (Eventually.of_forall fun x => by simpa using (B0579.density_pos m x).ne')

theorem eLpNorm_planeMeasure (m : ℝ) (f : B0579.Plane → ℝ) :
    eLpNorm f 2 (planeMeasure m) =
      eLpNorm (fun x => B0579.jb x ^ (m / 2) * f x) 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), planeMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0, ← Real.rpow_natCast,
    ← Real.rpow_mul (B0579.jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

theorem one_le_jb (x : B0579.Plane) : 1 ≤ B0579.jb x := by
  unfold B0579.jb
  nlinarith [sq_nonneg x.1, sq_nonneg x.2]

theorem eLpNorm_volume_le_planeMeasure {m : ℝ} (hm : 0 ≤ m) (f : B0579.Plane → ℝ) :
    eLpNorm f 2 volume ≤ eLpNorm f 2 (planeMeasure m) := by
  rw [eLpNorm_planeMeasure]
  refine eLpNorm_mono_enorm fun x => ?_
  have h1 : 1 ≤ B0579.jb x ^ (m / 2) := Real.one_le_rpow (one_le_jb x) (by linarith)
  have h0 : 0 ≤ B0579.jb x ^ (m / 2) := by positivity
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg h0]
  exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (abs_nonneg _) h1)

theorem memLp_jb_rpow_neg {s : ℝ} (hs : 1 < 2 * s) :
    MemLp (fun y : B0579.Plane => B0579.jb y ^ (-s)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun y : B0579.Plane => B0579.jb y ^ (-s)) volume :=
    (B0579.continuous_jb_rpow (-s)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (Cyl.integrable_rpow_neg_ρc hs).congr (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ B0579.jb y ^ (-s) := Real.rpow_nonneg (B0579.jb_pos y).le _
  change Cyl.ρc y ^ (-(2 * s)) = ‖B0579.jb y ^ (-s)‖ ^ 2
  rw [Real.norm_of_nonneg h0, ← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos y).le]
  have heq : B0579.jb y = Cyl.ρc y := rfl
  rw [heq]
  congr 1
  push_cast
  ring

def jbNegL2Norm (s : ℝ) : ℝ :=
  (eLpNorm (fun y : B0579.Plane => B0579.jb y ^ (-s)) 2 volume).toReal

theorem jbNegL2Norm_nonneg (s : ℝ) : 0 ≤ jbNegL2Norm s :=
  ENNReal.toReal_nonneg

theorem ofReal_jbNegL2Norm {s : ℝ} (hs : 1 < 2 * s) :
    ENNReal.ofReal (jbNegL2Norm s) =
      eLpNorm (fun y : B0579.Plane => B0579.jb y ^ (-s)) 2 volume :=
  ENNReal.ofReal_toReal (memLp_jb_rpow_neg hs).eLpNorm_ne_top

theorem eLpNorm_jb_mul_one_le {m k : ℝ} (hmk : 1 < m - 2 * k) {g : B0579.Plane → ℝ}
    (hg : Measurable g) :
    eLpNorm (fun y => B0579.jb y ^ k * g y) 1 volume ≤
      ENNReal.ofReal (jbNegL2Norm (m / 2 - k)) * eLpNorm g 2 (planeMeasure m) := by
  set s : ℝ := m / 2 - k
  have hs : 1 < 2 * s := by dsimp [s]; linarith
  have hψ : AEStronglyMeasurable (fun y : B0579.Plane => B0579.jb y ^ (-s)) volume :=
    (B0579.continuous_jb_rpow (-s)).aestronglyMeasurable
  have hgw : AEStronglyMeasurable (fun y : B0579.Plane => B0579.jb y ^ (m / 2) * g y) volume :=
    ((B0579.continuous_jb_rpow (m / 2)).measurable.mul hg).aestronglyMeasurable
  have hfun : (fun y : B0579.Plane => B0579.jb y ^ k * g y) =
      (fun y => B0579.jb y ^ (-s)) • (fun y => B0579.jb y ^ (m / 2) * g y) := by
    funext y
    show B0579.jb y ^ k * g y = B0579.jb y ^ (-s) * (B0579.jb y ^ (m / 2) * g y)
    rw [← mul_assoc, B0579.jb_rpow_mul]
    congr 2
    dsimp [s]
    ring
  rw [hfun, ofReal_jbNegL2Norm hs, eLpNorm_planeMeasure]
  exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hgw hψ

/-! ## 2. Core disk `|x| ≤ c / 4` and tail bounds -/

theorem continuous_euclidNorm : Continuous euclidNorm := by
  unfold euclidNorm
  fun_prop

theorem euclidNorm_sq (x : B0579.Plane) : euclidNorm x ^ 2 = x.1 ^ 2 + x.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem euclidNorm_le_jb_half (x : B0579.Plane) :
    euclidNorm x ≤ B0579.jb x ^ (1 / 2 : ℝ) := by
  rw [euclidNorm, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt (by unfold B0579.jb; linarith)

theorem one_le_jb_half (x : B0579.Plane) : 1 ≤ B0579.jb x ^ (1 / 2 : ℝ) :=
  Real.one_le_rpow (one_le_jb x) (by norm_num)

theorem one_add_euclidNorm_le_two_jb_half (x : B0579.Plane) :
    1 + euclidNorm x ≤ 2 * B0579.jb x ^ (1 / 2 : ℝ) := by
  linarith [one_le_jb_half x, euclidNorm_le_jb_half x]

theorem one_add_euclidNorm_add_le (x y : B0579.Plane) :
    1 + euclidNorm x + euclidNorm y ≤
      4 * B0579.jb x ^ (1 / 2 : ℝ) * B0579.jb y ^ (1 / 2 : ℝ) := by
  have hx := one_add_euclidNorm_le_two_jb_half x
  have hy := one_add_euclidNorm_le_two_jb_half y
  have hx0 := euclidNorm_nonneg x
  have hy0 := euclidNorm_nonneg y
  have hjb_x : 0 ≤ 2 * B0579.jb x ^ (1 / 2 : ℝ) :=
    mul_nonneg zero_le_two (Real.rpow_nonneg (B0579.jb_pos x).le _)
  have h1 : 1 + euclidNorm x + euclidNorm y ≤ (1 + euclidNorm x) * (1 + euclidNorm y) := by
    nlinarith
  have h2 : (1 + euclidNorm x) * (1 + euclidNorm y) ≤
      (2 * B0579.jb x ^ (1 / 2 : ℝ)) * (2 * B0579.jb y ^ (1 / 2 : ℝ)) :=
    mul_le_mul hx hy (by positivity) hjb_x
  linarith

def coreDisk (c : ℝ) : Set B0579.Plane :=
  {x : B0579.Plane | euclidNorm x ≤ c / 4}

theorem measurableSet_coreDisk (c : ℝ) : MeasurableSet (coreDisk c) :=
  (isClosed_le continuous_euclidNorm continuous_const).measurableSet

theorem coreDisk_subset_cell {c : ℝ} (hc : 1 ≤ c) : coreDisk c ⊆ B0579.cell c := by
  intro x hx
  change euclidNorm x ≤ c / 4 at hx
  have hq : |x.1| ≤ euclidNorm x := by
    rw [← Real.sqrt_sq_eq_abs, euclidNorm]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x.2])
  have hq' : |x.1| ≤ c / 4 := hq.trans hx
  rw [abs_le] at hq'
  refine ⟨⟨by linarith, by linarith⟩, trivial⟩

theorem one_le_sixteen_inv_sq_mul_jb {c : ℝ} (hc : 1 ≤ c) {x : B0579.Plane}
    (hx : x ∉ coreDisk c) :
    1 ≤ 16 * c ^ (-2 : ℝ) * B0579.jb x := by
  have hc0 : 0 < c := by linarith
  have hlt : c / 4 < euclidNorm x := not_le.mp hx
  have hsq : (c / 4) ^ 2 ≤ euclidNorm x ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlt.le 2
  have hjb : (c / 4) ^ 2 ≤ B0579.jb x := by
    rw [euclidNorm_sq] at hsq
    unfold B0579.jb
    linarith
  rw [Real.rpow_neg hc0.le, Real.rpow_two]
  have h1 : 1 = 16 * (c ^ 2)⁻¹ * (c / 4) ^ 2 := by
    have : c ≠ 0 := hc0.ne'
    field_simp
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left hjb (by positivity)

theorem eLpNorm_tail_two_le {c m : ℝ} (hc : 1 ≤ c) (hm : 2 ≤ m) (g : B0579.Plane → ℝ) :
    eLpNorm ((coreDisk c)ᶜ.indicator g) 2 volume ≤
      ENNReal.ofReal (16 * c ^ (-2 : ℝ)) * eLpNorm g 2 (planeMeasure m) := by
  have hc0 : 0 ≤ 16 * c ^ (-2 : ℝ) := by positivity
  rw [eLpNorm_planeMeasure]
  calc eLpNorm ((coreDisk c)ᶜ.indicator g) 2 volume
      ≤ eLpNorm ((16 * c ^ (-2 : ℝ)) • fun y => B0579.jb y ^ (m / 2) * g y) 2 volume := by
        refine eLpNorm_mono_enorm fun y => ?_
        by_cases hy : y ∈ coreDisk c
        · rw [indicator_of_notMem (Set.notMem_compl_iff.mpr hy), enorm_zero]
          exact bot_le
        · rw [indicator_of_mem (mem_compl hy), Pi.smul_apply, smul_eq_mul,
            Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := one_le_sixteen_inv_sq_mul_jb hc hy
          have hpow : B0579.jb y ^ (1 : ℝ) ≤ B0579.jb y ^ (m / 2) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_jb y) (by linarith)
          rw [Real.rpow_one] at hpow
          have h2 : 1 ≤ 16 * c ^ (-2 : ℝ) * B0579.jb y ^ (m / 2) :=
            h1.trans (mul_le_mul_of_nonneg_left hpow hc0)
          have hjb0 : 0 ≤ B0579.jb y ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
          rw [abs_mul (16 * c ^ (-2 : ℝ)), abs_mul (B0579.jb y ^ (m / 2)),
            abs_of_nonneg hc0, abs_of_nonneg hjb0, ← mul_assoc]
          exact le_mul_of_one_le_left (abs_nonneg _) h2
    _ = ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
          eLpNorm (fun y => B0579.jb y ^ (m / 2) * g y) 2 volume := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]

theorem eLpNorm_tail_one_le {c m : ℝ} (hc : 1 ≤ c) (hm : 4 < m) {g : B0579.Plane → ℝ}
    (hg : Measurable g) :
    eLpNorm ((coreDisk c)ᶜ.indicator g) 1 volume ≤
      ENNReal.ofReal (16 * jbNegL2Norm (m / 2 - 1) * c ^ (-2 : ℝ)) *
        eLpNorm g 2 (planeMeasure m) := by
  have hc0 : 0 ≤ 16 * c ^ (-2 : ℝ) := by positivity
  have h1 : eLpNorm ((coreDisk c)ᶜ.indicator g) 1 volume ≤
      ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
        eLpNorm (fun y => B0579.jb y ^ (1 : ℝ) * g y) 1 volume := by
    calc eLpNorm ((coreDisk c)ᶜ.indicator g) 1 volume
        ≤ eLpNorm ((16 * c ^ (-2 : ℝ)) • fun y => B0579.jb y ^ (1 : ℝ) * g y) 1 volume := by
          refine eLpNorm_mono_enorm fun y => ?_
          by_cases hy : y ∈ coreDisk c
          · rw [indicator_of_notMem (Set.notMem_compl_iff.mpr hy), enorm_zero]
            exact bot_le
          · rw [indicator_of_mem (mem_compl hy), Pi.smul_apply, smul_eq_mul,
              Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
            refine ENNReal.ofReal_le_ofReal ?_
            have hjb := one_le_sixteen_inv_sq_mul_jb hc hy
            have hjb0 : 0 ≤ B0579.jb y := (B0579.jb_pos y).le
            rw [Real.rpow_one, abs_mul (16 * c ^ (-2 : ℝ)), abs_mul (B0579.jb y),
              abs_of_nonneg hc0, abs_of_nonneg hjb0, ← mul_assoc]
            exact le_mul_of_one_le_left (abs_nonneg _) hjb
      _ = ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            eLpNorm (fun y => B0579.jb y ^ (1 : ℝ) * g y) 1 volume := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]
  have h2 := eLpNorm_jb_mul_one_le (m := m) (k := 1) (by linarith) hg
  calc eLpNorm ((coreDisk c)ᶜ.indicator g) 1 volume
      ≤ ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
          (ENNReal.ofReal (jbNegL2Norm (m / 2 - 1)) * eLpNorm g 2 (planeMeasure m)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (bot_le))
    _ = ENNReal.ofReal (16 * jbNegL2Norm (m / 2 - 1) * c ^ (-2 : ℝ)) *
          eLpNorm g 2 (planeMeasure m) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc0]
        congr 2
        ring

/-! ## 3. Weighted Gaussian decay of `planarGradE σ` -/

def gradSum (σ : ℝ) (x : B0579.Plane) : ℝ :=
  |(planarGradE σ x).1| + |(planarGradE σ x).2|

theorem gradSum_nonneg (σ : ℝ) (x : B0579.Plane) : 0 ≤ gradSum σ x := by
  unfold gradSum
  positivity

theorem continuous_planarGradE (σ : ℝ) : Continuous (planarGradE σ) := by
  have hsc : Continuous fun x : B0579.Plane => ofPlane (scalePlane (1 + σ) x) := by
    have h1 : (fun x : B0579.Plane => ofPlane (scalePlane (1 + σ) x)) =
        fun x => ((x.1 / Real.sqrt (1 + σ) : ℝ) : ℂ) +
          ((x.2 / Real.sqrt (1 + σ) : ℝ) : ℂ) * Complex.I := by
      funext x
      exact ofPlane_eq_add_mul_I (scalePlane (1 + σ) x)
    rw [h1]
    fun_prop
  unfold planarGradE
  exact (continuous_const.mul (B0009.continuous_gradE0_fst.comp hsc)).prodMk
    (continuous_const.mul (B0009.continuous_gradE0_snd.comp hsc))

theorem continuous_gradSum (σ : ℝ) : Continuous (gradSum σ) := by
  unfold gradSum
  exact ((continuous_planarGradE σ).fst.abs).add ((continuous_planarGradE σ).snd.abs)

private theorem rpow_mul_exp_neg_quarter_le (k : ℝ) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ (k + 2) * Real.exp (-(s / 4)) ≤ C := by
  set N : ℕ := ⌈k⌉₊ + 3
  have hN_pos : 0 < (N : ℝ) := by dsimp [N]; positivity
  have h4N_ge : 1 ≤ 4 * (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by
      dsimp [N]
      exact_mod_cast Nat.le_add_left 3 ⌈k⌉₊
    linarith
  have hkN : k + 2 ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    linarith [Nat.le_ceil k]
  refine ⟨(4 * (N : ℝ)) ^ N, by positivity, fun s hs => ?_⟩
  have h1s : 1 ≤ 1 + s := by linarith
  have hrpow : (1 + s) ^ (k + 2) ≤ (1 + s) ^ N := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1s hkN
  have hlin : 1 + s ≤ 4 * (N : ℝ) * (1 + s / (4 * (N : ℝ))) := by
    have : 4 * (N : ℝ) ≠ 0 := by positivity
    have heq : 4 * (N : ℝ) * (1 + s / (4 * (N : ℝ))) = 4 * (N : ℝ) + s := by
      field_simp
    linarith
  have hexp1 : 1 + s / (4 * (N : ℝ)) ≤ Real.exp (s / (4 * (N : ℝ))) := by
    linarith [Real.add_one_le_exp (s / (4 * (N : ℝ)))]
  have hbase : 1 + s ≤ 4 * (N : ℝ) * Real.exp (s / (4 * (N : ℝ))) :=
    hlin.trans (mul_le_mul_of_nonneg_left hexp1 (by positivity))
  have hpow : (1 + s) ^ N ≤ (4 * (N : ℝ)) ^ N * Real.exp (s / 4) := by
    calc (1 + s) ^ N
        ≤ (4 * (N : ℝ) * Real.exp (s / (4 * (N : ℝ)))) ^ N :=
          pow_le_pow_left₀ (by positivity) hbase N
      _ = (4 * (N : ℝ)) ^ N * (Real.exp (s / (4 * (N : ℝ)))) ^ N := mul_pow _ _ _
      _ = (4 * (N : ℝ)) ^ N * Real.exp (s / 4) := by
          rw [← Real.exp_nat_mul]
          congr 2
          have : (N : ℝ) ≠ 0 := hN_pos.ne'
          field_simp
  calc (1 + s) ^ (k + 2) * Real.exp (-(s / 4))
      ≤ (1 + s) ^ N * Real.exp (-(s / 4)) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
    _ ≤ ((4 * (N : ℝ)) ^ N * Real.exp (s / 4)) * Real.exp (-(s / 4)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (4 * (N : ℝ)) ^ N * (Real.exp (s / 4) * Real.exp (-(s / 4))) := by ring
    _ = (4 * (N : ℝ)) ^ N := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem jb_mul_gradSum_sup_bound (k : ℝ) (hk : 0 ≤ k) (Sg : ℝ) (hSg : 0 < Sg) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ ∈ Icc 0 Sg, ∀ x : B0579.Plane,
      B0579.jb x ^ k * gradSum σ x ≤ M := by
  obtain ⟨C, hC, hC_bd⟩ := rpow_mul_exp_neg_quarter_le k hk
  refine ⟨4 * (1 + Sg) ^ k * C, by positivity, fun σ hσ x => ?_⟩
  set a : ℝ := 1 + σ
  have ha1 : 1 ≤ a := by dsimp [a]; linarith [hσ.1]
  have haSg : a ≤ 1 + Sg := by dsimp [a]; linarith [hσ.2]
  have ha0 : 0 < a := by linarith
  set y : ℂ := ofPlane (scalePlane a x)
  have hy_sq : ‖y‖ ^ 2 = (x.1 ^ 2 + x.2 ^ 2) / a := by
    rw [norm_ofPlane_sq, scalePlane, div_pow, div_pow, ← add_div, Real.sq_sqrt ha0.le]
  have hjb_le : B0579.jb x ≤ (1 + Sg) * (1 + ‖y‖ ^ 2) := by
    have hxy : x.1 ^ 2 + x.2 ^ 2 = a * ‖y‖ ^ 2 := by
      rw [hy_sq, mul_div_cancel₀ _ ha0.ne']
    unfold B0579.jb
    calc 1 + x.1 ^ 2 + x.2 ^ 2 = 1 + a * ‖y‖ ^ 2 := by linarith
      _ ≤ (1 + Sg) + (1 + Sg) * ‖y‖ ^ 2 := by
          nlinarith [sq_nonneg ‖y‖]
      _ = (1 + Sg) * (1 + ‖y‖ ^ 2) := by ring
  have hjb_rpow : B0579.jb x ^ k ≤ (1 + Sg) ^ k * (1 + ‖y‖ ^ 2) ^ k := by
    calc B0579.jb x ^ k
        ≤ ((1 + Sg) * (1 + ‖y‖ ^ 2)) ^ k :=
          Real.rpow_le_rpow (B0579.jb_pos x).le hjb_le hk
      _ = (1 + Sg) ^ k * (1 + ‖y‖ ^ 2) ^ k :=
          Real.mul_rpow (by positivity) (by positivity)
  have ha_pow : a ^ (-5 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
  have ha_pow_nn : 0 ≤ a ^ (-5 / 2 : ℝ) := Real.rpow_nonneg ha0.le _
  have hgrad : gradSum σ x =
      a ^ (-5 / 2 : ℝ) * |GaussianVortex.radialK ‖y‖| * (|y.re| + |y.im|) := by
    unfold gradSum planarGradE
    change |a ^ (-5 / 2 : ℝ) * (B0009.gradE0 y).1| +
      |a ^ (-5 / 2 : ℝ) * (B0009.gradE0 y).2| = _
    rw [B0009.gradE0_eq y]
    simp only [abs_mul, abs_of_nonneg ha_pow_nn]
    ring
  have hre_im : |y.re| + |y.im| ≤ 1 + ‖y‖ ^ 2 := by
    have hre : |y.re| ≤ ‖y‖ := Complex.abs_re_le_norm y
    have him : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    nlinarith [sq_nonneg (‖y‖ - 1)]
  have hradK : |GaussianVortex.radialK ‖y‖| ≤ 2 * (1 + ‖y‖ ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4)) := by
    unfold GaussianVortex.radialK GaussianVortex.radialOmega
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |‖y‖ ^ 2 / 4 - 2| ≤ 2 * (1 + ‖y‖ ^ 2) := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg ‖y‖]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hgrad_le : gradSum σ x ≤ 4 * (1 + ‖y‖ ^ 2) ^ (2 : ℝ) * Real.exp (-(‖y‖ ^ 2 / 4)) := by
    rw [hgrad]
    have h1 : a ^ (-5 / 2 : ℝ) * |GaussianVortex.radialK ‖y‖| * (|y.re| + |y.im|) ≤
        1 * (2 * (1 + ‖y‖ ^ 2) * Real.exp (-(‖y‖ ^ 2 / 4))) * (1 + ‖y‖ ^ 2) := by
      refine mul_le_mul (mul_le_mul ha_pow hradK (abs_nonneg _) zero_le_one) hre_im
        (by positivity) (by positivity)
    have h2 : (1 + ‖y‖ ^ 2) ^ (2 : ℝ) = (1 + ‖y‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
      rw [Real.rpow_two, sq]
    rw [h2]
    nlinarith [Real.exp_pos (-(‖y‖ ^ 2 / 4)), sq_nonneg ‖y‖]
  calc B0579.jb x ^ k * gradSum σ x
      ≤ ((1 + Sg) ^ k * (1 + ‖y‖ ^ 2) ^ k) *
          (4 * (1 + ‖y‖ ^ 2) ^ (2 : ℝ) * Real.exp (-(‖y‖ ^ 2 / 4))) :=
        mul_le_mul hjb_rpow hgrad_le (gradSum_nonneg σ x) (by positivity)
    _ = 4 * (1 + Sg) ^ k * ((1 + ‖y‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ (2 : ℝ) *
          Real.exp (-(‖y‖ ^ 2 / 4))) := by ring
    _ = 4 * (1 + Sg) ^ k * ((1 + ‖y‖ ^ 2) ^ (k + 2) * Real.exp (-(‖y‖ ^ 2 / 4))) := by
        rw [← Real.rpow_add (by positivity)]
    _ ≤ 4 * (1 + Sg) ^ k * C :=
        mul_le_mul_of_nonneg_left (hC_bd (‖y‖ ^ 2) (sq_nonneg _)) (by positivity)

theorem planarGradE_weighted_bound (k : ℝ) (hk : 0 ≤ k) (Sg : ℝ) (hSg : 0 < Sg) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ ∈ Icc 0 Sg,
      (∀ x : B0579.Plane, B0579.jb x ^ k * gradSum σ x ≤ B) ∧
      eLpNorm (fun x : B0579.Plane => B0579.jb x ^ k * gradSum σ x) 2 volume ≤
        ENNReal.ofReal B := by
  obtain ⟨M₀, hM₀, hbd₀⟩ := jb_mul_gradSum_sup_bound k hk Sg hSg
  obtain ⟨M₁, hM₁, hbd₁⟩ := jb_mul_gradSum_sup_bound (k + 1) (by linarith) Sg hSg
  set B : ℝ := M₀ + M₁ * jbNegL2Norm 1
  have hB : 0 < B := add_pos_of_pos_of_nonneg hM₀ (mul_nonneg hM₁.le (jbNegL2Norm_nonneg 1))
  refine ⟨B, hB, fun σ hσ => ⟨fun x => ?_, ?_⟩⟩
  · exact (hbd₀ σ hσ x).trans (le_add_of_nonneg_right (mul_nonneg hM₁.le (jbNegL2Norm_nonneg 1)))
  · have h1 : eLpNorm (fun x : B0579.Plane => B0579.jb x ^ k * gradSum σ x) 2 volume ≤
        ENNReal.ofReal M₁ * eLpNorm (fun x : B0579.Plane => B0579.jb x ^ (-1 : ℝ)) 2 volume := by
      calc eLpNorm (fun x : B0579.Plane => B0579.jb x ^ k * gradSum σ x) 2 volume
          ≤ eLpNorm (M₁ • fun x : B0579.Plane => B0579.jb x ^ (-1 : ℝ)) 2 volume := by
            refine eLpNorm_mono_enorm fun x => ?_
            have hx0 : 0 ≤ B0579.jb x ^ k * gradSum σ x :=
              mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (gradSum_nonneg σ x)
            have hinv0 : 0 ≤ B0579.jb x ^ (-1 : ℝ) := Real.rpow_nonneg (B0579.jb_pos x).le _
            rw [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal hx0,
              Real.enorm_eq_ofReal (mul_nonneg hM₁.le hinv0)]
            refine ENNReal.ofReal_le_ofReal ?_
            have heq : B0579.jb x ^ k * gradSum σ x =
                (B0579.jb x ^ (k + 1) * gradSum σ x) * B0579.jb x ^ (-1 : ℝ) := by
              rw [mul_right_comm, B0579.jb_rpow_mul, add_neg_cancel_right]
            rw [heq]
            exact mul_le_mul_of_nonneg_right (hbd₁ σ hσ x) hinv0
        _ = ENNReal.ofReal M₁ *
              eLpNorm (fun x : B0579.Plane => B0579.jb x ^ (-1 : ℝ)) 2 volume := by
            rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hM₁.le]
    rw [← ofReal_jbNegL2Norm (by norm_num : (1 : ℝ) < 2 * 1), ← ENNReal.ofReal_mul hM₁.le] at h1
    exact h1.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hM₀.le))

/-! ## 4. Near/far `L² + L^∞` bounds for `Cyl.K c` and `planarK` -/

private theorem qwrap_of_mem_Ico {c q : ℝ} (hc : 0 < c) (hq : q ∈ Ico (-c / 2) (c / 2)) :
    qwrap c q = q := by
  unfold qwrap
  have h0 : 0 ≤ (q + c / 2) / c := div_nonneg (by linarith [hq.1]) hc.le
  have h1 : (q + c / 2) / c < 1 := (div_lt_one hc).2 (by linarith [hq.2])
  rw [Int.floor_eq_zero_iff.2 ⟨h0, h1⟩]
  simp

private theorem qwrap_add_period {c q : ℝ} (hc : 0 < c) : qwrap c (q + c) = qwrap c q := by
  unfold qwrap
  have h : (q + c + c / 2) / c = (q + c / 2) / c + 1 := by
    rw [div_add_one hc.ne']
    congr 1
    ring
  rw [h, Int.floor_add_one]
  push_cast
  ring

def cellWrap (c : ℝ) (z : B0579.Plane) : B0579.Plane :=
  (qwrap c z.1, z.2)

theorem measurable_cellWrap (c : ℝ) : Measurable (cellWrap c) := by
  unfold cellWrap qwrap
  refine (measurable_fst.sub (measurable_const.mul ?_)).prodMk measurable_snd
  exact (measurable_of_countable _).comp
    (Int.measurable_floor.comp ((measurable_fst.add_const _).div_const _))

theorem cellWrap_of_mem {c : ℝ} (hc : 0 < c) {z : B0579.Plane} (hz : z ∈ Cyl.cell c) :
    cellWrap c z = z := by
  ext
  · exact qwrap_of_mem_Ico hc hz.1
  · rfl

theorem isPeriodic_comp_cellWrap {E : Type*} {c : ℝ} (hc : 0 < c) (g : B0579.Plane → E) :
    Cyl.IsPeriodic c (fun z => g (cellWrap c z)) := by
  intro z
  simp only [cellWrap, qwrap_add_period hc]

theorem b0579_cell_eq_cyl_cell (c : ℝ) : B0579.cell c = Cyl.cell c := by
  simp only [B0579.cell, Cyl.cell, neg_div]

def gPer (c : ℝ) (g : B0579.Plane → ℝ) (z : B0579.Plane) : ℝ :=
  g (cellWrap c z)

theorem measurable_gPer (c : ℝ) {g : B0579.Plane → ℝ} (hg : Measurable g) :
    Measurable (gPer c g) :=
  hg.comp (measurable_cellWrap c)

theorem isPeriodic_gPer {c : ℝ} (hc : 0 < c) (g : B0579.Plane → ℝ) :
    Cyl.IsPeriodic c (gPer c g) :=
  isPeriodic_comp_cellWrap hc g

theorem gPer_eq_on_cell {c : ℝ} (hc : 0 < c) (g : B0579.Plane → ℝ) {z : B0579.Plane}
    (hz : z ∈ Cyl.cell c) :
    gPer c g z = g z := by
  simp [gPer, cellWrap_of_mem hc hz]

theorem Cyl_K_eq_gPer {c : ℝ} (hc : 0 < c) (g : B0579.Plane → ℝ) (x : B0579.Plane) :
    Cyl.K c g x = Cyl.K c (gPer c g) x := by
  unfold Cyl.K
  refine setIntegral_congr_fun (Cyl.measurableSet_cell c) fun y hy => ?_
  rw [gPer_eq_on_cell hc g hy]

theorem eLpNorm_gPer_cell_le {c : ℝ} (hc : 0 < c) (g : B0579.Plane → ℝ) (p : ℝ≥0∞) :
    eLpNorm (gPer c g) p (Cyl.cellμ c) ≤ eLpNorm g p volume := by
  have hae : gPer c g =ᵐ[Cyl.cellμ c] g := by
    rw [Cyl.cellμ]
    exact (ae_restrict_iff' (Cyl.measurableSet_cell c)).mpr
      (Eventually.of_forall fun z hz => gPer_eq_on_cell hc g hz)
  rw [eLpNorm_congr_ae hae, Cyl.cellμ]
  exact eLpNorm_mono_measure g Measure.restrict_le_self

theorem lintegral_gPer_cell_le {c : ℝ} (hc : 0 < c) (g : B0579.Plane → ℝ) :
    ∫⁻ y in Cyl.cell c, ‖gPer c g y‖ₑ ≤ eLpNorm g 1 volume := by
  change ∫⁻ y, ‖gPer c g y‖ₑ ∂(Cyl.cellμ c) ≤ _
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_gPer_cell_le hc g 1

theorem cyl_K_ae_split_and_integrable {c : ℝ} (hc1 : 1 ≤ c) {g : B0579.Plane → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g volume) :
    ∀ᵐ x ∂volume, x ∈ Cyl.cell c →
      Cyl.K c g x = Cyl.uNear c (gPer c g) x + Cyl.uFar c (gPer c g) x ∧
      IntegrableOn (fun y => g y • Cyl.bsKernel c (x - y)) (Cyl.cell c) volume := by
  have hc0 : 0 < c := by linarith
  set ω : B0579.Plane → ℝ := gPer c g
  have hω_meas : Measurable ω := measurable_gPer c hg_meas
  have hω_per : Cyl.IsPeriodic c ω := isPeriodic_gPer hc0 g
  have hω_l1 : ∫⁻ y in Cyl.cell c, ‖ω y‖ₑ < ⊤ :=
    (lintegral_gPer_cell_le hc0 g).trans_lt (by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact hg_int.2)
  obtain ⟨C_bs, _, h_bs⟩ := Cyl.bsKernel_split
  obtain ⟨hkNear_l1, hkFar_bd, hk_sum⟩ := h_bs c hc1
  have hkNear_meas : Measurable (Cyl.kNear c) :=
    (Cyl.measurable_bsKernel c).indicator
      ((Cyl.measurableSet_cell c).inter Metric.isOpen_ball.measurableSet)
  have hkFar_meas : Measurable (Cyl.kFar c) :=
    (Cyl.measurable_bsKernel c).indicator
      ((Cyl.measurableSet_cell c).diff Metric.isOpen_ball.measurableSet)
  have hFar_int : ∀ x : B0579.Plane,
      Integrable (fun y => ω (x - y) • Cyl.kFar c y) (Cyl.cellμ c) := by
    intro x
    refine ⟨((hω_meas.comp (measurable_const.sub measurable_id)).smul
        hkFar_meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ y in Cyl.cell c, ‖ω (x - y) • Cyl.kFar c y‖ₑ
        ≤ ∫⁻ y in Cyl.cell c, ENNReal.ofReal 2 * ‖ω (x - y)‖ₑ := by
          refine lintegral_mono fun y => ?_
          rw [enorm_smul, mul_comm, ← ofReal_norm (Cyl.kFar c y)]
          gcongr
          exact hkFar_bd y
      _ = ENNReal.ofReal 2 * ∫⁻ y in Cyl.cell c, ‖ω (x - y)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal 2 * ∫⁻ y in Cyl.cell c, ‖ω y‖ₑ := by
          rw [Cyl.lintegral_cell_comp_sub_left hc0 (G := fun y => ‖ω y‖ₑ)
            (fun z => by simp only [hω_per z]) x]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω_l1
  have hNear_prod :
      ∫⁻ x in Cyl.cell c, ∫⁻ y in Cyl.cell c, ‖ω (x - y) • Cyl.kNear c y‖ₑ < ⊤ := by
    have hmeas_prod : Measurable (fun p : B0579.Plane × B0579.Plane =>
        ‖ω (p.1 - p.2) • Cyl.kNear c p.2‖ₑ) :=
      ((hω_meas.comp (measurable_fst.sub measurable_snd)).smul
        (hkNear_meas.comp measurable_snd)).enorm
    rw [lintegral_lintegral_swap hmeas_prod.aemeasurable]
    have hinner : ∀ y : B0579.Plane,
        ∫⁻ x in Cyl.cell c, ‖ω (x - y) • Cyl.kNear c y‖ₑ =
          ‖Cyl.kNear c y‖ₑ * ∫⁻ x in Cyl.cell c, ‖ω x‖ₑ := by
      intro y
      calc ∫⁻ x in Cyl.cell c, ‖ω (x - y) • Cyl.kNear c y‖ₑ
          = ∫⁻ x in Cyl.cell c, ‖Cyl.kNear c y‖ₑ * ‖ω (x - y)‖ₑ := by
            refine lintegral_congr fun x => ?_
            rw [enorm_smul, mul_comm]
        _ = ‖Cyl.kNear c y‖ₑ * ∫⁻ x in Cyl.cell c, ‖ω (x - y)‖ₑ :=
            lintegral_const_mul _ (hω_meas.comp (measurable_id.sub_const y)).enorm
        _ = ‖Cyl.kNear c y‖ₑ * ∫⁻ x in Cyl.cell c, ‖ω x‖ₑ := by
            congr 1
            simp_rw [sub_eq_add_neg]
            exact Cyl.lintegral_cell_comp_add (f := fun z => ‖ω z‖ₑ) hc0
              (fun z => by dsimp; rw [hω_per z]) (-y)
    simp_rw [hinner]
    rw [lintegral_mul_const _ hkNear_meas.enorm]
    exact ENNReal.mul_lt_top (hkNear_l1.trans_lt ENNReal.ofReal_lt_top) hω_l1
  have hNear_ae : ∀ᵐ x ∂Cyl.cellμ c,
      ∫⁻ y in Cyl.cell c, ‖ω (x - y) • Cyl.kNear c y‖ₑ < ⊤ := by
    refine ae_lt_top ?_ hNear_prod.ne
    exact Measurable.lintegral_prod_right'
      (((hω_meas.comp (measurable_fst.sub measurable_snd)).smul
        (hkNear_meas.comp measurable_snd)).enorm)
  rw [Cyl.cellμ, ae_restrict_iff' (Cyl.measurableSet_cell c)] at hNear_ae
  filter_upwards [hNear_ae] with x hx hxc
  have hNear_int : Integrable (fun y => ω (x - y) • Cyl.kNear c y) (Cyl.cellμ c) :=
    ⟨((hω_meas.comp (measurable_const.sub measurable_id)).smul
      hkNear_meas).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr (hx hxc)⟩
  have hK_eq : Cyl.K c g x = Cyl.uNear c ω x + Cyl.uFar c ω x := by
    rw [Cyl_K_eq_gPer hc0 g x]
    exact (Cyl.K_split.choose_spec.2 c hc1 ω hω_meas.stronglyMeasurable hω_per).2.2
      x hNear_int (hFar_int x)
  refine ⟨hK_eq, ?_⟩
  have hsum_int : Integrable (fun w => ω (x - w) • Cyl.bsKernel c w) (Cyl.cellμ c) := by
    refine (hNear_int.add (hFar_int x)).congr ?_
    rw [Cyl.cellμ]
    exact (ae_restrict_iff' (Cyl.measurableSet_cell c)).mpr
      (Eventually.of_forall fun w hw => by
        simp only [Pi.add_apply, hk_sum w hw, smul_add])
  have hG_per : Cyl.IsPeriodic c (fun w => ‖ω (x - w) • Cyl.bsKernel c w‖ₑ) := by
    intro w
    simp only [Cyl.isPeriodic_bsKernel c w]
    congr 2
    have h1 := hω_per.sub_eq (x - w)
    rw [← h1]
    congr 1
    ext <;> simp <;> ring
  have hrefl := Cyl.lintegral_cell_comp_sub_left hc0 hG_per x
  have hrefl' : ∫⁻ y in Cyl.cell c, ‖ω y • Cyl.bsKernel c (x - y)‖ₑ < ⊤ := by
    have heq : (fun y : B0579.Plane => ‖ω (x - (x - y)) • Cyl.bsKernel c (x - y)‖ₑ) =
        fun y => ‖ω y • Cyl.bsKernel c (x - y)‖ₑ := by
      funext y
      rw [sub_sub_cancel]
    rw [heq] at hrefl
    rw [hrefl]
    exact hsum_int.2
  refine ⟨(hg_meas.smul ((Cyl.measurable_bsKernel c).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcongr : ∫⁻ y in Cyl.cell c, ‖g y • Cyl.bsKernel c (x - y)‖ₑ =
      ∫⁻ y in Cyl.cell c, ‖ω y • Cyl.bsKernel c (x - y)‖ₑ :=
    setLIntegral_congr_fun (Cyl.measurableSet_cell c) fun y hy => by
      change ‖g y • Cyl.bsKernel c (x - y)‖ₑ = ‖gPer c g y • Cyl.bsKernel c (x - y)‖ₑ
      rw [gPer_eq_on_cell hc0 g hy]
  rw [hcongr]
  exact hrefl'

def cylSplitConst : ℝ := Cyl.K_split.choose

theorem cylSplitConst_nonneg : 0 ≤ cylSplitConst := Cyl.K_split.choose_spec.1

theorem aestronglyMeasurable_cyl_uNear (c : ℝ) {ω : B0579.Plane → ℝ}
    (hω : Measurable ω) :
    AEStronglyMeasurable (Cyl.uNear c ω) volume := by
  have hkNear : Measurable (Cyl.kNear c) :=
    (Cyl.measurable_bsKernel c).indicator
      ((Cyl.measurableSet_cell c).inter Metric.isOpen_ball.measurableSet)
  unfold Cyl.uNear
  exact (((hω.comp (measurable_fst.sub measurable_snd)).smul
    (hkNear.comp measurable_snd)).aestronglyMeasurable).integral_prod_right'

theorem aestronglyMeasurable_cyl_uFar (c : ℝ) {ω : B0579.Plane → ℝ}
    (hω : Measurable ω) :
    AEStronglyMeasurable (Cyl.uFar c ω) volume := by
  have hkFar : Measurable (Cyl.kFar c) :=
    (Cyl.measurable_bsKernel c).indicator
      ((Cyl.measurableSet_cell c).diff Metric.isOpen_ball.measurableSet)
  unfold Cyl.uFar
  exact (((hω.comp (measurable_fst.sub measurable_snd)).smul
    (hkFar.comp measurable_snd)).aestronglyMeasurable).integral_prod_right'

theorem aestronglyMeasurable_cyl_K (c : ℝ) {g : B0579.Plane → ℝ}
    (hg : Measurable g) :
    AEStronglyMeasurable (Cyl.K c g) volume := by
  unfold Cyl.K
  exact (((hg.comp measurable_snd).smul
    ((Cyl.measurable_bsKernel c).comp
      (measurable_fst.sub measurable_snd))).aestronglyMeasurable).integral_prod_right'

theorem eLpNorm_weighted_cyl_K_le {c : ℝ} (hc1 : 1 ≤ c)
    {w : B0579.Plane → ℝ} (hw_meas : Measurable w) (hw_nn : ∀ x, 0 ≤ w x)
    {B : ℝ} (hB : 0 ≤ B) (hw_sup : ∀ x, w x ≤ B)
    (hw_l2 : eLpNorm w 2 volume ≤ ENNReal.ofReal B)
    {g : B0579.Plane → ℝ} (hg_meas : Measurable g) (hg_int : Integrable g volume) :
    eLpNorm (fun x => w x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x) 2 volume ≤
      ENNReal.ofReal B * (ENNReal.ofReal cylSplitConst * eLpNorm g 2 volume +
        ENNReal.ofReal 2 * eLpNorm g 1 volume) := by
  have hc0 : 0 < c := by linarith
  set ω : B0579.Plane → ℝ := gPer c g
  have hω_meas : Measurable ω := measurable_gPer c hg_meas
  have hω_per : Cyl.IsPeriodic c ω := isPeriodic_gPer hc0 g
  obtain ⟨huNear_l2, huFar_sup, _⟩ :=
    Cyl.K_split.choose_spec.2 c hc1 ω hω_meas.stronglyMeasurable hω_per
  have hpt : ∀ᵐ x ∂volume,
      ‖w x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x‖ₑ ≤
        ‖(Cyl.cell c).indicator (fun x => B * ‖Cyl.uNear c ω x‖) x +
          w x * ‖Cyl.uFar c ω x‖‖ₑ := by
    filter_upwards [cyl_K_ae_split_and_integrable hc1 hg_meas hg_int] with x hx
    rw [b0579_cell_eq_cyl_cell]
    by_cases hxc : x ∈ Cyl.cell c
    · rw [indicator_of_mem hxc, indicator_of_mem hxc,
        Real.enorm_eq_ofReal (mul_nonneg (hw_nn x) (norm_nonneg _)),
        Real.enorm_eq_ofReal (add_nonneg (mul_nonneg hB (norm_nonneg _))
          (mul_nonneg (hw_nn x) (norm_nonneg _)))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [(hx hxc).1]
      calc w x * ‖Cyl.uNear c ω x + Cyl.uFar c ω x‖
          ≤ w x * (‖Cyl.uNear c ω x‖ + ‖Cyl.uFar c ω x‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw_nn x)
        _ = w x * ‖Cyl.uNear c ω x‖ + w x * ‖Cyl.uFar c ω x‖ := mul_add _ _ _
        _ ≤ B * ‖Cyl.uNear c ω x‖ + w x * ‖Cyl.uFar c ω x‖ := by
            gcongr
            exact hw_sup x
    · rw [indicator_of_notMem hxc, mul_zero, enorm_zero]
      exact bot_le
  have hm1 : AEStronglyMeasurable
      (fun x => (Cyl.cell c).indicator (fun x => B * ‖Cyl.uNear c ω x‖) x) volume :=
    (aestronglyMeasurable_const.mul (aestronglyMeasurable_cyl_uNear c hω_meas).norm).indicator
      (Cyl.measurableSet_cell c)
  have hm2 : AEStronglyMeasurable (fun x => w x * ‖Cyl.uFar c ω x‖) volume :=
    hw_meas.aestronglyMeasurable.mul (aestronglyMeasurable_cyl_uFar c hω_meas).norm
  have hNear_bd :
      eLpNorm ((Cyl.cell c).indicator (fun x => B * ‖Cyl.uNear c ω x‖)) 2 volume ≤
        ENNReal.ofReal B * (ENNReal.ofReal cylSplitConst * eLpNorm g 2 volume) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (Cyl.measurableSet_cell c), ← Cyl.cellμ]
    have hsmul : (fun x : B0579.Plane => B * ‖Cyl.uNear c ω x‖) =
        B • fun x => ‖Cyl.uNear c ω x‖ := rfl
    rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal hB, eLpNorm_norm]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    exact huNear_l2.trans (mul_le_mul_of_nonneg_left (eLpNorm_gPer_cell_le hc0 g 2) bot_le)
  have hFar_bd :
      eLpNorm (fun x => w x * ‖Cyl.uFar c ω x‖) 2 volume ≤
        ENNReal.ofReal B * (ENNReal.ofReal 2 * eLpNorm g 1 volume) := by
    set L : ℝ := (eLpNorm g 1 volume).toReal
    have hL_nn : 0 ≤ L := ENNReal.toReal_nonneg
    have hL_eq : ENNReal.ofReal L = eLpNorm g 1 volume := by
      refine ENNReal.ofReal_toReal ?_
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact hg_int.2.ne
    have hFar_pt : ∀ x, ‖Cyl.uFar c ω x‖ ≤ 2 * L := by
      intro x
      have h1 : ‖Cyl.uFar c ω x‖ₑ ≤ ENNReal.ofReal (2 * L) := by
        rw [ENNReal.ofReal_mul zero_le_two, hL_eq]
        exact (huFar_sup x).trans
          (mul_le_mul_of_nonneg_left (lintegral_gPer_cell_le hc0 g) bot_le)
      rw [← ofReal_norm] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    calc eLpNorm (fun x => w x * ‖Cyl.uFar c ω x‖) 2 volume
        ≤ eLpNorm ((2 * L) • w) 2 volume := by
          refine eLpNorm_mono_enorm fun x => ?_
          rw [Pi.smul_apply, smul_eq_mul,
            Real.enorm_eq_ofReal (mul_nonneg (hw_nn x) (norm_nonneg _)),
            Real.enorm_eq_ofReal (mul_nonneg (by positivity) (hw_nn x))]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_comm (2 * L)]
          exact mul_le_mul_of_nonneg_left (hFar_pt x) (hw_nn x)
      _ = ENNReal.ofReal (2 * L) * eLpNorm w 2 volume := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
      _ ≤ ENNReal.ofReal (2 * L) * ENNReal.ofReal B :=
          mul_le_mul_of_nonneg_left hw_l2 bot_le
      _ = ENNReal.ofReal B * (ENNReal.ofReal 2 * eLpNorm g 1 volume) := by
          rw [ENNReal.ofReal_mul zero_le_two, hL_eq]
          ring
  calc eLpNorm (fun x => w x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x) 2 volume
      ≤ eLpNorm (fun x => (Cyl.cell c).indicator (fun x => B * ‖Cyl.uNear c ω x‖) x +
          w x * ‖Cyl.uFar c ω x‖) 2 volume := eLpNorm_mono_enorm_ae hpt
    _ ≤ eLpNorm ((Cyl.cell c).indicator (fun x => B * ‖Cyl.uNear c ω x‖)) 2 volume +
          eLpNorm (fun x => w x * ‖Cyl.uFar c ω x‖) 2 volume :=
        eLpNorm_add_le hm1 hm2 one_le_two
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal cylSplitConst * eLpNorm g 2 volume) +
          ENNReal.ofReal B * (ENNReal.ofReal 2 * eLpNorm g 1 volume) :=
        add_le_add hNear_bd hFar_bd
    _ = ENNReal.ofReal B * (ENNReal.ofReal cylSplitConst * eLpNorm g 2 volume +
          ENNReal.ofReal 2 * eLpNorm g 1 volume) := by ring

/-! ### Planar Biot–Savart near/far split on `B0579.Plane` -/

theorem measurable_planarBSKernel : Measurable planarBSKernel := by
  have hof : Measurable ofPlane := by
    have h1 : ofPlane = fun x : B0579.Plane => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I :=
      funext ofPlane_eq_add_mul_I
    rw [h1]
    fun_prop
  unfold planarBSKernel Cyl.vec
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => by
    fin_cases i
    · exact Complex.measurable_re.comp ((B0009.measurable_kernel 0).comp hof)
    · exact Complex.measurable_re.comp ((B0009.measurable_kernel 1).comp hof))

theorem norm_planarBSKernel_eq_inv (z : B0579.Plane) :
    ‖planarBSKernel z‖ = (2 * Real.pi * euclidNorm z)⁻¹ := by
  rw [norm_planarBSKernel, planarBSC, norm_inv, norm_mul, norm_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I, mul_one, norm_ofPlane]

theorem norm_planarBSKernel_le_near {y : B0579.Plane} (h0 : y ≠ 0) :
    ‖planarBSKernel y‖ ≤ 2 * ‖y‖ ^ (-1 : ℝ) := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 h0
  have he : ‖y‖ ≤ euclidNorm y := Cyl.sup_norm_le_euclid y
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hprod : ‖y‖ ≤ 2 * Real.pi * euclidNorm y := by
    calc ‖y‖ = 1 * ‖y‖ := (one_mul _).symm
      _ ≤ (2 * Real.pi) * euclidNorm y :=
        mul_le_mul hpi he hpos.le (by positivity)
  rw [norm_planarBSKernel_eq_inv, Real.rpow_neg_one]
  have hinv : (2 * Real.pi * euclidNorm y)⁻¹ ≤ ‖y‖⁻¹ := inv_anti₀ hpos hprod
  linarith [inv_nonneg.mpr hpos.le]

theorem norm_planarBSKernel_le_far {y : B0579.Plane} (h1 : 1 ≤ ‖y‖) :
    ‖planarBSKernel y‖ ≤ 2 := by
  have h0 : y ≠ 0 := by rintro rfl; norm_num at h1
  have hinv : ‖y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hnear := norm_planarBSKernel_le_near h0
  rw [Real.rpow_neg_one] at hnear
  linarith

def kPlNear : B0579.Plane → Cyl.Vec2 :=
  (Metric.ball (0 : B0579.Plane) 1).indicator planarBSKernel

def kPlFar : B0579.Plane → Cyl.Vec2 :=
  (Metric.ball (0 : B0579.Plane) 1)ᶜ.indicator planarBSKernel

theorem measurable_kPlNear : Measurable kPlNear :=
  measurable_planarBSKernel.indicator Metric.isOpen_ball.measurableSet

theorem measurable_kPlFar : Measurable kPlFar :=
  measurable_planarBSKernel.indicator Metric.isOpen_ball.measurableSet.compl

theorem kPlNear_add_kPlFar (y : B0579.Plane) :
    kPlNear y + kPlFar y = planarBSKernel y :=
  indicator_self_add_compl_apply _ _ _

theorem norm_kPlFar_le (y : B0579.Plane) : ‖kPlFar y‖ ≤ 2 := by
  by_cases hy : y ∈ Metric.ball (0 : B0579.Plane) 1
  · rw [kPlFar, indicator_of_notMem (Set.notMem_compl_iff.mpr hy), norm_zero]
    norm_num
  · rw [kPlFar, indicator_of_mem (mem_compl hy)]
    exact norm_planarBSKernel_le_far (by simpa [mem_ball_zero_iff] using hy)

theorem planarBSKernel_split :
    ∃ C : ℝ, 0 ≤ C ∧ ∫⁻ y : B0579.Plane, ‖kPlNear y‖ₑ ≤ ENNReal.ofReal C := by
  set g : B0579.Plane → ℝ := fun y => 2 * ‖y‖ ^ (-1 : ℝ)
  have hgi : IntegrableOn g (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 2) (α := 1) ?_ ?_ ?_ ?_
    · rw [Module.finrank_prod, Module.finrank_self]; norm_num
    · rw [Module.finrank_prod, Module.finrank_self]; norm_num
    · exact Eventually.of_forall fun y => by
        simp only [g, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  refine ⟨∫ y in Metric.ball 0 1, g y,
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun y _ => by positivity, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => by positivity)]
  calc ∫⁻ y : B0579.Plane, ‖kPlNear y‖ₑ
      = ∫⁻ y in Metric.ball (0 : B0579.Plane) 1, ‖planarBSKernel y‖ₑ := by
        rw [kPlNear]
        simp_rw [enorm_indicator_eq_indicator_enorm]
        exact lintegral_indicator Metric.isOpen_ball.measurableSet _
    _ ≤ ∫⁻ y in Metric.ball (0 : B0579.Plane) 1, ENNReal.ofReal (g y) := by
        refine setLIntegral_mono_ae' Metric.isOpen_ball.measurableSet ?_
        have hae : ∀ᵐ y ∂(volume : Measure B0579.Plane), y ≠ 0 := by
          rw [ae_iff]; simp [measure_singleton]
        filter_upwards [hae] with y h0 _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_planarBSKernel_le_near h0)

def plSplitConst : ℝ := planarBSKernel_split.choose

theorem plSplitConst_nonneg : 0 ≤ plSplitConst := planarBSKernel_split.choose_spec.1

def uPlNear (g : B0579.Plane → ℝ) (x : B0579.Plane) : Cyl.Vec2 :=
  ∫ y : B0579.Plane, g (x - y) • kPlNear y

def uPlFar (g : B0579.Plane → ℝ) (x : B0579.Plane) : Cyl.Vec2 :=
  ∫ y : B0579.Plane, g (x - y) • kPlFar y

theorem planarK_eq_reflect (g : B0579.Plane → ℝ) (x : B0579.Plane) :
    planarK g x = ∫ y : B0579.Plane, g (x - y) • planarBSKernel y := by
  unfold planarK
  have h := integral_sub_left_eq_self (fun y : B0579.Plane => g (x - y) • planarBSKernel y)
    volume x
  simp only [sub_sub_cancel] at h
  exact h

theorem aestronglyMeasurable_uPlNear {g : B0579.Plane → ℝ} (hg : Measurable g) :
    AEStronglyMeasurable (uPlNear g) volume := by
  unfold uPlNear
  exact (((hg.comp (measurable_fst.sub measurable_snd)).smul
    (measurable_kPlNear.comp measurable_snd)).aestronglyMeasurable).integral_prod_right'

theorem aestronglyMeasurable_uPlFar {g : B0579.Plane → ℝ} (hg : Measurable g) :
    AEStronglyMeasurable (uPlFar g) volume := by
  unfold uPlFar
  exact (((hg.comp (measurable_fst.sub measurable_snd)).smul
    (measurable_kPlFar.comp measurable_snd)).aestronglyMeasurable).integral_prod_right'

theorem aestronglyMeasurable_planarK {g : B0579.Plane → ℝ} (hg : Measurable g) :
    AEStronglyMeasurable (planarK g) volume := by
  unfold planarK
  exact (((hg.comp measurable_snd).smul
    (measurable_planarBSKernel.comp
      (measurable_fst.sub measurable_snd))).aestronglyMeasurable).integral_prod_right'

theorem eLpNorm_uPlNear_le {g : B0579.Plane → ℝ} (hg : Measurable g) :
    eLpNorm (uPlNear g) 2 volume ≤ ENNReal.ofReal plSplitConst * eLpNorm g 2 volume := by
  have hF : AEStronglyMeasurable
      (Function.uncurry fun x y : B0579.Plane => g (x - y) • kPlNear y)
      ((volume : Measure B0579.Plane).prod volume) :=
    ((hg.comp (measurable_fst.sub measurable_snd)).smul
      (measurable_kPlNear.comp measurable_snd)).aestronglyMeasurable
  have h1 := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le hF
    (p := 2) one_le_two ENNReal.ofNat_ne_top
  have h2 : (∫⁻ y : B0579.Plane, eLpNorm (fun x => g (x - y) • kPlNear y) 2 volume) =
      (∫⁻ y : B0579.Plane, ‖kPlNear y‖ₑ) * eLpNorm g 2 volume := by
    calc ∫⁻ y : B0579.Plane, eLpNorm (fun x => g (x - y) • kPlNear y) 2 volume
        = ∫⁻ y : B0579.Plane, ‖kPlNear y‖ₑ * eLpNorm g 2 volume := by
          refine lintegral_congr fun y => ?_
          have e : eLpNorm (fun x => g (x - y) • kPlNear y) 2 volume =
              eLpNorm (‖kPlNear y‖ • fun x => g (x - y)) 2 volume :=
            eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
              simp only [Pi.smul_apply, norm_smul, norm_norm]; ring)
          have hshift : eLpNorm (fun x => g (x - y)) 2 volume = eLpNorm g 2 volume :=
            eLpNorm_comp_measurePreserving (f := fun x => x - y) hg.aestronglyMeasurable
              (measurePreserving_sub_right volume y)
          rw [e, eLpNorm_const_smul, enorm_norm, hshift]
      _ = (∫⁻ y : B0579.Plane, ‖kPlNear y‖ₑ) * eLpNorm g 2 volume :=
          lintegral_mul_const _ measurable_kPlNear.enorm
  exact (h1.trans_eq h2).trans
    (mul_le_mul_of_nonneg_right planarBSKernel_split.choose_spec.2 bot_le)

theorem enorm_uPlFar_le {g : B0579.Plane → ℝ} (hg : Measurable g) (x : B0579.Plane) :
    ‖uPlFar g x‖ₑ ≤ ENNReal.ofReal 2 * eLpNorm g 1 volume := by
  calc ‖uPlFar g x‖ₑ
      ≤ ∫⁻ y : B0579.Plane, ‖g (x - y) • kPlFar y‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y : B0579.Plane, ENNReal.ofReal 2 * ‖g (x - y)‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [enorm_smul, mul_comm, ← ofReal_norm (kPlFar y)]
        gcongr
        exact norm_kPlFar_le y
    _ = ENNReal.ofReal 2 * ∫⁻ y : B0579.Plane, ‖g (x - y)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal 2 * eLpNorm g 1 volume := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        congr 1
        exact (Measure.measurePreserving_sub_left volume x).lintegral_comp
          (f := fun y => ‖g y‖ₑ) hg.enorm

theorem planarK_ae_split_and_integrable {g : B0579.Plane → ℝ}
    (hg_meas : Measurable g) (hg_int : Integrable g volume) :
    ∀ᵐ x ∂volume,
      planarK g x = uPlNear g x + uPlFar g x ∧
      Integrable (fun y => g y • planarBSKernel (x - y)) volume := by
  have hg_l1 : ∫⁻ y : B0579.Plane, ‖g y‖ₑ < ⊤ := hg_int.2
  have hkNear_l1 : ∫⁻ y : B0579.Plane, ‖kPlNear y‖ₑ < ⊤ :=
    planarBSKernel_split.choose_spec.2.trans_lt ENNReal.ofReal_lt_top
  have hFar_int : ∀ x : B0579.Plane,
      Integrable (fun y => g (x - y) • kPlFar y) volume := by
    intro x
    refine ⟨((hg_meas.comp (measurable_const.sub measurable_id)).smul
        measurable_kPlFar).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ y : B0579.Plane, ‖g (x - y) • kPlFar y‖ₑ
        ≤ ∫⁻ y : B0579.Plane, ENNReal.ofReal 2 * ‖g (x - y)‖ₑ := by
          refine lintegral_mono fun y => ?_
          rw [enorm_smul, mul_comm, ← ofReal_norm (kPlFar y)]
          gcongr
          exact norm_kPlFar_le y
      _ = ENNReal.ofReal 2 * ∫⁻ y : B0579.Plane, ‖g (x - y)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal 2 * ∫⁻ y : B0579.Plane, ‖g y‖ₑ := by
          rw [(Measure.measurePreserving_sub_left volume x).lintegral_comp
            (f := fun y => ‖g y‖ₑ) hg_meas.enorm]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg_l1
  have hNear_prod :
      ∫⁻ x : B0579.Plane, ∫⁻ y : B0579.Plane, ‖g (x - y) • kPlNear y‖ₑ < ⊤ := by
    have hmeas_prod : Measurable (fun p : B0579.Plane × B0579.Plane =>
        ‖g (p.1 - p.2) • kPlNear p.2‖ₑ) :=
      ((hg_meas.comp (measurable_fst.sub measurable_snd)).smul
        (measurable_kPlNear.comp measurable_snd)).enorm
    rw [lintegral_lintegral_swap hmeas_prod.aemeasurable]
    have hinner : ∀ y : B0579.Plane,
        ∫⁻ x : B0579.Plane, ‖g (x - y) • kPlNear y‖ₑ =
          ‖kPlNear y‖ₑ * ∫⁻ x : B0579.Plane, ‖g x‖ₑ := by
      intro y
      calc ∫⁻ x : B0579.Plane, ‖g (x - y) • kPlNear y‖ₑ
          = ∫⁻ x : B0579.Plane, ‖kPlNear y‖ₑ * ‖g (x - y)‖ₑ := by
            refine lintegral_congr fun x => ?_
            rw [enorm_smul, mul_comm]
        _ = ‖kPlNear y‖ₑ * ∫⁻ x : B0579.Plane, ‖g (x - y)‖ₑ :=
            lintegral_const_mul _ (hg_meas.comp (measurable_id.sub_const y)).enorm
        _ = ‖kPlNear y‖ₑ * ∫⁻ x : B0579.Plane, ‖g x‖ₑ := by
            congr 1
            exact (measurePreserving_sub_right volume y).lintegral_comp
              (f := fun x => ‖g x‖ₑ) hg_meas.enorm
    simp_rw [hinner]
    rw [lintegral_mul_const _ measurable_kPlNear.enorm]
    exact ENNReal.mul_lt_top hkNear_l1 hg_l1
  have hNear_ae : ∀ᵐ x ∂(volume : Measure B0579.Plane),
      ∫⁻ y : B0579.Plane, ‖g (x - y) • kPlNear y‖ₑ < ⊤ := by
    refine ae_lt_top ?_ hNear_prod.ne
    exact Measurable.lintegral_prod_right'
      (((hg_meas.comp (measurable_fst.sub measurable_snd)).smul
        (measurable_kPlNear.comp measurable_snd)).enorm)
  filter_upwards [hNear_ae] with x hx
  have hNear_int : Integrable (fun y => g (x - y) • kPlNear y) volume :=
    ⟨((hg_meas.comp (measurable_const.sub measurable_id)).smul
      measurable_kPlNear).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr hx⟩
  have hsum_int : Integrable (fun y => g (x - y) • planarBSKernel y) volume := by
    refine (hNear_int.add (hFar_int x)).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, ← kPlNear_add_kPlFar y, smul_add]
  have hK_eq : planarK g x = uPlNear g x + uPlFar g x := by
    rw [planarK_eq_reflect g x, uPlNear, uPlFar, ← integral_add hNear_int (hFar_int x)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [← kPlNear_add_kPlFar y, smul_add]
  refine ⟨hK_eq, ?_⟩
  refine ⟨(hg_meas.smul (measurable_planarBSKernel.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hrefl := (Measure.measurePreserving_sub_left volume x).lintegral_comp
    (f := fun w => ‖g (x - w) • planarBSKernel w‖ₑ)
    (((hg_meas.comp (measurable_const.sub measurable_id)).smul measurable_planarBSKernel).enorm)
  have heq : (fun y : B0579.Plane => ‖g (x - (x - y)) • planarBSKernel (x - y)‖ₑ) =
      fun y => ‖g y • planarBSKernel (x - y)‖ₑ := by
    funext y
    rw [sub_sub_cancel]
  change (∫⁻ y : B0579.Plane, ‖g (x - (x - y)) • planarBSKernel (x - y)‖ₑ) = _ at hrefl
  rw [heq] at hrefl
  rw [hrefl]
  exact hsum_int.2

theorem eLpNorm_weighted_planarK_le
    {w : B0579.Plane → ℝ} (hw_meas : Measurable w) (hw_nn : ∀ x, 0 ≤ w x)
    {B : ℝ} (hB : 0 ≤ B) (hw_sup : ∀ x, w x ≤ B)
    (hw_l2 : eLpNorm w 2 volume ≤ ENNReal.ofReal B)
    {g : B0579.Plane → ℝ} (hg_meas : Measurable g) (hg_int : Integrable g volume) :
    eLpNorm (fun x => w x * ‖planarK g x‖) 2 volume ≤
      ENNReal.ofReal B * (ENNReal.ofReal plSplitConst * eLpNorm g 2 volume +
        ENNReal.ofReal 2 * eLpNorm g 1 volume) := by
  have hpt : ∀ᵐ x ∂volume,
      ‖w x * ‖planarK g x‖‖ₑ ≤
        ‖B * ‖uPlNear g x‖ + w x * ‖uPlFar g x‖‖ₑ := by
    filter_upwards [planarK_ae_split_and_integrable hg_meas hg_int] with x hx
    rw [Real.enorm_eq_ofReal (mul_nonneg (hw_nn x) (norm_nonneg _)),
      Real.enorm_eq_ofReal (add_nonneg (mul_nonneg hB (norm_nonneg _))
        (mul_nonneg (hw_nn x) (norm_nonneg _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hx.1]
    calc w x * ‖uPlNear g x + uPlFar g x‖
        ≤ w x * (‖uPlNear g x‖ + ‖uPlFar g x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw_nn x)
      _ = w x * ‖uPlNear g x‖ + w x * ‖uPlFar g x‖ := mul_add _ _ _
      _ ≤ B * ‖uPlNear g x‖ + w x * ‖uPlFar g x‖ := by
          gcongr
          exact hw_sup x
  have hm1 : AEStronglyMeasurable (fun x => B * ‖uPlNear g x‖) volume :=
    aestronglyMeasurable_const.mul (aestronglyMeasurable_uPlNear hg_meas).norm
  have hm2 : AEStronglyMeasurable (fun x => w x * ‖uPlFar g x‖) volume :=
    hw_meas.aestronglyMeasurable.mul (aestronglyMeasurable_uPlFar hg_meas).norm
  have hNear_bd :
      eLpNorm (fun x => B * ‖uPlNear g x‖) 2 volume ≤
        ENNReal.ofReal B * (ENNReal.ofReal plSplitConst * eLpNorm g 2 volume) := by
    have hsmul : (fun x : B0579.Plane => B * ‖uPlNear g x‖) =
        B • fun x => ‖uPlNear g x‖ := rfl
    rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal hB, eLpNorm_norm]
    exact mul_le_mul_of_nonneg_left (eLpNorm_uPlNear_le hg_meas) bot_le
  have hFar_bd :
      eLpNorm (fun x => w x * ‖uPlFar g x‖) 2 volume ≤
        ENNReal.ofReal B * (ENNReal.ofReal 2 * eLpNorm g 1 volume) := by
    set L : ℝ := (eLpNorm g 1 volume).toReal
    have hL_nn : 0 ≤ L := ENNReal.toReal_nonneg
    have hL_eq : ENNReal.ofReal L = eLpNorm g 1 volume := by
      refine ENNReal.ofReal_toReal ?_
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact hg_int.2.ne
    have hFar_pt : ∀ x, ‖uPlFar g x‖ ≤ 2 * L := by
      intro x
      have h1 : ‖uPlFar g x‖ₑ ≤ ENNReal.ofReal (2 * L) := by
        rw [ENNReal.ofReal_mul zero_le_two, hL_eq]
        exact enorm_uPlFar_le hg_meas x
      rw [← ofReal_norm] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    calc eLpNorm (fun x => w x * ‖uPlFar g x‖) 2 volume
        ≤ eLpNorm ((2 * L) • w) 2 volume := by
          refine eLpNorm_mono_enorm fun x => ?_
          rw [Pi.smul_apply, smul_eq_mul,
            Real.enorm_eq_ofReal (mul_nonneg (hw_nn x) (norm_nonneg _)),
            Real.enorm_eq_ofReal (mul_nonneg (by positivity) (hw_nn x))]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_comm (2 * L)]
          exact mul_le_mul_of_nonneg_left (hFar_pt x) (hw_nn x)
      _ = ENNReal.ofReal (2 * L) * eLpNorm w 2 volume := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
      _ ≤ ENNReal.ofReal (2 * L) * ENNReal.ofReal B :=
          mul_le_mul_of_nonneg_left hw_l2 bot_le
      _ = ENNReal.ofReal B * (ENNReal.ofReal 2 * eLpNorm g 1 volume) := by
          rw [ENNReal.ofReal_mul zero_le_two, hL_eq]
          ring
  calc eLpNorm (fun x => w x * ‖planarK g x‖) 2 volume
      ≤ eLpNorm (fun x => B * ‖uPlNear g x‖ + w x * ‖uPlFar g x‖) 2 volume :=
        eLpNorm_mono_enorm_ae hpt
    _ ≤ eLpNorm (fun x => B * ‖uPlNear g x‖) 2 volume +
          eLpNorm (fun x => w x * ‖uPlFar g x‖) 2 volume :=
        eLpNorm_add_le hm1 hm2 one_le_two
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal plSplitConst * eLpNorm g 2 volume) +
          ENNReal.ofReal B * (ENNReal.ofReal 2 * eLpNorm g 1 volume) :=
        add_le_add hNear_bd hFar_bd
    _ = ENNReal.ofReal B * (ENNReal.ofReal plSplitConst * eLpNorm g 2 volume +
          ENNReal.ofReal 2 * eLpNorm g 1 volume) := by ring

/-! ## 5. Core-disk comparison and assembly of `PlanarKernelBoundStep` -/

theorem abs_vec_dot_planarGradE_le (σ : ℝ) (v : Cyl.Vec2) (x : B0579.Plane) :
    |-(v 0 * (planarGradE σ x).1 + v 1 * (planarGradE σ x).2)| ≤ gradSum σ x * ‖v‖ := by
  rw [abs_neg]
  have h0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 1
  calc |v 0 * (planarGradE σ x).1 + v 1 * (planarGradE σ x).2|
      ≤ |v 0 * (planarGradE σ x).1| + |v 1 * (planarGradE σ x).2| := abs_add_le _ _
    _ = |v 0| * |(planarGradE σ x).1| + |v 1| * |(planarGradE σ x).2| := by
        rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * |(planarGradE σ x).1| + ‖v‖ * |(planarGradE σ x).2| :=
        add_le_add (mul_le_mul_of_nonneg_right h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
    _ = gradSum σ x * ‖v‖ := by unfold gradSum; ring

theorem abs_AcGauss_le (c σ : ℝ) (g : B0579.Plane → ℝ) (x : B0579.Plane) :
    |AcGauss c σ g x| ≤ gradSum σ x * ‖Cyl.K c g x‖ :=
  abs_vec_dot_planarGradE_le σ (Cyl.K c g x) x

theorem abs_Apl_le (σ : ℝ) (g : B0579.Plane → ℝ) (x : B0579.Plane) :
    |Apl σ g x| ≤ gradSum σ x * ‖planarK g x‖ :=
  abs_vec_dot_planarGradE_le σ (planarK g x) x

theorem abs_AcGauss_sub_Apl_le (c σ : ℝ) (g : B0579.Plane → ℝ) (x : B0579.Plane) :
    |AcGauss c σ g x - Apl σ g x| ≤ gradSum σ x * ‖Cyl.K c g x - planarK g x‖ := by
  have heq : AcGauss c σ g x - Apl σ g x =
      -((Cyl.K c g x - planarK g x) 0 * (planarGradE σ x).1 +
        (Cyl.K c g x - planarK g x) 1 * (planarGradE σ x).2) := by
    unfold AcGauss Apl
    simp only [PiLp.sub_apply]
    ring
  rw [heq]
  exact abs_vec_dot_planarGradE_le σ (Cyl.K c g x - planarK g x) x

def gCore (c : ℝ) (g : B0579.Plane → ℝ) : B0579.Plane → ℝ :=
  (coreDisk c).indicator g

def gTail (c : ℝ) (g : B0579.Plane → ℝ) : B0579.Plane → ℝ :=
  (coreDisk c)ᶜ.indicator g

theorem measurable_gCore (c : ℝ) {g : B0579.Plane → ℝ} (hg : Measurable g) :
    Measurable (gCore c g) :=
  hg.indicator (measurableSet_coreDisk c)

theorem measurable_gTail (c : ℝ) {g : B0579.Plane → ℝ} (hg : Measurable g) :
    Measurable (gTail c g) :=
  hg.indicator (measurableSet_coreDisk c).compl

theorem gCore_add_gTail (c : ℝ) (g : B0579.Plane → ℝ) (y : B0579.Plane) :
    gCore c g y + gTail c g y = g y :=
  indicator_self_add_compl_apply (coreDisk c) g y

theorem eLpNorm_one_le_planeMeasure {m : ℝ} (hm : 1 < m) {g : B0579.Plane → ℝ}
    (hg : Measurable g) :
    eLpNorm g 1 volume ≤ ENNReal.ofReal (jbNegL2Norm (m / 2)) * eLpNorm g 2 (planeMeasure m) := by
  have h := eLpNorm_jb_mul_one_le (m := m) (k := 0) (by linarith) hg
  simpa only [Real.rpow_zero, one_mul, sub_zero] using h

theorem integrable_jb_mul_of_memLp {m k : ℝ} (hmk : 1 < m - 2 * k) {g : B0579.Plane → ℝ}
    (hg_meas : Measurable g) (hg_lp : eLpNorm g 2 (planeMeasure m) < ⊤) :
    Integrable (fun y => B0579.jb y ^ k * g y) volume := by
  rw [← memLp_one_iff_integrable]
  refine ⟨((B0579.continuous_jb_rpow k).measurable.mul hg_meas).aestronglyMeasurable, ?_⟩
  exact (eLpNorm_jb_mul_one_le hmk hg_meas).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg_lp)

theorem integrable_of_memLp_planeMeasure {m : ℝ} (hm : 1 < m) {g : B0579.Plane → ℝ}
    (hg_meas : Measurable g) (hg_lp : eLpNorm g 2 (planeMeasure m) < ⊤) :
    Integrable g volume := by
  have h := integrable_jb_mul_of_memLp (m := m) (k := 0) (by linarith) hg_meas hg_lp
  simpa only [Real.rpow_zero, one_mul] using h

theorem cyl_K_gCore_eq_univ_integral {c : ℝ} (hc : 1 ≤ c) (g : B0579.Plane → ℝ)
    (x : B0579.Plane) :
    Cyl.K c (gCore c g) x = ∫ y : B0579.Plane, gCore c g y • Cyl.bsKernel c (x - y) := by
  unfold Cyl.K
  rw [← integral_indicator (Cyl.measurableSet_cell c)]
  congr 1
  funext y
  by_cases hy : y ∈ Cyl.cell c
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy]
    have hy' : y ∉ coreDisk c := fun h => hy (by
      rw [← b0579_cell_eq_cyl_cell]
      exact coreDisk_subset_cell hc h)
    simp [gCore, indicator_of_notMem hy']

theorem norm_cyl_K_gCore_sub_planarK_gCore_le {c : ℝ} (hc : 1 ≤ c)
    {g : B0579.Plane → ℝ} (hg_half : Integrable (fun y => B0579.jb y ^ (1 / 2 : ℝ) * g y) volume)
    {x : B0579.Plane} (hx : x ∈ coreDisk c)
    (hIntC : IntegrableOn (fun y => g y • Cyl.bsKernel c (x - y)) (Cyl.cell c) volume)
    (hIntP : Integrable (fun y => g y • planarBSKernel (x - y)) volume) :
    ‖Cyl.K c (gCore c g) x - planarK (gCore c g) x‖ ≤
      4 * pairedImageConst * c ^ (-2 : ℝ) * B0579.jb x ^ (1 / 2 : ℝ) *
        ∫ y : B0579.Plane, ‖B0579.jb y ^ (1 / 2 : ℝ) * g y‖ := by
  have hc0 : 0 < c := by linarith
  have hIntC_core : Integrable (fun y => gCore c g y • Cyl.bsKernel c (x - y)) volume := by
    have h1 : IntegrableOn (fun y => gCore c g y • Cyl.bsKernel c (x - y)) (Cyl.cell c) volume := by
      have heq : (fun y => gCore c g y • Cyl.bsKernel c (x - y)) =
          (coreDisk c).indicator (fun y => g y • Cyl.bsKernel c (x - y)) := by
        funext y
        by_cases hy : y ∈ coreDisk c <;> simp [gCore, hy]
      rw [heq]
      exact hIntC.indicator (measurableSet_coreDisk c)
    rw [← integrable_indicator_iff (Cyl.measurableSet_cell c)] at h1
    refine h1.congr (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Cyl.cell c
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hy' : y ∉ coreDisk c := fun h => hy (by
        rw [← b0579_cell_eq_cyl_cell]
        exact coreDisk_subset_cell hc h)
      simp [gCore, indicator_of_notMem hy']
  have hIntP_core : Integrable (fun y => gCore c g y • planarBSKernel (x - y)) volume := by
    have heq : (fun y => gCore c g y • planarBSKernel (x - y)) =
        (coreDisk c).indicator (fun y => g y • planarBSKernel (x - y)) := by
      funext y
      by_cases hy : y ∈ coreDisk c <;> simp [gCore, hy]
    rw [heq]
    exact hIntP.indicator (measurableSet_coreDisk c)
  rw [cyl_K_gCore_eq_univ_integral hc g x, planarK, ← integral_sub hIntC_core hIntP_core]
  set Kx : ℝ := 4 * pairedImageConst * c ^ (-2 : ℝ) * B0579.jb x ^ (1 / 2 : ℝ)
  have hKx_nn : 0 ≤ Kx := by
    dsimp [Kx]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) pairedImageConst_pos.le)
      (Real.rpow_nonneg hc0.le _)) (Real.rpow_nonneg (B0579.jb_pos x).le _)
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg_half.norm.const_mul Kx) ?_
  have hae : ∀ᵐ y ∂(volume : Measure B0579.Plane), y ≠ x := by
    rw [ae_iff]
    simp [measure_singleton]
  filter_upwards [hae] with y hyx
  rw [ ← smul_sub, norm_smul, Real.norm_eq_abs]
  by_cases hy : y ∈ coreDisk c
  · rw [gCore, indicator_of_mem hy]
    have hxy : x ≠ y := hyx.symm
    have hpair := norm_bsKernel_sub_planarBSKernel_paired hc0 hxy hx hy
    have hjb := one_add_euclidNorm_add_le x y
    have hkern : ‖Cyl.bsKernel c (x - y) - planarBSKernel (x - y)‖ ≤
        Kx * B0579.jb y ^ (1 / 2 : ℝ) := by
      calc ‖Cyl.bsKernel c (x - y) - planarBSKernel (x - y)‖
          ≤ pairedImageConst * c ^ (-2 : ℝ) * (1 + euclidNorm x + euclidNorm y) := hpair
        _ ≤ pairedImageConst * c ^ (-2 : ℝ) *
              (4 * B0579.jb x ^ (1 / 2 : ℝ) * B0579.jb y ^ (1 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hjb ?_
            exact mul_nonneg pairedImageConst_pos.le (Real.rpow_nonneg hc0.le _)
        _ = Kx * B0579.jb y ^ (1 / 2 : ℝ) := by dsimp [Kx]; ring
    have hjb_y : 0 ≤ B0579.jb y ^ (1 / 2 : ℝ) := Real.rpow_nonneg (B0579.jb_pos y).le _
    calc |g y| * ‖Cyl.bsKernel c (x - y) - planarBSKernel (x - y)‖
        ≤ |g y| * (Kx * B0579.jb y ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hkern (abs_nonneg _)
      _ = Kx * ‖B0579.jb y ^ (1 / 2 : ℝ) * g y‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hjb_y]
          ring
  · rw [gCore, indicator_of_notMem hy, abs_zero, zero_mul]
    exact mul_nonneg hKx_nn (norm_nonneg _)

theorem cyl_K_split_core_tail {c : ℝ} (g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hIntC : IntegrableOn (fun y => g y • Cyl.bsKernel c (x - y)) (Cyl.cell c) volume) :
    Cyl.K c g x = Cyl.K c (gCore c g) x + Cyl.K c (gTail c g) x := by
  unfold Cyl.K
  have h1 : IntegrableOn (fun y => gCore c g y • Cyl.bsKernel c (x - y)) (Cyl.cell c) volume := by
    have heq : (fun y => gCore c g y • Cyl.bsKernel c (x - y)) =
        (coreDisk c).indicator (fun y => g y • Cyl.bsKernel c (x - y)) := by
      funext y; by_cases hy : y ∈ coreDisk c <;> simp [gCore, hy]
    rw [heq]
    exact hIntC.indicator (measurableSet_coreDisk c)
  have h2 : IntegrableOn (fun y => gTail c g y • Cyl.bsKernel c (x - y)) (Cyl.cell c) volume := by
    have heq : (fun y => gTail c g y • Cyl.bsKernel c (x - y)) =
        (coreDisk c)ᶜ.indicator (fun y => g y • Cyl.bsKernel c (x - y)) := by
      funext y; by_cases hy : y ∈ coreDisk c <;> simp [gTail, hy]
    rw [heq]
    exact hIntC.indicator (measurableSet_coreDisk c).compl
  rw [← integral_add h1 h2]
  refine setIntegral_congr_fun (Cyl.measurableSet_cell c) fun y _ => ?_
  rw [← add_smul, gCore_add_gTail]

theorem planarK_split_core_tail {c : ℝ} (g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hIntP : Integrable (fun y => g y • planarBSKernel (x - y)) volume) :
    planarK g x = planarK (gCore c g) x + planarK (gTail c g) x := by
  unfold planarK
  have h1 : Integrable (fun y => gCore c g y • planarBSKernel (x - y)) volume := by
    have heq : (fun y => gCore c g y • planarBSKernel (x - y)) =
        (coreDisk c).indicator (fun y => g y • planarBSKernel (x - y)) := by
      funext y; by_cases hy : y ∈ coreDisk c <;> simp [gCore, hy]
    rw [heq]
    exact hIntP.indicator (measurableSet_coreDisk c)
  have h2 : Integrable (fun y => gTail c g y • planarBSKernel (x - y)) volume := by
    have heq : (fun y => gTail c g y • planarBSKernel (x - y)) =
        (coreDisk c)ᶜ.indicator (fun y => g y • planarBSKernel (x - y)) := by
      funext y; by_cases hy : y ∈ coreDisk c <;> simp [gTail, hy]
    rw [heq]
    exact hIntP.indicator (measurableSet_coreDisk c).compl
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp
  rw [← add_smul, gCore_add_gTail]

theorem coeFn_Jc_AcG_Rc_sub_Apl_ae {c m σ : ℝ}
    {AcG : Xmc c m →L[ℝ] Xmc c m} {Apl_σ : Xm m →L[ℝ] Xm m}
    (hAcG : IsGaussCylInteractionOp c m σ AcG) (hApl : IsPlanarInteractionOp m σ Apl_σ)
    (f : Xm m) {g : B0579.Plane → ℝ} (hg : (f : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g) :
    (((Jc c m).comp (AcG.comp (Rc c m)) - Apl_σ) f : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => (B0579.cell c).indicator (AcGauss c σ g) x - Apl σ g x := by
  have hg_vol : (f : B0579.Plane → ℝ) =ᵐ[volume] g := (volume_ac_planeMeasure m).ae_le hg
  have hRc_cell : (Rc c m f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] g := by
    refine (coeFn_restrictCellFun c m f).trans ?_
    rw [cellMeasure_eq_restrict_planeMeasure]
    exact ae_restrict_of_ae hg
  have hRc_vol : (Rc c m f : B0579.Plane → ℝ) =ᵐ[volume.restrict (Cyl.cell c)] g := by
    rw [← b0579_cell_eq_cyl_cell]
    have h1 : (Rc c m f : B0579.Plane → ℝ) =ᵐ[(planeMeasure m).restrict (B0579.cell c)] g := by
      rwa [← cellMeasure_eq_restrict_planeMeasure]
    have h2 : ∀ᵐ y ∂planeMeasure m, y ∈ B0579.cell c → Rc c m f y = g y :=
      (ae_restrict_iff' (B0579.measurableSet_cell c)).mp h1
    exact (ae_restrict_iff' (B0579.measurableSet_cell c)).mpr
      ((volume_ac_planeMeasure m).ae_le h2)
  have hAcGauss_eq : AcGauss c σ (Rc c m f) = AcGauss c σ g := by
    funext x
    have hK : Cyl.K c (Rc c m f) x = Cyl.K c g x := by
      unfold Cyl.K
      refine integral_congr_ae ?_
      filter_upwards [hRc_vol] with y hy
      rw [hy]
    simp only [AcGauss, hK]
  have hApl_eq : Apl σ f = Apl σ g := by
    funext x
    have hK : planarK f x = planarK g x := by
      unfold planarK
      refine integral_congr_ae ?_
      filter_upwards [hg_vol] with y hy
      rw [hy]
    simp only [Apl, hK]
  have hJc : (Jc c m (AcG (Rc c m f)) : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      (B0579.cell c).indicator (AcGauss c σ g) := by
    refine (coeFn_zeroExtFun c m (AcG (Rc c m f))).trans ?_
    rw [← hAcGauss_eq]
    have h1 : (AcG (Rc c m f) : B0579.Plane → ℝ) =ᵐ[(planeMeasure m).restrict (B0579.cell c)]
        AcGauss c σ (Rc c m f) := by
      simpa only [cellMeasure_eq_restrict_planeMeasure] using hAcG (Rc c m f)
    filter_upwards [(ae_restrict_iff' (B0579.measurableSet_cell c)).1 h1] with x hx
    by_cases hxc : x ∈ B0579.cell c
    · simp only [indicator_of_mem hxc, hx hxc]
    · simp only [indicator_of_notMem hxc]
  have hApl' : (Apl_σ f : B0579.Plane → ℝ) =ᵐ[planeMeasure m] Apl σ g := by
    rw [← hApl_eq]
    exact hApl f
  filter_upwards [Lp.coeFn_sub (Jc c m (AcG (Rc c m f))) (Apl_σ f), hJc, hApl']
    with x hsub hx1 hx2
  change ((Jc c m (AcG (Rc c m f)) - Apl_σ f : Xm m) : B0579.Plane → ℝ) x = _
  rw [hsub, Pi.sub_apply, hx1, hx2]

theorem planarKernelBoundStep_proof : PlanarKernelBoundStep := by
  intro m hm Sg hSg
  obtain ⟨B₀, hB₀, hGrad₀⟩ := planarGradE_weighted_bound (m / 2) (by linarith) Sg hSg
  obtain ⟨B₁, hB₁, hGrad₁⟩ := planarGradE_weighted_bound (m / 2 + 1 / 2) (by linarith) Sg hSg
  obtain ⟨B₂, hB₂, hGrad₂⟩ := planarGradE_weighted_bound (m / 2 + 1) (by linarith) Sg hSg
  set L₀ : ℝ := jbNegL2Norm (m / 2)
  set L_half : ℝ := jbNegL2Norm (m / 2 - 1 / 2)
  set L₁ : ℝ := jbNegL2Norm (m / 2 - 1)
  have hL₀_nn : 0 ≤ L₀ := jbNegL2Norm_nonneg _
  have hL_half_nn : 0 ≤ L_half := jbNegL2Norm_nonneg _
  have hL₁_nn : 0 ≤ L₁ := jbNegL2Norm_nonneg _
  have hCcyl_nn : 0 ≤ cylSplitConst := cylSplitConst_nonneg
  have hCpl_nn : 0 ≤ plSplitConst := plSplitConst_nonneg
  have hpic_pos : 0 < pairedImageConst := pairedImageConst_pos
  set K₁ : ℝ := 4 * pairedImageConst * L_half * B₁
  set K₂ : ℝ := B₀ * (cylSplitConst * 16 + 32 * L₁)
  set K₃ : ℝ := B₀ * (plSplitConst * 16 + 32 * L₁)
  set K₄ : ℝ := 16 * B₂ * (cylSplitConst + 2 * L₀)
  set K₅ : ℝ := 16 * B₂ * (plSplitConst + 2 * L₀)
  set C₂ : ℝ := K₁ + K₂ + K₃ + K₄ + K₅ + 1
  have hK₁_nn : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂_nn : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hK₃_nn : 0 ≤ K₃ := by dsimp [K₃]; positivity
  have hK₄_nn : 0 ≤ K₄ := by dsimp [K₄]; positivity
  have hK₅_nn : 0 ≤ K₅ := by dsimp [K₅]; positivity
  have hC₂_pos : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨C₂, hC₂_pos, fun c hc σ hσ AcG Apl_σ hAcG hApl => ?_⟩
  have hc0 : 0 < c := by linarith
  have hcinv_nn : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC₂_pos.le hcinv_nn) fun f => ?_
  set g : B0579.Plane → ℝ := (Lp.aestronglyMeasurable f).mk f
  have hg_meas : Measurable g := (Lp.aestronglyMeasurable f).measurable_mk
  have hg_ae : (f : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g := (Lp.aestronglyMeasurable f).ae_eq_mk
  set N : ℝ≥0∞ := eLpNorm g 2 (planeMeasure m)
  have hN_eq : N = eLpNorm f 2 (planeMeasure m) := (eLpNorm_congr_ae hg_ae).symm
  have hN_lt : N < ⊤ := hN_eq ▸ Lp.eLpNorm_lt_top f
  have hg_int : Integrable g volume := integrable_of_memLp_planeMeasure (by linarith) hg_meas hN_lt
  have hg_half_int : Integrable (fun y => B0579.jb y ^ (1 / 2 : ℝ) * g y) volume :=
    integrable_jb_mul_of_memLp (m := m) (k := 1 / 2) (by linarith) hg_meas hN_lt
  have hgTail_meas : Measurable (gTail c g) := measurable_gTail c hg_meas
  have hgTail_int : Integrable (gTail c g) volume := hg_int.indicator (measurableSet_coreDisk c).compl
  set w₀ : B0579.Plane → ℝ := fun x => B0579.jb x ^ (m / 2) * gradSum σ x
  set w₁ : B0579.Plane → ℝ := fun x => B0579.jb x ^ (m / 2 + 1 / 2) * gradSum σ x
  set w₂ : B0579.Plane → ℝ := fun x => B0579.jb x ^ (m / 2 + 1) * gradSum σ x
  have hw₀_meas : Measurable w₀ :=
    (B0579.continuous_jb_rpow (m / 2)).measurable.mul (continuous_gradSum σ).measurable
  have hw₁_meas : Measurable w₁ :=
    (B0579.continuous_jb_rpow (m / 2 + 1 / 2)).measurable.mul (continuous_gradSum σ).measurable
  have hw₂_meas : Measurable w₂ :=
    (B0579.continuous_jb_rpow (m / 2 + 1)).measurable.mul (continuous_gradSum σ).measurable
  have hw₀_nn : ∀ x, 0 ≤ w₀ x := fun x =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (gradSum_nonneg σ x)
  have hw₁_nn : ∀ x, 0 ≤ w₁ x := fun x =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (gradSum_nonneg σ x)
  have hw₂_nn : ∀ x, 0 ≤ w₂ x := fun x =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (gradSum_nonneg σ x)
  set I_half : ℝ := ∫ y : B0579.Plane, ‖B0579.jb y ^ (1 / 2 : ℝ) * g y‖
  have hI_half_nn : 0 ≤ I_half := integral_nonneg fun _ => norm_nonneg _
  have hI_half_ofReal : ENNReal.ofReal I_half ≤ ENNReal.ofReal L_half * N := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hg_half_int, ← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_jb_mul_one_le (m := m) (k := 1 / 2) (by linarith) hg_meas
  set F₁ : B0579.Plane → ℝ := fun x => (4 * pairedImageConst * c ^ (-2 : ℝ) * I_half) * w₁ x
  set F₂ : B0579.Plane → ℝ := fun x =>
    w₀ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c (gTail c g) x‖) x
  set F₃ : B0579.Plane → ℝ := fun x => w₀ x * ‖planarK (gTail c g) x‖
  set F₄ : B0579.Plane → ℝ := fun x =>
    16 * c ^ (-2 : ℝ) * (w₂ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x)
  set F₅ : B0579.Plane → ℝ := fun x => 16 * c ^ (-2 : ℝ) * (w₂ x * ‖planarK g x‖)
  have hpt : ∀ᵐ x ∂volume,
      ‖B0579.jb x ^ (m / 2) * ((B0579.cell c).indicator (AcGauss c σ g) x - Apl σ g x)‖ₑ ≤
        ‖F₁ x + F₂ x + F₃ x + F₄ x + F₅ x‖ₑ := by
    filter_upwards [cyl_K_ae_split_and_integrable hc hg_meas hg_int,
      planarK_ae_split_and_integrable hg_meas hg_int] with x hxC hxP
    have hF1_nn : 0 ≤ F₁ x := by
      dsimp [F₁]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) pairedImageConst_pos.le)
        hcinv_nn) hI_half_nn) (hw₁_nn x)
    have hF2_nn : 0 ≤ F₂ x :=
      mul_nonneg (hw₀_nn x) (indicator_nonneg (fun _ _ => norm_nonneg _) _)
    have hF3_nn : 0 ≤ F₃ x := mul_nonneg (hw₀_nn x) (norm_nonneg _)
    have hF4_nn : 0 ≤ F₄ x :=
      mul_nonneg (mul_nonneg (by norm_num) hcinv_nn)
        (mul_nonneg (hw₂_nn x) (indicator_nonneg (fun _ _ => norm_nonneg _) _))
    have hF5_nn : 0 ≤ F₅ x :=
      mul_nonneg (mul_nonneg (by norm_num) hcinv_nn) (mul_nonneg (hw₂_nn x) (norm_nonneg _))
    have hjb_m : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hjb_m,
      Real.enorm_eq_ofReal (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hx_core : x ∈ coreDisk c
    · have hx_cell : x ∈ B0579.cell c := coreDisk_subset_cell hc hx_core
      have hx_cyl : x ∈ Cyl.cell c := by rwa [← b0579_cell_eq_cyl_cell]
      rw [indicator_of_mem hx_cell]
      have hIntC := (hxC hx_cyl).2
      have hIntP := hxP.2
      have hdiff_K : Cyl.K c g x - planarK g x =
          (Cyl.K c (gCore c g) x - planarK (gCore c g) x) +
            Cyl.K c (gTail c g) x - planarK (gTail c g) x := by
        rw [cyl_K_split_core_tail g x hIntC, planarK_split_core_tail g x hIntP]
        abel
      have hnorm_K : ‖Cyl.K c g x - planarK g x‖ ≤
          ‖Cyl.K c (gCore c g) x - planarK (gCore c g) x‖ +
            (B0579.cell c).indicator (fun x => ‖Cyl.K c (gTail c g) x‖) x +
            ‖planarK (gTail c g) x‖ := by
        rw [hdiff_K, indicator_of_mem hx_cell]
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have hcore_bd := norm_cyl_K_gCore_sub_planarK_gCore_le hc hg_half_int hx_core hIntC hIntP
      have hw0_jb : w₀ x * B0579.jb x ^ (1 / 2 : ℝ) = w₁ x := by
        dsimp [w₀, w₁]
        rw [mul_right_comm, B0579.jb_rpow_mul]
      have h1 : B0579.jb x ^ (m / 2) * |AcGauss c σ g x - Apl σ g x| ≤
          w₀ x * ‖Cyl.K c g x - planarK g x‖ := by
        calc B0579.jb x ^ (m / 2) * |AcGauss c σ g x - Apl σ g x|
            ≤ B0579.jb x ^ (m / 2) * (gradSum σ x * ‖Cyl.K c g x - planarK g x‖) :=
              mul_le_mul_of_nonneg_left (abs_AcGauss_sub_Apl_le c σ g x) hjb_m
          _ = w₀ x * ‖Cyl.K c g x - planarK g x‖ := by dsimp [w₀]; ring
      have h2 : w₀ x * ‖Cyl.K c (gCore c g) x - planarK (gCore c g) x‖ ≤ F₁ x := by
        calc w₀ x * ‖Cyl.K c (gCore c g) x - planarK (gCore c g) x‖
            ≤ w₀ x * (4 * pairedImageConst * c ^ (-2 : ℝ) * B0579.jb x ^ (1 / 2 : ℝ) * I_half) :=
              mul_le_mul_of_nonneg_left hcore_bd (hw₀_nn x)
          _ = (4 * pairedImageConst * c ^ (-2 : ℝ) * I_half) *
                (w₀ x * B0579.jb x ^ (1 / 2 : ℝ)) := by ring
          _ = F₁ x := by rw [hw0_jb]
      calc B0579.jb x ^ (m / 2) * |AcGauss c σ g x - Apl σ g x|
          ≤ w₀ x * ‖Cyl.K c g x - planarK g x‖ := h1
        _ ≤ w₀ x * (‖Cyl.K c (gCore c g) x - planarK (gCore c g) x‖ +
              (B0579.cell c).indicator (fun x => ‖Cyl.K c (gTail c g) x‖) x +
              ‖planarK (gTail c g) x‖) :=
            mul_le_mul_of_nonneg_left hnorm_K (hw₀_nn x)
        _ = w₀ x * ‖Cyl.K c (gCore c g) x - planarK (gCore c g) x‖ + F₂ x + F₃ x := by
            dsimp [F₂, F₃]; ring
        _ ≤ F₁ x + F₂ x + F₃ x + F₄ x + F₅ x := by linarith
    · have hjb16 := one_le_sixteen_inv_sq_mul_jb hc hx_core
      have hw0_jb1 : w₀ x * B0579.jb x = w₂ x := by
        dsimp [w₀, w₂]
        rw [Real.rpow_add (B0579.jb_pos x) (m / 2) 1, Real.rpow_one]
        ring
      have hind_nn : 0 ≤ (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x :=
        indicator_nonneg (fun _ _ => norm_nonneg _) _
      have habs_sub : |(B0579.cell c).indicator (AcGauss c σ g) x - Apl σ g x| ≤
          gradSum σ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x +
            gradSum σ x * ‖planarK g x‖ := by
        have htri : |(B0579.cell c).indicator (AcGauss c σ g) x - Apl σ g x| ≤
            |(B0579.cell c).indicator (AcGauss c σ g) x| + |Apl σ g x| := abs_sub _ _
        have hind : |(B0579.cell c).indicator (AcGauss c σ g) x| ≤
            gradSum σ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x := by
          by_cases hxc : x ∈ B0579.cell c
          · rw [indicator_of_mem hxc, indicator_of_mem hxc]
            exact abs_AcGauss_le c σ g x
          · rw [indicator_of_notMem hxc, indicator_of_notMem hxc, abs_zero, mul_zero]
        exact htri.trans (add_le_add hind (abs_Apl_le σ g x))
      calc B0579.jb x ^ (m / 2) * |(B0579.cell c).indicator (AcGauss c σ g) x - Apl σ g x|
          ≤ B0579.jb x ^ (m / 2) *
              (gradSum σ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x +
                gradSum σ x * ‖planarK g x‖) :=
            mul_le_mul_of_nonneg_left habs_sub hjb_m
        _ = w₀ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x +
              w₀ x * ‖planarK g x‖ := by dsimp [w₀]; ring
        _ ≤ (16 * c ^ (-2 : ℝ) * B0579.jb x) *
              (w₀ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x +
                w₀ x * ‖planarK g x‖) :=
            le_mul_of_one_le_left
              (add_nonneg (mul_nonneg (hw₀_nn x) hind_nn)
                (mul_nonneg (hw₀_nn x) (norm_nonneg _))) hjb16
        _ = 16 * c ^ (-2 : ℝ) *
              ((w₀ x * B0579.jb x) * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x) +
            16 * c ^ (-2 : ℝ) * ((w₀ x * B0579.jb x) * ‖planarK g x‖) := by ring
        _ = F₄ x + F₅ x := by rw [hw0_jb1]
        _ ≤ F₁ x + F₂ x + F₃ x + F₄ x + F₅ x := by linarith
  have hmF₁ : AEStronglyMeasurable F₁ volume :=
    aestronglyMeasurable_const.mul hw₁_meas.aestronglyMeasurable
  have hmF₂ : AEStronglyMeasurable F₂ volume :=
    hw₀_meas.aestronglyMeasurable.mul
      ((aestronglyMeasurable_cyl_K c hgTail_meas).norm.indicator (B0579.measurableSet_cell c))
  have hmF₃ : AEStronglyMeasurable F₃ volume :=
    hw₀_meas.aestronglyMeasurable.mul (aestronglyMeasurable_planarK hgTail_meas).norm
  have hmF₄ : AEStronglyMeasurable F₄ volume :=
    aestronglyMeasurable_const.mul (hw₂_meas.aestronglyMeasurable.mul
      ((aestronglyMeasurable_cyl_K c hg_meas).norm.indicator (B0579.measurableSet_cell c)))
  have hmF₅ : AEStronglyMeasurable F₅ volume :=
    aestronglyMeasurable_const.mul
      (hw₂_meas.aestronglyMeasurable.mul (aestronglyMeasurable_planarK hg_meas).norm)
  have hbd₁ : eLpNorm F₁ 2 volume ≤ ENNReal.ofReal (K₁ * c ^ (-2 : ℝ)) * N := by
    have hsmul : F₁ = (4 * pairedImageConst * c ^ (-2 : ℝ) * I_half) • w₁ := rfl
    have hcI_nn : 0 ≤ 4 * pairedImageConst * c ^ (-2 : ℝ) * I_half :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) pairedImageConst_pos.le) hcinv_nn)
        hI_half_nn
    rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal hcI_nn,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) pairedImageConst_pos.le) hcinv_nn)]
    calc ENNReal.ofReal (4 * pairedImageConst * c ^ (-2 : ℝ)) * ENNReal.ofReal I_half *
            eLpNorm w₁ 2 volume
        ≤ ENNReal.ofReal (4 * pairedImageConst * c ^ (-2 : ℝ)) * (ENNReal.ofReal L_half * N) *
            ENNReal.ofReal B₁ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hI_half_ofReal bot_le)
            (hGrad₁ σ hσ).2 bot_le bot_le
      _ = ENNReal.ofReal (4 * pairedImageConst * c ^ (-2 : ℝ)) *
            ENNReal.ofReal L_half * ENNReal.ofReal B₁ * N := by ring
      _ = ENNReal.ofReal (K₁ * c ^ (-2 : ℝ)) * N := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          dsimp [K₁]
          ring
  have hTail2 : eLpNorm (gTail c g) 2 volume ≤ ENNReal.ofReal (16 * c ^ (-2 : ℝ)) * N :=
    eLpNorm_tail_two_le (m := m) hc (by linarith) g
  have hTail1 : eLpNorm (gTail c g) 1 volume ≤ ENNReal.ofReal (16 * L₁ * c ^ (-2 : ℝ)) * N :=
    eLpNorm_tail_one_le (m := m) hc (by linarith) hg_meas
  have hbd₂ : eLpNorm F₂ 2 volume ≤ ENNReal.ofReal (K₂ * c ^ (-2 : ℝ)) * N := by
    have h1 := eLpNorm_weighted_cyl_K_le hc hw₀_meas hw₀_nn hB₀.le
      (hGrad₀ σ hσ).1 (hGrad₀ σ hσ).2 hgTail_meas hgTail_int
    calc eLpNorm F₂ 2 volume
        ≤ ENNReal.ofReal B₀ * (ENNReal.ofReal cylSplitConst * eLpNorm (gTail c g) 2 volume +
            ENNReal.ofReal 2 * eLpNorm (gTail c g) 1 volume) := h1
      _ ≤ ENNReal.ofReal B₀ *
            (ENNReal.ofReal cylSplitConst * (ENNReal.ofReal (16 * c ^ (-2 : ℝ)) * N) +
              ENNReal.ofReal 2 * (ENNReal.ofReal (16 * L₁ * c ^ (-2 : ℝ)) * N)) := by
          gcongr
      _ = ENNReal.ofReal (K₂ * c ^ (-2 : ℝ)) * N := by
          rw [← mul_assoc (ENNReal.ofReal cylSplitConst),
            ← ENNReal.ofReal_mul hCcyl_nn,
            ← mul_assoc (ENNReal.ofReal 2),
            ← ENNReal.ofReal_mul zero_le_two,
            ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← mul_assoc,
            ← ENNReal.ofReal_mul hB₀.le]
          congr 2
          dsimp [K₂]
          ring
  have hbd₃ : eLpNorm F₃ 2 volume ≤ ENNReal.ofReal (K₃ * c ^ (-2 : ℝ)) * N := by
    have h1 := eLpNorm_weighted_planarK_le hw₀_meas hw₀_nn hB₀.le
      (hGrad₀ σ hσ).1 (hGrad₀ σ hσ).2 hgTail_meas hgTail_int
    calc eLpNorm F₃ 2 volume
        ≤ ENNReal.ofReal B₀ * (ENNReal.ofReal plSplitConst * eLpNorm (gTail c g) 2 volume +
            ENNReal.ofReal 2 * eLpNorm (gTail c g) 1 volume) := h1
      _ ≤ ENNReal.ofReal B₀ *
            (ENNReal.ofReal plSplitConst * (ENNReal.ofReal (16 * c ^ (-2 : ℝ)) * N) +
              ENNReal.ofReal 2 * (ENNReal.ofReal (16 * L₁ * c ^ (-2 : ℝ)) * N)) := by
          gcongr
      _ = ENNReal.ofReal (K₃ * c ^ (-2 : ℝ)) * N := by
          rw [← mul_assoc (ENNReal.ofReal plSplitConst),
            ← ENNReal.ofReal_mul hCpl_nn,
            ← mul_assoc (ENNReal.ofReal 2),
            ← ENNReal.ofReal_mul zero_le_two,
            ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← mul_assoc,
            ← ENNReal.ofReal_mul hB₀.le]
          congr 2
          dsimp [K₃]
          ring
  have hg2_le : eLpNorm g 2 volume ≤ ENNReal.ofReal 1 * N := by
    rw [ENNReal.ofReal_one, one_mul]
    exact eLpNorm_volume_le_planeMeasure (by linarith) g
  have hg1_le : eLpNorm g 1 volume ≤ ENNReal.ofReal L₀ * N :=
    eLpNorm_one_le_planeMeasure (by linarith) hg_meas
  have hbd₄ : eLpNorm F₄ 2 volume ≤ ENNReal.ofReal (K₄ * c ^ (-2 : ℝ)) * N := by
    have hsmul : F₄ = (16 * c ^ (-2 : ℝ)) •
        fun x => w₂ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x := rfl
    rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    have h1 := eLpNorm_weighted_cyl_K_le hc hw₂_meas hw₂_nn hB₂.le
      (hGrad₂ σ hσ).1 (hGrad₂ σ hσ).2 hg_meas hg_int
    calc ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            eLpNorm (fun x => w₂ x * (B0579.cell c).indicator (fun x => ‖Cyl.K c g x‖) x) 2 volume
        ≤ ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            (ENNReal.ofReal B₂ * (ENNReal.ofReal cylSplitConst * eLpNorm g 2 volume +
              ENNReal.ofReal 2 * eLpNorm g 1 volume)) :=
          mul_le_mul_of_nonneg_left h1 bot_le
      _ ≤ ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            (ENNReal.ofReal B₂ * (ENNReal.ofReal cylSplitConst * (ENNReal.ofReal 1 * N) +
              ENNReal.ofReal 2 * (ENNReal.ofReal L₀ * N))) := by
          gcongr
      _ = ENNReal.ofReal (K₄ * c ^ (-2 : ℝ)) * N := by
          rw [← mul_assoc (ENNReal.ofReal cylSplitConst),
            ← ENNReal.ofReal_mul hCcyl_nn,
            ← mul_assoc (ENNReal.ofReal 2),
            ← ENNReal.ofReal_mul zero_le_two,
            ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← mul_assoc (ENNReal.ofReal B₂),
            ← ENNReal.ofReal_mul hB₂.le,
            ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          dsimp [K₄]
          ring
  have hbd₅ : eLpNorm F₅ 2 volume ≤ ENNReal.ofReal (K₅ * c ^ (-2 : ℝ)) * N := by
    have hsmul : F₅ = (16 * c ^ (-2 : ℝ)) • fun x => w₂ x * ‖planarK g x‖ := rfl
    rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    have h1 := eLpNorm_weighted_planarK_le hw₂_meas hw₂_nn hB₂.le
      (hGrad₂ σ hσ).1 (hGrad₂ σ hσ).2 hg_meas hg_int
    calc ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            eLpNorm (fun x => w₂ x * ‖planarK g x‖) 2 volume
        ≤ ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            (ENNReal.ofReal B₂ * (ENNReal.ofReal plSplitConst * eLpNorm g 2 volume +
              ENNReal.ofReal 2 * eLpNorm g 1 volume)) :=
          mul_le_mul_of_nonneg_left h1 bot_le
      _ ≤ ENNReal.ofReal (16 * c ^ (-2 : ℝ)) *
            (ENNReal.ofReal B₂ * (ENNReal.ofReal plSplitConst * (ENNReal.ofReal 1 * N) +
              ENNReal.ofReal 2 * (ENNReal.ofReal L₀ * N))) := by
          gcongr
      _ = ENNReal.ofReal (K₅ * c ^ (-2 : ℝ)) * N := by
          rw [← mul_assoc (ENNReal.ofReal plSplitConst),
            ← ENNReal.ofReal_mul hCpl_nn,
            ← mul_assoc (ENNReal.ofReal 2),
            ← ENNReal.ofReal_mul zero_le_two,
            ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← mul_assoc (ENNReal.ofReal B₂),
            ← ENNReal.ofReal_mul hB₂.le,
            ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          dsimp [K₅]
          ring
  have hadd12 : eLpNorm (F₁ + F₂) 2 volume ≤ eLpNorm F₁ 2 volume + eLpNorm F₂ 2 volume :=
    eLpNorm_add_le hmF₁ hmF₂ one_le_two
  have hadd123 : eLpNorm (F₁ + F₂ + F₃) 2 volume ≤
      eLpNorm F₁ 2 volume + eLpNorm F₂ 2 volume + eLpNorm F₃ 2 volume :=
    (eLpNorm_add_le (hmF₁.add hmF₂) hmF₃ one_le_two).trans (add_le_add hadd12 le_rfl)
  have hadd1234 : eLpNorm (F₁ + F₂ + F₃ + F₄) 2 volume ≤
      eLpNorm F₁ 2 volume + eLpNorm F₂ 2 volume + eLpNorm F₃ 2 volume + eLpNorm F₄ 2 volume :=
    (eLpNorm_add_le ((hmF₁.add hmF₂).add hmF₃) hmF₄ one_le_two).trans (add_le_add hadd123 le_rfl)
  have hadd_all : eLpNorm (F₁ + F₂ + F₃ + F₄ + F₅) 2 volume ≤
      eLpNorm F₁ 2 volume + eLpNorm F₂ 2 volume + eLpNorm F₃ 2 volume +
        eLpNorm F₄ 2 volume + eLpNorm F₅ 2 volume :=
    (eLpNorm_add_le (((hmF₁.add hmF₂).add hmF₃).add hmF₄) hmF₅ one_le_two).trans
      (add_le_add hadd1234 le_rfl)
  have heLp :
      eLpNorm (((Jc c m).comp (AcG.comp (Rc c m)) - Apl_σ) f) 2 (planeMeasure m) ≤
        ENNReal.ofReal (C₂ * c ^ (-2 : ℝ)) * eLpNorm f 2 (planeMeasure m) := by
    rw [eLpNorm_congr_ae (coeFn_Jc_AcG_Rc_sub_Apl_ae hAcG hApl f hg_ae),
      eLpNorm_planeMeasure, ← hN_eq]
    calc eLpNorm (fun x => B0579.jb x ^ (m / 2) *
            ((B0579.cell c).indicator (AcGauss c σ g) x - Apl σ g x)) 2 volume
        ≤ eLpNorm (F₁ + F₂ + F₃ + F₄ + F₅) 2 volume := eLpNorm_mono_enorm_ae hpt
      _ ≤ eLpNorm F₁ 2 volume + eLpNorm F₂ 2 volume + eLpNorm F₃ 2 volume +
            eLpNorm F₄ 2 volume + eLpNorm F₅ 2 volume := hadd_all
      _ ≤ ENNReal.ofReal (K₁ * c ^ (-2 : ℝ)) * N +
            ENNReal.ofReal (K₂ * c ^ (-2 : ℝ)) * N +
            ENNReal.ofReal (K₃ * c ^ (-2 : ℝ)) * N +
            ENNReal.ofReal (K₄ * c ^ (-2 : ℝ)) * N +
            ENNReal.ofReal (K₅ * c ^ (-2 : ℝ)) * N :=
          add_le_add (add_le_add (add_le_add (add_le_add hbd₁ hbd₂) hbd₃) hbd₄) hbd₅
      _ ≤ ENNReal.ofReal (C₂ * c ^ (-2 : ℝ)) * N := by
          rw [← add_mul, ← add_mul, ← add_mul, ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
          dsimp [C₂]
          nlinarith
  rw [Lp.norm_def, Lp.norm_def]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) heLp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC₂_pos.le hcinv_nn)] at h
  exact h

end UnforcedLeray.Short.IIb

namespace Short.PartIIb

abbrev PlanarKernelBoundStep : Prop :=
  UnforcedLeray.Short.IIb.PlanarKernelBoundStep

theorem planarKernelBoundStep_proof : PlanarKernelBoundStep :=
  UnforcedLeray.Short.IIb.planarKernelBoundStep_proof

end Short.PartIIb

end
