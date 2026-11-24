import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenEulerSplitting.PeriodizedCylinderCoord.GaussDil
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Helper 2 for `PartII-b:F2/3/2` (`PeriodizedCylinderCoord`): Periodized modes & uniform tail bound

Source of record: `the November 2 reference manuscript`, lines 2167–2171, 2347–2358.

Establishes:
1. `HasZeroCirculationR c (frozenDirectMode q c a i)` for `c > 0`, `a ∈ [1, A]`;
2. Uniform `MemLp 2 (B0579.cellMeasure c m)` and norm bound for `frozenDirectMode q c a i`;
3. Uniform exponential `Xm m` convergence of `(B0579.cell c).indicator (frozenDirectMode q c a i)`
   to `planarFrozenDirectMode q a i` over `a ∈ [1, A]` as `c → ∞`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.PeriodizedCylCoordAux

open UnforcedLeray.Short.IIb

lemma summable_exp_neg_sq {B : ℝ} (hB : 0 < B) :
    Summable (fun n : ℤ => Real.exp (-(B * (n : ℝ) ^ 2))) := by
  have hr : Real.exp (-B) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hr0 : 0 ≤ Real.exp (-B) := (Real.exp_pos _).le
  have hnat : Summable (fun n : ℕ => Real.exp (-(B * ((n : ℤ) : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one hr0 hr)
    rw [Int.cast_natCast, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hn hB.le]
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr fun n => ?_
  push_cast
  ring_nf

lemma tsum_enorm_sq_le {B : ℝ} (hB : 0 < B) (s : ℤ → ℂ) :
    let w : ℤ → ℝ := fun n => Real.exp (-(B * (n : ℝ) ^ 2))
    let S : ℝ := ∑' n : ℤ, w n
    ‖∑' n : ℤ, s n‖ₑ ^ 2 ≤
      ENNReal.ofReal S *
        ∑' n : ℤ, ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2)) * ‖s n‖ₑ ^ 2 := by
  intro w S
  have hw_sum : Summable w := summable_exp_neg_sq hB
  have hw_pos : ∀ n : ℤ, 0 < w n := fun _ => Real.exp_pos _
  have hS_pos : 0 < S := by
    have h0 : w 0 ≤ S := hw_sum.le_tsum 0 (fun n _ => (hw_pos n).le)
    have hw0 : w 0 = 1 := by simp [w]
    linarith
  set u : ℤ → ℝ := fun n => ‖s n‖
  set v : ℤ → ℝ := fun n => Real.exp (B * (n : ℝ) ^ 2) * u n ^ 2
  have hv_nonneg : ∀ n : ℤ, 0 ≤ v n := fun _ => by positivity
  have hwv : ∀ n : ℤ, w n * Real.exp (B * (n : ℝ) ^ 2) = 1 := fun n => by
    dsimp [w]
    rw [← Real.exp_add]
    simp
  have hterm_eq : ∀ n : ℤ,
      ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2)) * ‖s n‖ₑ ^ 2 = ENNReal.ofReal (v n) := fun n => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hterm_eq]
  by_cases hv : Summable v
  · have hu : Summable u := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        ((hw_sum.add hv).mul_left (1 / 2))
      have hsq : 0 ≤ w n * (1 - Real.exp (B * (n : ℝ) ^ 2) * u n) ^ 2 := by positivity
      have hexp : w n * (1 - Real.exp (B * (n : ℝ) ^ 2) * u n) ^ 2 =
          w n - 2 * u n + v n := by
        dsimp [v]
        calc w n * (1 - Real.exp (B * (n : ℝ) ^ 2) * u n) ^ 2
            = w n - 2 * (w n * Real.exp (B * (n : ℝ) ^ 2)) * u n +
              (w n * Real.exp (B * (n : ℝ) ^ 2)) *
                (Real.exp (B * (n : ℝ) ^ 2) * u n ^ 2) := by ring
          _ = w n - 2 * u n + Real.exp (B * (n : ℝ) ^ 2) * u n ^ 2 := by
            rw [hwv n]; ring
      linarith
    set U := (∑' n : ℤ, u n) / S
    have hpt_amgm : ∀ n : ℤ, 2 * U * u n ≤ U ^ 2 * w n + v n := fun n => by
      have hsq : 0 ≤ w n * (U - Real.exp (B * (n : ℝ) ^ 2) * u n) ^ 2 := by positivity
      have hexp : w n * (U - Real.exp (B * (n : ℝ) ^ 2) * u n) ^ 2 =
          U ^ 2 * w n - 2 * U * u n + v n := by
        dsimp [v]
        calc w n * (U - Real.exp (B * (n : ℝ) ^ 2) * u n) ^ 2
            = U ^ 2 * w n - 2 * U * (w n * Real.exp (B * (n : ℝ) ^ 2)) * u n +
              (w n * Real.exp (B * (n : ℝ) ^ 2)) *
                (Real.exp (B * (n : ℝ) ^ 2) * u n ^ 2) := by ring
          _ = U ^ 2 * w n - 2 * U * u n + Real.exp (B * (n : ℝ) ^ 2) * u n ^ 2 := by
            rw [hwv n]; ring
      linarith
    have hsum_le := (hu.mul_left (2 * U)).tsum_le_tsum hpt_amgm ((hw_sum.mul_left (U ^ 2)).add hv)
    rw [tsum_mul_left, Summable.tsum_add (hw_sum.mul_left (U ^ 2)) hv, tsum_mul_left] at hsum_le
    have hcs : (∑' n : ℤ, u n) ^ 2 ≤ S * ∑' n : ℤ, v n := by
      have hmul := mul_le_mul_of_nonneg_left hsum_le hS_pos.le
      have hS_ne : S ≠ 0 := hS_pos.ne'
      have h1 : S * (2 * U * ∑' n : ℤ, u n) = 2 * (∑' n : ℤ, u n) ^ 2 := by
        dsimp [U]; field_simp
      have h2 : S * (U ^ 2 * S + ∑' n : ℤ, v n) =
          (∑' n : ℤ, u n) ^ 2 + S * ∑' n : ℤ, v n := by
        dsimp [U]; field_simp
      linarith
    have hnorm_per : ‖∑' n : ℤ, s n‖ ≤ ∑' n : ℤ, u n := norm_tsum_le_tsum_norm hu
    have hnorm_sq : ‖∑' n : ℤ, s n‖ ^ 2 ≤ S * ∑' n : ℤ, v n :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_per 2).trans hcs
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_tsum_of_nonneg hv_nonneg hv, ← ENNReal.ofReal_mul hS_pos.le]
    exact ENNReal.ofReal_le_ofReal hnorm_sq
  · have htop : (∑' n : ℤ, ENNReal.ofReal (v n)) = ⊤ := by
      by_contra hne
      apply hv
      have hnn : Summable (fun n : ℤ => (v n).toNNReal) :=
        ENNReal.tsum_coe_ne_top_iff_summable.mp hne
      have hcoe : Summable (fun n : ℤ => ((v n).toNNReal : ℝ)) :=
        NNReal.summable_coe.mpr hnn
      exact hcoe.congr fun n => Real.coe_toNNReal (v n) (hv_nonneg n)
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hS_pos).ne']
    exact le_top

lemma cell_shift_sq_ge_ne_zero {c : ℝ} (hc1 : 1 ≤ c) {x : B0579.Plane} (hx : x ∈ B0579.cell c)
    {n : ℤ} (hn0 : n ≠ 0) :
    (x.1 ^ 2 + x.2 ^ 2) / 2 + (n : ℝ) ^ 2 / 16 + c ^ 2 / 16 ≤ (x.1 - n * c) ^ 2 + x.2 ^ 2 := by
  have hx1_lo : -(c / 2) ≤ x.1 := hx.1.1
  have hx1_hi : x.1 ≤ c / 2 := hx.1.2.le
  have hx1_sq : x.1 ^ 2 ≤ c ^ 2 / 4 := by nlinarith
  have hc_sq : 1 ≤ c ^ 2 := by nlinarith
  have hnc : (n : ℝ) ^ 2 * c ^ 2 / 4 ≤ (x.1 - n * c) ^ 2 := by
    rcases lt_or_gt_of_ne hn0 with hlt | hgt
    · have hn_le : n ≤ -1 := Int.le_sub_one_of_lt hlt
      have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hn_le
      have h1' : (n : ℝ) * c / 2 ≤ -(c / 2) := by nlinarith
      have h2' : -(n : ℝ) * c / 2 ≤ x.1 - (n : ℝ) * c := by linarith
      have h3' : 0 ≤ -(n : ℝ) * c / 2 := by nlinarith
      nlinarith
    · have hn_ge : 1 ≤ n := hgt
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      have h1' : c / 2 ≤ (n : ℝ) * c / 2 := by nlinarith
      have h2' : (n : ℝ) * c / 2 ≤ (n : ℝ) * c - x.1 := by linarith
      have h3' : 0 ≤ (n : ℝ) * c / 2 := by nlinarith
      nlinarith
  have hn_sq : 1 ≤ (n : ℝ) ^ 2 := by
    have h1 : 1 ≤ |n| := Int.one_le_abs hn0
    have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1
    nlinarith [sq_abs (n : ℝ)]
  have hpart1 : x.1 ^ 2 / 2 ≤ (n : ℝ) ^ 2 * c ^ 2 / 8 := by nlinarith
  have hpart2 : (n : ℝ) ^ 2 / 16 ≤ (n : ℝ) ^ 2 * c ^ 2 / 16 := by nlinarith
  have hpart3 : c ^ 2 / 16 ≤ (n : ℝ) ^ 2 * c ^ 2 / 16 := by nlinarith
  linarith [sq_nonneg x.2]

lemma cell_shift_sq_ge_all {c : ℝ} (hc1 : 1 ≤ c) {x : B0579.Plane} (hx : x ∈ B0579.cell c)
    (n : ℤ) :
    (x.1 ^ 2 + x.2 ^ 2) / 2 + (n : ℝ) ^ 2 / 16 ≤ (x.1 - n * c) ^ 2 + x.2 ^ 2 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Int.cast_zero, zero_mul, sub_zero]
    linarith [sq_nonneg x.1, sq_nonneg x.2]
  · have h := cell_shift_sq_ge_ne_zero hc1 hx hn0
    linarith [sq_nonneg c]

lemma not_mem_cell_sq_ge {c : ℝ} (hc0 : 0 ≤ c) {x : B0579.Plane} (hx : x ∉ B0579.cell c) :
    c ^ 2 / 4 ≤ x.1 ^ 2 + x.2 ^ 2 := by
  have hx1 : ¬ (-(c / 2) ≤ x.1 ∧ x.1 < c / 2) := fun h => hx ⟨h, trivial⟩
  rcases not_and_or.mp hx1 with hlo | hhi
  · have hlo' := not_le.mp hlo
    nlinarith [sq_nonneg x.2]
  · have hhi' := not_lt.mp hhi
    nlinarith [sq_nonneg x.2]

lemma exists_jb_rpow_le_exp {m A : ℝ} (hm : 0 ≤ m) (hA : 1 ≤ A) :
    ∃ C_jb : ℝ, 0 < C_jb ∧ ∀ x : B0579.Plane,
      B0579.jb x ^ m ≤ C_jb * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by
  have h8A : 0 < 8 * A := by linarith
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := UnforcedLeray.Gaussian.rpow_mul_exp_neg_le hm
  let K : ℝ := (8 * A) ^ m * Real.exp (1 / (8 * A)) * C₀
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, fun x => ?_⟩
  have hs_nn : 0 ≤ B0579.jb x / (8 * A) := div_nonneg (B0579.jb_pos x).le h8A.le
  have habs := hC₀ (B0579.jb x / (8 * A)) hs_nn
  have h1 : (B0579.jb x / (8 * A)) ^ m = B0579.jb x ^ m / (8 * A) ^ m :=
    Real.div_rpow (B0579.jb_pos x).le h8A.le m
  have h2 : Real.exp (-(B0579.jb x / (8 * A))) *
      (Real.exp (1 / (8 * A)) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A))) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    unfold B0579.jb
    have : -((1 + x.1 ^ 2 + x.2 ^ 2) / (8 * A)) +
        (1 / (8 * A) + (x.1 ^ 2 + x.2 ^ 2) / (8 * A)) = 0 := by ring
    rw [this, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_left habs
    (by positivity : 0 ≤ (8 * A) ^ m * Real.exp (1 / (8 * A)) *
      Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
  rw [h1] at h3
  have h8_ne : (8 * A) ^ m ≠ 0 := (Real.rpow_pos_of_pos h8A m).ne'
  have h4 : (8 * A) ^ m * Real.exp (1 / (8 * A)) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) *
      (B0579.jb x ^ m / (8 * A) ^ m * Real.exp (-(B0579.jb x / (8 * A)))) = B0579.jb x ^ m := by
    calc (8 * A) ^ m * Real.exp (1 / (8 * A)) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) *
          (B0579.jb x ^ m / (8 * A) ^ m * Real.exp (-(B0579.jb x / (8 * A))))
        = ((8 * A) ^ m / (8 * A) ^ m) * B0579.jb x ^ m *
          (Real.exp (-(B0579.jb x / (8 * A))) *
            (Real.exp (1 / (8 * A)) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)))) := by ring
      _ = B0579.jb x ^ m := by rw [div_self h8_ne, h2, one_mul, mul_one]
  rw [h4] at h3
  calc B0579.jb x ^ m
      ≤ (8 * A) ^ m * Real.exp (1 / (8 * A)) * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) * C₀ := h3
    _ = K * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := by dsimp [K]; ring

lemma ae_summable_cylPeriodize {c : ℝ} (hc : 0 < c) {F : B0579.Plane → ℂ}
    (hFm : Measurable F) (hFi : Integrable F volume) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Summable (fun n : ℤ => F (x.1 - n * c, x.2)) := by
  have hlin : ∫⁻ x in B0579.cell c, (∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ) = ∫⁻ y, ‖F y‖ₑ := by
    rw [cell_eq_cylCell]
    exact UnforcedLeray.Cyl.lintegral_cell_periodize hc hFm.enorm
  have hmeas_sum : Measurable (fun x : B0579.Plane => ∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ) :=
    Measurable.tsum fun n => hFm.enorm.comp (UnforcedLeray.Cyl.measurable_shift c n)
  have hlt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ) < ⊤ :=
    ae_lt_top hmeas_sum (by rw [hlin]; exact hFi.2.ne)
  filter_upwards [hlt] with x hx
  have hnn : Summable (fun n : ℤ => ‖F (x.1 - n * c, x.2)‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hx.ne
  exact Summable.of_nnnorm hnn

lemma aestronglyMeasurable_cylPeriodize_cell {c : ℝ} (hc : 0 < c) {F : B0579.Plane → ℂ}
    (hFm : Measurable F) (hFi : Integrable F volume) :
    AEStronglyMeasurable (UnforcedLeray.Cyl.periodize c F)
      (volume.restrict (B0579.cell c)) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset ℤ)))
    (f := fun (s : Finset ℤ) (x : B0579.Plane) => ∑ n ∈ s, F (x.1 - n * c, x.2))
    (fun s => (Finset.measurable_sum s fun n _ =>
      hFm.comp (UnforcedLeray.Cyl.measurable_shift c n)).aestronglyMeasurable) ?_
  filter_upwards [ae_summable_cylPeriodize hc hFm hFi] with x hx
  exact hx.hasSum

lemma integrableOn_and_integral_cylPeriodize {c : ℝ} (hc : 0 < c) {F : B0579.Plane → ℂ}
    (hFm : Measurable F) (hFi : Integrable F volume) :
    IntegrableOn (UnforcedLeray.Cyl.periodize c F) (B0579.cell c) volume ∧
      (∫ x in B0579.cell c, UnforcedLeray.Cyl.periodize c F x) = ∫ y, F y := by
  have haesm := aestronglyMeasurable_cylPeriodize_cell hc hFm hFi
  have hfin : ∫⁻ x in B0579.cell c, ‖UnforcedLeray.Cyl.periodize c F x‖ₑ < ⊤ := by
    have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        ‖UnforcedLeray.Cyl.periodize c F x‖ₑ ≤ ∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ := by
      filter_upwards [ae_summable_cylPeriodize hc hFm hFi] with x hx
      have hn : Summable (fun n : ℤ => ‖F (x.1 - n * c, x.2)‖) := hx.norm
      have h1 : ‖UnforcedLeray.Cyl.periodize c F x‖ ≤ ∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ :=
        norm_tsum_le_tsum_norm hn
      rw [← ofReal_norm]
      calc ENNReal.ofReal ‖UnforcedLeray.Cyl.periodize c F x‖
          ≤ ENNReal.ofReal (∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖) := ENNReal.ofReal_le_ofReal h1
        _ = ∑' n : ℤ, ENNReal.ofReal ‖F (x.1 - n * c, x.2)‖ :=
            ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hn
        _ = ∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ := by simp_rw [ofReal_norm]
    calc ∫⁻ x in B0579.cell c, ‖UnforcedLeray.Cyl.periodize c F x‖ₑ
        ≤ ∫⁻ x in B0579.cell c, ∑' n : ℤ, ‖F (x.1 - n * c, x.2)‖ₑ := lintegral_mono_ae hpt
      _ = ∫⁻ y, ‖F y‖ₑ := by
          rw [cell_eq_cylCell]
          exact UnforcedLeray.Cyl.lintegral_cell_periodize hc hFm.enorm
      _ < ⊤ := hFi.2
  have hintOn : IntegrableOn (UnforcedLeray.Cyl.periodize c F) (B0579.cell c) volume :=
    ⟨haesm, hfin⟩
  have hI := UnforcedLeray.Cyl.integral_cell_periodize_mul (𝕜 := ℂ) hc (f := F)
    (g := fun _ : B0579.Plane => (1 : ℂ)) hFm.stronglyMeasurable stronglyMeasurable_const
    (fun _ => rfl) (by simpa using hFi)
  simp only [mul_one] at hI
  rw [← cell_eq_cylCell] at hI
  exact ⟨hintOn, hI⟩

lemma frozenDirectMode_eq_cylPeriodize (q : Blueprint.Planar.Profile) (c a : ℝ) (i : Fin 2)
    (x : B0579.Plane) :
    frozenDirectMode q c a i x =
      ![2 * (UnforcedLeray.Cyl.periodize c (dilPlanarMode q a) x).re,
        -2 * (UnforcedLeray.Cyl.periodize c (dilPlanarMode q a) x).im] i := by
  unfold frozenDirectMode
  rw [periodizePlanar_eq_cylPeriodize]

lemma hasZeroCirculationR_frozenDirectMode {q : Blueprint.Planar.Profile} {A c a : ℝ}
    (hc : 0 < c) (ha1 : 1 ≤ a) (haA : a ≤ A)
    (hq : Blueprint.Planar.MemXG q) (hqc : ContinuousOn q (Ioi 0)) (i : Fin 2) :
    HasZeroCirculationR c (frozenDirectMode q c a i) := by
  have hFm := measurable_dilPlanarMode hqc a
  have hFi := integrable_dilPlanarMode ha1 haA hq hqc
  obtain ⟨hintOn, hInt⟩ := integrableOn_and_integral_cylPeriodize hc hFm hFi
  rw [integral_dilPlanarMode_eq_zero] at hInt
  have heq : frozenDirectMode q c a i =
      fun x => ![2 * Complex.reCLM (UnforcedLeray.Cyl.periodize c (dilPlanarMode q a) x),
                 -2 * Complex.imCLM (UnforcedLeray.Cyl.periodize c (dilPlanarMode q a) x)] i := by
    funext x
    exact frozenDirectMode_eq_cylPeriodize q c a i x
  rw [heq]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    refine ⟨(Complex.reCLM.integrable_comp hintOn).const_mul 2, ?_⟩
    rw [integral_const_mul, Complex.reCLM.integral_comp_comm hintOn, hInt]
    simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨(Complex.imCLM.integrable_comp hintOn).const_mul (-2), ?_⟩
    rw [integral_const_mul, Complex.imCLM.integral_comp_comm hintOn, hInt]
    simp

/-- Uniform `Xmc c m` norm bound and exponential `Xm m` convergence of periodized direct modes. -/
theorem exists_frozenDirectMode_memLp_and_tail {m A : ℝ} (hm : 0 ≤ m) (hA : 1 ≤ A)
    {q : Blueprint.Planar.Profile} (hq : Blueprint.Planar.MemXG q)
    (hqc : ContinuousOn q (Ioi 0)) :
    ∃ (K_norm K_tail : ℝ), 0 ≤ K_norm ∧ 0 ≤ K_tail ∧
      ∀ (c a : ℝ), 1 ≤ c → 1 ≤ a → a ≤ A → ∀ i : Fin 2,
        MemLp (frozenDirectMode q c a i) 2 (B0579.cellMeasure c m) ∧
        eLpNorm (frozenDirectMode q c a i) 2 (B0579.cellMeasure c m) ≤ ENNReal.ofReal K_norm ∧
        eLpNorm ((B0579.cell c).indicator (frozenDirectMode q c a i) - planarFrozenDirectMode q a i)
            2 (planeMeasure m) ≤
          ENNReal.ofReal (K_tail * Real.exp (-(c ^ 2 / (128 * A)))) := by
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  let B : ℝ := 1 / (64 * A)
  have hB : 0 < B := by dsimp [B]; positivity
  have hw_sum : Summable (fun n : ℤ => Real.exp (-(B * (n : ℝ) ^ 2))) := summable_exp_neg_sq hB
  let S : ℝ := ∑' n : ℤ, Real.exp (-(B * (n : ℝ) ^ 2))
  have hS_pos : 0 < S := by
    have h0 : Real.exp (-(B * ((0 : ℤ) : ℝ) ^ 2)) ≤ S :=
      hw_sum.le_tsum 0 (fun _ _ => (Real.exp_pos _).le)
    simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      neg_zero, Real.exp_zero] at h0
    linarith
  obtain ⟨C_jb, hCjb_pos, hCjb⟩ := exists_jb_rpow_le_exp hm hA
  let Qg : ℝ := A * Blueprint.Planar.gaussianNorm q ^ 2
  have hQg_nn : 0 ≤ Qg := by dsimp [Qg]; positivity
  let K_norm : ℝ := Real.sqrt (4 * S * C_jb * Qg)
  let K_tail : ℝ := Real.sqrt (4 * (S + 1) * C_jb * Qg)
  refine ⟨K_norm, K_tail, Real.sqrt_nonneg _, Real.sqrt_nonneg _, fun c a hc1 ha1 haA i => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  set F := dilPlanarMode q a
  have hFm : Measurable F := measurable_dilPlanarMode hqc a
  have hFi : Integrable F volume := integrable_dilPlanarMode ha1 haA hq hqc
  set G : B0579.Plane → ℝ≥0∞ := fun y =>
    ‖F y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((y.1 ^ 2 + y.2 ^ 2) / (4 * A)))
  have hGm : Measurable G := (hFm.enorm.pow_const 2).mul (by fun_prop)
  have hG_int : ∫⁻ y, G y ≤ ENNReal.ofReal Qg := lintegral_dilPlanarMode_gauss_le ha1 haA hq
  -- Measurability of `frozenDirectMode q c a i` on `B0579.cellMeasure c m`
  have haesm_cell : AEStronglyMeasurable (frozenDirectMode q c a i)
      (B0579.cellMeasure c m) := by
    have hper_m : AEStronglyMeasurable (UnforcedLeray.Cyl.periodize c F)
        (B0579.cellMeasure c m) :=
      (aestronglyMeasurable_cylPeriodize_cell hc0 hFm hFi).mono_ac (B0579.cellMeasure_ac c m)
    have heq : frozenDirectMode q c a i =
        fun x => ![2 * (UnforcedLeray.Cyl.periodize c F x).re,
                   -2 * (UnforcedLeray.Cyl.periodize c F x).im] i :=
      funext (frozenDirectMode_eq_cylPeriodize q c a i)
    rw [heq]
    fin_cases i
    · exact (Complex.continuous_re.comp_aestronglyMeasurable hper_m).const_mul 2
    · exact (Complex.continuous_im.comp_aestronglyMeasurable hper_m).const_mul (-2)
  -- Part A: Bound on `eLpNorm (frozenDirectMode q c a i) 2 (B0579.cellMeasure c m)`
  have hpt_norm : ∀ x ∈ B0579.cell c,
      (B0579.density m x : ℝ≥0∞) * ‖frozenDirectMode q c a i x‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * S * C_jb) * UnforcedLeray.Cyl.periodize c G x := by
    intro x hx
    have hdens : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
      rw [← B0579.coe_density m x, ENNReal.ofReal_coe_nnreal]
    rw [hdens]
    have hfdm : ‖frozenDirectMode q c a i x‖ ≤ 2 * ‖UnforcedLeray.Cyl.periodize c F x‖ := by
      rw [frozenDirectMode_eq_cylPeriodize]
      have hre := Complex.abs_re_le_norm (UnforcedLeray.Cyl.periodize c F x)
      have him := Complex.abs_im_le_norm (UnforcedLeray.Cyl.periodize c F x)
      fin_cases i <;> simp <;> linarith
    have hfdm_sq : ‖frozenDirectMode q c a i x‖ₑ ^ 2 ≤
        ENNReal.ofReal 4 * ‖UnforcedLeray.Cyl.periodize c F x‖ₑ ^ 2 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (frozenDirectMode q c a i x)])
    have hcs := tsum_enorm_sq_le hB (fun n : ℤ => F (x.1 - n * c, x.2))
    have hjb_n : ∀ n : ℤ,
        ENNReal.ofReal (B0579.jb x ^ m) * ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2)) ≤
          ENNReal.ofReal C_jb *
            ENNReal.ofReal (Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A))) := fun n => by
      have h0 : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
      rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul hCjb_pos.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsh := cell_shift_sq_ge_all hc1 hx n
      have hexp_le : Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) * Real.exp (B * (n : ℝ) ^ 2) ≤
          Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [B]
        have hdiv := div_le_div_of_nonneg_right hsh (by positivity : 0 ≤ 4 * A)
        linarith [show ((x.1 ^ 2 + x.2 ^ 2) / 2 + (n : ℝ) ^ 2 / 16) / (4 * A) =
          (x.1 ^ 2 + x.2 ^ 2) / (8 * A) + 1 / (64 * A) * (n : ℝ) ^ 2 by field_simp; ring]
      calc B0579.jb x ^ m * Real.exp (B * (n : ℝ) ^ 2)
          ≤ (C_jb * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A))) * Real.exp (B * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (hCjb x) (Real.exp_pos _).le
        _ = C_jb * (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) * Real.exp (B * (n : ℝ) ^ 2)) := by
            ring
        _ ≤ C_jb * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)) :=
            mul_le_mul_of_nonneg_left hexp_le hCjb_pos.le
    calc ENNReal.ofReal (B0579.jb x ^ m) * ‖frozenDirectMode q c a i x‖ₑ ^ 2
        ≤ ENNReal.ofReal (B0579.jb x ^ m) *
            (ENNReal.ofReal 4 *
              (ENNReal.ofReal S * ∑' n : ℤ,
                ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2)) * ‖F (x.1 - n * c, x.2)‖ₑ ^ 2)) := by
          gcongr
          exact hfdm_sq.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
      _ = ENNReal.ofReal (4 * S) * ∑' n : ℤ,
            (ENNReal.ofReal (B0579.jb x ^ m) * ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2))) *
              ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 := by
          simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← ENNReal.tsum_mul_left]
          exact tsum_congr fun n => by ring
      _ ≤ ENNReal.ofReal (4 * S) * ∑' n : ℤ,
            ENNReal.ofReal C_jb * G (x.1 - n * c, x.2) := by
          refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun n => ?_)
          calc (ENNReal.ofReal (B0579.jb x ^ m) * ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2))) *
                ‖F (x.1 - n * c, x.2)‖ₑ ^ 2
              ≤ (ENNReal.ofReal C_jb *
                  ENNReal.ofReal (Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)))) *
                ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 := mul_le_mul' (hjb_n n) le_rfl
            _ = ENNReal.ofReal C_jb * G (x.1 - n * c, x.2) := by dsimp [G]; ring
      _ = ENNReal.ofReal (4 * S * C_jb) * UnforcedLeray.Cyl.periodize c G x := by
          rw [ENNReal.tsum_mul_left, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rfl
  have hlint_norm : ∫⁻ x in B0579.cell c,
      (B0579.density m x : ℝ≥0∞) * ‖frozenDirectMode q c a i x‖ₑ ^ 2 ≤
        ENNReal.ofReal (K_norm ^ 2) := by
    calc ∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖frozenDirectMode q c a i x‖ₑ ^ 2
        ≤ ∫⁻ x in B0579.cell c,
            ENNReal.ofReal (4 * S * C_jb) * UnforcedLeray.Cyl.periodize c G x :=
          setLIntegral_mono' (B0579.measurableSet_cell c) hpt_norm
      _ = ENNReal.ofReal (4 * S * C_jb) * ∫⁻ y, G y := by
          rw [cell_eq_cylCell, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            UnforcedLeray.Cyl.lintegral_cell_periodize hc0 hGm]
      _ ≤ ENNReal.ofReal (4 * S * C_jb) * ENNReal.ofReal Qg :=
          mul_le_mul' le_rfl hG_int
      _ = ENNReal.ofReal (K_norm ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          exact (Real.sq_sqrt (by positivity)).symm
  have heLp_norm : eLpNorm (frozenDirectMode q c a i) 2 (B0579.cellMeasure c m) ≤
      ENNReal.ofReal K_norm := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      B0579.cellMeasure,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (B0579.measurable_density m).coe_nnreal_ennreal
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
    calc (∫⁻ x in B0579.cell c,
            (B0579.density m x : ℝ≥0∞) * ‖frozenDirectMode q c a i x‖ₑ ^ 2) ^ (2 : ℝ)⁻¹
        ≤ (ENNReal.ofReal (K_norm ^ 2)) ^ (2 : ℝ)⁻¹ :=
          ENNReal.rpow_le_rpow hlint_norm (by positivity)
      _ = ENNReal.ofReal K_norm := by
          rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by positivity),
            ← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq (Real.sqrt_nonneg _)]
  -- Part B: Tail bound on `planeMeasure m`
  set D : B0579.Plane → ℝ :=
    (B0579.cell c).indicator (frozenDirectMode q c a i) - planarFrozenDirectMode q a i
  set E_c : ℝ := Real.exp (-(B * c ^ 2))
  have hEc_pos : 0 < E_c := Real.exp_pos _
  -- Region 1: a.e. on `B0579.cell c`
  have hae_cell_tail : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * S * C_jb * E_c) * UnforcedLeray.Cyl.periodize c G x := by
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c),
      ae_summable_cylPeriodize hc0 hFm hFi] with x hx hsum
    have hdens : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
      rw [← B0579.coe_density m x, ENNReal.ofReal_coe_nnreal]
    rw [hdens]
    set s : ℤ → ℂ := fun n => F (x.1 - n * c, x.2)
    set s_tail : ℤ → ℂ := fun n => if n = 0 then 0 else s n
    have hs₀ : HasSum (fun n : ℤ => if n = 0 then s 0 else 0) (s 0) := hasSum_ite_eq 0 (s 0)
    have hper_sub : UnforcedLeray.Cyl.periodize c F x - F x = ∑' n : ℤ, s_tail n := by
      have hs0_eq : s 0 = F x := by dsimp [s]; simp
      calc UnforcedLeray.Cyl.periodize c F x - F x
          = (∑' n : ℤ, s n) - s 0 := by rw [hs0_eq]; rfl
        _ = (∑' n : ℤ, s n) - ∑' n : ℤ, (if n = 0 then s 0 else 0) := by rw [hs₀.tsum_eq]
        _ = ∑' n : ℤ, (s n - if n = 0 then s 0 else 0) := (hsum.tsum_sub hs₀.summable).symm
        _ = ∑' n : ℤ, s_tail n := by
            refine tsum_congr fun n => ?_
            by_cases hn : n = 0 <;> simp [s_tail, hn]
    have hD_le : ‖D x‖ ≤ 2 * ‖∑' n : ℤ, s_tail n‖ := by
      change ‖(B0579.cell c).indicator (frozenDirectMode q c a i) x -
          planarFrozenDirectMode q a i x‖ ≤ 2 * ‖∑' n : ℤ, s_tail n‖
      rw [indicator_of_mem hx, frozenDirectMode_eq_cylPeriodize]
      unfold planarFrozenDirectMode
      rw [← hper_sub]
      have hre := Complex.abs_re_le_norm (UnforcedLeray.Cyl.periodize c F x - F x)
      have him := Complex.abs_im_le_norm (UnforcedLeray.Cyl.periodize c F x - F x)
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Real.norm_eq_abs]
        have : |2 * (UnforcedLeray.Cyl.periodize c F x).re - 2 * (F x).re| =
            2 * |(UnforcedLeray.Cyl.periodize c F x - F x).re| := by
          rw [Complex.sub_re, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs]
        have : |-2 * (UnforcedLeray.Cyl.periodize c F x).im - -2 * (F x).im| =
            2 * |(UnforcedLeray.Cyl.periodize c F x - F x).im| := by
          rw [Complex.sub_im]
          have h1 : -2 * (UnforcedLeray.Cyl.periodize c F x).im - -2 * (F x).im =
              (-2) * ((UnforcedLeray.Cyl.periodize c F x).im - (F x).im) := by ring
          rw [h1, abs_mul]; norm_num
        linarith
    have hD_sq : ‖D x‖ₑ ^ 2 ≤ ENNReal.ofReal 4 * ‖∑' n : ℤ, s_tail n‖ₑ ^ 2 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (D x)])
    have hcs := tsum_enorm_sq_le hB s_tail
    have hterm_n : ∀ n : ℤ,
        (ENNReal.ofReal (B0579.jb x ^ m) * ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2))) *
          ‖s_tail n‖ₑ ^ 2 ≤
        ENNReal.ofReal (C_jb * E_c) * G (x.1 - n * c, x.2) := fun n => by
      by_cases hn0 : n = 0
      · subst hn0
        simp [s_tail]
      · have hs_eq : s_tail n = F (x.1 - n * c, x.2) := by simp [s_tail, s, hn0]
        rw [hs_eq]
        have h0 : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
        have hjb_e : ENNReal.ofReal (B0579.jb x ^ m) *
            ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2)) ≤
              ENNReal.ofReal (C_jb * E_c) *
                ENNReal.ofReal (Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A))) := by
          rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hsh := cell_shift_sq_ge_ne_zero hc1 hx hn0
          have hexp_le : Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) * Real.exp (B * (n : ℝ) ^ 2) ≤
              E_c * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)) := by
            dsimp [E_c]
            rw [← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            dsimp [B]
            have hdiv := div_le_div_of_nonneg_right hsh (by positivity : 0 ≤ 4 * A)
            linarith [show ((x.1 ^ 2 + x.2 ^ 2) / 2 + (n : ℝ) ^ 2 / 16 + c ^ 2 / 16) / (4 * A) =
              (x.1 ^ 2 + x.2 ^ 2) / (8 * A) + 1 / (64 * A) * (n : ℝ) ^ 2 +
                1 / (64 * A) * c ^ 2 by field_simp; ring]
          calc B0579.jb x ^ m * Real.exp (B * (n : ℝ) ^ 2)
              ≤ (C_jb * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A))) * Real.exp (B * (n : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right (hCjb x) (Real.exp_pos _).le
            _ = C_jb * (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) * Real.exp (B * (n : ℝ) ^ 2)) := by
                ring
            _ ≤ C_jb * (E_c * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A))) :=
                mul_le_mul_of_nonneg_left hexp_le hCjb_pos.le
            _ = C_jb * E_c * Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)) := by ring
        calc (ENNReal.ofReal (B0579.jb x ^ m) * ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2))) *
              ‖F (x.1 - n * c, x.2)‖ₑ ^ 2
            ≤ (ENNReal.ofReal (C_jb * E_c) *
                ENNReal.ofReal (Real.exp (((x.1 - n * c) ^ 2 + x.2 ^ 2) / (4 * A)))) *
              ‖F (x.1 - n * c, x.2)‖ₑ ^ 2 := by gcongr
          _ = ENNReal.ofReal (C_jb * E_c) * G (x.1 - n * c, x.2) := by dsimp [G]; ring
    calc ENNReal.ofReal (B0579.jb x ^ m) * ‖D x‖ₑ ^ 2
        ≤ ENNReal.ofReal (B0579.jb x ^ m) *
            (ENNReal.ofReal 4 *
              (ENNReal.ofReal S * ∑' n : ℤ,
                ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2)) * ‖s_tail n‖ₑ ^ 2)) := by
          gcongr
          exact hD_sq.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
      _ = ENNReal.ofReal (4 * S) * ∑' n : ℤ,
            (ENNReal.ofReal (B0579.jb x ^ m) * ENNReal.ofReal (Real.exp (B * (n : ℝ) ^ 2))) *
              ‖s_tail n‖ₑ ^ 2 := by
          simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← ENNReal.tsum_mul_left]
          exact tsum_congr fun n => by ring
      _ ≤ ENNReal.ofReal (4 * S) * ∑' n : ℤ,
            ENNReal.ofReal (C_jb * E_c) * G (x.1 - n * c, x.2) :=
          mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hterm_n)
      _ = ENNReal.ofReal (4 * S * C_jb * E_c) * UnforcedLeray.Cyl.periodize c G x := by
          rw [ENNReal.tsum_mul_left, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf; rfl
  have hlint_cell_tail : ∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * S * C_jb * Qg * E_c) := by
    calc ∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2
        ≤ ∫⁻ x in B0579.cell c,
            ENNReal.ofReal (4 * S * C_jb * E_c) * UnforcedLeray.Cyl.periodize c G x :=
          lintegral_mono_ae hae_cell_tail
      _ = ENNReal.ofReal (4 * S * C_jb * E_c) * ∫⁻ y, G y := by
          rw [cell_eq_cylCell, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            UnforcedLeray.Cyl.lintegral_cell_periodize hc0 hGm]
      _ ≤ ENNReal.ofReal (4 * S * C_jb * E_c) * ENNReal.ofReal Qg :=
          mul_le_mul' le_rfl hG_int
      _ = ENNReal.ofReal (4 * S * C_jb * Qg * E_c) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- Region 2: outside `B0579.cell c`
  have hpt_compl_tail : ∀ x ∈ (B0579.cell c)ᶜ,
      (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * C_jb * E_c) * G x := by
    intro x hx
    have hdens : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
      rw [← B0579.coe_density m x, ENNReal.ofReal_coe_nnreal]
    rw [hdens]
    have hD_le : ‖D x‖ ≤ 2 * ‖F x‖ := by
      change ‖(B0579.cell c).indicator (frozenDirectMode q c a i) x -
          planarFrozenDirectMode q a i x‖ ≤ 2 * ‖F x‖
      rw [indicator_of_notMem hx, zero_sub, norm_neg]
      unfold planarFrozenDirectMode
      have hre := Complex.abs_re_le_norm (F x)
      have him := Complex.abs_im_le_norm (F x)
      fin_cases i <;> simp <;> linarith
    have hD_sq : ‖D x‖ₑ ^ 2 ≤ ENNReal.ofReal 4 * ‖F x‖ₑ ^ 2 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (D x)])
    have hsq_ge : c ^ 2 / 4 ≤ x.1 ^ 2 + x.2 ^ 2 := not_mem_cell_sq_ge hc0.le hx
    have hjb_out : ENNReal.ofReal (B0579.jb x ^ m) ≤
        ENNReal.ofReal (C_jb * E_c) *
          ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp_le : Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) ≤
          E_c * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
        dsimp [E_c]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [B]
        have hdiv := div_le_div_of_nonneg_right hsq_ge (by positivity : 0 ≤ 8 * A)
        have h1 : (c ^ 2 / 4) / (8 * A) = c ^ 2 / (32 * A) := by ring
        have h2 : 1 / (64 * A) * c ^ 2 ≤ c ^ 2 / (32 * A) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left (sq_nonneg c) (by positivity) (by linarith)
        linarith [show -(1 / (64 * A) * c ^ 2) + (x.1 ^ 2 + x.2 ^ 2) / (4 * A) =
          (x.1 ^ 2 + x.2 ^ 2) / (8 * A) + ((x.1 ^ 2 + x.2 ^ 2) / (8 * A) - 1 / (64 * A) * c ^ 2)
          by ring]
      calc B0579.jb x ^ m
          ≤ C_jb * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (8 * A)) := hCjb x
        _ ≤ C_jb * (E_c * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A))) :=
            mul_le_mul_of_nonneg_left hexp_le hCjb_pos.le
        _ = C_jb * E_c * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by ring
    calc ENNReal.ofReal (B0579.jb x ^ m) * ‖D x‖ₑ ^ 2
        ≤ (ENNReal.ofReal (C_jb * E_c) *
            ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / (4 * A)))) *
          (ENNReal.ofReal 4 * ‖F x‖ₑ ^ 2) := mul_le_mul' hjb_out hD_sq
      _ = (ENNReal.ofReal 4 * ENNReal.ofReal (C_jb * E_c)) * G x := by dsimp [G]; ring
      _ = ENNReal.ofReal (4 * C_jb * E_c) * G x := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          congr 2; ring
  have hlint_compl_tail : ∫⁻ x in (B0579.cell c)ᶜ, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * C_jb * Qg * E_c) := by
    calc ∫⁻ x in (B0579.cell c)ᶜ, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2
        ≤ ∫⁻ x in (B0579.cell c)ᶜ, ENNReal.ofReal (4 * C_jb * E_c) * G x :=
          setLIntegral_mono' (B0579.measurableSet_cell c).compl hpt_compl_tail
      _ ≤ ∫⁻ x, ENNReal.ofReal (4 * C_jb * E_c) * G x :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal (4 * C_jb * E_c) * ∫⁻ x, G x :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (4 * C_jb * E_c) * ENNReal.ofReal Qg :=
          mul_le_mul' le_rfl hG_int
      _ = ENNReal.ofReal (4 * C_jb * Qg * E_c) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- Combine cell + complement on `planeMeasure m`
  have hlint_total : ∫⁻ x, ‖D x‖ₑ ^ 2 ∂(planeMeasure m) ≤
      ENNReal.ofReal ((K_tail * Real.exp (-(c ^ 2 / (128 * A)))) ^ 2) := by
    have hdens_eq : ∫⁻ x, ‖D x‖ₑ ^ 2 ∂(planeMeasure m) =
        ∫⁻ x, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2 :=
      PlanarModesHelp.lint_planeMeasure m hm _
    rw [hdens_eq, ← lintegral_add_compl _ (B0579.measurableSet_cell c)]
    calc (∫⁻ x in B0579.cell c, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2) +
            (∫⁻ x in (B0579.cell c)ᶜ, (B0579.density m x : ℝ≥0∞) * ‖D x‖ₑ ^ 2)
        ≤ ENNReal.ofReal (4 * S * C_jb * Qg * E_c) + ENNReal.ofReal (4 * C_jb * Qg * E_c) :=
          add_le_add hlint_cell_tail hlint_compl_tail
      _ = ENNReal.ofReal ((K_tail * Real.exp (-(c ^ 2 / (128 * A)))) ^ 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          have hKt_sq : K_tail ^ 2 = 4 * (S + 1) * C_jb * Qg := Real.sq_sqrt (by positivity)
          have hexp_sq : Real.exp (-(c ^ 2 / (128 * A))) ^ 2 = E_c := by
            dsimp [E_c, B]
            rw [← Real.exp_nat_mul]
            congr 1; push_cast; ring
          rw [mul_pow, hKt_sq, hexp_sq]
          ring
  have heLp_tail : eLpNorm D 2 (planeMeasure m) ≤
      ENNReal.ofReal (K_tail * Real.exp (-(c ^ 2 / (128 * A)))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
    calc (∫⁻ x, ‖D x‖ₑ ^ 2 ∂planeMeasure m) ^ (2 : ℝ)⁻¹
        ≤ (ENNReal.ofReal ((K_tail * Real.exp (-(c ^ 2 / (128 * A)))) ^ 2)) ^ (2 : ℝ)⁻¹ :=
          ENNReal.rpow_le_rpow hlint_total (by positivity)
      _ = ENNReal.ofReal (K_tail * Real.exp (-(c ^ 2 / (128 * A)))) := by
          have h0 : 0 ≤ K_tail * Real.exp (-(c ^ 2 / (128 * A))) := by positivity
          rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by positivity),
            ← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq h0]
  exact ⟨⟨haesm_cell, lt_of_le_of_lt heLp_norm ENNReal.ofReal_lt_top⟩, heLp_norm, heLp_tail⟩

end UnforcedLeray.Short.IIb.PeriodizedCylCoordAux
