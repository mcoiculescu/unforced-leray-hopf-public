import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1

/-!
# Part I, task `PartI:T02/1/4/4/1/8`: the abstract strong Duhamel formula

Target: `abstractStrongDuhamel : AbstractStrongDuhamel` (`Short/PartI/Sub/T02_1_4_4_1.lean`).
Source of record: `the November 2 reference manuscript`, lines 261-288.

Route.  Write `u s = j (v s)`, `g r = L (v r) - G r` and `F s = u s - u 0 - ∫_0^s g`.

1. Shift identity (`hstar` in the main proof): for `0 ≤ t < y ≤ T`,
   `u y = S (y - t) (u t) - ∫_t^y S (y - r) (G r) dr`.  It follows from the mild equation at `t`
   and `y`, the semigroup law and `∫_0^y = ∫_0^t + ∫_t^y`.
2. Right derivative of `u` at `t ∈ [0, T)`: `(y - t)⁻¹ • (u y - u t) → L (v t) - G t` as `y → t⁺`.
   The part `(y - t)⁻¹ • (S (y - t) (u t) - u t) → L (v t)` is the generator hypothesis at `v t`;
   the part `(y - t)⁻¹ • ∫_t^y S (y - r) (G r) dr → G t` is `asd_avg`.
3. `F` is continuous on `[0, T]` with right derivative `0` on `[0, T)`, so `F t = F 0 = 0`
   (`constant_of_has_deriv_right_zero`).

No Fubini and no dominated convergence are used.  Integrability of `r ↦ S (a - r) (G r)` comes from
continuity on `Iic a` (`asd_cont_on`), using the contraction bound for `θ ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

section AsdAux

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A contraction family: `‖S θ x‖ ≤ ‖x‖` for `θ ≥ 0`. -/
theorem asd_norm_le (S : ℝ → X →L[ℝ] X) (hS1 : ∀ θ : ℝ, 0 ≤ θ → ‖S θ‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (x : X) : ‖S θ x‖ ≤ ‖x‖ :=
  calc ‖S θ x‖ ≤ ‖S θ‖ * ‖x‖ := (S θ).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hS1 θ hθ) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- `r ↦ S (a - r) (G r)` is continuous on `Iic a`. -/
theorem asd_cont_on (S : ℝ → X →L[ℝ] X) (hS1 : ∀ θ : ℝ, 0 ≤ θ → ‖S θ‖ ≤ 1)
    (hScont : ∀ x : X, Continuous fun θ : ℝ => S θ x)
    (G : ℝ → X) (hG : Continuous G) (a : ℝ) :
    ContinuousOn (fun r : ℝ => S (a - r) (G r)) (Iic a) := by
  intro r₀ _
  have hψ : Continuous fun r : ℝ => S (a - r) (G r₀) :=
    (hScont (G r₀)).comp (continuous_const.sub continuous_id)
  have hG0 : Tendsto (fun r : ℝ => ‖G r - G r₀‖) (𝓝[Iic a] r₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((hG.tendsto r₀).mono_left nhdsWithin_le_nhds)
  have hψ0 : Tendsto (fun r : ℝ => ‖S (a - r) (G r₀) - S (a - r₀) (G r₀)‖)
      (𝓝[Iic a] r₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((hψ.tendsto r₀).mono_left nhdsWithin_le_nhds)
  have hsum := hG0.add hψ0
  rw [add_zero] at hsum
  refine tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hθ : 0 ≤ a - r := sub_nonneg.mpr (show r ≤ a from hr)
  calc ‖S (a - r) (G r) - S (a - r₀) (G r₀)‖
      = ‖S (a - r) (G r - G r₀) + (S (a - r) (G r₀) - S (a - r₀) (G r₀))‖ := by
        congr 1
        rw [map_sub]
        abel
    _ ≤ ‖S (a - r) (G r - G r₀)‖ + ‖S (a - r) (G r₀) - S (a - r₀) (G r₀)‖ :=
        norm_add_le _ _
    _ ≤ ‖G r - G r₀‖ + ‖S (a - r) (G r₀) - S (a - r₀) (G r₀)‖ :=
        add_le_add (asd_norm_le S hS1 hθ _) le_rfl

/-- Interval integrability of `r ↦ S (a - r) (G r)` on `[p, q]` when `q ≤ a`. -/
theorem asd_ii (S : ℝ → X →L[ℝ] X) (hS1 : ∀ θ : ℝ, 0 ≤ θ → ‖S θ‖ ≤ 1)
    (hScont : ∀ x : X, Continuous fun θ : ℝ => S θ x) (G : ℝ → X) (hG : Continuous G)
    (a p q : ℝ) (hpq : p ≤ q) (hqa : q ≤ a) :
    IntervalIntegrable (fun r : ℝ => S (a - r) (G r)) MeasureTheory.volume p q :=
  ContinuousOn.intervalIntegrable_of_Icc hpq
    ((asd_cont_on S hS1 hScont G hG a).mono fun _ hr => le_trans hr.2 hqa)

/-- The Duhamel average: `(y - t)⁻¹ • ∫_t^y S (y - r) (G r) dr → G t` as `y → t⁺`. -/
theorem asd_avg (S : ℝ → X →L[ℝ] X) (hS0 : S 0 = ContinuousLinearMap.id ℝ X)
    (hS1 : ∀ θ : ℝ, 0 ≤ θ → ‖S θ‖ ≤ 1)
    (hScont : ∀ x : X, Continuous fun θ : ℝ => S θ x)
    (G : ℝ → X) (hG : Continuous G) (t : ℝ) :
    Tendsto (fun y : ℝ => (y - t)⁻¹ • (∫ r in t..y, S (y - r) (G r))) (𝓝[>] t) (𝓝 (G t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨δ₁, hδ₁, hGδ⟩ := Metric.continuous_iff.mp hG t (ε / 4) hε4
  obtain ⟨δ₂, hδ₂, hφδ⟩ := Metric.continuous_iff.mp (hScont (G t)) 0 (ε / 4) hε4
  have hpos : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hm1 : min δ₁ δ₂ ≤ δ₁ := min_le_left δ₁ δ₂
  have hm2 : min δ₁ δ₂ ≤ δ₂ := min_le_right δ₁ δ₂
  filter_upwards [Ioo_mem_nhdsGT (show t < t + min δ₁ δ₂ by linarith)] with y hy
  obtain ⟨hty, hyt⟩ := hy
  have hbound : ∀ r ∈ Ioc t y, ‖S (y - r) (G r) - G t‖ ≤ ε / 2 := by
    intro r hr
    have hθ : 0 ≤ y - r := sub_nonneg.mpr hr.2
    have hGr : ‖G r - G t‖ < ε / 4 := by
      have h := hGδ r (by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1.le)]
        linarith [hr.2])
      rwa [dist_eq_norm] at h
    have hφr : ‖S (y - r) (G t) - G t‖ < ε / 4 := by
      have h := hφδ (y - r) (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hθ]
        linarith [hr.1])
      simpa only [hS0, ContinuousLinearMap.id_apply, dist_eq_norm] using h
    calc ‖S (y - r) (G r) - G t‖
        = ‖S (y - r) (G r - G t) + (S (y - r) (G t) - G t)‖ := by
          congr 1
          rw [map_sub]
          abel
      _ ≤ ‖S (y - r) (G r - G t)‖ + ‖S (y - r) (G t) - G t‖ := norm_add_le _ _
      _ ≤ ‖G r - G t‖ + ‖S (y - r) (G t) - G t‖ :=
          add_le_add (asd_norm_le S hS1 hθ _) le_rfl
      _ ≤ ε / 2 := by linarith
  have hII : IntervalIntegrable (fun r : ℝ => S (y - r) (G r)) MeasureTheory.volume t y :=
    asd_ii S hS1 hScont G hG y t y hty.le le_rfl
  have hsub : ∫ r in t..y, (S (y - r) (G r) - G t)
      = (∫ r in t..y, S (y - r) (G r)) - (y - t) • G t := by
    rw [intervalIntegral.integral_sub hII intervalIntegrable_const,
      intervalIntegral.integral_const]
  have hint : ‖∫ r in t..y, (S (y - r) (G r) - G t)‖ ≤ ε / 2 * |y - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun r hr => hbound r (by rwa [Set.uIoc_of_le hty.le] at hr))
  have hpos' : 0 < y - t := sub_pos.mpr hty
  have hne : y - t ≠ 0 := hpos'.ne'
  have heq : (y - t)⁻¹ • (∫ r in t..y, S (y - r) (G r)) - G t
      = (y - t)⁻¹ • ∫ r in t..y, (S (y - r) (G r) - G t) := by
    rw [hsub, smul_sub, inv_smul_smul₀ hne (G t)]
  simp only [dist_eq_norm]
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos'.le)]
  calc (y - t)⁻¹ * ‖∫ r in t..y, (S (y - r) (G r) - G t)‖
      ≤ (y - t)⁻¹ * (ε / 2 * |y - t|) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpos'.le)
    _ = ε / 2 := by
        rw [abs_of_pos hpos', mul_comm (ε / 2), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ < ε := by linarith

end AsdAux

/-- **Abstract strong Duhamel** (source lines 261-288, semigroup theory). -/
theorem abstractStrongDuhamel : AbstractStrongDuhamel := by
  intro X Y _ _ _ _ _ _ j L S hS1 hS0 hSsg hScont hgen T hT G v hG hv hmild
  -- the right derivative of `u = j ∘ v` on `[0, T)`
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => j (v s)) (L (v t) - G t) (Ici t) t := by
    intro t ht
    refine HasDerivWithinAt.Ici_of_Ioi ?_
    rw [hasDerivWithinAt_iff_tendsto_slope' (show t ∉ Ioi t from lt_irrefl t)]
    have hc : Continuous fun y : ℝ => y - t := continuous_id.sub continuous_const
    have hshift : Tendsto (fun y : ℝ => y - t) (𝓝[>] t) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using (hc.tendsto t).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_pos.mpr (show t < y from hy)
    have hA : Tendsto (fun y : ℝ => (y - t)⁻¹ • (S (y - t) (j (v t)) - j (v t)))
        (𝓝[>] t) (𝓝 (L (v t))) :=
      (hgen (v t)).comp hshift
    have hB := asd_avg S hS0 hS1 hScont G hG t
    refine (hA.sub hB).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht.2] with y hy
    have hty : t < y := hy.1
    have hyT : y < T := hy.2
    have hy0 : 0 ≤ y := le_trans ht.1 hty.le
    have hcomp1 : S (y - t) (S t (j (v 0))) = S y (j (v 0)) := by
      have h := congrArg (fun A : X →L[ℝ] X => A (j (v 0)))
        (hSsg (y - t) t (sub_nonneg.mpr hty.le) ht.1)
      simpa only [ContinuousLinearMap.comp_apply, sub_add_cancel] using h
    have hi_t : IntervalIntegrable (fun r : ℝ => S (t - r) (G r)) MeasureTheory.volume 0 t :=
      asd_ii S hS1 hScont G hG t 0 t ht.1 le_rfl
    have hcomp2 : S (y - t) (∫ r in (0 : ℝ)..t, S (t - r) (G r))
        = ∫ r in (0 : ℝ)..t, S (y - r) (G r) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm (S (y - t)) hi_t]
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le ht.1] at hr
      have h := congrArg (fun A : X →L[ℝ] X => A (G r))
        (hSsg (y - t) (t - r) (sub_nonneg.mpr hty.le) (sub_nonneg.mpr hr.2))
      simp only [ContinuousLinearMap.comp_apply, show y - t + (t - r) = y - r by ring] at h
      exact h
    have h1 : IntervalIntegrable (fun r : ℝ => S (y - r) (G r)) MeasureTheory.volume 0 t :=
      asd_ii S hS1 hScont G hG y 0 t ht.1 hty.le
    have h2 : IntervalIntegrable (fun r : ℝ => S (y - r) (G r)) MeasureTheory.volume t y :=
      asd_ii S hS1 hScont G hG y t y hty.le le_rfl
    have hsplit : ∫ r in (0 : ℝ)..y, S (y - r) (G r)
        = (∫ r in (0 : ℝ)..t, S (y - r) (G r)) + ∫ r in t..y, S (y - r) (G r) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    have htI : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hyI : y ∈ Icc (0 : ℝ) T := ⟨hy0, hyT.le⟩
    have hA1 : S (y - t) (j (v t)) = S y (j (v 0)) - ∫ r in (0 : ℝ)..t, S (y - r) (G r) := by
      rw [hmild t htI, map_sub, hcomp1, hcomp2]
    have hstar : j (v y) = S (y - t) (j (v t)) - ∫ r in t..y, S (y - r) (G r) := by
      rw [hA1, hmild y hyI, hsplit]
      abel
    simp only [slope_def_module, hstar, smul_sub]
    abel
  -- the Duhamel integral of `g = L ∘ v - G`, its derivative, and `F`
  have hgc : Continuous fun r : ℝ => L (v r) - G r := (L.continuous.comp hv).sub hG
  have hI : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => ∫ r in (0 : ℝ)..s', (L (v r) - G r))
      (L (v s) - G s) s :=
    fun s => (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hIc : Continuous fun s' : ℝ => ∫ r in (0 : ℝ)..s', (L (v r) - G r) :=
    continuous_iff_continuousAt.mpr fun s => (hI s).continuousAt
  have hFc : Continuous fun s : ℝ => j (v s) - j (v 0) - ∫ r in (0 : ℝ)..s, (L (v r) - G r) :=
    ((j.continuous.comp hv).sub continuous_const).sub hIc
  have hFder : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => j (v s) - j (v 0) - ∫ r in (0 : ℝ)..s, (L (v r) - G r))
        0 (Ici t) t := by
    intro t ht
    have h3 := ((hderiv t ht).sub_const (j (v 0))).sub (hI t).hasDerivWithinAt
    exact h3.congr_deriv (sub_self _)
  intro t ht
  have h := constant_of_has_deriv_right_zero (hFc.continuousOn (s := Icc (0 : ℝ) T)) hFder t ht
  simp only [intervalIntegral.integral_same, sub_self] at h
  rw [sub_eq_zero] at h
  rw [← h]
  abel

end UnforcedLeray.Short.PartI
