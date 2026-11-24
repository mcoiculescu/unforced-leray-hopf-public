import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2

/-!
# `PartIII-b:C/ward/13/8/2/2/1`: Poincare inequality on a compact convex set

Proof of `convexPoincare` (source 117-118, 2641-2642). Route:

* segment formula and Cauchy-Schwarz: `(p x - p y)^2 <= D^2 * int_0^1 |grad p (y + t (x - y))|^2 dt`
  for `|x - y| <= D`;
* affine change of variables `z = a + s x` (Jacobian `s^3`), with `s >= 1/2` or `1 - s >= 1/2`
  (the two cases use the symmetry of `K x K`), gives
  `int_K int_K int_0^1 |grad p|^2(y + t(x-y)) <= 8 vol(K) int_K |grad p|^2`;
* the mean `m = (int_K p)/vol(K)` satisfies `(p x - m)^2 <= vol(K)^{-1} int_K (p x - p y)^2 dy`.

Constant: `C = 8 (2 R0)^2` where `K subset closedBall 0 R0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP

abbrev Sp := UnforcedLeray.Space

theorem fderiv_apply_eq_inner_physGrad (q : Sp → ℝ) (z v : Sp) :
    fderiv ℝ q z v = inner ℝ (physGrad q z) v := by
  have hv : v = ∑ j : Fin 3, v j • UnforcedLeray.coordinateVector j := by
    ext i
    simp [UnforcedLeray.coordinateVector, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, PiLp.inner_apply, physGrad, RCLike.inner_apply,
    conj_trivial]

theorem continuous_physGrad {p : Sp → ℝ} (hp : ContDiff ℝ 1 p) : Continuous (physGrad p) := by
  have hfd : Continuous (fderiv ℝ p) := hp.continuous_fderiv one_ne_zero
  unfold physGrad
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => hfd.clm_apply continuous_const)

/-- Segment bound: `(p x - p y)^2 <= D^2 int_0^1 |grad p (y + t(x-y))|^2 dt` when `|x-y| <= D`. -/
theorem seg_bound {p : Sp → ℝ} (hp : ContDiff ℝ 1 p) (x y : Sp) (D : ℝ)
    (hD : ‖x - y‖ ≤ D) :
    (p x - p y) ^ 2 ≤ D ^ 2 * ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2 := by
  have hfd : Continuous (fderiv ℝ p) := hp.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ p := hp.differentiable one_ne_zero
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
  have hderiv : ∀ t ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => p (y + t • (x - y))) (fderiv ℝ p (y + t • (x - y)) (x - y)) t :=
    fun t _ => (hdiff (y + t • (x - y))).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hfc : Continuous fun t : ℝ => fderiv ℝ p (y + t • (x - y)) (x - y) :=
    (hfd.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hGc : Continuous fun t : ℝ => ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
    ((continuous_physGrad hp).comp
      (continuous_const.add (continuous_id.smul continuous_const))).norm.pow 2
  have hFTC : ∫ t in (0:ℝ)..1, fderiv ℝ p (y + t • (x - y)) (x - y) = p x - p y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hfc.intervalIntegrable _ _)]
    simp
  have hsq : (∫ t in (0:ℝ)..1, fderiv ℝ p (y + t • (x - y)) (x - y)) ^ 2 ≤
      ∫ t in (0:ℝ)..1, fderiv ℝ p (y + t • (x - y)) (x - y) ^ 2 := by
    set c := ∫ t in (0:ℝ)..1, fderiv ℝ p (y + t • (x - y)) (x - y) with hc
    have i1 : IntervalIntegrable (fun t : ℝ => fderiv ℝ p (y + t • (x - y)) (x - y) ^ 2)
        volume 0 1 := (hfc.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t : ℝ => 2 * c * fderiv ℝ p (y + t • (x - y)) (x - y))
        volume 0 1 := (continuous_const.mul hfc).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 1 := intervalIntegrable_const
    have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (fderiv ℝ p (y + t • (x - y)) (x - y) - c) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have hrw : ∀ t : ℝ, (fderiv ℝ p (y + t • (x - y)) (x - y) - c) ^ 2 =
        (fderiv ℝ p (y + t • (x - y)) (x - y) ^ 2 - 2 * c * fderiv ℝ p (y + t • (x - y)) (x - y))
          + c ^ 2 := fun t => by ring
    simp only [hrw] at h0
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h0
    simp only [sub_zero, smul_eq_mul, one_mul] at h0
    nlinarith [h0]
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, fderiv ℝ p (y + t • (x - y)) (x - y) ^ 2 ≤
      D ^ 2 * ‖physGrad p (y + t • (x - y))‖ ^ 2 := by
    intro t _
    have hi : fderiv ℝ p (y + t • (x - y)) (x - y) =
        inner ℝ (physGrad p (y + t • (x - y))) (x - y) :=
      fderiv_apply_eq_inner_physGrad p _ _
    have hcs := abs_real_inner_le_norm (physGrad p (y + t • (x - y))) (x - y)
    have h2 : |fderiv ℝ p (y + t • (x - y)) (x - y)| ≤
        ‖physGrad p (y + t • (x - y))‖ * D := by
      rw [hi]
      exact hcs.trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))
    calc fderiv ℝ p (y + t • (x - y)) (x - y) ^ 2
        = |fderiv ℝ p (y + t • (x - y)) (x - y)| ^ 2 := (sq_abs _).symm
      _ ≤ (‖physGrad p (y + t • (x - y))‖ * D) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = D ^ 2 * ‖physGrad p (y + t • (x - y))‖ ^ 2 := by ring
  have hI : ∫ t in (0:ℝ)..1, fderiv ℝ p (y + t • (x - y)) (x - y) ^ 2 ≤
      ∫ t in (0:ℝ)..1, D ^ 2 * ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one ((hfc.pow 2).intervalIntegrable _ _)
      ((continuous_const.mul hGc).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const_mul] at hI
  rw [← hFTC]
  linarith [hsq, hI]

/-- Affine change of variables on a compact set: `int_K g(a + s x) <= s^{-3} int_K g`. -/
theorem affine_setIntegral_le {K : Set Sp} (hKc : IsCompact K) (g : Sp → ℝ) (hg : Continuous g)
    (hg0 : ∀ z, 0 ≤ g z) (a : Sp) {s : ℝ} (hs : 0 < s) (ha : ∀ x ∈ K, a + s • x ∈ K) :
    ∫ x in K, g (a + s • x) ≤ (s ^ 3)⁻¹ * ∫ z in K, g z := by
  have hinj : Set.InjOn (fun x : Sp => a + s • x) K := by
    intro x _ y _ hxy
    exact smul_right_injective Sp hs.ne' (add_left_cancel hxy)
  have hd : ∀ x ∈ K, HasFDerivWithinAt (fun x : Sp => a + s • x)
      (s • ContinuousLinearMap.id ℝ Sp) K x := fun x _ =>
    (((hasFDerivAt_id x).const_smul s).const_add a).hasFDerivWithinAt
  have key := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    hKc.measurableSet hd hinj g
  have hdet : (s • ContinuousLinearMap.id ℝ Sp : Sp →L[ℝ] Sp).det = s ^ 3 := by
    have h1 : ((s • ContinuousLinearMap.id ℝ Sp : Sp →L[ℝ] Sp) : Sp →ₗ[ℝ] Sp) =
        s • LinearMap.id := by
      ext v
      simp
    show LinearMap.det ((s • ContinuousLinearMap.id ℝ Sp : Sp →L[ℝ] Sp) : Sp →ₗ[ℝ] Sp) = s ^ 3
    rw [h1, LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin]
    simp
  simp only [hdet, abs_of_pos (pow_pos hs 3), smul_eq_mul] at key
  rw [integral_const_mul] at key
  have hsub : ∫ z in (fun x : Sp => a + s • x) '' K, g z ≤ ∫ z in K, g z := by
    apply setIntegral_mono_set (hg.continuousOn.integrableOn_compact hKc)
    · exact Filter.Eventually.of_forall fun z => hg0 z
    · refine Filter.Eventually.of_forall fun z hz => ?_
      obtain ⟨x, hx, rfl⟩ := hz
      exact ha x hx
  have hpos : 0 < s ^ 3 := pow_pos hs 3
  have hI : s ^ 3 * ∫ x in K, g (a + s • x) ≤ ∫ z in K, g z := by
    rw [← key]
    exact hsub
  calc ∫ x in K, g (a + s • x) = (s ^ 3)⁻¹ * (s ^ 3 * ∫ x in K, g (a + s • x)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ (s ^ 3)⁻¹ * ∫ z in K, g z := mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hpos.le)

/-- A set integral of a function bounded above by a constant on a compact set. -/
theorem setIntegral_le_volume_mul {K : Set Sp} (hKc : IsCompact K) (F : Sp → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ y ∈ K, F y ≤ c) :
    ∫ y in K, F y ≤ volume.real K * c := by
  by_cases hF : IntegrableOn F K volume
  · calc ∫ y in K, F y ≤ ∫ y in K, c :=
          setIntegral_mono_on hF (integrableOn_const (C := c) hKc.measure_lt_top.ne)
            hKc.measurableSet h
      _ = volume.real K * c := by rw [setIntegral_const, smul_eq_mul]
  · rw [integral_undef hF]
    exact mul_nonneg measureReal_nonneg hc

theorem integrable_uncurry_real {f : ℝ → Sp → ℝ} (hf : Continuous (Function.uncurry f))
    (K : Set Sp) (hK : IsCompact K) (a b : ℝ) :
    Integrable (Function.uncurry f) ((volume.restrict (uIoc a b)).prod (volume.restrict K)) := by
  rw [Measure.prod_restrict]
  have hc : IntegrableOn (Function.uncurry f) (uIcc a b ×ˢ K) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod hK)
  exact hc.mono_set (prod_mono uIoc_subset_uIcc Subset.rfl)

theorem integrable_uncurry_sp {f : Sp → Sp → ℝ} (hf : Continuous (Function.uncurry f))
    (K : Set Sp) (hK : IsCompact K) :
    Integrable (Function.uncurry f) ((volume.restrict K).prod (volume.restrict K)) := by
  rw [Measure.prod_restrict]
  exact hf.continuousOn.integrableOn_compact (hK.prod hK)

/-- The triple integral bound: `int_K int_K int_0^1 g(y + t(x-y)) <= 8 vol(K) int_K g`. -/
theorem key_bound {K : Set Sp} (hK : Convex ℝ K) (hKc : IsCompact K) (g : Sp → ℝ)
    (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫ x in K, ∫ y in K, ∫ t in (0:ℝ)..1, g (y + t • (x - y)) ≤
      8 * volume.real K * ∫ z in K, g z := by
  have hKm : MeasurableSet K := hKc.measurableSet
  have hgnn : 0 ≤ ∫ z in K, g z := setIntegral_nonneg hKm fun z _ => hg0 z
  have hc3 : Continuous fun q : ℝ × Sp × Sp => g (q.2.2 + q.1 • (q.2.1 - q.2.2)) :=
    hg.comp (by fun_prop)
  -- step 1: for each x, exchange the y-set integral with the t-interval integral
  have h1 : ∀ x : Sp, ∫ y in K, ∫ t in (0:ℝ)..1, g (y + t • (x - y)) =
      ∫ t in (0:ℝ)..1, ∫ y in K, g (y + t • (x - y)) := by
    intro x
    have hcx : Continuous (Function.uncurry fun (t : ℝ) (y : Sp) => g (y + t • (x - y))) :=
      hc3.comp (by fun_prop : Continuous fun q : ℝ × Sp => (q.1, x, q.2))
    exact (intervalIntegral_integral_swap (integrable_uncurry_real hcx K hKc 0 1)).symm
  -- joint continuity of the y-integral
  have hΨc : Continuous (Function.uncurry fun (t : ℝ) (x : Sp) =>
      ∫ y in K, g (y + t • (x - y))) := by
    have hq : Continuous fun q : (ℝ × Sp) × Sp => g (q.2 + q.1.1 • (q.1.2 - q.2)) :=
      hg.comp (by fun_prop)
    exact continuous_parametric_integral_of_continuous
      (f := fun (q : ℝ × Sp) (y : Sp) => g (y + q.1 • (q.2 - y))) hq hKc
  -- step 2: exchange the x-set integral with the t-interval integral
  have h2 : ∫ x in K, ∫ t in (0:ℝ)..1, ∫ y in K, g (y + t • (x - y)) =
      ∫ t in (0:ℝ)..1, ∫ x in K, ∫ y in K, g (y + t • (x - y)) :=
    (intervalIntegral_integral_swap
      (integrable_uncurry_real (f := fun (t : ℝ) (x : Sp) => ∫ y in K, g (y + t • (x - y)))
        hΨc K hKc 0 1)).symm
  have hW : ∫ x in K, ∫ y in K, ∫ t in (0:ℝ)..1, g (y + t • (x - y)) =
      ∫ t in (0:ℝ)..1, ∫ x in K, ∫ y in K, g (y + t • (x - y)) := by
    simp only [h1]
    exact h2
  have hA : Continuous fun t : ℝ => ∫ x in K, ∫ y in K, g (y + t • (x - y)) :=
    continuous_parametric_integral_of_continuous
      (f := fun (t : ℝ) (x : Sp) => ∫ y in K, g (y + t • (x - y))) hΨc hKc
  have hbound : ∀ t ∈ Icc (0:ℝ) 1, ∫ x in K, ∫ y in K, g (y + t • (x - y)) ≤
      8 * volume.real K * ∫ z in K, g z := by
    intro t ht
    rcases le_total t (1/2) with htl | htl
    · -- `t <= 1/2`: integrate over y for fixed x, with factor `(1-t)^3 >= 1/8`
      have hs0 : (0:ℝ) < 1 - t := by linarith [ht.2]
      have hs8 : ((1 - t) ^ 3)⁻¹ ≤ 8 := by
        rw [inv_le_comm₀ (pow_pos hs0 3) (by norm_num)]
        have h12 : (1/2 : ℝ) ≤ 1 - t := by linarith
        have := pow_le_pow_left₀ (by norm_num) h12 3
        norm_num at this ⊢
        linarith
      have hx : ∀ x ∈ K, ∫ y in K, g (y + t • (x - y)) ≤ 8 * ∫ z in K, g z := by
        intro x hxK
        have hrw : ∀ y : Sp, y + t • (x - y) = (x - (1 - t) • x) + (1 - t) • y :=
          fun y => by module
        have hmem : ∀ y ∈ K, (x - (1 - t) • x) + (1 - t) • y ∈ K := by
          intro y hy
          have e : (x - (1 - t) • x) + (1 - t) • y = x + (1 - t) • (y - x) := by module
          rw [e]
          exact hK.add_smul_sub_mem hxK hy ⟨hs0.le, by linarith [ht.1]⟩
        simp only [hrw]
        calc ∫ y in K, g ((x - (1 - t) • x) + (1 - t) • y)
            ≤ ((1 - t) ^ 3)⁻¹ * ∫ z in K, g z :=
              affine_setIntegral_le hKc g hg hg0 _ hs0 hmem
          _ ≤ 8 * ∫ z in K, g z := mul_le_mul_of_nonneg_right hs8 hgnn
      calc ∫ x in K, ∫ y in K, g (y + t • (x - y)) ≤ volume.real K * (8 * ∫ z in K, g z) :=
            setIntegral_le_volume_mul hKc _ _ (by linarith) hx
        _ = 8 * volume.real K * ∫ z in K, g z := by ring
    · -- `t >= 1/2`: exchange the two set integrals, then integrate over x for fixed y
      have ht0 : 0 < t := by linarith
      have hcont : Continuous (fun q : Sp × Sp => g (q.2 + t • (q.1 - q.2))) :=
        hg.comp (by fun_prop)
      have hswap : ∫ x in K, ∫ y in K, g (y + t • (x - y)) =
          ∫ y in K, ∫ x in K, g (y + t • (x - y)) :=
        integral_integral_swap (integrable_uncurry_sp (f := fun x y => g (y + t • (x - y)))
          hcont K hKc)
      rw [hswap]
      have hinner : ∀ y ∈ K, ∫ x in K, g (y + t • (x - y)) ≤ 8 * ∫ z in K, g z := by
        intro y hy
        have hrw : ∀ x : Sp, y + t • (x - y) = (y - t • y) + t • x :=
          fun x => by module
        simp only [hrw]
        have hmem : ∀ x ∈ K, (y - t • y) + t • x ∈ K := by
          intro x hx
          have e : (y - t • y) + t • x = y + t • (x - y) := by module
          rw [e]
          exact hK.add_smul_sub_mem hy hx ⟨ht0.le, ht.2⟩
        calc ∫ x in K, g ((y - t • y) + t • x) ≤ (t ^ 3)⁻¹ * ∫ z in K, g z :=
              affine_setIntegral_le hKc g hg hg0 _ ht0 hmem
          _ ≤ 8 * ∫ z in K, g z := by
              apply mul_le_mul_of_nonneg_right _ hgnn
              rw [inv_le_comm₀ (pow_pos ht0 3) (by norm_num)]
              have h12 : (1/2 : ℝ) ≤ t := htl
              have := pow_le_pow_left₀ (by norm_num) h12 3
              norm_num at this ⊢
              linarith
      calc ∫ y in K, ∫ x in K, g (y + t • (x - y)) ≤ volume.real K * (8 * ∫ z in K, g z) :=
            setIntegral_le_volume_mul hKc _ _ (by linarith) hinner
        _ = 8 * volume.real K * ∫ z in K, g z := by ring
  rw [hW]
  have := intervalIntegral.integral_mono_on zero_le_one
    (hA.intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 8 * volume.real K * ∫ z in K, g z) volume 0 1) hbound
  simpa using this

end UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.CP in
/-- **Poincare inequality on a compact convex set of positive volume** (constant depends on `K`). -/
theorem convexPoincare : UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.ConvexPoincare := by
  intro K hK hKc hV
  obtain ⟨R0, hR0⟩ := hKc.isBounded.subset_closedBall (0 : Sp)
  have hVr : 0 < volume.real K := by rw [measureReal_def]; exact hV
  have hKm : MeasurableSet K := hKc.measurableSet
  refine ⟨8 * (2 * R0) ^ 2, fun p hp => ?_⟩
  have hpc : Continuous p := hp.continuous
  have hgc : Continuous fun z : Sp => ‖physGrad p z‖ ^ 2 := ((continuous_physGrad hp).norm).pow 2
  have hdist : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 2 * R0 := by
    intro x hx y hy
    have hx' : ‖x‖ ≤ R0 := by simpa using hR0 hx
    have hy' : ‖y‖ ≤ R0 := by simpa using hR0 hy
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * R0 := by linarith
  refine ⟨(∫ y in K, p y) / volume.real K, ?_⟩
  have hI1 : IntegrableOn (fun y => p y ^ 2) K volume :=
    (hpc.pow 2).continuousOn.integrableOn_compact hKc
  have hI2 : IntegrableOn (fun y => p y) K volume := hpc.continuousOn.integrableOn_compact hKc
  -- expansion of the square about a constant
  have hexp : ∀ c : ℝ, ∫ y in K, (p y - c) ^ 2 =
      (∫ y in K, p y ^ 2) - 2 * c * (∫ y in K, p y) + c ^ 2 * volume.real K := by
    intro c
    have e : ∀ y, (p y - c) ^ 2 = p y ^ 2 + (-(2 * c)) * p y + c ^ 2 := fun y => by ring
    simp only [e]
    have hA1 : IntegrableOn (fun y => p y ^ 2 + (-(2 * c)) * p y) K volume :=
      hI1.add (hI2.const_mul _)
    have hA2 : IntegrableOn (fun _ : Sp => c ^ 2) K volume :=
      integrableOn_const (C := c ^ 2) hKc.measure_lt_top.ne
    rw [integral_add hA1 hA2, integral_add hI1 (hI2.const_mul _), integral_const_mul,
      setIntegral_const, smul_eq_mul]
    ring
  -- the mean satisfies `P^2 <= S V`
  have hPS : (∫ y in K, p y) ^ 2 ≤ (∫ y in K, p y ^ 2) * volume.real K := by
    have h0 : 0 ≤ ∫ y in K, (p y - (∫ y in K, p y) / volume.real K) ^ 2 :=
      setIntegral_nonneg hKm fun y _ => sq_nonneg _
    rw [hexp] at h0
    have hVne : volume.real K ≠ 0 := hVr.ne'
    have h3 : ((∫ y in K, p y) / volume.real K) ^ 2 * volume.real K =
        ((∫ y in K, p y) / volume.real K) * (∫ y in K, p y) := by
      field_simp
    have h2 : ((∫ y in K, p y) / volume.real K) * (∫ y in K, p y) ≤ ∫ y in K, p y ^ 2 := by
      nlinarith [h0, h3]
    have h4 : ((∫ y in K, p y) / volume.real K) * (∫ y in K, p y) * volume.real K =
        (∫ y in K, p y) ^ 2 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hVr.le, h4]
  -- pointwise variance bound
  have hpt : ∀ x ∈ K, (p x - (∫ y in K, p y) / volume.real K) ^ 2 ≤
      (volume.real K)⁻¹ * ∫ y in K, (p x - p y) ^ 2 := by
    intro x _
    have e2 : ∫ y in K, (p x - p y) ^ 2 =
        (∫ y in K, p y ^ 2) - 2 * p x * (∫ y in K, p y) + p x ^ 2 * volume.real K := by
      have : ∀ y, (p x - p y) ^ 2 = (p y - p x) ^ 2 := fun y => by ring
      simp only [this]
      exact hexp (p x)
    rw [e2]
    have hq : ((∫ y in K, p y) / volume.real K) ^ 2 ≤
        (∫ y in K, p y ^ 2) / volume.real K := by
      rw [div_pow, div_le_div_iff₀ (pow_pos hVr 2) hVr]
      nlinarith [mul_le_mul_of_nonneg_right hPS hVr.le]
    have eR : (volume.real K)⁻¹ * ((∫ y in K, p y ^ 2) - 2 * p x * (∫ y in K, p y) +
        p x ^ 2 * volume.real K) =
        (∫ y in K, p y ^ 2) / volume.real K - 2 * p x * (∫ y in K, p y) / volume.real K
          + p x ^ 2 := by
      field_simp
    rw [eR]
    have eL : (p x - (∫ y in K, p y) / volume.real K) ^ 2 =
        p x ^ 2 - 2 * p x * (∫ y in K, p y) / volume.real K
          + ((∫ y in K, p y) / volume.real K) ^ 2 := by
      ring
    rw [eL]
    linarith [hq]
  have hcontInner : Continuous fun x : Sp => ∫ y in K, (p x - p y) ^ 2 :=
    continuous_parametric_integral_of_continuous
      (f := fun (x y : Sp) => (p x - p y) ^ 2)
      (show Continuous fun q : Sp × Sp => (p q.1 - p q.2) ^ 2 from
        ((hpc.comp continuous_fst).sub (hpc.comp continuous_snd)).pow 2) hKc
  have hint1 : ∫ x in K, (p x - (∫ y in K, p y) / volume.real K) ^ 2 ≤
      (volume.real K)⁻¹ * ∫ x in K, ∫ y in K, (p x - p y) ^ 2 := by
    calc ∫ x in K, (p x - (∫ y in K, p y) / volume.real K) ^ 2
        ≤ ∫ x in K, (volume.real K)⁻¹ * ∫ y in K, (p x - p y) ^ 2 :=
          setIntegral_mono_on
            ((((hpc.sub continuous_const).pow 2)).continuousOn.integrableOn_compact hKc)
            ((hcontInner.const_mul _).continuousOn.integrableOn_compact hKc) hKm hpt
      _ = (volume.real K)⁻¹ * ∫ x in K, ∫ y in K, (p x - p y) ^ 2 := integral_const_mul _ _
  -- segment bound, integrated over K x K
  have hin : ∀ x ∈ K, ∫ y in K, (p x - p y) ^ 2 ≤
      (2 * R0) ^ 2 * ∫ y in K, ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2 := by
    intro x hx
    have hGy : Continuous (Function.uncurry fun (y : Sp) (t : ℝ) =>
        ‖physGrad p (y + t • (x - y))‖ ^ 2) := by
      have hc : Continuous fun z : Sp × ℝ => physGrad p (z.1 + z.2 • (x - z.1)) :=
        (continuous_physGrad hp).comp (by fun_prop)
      exact hc.norm.pow 2
    have hcontT : Continuous fun y : Sp => ∫ t in (0:ℝ)..1,
        ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (y : Sp) (t : ℝ) => ‖physGrad p (y + t • (x - y))‖ ^ 2) hGy 0 1
    calc ∫ y in K, (p x - p y) ^ 2
        ≤ ∫ y in K, (2 * R0) ^ 2 * ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
          setIntegral_mono_on
            (((continuous_const.sub hpc).pow 2).continuousOn.integrableOn_compact hKc)
            ((hcontT.const_mul _).continuousOn.integrableOn_compact hKc) hKm
            (fun y hy => seg_bound hp x y (2 * R0) (hdist x hx y hy))
      _ = (2 * R0) ^ 2 * ∫ y in K, ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
          integral_const_mul _ _
  have hGq : Continuous (Function.uncurry fun (q : Sp × Sp) (t : ℝ) =>
      ‖physGrad p (q.2 + t • (q.1 - q.2))‖ ^ 2) := by
    have hc : Continuous fun z : (Sp × Sp) × ℝ => physGrad p (z.1.2 + z.2 • (z.1.1 - z.1.2)) :=
      (continuous_physGrad hp).comp (by fun_prop)
    exact hc.norm.pow 2
  have hF2 : Continuous (Function.uncurry fun (x y : Sp) =>
      ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : Sp × Sp) (t : ℝ) => ‖physGrad p (q.2 + t • (q.1 - q.2))‖ ^ 2) hGq 0 1
  have hcontX : Continuous fun x : Sp => ∫ y in K, ∫ t in (0:ℝ)..1,
      ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
    continuous_parametric_integral_of_continuous
      (f := fun (x y : Sp) => ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2) hF2 hKc
  have hint2 : ∫ x in K, ∫ y in K, (p x - p y) ^ 2 ≤
      (2 * R0) ^ 2 * ∫ x in K, ∫ y in K, ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2 := by
    calc ∫ x in K, ∫ y in K, (p x - p y) ^ 2
        ≤ ∫ x in K, (2 * R0) ^ 2 * ∫ y in K, ∫ t in (0:ℝ)..1,
            ‖physGrad p (y + t • (x - y))‖ ^ 2 :=
          setIntegral_mono_on (hcontInner.continuousOn.integrableOn_compact hKc)
            ((hcontX.const_mul _).continuousOn.integrableOn_compact hKc) hKm hin
      _ = (2 * R0) ^ 2 * ∫ x in K, ∫ y in K, ∫ t in (0:ℝ)..1,
            ‖physGrad p (y + t • (x - y))‖ ^ 2 := integral_const_mul _ _
  have hW := key_bound hK hKc (fun z : Sp => ‖physGrad p z‖ ^ 2) hgc (fun z => sq_nonneg _)
  have hV0 : 0 ≤ (volume.real K)⁻¹ := inv_nonneg.2 hVr.le
  calc ∫ y in K, (p y - (∫ y in K, p y) / volume.real K) ^ 2
      ≤ (volume.real K)⁻¹ * ∫ x in K, ∫ y in K, (p x - p y) ^ 2 := hint1
    _ ≤ (volume.real K)⁻¹ * ((2 * R0) ^ 2 * ∫ x in K, ∫ y in K,
          ∫ t in (0:ℝ)..1, ‖physGrad p (y + t • (x - y))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hint2 hV0
    _ ≤ (volume.real K)⁻¹ * ((2 * R0) ^ 2 * (8 * volume.real K * ∫ y in K, ‖physGrad p y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (by positivity)) hV0
    _ = 8 * (2 * R0) ^ 2 * ∫ y in K, ‖physGrad p y‖ ^ 2 := by
          field_simp
