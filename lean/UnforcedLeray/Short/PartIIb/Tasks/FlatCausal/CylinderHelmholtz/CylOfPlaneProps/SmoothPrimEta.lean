import UnforcedLeray.Short.PartIIb.Sub.T12_1_5

/-!
# Part II-b, leaf `PartII-b:T12/1/5/5` (`SmoothPrimEta`): smooth primitive in the last variable

Source of record: `the November 2 reference manuscript` lines 1727-1731 (the
primitives of the zero-frequency components). The target is `SmoothPrimEta` of `Sub/T12_1_5.lean`.

Proof. Substituting `s = -L + t (η + L)` gives
`∫_{-L}^{η} g(q, s) ds = (η + L) ∫_0^1 g(q, -L + t (η + L)) dt` (`spe_subst`). The integrand
`Φ(z, t) = (η + L) g(q, -L + t (η + L))` has `z`-derivative `D1 • fst + D2 • snd` with
`D1 = (η + L) ∂_q g` and `D2 = g + t (η + L) ∂_η g` (`spe_pt_hasFDerivAt`). Differentiation under
the integral over the compact `t`-interval gives the `HasFDerivAt` (`spe_param_hasFDerivAt`); the
two coefficients are identified by the substitution (for `D1`) and the fundamental theorem of
calculus in `t` (for `D2`) (`spe_integral_F`). Smoothness is by induction on the order: the
derivative is again a primitive of the same form, with `g` replaced by `∂_q g`
(`spe_contDiff_nat`). The vanishing hypothesis of `SmoothPrimEta` is not used.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- Substitution `s = -L + t (η + L)` on the interval `[-L, η]`. -/
theorem spe_subst (f : ℝ → ℝ) (L η : ℝ) :
    ∫ s in (-L)..η, f s = (η + L) * ∫ t in (0:ℝ)..1, f (-L + t * (η + L)) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (f := f) (a := (0:ℝ)) (b := 1)
    (η + L) (-L)
  have e1 : (η + L) * 0 + -L = -L := by ring
  have e2 : (η + L) * 1 + -L = η := by ring
  rw [e1, e2, smul_eq_mul] at h
  rw [← h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  show f ((η + L) * t + -L) = f (-L + t * (η + L))
  congr 1
  ring

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on `(1,0)` and `(0,1)`. -/
theorem spe_key (A : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    A v = v.1 * A (1, 0) + v.2 * A (0, 1) := by
  have h : A v = A (v.1 • ((1:ℝ), (0:ℝ)) + v.2 • ((0:ℝ), (1:ℝ))) := by
    congr 1
    ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `q`-coefficient of the `z`-derivative of `Φ(z, t) = (η + L) g(q, -L + t (η + L))`. -/
noncomputable def spe_D1 (g : ℝ × ℝ → ℝ) (L : ℝ) (x : ℝ × ℝ) (t : ℝ) : ℝ :=
  (x.2 + L) * fderiv ℝ g (x.1, -L + t * (x.2 + L)) (1, 0)

/-- `η`-coefficient of the `z`-derivative of `Φ(z, t) = (η + L) g(q, -L + t (η + L))`. -/
noncomputable def spe_D2 (g : ℝ × ℝ → ℝ) (L : ℝ) (x : ℝ × ℝ) (t : ℝ) : ℝ :=
  g (x.1, -L + t * (x.2 + L)) + t * (x.2 + L) * fderiv ℝ g (x.1, -L + t * (x.2 + L)) (0, 1)

/-- The `z`-derivative of `Φ(·, t)` at `x`. -/
noncomputable def spe_F (g : ℝ × ℝ → ℝ) (L : ℝ) (x : ℝ × ℝ) (t : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  spe_D1 g L x t • ContinuousLinearMap.fst ℝ ℝ ℝ + spe_D2 g L x t • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem spe_cont (g : ℝ × ℝ → ℝ) (L : ℝ) (hg : ContDiff ℝ ∞ g) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => spe_D1 g L p.1 p.2) ∧
      Continuous (fun p : (ℝ × ℝ) × ℝ => spe_D2 g L p.1 p.2) := by
  have hgc : Continuous g := hg.continuous
  have hfd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hu : Continuous (fun p : (ℝ × ℝ) × ℝ => ((p.1.1, -L + p.2 * (p.1.2 + L)) : ℝ × ℝ)) := by
    fun_prop
  have hA : Continuous (fun p : (ℝ × ℝ) × ℝ => fderiv ℝ g (p.1.1, -L + p.2 * (p.1.2 + L))) :=
    hfd.comp hu
  have hB : Continuous (fun p : (ℝ × ℝ) × ℝ => g (p.1.1, -L + p.2 * (p.1.2 + L))) :=
    hgc.comp hu
  constructor
  · unfold spe_D1
    fun_prop
  · unfold spe_D2
    fun_prop

/-- Pointwise chain rule for `y ↦ (y.2 + L) g(y.1, -L + t (y.2 + L))`. -/
theorem spe_pt_hasFDerivAt (g : ℝ × ℝ → ℝ) (L t : ℝ) (hg : ContDiff ℝ ∞ g) (z : ℝ × ℝ) :
    HasFDerivAt (fun y : ℝ × ℝ => (y.2 + L) * g (y.1, -L + t * (y.2 + L))) (spe_F g L z t) z := by
  have hgd : HasFDerivAt g (fderiv ℝ g (z.1, -L + t * (z.2 + L))) (z.1, -L + t * (z.2 + L)) :=
    ((hg.differentiable (by simp)) _).hasFDerivAt
  have hA : HasFDerivAt (fun y : ℝ × ℝ => (y.1, -L + t * (y.2 + L)))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (t • ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    hasFDerivAt_fst.prodMk (((hasFDerivAt_snd.add_const L).const_mul t).const_add (-L))
  have hcomp := hgd.comp z hA
  have hmul := (hasFDerivAt_snd.add_const L).mul hcomp
  refine hmul.congr_fderiv ?_
  unfold spe_F spe_D1 spe_D2
  refine ContinuousLinearMap.ext fun v => ?_
  have k := spe_key (fderiv ℝ g (z.1, -L + t * (z.2 + L))) (v.1, t * v.2)
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [k]
  dsimp only
  ring

/-- The parametric integral `z ↦ ∫_0^1 Φ(z, t) dt` is differentiable at `z`. -/
theorem spe_param_hasFDerivAt (g : ℝ × ℝ → ℝ) (L : ℝ) (hg : ContDiff ℝ ∞ g) (z : ℝ × ℝ) :
    HasFDerivAt (fun y : ℝ × ℝ => ∫ t in (0:ℝ)..1, (y.2 + L) * g (y.1, -L + t * (y.2 + L)))
      (∫ t in (0:ℝ)..1, spe_F g L z t) z := by
  have hgc : Continuous g := hg.continuous
  have hF : Continuous (fun p : (ℝ × ℝ) × ℝ => spe_F g L p.1 p.2) := by
    unfold spe_F
    exact ((spe_cont g L hg).1.smul continuous_const).add
      ((spe_cont g L hg).2.smul continuous_const)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).exists_bound_of_continuousOn
    hF.continuousOn
  have hcont_t : ∀ y : ℝ × ℝ, Continuous (fun t : ℝ => (y.2 + L) * g (y.1, -L + t * (y.2 + L))) := by
    intro y
    fun_prop
  have hcontF : ∀ y : ℝ × ℝ, Continuous (fun t : ℝ => spe_F g L y t) := fun y =>
    hF.comp (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (y, t))
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => (y.2 + L) * g (y.1, -L + t * (y.2 + L)))
    (F' := fun y t => spe_F g L y t) (bound := fun _ => C) (s := Metric.closedBall z 1)
    (Metric.closedBall_mem_nhds z one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y => (hcont_t y).aestronglyMeasurable
  · exact (hcont_t z).intervalIntegrable 0 1
  · exact (hcontF z).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht
    exact hC (x, t) ⟨hx, ht'⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ x _ => spe_pt_hasFDerivAt g L t hg x

/-- The integral of the derivative: the `q`-coefficient is the substituted primitive of
`∂_q g` and the `η`-coefficient is `g(z)` by the fundamental theorem of calculus in `t`. -/
theorem spe_integral_F (g : ℝ × ℝ → ℝ) (L : ℝ) (hg : ContDiff ℝ ∞ g) (z : ℝ × ℝ) :
    ∫ t in (0:ℝ)..1, spe_F g L z t =
      (∫ s in (-L)..z.2, fderiv ℝ g (z.1, s) (1, 0)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + g z • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  have hD1t : Continuous (fun t : ℝ => spe_D1 g L z t) :=
    (spe_cont g L hg).1.comp (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (z, t))
  have hD2t : Continuous (fun t : ℝ => spe_D2 g L z t) :=
    (spe_cont g L hg).2.comp (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (z, t))
  have hc1 : Continuous (fun t : ℝ => spe_D1 g L z t • ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    hD1t.smul continuous_const
  have hc2 : Continuous (fun t : ℝ => spe_D2 g L z t • ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    hD2t.smul continuous_const
  have e1 : ∫ t in (0:ℝ)..1, spe_D1 g L z t = ∫ s in (-L)..z.2, fderiv ℝ g (z.1, s) (1, 0) := by
    rw [spe_subst (fun s => fderiv ℝ g (z.1, s) (1, 0)) L z.2]
    simp only [spe_D1, intervalIntegral.integral_const_mul]
  have e2 : ∫ t in (0:ℝ)..1, spe_D2 g L z t = g z := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * g (z.1, -L + t * (z.2 + L)))
        (spe_D2 g L z t) t := by
      intro t
      have hline : HasDerivAt (fun t : ℝ => ((z.1, -L + t * (z.2 + L)) : ℝ × ℝ))
          ((0:ℝ), z.2 + L) t := by
        apply HasDerivAt.prodMk (hasDerivAt_const t z.1)
        simpa using ((hasDerivAt_id' t).mul_const (z.2 + L)).const_add (-L)
      have hgd : HasFDerivAt g (fderiv ℝ g (z.1, -L + t * (z.2 + L)))
          (z.1, -L + t * (z.2 + L)) :=
        ((hg.differentiable (by simp)) _).hasFDerivAt
      have hgt := hgd.comp_hasDerivAt t hline
      have hprod := (hasDerivAt_id' t).mul hgt
      refine hprod.congr_deriv ?_
      unfold spe_D2
      rw [spe_key (fderiv ℝ g (z.1, -L + t * (z.2 + L))) (0, z.2 + L)]
      dsimp only [Function.comp_apply]
      ring
    have hint : IntervalIntegrable (fun t : ℝ => spe_D2 g L z t) volume 0 1 :=
      hD2t.intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
    show (1:ℝ) * g (z.1, -L + 1 * (z.2 + L)) - 0 * g (z.1, -L + 0 * (z.2 + L)) = g z
    have e : -L + (1:ℝ) * (z.2 + L) = z.2 := by ring
    rw [e]
    simp
  unfold spe_F
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1),
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const, e1, e2]

/-- The primitive `P(z) = ∫_{-L}^{η} g(q, s) ds` is differentiable, with the derivative stated in
`SmoothPrimEta`. -/
theorem spe_hasFDerivAt_P (g : ℝ × ℝ → ℝ) (L : ℝ) (hg : ContDiff ℝ ∞ g) (z : ℝ × ℝ) :
    HasFDerivAt (fun y : ℝ × ℝ => ∫ s in (-L)..y.2, g (y.1, s))
      ((∫ s in (-L)..z.2, fderiv ℝ g (z.1, s) (1, 0)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + g z • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  have e : (fun y : ℝ × ℝ => ∫ s in (-L)..y.2, g (y.1, s)) =
      (fun y : ℝ × ℝ => ∫ t in (0:ℝ)..1, (y.2 + L) * g (y.1, -L + t * (y.2 + L))) := by
    funext y
    rw [spe_subst (fun s => g (y.1, s)) L y.2, intervalIntegral.integral_const_mul]
  rw [e]
  exact (spe_param_hasFDerivAt g L hg z).congr_fderiv (spe_integral_F g L hg z)

/-- Smoothness of the primitive, by induction on the order (for all smooth `g` at once). -/
theorem spe_contDiff_nat (L : ℝ) (n : ℕ) : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g →
    ContDiff ℝ (n : WithTop ℕ∞) (fun z : ℝ × ℝ => ∫ s in (-L)..z.2, g (z.1, s)) := by
  induction n with
  | zero =>
    intro g hg
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun z => (spe_hasFDerivAt_P g L hg z).continuousAt
  | succ n ih =>
    intro g hg
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun z => (spe_hasFDerivAt_P g L hg z).differentiableAt, fun h => absurd h (by simp), ?_⟩
    have hfd : fderiv ℝ (fun z : ℝ × ℝ => ∫ s in (-L)..z.2, g (z.1, s)) =
        fun z => (∫ s in (-L)..z.2, fderiv ℝ g (z.1, s) (1, 0)) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + g z • ContinuousLinearMap.snd ℝ ℝ ℝ :=
      funext fun z => (spe_hasFDerivAt_P g L hg z).fderiv
    rw [hfd]
    have hgd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
    have hh : ContDiff ℝ ∞ (fun z : ℝ × ℝ => fderiv ℝ g z (1, 0)) :=
      hgd.clm_apply contDiff_const
    have hc := ih (fun z => fderiv ℝ g z (1, 0)) hh
    have hg' : ContDiff ℝ (n : WithTop ℕ∞) g := contDiff_infty.1 hg n
    exact (hc.smul contDiff_const).add (hg'.smul contDiff_const)

theorem smoothPrimEta : SmoothPrimEta := by
  unfold SmoothPrimEta
  intro g L hg _
  refine ⟨contDiff_infty.2 fun n => spe_contDiff_nat L n g hg, fun z => ?_, fun z => ?_⟩
  · rw [(spe_hasFDerivAt_P g L hg z).fderiv]
    simp
  · rw [(spe_hasFDerivAt_P g L hg z).fderiv]
    simp

end UnforcedLeray.Short.IIb
