import UnforcedLeray.Short.PartI.Sub.PartI_S15_2

/-!
# Part I, task `PartI:S15/2/2`: `xgEmbDense`

Source: `the November 2 reference manuscript` lines 841-889 and the embedding
task `PartI:S01` (`XgEmbGeneral.lean`).

Route (Hilbert-space duality).  Let `K` be the range of the embedding `T = xgEmbM hM`.  If
`x ⊥ K` in `L²(profileMeasure M)`, then testing against the indicators `1_S` of sets `S` with
finite `X_G` measure (these lie in `X_G` and `T 1_S = 1_S` a.e.) gives `∫_S x = 0` for all such
`S`.  Sets inside `(0,n)` have finite `X_G` measure, so `x = 0` a.e. on each `(0,n)`, hence a.e.
on `(0,∞)`, which carries the profile measure.  Thus `K^⊥ = ⊥`, so `K̄ = K^⊥⊥ = ⊤`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal InnerProductSpace ComplexConjugate Topology

namespace UnforcedLeray.Short.PartI

/-- The `X_G` measure is finite on bounded subintervals of `(0,∞)`. -/
theorem xGMeasure_Ioo_lt_top (R : ℝ) : B0010.xGMeasure (Ioo 0 R) < ⊤ := by
  rw [B0010.xGMeasure_apply measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
  calc ∫⁻ r in Ioo 0 R, ENNReal.ofReal ((B0010.radialGaussianWeight r)⁻¹ * r)
      ≤ ∫⁻ _ in Ioo 0 R, ENNReal.ofReal (4 * π * Real.exp (R ^ 2 / 4) * R) := by
        refine setLIntegral_mono' measurableSet_Ioo (fun r hr => ?_)
        rw [B0010.radialGaussianWeight_inv]
        apply ENNReal.ofReal_le_ofReal
        have hr0 : 0 < r := hr.1
        have hrR : r < R := hr.2
        have h1 : Real.exp (r ^ 2 / 4) ≤ Real.exp (R ^ 2 / 4) :=
          Real.exp_le_exp.2 (by nlinarith)
        calc 4 * π * Real.exp (r ^ 2 / 4) * r
            ≤ 4 * π * Real.exp (R ^ 2 / 4) * r :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hr0.le
          _ ≤ 4 * π * Real.exp (R ^ 2 / 4) * R :=
              mul_le_mul_of_nonneg_left hrR.le (by positivity)
    _ = ENNReal.ofReal (4 * π * Real.exp (R ^ 2 / 4) * R) * volume (Ioo 0 R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)

/-- The profile measure is finite on bounded subintervals of `(0,∞)`. -/
theorem profileMeasure_Ioo_lt_top {M : ℝ} (hM : 0 ≤ M) (R : ℝ) :
    Planar.profileMeasure M (Ioo 0 R) < ⊤ := by
  have h := Measure.le_iff'.1 (profileMeasure_le_xGMeasure_smul hM) (Ioo 0 R)
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (xGMeasure_Ioo_lt_top R))

/-- **Target.** The embedding `X_G → L²_M` has dense range for `M > 1`. -/
theorem xgEmbDense : XgEmbDense := by
  unfold XgEmbDense
  intro M hM
  have hM0 : (0 : ℝ) ≤ M := by linarith
  set T : B0010.XG →L[ℂ] Planar.ProfL2 M := xgEmbM hM with hT
  set K : Submodule ℂ (Planar.ProfL2 M) := LinearMap.range (T : B0010.XG →ₗ[ℂ] Planar.ProfL2 M)
    with hK
  have hKs : (K : Set (Planar.ProfL2 M)) = Set.range T := by
    ext y
    simp [K]
  -- the orthogonal complement of `K` is trivial
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hort : ∀ f : B0010.XG, ⟪T f, x⟫_ℂ = 0 := by
      intro f
      have hx' := hx
      rw [Submodule.mem_orthogonal] at hx'
      exact hx' (T f) (LinearMap.mem_range.2 ⟨f, rfl⟩)
    -- integrals of `x` over sets of finite `X_G` measure vanish
    have hset : ∀ S : Set ℝ, MeasurableSet S → B0010.xGMeasure S ≠ ⊤ →
        ∫ a in S, x a ∂(Planar.profileMeasure M) = 0 := by
      intro S hS hxS
      have h1 : ⇑(indicatorConstLp 2 hS hxS (1 : ℂ)) =ᵐ[B0010.xGMeasure]
          S.indicator fun _ => (1 : ℂ) := indicatorConstLp_coeFn
      have hae : ⇑(T (indicatorConstLp 2 hS hxS (1 : ℂ))) =ᵐ[Planar.profileMeasure M]
          S.indicator fun _ => (1 : ℂ) :=
        (coeFn_xgEmbM hM _).trans ((profileMeasure_ac_xGMeasure hM0).ae_le h1)
      have h0 := hort (indicatorConstLp 2 hS hxS (1 : ℂ))
      rw [MeasureTheory.L2.inner_def] at h0
      have hcongr : ∫ a, ⟪(T (indicatorConstLp 2 hS hxS (1 : ℂ))) a, x a⟫_ℂ
          ∂(Planar.profileMeasure M) = ∫ a, S.indicator x a ∂(Planar.profileMeasure M) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with a ha
        rw [ha]
        by_cases haS : a ∈ S <;> simp [Set.indicator, haS, RCLike.inner_apply]
      rw [← integral_indicator hS, ← hcongr]
      exact h0
    -- hence `x = 0` a.e. on each `(0,n)`, and so a.e. on `(0,∞)`
    have hall : ∀ n : ℕ, ∀ᵐ a ∂(Planar.profileMeasure M), a ∈ Ioo 0 (n : ℝ) → x a = 0 := by
      intro n
      haveI : IsFiniteMeasure ((Planar.profileMeasure M).restrict (Ioo 0 (n : ℝ))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact profileMeasure_Ioo_lt_top hM0 n⟩
      have hint : ∀ s : Set ℝ, MeasurableSet s →
          ((Planar.profileMeasure M).restrict (Ioo 0 (n : ℝ))) s < ⊤ →
          IntegrableOn (⇑x) s ((Planar.profileMeasure M).restrict (Ioo 0 (n : ℝ))) :=
        fun s _ _ => ((MemLp.restrict (Ioo 0 (n : ℝ)) (Lp.memLp x)).integrable one_le_two).integrableOn
      have hzero' : ∀ s : Set ℝ, MeasurableSet s →
          ((Planar.profileMeasure M).restrict (Ioo 0 (n : ℝ))) s < ⊤ →
          ∫ a in s, x a ∂((Planar.profileMeasure M).restrict (Ioo 0 (n : ℝ))) = 0 := by
        intro s hs _
        rw [Measure.restrict_restrict hs]
        exact hset (s ∩ Ioo 0 (n : ℝ)) (hs.inter measurableSet_Ioo)
          (ne_top_of_le_ne_top (xGMeasure_Ioo_lt_top n).ne (measure_mono inter_subset_right))
      have hae := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint hzero'
      exact (ae_restrict_iff' measurableSet_Ioo).1 hae
    have hall' : ∀ᵐ a ∂(Planar.profileMeasure M), ∀ n : ℕ, a ∈ Ioo 0 (n : ℝ) → x a = 0 :=
      ae_all_iff.2 hall
    have hfull : ∀ᵐ a ∂(Planar.profileMeasure M), x a = 0 := by
      filter_upwards [hall', Planar.ae_profile_pos M] with a h1 h2
      obtain ⟨n, hn⟩ := exists_nat_gt a
      exact h1 n ⟨h2, hn⟩
    exact Lp.eq_zero_iff_ae_eq_zero.2 hfull
  -- `K̄ = K^⊥⊥ = ⊤`, so `K` is dense
  have hdense : Dense (K : Set (Planar.ProfL2 M)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      ← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top,
      Submodule.top_coe]
  unfold DenseRange
  rw [← hKs]
  exact hdense

end UnforcedLeray.Short.PartI
