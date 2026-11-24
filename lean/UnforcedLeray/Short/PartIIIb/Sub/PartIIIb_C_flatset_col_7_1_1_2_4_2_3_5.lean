import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2

/-!
# `SmoothForceGradBound` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/5`)

Source `the November 2 reference manuscript`
1684-1689: `g` is `C^∞`, `c`-periodic, supported in `s ∈ [s₀, s₁]`, `|η| ≤ L`.

Proof: the `y`-gradient of the slice `y ↦ F(σ, y)` is the `(0, ·)`-derivative of `F` at `(σ, y)`
(chain rule along `y ↦ (σ, y)`), which is continuous and hence bounded by `C0` on the compact set
`[s₀, s₁] × B`, where `B = [-c/2, c/2] × [-L', L']`, `L' = max L 0`. The slice gradient vanishes
off `[s₀, s₁]` and for `|η| > L`, so the integrand over `[-c/2, c/2) × ℝ` is at most
`ofReal (4 M²)` times the indicator of `B`, whose measure is `c · 2L'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff
open UnforcedLeray.Short.IIIa (tnorm2)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem smoothForceGradBound : SmoothForceGradBound := by
  intro c hc F hFs _hFp hband
  obtain ⟨s0, s1, L, hs0, hFsupp⟩ := hband
  obtain ⟨L', hL'⟩ : ∃ L' : ℝ, L' = max L 0 := ⟨_, rfl⟩
  have hLL' : L ≤ L' := by rw [hL']; exact le_max_left _ _
  have hL'0 : 0 ≤ L' := by rw [hL']; exact le_max_right _ _
  -- compact set of `(σ, y)` where the slice gradient may be nonzero
  have hKc : IsCompact (Icc s0 s1 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L')) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : ∀ i : Fin 2, Continuous fun p : Chart => fderiv ℝ (fun q : Chart => F q i) p :=
    fun i => (hFs i).continuous_fderiv (by simp)
  have hDn : Continuous fun p : Chart => ∑ i : Fin 2, ‖fderiv ℝ (fun q : Chart => F q i) p‖ :=
    continuous_finsetSum _ fun i _ => (hcont i).norm
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hDn.continuousOn
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max C0 0 := ⟨_, rfl⟩
  have hC0M : C0 ≤ M := by rw [hM]; exact le_max_left _ _
  have hM0 : 0 ≤ M := by rw [hM]; exact le_max_right _ _
  -- chain rule along `y ↦ (σ, y)`
  have hchain : ∀ (σ : ℝ) (i : Fin 2) (x v : ℝ × ℝ),
      fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x v
        = fderiv ℝ (fun q : Chart => F q i) (σ, x) ((0 : ℝ), v) := by
    intro σ i x v
    have hF : DifferentiableAt ℝ (fun q : Chart => F q i) (σ, x) :=
      ((hFs i).differentiable (by simp)).differentiableAt
    have hg : HasFDerivAt (fun y : ℝ × ℝ => ((σ : ℝ), y))
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
      (hasFDerivAt_const σ x).prodMk (hasFDerivAt_id x)
    have hcomp := hF.hasFDerivAt.comp x hg
    have h1 : fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x =
        (fderiv ℝ (fun q : Chart => F q i) (σ, x)).comp
          ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) := hcomp.fderiv
    rw [h1]
    simp
  -- the `(0, dir j)` vectors have norm at most one
  have hdir : ∀ j : Fin 2, ‖((0 : ℝ), UnforcedLeray.B0579.dir j)‖ ≤ 1 := by
    intro j
    fin_cases j <;> simp [Prod.norm_def, UnforcedLeray.B0579.dir]
  -- bound on the slice gradient over the compact set
  have hentryK : ∀ (σ : ℝ) (x : ℝ × ℝ),
      (σ, x) ∈ Icc s0 s1 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L') →
      ∀ (i j : Fin 2),
        ‖fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j)‖ ≤ M := by
    intro σ x hmem i j
    have hsum : ∑ i' : Fin 2, ‖fderiv ℝ (fun q : Chart => F q i') (σ, x)‖ ≤ C0 := by
      have h1 : ‖∑ i' : Fin 2, ‖fderiv ℝ (fun q : Chart => F q i') (σ, x)‖‖ ≤ C0 :=
        hC0 (σ, x) hmem
      exact le_trans (le_abs_self _) (by rw [← Real.norm_eq_abs]; exact h1)
    have hle : ‖fderiv ℝ (fun q : Chart => F q i) (σ, x)‖ ≤ C0 :=
      le_trans (Finset.single_le_sum (f := fun i' : Fin 2 =>
        ‖fderiv ℝ (fun q : Chart => F q i') (σ, x)‖) (fun i' _ => norm_nonneg _)
        (Finset.mem_univ i)) hsum
    calc ‖fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j)‖
        = ‖fderiv ℝ (fun q : Chart => F q i) (σ, x) ((0 : ℝ), UnforcedLeray.B0579.dir j)‖ := by
          rw [hchain]
      _ ≤ ‖fderiv ℝ (fun q : Chart => F q i) (σ, x)‖ * 1 :=
          (fderiv ℝ (fun q : Chart => F q i) (σ, x)).le_opNorm_of_le (hdir j)
      _ ≤ C0 := by rw [mul_one]; exact hle
      _ ≤ M := hC0M
  -- the slice gradient vanishes for `σ` outside `[s₀, s₁]`
  have hzeroσ : ∀ σ : ℝ, σ ∉ Icc s0 s1 → ∀ (x : ℝ × ℝ) (i : Fin 2) (v : ℝ × ℝ),
      fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x v = 0 := by
    intro σ hσ x i v
    have hfun : (fun y : ℝ × ℝ => F (σ, y) i) = fun _ => (0 : ℝ) := by
      funext y
      show F (σ, y) i = 0
      by_contra h
      have hne : F (σ, y) ≠ 0 := fun h0 => h (by simp [h0])
      exact hσ (hFsupp (σ, y) hne).1
    rw [hfun]
    simp
  -- the slice gradient vanishes for `|η| > L`
  have hzeroη : ∀ (σ : ℝ) (x : ℝ × ℝ) (i : Fin 2) (v : ℝ × ℝ), L < |x.2| →
      fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x v = 0 := by
    intro σ x i v hx
    have hopen : IsOpen {y : ℝ × ℝ | L < |y.2|} :=
      isOpen_lt continuous_const (by fun_prop)
    have hev : (fun y : ℝ × ℝ => F (σ, y) i) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      show F (σ, y) i = 0
      by_contra h
      have hne : F (σ, y) ≠ 0 := fun h0 => h (by simp [h0])
      have h1 : |y.2| ≤ L := (hFsupp (σ, y) hne).2
      have h2 : L < |y.2| := hy
      linarith
    rw [hev.fderiv_eq]
    simp
  have hentry : ∀ (σ : ℝ) (x : ℝ × ℝ), x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L' →
      ∀ (i j : Fin 2),
        ‖fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j)‖ ≤ M := by
    intro σ x hx i j
    by_cases hσ : σ ∈ Icc s0 s1
    · exact hentryK σ x ⟨hσ, hx⟩ i j
    · rw [hzeroσ σ hσ x i _, norm_zero]
      exact hM0
  have hBm : MeasurableSet (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L') :=
    measurableSet_Icc.prod measurableSet_Icc
  have hmeas : Measurable
      ((Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L').indicator
        (fun _ : ℝ × ℝ => ENNReal.ofReal (4 * M ^ 2))) :=
    measurable_const.indicator hBm
  have hv1 : ENNReal.ofReal (c / 2 - -(c / 2)) * ENNReal.ofReal (L' - -L')
      = ENNReal.ofReal (c * (2 * L')) := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ c / 2 - -(c / 2) by linarith)]
    congr 1
    ring
  have hv2 : ENNReal.ofReal (4 * M ^ 2) * ENNReal.ofReal (c * (2 * L'))
      = ENNReal.ofReal (4 * M ^ 2 * (c * (2 * L'))) :=
    (ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 * M ^ 2 by positivity)).symm
  refine ⟨4 * M ^ 2 * (c * (2 * L')), fun σ => ?_⟩
  -- pointwise bound of the integrand on `Ico × ℝ`
  have hpt : ∀ x ∈ Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (tnorm2 (fun i j =>
        ((fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j) : ℝ) : ℂ)) ^ 2)
        ≤ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L').indicator
            (fun _ : ℝ × ℝ => ENNReal.ofReal (4 * M ^ 2)) x := by
    intro x hx
    have hx1 : x.1 ∈ Icc (-(c / 2)) (c / 2) := Ico_subset_Icc_self hx.1
    by_cases hxB : x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L'
    · rw [Set.indicator_of_mem hxB]
      apply ENNReal.ofReal_le_ofReal
      have hsq : ∀ i j : Fin 2,
          ‖((fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j) : ℝ) : ℂ)‖ ^ 2
            ≤ M ^ 2 := by
        intro i j
        rw [Complex.norm_real]
        exact pow_le_pow_left₀ (norm_nonneg _) (hentry σ x hxB i j) 2
      simp only [projGrad_tnorm2_sq]
      calc ∑ i : Fin 2, ∑ j : Fin 2,
            ‖((fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j) : ℝ) : ℂ)‖ ^ 2
          ≤ ∑ i : Fin 2, ∑ j : Fin 2, M ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq i j
        _ = 4 * M ^ 2 := by simp [Fin.sum_univ_two]; ring
    · rw [Set.indicator_of_notMem hxB]
      have hη : L' < |x.2| := by
        by_contra hle
        rw [not_lt] at hle
        exact hxB ⟨hx1, abs_le.mp hle⟩
      have hD : ∀ i j : Fin 2,
          fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j) = 0 :=
        fun i j => hzeroη σ x i _ (lt_of_le_of_lt hLL' hη)
      have hT : tnorm2 (fun i j =>
          ((fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j) : ℝ) : ℂ)) ^ 2
          = 0 := by
        simp only [projGrad_tnorm2_sq, hD]
        simp
      rw [hT, ENNReal.ofReal_zero]
  calc ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j =>
          ((fderiv ℝ (fun y : ℝ × ℝ => F (σ, y) i) x (UnforcedLeray.B0579.dir j) : ℝ) : ℂ)) ^ 2)
      ≤ ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
          (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L').indicator
            (fun _ : ℝ × ℝ => ENNReal.ofReal (4 * M ^ 2)) x :=
        setLIntegral_mono hmeas hpt
    _ ≤ ∫⁻ x, (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L').indicator
            (fun _ : ℝ × ℝ => ENNReal.ofReal (4 * M ^ 2)) x :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (4 * M ^ 2) * volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L') L') :=
        lintegral_indicator_const hBm _
    _ = ENNReal.ofReal (4 * M ^ 2) *
          (ENNReal.ofReal (c / 2 - -(c / 2)) * ENNReal.ofReal (L' - -L')) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    _ = ENNReal.ofReal (4 * M ^ 2 * (c * (2 * L'))) := by
        rw [hv1, hv2]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
