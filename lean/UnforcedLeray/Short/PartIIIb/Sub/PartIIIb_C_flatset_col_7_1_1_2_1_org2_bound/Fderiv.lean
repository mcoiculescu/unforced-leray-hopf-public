import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bound.Sup

/-!
# `DuhamelFderivBound`: the `x`-derivative of the Duhamel integral on a slice `s > 0`

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.

The derivative is bounded through a global Lipschitz bound in `x`: the planar heat is
Lipschitz with the same constant as its data (Gaussian probability density), the `σ`-integrand
is bounded by `(σ/s)^μ` times that, and `norm_fderiv_le_of_lipschitz` converts Lipschitz into a
derivative bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The `σ`-integrand of `duhamel` at the point `x` (definitionally the integrand of `duhamel`). -/
def sliceTerm (G : Chart → Fin 2 → ℝ) (ν μ s : ℝ) (i : Fin 2) (x : ℝ × ℝ) (σ : ℝ) : ℂ :=
  (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
    UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x

theorem duhamel_eq_sliceTerm (ν μ : ℝ) (G : Chart → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    duhamel ν μ G (s, x) i = ∫ σ in (0 : ℝ)..s, sliceTerm G ν μ s i x σ := rfl

/-- Integrability of `y ↦ g(y) • v(y)` for a Gaussian `g` and a bounded continuous `v`. -/
theorem integrable_gauss_smul {θ M : ℝ} (hθ : 0 < θ) {v : UnforcedLeray.Gaussian.Euc 2 → ℂ}
    (hv : Continuous v) (hb : ∀ y, ‖v y‖ ≤ M) :
    Integrable (fun y => UnforcedLeray.Gaussian.gaussKernel 2 θ y • v y) := by
  have hint := UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  exact hint.smul_bdd M hv.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- The planar heat is Lipschitz with the constant of its (bounded, continuous) data. -/
theorem planeHeat_lipschitz {θ L M : ℝ} (u : ℝ × ℝ → ℂ) (hu : Continuous u) (hL : 0 ≤ L)
    (hlip : ∀ z z' : ℝ × ℝ, ‖u z' - u z‖ ≤ L * ‖z' - z‖) (hbdd : ∀ z, ‖u z‖ ≤ M)
    (x x' : ℝ × ℝ) :
    ‖UnforcedLeray.B0224.planeHeat θ u x' - UnforcedLeray.B0224.planeHeat θ u x‖
      ≤ L * ‖x' - x‖ := by
  by_cases hθ : 0 < θ
  · have hcx : ∀ x'' : ℝ × ℝ, Continuous fun y : UnforcedLeray.Gaussian.Euc 2 =>
        u (x'' - UnforcedLeray.B0224.planeι y) := fun x'' =>
      hu.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)
    have hbd : ∀ (x'' : ℝ × ℝ) (y : UnforcedLeray.Gaussian.Euc 2),
        ‖u (x'' - UnforcedLeray.B0224.planeι y)‖ ≤ M := fun x'' y => hbdd _
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ,
      ← integral_sub (integrable_gauss_smul hθ (hcx x') (hbd x'))
        (integrable_gauss_smul hθ (hcx x) (hbd x))]
    calc _ ≤ ∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y * (L * ‖x' - x‖) := by
          apply MeasureTheory.norm_integral_le_of_norm_le
            ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const _)
          refine Filter.Eventually.of_forall (fun y => ?_)
          show ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x' - UnforcedLeray.B0224.planeι y)
              - UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)‖
            ≤ UnforcedLeray.Gaussian.gaussKernel 2 θ y * (L * ‖x' - x‖)
          rw [← smul_sub, norm_smul,
            Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
          apply mul_le_mul_of_nonneg_left _ (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
          have h := hlip (x - UnforcedLeray.B0224.planeι y) (x' - UnforcedLeray.B0224.planeι y)
          rwa [sub_sub_sub_cancel_right] at h
      _ = L * ‖x' - x‖ := by
          rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel hθ, one_mul]
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    exact hlip x x'

/-- Pointwise bound of the `σ`-integrand on `(0, s]`: a uniform sup bound (as in `Sup.lean`). -/
theorem sliceTerm_bound {G : Chart → Fin 2 → ℝ} {ν μ s s0 s1 M : ℝ} {i : Fin 2}
    (hs0 : 0 < s0) (hs : 0 < s) (hM0 : 0 ≤ M)
    (hsupp : ∀ p : Chart, G p ≠ 0 → p.1 ∈ Icc s0 s1)
    (hGM : ∀ p : Chart, ‖G p i‖ ≤ M) (x : ℝ × ℝ) (σ : ℝ) (hσ : σ ∈ Ioc 0 s) :
    ‖sliceTerm G ν μ s i x σ‖ ≤ Real.exp (|Real.log (s0 / s)| * |μ|) * M := by
  unfold sliceTerm
  obtain ⟨hσ0, hσs⟩ := hσ
  rw [norm_smul]
  by_cases hlt : σ < s0
  · have hz : ∀ z, G (σ, z) = 0 := by
      intro z
      by_contra hne
      have h1 : s0 ≤ (σ, z).1 := (hsupp (σ, z) hne).1
      exact absurd h1 (not_le.2 hlt)
    have hu : ∀ z, ‖((G (σ, z) i : ℝ) : ℂ)‖ ≤ 0 := fun z => by
      rw [hz z]
      simp
    have h0 : ‖UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => ((G (σ, z) i : ℝ) : ℂ)) x‖ = 0 :=
      le_antisymm (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.norm_planeHeat_le_of_bound
        (θ := ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) hu x) (norm_nonneg _)
    rw [h0, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le hM0
  · have hlt' : s0 ≤ σ := not_lt.1 hlt
    have hu : ∀ z, ‖((G (σ, z) i : ℝ) : ℂ)‖ ≤ M := fun z => by
      rw [Complex.norm_real]
      exact hGM (σ, z)
    have hH := UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.norm_planeHeat_le_of_bound
      (θ := ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) hu x
    have ha := UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.cpow_ratio_bound
      (μ := μ) hs0 hσ0 hσs hlt' hs
    exact mul_le_mul ha hH (norm_nonneg _) (Real.exp_pos _).le

/-- Lipschitz bound of the `σ`-integrand difference on `(0, s]`. -/
theorem sliceTerm_lip {G : Chart → Fin 2 → ℝ} {ν μ s s0 s1 M C : ℝ} {i : Fin 2}
    (hs0 : 0 < s0) (hs : 0 < s) (hC : 0 ≤ C)
    (hsupp : ∀ p : Chart, G p ≠ 0 → p.1 ∈ Icc s0 s1)
    (hlipG : ∀ (σ : ℝ) (z z' : ℝ × ℝ),
      ‖((G (σ, z') i : ℝ) : ℂ) - ((G (σ, z) i : ℝ) : ℂ)‖ ≤ C * ‖z' - z‖)
    (hGM : ∀ p : Chart, ‖G p i‖ ≤ M) (hM0 : 0 ≤ M)
    (hcont : ∀ σ : ℝ, Continuous fun z : ℝ × ℝ => ((G (σ, z) i : ℝ) : ℂ))
    (x x' : ℝ × ℝ) (σ : ℝ) (hσ : σ ∈ Ioc 0 s) :
    ‖sliceTerm G ν μ s i x' σ - sliceTerm G ν μ s i x σ‖
      ≤ Real.exp (|Real.log (s0 / s)| * |μ|) * (C * ‖x' - x‖) := by
  unfold sliceTerm
  obtain ⟨hσ0, hσs⟩ := hσ
  rw [← smul_sub, norm_smul]
  by_cases hlt : σ < s0
  · have hz : ∀ z, G (σ, z) = 0 := by
      intro z
      by_contra hne
      have h1 : s0 ≤ (σ, z).1 := (hsupp (σ, z) hne).1
      exact absurd h1 (not_le.2 hlt)
    have hL0 := planeHeat_lipschitz (θ := ν * (s - σ)) (L := 0) (M := 0)
      (fun z => ((G (σ, z) i : ℝ) : ℂ)) (hcont σ) le_rfl
      (fun z z' => by simp [hz z', hz z]) (fun z => by simp [hz z]) x x'
    have h1 : ‖UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => ((G (σ, z) i : ℝ) : ℂ)) x' -
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => ((G (σ, z) i : ℝ) : ℂ)) x‖ = 0 :=
      le_antisymm (by have h := hL0; rw [zero_mul] at h; exact h) (norm_nonneg _)
    rw [h1, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hC (norm_nonneg _))
  · have hlt' : s0 ≤ σ := not_lt.1 hlt
    have hu : ∀ z, ‖((G (σ, z) i : ℝ) : ℂ)‖ ≤ M := fun z => by
      rw [Complex.norm_real]
      exact hGM (σ, z)
    have hL := planeHeat_lipschitz (θ := ν * (s - σ)) (L := C) (M := M)
      (fun z => ((G (σ, z) i : ℝ) : ℂ)) (hcont σ) hC (fun z z' => hlipG σ z z') hu x x'
    have ha := UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.cpow_ratio_bound
      (μ := μ) hs0 hσ0 hσs hlt' hs
    exact mul_le_mul ha hL (norm_nonneg _) (Real.exp_pos _).le

/-- Measurability in `σ` of the `σ`-integrand (joint measurability of the Gaussian average). -/
theorem sliceTerm_measurable {G : Chart → Fin 2 → ℝ} {i : Fin 2} (ν μ s : ℝ)
    (hGc : Continuous fun p : Chart => G p i) (x : ℝ × ℝ) :
    Measurable fun σ : ℝ => sliceTerm G ν μ s i x σ := by
  have hH : Measurable fun σ : ℝ =>
      UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x := by
    have hfun : (fun σ : ℝ => UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => ((G (σ, z) i : ℝ) : ℂ)) x) =
        fun σ => if 0 < ν * (s - σ) then
          ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - σ)) y •
            ((G (σ, x - UnforcedLeray.B0224.planeι y) i : ℝ) : ℂ)
        else ((G (σ, x) i : ℝ) : ℂ) := by
      funext σ
      by_cases h : 0 < ν * (s - σ)
      · rw [if_pos h, UnforcedLeray.B0224.planeHeat_of_pos h]
      · rw [if_neg h, UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 h)]
    rw [hfun]
    have hsm : StronglyMeasurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - p.1)) p.2 •
          ((G (p.1, x - UnforcedLeray.B0224.planeι p.2) i : ℝ) : ℂ)) := by
      have m1 : Measurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
          UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - p.1)) p.2) :=
        UnforcedLeray.B0224.measurable_gaussKernel_two.comp
          ((measurable_const.mul (measurable_const.sub measurable_fst)).prodMk measurable_snd)
      have m2 : Continuous (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
          ((G (p.1, x - UnforcedLeray.B0224.planeι p.2) i : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (hGc.comp (continuous_fst.prodMk
          (continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp continuous_snd))))
      exact (m1.smul m2.measurable).stronglyMeasurable
    refine Measurable.ite ?_ ?_ ?_
    · exact measurableSet_lt measurable_const
        (measurable_const.mul (measurable_const.sub measurable_id))
    · exact (StronglyMeasurable.integral_prod_right' hsm).measurable
    · exact (Complex.continuous_ofReal.comp (hGc.comp (continuous_id.prodMk
        continuous_const))).measurable
  have ha : Measurable fun σ : ℝ => ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) :=
    (Complex.continuous_ofReal.measurable.comp (measurable_id.div_const s)).pow_const (μ : ℂ)
  exact ha.smul hH

/-- Interval integrability of the `σ`-integrand on `[0, s]`. -/
theorem sliceTerm_intervalIntegrable {G : Chart → Fin 2 → ℝ} {ν μ s s0 s1 M : ℝ} {i : Fin 2}
    (hs0 : 0 < s0) (hs : 0 < s) (hM0 : 0 ≤ M)
    (hsupp : ∀ p : Chart, G p ≠ 0 → p.1 ∈ Icc s0 s1)
    (hGM : ∀ p : Chart, ‖G p i‖ ≤ M) (hGc : Continuous fun p : Chart => G p i) (x : ℝ × ℝ) :
    IntervalIntegrable (fun σ => sliceTerm G ν μ s i x σ) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
  exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (sliceTerm_measurable ν μ s hGc x).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun σ hσ => sliceTerm_bound hs0 hs hM0 hsupp hGM x σ hσ))

theorem duhamelFderivBound : DuhamelFderivBound := by
  intro c ν μ G hG hν s hs
  have hGc : ∀ i : Fin 2, Continuous fun p : Chart => G p i := fun i => (hG.1 i).continuous
  have hdiff : ∀ i : Fin 2, Differentiable ℝ fun p : Chart => G p i :=
    fun i => (hG.1 i).differentiable (by simp)
  obtain ⟨s0, s1, hs0, hsupp⟩ := hG.2.2.1
  have hbG : ∀ i : Fin 2, ∃ M : ℝ, ∀ p : Chart, ‖G p i‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := hG.2.2.2 i 0
    exact ⟨M, fun p => by simpa [norm_iteratedFDeriv_zero] using hM p⟩
  have hbD : ∀ i : Fin 2, ∃ C : ℝ, ∀ p : Chart, ‖fderiv ℝ (fun p : Chart => G p i) p‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := hG.2.2.2 i 1
    exact ⟨C, fun p => by simpa [norm_iteratedFDeriv_one] using hC p⟩
  choose Mb hMb using hbG
  choose Cd hCd using hbD
  set M : ℝ := |Mb 0| + |Mb 1| with hMdef
  set C : ℝ := |Cd 0| + |Cd 1| with hCdef
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hMle : ∀ i : Fin 2, Mb i ≤ M := Fin.forall_fin_two.2
    ⟨by linarith [abs_nonneg (Mb 1), le_abs_self (Mb 0)],
      by linarith [abs_nonneg (Mb 0), le_abs_self (Mb 1)]⟩
  have hCle : ∀ i : Fin 2, Cd i ≤ C := Fin.forall_fin_two.2
    ⟨by linarith [abs_nonneg (Cd 1), le_abs_self (Cd 0)],
      by linarith [abs_nonneg (Cd 0), le_abs_self (Cd 1)]⟩
  have hGM : ∀ (i : Fin 2) (p : Chart), ‖G p i‖ ≤ M := fun i p => (hMb i p).trans (hMle i)
  have hCi : ∀ (i : Fin 2) (p : Chart), ‖fderiv ℝ (fun p : Chart => G p i) p‖ ≤ C :=
    fun i p => (hCd i p).trans (hCle i)
  have hlipG : ∀ (i : Fin 2) (σ : ℝ) (z z' : ℝ × ℝ),
      ‖((G (σ, z') i : ℝ) : ℂ) - ((G (σ, z) i : ℝ) : ℂ)‖ ≤ C * ‖z' - z‖ := by
    intro i σ z z'
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun p : Chart => G p i)
      (s := univ) (C := C) (fun p _ => hdiff i p) (fun p _ => hCi i p) convex_univ
      (mem_univ (σ, z)) (mem_univ (σ, z'))
    have hnorm : ‖((σ, z') : Chart) - (σ, z)‖ ≤ ‖z' - z‖ := by
      rw [Prod.norm_def]
      apply max_le
      · simp
      · simp
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact h.trans (mul_le_mul_of_nonneg_left hnorm hC0)
  have hcont : ∀ (i : Fin 2) (σ : ℝ), Continuous fun z : ℝ × ℝ => ((G (σ, z) i : ℝ) : ℂ) :=
    fun i σ => Complex.continuous_ofReal.comp ((hGc i).comp (continuous_const.prodMk continuous_id))
  have hLip : ∀ (i : Fin 2) (x x' : ℝ × ℝ),
      ‖duhamel ν μ G (s, x') i - duhamel ν μ G (s, x) i‖
        ≤ (Real.exp (|Real.log (s0 / s)| * |μ|) * C * s) * ‖x' - x‖ := by
    intro i x x'
    rw [duhamel_eq_sliceTerm, duhamel_eq_sliceTerm,
      ← intervalIntegral.integral_sub
        (sliceTerm_intervalIntegrable hs0 hs hM0 hsupp (hGM i) (hGc i) x')
        (sliceTerm_intervalIntegrable hs0 hs hM0 hsupp (hGM i) (hGc i) x)]
    calc _ ≤ (Real.exp (|Real.log (s0 / s)| * |μ|) * (C * ‖x' - x‖)) * |s - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro σ hσ
          rw [Set.uIoc_of_le hs.le] at hσ
          exact sliceTerm_lip hs0 hs hC0 hsupp (hlipG i) (hGM i) hM0 (hcont i) x x' σ hσ
      _ = (Real.exp (|Real.log (s0 / s)| * |μ|) * C * s) * ‖x' - x‖ := by
          rw [sub_zero, abs_of_pos hs]
          ring
  refine ⟨Real.toNNReal (Real.exp (|Real.log (s0 / s)| * |μ|) * C * s), fun x i => ?_⟩
  refine norm_fderiv_le_of_lipschitz (𝕜 := ℝ) ?_
  refine LipschitzWith.of_dist_le' (fun y y' => ?_)
  simp only [dist_eq_norm]
  exact hLip i y' y

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
