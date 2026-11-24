import UnforcedLeray.Short.PartIIa.Sub.F01

/-!


Source of record: `the November 2 reference manuscript`, lines 1351-1368.
The free semigroup `S_ν(r)` on complex fields is the complexification of the real operator
`S_ν(r)` (`B0421.freeC`). For `t = ν(e^r - 1) > 0` the heat average is a positive kernel
average, so `|S_ν(r)F(y)| ≤ S_ν(r)|F|(y)` for a.e. `y`, with `c = e^{r/2}`. For `t ≤ 0` the heat
flow is the identity and both sides equal `c · |F(c y)|` a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace (CVec3)
open UnforcedLeray.RieszLp

/-- The vector `a e₀` is the scalar `a` times the first unit vector. -/
theorem single_zero_eq_smul_unit (a : ℝ) :
    EuclideanSpace.single (0 : Fin 3) a = a • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  ext j
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [hj]

/-- The norm of a heat average is dominated by the heat average of the norm placed on the first
coordinate axis. Only the positivity of the Gaussian kernel is used. -/
theorem norm_average_le_single {t : ℝ} (ht : 0 < t) (F0 : UnforcedLeray.Space → CVec3)
    (x : UnforcedLeray.Space) :
    ‖UnforcedLeray.Heat.average t F0 x‖ ≤
      ‖UnforcedLeray.Heat.average t (fun z => EuclideanSpace.single (0 : Fin 3) ‖F0 z‖) x‖ := by
  have hL : UnforcedLeray.Heat.average t (fun z => EuclideanSpace.single (0 : Fin 3) ‖F0 z‖) x
      = (∫ w, UnforcedLeray.Heat.kernel t w * ‖F0 (x - w)‖) •
          EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
    unfold UnforcedLeray.Heat.average
    rw [← integral_smul_const]
    congr 1
    funext w
    show UnforcedLeray.Heat.kernel t w • EuclideanSpace.single (0 : Fin 3) ‖F0 (x - w)‖ =
      (UnforcedLeray.Heat.kernel t w * ‖F0 (x - w)‖) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
    rw [single_zero_eq_smul_unit (‖F0 (x - w)‖), smul_smul]
  have he1 : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := by simp
  have hnorm : ‖(∫ w, UnforcedLeray.Heat.kernel t w * ‖F0 (x - w)‖) •
      EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = ∫ w, UnforcedLeray.Heat.kernel t w * ‖F0 (x - w)‖ := by
    rw [norm_smul, he1, mul_one, Real.norm_of_nonneg]
    exact integral_nonneg fun w => mul_nonneg (UnforcedLeray.Heat.kernel_nonneg ht w) (norm_nonneg _)
  rw [hL, hnorm]
  unfold UnforcedLeray.Heat.average
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext w
  rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Heat.kernel_nonneg ht w)]

/-- The complex heat average splits into its real and imaginary parts, which recombine to the
original field. -/
theorem ofReV_average_add_ofImV_average {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {t : ℝ}
    (ht : 0 < t) (F0 : UnforcedLeray.Space → CVec3) (hF : MemLp F0 p volume)
    (x : UnforcedLeray.Space) :
    ofReV (UnforcedLeray.Heat.average t (fun z => reV (F0 z)) x) +
      ofImV (UnforcedLeray.Heat.average t (fun z => imV (F0 z)) x) =
        UnforcedLeray.Heat.average t F0 x := by
  have hint : Integrable (fun w : UnforcedLeray.Space =>
      UnforcedLeray.Heat.kernel t w • F0 (x - w)) volume :=
    UnforcedLeray.B0418.heat_integrand_integrable ht Fact.out hp hF x
  have hR : Integrable (fun w : UnforcedLeray.Space =>
      UnforcedLeray.Heat.kernel t w • reV (F0 (x - w))) volume := by
    have h := reV.integrable_comp hint
    simpa only [map_smul] using h
  have hI : Integrable (fun w : UnforcedLeray.Space =>
      UnforcedLeray.Heat.kernel t w • imV (F0 (x - w))) volume := by
    have h := imV.integrable_comp hint
    simpa only [map_smul] using h
  unfold UnforcedLeray.Heat.average
  rw [← ContinuousLinearMap.integral_comp_comm ofReV hR,
    ← ContinuousLinearMap.integral_comp_comm ofImV hI,
    ← integral_add (ofReV.integrable_comp hR) (ofImV.integrable_comp hI)]
  congr 1
  funext w
  rw [map_smul, map_smul, ← smul_add, ofReV_reV_add_ofImV_imV]

theorem freeCPointwiseLe_proof : UnforcedLeray.Short.PartIIa.FreeCPointwiseLe := by
  unfold FreeCPointwiseLe
  intro p hp1 hp ν r F G hG
  have hc : 0 < Real.exp (r / 2) := Real.exp_pos _
  have hFm : MemLp (⇑F) p volume := Lp.memLp F
  have hA : (⇑(reV.compLpL p volume F) : UnforcedLeray.Space → UnforcedLeray.Space) =ᵐ[volume]
      fun z => reV (F z) :=
    reV.coeFn_compLpL (μ := (volume : Measure UnforcedLeray.Space)) (p := p) F
  have hB : (⇑(imV.compLpL p volume F) : UnforcedLeray.Space → UnforcedLeray.Space) =ᵐ[volume]
      fun z => imV (F z) :=
    imV.coeFn_compLpL (μ := (volume : Measure UnforcedLeray.Space)) (p := p) F
  rcases le_or_gt (ν * (Real.exp r - 1)) 0 with ht | ht
  · -- Case `t ≤ 0`: the heat flow is the identity, so both sides are `c |F(c y)|` a.e.
    have hA' := UnforcedLeray.SpatialScaling.ae_eq_comp_dilation hA hc.ne'
    have hB' := UnforcedLeray.SpatialScaling.ae_eq_comp_dilation hB hc.ne'
    have hG' := UnforcedLeray.SpatialScaling.ae_eq_comp_dilation hG hc.ne'
    filter_upwards [UnforcedLeray.B0421.coeFn_freeC hp ν r F,
      UnforcedLeray.B0418.coeFn_freeSemigroupLp hp ν r G, hA', hB', hG'] with y h1 h4 h2 h3 h5
    rw [h1, h4]
    simp only [UnforcedLeray.B0418.eq_free_stress_7, UnforcedLeray.Heat.flow_nonpos _ ht]
    rw [h2, h3, h5]
    simp [map_smul, ← smul_add, ofReV_reV_add_ofImV_imV, norm_smul, Real.norm_of_nonneg hc.le]
  · -- Case `t > 0`: the heat flow is a positive Gaussian average.
    have hAavg : UnforcedLeray.Heat.average (ν * (Real.exp r - 1))
        (⇑(reV.compLpL p volume F)) =
          UnforcedLeray.Heat.average (ν * (Real.exp r - 1)) (fun z => reV (F z)) :=
      UnforcedLeray.Heat.average_congr_ae hA _
    have hBavg : UnforcedLeray.Heat.average (ν * (Real.exp r - 1))
        (⇑(imV.compLpL p volume F)) =
          UnforcedLeray.Heat.average (ν * (Real.exp r - 1)) (fun z => imV (F z)) :=
      UnforcedLeray.Heat.average_congr_ae hB _
    have hGavg : UnforcedLeray.Heat.average (ν * (Real.exp r - 1)) (⇑G) =
          UnforcedLeray.Heat.average (ν * (Real.exp r - 1))
            (fun z => EuclideanSpace.single (0 : Fin 3) ‖F z‖) :=
      UnforcedLeray.Heat.average_congr_ae hG _
    filter_upwards [UnforcedLeray.B0421.coeFn_freeC hp ν r F,
      UnforcedLeray.B0418.coeFn_freeSemigroupLp hp ν r G] with y h1 h4
    rw [h1, h4]
    simp only [UnforcedLeray.B0418.eq_free_stress_7, UnforcedLeray.Heat.flow_pos _ ht]
    rw [hAavg, hBavg, hGavg]
    rw [map_smul, map_smul, ← smul_add,
      ofReV_average_add_ofImV_average hp ht (⇑F) hFm (Real.exp (r / 2) • y)]
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left (norm_average_le_single ht (⇑F) _) hc.le

end UnforcedLeray.Short.PartIIa
