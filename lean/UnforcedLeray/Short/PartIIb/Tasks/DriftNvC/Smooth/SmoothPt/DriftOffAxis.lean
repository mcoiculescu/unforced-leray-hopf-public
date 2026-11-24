import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2_2
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftOffAxis.Rep

/-!
# Part II-b, leaf `PartII-b:T08/1/2/2/1` (`NvCDriftOffAxis`)

Source: `the November 2 reference manuscript` 1912-1915.
Off the axis the chain rule along the line `τ ↦ (τ₀ + t, e^{-t/2} y₀)` gives
`(∂_τ - ½ y·∇) N_v b = N_v (s ∂_s b + b/2)`: the phase is constant along this line, `s` scales like
`e^t`, and `√s` like `e^{t/2}`, so the derivative at `t = 0` is `½ √s · b + s ∂_s b · √s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.DriftOff

open UnforcedLeray.PhaseSpace (CVec3)

/-- The line through `p` along `(1, -y/2)`: `τ ↦ τ₀ + t`, `y ↦ e^{-t/2} y`. -/
def offLine (p : ℝ × UnforcedLeray.Space) (t : ℝ) : ℝ × UnforcedLeray.Space :=
  (p.1 + t, Real.exp (-t / 2) • p.2)

/-- The chart point of the line: `s ↦ s e^t`, phase and transverse coordinate constant. -/
def offCurve (R : ℝ) (p : ℝ × UnforcedLeray.Space) (t : ℝ) : ℝ × (ℝ × ℝ) :=
  (UnforcedLeray.Axi.age R p.2 * Real.exp t,
    (UnforcedLeray.Axi.phase R p.1 p.2, UnforcedLeray.Axi.trans R p.2))

theorem age_offLine {R : ℝ} {y : UnforcedLeray.Space} (hy : y ∉ UnforcedLeray.Axi.axis) (t : ℝ) :
    UnforcedLeray.Axi.age R (Real.exp (-t / 2) • y) =
      UnforcedLeray.Axi.age R y * Real.exp t := by
  have hϱ := UnforcedLeray.Axi.ϱ_ne_zero hy
  have hE : Real.exp (-t) = 1 / Real.exp t := by rw [Real.exp_neg, one_div]
  have hμ2 : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]; ring_nf
  unfold UnforcedLeray.Axi.age
  rw [UnforcedLeray.Axi.ϱ_smul, abs_of_pos (Real.exp_pos _), mul_pow, hμ2, hE]
  field_simp

theorem phase_offLine {R : ℝ} (hR : R ≠ 0) {y : UnforcedLeray.Space}
    (hy : y ∉ UnforcedLeray.Axi.axis) (τ t : ℝ) :
    UnforcedLeray.Axi.phase R (τ + t) (Real.exp (-t / 2) • y) = UnforcedLeray.Axi.phase R τ y := by
  have ha := UnforcedLeray.Axi.age_pos hR hy
  unfold UnforcedLeray.Axi.phase
  rw [age_offLine hy, Real.log_mul ha.ne' (Real.exp_pos t).ne', Real.log_exp]
  ring

theorem trans_offLine {R : ℝ} (y : UnforcedLeray.Space) (t : ℝ) :
    UnforcedLeray.Axi.trans R (Real.exp (-t / 2) • y) = UnforcedLeray.Axi.trans R y := by
  have hμ : 0 < Real.exp (-t / 2) := Real.exp_pos _
  unfold UnforcedLeray.Axi.trans
  rw [UnforcedLeray.Axi.ϱ_smul, abs_of_pos hμ]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [show R * (Real.exp (-t / 2) * y 2) = Real.exp (-t / 2) * (R * y 2) by ring,
    mul_div_mul_left _ _ hμ.ne']

theorem chart_offLine {R : ℝ} (hR : R ≠ 0) {p : ℝ × UnforcedLeray.Space}
    (hp : p.2 ∉ UnforcedLeray.Axi.axis) (t : ℝ) :
    UnforcedLeray.Axi.chart R (offLine p t).1 (offLine p t).2 = offCurve R p t := by
  unfold offLine offCurve UnforcedLeray.Axi.chart
  simp only
  rw [age_offLine hp, phase_offLine hR hp, trans_offLine]

theorem sqrt_age_offLine {R : ℝ} {y : UnforcedLeray.Space} (hy : y ∉ UnforcedLeray.Axi.axis)
    (t : ℝ) :
    √(UnforcedLeray.Axi.age R (Real.exp (-t / 2) • y)) =
      √(UnforcedLeray.Axi.age R y) * Real.exp (t / 2) := by
  have hpos : 0 ≤ UnforcedLeray.Axi.age R y := by
    unfold UnforcedLeray.Axi.age; positivity
  have hsq : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [age_offLine hy, Real.sqrt_mul hpos, hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- The ring lift along the line, in terms of the complex meridional components. -/
theorem nvC_offLine {R : ℝ} (hR : R ≠ 0) (b : UnforcedLeray.Short.IIb.CProf)
    {p : ℝ × UnforcedLeray.Space} (hp : p.2 ∉ UnforcedLeray.Axi.axis) (t : ℝ) :
    UnforcedLeray.Short.IIb.NvC R b (offLine p t) =
      (√(UnforcedLeray.Axi.age R p.2) * Real.exp (t / 2)) •
        pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)
          (b (offCurve R p t)) := by
  rw [nvC_rep]
  have hline : (offLine p t).2 = Real.exp (-t / 2) • p.2 := rfl
  have hfst : (offLine p t).1 = p.1 + t := rfl
  rw [chart_offLine hR hp, hline, sqrt_age_offLine hp, UnforcedLeray.Axi.eR_smul (Real.exp_pos _)]
  rw [pairL_apply, smul_add]


theorem offCurve_zero (R : ℝ) (p : ℝ × UnforcedLeray.Space) :
    offCurve R p 0 = UnforcedLeray.Axi.chart R p.1 p.2 := by
  simp [offCurve, UnforcedLeray.Axi.chart]

/-- Derivative at `t = 0` of the ring lift along the line. -/
theorem hasDerivAt_nvC_offLine {R : ℝ} (hR : R ≠ 0) {b : UnforcedLeray.Short.IIb.CProf}
    (hbd : Differentiable ℝ b) {p : ℝ × UnforcedLeray.Space}
    (hp : p.2 ∉ UnforcedLeray.Axi.axis) :
    HasDerivAt (fun t : ℝ => UnforcedLeray.Short.IIb.NvC R b (offLine p t))
      ((√(UnforcedLeray.Axi.age R p.2) * (1 / 2 : ℝ)) •
          pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)
            (b (offCurve R p 0)) +
        √(UnforcedLeray.Axi.age R p.2) •
          pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)
            (fderiv ℝ b (offCurve R p 0) (UnforcedLeray.Axi.age R p.2, ((0 : ℝ), (0 : ℝ)))))
      0 := by
  have hfun : (fun t : ℝ => UnforcedLeray.Short.IIb.NvC R b (offLine p t)) =
      fun t : ℝ => (√(UnforcedLeray.Axi.age R p.2) * Real.exp (t / 2)) •
        pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)
          (b (offCurve R p t)) :=
    funext fun t => nvC_offLine hR b hp t
  rw [hfun]
  have hA : HasDerivAt (fun t : ℝ => √(UnforcedLeray.Axi.age R p.2) * Real.exp (t / 2))
      (√(UnforcedLeray.Axi.age R p.2) * (1 / 2 : ℝ)) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).div_const 2).exp).const_mul
      (√(UnforcedLeray.Axi.age R p.2))
    exact h.congr_deriv (by simp)
  have ha : 0 < UnforcedLeray.Axi.age R p.2 := UnforcedLeray.Axi.age_pos hR hp
  have hcurve : HasDerivAt (offCurve R p)
      ((UnforcedLeray.Axi.age R p.2, ((0 : ℝ), (0 : ℝ))) : ℝ × (ℝ × ℝ)) 0 := by
    unfold offCurve
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_const _ _))
    simpa using (Real.hasDerivAt_exp (0 : ℝ)).const_mul (UnforcedLeray.Axi.age R p.2)
  have hbF : HasFDerivAt b (fderiv ℝ b (offCurve R p 0)) (offCurve R p 0) :=
    (hbd _).hasFDerivAt
  have hB := hbF.comp_hasDerivAt (0 : ℝ) hcurve
  have hL := ((pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hB
  exact (hA.smul hL).congr_deriv (by simp [add_comm])

/-- The `ℝ`-action on the `ℂ`-linear map `pairL` through the real scalar `a`. -/
theorem pairL_smul_real (X E : CVec3) (a : ℝ) (v : UnforcedLeray.Short.IIb.CMerid) :
    pairL X E (a • v) = a • pairL X E v :=
  (pairL X E).map_smul_of_tower a v

theorem half_smul_cvec (w : CVec3) : (1 / 2 : ℂ) • w = (1 / 2 : ℝ) • w := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num

theorem pairL_half (X E : CVec3) (v : UnforcedLeray.Short.IIb.CMerid) :
    pairL X E ((1 / 2 : ℂ) • v) = (1 / 2 : ℝ) • pairL X E v := by
  rw [map_smul, half_smul_cvec]

theorem cdir_zero_smul (a : ℝ) :
    ((a, ((0 : ℝ), (0 : ℝ))) : ℝ × (ℝ × ℝ)) = a • UnforcedLeray.Short.IIb.cdir 0 := by
  simp [UnforcedLeray.Short.IIb.cdir]

end UnforcedLeray.Short.IIb.DriftOff

open UnforcedLeray.Short.IIb.DriftOff

theorem nvCDriftOffAxis_proof : UnforcedLeray.Short.IIb.NvCDriftOffAxis := by
  intro c ε b hc hε hb p hp
  obtain ⟨hbC, _, _⟩ := hb
  have hbd : Differentiable ℝ b := hbC.differentiable (by simp)
  have hR : ε⁻¹ ≠ 0 := (inv_pos.2 hε).ne'
  have hγ : HasDerivAt (offLine p) ((1 : ℝ), (-(1 / 2 : ℝ)) • p.2) 0 := by
    unfold offLine
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using (hasDerivAt_id (0 : ℝ)).const_add p.1
    · have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (-(1 / 2 : ℝ)) 0 := by
        have h := (((hasDerivAt_id (0 : ℝ)).neg).div_const 2).exp
        exact h.congr_deriv (by norm_num)
      exact h1.smul_const p.2
  have hγ0 : offLine p 0 = p := by simp [offLine]
  have hGd : HasFDerivAt (UnforcedLeray.Short.IIb.NvC ε⁻¹ b)
      (fderiv ℝ (UnforcedLeray.Short.IIb.NvC ε⁻¹ b) p) (offLine p 0) := by
    rw [hγ0]
    exact (nvC_diffAt hR hbd hp).hasFDerivAt
  have hline := hGd.comp_hasDerivAt (0 : ℝ) hγ
  have hder := hasDerivAt_nvC_offLine hR hbd hp
  have hkey := hline.unique hder
  have hlin : UnforcedLeray.PhaseSpace.dτ (UnforcedLeray.Short.IIb.NvC ε⁻¹ b) p -
      (1 / 2 : ℝ) • UnforcedLeray.PhaseSpace.radialT (UnforcedLeray.Short.IIb.NvC ε⁻¹ b) p =
      fderiv ℝ (UnforcedLeray.Short.IIb.NvC ε⁻¹ b) p ((1 : ℝ), (-(1 / 2 : ℝ)) • p.2) := by
    have hy : ∑ j : Fin 3, p.2 j • UnforcedLeray.coordinateVector j = p.2 := by
      ext i
      fin_cases i <;> simp [UnforcedLeray.coordinateVector, Fin.sum_univ_three, EuclideanSpace.single_apply]
    have hsnd : ((0 : ℝ), p.2) = ∑ j : Fin 3, p.2 j • ((0 : ℝ), UnforcedLeray.coordinateVector j) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · rw [Prod.snd_sum]
        simp only [Prod.smul_snd]
        exact hy.symm
    have hv : ((1 : ℝ), (-(1 / 2 : ℝ)) • p.2) =
        ((1 : ℝ), (0 : UnforcedLeray.Space)) + (-(1 / 2 : ℝ)) • ((0 : ℝ), p.2) := by
      refine Prod.ext ?_ ?_ <;> simp
    simp only [UnforcedLeray.PhaseSpace.dτ, UnforcedLeray.PhaseSpace.radialT,
      UnforcedLeray.PhaseSpace.dy]
    rw [hv, map_add, map_smul, hsnd, map_sum]
    simp only [map_smul]
    module
  have hRHS : UnforcedLeray.Short.IIb.NvC ε⁻¹
      (fun x : ℝ × ℝ × ℝ => x.1 • fderiv ℝ b x (UnforcedLeray.Short.IIb.cdir 0) + (1 / 2 : ℂ) • b x)
      p = (√(UnforcedLeray.Axi.age ε⁻¹ p.2) * (1 / 2 : ℝ)) •
          pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)
            (b (offCurve ε⁻¹ p 0)) +
        √(UnforcedLeray.Axi.age ε⁻¹ p.2) •
          pairL (realCL (UnforcedLeray.Axi.eR p.2)) (realCL UnforcedLeray.Axi.e3)
            (fderiv ℝ b (offCurve ε⁻¹ p 0) (UnforcedLeray.Axi.age ε⁻¹ p.2, ((0 : ℝ), (0 : ℝ)))) := by
    rw [offCurve_zero, nvC_rep, ← pairL_apply]
    have hc0 : (UnforcedLeray.Axi.chart ε⁻¹ p.1 p.2).1 = UnforcedLeray.Axi.age ε⁻¹ p.2 := rfl
    simp only [hc0, map_add, pairL_smul_real, pairL_half, cdir_zero_smul,
      ContinuousLinearMap.map_smul, smul_add, smul_smul]
    module
  rw [hlin, hkey, hRHS]

#print axioms nvCDriftOffAxis_proof
