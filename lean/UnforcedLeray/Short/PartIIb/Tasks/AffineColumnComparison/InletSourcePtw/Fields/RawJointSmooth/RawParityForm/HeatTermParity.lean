import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HeatTermSmooth

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Directional derivative along a line through a differentiable point (helper). -/
theorem heatTermParity_fderiv_line {f : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)}
    (hf : DifferentiableAt ℝ f y) (v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ f y v = deriv (fun t : ℝ => f (y + t • v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h2 : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (x := (0 : ℝ)) h1).deriv.symm

/-- **The heat terms have the stated parity coefficients** (`HeatTermParity`; SP 1310-1313,
SP 1267-1268). -/
theorem heatTermParity : UnforcedLeray.Short.IIb.HeatTermParity := by
  intro ν R hν hR j x hx
  have hsmooth := heatTermSmooth ν hν j
  have hpos : (0 : ℝ) < R := hR
  have hRne : R ≠ 0 := hR.ne'
  have hsqw : 0 < Real.sqrt x.2.1 := Real.sqrt_pos.mpr hx
  have hsqne : Real.sqrt x.2.1 ≠ 0 := hsqw.ne'
  have hwne : x.2.1 ≠ 0 := hx.ne'
  set y := UnforcedLeray.Short.IIb.parChart R x with hy
  have hy_pos : 0 < y.1 := (parChart_fst_pos hR hx).1
  have hdiff : DifferentiableAt ℝ (heatTerm ν j) y :=
    differentiableAt_of_contDiffOn_pos hsmooth (parChart_fst_pos hR hx)
  have hyS : y.1 = R ^ 2 / x.2.1 := by rw [hy]; rfl
  have hy2 : y.2.2 = R * x.2.2 / Real.sqrt x.2.1 := by rw [hy]; rfl
  -- the heat kernel at age `ν s` is the Gaussian at age `s`
  have hfun : ∀ t : ℝ, UnforcedLeray.Short.PartI.heatKernel1 (ν * t) =
      UnforcedLeray.B0191.heatKernel ν t := by
    intro t
    funext η
    simp only [UnforcedLeray.Short.PartI.heatKernel1, UnforcedLeray.B0191.heatKernel, mul_assoc]
  have hTy : ∀ z : ℝ × (ℝ × ℝ), heatTerm ν j z =
      iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν z.1) z.2.2 := by
    intro z
    unfold heatTerm
    rw [hfun]
  -- the three partial derivatives of the heat term at `y`
  have hdQ : UnforcedLeray.Axi.dQ (heatTerm ν j) y = 0 := by
    unfold UnforcedLeray.Axi.dQ
    rw [heatTermParity_fderiv_line hdiff]
    have hc : ∀ t : ℝ, heatTerm ν j (y + t • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) =
        heatTerm ν j y := by
      intro t
      rw [hTy, hTy]
      simp
    simp only [hc]
    exact deriv_const _ _
  have hdEta : UnforcedLeray.Axi.dEta (heatTerm ν j) y =
      iteratedDeriv (2 * j + 1) (UnforcedLeray.B0191.heatKernel ν y.1) y.2.2 := by
    unfold UnforcedLeray.Axi.dEta
    rw [heatTermParity_fderiv_line hdiff]
    have hfn : (fun t : ℝ => heatTerm ν j (y + t • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
        fun t : ℝ => iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν y.1) (y.2.2 + t) := by
      funext t
      rw [hTy]
      simp
    have hcomp : deriv (fun t : ℝ => iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν y.1)
          (y.2.2 + t)) 0 =
        deriv (iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν y.1)) (y.2.2 + 0) :=
      deriv_comp_const_add (f := iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν y.1))
        (a := y.2.2) (x := 0)
    rw [hfn, hcomp, add_zero, iteratedDeriv_succ]
  have hdS : UnforcedLeray.Axi.dS (heatTerm ν j) y =
      deriv (fun t : ℝ => iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν t) y.2.2) y.1 := by
    unfold UnforcedLeray.Axi.dS
    rw [heatTermParity_fderiv_line hdiff]
    have hfn : (fun t : ℝ => heatTerm ν j (y + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))) =
        fun t : ℝ => iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν (y.1 + t)) y.2.2 := by
      funext t
      rw [hTy]
      simp
    have hcomp : deriv (fun t : ℝ => iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν (y.1 + t))
          y.2.2) 0 =
        deriv (fun s : ℝ => iteratedDeriv (2 * j) (UnforcedLeray.B0191.heatKernel ν s) y.2.2)
          (y.1 + 0) :=
      deriv_comp_const_add (f := fun s : ℝ => iteratedDeriv (2 * j)
        (UnforcedLeray.B0191.heatKernel ν s) y.2.2) (a := y.1) (x := 0)
    rw [hfn, hcomp, add_zero]
  -- the age Euler identity `η ∂_η + 2 s ∂_s` on the heat term
  have hK' : y.2.2 * UnforcedLeray.Axi.dEta (heatTerm ν j) y +
      2 * y.1 * UnforcedLeray.Axi.dS (heatTerm ν j) y =
      -(2 * (j : ℝ) + 1) * heatTerm ν j y := by
    rw [hdEta, hdS, hTy]
    have hK := UnforcedLeray.B0191.K_iteratedDeriv_heatKernel ν (2 * j) hy_pos y.2.2
    rw [iteratedDeriv_succ]
    push_cast at hK
    linear_combination hK
  -- the ring stream profile at the chart point
  have hH : UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j) y 1 =
      R⁻¹ * ((2 * (j : ℝ) + 2) * heatTerm ν j y) := by
    rw [UnforcedLeray.Short.IIb.ringStreamProfile_apply_one, hdQ, zero_add]
    congr 1
    linear_combination -hK'
  -- the chart point: `√s = R/√w` and `(√s)⁻¹ η = z`
  have hsy : Real.sqrt y.1 = R / Real.sqrt x.2.1 := by
    rw [hyS, Real.sqrt_div' _ hx.le, Real.sqrt_sq hpos.le]
  have hinv : (Real.sqrt y.1)⁻¹ = Real.sqrt x.2.1 / R := by
    rw [hsy, inv_div]
  have hz : (Real.sqrt y.1)⁻¹ * y.2.2 = x.2.2 := by
    rw [hinv, hy2]
    field_simp
  have hpw : ∀ n : ℕ, (Real.sqrt x.2.1) ^ (2 * n) = x.2.1 ^ n := fun n => by
    rw [pow_mul, Real.sq_sqrt hx.le]
  have hodd : ∀ n : ℕ, (Real.sqrt x.2.1) ^ (2 * n + 1) = x.2.1 ^ n * Real.sqrt x.2.1 :=
    fun n => by
      rw [pow_succ, hpw n]
  -- self-similarity of the heat terms and of their `η`-derivatives
  have hT : heatTerm ν j y = (Real.sqrt y.1)⁻¹ ^ (2 * j + 1) *
      UnforcedLeray.B0191.profileDeriv ν (2 * j) ((Real.sqrt y.1)⁻¹ * y.2.2) := by
    have h := UnforcedLeray.B0191.heatDeriv_selfSimilar ν (2 * j) y.2.2 hy_pos
    unfold UnforcedLeray.B0191.heatDeriv at h
    rw [hTy]
    exact h
  have hA : iteratedDeriv (2 * j + 1) (UnforcedLeray.B0191.heatKernel ν y.1) y.2.2 =
      (Real.sqrt y.1)⁻¹ ^ (2 * (j + 1)) *
        UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) ((Real.sqrt y.1)⁻¹ * y.2.2) := by
    have h := UnforcedLeray.B0191.heatDeriv_selfSimilar ν (2 * j + 1) y.2.2 hy_pos
    unfold UnforcedLeray.B0191.heatDeriv at h
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e]
    exact h
  refine ⟨?_, ?_⟩
  · show R / x.2.1 * UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j) y 0 =
      heatParG ν R j x
    rw [UnforcedLeray.Short.IIb.ringStreamProfile_apply_zero, hdEta, hA, hz, hinv,
      div_pow, hpw (j + 1)]
    unfold heatParG
    field_simp
    ring
  · show R / Real.sqrt x.2.1 * UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j) y 1 =
      heatParH ν R j x
    rw [hH, hT, hz, hinv, div_pow, hodd j]
    unfold heatParH
    field_simp

end UnforcedLeray.Short.IIb
