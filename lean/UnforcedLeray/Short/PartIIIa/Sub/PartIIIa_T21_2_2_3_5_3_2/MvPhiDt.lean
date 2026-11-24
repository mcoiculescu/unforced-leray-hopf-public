import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.B_ChiC1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv.AgeDeriv

/-!
# `PartIII-a:T21/2/2/3/5/3/2` leaf `MvPhiDt`: chain rule for the moving adjoint

Source of record: `the November 2 reference manuscript` (SP) lines 2854-2862
(`w(s,x) = a⁻²W(z,x/√a)`, `dr/dζ = -a²`), 2857. With `a = clockA ν r`, `r = revAge ν s ζ`,
`Φ = mvPhi`, `∂_ζΦ(y) = βΦ(y) - (β/2) y·∇Φ(y) - a ∂_rφ(r, √a y)`, `β = νa`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-- Linear decomposition of the spatial part of `∂` of the joint field. -/
theorem mvPhiDt_fderiv_pair (ψ : ℝ → ℝ × ℝ → ℂ) {a b ρ : ℝ}
    (hj : ContDiffOn ℝ ∞ (jF ψ) (Ioo a b ×ˢ univ)) (hρ : ρ ∈ Ioo a b) (x v : ℝ × ℝ) :
    fderiv ℝ (jF ψ) (ρ, x) ((0 : ℝ), v) =
      (v.1 : ℂ) * pdCx 0 (ψ ρ) x + (v.2 : ℂ) * pdCx 1 (ψ ρ) x := by
  have hdec : ((0 : ℝ), v) = v.1 • ((0 : ℝ), B0579.dir 0) + v.2 • ((0 : ℝ), B0579.dir 1) := by
    ext <;> simp [B0579.dir]
  rw [hdec, map_add, map_smul, map_smul, ← pdCx_slice_eq hj hρ 0 x, ← pdCx_slice_eq hj hρ 1 x]
  simp only [Complex.real_smul]

theorem mvPhiDt (m : ℝ) : MvPhiDt m := by
  unfold MvPhiDt
  intro ν tr t s φ ζ hflow
  have hfl := hflow
  obtain ⟨_, ha⟩ := adjFlowAt_age hflow
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, hζ⟩ := hflow
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hφ : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hF.smooth _ (Ioo_subset_Ico_self hr)
  have hJ : ContDiffOn ℝ ∞ (jF φ) (Ioo t s ×ˢ univ) :=
    hF.jointSmooth.mono (prod_mono Ioo_subset_Ico_self subset_rfl)
  have hadj : adjDt t s φ (revAge ν s ζ) =
      fun x => fderiv ℝ (jF φ) (revAge ν s ζ, x) ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun x => adjDt_eq_fderiv hJ hr x
  have ha0 : clockA ν (revAge ν s ζ) ≠ 0 := ha.ne'
  refine ⟨?_, fun y => ?_⟩
  · rw [hadj]
    intro x
    have hD1 : DifferentiableAt ℝ (fderiv ℝ (jF φ)) (revAge ν s ζ, x) :=
      ((contDiffOn_fderiv_jF hJ).contDiffAt
        (IsOpen.mem_nhds (isOpen_strip t s) ⟨hr, mem_univ x⟩)).differentiableAt (by simp)
    have hι : DifferentiableAt ℝ (fun x' : ℝ × ℝ => (revAge ν s ζ, x')) x :=
      (differentiableAt_const _).prodMk differentiableAt_id
    have h1 : DifferentiableAt ℝ (fun x' : ℝ × ℝ => fderiv ℝ (jF φ) (revAge ν s ζ, x')) x :=
      hD1.comp x hι
    exact h1.clm_apply (differentiableAt_const _)
  · have hR : HasDerivAt (fun ζ' => revAge ν s ζ') (-(clockA ν (revAge ν s ζ)) ^ 2) ζ :=
      revAgeDeriv m ν tr t s φ ζ hfl
    have hA : HasDerivAt (fun ζ' => clockA ν (revAge ν s ζ'))
        (ν * (-(clockA ν (revAge ν s ζ)) ^ 2)) ζ :=
      (hR.const_mul ν).const_add 1
    have hsq : HasDerivAt (fun ζ' => Real.sqrt (clockA ν (revAge ν s ζ')))
        (ν * (-(clockA ν (revAge ν s ζ)) ^ 2) / (2 * Real.sqrt (clockA ν (revAge ν s ζ)))) ζ :=
      hA.sqrt ha0
    have hinv : HasDerivAt (fun ζ' => (clockA ν (revAge ν s ζ'))⁻¹)
        (-(ν * (-(clockA ν (revAge ν s ζ)) ^ 2)) / clockA ν (revAge ν s ζ) ^ 2) ζ :=
      hA.inv ha0
    have hinvC : HasDerivAt (fun ζ' => (((clockA ν (revAge ν s ζ'))⁻¹ : ℝ) : ℂ))
        ((((-(ν * (-(clockA ν (revAge ν s ζ)) ^ 2)) / clockA ν (revAge ν s ζ) ^ 2 : ℝ)) : ℂ)) ζ :=
      hinv.ofReal_comp
    have hγ : HasDerivAt (fun ζ' => (revAge ν s ζ', Real.sqrt (clockA ν (revAge ν s ζ')) • y))
        ((-(clockA ν (revAge ν s ζ)) ^ 2),
          (ν * (-(clockA ν (revAge ν s ζ)) ^ 2) / (2 * Real.sqrt (clockA ν (revAge ν s ζ)))) • y) ζ :=
      hR.prodMk (hsq.smul_const y)
    have hJd : HasFDerivAt (jF φ)
        (fderiv ℝ (jF φ) (revAge ν s ζ, Real.sqrt (clockA ν (revAge ν s ζ)) • y))
        (revAge ν s ζ, Real.sqrt (clockA ν (revAge ν s ζ)) • y) :=
      ((contDiffAt_jF hJ hr _).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hJd.comp_hasDerivAt ζ hγ
    have hprod := hinvC.mul hcomp
    -- the linear part of the derivative of the joint field
    have hlin : fderiv ℝ (jF φ) (revAge ν s ζ, Real.sqrt (clockA ν (revAge ν s ζ)) • y)
        (-(clockA ν (revAge ν s ζ)) ^ 2,
          (ν * (-(clockA ν (revAge ν s ζ)) ^ 2) / (2 * Real.sqrt (clockA ν (revAge ν s ζ)))) • y) =
        ((-(clockA ν (revAge ν s ζ)) ^ 2 : ℝ) : ℂ) *
            adjDt t s φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) +
          ((ν * (-(clockA ν (revAge ν s ζ)) ^ 2) / (2 * Real.sqrt (clockA ν (revAge ν s ζ))) : ℝ) : ℂ) *
            ((y.1 : ℂ) * pdCx 0 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) +
              (y.2 : ℂ) * pdCx 1 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)) := by
      have hdec : ((-(clockA ν (revAge ν s ζ)) ^ 2),
          (ν * (-(clockA ν (revAge ν s ζ)) ^ 2) / (2 * Real.sqrt (clockA ν (revAge ν s ζ)))) • y) =
          (-(clockA ν (revAge ν s ζ)) ^ 2) • ((1 : ℝ), (0 : ℝ × ℝ)) +
            ((0 : ℝ), (ν * (-(clockA ν (revAge ν s ζ)) ^ 2) / (2 * Real.sqrt (clockA ν (revAge ν s ζ)))) • y) := by
        ext <;> simp
      rw [hdec, map_add, map_smul, ← adjDt_eq_fderiv hJ hr,
        mvPhiDt_fderiv_pair φ hJ hr]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    have hφv : jF φ (revAge ν s ζ, Real.sqrt (clockA ν (revAge ν s ζ)) • y) =
        ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) * mvPhi ν φ s ζ y := by
      have hc : ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) * (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha0, Complex.ofReal_one]
      have e : mvPhi ν φ s ζ y = (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) *
          φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) := rfl
      show φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) = _
      rw [e, ← mul_assoc, hc, one_mul]
    have hP : ∀ k : Fin 2, pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) =
        ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) * pdCx k (mvPhi ν φ s ζ) y := by
      intro k
      have h : pdCx k (mvPhi ν φ s ζ) y =
          (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) *
            pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) :=
        pdCx_movingPhi ν φ (revAge ν s ζ) hφ k y
      have hk := sqrt_mul_sqrt_inv_mul _ ha
      linear_combination (-((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ)) * h +
        (-(pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y))) * hk
    refine hprod.congr_deriv ?_
    simp only [Function.comp_apply]
    rw [hlin, hφv, hP 0, hP 1]
    unfold mvBeta radC
    generalize hσ : Real.sqrt (clockA ν (revAge ν s ζ)) = σ
    have hσpos : 0 < σ := by
      rw [← hσ]
      exact Real.sqrt_pos.mpr ha
    have hσ2 : σ ^ 2 = clockA ν (revAge ν s ζ) := by
      rw [← hσ]
      exact Real.sq_sqrt ha.le
    rw [← hσ2]
    have hσc : ((σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσpos.ne'
    push_cast
    field_simp
    ring

end UnforcedLeray.Short.IIIa.AdjE1
