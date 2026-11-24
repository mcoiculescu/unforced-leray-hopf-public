import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Scale

/-!
# `PartIII-a:T21/2/2/2/2/4/1`: the pointwise chain rule `ReyPointwise` (SP 2860, 2945-2946)

Work in progress: generic calculus helpers for `ReyPointwise`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- `d/dζ ‖f ζ‖² = 2 Re(conj f · f')`. -/
theorem hasDerivAt_norm_sq_c {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun u => ‖f u‖ ^ 2) (2 * (starRingEnd ℂ (f t) * f').re) t := by
  have h := hf.norm_sq
  convert h using 1
  rw [Complex.inner, mul_comm (starRingEnd ℂ (f t)) f']

/-- Linear maps on `ℝ × (ℝ × ℝ)` split along the basis. -/
theorem clm_triple_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ × (ℝ × ℝ) →L[ℝ] E) (α β1 β2 : ℝ) :
    L (α, (β1, β2)) = α • L (1, (0, 0)) + β1 • L (0, (1, 0)) + β2 • L (0, (0, 1)) := by
  have h : ((α, (β1, β2)) : ℝ × (ℝ × ℝ)) =
      α • ((1, (0, 0)) : ℝ × (ℝ × ℝ)) + β1 • ((0, (1, 0)) : ℝ × (ℝ × ℝ)) +
        β2 • ((0, (0, 1)) : ℝ × (ℝ × ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_add, map_smul, map_smul, map_smul]

/-- The fixed-`r` slice of the joint adjoint is differentiable at interior ages. -/
theorem diffAt_joint {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ioo t s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) := by
  have hn : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, x) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩
  have hn2 : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, x) :=
    Filter.mem_of_superset hn (Set.prod_mono Ioo_subset_Ico_self subset_rfl)
  exact (hj.contDiffAt hn2).differentiableAt (by simp)

/-- The `x`-slice derivative of the joint adjoint is the spatial derivative of `φ r`. -/
theorem fderiv_joint_snd {φ : ℝ → ℝ × ℝ → ℂ} {r : ℝ} (x : ℝ × ℝ)
    (hP : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x)) (v : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) (0, v) = fderiv ℝ (φ r) x v := by
  have hc : HasFDerivAt (fun z : ℝ × ℝ => ((r, z) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
  have hcomp := hP.hasFDerivAt.comp x hc
  have hfun : (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) ∘ (fun z : ℝ × ℝ => ((r, z) : ℝ × (ℝ × ℝ))) =
      φ r := rfl
  rw [hfun] at hcomp
  rw [hcomp.fderiv]
  simp


/-- Chain rule along a curve in `ℝ × (ℝ × ℝ)` for a `DifferentiableAt` map. -/
theorem hasDerivAt_comp_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × (ℝ × ℝ) → E) (p : ℝ × (ℝ × ℝ)) (hF : DifferentiableAt ℝ F p)
    (γ : ℝ → ℝ × (ℝ × ℝ)) (γ' : ℝ × (ℝ × ℝ)) (ζ : ℝ)
    (hγ : HasDerivAt γ γ' ζ) (hp : γ ζ = p) :
    HasDerivAt (fun ζ' => F (γ ζ')) (fderiv ℝ F p γ') ζ := by
  have hl : HasFDerivAt F (fderiv ℝ F p) (γ ζ) := by
    rw [hp]; exact hF.hasFDerivAt
  exact hl.comp_hasDerivAt ζ hγ

/-- The second-slot derivative of a map on `ℝ × (ℝ × ℝ)` is the derivative of its slice. -/
theorem fderiv_snd_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × (ℝ × ℝ) → E) (r : ℝ) (x : ℝ × ℝ) (hF : DifferentiableAt ℝ F (r, x)) (v : ℝ × ℝ) :
    fderiv ℝ F (r, x) (0, v) = fderiv ℝ (fun z => F (r, z)) x v := by
  have hc : HasFDerivAt (fun z : ℝ × ℝ => ((r, z) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
  have hcomp := hF.hasFDerivAt.comp x hc
  have e : fderiv ℝ (fun z => F (r, z)) x = (fderiv ℝ F (r, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) :=
    hcomp.fderiv
  rw [e]
  simp

/-- Joint differentiability of the periodic weight at a point with nonzero cell length. -/
theorem diffAt_pw (m : ℝ) (q : ℝ × (ℝ × ℝ)) (hd : q.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) q := by
  unfold periodicWeight
  apply DifferentiableAt.rpow_const
  · fun_prop (disch := assumption)
  · left
    positivity

/-- The algebra of the moving-point derivative `Y' = y/(2θ)` (SP 2860). -/
theorem alg_beta (ν X a q : ℝ) (hq0 : 0 < q) (hq2 : q ^ 2 = a) :
    (0 * q - X * (ν * -a ^ 2 / (2 * q))) / q ^ 2 = (2 * (ν * a)⁻¹)⁻¹ * (X / q) := by
  subst hq2
  field_simp
  ring

/-- The cell-length chain rule for the periodic weight on the moving cell, with the moving point
`Y(ζ) = (X₁/√a, X₂/√a)`, `a = clockA ν (revAge ν s ζ)`. -/
theorem pw_chain (m ν c s ζ X1 X2 : ℝ) (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) (hζ0 : 0 < ζ)
    (ha : 0 < clockA ν (revAge ν s ζ)) :
    HasDerivAt (fun u => periodicWeight (-m) (revCell ν c s u)
        (X1 / Real.sqrt (clockA ν (revAge ν s u)), X2 / Real.sqrt (clockA ν (revAge ν s u))))
      (revCell ν c s ζ / (2 * revTheta ν s ζ) *
          wDd m (revCell ν c s ζ) (X1 / Real.sqrt (clockA ν (revAge ν s ζ)),
            X2 / Real.sqrt (clockA ν (revAge ν s ζ))) +
        (2 * revTheta ν s ζ)⁻¹ *
          wDil m (revCell ν c s ζ) (X1 / Real.sqrt (clockA ν (revAge ν s ζ)),
            X2 / Real.sqrt (clockA ν (revAge ν s ζ)))) ζ := by
  have hrd := reyRevAge_hasDeriv hν hs hζ0
  have hac : HasDerivAt (fun u => clockA ν (revAge ν s u))
      (ν * -(clockA ν (revAge ν s ζ)) ^ 2) ζ := (hrd.const_mul ν).const_add 1
  have hsq := hac.sqrt ha.ne'
  have hcell := reyRevCell_hasDeriv (c := c) hν hs hζ0
  have hsa : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.mpr ha
  have hY1 := (hasDerivAt_const ζ X1).div hsq hsa.ne'
  have hY2 := (hasDerivAt_const ζ X2).div hsq hsa.ne'
  have hγ := hcell.prodMk (hY1.prodMk hY2)
  have hdne : revCell ν c s ζ ≠ 0 := by
    unfold revCell cellLen
    exact (div_pos hc hsa).ne'
  have hF := diffAt_pw m (revCell ν c s ζ, (X1 / Real.sqrt (clockA ν (revAge ν s ζ)),
    X2 / Real.sqrt (clockA ν (revAge ν s ζ)))) hdne
  set d := revCell ν c s ζ with hd_def
  set Y : ℝ × ℝ := (X1 / Real.sqrt (clockA ν (revAge ν s ζ)),
    X2 / Real.sqrt (clockA ν (revAge ν s ζ))) with hY_def
  have h := hasDerivAt_comp_pair (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2)
    (d, Y) hF _ _ ζ hγ rfl
  have hdY1 : HasDerivAt (fun d' => periodicWeight (-m) d' Y) (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) (d, Y) (1, (0, 0))) d :=
    hasDerivAt_comp_pair (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) (d, Y) hF
      (fun d' => (d', Y)) (1, (0, 0)) d ((hasDerivAt_id' d).prodMk (hasDerivAt_const d Y)) rfl
  have e1 : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) (d, Y) (1, (0, 0)) =
      wDd m d Y := hdY1.deriv.symm
  have e2 : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) (d, Y) (0, (1, 0)) =
      B0579.pd 0 (periodicWeight (-m) d) Y :=
    fderiv_snd_gen (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) d Y hF (1, 0)
  have e3 : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) (d, Y) (0, (0, 1)) =
      B0579.pd 1 (periodicWeight (-m) d) Y :=
    fderiv_snd_gen (fun p : ℝ × (ℝ × ℝ) => periodicWeight (-m) p.1 p.2) d Y hF (0, 1)
  rw [clm_triple_apply, e1, e2, e3] at h
  refine h.congr_deriv ?_
  have hb1 := alg_beta ν X1 _ _ hsa (Real.sq_sqrt ha.le)
  have hb2 := alg_beta ν X2 _ _ hsa (Real.sq_sqrt ha.le)
  have hθ : revTheta ν s ζ = (ν * clockA ν (revAge ν s ζ))⁻¹ := rfl
  rw [hb1, hb2, hθ]
  simp only [smul_eq_mul, wDil, hY_def]
  ring

/-- The fixed-`x` derivative of `r ↦ φ(r, x)` along the reverse age (SP 2860, 2945). -/
theorem phi_fix_deriv {ν s ζ t : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (hs : 0 ≤ s)
    (hζ0 : 0 < ζ) (hr : revAge ν s ζ ∈ Ioo t s)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) (x : ℝ × ℝ) :
    HasDerivAt (fun u => φ (revAge ν s u) x)
      (-(clockA ν (revAge ν s ζ)) ^ 2 *
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ, x) (1, (0, 0))) ζ := by
  have hγ : HasDerivAt (fun u => (revAge ν s u, x)) (-(clockA ν (revAge ν s ζ)) ^ 2, (0, 0)) ζ :=
    (reyRevAge_hasDeriv hν hs hζ0).prodMk (hasDerivAt_const ζ x)
  have h := hasDerivAt_comp_pair (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ, x)
    (diffAt_joint hj hr x) _ _ ζ hγ rfl
  rw [clm_triple_apply] at h
  refine h.congr_deriv ?_
  simp [Complex.real_smul]

/-- The algebra `sq·a⁻¹ + (νa/2)(a⁻¹√a) = 0` for `sq = ν(-a²)/(2√a)`. -/
theorem alg_psi (ν a q : ℝ) (hq : 0 < q) (hq2 : q ^ 2 = a) :
    ν * -a ^ 2 / (2 * q) * a⁻¹ + ν * a / 2 * (a⁻¹ * q) = 0 := by
  subst hq2
  field_simp
  ring

/-- The moving derivative `revDt` in terms of the fixed-`x` data (SP 2860, 2945-2946). -/
theorem revDt_formula {ν s ζ t : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (hs : 0 ≤ s)
    (hζ0 : 0 < ζ) (hr : revAge ν s ζ ∈ Ioo t s)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) (y : ℝ × ℝ) :
    revDt ν φ s ζ y =
      ((ν : ℝ) : ℂ) * φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) +
      ((((clockA ν (revAge ν s ζ))⁻¹ : ℝ)) : ℂ) *
        ((-(clockA ν (revAge ν s ζ)) ^ 2 : ℝ) : ℂ) *
          fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
            (1, (0, 0)) +
      ((((clockA ν (revAge ν s ζ))⁻¹ : ℝ)) : ℂ) *
        ((ν * -(clockA ν (revAge ν s ζ)) ^ 2 / (2 * Real.sqrt (clockA ν (revAge ν s ζ))) * y.1 : ℝ) : ℂ) *
          pdCx 0 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
            Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) +
      ((((clockA ν (revAge ν s ζ))⁻¹ : ℝ)) : ℂ) *
        ((ν * -(clockA ν (revAge ν s ζ)) ^ 2 / (2 * Real.sqrt (clockA ν (revAge ν s ζ))) * y.2 : ℝ) : ℂ) *
          pdCx 1 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
            Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) := by
  have hrd := reyRevAge_hasDeriv hν hs hζ0
  have ha : 0 < clockA ν (revAge ν s ζ) := chgClockA_pos hν hs hζ0
  have hac : HasDerivAt (fun u => clockA ν (revAge ν s u))
      (ν * -(clockA ν (revAge ν s ζ)) ^ 2) ζ := (hrd.const_mul ν).const_add 1
  have hsq := hac.sqrt ha.ne'
  have hγ : HasDerivAt (fun u => (revAge ν s u, (Real.sqrt (clockA ν (revAge ν s u)) * y.1,
      Real.sqrt (clockA ν (revAge ν s u)) * y.2)))
      (-(clockA ν (revAge ν s ζ)) ^ 2, (ν * -(clockA ν (revAge ν s ζ)) ^ 2 /
        (2 * Real.sqrt (clockA ν (revAge ν s ζ))) * y.1,
        ν * -(clockA ν (revAge ν s ζ)) ^ 2 / (2 * Real.sqrt (clockA ν (revAge ν s ζ))) * y.2)) ζ :=
    hrd.prodMk ((hsq.mul_const y.1).prodMk (hsq.mul_const y.2))
  have hPγ := hasDerivAt_comp_pair (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
    (revAge ν s ζ, (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
      Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) (diffAt_joint hj hr _) _ _ ζ hγ rfl
  rw [clm_triple_apply] at hPγ
  have hG0 := fderiv_snd_gen (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ)
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)
    (diffAt_joint hj hr _) (1, 0)
  have hG1 := fderiv_snd_gen (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ)
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)
    (diffAt_joint hj hr _) (0, 1)
  rw [hG0, hG1] at hPγ
  have hfac0 : HasDerivAt (fun u => (((clockA ν (revAge ν s u))⁻¹ : ℝ) : ℂ))
      (((-(ν * -(clockA ν (revAge ν s ζ)) ^ 2) / (clockA ν (revAge ν s ζ)) ^ 2 : ℝ) : ℂ)) ζ :=
    (hac.inv ha.ne').ofReal_comp
  have hfac : HasDerivAt (fun u => (((clockA ν (revAge ν s u))⁻¹ : ℝ) : ℂ))
      ((ν : ℝ) : ℂ) ζ := by
    refine hfac0.congr_deriv ?_
    congr 1
    field_simp
  have hprod := hfac.mul hPγ
  have hrev : revDt ν φ s ζ y = deriv (fun u => (((clockA ν (revAge ν s u))⁻¹ : ℝ) : ℂ) *
      (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s u, (Real.sqrt (clockA ν (revAge ν s u)) * y.1,
        Real.sqrt (clockA ν (revAge ν s u)) * y.2))) ζ := rfl
  rw [hrev]
  refine (hprod.deriv).trans ?_
  simp only [Complex.real_smul, pdCx, B0579.dir, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  push_cast
  ring

/-- `Ψ = ∂_ζΦ + (2θ)⁻¹ y·∇Φ = ν φ(r, x) - a ∂_rφ(r, x)`: the dilation terms cancel (SP 2945-2946). -/
theorem reyPsi_eq {ν s ζ t : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hν : 0 < ν) (hs : 0 ≤ s)
    (hζ0 : 0 < ζ) (hr : revAge ν s ζ ∈ Ioo t s)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hφsm : ContDiff ℝ ∞ (φ (revAge ν s ζ))) (y : ℝ × ℝ) :
    reyPsi ν s ζ φ y =
      ((ν : ℝ) : ℂ) * φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) -
      ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
          (1, (0, 0)) := by
  have ha : 0 < clockA ν (revAge ν s ζ) := chgClockA_pos hν hs hζ0
  have hsa : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.mpr ha
  have hdil : dilCx (revPhi ν φ s ζ) y =
      (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) *
        (y.1 * pdCx 0 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
            Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) +
          y.2 * pdCx 1 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
            Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) := by
    have hsm : Real.sqrt (clockA ν (revAge ν s ζ)) • y =
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) := by
      ext <;> simp [smul_eq_mul]
    unfold dilCx revPhi
    rw [AdjE1.pdCx_movingPhi ν φ (revAge ν s ζ) hφsm 0 y,
      AdjE1.pdCx_movingPhi ν φ (revAge ν s ζ) hφsm 1 y, hsm]
    ring
  have hθ : (2 * revTheta ν s ζ)⁻¹ = ν * clockA ν (revAge ν s ζ) / 2 := by
    unfold revTheta clockTheta
    field_simp
  unfold reyPsi
  rw [revDt_formula hν hs hζ0 hr hj y, hdil, hθ]
  have hk := alg_psi ν (clockA ν (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ))) hsa
    (Real.sq_sqrt ha.le)
  have hk' : ((ν * -(clockA ν (revAge ν s ζ)) ^ 2 / (2 * Real.sqrt (clockA ν (revAge ν s ζ))) *
      (clockA ν (revAge ν s ζ))⁻¹ + ν * clockA ν (revAge ν s ζ) / 2 *
      ((clockA ν (revAge ν s ζ))⁻¹ * Real.sqrt (clockA ν (revAge ν s ζ))) : ℝ) : ℂ) = 0 := by
    rw [hk]
    simp
  have hA : ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) * ((clockA ν (revAge ν s ζ) : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast ha.ne')
  push_cast at hk' ⊢
  linear_combination (-((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
        (1, (0, 0))) * hA +
    (y.1 * pdCx 0 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) +
      y.2 * pdCx 1 (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) * hk'

/-- `Re(conj(a⁻¹φ)·(νφ - aD)) = a⁻¹(ν‖φ‖² - a Re(conj φ·D))`. -/
theorem re_conj_combo (ν a : ℝ) (φ D : ℂ) :
    (starRingEnd ℂ (((a⁻¹ : ℝ) : ℂ) * φ) * (((ν : ℝ) : ℂ) * φ - ((a : ℝ) : ℂ) * D)).re =
      a⁻¹ * (ν * ‖φ‖ ^ 2 - a * (starRingEnd ℂ φ * D).re) := by
  have hself : (starRingEnd ℂ φ * φ).re = ‖φ‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have e : starRingEnd ℂ (((a⁻¹ : ℝ) : ℂ) * φ) * (((ν : ℝ) : ℂ) * φ - ((a : ℝ) : ℂ) * D) =
      ((a⁻¹ : ℝ) : ℂ) * (((ν : ℝ) : ℂ) * (starRingEnd ℂ φ * φ) -
        ((a : ℝ) : ℂ) * (starRingEnd ℂ φ * D)) := by
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [e, Complex.re_ofReal_mul, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    hself]

/-- `Re(conj φ · (r D)) = r Re(conj φ · D)` for real `r`. -/
theorem re_conj_realmul (φ D : ℂ) (r : ℝ) :
    (starRingEnd ℂ φ * (((r : ℝ) : ℂ) * D)).re = r * (starRingEnd ℂ φ * D).re := by
  have e : starRingEnd ℂ φ * (((r : ℝ) : ℂ) * D) = ((r : ℝ) : ℂ) * (starRingEnd ℂ φ * D) := by
    ring
  rw [e, Complex.re_ofReal_mul]

/-- `Re(conj φ · (-a² D)) = -a² Re(conj φ · D)`. -/
theorem re_conj_negsq (φ D : ℂ) (a : ℝ) :
    (starRingEnd ℂ φ * (-((a : ℂ)) ^ 2 * D)).re = -(a ^ 2) * (starRingEnd ℂ φ * D).re := by
  have e : starRingEnd ℂ φ * (-((a : ℂ)) ^ 2 * D) = ((-(a ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ φ * D) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul]

/-- **Leaf (pointwise chain rule, SP 2860, 2945-2946).** -/
theorem reyPointwise (m : ℝ) (hm : 8 < m) (hc : UnforcedLeray.Short.IIIa.E0.ReyChain) :
    UnforcedLeray.Short.IIIa.E0.ReyPointwise m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ y
  have hs : 0 ≤ s := le_trans ht hts.le
  have hζ0 : 0 < ζ := hζ.1
  have hr : revAge ν s ζ ∈ Ioo t s := UnforcedLeray.Short.IIIa.AdjE1.revAge_mem_Ioo_A hν ht hts hζ
  have hj := hφ.jointSmooth
  have hφsm : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hφ.smooth _ (Ioo_subset_Ico_self hr)
  have ha : 0 < clockA ν (revAge ν s ζ) := chgClockA_pos hν hs hζ0
  have hcpos : (0:ℝ) < ν ^ (-2:ℝ) := Real.rpow_pos_of_pos hν _
  have hsa : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.mpr ha
  have hrd := reyRevAge_hasDeriv hν hs hζ0
  have hac : HasDerivAt (fun u => clockA ν (revAge ν s u))
      (ν * -(clockA ν (revAge ν s ζ)) ^ 2) ζ := (hrd.const_mul ν).const_add 1
  have hfix := phi_fix_deriv (φ := φ) hν hs hζ0 hr hj
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)
  have hG := hasDerivAt_norm_sq_c hfix
  have hA3 := (hac.pow 3).inv (pow_ne_zero 3 ha.ne')
  have hW := pw_chain m ν (ν ^ (-2 : ℝ)) s ζ (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1)
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) hν hcpos hs hζ0 ha
  have hprod := (hA3.mul hW).mul hG
  have hYy : (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1 / Real.sqrt (clockA ν (revAge ν s ζ)),
      Real.sqrt (clockA ν (revAge ν s ζ)) * y.2 / Real.sqrt (clockA ν (revAge ν s ζ))) = y := by
    refine Prod.ext ?_ ?_ <;> dsimp only <;> field_simp
  rw [show deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ'
      (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) ζ
      = _ from hprod.deriv]
  rw [hYy]
  unfold reyAPart wRe
  rw [reyPsi_eq hν hs hζ0 hr hj hφsm y]
  have hn : ‖revPhi ν φ s ζ y‖ ^ 2 = (clockA ν (revAge ν s ζ))⁻¹ ^ 2 *
      ‖φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ ^ 2 :=
    norm_movingPhi_sq ha y
  have hΦ : revPhi ν φ s ζ y = (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) *
      φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) := rfl
  rw [hn, hΦ, re_conj_combo, re_conj_negsq]
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  unfold revTheta clockTheta
  field_simp
  ring

end UnforcedLeray.Short.IIIa.E0
