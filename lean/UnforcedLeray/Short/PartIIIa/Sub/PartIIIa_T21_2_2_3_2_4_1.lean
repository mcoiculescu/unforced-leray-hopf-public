import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.C_ChiPer
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg.Scale

/-!
# `PartIII-a:T21/2/2/3/2/4/1`: the rescaled interaction identity `mvChi = a ladChi`

Source of record: `the November 2 reference manuscript` (SP) lines 2854-2865,
3052-3060. With `r = revAge ν s ζ`, `a = clockA ν r = 1 + ν r`, `σ = √a`, the moving adjoint is
`Φ(y) = a⁻¹ φ(r, σ y)`, `∂_ζΦ = -a² ∂_rΦ`, and

* `∂_ζΦ = ν φ - a ∂_rφ - (ν/2) σ y·∇φ`  (at the point `σ y`),
* `adjGen = ν a Δφ - (ν/2) σ y·∇φ + ν φ + a v·∇φ`,

so `mvChi = adjGen - ∂_ζΦ = a (∂_rφ + ν Δφ + v·∇φ)(r, σ y) = a ladChi`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Decomposition of a bounded linear functional on `ℝ × (ℝ × ℝ)` in the basis of directions. -/
theorem fderiv_decomp_aux (L : ℝ × (ℝ × ℝ) →L[ℝ] ℂ) (u v1 v2 : ℝ) :
    L (u, (v1, v2)) = u * L (1, (0, 0)) + v1 * L (0, B0579.dir 0) + v2 * L (0, B0579.dir 1) := by
  have e : ((u, (v1, v2)) : ℝ × (ℝ × ℝ)) = u • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
      v1 • ((0 : ℝ), B0579.dir 0) + v2 • ((0 : ℝ), B0579.dir 1) := by
    ext <;> simp [B0579.dir]
  rw [e]
  simp only [map_add, map_smul, Complex.real_smul]

/-- `a^{3/2} = a √a`. -/
theorem rpow32_aux (a : ℝ) (ha : 0 < a) : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha, Real.rpow_one]

theorem mvChi_eq_ladChi_scaled (m ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ) (hflow : AdjFlowAt m ν tr t s φ ζ) (y : ℝ × ℝ) :
    mvChi ν tr s φ ζ y = ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
      ladChi tr φ (revAge ν s ζ)
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) := by
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, hζ⟩ := hflow
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hzs : ν * movingZ ν s < 1 := movingZ_mul_lt_one_A hν (ht0.trans hts.le)
  have hd : 0 < 1 - ν * (movingZ ν s - ζ) := revAge_denom_pos_A hν hζ.1 hzs
  have hRd := hasDerivAt_revAge_C ν s ζ hd
  set r := revAge ν s ζ with hr_def
  have ha : 0 < clockA ν r := by
    have h0 : 0 ≤ ν * r := mul_nonneg hν.le (by linarith [hr.1, ht0])
    unfold clockA
    linarith
  -- smoothness of the adjoint at the interior age
  have hφr : ContDiff ℝ ∞ (φ r) := by
    have hc : ContDiff ℝ ∞ (fun x' : ℝ × ℝ => ((r, x') : ℝ × (ℝ × ℝ))) :=
      contDiff_const.prodMk contDiff_id
    have h : ContDiffOn ℝ ∞ ((fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) ∘
        (fun x' : ℝ × ℝ => ((r, x') : ℝ × (ℝ × ℝ)))) univ :=
      hF.jointSmooth.comp hc.contDiffOn (fun x' _ => ⟨Set.Ioo_subset_Ico_self hr, Set.mem_univ _⟩)
    exact contDiffOn_univ.1 h
  -- derivatives of the clock and of the rescaling
  have hA : HasDerivAt (fun ζ' => clockA ν (revAge ν s ζ')) (ν * -(clockA ν r) ^ 2) ζ :=
    (hRd.const_mul ν).const_add 1
  have hS : HasDerivAt (fun ζ' => Real.sqrt (clockA ν (revAge ν s ζ')))
      ((ν * -(clockA ν r) ^ 2) / (2 * Real.sqrt (clockA ν r))) ζ :=
    hA.sqrt ha.ne'
  obtain ⟨L, hPL⟩ : ∃ L : ℝ × (ℝ × ℝ) →L[ℝ] ℂ, HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) L
      (r, (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) :=
    ⟨_, ((joint_contDiffAt_A hF.jointSmooth hr _).differentiableAt (by simp)).hasFDerivAt⟩
  have hγ : HasDerivAt (fun ζ' => (revAge ν s ζ', (Real.sqrt (clockA ν (revAge ν s ζ')) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ')) * y.2)))
      (-(clockA ν r) ^ 2, ((ν * -(clockA ν r) ^ 2) / (2 * Real.sqrt (clockA ν r)) * y.1,
        (ν * -(clockA ν r) ^ 2) / (2 * Real.sqrt (clockA ν r)) * y.2)) ζ :=
    hRd.prodMk ((hS.mul_const y.1).prodMk (hS.mul_const y.2))
  have hcomp := hPL.comp_hasDerivAt ζ hγ
  have hinvC : HasDerivAt (fun ζ' => (((clockA ν (revAge ν s ζ'))⁻¹ : ℝ) : ℂ))
      (((-(ν * -(clockA ν r) ^ 2)) / (clockA ν r) ^ 2 : ℝ) : ℂ) ζ :=
    (hA.inv ha.ne').ofReal_comp
  have hmv := hinvC.mul hcomp
  have hD : deriv (fun ζ' => mvPhi ν φ s ζ' y) ζ =
      ((((-(ν * -(clockA ν r) ^ 2)) / (clockA ν r) ^ 2 : ℝ) : ℂ) * φ r
        (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) +
      (((clockA ν r)⁻¹ : ℝ) : ℂ) * L (-(clockA ν r) ^ 2,
        ((ν * -(clockA ν r) ^ 2) / (2 * Real.sqrt (clockA ν r)) * y.1,
          (ν * -(clockA ν r) ^ 2) / (2 * Real.sqrt (clockA ν r)) * y.2))) := hmv.deriv
  -- partial derivatives of the adjoint at the rescaled point
  have hc1 : HasDerivAt (fun r' : ℝ => (r', (Real.sqrt (clockA ν r) * y.1,
      Real.sqrt (clockA ν r) * y.2))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r _)
  have h1 := hPL.comp_hasDerivAt r hc1
  have hLr : ladDt φ r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
      L (1, (0, 0)) := ladDt_eq_of_hasDerivAt h1
  have hQ : HasFDerivAt (fun x' : ℝ × ℝ => φ r x') (L.comp
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))))
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) := by
    have hc : HasFDerivAt (fun x' : ℝ × ℝ => ((r, x') : ℝ × (ℝ × ℝ)))
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
        (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
      (hasFDerivAt_const r _).prodMk (hasFDerivAt_id _)
    exact HasFDerivAt.comp _ hPL hc
  have hLx : ∀ k : Fin 2, pdCx k (φ r) (Real.sqrt (clockA ν r) * y.1,
      Real.sqrt (clockA ν r) * y.2) = L (0, B0579.dir k) := by
    intro k
    have h := hQ.fderiv
    unfold pdCx
    rw [show (fun x' : ℝ × ℝ => φ r x') = φ r from rfl] at h
    rw [h]
    simp
  -- derivatives of the moving adjoint at fixed age
  have hMP1 : ∀ k : Fin 2, pdCx k (mvPhi ν φ s ζ) y =
      (((clockA ν r)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν r) : ℝ) : ℂ) *
        pdCx k (φ r) (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
    fun k => pdCx_movingPhi ν φ r hφr k y
  have hMP2 : ∀ k l : Fin 2, pdCx k (pdCx l (mvPhi ν φ s ζ)) y =
      pdCx k (pdCx l (φ r)) (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) :=
    fun k l => congrFun (pdCx_movingPhi_two ν φ r hφr ha k l) y
  have hv3 : clockA ν r ^ (3 / 2 : ℝ) = clockA ν r * Real.sqrt (clockA ν r) :=
    rpow32_aux _ ha
  -- assemble
  unfold mvChi
  rw [hD, fderiv_decomp_aux L, ← hLr, ← hLx 0, ← hLx 1]
  unfold adjGen lapC radC transC
  simp only [mvBeta, movingTrainV]
  rw [hMP2 0 0, hMP2 1 1, hMP1 0, hMP1 1, hv3]
  unfold mvPhi movingPhi
  unfold ladChi ladLapCx ladTransport
  rw [← hr_def]
  have hσpos : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha
  have hσ2 : Real.sqrt (clockA ν r) * Real.sqrt (clockA ν r) = clockA ν r :=
    Real.mul_self_sqrt ha.le
  generalize Real.sqrt (clockA ν r) = σ at hσpos hσ2 ⊢
  rw [← hσ2]
  have hσ0 : σ ≠ 0 := hσpos.ne'
  have hσC : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ0
  push_cast
  field_simp
  ring

end UnforcedLeray.Short.IIIa.AdjE1
