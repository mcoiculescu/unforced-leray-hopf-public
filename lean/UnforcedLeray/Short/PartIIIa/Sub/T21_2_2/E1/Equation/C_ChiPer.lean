import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.B_ChiC1

/-!
# `PartIII-a:T21/2/2/3/2/3`: `MvChiPer` (leaf C of `movAdjEquation_of`)

`mvChi` is `d(ζ)`-periodic in `y₁`, `d = mvLen = c/√a`. The moving adjoint `Φ = mvPhi ν φ s ζ` and
the velocity `movingTrainV` are `d`-periodic. The `ζ`-derivative term is not periodic on its own:
differentiating the identity `mvPhi ζ' (y₁ + d(ζ'), y₂) = mvPhi ζ' y` in `ζ'` gives
`∂_ζΦ(y') + d'(ζ) ∂_{y₁}Φ(y') = ∂_ζΦ(y)` with `d' = β d / 2` (`β = νa`, `dr/dζ = -a²`), and the
dilation term `-(β/2) y·∇Φ` of `adjGen` shifts by exactly `-(β d/2) ∂_{y₁}Φ`, which cancels.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem clockA_pos_revAge_C {ν t s ζ : ℝ} (hν : 0 < ν) (ht0 : 0 ≤ t)
    (hr : revAge ν s ζ ∈ Ioo t s) : 0 < clockA ν (revAge ν s ζ) := by
  have h0 : 0 ≤ ν * revAge ν s ζ := mul_nonneg hν.le (by linarith [hr.1, ht0])
  unfold clockA
  linarith

/-- Shift of a planar partial derivative by a periodicity `(x₁ + d, x₂)`. -/
theorem pdCx_shift_C (k : Fin 2) (Ψ : ℝ × ℝ → ℂ) (d : ℝ)
    (hper : ∀ x : ℝ × ℝ, Ψ (x.1 + d, x.2) = Ψ x) (x : ℝ × ℝ) :
    pdCx k Ψ (x.1 + d, x.2) = pdCx k Ψ x := by
  have hs : (fun z : ℝ × ℝ => Ψ (z + ((d : ℝ), (0 : ℝ)))) = Ψ := by
    funext z
    rw [show z + ((d : ℝ), (0 : ℝ)) = (z.1 + d, z.2) by ext <;> simp]
    exact hper z
  have h1 : fderiv ℝ (fun z : ℝ × ℝ => Ψ (z + ((d : ℝ), (0 : ℝ)))) x
      = fderiv ℝ Ψ (x + ((d : ℝ), (0 : ℝ))) := fderiv_comp_add_right _
  rw [hs, show x + ((d : ℝ), (0 : ℝ)) = (x.1 + d, x.2) by ext <;> simp] at h1
  unfold pdCx
  rw [h1]

theorem mvPhi_shift_C {t s ν c : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x)
    {ζ' : ℝ} (hr : revAge ν s ζ' ∈ Ico t s) (hA : 0 < clockA ν (revAge ν s ζ')) (x : ℝ × ℝ) :
    mvPhi ν φ s ζ' (x.1 + cellLen c (clockA ν (revAge ν s ζ')), x.2) = mvPhi ν φ s ζ' x := by
  have hsne : Real.sqrt (clockA ν (revAge ν s ζ')) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hdiv : Real.sqrt (clockA ν (revAge ν s ζ')) * cellLen c (clockA ν (revAge ν s ζ')) = c := by
    unfold cellLen
    field_simp
  have e : (Real.sqrt (clockA ν (revAge ν s ζ')) * (x.1 + cellLen c (clockA ν (revAge ν s ζ'))),
      Real.sqrt (clockA ν (revAge ν s ζ')) * x.2) =
      (Real.sqrt (clockA ν (revAge ν s ζ')) * x.1 + c,
        Real.sqrt (clockA ν (revAge ν s ζ')) * x.2) := by
    refine Prod.ext ?_ rfl
    show Real.sqrt (clockA ν (revAge ν s ζ')) * (x.1 + cellLen c (clockA ν (revAge ν s ζ')))
      = Real.sqrt (clockA ν (revAge ν s ζ')) * x.1 + c
    rw [mul_add, hdiv]
  unfold mvPhi movingPhi
  dsimp only
  rw [e]
  congr 1
  exact hper _ hr (Real.sqrt (clockA ν (revAge ν s ζ')) * x.1,
    Real.sqrt (clockA ν (revAge ν s ζ')) * x.2)

theorem movingTrainV_shift_C {ν c s : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ζ' : ℝ}
    (hr0 : 0 ≤ revAge ν s ζ') (hA : 0 < clockA ν (revAge ν s ζ')) (x : ℝ × ℝ) :
    movingTrainV tr (revAge ν s ζ') (x.1 + cellLen c (clockA ν (revAge ν s ζ')), x.2) =
      movingTrainV tr (revAge ν s ζ') x := by
  have hsne : Real.sqrt (clockA ν (revAge ν s ζ')) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hdiv : Real.sqrt (clockA ν (revAge ν s ζ')) * cellLen c (clockA ν (revAge ν s ζ')) = c := by
    unfold cellLen
    field_simp
  have e : (Real.sqrt (clockA ν (revAge ν s ζ')) * (x.1 + cellLen c (clockA ν (revAge ν s ζ'))),
      Real.sqrt (clockA ν (revAge ν s ζ')) * x.2) =
      (Real.sqrt (clockA ν (revAge ν s ζ')) * x.1 + c,
        Real.sqrt (clockA ν (revAge ν s ζ')) * x.2) := by
    refine Prod.ext ?_ rfl
    show Real.sqrt (clockA ν (revAge ν s ζ')) * (x.1 + cellLen c (clockA ν (revAge ν s ζ')))
      = Real.sqrt (clockA ν (revAge ν s ζ')) * x.1 + c
    rw [mul_add, hdiv]
  have hp := tr.isTrain.periodic_v (revAge ν s ζ') hr0
    (Real.sqrt (clockA ν (revAge ν s ζ')) * x.1, Real.sqrt (clockA ν (revAge ν s ζ')) * x.2)
  dsimp only at hp
  unfold movingTrainV
  funext j
  dsimp only
  rw [e, hp]

/-- The shift of `adjGen` by the cell length: the dilation term `-(β/2) y·∇Φ` produces the drift
`-(β d/2) ∂_{y₁}Φ`. -/
theorem adjGen_shift_C (β d : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ)
    (hΦ : ∀ x : ℝ × ℝ, Φ (x.1 + d, x.2) = Φ x)
    (hV : ∀ x : ℝ × ℝ, V (x.1 + d, x.2) = V x) (y : ℝ × ℝ) :
    adjGen β V Φ (y.1 + d, y.2) = adjGen β V Φ y - ((β * d / 2 : ℝ) : ℂ) * pdCx 0 Φ y := by
  have h0 : pdCx 0 Φ (y.1 + d, y.2) = pdCx 0 Φ y := pdCx_shift_C 0 Φ d hΦ y
  have h1 : pdCx 1 Φ (y.1 + d, y.2) = pdCx 1 Φ y := pdCx_shift_C 1 Φ d hΦ y
  have h00 : pdCx 0 (pdCx 0 Φ) (y.1 + d, y.2) = pdCx 0 (pdCx 0 Φ) y :=
    pdCx_shift_C 0 (pdCx 0 Φ) d (fun x => pdCx_shift_C 0 Φ d hΦ x) y
  have h11 : pdCx 1 (pdCx 1 Φ) (y.1 + d, y.2) = pdCx 1 (pdCx 1 Φ) y :=
    pdCx_shift_C 1 (pdCx 1 Φ) d (fun x => pdCx_shift_C 1 Φ d hΦ x) y
  have hV0 : V (y.1 + d, y.2) 0 = V y 0 := congrFun (hV y) 0
  have hV1 : V (y.1 + d, y.2) 1 = V y 1 := congrFun (hV y) 1
  have hΦy : Φ (y.1 + d, y.2) = Φ y := hΦ y
  unfold adjGen lapC radC transC
  dsimp only
  rw [hΦy, h0, h1, h00, h11, hV0, hV1]
  push_cast
  ring

theorem hasDerivAt_revAge_C (ν s ζ : ℝ) (hd : 0 < 1 - ν * (movingZ ν s - ζ)) :
    HasDerivAt (fun ζ' => revAge ν s ζ') (-(clockA ν (revAge ν s ζ)) ^ 2) ζ := by
  have hne : (1 - ν * (movingZ ν s - ζ)) ≠ 0 := hd.ne'
  have hc : HasDerivAt (fun ζ' => movingZ ν s - ζ') (-1) ζ :=
    (hasDerivAt_id' ζ).const_sub (movingZ ν s)
  have hd2 : HasDerivAt (fun ζ' => 1 - ν * (movingZ ν s - ζ')) (-(ν * -1)) ζ :=
    (hc.const_mul ν).const_sub 1
  have hq := hc.div hd2 hne
  have hfun : (fun ζ' => revAge ν s ζ') =
      fun ζ' => (movingZ ν s - ζ') / (1 - ν * (movingZ ν s - ζ')) := by
    funext ζ'
    rfl
  have hcl : clockA ν (revAge ν s ζ) = 1 / (1 - ν * (movingZ ν s - ζ)) := by
    unfold clockA revAge ageOfZ
    field_simp
    ring
  have hval : -(clockA ν (revAge ν s ζ)) ^ 2
      = (-1 * (1 - ν * (movingZ ν s - ζ)) - (movingZ ν s - ζ) * -(ν * -1))
          / (1 - ν * (movingZ ν s - ζ)) ^ 2 := by
    rw [hcl]
    field_simp
    ring
  rw [hval, hfun]
  exact hq

theorem hasDerivAt_cellLen_revAge_C {ν s ζ c : ℝ} (hd : 0 < 1 - ν * (movingZ ν s - ζ))
    (hApos : 0 < clockA ν (revAge ν s ζ)) :
    HasDerivAt (fun ζ' => cellLen c (clockA ν (revAge ν s ζ')))
      (mvBeta ν s ζ * cellLen c (clockA ν (revAge ν s ζ)) / 2) ζ := by
  have hR := hasDerivAt_revAge_C ν s ζ hd
  have hA : HasDerivAt (fun ζ' => clockA ν (revAge ν s ζ'))
      (ν * -(clockA ν (revAge ν s ζ)) ^ 2) ζ :=
    (hR.const_mul ν).const_add 1
  have hS := hA.sqrt hApos.ne'
  have hsq : Real.sqrt (clockA ν (revAge ν s ζ)) ≠ 0 := (Real.sqrt_pos.2 hApos).ne'
  have hD := (hasDerivAt_const ζ c).div hS hsq
  have key : HasDerivAt (fun ζ' => c / Real.sqrt (clockA ν (revAge ν s ζ')))
      (mvBeta ν s ζ * cellLen c (clockA ν (revAge ν s ζ)) / 2) ζ := by
    refine HasDerivAt.congr_deriv hD ?_
    unfold mvBeta cellLen
    have hσ : Real.sqrt (clockA ν (revAge ν s ζ)) ^ 2 = clockA ν (revAge ν s ζ) :=
      Real.sq_sqrt hApos.le
    have hσpos : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.2 hApos
    generalize Real.sqrt (clockA ν (revAge ν s ζ)) = σ at hσ hσpos ⊢
    rw [← hσ]
    field_simp
    ring
  exact key

/-- The fibre derivative of `mvPhi` in the `y`-direction is the slice derivative of the joint map. -/
theorem fderiv_mvPhi_slice_C {ν s ζ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (q v : ℝ × ℝ)
    (hH : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, q)) :
    fderiv ℝ (mvPhi ν φ s ζ) q v =
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, q) (0, v) := by
  have hg : HasFDerivAt (fun q' : ℝ × ℝ => ((ζ, q') : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) q :=
    (hasFDerivAt_const ζ q).prodMk (hasFDerivAt_id q)
  have hc := hH.hasFDerivAt.comp q hg
  have e : mvPhi ν φ s ζ =
      (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) ∘ (fun q' : ℝ × ℝ => (ζ, q')) := rfl
  rw [e, hc.fderiv]
  simp

theorem mvChiPer (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.MvChiPer m := by
  intro ν tr t s φ ζ hflow y
  obtain ⟨hν, ht0, hts, ⟨G, _, hF⟩, hζ⟩ := hflow
  have hr : revAge ν s ζ ∈ Ioo t s := revAge_mem_Ioo_A hν ht0 hts hζ
  have hrI : revAge ν s ζ ∈ Ico t s := Ioo_subset_Ico_self hr
  have hA : 0 < clockA ν (revAge ν s ζ) := clockA_pos_revAge_C hν ht0 hr
  have hr0 : 0 ≤ revAge ν s ζ := le_of_lt (lt_of_le_of_lt ht0 hr.1)
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) := hF.jointSmooth
  have hd : 0 < 1 - ν * (movingZ ν s - ζ) :=
    revAge_denom_pos_A hν hζ.1 (movingZ_mul_lt_one_A hν (ht0.trans hts.le))
  have hΦper : ∀ x : ℝ × ℝ, mvPhi ν φ s ζ (x.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, x.2)
      = mvPhi ν φ s ζ x :=
    fun x => mvPhi_shift_C hF.periodic hrI hA x
  have hVper : ∀ x : ℝ × ℝ, movingTrainV tr (revAge ν s ζ)
      (x.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, x.2) = movingTrainV tr (revAge ν s ζ) x :=
    fun x => movingTrainV_shift_C tr hr0 hA x
  have hadj := adjGen_shift_C (mvBeta ν s ζ) (mvLen ν (ν ^ (-2 : ℝ)) s ζ)
    (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) hΦper hVper y
  have hdd : HasDerivAt (fun ζ' => mvLen ν (ν ^ (-2 : ℝ)) s ζ')
      (mvBeta ν s ζ * mvLen ν (ν ^ (-2 : ℝ)) s ζ / 2) ζ :=
    hasDerivAt_cellLen_revAge_C (c := ν ^ (-2 : ℝ)) hd hA
  have hL : HasDerivAt (fun ζ' : ℝ => (ζ', (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ', y.2)))
      ((1 : ℝ), ((mvBeta ν s ζ * mvLen ν (ν ^ (-2 : ℝ)) s ζ / 2), (0 : ℝ))) ζ :=
    (hasDerivAt_id' ζ).prodMk ((hdd.const_add y.1).prodMk (hasDerivAt_const ζ y.2))
  have hH := (contDiffAt_mvPhi_joint_B hν ht0 hts hζ hJ
    (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2)).differentiableAt (by simp)
  have hG := hH.hasFDerivAt.comp_hasDerivAt ζ hL
  have hEv : (fun ζ' => mvPhi ν φ s ζ' y) =ᶠ[𝓝 ζ]
      (fun ζ' : ℝ => (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2)
        (ζ', (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ', y.2))) := by
    filter_upwards [Ioo_mem_nhds hζ.1 hζ.2] with ζ' hζ'
    have hr' : revAge ν s ζ' ∈ Ico t s := Ioo_subset_Ico_self (revAge_mem_Ioo_A hν ht0 hts hζ')
    have hA' : 0 < clockA ν (revAge ν s ζ') :=
      clockA_pos_revAge_C hν ht0 (revAge_mem_Ioo_A hν ht0 hts hζ')
    exact (mvPhi_shift_C hF.periodic hr' hA' y).symm
  have hchain := hEv.deriv_eq.trans hG.deriv
  have hdec : ((1 : ℝ), ((mvBeta ν s ζ * mvLen ν (ν ^ (-2 : ℝ)) s ζ / 2), (0 : ℝ)))
      = ((1 : ℝ), (0 : ℝ × ℝ)) + (mvBeta ν s ζ * mvLen ν (ν ^ (-2 : ℝ)) s ζ / 2) •
          ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
    simp
  rw [hdec, map_add, map_smul, Complex.real_smul] at hchain
  have hdir0 : UnforcedLeray.B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
  have hslice : ∀ q : ℝ × ℝ,
      fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, q) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
        = pdCx 0 (mvPhi ν φ s ζ) q := by
    intro q
    have hHq := (contDiffAt_mvPhi_joint_B hν ht0 hts hζ hJ q).differentiableAt (by simp)
    unfold pdCx
    rw [hdir0]
    exact (fderiv_mvPhi_slice_C q _ hHq).symm
  have hP := pdCx_shift_C 0 (mvPhi ν φ s ζ) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) hΦper y
  have hD1 := deriv_mvPhi_eq_B hν ht0 hts hζ hJ y
  have hfin : fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2) (ζ, y) (1, 0)
      = fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => mvPhi ν φ s p.1 p.2)
          (ζ, (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2)) (1, 0)
        + ((mvBeta ν s ζ * mvLen ν (ν ^ (-2 : ℝ)) s ζ / 2 : ℝ) : ℂ) *
          pdCx 0 (mvPhi ν φ s ζ) y := by
    rw [← hD1, hchain, hslice, hP]
  unfold mvChi
  rw [hadj, deriv_mvPhi_eq_B hν ht0 hts hζ hJ
    (y.1 + mvLen ν (ν ^ (-2 : ℝ)) s ζ, y.2), hD1]
  linear_combination hfin

end UnforcedLeray.Short.IIIa.AdjE1
