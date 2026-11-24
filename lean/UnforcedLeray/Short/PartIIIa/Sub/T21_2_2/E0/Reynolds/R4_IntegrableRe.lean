import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R4_Pointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reg
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation.A_Diff
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/2/2/4/2`: integrability of `w Re(Φ̄ Ψ)` on the moving cell (SP 2945-2946, 3060-3062)

With `Ψ = νφ(r, √a·) - a ∂_rφ(r, √a·)` (`reyPsi_eq`), `|w Re(Φ̄Ψ)| ≤ w (p q)` where `p = |Φ|`,
`q ≤ ν a p + a v`, `v = |∂_rφ(r, √a·)|`, and `w p q` is dominated by `(ν²a²+2) w p² + a² w v²`.
Both terms are integrable on the moving cell: `w p²` by `RevPhiReg`, and `w v²` by the scaling of
the physical `L²` bound `AdjHigherCont` (the time derivative `adjDt`) to the moving cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- `adjDt` is the `r`-derivative of the joint adjoint at interior ages (SP 3060). -/
theorem adjDt_eq_fderiv {t s r : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hr : r ∈ Ioo t s)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) (x : ℝ × ℝ) :
    adjDt t s φ r x = fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) (1, (0, 0)) := by
  unfold adjDt
  rw [derivWithin_of_mem_nhds (Ico_mem_nhds hr.1 hr.2)]
  have hγ : HasDerivAt (fun u : ℝ => (u, x)) (1, (0, 0)) r :=
    (hasDerivAt_id' r).prodMk (hasDerivAt_const r x)
  exact (hasDerivAt_comp_pair (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x)
    (diffAt_joint hj hr x) _ _ r hγ rfl).deriv

/-- Continuity in the physical variable of the time derivative slice. -/
theorem cont_slice {t s r : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hr : r ∈ Ioo t s)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    Continuous (fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) (1, (0, 0))) := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hcd : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) :=
    hj.mono (Set.prod_mono Ioo_subset_Ico_self subset_rfl)
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2))
      (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := hcd.fderiv_of_isOpen hU (by simp)
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, x) := hU.mem_nhds ⟨hr, mem_univ _⟩
  have h1 : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => φ q.1 q.2) p)
      (r, x) := (hfd.contDiffAt hmem).continuousAt
  have h2 : ContinuousAt (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => φ q.1 q.2) p (1, (0, 0))) (r, x) :=
    h1.clm_apply continuousAt_const
  exact h2.comp (f := fun y : ℝ × ℝ => (r, y)) (continuous_const.prodMk continuous_id).continuousAt

/-- The time derivative of an adjoint is in `L²` of the physical cell (SP 3060-3073). -/
theorem memLp_slice {t s r : ℝ} {ν m : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {g : ℝ × ℝ → ℂ} (hφ : IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ) (hr : r ∈ Ioo t s)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    MemLp (fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) (1, (0, 0)))
      2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
  have hA := (hφ.higherCont r (Ioo_subset_Ico_self hr) []).2 (by simp)
  have e : (fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) (1, (0, 0))) =
      adjDt t s φ r := funext fun x => (adjDt_eq_fderiv hr hj x).symm
  rw [e]
  exact hA.1

/-- Scalar inequality: `p q ≤ (ν²a² + 2) p² + a² v²` when `q ≤ ν a p + a v`. -/
theorem key_ineq (p q v a ν : ℝ) (hp : 0 ≤ p) (hq : q ≤ ν * a * p + a * v) :
    p * q ≤ (ν ^ 2 * a ^ 2 + 2) * p ^ 2 + a ^ 2 * v ^ 2 := by
  nlinarith [sq_nonneg (ν * a * p - p), sq_nonneg (p - a * v), mul_le_mul_of_nonneg_left hq hp,
    mul_nonneg (sq_nonneg (ν * a)) (sq_nonneg p)]

/-- **Leaf: integrability of `w Re(Φ̄Ψ)` on the moving cell (SP 2945-2946, 3060-3062).** -/
theorem reyIntegrableRe (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.E0.ReyIntegrableRe m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ
  have hs : 0 ≤ s := le_trans ht hts.le
  have hζ0 : 0 < ζ := hζ.1
  have hr : revAge ν s ζ ∈ Ioo t s :=
    UnforcedLeray.Short.IIIa.AdjE1.revAge_mem_Ioo_A hν ht hts hζ
  have hrI : revAge ν s ζ ∈ Ico t s := Ioo_subset_Ico_self hr
  have hCF := (revPhiReg m hm ν hν tr t s ht hts g φ hφ (revAge ν s ζ) hrI).1
  have hj := hφ.jointSmooth
  have hφsm : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hφ.smooth _ hrI
  have ha : 0 < clockA ν (revAge ν s ζ) := chgClockA_pos hν hs hζ0
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hd : 0 < revCell ν (ν ^ (-2 : ℝ)) s ζ := by
    unfold revCell cellLen
    exact div_pos hc (Real.sqrt_pos.mpr ha)
  have hFc := cont_slice hr hj
  have hFL := memLp_slice hφ hr hj
  have hG : IntegrableOn (fun y : ℝ × ℝ => periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y *
      ‖fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
        (1, (0, 0))‖ ^ 2) (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ)) := by
    have hL := mpScaleMemLp m (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)) hc ha 1
      (fun x : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ, x) (1, (0, 0)))
      hFc hFL
    have hLc : Continuous (fun y : ℝ × ℝ => ((1 : ℝ) : ℂ) *
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
          (1, (0, 0))) :=
      continuous_const.mul ((hFc).comp ((continuous_const.mul continuous_fst).prodMk
        (continuous_const.mul continuous_snd)))
    have := cellWeight_integrableOn_aux m _ hm hd _ hLc hL
    simpa using this
  have hΨ : ∀ y : ℝ × ℝ, reyPsi ν s ζ φ y =
      ((ν : ℝ) : ℂ) * φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) -
      ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
          (1, (0, 0)) :=
    fun y => reyPsi_eq hν hs hζ0 hr hj hφsm y
  have hΨc : Continuous (reyPsi ν s ζ φ) := by
    have e : reyPsi ν s ζ φ = fun y : ℝ × ℝ => ((ν : ℝ) : ℂ) * φ (revAge ν s ζ)
          (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) -
        ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
          fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
            (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
            (1, (0, 0)) := funext hΨ
    rw [e]
    have hpc : Continuous (fun y : ℝ × ℝ => (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) :=
      (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)
    have hφc : Continuous (fun y : ℝ × ℝ => φ (revAge ν s ζ)
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) :=
      hφsm.continuous.comp hpc
    have hFc' : Continuous (fun y : ℝ × ℝ => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
        (revAge ν s ζ, (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) (1, (0, 0))) :=
      hFc.comp hpc
    exact (continuous_const.mul hφc).sub (continuous_const.mul hFc')
  have hΦc : Continuous (revPhi ν φ s ζ) := hCF.smooth.continuous
  have hwc : Continuous (periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ)) :=
    (UnforcedLeray.Short.IIIa.AdjE1.pw_contDiff (-m) _).continuous
  have hcontRe : Continuous (wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ)
      (reyPsi ν s ζ φ)) := by
    unfold wRe
    exact hwc.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hΦc).mul hΨc))
  refine Integrable.mono' ((hCF.int0.const_mul (ν ^ 2 * clockA ν (revAge ν s ζ) ^ 2 + 2)).add
    (hG.const_mul (clockA ν (revAge ν s ζ) ^ 2))) hcontRe.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (B0579.measurableSet_cell _) (fun y hy => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  unfold wRe
  have hw : 0 ≤ periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y :=
    (UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) _ y).le
  have hΦn : ‖revPhi ν φ s ζ y‖ ^ 2 = ((clockA ν (revAge ν s ζ))⁻¹) ^ 2 *
      ‖φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ ^ 2 :=
    norm_movingPhi_sq ha y
  have hsq : ‖φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ ^ 2 =
      (clockA ν (revAge ν s ζ) * ‖revPhi ν φ s ζ y‖) ^ 2 := by
    rw [mul_pow, hΦn]
    field_simp
  have hu : ‖φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ = clockA ν (revAge ν s ζ) * ‖revPhi ν φ s ζ y‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg ha.le (norm_nonneg _))).1 hsq
  have hΨb : ‖reyPsi ν s ζ φ y‖ ≤ ν * ‖φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)‖ +
      clockA ν (revAge ν s ζ) * ‖fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
        (1, (0, 0))‖ := by
    rw [hΨ y]
    have h := norm_sub_le (((ν : ℝ) : ℂ) * φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
        (((clockA ν (revAge ν s ζ) : ℝ) : ℂ) * fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
          (revAge ν s ζ, (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
            Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) (1, (0, 0)))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hν.le,
      Real.norm_of_nonneg ha.le] at h
    exact h
  have hre : |(starRingEnd ℂ (revPhi ν φ s ζ y) * reyPsi ν s ζ φ y).re| ≤
      ‖revPhi ν φ s ζ y‖ * ‖reyPsi ν s ζ φ y‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hq : ‖reyPsi ν s ζ φ y‖ ≤ ν * clockA ν (revAge ν s ζ) * ‖revPhi ν φ s ζ y‖ +
      clockA ν (revAge ν s ζ) * ‖fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
        (1, (0, 0))‖ := by
    rw [hu] at hΨb
    nlinarith [hΨb]
  have hk := key_ineq ‖revPhi ν φ s ζ y‖ ‖reyPsi ν s ζ φ y‖
    ‖fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (revAge ν s ζ,
        (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2))
        (1, (0, 0))‖
    (clockA ν (revAge ν s ζ)) ν (norm_nonneg _) hq
  calc |periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y *
        (starRingEnd ℂ (revPhi ν φ s ζ y) * reyPsi ν s ζ φ y).re|
      = periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y *
          |(starRingEnd ℂ (revPhi ν φ s ζ y) * reyPsi ν s ζ φ y).re| := by
        rw [abs_mul, abs_of_nonneg hw]
    _ ≤ periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y *
          (‖revPhi ν φ s ζ y‖ * ‖reyPsi ν s ζ φ y‖) := mul_le_mul_of_nonneg_left hre hw
    _ ≤ periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y *
          ((ν ^ 2 * clockA ν (revAge ν s ζ) ^ 2 + 2) * ‖revPhi ν φ s ζ y‖ ^ 2 +
            clockA ν (revAge ν s ζ) ^ 2 * ‖fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
              (revAge ν s ζ, (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
                Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) (1, (0, 0))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hk hw
    _ = (ν ^ 2 * clockA ν (revAge ν s ζ) ^ 2 + 2) * (periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y *
          ‖revPhi ν φ s ζ y‖ ^ 2) + clockA ν (revAge ν s ζ) ^ 2 *
          (periodicWeight (-m) (revCell ν (ν ^ (-2 : ℝ)) s ζ) y * ‖fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
            (revAge ν s ζ, (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
              Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) (1, (0, 0))‖ ^ 2) := by ring

end UnforcedLeray.Short.IIIa.E0
