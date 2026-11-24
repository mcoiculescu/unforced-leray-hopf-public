import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Final

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: norms and pairings at the block ends

Source: SP 2861, 2937-2958, 2962-2964.

* `entrance_norm`: `‖Wφ‖² = a_s³ ∫_{C_c} f² p_{a_s}` (the datum is `J_{a_s} φ` on the cell).
* `exit_TW_norm`, `exit_diff_norm`: `‖T Wφ‖` and `‖X - T Wφ‖` as weighted cell energies of `ψ`
  and `ω(t) - ψ`, `ψ = J_{a_t}[T(z_t - z_s)φ]`.
* `energy_of_xNorm`: the free moving energy bound in real form.
* `pairing_entrance`, `pairing_exit`: the pairing `∫ ω cmp` at both ends.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem entrance_norm {m R ν b s : ℝ} {φ : ℝ × ℝ → ℝ} (hφc : Continuous φ) (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (hs : 0 ≤ s) (hθ : b ≤ clockTheta ν s)
    {f : ℝ × ℝ → ℝ}
    (hfi : IntegrableOn (fun x : ℝ × ℝ => f x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν s) ^ m)
      (B0579.cell (ν ^ (-2 : ℝ))))
    (hfφ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
      JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) y = ((φ y : ℝ) : ℂ))
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ)) :
    ‖Wφ‖ = Real.sqrt (clockA ν s ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν s) f) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha := clockA_pos hν.le hs
  have hd := radius_lt_half_cellLen hν hνR hR.le hb hs hθ
  refine norm_eq_sqrt_movEnergy hc ha hfi (V := fun y => ((φ y : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hφc).aestronglyMeasurable (fun y hy => (hfφ y hy).symm) Wφ ?_
  filter_upwards [(Planar.wMeasure_ac m).ae_le hWφ] with z hz
  rw [hz]
  by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s))
  · simp only [cellZeroExt, indicator_of_mem hmem]
  · simp only [cellZeroExt, indicator_of_notMem hmem, eq_zero_of_not_mem_cell hR.le hd hφR hmem,
      Complex.ofReal_zero]

theorem integrableOn_psiT_sq {m R ν s t c : ℝ} {φ : ℝ × ℝ → ℝ} (hφs : ContDiff ℝ ∞ φ)
    (hR : 0 ≤ R) (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 ≤ ν)
    (ht : 0 ≤ t) :
    IntegrableOn (fun x : ℝ × ℝ => psiT φ ν s t x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν t) ^ m)
      (B0579.cell c) := by
  have ha := clockA_pos hν ht
  refine Integrable.integrableOn ?_
  refine Continuous.integrable_of_hasCompactSupport
    (((continuous_psiT hφs ν s t).pow 2).mul (continuous_movWeight m ha)) ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t)))
    fun x hx => ?_
  simp only [psiT_eq_zero hR hφR hν ht hx]
  ring

theorem continuous_phiFlow {φ : ℝ × ℝ → ℝ} (hφs : ContDiff ℝ ∞ φ) (z : ℝ) :
    Continuous fun y : ℝ × ℝ => ((φ (flowP z y) : ℝ) : ℂ) := by
  have h0 : Continuous fun y : ℝ × ℝ => tprof φ (z, y) :=
    (contDiff_tprof hφs).continuous.comp (continuous_const.prodMk continuous_id)
  exact Complex.continuous_ofReal.comp h0

theorem transport_ae_cellZeroExt {m R ν b s t : ℝ} {φ : ℝ × ℝ → ℝ} (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (ht : 0 ≤ t) (hθ : b ≤ clockTheta ν t)
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ)) :
    ⇑(Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
        (fun y => ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ)) (cToPlane z) := by
  have hd := radius_lt_half_cellLen hν hνR hR.le hb ht hθ
  have hG : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      φ (flowP (movingZ ν t - movingZ ν s) y) = 0 := fun y hy =>
    hφR _ (by rw [flowP_normSq]; exact hy)
  filter_upwards [(Planar.wMeasure_ac m).ae_le (transportGroupW_ae (movingZ ν t - movingZ ν s) hWφ)]
    with z hz
  rw [hz]
  by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
  · simp only [cellZeroExt, indicator_of_mem hmem]
  · simp only [cellZeroExt, indicator_of_notMem hmem, eq_zero_of_not_mem_cell hR.le hd hG hmem,
      Complex.ofReal_zero]

theorem exit_TW_norm {m R ν b s t : ℝ} {φ : ℝ × ℝ → ℝ} (hφs : ContDiff ℝ ∞ φ) (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (ht : 0 ≤ t) (hθ : b ≤ clockTheta ν t)
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ)) :
    ‖Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ‖ =
      Real.sqrt (clockA ν t ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (psiT φ ν s t)) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha := clockA_pos hν.le ht
  have hint : IntegrableOn (fun x : ℝ × ℝ =>
      psiT φ ν s t x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν t) ^ m)
      (B0579.cell (ν ^ (-2 : ℝ))) := integrableOn_psiT_sq hφs hR.le hφR hν.le ht
  have hVJ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)),
      ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ) =
        JscaleInv (clockA ν t) (fun x => ((psiT φ ν s t x : ℝ) : ℂ)) y :=
    fun y _ => (jscaleInv_psiT φ hν.le ht y).symm
  have hV : AEStronglyMeasurable
      (fun y : ℝ × ℝ => ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ))
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m) :=
    (continuous_phiFlow hφs _).aestronglyMeasurable
  exact norm_eq_sqrt_movEnergy hc ha hint hV hVJ _
    (transport_ae_cellZeroExt hR hφR hν hνR hb ht hθ Wφ hWφ)

theorem diff_ae_cellZeroExt {m R ν b s t : ℝ} {φ : ℝ × ℝ → ℝ} (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (ht : 0 ≤ t) (hθ : b ≤ clockTheta ν t)
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ))
    (w : ℝ × ℝ → ℝ) (X : Planar.L2w m) (hX : ⇑X =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
          (JscaleInv (clockA ν t) (fun x => ((w x : ℝ) : ℂ))) (cToPlane z)) :
    ⇑(X - Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
        (fun y => JscaleInv (clockA ν t) (fun x => ((w x : ℝ) : ℂ)) y -
          ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ)) (cToPlane z) := by
  have hd := radius_lt_half_cellLen hν hνR hR.le hb ht hθ
  have hG : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      φ (flowP (movingZ ν t - movingZ ν s) y) = 0 := fun y hy =>
    hφR _ (by rw [flowP_normSq]; exact hy)
  filter_upwards [Lp.coeFn_sub X (Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ),
    (Planar.wMeasure_ac m).ae_le hX,
    (Planar.wMeasure_ac m).ae_le (transportGroupW_ae (movingZ ν t - movingZ ν s) hWφ)]
    with z h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
  · simp only [cellZeroExt, indicator_of_mem hmem]
  · simp only [cellZeroExt, indicator_of_notMem hmem,
      eq_zero_of_not_mem_cell hR.le hd hG hmem, Complex.ofReal_zero, sub_zero]

theorem exit_diff_norm {m R ν b s t : ℝ} (hm0 : 0 ≤ m) {φ : ℝ × ℝ → ℝ} (hφs : ContDiff ℝ ∞ φ)
    (hR : 0 < R) (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (ht : 0 ≤ t) (hθ : b ≤ clockTheta ν t)
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ))
    {w : ℝ × ℝ → ℝ} (hw : MemLp w 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hint : IntegrableOn (fun x : ℝ × ℝ =>
      (w x - psiT φ ν s t x) ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν t) ^ m)
      (B0579.cell (ν ^ (-2 : ℝ))))
    (X : Planar.L2w m) (hX : ⇑X =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
          (JscaleInv (clockA ν t) (fun x => ((w x : ℝ) : ℂ))) (cToPlane z)) :
    ‖X - Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ‖ =
      Real.sqrt (clockA ν t ^ 3 *
        movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (fun x => w x - psiT φ ν s t x)) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha := clockA_pos hν.le ht
  have hJw : MemLp (JscaleInv (clockA ν t) (fun x => ((w x : ℝ) : ℂ))) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m) :=
    ComplCouplingSub.memLp_JscaleInv hm0 (one_le_clockA' hν.le ht) (hw.ofReal (K := ℂ))
  have hV : AEStronglyMeasurable
      (fun y => JscaleInv (clockA ν t) (fun x => ((w x : ℝ) : ℂ)) y -
        ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ))
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m) :=
    hJw.aestronglyMeasurable.sub (continuous_phiFlow hφs _).aestronglyMeasurable
  have hVJ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)),
      JscaleInv (clockA ν t) (fun x => ((w x : ℝ) : ℂ)) y -
        ((φ (flowP (movingZ ν t - movingZ ν s) y) : ℝ) : ℂ) =
      JscaleInv (clockA ν t) (fun x => ((w x - psiT φ ν s t x : ℝ) : ℂ)) y := by
    intro y _
    have h := jscaleInv_psiT φ hν.le ht (s := s) y
    simp only [JscaleInv] at h ⊢
    rw [← h]
    push_cast
    ring
  exact norm_eq_sqrt_movEnergy hc ha hint hV hVJ _
    (diff_ae_cellZeroExt hR hφR hν hνR hb ht hθ Wφ hWφ w X hX)

theorem energy_of_xNorm {m ν s σ k c : ℝ} (hc : 0 < c) (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hσ : 0 ≤ σ) {w f : ℝ × ℝ → ℝ}
    (hwi : IntegrableOn (fun x : ℝ × ℝ => w x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m)
      (B0579.cell c))
    (hfi : IntegrableOn (fun x : ℝ × ℝ => f x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν s) ^ m)
      (B0579.cell c))
    (h : xNorm (cellLen c (clockA ν σ)) m (JscaleInv (clockA ν σ) (fun x => ((w x : ℝ) : ℂ))) ≤
      ENNReal.ofReal (Real.exp (k * (movingZ ν σ - movingZ ν s))) *
        xNorm (cellLen c (clockA ν s)) m (JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)))) :
    clockA ν σ ^ 3 * movEnergy c m (clockA ν σ) w ≤
      Real.exp (2 * (k * (movingZ ν σ - movingZ ν s))) *
        (clockA ν s ^ 3 * movEnergy c m (clockA ν s) f) := by
  have haσ := clockA_pos hν hσ
  have has := clockA_pos hν hs
  rw [fmeScale c m (clockA ν σ) hc haσ w hwi, fmeScale c m (clockA ν s) hc has f hfi] at h
  exact le_of_sqrt_le (mul_nonneg (pow_nonneg haσ.le 3) (movEnergy_nonneg c m _ haσ w))
    (mul_nonneg (pow_nonneg has.le 3) (movEnergy_nonneg c m _ has f)) h

theorem pairing_entrance {m R ν b s : ℝ} (φ : ℝ × ℝ → ℝ) (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (hs : 0 ≤ s) (hθ : b ≤ clockTheta ν s)
    {f : ℝ × ℝ → ℝ}
    (hfφ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
      JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) y = ((φ y : ℝ) : ℂ)) :
    ∫ x, f x * cmp (tprof (gP m φ)) ν s s x =
      clockA ν s ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν s) f := by
  have hrc := radius_lt_half_cell hν hνR hR.le hb hs hθ
  have hsupp : SuppIn R (tprof (gP m φ)) := fun p hp => tprof_eq_zero (gP_eq_zero hφR) hp
  have hzero : ∀ x, x ∉ B0579.cell (ν ^ (-2 : ℝ)) → f x * cmp (tprof (gP m φ)) ν s s x = 0 := by
    intro x hx
    have hx' : x ∉ Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν s)) :=
      fun h => hx (mem_cell_of_mem_closedBall hrc h)
    rw [cmp_outside hsupp hν.le hs le_rfl hR.le hx', mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [setIntegral_congr_fun (B0579.measurableSet_cell _) (g := fun x =>
    clockA ν s ^ 3 * (f x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν s) ^ m)) (fun x hx => by
      simp only
      rw [cmp_entrance m φ hν.le hs hfφ hx, movWeight]
      ring)]
  rw [integral_const_mul]
  rfl

theorem pairing_exit {m R ν b s t : ℝ} (φ : ℝ × ℝ → ℝ) (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0) (hν : 0 < ν)
    (hνR : ν * (2 * R + 1) ≤ 1) (hb : 1 ≤ b) (ht : 0 ≤ t) (hθ : b ≤ clockTheta ν t)
    (w : ℝ × ℝ → ℝ) :
    ∫ x, w x * cmp (tprof (gP m φ)) ν s t x =
      clockA ν t ^ 3 * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        w x * psiT φ ν s t x * movWeight m (clockA ν t) x := by
  have hrc := radius_lt_half_cell hν hνR hR.le hb ht hθ
  have hsupp : SuppIn R (tprof (gP m φ)) := fun p hp => tprof_eq_zero (gP_eq_zero hφR) hp
  have hzero : ∀ x, x ∉ B0579.cell (ν ^ (-2 : ℝ)) → w x * cmp (tprof (gP m φ)) ν s t x = 0 := by
    intro x hx
    have hx' : x ∉ Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t)) :=
      fun h => hx (mem_cell_of_mem_closedBall hrc h)
    rw [cmp_outside hsupp hν.le ht le_rfl hR.le hx', mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_const_mul]
  refine setIntegral_congr_fun (B0579.measurableSet_cell _) fun x _ => ?_
  rw [cmp_eq_psiT m φ hν.le ht]
  ring

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
