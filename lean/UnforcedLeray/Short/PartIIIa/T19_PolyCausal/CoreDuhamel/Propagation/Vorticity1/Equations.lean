import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Represent

/-!
# `PartIII-a:T19/2/3/2/1` helpers: the integrand identity and joint integrability

* `rep_TI`: at an age `r > 0` with `L²(cell)` slices, the integrand of `CoreVortWeakEqAt` equals
  `J(r) = r^μ ∫ jInt` (SP 3462-3466).
* `joint_hInt`, `joint_jInt`, `Hf_int`, `Jf_int`: `r^μ' w · Ψ` and `r^μ jInt` are integrable on
  `(0, T) × cell`, hence `H`, `J` are integrable on `(0, T)` (zero entrance, SP 3428-3431).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.V1

open UnforcedLeray.Short.IIIa

variable {ν c : ℝ}

/-- The combination of weak-gradient and divergence identities in `pointwise_TI`. -/
def Zs (tr : UnforcedLeray.B0140.TrainSol ν c) (b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (r : ℝ) (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  ((((((((((Wk G_sol b_sol r 1 0 (psiF tr r φ) x -
    Wk G₀ b₀ r 1 0 (psiF tr r φ) x) - Wk G_sol b_sol r 0 1 (psiF tr r φ) x) +
    Wk G₀ b₀ r 0 1 (psiF tr r φ) x) + Wk G₀ b₀ r 1 0 (vfF tr r 0 0 φ) x) +
    Wk G₀ b₀ r 1 1 (vfF tr r 1 0 φ) x) - Wk G₀ b₀ r 0 0 (vfF tr r 0 1 φ) x) -
    Wk G₀ b₀ r 0 1 (vfF tr r 1 1 φ) x) - Dv b_sol r (chiwF tr r φ) x) +
    Dv b₀ r (chiwF tr r φ) x) - Dv b₀ r (chi0F tr r φ) x)

section Rep

variable {ν' : ℝ} {μ' : ℂ} {vel₀ vel₁ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
  {F₀ F₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
  {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}

theorem Zs_IZ (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hfree : IsCausalEnergySolution c ν' μ' vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ' vel₁ F₁ b_sol G_sol) {r : ℝ} (hr : 0 < r)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) : IZ c (Zs tr b₀ b_sol G₀ G_sol r φ) := by
  have hψ := psiF_test tr hr.le hφ
  exact ((((((((((Wk_IZ hsol hr 1 0 hψ).sub (Wk_IZ hfree hr 1 0 hψ)).sub
    (Wk_IZ hsol hr 0 1 hψ)).add (Wk_IZ hfree hr 0 1 hψ)).add
    (Wk_IZ hfree hr 1 0 (vfF_test tr hr.le hφ 0 0))).add
    (Wk_IZ hfree hr 1 1 (vfF_test tr hr.le hφ 1 0))).sub
    (Wk_IZ hfree hr 0 0 (vfF_test tr hr.le hφ 0 1))).sub
    (Wk_IZ hfree hr 0 1 (vfF_test tr hr.le hφ 1 1))).sub
    (Dv_IZ hsol hr (chiwF_test tr hr.le hφ))).add
    (Dv_IZ hfree hr (chiwF_test tr hr.le hφ))).sub (Dv_IZ hfree hr (chi0F_test tr hr.le hφ))

/-- **The integrand of the time equation** at an age with `L²` slices (SP 3462-3466). -/
theorem rep_TI (tr : UnforcedLeray.B0140.TrainSol ν c) {γ : ℝ} {μ : ℂ}
    (hfree : IsCausalEnergySolution c ν' μ' vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ' vel₁ F₁ b_sol G_sol) {r : ℝ} (hr : 0 < r)
    (h0L2 : ∀ i, MemLp (fun x => b₀ (r, x) i) 2 (volume.restrict (B0579.cell c)))
    (h1L2 : ∀ i, MemLp (fun x => b_sol (r, x) i) 2 (volume.restrict (B0579.cell c)))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    (∫ x in B0579.cell c, flowIntegrand tr
        (fun y => ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) * corePerturbVort γ ν G₀ G_sol r y)
        (fun y => ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) • corePerturbVel γ ν b₀ b_sol (r, y)) r φ x) +
      ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) *
        coreSrcFun c (coreAdvSlice γ tr b₀ G₀ r) (fun j x => (B0579.pd j φ x : ℂ)) =
    Jf c μ tr b_sol (wF b₀ b_sol) φ r := by
  have hmc := B0579.measurableSet_cell c
  set K : ℂ := (r : ℂ) ^ μ * (gainG γ ν r : ℂ) with hK
  obtain ⟨R, hR⟩ := hφ.band
  have hB : Band R φ := hR
  have hB0 : Band R (B0579.pd 0 φ) := hB.pd 0
  have hB1 : Band R (B0579.pd 1 φ) := hB.pd 1
  have hZ := Zs_IZ tr hfree hsol hr hφ
  set FI : ℝ × ℝ → ℂ := fun x => flowIntegrand tr
    (fun y => ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) * corePerturbVort γ ν G₀ G_sol r y)
    (fun y => ((r : ℂ) ^ μ * (gainG γ ν r : ℂ)) • corePerturbVel γ ν b₀ b_sol (r, y)) r φ x
    with hFI_def
  set SI : ℝ × ℝ → ℂ := fun x => coreAdvSlice γ tr b₀ G₀ r x 1 * (B0579.pd 0 φ x : ℂ) -
    coreAdvSlice γ tr b₀ G₀ r x 0 * (B0579.pd 1 φ x : ℂ) with hSI_def
  have hpt : ∀ x, FI x + K * SI x = (r : ℂ) ^ μ * jInt tr b_sol (wF b₀ b_sol) φ (r, x) +
      (r : ℂ) ^ μ * Zs tr b₀ b_sol G₀ G_sol r φ x := fun x => pointwise_TI tr hr hφ x
  -- integrability of the source integrand
  have hSI : IntegrableOn SI (B0579.cell c) := by
    have mc : ∀ j : Fin 2, Continuous (fun x => B0579.pd j (vC tr r 1) x * B0579.pd 0 φ x -
        B0579.pd j (vC tr r 0) x * B0579.pd 1 φ x) := fun j =>
      ((pdv_contDiff tr hr.le 1 j).continuous.mul (hφ.pd 0).continuous).sub
        ((pdv_contDiff tr hr.le 0 j).continuous.mul (hφ.pd 1).continuous)
    have mb : ∀ j : Fin 2, Band R (fun x => B0579.pd j (vC tr r 1) x * B0579.pd 0 φ x -
        B0579.pd j (vC tr r 0) x * B0579.pd 1 φ x) := fun j =>
      (hB0.mul_left _).sub (hB1.mul_left _)
    have hG : ∀ i j a k : Fin 2, IntegrableOn (fun x => G₀ (r, x) i j * (vfF tr r a k φ x : ℂ))
        (B0579.cell c) := fun i j a k =>
      ((hfree.weakGrad r hr i j).1 _ (vfF_test tr hr.le hφ a k)).2
    refine IntegrableOn.congr_fun ((((((((hG 1 0 0 0).add (hG 1 1 1 0)).sub (hG 0 0 0 1)).sub
      (hG 0 1 1 1)).add (intL2 (h0L2 0) (mc 0) (mb 0))).add
      (intL2 (h0L2 1) (mc 1) (mb 1))).const_mul ((gainG γ ν r : ℂ))⁻¹)) (fun x _ => ?_) hmc
    simp only [hSI_def, coreAdvSlice, advStretch, gainConj, Fin.sum_univ_two, Pi.smul_apply,
      Complex.real_smul, trainVel_fun tr hr.le, Pi.add_apply, Pi.sub_apply]
    simp only [trainVel_of_nonneg tr hr.le, vfF, vC_apply]
    push_cast
    ring
  -- integrability of the velocity-form integrand
  have hJ : IntegrableOn (fun x => jInt tr b_sol (wF b₀ b_sol) φ (r, x)) (B0579.cell c) := by
    have cL : ∀ j : Fin 2, Continuous (lapP (B0579.pd j φ)) := fun j =>
      (cylTest_lapP (hφ.pd j)).continuous
    have cf : ∀ i j : Fin 2, Continuous (B0579.pd i (B0579.pd j φ)) := fun i j =>
      ((hφ.pd j).pd i).continuous
    have cv : ∀ k : Fin 2, Continuous (vC tr r k) := fun k => (vC_contDiff tr hr.le k).continuous
    have bL0 : Band R (lapP (B0579.pd 0 φ)) := hB0.lapP
    have bL1 : Band R (lapP (B0579.pd 1 φ)) := hB1.lapP
    have b00 : Band R (B0579.pd 0 (B0579.pd 0 φ)) := hB0.pd 0
    have b10 : Band R (B0579.pd 1 (B0579.pd 0 φ)) := hB0.pd 1
    have b01 : Band R (B0579.pd 0 (B0579.pd 1 φ)) := hB1.pd 0
    have b11 : Band R (B0579.pd 1 (B0579.pd 1 φ)) := hB1.pd 1
    set M0 : ℝ × ℝ → ℝ := fun x => ν * lapP (B0579.pd 1 φ) x +
      2 * vC tr r 0 x * B0579.pd 0 (B0579.pd 1 φ) x + vC tr r 1 x * B0579.pd 1 (B0579.pd 1 φ) x -
      vC tr r 1 x * B0579.pd 0 (B0579.pd 0 φ) x with hM0
    set M1 : ℝ × ℝ → ℝ := fun x => -(ν * lapP (B0579.pd 0 φ) x) +
      vC tr r 0 x * B0579.pd 1 (B0579.pd 1 φ) x - vC tr r 0 x * B0579.pd 0 (B0579.pd 0 φ) x -
      2 * vC tr r 1 x * B0579.pd 1 (B0579.pd 0 φ) x with hM1
    set N0 : ℝ × ℝ → ℝ := fun x => -(ν * lapP (B0579.pd 1 φ) x) with hN0
    set N1 : ℝ × ℝ → ℝ := fun x => ν * lapP (B0579.pd 0 φ) x with hN1
    have cM0 : Continuous M0 :=
      (((continuous_const.mul (cL 1)).add ((continuous_const.mul (cv 0)).mul (cf 0 1))).add
        ((cv 1).mul (cf 1 1))).sub ((cv 1).mul (cf 0 0))
    have cM1 : Continuous M1 :=
      ((((continuous_const.mul (cL 0)).neg).add ((cv 0).mul (cf 1 1))).sub
        ((cv 0).mul (cf 0 0))).sub ((continuous_const.mul (cv 1)).mul (cf 1 0))
    have cN0 : Continuous N0 := (continuous_const.mul (cL 1)).neg
    have cN1 : Continuous N1 := continuous_const.mul (cL 0)
    have bM0 : Band R M0 := fun x hx => by
      simp only [hM0, bL1 x hx, b01 x hx, b11 x hx, b00 x hx]; ring
    have bM1 : Band R M1 := fun x hx => by
      simp only [hM1, bL0 x hx, b11 x hx, b00 x hx, b10 x hx]; ring
    have bN0 : Band R N0 := fun x hx => by simp only [hN0, bL1 x hx]; ring
    have bN1 : Band R N1 := fun x hx => by simp only [hN1, bL0 x hx]; ring
    refine IntegrableOn.congr_fun ((((intL2 (h1L2 0) cM0 bM0).add (intL2 (h1L2 1) cM1 bM1)).add
      (intL2 (h0L2 0) cN0 bN0)).add (intL2 (h0L2 1) cN1 bN1)) (fun x _ => ?_) hmc
    have hperp1 : (fun y => perpF φ y 1) = fun y => -B0579.pd 0 φ y := rfl
    have hperp0 : (fun y => perpF φ y 0) = B0579.pd 1 φ := rfl
    simp only [jInt, wF, Fin.sum_univ_two, hperp0, hperp1, trainVel_of_nonneg tr hr.le]
    rw [pd_neg, pd_neg, lapP_neg (hφ.pd 0)]
    simp only [hM0, hM1, hN0, hN1, vC_apply, Pi.add_apply]
    push_cast
    ring
  have hFI : IntegrableOn FI (B0579.cell c) := by
    refine IntegrableOn.congr_fun (((hJ.const_mul ((r : ℂ) ^ μ)).add
      (hZ.1.const_mul ((r : ℂ) ^ μ))).sub (hSI.const_mul K)) (fun x _ => ?_) hmc
    have := hpt x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← this]
    ring
  have hcs : coreSrcFun c (coreAdvSlice γ tr b₀ G₀ r) (fun j x => (B0579.pd j φ x : ℂ)) =
      ∫ x in B0579.cell c, SI x := rfl
  rw [hcs]
  calc (∫ x in B0579.cell c, FI x) + K * ∫ x in B0579.cell c, SI x
      = (∫ x in B0579.cell c, FI x) + ∫ x in B0579.cell c, K * SI x := by
        rw [integral_const_mul]
    _ = ∫ x in B0579.cell c, (FI x + K * SI x) := (integral_add hFI (hSI.const_mul K)).symm
    _ = ∫ x in B0579.cell c, ((r : ℂ) ^ μ * jInt tr b_sol (wF b₀ b_sol) φ (r, x) +
          (r : ℂ) ^ μ * Zs tr b₀ b_sol G₀ G_sol r φ x) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ x in B0579.cell c, (r : ℂ) ^ μ * jInt tr b_sol (wF b₀ b_sol) φ (r, x)) +
          ∫ x in B0579.cell c, (r : ℂ) ^ μ * Zs tr b₀ b_sol G₀ G_sol r φ x :=
        integral_add (hJ.const_mul _) (hZ.1.const_mul _)
    _ = Jf c μ tr b_sol (wF b₀ b_sol) φ r := by
        rw [integral_const_mul, integral_const_mul, hZ.2, mul_zero, add_zero]
        rfl

end Rep

/-! ## Joint integrability on `(0, T) × cell` -/

theorem coef_test {T : ℝ} {m : ℝ × ℝ → ℝ} (hm : B0579.IsCylTest c m) :
    ∃ M R : ℝ, 0 ≤ M ∧ ∀ p ∈ Ioo (0 : ℝ) T ×ˢ B0579.cell c,
      ‖((m p.2 : ℝ) : ℂ)‖ ≤ M * (Icc (-R) R).indicator 1 p.2.2 := by
  obtain ⟨M, R, hM, -, hb⟩ := cylTest_bound_band hm
  exact ⟨M, R, hM, fun p hp => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb p.2 hp.2⟩

theorem coef_vel (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) (k : Fin 2)
    {m : ℝ × ℝ → ℝ} (hm : B0579.IsCylTest c m) :
    ∃ M R : ℝ, 0 ≤ M ∧ ∀ p ∈ Ioo (0 : ℝ) T ×ˢ B0579.cell c,
      ‖((trainVel tr p.1 p.2 k * m p.2 : ℝ) : ℂ)‖ ≤ M * (Icc (-R) R).indicator 1 p.2.2 := by
  obtain ⟨Mv, hMv0, hMv⟩ := trainVel_bound hbuc hT
  obtain ⟨M, R, hM, -, hb⟩ := cylTest_bound_band hm
  refine ⟨Mv * M, R, mul_nonneg hMv0 hM, fun p hp => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h1 := hMv p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 k
  have h2 := hb p.2 hp.2
  calc |trainVel tr p.1 p.2 k| * |m p.2| ≤ Mv * (M * (Icc (-R) R).indicator 1 p.2.2) :=
        mul_le_mul h1 h2 (abs_nonneg _) hMv0
    _ = Mv * M * (Icc (-R) R).indicator 1 p.2.2 := by ring

theorem int_atom {ν' : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hc : 0 < c)
    (hb : IsCausalEnergySolution c ν' μ vel F b G) {μ' : ℂ} (hμ' : -5 / 4 < μ'.re) (T : ℝ)
    (i : Fin 2) {k : ℝ × (ℝ × ℝ) → ℂ} (hk : Measurable k)
    (hkb : ∃ M R : ℝ, 0 ≤ M ∧ ∀ p ∈ Ioo (0 : ℝ) T ×ˢ B0579.cell c,
      ‖k p‖ ≤ M * (Icc (-R) R).indicator 1 p.2.2) :
    IntegrableOn (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ' * (b p i * k p))
      (Ioo 0 T ×ˢ B0579.cell c) := by
  obtain ⟨M, R, hM, hb'⟩ := hkb
  exact integrableOn_cpow_mul hc hb hμ' T i hk.aestronglyMeasurable hM hb'

theorem meas_test {m : ℝ × ℝ → ℝ} (hm : B0579.IsCylTest c m) :
    Measurable fun p : ℝ × (ℝ × ℝ) => ((m p.2 : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (hm.continuous.measurable.comp measurable_snd)

theorem meas_vel (tr : UnforcedLeray.B0140.TrainSol ν c) (k : Fin 2) {m : ℝ × ℝ → ℝ}
    (hm : B0579.IsCylTest c m) :
    Measurable fun p : ℝ × (ℝ × ℝ) => ((trainVel tr p.1 p.2 k * m p.2 : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp
    ((measurable_trainVel tr k).mul (hm.continuous.measurable.comp measurable_snd))

section Joint

variable {ν' : ℝ} {μ : ℂ} {vel₀ vel₁ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
  {F₀ F₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b₀ b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
  {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}

theorem joint_hInt (hc : 0 < c) (hfree : IsCausalEnergySolution c ν' μ vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ vel₁ F₁ b_sol G_sol) {μ' : ℂ} (hμ' : -5 / 4 < μ'.re)
    (T : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ' * hInt (wF b₀ b_sol) φ p)
      (Ioo 0 T ×ˢ B0579.cell c) := by
  have hmeas : MeasurableSet (Ioo (0 : ℝ) T ×ˢ B0579.cell c) :=
    measurableSet_Ioo.prod (B0579.measurableSet_cell c)
  have a : ∀ i : Fin 2, ∀ {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {vel F G},
      IsCausalEnergySolution c ν' μ vel F b G →
      IntegrableOn (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ' * (b p i * ((perpF φ p.2 i : ℝ) : ℂ)))
        (Ioo 0 T ×ˢ B0579.cell c) := fun i _ _ _ _ hb =>
    int_atom hc hb hμ' T i (meas_test (perpF_cylTest hφ i)) (coef_test (perpF_cylTest hφ i))
  refine IntegrableOn.congr_fun ((((a 0 hsol).sub (a 0 hfree)).add ((a 1 hsol).sub (a 1 hfree))))
    (fun p _ => ?_) hmeas
  simp only [hInt, wF, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply]
  ring

theorem joint_jInt (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hfree : IsCausalEnergySolution c ν' μ vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ vel₁ F₁ b_sol G_sol) (hμ' : -5 / 4 < μ.re)
    {T : ℝ} (hT : 0 ≤ T) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ * jInt tr b_sol (wF b₀ b_sol) φ p)
      (Ioo 0 T ×ˢ B0579.cell c) := by
  have hmeas : MeasurableSet (Ioo (0 : ℝ) T ×ˢ B0579.cell c) :=
    measurableSet_Ioo.prod (B0579.measurableSet_cell c)
  have tL : ∀ i : Fin 2, B0579.IsCylTest c (lapP (fun y => perpF φ y i)) := fun i =>
    cylTest_lapP (perpF_cylTest hφ i)
  have tD : ∀ i j : Fin 2, B0579.IsCylTest c (B0579.pd j (fun y => perpF φ y i)) := fun i j =>
    (perpF_cylTest hφ i).pd j
  have aL : ∀ i : Fin 2, ∀ {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {vel F G},
      IsCausalEnergySolution c ν' μ vel F b G →
      IntegrableOn (fun p : ℝ × (ℝ × ℝ) =>
        (p.1 : ℂ) ^ μ * (b p i * ((lapP (fun y => perpF φ y i) p.2 : ℝ) : ℂ)))
        (Ioo 0 T ×ˢ B0579.cell c) := fun i _ _ _ _ hb =>
    int_atom hc hb hμ' T i (meas_test (tL i)) (coef_test (tL i))
  have aV : ∀ i j l k : Fin 2, IntegrableOn (fun p : ℝ × (ℝ × ℝ) =>
      (p.1 : ℂ) ^ μ * (b_sol p l *
        ((trainVel tr p.1 p.2 k * B0579.pd j (fun y => perpF φ y i) p.2 : ℝ) : ℂ)))
      (Ioo 0 T ×ˢ B0579.cell c) := fun i j l k =>
    int_atom hc hsol hμ' T l (meas_vel tr k (tD i j)) (coef_vel tr hbuc hT k (tD i j))
  have s1 := (((aL 0 hsol).sub (aL 0 hfree)).const_mul (ν : ℂ)).add
    (((aL 1 hsol).sub (aL 1 hfree)).const_mul (ν : ℂ))
  have s2 := ((((s1.add (aV 0 0 0 0)).add (aV 0 0 0 0)).add (aV 0 1 1 0)).add (aV 0 1 0 1))
  have s3 := ((((s2.add (aV 1 0 0 1)).add (aV 1 0 1 0)).add (aV 1 1 1 1)).add (aV 1 1 1 1))
  refine IntegrableOn.congr_fun s3 (fun p _ => ?_) hmeas
  simp only [jInt, wF, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

theorem Hf_int (hc : 0 < c) (hfree : IsCausalEnergySolution c ν' μ vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ vel₁ F₁ b_sol G_sol) (hμ' : -5 / 4 < μ.re)
    (T : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (Hf c μ (wF b₀ b_sol) φ) (Ioo 0 T) := by
  have hJ := joint_hInt hc hfree hsol hμ' T hφ
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hJ
  refine hJ.integral_prod_left.congr (Eventually.of_forall fun r => ?_)
  simp only [Hf]
  rw [integral_const_mul]

theorem Jf_int (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hfree : IsCausalEnergySolution c ν' μ vel₀ F₀ b₀ G₀)
    (hsol : IsCausalEnergySolution c ν' μ vel₁ F₁ b_sol G_sol) (hμ' : -5 / 4 < μ.re)
    {T : ℝ} (hT : 0 ≤ T) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (Jf c μ tr b_sol (wF b₀ b_sol) φ) (Ioo 0 T) := by
  have hJ := joint_jInt hc tr hbuc hfree hsol hμ' hT hφ
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hJ
  refine hJ.integral_prod_left.congr (Eventually.of_forall fun r => ?_)
  simp only [Jf]
  rw [integral_const_mul]

end Joint

end UnforcedLeray.Short.IIIa.V1

end
