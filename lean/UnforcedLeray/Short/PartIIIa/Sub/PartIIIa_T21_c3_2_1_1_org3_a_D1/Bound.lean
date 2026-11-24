import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Point

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the bound at one parameter point

Source: SP 2937-2964.

`point_bound`: `‖X - T Wφ‖² ≤ (e^{2κB} - 1)‖Wφ‖² + 2BΛ`, `Λ = 2RL(C_Q/b + ε'C_Y)`, from
`‖X - TWφ‖² = E(t) - 2I(t) + ‖ψ‖²` (`exit_diff_norm`, `movEnergy_sub_expand`), the energy bound
`E(t) ≤ e^{2κB}‖Wφ‖²` (`freeMovingEnergy`), `‖ψ‖ = ‖T Wφ‖ ≤ ‖Wφ‖`, `I(s) = ‖Wφ‖²` and the drift
`|I(t) - I(s)| ≤ ΛB` (`drift_bound`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem movEnergy_sub_expand {c m a : ℝ} (ha : 0 < a) {w om ψ : ℝ × ℝ → ℝ}
    (hae : om =ᵐ[volume.restrict (B0579.cell c)] w) (homc : Continuous om)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hi : IntegrableOn (fun x => om x ^ 2 * movWeight m a x) (B0579.cell c)) :
    IntegrableOn (fun x : ℝ × ℝ => (w x - ψ x) ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m)
        (B0579.cell c) ∧
      movEnergy c m a (fun x => w x - ψ x) =
        movEnergy c m a w - 2 * (∫ x in B0579.cell c, om x * ψ x * movWeight m a x) +
          movEnergy c m a ψ := by
  have hp := continuous_movWeight m ha
  have i2 : IntegrableOn (fun x => om x * ψ x * movWeight m a x) (B0579.cell c) :=
    (Continuous.integrable_of_hasCompactSupport ((homc.mul hψc).mul hp)
      (hψcs.mul_left.mul_right)).integrableOn
  have i3 : IntegrableOn (fun x => ψ x ^ 2 * movWeight m a x) (B0579.cell c) := by
    refine (Continuous.integrable_of_hasCompactSupport ((hψc.pow 2).mul hp) ?_).integrableOn
    refine HasCompactSupport.intro hψcs fun x hx => ?_
    simp [image_eq_zero_of_notMem_tsupport hx]
  have i12 : IntegrableOn (fun x => om x ^ 2 * movWeight m a x -
      2 * (om x * ψ x * movWeight m a x)) (B0579.cell c) := hi.sub (i2.const_mul 2)
  have i123 : IntegrableOn (fun x => om x ^ 2 * movWeight m a x -
      2 * (om x * ψ x * movWeight m a x) + ψ x ^ 2 * movWeight m a x) (B0579.cell c) :=
    i12.add i3
  have hpt : ∀ x, (om x - ψ x) ^ 2 * movWeight m a x = om x ^ 2 * movWeight m a x -
      2 * (om x * ψ x * movWeight m a x) + ψ x ^ 2 * movWeight m a x := fun x => by ring
  have hae2 : (fun x : ℝ × ℝ => (om x - ψ x) ^ 2 * movWeight m a x) =ᵐ[volume.restrict
      (B0579.cell c)] fun x : ℝ × ℝ => (w x - ψ x) ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m := by
    filter_upwards [hae] with x hx
    rw [hx]; rfl
  refine ⟨(i123.congr_fun_ae (Eventually.of_forall fun x => (hpt x).symm)).congr_fun_ae hae2, ?_⟩
  have e1 : movEnergy c m a (fun x => w x - ψ x) =
      ∫ x in B0579.cell c, (om x ^ 2 * movWeight m a x -
        2 * (om x * ψ x * movWeight m a x) + ψ x ^ 2 * movWeight m a x) := by
    unfold movEnergy
    rw [← integral_congr_ae hae2]
    exact integral_congr_ae (Eventually.of_forall fun x => hpt x)
  have e2 : movEnergy c m a w = ∫ x in B0579.cell c, om x ^ 2 * movWeight m a x := by
    unfold movEnergy
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]; rfl
  rw [e1, e2, integral_add i12 i3, integral_sub hi (i2.const_mul 2), integral_const_mul]
  rfl

/-- **The bound at one parameter point.** -/
theorem point_bound {m B R CQ CY κ Lb b ε₁ ε' ν : ℝ} (hm : 8 < m) (hB : 0 < B)
    {φ : ℝ × ℝ → ℝ} (hφs : ContDiff ℝ ∞ φ) (hR : 0 < R)
    (hφR : ∀ y : ℝ × ℝ, R ^ 2 < y.1 ^ 2 + y.2 ^ 2 → φ y = 0)
    (Wφ : Planar.L2w m) (hWφ : ⇑Wφ =ᵐ[volume] fun z => ((φ (cToPlane z) : ℝ) : ℂ))
    (hCQ : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → p.1 ≤ B → |bracketQ (tprof (gP m φ)) p| ≤ CQ)
    (hCY : ∀ j : Fin 2, ∀ p : ℝ × (ℝ × ℝ), 0 ≤ p.1 → p.1 ≤ B →
      |dY (tprof (gP m φ)) j p| ≤ CY)
    (hκ1 : κ ≤ 1) (hLb0 : 0 < Lb) (hLbN : Real.exp B * ‖Wφ‖ ≤ Lb)
    (hb : 1 ≤ b) (hε₁ : 0 < ε₁) (hk : normGrowthConst m / b + ε₁ ≤ κ) (hε' : 0 ≤ ε')
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hνR : ν * (2 * R + 1) ≤ 1)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (H1 : ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
          ∀ w : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t f w →
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m
                (JscaleInv (clockA ν s) (fun x => ((w s x : ℝ) : ℂ))) ≤
              ENNReal.ofReal (Real.exp ((normGrowthConst m / b + ε₁) *
                (movingZ ν s - movingZ ν t))) *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m
                  (JscaleInv (clockA ν t) (fun x => ((f x : ℝ) : ℂ))))
    (H2 : ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
          ∀ w : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t f w →
            IntegrableOn (fun x : ℝ × ℝ => f x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν t) ^ m)
                (B0579.cell (ν ^ (-2 : ℝ))) ∧
            (∀ σ ∈ Icc t s, IntegrableOn
                (fun x : ℝ × ℝ => w σ x ^ 2 * (1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ) ^ m)
                (B0579.cell (ν ^ (-2 : ℝ)))))
    (H3 : ∀ s : ℝ, 0 ≤ s → b ≤ clockTheta ν s →
      ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
        |tr.v s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1| +
            |tr.v s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2|
          ≤ ε' * clockA ν s ^ (-(3 / 2) : ℝ))
    (H4 : UnforcedLeray.Short.IIb.TrainClose tr (ν * b)⁻¹ 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hθ : b ≤ clockTheta ν t)
    (hBz : movingZ ν t - movingZ ν s ≤ B)
    {f : B0579.Plane → ℝ} (hf : B0579.IsCylTest (ν ^ (-2 : ℝ)) f)
    (hfφ : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)),
      JscaleInv (clockA ν s) (fun x => ((f x : ℝ) : ℂ)) y = ((φ y : ℝ) : ℂ))
    {ω₀ : ℝ → B0579.Plane → ℝ} (hω₀ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω₀)
    (X : Planar.L2w m) (hX : ⇑X =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν t))
          (JscaleInv (clockA ν t) (fun x => ((ω₀ t x : ℝ) : ℂ))) (cToPlane z)) :
    ‖X - Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ‖ ^ 2 ≤
      (Real.exp (2 * κ * B) - 1) * ‖Wφ‖ ^ 2 + 2 * B * (2 * R * Lb * (CQ / b + ε' * CY)) := by
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hν0 := hν.le
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hb0 : (0 : ℝ) < b := by linarith
  have ht0 : 0 ≤ t := hs.trans hst
  have hθs : ∀ σ ∈ Icc s t, b ≤ clockTheta ν σ := fun σ hσ =>
    hθ.trans (theta_anti' hν (hs.trans hσ.1) hσ.2)
  set k := normGrowthConst m / b + ε₁ with hkdef
  have hCm : 0 < normGrowthConst m := by unfold normGrowthConst; positivity
  have hk0 : 0 ≤ k := by positivity
  have hk1 : k ≤ 1 := hk.trans hκ1
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hCQ (0, (0, 0)) le_rfl hB.le)
  have hCY0 : 0 ≤ CY := (abs_nonneg _).trans (hCY 0 (0, (0, 0)) le_rfl hB.le)
  -- the regular flow
  have hSg : 0 < (ν * b)⁻¹ := inv_pos.2 (mul_pos hν hb0)
  have htSg : t ≤ (ν * b)⁻¹ / ν := by
    have ha := clockA_pos hν0 ht0
    have hθ' : b ≤ (ν * clockA ν t)⁻¹ := hθ
    have h1 : ν * (1 + ν * t) ≤ b⁻¹ := (le_inv_comm₀ (mul_pos hν ha) hb0).2 hθ'
    rw [le_div_iff₀ hν, ← one_div, le_div_iff₀ (mul_pos hν hb0)]
    have h2 : b * (ν * (1 + ν * t)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hb0.le
      rwa [mul_inv_cancel₀ hb0.ne'] at this
    nlinarith [mul_pos hν hb0, mul_nonneg hν0 ht0]
  obtain ⟨om, hreg, homs⟩ := UnforcedLeray.Short.IIb.cylClassicalExists (ν * b)⁻¹ hSg ν
    (ν ^ (-2 : ℝ)) 1 hν hc1 zero_le_one tr H4 s hs (hst.trans htSg) f hf
  have hae := _root_.cylWeakEqClassical m hm (ν * b)⁻¹ hSg ν (ν ^ (-2 : ℝ)) 1 hν hc zero_le_one
    tr H4 s hs f hf om hreg homs ω₀ hω₀
  have haeI : ∀ σ ∈ Icc s t, om σ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω₀ σ :=
    fun σ hσ => hae σ ⟨hσ.1, hσ.2.trans htSg⟩
  -- integrability
  obtain ⟨hfi, hωi⟩ := H2 s t hs hst hθ f hf ω₀ hω₀
  -- the entrance energy
  set N2 := clockA ν s ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν s) f with hN2def
  have hN : ‖Wφ‖ = Real.sqrt N2 :=
    entrance_norm hφs.continuous hR hφR hν hνR hb hs (hθs s ⟨le_rfl, hst⟩) hfi hfφ Wφ hWφ
  have hN2nn : 0 ≤ N2 := mul_nonneg (pow_nonneg (clockA_pos hν0 hs).le 3)
    (movEnergy_nonneg _ _ _ (clockA_pos hν0 hs) f)
  have hNsq : ‖Wφ‖ ^ 2 = N2 := by rw [hN, Real.sq_sqrt hN2nn]
  -- the energies along the block
  have hEσ : ∀ σ ∈ Icc s t, clockA ν σ ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν σ) (ω₀ σ) ≤
      Real.exp (2 * (k * (movingZ ν σ - movingZ ν s))) * N2 := fun σ hσ =>
    energy_of_xNorm hc hν0 hs (hs.trans hσ.1) (hωi σ hσ) hfi
      (H1 s σ hs hσ.1 (hθs σ hσ) f hf ω₀ hω₀)
  have hmovE : ∀ σ ∈ Icc s t, movEnergy (ν ^ (-2 : ℝ)) m (clockA ν σ) (om σ) =
      movEnergy (ν ^ (-2 : ℝ)) m (clockA ν σ) (ω₀ σ) := by
    intro σ hσ
    unfold movEnergy
    refine integral_congr_ae ?_
    filter_upwards [haeI σ hσ] with x hx
    rw [hx]
  have hEi : ∀ σ ∈ Icc s t, IntegrableOn (fun x => om σ x ^ 2 * movWeight m (clockA ν σ) x)
      (B0579.cell (ν ^ (-2 : ℝ))) := by
    intro σ hσ
    refine (hωi σ hσ).congr_fun_ae ?_
    filter_upwards [haeI σ hσ] with x hx
    rw [hx]; rfl
  have hexpB : ∀ σ ∈ Icc s t, Real.exp (2 * (k * (movingZ ν σ - movingZ ν s))) * N2 ≤ Lb ^ 2 := by
    intro σ hσ
    have hΔ0 : 0 ≤ movingZ ν σ - movingZ ν s := sub_nonneg.2 (movingZ_mono hν0 hs hσ.1)
    have hΔB : movingZ ν σ - movingZ ν s ≤ B := by
      linarith [movingZ_mono hν0 (hs.trans hσ.1) hσ.2]
    have h1 : k * (movingZ ν σ - movingZ ν s) ≤ B := by
      calc k * (movingZ ν σ - movingZ ν s) ≤ 1 * B :=
            mul_le_mul hk1 hΔB hΔ0 zero_le_one
        _ = B := one_mul B
    have h2 : Real.exp (2 * (k * (movingZ ν σ - movingZ ν s))) * N2 =
        (Real.exp (k * (movingZ ν σ - movingZ ν s)) * ‖Wφ‖) ^ 2 := by
      rw [mul_pow, hNsq, ← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp (k * (movingZ ν σ - movingZ ν s)) * ‖Wφ‖ ≤ Lb :=
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) (norm_nonneg _)).trans hLbN
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) h3 2
  have hE : ∀ σ ∈ Icc s t, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      om σ x ^ 2 * movWeight m (clockA ν σ) x ≤ (clockA ν σ)⁻¹ ^ 3 * Lb ^ 2 := by
    intro σ hσ
    have ha := clockA_pos hν0 (hs.trans hσ.1)
    have h1 := (hEσ σ hσ).trans (hexpB σ hσ)
    rw [← hmovE σ hσ] at h1
    have e : movEnergy (ν ^ (-2 : ℝ)) m (clockA ν σ) (om σ) =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), om σ x ^ 2 * movWeight m (clockA ν σ) x := rfl
    rw [← e, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos ha 3)]
    linarith
  -- velocity facts
  obtain ⟨M, hM⟩ := fmrVelBdd ν (ν ^ (-2 : ℝ)) hν hc tr htr t
  have hM' : ∀ σ ∈ Icc s t, ∀ x, |tr.v σ x 0| + |tr.v σ x 1| ≤ M := fun σ hσ x =>
    hM σ ⟨hs.trans hσ.1, hσ.2⟩ x
  have hgap : ∀ σ ∈ Icc s t, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      |tr.v σ x 0 - (UnforcedLeray.B0146.isoVelocity ν σ x).1| +
        |tr.v σ x 1 - (UnforcedLeray.B0146.isoVelocity ν σ x).2| ≤
          ε' * clockA ν σ ^ (-(3 / 2) : ℝ) := fun σ hσ x hx =>
    H3 σ (hs.trans hσ.1) (hθs σ hσ) x hx
  -- the drift
  have hdrift := drift_bound (contDiff_gP m hφs) hR (gP_eq_zero hφR) hCQ hCY hm0 hb hν hνR hε'
    hLb0 hs hst htSg hθ hBz tr hgap hM' hreg hEi hE
  have hIs : ∫ x, om s x * cmp (tprof (gP m φ)) ν s s x = N2 := by
    rw [homs]
    exact pairing_entrance φ hR hφR hν hνR hb hs (hθs s ⟨le_rfl, hst⟩) hfφ
  have hIt := pairing_exit (m := m) (s := s) φ hR hφR hν hνR hb ht0 hθ (om t)
  rw [hIs, hIt] at hdrift
  -- the exit norms
  have hTW := exit_TW_norm (s := s) hφs hR hφR hν hνR hb ht0 hθ Wφ hWφ
  have hψcs : HasCompactSupport (psiT φ ν s t) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (R * Real.sqrt (clockA ν t)))
      fun x hx => psiT_eq_zero hR.le hφR hν0 ht0 hx
  have homtc : Continuous (om t) :=
    ((hreg.slice t ⟨hst, htSg⟩).smooth).continuous
  obtain ⟨hint, hexp⟩ := movEnergy_sub_expand (clockA_pos hν0 ht0) (haeI t ⟨hst, le_rfl⟩) homtc
    (continuous_psiT hφs ν s t) hψcs (hEi t ⟨hst, le_rfl⟩)
  have hXT := exit_diff_norm hm0 hφs hR hφR hν hνR hb ht0 hθ Wφ hWφ (hω₀.memX t hst) hint X hX
  -- assemble
  have hTWle : ‖Planar.transportGroupW m (movingZ ν t - movingZ ν s) Wφ‖ ≤ ‖Wφ‖ := by
    calc _ ≤ ‖Planar.transportGroupW m (movingZ ν t - movingZ ν s)‖ * ‖Wφ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖Wφ‖ :=
          mul_le_mul_of_nonneg_right (Planar.norm_transportGroupW_le _ _) (norm_nonneg _)
      _ = ‖Wφ‖ := one_mul _
  have ha := clockA_pos hν0 ht0
  have hEψnn : 0 ≤ clockA ν t ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (psiT φ ν s t) :=
    mul_nonneg (pow_nonneg ha.le 3) (movEnergy_nonneg _ _ _ ha _)
  have hEψ : clockA ν t ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (psiT φ ν s t) ≤ N2 := by
    rw [← hNsq, ← Real.sq_sqrt hEψnn, ← hTW]
    exact pow_le_pow_left₀ (norm_nonneg _) hTWle 2
  have hEt := hEσ t ⟨hst, le_rfl⟩
  have hDnn : 0 ≤ clockA ν t ^ 3 *
      movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (fun x => ω₀ t x - psiT φ ν s t x) :=
    mul_nonneg (pow_nonneg ha.le 3) (movEnergy_nonneg _ _ _ ha _)
  rw [hXT, Real.sq_sqrt hDnn, hexp, hNsq]
  -- numerics
  have hΔ0 : 0 ≤ movingZ ν t - movingZ ν s := sub_nonneg.2 (movingZ_mono hν0 hs hst)
  have hexpk : Real.exp (2 * (k * (movingZ ν t - movingZ ν s))) ≤ Real.exp (2 * κ * B) := by
    apply Real.exp_le_exp.2
    have : k * (movingZ ν t - movingZ ν s) ≤ κ * B :=
      mul_le_mul hk hBz hΔ0 ((hk0).trans hk)
    linarith
  have hΛ0 : 0 ≤ 2 * R * Lb * (CQ / b + ε' * CY) := by positivity
  have hdr := (abs_le.1 hdrift).1
  have hdrB : 2 * R * Lb * (CQ / b + ε' * CY) * (movingZ ν t - movingZ ν s) ≤
      2 * R * Lb * (CQ / b + ε' * CY) * B := mul_le_mul_of_nonneg_left hBz hΛ0
  have hEt' : clockA ν t ^ 3 * movEnergy (ν ^ (-2 : ℝ)) m (clockA ν t) (ω₀ t) ≤
      Real.exp (2 * κ * B) * N2 := hEt.trans (mul_le_mul_of_nonneg_right hexpk hN2nn)
  nlinarith

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
