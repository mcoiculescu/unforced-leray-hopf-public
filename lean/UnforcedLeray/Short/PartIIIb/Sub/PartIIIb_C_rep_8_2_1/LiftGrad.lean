import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1

/-!
# `RingChartLiftGrad` (`PartIII-b:C/rep/8/2/1/4`)

Source `the November 2 reference manuscript`
lines 1217 (`p_raw = a_r² p`), 5465, 5272-5282.  The lifted pressure is `G ∘ chart` with
`G(s,x) = s·p(s,x)`; at the chart point (azimuth `0`), the chain rule of `Lib/Axisymmetric/RingChart`
gives `∂_ρ ↦ √s(∂_q - ε(2s∂_s + η∂_η))`, `∂_{y₂} = 0`, `∂_z = √s ∂_η`.
-/

set_option autoImplicit false

noncomputable section

open Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Geometry

variable {R s q η : ℝ}

/-- The chart point `y = (R/√s, 0, η/√s)` lies off the axis with `ϱ = R/√s`. -/
theorem chartY_data (hR : 0 < R) (hs : 0 < s) :
    NearInst.chartY R (s, (q, η)) ∉ axis ∧ ϱ (NearInst.chartY R (s, (q, η))) = R / Real.sqrt s ∧
      chart R (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) = (s, (q, η)) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h0 : (NearInst.chartY R (s, (q, η))) 0 = R / Real.sqrt s := by
    simp [NearInst.chartY]
  have h1 : (NearInst.chartY R (s, (q, η))) 1 = 0 := by simp [NearInst.chartY]
  have h2 : (NearInst.chartY R (s, (q, η))) 2 = η / Real.sqrt s := by simp [NearInst.chartY]
  have hr : 0 < R / Real.sqrt s := div_pos hR hsq
  have hrho : ϱ (NearInst.chartY R (s, (q, η))) = R / Real.sqrt s := by
    unfold ϱ
    rw [h0, h1, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]
  have hax : NearInst.chartY R (s, (q, η)) ∉ axis := by
    intro h; exact hr.ne' (h0 ▸ h.1)
  refine ⟨hax, hrho, ?_⟩
  have hage : age R (NearInst.chartY R (s, (q, η))) = s := by
    unfold age
    rw [hrho, div_pow, Real.sq_sqrt hs.le]
    field_simp
  have htr : Axi.trans R (NearInst.chartY R (s, (q, η))) = η := by
    unfold Axi.trans
    rw [h2, hrho]
    field_simp
  have hph : phase R (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) = q := by
    unfold phase NearInst.chartTau
    rw [hage]
    field_simp
    ring
  simp only [chart, hage, htr, hph]

/-- The chart differential at the chart point on the three coordinate directions. -/
theorem chartD_coord (hR : 0 < R) (hs : 0 < s) :
    chartD R (NearInst.chartY R (s, (q, η))) (coordinateVector 0) =
      (-(2 * s * Real.sqrt s / R), (Real.sqrt s, -(η * Real.sqrt s / R))) ∧
    chartD R (NearInst.chartY R (s, (q, η))) (coordinateVector 1) = (0, (0, 0)) ∧
    chartD R (NearInst.chartY R (s, (q, η))) (coordinateVector 2) = (0, (0, Real.sqrt s)) := by
  obtain ⟨hax, hrho, -⟩ := chartY_data (q := q) (η := η) hR hs
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have h0 : (NearInst.chartY R (s, (q, η))) 0 = R / Real.sqrt s := by simp [NearInst.chartY]
  have h1 : (NearInst.chartY R (s, (q, η))) 1 = 0 := by simp [NearInst.chartY]
  have h2 : (NearInst.chartY R (s, (q, η))) 2 = η / Real.sqrt s := by simp [NearInst.chartY]
  have hRne : R ≠ 0 := hR.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [chartD_apply, ϱD_apply, hrho, h0, h1]
    simp only [coordinateVector, PiLp.single_apply]
    simp only [Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      if_false, mul_zero, add_zero, h2]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only
      field_simp
      rw [Real.sq_sqrt hs.le]
    · simp only
      field_simp
    · simp only
      field_simp
      rw [← hss]; ring
  · rw [chartD_apply, ϱD_apply, hrho, h0, h1]
    simp [coordinateVector, PiLp.single_apply]
  · rw [chartD_apply, ϱD_apply, hrho, h0, h1]
    simp [coordinateVector, PiLp.single_apply]
    field_simp

end Geometry

section Analysis

/-- Derivative bounds for the train pressure profile at a chart point. -/
theorem trainFp_derivs (L : ReturnLevel) {s q η : ℝ} (hs : 0 < s) :
    let P : ℝ × (ℝ × ℝ) → ℝ := fun z => L.train.p z.1 z.2
    let c : ℝ × (ℝ × ℝ) := (s, (q, η))
    |P c| ≤ ‖iteratedFDeriv ℝ 0 (trainFp L) (Real.log s, (q, η))‖ ∧
    |s * fderiv ℝ P c (1, (0, 0))| ≤ ‖iteratedFDeriv ℝ 1 (trainFp L) (Real.log s, (q, η))‖ ∧
    |fderiv ℝ P c (0, (0, 1))| ≤ ‖iteratedFDeriv ℝ 1 (trainFp L) (Real.log s, (q, η))‖ := by
  intro P c
  have hPd : DifferentiableAt ℝ P c := by
    have hmem : c ∈ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ))) := by
      simp only [c, Set.mem_prod, Set.mem_Ici, Set.mem_univ, and_true]; exact hs.le
    have hn : (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ))) ∈ nhds c := by
      refine prod_mem_nhds (Ici_mem_nhds hs) Filter.univ_mem
    exact ((L.train.isTrain.smooth_p.contDiffAt hn).differentiableAt (by simp))
  set z0 : ℝ × (ℝ × ℝ) := (Real.log s, (q, η)) with hz0
  have hE : HasFDerivAt (fun z : ℝ × (ℝ × ℝ) => (Real.exp z.1, z.2))
      ((Real.exp z0.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) z0 :=
    ((Real.hasDerivAt_exp _).comp_hasFDerivAt z0 (hasFDerivAt_fst)).prodMk hasFDerivAt_snd
  have hE0 : (Real.exp z0.1, z0.2) = c := by
    simp only [hz0, c, Real.exp_log hs]
  have hPc : HasFDerivAt P (fderiv ℝ P c) (Real.exp z0.1, z0.2) := by
    rw [hE0]; exact hPd.hasFDerivAt
  have hcomp := hPc.comp z0 hE
  have hfd : ∀ w : ℝ × (ℝ × ℝ), fderiv ℝ (trainFp L) z0 w =
      fderiv ℝ P c (s * w.1, w.2) := by
    intro w
    have : trainFp L = P ∘ (fun z : ℝ × (ℝ × ℝ) => (Real.exp z.1, z.2)) := rfl
    rw [this, hcomp.fderiv]
    simp [hz0, Real.exp_log hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_zero]
    have : trainFp L z0 = P c := by
      simp only [trainFp, hz0, c, P, Real.exp_log hs]
    rw [this, Real.norm_eq_abs]
  · rw [norm_iteratedFDeriv_one]
    have h1 := (fderiv ℝ (trainFp L) z0).le_opNorm ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
    rw [hfd] at h1
    have hn : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ = 1 := by simp [Prod.norm_def]
    rw [hn, mul_one, Real.norm_eq_abs] at h1
    have hsm : ((s : ℝ), ((0 : ℝ), (0 : ℝ))) = s • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by simp
    simp only [mul_one, mul_zero] at h1
    rw [hsm, map_smul, smul_eq_mul] at h1
    exact h1
  · rw [norm_iteratedFDeriv_one]
    have h1 := (fderiv ℝ (trainFp L) z0).le_opNorm ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
    rw [hfd] at h1
    have hn : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ = 1 := by simp [Prod.norm_def]
    rw [hn, mul_one, Real.norm_eq_abs] at h1
    simpa using h1

end Analysis

/-- **`RingChartLiftGrad`**: the gradient of the lifted pressure at the chart point
(source 1217, 5465, 5272-5282). -/
theorem ringChartLiftGrad : RingChartLiftGrad := by
  refine ⟨3, fun Pl L hε p hp0 hp1 => ?_⟩
  obtain ⟨s, q, η⟩ := p
  simp only at hp0
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  set R : ℝ := L.ε⁻¹ with hRdef
  have hRe : R⁻¹ = L.ε := inv_inv _
  obtain ⟨hax, hrho, hch⟩ := chartY_data (q := q) (η := η) hR hp0
  obtain ⟨hD0, hD1, hD2⟩ := chartD_coord (q := q) (η := η) hR hp0
  set y : Space := NearInst.chartY R (s, (q, η)) with hy
  set τ : ℝ := NearInst.chartTau R (s, (q, η)) with hτ
  let P : ℝ × (ℝ × ℝ) → ℝ := fun z => L.train.p z.1 z.2
  let G : ℝ × (ℝ × ℝ) → ℝ := fun z => z.1 * P z
  let c : ℝ × (ℝ × ℝ) := (s, (q, η))
  have hPd : DifferentiableAt ℝ P c := by
    have hn : (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ))) ∈ nhds c :=
      prod_mem_nhds (Ici_mem_nhds hp0) Filter.univ_mem
    exact ((L.train.isTrain.smooth_p.contDiffAt hn).differentiableAt (by simp))
  have hGd : DifferentiableAt ℝ G c := differentiableAt_fst.mul hPd
  have hGf : ∀ w : ℝ × (ℝ × ℝ), fderiv ℝ G c w = w.1 * P c + s * fderiv ℝ P c w := by
    intro w
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ × ℝ) (p := c)).mul hPd.hasFDerivAt
    have h' : HasFDerivAt G _ c := h
    rw [h'.fderiv]
    simp [c]
    ring
  have hlift : liftP L τ = fun x => G (chart R τ x) := rfl
  have key : ∀ j : Fin 3, fderiv ℝ (liftP L τ) y (coordinateVector j) =
      fderiv ℝ G c (chartD R y (coordinateVector j)) := by
    intro j
    rw [hlift, fderiv_comp_chart_apply hR.ne' hax (by rw [hch]; exact hGd), hch]
  have hmg : ∀ v : ℝ × ℝ, fderiv ℝ (trainP L s) (q, η) v = fderiv ℝ P c ((0 : ℝ), v) := by
    intro v
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => (s, x))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) (q, η) :=
      (hasFDerivAt_const s _).prodMk (hasFDerivAt_id _)
    have h2 := hPd.hasFDerivAt.comp (q, η) h1
    have : trainP L s = P ∘ (fun x : ℝ × ℝ => (s, x)) := rfl
    rw [this, h2.fderiv]
    simp
  set dS := fderiv ℝ P c (1, (0, 0)) with hdS
  set dQ := fderiv ℝ P c (0, (1, 0)) with hdQ
  set dE := fderiv ℝ P c (0, (0, 1)) with hdE
  have hexp : ∀ a b d : ℝ, fderiv ℝ P c (a, (b, d)) = a * dS + b * dQ + d * dE := by
    intro a b d
    rw [clm_triple]; simp [dS, dQ, dE]
  have hs32 : s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hp0.le (by norm_num)]
    norm_num
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hp0
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hp0.le
  -- the components
  have c0 : fderiv ℝ (liftP L τ) y (coordinateVector 0) =
      s * Real.sqrt s * dQ + L.ε * (s * Real.sqrt s) * (-2 * P c - 2 * (s * dS) - η * dE) := by
    rw [key, hD0, hGf, hexp]
    simp only [c, div_eq_mul_inv, hRe, P]
    ring
  have c1 : fderiv ℝ (liftP L τ) y (coordinateVector 1) = 0 := by
    rw [key, hD1]
    show fderiv ℝ G c 0 = 0
    exact map_zero _
  have c2 : fderiv ℝ (liftP L τ) y (coordinateVector 2) = s * Real.sqrt s * dE := by
    rw [key, hD2, hGf, hexp]
    simp only [c]
    ring
  set e : ℝ := L.ε * (s * Real.sqrt s) * (-2 * P c - 2 * (s * dS) - η * dE) with he
  have hvec : physGrad (liftP L τ) y - s ^ (3 / 2 : ℝ) • vecSp (emb (mgrad (trainP L s) (q, η))) =
      WithLp.toLp 2 ![e, 0, 0] := by
    ext j
    fin_cases j
    · simp only [physGrad, vecSp, emb, mgrad, ei, PiLp.sub_apply, PiLp.smul_apply]
      simp [c0, hmg, hs32]
      rw [← hdQ]
      ring
    · simp only [physGrad, vecSp, emb, mgrad, ei, PiLp.sub_apply, PiLp.smul_apply]
      simp [c1]
    · simp only [physGrad, vecSp, emb, mgrad, ei, PiLp.sub_apply, PiLp.smul_apply]
      simp [c2, hmg, hs32]
      rw [← hdE]
      ring
  rw [hvec]
  have hnorm : ‖(WithLp.toLp 2 ![e, 0, 0] : Space)‖ = |e| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp [Real.sqrt_sq_eq_abs]
  rw [hnorm]
  have hA : |P c| ≤ ‖iteratedFDeriv ℝ 0 (trainFp L) (Real.log s, (q, η))‖ :=
    (trainFp_derivs L (q := q) (η := η) hp0).1
  have hB1 : |s * dS| ≤ ‖iteratedFDeriv ℝ 1 (trainFp L) (Real.log s, (q, η))‖ :=
    (trainFp_derivs L (q := q) (η := η) hp0).2.1
  have hB2 : |dE| ≤ ‖iteratedFDeriv ℝ 1 (trainFp L) (Real.log s, (q, η))‖ :=
    (trainFp_derivs L (q := q) (η := η) hp0).2.2
  set A := ‖iteratedFDeriv ℝ 0 (trainFp L) (Real.log s, (q, η))‖ with hAdef
  set B := ‖iteratedFDeriv ℝ 1 (trainFp L) (Real.log s, (q, η))‖ with hBdef
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hW : (1 + |η|) ^ 3 * (A + B) ≤ trainWeight 3 L (s, (q, η)) := by
    unfold trainWeight
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h1 := norm_nonneg (iteratedFDeriv ℝ 0 (trainFv L) (Real.log s, (q, η)))
    have h2 := norm_nonneg (iteratedFDeriv ℝ 0 (trainFpsi L) (Real.log s, (q, η)))
    have h3 := norm_nonneg (iteratedFDeriv ℝ 1 (trainFv L) (Real.log s, (q, η)))
    have h4 := norm_nonneg (iteratedFDeriv ℝ 1 (trainFpsi L) (Real.log s, (q, η)))
    have h5 := norm_nonneg (iteratedFDeriv ℝ 2 (trainFv L) (Real.log s, (q, η)))
    have h6 := norm_nonneg (iteratedFDeriv ℝ 2 (trainFp L) (Real.log s, (q, η)))
    have h7 := norm_nonneg (iteratedFDeriv ℝ 2 (trainFpsi L) (Real.log s, (q, η)))
    have h8 := norm_nonneg (iteratedFDeriv ℝ 3 (trainFv L) (Real.log s, (q, η)))
    have h9 := norm_nonneg (iteratedFDeriv ℝ 3 (trainFp L) (Real.log s, (q, η)))
    have h10 := norm_nonneg (iteratedFDeriv ℝ 3 (trainFpsi L) (Real.log s, (q, η)))
    have h11 := norm_nonneg (iteratedFDeriv ℝ 4 (trainFv L) (Real.log s, (q, η)))
    have h12 := norm_nonneg (iteratedFDeriv ℝ 4 (trainFp L) (Real.log s, (q, η)))
    have h13 := norm_nonneg (iteratedFDeriv ℝ 4 (trainFpsi L) (Real.log s, (q, η)))
    have hm : 0 ≤ (1 + |η|) ^ 3 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hm
    linarith
  have hm1 : 1 ≤ (1 + |η|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg η])
  have hm2 : 1 + |η| ≤ (1 + |η|) ^ 3 := by
    have := abs_nonneg η
    nlinarith [sq_nonneg (1 + |η|), sq_nonneg |η|]
  have hX : |-2 * P c - 2 * (s * dS) - η * dE| ≤ 3 * trainWeight 3 L (s, (q, η)) := by
    have hη : |η * dE| ≤ |η| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB2 (abs_nonneg _)
    calc |-2 * P c - 2 * (s * dS) - η * dE|
        ≤ |-2 * P c| + |2 * (s * dS)| + |η * dE| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ 2 * A + 2 * B + |η| * B := by
          have e1 : |-2 * P c| = 2 * |P c| := by rw [abs_mul]; norm_num
          have e2 : |2 * (s * dS)| = 2 * |s * dS| := by rw [abs_mul]; norm_num
          linarith
      _ ≤ 3 * ((1 + |η|) ^ 3 * (A + B)) := by
          nlinarith [mul_nonneg hA0 (sub_nonneg.2 hm1), mul_nonneg hB0 (sub_nonneg.2 hm1),
            mul_nonneg hB0 (sub_nonneg.2 hm2), abs_nonneg η]
      _ ≤ 3 * trainWeight 3 L (s, (q, η)) := by linarith
  have hεs : 0 ≤ L.ε * (s * Real.sqrt s) :=
    mul_nonneg L.ε_pos.le (mul_nonneg hp0.le hsq.le)
  calc |e| = L.ε * (s * Real.sqrt s) * |-2 * P c - 2 * (s * dS) - η * dE| := by
        rw [he, abs_mul, abs_of_nonneg hεs]
    _ ≤ L.ε * (s * Real.sqrt s) * (3 * trainWeight 3 L (s, (q, η))) :=
        mul_le_mul_of_nonneg_left hX hεs
    _ = 3 * L.ν⁻¹ ^ 0 * L.ε * s ^ (3 / 2 : ℝ) * trainWeight 3 L (s, (q, η)) := by
        rw [hs32]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
