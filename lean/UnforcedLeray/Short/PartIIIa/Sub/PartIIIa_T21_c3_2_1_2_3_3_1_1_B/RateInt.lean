import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLip
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PdEcCont
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.FluxContinuity.MulDCT

/-!
# Integrability of the physical interaction rate (`LinFreeAdjRateInt`)

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958
(the free adjoint pairing), 3052-3054 (`u·∇E ∈ X_m` by weighted Cauchy-Schwarz).

For a linearised flow `w` (velocity `u`, zero-circulation datum) and a regular free adjoint flow
`φ` on `[t₁, s]`, the rate `I(r) = ∫_{C_c} (u(r)·∇E(r)) φ(r)` is continuous on `[t₁, s]`:
`I(r) - I(r₀) = ⟨F(r) - F(r₀), φ(r)⟩ + ⟨F(r₀), φ(r) - φ(r₀)⟩` with `F(r) = u(r)·∇E(r) ∈ X_m`
(`ladForceMemX`, `pair_bound`), where `F(r) - F(r₀) = (u(r) - u(r₀))·∇E(r) + u(r₀)·(∇E(r) - ∇E(r₀))`:
the first piece by `ladForceMemX` and `ladVelLip` with the strong continuity of `w`, the second by
dominated convergence (`Exist.tendsto_eLpNorm_mul_sub`, the bound `⟨x⟩^{m+2}|∇E| ≤ C` of
`LadTrainBdd` and the continuity in age of `∇E`, `PdEc.pdEc_continuousOn`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplMildTestedSplit

open ComplFreeRateSub

/-- **Integrability of the physical interaction rate** (SP 2937-2958, 3052-3054): for a linearised
flow with zero-circulation datum and a regular free adjoint flow `φ` on `[t₁, s]`, the rate
`r ↦ ∫_{C_c} (u(r)·∇E(r)) φ(r)` of `LinFreeAdjPairing` is integrable on `(t₁, s]`. -/
def LinFreeAdjRateInt (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ : ℝ) : Prop :=
  8 < m → 0 < ν → ν ≤ 1 → 0 ≤ t₁ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
  ∀ (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u → HasZeroCirculation (ν ^ (-2 : ℝ)) f →
    ∀ (s : ℝ) (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ →
      IntegrableOn (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (u r x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
            u r x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) * φ r x)
        (Ioc t₁ s)

namespace RateIntSub

/-- The cell pairing of `X_{m,d}` and `X_{-m,d}`, extended-norm form of `pair_bound`. -/
theorem pair_enorm_le {d m : ℝ} {A B : ℝ × ℝ → ℂ} (hA : MemLp A 2 (B0579.cellMeasure d m))
    (hB : MemLp B 2 (B0579.cellMeasure d (-m))) :
    ‖∫ y in B0579.cell d, A y * B y‖ₑ ≤ xNorm d m A * xNorm d (-m) B := by
  have h := (Leaf2DualityNeeded.pair_bound hA hB).2
  have hfin : xNorm d m A * xNorm d (-m) B ≠ ⊤ := ENNReal.mul_ne_top hA.2.ne hB.2.ne
  calc ‖∫ y in B0579.cell d, A y * B y‖ₑ = ENNReal.ofReal ‖∫ y in B0579.cell d, A y * B y‖ :=
        (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ((xNorm d m A * xNorm d (-m) B).toReal) := ENNReal.ofReal_le_ofReal h
    _ = xNorm d m A * xNorm d (-m) B := ENNReal.ofReal_toReal hfin

/-- The weighted train gradient bound of `LadTrainBdd`, at the weight `⟨x⟩^m`. -/
theorem weighted_pd_le {ν c m S C : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hbd : LadTrainBdd tr m S C) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) S) {x : ℝ × ℝ}
    (hx : x ∈ B0579.cell c) (j : Fin 2) :
    |B0579.jb x ^ (m / 2) * B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x| ≤ C := by
  have hj1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hw : B0579.jb x ^ (m / 2) ≤ B0579.jb x ^ ((m + 2) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
  have hw0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [abs_mul, abs_of_nonneg hw0]
  exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans ((hbd ρ hρ x hx).2 j)

end RateIntSub

open RateIntSub in
/-- **`LinFreeAdjRateInt`**: the rate is continuous on `[t₁, s]`, hence integrable. -/
theorem linFreeAdjRateInt (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ : ℝ) : LinFreeAdjRateInt ν m tr t₁ := by
  intro hm hν hν1 ht₁ _htr hLad f w u hw hz s g φ hφ
  rcases le_or_gt s t₁ with hst | hts
  · rw [Ioc_eq_empty (not_lt.2 hst)]
    exact integrableOn_empty
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell (ν ^ (-2 : ℝ))) with hμ
  have hs0 : 0 ≤ s := ht₁.trans hts.le
  obtain ⟨CT, hCT⟩ := hLad s hs0
  obtain ⟨CV, hCV⟩ := ladVelLip m hm ν (ν ^ (-2 : ℝ)) tr t₁ f w u hc1 hz hw
  have hU : ∀ r, t₁ ≤ r → ∀ j : Fin 2, MemLp (fun x => u r x j) 2 μ :=
    fun r hr j => (hw.biotSavart r hr).1 j
  set F : ℝ → ℝ × ℝ → ℂ := fun r => ladForce tr (u r) r with hF_def
  have hF : ∀ r ∈ Icc t₁ s, MemLp (F r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    fun r hr => (ladForceMemX m ν (ν ^ (-2 : ℝ)) tr s CT r hCT ⟨ht₁.trans hr.1, hr.2⟩ (u r) (hU r hr.1)).1
  have hφm : ∀ r ∈ Icc t₁ s, MemLp (φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφ.memX
  have hcell : MeasurableSet (B0579.cell (ν ^ (-2 : ℝ))) := B0579.measurableSet_cell (ν ^ (-2 : ℝ))
  -- continuity of the rate
  have hcont : ContinuousOn (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), F r x * φ r x) (Icc t₁ s) := by
    intro r₀ hr₀
    have hr₀0 : 0 ≤ r₀ := ht₁.trans hr₀.1
    -- the velocity increment `L r = (u(r) - u(r₀))·∇E(r)`
    set L : ℝ → ℝ × ℝ → ℂ := fun r => ladForce tr (fun x j => u r x j - u r₀ x j) r with hL_def
    have hΔU : ∀ r, t₁ ≤ r → ∀ j : Fin 2,
        MemLp (fun x => (fun x j => u r x j - u r₀ x j) x j) 2 μ :=
      fun r hr j => (hU r hr j).sub (hU r₀ hr₀.1 j)
    have hLm : ∀ r ∈ Icc t₁ s, MemLp (L r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
        xNorm (ν ^ (-2 : ℝ)) m (L r) ≤ ENNReal.ofReal CT *
          (ENNReal.ofReal CV * xNorm (ν ^ (-2 : ℝ)) m (w r - w r₀) +
            ENNReal.ofReal CV * xNorm (ν ^ (-2 : ℝ)) m (w r - w r₀)) := by
      intro r hr
      obtain ⟨h1, h2⟩ := ladForceMemX m ν (ν ^ (-2 : ℝ)) tr s CT r hCT ⟨ht₁.trans hr.1, hr.2⟩ _ (hΔU r hr.1)
      refine ⟨h1, h2.trans ?_⟩
      gcongr
      · exact hCV r r₀ hr.1 hr₀.1 0
      · exact hCV r r₀ hr.1 hr₀.1 1
    -- the age increment `H r = u(r₀)·(∇E(r) - ∇E(r₀))`, via the multipliers `G j r`
    set G : Fin 2 → ℝ → ℝ × ℝ → ℝ := fun j r x =>
      B0579.jb x ^ (m / 2) * B0579.pd j (UnforcedLeray.B0238.Ec tr (max r 0)) x with hG_def
    set h : Fin 2 → ℝ × ℝ → ℝ := fun j x => ‖u r₀ x j‖ with hh_def
    have hGcont : ∀ j r, Continuous (G j r) := by
      intro j r
      exact (B0579.continuous_jb_rpow _).mul
        (ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_Ec tr (le_max_right r 0)) j).continuous
    have hDj : ∀ j : Fin 2, Tendsto
        (fun r => eLpNorm ((fun x => G j r x * h j x) - fun x => G j r₀ x * h j x) 2 μ)
        (𝓝[Icc t₁ s] r₀) (𝓝 0) := by
      intro j
      refine Exist.tendsto_eLpNorm_mul_sub (C := CT) ((hU r₀ hr₀.1 j).norm) (G j) (G j r₀)
        (fun r => (hGcont j r).aestronglyMeasurable) (hGcont j r₀).aestronglyMeasurable ?_ ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with r hr
        filter_upwards [ae_restrict_mem hcell] with x hx
        simp only [hG_def, max_eq_left (ht₁.trans hr.1)]
        exact weighted_pd_le hCT ⟨ht₁.trans hr.1, hr.2⟩ hx j
      · filter_upwards [ae_restrict_mem hcell] with x hx
        simp only [hG_def, max_eq_left hr₀0]
        exact weighted_pd_le hCT ⟨hr₀0, hr₀.2⟩ hx j
      · refine Eventually.of_forall fun x => ?_
        have hpc : Continuous fun r => B0579.pd j (UnforcedLeray.B0238.Ec tr (max r 0)) x :=
          (PdEc.pdEc_continuousOn tr j x).comp_continuous (continuous_id.max continuous_const)
            (fun r => le_max_right r 0)
        exact ((hpc.tendsto r₀).const_mul (B0579.jb x ^ (m / 2))).mono_left nhdsWithin_le_nhds
    have hHle : ∀ r ∈ Icc t₁ s, xNorm (ν ^ (-2 : ℝ)) m (F r - F r₀ - L r) ≤
        eLpNorm ((fun x => G 0 r x * h 0 x) - fun x => G 0 r₀ x * h 0 x) 2 μ +
          eLpNorm ((fun x => G 1 r x * h 1 x) - fun x => G 1 r₀ x * h 1 x) 2 μ := by
      intro r hr
      have hr0 : 0 ≤ r := ht₁.trans hr.1
      unfold xNorm
      rw [ForceMemXAux.eLpNorm_cellMeasure_cx]
      refine (eLpNorm_mono_ae_real (g := fun x =>
        ‖((fun x => G 0 r x * h 0 x) - fun x => G 0 r₀ x * h 0 x) x‖ +
          ‖((fun x => G 1 r x * h 1 x) - fun x => G 1 r₀ x * h 1 x) x‖) ?_).trans ?_
      · refine Eventually.of_forall fun x => ?_
        have hw0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
        simp only [hG_def, hh_def, hF_def, hL_def, Pi.sub_apply, max_eq_left hr0,
          max_eq_left hr₀0, Real.norm_eq_abs, ladForce]
        rw [abs_of_nonneg (mul_nonneg hw0 (norm_nonneg _))]
        have e : u r x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
              u r x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) -
            (u r₀ x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ) +
              u r₀ x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r₀) x : ℝ) : ℂ)) -
            ((u r x 0 - u r₀ x 0) * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
              (u r x 1 - u r₀ x 1) * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) =
            u r₀ x 0 * (((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x -
                B0579.pd 0 (UnforcedLeray.B0238.Ec tr r₀) x : ℝ)) : ℂ) +
              u r₀ x 1 * (((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x -
                B0579.pd 1 (UnforcedLeray.B0238.Ec tr r₀) x : ℝ)) : ℂ) := by
          push_cast; ring
        rw [e]
        refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) hw0).trans (le_of_eq ?_)
        have k : ∀ (J p q a : ℝ), 0 ≤ J → 0 ≤ a →
            |J * p * a - J * q * a| = J * (a * |p - q|) := by
          intro J p q a hJ ha
          rw [show J * p * a - J * q * a = (J * a) * (p - q) by ring, abs_mul,
            abs_of_nonneg (mul_nonneg hJ ha)]
          ring
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, k _ _ _ _ hw0 (norm_nonneg _), k _ _ _ _ hw0 (norm_nonneg _)]
        ring
      · have hm0 : AEStronglyMeasurable
            ((fun x => G 0 r x * h 0 x) - fun x => G 0 r₀ x * h 0 x) μ :=
          ((hGcont 0 r).aestronglyMeasurable.mul (hU r₀ hr₀.1 0).1.norm).sub
            ((hGcont 0 r₀).aestronglyMeasurable.mul (hU r₀ hr₀.1 0).1.norm)
        have hm1 : AEStronglyMeasurable
            ((fun x => G 1 r x * h 1 x) - fun x => G 1 r₀ x * h 1 x) μ :=
          ((hGcont 1 r).aestronglyMeasurable.mul (hU r₀ hr₀.1 1).1.norm).sub
            ((hGcont 1 r₀).aestronglyMeasurable.mul (hU r₀ hr₀.1 1).1.norm)
        calc eLpNorm (fun x =>
              ‖((fun x => G 0 r x * h 0 x) - fun x => G 0 r₀ x * h 0 x) x‖ +
                ‖((fun x => G 1 r x * h 1 x) - fun x => G 1 r₀ x * h 1 x) x‖) 2 μ
            = eLpNorm ((fun x => ‖((fun x => G 0 r x * h 0 x) - fun x => G 0 r₀ x * h 0 x) x‖) +
                fun x => ‖((fun x => G 1 r x * h 1 x) - fun x => G 1 r₀ x * h 1 x) x‖) 2 μ := rfl
          _ ≤ eLpNorm (fun x => ‖((fun x => G 0 r x * h 0 x) - fun x => G 0 r₀ x * h 0 x) x‖) 2 μ +
              eLpNorm (fun x => ‖((fun x => G 1 r x * h 1 x) - fun x => G 1 r₀ x * h 1 x) x‖)
                2 μ := eLpNorm_add_le hm0.norm hm1.norm (by norm_num)
          _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]
    have hH : Tendsto (fun r => xNorm (ν ^ (-2 : ℝ)) m (F r - F r₀ - L r)) (𝓝[Icc t₁ s] r₀) (𝓝 0) := by
      have hsum := (hDj 0).add (hDj 1)
      rw [add_zero] at hsum
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall fun _ => zero_le) (eventually_nhdsWithin_of_forall hHle)
    have hwlim : Tendsto (fun r => xNorm (ν ^ (-2 : ℝ)) m (w r - w r₀)) (𝓝[Icc t₁ s] r₀) (𝓝 0) :=
      (hw.strongCont r₀ hr₀.1).mono_left (nhdsWithin_mono _ Icc_subset_Ici_self)
    have hLlim : Tendsto (fun r => ENNReal.ofReal CT *
        (ENNReal.ofReal CV * xNorm (ν ^ (-2 : ℝ)) m (w r - w r₀) +
          ENNReal.ofReal CV * xNorm (ν ^ (-2 : ℝ)) m (w r - w r₀))) (𝓝[Icc t₁ s] r₀) (𝓝 0) := by
      have h1 : Tendsto (fun r => ENNReal.ofReal CV * xNorm (ν ^ (-2 : ℝ)) m (w r - w r₀))
          (𝓝[Icc t₁ s] r₀) (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hwlim (Or.inr ENNReal.ofReal_ne_top)
      have h2 := h1.add h1
      rw [add_zero] at h2
      simpa using ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
    -- `‖F(r) - F(r₀)‖_{X_m} → 0`
    have hFlim : Tendsto (fun r => xNorm (ν ^ (-2 : ℝ)) m (F r - F r₀)) (𝓝[Icc t₁ s] r₀) (𝓝 0) := by
      have hsum := hLlim.add hH
      rw [add_zero] at hsum
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall fun _ => zero_le) (eventually_nhdsWithin_of_forall ?_)
      intro r hr
      have hdec : L r + (F r - F r₀ - L r) = F r - F r₀ := by abel
      calc xNorm (ν ^ (-2 : ℝ)) m (F r - F r₀)
          = xNorm (ν ^ (-2 : ℝ)) m (L r + (F r - F r₀ - L r)) := by rw [hdec]
        _ ≤ xNorm (ν ^ (-2 : ℝ)) m (L r) + xNorm (ν ^ (-2 : ℝ)) m (F r - F r₀ - L r) :=
          eLpNorm_add_le (hLm r hr).1.1 (((hF r hr).sub (hF r₀ hr₀)).sub (hLm r hr).1).1
            (by norm_num)
        _ ≤ _ := add_le_add (hLm r hr).2 le_rfl
    have hφlim : Tendsto (fun r => xNorm (ν ^ (-2 : ℝ)) (-m) (φ r - φ r₀)) (𝓝[Icc t₁ s] r₀) (𝓝 0) :=
      hφ.strongCont r₀ hr₀
    -- the bound on the increment of the rate
    have hbound : ∀ r ∈ Icc t₁ s,
        edist (∫ x in B0579.cell (ν ^ (-2 : ℝ)), F r x * φ r x) (∫ x in B0579.cell (ν ^ (-2 : ℝ)), F r₀ x * φ r₀ x) ≤
          xNorm (ν ^ (-2 : ℝ)) m (F r - F r₀) * (xNorm (ν ^ (-2 : ℝ)) (-m) (φ r - φ r₀) + xNorm (ν ^ (-2 : ℝ)) (-m) (φ r₀)) +
            xNorm (ν ^ (-2 : ℝ)) m (F r₀) * xNorm (ν ^ (-2 : ℝ)) (-m) (φ r - φ r₀) := by
      intro r hr
      have hA := hF r hr
      have hA₀ := hF r₀ hr₀
      have hB := hφm r hr
      have hB₀ := hφm r₀ hr₀
      have hi1 := (Leaf2DualityNeeded.pair_bound (hA.sub hA₀) hB).1
      have hi2 := (Leaf2DualityNeeded.pair_bound hA₀ (hB.sub hB₀)).1
      have hi3 := (Leaf2DualityNeeded.pair_bound hA hB).1
      have hi4 := (Leaf2DualityNeeded.pair_bound hA₀ hB₀).1
      have hsplit : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), F r x * φ r x) - ∫ x in B0579.cell (ν ^ (-2 : ℝ)), F r₀ x * φ r₀ x =
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), (F r - F r₀) x * φ r x) +
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), F r₀ x * (φ r - φ r₀) x := by
        rw [← integral_sub hi3 hi4, ← integral_add hi1 hi2]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.sub_apply]
        ring
      rw [edist_eq_enorm_sub, hsplit]
      refine (enorm_add_le _ _).trans (add_le_add ?_ (pair_enorm_le hA₀ (hB.sub hB₀)))
      refine (pair_enorm_le (hA.sub hA₀) hB).trans ?_
      have hdec : (φ r - φ r₀) + φ r₀ = φ r := by abel
      have hle : xNorm (ν ^ (-2 : ℝ)) (-m) (φ r) ≤
          xNorm (ν ^ (-2 : ℝ)) (-m) (φ r - φ r₀) + xNorm (ν ^ (-2 : ℝ)) (-m) (φ r₀) := by
        calc xNorm (ν ^ (-2 : ℝ)) (-m) (φ r)
            = xNorm (ν ^ (-2 : ℝ)) (-m) ((φ r - φ r₀) + φ r₀) := by rw [hdec]
          _ ≤ _ := eLpNorm_add_le (hB.sub hB₀).1 hB₀.1 (by norm_num)
      gcongr
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
    have hK : xNorm (ν ^ (-2 : ℝ)) (-m) (φ r₀) ≠ ⊤ := (hφm r₀ hr₀).2.ne
    have hK' : xNorm (ν ^ (-2 : ℝ)) m (F r₀) ≠ ⊤ := (hF r₀ hr₀).2.ne
    have hlim1 := ENNReal.Tendsto.mul hFlim (Or.inr (by
        rw [zero_add]; exact hK)) (hφlim.add (tendsto_const_nhds (x := xNorm (ν ^ (-2 : ℝ)) (-m) (φ r₀))))
      (Or.inr ENNReal.zero_ne_top)
    have hlim2 := ENNReal.Tendsto.const_mul hφlim (Or.inr hK')
    have hlim := hlim1.add hlim2
    simp only [zero_mul, mul_zero, add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) (eventually_nhdsWithin_of_forall hbound)
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
