import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.FluxPairDuhamel

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/6/2/2`: joint continuity of the adjoint flux pairing
(`AdjFluxPairContinuous`)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. The pairing `(r, θ) ↦ ℓ(F r; P_θ g)` is split into the variation in the
source `F` (controlled by a uniform `X_{-m,c}`-`X_m` bound on the smoothed tests, from
`AdjSmoothDecay`) and the variation in the time `θ` (dominated convergence).
Forward analogue: `Exist.fluxPairHeatContinuous` (`Clock/Existence/UnitHeatWeak/FluxContinuous.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A uniform constant for the pairing of `X_{-m,c}` with functions dominated by
`|D| (1+x.2²)^{-k}`, `k = m/2 + 1`. -/
theorem fdc_uniform_pair {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) :
    ∃ C : ℝ, ∀ (ψ : ℝ × ℝ → ℝ) (D : ℝ), Continuous ψ →
      (∀ x : ℝ × ℝ, |ψ x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) →
      ∀ w : AdjX c m, ‖∫ x in B0579.cell c, w x * ((ψ x : ℝ) : ℂ)‖ ≤ (|D| * C) * ‖w‖ := by
  have hk : (0:ℝ) ≤ m / 2 + 1 := by linarith
  have hcontH : Continuous (fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) := by
    apply Continuous.rpow_const (by fun_prop)
    intro x
    left
    positivity
  have hHmem : MemLp (fun x : ℝ × ℝ => (((1 + x.2 ^ 2) ^ (-(m / 2 + 1)) : ℝ) : ℂ)) 2
      (B0579.cellMeasure c m) :=
    fdj_memLp hm rfl hcontH (fun x hx =>
      fdj_cell_decay (C := 1) hc hk
        (h := fun x : ℝ × ℝ => (1 + x.2 ^ 2) ^ (-(m / 2 + 1)))
        (fun x => by
          show |(1 + x.2 ^ 2) ^ (-(m / 2 + 1))| ≤ 1 * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))
          exact le_of_eq (by rw [one_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]))
        hx)
  refine ⟨‖hHmem.toLp _‖, fun ψ D hψc hψb w => ?_⟩
  have hψmem : MemLp (fun x => ((ψ x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    fdj_memLp hm rfl hψc (fun x hx => fdj_cell_decay hc hk hψb hx)
  set ψX := hψmem.toLp _ with hψXdef
  set hX := hHmem.toLp _ with hhXdef
  have hnorm : ‖ψX‖ ≤ |D| * ‖hX‖ := by
    have h1 : ‖ψX‖ ≤ ‖|D| • hX‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [hψmem.coeFn_toLp, Lp.coeFn_smul |D| hX, hHmem.coeFn_toLp] with x e1 e2 e3
      rw [e1, e2, Pi.smul_apply, e3]
      have hψx : ‖((ψ x : ℝ) : ℂ)‖ ≤ |D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (hψb x) (mul_le_mul_of_nonneg_right (le_abs_self D)
          (Real.rpow_nonneg (by positivity) _))
      exact le_of_le_of_eq hψx (by
        rw [norm_smul, Real.norm_eq_abs, abs_abs, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by positivity) _)])
    rw [norm_smul, Real.norm_eq_abs, abs_abs] at h1
    exact h1
  have hae : (⇑ψX) =ᵐ[volume.restrict (B0579.cell c)] fun x => ((ψ x : ℝ) : ℂ) :=
    (B0579.ac_cellMeasure c m).ae_le hψmem.coeFn_toLp
  have hint : ∫ x in B0579.cell c, w x * ((ψ x : ℝ) : ℂ) = ∫ x in B0579.cell c, ψX x * w x :=
    integral_congr_ae (by
      filter_upwards [hae] with x hx
      rw [hx, mul_comm])
  rw [hint]
  have H := PairContAux.holder (Lp.memLp ψX) (Lp.memLp w)
  have hfin := H.2
  rw [← Lp.norm_def, ← Lp.norm_def] at hfin
  exact hfin.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Joint continuity of the pairing `(r, θ) ↦ ∫_cell w(r) P_θ-type(θ)` on `[a, b] × [0, Θ]`,
for a source path `w` continuous into `X_{-m,c}` and a family `ψ θ` jointly continuous with a
uniform decay bound. -/
theorem fdc_core {c m a b Θ D : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (hΘ : 0 ≤ Θ) {w : ℝ → AdjX c m}
    (hw : ContinuousOn w (Icc a b)) {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψc : Continuous (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hψb : ∀ θ ∈ Icc (0:ℝ) Θ, ∀ x : ℝ × ℝ, |ψ θ x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ x in B0579.cell c, w p.1 x * ((ψ p.2 x : ℝ) : ℂ))
      (Icc a b ×ˢ Icc (0:ℝ) Θ) := by
  obtain ⟨C, hC⟩ := fdc_uniform_pair (m := m) hc hm
  have hk : (0:ℝ) ≤ m / 2 + 1 := by linarith
  have hcontH : Continuous (fun x : ℝ × ℝ => |D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1))) := by
    apply Continuous.mul continuous_const
    apply Continuous.rpow_const (by fun_prop)
    intro x
    left
    positivity
  have hψcθ : ∀ θ : ℝ, Continuous (fun x : ℝ × ℝ => ψ θ x) := fun θ =>
    hψc.comp (continuous_const.prodMk continuous_id)
  have hdomInt : ∀ r : ℝ, Integrable
      (fun x => ‖w r x * ((|D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) : ℝ) : ℂ)‖)
      (volume.restrict (B0579.cell c)) := fun r =>
    (fdj_integrable_mul hc hm (Lp.memLp (w r)) hcontH
      (fun x => le_of_eq (abs_of_nonneg (by positivity)))).norm
  have hIntegr : ∀ r : ℝ, ∀ θ ∈ Icc (0:ℝ) Θ,
      IntegrableOn (fun x => w r x * ((ψ θ x : ℝ) : ℂ)) (B0579.cell c) := fun r θ hθ =>
    fdj_integrable_mul hc hm (Lp.memLp (w r)) (hψcθ θ) (hψb θ hθ)
  -- continuity in the time variable, for a fixed source
  have hθc : ∀ r : ℝ, ContinuousOn
      (fun θ : ℝ => ∫ x in B0579.cell c, w r x * ((ψ θ x : ℝ) : ℂ)) (Icc 0 Θ) := by
    intro r
    refine continuousOn_of_dominated (bound := fun x =>
        ‖w r x * ((|D| * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) : ℝ) : ℂ)‖) ?_ ?_ (hdomInt r) ?_
    · intro θ _
      exact ((Lp.aestronglyMeasurable (w r)).mono_ac (B0579.ac_cellMeasure c (-m))).mul
        (Complex.continuous_ofReal.comp (hψcθ θ)).aestronglyMeasurable
    · intro θ hθ
      refine Eventually.of_forall fun x => ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      rw [abs_of_nonneg (show (0:ℝ) ≤ (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) from
        Real.rpow_nonneg (by positivity) _)]
      exact mul_le_mul_of_nonneg_left
        (le_trans (hψb θ hθ x) (mul_le_mul_of_nonneg_right (le_abs_self D)
          (Real.rpow_nonneg (by positivity) _))) (norm_nonneg _)
    · refine Eventually.of_forall fun x => ?_
      have hx : Continuous (fun θ : ℝ => ψ θ x) :=
        hψc.comp (continuous_id.prodMk continuous_const)
      exact (continuousOn_const.mul (Complex.continuous_ofReal.comp hx).continuousOn)
  -- joint continuity
  intro p0 hp0
  set S := Icc a b ×ˢ Icc (0:ℝ) Θ with hS
  have hw_tend : Tendsto (fun p : ℝ × ℝ => ‖w p.1 - w p0.1‖) (𝓝[S] p0) (𝓝 0) := by
    have hcontw0 : ContinuousWithinAt w (Icc a b) p0.1 := hw p0.1 hp0.1
    have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[S] p0) (𝓝[Icc a b] p0.1) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun p hp => hp.1⟩
    have h1 : Tendsto (fun p : ℝ × ℝ => w p.1) (𝓝[S] p0) (𝓝 (w p0.1)) :=
      hcontw0.tendsto.comp hfst
    exact tendsto_iff_norm_sub_tendsto_zero.1 h1
  have hθ0 : ContinuousWithinAt
      (fun p : ℝ × ℝ => ∫ x in B0579.cell c, w p0.1 x * ((ψ p.2 x : ℝ) : ℂ)) S p0 := by
    have h := (hθc p0.1).comp continuous_snd.continuousOn
      (fun p (hp : p ∈ S) => (show p.2 ∈ Icc (0:ℝ) Θ from hp.2))
    exact h p0 hp0
  have hdiff : Tendsto (fun p : ℝ × ℝ =>
      (∫ x in B0579.cell c, w p.1 x * ((ψ p.2 x : ℝ) : ℂ)) -
        ∫ x in B0579.cell c, w p0.1 x * ((ψ p.2 x : ℝ) : ℂ)) (𝓝[S] p0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hw_tend.const_mul (|D| * C))
    filter_upwards [(self_mem_nhdsWithin : S ∈ 𝓝[S] p0)] with p hp
    have hsub : (∫ x in B0579.cell c, w p.1 x * ((ψ p.2 x : ℝ) : ℂ)) -
        ∫ x in B0579.cell c, w p0.1 x * ((ψ p.2 x : ℝ) : ℂ) =
        ∫ x in B0579.cell c, (w p.1 - w p0.1) x * ((ψ p.2 x : ℝ) : ℂ) := by
      rw [← integral_sub (hIntegr p.1 p.2 hp.2) (hIntegr p0.1 p.2 hp.2)]
      refine integral_congr_ae ?_
      filter_upwards [(B0579.ac_cellMeasure c (-m)).ae_le (Lp.coeFn_sub (w p.1) (w p0.1))] with x hx
      rw [hx]
      simp only [Pi.sub_apply]
      ring
    rw [hsub]
    exact hC (ψ p.2) D (hψcθ p.2) (hψb p.2 hp.2) (w p.1 - w p0.1)
  have hfin := hdiff.add hθ0
  rw [zero_add] at hfin
  exact Tendsto.congr (fun p => sub_add_cancel _ _) hfin

theorem adjFluxPairContinuous (m : ℝ) (hm : 8 < m) : AdjFluxPairContinuous m := by
  intro c hc F a b hF g hg Θ hΘ
  have hm0 : 0 ≤ m := by linarith
  have hk : (0:ℝ) ≤ m / 2 + 1 := by linarith
  have hbdP : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∃ D : ℝ, ∀ θ ∈ Icc (0:ℝ) Θ, ∀ x : ℝ × ℝ,
      |Exist.cylHeatSmooth c θ ψ x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := adjSmoothDecay c hc ψ hψ Θ (m / 2 + 1) hΘ hk
    refine ⟨|C|, fun θ hθ x => ?_⟩
    exact le_trans (hC θ hθ x)
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _))
  have hpdbd : ∀ j : Fin 2, ∃ D : ℝ, ∀ θ ∈ Icc (0:ℝ) Θ, ∀ x : ℝ × ℝ,
      |B0579.pd j (Exist.cylHeatSmooth c θ g) x| ≤ D * (1 + x.2 ^ 2) ^ (-(m / 2 + 1)) := by
    intro j
    obtain ⟨D, hD⟩ := hbdP (B0579.pd j g) (hg.pd j)
    refine ⟨D, fun θ hθ x => ?_⟩
    rw [Exist.pd_cylHeatSmooth hc hg j]
    exact hD θ hθ x
  obtain ⟨D0, hD0⟩ := hpdbd 0
  obtain ⟨D1, hD1⟩ := hpdbd 1
  obtain ⟨D2, hD2⟩ := hbdP g hg
  have hcont0 : ∀ j : Fin 2, Continuous
      (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (Exist.cylHeatSmooth c p.1 g) p.2) :=
    fun j => Exist.continuous_pd_cylHeatSmooth_joint hc hg j
  have hcont2 : Continuous (fun p : ℝ × (ℝ × ℝ) => Exist.cylHeatSmooth c p.1 g p.2) :=
    Exist.continuous_cylHeatSmooth_joint_test hc hg
  have hw0 : ContinuousOn (fun r => (F r).1 0) (Icc a b) :=
    ((continuous_apply 0).comp continuous_fst).comp_continuousOn hF
  have hw1 : ContinuousOn (fun r => (F r).1 1) (Icc a b) :=
    ((continuous_apply 1).comp continuous_fst).comp_continuousOn hF
  have hw2 : ContinuousOn (fun r => (F r).2) (Icc a b) :=
    continuous_snd.comp_continuousOn hF
  have C0 := fdc_core (w := fun r => (F r).1 0) (ψ := fun θ x =>
    B0579.pd 0 (Exist.cylHeatSmooth c θ g) x) hc hm0 hΘ hw0 (hcont0 0) hD0
  have C1 := fdc_core (w := fun r => (F r).1 1) (ψ := fun θ x =>
    B0579.pd 1 (Exist.cylHeatSmooth c θ g) x) hc hm0 hΘ hw1 (hcont0 1) hD1
  have C2 := fdc_core (w := fun r => (F r).2) (ψ := fun θ x =>
    Exist.cylHeatSmooth c θ g x) hc hm0 hΘ hw2 hcont2 hD2
  simp only [adjFluxPair]
  exact (C0.add C1).add C2

end UnforcedLeray.Short.IIIa
