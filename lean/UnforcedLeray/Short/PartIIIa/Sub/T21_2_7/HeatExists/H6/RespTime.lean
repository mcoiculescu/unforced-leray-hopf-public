import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.FluxPairDuhamel
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.FluxPairContinuous
import UnforcedLeray.Lib.EvolutionFamilies.Fubini

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/6/2`: the tested Duhamel identity of the response
(`AdjHeatRespTime`)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836.
Mirror of `Exist.unitHeatDuhamel_of` (`Clock/Existence/UnitHeatWeak/DuhamelOf.lean`) with
`fluxPair` replaced by `adjFluxPair`, the time `t - r` replaced by `ν (τ - r)`, and the
substitution `η = ν (u - r)` in the inner integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

private theorem adjRespTime_clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    max a (min b x) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem adjRespTime_clamp_eq {a b x : ℝ} (hx : x ∈ Icc a b) :
    max a (min b x) = x := by
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem adjHeatRespTime (m : ℝ) (hm : 8 < m) : AdjHeatRespTime m := by
  intro ν c hν hc F a b hab hb hF ψ hψ τ hτ
  have hΦ := adjFluxPairContinuous m hm c hc F a b hF (lapP ψ) (Exist.cylTest_lapP hψ) ν hν.le
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hΦ
  obtain ⟨Gc, hGcdef⟩ : ∃ Gc : ℝ × ℝ → ℂ, Gc = fun p =>
      adjFluxPair (F (max a (min b p.1))) (Exist.cylHeatSmooth c (max 0 (min ν p.2)) (lapP ψ)) :=
    ⟨_, rfl⟩
  have hGcapp : ∀ p : ℝ × ℝ, Gc p =
      adjFluxPair (F (max a (min b p.1))) (Exist.cylHeatSmooth c (max 0 (min ν p.2)) (lapP ψ)) :=
    fun p => by rw [hGcdef]
  have hmem : ∀ p : ℝ × ℝ, (max a (min b p.1), max 0 (min ν p.2)) ∈ Icc a b ×ˢ Icc (0 : ℝ) ν :=
    fun p => ⟨adjRespTime_clamp_mem hab p.1, adjRespTime_clamp_mem hν.le p.2⟩
  have hcl : Continuous (fun p : ℝ × ℝ => (max a (min b p.1), max 0 (min ν p.2))) := by
    fun_prop
  have hGcont : Continuous Gc := by
    have hGeq : Gc = (fun p : ℝ × ℝ =>
        adjFluxPair (F p.1) (Exist.cylHeatSmooth c p.2 (lapP ψ))) ∘
        (fun p : ℝ × ℝ => (max a (min b p.1), max 0 (min ν p.2))) :=
      funext fun p => hGcapp p
    rw [hGeq]
    exact hΦ.comp_continuous hcl hmem
  have hGbd : ∀ p, ‖Gc p‖ ≤ C := fun p => by
    rw [hGcapp p]
    exact hC (max a (min b p.1), max 0 (min ν p.2)) (hmem p)
  have hΦ' : ∀ r η : ℝ, r ∈ Icc a b → η ∈ Icc (0 : ℝ) ν →
      Gc (r, η) = adjFluxPair (F r) (Exist.cylHeatSmooth c η (lapP ψ)) := by
    intro r η hr hη
    have := hGcapp (r, η)
    simp only at this
    rw [this, adjRespTime_clamp_eq hr, adjRespTime_clamp_eq hη]
  -- pointwise Duhamel identity for the smoothed tests at `θ = ν (τ - r)`
  have hint1 : ∀ r ∈ uIcc a τ, adjFluxPair (F r) (Exist.cylHeatSmooth c (ν * (τ - r)) ψ) =
      adjFluxPair (F r) ψ + ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η) := by
    intro r hr
    rw [uIcc_of_le hτ.1] at hr
    have hτr : 0 ≤ τ - r := by linarith [hr.2]
    have hτr1 : τ - r ≤ 1 := by linarith [hr.1, hτ.2, hb]
    have hθ0 : 0 ≤ ν * (τ - r) := mul_nonneg hν.le hτr
    have hθle : ν * (τ - r) ≤ ν := by nlinarith [mul_nonneg hν.le (sub_nonneg.mpr hτr1)]
    rw [adjFluxPairDuhamel m hm c hc (F r) ψ hψ (ν * (τ - r)) hθ0]
    congr 1
    refine intervalIntegral.integral_congr (fun η hη => ?_)
    rw [uIcc_of_le hθ0] at hη
    show adjFluxPair (F r) (Exist.cylHeatSmooth c η (lapP ψ)) = Gc (r, η)
    rw [hΦ' r η ⟨hr.1, hr.2.trans hτ.2⟩ ⟨hη.1, hη.2.trans hθle⟩]
  -- substitution `η = ν (u - r)`
  have key : ∀ r ∈ Icc a τ, ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η) =
      (ν : ℂ) * ∫ u in r..τ, Gc (r, ν * (u - r)) := by
    intro r _
    have hn : ν ≠ 0 := hν.ne'
    have h1 : ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η) =
        ν • ∫ s in (0 : ℝ)..(τ - r), Gc (r, ν * s) := by
      have := intervalIntegral.integral_comp_mul_left (f := fun η => Gc (r, η))
        (a := 0) (b := τ - r) (c := ν) hn
      rw [this, mul_zero, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h2 : ∫ s in (0 : ℝ)..(τ - r), Gc (r, ν * s) =
        ∫ u in r..τ, Gc (r, ν * (u - r)) := by
      have := intervalIntegral.integral_comp_sub_right (f := fun u => Gc (r, ν * u))
        (a := r) (b := τ) r
      rw [sub_self] at this
      exact this.symm
    rw [h1, h2, Complex.real_smul]
  have hA0 := (adjFluxPairContinuous m hm c hc F a b hF ψ hψ ν hν.le).comp (continuousOn_id.prodMk (continuousOn_const (c := (0 : ℝ))))
    (fun x hx => ⟨hx, ⟨le_rfl, hν.le⟩⟩)
  have hA : ContinuousOn (fun r => adjFluxPair (F r) ψ) (Icc a b) := by
    refine hA0.congr ?_
    intro r _
    simp [Exist.cylHeatSmooth_zero]
  have hAint : IntervalIntegrable (fun r => adjFluxPair (F r) ψ) volume a τ :=
    ContinuousOn.intervalIntegrable_of_Icc hτ.1 (hA.mono (Icc_subset_Icc le_rfl hτ.2))
  have hBc : Continuous (fun r : ℝ => ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun r η => Gc (r, η)) hGcont (continuous_const.mul (continuous_const.sub continuous_id))
  have hBint : IntervalIntegrable (fun r : ℝ => ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η))
      volume a τ :=
    hBc.intervalIntegrable _ _
  have e : (∫ r in a..τ, adjFluxPair (F r) (Exist.cylHeatSmooth c (ν * (τ - r)) ψ)) =
      ∫ r in a..τ, (adjFluxPair (F r) ψ + ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η)) :=
    intervalIntegral.integral_congr hint1
  have hB : (∫ r in a..τ, ∫ η in (0 : ℝ)..(ν * (τ - r)), Gc (r, η)) =
      ∫ r in a..τ, (ν : ℂ) * ∫ u in r..τ, Gc (r, ν * (u - r)) := by
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [uIcc_of_le hτ.1] at hr
    exact key r hr
  -- triangle swap, in `ℂ`
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (q r : ℝ) => Gc (r, ν * (q - r)))
      (UnforcedLeray.Evolution.triMeasure a τ) :=
    (hGcont.comp (continuous_snd.prodMk (continuous_const.mul
      (continuous_fst.sub continuous_snd)))).aestronglyMeasurable
  have hK : ∀ q r : ℝ, a < r → r < q → q ≤ τ → ‖Gc (r, ν * (q - r))‖ ≤ C :=
    fun q r _ _ _ => hGbd _
  have tri := UnforcedLeray.Evolution.integral_triangle_swap (X := ℂ) hτ.1
    (G := fun q r => Gc (r, ν * (q - r))) hmeas hK
  have hswap : (∫ r in a..τ, ∫ u in r..τ, Gc (r, ν * (u - r))) =
      ∫ r in a..τ, ∫ σ in a..r, Gc (σ, ν * (r - σ)) := by
    exact tri.symm
  have hL : (∫ r in a..τ, (ν : ℂ) * ∫ u in r..τ, Gc (r, ν * (u - r))) =
      (ν : ℂ) * ∫ r in a..τ, ∫ σ in a..r, Gc (σ, ν * (r - σ)) := by
    rw [intervalIntegral.integral_const_mul, hswap]
  -- identify the integrand of the target with `Gc`
  have hK' : ∀ r ∈ Icc a τ, (∫ σ in a..r,
      adjFluxPair (F σ) (Exist.cylHeatSmooth c (ν * (r - σ)) (lapP ψ))) =
      ∫ σ in a..r, Gc (σ, ν * (r - σ)) := by
    intro r hr
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [uIcc_of_le hr.1] at hσ
    have hra1 : r - a ≤ 1 := by linarith [hr.2, hτ.2, hb]
    have hrs1 : r - σ ≤ 1 := by linarith [hσ.1, hra1]
    have hrs0 : 0 ≤ r - σ := by linarith [hσ.2]
    have hθ0 : 0 ≤ ν * (r - σ) := mul_nonneg hν.le hrs0
    have hθle : ν * (r - σ) ≤ ν := by nlinarith [mul_nonneg hν.le (sub_nonneg.mpr hrs1)]
    show adjFluxPair (F σ) (Exist.cylHeatSmooth c (ν * (r - σ)) (lapP ψ)) =
      Gc (σ, ν * (r - σ))
    rw [hΦ' σ (ν * (r - σ)) ⟨hσ.1, hσ.2.trans (hr.2.trans hτ.2)⟩ ⟨hθ0, hθle⟩]
  have hR : (∫ r in a..τ, (ν : ℂ) * ∫ σ in a..r,
      adjFluxPair (F σ) (Exist.cylHeatSmooth c (ν * (r - σ)) (lapP ψ))) =
      (ν : ℂ) * ∫ r in a..τ, ∫ σ in a..r, Gc (σ, ν * (r - σ)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_congr (fun r hr => by
      rw [uIcc_of_le hτ.1] at hr
      exact hK' r hr)
  rw [e, intervalIntegral.integral_add hAint hBint, hB, hL, ← hR, add_comm]

end UnforcedLeray.Short.IIIa
