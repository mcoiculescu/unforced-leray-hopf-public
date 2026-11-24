import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2_3_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Equations
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd

/-!
# `PartIII-a:T19/2/3/2/3/1/1` helper: flat-test stream decomposition and core uniqueness

Given the explicit nice-force free solution `(b_cl, G_cl)` and source `f` (from `Source.lean`) and
the Biot-Savart reconstructed Duhamel velocity/gradient `(u_duh, G_duh)` satisfying the
time-dependent cylinder-test identity (from `FlowKernel.lean`), this module proves that
`(b_cand, G_cand) = (b_cl + g • u_duh, G_cl + g • G_duh)` is an `IsCoreCausalSolution` on
`(0, coreEnd ν b)` and applies `coreCausalHomogeneousZero` to identify `corePerturbVort` a.e. on
`B0579.cell (ν ^ (-2 : ℝ))` with `ω_duh` (`=ᵐ fun x => ∫ t in Ioo 0 s, k_ker s t x`).

Source of record: `the November 2 reference manuscript` (SP), lines 3511-3515 and
3541-3545.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.CoreDuhamelNiceAux

open UnforcedLeray.Short.IIIa

/-! ## 1. Extending `H^1_{-9,c}` source pairing to all cylinder tests -/

private theorem hasWeakCellDerivC_of_cylTest {c : ℝ} {χ : ℝ × ℝ → ℝ}
    (hχ : B0579.IsCylTest c χ) (j : Fin 2) :
    HasWeakCellDerivC c j (fun x => (χ x : ℂ)) (fun x => (B0579.pd j χ x : ℂ)) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have hreal := (hχ.mul (hψ.pd j)).integrableOn
    simpa [Complex.ofReal_mul] using hreal.ofReal (𝕜 := ℂ)
  · have hreal := ((hχ.pd j).mul hψ).integrableOn
    simpa [Complex.ofReal_mul] using hreal.ofReal (𝕜 := ℂ)
  · have hibp := B0579.integral_mul_pd hχ hψ j
    have h1 : (fun x : ℝ × ℝ => (χ x : ℂ) * (B0579.pd j ψ x : ℂ)) =
        fun x => ((χ x * B0579.pd j ψ x : ℝ) : ℂ) := by
      funext x; push_cast; rfl
    have h2 : (fun x : ℝ × ℝ => (B0579.pd j χ x : ℂ) * (ψ x : ℂ)) =
        fun x => ((B0579.pd j χ x * ψ x : ℝ) : ℂ) := by
      funext x; push_cast; rfl
    rw [h1, h2, integral_complex_ofReal, integral_complex_ofReal, hibp, Complex.ofReal_neg]

private theorem integrableOn_const_mul_local {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (a : ℂ) {f : α → ℂ} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x => a * f x) s μ := by
  unfold IntegrableOn at hf ⊢
  exact hf.const_mul a

private theorem pd_eq_of_eventuallyEq {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h : f =ᶠ[𝓝 x] g) (k : Fin 2) : B0579.pd k f x = B0579.pd k g x := by
  unfold B0579.pd; rw [h.fderiv_eq]

private theorem pd_eq_zero_of_eventuallyEq {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h : f =ᶠ[𝓝 x] 0) (k : Fin 2) : B0579.pd k f x = 0 := by
  unfold B0579.pd; rw [h.fderiv_eq]; simp

private theorem hasWeakCellDerivC_const_mul {c : ℝ} {j : Fin 2} {φ g : ℝ × ℝ → ℂ}
    (a : ℂ) (h : HasWeakCellDerivC c j φ g) :
    HasWeakCellDerivC c j (fun x => a * φ x) (fun x => a * g x) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · exact (integrableOn_const_mul_local a (h.1 ψ hψ).1).congr_fun
      (fun _ _ => by ring) (B0579.measurableSet_cell c)
  · exact (integrableOn_const_mul_local a (h.1 ψ hψ).2).congr_fun
      (fun _ _ => by ring) (B0579.measurableSet_cell c)
  · simp_rw [mul_assoc, integral_const_mul, h.2 ψ hψ, mul_neg]

private theorem xNorm_const_mul_real {c m δ : ℝ} (hδ : 0 ≤ δ) (φ : ℝ × ℝ → ℂ) :
    xNorm c m (fun x => (δ : ℂ) * φ x) = ENNReal.ofReal δ * xNorm c m φ := by
  have heq : (fun x => (δ : ℂ) * φ x) = δ • φ := by
    funext x; simp [Complex.real_smul]
  rw [heq]
  unfold xNorm
  rw [eLpNorm_const_smul]
  simp [Real.enorm_eq_ofReal hδ]

private theorem h1Norm_cylTest_lt_top {c : ℝ} {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    h1Norm c 9 (fun x => (χ x : ℂ)) (fun j x => (B0579.pd j χ x : ℂ)) < ⊤ := by
  have h0 : xNorm c (-9) (fun x => (χ x : ℂ)) < ⊤ := ((hχ.memLp (-9)).ofReal (K := ℂ)).2
  have hg : ∀ j : Fin 2, xNorm c (-9) (fun x => (B0579.pd j χ x : ℂ)) < ⊤ := fun j =>
    (((hχ.pd j).memLp (-9)).ofReal (K := ℂ)).2
  unfold h1Norm
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  rw [Fin.sum_univ_two]
  exact (ENNReal.add_lt_top.2
    ⟨ENNReal.pow_lt_top h0, ENNReal.add_lt_top.2
      ⟨ENNReal.pow_lt_top (hg 0), ENNReal.pow_lt_top (hg 1)⟩⟩).ne

private theorem pairing_of_cylTest {c : ℝ} {f : ℝ × ℝ → ℂ} {a : ℝ × ℝ → Fin 2 → ℂ}
    (hpair : ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
      ∫ x in B0579.cell c, f x * φ x = coreSrcFun c a g)
    {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    ∫ x in B0579.cell c, f x * (χ x : ℂ) =
      coreSrcFun c a (fun j x => (B0579.pd j χ x : ℂ)) := by
  set φ₀ : ℝ × ℝ → ℂ := fun x => (χ x : ℂ)
  set g₀ : Fin 2 → ℝ × ℝ → ℂ := fun j x => (B0579.pd j χ x : ℂ)
  set M : ℝ≥0∞ := h1Norm c 9 φ₀ g₀
  have hM_lt : M < ⊤ := h1Norm_cylTest_lt_top hχ
  set δ : ℝ := (M.toReal + 1)⁻¹
  have hδ_pos : 0 < δ := inv_pos.2 (by positivity)
  have hδc_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ_pos.ne'
  have hg_δ : ∀ j, HasWeakCellDerivC c j (fun x => (δ : ℂ) * φ₀ x)
      (fun x => (δ : ℂ) * g₀ j x) :=
    fun j => hasWeakCellDerivC_const_mul (δ : ℂ) (hasWeakCellDerivC_of_cylTest hχ j)
  have hh1_δ : h1Norm c 9 (fun x => (δ : ℂ) * φ₀ x) (fun j x => (δ : ℂ) * g₀ j x) ≤ 1 := by
    unfold h1Norm
    simp_rw [xNorm_const_mul_real hδ_pos.le, mul_pow, Fin.sum_univ_two, ← mul_add]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hpow : (ENNReal.ofReal δ ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal δ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    have hM_eq : (xNorm c (-9) φ₀ ^ 2 +
        (xNorm c (-9) (g₀ 0) ^ 2 + xNorm c (-9) (g₀ 1) ^ 2)) ^ (1 / 2 : ℝ) = M := by
      simp [M, h1Norm, Fin.sum_univ_two]
    rw [hpow, hM_eq, ← ENNReal.ofReal_toReal hM_lt.ne, ← ENNReal.ofReal_mul hδ_pos.le]
    refine ENNReal.ofReal_le_one.2 ?_
    have hden : 0 < M.toReal + 1 := by positivity
    calc δ * M.toReal ≤ δ * (M.toReal + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hδ_pos.le
      _ = 1 := inv_mul_cancel₀ hden.ne'
  have hscaled := hpair _ _ hg_δ hh1_δ
  have hL : ∫ x in B0579.cell c, f x * ((δ : ℂ) * φ₀ x) =
      (δ : ℂ) * ∫ x in B0579.cell c, f x * φ₀ x := by
    have heq : (fun x => f x * ((δ : ℂ) * φ₀ x)) = fun x => (δ : ℂ) * (f x * φ₀ x) := by
      funext x; ring
    rw [heq, integral_const_mul]
  have hR : coreSrcFun c a (fun j x => (δ : ℂ) * g₀ j x) =
      (δ : ℂ) * coreSrcFun c a g₀ := by
    unfold coreSrcFun
    have heq : (fun x => a x 1 * ((δ : ℂ) * g₀ 0 x) - a x 0 * ((δ : ℂ) * g₀ 1 x)) =
        fun x => (δ : ℂ) * (a x 1 * g₀ 0 x - a x 0 * g₀ 1 x) := by
      funext x; ring
    rw [heq, integral_const_mul]
  rw [hL, hR] at hscaled
  exact mul_left_cancel₀ hδc_ne hscaled

/-! ## 2. `flatDiffIntegrand` and the `perpF ∘ ψ` identity -/

private def flatDiffIntegrand (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (b_cand b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ i : Fin 2,
    (-(b_1 p i * (flatDt Φ p.1 p.2 i : ℂ)) + (μ / (p.1 : ℂ)) * b_1 p i * (Φ p.1 p.2 i : ℂ) -
      (ν : ℂ) * b_1 p i * (flatLap Φ p.1 p.2 i : ℂ) -
      ∑ j : Fin 2, (((vel p.1 p.2 i : ℂ) * b_cand p j + b_cand p i * (vel p.1 p.2 j : ℂ))) *
        (flatGrad Φ p.1 p.2 i j : ℂ))

private theorem flatIntegrand_eq_add_diff (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b_cl b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν μ vel F (fun q i => b_cl q i + b_1 q i) Φ p =
      flatIntegrand ν μ (fun _ _ _ => 0) F b_cl Φ p +
        flatDiffIntegrand ν μ vel (fun q i => b_cl q i + b_1 q i) b_1 Φ p := by
  simp only [flatIntegrand, flatDiffIntegrand, Fin.sum_univ_two]
  push_cast
  ring

private theorem flatDiffIntegrand_sub_test (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (b_cand b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ₁ Φ₂ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (h₁ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ₁ p.1 p.2 i))
    (h₂ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ₂ p.1 p.2 i))
    (p : ℝ × (ℝ × ℝ)) :
    flatDiffIntegrand ν μ vel b_cand b_1 (fun s x i => Φ₁ s x i - Φ₂ s x i) p =
      flatDiffIntegrand ν μ vel b_cand b_1 Φ₁ p -
        flatDiffIntegrand ν μ vel b_cand b_1 Φ₂ p := by
  have hdt : ∀ i : Fin 2, flatDt (fun s x i => Φ₁ s x i - Φ₂ s x i) p.1 p.2 i =
      flatDt Φ₁ p.1 p.2 i - flatDt Φ₂ p.1 p.2 i := by
    intro i
    unfold flatDt
    have hd1 : DifferentiableAt ℝ (fun s' => Φ₁ s' p.2 i) p.1 :=
      ((h₁ i).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1
    have hd2 : DifferentiableAt ℝ (fun s' => Φ₂ s' p.2 i) p.1 :=
      ((h₂ i).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1
    exact deriv_sub hd1 hd2
  have hgr : ∀ i j : Fin 2, flatGrad (fun s x i => Φ₁ s x i - Φ₂ s x i) p.1 p.2 i j =
      flatGrad Φ₁ p.1 p.2 i j - flatGrad Φ₂ p.1 p.2 i j := by
    intro i j
    unfold flatGrad B0579.pd
    have hd1 : DifferentiableAt ℝ (fun y => Φ₁ p.1 y i) p.2 :=
      ((h₁ i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
    have hd2 : DifferentiableAt ℝ (fun y => Φ₂ p.1 y i) p.2 :=
      ((h₂ i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
    change (fderiv ℝ ((fun y => Φ₁ p.1 y i) - (fun y => Φ₂ p.1 y i)) p.2) (B0579.dir j) = _
    rw [fderiv_sub hd1 hd2, sub_apply]
  have hlp : ∀ i : Fin 2, flatLap (fun s x i => Φ₁ s x i - Φ₂ s x i) p.1 p.2 i =
      flatLap Φ₁ p.1 p.2 i - flatLap Φ₂ p.1 p.2 i := by
    intro i
    unfold flatLap lapP
    have hc1 : ContDiff ℝ ∞ (fun y => Φ₁ p.1 y i) :=
      (h₁ i).comp (contDiff_const.prodMk contDiff_id)
    have hc2 : ContDiff ℝ ∞ (fun y => Φ₂ p.1 y i) :=
      (h₂ i).comp (contDiff_const.prodMk contDiff_id)
    have hpd_sub : ∀ k : Fin 2, B0579.pd k (fun y => Φ₁ p.1 y i - Φ₂ p.1 y i) =
        fun y => B0579.pd k (fun z => Φ₁ p.1 z i) y - B0579.pd k (fun z => Φ₂ p.1 z i) y := by
      intro k; funext y; unfold B0579.pd
      change (fderiv ℝ ((fun z => Φ₁ p.1 z i) - (fun z => Φ₂ p.1 z i)) y) (B0579.dir k) = _
      rw [fderiv_sub (hc1.differentiable (by simp) y) (hc2.differentiable (by simp) y),
        sub_apply]
    have hpd2 : ∀ k : Fin 2,
        B0579.pd k (fun y => B0579.pd k (fun z => Φ₁ p.1 z i) y -
          B0579.pd k (fun z => Φ₂ p.1 z i) y) p.2 =
        B0579.pd k (B0579.pd k (fun z => Φ₁ p.1 z i)) p.2 -
          B0579.pd k (B0579.pd k (fun z => Φ₂ p.1 z i)) p.2 := by
      intro k; unfold B0579.pd
      have d1 : DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => Φ₁ p.1 z i) y (B0579.dir k)) p.2 :=
        ((hc1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable
          (by simp) p.2
      have d2 : DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => Φ₂ p.1 z i) y (B0579.dir k)) p.2 :=
        ((hc2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable
          (by simp) p.2
      change (fderiv ℝ ((fun z => fderiv ℝ (fun w => Φ₁ p.1 w i) z (B0579.dir k)) -
        (fun z => fderiv ℝ (fun w => Φ₂ p.1 w i) z (B0579.dir k))) p.2) (B0579.dir k) = _
      rw [fderiv_sub d1 d2, sub_apply]
    rw [hpd_sub 0, hpd_sub 1, hpd2 0, hpd2 1]
    ring
  simp only [flatDiffIntegrand, hdt, hgr, hlp, Fin.sum_univ_two]
  push_cast
  ring

private theorem deriv_pd_comm {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (j : Fin 2) (ρ : ℝ) (x : ℝ × ℝ) :
    deriv (fun ρ' => B0579.pd j (ψ ρ') x) ρ =
      B0579.pd j (fun y => deriv (fun ρ' => ψ ρ' y) ρ) x := by
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun p => ψ p.1 p.2
  set v₁ : ℝ × (ℝ × ℝ) := (1, (0, 0))
  set v₂ : ℝ × (ℝ × ℝ) := (0, B0579.dir j)
  have hΨ_diff : Differentiable ℝ Ψ := hψ.differentiable (by simp)
  have hfd_diff : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h_pd : ∀ ρ' : ℝ, B0579.pd j (ψ ρ') x = fderiv ℝ Ψ (ρ', x) v₂ := by
    intro ρ'
    unfold B0579.pd
    have hcomp : HasFDerivAt (ψ ρ')
        ((fderiv ℝ Ψ (ρ', x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
      (hΨ_diff (ρ', x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right ρ' x)
    rw [hcomp.fderiv]
    rfl
  have h_dt : ∀ y : ℝ × ℝ, deriv (fun ρ' => ψ ρ' y) ρ = fderiv ℝ Ψ (ρ, y) v₁ := by
    intro y
    have hcomp : HasDerivAt (fun ρ' => ψ ρ' y) (fderiv ℝ Ψ (ρ, y) v₁) ρ := by
      have h1 : HasDerivAt (fun ρ' : ℝ => (ρ', y)) v₁ ρ :=
        (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ y)
      exact (hΨ_diff (ρ, y)).hasFDerivAt.comp_hasDerivAt ρ h1
    exact hcomp.deriv
  simp_rw [h_pd, h_dt]
  have hLHS : HasDerivAt (fun ρ' => fderiv ℝ Ψ (ρ', x) v₂)
      (fderiv ℝ (fderiv ℝ Ψ) (ρ, x) v₁ v₂) ρ := by
    have h1 : HasDerivAt (fun ρ' : ℝ => (ρ', x)) v₁ ρ :=
      (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
    have h2 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p v₂)
        ((ContinuousLinearMap.apply ℝ ℝ v₂).comp (fderiv ℝ (fderiv ℝ Ψ) (ρ, x))) (ρ, x) :=
      (ContinuousLinearMap.apply ℝ ℝ v₂).hasFDerivAt.comp (ρ, x) (hfd_diff (ρ, x)).hasFDerivAt
    exact h2.comp_hasDerivAt ρ h1
  have hRHS : B0579.pd j (fun y => fderiv ℝ Ψ (ρ, y) v₁) x =
      fderiv ℝ (fderiv ℝ Ψ) (ρ, x) v₂ v₁ := by
    unfold B0579.pd
    have h2 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p v₁)
        ((ContinuousLinearMap.apply ℝ ℝ v₁).comp (fderiv ℝ (fderiv ℝ Ψ) (ρ, x))) (ρ, x) :=
      (ContinuousLinearMap.apply ℝ ℝ v₁).hasFDerivAt.comp (ρ, x) (hfd_diff (ρ, x)).hasFDerivAt
    have hcomp := h2.comp x (hasFDerivAt_prodMk_right ρ x)
    exact DFunLike.congr_fun hcomp.fderiv (B0579.dir j)
  rw [hLHS.deriv, hRHS]
  have hsymm : IsSymmSndFDerivAt ℝ Ψ (ρ, x) :=
    (hψ.contDiffAt (x := (ρ, x))).isSymmSndFDerivAt (by simp)
  exact hsymm.eq v₁ v₂

private theorem isCylTest_slice {c R₁ : ℝ} {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + c, x.2) = ψ s x)
    (hband : ∀ s x, R₁ < |x.2| → ψ s x = 0) (ρ : ℝ) :
    B0579.IsCylTest c (ψ ρ) where
  smooth := hψ.comp (contDiff_const.prodMk contDiff_id)
  periodic x := hper ρ x
  band := ⟨R₁, fun x hx => hband ρ x hx⟩

private theorem isCylTest_dt_slice {c R₁ : ℝ} {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + c, x.2) = ψ s x)
    (hband : ∀ s x, R₁ < |x.2| → ψ s x = 0) (ρ : ℝ) :
    B0579.IsCylTest c (fun x => deriv (fun ρ' => ψ ρ' x) ρ) := by
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun p => ψ p.1 p.2
  have h_dt_eq : (fun x : ℝ × ℝ => deriv (fun ρ' => ψ ρ' x) ρ) =
      fun x => fderiv ℝ Ψ (ρ, x) (1, (0, 0)) := by
    funext x
    have h1 : HasDerivAt (fun ρ' : ℝ => (ρ', x)) (1, (0, 0)) ρ :=
      (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
    exact ((hψ.differentiable (by simp) (ρ, x)).hasFDerivAt.comp_hasDerivAt ρ h1).deriv
  refine ⟨?_, ?_, ⟨R₁, ?_⟩⟩
  · rw [h_dt_eq]
    exact ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).comp
      (contDiff_const.prodMk contDiff_id)
  · intro x
    simp only [hper _ x]
  · intro x hx
    have heq : (fun ρ' => ψ ρ' x) = fun _ => 0 := funext fun ρ' => hband ρ' x hx
    simp [heq]

private theorem wk_iz_slice {c : ℝ} {b : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun x => b x i) (fun x => G x i j))
    (i j : Fin 2) {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    V1.IZ c (fun x => G x i j * (χ x : ℂ) + b x i * (B0579.pd j χ x : ℂ)) := by
  obtain ⟨h1, h2⟩ := (hw i j).1 χ hχ
  refine ⟨h2.add h1, ?_⟩
  rw [integral_add h2 h1, (hw i j).2 χ hχ]
  ring

private theorem dv_iz_slice {c : ℝ} {b : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun x => b x i) (fun x => G x i j))
    (hd : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (b x 0 * (B0579.pd 0 ψ x : ℂ) + b x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    V1.IZ c (fun x => b x 0 * (B0579.pd 0 χ x : ℂ) + b x 1 * (B0579.pd 1 χ x : ℂ)) :=
  ⟨(((hw 0 0).1 χ hχ).1).add (((hw 1 1).1 χ hχ).1), hd χ hχ⟩

private theorem curl_pair_eq {c : ℝ} {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    {w : ℝ × ℝ → ℂ}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j))
    (hcurl : (fun x => G x 1 0 - G x 0 1) =ᵐ[volume.restrict (B0579.cell c)] w)
    {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    ∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 χ x : ℂ) - u x 1 * (B0579.pd 0 χ x : ℂ)) =
      ∫ x in B0579.cell c, w x * (χ x : ℂ) := by
  have h01 := hw 0 1
  have h10 := hw 1 0
  have Iu0 := (h01.1 χ hχ).1
  have IG0 := (h01.1 χ hχ).2
  have Iu1 := (h10.1 χ hχ).1
  have IG1 := (h10.1 χ hχ).2
  rw [integral_sub Iu0 Iu1, h01.2 χ hχ, h10.2 χ hχ]
  have hsub : -(∫ x in B0579.cell c, G x 0 1 * (χ x : ℂ)) -
      -(∫ x in B0579.cell c, G x 1 0 * (χ x : ℂ)) =
      ∫ x in B0579.cell c, (G x 1 0 - G x 0 1) * (χ x : ℂ) := by
    have heq : (fun x => (G x 1 0 - G x 0 1) * (χ x : ℂ)) =
        fun x => G x 1 0 * (χ x : ℂ) - G x 0 1 * (χ x : ℂ) := by funext x; ring
    rw [heq, integral_sub IG1 IG0]
    ring
  rw [hsub]
  refine integral_congr_ae ?_
  filter_upwards [hcurl] with x hx
  rw [← hx]

/-! ## 3. Space-time `L²` integrability of `flatDiffIntegrand` on bounded strips -/

private theorem gainG_le_of_le {γ ν s H : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν)
    (hs0 : 0 ≤ s) (hsH : s ≤ H) :
    0 < gainG γ ν s ∧ gainG γ ν s ≤ Real.exp (γ * H) := by
  unfold gainG
  refine ⟨Real.exp_pos _, Real.exp_le_exp.2 ?_⟩
  have hden : 1 ≤ 1 + ν * s := by nlinarith
  calc γ * s / (1 + ν * s) ≤ γ * s := div_le_self (mul_nonneg hγ hs0) hden
    _ ≤ γ * H := mul_le_mul_of_nonneg_left hsH hγ

private theorem measurable_gainG_fst (γ ν : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => gainG γ ν p.1 := by
  unfold gainG
  exact Real.measurable_exp.comp ((measurable_const.mul measurable_fst).div
    (measurable_const.add (measurable_const.mul measurable_fst)))

private theorem vnorm2_smul_sq {a : ℝ} (u : Fin 2 → ℂ) :
    vnorm2 (a • u) ^ 2 = a ^ 2 * vnorm2 u ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem tnorm2_smul_sq {a : ℝ} (G : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (a • G) ^ 2 = a ^ 2 * tnorm2 G ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Pi.smul_apply, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem vnorm2_add_sq_le (u v : Fin 2 → ℂ) :
    vnorm2 (fun i => u i + v i) ^ 2 ≤ 2 * vnorm2 u ^ 2 + 2 * vnorm2 v ^ 2 := by
  have heq : (fun i => u i + v i) = fun i => u i - (-v i) := by funext i; ring
  have hnv : vnorm2 (fun i => -v i) = vnorm2 v := by
    unfold vnorm2; simp [norm_neg]
  rw [heq]
  simpa [hnv] using causalLin_vnorm2_sub_sq_le u (fun i => -v i)

private theorem tnorm2_add_sq_le (G₁ G₂ : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => G₁ i j + G₂ i j) ^ 2 ≤ 2 * tnorm2 G₁ ^ 2 + 2 * tnorm2 G₂ ^ 2 := by
  have heq : (fun i j => G₁ i j + G₂ i j) = fun i j => G₁ i j - (-G₂ i j) := by funext i j; ring
  have hnv : tnorm2 (fun i j => -G₂ i j) = tnorm2 G₂ := by
    unfold tnorm2; simp [norm_neg]
  rw [heq]
  simpa [hnv] using causalLin_tnorm2_sub_sq_le G₁ (fun i j => -G₂ i j)

private theorem energyLoc_cand {c ν γ H s₁ s₂ M_duh : ℝ}
    (hγ : 0 ≤ γ) (hν : 0 < ν) (hs₁ : 0 < s₁) (_hs₁₂ : s₁ < s₂) (hs₂H : s₂ < H)
    (_hM : 0 ≤ M_duh)
    {b_cl u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G_cl G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hbcl_meas : ∀ i, Measurable fun p => b_cl p i)
    (hGcl_meas : ∀ i j, Measurable fun p => G_cl p i j)
    (hbcl_loc : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) < ⊤)
    (huduh_meas : ∀ i, Measurable fun p => u_duh p i)
    (hGduh_meas : ∀ i j, Measurable fun p => G_duh p i j)
    (hduh_bd : ∀ s ∈ Ioo (0 : ℝ) H,
      ∫⁻ x in B0579.cell c,
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
          ENNReal.ofReal M_duh) :
    let b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p => gainG γ ν p.1 • u_duh p
    let G_1 : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p => gainG γ ν p.1 • G_duh p
    let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
    let G_cand : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => G_cl p i j + G_1 p i j
    (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b_1 p) ^ 2 + tnorm2 (G_1 p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b_cand p) ^ 2 + tnorm2 (G_cand p) ^ 2) < ⊤) ∧
      IntegrableOn (fun p => (vnorm2 (b_1 p) + vnorm2 (b_cand p)) ^ 2)
        (Icc s₁ s₂ ×ˢ B0579.cell c) := by
  intro b_1 G_1 b_cand G_cand
  have hg_meas := measurable_gainG_fst γ ν
  have hb1_meas : ∀ i, Measurable fun p => b_1 p i := fun i => hg_meas.smul (huduh_meas i)
  have hbcand_meas : ∀ i, Measurable fun p => b_cand p i :=
    fun i => (hbcl_meas i).add (hb1_meas i)
  have hduh_prod_meas : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (u_duh p) ^ 2 + tnorm2 (G_duh p) ^ 2) :=
    (((causalLin_measurable_vnorm2 huduh_meas).pow_const 2).add
      ((causalLin_measurable_tnorm2 hGduh_meas).pow_const 2)).ennreal_ofReal
  have hduh_lint : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (u_duh p) ^ 2 + tnorm2 (G_duh p) ^ 2) < ⊤ := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hduh_prod_meas.aemeasurable]
    have hle : ∫⁻ s in Icc s₁ s₂,
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2)) ≤
        ∫⁻ _ in Icc s₁ s₂, ENNReal.ofReal M_duh := by
      refine setLIntegral_mono measurable_const fun s hs => ?_
      exact hduh_bd s ⟨lt_of_lt_of_le hs₁ hs.1, lt_of_le_of_lt hs.2 hs₂H⟩
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hb1_lt : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (b_1 p) ^ 2 + tnorm2 (G_1 p) ^ 2) < ⊤ := by
    have hmono : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (b_1 p) ^ 2 + tnorm2 (G_1 p) ^ 2) ≤
        ENNReal.ofReal (Real.exp (γ * H) ^ 2) *
          ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (u_duh p) ^ 2 + tnorm2 (G_duh p) ^ 2) := by
      rw [← lintegral_const_mul _ hduh_prod_meas]
      refine setLIntegral_mono (hduh_prod_meas.const_mul _) fun p hp => ?_
      have hg := gainG_le_of_le hγ hν (hs₁.le.trans hp.1.1) (hp.1.2.trans hs₂H.le)
      have hsq : gainG γ ν p.1 ^ 2 ≤ Real.exp (γ * H) ^ 2 :=
        pow_le_pow_left₀ hg.1.le hg.2 2
      have hnn : 0 ≤ vnorm2 (u_duh p) ^ 2 + tnorm2 (G_duh p) ^ 2 := by positivity
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      dsimp only [b_1, G_1]
      rw [vnorm2_smul_sq, tnorm2_smul_sq, ← mul_add]
      exact mul_le_mul_of_nonneg_right hsq hnn
    exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hduh_lint)
  have hcand_lt : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (b_cand p) ^ 2 + tnorm2 (G_cand p) ^ 2) < ⊤ := by
    have hX : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2 :=
      ((causalLin_measurable_vnorm2 hbcl_meas).pow_const 2).add
        ((causalLin_measurable_tnorm2 hGcl_meas).pow_const 2)
    have hD : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (b_cand p) ^ 2 + tnorm2 (G_cand p) ^ 2 ≤
          2 * (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) +
            2 * (vnorm2 (b_1 p) ^ 2 + tnorm2 (G_1 p) ^ 2) := fun p => by
      linarith [vnorm2_add_sq_le (b_cl p) (b_1 p), tnorm2_add_sq_le (G_cl p) (G_1 p)]
    have key := causalLin_lintegral_le (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) hX hD
    exact lt_of_le_of_lt key (by finiteness)
  refine ⟨hb1_lt, hcand_lt, ?_⟩
  have hmeas_sum : Measurable fun p : ℝ × (ℝ × ℝ) => (vnorm2 (b_1 p) + vnorm2 (b_cand p)) ^ 2 :=
    ((causalLin_measurable_vnorm2 hb1_meas).add
      (causalLin_measurable_vnorm2 hbcand_meas)).pow_const 2
  refine ⟨hmeas_sum.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)]
  have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal ((vnorm2 (b_1 p) + vnorm2 (b_cand p)) ^ 2) ≤
      ENNReal.ofReal 2 *
        (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b_1 p) ^ 2 + tnorm2 (G_1 p) ^ 2)) +
      ENNReal.ofReal 2 *
        (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b_cand p) ^ 2 + tnorm2 (G_cand p) ^ 2)) := by
    have hm1 : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (vnorm2 (b_1 p) ^ 2 + tnorm2 (G_1 p) ^ 2) :=
      (((causalLin_measurable_vnorm2 hb1_meas).pow_const 2).add
        ((causalLin_measurable_tnorm2 (fun i j => hg_meas.smul (hGduh_meas i j))).pow_const 2)).ennreal_ofReal
    have hm2 : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (vnorm2 (b_cand p) ^ 2 + tnorm2 (G_cand p) ^ 2) :=
      (((causalLin_measurable_vnorm2 hbcand_meas).pow_const 2).add
        ((causalLin_measurable_tnorm2
          (fun i j => (hGcl_meas i j).add (hg_meas.smul (hGduh_meas i j)))).pow_const 2)).ennreal_ofReal
    rw [← lintegral_const_mul _ hm1, ← lintegral_const_mul _ hm2,
      ← lintegral_add_left (hm1.const_mul _)]
    refine lintegral_mono fun p => ?_
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (vnorm2 (b_1 p) - vnorm2 (b_cand p)),
      sq_nonneg (tnorm2 (G_1 p)), sq_nonneg (tnorm2 (G_cand p))]
  exact lt_of_le_of_lt hle (by finiteness)

private theorem flatDerivs_zero_outside {s₁ s₂ R : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R < |x.2|) → Φ s x i = 0)
    {s : ℝ} {x : ℝ × ℝ} (hout : s < s₁ ∨ s₂ < s ∨ R < |x.2|) :
    (∀ i, Φ s x i = 0) ∧
      (∀ i, flatDt Φ s x i = 0) ∧
      (∀ i j, flatGrad Φ s x i j = 0) ∧
      (∀ i, flatLap Φ s x i = 0) := by
  have h0 : ∀ i, Φ s x i = 0 := fun i => hsupp s x i hout
  rcases hout with hs | hs | hx
  · have hUt : {s' : ℝ | s' < s₁} ∈ 𝓝 s :=
      (isOpen_lt continuous_id continuous_const).mem_nhds hs
    have hslice : ∀ i, (fun y => Φ s y i) = 0 := fun i => funext fun y => hsupp s y i (Or.inl hs)
    refine ⟨h0, fun i => ?_, fun i j => ?_, fun i => ?_⟩
    · unfold flatDt
      have hev : (fun s' => Φ s' x i) =ᶠ[𝓝 s] 0 :=
        Filter.eventually_of_mem hUt fun s' hs' => hsupp s' x i (Or.inl hs')
      rw [hev.deriv_eq]; simp
    · unfold flatGrad B0579.pd; rw [hslice i]; simp
    · unfold flatLap lapP B0579.pd; rw [hslice i]; simp
  · have hUt : {s' : ℝ | s₂ < s'} ∈ 𝓝 s :=
      (isOpen_lt continuous_const continuous_id).mem_nhds hs
    have hslice : ∀ i, (fun y => Φ s y i) = 0 :=
      fun i => funext fun y => hsupp s y i (Or.inr (Or.inl hs))
    refine ⟨h0, fun i => ?_, fun i j => ?_, fun i => ?_⟩
    · unfold flatDt
      have hev : (fun s' => Φ s' x i) =ᶠ[𝓝 s] 0 :=
        Filter.eventually_of_mem hUt fun s' hs' => hsupp s' x i (Or.inr (Or.inl hs'))
      rw [hev.deriv_eq]; simp
    · unfold flatGrad B0579.pd; rw [hslice i]; simp
    · unfold flatLap lapP B0579.pd; rw [hslice i]; simp
  · have hUx_open : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hUx : {y : ℝ × ℝ | R < |y.2|} ∈ 𝓝 x := hUx_open.mem_nhds hx
    have hpd_zero_on : ∀ y ∈ {y : ℝ × ℝ | R < |y.2|}, ∀ i k,
        B0579.pd k (fun z => Φ s z i) y = 0 := by
      intro y hy i k
      have hev : (fun z => Φ s z i) =ᶠ[𝓝 y] 0 :=
        Filter.eventually_of_mem (hUx_open.mem_nhds hy) fun z hz => hsupp s z i (Or.inr (Or.inr hz))
      exact pd_eq_zero_of_eventuallyEq hev k
    have hpd_ev : ∀ i k, B0579.pd k (fun y => Φ s y i) =ᶠ[𝓝 x] 0 :=
      fun i k => Filter.eventually_of_mem hUx fun y hy => hpd_zero_on y hy i k
    refine ⟨h0, fun i => ?_, fun i j => ?_, fun i => ?_⟩
    · unfold flatDt
      have heq : (fun s' => Φ s' x i) = 0 :=
        funext fun s' => hsupp s' x i (Or.inr (Or.inr hx))
      rw [heq]; simp
    · unfold flatGrad; exact hpd_zero_on x hx i j
    · unfold flatLap lapP
      have h00 : B0579.pd 0 (B0579.pd 0 (fun y => Φ s y i)) x = 0 :=
        pd_eq_zero_of_eventuallyEq (hpd_ev i 0) 0
      have h11 : B0579.pd 1 (B0579.pd 1 (fun y => Φ s y i)) x = 0 :=
        pd_eq_zero_of_eventuallyEq (hpd_ev i 1) 1
      rw [h00, h11, add_zero]

private theorem flatDiffIntegrand_zero_outside {ν s₁ s₂ R : ℝ} {μ : ℂ}
    {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ} {b_cand b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R < |x.2|) → Φ s x i = 0)
    {p : ℝ × (ℝ × ℝ)} (hout : p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) :
    flatDiffIntegrand ν μ vel b_cand b_1 Φ p = 0 := by
  obtain ⟨h0, hdt, hgr, hlp⟩ := flatDerivs_zero_outside hsupp hout
  simp [flatDiffIntegrand, h0, hdt, hgr, hlp]

private theorem contDiff_flatDt {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i)) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => flatDt Φ p.1 p.2 i) := by
  set F : ℝ × (ℝ × ℝ) → ℝ := fun p => Φ p.1 p.2 i
  have heq : (fun p : ℝ × (ℝ × ℝ) => flatDt Φ p.1 p.2 i) =
      fun p => fderiv ℝ F p (1, (0, 0)) := by
    funext p
    unfold flatDt
    have h1 : HasDerivAt (fun s' : ℝ => (s', p.2)) (1, (0, 0)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (((hΦ i).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1 h1).deriv
  rw [heq]
  exact ((hΦ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem contDiff_flatGrad {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i)) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => flatGrad Φ p.1 p.2 i j) := by
  set F : ℝ × (ℝ × ℝ) → ℝ := fun p => Φ p.1 p.2 i
  have heq : (fun p : ℝ × (ℝ × ℝ) => flatGrad Φ p.1 p.2 i j) =
      fun p => fderiv ℝ F p (0, B0579.dir j) := by
    funext p
    unfold flatGrad B0579.pd
    have hcomp : HasFDerivAt (fun y => Φ p.1 y i)
        ((fderiv ℝ F (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) p.2 :=
      ((hΦ i).differentiable (by simp) (p.1, p.2)).hasFDerivAt.comp p.2
        (hasFDerivAt_prodMk_right p.1 p.2)
    exact DFunLike.congr_fun hcomp.fderiv (B0579.dir j)
  rw [heq]
  exact ((hΦ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem contDiff_flatLap {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i)) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => flatLap Φ p.1 p.2 i) := by
  have hpd : ∀ k : Fin 2, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (fun z => Φ p.1 z i) p.2) :=
    fun k => contDiff_flatGrad hΦ i k
  have hpd2 : ∀ k : Fin 2, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (B0579.pd k (fun z => Φ p.1 z i)) p.2) := by
    intro k
    set G : ℝ × (ℝ × ℝ) → ℝ := fun p => B0579.pd k (fun z => Φ p.1 z i) p.2
    have heq : (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (B0579.pd k (fun z => Φ p.1 z i)) p.2) =
        fun p => fderiv ℝ G p (0, B0579.dir k) := by
      funext p
      unfold B0579.pd
      have hcomp : HasFDerivAt (B0579.pd k (fun z => Φ p.1 z i))
          ((fderiv ℝ G (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) p.2 :=
        ((hpd k).differentiable (by simp) (p.1, p.2)).hasFDerivAt.comp p.2
          (hasFDerivAt_prodMk_right p.1 p.2)
      exact DFunLike.congr_fun hcomp.fderiv (B0579.dir k)
    rw [heq]
    exact ((hpd k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hpd2 0).add (hpd2 1)

private theorem integrableOn_sum_vnorm2_box {c s₁ s₂ R : ℝ} (hc : 0 < c) (hs₁₂ : s₁ ≤ s₂)
    (hR : 0 ≤ R) {b_1 b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hb1_meas : ∀ i, Measurable fun p => b_1 p i)
    (hbcand_meas : ∀ i, Measurable fun p => b_cand p i)
    (hsq : IntegrableOn (fun p => (vnorm2 (b_1 p) + vnorm2 (b_cand p)) ^ 2)
      (Icc s₁ s₂ ×ˢ B0579.cell c)) :
    IntegrableOn (fun p => vnorm2 (b_1 p) + vnorm2 (b_cand p))
      (Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) := by
  set S : Set (ℝ × (ℝ × ℝ)) := Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  have hsub : S ⊆ Icc s₁ s₂ ×ˢ B0579.cell c :=
    prod_mono Subset.rfl (prod_mono Subset.rfl (subset_univ _))
  have hvol : volume S < ⊤ := by
    dsimp [S]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have _ := hc; have _ := hs₁₂; have _ := hR
  have hdom : IntegrableOn (fun p => 1 + (vnorm2 (b_1 p) + vnorm2 (b_cand p)) ^ 2) S :=
    (integrableOn_const hvol.ne).add (hsq.mono_set hsub)
  have hm : Measurable fun p => vnorm2 (b_1 p) + vnorm2 (b_cand p) :=
    (causalLin_measurable_vnorm2 hb1_meas).add (causalLin_measurable_vnorm2 hbcand_meas)
  refine hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  have hnn : 0 ≤ vnorm2 (b_1 p) + vnorm2 (b_cand p) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  nlinarith [sq_nonneg (vnorm2 (b_1 p) + vnorm2 (b_cand p) - 1)]

private theorem norm_le_vnorm2_local (v : Fin 2 → ℂ) (i : Fin 2) : ‖v i‖ ≤ vnorm2 v := by
  unfold vnorm2
  rw [← Real.sqrt_sq (norm_nonneg (v i))]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i))

private theorem integrableOn_flatDiff_supported {ν γ H s₁ s₂ R M_duh : ℝ} {μ : ℂ}
    (hγ : 0 ≤ γ) (hν : 0 < ν) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂H : s₂ < H)
    (hR : 0 < R) (hM : 0 ≤ M_duh)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {b_cl u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G_cl G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hbcl_meas : ∀ i, Measurable fun p => b_cl p i)
    (hGcl_meas : ∀ i j, Measurable fun p => G_cl p i j)
    (hbcl_loc : ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ < a₂ →
      ∫⁻ p in Icc a₁ a₂ ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) < ⊤)
    (huduh_meas : ∀ i, Measurable fun p => u_duh p i)
    (hGduh_meas : ∀ i j, Measurable fun p => G_duh p i j)
    (hduh_bd : ∀ s ∈ Ioo (0 : ℝ) H,
      ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
          ENNReal.ofReal M_duh)
    {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i))
    (hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R < |x.2|) → Φ s x i = 0) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p => gainG γ ν p.1 • u_duh p
    let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
    IntegrableOn (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p =
        ∫ p in Ioo (0 : ℝ) H ×ˢ B0579.cell c,
          flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p := by
  intro c b_1 b_cand
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  set S : Set (ℝ × (ℝ × ℝ)) := Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  have hS_meas : MeasurableSet S :=
    measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
  have hS_sub_Ioo : S ⊆ Ioo (0 : ℝ) H ×ˢ B0579.cell c := by
    intro p hp
    exact ⟨⟨lt_of_lt_of_le hs₁ hp.1.1, lt_of_le_of_lt hp.1.2 hs₂H⟩, hp.2.1, trivial⟩
  have hS_sub_Ioi : S ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
    hS_sub_Ioo.trans (prod_mono Ioo_subset_Ioi_self Subset.rfl)
  have h_zero_off : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ S,
      flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p = 0 := by
    intro p hp
    refine flatDiffIntegrand_zero_outside hsupp ?_
    by_contra hnot
    simp only [not_or, not_lt] at hnot
    exact hp.2 ⟨⟨hnot.1, hnot.2.1⟩, hp.1.2.1, abs_le.1 hnot.2.2⟩
  have hloc := energyLoc_cand hγ hν hs₁ hs₁₂ hs₂H hM hbcl_meas hGcl_meas
    (hbcl_loc s₁ s₂ hs₁ hs₁₂) huduh_meas hGduh_meas hduh_bd
  have hb1_meas : ∀ i, Measurable fun p => b_1 p i :=
    fun i => (measurable_gainG_fst γ ν).smul (huduh_meas i)
  have hbcand_meas : ∀ i, Measurable fun p => b_cand p i :=
    fun i => (hbcl_meas i).add (hb1_meas i)
  have hbox_int := integrableOn_sum_vnorm2_box hc hs₁₂.le hR.le hb1_meas hbcand_meas hloc.2.2
  -- Bound coefficients on compact box `K_box`
  set K_box : Set (ℝ × (ℝ × ℝ)) := Icc s₁ s₂ ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  have hK_comp : IsCompact K_box :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hS_K : S ⊆ K_box :=
    prod_mono Subset.rfl (prod_mono Ico_subset_Icc_self Subset.rfl)
  have hc_val : Continuous fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, (|flatDt Φ p.1 p.2 i| + (‖μ‖ / s₁) * |Φ p.1 p.2 i| +
        |ν| * |flatLap Φ p.1 p.2 i| + ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j|) := by
    refine continuous_finsetSum _ fun i _ => ?_
    have c1 := (contDiff_flatDt hΦ i).continuous.abs
    have c2 := (continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => ‖μ‖ / s₁).mul
      (hΦ i).continuous.abs
    have c3 := (continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => |ν|).mul
      (contDiff_flatLap hΦ i).continuous.abs
    have c4 := continuous_finsetSum Finset.univ fun j _ =>
      (contDiff_flatGrad hΦ i j).continuous.abs
    exact ((c1.add c2).add c3).add c4
  obtain ⟨M_Φ, hM_Φ⟩ := hK_comp.exists_bound_of_continuousOn hc_val.continuousOn
  have hM_Φ0 : 0 ≤ M_Φ := by
    have hmem : (s₁, (-(c / 2), 0)) ∈ K_box :=
      ⟨⟨le_rfl, hs₁₂.le⟩, ⟨le_rfl, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    exact (norm_nonneg _).trans (hM_Φ _ hmem)
  obtain ⟨M_v, hMv0, hMv⟩ := core_trainVel_bound_le tr hbuc (hs₁.le.trans (hs₁₂.le.trans hs₂H.le))
  set C_bd : ℝ := (1 + 2 * M_v) * M_Φ
  have hmeas_diff : Measurable (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ) := by
    unfold flatDiffIntegrand
    refine Finset.measurable_sum _ fun i _ => ?_
    have m_dt : Measurable fun p : ℝ × (ℝ × ℝ) => (flatDt Φ p.1 p.2 i : ℂ) :=
      Complex.measurable_ofReal.comp (contDiff_flatDt hΦ i).continuous.measurable
    have m_ph : Measurable fun p : ℝ × (ℝ × ℝ) => (Φ p.1 p.2 i : ℂ) :=
      Complex.measurable_ofReal.comp (hΦ i).continuous.measurable
    have m_lp : Measurable fun p : ℝ × (ℝ × ℝ) => (flatLap Φ p.1 p.2 i : ℂ) :=
      Complex.measurable_ofReal.comp (contDiff_flatLap hΦ i).continuous.measurable
    have m_s : Measurable fun p : ℝ × (ℝ × ℝ) => μ / (p.1 : ℂ) :=
      measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)
    have m_t1 := ((hb1_meas i).mul m_dt).neg
    have m_t2 := (m_s.mul (hb1_meas i)).mul m_ph
    have m_t3 := ((measurable_const : Measurable fun _ : ℝ × (ℝ × ℝ) => (ν : ℂ)).mul (hb1_meas i)).mul m_lp
    have m_t4 : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ∑ j : Fin 2, (((trainVel tr p.1 p.2 i : ℂ) * b_cand p j +
          b_cand p i * (trainVel tr p.1 p.2 j : ℂ))) * (flatGrad Φ p.1 p.2 i j : ℂ) := by
      refine Finset.measurable_sum _ fun j _ => ?_
      have mv_i := Complex.measurable_ofReal.comp (V1.measurable_trainVel tr i)
      have mv_j := Complex.measurable_ofReal.comp (V1.measurable_trainVel tr j)
      have m_gr := Complex.measurable_ofReal.comp (contDiff_flatGrad hΦ i j).continuous.measurable
      exact ((mv_i.mul (hbcand_meas j)).add ((hbcand_meas i).mul mv_j)).mul m_gr
    exact ((m_t1.add m_t2).sub m_t3).sub m_t4
  have hint_S : IntegrableOn (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ) S := by
    refine (hbox_int.const_mul C_bd).mono' hmeas_diff.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS_meas] with p hp
    have hp_s1 : s₁ ≤ p.1 := hp.1.1
    have hp_s0 : 0 < p.1 := lt_of_lt_of_le hs₁ hp_s1
    have hp_s2 : p.1 ≤ H := hp.1.2.trans hs₂H.le
    have hK_le : ∑ i : Fin 2, (|flatDt Φ p.1 p.2 i| + (‖μ‖ / s₁) * |Φ p.1 p.2 i| +
        |ν| * |flatLap Φ p.1 p.2 i| + ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j|) ≤ M_Φ := by
      have h1 := hM_Φ p (hS_K hp)
      have hnn : 0 ≤ ∑ i : Fin 2, (|flatDt Φ p.1 p.2 i| + (‖μ‖ / s₁) * |Φ p.1 p.2 i| +
          |ν| * |flatLap Φ p.1 p.2 i| + ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j|) :=
        Finset.sum_nonneg fun i _ => add_nonneg (add_nonneg (add_nonneg (abs_nonneg _)
          (mul_nonneg (div_nonneg (norm_nonneg _) hs₁.le) (abs_nonneg _)))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      rwa [Real.norm_of_nonneg hnn] at h1
    set B : ℝ := vnorm2 (b_1 p) + vnorm2 (b_cand p)
    have hB0 : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hb1_le : ∀ i, ‖b_1 p i‖ ≤ B :=
      fun i => (norm_le_vnorm2_local _ i).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    have hbc_le : ∀ i, ‖b_cand p i‖ ≤ B :=
      fun i => (norm_le_vnorm2_local _ i).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    unfold flatDiffIntegrand
    calc ‖∑ i : Fin 2, (-(b_1 p i * (flatDt Φ p.1 p.2 i : ℂ)) +
            (μ / (p.1 : ℂ)) * b_1 p i * (Φ p.1 p.2 i : ℂ) -
            (ν : ℂ) * b_1 p i * (flatLap Φ p.1 p.2 i : ℂ) -
            ∑ j : Fin 2, (((trainVel tr p.1 p.2 i : ℂ) * b_cand p j +
              b_cand p i * (trainVel tr p.1 p.2 j : ℂ))) * (flatGrad Φ p.1 p.2 i j : ℂ))‖
        ≤ ∑ i : Fin 2, (1 + 2 * M_v) * B *
            (|flatDt Φ p.1 p.2 i| + (‖μ‖ / s₁) * |Φ p.1 p.2 i| +
              |ν| * |flatLap Φ p.1 p.2 i| + ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j|) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          have ht1 : ‖-(b_1 p i * (flatDt Φ p.1 p.2 i : ℂ))‖ ≤ B * |flatDt Φ p.1 p.2 i| := by
            rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hb1_le i) (abs_nonneg _)
          have ht2 : ‖(μ / (p.1 : ℂ)) * b_1 p i * (Φ p.1 p.2 i : ℂ)‖ ≤
              B * ((‖μ‖ / s₁) * |Φ p.1 p.2 i|) := by
            rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hp_s0.le,
              Complex.norm_real, Real.norm_eq_abs]
            have hdiv : ‖μ‖ / p.1 ≤ ‖μ‖ / s₁ :=
              div_le_div_of_nonneg_left (norm_nonneg _) hs₁ hp_s1
            calc (‖μ‖ / p.1) * ‖b_1 p i‖ * |Φ p.1 p.2 i|
                ≤ (‖μ‖ / s₁) * B * |Φ p.1 p.2 i| :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul hdiv (hb1_le i) (norm_nonneg _) (div_nonneg (norm_nonneg _) hs₁.le))
                    (abs_nonneg _)
              _ = B * ((‖μ‖ / s₁) * |Φ p.1 p.2 i|) := by ring
          have ht3 : ‖(ν : ℂ) * b_1 p i * (flatLap Φ p.1 p.2 i : ℂ)‖ ≤
              B * (|ν| * |flatLap Φ p.1 p.2 i|) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_real, Real.norm_eq_abs]
            calc |ν| * ‖b_1 p i‖ * |flatLap Φ p.1 p.2 i|
                ≤ |ν| * B * |flatLap Φ p.1 p.2 i| :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb1_le i) (abs_nonneg _))
                    (abs_nonneg _)
              _ = B * (|ν| * |flatLap Φ p.1 p.2 i|) := by ring
          have ht4 : ‖∑ j : Fin 2, (((trainVel tr p.1 p.2 i : ℂ) * b_cand p j +
              b_cand p i * (trainVel tr p.1 p.2 j : ℂ))) * (flatGrad Φ p.1 p.2 i j : ℂ)‖ ≤
              (2 * M_v * B) * ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j| := by
            rw [Finset.mul_sum]
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            have hv1 := hMv p.1 hp_s2 p.2 i
            have hv2 := hMv p.1 hp_s2 p.2 j
            calc ‖(trainVel tr p.1 p.2 i : ℂ)‖ * ‖b_cand p j‖ +
                  ‖b_cand p i‖ * ‖(trainVel tr p.1 p.2 j : ℂ)‖
                ≤ M_v * B + B * M_v :=
                  add_le_add (mul_le_mul hv1 (hbc_le j) (norm_nonneg _) hMv0)
                    (mul_le_mul (hbc_le i) hv2 (norm_nonneg _) hB0)
              _ = 2 * M_v * B := by ring
          have htri : ‖-(b_1 p i * (flatDt Φ p.1 p.2 i : ℂ)) +
              (μ / (p.1 : ℂ)) * b_1 p i * (Φ p.1 p.2 i : ℂ) -
              (ν : ℂ) * b_1 p i * (flatLap Φ p.1 p.2 i : ℂ) -
              ∑ j : Fin 2, (((trainVel tr p.1 p.2 i : ℂ) * b_cand p j +
                b_cand p i * (trainVel tr p.1 p.2 j : ℂ))) * (flatGrad Φ p.1 p.2 i j : ℂ)‖ ≤
              B * |flatDt Φ p.1 p.2 i| + B * ((‖μ‖ / s₁) * |Φ p.1 p.2 i|) +
                B * (|ν| * |flatLap Φ p.1 p.2 i|) +
                (2 * M_v * B) * ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j| := by
            refine (norm_sub_le _ _).trans (add_le_add ?_ ht4)
            refine (norm_sub_le _ _).trans (add_le_add ?_ ht3)
            exact (norm_add_le _ _).trans (add_le_add ht1 ht2)
          refine htri.trans ?_
          have hnn1 : 0 ≤ |flatDt Φ p.1 p.2 i| + (‖μ‖ / s₁) * |Φ p.1 p.2 i| +
              |ν| * |flatLap Φ p.1 p.2 i| :=
            add_nonneg (add_nonneg (abs_nonneg _)
              (mul_nonneg (div_nonneg (norm_nonneg _) hs₁.le) (abs_nonneg _)))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          have hnn2 : 0 ≤ ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          nlinarith [mul_nonneg (mul_nonneg hMv0 hB0) hnn1, mul_nonneg hB0 hnn2]
      _ = (1 + 2 * M_v) * B * ∑ i : Fin 2,
            (|flatDt Φ p.1 p.2 i| + (‖μ‖ / s₁) * |Φ p.1 p.2 i| +
              |ν| * |flatLap Φ p.1 p.2 i| + ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j|) := by
          rw [← Finset.mul_sum]
      _ ≤ (1 + 2 * M_v) * B * M_Φ :=
          mul_le_mul_of_nonneg_left hK_le (mul_nonneg (by linarith) hB0)
      _ = C_bd * B := by dsimp [C_bd]; ring
  -- Extend from `S` to `Ioi 0 ×ˢ B0579.cell c` and `Ioo 0 H ×ˢ B0579.cell c`
  have hint_off : IntegrableOn (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ)
      ((Ioi (0 : ℝ) ×ˢ B0579.cell c) \ S) := by
    refine (integrableOn_zero (s := (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ S)).congr_fun
      (fun p hp => (h_zero_off p hp).symm)
      ((measurableSet_Ioi.prod (B0579.measurableSet_cell c)).diff hS_meas)
  have hint_Ioi : IntegrableOn (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
    have hunion := hint_S.union hint_off
    rwa [Set.union_sdiff_cancel hS_sub_Ioi] at hunion
  refine ⟨hint_Ioi, ?_⟩
  have hsub_Ioo : Ioo (0 : ℝ) H ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
    prod_mono Ioo_subset_Ioi_self Subset.rfl
  have h1 : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p =
      ∫ p in S, flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p :=
    MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (measurableSet_Ioi.prod (B0579.measurableSet_cell c)).nullMeasurableSet
      hS_sub_Ioi (Eventually.of_forall h_zero_off)
  have h2 : ∫ p in Ioo (0 : ℝ) H ×ˢ B0579.cell c,
      flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p =
      ∫ p in S, flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p :=
    MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (measurableSet_Ioo.prod (B0579.measurableSet_cell c)).nullMeasurableSet hS_sub_Ioo
      (Eventually.of_forall fun p hp => h_zero_off p ⟨hsub_Ioo hp.1, hp.2⟩)
  rw [h1, h2]

/-! ## 4. Vanishing of `flatDiffIntegrand` on stream-function tests `perpF ∘ ψ` -/

private theorem contDiff_perpF_comp {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => V1.perpF (ψ p.1) p.2 i) := by
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun p => ψ p.1 p.2
  have hpd : ∀ k : Fin 2, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (ψ p.1) p.2) := by
    intro k
    have heq : (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (ψ p.1) p.2) =
        fun p => fderiv ℝ Ψ p (0, B0579.dir k) := by
      funext p; unfold B0579.pd
      have hcomp : HasFDerivAt (ψ p.1)
          ((fderiv ℝ Ψ (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) p.2 :=
        (hψ.differentiable (by simp) (p.1, p.2)).hasFDerivAt.comp p.2
          (hasFDerivAt_prodMk_right p.1 p.2)
      exact DFunLike.congr_fun hcomp.fderiv (B0579.dir k)
    rw [heq]
    exact (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  fin_cases i
  · exact hpd 1
  · exact (hpd 0).neg

private theorem supp_perpF_comp {s₁ s₂ R₁ : ℝ} {ψ : ℝ → ℝ × ℝ → ℝ}
    (hsupp : ∀ s x, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → ψ s x = 0) :
    ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → V1.perpF (ψ s) x i = 0 := by
  intro s x i hout
  have hpd0 : ∀ k : Fin 2, B0579.pd k (ψ s) x = 0 := by
    intro k
    rcases hout with hs | hs | hx
    · have hslice : ψ s = 0 := funext fun y => hsupp s y (Or.inl hs)
      unfold B0579.pd; rw [hslice]; simp
    · have hslice : ψ s = 0 := funext fun y => hsupp s y (Or.inr (Or.inl hs))
      unfold B0579.pd; rw [hslice]; simp
    · have hUx : {y : ℝ × ℝ | R₁ < |y.2|} ∈ 𝓝 x :=
        (isOpen_lt continuous_const (continuous_abs.comp continuous_snd)).mem_nhds hx
      have hev : ψ s =ᶠ[𝓝 x] 0 :=
        Filter.eventually_of_mem hUx fun y hy => hsupp s y (Or.inr (Or.inr hy))
      exact pd_eq_zero_of_eventuallyEq hev k
  fin_cases i
  · exact hpd0 1
  · simp [V1.perpF_one, hpd0 0]

private theorem flatDiff_perpF_pointwise {ν : ℝ} {μ : ℂ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (b_cl b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    {ψ : ℝ → ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (ρ : ℝ) (x : ℝ × ℝ) :
    let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
    flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (fun s y => V1.perpF (ψ s) y) (ρ, x) =
      -V1.hInt b_1 (fun y => deriv (fun ρ' => ψ ρ' y) ρ) (ρ, x) +
        (μ / (ρ : ℂ)) * V1.hInt b_1 (ψ ρ) (ρ, x) -
        V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x) := by
  intro b_cand
  have hdt0 : flatDt (fun s y => V1.perpF (ψ s) y) ρ x 0 =
      V1.perpF (fun y => deriv (fun ρ' => ψ ρ' y) ρ) x 0 := by
    unfold flatDt
    simp only [V1.perpF_zero]
    exact deriv_pd_comm hψ 1 ρ x
  have hdt1 : flatDt (fun s y => V1.perpF (ψ s) y) ρ x 1 =
      V1.perpF (fun y => deriv (fun ρ' => ψ ρ' y) ρ) x 1 := by
    unfold flatDt
    simp only [V1.perpF_one]
    change deriv (-(fun s' => B0579.pd 0 (ψ s') x)) ρ = _
    rw [deriv.neg, deriv_pd_comm hψ 0 ρ x]
  simp only [flatDiffIntegrand, Fin.sum_univ_two, hdt0, hdt1, flatGrad, flatLap,
    V1.hInt, V1.jInt, V1.wF, b_cand]
  ring

private theorem flatDiff_perpF_slice_eq {ν γ H : ℝ} {μ : ℂ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {b_cl u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G_cl G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {ω_duh f : ℝ → ℝ × ℝ → ℂ}
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) H)
    (hbcl_lp : ∀ i, MemLp (fun x => b_cl (ρ, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hbcl_div : ∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        (b_cl (ρ, x) 0 * (B0579.pd 0 χ x : ℂ) + b_cl (ρ, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0)
    (hbcl_wg : ∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
      (fun x => b_cl (ρ, x) i) (fun x => G_cl (ρ, x) i j))
    (_hf_mem : MemLp (f ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (hf_pair : ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
      h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f ρ x * φ x =
        coreSrcFun (ν ^ (-2 : ℝ))
          (advStretch (trainVel tr ρ)
            (fun x => gainConj γ ν b_cl (ρ, x))
            (fun x => gainConj γ ν G_cl (ρ, x))) g)
    (huduh_lp : ∀ i, MemLp (fun x => u_duh (ρ, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hωduh_mem : MemLp (ω_duh ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (huduh_div : ∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        (u_duh (ρ, x) 0 * (B0579.pd 0 χ x : ℂ) + u_duh (ρ, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0)
    (huduh_wg : ∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
      (fun x => u_duh (ρ, x) i) (fun x => G_duh (ρ, x) i j))
    (huduh_curl : (fun x => G_duh (ρ, x) 1 0 - G_duh (ρ, x) 0 1)
      =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω_duh ρ)
    {ψ : ℝ → ℝ × ℝ → ℝ} {R₁ : ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x)
    (hband : ∀ s x, R₁ < |x.2| → ψ s x = 0) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p => gainG γ ν p.1 • u_duh p
    let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
    ∫ x in B0579.cell c,
        flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (fun s y => V1.perpF (ψ s) y) (ρ, x) =
      -((∫ x in B0579.cell c,
          flowIntegrand tr
            (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
            (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x) +
        (∫ x in B0579.cell c,
          ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
            (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))) +
        (gainG γ ν ρ : ℂ) * ∫ x in B0579.cell c, f ρ x * (ψ ρ x : ℂ)) := by
  intro c b_1 b_cand
  let G_1 : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p => gainG γ ν p.1 • G_duh p
  let G_cand : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => G_cl p i j + G_1 p i j
  have hmc := B0579.measurableSet_cell c
  have hφ : B0579.IsCylTest c (ψ ρ) := isCylTest_slice hψ hper hband ρ
  have hdtφ : B0579.IsCylTest c (fun y => deriv (fun ρ' => ψ ρ' y) ρ) :=
    isCylTest_dt_slice hψ hper hband ρ
  have hω_l2 : MemLp (ω_duh ρ) 2 (volume.restrict (B0579.cell c)) :=
    CoreDuhamelRepSub.memLp_unweighted_of_memX hωduh_mem
  have hb1_lp : ∀ i, MemLp (fun x => b_1 (ρ, x) i) 2 (volume.restrict (B0579.cell c)) := by
    intro i
    have heq : (fun x => b_1 (ρ, x) i) = fun x => (gainG γ ν ρ : ℂ) * u_duh (ρ, x) i := by
      funext x; simp [b_1, Complex.real_smul]
    rw [heq]
    exact (huduh_lp i).const_mul _
  have hbcand_lp : ∀ i, MemLp (fun x => b_cand (ρ, x) i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (hbcl_lp i).add (hb1_lp i)
  have hb1_wg : ∀ i j, HasWeakCellDerivC c j
      (fun x => b_1 (ρ, x) i) (fun x => G_1 (ρ, x) i j) := by
    intro i j
    have heq1 : (fun x => b_1 (ρ, x) i) = fun x => (gainG γ ν ρ : ℂ) * u_duh (ρ, x) i := by
      funext x; simp [b_1, Complex.real_smul]
    have heq2 : (fun x => G_1 (ρ, x) i j) = fun x => (gainG γ ν ρ : ℂ) * G_duh (ρ, x) i j := by
      funext x; simp [G_1, Complex.real_smul]
    rw [heq1, heq2]
    exact hasWeakCellDerivC_const_mul _ (huduh_wg i j)
  have hbcand_wg : ∀ i j, HasWeakCellDerivC c j
      (fun x => b_cand (ρ, x) i) (fun x => G_cand (ρ, x) i j) := by
    intro i j
    refine ⟨fun χ hχ => ⟨IntegrableOn.congr_fun (((hbcl_wg i j).1 χ hχ).1.add ((hb1_wg i j).1 χ hχ).1)
        (fun x _ => by simp only [Pi.add_apply, b_cand]; ring) hmc,
      IntegrableOn.congr_fun (((hbcl_wg i j).1 χ hχ).2.add ((hb1_wg i j).1 χ hχ).2)
        (fun x _ => by simp only [Pi.add_apply, G_cand]; ring) hmc⟩,
      fun χ hχ => ?_⟩
    have hA1 := ((hbcl_wg i j).1 χ hχ).1
    have hB1 := ((hb1_wg i j).1 χ hχ).1
    have hA2 := ((hbcl_wg i j).1 χ hχ).2
    have hB2 := ((hb1_wg i j).1 χ hχ).2
    have e1 : (fun x => b_cand (ρ, x) i * (B0579.pd j χ x : ℂ)) =
        fun x => b_cl (ρ, x) i * (B0579.pd j χ x : ℂ) + b_1 (ρ, x) i * (B0579.pd j χ x : ℂ) := by
      funext x; dsimp [b_cand]; ring
    have e2 : (fun x => G_cand (ρ, x) i j * (χ x : ℂ)) =
        fun x => G_cl (ρ, x) i j * (χ x : ℂ) + G_1 (ρ, x) i j * (χ x : ℂ) := by
      funext x; dsimp [G_cand]; ring
    rw [e1, e2, integral_add hA1 hB1, integral_add hA2 hB2,
      (hbcl_wg i j).2 χ hχ, (hb1_wg i j).2 χ hχ]
    ring
  have hbcand_div : ∀ χ, B0579.IsCylTest c χ →
      ∫ x in B0579.cell c,
        (b_cand (ρ, x) 0 * (B0579.pd 0 χ x : ℂ) + b_cand (ρ, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0 := by
    intro χ hχ
    have hA0 := ((hbcl_wg 0 0).1 χ hχ).1
    have hA1 := ((hbcl_wg 1 1).1 χ hχ).1
    have hB0 := ((huduh_wg 0 0).1 χ hχ).1
    have hB1 := ((huduh_wg 1 1).1 χ hχ).1
    let fA : ℝ × ℝ → ℂ :=
      fun x => b_cl (ρ, x) 0 * (B0579.pd 0 χ x : ℂ) + b_cl (ρ, x) 1 * (B0579.pd 1 χ x : ℂ)
    let fB : ℝ × ℝ → ℂ :=
      fun x => u_duh (ρ, x) 0 * (B0579.pd 0 χ x : ℂ) + u_duh (ρ, x) 1 * (B0579.pd 1 χ x : ℂ)
    have hfA : IntegrableOn fA (B0579.cell c) := (hA0.add hA1 : IntegrableOn fA (B0579.cell c))
    have hfB : IntegrableOn (fun x => (gainG γ ν ρ : ℂ) * fB x) (B0579.cell c) :=
      integrableOn_const_mul_local (gainG γ ν ρ : ℂ) (hB0.add hB1 : IntegrableOn fB (B0579.cell c))
    have heq : (fun x => b_cand (ρ, x) 0 * (B0579.pd 0 χ x : ℂ) +
        b_cand (ρ, x) 1 * (B0579.pd 1 χ x : ℂ)) =
        fun x => fA x + (gainG γ ν ρ : ℂ) * fB x := by
      funext x; simp [fA, fB, b_cand, b_1, Complex.real_smul]; ring
    rw [heq, integral_add hfA hfB, hbcl_div χ hχ, integral_const_mul, huduh_div χ hχ,
      mul_zero, add_zero]
  -- 1. First two pairings: `hInt b_1` with `dt ψ ρ` and `ψ ρ`
  have hb1_curl : (fun x => G_1 (ρ, x) 1 0 - G_1 (ρ, x) 0 1)
      =ᵐ[volume.restrict (B0579.cell c)] fun x => (gainG γ ν ρ : ℂ) * ω_duh ρ x := by
    filter_upwards [huduh_curl] with x hx
    simp only [G_1, Pi.smul_apply, Complex.real_smul, ← hx]
    ring
  have hInt_eq : ∀ {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ),
      IntegrableOn (fun x => V1.hInt b_1 χ (ρ, x)) (B0579.cell c) ∧
        ∫ x in B0579.cell c, V1.hInt b_1 χ (ρ, x) =
          ∫ x in B0579.cell c, ((gainG γ ν ρ : ℂ) * ω_duh ρ x) * (χ x : ℂ) := by
    intro χ hχ
    have heq : (fun x => V1.hInt b_1 χ (ρ, x)) =
        fun x => b_1 (ρ, x) 0 * (B0579.pd 1 χ x : ℂ) - b_1 (ρ, x) 1 * (B0579.pd 0 χ x : ℂ) := by
      funext x
      simp [V1.hInt, Fin.sum_univ_two, V1.perpF_zero, V1.perpF_one]
      ring
    rw [heq]
    exact ⟨(((hb1_wg 0 1).1 χ hχ).1).sub (((hb1_wg 1 0).1 χ hχ).1),
      curl_pair_eq hb1_wg hb1_curl hχ⟩
  obtain ⟨hI_dt, hEq_dt⟩ := hInt_eq hdtφ
  obtain ⟨hI_ph, hEq_ph⟩ := hInt_eq hφ
  -- 2. Vorticity-velocity identity for `jInt` at `μ' = 0`
  have hZs_IZ : V1.IZ c (V1.Zs tr b_cl b_cand G_cl G_cand ρ (ψ ρ)) := by
    have hψ_t := V1.psiF_test tr hρ.1.le hφ
    exact ((((((((((wk_iz_slice hbcand_wg 1 0 hψ_t).sub (wk_iz_slice hbcl_wg 1 0 hψ_t)).sub
      (wk_iz_slice hbcand_wg 0 1 hψ_t)).add (wk_iz_slice hbcl_wg 0 1 hψ_t)).add
      (wk_iz_slice hbcl_wg 1 0 (V1.vfF_test tr hρ.1.le hφ 0 0))).add
      (wk_iz_slice hbcl_wg 1 1 (V1.vfF_test tr hρ.1.le hφ 1 0))).sub
      (wk_iz_slice hbcl_wg 0 0 (V1.vfF_test tr hρ.1.le hφ 0 1))).sub
      (wk_iz_slice hbcl_wg 0 1 (V1.vfF_test tr hρ.1.le hφ 1 1))).sub
      (dv_iz_slice hbcand_wg hbcand_div (V1.chiwF_test tr hρ.1.le hφ))).add
      (dv_iz_slice hbcl_wg hbcl_div (V1.chiwF_test tr hρ.1.le hφ))).sub
      (dv_iz_slice hbcl_wg hbcl_div (V1.chi0F_test tr hρ.1.le hφ))
  obtain ⟨R, hR⟩ := hφ.band
  have hB : V1.Band R (ψ ρ) := hR
  have hB0 : V1.Band R (B0579.pd 0 (ψ ρ)) := hB.pd 0
  have hB1 : V1.Band R (B0579.pd 1 (ψ ρ)) := hB.pd 1
  set SI : ℝ × ℝ → ℂ := fun x =>
    coreAdvSlice γ tr b_cl G_cl ρ x 1 * (B0579.pd 0 (ψ ρ) x : ℂ) -
      coreAdvSlice γ tr b_cl G_cl ρ x 0 * (B0579.pd 1 (ψ ρ) x : ℂ) with hSI_def
  have hSI_int : IntegrableOn SI (B0579.cell c) := by
    have mc : ∀ j : Fin 2, Continuous (fun x => B0579.pd j (V1.vC tr ρ 1) x * B0579.pd 0 (ψ ρ) x -
        B0579.pd j (V1.vC tr ρ 0) x * B0579.pd 1 (ψ ρ) x) := fun j =>
      ((V1.pdv_contDiff tr hρ.1.le 1 j).continuous.mul (hφ.pd 0).continuous).sub
        ((V1.pdv_contDiff tr hρ.1.le 0 j).continuous.mul (hφ.pd 1).continuous)
    have mb : ∀ j : Fin 2, V1.Band R (fun x => B0579.pd j (V1.vC tr ρ 1) x * B0579.pd 0 (ψ ρ) x -
        B0579.pd j (V1.vC tr ρ 0) x * B0579.pd 1 (ψ ρ) x) := fun j =>
      (hB0.mul_left _).sub (hB1.mul_left _)
    have hG : ∀ i j a k : Fin 2, IntegrableOn
        (fun x => G_cl (ρ, x) i j * (V1.vfF tr ρ a k (ψ ρ) x : ℂ)) (B0579.cell c) := fun i j a k =>
      ((hbcl_wg i j).1 _ (V1.vfF_test tr hρ.1.le hφ a k)).2
    refine IntegrableOn.congr_fun ((((((((hG 1 0 0 0).add (hG 1 1 1 0)).sub (hG 0 0 0 1)).sub
      (hG 0 1 1 1)).add (V1.intL2 (hbcl_lp 0) (mc 0) (mb 0))).add
      (V1.intL2 (hbcl_lp 1) (mc 1) (mb 1))).const_mul ((gainG γ ν ρ : ℂ))⁻¹)) (fun x _ => ?_) hmc
    simp only [hSI_def, coreAdvSlice, advStretch, gainConj, Fin.sum_univ_two, Pi.smul_apply,
      Complex.real_smul, V1.trainVel_fun tr hρ.1.le, Pi.add_apply, Pi.sub_apply]
    simp only [V1.trainVel_of_nonneg tr hρ.1.le, V1.vfF, V1.vC_apply]
    push_cast
    ring
  have hJ_int : IntegrableOn
      (fun x => V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x)) (B0579.cell c) := by
    have cL : ∀ j : Fin 2, Continuous (lapP (B0579.pd j (ψ ρ))) := fun j =>
      (V1.cylTest_lapP (hφ.pd j)).continuous
    have cf : ∀ i j : Fin 2, Continuous (B0579.pd i (B0579.pd j (ψ ρ))) := fun i j =>
      ((hφ.pd j).pd i).continuous
    have cv : ∀ k : Fin 2, Continuous (V1.vC tr ρ k) :=
      fun k => (V1.vC_contDiff tr hρ.1.le k).continuous
    have bL0 : V1.Band R (lapP (B0579.pd 0 (ψ ρ))) := hB0.lapP
    have bL1 : V1.Band R (lapP (B0579.pd 1 (ψ ρ))) := hB1.lapP
    have b00 : V1.Band R (B0579.pd 0 (B0579.pd 0 (ψ ρ))) := hB0.pd 0
    have b10 : V1.Band R (B0579.pd 1 (B0579.pd 0 (ψ ρ))) := hB0.pd 1
    have b01 : V1.Band R (B0579.pd 0 (B0579.pd 1 (ψ ρ))) := hB1.pd 0
    have b11 : V1.Band R (B0579.pd 1 (B0579.pd 1 (ψ ρ))) := hB1.pd 1
    set M0 : ℝ × ℝ → ℝ := fun x => ν * lapP (B0579.pd 1 (ψ ρ)) x +
      2 * V1.vC tr ρ 0 x * B0579.pd 0 (B0579.pd 1 (ψ ρ)) x +
      V1.vC tr ρ 1 x * B0579.pd 1 (B0579.pd 1 (ψ ρ)) x -
      V1.vC tr ρ 1 x * B0579.pd 0 (B0579.pd 0 (ψ ρ)) x with hM0
    set M1 : ℝ × ℝ → ℝ := fun x => -(ν * lapP (B0579.pd 0 (ψ ρ)) x) +
      V1.vC tr ρ 0 x * B0579.pd 1 (B0579.pd 1 (ψ ρ)) x -
      V1.vC tr ρ 0 x * B0579.pd 0 (B0579.pd 0 (ψ ρ)) x -
      2 * V1.vC tr ρ 1 x * B0579.pd 1 (B0579.pd 0 (ψ ρ)) x with hM1
    set N0 : ℝ × ℝ → ℝ := fun x => -(ν * lapP (B0579.pd 1 (ψ ρ)) x) with hN0
    set N1 : ℝ × ℝ → ℝ := fun x => ν * lapP (B0579.pd 0 (ψ ρ)) x with hN1
    have cM0 : Continuous M0 :=
      (((continuous_const.mul (cL 1)).add ((continuous_const.mul (cv 0)).mul (cf 0 1))).add
        ((cv 1).mul (cf 1 1))).sub ((cv 1).mul (cf 0 0))
    have cM1 : Continuous M1 :=
      ((((continuous_const.mul (cL 0)).neg).add ((cv 0).mul (cf 1 1))).sub
        ((cv 0).mul (cf 0 0))).sub ((continuous_const.mul (cv 1)).mul (cf 1 0))
    have cN0 : Continuous N0 := (continuous_const.mul (cL 1)).neg
    have cN1 : Continuous N1 := continuous_const.mul (cL 0)
    have bM0 : V1.Band R M0 := fun x hx => by
      simp only [hM0, bL1 x hx, b01 x hx, b11 x hx, b00 x hx]; ring
    have bM1 : V1.Band R M1 := fun x hx => by
      simp only [hM1, bL0 x hx, b11 x hx, b00 x hx, b10 x hx]; ring
    have bN0 : V1.Band R N0 := fun x hx => by simp only [hN0, bL1 x hx]; ring
    have bN1 : V1.Band R N1 := fun x hx => by simp only [hN1, bL0 x hx]; ring
    refine IntegrableOn.congr_fun
      ((((V1.intL2 (hbcand_lp 0) cM0 bM0).add (V1.intL2 (hbcand_lp 1) cM1 bM1)).add
        (V1.intL2 (hbcl_lp 0) cN0 bN0)).add (V1.intL2 (hbcl_lp 1) cN1 bN1)) (fun x _ => ?_) hmc
    have hperp1 : (fun y => V1.perpF (ψ ρ) y 1) = fun y => -B0579.pd 0 (ψ ρ) y := rfl
    have hperp0 : (fun y => V1.perpF (ψ ρ) y 0) = B0579.pd 1 (ψ ρ) := rfl
    simp only [V1.jInt, V1.wF, Fin.sum_univ_two, hperp0, hperp1, V1.trainVel_of_nonneg tr hρ.1.le]
    rw [V1.pd_neg, V1.pd_neg, V1.lapP_neg (hφ.pd 0)]
    simp only [hM0, hM1, hN0, hN1, V1.vC_apply, Pi.add_apply]
    push_cast
    ring
  set FI₀ : ℝ × ℝ → ℂ := fun x => flowIntegrand tr
    (fun y => (((ρ : ℂ) ^ (0 : ℂ) * (gainG γ ν ρ : ℂ)) * corePerturbVort γ ν G_cl G_cand ρ y))
    (fun y => (((ρ : ℂ) ^ (0 : ℂ) * (gainG γ ν ρ : ℂ)) • corePerturbVel γ ν b_cl b_cand (ρ, y)))
    ρ (ψ ρ) x
  have hpt_TI : ∀ x, FI₀ x + ((ρ : ℂ) ^ (0 : ℂ) * (gainG γ ν ρ : ℂ)) * SI x =
      (ρ : ℂ) ^ (0 : ℂ) * V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x) +
        (ρ : ℂ) ^ (0 : ℂ) * V1.Zs tr b_cl b_cand G_cl G_cand ρ (ψ ρ) x :=
    fun x => V1.pointwise_TI tr hρ.1 hφ x
  have hFI₀_int : IntegrableOn FI₀ (B0579.cell c) := by
    refine IntegrableOn.congr_fun
      (((hJ_int.const_mul ((ρ : ℂ) ^ (0 : ℂ))).add
        (hZs_IZ.1.const_mul ((ρ : ℂ) ^ (0 : ℂ)))).sub
        (hSI_int.const_mul ((ρ : ℂ) ^ (0 : ℂ) * (gainG γ ν ρ : ℂ)))) (fun x _ => ?_) hmc
    have := hpt_TI x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← this]; ring
  have hFI₀_ae : FI₀ =ᵐ[volume.restrict (B0579.cell c)]
      fun x => flowIntegrand tr
        (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
        (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x := by
    have hgc_ne : (gainG γ ν ρ : ℂ) ≠ 0 := V1.gain_ne γ ν ρ
    filter_upwards [huduh_curl] with x hx
    have hvel : ((gainG γ ν ρ : ℂ) • corePerturbVel γ ν b_cl b_cand (ρ, x)) =
        (gainG γ ν ρ : ℂ) • u_duh (ρ, x) := by
      funext i
      simp only [corePerturbVel, gainConj, b_cand, b_1, Pi.smul_apply, Complex.real_smul,
        smul_eq_mul, Complex.ofReal_inv, add_sub_cancel_left, inv_mul_cancel_left₀ hgc_ne]
    have hvort : (gainG γ ν ρ : ℂ) * corePerturbVort γ ν G_cl G_cand ρ x =
        (gainG γ ν ρ : ℂ) * ω_duh ρ x := by
      rw [← hx]
      simp only [corePerturbVort, corePerturbGrad, gainConj, G_cand, G_1, Pi.smul_apply,
        Complex.real_smul, Complex.ofReal_inv, add_sub_cancel_left, inv_mul_cancel_left₀ hgc_ne]
    dsimp only [FI₀, flowIntegrand]
    simp only [Complex.cpow_zero, one_mul, hvort, hvel]
  have hJ_eq : ∫ x in B0579.cell c, V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x) =
      (∫ x in B0579.cell c, flowIntegrand tr
        (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
        (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x) +
      (gainG γ ν ρ : ℂ) * ∫ x in B0579.cell c, f ρ x * (ψ ρ x : ℂ) := by
    have h1 : (∫ x in B0579.cell c, FI₀ x) + (gainG γ ν ρ : ℂ) * ∫ x in B0579.cell c, SI x =
        ∫ x in B0579.cell c, V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x) := by
      have hpt' : ∀ x, FI₀ x + (gainG γ ν ρ : ℂ) * SI x =
          V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x) +
            V1.Zs tr b_cl b_cand G_cl G_cand ρ (ψ ρ) x := by
        intro x
        simpa [Complex.cpow_zero] using hpt_TI x
      rw [← integral_const_mul, ← integral_add hFI₀_int (hSI_int.const_mul _),
        integral_congr_ae (Eventually.of_forall hpt'), integral_add hJ_int hZs_IZ.1,
        hZs_IZ.2, add_zero]
    have hSI_eq : ∫ x in B0579.cell c, SI x = ∫ x in B0579.cell c, f ρ x * (ψ ρ x : ℂ) :=
      (pairing_of_cylTest hf_pair hφ).symm
    rw [← h1, integral_congr_ae hFI₀_ae, hSI_eq]
  -- 3. Combine the three pieces
  have hpt := fun x => flatDiff_perpF_pointwise (μ := μ) tr b_cl b_1 hψ ρ x
  have hcongr : (fun x =>
      flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (fun s y => V1.perpF (ψ s) y) (ρ, x)) =
      fun x => (-V1.hInt b_1 (fun y => deriv (fun ρ' => ψ ρ' y) ρ) (ρ, x) +
        (μ / (ρ : ℂ)) * V1.hInt b_1 (ψ ρ) (ρ, x)) -
        V1.jInt tr b_cand (V1.wF b_cl b_cand) (ψ ρ) (ρ, x) := by
    funext x; rw [hpt x]
  have hI_dt_neg : IntegrableOn
      (fun x => -V1.hInt b_1 (fun y => deriv (fun ρ' => ψ ρ' y) ρ) (ρ, x)) (B0579.cell c) :=
    hI_dt.neg
  have hI_ph_mul : IntegrableOn
      (fun x => (μ / (ρ : ℂ)) * V1.hInt b_1 (ψ ρ) (ρ, x)) (B0579.cell c) :=
    integrableOn_const_mul_local (μ / (ρ : ℂ)) hI_ph
  have hI_sum : IntegrableOn
      (fun x => -V1.hInt b_1 (fun y => deriv (fun ρ' => ψ ρ' y) ρ) (ρ, x) +
        (μ / (ρ : ℂ)) * V1.hInt b_1 (ψ ρ) (ρ, x)) (B0579.cell c) :=
    hI_dt_neg.add hI_ph_mul
  rw [hcongr, integral_sub hI_sum hJ_int,
    integral_add hI_dt_neg hI_ph_mul, integral_neg, integral_const_mul,
    hEq_dt, hEq_ph, hJ_eq]
  have Iω_ph : IntegrableOn
      (fun x => ((gainG γ ν ρ : ℂ) * ω_duh ρ x) * (ψ ρ x : ℂ)) (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul hφ (hω_l2.const_mul _)
  have Iω_ph_mul : IntegrableOn
      (fun x => (μ / (ρ : ℂ)) * (((gainG γ ν ρ : ℂ) * ω_duh ρ x) * (ψ ρ x : ℂ)))
      (B0579.cell c) :=
    integrableOn_const_mul_local (μ / (ρ : ℂ)) Iω_ph
  have Iω_dt : IntegrableOn
      (fun x => ((gainG γ ν ρ : ℂ) * ω_duh ρ x) * ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul hdtφ (hω_l2.const_mul _)
  have hω_comb : -(∫ x in B0579.cell c,
        ((gainG γ ν ρ : ℂ) * ω_duh ρ x) * ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ)) +
      (μ / (ρ : ℂ)) * ∫ x in B0579.cell c, ((gainG γ ν ρ : ℂ) * ω_duh ρ x) * (ψ ρ x : ℂ) =
      -∫ x in B0579.cell c, ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
        (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    have heq : (fun x => ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
        (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))) =
        fun x => ((gainG γ ν ρ : ℂ) * ω_duh ρ x) * ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ) -
          (μ / (ρ : ℂ)) * (((gainG γ ν ρ : ℂ) * ω_duh ρ x) * (ψ ρ x : ℂ)) := by
      funext x; ring
    rw [heq, integral_sub Iω_dt Iω_ph_mul]
    ring
  linear_combination hω_comb

private theorem flatDiff_perpF_eq_zero {ν γ H s₁ s₂ R₁ M_duh : ℝ} {μ : ℂ}
    (hγ : 0 ≤ γ) (hν : 0 < ν) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂H : s₂ < H)
    (hR₁ : 0 < R₁) (hM : 0 ≤ M_duh)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {b_cl u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G_cl G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {ω_duh f : ℝ → ℝ × ℝ → ℂ}
    (hbcl_meas : ∀ i, Measurable fun p => b_cl p i)
    (hGcl_meas : ∀ i j, Measurable fun p => G_cl p i j)
    (hbcl_loc : ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ < a₂ →
      ∫⁻ p in Icc a₁ a₂ ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) < ⊤)
    (hbcl_div : ∀ s, 0 < s → ∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        (b_cl (s, x) 0 * (B0579.pd 0 χ x : ℂ) + b_cl (s, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0)
    (hbcl_wg : ∀ s, 0 < s → ∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
      (fun x => b_cl (s, x) i) (fun x => G_cl (s, x) i j))
    (hsrc_slice : ∀ t ∈ Ioo (0 : ℝ) H,
      (∀ i, MemLp (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      MemLp (f t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
        h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f t x * φ x =
          coreSrcFun (ν ^ (-2 : ℝ))
            (advStretch (trainVel tr t)
              (fun x => gainConj γ ν b_cl (t, x))
              (fun x => gainConj γ ν G_cl (t, x))) g)
    (huduh_meas : ∀ i, Measurable fun p => u_duh p i)
    (hGduh_meas : ∀ i j, Measurable fun p => G_duh p i j)
    (hduh_bd : ∀ s ∈ Ioo (0 : ℝ) H,
      ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
          ENNReal.ofReal M_duh)
    (hduh_slice : ∀ s ∈ Ioo (0 : ℝ) H,
      (∀ i, MemLp (fun x => u_duh (s, x) i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      MemLp (ω_duh s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      (∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (u_duh (s, x) 0 * (B0579.pd 0 χ x : ℂ) + u_duh (s, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0) ∧
      (∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
        (fun x => u_duh (s, x) i) (fun x => G_duh (s, x) i j)) ∧
      ((fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
        =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω_duh s))
    (hduh_eq : ∀ (ψ : ℝ → ℝ × ℝ → ℝ) (a₁ a₂ R : ℝ),
      0 < a₁ → a₁ < a₂ → a₂ < H → 0 < R →
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) →
      (∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x) →
      (∀ s x, (s < a₁ ∨ a₂ < s ∨ R < |x.2|) → ψ s x = 0) →
      ∫ ρ in Ioo (0 : ℝ) H,
        ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr
              (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
              (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x) +
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
              (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))) +
          (gainG γ ν ρ : ℂ) *
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f ρ x * (ψ ρ x : ℂ)) = 0)
    {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x)
    (hsupp : ∀ s x, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → ψ s x = 0) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p => gainG γ ν p.1 • u_duh p
    let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (fun s y => V1.perpF (ψ s) y) p = 0 := by
  intro c b_1 b_cand
  have hΦ_sm : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => V1.perpF (ψ p.1) p.2 i) :=
    contDiff_perpF_comp hψ
  have hΦ_sp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → V1.perpF (ψ s) x i = 0 :=
    supp_perpF_comp hsupp
  obtain ⟨hint_Ioi, heq_Ioo⟩ := integrableOn_flatDiff_supported hγ hν hs₁ hs₁₂ hs₂H hR₁ hM
    hbuc hbcl_meas hGcl_meas hbcl_loc huduh_meas hGduh_meas hduh_bd hΦ_sm hΦ_sp
  have hint_Ioo : IntegrableOn
      (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (fun s y => V1.perpF (ψ s) y))
      (Ioo (0 : ℝ) H ×ˢ B0579.cell c) :=
    hint_Ioi.mono_set (prod_mono Ioo_subset_Ioi_self Subset.rfl)
  rw [heq_Ioo]
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint_Ioo
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint_Ioo]
  have hband : ∀ s x, R₁ < |x.2| → ψ s x = 0 := fun s x hx => hsupp s x (Or.inr (Or.inr hx))
  have hslice_congr : ∀ ρ ∈ Ioo (0 : ℝ) H,
      (∫ x in B0579.cell c,
        flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (fun s y => V1.perpF (ψ s) y) (ρ, x)) =
      -((∫ x in B0579.cell c,
          flowIntegrand tr
            (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
            (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x) +
        (∫ x in B0579.cell c,
          ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
            (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))) +
        (gainG γ ν ρ : ℂ) * ∫ x in B0579.cell c, f ρ x * (ψ ρ x : ℂ)) := by
    intro ρ hρ
    obtain ⟨hbcl_lp, hf_mem, hf_pair⟩ := hsrc_slice ρ hρ
    obtain ⟨huduh_lp, hω_mem, huduh_div, huduh_wg, huduh_curl⟩ := hduh_slice ρ hρ
    exact flatDiff_perpF_slice_eq hρ hbcl_lp (hbcl_div ρ hρ.1) (hbcl_wg ρ hρ.1)
      hf_mem hf_pair huduh_lp hω_mem huduh_div huduh_wg huduh_curl hψ hper hband
  rw [setIntegral_congr_fun measurableSet_Ioo hslice_congr, integral_neg,
    hduh_eq ψ s₁ s₂ R₁ hs₁ hs₁₂ hs₂H hR₁ hψ hper hsupp, neg_zero]

/-! ## 5. Stream-cutoff approximation for general core flat tests -/

private def etaPrim (R₀ : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ τ in (-(R₀ + 1))..x.2, Φ s (x.1, τ) 0

private theorem etaPrim_props {c s₁ s₂ R₀ : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : IsFlatTest c Φ)
    (hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₀ < |x.2|) → Φ s x i = 0)
    (hR₀ : 0 < R₀) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => etaPrim R₀ Φ p.1 p.2) ∧
      (∀ s x, etaPrim R₀ Φ s (x.1 + c, x.2) = etaPrim R₀ Φ s x) ∧
      (∀ s x, (s < s₁ ∨ s₂ < s) → etaPrim R₀ Φ s x = 0) ∧
      (∀ s x, x.2 < -(R₀ + 1) → etaPrim R₀ Φ s x = 0) ∧
      (∀ s x, B0579.pd 1 (etaPrim R₀ Φ s) x = Φ s x 0) ∧
      (∀ s x, B0579.pd 0 (etaPrim R₀ Φ s) x = -Φ s x 1) ∧
      (∀ s x, R₀ + 1 ≤ x.2 → etaPrim R₀ Φ s x = etaPrim R₀ Φ s (0, R₀ + 1)) := by
  have hsm : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => etaPrim R₀ Φ p.1 p.2) := by
    have hmul : (fun p : ℝ × (ℝ × ℝ) => etaPrim R₀ Φ p.1 p.2) =
        fun p => (p.2.2 + (R₀ + 1)) *
          ∫ u in (0 : ℝ)..1, Φ p.1 (p.2.1, (p.2.2 + (R₀ + 1)) * u + -(R₀ + 1)) 0 := by
      funext p
      have h := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun τ => Φ p.1 (p.2.1, τ) 0) (p.2.2 + (R₀ + 1)) (-(R₀ + 1))
      have e0 : (p.2.2 + (R₀ + 1)) * 0 + -(R₀ + 1) = -(R₀ + 1) := by ring
      have e1 : (p.2.2 + (R₀ + 1)) * 1 + -(R₀ + 1) = p.2.2 := by ring
      rw [e0, e1, smul_eq_mul] at h
      exact h.symm
    rw [hmul]
    set H_in : (ℝ × (ℝ × ℝ)) × ℝ → ℝ :=
      fun z => Φ z.1.1 (z.1.2.1, (z.1.2.2 + (R₀ + 1)) * z.2 + -(R₀ + 1)) 0
    have hH_in : ContDiff ℝ ∞ H_in :=
      (hΦ.smooth 0).comp (contDiff_fst.fst.prodMk
        (contDiff_fst.snd.fst.prodMk
          (((contDiff_fst.snd.snd.add contDiff_const).mul contDiff_snd).add contDiff_const)))
    have hint_sm : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ∫ u in (0 : ℝ)..1, H_in (p, u)) :=
      contDiff_infty.2 fun n =>
        DfcQPrimSmoothAux.ipsContDiff (ℝ × (ℝ × ℝ)) 0 1 n ℝ H_in
          (contDiff_infty.1 hH_in n)
    exact (contDiff_snd.snd.add contDiff_const).mul hint_sm
  have hper : ∀ s x, etaPrim R₀ Φ s (x.1 + c, x.2) = etaPrim R₀ Φ s x := by
    intro s x; unfold etaPrim; congr 1; funext τ; exact hΦ.periodic s (x.1, τ) 0
  have hts : ∀ s x, (s < s₁ ∨ s₂ < s) → etaPrim R₀ Φ s x = 0 := by
    intro s x hs; unfold etaPrim
    have h0 : ∀ τ : ℝ, Φ s (x.1, τ) 0 = 0 :=
      fun τ => hsupp s (x.1, τ) 0 (hs.imp id Or.inl)
    simp [h0]
  have hbot : ∀ s x, x.2 < -(R₀ + 1) → etaPrim R₀ Φ s x = 0 := by
    intro s x hx; unfold etaPrim
    have h0 : EqOn (fun τ => Φ s (x.1, τ) 0) 0 (uIcc (-(R₀ + 1)) x.2) := by
      intro τ hτ
      rw [uIcc_of_ge hx.le] at hτ
      have hlt : R₀ < |τ| := by
        rw [abs_of_neg (by linarith [hτ.2, hR₀])]
        linarith [hτ.2]
      exact hsupp s (x.1, τ) 0 (Or.inr (Or.inr hlt))
    rw [intervalIntegral.integral_congr h0]; simp
  have hpd1 : ∀ s x, B0579.pd 1 (etaPrim R₀ Φ s) x = Φ s x 0 := by
    intro s ⟨q, η⟩
    have hslice_sm : ContDiff ℝ ∞ (etaPrim R₀ Φ s) :=
      hsm.comp (contDiff_const.prodMk contDiff_id)
    rw [DfcQPrimDerivAux.pd1_eq _ q η (hslice_sm.differentiable (by simp) (q, η))]
    have hfc : Continuous fun τ : ℝ => Φ s (q, τ) 0 :=
      (hΦ.smooth 0).continuous.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    exact (intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt).deriv
  have hpd0 : ∀ s x, B0579.pd 0 (etaPrim R₀ Φ s) x = -Φ s x 1 := by
    intro s ⟨q, η⟩
    have hslice_sm : ContDiff ℝ ∞ (etaPrim R₀ Φ s) :=
      hsm.comp (contDiff_const.prodMk contDiff_id)
    rw [DfcQPrimDerivAux.pd0_eq _ q η (hslice_sm.differentiable (by simp) (q, η))]
    set g_sw : ℝ × ℝ → ℝ := fun z => Φ s (z.2, z.1) 0
    have hg_sw : ContDiff ℝ ∞ g_sw :=
      (hΦ.smooth 0).comp (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))
    have hd_param := (DfcQPrimDerivAux.hasDerivAt_param g_sw hg_sw (-(R₀ + 1)) η q).deriv
    have hfun : (fun q' : ℝ => etaPrim R₀ Φ s (q', η)) =
        fun q' : ℝ => ∫ τ in (-(R₀ + 1))..η, g_sw (τ, q') := rfl
    rw [hfun, hd_param]
    have hsw_pd : ∀ τ : ℝ, B0579.pd 1 g_sw (τ, q) = -B0579.pd 1 (fun y => Φ s y 1) (q, τ) := by
      intro τ
      have h1 : B0579.pd 1 g_sw (τ, q) = B0579.pd 0 (fun y => Φ s y 0) (q, τ) := by
        rw [DfcQPrimDerivAux.pd1_eq g_sw τ q (hg_sw.differentiable (by simp) (τ, q)),
          DfcQPrimDerivAux.pd0_eq (fun y => Φ s y 0) q τ
            (((hΦ.smooth 0).comp (contDiff_const.prodMk contDiff_id)).differentiable
              (by simp) (q, τ))]
      linarith [hΦ.divFree s (q, τ)]
    simp_rw [hsw_pd]
    have hftc : ∀ τ ∈ uIcc (-(R₀ + 1)) η,
        HasDerivAt (fun τ' : ℝ => -Φ s (q, τ') 1)
          (-B0579.pd 1 (fun y => Φ s y 1) (q, τ)) τ := by
      intro τ _
      have hf1_τ : DifferentiableAt ℝ (fun τ' => Φ s (q, τ') 1) τ :=
        ((hΦ.smooth 1).comp
          (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).differentiable
          (by simp) τ
      have hpd1_eq := DfcQPrimDerivAux.pd1_eq (fun y => Φ s y 1) q τ
        (((hΦ.smooth 1).comp (contDiff_const.prodMk contDiff_id)).differentiable
          (by simp) (q, τ))
      rw [hpd1_eq]
      exact hf1_τ.hasDerivAt.neg
    have hint_f1 : IntervalIntegrable
        (fun τ => -B0579.pd 1 (fun y => Φ s y 1) (q, τ)) volume (-(R₀ + 1)) η := by
      have hc : Continuous fun τ : ℝ => -B0579.pd 1 (fun y => Φ s y 1) (q, τ) :=
        ((contDiff_flatGrad hΦ.smooth 1 1).continuous.comp
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))).neg
      exact hc.intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint_f1]
    have hbot1 : Φ s (q, -(R₀ + 1)) 1 = 0 := by
      refine hsupp s (q, -(R₀ + 1)) 1 (Or.inr (Or.inr ?_))
      rw [abs_of_neg (by linarith)]; linarith
    rw [hbot1]; ring
  have htop : ∀ s x, R₀ + 1 ≤ x.2 → etaPrim R₀ Φ s x = etaPrim R₀ Φ s (0, R₀ + 1) := by
    intro s x hx
    have hsplit : etaPrim R₀ Φ s x = etaPrim R₀ Φ s (x.1, R₀ + 1) := by
      unfold etaPrim
      have hc : Continuous fun τ : ℝ => Φ s (x.1, τ) 0 :=
        (hΦ.smooth 0).continuous.comp
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (-(R₀ + 1)) (R₀ + 1)) (hc.intervalIntegrable (R₀ + 1) x.2)]
      have h0 : EqOn (fun τ => Φ s (x.1, τ) 0) 0 (uIcc (R₀ + 1) x.2) := by
        intro τ hτ
        rw [uIcc_of_le hx] at hτ
        have hlt : R₀ < |τ| := by
          rw [abs_of_pos (by linarith [hτ.1])]
          linarith [hτ.1]
        exact hsupp s (x.1, τ) 0 (Or.inr (Or.inr hlt))
      rw [intervalIntegral.integral_congr h0]
      simp
    rw [hsplit]
    set hq : ℝ → ℝ := fun q => etaPrim R₀ Φ s (q, R₀ + 1)
    have hq_diff : Differentiable ℝ hq :=
      (hsm.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).differentiable
        (by simp)
    have hq_deriv : ∀ q : ℝ, deriv hq q = 0 := by
      intro q
      have hslice_sm : ContDiff ℝ ∞ (etaPrim R₀ Φ s) :=
        hsm.comp (contDiff_const.prodMk contDiff_id)
      rw [← DfcQPrimDerivAux.pd0_eq _ q (R₀ + 1) (hslice_sm.differentiable (by simp) (q, R₀ + 1)),
        hpd0 s (q, R₀ + 1)]
      have h0 : Φ s (q, R₀ + 1) 1 = 0 := by
        refine hsupp s (q, R₀ + 1) 1 (Or.inr (Or.inr ?_))
        rw [abs_of_pos (by linarith)]; linarith
      simp [h0]
    exact is_const_of_deriv_eq_zero hq_diff hq_deriv x.1 0
  exact ⟨hsm, hper, hts, hbot, hpd1, hpd0, htop⟩

private theorem flatDiff_compactTime_eq_zero {ν γ H H' M_duh : ℝ} {μ : ℂ}
    (hγ : 0 ≤ γ) (hν : 0 < ν) (hH'0 : 0 < H') (hH'H : H' < H) (hM : 0 ≤ M_duh)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {b_cl u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G_cl G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {ω_duh f : ℝ → ℝ × ℝ → ℂ}
    (hbcl_meas : ∀ i, Measurable fun p => b_cl p i)
    (hGcl_meas : ∀ i j, Measurable fun p => G_cl p i j)
    (hbcl_loc : ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ < a₂ →
      ∫⁻ p in Icc a₁ a₂ ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) < ⊤)
    (hbcl_div : ∀ s, 0 < s → ∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        (b_cl (s, x) 0 * (B0579.pd 0 χ x : ℂ) + b_cl (s, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0)
    (hbcl_wg : ∀ s, 0 < s → ∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
      (fun x => b_cl (s, x) i) (fun x => G_cl (s, x) i j))
    (hsrc_slice : ∀ t ∈ Ioo (0 : ℝ) H,
      (∀ i, MemLp (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      MemLp (f t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
        h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f t x * φ x =
          coreSrcFun (ν ^ (-2 : ℝ))
            (advStretch (trainVel tr t)
              (fun x => gainConj γ ν b_cl (t, x))
              (fun x => gainConj γ ν G_cl (t, x))) g)
    (huduh_meas : ∀ i, Measurable fun p => u_duh p i)
    (hGduh_meas : ∀ i j, Measurable fun p => G_duh p i j)
    (hduh_bd : ∀ s ∈ Ioo (0 : ℝ) H,
      ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
          ENNReal.ofReal M_duh)
    (hduh_slice : ∀ s ∈ Ioo (0 : ℝ) H,
      (∀ i, MemLp (fun x => u_duh (s, x) i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      MemLp (ω_duh s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      (∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (u_duh (s, x) 0 * (B0579.pd 0 χ x : ℂ) + u_duh (s, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0) ∧
      (∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
        (fun x => u_duh (s, x) i) (fun x => G_duh (s, x) i j)) ∧
      ((fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
        =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω_duh s))
    (hduh_eq : ∀ (ψ : ℝ → ℝ × ℝ → ℝ) (a₁ a₂ R : ℝ),
      0 < a₁ → a₁ < a₂ → a₂ < H → 0 < R →
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) →
      (∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x) →
      (∀ s x, (s < a₁ ∨ a₂ < s ∨ R < |x.2|) → ψ s x = 0) →
      ∫ ρ in Ioo (0 : ℝ) H,
        ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr
              (fun y => (gainG γ ν ρ : ℂ) * ω_duh ρ y)
              (fun y => (gainG γ ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x) +
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            ((gainG γ ν ρ : ℂ) * ω_duh ρ x) *
              (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))) +
          (gainG γ ν ρ : ℂ) *
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f ρ x * (ψ ρ x : ℂ)) = 0)
    {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ : IsFlatTest (ν ^ (-2 : ℝ)) Φ)
    (hΦ_H' : ∀ s x i, H' ≤ s → Φ s x i = 0) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p => gainG γ ν p.1 • u_duh p
    let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
    IntegrableOn (flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p = 0 := by
  intro c b_1 b_cand
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨s₁_raw, s₂_raw, R_raw, hs₁_raw, hsupp_raw⟩ := hΦ.support
  set s₁ : ℝ := min (s₁_raw / 2) (H' / 2)
  set s₂ : ℝ := (H' + H) / 2
  set R₀ : ℝ := max R_raw 1
  have hs₁ : 0 < s₁ := lt_min (half_pos hs₁_raw) (half_pos hH'0)
  have hs₁₂ : s₁ < s₂ := by
    have h1 : s₁ ≤ H' / 2 := min_le_right _ _
    dsimp [s₂]; linarith
  have hs₂H : s₂ < H := by dsimp [s₂]; linarith
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₀ < |x.2|) → Φ s x i = 0 := by
    intro s x i hout
    rcases hout with h1 | h2 | h3
    · have : s < s₁_raw := lt_of_lt_of_le h1 ((min_le_left _ _).trans (by linarith))
      exact hsupp_raw s x i (Or.inl this)
    · exact hΦ_H' s x i (by dsimp [s₂] at h2; linarith)
    · exact hsupp_raw s x i (Or.inr (Or.inr (lt_of_le_of_lt (le_max_left _ _) h3)))
  obtain ⟨hint_Φ, _⟩ := integrableOn_flatDiff_supported hγ hν hs₁ hs₁₂ hs₂H hR₀ hM
    hbuc hbcl_meas hGcl_meas hbcl_loc huduh_meas hGduh_meas hduh_bd hΦ.smooth hsupp
  refine ⟨hint_Φ, ?_⟩
  -- Construct `Θ` and bump cutoffs `ψ_k`
  obtain ⟨hΘ_sm, hΘ_per, hΘ_ts, hΘ_bot, hΘ_pd1, hΘ_pd0, hΘ_top⟩ :=
    etaPrim_props hΦ hsupp hR₀
  set Θ := etaPrim R₀ Φ
  set m_s : ℝ → ℝ := fun s => Θ s (0, R₀ + 1)
  have hm_sm : ContDiff ℝ ∞ m_s :=
    hΘ_sm.comp (contDiff_id.prodMk contDiff_const)
  have hm_diff : Differentiable ℝ m_s := hm_sm.differentiable (by simp)
  have hdm_sm : ContDiff ℝ ∞ (deriv m_s) := (contDiff_infty_iff_deriv.mp hm_sm).2
  obtain ⟨M_m, hM_m⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hm_sm.continuous.abs.add hdm_sm.continuous.abs).continuousOn
  have hM_m0 : 0 ≤ M_m :=
    (norm_nonneg _).trans (hM_m s₁ ⟨le_rfl, hs₁₂.le⟩)
  -- Bump function `b_bump` with radii `1` and `2`
  let b_bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb_sm : ContDiff ℝ ∞ (⇑b_bump) := b_bump.contDiff
  have hdb1_sm : ContDiff ℝ ∞ (deriv (⇑b_bump)) := (contDiff_infty_iff_deriv.mp hb_sm).2
  have hdb2_sm : ContDiff ℝ ∞ (deriv (deriv (⇑b_bump))) :=
    (contDiff_infty_iff_deriv.mp hdb1_sm).2
  have hdb3_sm : ContDiff ℝ ∞ (deriv (deriv (deriv (⇑b_bump)))) :=
    (contDiff_infty_iff_deriv.mp hdb2_sm).2
  obtain ⟨Cb1, hCb1⟩ := hdb1_sm.continuous.bounded_above_of_compact_support
    b_bump.hasCompactSupport.deriv
  obtain ⟨Cb2, hCb2⟩ := hdb2_sm.continuous.bounded_above_of_compact_support
    b_bump.hasCompactSupport.deriv.deriv
  obtain ⟨Cb3, hCb3⟩ := hdb3_sm.continuous.bounded_above_of_compact_support
    b_bump.hasCompactSupport.deriv.deriv.deriv
  have hCb_nn : 0 ≤ Cb1 + Cb2 + Cb3 := by
    have h1 := (norm_nonneg _).trans (hCb1 0)
    have h2 := (norm_nonneg _).trans (hCb2 0)
    have h3 := (norm_nonneg _).trans (hCb3 0)
    linarith
  have hb_one : ∀ t : ℝ, |t| ≤ 1 → b_bump t = 1 := by
    intro t ht; apply b_bump.one_of_mem_closedBall
    simpa [b_bump, Metric.mem_closedBall, Real.dist_eq] using ht
  have hb_zero : ∀ t : ℝ, 2 ≤ |t| → b_bump t = 0 := by
    intro t ht; apply b_bump.zero_of_le_dist
    simpa [b_bump, Real.dist_eq] using ht
  -- Family `R_k = R₀ + 2 + k`
  set R_seq : ℕ → ℝ := fun k => R₀ + 2 + (k : ℝ)
  set χ_seq : ℕ → ℝ → ℝ := fun k η => b_bump (η / R_seq k)
  set ψ_seq : ℕ → ℝ → ℝ × ℝ → ℝ := fun k s x => χ_seq k x.2 * Θ s x
  set E_seq : ℕ → ℝ → ℝ × ℝ → Fin 2 → ℝ :=
    fun k s x i => V1.perpF (ψ_seq k s) x i - Φ s x i
  -- Energy and velocity bounds on `[s₁, s₂]`
  have hloc := energyLoc_cand hγ hν hs₁ hs₁₂ hs₂H hM hbcl_meas hGcl_meas
    (hbcl_loc s₁ s₂ hs₁ hs₁₂) huduh_meas hGduh_meas hduh_bd
  have hb1_meas : ∀ i, Measurable fun p => b_1 p i :=
    fun i => (measurable_gainG_fst γ ν).smul (huduh_meas i)
  have hbcand_meas : ∀ i, Measurable fun p => b_cand p i :=
    fun i => (hbcl_meas i).add (hb1_meas i)
  obtain ⟨M_v, hMv0, hMv⟩ := core_trainVel_bound_le tr hbuc (hs₁.le.trans (hs₁₂.le.trans hs₂H.le))
  set g_sq : ℝ × (ℝ × ℝ) → ℝ := fun p => (vnorm2 (b_1 p) + vnorm2 (b_cand p)) ^ 2
  set E_tot : ℝ := ∫ p in Icc s₁ s₂ ×ˢ B0579.cell c, g_sq p
  have hEtot_nn : 0 ≤ E_tot := setIntegral_nonneg
    (measurableSet_Icc.prod (B0579.measurableSet_cell c)) (fun _ _ => sq_nonneg _)
  set C_err : ℝ :=
    (1 + ‖μ‖ / s₁ + |ν| + 2 * M_v) * (Cb1 + Cb2 + Cb3) * M_m
  have hCerr_nn : 0 ≤ C_err := by
    dsimp [C_err]
    exact mul_nonneg (mul_nonneg (by positivity) hCb_nn) hM_m0
  -- Show `‖∫ flatDiffIntegrand ... Φ‖ ≤ C_err * ((s₂ - s₁) * c + E_tot) / (2 * √(R_seq k))`
  have hbound_k : ∀ k : ℕ,
      ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p‖ ≤
        C_err * (((s₂ - s₁) * c + E_tot) / (2 * Real.sqrt (R_seq k))) := by
    intro k
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hRk_ge1 : 1 ≤ R_seq k := by dsimp [R_seq]; linarith
    have hRk_pos : 0 < R_seq k := by linarith
    have hRk_gt : R₀ + 1 < R_seq k := by dsimp [R_seq]; linarith
    -- Smoothness, periodicity, support of `ψ_seq k`
    have hχ_sm : ContDiff ℝ ∞ (χ_seq k) := hb_sm.comp (contDiff_id.div_const _)
    have hψk_sm : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ_seq k p.1 p.2) :=
      (hχ_sm.comp contDiff_snd.snd).mul hΘ_sm
    have hψk_per : ∀ s x, ψ_seq k s (x.1 + c, x.2) = ψ_seq k s x := by
      intro s x; dsimp [ψ_seq]; rw [hΘ_per]
    have hψk_supp : ∀ s x, (s < s₁ ∨ s₂ < s ∨ 2 * R_seq k < |x.2|) → ψ_seq k s x = 0 := by
      intro s x hout
      rcases hout with hs | hs | hx
      · dsimp [ψ_seq]; rw [hΘ_ts s x (Or.inl hs), mul_zero]
      · dsimp [ψ_seq]; rw [hΘ_ts s x (Or.inr hs), mul_zero]
      · dsimp [ψ_seq, χ_seq]
        have h2 : 2 ≤ |x.2 / R_seq k| := by
          rw [abs_div, abs_of_pos hRk_pos, le_div_iff₀ hRk_pos]
          exact hx.le
        rw [hb_zero _ h2, zero_mul]
    have hperp_int_zero := flatDiff_perpF_eq_zero hγ hν hs₁ hs₁₂ hs₂H (by positivity : 0 < 2 * R_seq k)
      hM hbuc hbcl_meas hGcl_meas hbcl_loc hbcl_div hbcl_wg hsrc_slice
      huduh_meas hGduh_meas hduh_bd hduh_slice hduh_eq hψk_sm hψk_per hψk_supp
    have hperp_sm := contDiff_perpF_comp hψk_sm
    have hperp_sp := supp_perpF_comp hψk_supp
    obtain ⟨hint_perp, _⟩ := integrableOn_flatDiff_supported hγ hν hs₁ hs₁₂ hs₂H
      (by positivity : 0 < 2 * R_seq k) hM hbuc hbcl_meas hGcl_meas hbcl_loc
      huduh_meas hGduh_meas hduh_bd hperp_sm hperp_sp
    have hEk_sm : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => E_seq k p.1 p.2 i) :=
      fun i => (hperp_sm i).sub (hΦ.smooth i)
    have hEk_sp_coarse : ∀ s x i,
        (s < s₁ ∨ s₂ < s ∨ 2 * R_seq k < |x.2|) → E_seq k s x i = 0 := by
      intro s x i hout
      dsimp [E_seq]
      rw [hperp_sp s x i hout, hsupp s x i ?_, sub_zero]
      exact hout.imp id (Or.imp id fun h => lt_trans (by linarith) h)
    obtain ⟨hint_Ek, _⟩ := integrableOn_flatDiff_supported hγ hν hs₁ hs₁₂ hs₂H
      (by positivity : 0 < 2 * R_seq k) hM hbuc hbcl_meas hGcl_meas hbcl_loc
      huduh_meas hGduh_meas hduh_bd hEk_sm hEk_sp_coarse
    have hint_eq : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p =
        -∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p := by
      have hsub_fn : flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) =
          fun p => flatDiffIntegrand ν μ (trainVel tr) b_cand b_1
              (fun s y => V1.perpF (ψ_seq k s) y) p -
            flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p :=
        funext fun p => flatDiffIntegrand_sub_test ν μ (trainVel tr) b_cand b_1 _ Φ
          hperp_sm hΦ.smooth p
      rw [hsub_fn, integral_sub hint_perp hint_Φ, hperp_int_zero, zero_sub, neg_neg]
    -- Derivatives of `χ_seq k`
    have hdχ1 : deriv (χ_seq k) = fun η => deriv (⇑b_bump) (η / R_seq k) * (1 / R_seq k) := by
      funext η
      exact (((hb_sm.differentiable (by simp) _).hasDerivAt).comp η
        ((hasDerivAt_id' η).div_const (R_seq k))).deriv
    have hdχ2 : deriv (deriv (χ_seq k)) =
        fun η => deriv (deriv (⇑b_bump)) (η / R_seq k) * (1 / R_seq k) * (1 / R_seq k) := by
      funext η; rw [hdχ1]
      exact ((((hdb1_sm.differentiable (by simp) _).hasDerivAt).comp η
        ((hasDerivAt_id' η).div_const (R_seq k))).mul_const _).deriv
    have hdχ3 : deriv (deriv (deriv (χ_seq k))) = fun η =>
        deriv (deriv (deriv (⇑b_bump))) (η / R_seq k) *
          (1 / R_seq k) * (1 / R_seq k) * (1 / R_seq k) := by
      funext η; rw [hdχ2]
      exact (((((hdb2_sm.differentiable (by simp) _).hasDerivAt).comp η
        ((hasDerivAt_id' η).div_const (R_seq k))).mul_const _).mul_const _).deriv
    have hinv_le1 : 1 / R_seq k ≤ 1 := (div_le_one hRk_pos).2 hRk_ge1
    have hinv_pos : 0 < 1 / R_seq k := one_div_pos.2 hRk_pos
    have hdχ1_bd : ∀ η, |deriv (χ_seq k) η| ≤ Cb1 / R_seq k := by
      intro η
      have h := hCb1 (η / R_seq k); rw [Real.norm_eq_abs] at h
      rw [hdχ1, abs_mul, abs_of_pos hinv_pos, mul_one_div]
      exact div_le_div_of_nonneg_right h hRk_pos.le
    have hdχ2_bd : ∀ η, |deriv (deriv (χ_seq k)) η| ≤ Cb2 / R_seq k := by
      intro η
      have h := hCb2 (η / R_seq k); rw [Real.norm_eq_abs] at h
      rw [hdχ2, abs_mul, abs_mul, abs_of_pos hinv_pos]
      calc |deriv (deriv (⇑b_bump)) (η / R_seq k)| * (1 / R_seq k) * (1 / R_seq k)
          ≤ Cb2 * 1 * (1 / R_seq k) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul h hinv_le1 hinv_pos.le ((norm_nonneg _).trans (hCb2 0))) hinv_pos.le
        _ = Cb2 / R_seq k := by ring
    have hdχ3_bd : ∀ η, |deriv (deriv (deriv (χ_seq k))) η| ≤ Cb3 / R_seq k := by
      intro η
      have h := hCb3 (η / R_seq k); rw [Real.norm_eq_abs] at h
      rw [hdχ3, abs_mul, abs_mul, abs_mul, abs_of_pos hinv_pos]
      have hCb3_0 := (norm_nonneg _).trans (hCb3 0)
      calc |deriv (deriv (deriv (⇑b_bump))) (η / R_seq k)| *
              (1 / R_seq k) * (1 / R_seq k) * (1 / R_seq k)
          ≤ Cb3 * 1 * 1 * (1 / R_seq k) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (mul_le_mul h hinv_le1 hinv_pos.le hCb3_0)
                hinv_le1 hinv_pos.le (by positivity)) hinv_pos.le
        _ = Cb3 / R_seq k := by ring
    -- `E_seq k` vanishes on `{s < s₁ ∨ s₂ < s ∨ x.2 < R_seq k ∨ 2 * R_seq k < x.2}`
    have hEk_zero_region : ∀ s (x : ℝ × ℝ) i,
        (s < s₁ ∨ s₂ < s ∨ x.2 < R_seq k ∨ 2 * R_seq k < x.2) → E_seq k s x i = 0 := by
      intro s x i hout
      rcases hout with hs | hs | hx_lt | hx_gt
      · exact hEk_sp_coarse s x i (Or.inl hs)
      · exact hEk_sp_coarse s x i (Or.inr (Or.inl hs))
      · by_cases hlow : -(R₀ + 1) - 1 / 2 < x.2
        · -- `|x.2| < R_seq k`, so `χ_seq k = 1` near `x`
          have habs : |x.2| < R_seq k := abs_lt.2 ⟨by dsimp [R_seq]; linarith, hx_lt⟩
          have hU : {y : ℝ × ℝ | |y.2| < R_seq k} ∈ 𝓝 x :=
            (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).mem_nhds habs
          have hev : ψ_seq k s =ᶠ[𝓝 x] Θ s := by
            filter_upwards [hU] with y hy
            dsimp [ψ_seq, χ_seq]
            have h1 : |y.2 / R_seq k| ≤ 1 := by
              rw [abs_div, abs_of_pos hRk_pos, div_le_one hRk_pos]
              exact hy.le
            rw [hb_one _ h1, one_mul]
          have hpd_eq : ∀ j : Fin 2, B0579.pd j (ψ_seq k s) x = B0579.pd j (Θ s) x :=
            fun j => pd_eq_of_eventuallyEq hev j
          dsimp [E_seq]
          fin_cases i
          · simp [V1.perpF_zero, hpd_eq 1, hΘ_pd1]
          · simp [V1.perpF_one, hpd_eq 0, hΘ_pd0]
        · -- `x.2 ≤ -(R₀ + 1) - 1/2 < -(R₀ + 1)`, so `Θ s = 0` and `Φ s = 0` near `x`
          have hx_neg : x.2 < -(R₀ + 1) := by linarith
          have hU : {y : ℝ × ℝ | y.2 < -(R₀ + 1)} ∈ 𝓝 x :=
            (isOpen_lt continuous_snd continuous_const).mem_nhds hx_neg
          have hev : ψ_seq k s =ᶠ[𝓝 x] 0 := by
            filter_upwards [hU] with y hy
            dsimp [ψ_seq]; rw [hΘ_bot s y hy, mul_zero]
          have hpd0 : ∀ j : Fin 2, B0579.pd j (ψ_seq k s) x = 0 :=
            fun j => pd_eq_zero_of_eventuallyEq hev j
          have hΦ0 : Φ s x i = 0 := by
            refine hsupp s x i (Or.inr (Or.inr ?_))
            rw [abs_of_neg (by linarith)]; linarith
          dsimp [E_seq]; rw [hΦ0, sub_zero]
          fin_cases i
          · simp [V1.perpF_zero, hpd0 1]
          · simp [V1.perpF_one, hpd0 0]
      · exact hEk_sp_coarse s x i (Or.inr (Or.inr (lt_of_lt_of_le hx_gt (le_abs_self x.2))))
    -- Outside `S_k := Icc s₁ s₂ ×ˢ (Ico (-(c/2)) (c/2) ×ˢ Icc (R_seq k) (2 * R_seq k))`,
    -- `flatDiffIntegrand ... (E_seq k) = 0`
    set S_k : Set (ℝ × (ℝ × ℝ)) :=
      Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (R_seq k) (2 * R_seq k))
    have hSk_meas : MeasurableSet S_k :=
      measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
    have hSk_sub_Ioi : S_k ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
      fun p hp => ⟨lt_of_lt_of_le hs₁ hp.1.1, hp.2.1, trivial⟩
    have hSk_sub_strip : S_k ⊆ Icc s₁ s₂ ×ˢ B0579.cell c :=
      prod_mono Subset.rfl (prod_mono Subset.rfl (subset_univ _))
    have hEk_diff_zero_off : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ S_k,
        flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p = 0 := by
      intro p hp
      have hout : p.1 < s₁ ∨ s₂ < p.1 ∨ p.2.2 < R_seq k ∨ 2 * R_seq k < p.2.2 := by
        by_contra hnot
        simp only [not_or, not_lt] at hnot
        exact hp.2 ⟨⟨hnot.1, hnot.2.1⟩, hp.1.2.1, ⟨hnot.2.2.1, hnot.2.2.2⟩⟩
      let U_out : Set (ℝ × (ℝ × ℝ)) :=
        {q | q.1 < s₁ ∨ s₂ < q.1 ∨ q.2.2 < R_seq k ∨ 2 * R_seq k < q.2.2}
      have hU_open : IsOpen U_out :=
        (isOpen_lt continuous_fst continuous_const).union
          ((isOpen_lt continuous_const continuous_fst).union
            ((isOpen_lt continuous_snd.snd continuous_const).union
              (isOpen_lt continuous_const continuous_snd.snd)))
      have hU_mem := hU_open.mem_nhds hout
      have h0 : ∀ i, E_seq k p.1 p.2 i = 0 := fun i => hEk_zero_region p.1 p.2 i hout
      have hdt0 : ∀ i, flatDt (E_seq k) p.1 p.2 i = 0 := by
        intro i; unfold flatDt
        have hev : (fun s' => E_seq k s' p.2 i) =ᶠ[𝓝 p.1] 0 := by
          have hc_in : ContinuousAt (fun s' : ℝ => (s', p.2)) p.1 :=
            continuousAt_id.prodMk continuousAt_const
          filter_upwards [hc_in hU_mem] with s' hs'
          exact hEk_zero_region s' p.2 i hs'
        rw [hev.deriv_eq]; simp
      let V_x : Set (ℝ × ℝ) := {y | (p.1, y) ∈ U_out}
      have hVx_open : IsOpen V_x := hU_open.preimage (continuous_const.prodMk continuous_id)
      have hpd_zero_on : ∀ y ∈ V_x, ∀ i j, B0579.pd j (fun z => E_seq k p.1 z i) y = 0 := by
        intro y hy i j
        have hev_y : (fun z => E_seq k p.1 z i) =ᶠ[𝓝 y] 0 :=
          Filter.eventually_of_mem (hVx_open.mem_nhds hy) fun z hz => hEk_zero_region p.1 z i hz
        exact pd_eq_zero_of_eventuallyEq hev_y j
      have hpd_ev : ∀ i j, B0579.pd j (fun y => E_seq k p.1 y i) =ᶠ[𝓝 p.2] 0 :=
        fun i j => Filter.eventually_of_mem (hVx_open.mem_nhds hout) fun y hy =>
          hpd_zero_on y hy i j
      have hgr0 : ∀ i j, flatGrad (E_seq k) p.1 p.2 i j = 0 :=
        fun i j => hpd_zero_on p.2 hout i j
      have hlp0 : ∀ i, flatLap (E_seq k) p.1 p.2 i = 0 := by
        intro i; unfold flatLap lapP
        have h00 : B0579.pd 0 (B0579.pd 0 (fun y => E_seq k p.1 y i)) p.2 = 0 :=
          pd_eq_zero_of_eventuallyEq (hpd_ev i 0) 0
        have h11 : B0579.pd 1 (B0579.pd 1 (fun y => E_seq k p.1 y i)) p.2 = 0 :=
          pd_eq_zero_of_eventuallyEq (hpd_ev i 1) 1
        rw [h00, h11, add_zero]
      simp [flatDiffIntegrand, h0, hdt0, hgr0, hlp0]
    have hint_Ek_Sk : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p =
        ∫ p in S_k, flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p :=
      MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        (measurableSet_Ioi.prod (B0579.measurableSet_cell c)).nullMeasurableSet
        hSk_sub_Ioi (Eventually.of_forall hEk_diff_zero_off)
    -- Explicit formulas for `E_seq k` on `{y | R₀ + 1 < y.2}` (hence on `S_k`)
    have hEk_top : ∀ s (y : ℝ × ℝ), R₀ + 1 < y.2 →
        E_seq k s y 0 = deriv (χ_seq k) y.2 * m_s s ∧ E_seq k s y 1 = 0 := by
      intro s y hy
      have hU : {z : ℝ × ℝ | R₀ + 1 < z.2} ∈ 𝓝 y :=
        (isOpen_lt continuous_const continuous_snd).mem_nhds hy
      have hev_ψ : ψ_seq k s =ᶠ[𝓝 y] fun z => χ_seq k z.2 * m_s s := by
        filter_upwards [hU] with z hz
        dsimp [ψ_seq, m_s]
        rw [hΘ_top s z hz.le]
      have hΦ0 : ∀ i, Φ s y i = 0 :=
        fun i => hsupp s y i (Or.inr (Or.inr (by rw [abs_of_pos (by linarith)]; linarith)))
      have hd_χ : Differentiable ℝ (χ_seq k) := hχ_sm.differentiable (by simp)
      have hpd0_ψ : B0579.pd 0 (ψ_seq k s) y = 0 := by
        have h1 : B0579.pd 0 (ψ_seq k s) y = B0579.pd 0 (fun z : ℝ × ℝ => χ_seq k z.2 * m_s s) y :=
          pd_eq_of_eventuallyEq hev_ψ 0
        rw [h1, DfcCutPdAux.pdSndMul 0 (χ_seq k) (fun _ => m_s s) hd_χ
          (differentiable_const (m_s s)) y, DfcCutPdAux.dir0_snd]
        unfold B0579.pd; simp
      have hpd1_ψ : B0579.pd 1 (ψ_seq k s) y = deriv (χ_seq k) y.2 * m_s s := by
        have h1 : B0579.pd 1 (ψ_seq k s) y = B0579.pd 1 (fun z : ℝ × ℝ => χ_seq k z.2 * m_s s) y :=
          pd_eq_of_eventuallyEq hev_ψ 1
        rw [h1, DfcCutPdAux.pdSndMul 1 (χ_seq k) (fun _ => m_s s) hd_χ
          (differentiable_const (m_s s)) y, DfcCutPdAux.dir1_snd]
        have hpd_c : B0579.pd 1 (fun _ : ℝ × ℝ => m_s s) y = 0 := by unfold B0579.pd; simp
        rw [hpd_c]; ring
      exact ⟨by simp [E_seq, V1.perpF_zero, hpd1_ψ, hΦ0 0],
        by simp [E_seq, V1.perpF_one, hpd0_ψ, hΦ0 1]⟩
    -- Pointwise norm bound on `S_k`
    have hpt_Sk : ∀ p ∈ S_k,
        ‖flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p‖ ≤
          C_err * ((vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k) := by
      intro p hp
      have hp_top : R₀ + 1 < p.2.2 := lt_of_lt_of_le hRk_gt hp.2.2.1
      let U_top : Set (ℝ × ℝ) := {y | R₀ + 1 < y.2}
      have hU_top_open : IsOpen U_top := isOpen_lt continuous_const continuous_snd
      have hU : U_top ∈ 𝓝 p.2 := hU_top_open.mem_nhds hp_top
      have hev0 : (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 p.2] fun y => deriv (χ_seq k) y.2 * m_s p.1 :=
        Filter.eventually_of_mem hU fun y hy => (hEk_top p.1 y hy).1
      have hev1 : (fun y => E_seq k p.1 y 1) =ᶠ[𝓝 p.2] 0 :=
        Filter.eventually_of_mem hU fun y hy => (hEk_top p.1 y hy).2
      have hd1_χ : Differentiable ℝ (deriv (χ_seq k)) :=
        ((contDiff_infty_iff_deriv.mp hχ_sm).2).differentiable (by simp)
      have hd2_χ : Differentiable ℝ (deriv (deriv (χ_seq k))) :=
        ((contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hχ_sm).2)).2).differentiable
          (by simp)
      have hdt0 : flatDt (E_seq k) p.1 p.2 0 = deriv (χ_seq k) p.2.2 * deriv m_s p.1 := by
        unfold flatDt
        have hfn : (fun s' => E_seq k s' p.2 0) = fun s' => deriv (χ_seq k) p.2.2 * m_s s' :=
          funext fun s' => (hEk_top s' p.2 hp_top).1
        rw [hfn, ((hm_diff p.1).hasDerivAt.const_mul _).deriv]
      have hdt1 : flatDt (E_seq k) p.1 p.2 1 = 0 := by
        unfold flatDt
        have hfn : (fun s' => E_seq k s' p.2 1) = 0 :=
          funext fun s' => (hEk_top s' p.2 hp_top).2
        rw [hfn]; simp
      have hpd0_0 : B0579.pd 0 (fun y => deriv (χ_seq k) y.2 * m_s p.1) = 0 := by
        funext z
        rw [DfcCutPdAux.pdSndMul 0 (deriv (χ_seq k)) (fun _ => m_s p.1) hd1_χ
          (differentiable_const (m_s p.1)) z, DfcCutPdAux.dir0_snd]
        unfold B0579.pd; simp
      have hpd1_0 : B0579.pd 1 (fun y => deriv (χ_seq k) y.2 * m_s p.1) =
          fun z => deriv (deriv (χ_seq k)) z.2 * m_s p.1 := by
        funext z
        rw [DfcCutPdAux.pdSndMul 1 (deriv (χ_seq k)) (fun _ => m_s p.1) hd1_χ
          (differentiable_const (m_s p.1)) z, DfcCutPdAux.dir1_snd]
        have hc0 : B0579.pd 1 (fun _ : ℝ × ℝ => m_s p.1) z = 0 := by unfold B0579.pd; simp
        rw [hc0]; ring
      have hgr00 : flatGrad (E_seq k) p.1 p.2 0 0 = 0 := by
        unfold flatGrad
        have h : B0579.pd 0 (fun y => E_seq k p.1 y 0) p.2 =
            B0579.pd 0 (fun y => deriv (χ_seq k) y.2 * m_s p.1) p.2 :=
          pd_eq_of_eventuallyEq hev0 0
        rw [h, hpd0_0]; rfl
      have hgr01 : flatGrad (E_seq k) p.1 p.2 0 1 =
          deriv (deriv (χ_seq k)) p.2.2 * m_s p.1 := by
        unfold flatGrad
        have h : B0579.pd 1 (fun y => E_seq k p.1 y 0) p.2 =
            B0579.pd 1 (fun y => deriv (χ_seq k) y.2 * m_s p.1) p.2 :=
          pd_eq_of_eventuallyEq hev0 1
        rw [h, hpd1_0]
      have hgr1 : ∀ j, flatGrad (E_seq k) p.1 p.2 1 j = 0 :=
        fun j => pd_eq_zero_of_eventuallyEq hev1 j
      have hlp0 : flatLap (E_seq k) p.1 p.2 0 =
          deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 := by
        unfold flatLap lapP
        have hev_pd0 : B0579.pd 0 (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 p.2] 0 := by
          filter_upwards [hU] with z hz
          have hz0 : (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 z]
              fun y => deriv (χ_seq k) y.2 * m_s p.1 :=
            Filter.eventually_of_mem (hU_top_open.mem_nhds hz) fun y hy => (hEk_top p.1 y hy).1
          have h : B0579.pd 0 (fun y => E_seq k p.1 y 0) z =
              B0579.pd 0 (fun y => deriv (χ_seq k) y.2 * m_s p.1) z :=
            pd_eq_of_eventuallyEq hz0 0
          rw [h, hpd0_0]
        have hev_pd1 : B0579.pd 1 (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 p.2]
            fun z => deriv (deriv (χ_seq k)) z.2 * m_s p.1 := by
          filter_upwards [hU] with z hz
          have hz0 : (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 z]
              fun y => deriv (χ_seq k) y.2 * m_s p.1 :=
            Filter.eventually_of_mem (hU_top_open.mem_nhds hz) fun y hy => (hEk_top p.1 y hy).1
          have h : B0579.pd 1 (fun y => E_seq k p.1 y 0) z =
              B0579.pd 1 (fun y => deriv (χ_seq k) y.2 * m_s p.1) z :=
            pd_eq_of_eventuallyEq hz0 1
          rw [h, hpd1_0]
        have h00 : B0579.pd 0 (B0579.pd 0 (fun y => E_seq k p.1 y 0)) p.2 = 0 :=
          pd_eq_zero_of_eventuallyEq hev_pd0 0
        have h11 : B0579.pd 1 (B0579.pd 1 (fun y => E_seq k p.1 y 0)) p.2 =
            deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 := by
          have h : B0579.pd 1 (B0579.pd 1 (fun y => E_seq k p.1 y 0)) p.2 =
              B0579.pd 1 (fun z : ℝ × ℝ => deriv (deriv (χ_seq k)) z.2 * m_s p.1) p.2 :=
            pd_eq_of_eventuallyEq hev_pd1 1
          rw [h, DfcCutPdAux.pdSndMul 1 (deriv (deriv (χ_seq k))) (fun _ => m_s p.1) hd2_χ
            (differentiable_const (m_s p.1)) p.2, DfcCutPdAux.dir1_snd]
          have hc0 : B0579.pd 1 (fun _ : ℝ × ℝ => m_s p.1) p.2 = 0 := by unfold B0579.pd; simp
          rw [hc0]; ring
        rw [h00, h11, zero_add]
      have hlp1 : flatLap (E_seq k) p.1 p.2 1 = 0 := by
        unfold flatLap lapP
        have hev_pd : ∀ j, B0579.pd j (fun y => E_seq k p.1 y 1) =ᶠ[𝓝 p.2] 0 := by
          intro j
          filter_upwards [hU] with z hz
          have hz1 : (fun y => E_seq k p.1 y 1) =ᶠ[𝓝 z] 0 :=
            Filter.eventually_of_mem (hU_top_open.mem_nhds hz) fun y hy => (hEk_top p.1 y hy).2
          exact pd_eq_zero_of_eventuallyEq hz1 j
        have h00 : B0579.pd 0 (B0579.pd 0 (fun y => E_seq k p.1 y 1)) p.2 = 0 :=
          pd_eq_zero_of_eventuallyEq (hev_pd 0) 0
        have h11 : B0579.pd 1 (B0579.pd 1 (fun y => E_seq k p.1 y 1)) p.2 = 0 :=
          pd_eq_zero_of_eventuallyEq (hev_pd 1) 1
        rw [h00, h11, add_zero]
      -- Estimate on `S_k`
      have hm_le : |m_s p.1| + |deriv m_s p.1| ≤ M_m := by
        have h := hM_m p.1 hp.1
        simp only [Pi.add_apply] at h
        rwa [Real.norm_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at h
      have hm0_le : |m_s p.1| ≤ M_m := (le_add_of_nonneg_right (abs_nonneg _)).trans hm_le
      have hdm_le : |deriv m_s p.1| ≤ M_m := (le_add_of_nonneg_left (abs_nonneg _)).trans hm_le
      set B : ℝ := vnorm2 (b_1 p) + vnorm2 (b_cand p)
      have hB0 : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hb1_le : ‖b_1 p 0‖ ≤ B :=
        (norm_le_vnorm2_local _ 0).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      have hbc0_le : ‖b_cand p 0‖ ≤ B :=
        (norm_le_vnorm2_local _ 0).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
      have hbc1_le : ‖b_cand p 1‖ ≤ B :=
        (norm_le_vnorm2_local _ 1).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
      have hp_s1 : s₁ ≤ p.1 := hp.1.1
      have hp_s0 : 0 < p.1 := lt_of_lt_of_le hs₁ hp_s1
      have hp_s2 : p.1 ≤ H := hp.1.2.trans hs₂H.le
      have hE0 := (hEk_top p.1 p.2 hp_top).1
      have hE1 := (hEk_top p.1 p.2 hp_top).2
      have hCb_tot : ∀ {C_i : ℝ}, C_i ≤ Cb1 + Cb2 + Cb3 → 0 ≤ C_i →
          (C_i / R_seq k) * M_m ≤ (Cb1 + Cb2 + Cb3) * M_m / R_seq k := by
        intro C_i hCi _
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hM_m0) hRk_pos.le
      have hCb1_nn : 0 ≤ Cb1 := (norm_nonneg _).trans (hCb1 0)
      have hCb2_nn : 0 ≤ Cb2 := (norm_nonneg _).trans (hCb2 0)
      have hCb3_nn : 0 ≤ Cb3 := (norm_nonneg _).trans (hCb3 0)
      unfold flatDiffIntegrand
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [hE0, hE1, hdt0, hdt1, hgr00, hgr01, hgr1, hlp0, hlp1,
        Complex.ofReal_zero, mul_zero, sub_zero, zero_add, add_zero, neg_zero]
      have ht1 : ‖-(b_1 p 0 * ((deriv (χ_seq k) p.2.2 * deriv m_s p.1 : ℝ) : ℂ))‖ ≤
          1 * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 : |deriv (χ_seq k) p.2.2| * |deriv m_s p.1| ≤
            (Cb1 + Cb2 + Cb3) * M_m / R_seq k :=
          (mul_le_mul (hdχ1_bd p.2.2) hdm_le (abs_nonneg _) (by positivity)).trans
            (hCb_tot (by linarith) hCb1_nn)
        calc ‖b_1 p 0‖ * (|deriv (χ_seq k) p.2.2| * |deriv m_s p.1|)
            ≤ B * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) :=
              mul_le_mul hb1_le h1 (by positivity) hB0
          _ = 1 * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have ht2 : ‖(μ / (p.1 : ℂ)) * b_1 p 0 * ((deriv (χ_seq k) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          (‖μ‖ / s₁) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hp_s0.le,
          Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have hdiv : ‖μ‖ / p.1 ≤ ‖μ‖ / s₁ :=
          div_le_div_of_nonneg_left (norm_nonneg _) hs₁ hp_s1
        have h1 : |deriv (χ_seq k) p.2.2| * |m_s p.1| ≤
            (Cb1 + Cb2 + Cb3) * M_m / R_seq k :=
          (mul_le_mul (hdχ1_bd p.2.2) hm0_le (abs_nonneg _) (by positivity)).trans
            (hCb_tot (by linarith) hCb1_nn)
        calc (‖μ‖ / p.1) * ‖b_1 p 0‖ * (|deriv (χ_seq k) p.2.2| * |m_s p.1|)
            ≤ (‖μ‖ / s₁) * B * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) :=
              mul_le_mul (mul_le_mul hdiv hb1_le (norm_nonneg _) (by positivity))
                h1 (by positivity) (by positivity)
          _ = (‖μ‖ / s₁) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have ht3 : ‖(ν : ℂ) * b_1 p 0 *
            ((deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          |ν| * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 : |deriv (deriv (deriv (χ_seq k))) p.2.2| * |m_s p.1| ≤
            (Cb1 + Cb2 + Cb3) * M_m / R_seq k :=
          (mul_le_mul (hdχ3_bd p.2.2) hm0_le (abs_nonneg _) (by positivity)).trans
            (hCb_tot (by linarith) hCb3_nn)
        calc |ν| * ‖b_1 p 0‖ * (|deriv (deriv (deriv (χ_seq k))) p.2.2| * |m_s p.1|)
            ≤ |ν| * B * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hb1_le (abs_nonneg _))
                h1 (by positivity) (by positivity)
          _ = |ν| * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have ht4 : ‖((trainVel tr p.1 p.2 0 : ℂ) * b_cand p 1 +
            b_cand p 0 * (trainVel tr p.1 p.2 1 : ℂ)) *
            ((deriv (deriv (χ_seq k)) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          (2 * M_v) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have hv0 := hMv p.1 hp_s2 p.2 0
        have hv1 := hMv p.1 hp_s2 p.2 1
        have hvb : ‖(trainVel tr p.1 p.2 0 : ℂ) * b_cand p 1 +
            b_cand p 0 * (trainVel tr p.1 p.2 1 : ℂ)‖ ≤ 2 * M_v * B := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          calc ‖(trainVel tr p.1 p.2 0 : ℂ)‖ * ‖b_cand p 1‖ +
                ‖b_cand p 0‖ * ‖(trainVel tr p.1 p.2 1 : ℂ)‖
              ≤ M_v * B + B * M_v :=
                add_le_add (mul_le_mul hv0 hbc1_le (norm_nonneg _) hMv0)
                  (mul_le_mul hbc0_le hv1 (norm_nonneg _) hB0)
            _ = 2 * M_v * B := by ring
        have h1 : |deriv (deriv (χ_seq k)) p.2.2| * |m_s p.1| ≤
            (Cb1 + Cb2 + Cb3) * M_m / R_seq k :=
          (mul_le_mul (hdχ2_bd p.2.2) hm0_le (abs_nonneg _) (by positivity)).trans
            (hCb_tot (by linarith) hCb2_nn)
        calc ‖(trainVel tr p.1 p.2 0 : ℂ) * b_cand p 1 +
                b_cand p 0 * (trainVel tr p.1 p.2 1 : ℂ)‖ *
              (|deriv (deriv (χ_seq k)) p.2.2| * |m_s p.1|)
            ≤ (2 * M_v * B) * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) :=
              mul_le_mul hvb h1 (by positivity) (by positivity)
          _ = (2 * M_v) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have htri : ‖-(b_1 p 0 * ((deriv (χ_seq k) p.2.2 * deriv m_s p.1 : ℝ) : ℂ)) +
          (μ / (p.1 : ℂ)) * b_1 p 0 * ((deriv (χ_seq k) p.2.2 * m_s p.1 : ℝ) : ℂ) -
          (ν : ℂ) * b_1 p 0 *
            ((deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 : ℝ) : ℂ) -
          ((trainVel tr p.1 p.2 0 : ℂ) * b_cand p 1 +
            b_cand p 0 * (trainVel tr p.1 p.2 1 : ℂ)) *
            ((deriv (deriv (χ_seq k)) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          1 * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) +
            (‖μ‖ / s₁) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) +
            |ν| * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) +
            (2 * M_v) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ht4)
        refine (norm_sub_le _ _).trans (add_le_add ?_ ht3)
        exact (norm_add_le _ _).trans (add_le_add ht1 ht2)
      refine htri.trans_eq ?_
      dsimp [C_err]; ring
    -- AM-GM bound on `∫_{S_k} B / R_seq k`
    set r_k : ℝ := Real.sqrt (R_seq k)
    have hrk_pos : 0 < r_k := Real.sqrt_pos.2 hRk_pos
    have hrk_sq : r_k ^ 2 = R_seq k := Real.sq_sqrt hRk_pos.le
    have hvol_Sk_eq : volume S_k =
        ENNReal.ofReal ((s₂ - s₁) * c * R_seq k) := by
      dsimp [S_k]
      rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_Icc, Real.volume_Ico, Real.volume_Icc]
      have h1 : c / 2 - -(c / 2) = c := by ring
      have h2 : 2 * R_seq k - R_seq k = R_seq k := by ring
      rw [h1, h2, ← ENNReal.ofReal_mul hc.le,
        ← ENNReal.ofReal_mul (sub_nonneg.2 hs₁₂.le)]
      ring_nf
    have hvol_Sk_lt : volume S_k < ⊤ := by rw [hvol_Sk_eq]; exact ENNReal.ofReal_lt_top
    have hint_B_Sk : IntegrableOn
        (fun p => (vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k) S_k := by
      have hsub_box : S_k ⊆
          Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R_seq k)) (2 * R_seq k)) := by
        refine prod_mono Subset.rfl (prod_mono Subset.rfl fun η hη => ?_)
        exact ⟨by linarith [hη.1], hη.2⟩
      exact ((integrableOn_sum_vnorm2_box hc hs₁₂.le (by positivity)
        hb1_meas hbcand_meas hloc.2.2).mono_set hsub_box).div_const _
    have hamgm : ∀ p : ℝ × (ℝ × ℝ),
        (vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k ≤
          1 / (2 * r_k ^ 3) + g_sq p / (2 * r_k) := by
      intro p
      dsimp only [g_sq]
      set y := vnorm2 (b_1 p) + vnorm2 (b_cand p)
      have hdiff : 1 / (2 * r_k ^ 3) + y ^ 2 / (2 * r_k) - y / R_seq k =
          (r_k * y - 1) ^ 2 / (2 * r_k ^ 3) := by
        rw [← hrk_sq]
        field_simp [hrk_pos.ne']
        ring
      linarith [div_nonneg (sq_nonneg (r_k * y - 1)) (by positivity : (0 : ℝ) ≤ 2 * r_k ^ 3)]
    have hc_Sk : IntegrableOn (fun _ : ℝ × (ℝ × ℝ) => (1 / (2 * r_k ^ 3) : ℝ)) S_k :=
      integrableOn_const hvol_Sk_lt.ne
    have hg_Sk : IntegrableOn (fun p => g_sq p / (2 * r_k)) S_k :=
      (hloc.2.2.mono_set hSk_sub_strip).div_const _
    have hint_amgm_rhs : IntegrableOn
        (fun p => 1 / (2 * r_k ^ 3) + g_sq p / (2 * r_k)) S_k :=
      hc_Sk.add hg_Sk
    have hint_B_le : ∫ p in S_k, (vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k ≤
        ((s₂ - s₁) * c + E_tot) / (2 * r_k) := by
      calc ∫ p in S_k, (vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k
          ≤ ∫ p in S_k, (1 / (2 * r_k ^ 3) + g_sq p / (2 * r_k)) :=
            setIntegral_mono_on hint_B_Sk hint_amgm_rhs hSk_meas fun p _ => hamgm p
        _ = (∫ _ in S_k, (1 / (2 * r_k ^ 3) : ℝ)) +
              (∫ p in S_k, g_sq p) / (2 * r_k) := by
            rw [integral_add hc_Sk hg_Sk]
            congr 1
            exact integral_div (2 * r_k) g_sq
        _ ≤ ((s₂ - s₁) * c * r_k ^ 2) * (1 / (2 * r_k ^ 3)) + E_tot / (2 * r_k) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, hvol_Sk_eq,
              ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (sub_nonneg.2 hs₁₂.le) hc.le) hRk_pos.le),
              ← hrk_sq]
            refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ (by positivity))
            exact setIntegral_mono_set hloc.2.2 (Eventually.of_forall fun _ => sq_nonneg _)
              hSk_sub_strip.eventuallyLE
        _ = ((s₂ - s₁) * c + E_tot) / (2 * r_k) := by
            field_simp [hrk_pos.ne']
    rw [hint_eq, norm_neg, hint_Ek_Sk]
    calc ‖∫ p in S_k, flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p‖
        ≤ ∫ p in S_k, ‖flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 (E_seq k) p‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ p in S_k, C_err * ((vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k) :=
          setIntegral_mono_on (hint_Ek.mono_set hSk_sub_Ioi).norm
            (hint_B_Sk.const_mul C_err) hSk_meas hpt_Sk
      _ = C_err * ∫ p in S_k, (vnorm2 (b_1 p) + vnorm2 (b_cand p)) / R_seq k :=
          integral_const_mul _ _
      _ ≤ C_err * (((s₂ - s₁) * c + E_tot) / (2 * r_k)) :=
          mul_le_mul_of_nonneg_left hint_B_le hCerr_nn
  -- Send `k → ∞`
  have hlim_zero : Tendsto
      (fun k : ℕ => C_err * (((s₂ - s₁) * c + E_tot) / (2 * Real.sqrt (R_seq k))))
      atTop (𝓝 0) := by
    have hR_top : Tendsto R_seq atTop atTop := by
      have h1 : Tendsto (fun k : ℕ => (k : ℝ) + (R₀ + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact h1.congr fun k => by dsimp [R_seq]; ring
    have hsqrt_top : Tendsto (fun k : ℕ => 2 * Real.sqrt (R_seq k)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop two_pos (Real.tendsto_sqrt_atTop.comp hR_top)
    have hinv_0 : Tendsto (fun k : ℕ => (2 * Real.sqrt (R_seq k))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsqrt_top
    simpa [div_eq_mul_inv, mul_zero] using
      (hinv_0.const_mul ((s₂ - s₁) * c + E_tot)).const_mul C_err
  have hnorm_zero :
      ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    exact ge_of_tendsto hlim_zero (Eventually.of_forall hbound_k)
  exact norm_eq_zero.1 hnorm_zero

/-! ## 6. Core causal uniqueness and a.e. slice vorticity identification -/

private theorem eLpNorm_restrict_Iio_eq_zero_of_lt_local {μm : Measure (ℝ × (ℝ × ℝ))}
    {H : ℝ} (hH : 0 < H) (F : ℝ × (ℝ × ℝ) → ℝ) (hF : ∀ p, 0 ≤ F p)
    (h : ∀ H' ∈ Ioo 0 H, eLpNorm F 2 (μm.restrict (Iio H' ×ˢ univ)) = 0) :
    eLpNorm F 2 (μm.restrict (Iio H ×ˢ univ)) = 0 := by
  have hcov : Iio H ×ˢ (univ : Set (ℝ × ℝ)) ⊆
      ⋃ n : ℕ, Iio (H - H / ((n : ℝ) + 2)) ×ˢ (univ : Set (ℝ × ℝ)) := by
    intro p hp
    have hpH : 0 < (H - p.1) / H := div_pos (sub_pos.2 hp.1) hH
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpH
    refine mem_iUnion.2 ⟨n, ?_, trivial⟩
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 1 / ((n : ℝ) + 2) < (H - p.1) / H :=
      (one_div_le_one_div_of_le (by positivity) (by linarith)).trans_lt hn
    have h2 : H / ((n : ℝ) + 2) < H - p.1 := by
      have := mul_lt_mul_of_pos_right h1 hH
      rwa [one_div_mul_eq_div, div_mul_cancel₀ _ hH.ne'] at this
    show p.1 < H - H / ((n : ℝ) + 2)
    linarith
  have hsq : eLpNorm F 2 (μm.restrict (Iio H ×ˢ univ)) ^ 2 ≤
      ∑' n : ℕ, eLpNorm F 2 (μm.restrict (Iio (H - H / ((n : ℝ) + 2)) ×ˢ univ)) ^ 2 := by
    simp only [eLpNorm_two_sq_eq_lintegral_nonneg _ F hF]
    exact (lintegral_mono_set hcov).trans (lintegral_iUnion_le _ _)
  have hsum : (∑' n : ℕ, eLpNorm F 2
      (μm.restrict (Iio (H - H / ((n : ℝ) + 2)) ×ˢ univ)) ^ 2) = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmem : H - H / ((n : ℝ) + 2) ∈ Ioo 0 H := by
      refine ⟨?_, ?_⟩
      · have hle : H / ((n : ℝ) + 2) ≤ H / 2 :=
          div_le_div_of_nonneg_left hH.le (by positivity) (by linarith)
        linarith
      · have hpos : 0 < H / ((n : ℝ) + 2) := by positivity
        linarith
    rw [h _ hmem, sq, zero_mul]
  rw [hsum] at hsq
  exact sq_eq_zero_iff.1 (le_antisymm hsq zero_le)

private theorem ae_slice_eq_of_tCalNormOn_sub_zero {c γ ν H : ℝ} (hc : 0 < c)
    {G₁ G₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG₁ : ∀ i j, Measurable fun p => G₁ p i j)
    (hG₂ : ∀ i j, Measurable fun p => G₂ p i j)
    (h0 : tCalNormOn c H (gainConj γ ν (fun p i j => G₁ p i j - G₂ p i j)) = 0) :
    ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H →
      ∀ᵐ x ∂(volume.restrict (B0579.cell c)), G₁ (s, x) = G₂ (s, x) := by
  set D : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => G₁ p i j - G₂ p i j
  have hDm : ∀ i j, Measurable fun p => D p i j := fun i j => (hG₁ i j).sub (hG₂ i j)
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (gainConj γ ν D p) :=
    measurable_tnorm2_gainConj γ ν hDm
  unfold tCalNormOn at h0
  have hae_age := (eLpNorm_eq_zero_iff hm.aestronglyMeasurable (by norm_num)).1 h0
  set g : ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    (Iio H ×ˢ (univ : Set (ℝ × ℝ))).indicator
      (fun p => ENNReal.ofReal (tnorm2 (gainConj γ ν D p)))
  have hg_meas : Measurable g :=
    hm.ennreal_ofReal.indicator (measurableSet_Iio.prod MeasurableSet.univ)
  have hlint_zero : ∫⁻ p, g p ∂(ageμ c (-1 / 2)) = 0 := by
    dsimp [g]
    rw [lintegral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
    refine lintegral_eq_zero_iff hm.ennreal_ofReal |>.2 ?_
    filter_upwards [hae_age] with p hp
    simp [hp]
  rw [lintegral_ageμ hc (-1 / 2) hg_meas] at hlint_zero
  have hmeas_prod : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * g p :=
    (ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const (-1 / 2 : ℝ)).const_mul c⁻¹)).mul
      hg_meas
  have hae_vol := (lintegral_eq_zero_iff hmeas_prod).1 hlint_zero
  rw [qCell_eq_B0579_cell] at hae_vol
  have hae_Ioo : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) H ×ˢ B0579.cell c)), G₁ p = G₂ p := by
    have hsub : Ioo (0 : ℝ) H ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
      prod_mono Ioo_subset_Ioi_self Subset.rfl
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae_vol,
      ae_restrict_mem (measurableSet_Ioo.prod (B0579.measurableSet_cell c))] with p hp hp_mem
    have hw_pos : 0 < c⁻¹ * p.1 ^ (-1 / 2 : ℝ) :=
      mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hp_mem.1.1 _)
    have hw_ne : ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hw_pos).ne'
    have hg0 : g p = 0 := (mul_eq_zero.1 hp).resolve_left hw_ne
    have hmem_Iio : p ∈ Iio H ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hp_mem.1.2, trivial⟩
    dsimp [g] at hg0
    rw [Set.indicator_of_mem hmem_Iio, ENNReal.ofReal_eq_zero] at hg0
    have htn0 : tnorm2 (gainConj γ ν D p) = 0 := le_antisymm hg0 (Real.sqrt_nonneg _)
    have hD0 : D p = 0 := eq_zero_of_tnorm2_gainConj htn0
    funext i j
    have hij := congrFun (congrFun hD0 i) j
    simpa [D, sub_eq_zero] using hij
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hae_Ioo
  exact (ae_restrict_iff' measurableSet_Ioo).1 (Measure.ae_ae_of_ae_prod hae_Ioo)

/-- **Core causal uniqueness and slice vorticity identification for nice forces**
(`PartIII-a:T19/2/3/2/3/1/1`, SP 3511-3515, 3541-3545): combines the free nice-force solution
`(b_cl, G_cl)` and source `f` with the Biot-Savart reconstructed Duhamel velocity/gradient
`(u_duh, G_duh)` to form an `IsCoreCausalSolution` on `(0, H')` for every `H' ∈ (0, coreEnd ν b)`,
and applies `coreCausalHomogeneousZero` to identify `corePerturbVort` with `ω_duh` on a.e. slice
`s ∈ (0, coreEnd ν b)`. -/
theorem nicePerturbVortEq
    (P : PlanarData) (hP : IsPlanarReference P)
    (K : Set ℂ) (hK : IsAdmissibleK K)
    (b : ℝ) (hb : 1 ≤ b)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1 / 2) (hνb : ν ≤ (2 * b)⁻¹)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (μ : ℂ) (A_m : ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b₀ b_sol b_cl u_duh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G₀ G_sol G_cl G_duh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (f ω_duh : ℝ → ℝ × ℝ → ℂ)
    (a_zero M_duh : ℝ)
    (hd : VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol)
    (ha0 : 0 < a_zero) (hMduh : 0 ≤ M_duh)
    (hb_cl : IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b_cl G_cl)
    (hbcl_zero : ∀ s ≤ a_zero, ∀ x i, b_cl (s, x) i = 0)
    (hG0_eq_cl : tCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b)
      (gainConj P.eigenvalue.re ν (fun p i j => G₀ p i j - G_cl p i j)) = 0)
    (hsrc_slice : ∀ t ∈ Ioo (0 : ℝ) (coreEnd ν b),
      (∀ i, MemLp (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      MemLp (f t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
        h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f t x * φ x =
          coreSrcFun (ν ^ (-2 : ℝ))
            (advStretch (trainVel tr t)
              (fun x => gainConj P.eigenvalue.re ν b_cl (t, x))
              (fun x => gainConj P.eigenvalue.re ν G_cl (t, x))) g)
    (huduh_meas : ∀ i, Measurable fun p => u_duh p i)
    (hGduh_meas : ∀ i j, Measurable fun p => G_duh p i j)
    (huduh_zero : ∀ s ≤ a_zero, ∀ x i, u_duh (s, x) i = 0)
    (hduh_bd : ∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
      ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
        ENNReal.ofReal (vnorm2 (u_duh (s, x)) ^ 2 + tnorm2 (G_duh (s, x)) ^ 2) ≤
          ENNReal.ofReal M_duh)
    (hduh_slice : ∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
      (∀ i, MemLp (fun x => u_duh (s, x) i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      MemLp (ω_duh s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      (∀ χ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (u_duh (s, x) 0 * (B0579.pd 0 χ x : ℂ) + u_duh (s, x) 1 * (B0579.pd 1 χ x : ℂ)) = 0) ∧
      (∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j
        (fun x => u_duh (s, x) i) (fun x => G_duh (s, x) i j)) ∧
      ((fun x => G_duh (s, x) 1 0 - G_duh (s, x) 0 1)
        =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω_duh s))
    (hduh_eq : ∀ (ψ : ℝ → ℝ × ℝ → ℝ) (s₁ s₂ R₁ : ℝ),
      0 < s₁ → s₁ < s₂ → s₂ < coreEnd ν b → 0 < R₁ →
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) →
      (∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x) →
      (∀ s x, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → ψ s x = 0) →
      ∫ ρ in Ioo (0 : ℝ) (coreEnd ν b),
        ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr
              (fun y => (gainG P.eigenvalue.re ν ρ : ℂ) * ω_duh ρ y)
              (fun y => (gainG P.eigenvalue.re ν ρ : ℂ) • u_duh (ρ, y)) ρ (ψ ρ) x) +
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            ((gainG P.eigenvalue.re ν ρ : ℂ) * ω_duh ρ x) *
              (-(μ / (ρ : ℂ)) * (ψ ρ x : ℂ) + ((deriv (fun ρ' => ψ ρ' x) ρ : ℝ) : ℂ))) +
          (gainG P.eigenvalue.re ν ρ : ℂ) *
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f ρ x * (ψ ρ x : ℂ)) = 0) :
    ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
      corePerturbVort P.eigenvalue.re ν G₀ G_sol s
        =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω_duh s := by
  obtain ⟨hbuc, hμ, _, _, _, _, _, hfree, hsol⟩ := hd
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  have hmc := B0579.measurableSet_cell c
  let γ : ℝ := P.eigenvalue.re
  have hγ : 0 ≤ γ := hP.eigenpair.re_pos.le
  let H : ℝ := coreEnd ν b
  have hH_gt1 : 1 < H := (coreEnd_bounds hb hν0 hν1 hνb).1
  have hH0 : 0 < H := zero_lt_one.trans hH_gt1
  let b_1 : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p => gainG γ ν p.1 • u_duh p
  let G_1 : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p => gainG γ ν p.1 • G_duh p
  let b_cand : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_cl p i + b_1 p i
  let G_cand : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => G_cl p i j + G_1 p i j
  have hg_meas := measurable_gainG_fst γ ν
  have hb1_meas : ∀ i, Measurable fun p => b_1 p i := fun i => hg_meas.smul (huduh_meas i)
  have hG1_meas : ∀ i j, Measurable fun p => G_1 p i j :=
    fun i j => hg_meas.smul (hGduh_meas i j)
  have hbcand_meas : ∀ i, Measurable fun p => b_cand p i :=
    fun i => (hb_cl.measurable i).add (hb1_meas i)
  have hGcand_meas : ∀ i j, Measurable fun p => G_cand p i j :=
    fun i j => (hb_cl.gradMeasurable i j).add (hG1_meas i j)
  -- For every `H' ∈ (0, H)`, `(b_cand, G_cand)` is an `IsCoreCausalSolution` on `(0, H')`
  have hCore_cand : ∀ H' ∈ Ioo (0 : ℝ) H,
      IsCoreCausalSolution c ν H' μ (trainVel tr) F b_cand G_cand := by
    intro H' hH'
    refine ⟨hbcand_meas, hGcand_meas, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s₁ s₂ hs₁ hs₁₂ hs₂H'
      exact (energyLoc_cand hγ hν0 hs₁ hs₁₂ (hs₂H'.trans hH'.2) hMduh
        hb_cl.measurable hb_cl.gradMeasurable (hb_cl.energyLoc s₁ s₂ hs₁ hs₁₂)
        huduh_meas hGduh_meas hduh_bd).2.1
    · refine ⟨a_zero, ha0, ?_⟩
      have hzero_ae : ∀ p ∈ Ioo (0 : ℝ) a_zero ×ˢ (univ : Set (ℝ × ℝ)),
          ENNReal.ofReal (vnorm2 (b_cand p) ^ 2) = 0 := by
        intro p hp
        have hp_zero : b_cand p = 0 := by
          funext i
          simp [b_cand, b_1, hbcl_zero p.1 hp.1.2.le p.2 i, huduh_zero p.1 hp.1.2.le p.2 i]
        simp [hp_zero, vnorm2]
      rw [setLIntegral_congr_fun (measurableSet_Ioo.prod MeasurableSet.univ) hzero_ae]
      simp
    · intro s hs ψ hψ
      have hsH : s ∈ Ioo (0 : ℝ) H := ⟨hs.1, hs.2.trans hH'.2⟩
      obtain ⟨_, _, hdiv_u, hwg_u, _⟩ := hduh_slice s hsH
      have hA0 := ((hb_cl.weakGrad s hs.1 0 0).1 ψ hψ).1
      have hA1 := ((hb_cl.weakGrad s hs.1 1 1).1 ψ hψ).1
      have hB0 := ((hwg_u 0 0).1 ψ hψ).1
      have hB1 := ((hwg_u 1 1).1 ψ hψ).1
      let fA : ℝ × ℝ → ℂ :=
        fun x => b_cl (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b_cl (s, x) 1 * (B0579.pd 1 ψ x : ℂ)
      let fB : ℝ × ℝ → ℂ :=
        fun x => u_duh (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + u_duh (s, x) 1 * (B0579.pd 1 ψ x : ℂ)
      have hfA : IntegrableOn fA (B0579.cell c) := (hA0.add hA1 : IntegrableOn fA (B0579.cell c))
      have hfB : IntegrableOn (fun x => (gainG γ ν s : ℂ) * fB x) (B0579.cell c) :=
        integrableOn_const_mul_local (gainG γ ν s : ℂ) (hB0.add hB1 : IntegrableOn fB (B0579.cell c))
      have heq : (fun x => b_cand (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
          b_cand (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) =
          fun x => fA x + (gainG γ ν s : ℂ) * fB x := by
        funext x; simp [fA, fB, b_cand, b_1, Complex.real_smul]; ring
      rw [heq, integral_add hfA hfB, hb_cl.divFree s hs.1 ψ hψ, integral_const_mul,
        hdiv_u ψ hψ, mul_zero, add_zero]
    · intro s hs i j
      have hsH : s ∈ Ioo (0 : ℝ) H := ⟨hs.1, hs.2.trans hH'.2⟩
      obtain ⟨_, _, _, hwg_u, _⟩ := hduh_slice s hsH
      have hb1_wg : HasWeakCellDerivC c j
          (fun x => b_1 (s, x) i) (fun x => G_1 (s, x) i j) := by
        have e1 : (fun x => b_1 (s, x) i) = fun x => (gainG γ ν s : ℂ) * u_duh (s, x) i := by
          funext x; simp [b_1, Complex.real_smul]
        have e2 : (fun x => G_1 (s, x) i j) = fun x => (gainG γ ν s : ℂ) * G_duh (s, x) i j := by
          funext x; simp [G_1, Complex.real_smul]
        rw [e1, e2]
        exact hasWeakCellDerivC_const_mul _ (hwg_u i j)
      have hcl_wg := hb_cl.weakGrad s hs.1 i j
      refine ⟨fun ψ hψ => ⟨IntegrableOn.congr_fun ((hcl_wg.1 ψ hψ).1.add (hb1_wg.1 ψ hψ).1)
          (fun x _ => by simp only [Pi.add_apply, b_cand]; ring) hmc,
        IntegrableOn.congr_fun ((hcl_wg.1 ψ hψ).2.add (hb1_wg.1 ψ hψ).2)
          (fun x _ => by simp only [Pi.add_apply, G_cand]; ring) hmc⟩,
        fun ψ hψ => ?_⟩
      have e1 : (fun x => b_cand (s, x) i * (B0579.pd j ψ x : ℂ)) =
          fun x => b_cl (s, x) i * (B0579.pd j ψ x : ℂ) + b_1 (s, x) i * (B0579.pd j ψ x : ℂ) := by
        funext x; dsimp [b_cand]; ring
      have e2 : (fun x => G_cand (s, x) i j * (ψ x : ℂ)) =
          fun x => G_cl (s, x) i j * (ψ x : ℂ) + G_1 (s, x) i j * (ψ x : ℂ) := by
        funext x; dsimp [G_cand]; ring
      rw [e1, e2, integral_add (hcl_wg.1 ψ hψ).1 (hb1_wg.1 ψ hψ).1,
        integral_add (hcl_wg.1 ψ hψ).2 (hb1_wg.1 ψ hψ).2, hcl_wg.2 ψ hψ, hb1_wg.2 ψ hψ]
      ring
    · intro Φ hΦ hΦ_H'
      obtain ⟨hint_d, _⟩ := flatDiff_compactTime_eq_zero hγ hν0 hH'.1 hH'.2 hMduh hbuc
        hb_cl.measurable hb_cl.gradMeasurable hb_cl.energyLoc hb_cl.divFree hb_cl.weakGrad
        hsrc_slice huduh_meas hGduh_meas hduh_bd hduh_slice hduh_eq hΦ hΦ_H'
      exact IntegrableOn.congr_fun ((hb_cl.integrable Φ hΦ).add hint_d)
        (fun p _ => by
          simp only [Pi.add_apply]
          exact (flatIntegrand_eq_add_diff ν μ (trainVel tr) F b_cl b_1 Φ p).symm)
        (measurableSet_Ioi.prod hmc)
    · intro Φ hΦ hΦ_H'
      have hfun : flatIntegrand ν μ (trainVel tr) F b_cand Φ =
          fun p => flatIntegrand ν μ (fun _ _ _ => 0) F b_cl Φ p +
            flatDiffIntegrand ν μ (trainVel tr) b_cand b_1 Φ p :=
        funext fun p => flatIntegrand_eq_add_diff ν μ (trainVel tr) F b_cl b_1 Φ p
      obtain ⟨hint_d, hzero_d⟩ := flatDiff_compactTime_eq_zero hγ hν0 hH'.1 hH'.2 hMduh hbuc
        hb_cl.measurable hb_cl.gradMeasurable hb_cl.energyLoc hb_cl.divFree hb_cl.weakGrad
        hsrc_slice huduh_meas hGduh_meas hduh_bd hduh_slice hduh_eq hΦ hΦ_H'
      rw [hfun, integral_add (hb_cl.integrable Φ hΦ) hint_d, hb_cl.weak Φ hΦ, hzero_d, add_zero]
  -- Apply `coreCausalHomogeneousZero` on each `(0, H')` and lift to `(0, H)`
  have htCal_zero_H : tCalNormOn c H
      (gainConj γ ν (fun p i j => G_sol p i j - G_cand p i j)) = 0 := by
    unfold tCalNormOn
    refine eLpNorm_restrict_Iio_eq_zero_of_lt_local hH0 _ (fun _ => Real.sqrt_nonneg _)
      fun H' hH' => ?_
    have hdiff_sol := coreCausalSolSub c ν H' μ (trainVel tr) F F b_sol b_cand G_sol G_cand
      (coreCausalSol_of_causalSol hsol) (hCore_cand H' hH')
    have hF0 : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => F p i j - F p i j) =
        fun _ _ _ => (0 : ℂ) := by funext p i j; exact sub_self _
    rw [hF0] at hdiff_sol
    exact (coreCausalHomogeneousZero P hP K hK ν H' hν0 hH'.1 tr hbuc μ hμ _ _ hdiff_sol).2
  -- Extract slice a.e. equalities and conclude
  have hae_sol := ae_slice_eq_of_tCalNormOn_sub_zero hc hsol.gradMeasurable hGcand_meas htCal_zero_H
  have hae_free := ae_slice_eq_of_tCalNormOn_sub_zero hc hfree.gradMeasurable hb_cl.gradMeasurable
    hG0_eq_cl
  filter_upwards [hae_sol, hae_free] with s hs_sol hs_free hsH
  obtain ⟨_, _, _, _, hcurl_s⟩ := hduh_slice s hsH
  filter_upwards [hs_sol hsH, hs_free hsH, hcurl_s] with x hx_sol hx_free hx_curl
  have hgc_ne : (gainG γ ν s : ℂ) ≠ 0 := V1.gain_ne γ ν s
  rw [← hx_curl]
  dsimp only [γ] at hgc_ne ⊢
  simp only [corePerturbVort, corePerturbGrad, gainConj, hx_sol, hx_free, G_cand, G_1, γ,
    Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv, add_sub_cancel_left,
    inv_mul_cancel_left₀ hgc_ne]

end UnforcedLeray.Short.IIIa.CoreDuhamelNiceAux

end
