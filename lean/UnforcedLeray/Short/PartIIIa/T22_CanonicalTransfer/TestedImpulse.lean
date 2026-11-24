import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse

/-!
# Part III-a, `PartIII-a:T22/3`: Partial moment and tested impulse (`eq:ct-partial-moment`, `eq:ct-tested-impulse`)

Source of record: `the November 2 reference manuscript` (SP), lines 3252-3274.

Proves `ctTestedImpulsePair : CTPartialMoment ∧ CTTestedImpulse` (and the projections
`ctPartialMoment`, `ctTestedImpulse`):
1. **Scale invariance of `quadQ` and intermediate kinetic bound**:
   Under `JscaleInv a` (`a > 0`), `quadQ d (JscaleInv a g) = quadQ (d * √a) g`, identifying
   `quadQ (d(θ)) Zh = quadQ c (w s_θ)` and `quadQ c (Jscale (ν r)⁻¹ h) = quadQ (d(r)) h`
   (`c = ν⁻²`). Applying `ctKineticImpulse` together with `CTE.isBiotSavart_unique` at intermediate
   clocks `θ' = clockTheta ν τ` (`τ ∈ [s_r, s_θ]`) yields
   `velNorm c (u τ) ≤ ENNReal.ofReal (C_kin * ν * r) * kinNorm (d(r)) h`.
2. **Exact tested identity for `q`-independent cylinder tests and scaling of `η² χ(η/(n+1))`**:
   Testing the linearised vorticity equation against `φ(q, η) = g(η)` and combining the weak curl
   and solenoidal identities of `IsBiotSavart` against `v_η g'` and `v_q g' + E_c g` cancels all
   first-derivative and vorticity-gradient terms, leaving
   `∫ flowIntegrand = ν ∫ ω g'' + ∫ (v_q u_η + v_η u_q) g''`.
   For `g_n(η) = η² χ(η/(n+1)) = R² ψ₀(R⁻¹ η)` (`R = n + 1`, `ψ₀(y) = y² χ(y)`), `g_n''` is
   uniformly bounded and eventually equal to `2` at each `η`.
3. **Horizontal-mean cancellation and limit `n → ∞`**:
   Using `TrainMeanEquations` (`\bar v_η = 0`, `\bar v_q = -∂_η S`), boundedness of `S = \bar ψ`
   from `IsTrain.stream_decay`, and `div u = 0` tested against `S(η) χ(η/(n+1))`, the mean vertical
   velocity pairing vanishes: `∫ \bar v_q u_η = 0`. Zero circulation (`zeroCirculationPreserved`)
   annihilates the viscous limit `2 ν ∫ w(τ) = 0`, and dominated convergence on `s_r..s_θ` yields
   `∫ η² w(s_θ) - ∫ η² f₀ = ∫_{s_r}^{s_θ} 2 ∫ (\tilde v_q u_η + \tilde v_η u_q) dτ`.
4. **Uniform all-age fluctuation bound and `CTPartialMoment`**:
   Combining `TrainL2Decay` before overlap and `TrainOverlap` (`j = 0`) after overlap gives
   `‖\tilde v(τ)‖₂ ≤ C_fl (1 + ν τ)⁻¹` for all `τ ≥ 0`. Integrating `(1 + ν τ)⁻¹` over `[s_r, s_θ]`
   yields `ν⁻¹ log(r/θ)`, cancelling the factor `ν` from `velNorm c (u τ)` to give `CTPartialMoment`.
5. **Weighted `θ^{p-1}` integration (`CTTestedImpulse`)**:
   Integrating `CTPartialMoment` against `θ^{p-1}` on `Ioo 0 r` (`p > 0`) via monotone convergence
   on `Ioo (r/(n+2)) r` and exact primitives of `θ^{p-1}` and `θ^{p-1} log(r/θ)` gives
   `CTTestedImpulse`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace TestedImpulseAux

/-! ## Section 1: Moment integrability, `JscaleInv` rescaling, and intermediate `velNorm` bound -/

private lemma jscale_eq_jscaleInv_inv {a : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) :
    Jscale a f = JscaleInv a⁻¹ f := by
  funext x
  unfold Jscale JscaleInv
  have hpow : a ^ (-2 : ℝ) = (a⁻¹) ^ 2 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, inv_pow]
  have h1 : x.1 / Real.sqrt a = Real.sqrt a⁻¹ * x.1 := by
    rw [Real.sqrt_inv, div_eq_inv_mul]
  have h2 : x.2 / Real.sqrt a = Real.sqrt a⁻¹ * x.2 := by
    rw [Real.sqrt_inv, div_eq_inv_mul]
  rw [hpow, h1, h2]

private lemma map_sqrt_smul_volume {a : ℝ} (ha : 0 < a) :
    Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume =
      ENNReal.ofReal a⁻¹ • (volume : Measure (ℝ × ℝ)) := by
  have hR : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hR
  simpa only [hfin, Real.sq_sqrt ha.le, abs_inv, abs_of_pos ha] using hmap

private lemma qmp_sqrt_smul {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ => Real.sqrt a • y) volume volume :=
  ⟨measurable_const_smul (Real.sqrt a), by
    rw [map_sqrt_smul_volume ha]
    exact Measure.smul_absolutelyContinuous⟩

private lemma lintegral_aemeasurable_comp_sqrt_smul {a : ℝ} (ha : 0 < a)
    {H : ℝ × ℝ → ℝ≥0∞} (hH : AEMeasurable H volume) :
    ∫⁻ y, H (Real.sqrt a • y) = ENNReal.ofReal a⁻¹ * ∫⁻ x, H x := by
  have hmap := map_sqrt_smul_volume ha
  have hH_map : AEMeasurable H (Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume) := by
    rw [hmap]
    exact hH.mono_ac Measure.smul_absolutelyContinuous
  rw [← lintegral_map' hH_map (measurable_const_smul (Real.sqrt a)).aemeasurable,
    hmap, lintegral_smul_measure, smul_eq_mul]

private lemma integrableOn_and_integral_comp_sqrt_smul {a d : ℝ} (ha : 0 < a)
    {g : ℝ × ℝ → ℂ} (hg : IntegrableOn g (B0579.cell (d * Real.sqrt a))) :
    IntegrableOn (fun y => g (Real.sqrt a • y)) (B0579.cell d) ∧
      (∫ y in B0579.cell d, g (Real.sqrt a • y)) =
        ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), g x := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set G : ℝ × ℝ → ℂ := (B0579.cell (d * Real.sqrt a)).indicator g
  have hG_int : Integrable G volume :=
    (integrable_indicator_iff (B0579.measurableSet_cell _)).2 hg
  have hmap := map_sqrt_smul_volume ha
  have hG_map : Integrable G (Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume) := by
    rw [hmap]
    exact hG_int.smul_measure ENNReal.ofReal_ne_top
  have hcomp_int : Integrable (fun y => G (Real.sqrt a • y)) volume :=
    (integrable_map_measure hG_map.1 (measurable_const_smul (Real.sqrt a)).aemeasurable).1 hG_map
  have hind_eq : (fun y : ℝ × ℝ => G (Real.sqrt a • y)) =
      (B0579.cell d).indicator (fun y => g (Real.sqrt a • y)) := by
    funext y
    by_cases hy : y ∈ B0579.cell d
    · have hy' : Real.sqrt a • y ∈ B0579.cell (d * Real.sqrt a) :=
        (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp [G, hy, hy']
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [G, hy, hy']
  have hint_d : IntegrableOn (fun y => g (Real.sqrt a • y)) (B0579.cell d) := by
    rw [← integrable_indicator_iff (B0579.measurableSet_cell d), ← hind_eq]
    exact hcomp_int
  refine ⟨hint_d, ?_⟩
  rw [← integral_indicator (B0579.measurableSet_cell d), ← hind_eq,
    ← integral_map (measurable_const_smul (Real.sqrt a)).aemeasurable hG_map.1,
    hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 ha.le),
    Complex.real_smul, integral_indicator (B0579.measurableSet_cell _)]

private def rescaleVel (a : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (y : ℝ × ℝ) (j : Fin 2) : ℂ :=
  ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u (Real.sqrt a • y) j

private lemma memLp_and_eLpNorm_rescaleVel {a d : ℝ} (ha : 0 < a)
    {u : ℝ × ℝ → Fin 2 → ℂ} (j : Fin 2)
    (hu : MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a)))) :
    MemLp (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) =
        ENNReal.ofReal a *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have ha32_nn : 0 ≤ a ^ (3 / 2 : ℝ) := Real.rpow_nonneg ha.le _
  have hind_aesm : AEStronglyMeasurable
      ((B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j)) volume :=
    (aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell _)).2 hu.1
  have hcomp_aesm : AEStronglyMeasurable
      (fun y : ℝ × ℝ => (B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j) (Real.sqrt a • y))
      volume :=
    hind_aesm.comp_quasiMeasurePreserving (qmp_sqrt_smul ha)
  have hind_eq : (fun y : ℝ × ℝ =>
        (B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j) (Real.sqrt a • y)) =
      (B0579.cell d).indicator (fun y => u (Real.sqrt a • y) j) := by
    funext y
    by_cases hy : y ∈ B0579.cell d
    · have hy' := (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp [hy, hy']
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [hy, hy']
  rw [hind_eq] at hcomp_aesm
  have hu_comp_aesm : AEStronglyMeasurable (fun y => u (Real.sqrt a • y) j)
      (volume.restrict (B0579.cell d)) :=
    (aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell d)).1 hcomp_aesm
  have hsc_aesm : AEStronglyMeasurable (fun y => rescaleVel a u y j)
      (volume.restrict (B0579.cell d)) :=
    hu_comp_aesm.const_mul _
  set H : ℝ × ℝ → ℝ≥0∞ :=
    (B0579.cell (d * Real.sqrt a)).indicator (fun x => ‖u x j‖ₑ ^ 2)
  have hH_aem : AEMeasurable H volume :=
    (aemeasurable_indicator_iff (B0579.measurableSet_cell _)).2 (hu.1.enorm.pow_const 2)
  have hpt : ∀ y : ℝ × ℝ,
      (B0579.cell d).indicator (fun y => ‖rescaleVel a u y j‖ₑ ^ 2) y =
        ENNReal.ofReal (a ^ 3) * H (Real.sqrt a • y) := by
    intro y
    have hpow_a : (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
      rw [← Real.rpow_natCast (a ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul ha.le]
      norm_num
    by_cases hy : y ∈ B0579.cell d
    · have hy' := (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp only [H, hy, hy', indicator_of_mem, rescaleVel, enorm_mul,
        T07.enorm_ofReal_cast ha32_nn, mul_pow, ← ENNReal.ofReal_pow ha32_nn 2, hpow_a]
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [H, hy, hy']
  have hlint : ∫⁻ y in B0579.cell d, ‖rescaleVel a u y j‖ₑ ^ 2 =
      ENNReal.ofReal (a ^ 2) * ∫⁻ x in B0579.cell (d * Real.sqrt a), ‖u x j‖ₑ ^ 2 := by
    rw [← lintegral_indicator (B0579.measurableSet_cell d), lintegral_congr hpt,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_aemeasurable_comp_sqrt_smul ha hH_aem, ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg ha.le 3),
      show a ^ 3 * a⁻¹ = a ^ 2 by field_simp,
      lintegral_indicator (B0579.measurableSet_cell _)]
  have hnorm_eq : eLpNorm (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) =
      ENNReal.ofReal a *
        eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
    rw [T07.eLpNorm_two_eq_lintegral, T07.eLpNorm_two_eq_lintegral, hlint,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg a) (by norm_num),
      ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    norm_num
  refine ⟨⟨hsc_aesm, ?_⟩, hnorm_eq⟩
  rw [hnorm_eq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2

private lemma velNorm_rescaleVel {a d : ℝ} (ha : 0 < a)
    {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a)))) :
    velNorm d (rescaleVel a u) = ENNReal.ofReal a * velNorm (d * Real.sqrt a) u := by
  unfold velNorm
  have hj : ∀ j : Fin 2,
      eLpNorm (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) ^ 2 =
        ENNReal.ofReal a ^ 2 *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) ^ 2 := by
    intro j
    rw [(memLp_and_eLpNorm_rescaleVel ha j (hu j)).2, mul_pow]
  simp_rw [hj, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]

private lemma isCylTest_inv_sqrt_smul {a d : ℝ} (ha : 0 < a) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) :
    B0579.IsCylTest (d * Real.sqrt a) (fun x => ψ ((Real.sqrt a)⁻¹ • x)) ∧
      ∀ (j : Fin 2) (y : ℝ × ℝ),
        B0579.pd j (fun x => ψ ((Real.sqrt a)⁻¹ • x)) (Real.sqrt a • y) =
          (Real.sqrt a)⁻¹ * B0579.pd j ψ y := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hR_ne : Real.sqrt a ≠ 0 := hR.ne'
  obtain ⟨R, hR_band⟩ := hψ.band
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := (Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have htest : B0579.IsCylTest (d * Real.sqrt a) (fun x => ψ ((Real.sqrt a)⁻¹ • x)) := by
    refine ⟨hψ.smooth.comp L.contDiff, ?_, ⟨|R| * Real.sqrt a, ?_⟩⟩
    · intro x
      have heq : (Real.sqrt a)⁻¹ • (x.1 + d * Real.sqrt a, x.2) =
          (((Real.sqrt a)⁻¹ • x).1 + d, ((Real.sqrt a)⁻¹ • x).2) := by
        ext
        · dsimp; field_simp [hR_ne]
        · rfl
      rw [heq]
      exact hψ.periodic _
    · intro x hx
      apply hR_band
      have h1 : |R| < |(Real.sqrt a)⁻¹ * x.2| := by
        rw [abs_mul, abs_inv, abs_of_pos hR]
        calc |R| = |R| * Real.sqrt a * (Real.sqrt a)⁻¹ := by field_simp [hR_ne]
          _ < |x.2| * (Real.sqrt a)⁻¹ := mul_lt_mul_of_pos_right hx (inv_pos.2 hR)
          _ = (Real.sqrt a)⁻¹ * |x.2| := mul_comm _ _
      exact (le_abs_self R).trans_lt h1
  refine ⟨htest, fun j y => ?_⟩
  have hLy : L (Real.sqrt a • y) = y := inv_smul_smul₀ hR_ne y
  have hfderiv : HasFDerivAt (fun x => ψ ((Real.sqrt a)⁻¹ • x))
      ((fderiv ℝ ψ y).comp L) (Real.sqrt a • y) := by
    have hψ_fderiv : HasFDerivAt ψ (fderiv ℝ ψ y) (L (Real.sqrt a • y)) := by
      rw [hLy]
      exact (hψ.smooth.differentiable (by simp) y).hasFDerivAt
    exact HasFDerivAt.comp (Real.sqrt a • y) hψ_fderiv L.hasFDerivAt
  unfold B0579.pd
  rw [hfderiv.fderiv]
  simp [L, smul_eq_mul]

private lemma hasZeroCirculation_jscaleInv {a d : ℝ} (ha : 0 < a) {f : ℝ × ℝ → ℂ}
    (hf : HasZeroCirculation (d * Real.sqrt a) f) :
    HasZeroCirculation d (JscaleInv a f) := by
  obtain ⟨hint_comp, hval_comp⟩ := integrableOn_and_integral_comp_sqrt_smul ha hf.1
  have heq : JscaleInv a f = fun y => ((a ^ 2 : ℝ) : ℂ) * f (Real.sqrt a • y) := by
    funext y; unfold JscaleInv; rw [T07.sqrt_smul_eq]
  rw [heq]
  refine ⟨hint_comp.const_mul _, ?_⟩
  rw [integral_const_mul, hval_comp, hf.2, mul_zero, mul_zero]

private lemma isBiotSavart_jscaleInv {a d : ℝ} (ha : 0 < a) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ}
    (hf : MemLp f 2 (volume.restrict (B0579.cell (d * Real.sqrt a))))
    (hu : IsBiotSavart (d * Real.sqrt a) f u) :
    IsBiotSavart d (JscaleInv a f) (rescaleVel a u) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hR_ne : Real.sqrt a ≠ 0 := hR.ne'
  have ha_pow : a ^ (3 / 2 : ℝ) * Real.sqrt a = a ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]
    norm_num
  refine ⟨fun j => (memLp_and_eLpNorm_rescaleVel ha j (hu.1 j)).1, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨hψ_sc, hpd_sc⟩ := isCylTest_inv_sqrt_smul ha hψ
    set g_div : ℝ × ℝ → ℂ := fun x =>
      u x 0 * (B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ) +
        u x 1 * (B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ)
    have hg_int : IntegrableOn g_div (B0579.cell (d * Real.sqrt a)) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 0) (hu.1 0)).add
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 1) (hu.1 1))
    obtain ⟨_, hcov⟩ := integrableOn_and_integral_comp_sqrt_smul ha hg_int
    have hpt : (fun y : ℝ × ℝ =>
          rescaleVel a u y 0 * (B0579.pd 0 ψ y : ℂ) +
            rescaleVel a u y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_div (Real.sqrt a • y) := by
      funext y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 0 y]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 1 y]; field_simp [hR_ne]
      dsimp only [rescaleVel, g_div]
      rw [hp0', hp1', ← ha_pow]
      push_cast; ring
    rw [hpt, integral_const_mul, hcov, hu.2.1 _ hψ_sc, mul_zero, mul_zero]
  · intro ψ hψ
    obtain ⟨hψ_sc, hpd_sc⟩ := isCylTest_inv_sqrt_smul ha hψ
    set g_lhs : ℝ × ℝ → ℂ := fun x => f x * (ψ ((Real.sqrt a)⁻¹ • x) : ℂ)
    set g_rhs : ℝ × ℝ → ℂ := fun x =>
      u x 0 * (B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ) -
        u x 1 * (B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ)
    have hgl_int : IntegrableOn g_lhs (B0579.cell (d * Real.sqrt a)) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hψ_sc hf
    have hgr_int : IntegrableOn g_rhs (B0579.cell (d * Real.sqrt a)) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 1) (hu.1 0)).sub
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 0) (hu.1 1))
    obtain ⟨_, hcov_l⟩ := integrableOn_and_integral_comp_sqrt_smul ha hgl_int
    obtain ⟨_, hcov_r⟩ := integrableOn_and_integral_comp_sqrt_smul ha hgr_int
    have hpt_l : (fun y : ℝ × ℝ => JscaleInv a f y * (ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_lhs (Real.sqrt a • y) := by
      funext y
      dsimp only [JscaleInv, g_lhs]
      rw [← T07.sqrt_smul_eq, inv_smul_smul₀ hR_ne]
      ring
    have hpt_r : (fun y : ℝ × ℝ =>
          rescaleVel a u y 0 * (B0579.pd 1 ψ y : ℂ) -
            rescaleVel a u y 1 * (B0579.pd 0 ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_rhs (Real.sqrt a • y) := by
      funext y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 0 y]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 1 y]; field_simp [hR_ne]
      dsimp only [rescaleVel, g_rhs]
      rw [hp0', hp1', ← ha_pow]
      push_cast; ring
    rw [hpt_l, hpt_r, integral_const_mul, integral_const_mul, hcov_l, hcov_r, hu.2.2 _ hψ_sc]

private lemma dOfTheta_mul_sqrt_inv {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    dOfTheta ν x * Real.sqrt ((ν * x)⁻¹) = ν ^ (-2 : ℝ) := by
  unfold dOfTheta
  have hc_pos : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
    ring
  rw [← Real.sqrt_mul (by positivity : 0 ≤ x / ν ^ 3)]
  have hprod : x / ν ^ 3 * (ν * x)⁻¹ = (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hc_sq]
    have hν_ne := hν.ne'
    have hx_ne := hx.ne'
    field_simp
  rw [hprod, Real.sqrt_sq hc_pos.le]

private lemma c_mul_sqrt_eq_dOfTheta {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    ν ^ (-2 : ℝ) * Real.sqrt (ν * r) = dOfTheta ν r := by
  have h := dOfTheta_mul_sqrt_inv hν hr
  rw [Real.sqrt_inv] at h
  calc ν ^ (-2 : ℝ) * Real.sqrt (ν * r)
      = dOfTheta ν r * (Real.sqrt (ν * r))⁻¹ * Real.sqrt (ν * r) := by rw [h]
    _ = dOfTheta ν r := inv_mul_cancel_right₀ (Real.sqrt_pos.2 (by positivity)).ne' _

private lemma velNorm_congr_ae {d : ℝ} {u v : ℝ × ℝ → Fin 2 → ℂ}
    (h : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), u x = v x) :
    velNorm d u = velNorm d v := by
  unfold velNorm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

private lemma kinNorm_eq_velNorm {d : ℝ} (hd : 0 < d) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hu : IsBiotSavart d f u) :
    kinNorm d f = velNorm d u := by
  apply le_antisymm (iInf₂_le u hu)
  refine le_iInf₂ fun v hv => le_of_eq ?_
  exact velNorm_congr_ae (CTE.isBiotSavart_unique d hd f u v hu hv)

private lemma velNorm_lt_top {d : ℝ} {f : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : IsBiotSavart d f u) : velNorm d u < ⊤ := by
  unfold velNorm
  have hsum : ∑ j : Fin 2, eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ^ 2 < ⊤ := by
    rw [Fin.sum_univ_two]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.pow_lt_top (hu.1 0).2, ENNReal.pow_lt_top (hu.1 1).2⟩
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hsum.ne

private lemma eLpNorm_le_velNorm {d : ℝ} (u : ℝ × ℝ → Fin 2 → ℂ) (j : Fin 2) :
    eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ≤ velNorm d u := by
  set a := eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d))
  have hle : a ^ 2 ≤ ∑ i : Fin 2,
      eLpNorm (fun x => u x i) 2 (volume.restrict (B0579.cell d)) ^ 2 :=
    Finset.single_le_sum
      (f := fun i => eLpNorm (fun x => u x i) 2 (volume.restrict (B0579.cell d)) ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc a = (a ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    _ ≤ velNorm d u := ENNReal.rpow_le_rpow hle (by norm_num)

private lemma integrableOn_etaSq_mul {d m : ℝ} (hm : 3 < m) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure d m)) :
    IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * g x) (B0579.cell d) := by
  have hg_aesm : AEStronglyMeasurable g (volume.restrict (B0579.cell d)) :=
    hg.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d m)
  have hmeas_eta : Continuous (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_snd.pow 2)
  refine ⟨hmeas_eta.aestronglyMeasurable.mul hg_aesm, ?_⟩
  show ∫⁻ x in B0579.cell d, ‖((x.2 ^ 2 : ℝ) : ℂ) * g x‖ₑ < ⊤
  simp_rw [enorm_mul]
  rw [CTE.QuadQBoundProof.lintegral_cell_eq d m]
  have hF : AEMeasurable (fun x : ℝ × ℝ => (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ *
      ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) (B0579.cellMeasure d m) := by
    apply Measurable.aemeasurable
    exact ((B0579.continuous_jb_rpow m).measurable.ennreal_ofReal.inv).mul
      hmeas_eta.measurable.enorm
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure d m)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hF hg.aestronglyMeasurable.enorm
  simp only [ENNReal.rpow_two] at hCS
  have hstep : ∫⁻ x, (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * (‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖g x‖ₑ)
      ∂(B0579.cellMeasure d m) ≤
      (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) *
        xNorm d m g := by
    refine (le_of_eq (lintegral_congr fun x => by simp only [Pi.mul_apply, mul_assoc])).trans
      (hCS.trans ?_)
    rw [← CTE.QuadQBoundProof.eLpNorm_two_eq]
    refine mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) zero_le
    rw [CTE.QuadQBoundProof.lintegral_cellMeasure_eq]
    exact (lintegral_mono fun x => CTE.QuadQBoundProof.density_mul_sq_le m hm x).trans
      (setLIntegral_le_lintegral _ _)
  refine hstep.trans_lt (ENNReal.mul_lt_top ?_ hg.2)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (CTE.QuadQBoundProof.integrable_moment m hm).lintegral_lt_top.ne

private lemma integrableOn_and_quadQ_jscaleInv {a d : ℝ} (ha : 0 < a) {g : ℝ × ℝ → ℂ}
    (hg : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * g x) (B0579.cell (d * Real.sqrt a))) :
    IntegrableOn (fun y => ((y.2 ^ 2 : ℝ) : ℂ) * JscaleInv a g y) (B0579.cell d) ∧
      quadQ d (JscaleInv a g) = quadQ (d * Real.sqrt a) g := by
  obtain ⟨hint_comp, hval_comp⟩ := integrableOn_and_integral_comp_sqrt_smul ha hg
  have hpt : (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * JscaleInv a g y) =
      fun y => ((a : ℝ) : ℂ) * ((((Real.sqrt a • y).2 ^ 2 : ℝ) : ℂ) * g (Real.sqrt a • y)) := by
    funext y
    unfold JscaleInv
    have hsmul : (Real.sqrt a • y).2 ^ 2 = a * y.2 ^ 2 := by
      simp only [Prod.smul_snd, smul_eq_mul, mul_pow, Real.sq_sqrt ha.le]
    rw [← T07.sqrt_smul_eq, hsmul]
    push_cast
    ring
  refine ⟨by rw [hpt]; exact hint_comp.const_mul _, ?_⟩
  unfold quadQ
  have hainv : ((a : ℝ) : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one]
  rw [hpt, integral_const_mul, hval_comp, ← mul_assoc ((a : ℝ) : ℂ) ((a⁻¹ : ℝ) : ℂ),
    hainv, one_mul]

private lemma quadQ_congr_ae {d : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell d)] g) :
    quadQ d f = quadQ d g := by
  unfold quadQ
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

private lemma integrable_inv_jb_plane {m : ℝ} (hm : 1 < m) :
    Integrable (fun x : ℝ × ℝ => (1 + ‖x‖ ^ 2) ^ (-m)) volume := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by simp
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume)
    (r := 2 * m) (by rw [hd]; linarith)
  convert h using 1
  funext x
  congr 1
  ring

private lemma cellL1_le_xNorm {m : ℝ} (hm : 1 < m) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (c : ℝ) (f : ℝ × ℝ → ℂ), MemLp f 2 (B0579.cellMeasure c m) →
      ∫ x in B0579.cell c, ‖f x‖ ≤ K₁ * (xNorm c m f).toReal := by
  set I₀ : ℝ≥0∞ := ∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-m))
  have hI₀_ne : I₀ ≠ ⊤ := (integrable_inv_jb_plane hm).lintegral_lt_top.ne
  refine ⟨I₀.toReal ^ (1 / 2 : ℝ), by positivity, fun c f hf => ?_⟩
  have hf_int : IntegrableOn f (B0579.cell c) := zcCellIntegrable c m hm f hf
  have hF : AEMeasurable (fun x : ℝ × ℝ => (ENNReal.ofReal (B0579.jb x ^ m))⁻¹)
      (B0579.cellMeasure c m) :=
    ((B0579.continuous_jb_rpow m).measurable.ennreal_ofReal.inv).aemeasurable
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure c m)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hF hf.aestronglyMeasurable.enorm
  simp only [ENNReal.rpow_two] at hCS
  have hwt_le : ∀ x : ℝ × ℝ,
      ENNReal.ofReal (B0579.jb x ^ m) * ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹) ^ 2 ≤
        ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-m)) := by
    intro x
    have hA : 0 < B0579.jb x ^ m := Real.rpow_pos_of_pos (B0579.jb_pos x) m
    have hq0 : 0 < 1 + ‖x‖ ^ 2 := by positivity
    have hn : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
      rw [Prod.norm_def]
      rcases max_choice ‖x.1‖ ‖x.2‖ with h | h <;> rw [h, Real.norm_eq_abs, sq_abs] <;>
        nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hqjb : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by unfold B0579.jb; linarith
    have hreal : B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹) ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ (-m) := by
      have he : B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹) ^ 2 = (B0579.jb x ^ m)⁻¹ := by
        field_simp [hA.ne']
      rw [he, Real.rpow_neg hq0.le]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hq0.le hqjb (by linarith))
    rw [← ENNReal.ofReal_inv_of_pos hA, ← ENNReal.ofReal_pow (inv_nonneg.2 hA.le),
      ← ENNReal.ofReal_mul hA.le]
    exact ENNReal.ofReal_le_ofReal hreal
  have hsq : ∫⁻ x, ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹) ^ 2 ∂(B0579.cellMeasure c m) ≤ I₀ := by
    rw [CTE.QuadQBoundProof.lintegral_cellMeasure_eq]
    exact (lintegral_mono hwt_le).trans (setLIntegral_le_lintegral _ _)
  have hlint : ∫⁻ x in B0579.cell c, ‖f x‖ₑ ≤ I₀ ^ (1 / 2 : ℝ) * xNorm c m f := by
    rw [CTE.QuadQBoundProof.lintegral_cell_eq c m]
    refine hCS.trans ?_
    rw [← CTE.QuadQBoundProof.eLpNorm_two_eq]
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hsq (by norm_num)) zero_le
  have heq : ENNReal.ofReal (∫ x in B0579.cell c, ‖f x‖) = ∫⁻ x in B0579.cell c, ‖f x‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hf_int.norm (Eventually.of_forall fun _ => norm_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm]
  have hx_ne : xNorm c m f ≠ ⊤ := hf.2.ne
  have hrhs : I₀ ^ (1 / 2 : ℝ) * xNorm c m f =
      ENNReal.ofReal (I₀.toReal ^ (1 / 2 : ℝ) * (xNorm c m f).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hI₀_ne, ENNReal.ofReal_toReal hx_ne]
  rw [← heq, hrhs] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlint

/-! ## Section 2: `q`-independent cylinder tests, exact Biot-Savart cancellation, and `ψ₀` scaling -/

private lemma contDiff_deriv_real {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (deriv g) := by
  unfold deriv
  exact ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

private lemma isCylTest_of_snd {c : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hband : ∃ R : ℝ, ∀ y : ℝ, R < |y| → g y = 0) :
    B0579.IsCylTest c (fun x => g x.2) ∧
      (∀ x : ℝ × ℝ, B0579.pd 0 (fun z => g z.2) x = 0) ∧
      (∀ x : ℝ × ℝ, B0579.pd 1 (fun z => g z.2) x = deriv g x.2) := by
  obtain ⟨R, hR⟩ := hband
  have htest : B0579.IsCylTest c (fun x => g x.2) :=
    ⟨hg.comp contDiff_snd, fun _ => rfl, ⟨R, fun x hx => hR x.2 hx⟩⟩
  have hfderiv : ∀ x : ℝ × ℝ,
      HasFDerivAt (fun z : ℝ × ℝ => g z.2)
        (deriv g x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x := fun x =>
    ((hg.differentiable (by simp) x.2).hasDerivAt).comp_hasFDerivAt x hasFDerivAt_snd
  refine ⟨htest, fun x => ?_, fun x => ?_⟩
  · unfold B0579.pd
    rw [(hfderiv x).fderiv]
    simp [B0579.dir]
  · unfold B0579.pd
    rw [(hfderiv x).fderiv]
    simp [B0579.dir]

private lemma lapP_of_snd {c : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hband : ∃ R : ℝ, ∀ y : ℝ, R < |y| → g y = 0) :
    B0579.IsCylTest c (fun x => deriv g x.2) ∧
      B0579.IsCylTest c (fun x => deriv (deriv g) x.2) ∧
      ∀ x : ℝ × ℝ, lapP (fun z => g z.2) x = deriv (deriv g) x.2 := by
  obtain ⟨_, hpd0, hpd1⟩ := isCylTest_of_snd (c := c) hg hband
  obtain ⟨R, hR⟩ := hband
  have hband1 : ∃ R₁ : ℝ, ∀ y : ℝ, R₁ < |y| → deriv g y = 0 := by
    refine ⟨R, fun y hy => ?_⟩
    have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hR z hz
    rw [hev.deriv_eq, deriv_const]
  have hband2 : ∃ R₂ : ℝ, ∀ y : ℝ, R₂ < |y| → deriv (deriv g) y = 0 := by
    obtain ⟨R₁, hR1⟩ := hband1
    refine ⟨R₁, fun y hy => ?_⟩
    have hev : deriv g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hR1 z hz
    rw [hev.deriv_eq, deriv_const]
  have hg1 := contDiff_deriv_real hg
  have hg2 := contDiff_deriv_real hg1
  obtain ⟨htest1, _, hpd11⟩ := isCylTest_of_snd (c := c) hg1 hband1
  obtain ⟨htest2, _, _⟩ := isCylTest_of_snd (c := c) hg2 hband2
  refine ⟨htest1, htest2, fun x => ?_⟩
  unfold lapP
  have heq0 : B0579.pd 0 (fun z => g z.2) = fun _ => (0 : ℝ) := funext hpd0
  have heq1 : B0579.pd 1 (fun z => g z.2) = fun z => deriv g z.2 := funext hpd1
  rw [heq0, heq1, hpd11 x]
  have h00 : B0579.pd 0 (fun _ : ℝ × ℝ => (0 : ℝ)) x = 0 := by
    unfold B0579.pd; simp
  rw [h00, zero_add]

private lemma flowIntegrand_snd_identity {ν c τ : ℝ} (hτ : 0 ≤ τ)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    {om : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hom : MemLp om 2 (volume.restrict (B0579.cell c)))
    (hu : IsBiotSavart c om u)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hband : ∃ R : ℝ, ∀ y : ℝ, R < |y| → g y = 0) :
    ∫ x in B0579.cell c, flowIntegrand tr om u τ (fun z => g z.2) x =
      (ν : ℂ) * (∫ x in B0579.cell c, om x * ((deriv (deriv g) x.2 : ℝ) : ℂ)) +
        ∫ x in B0579.cell c,
          ((tr.v τ x 0 : ℂ) * u x 1 + (tr.v τ x 1 : ℂ) * u x 0) *
            ((deriv (deriv g) x.2 : ℝ) : ℂ) := by
  set φ : ℝ × ℝ → ℝ := fun z => g z.2
  set dg : ℝ × ℝ → ℝ := fun z => deriv g z.2
  set ddg : ℝ × ℝ → ℝ := fun z => deriv (deriv g) z.2
  obtain ⟨hφ, hφ0, hφ1⟩ := isCylTest_of_snd (c := c) hg hband
  obtain ⟨hdg, hddg, hlap⟩ := lapP_of_snd (c := c) hg hband
  obtain ⟨_, hdg0, hdg1⟩ := isCylTest_of_snd (c := c) (contDiff_deriv_real hg) (by
    obtain ⟨R, hR⟩ := hband
    refine ⟨R, fun y hy => ?_⟩
    have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hR z hz
    rw [hev.deriv_eq, deriv_const])
  set ψ₁ : ℝ × ℝ → ℝ := fun x => V1.vC tr τ 1 x * dg x
  set ψ₂a : ℝ × ℝ → ℝ := fun x => V1.vC tr τ 0 x * dg x
  set ψ₂b : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0238.Ec tr τ x * φ x
  set ψ₂ : ℝ × ℝ → ℝ := fun x => ψ₂a x + ψ₂b x
  have hψ₁ : B0579.IsCylTest c ψ₁ :=
    V1.cylTest_mul_left (V1.vC_contDiff tr hτ 1) (V1.vC_periodic tr hτ 1) hdg
  have hψ₂a : B0579.IsCylTest c ψ₂a :=
    V1.cylTest_mul_left (V1.vC_contDiff tr hτ 0) (V1.vC_periodic tr hτ 0) hdg
  have hψ₂b : B0579.IsCylTest c ψ₂b :=
    V1.cylTest_mul_left (V1.Ec_contDiff tr hτ) (V1.Ec_periodic tr hτ) hφ
  have hψ₂ : B0579.IsCylTest c ψ₂ := V1.cylTest_add hψ₂a hψ₂b
  have hec_test : ∀ j : Fin 2,
      B0579.IsCylTest c (fun x => B0579.pd j (UnforcedLeray.B0238.Ec tr τ) x * φ x) := fun j =>
    V1.cylTest_mul_left (V1.pdE_contDiff tr hτ j)
      (fun x => by
        have hEc_diff : Differentiable ℝ (UnforcedLeray.B0238.Ec tr τ) :=
          (V1.Ec_contDiff tr hτ).differentiable (by simp)
        have hT : UnforcedLeray.B0238.Ec tr τ ∘ (fun y : ℝ × ℝ => (y.1 + c, y.2)) =
            UnforcedLeray.B0238.Ec tr τ := funext (V1.Ec_periodic tr hτ)
        have hS : HasFDerivAt (fun y : ℝ × ℝ => (y.1 + c, y.2))
            (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
          have : (fun y : ℝ × ℝ => (y.1 + c, y.2)) = fun y => y + ((c, 0) : ℝ × ℝ) := by
            funext y; ext <;> simp
          rw [this]; exact (hasFDerivAt_id x).add_const _
        have hc_fd := (hEc_diff (x.1 + c, x.2)).hasFDerivAt.comp x hS
        rw [hT] at hc_fd
        simp only [B0579.pd]; rw [hc_fd.fderiv]; rfl) hφ
  -- Split `flowIntegrand` into viscous, advection `om * ψ₁`, and `-∇Ec * φ`
  have hint_visc : IntegrableOn (fun x => (ν : ℂ) * (om x * (ddg x : ℂ))) (B0579.cell c) :=
    (CoreDuhamelRepSub.integrableOn_cylTest_mul hddg hom).const_mul _
  have hint_adv : IntegrableOn (fun x => om x * (ψ₁ x : ℂ)) (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul hψ₁ hom
  have hint_ec0 : IntegrableOn
      (fun x => u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul (hec_test 0) (hu.1 0)
  have hint_ec1 : IntegrableOn
      (fun x => u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul (hec_test 1) (hu.1 1)
  have hint_ec : IntegrableOn
      (fun x => u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
        u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      (B0579.cell c) := hint_ec0.add hint_ec1
  have hint_rest : IntegrableOn
      (fun x => om x * (ψ₁ x : ℂ) -
        (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
          u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ)))
      (B0579.cell c) := hint_adv.sub hint_ec
  have hflow_pt : ∀ x : ℝ × ℝ,
      flowIntegrand tr om u τ φ x =
        (ν : ℂ) * (om x * (ddg x : ℂ)) +
          (om x * (ψ₁ x : ℂ) -
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))) := by
    intro x
    unfold flowIntegrand
    rw [hlap x, hφ0 x, hφ1 x]
    dsimp only [ψ₁, V1.vC, dg, ddg, φ]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hflow_pt),
    integral_add hint_visc hint_rest,
    integral_const_mul, integral_sub hint_adv hint_ec,
    hu.2.2 ψ₁ hψ₁]
  congr 1
  -- Add `0 = ∫ (u_0 pd_0 ψ₂ + u_1 pd_1 ψ₂)` and cancel first derivatives pointwise
  have hint_curl : IntegrableOn
      (fun x => u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ))
      (B0579.cell c) :=
    (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₁.pd 1) (hu.1 0)).sub
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₁.pd 0) (hu.1 1))
  have hint_curl_sub : IntegrableOn
      (fun x => (u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ)) -
        (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
          u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ)))
      (B0579.cell c) := hint_curl.sub hint_ec
  have hint_div : IntegrableOn
      (fun x => u x 0 * (B0579.pd 0 ψ₂ x : ℂ) + u x 1 * (B0579.pd 1 ψ₂ x : ℂ))
      (B0579.cell c) :=
    (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₂.pd 0) (hu.1 0)).add
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ₂.pd 1) (hu.1 1))
  have hdiv_zero := hu.2.1 ψ₂ hψ₂
  calc (∫ x in B0579.cell c, (u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ))) -
          ∫ x in B0579.cell c,
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))
      = (∫ x in B0579.cell c,
          ((u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ)) -
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ)))) +
          ∫ x in B0579.cell c,
            (u x 0 * (B0579.pd 0 ψ₂ x : ℂ) + u x 1 * (B0579.pd 1 ψ₂ x : ℂ)) := by
        rw [hdiv_zero, add_zero, ← integral_sub hint_curl hint_ec]
    _ = ∫ x in B0579.cell c,
          (((u x 0 * (B0579.pd 1 ψ₁ x : ℂ) - u x 1 * (B0579.pd 0 ψ₁ x : ℂ)) -
            (u x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ) +
              u x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x : ℝ) : ℂ))) +
            (u x 0 * (B0579.pd 0 ψ₂ x : ℂ) + u x 1 * (B0579.pd 1 ψ₂ x : ℂ))) := by
        rw [← integral_add hint_curl_sub hint_div]
    _ = ∫ x in B0579.cell c,
          ((tr.v τ x 0 : ℂ) * u x 1 + (tr.v τ x 1 : ℂ) * u x 0) * (ddg x : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have hEc_diff : Differentiable ℝ (UnforcedLeray.B0238.Ec tr τ) :=
          (V1.Ec_contDiff tr hτ).differentiable (by simp)
        have hp10 : B0579.pd 0 ψ₁ x = B0579.pd 0 (V1.vC tr τ 1) x * dg x := by
          rw [V1.pd_mul' (V1.vC_diff tr hτ 1) hdg.differentiable 0 x, hdg0 x, mul_zero, add_zero]
        have hp11 : B0579.pd 1 ψ₁ x =
            B0579.pd 1 (V1.vC tr τ 1) x * dg x + V1.vC tr τ 1 x * ddg x := by
          rw [V1.pd_mul' (V1.vC_diff tr hτ 1) hdg.differentiable 1 x, hdg1 x]
        have hp20 : B0579.pd 0 ψ₂ x =
            B0579.pd 0 (V1.vC tr τ 0) x * dg x +
              B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x * φ x := by
          rw [V1.pd_add hψ₂a.differentiable.differentiableAt hψ₂b.differentiable.differentiableAt 0,
            V1.pd_mul' (V1.vC_diff tr hτ 0) hdg.differentiable 0 x,
            V1.pd_mul' hEc_diff hφ.differentiable 0 x, hdg0 x, hφ0 x]
          ring
        have hp21 : B0579.pd 1 ψ₂ x =
            B0579.pd 1 (V1.vC tr τ 0) x * dg x + V1.vC tr τ 0 x * ddg x +
              B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x * φ x +
              UnforcedLeray.B0238.Ec tr τ x * dg x := by
          rw [V1.pd_add hψ₂a.differentiable.differentiableAt hψ₂b.differentiable.differentiableAt 1,
            V1.pd_mul' (V1.vC_diff tr hτ 0) hdg.differentiable 1 x,
            V1.pd_mul' hEc_diff hφ.differentiable 1 x, hdg1 x, hφ1 x]
          ring
        have hdiv_v : B0579.pd 0 (V1.vC tr τ 0) x = -B0579.pd 1 (V1.vC tr τ 1) x := by
          linarith [V1.vC_div tr hτ x]
        have hcurl_v : UnforcedLeray.B0238.Ec tr τ x =
            B0579.pd 0 (V1.vC tr τ 1) x - B0579.pd 1 (V1.vC tr τ 0) x :=
          congrFun (V1.Ec_eq tr hτ) x
        dsimp only
        rw [hp10, hp11, hp20, hp21, hdiv_v, hcurl_v]
        dsimp only [V1.vC]
        push_cast
        ring

private def psi0 (y : ℝ) : ℝ := y ^ 2 * B0285.chi0 y

private def quadCut1 (n : ℕ) (y : ℝ) : ℝ := y ^ 2 * B0285.chi0 (((n : ℝ) + 1)⁻¹ * y)

private lemma quadCut1_Properties :
    (∀ n : ℕ, ContDiff ℝ ∞ (quadCut1 n)) ∧
    (∀ n : ℕ, ∃ R : ℝ, ∀ y : ℝ, R < |y| → quadCut1 n y = 0) ∧
    (∀ (n : ℕ) (x : ℝ × ℝ), quadCut1 n x.2 = x.2 ^ 2 * B0285.cutT n x) ∧
    (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ (n : ℕ) (y : ℝ), |deriv (deriv (quadCut1 n)) y| ≤ M₂) ∧
    (∀ y : ℝ, ∀ᶠ n : ℕ in atTop, deriv (deriv (quadCut1 n)) y = 2) := by
  have hpsi_smooth : ContDiff ℝ ∞ psi0 := (contDiff_id.pow 2).mul B0285.chi0.contDiff
  have hpsi_supp : ∀ y : ℝ, 2 < |y| → psi0 y = 0 := by
    intro y hy
    unfold psi0
    have h0 : B0285.chi0 y = 0 := by
      apply B0285.chi0.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      exact hy.le
    rw [h0, mul_zero]
  have hdpsi_smooth : ContDiff ℝ ∞ (deriv psi0) := contDiff_deriv_real hpsi_smooth
  have hddpsi_smooth : ContDiff ℝ ∞ (deriv (deriv psi0)) := contDiff_deriv_real hdpsi_smooth
  have hddpsi_supp : ∀ y : ℝ, 2 < |y| → deriv (deriv psi0) y = 0 := by
    intro y hy
    have hev1 : ∀ z : ℝ, 2 < |z| → deriv psi0 z = 0 := by
      intro z hz
      have hev : psi0 =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hz] with w hw
        exact hpsi_supp w hw
      rw [hev.deriv_eq, deriv_const]
    have hev2 : deriv psi0 =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hev1 z hz
    rw [hev2.deriv_eq, deriv_const]
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hddpsi_smooth.continuous.continuousOn
  set M₂ : ℝ := max M₀ 2
  have hM₂_nn : 0 ≤ M₂ := by positivity
  have hddpsi_bd : ∀ y : ℝ, |deriv (deriv psi0) y| ≤ M₂ := by
    intro y
    by_cases hy : y ∈ Icc (-2 : ℝ) 2
    · exact (Real.norm_eq_abs _ ▸ hM₀ y hy).trans (le_max_left _ _)
    · have hy' : 2 < |y| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hddpsi_supp y hy', abs_zero]
      exact hM₂_nn
  have hddpsi_ball : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv (deriv psi0) y = 2 := by
    have hval : ∀ z ∈ Ioo (-1 : ℝ) 1, psi0 z = z ^ 2 := by
      intro z hz
      unfold psi0
      have h1 : B0285.chi0 z = 1 := by
        apply B0285.chi0.one_of_mem_closedBall
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
        exact ⟨hz.1.le, hz.2.le⟩
      rw [h1, mul_one]
    have hdval : ∀ z ∈ Ioo (-1 : ℝ) 1, deriv psi0 z = 2 * z := by
      intro z hz
      have hev : psi0 =ᶠ[𝓝 z] fun w : ℝ => w ^ 2 := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
        exact hval w hw
      rw [hev.deriv_eq, ((hasDerivAt_pow 2 z).congr_deriv (by ring : (2 : ℕ) * z ^ (2 - 1) = 2 * z)).deriv]
    intro y hy
    have hev : deriv psi0 =ᶠ[𝓝 y] fun z : ℝ => 2 * z := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact hdval z hz
    rw [hev.deriv_eq, (((hasDerivAt_id' y).const_mul (2 : ℝ)).congr_deriv (mul_one 2)).deriv]
  have hscale_eq : ∀ (n : ℕ) (y : ℝ),
      quadCut1 n y = ((n : ℝ) + 1) ^ 2 * psi0 (((n : ℝ) + 1)⁻¹ * y) := by
    intro n y
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    unfold quadCut1 psi0
    field_simp [hpos.ne']
  have hdd_scale : ∀ (n : ℕ) (y : ℝ),
      deriv (deriv (quadCut1 n)) y = deriv (deriv psi0) (((n : ℝ) + 1)⁻¹ * y) := by
    intro n y
    set R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by positivity
    have hd1 : deriv (quadCut1 n) = fun z : ℝ => R * deriv psi0 (R⁻¹ * z) := by
      funext z
      have hfn : quadCut1 n = fun w : ℝ => R ^ 2 * psi0 (R⁻¹ * w) := funext (hscale_eq n)
      rw [hfn]
      have h_in : HasDerivAt (fun w : ℝ => R⁻¹ * w) R⁻¹ z :=
        ((hasDerivAt_id' z).const_mul R⁻¹).congr_deriv (mul_one R⁻¹)
      have h_out : HasDerivAt psi0 (deriv psi0 (R⁻¹ * z)) (R⁻¹ * z) :=
        (hpsi_smooth.differentiable (by simp) _).hasDerivAt
      have h_comp : HasDerivAt (fun w : ℝ => R ^ 2 * psi0 (R⁻¹ * w))
          (R * deriv psi0 (R⁻¹ * z)) z :=
        ((h_out.comp z h_in).const_mul (R ^ 2)).congr_deriv (by field_simp [hR.ne'])
      exact h_comp.deriv
    rw [hd1]
    have h_in : HasDerivAt (fun w : ℝ => R⁻¹ * w) R⁻¹ y :=
      ((hasDerivAt_id' y).const_mul R⁻¹).congr_deriv (mul_one R⁻¹)
    have h_out : HasDerivAt (deriv psi0) (deriv (deriv psi0) (R⁻¹ * y)) (R⁻¹ * y) :=
      (hdpsi_smooth.differentiable (by simp) _).hasDerivAt
    have h_comp : HasDerivAt (fun z : ℝ => R * deriv psi0 (R⁻¹ * z))
        (deriv (deriv psi0) (R⁻¹ * y)) y :=
      ((h_out.comp y h_in).const_mul R).congr_deriv (by field_simp [hR.ne'])
    exact h_comp.deriv
  refine ⟨?_, ?_, fun _ _ => rfl, ⟨M₂, hM₂_nn, fun n y => ?_⟩, fun y => ?_⟩
  · intro n
    have hfn : quadCut1 n = fun y : ℝ => ((n : ℝ) + 1) ^ 2 * psi0 (((n : ℝ) + 1)⁻¹ * y) :=
      funext (hscale_eq n)
    rw [hfn]
    exact contDiff_const.mul (hpsi_smooth.comp (contDiff_const.mul contDiff_id))
  · intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine ⟨2 * ((n : ℝ) + 1), fun y hy => ?_⟩
    rw [hscale_eq n y, hpsi_supp]
    · simp
    · rw [abs_mul, abs_inv, abs_of_pos hpos, lt_inv_mul_iff₀ hpos]
      linarith
  · rw [hdd_scale n y]
    exact hddpsi_bd _
  · refine (eventually_ge_atTop ⌈|y|⌉₊).mono fun n hn => ?_
    rw [hdd_scale n y]
    apply hddpsi_ball
    have hn' : |y| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have habs : |((n : ℝ) + 1)⁻¹ * y| < 1 := by
      rw [abs_mul, abs_inv, abs_of_pos hpos, inv_mul_lt_iff₀ hpos]
      linarith
    exact abs_lt.1 habs

/-! ## Section 3: Horizontal-mean cancellation, fluctuation `L²` decay, and age continuity -/

private lemma cellμ_eq_cellVol (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ
  rw [V1.cell_eq c]

private lemma hmean_vec_continuous {c : ℝ} {f : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec}
    (hf : Continuous f) : Continuous (fun η : ℝ => PartI.hmean c f η) := by
  have hF' : Continuous (fun p : ℝ × ℝ => f (p.2, p.1)) :=
    hf.comp (continuous_snd.prodMk continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun η q : ℝ => f (q, η)) hF' (isCompact_Icc : IsCompact (Icc (-c / 2) (c / 2)))
  have heq : (fun η : ℝ => PartI.hmean c f η) =
      fun η : ℝ => c⁻¹ • ∫ q in Icc (-c / 2) (c / 2), f (q, η) := by
    funext η
    unfold PartI.hmean
    rw [integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact h.const_smul c⁻¹

private lemma hfluct_vec_continuous {c : ℝ}
    {f : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec} (hf : Continuous f) :
    Continuous (PartI.hfluct c f) :=
  hf.sub ((hmean_vec_continuous hf).comp continuous_snd)

private lemma continuous_train_v_slice {ν c s : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hs : 0 ≤ s) : Continuous (tr.v s) :=
  (V1.vS_contDiff tr hs).continuous

private lemma hmean_vec_apply {c : ℝ} {f : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec}
    (hf : Continuous f) (η : ℝ) (k : Fin 2) :
    PartI.hmean c f η k = PartI.hmean c (fun z => f z k) η := by
  unfold PartI.hmean
  have hint : IntegrableOn (fun q : ℝ => f (q, η)) (Ioc (-c / 2) (c / 2)) volume :=
    ((hf.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hproj : (∫ q in Ioc (-c / 2) (c / 2), f (q, η) k) =
      (∫ q in Ioc (-c / 2) (c / 2), f (q, η)) k :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).integral_comp_comm hint
  rw [PiLp.smul_apply, smul_eq_mul, smul_eq_mul, ← hproj]

private lemma cellL2_hmean_le {c : ℝ} (hc : 0 < c)
    {f : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec}
    (hf : Continuous f) (hl2 : UnforcedLeray.Train.cellL2 c f < ⊤) :
    UnforcedLeray.Train.cellL2 c (fun z => PartI.hmean c f z.2) ≤
      UnforcedLeray.Train.cellL2 c f := by
  have hmem : MemLp (fun z => ‖f z‖) 2 (UnforcedLeray.Cyl.cellμ c) :=
    ⟨hf.norm.aestronglyMeasurable, by rw [eLpNorm_norm]; exact hl2⟩
  have hprod : Integrable (fun z : ℝ × ℝ => ‖f z‖ ^ 2)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← UnforcedLeray.Cyl.cellμ_eq_prod]
    exact hmem.integrable_sq
  set Φ : ℝ → ℝ := fun η => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2
  have hΦ_int : Integrable Φ volume := hprod.integral_prod_right.const_mul c⁻¹
  have : IsFiniteMeasure (volume.restrict (Ico (-c / 2) (c / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  have hΦ_prod : Integrable (fun z : ℝ × ℝ => Φ z.2) (UnforcedLeray.Cyl.cellμ c) := by
    rw [UnforcedLeray.Cyl.cellμ_eq_prod]
    exact hΦ_int.comp_snd _
  set g : ℝ × ℝ → UnforcedLeray.Train.Vec := fun z => PartI.hmean c f z.2
  have hg_cont : Continuous g := (hmean_vec_continuous hf).comp continuous_snd
  have hg_sq : ∀ z : ℝ × ℝ, ‖g z‖ ^ 2 ≤ Φ z.2 := by
    intro z
    have h1 : ‖PartI.hmean c f z.2‖ ≤ PartI.hmean c (fun w => ‖f w‖) z.2 := by
      unfold PartI.hmean
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.2 hc.le)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (PartI.meanEnergy_hmean_sq_le hc hf.norm (hf.norm.pow 2) (fun _ => le_rfl) z.2)
  have hg_mem : MemLp (fun z => ‖g z‖) 2 (UnforcedLeray.Cyl.cellμ c) := by
    refine (memLp_two_iff_integrable_sq hg_cont.norm.aestronglyMeasurable).2 ?_
    refine Integrable.mono' hΦ_prod (hg_cont.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hg_sq z
  have heq_g : UnforcedLeray.Train.cellL2 c g =
      ENNReal.ofReal (Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c))) := by
    unfold UnforcedLeray.Train.cellL2
    rw [← eLpNorm_norm]
    simpa [abs_of_nonneg (norm_nonneg _)] using
      PartI.jl2_abs_eLpNorm (UnforcedLeray.Cyl.cellμ c) (fun z => ‖g z‖) hg_mem
  have heq_f : UnforcedLeray.Train.cellL2 c f =
      ENNReal.ofReal (Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c))) := by
    unfold UnforcedLeray.Train.cellL2
    rw [← eLpNorm_norm]
    simpa [abs_of_nonneg (norm_nonneg _)] using
      PartI.jl2_abs_eLpNorm (UnforcedLeray.Cyl.cellμ c) (fun z => ‖f z‖) hmem
  have hint_Φ : ∫ z, Φ z.2 ∂(UnforcedLeray.Cyl.cellμ c) =
      ∫ z, ‖f z‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c) := by
    rw [UnforcedLeray.Cyl.cellμ_eq_prod,
      integral_prod (fun z : ℝ × ℝ => Φ z.2) (by rwa [← UnforcedLeray.Cyl.cellμ_eq_prod])]
    have hconst : ∫ _q in Ico (-c / 2) (c / 2), (∫ η : ℝ, Φ η) = c * ∫ η : ℝ, Φ η := by
      rw [setIntegral_const, Measure.real, Real.volume_Ico,
        show c / 2 - (-c / 2) = c by ring, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
    rw [hconst, integral_const_mul c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
      MeasureTheory.integral_prod_symm _ hprod]
  rw [heq_g, heq_f]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt
    ((integral_mono hg_mem.integrable_sq hΦ_prod hg_sq).trans_eq hint_Φ))

private lemma memLp_comp_le_cellL2 {c : ℝ}
    {f : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec}
    (hf : Continuous f) (hl2 : UnforcedLeray.Train.cellL2 c f < ⊤) (k : Fin 2) :
    MemLp (fun x => f x k) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => f x k) 2 (volume.restrict (B0579.cell c)) ≤
        UnforcedLeray.Train.cellL2 c f := by
  have hf_k : Continuous (fun x => f x k) := (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp hf
  have hle : eLpNorm (fun x => f x k) 2 (volume.restrict (B0579.cell c)) ≤
      UnforcedLeray.Train.cellL2 c f := by
    unfold UnforcedLeray.Train.cellL2
    rw [cellμ_eq_cellVol c]
    exact eLpNorm_mono fun x => PiLp.norm_apply_le (f x) k
  exact ⟨⟨hf_k.aestronglyMeasurable, hle.trans_lt hl2⟩, hle⟩

private lemma meanStream_smooth_and_bounded {ν c τ : ℝ} (hν : 0 < ν) (hc : 0 < c) (hτ : 0 < τ)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : PartI.IsBUCTrain tr) :
    ContDiff ℝ ∞ (fun η => PartI.meanStream tr τ η) ∧
      ∃ B_S : ℝ, 0 ≤ B_S ∧ ∀ η : ℝ, |PartI.meanStream tr τ η| ≤ B_S := by
  have hMean := T22Sub.trainMeanEquations_unconditional ν c hν hc tr htr
  have hS_smooth : ContDiff ℝ ∞ (fun η => PartI.meanStream tr τ η) := by
    have hg : ContDiff ℝ ∞ (fun η : ℝ => ((τ, η) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1 (hMean.1.comp hg.contDiffOn (fun _ _ => ⟨hτ, trivial⟩))
  have hdecay := tr.isTrain.stream_decay τ hτ.le
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 one_pos
  rw [Filter.tendsto_def] at hdecay
  obtain ⟨S_set, hS_atTop, hS_sub⟩ := Filter.mem_comap.1 (hdecay _ hball)
  obtain ⟨R₀, hR₀⟩ := Filter.mem_atTop_sets.1 hS_atTop
  set R₁ : ℝ := max R₀ 0
  have hR₁_nn : 0 ≤ R₁ := le_max_right _ _
  have htail : ∀ η : ℝ, R₁ ≤ |η| → |PartI.meanStream tr τ η| ≤ 1 := by
    intro η hη
    have hψ_le : ∀ q ∈ Ioc (-c / 2) (c / 2), ‖tr.ψ τ (q, η)‖ ≤ 1 := by
      intro q _
      have hz : (q, η) ∈ (fun z : ℝ × ℝ => |z.2|) ⁻¹' S_set :=
        hR₀ |η| ((le_max_left R₀ 0).trans hη)
      have hlt : dist (tr.ψ τ (q, η)) 0 < 1 := hS_sub hz
      rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs] at hlt
      exact hlt.le
    unfold PartI.meanStream PartI.hmean
    rw [smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc, ← Real.norm_eq_abs]
    have hint_le : ‖∫ q in Ioc (-c / 2) (c / 2), tr.ψ τ (q, η)‖ ≤ c := by
      have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (C := 1)
        measure_Ioc_lt_top hψ_le
      simpa only [one_mul, Measure.real, Real.volume_Ioc, show c / 2 - (-c / 2) = c by ring,
        ENNReal.toReal_ofReal hc.le] using hbd
    calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), tr.ψ τ (q, η)‖
        ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left hint_le (inv_nonneg.2 hc.le)
      _ = 1 := inv_mul_cancel₀ hc.ne'
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -R₁) (b := R₁)).exists_bound_of_continuousOn
    hS_smooth.continuous.continuousOn
  refine ⟨hS_smooth, max M₀ 1, by positivity, fun η => ?_⟩
  by_cases hη : η ∈ Icc (-R₁) R₁
  · exact (Real.norm_eq_abs _ ▸ hM₀ η hη).trans (le_max_left _ _)
  · have hη' : R₁ ≤ |η| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hη
      rcases hη with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact (htail η hη').trans (le_max_right _ _)

private lemma integral_train_mul_u_eq_fluct {ν c τ : ℝ} (hν : 0 < ν) (hc : 0 < c) (hτ : 0 < τ)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : PartI.IsBUCTrain tr)
    (hv_l2 : UnforcedLeray.Train.cellL2 c (tr.v τ) < ⊤)
    {om : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ} (hu : IsBiotSavart c om u) :
    ∫ x in B0579.cell c, ((tr.v τ x 0 : ℂ) * u x 1 + (tr.v τ x 1 : ℂ) * u x 0) =
      ∫ x in B0579.cell c,
        ((PartI.hfluct c (tr.v τ) x 0 : ℂ) * u x 1 +
          (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u x 0) := by
  set μ := volume.restrict (B0579.cell c)
  have hv_cont : Continuous (tr.v τ) := continuous_train_v_slice tr hτ.le
  have hmean_l2 : UnforcedLeray.Train.cellL2 c (fun z => PartI.hmean c (tr.v τ) z.2) < ⊤ :=
    (cellL2_hmean_le hc hv_cont hv_l2).trans_lt hv_l2
  have hfluct_cont : Continuous (PartI.hfluct c (tr.v τ)) := hfluct_vec_continuous hv_cont
  have hfluct_l2 : UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v τ)) < ⊤ := by
    unfold UnforcedLeray.Train.cellL2 PartI.hfluct
    exact (eLpNorm_sub_le hv_cont.aestronglyMeasurable
      ((hmean_vec_continuous hv_cont).comp continuous_snd).aestronglyMeasurable
      one_le_two).trans_lt (ENNReal.add_lt_top.2 ⟨hv_l2, hmean_l2⟩)
  have hMeanEq := (T22Sub.trainMeanEquations_unconditional ν c hν hc tr htr).2 τ hτ
  obtain ⟨hS_smooth, B_S, hB_S_nn, hB_S⟩ := meanStream_smooth_and_bounded hν hc hτ tr htr
  -- Show `∫ \bar v_0 * u_1 = 0` by testing `div u = 0` against `S(η) * cutT n`
  set vbar0 : ℝ × ℝ → ℝ := fun x => PartI.hmean c (tr.v τ) x.2 0
  have hvbar0_mem : MemLp vbar0 2 μ :=
    (memLp_comp_le_cellL2 ((hmean_vec_continuous hv_cont).comp continuous_snd) hmean_l2 0).1
  have hvbar0_u1_int : IntegrableOn (fun x => (vbar0 x : ℂ) * u x 1) (B0579.cell c) :=
    hvbar0_mem.ofReal.integrable_mul (hu.1 1)
  obtain ⟨M_chi, hM_chi_nn, hM_chi⟩ := zcChiDeriv
  set A₁ : ℝ := (eLpNorm (fun x => u x 1) 2 μ).toReal
  set B_seq : ℕ → ℝ := fun n => (B_S * M_chi) * Real.sqrt (4 * c * (1 / ((n : ℝ) + 1)))
  have hbound_n : ∀ n : ℕ,
      ‖∫ x in B0579.cell c, ((vbar0 x : ℂ) * u x 1) * (B0285.cutT n x : ℂ)‖ ≤ A₁ * B_seq n := by
    intro n
    obtain ⟨hcut, hcut0, hcut1⟩ := zcCutoffTest c n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set S2 : ℝ × ℝ → ℝ := fun x => PartI.meanStream tr τ x.2
    have hS2_smooth : ContDiff ℝ ∞ S2 := hS_smooth.comp contDiff_snd
    have hS2_diff : Differentiable ℝ S2 := hS2_smooth.differentiable (by simp)
    have hS2_pd0 : ∀ x : ℝ × ℝ, B0579.pd 0 S2 x = 0 := by
      intro x
      have hf : HasFDerivAt S2
          (deriv (fun e => PartI.meanStream tr τ e) x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
        ((hS_smooth.differentiable (by simp) x.2).hasDerivAt).comp_hasFDerivAt x hasFDerivAt_snd
      unfold B0579.pd; rw [hf.fderiv]; simp [B0579.dir]
    have hS2_pd1 : ∀ x : ℝ × ℝ, B0579.pd 1 S2 x = -vbar0 x := by
      intro x
      have hf : HasFDerivAt S2
          (deriv (fun e => PartI.meanStream tr τ e) x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
        ((hS_smooth.differentiable (by simp) x.2).hasDerivAt).comp_hasFDerivAt x hasFDerivAt_snd
      have h1 : B0579.pd 1 S2 x = deriv (fun e => PartI.meanStream tr τ e) x.2 := by
        unfold B0579.pd; rw [hf.fderiv]; simp [B0579.dir]
      rw [h1]
      dsimp only [vbar0]
      rw [hmean_vec_apply hv_cont x.2 0, (hMeanEq x.2).2.1, neg_neg]
    set χn : ℝ × ℝ → ℝ := fun x => S2 x * B0285.cutT n x
    have hχn : B0579.IsCylTest c χn := V1.cylTest_mul_left hS2_smooth (fun _ => rfl) hcut
    have hdiv_n := hu.2.1 χn hχn
    have hpd0_χ : ∀ x : ℝ × ℝ, B0579.pd 0 χn x = 0 := by
      intro x
      rw [V1.pd_mul' hS2_diff hcut.differentiable 0 x, hS2_pd0 x, hcut0 x, zero_mul, mul_zero,
        add_zero]
    have hpd1_χ : ∀ x : ℝ × ℝ,
        B0579.pd 1 χn x = -vbar0 x * B0285.cutT n x + S2 x * B0579.pd 1 (B0285.cutT n) x := by
      intro x
      rw [V1.pd_mul' hS2_diff hcut.differentiable 1 x, hS2_pd1 x]
    set rem_n : ℝ × ℝ → ℝ := fun x => S2 x * B0579.pd 1 (B0285.cutT n) x
    have hrem_test : B0579.IsCylTest c rem_n :=
      V1.cylTest_mul_left hS2_smooth (fun _ => rfl) (hcut.pd 1)
    have hrem_int : IntegrableOn (fun x => u x 1 * (rem_n x : ℂ)) (B0579.cell c) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hrem_test (hu.1 1)
    have hlhs_int : IntegrableOn
        (fun x => ((vbar0 x : ℂ) * u x 1) * (B0285.cutT n x : ℂ)) (B0579.cell c) := by
      have hc_bd : ∀ x : ℝ × ℝ, ‖(B0285.cutT n x : ℂ)‖ ≤ 1 := fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact B0285.abs_cutT_le n x
      exact hvbar0_u1_int.integrable.norm.mono'
        (hvbar0_u1_int.aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp hcut.continuous).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hc_bd x))
    have hid_n : ∫ x in B0579.cell c, ((vbar0 x : ℂ) * u x 1) * (B0285.cutT n x : ℂ) =
        ∫ x in B0579.cell c, u x 1 * (rem_n x : ℂ) := by
      have hrew : (fun x : ℝ × ℝ =>
            u x 0 * (B0579.pd 0 χn x : ℂ) + u x 1 * (B0579.pd 1 χn x : ℂ)) =
          fun x => u x 1 * (rem_n x : ℂ) -
            ((vbar0 x : ℂ) * u x 1) * (B0285.cutT n x : ℂ) := by
        funext x
        rw [hpd0_χ x, hpd1_χ x]
        dsimp only [rem_n]
        push_cast; ring
      rw [hrew, integral_sub hrem_int hlhs_int] at hdiv_n
      exact (sub_eq_zero.1 hdiv_n).symm
    have hrem_bd : ∀ x : ℝ × ℝ, |rem_n x| ≤ (B_S * M_chi) / ((n : ℝ) + 1) := by
      intro x
      dsimp only [rem_n, S2]
      rw [hcut1 x, abs_mul, abs_mul, abs_inv, abs_of_pos hpos, mul_div_assoc, div_eq_mul_inv]
      exact mul_le_mul (hB_S x.2)
        (mul_le_mul_of_nonneg_right (hM_chi _).1 (inv_nonneg.2 hpos.le)) (by positivity) hB_S_nn
    have hrem_van : ∀ x : ℝ × ℝ, 2 * ((n : ℝ) + 1) < |x.2| → rem_n x = 0 := by
      intro x hx
      have hy : 2 < |((n : ℝ) + 1)⁻¹ * x.2| := by
        rw [abs_mul, abs_inv, abs_of_pos hpos, lt_inv_mul_iff₀ hpos]; linarith
      dsimp only [rem_n]
      rw [hcut1 x, (hM_chi _).2 hy, zero_mul, mul_zero]
    have hL2 := zcBandL2 c hc rem_n ((B_S * M_chi) / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1))
      (div_nonneg (mul_nonneg hB_S_nn hM_chi_nn) hpos.le) (by positivity)
      hrem_test.continuous hrem_bd hrem_van
    have hmem_rem : MemLp rem_n 2 μ :=
      ⟨hrem_test.continuous.aestronglyMeasurable, hL2.trans_lt ENNReal.ofReal_lt_top⟩
    have hCS := zcCauchySchwarz μ (fun x => u x 1) rem_n (hu.1 1) hmem_rem
    have hgle : (eLpNorm rem_n 2 μ).toReal ≤ B_seq n := by
      have heq := zc_bound_eq (B_S * M_chi) c ((n : ℝ) + 1) hpos
      dsimp only [B_seq]
      rw [← heq]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL2
    rw [hid_n]
    exact hCS.trans (mul_le_mul_of_nonneg_left hgle ENNReal.toReal_nonneg)
  have hlim_zero : Tendsto (fun n : ℕ => A₁ * B_seq n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcont : Continuous fun ε : ℝ => A₁ * ((B_S * M_chi) * Real.sqrt (4 * c * ε)) := by
      fun_prop
    simpa [Function.comp_def, B_seq] using (hcont.tendsto 0).comp h1
  have hvbar0_zero : ∫ x in B0579.cell c, (vbar0 x : ℂ) * u x 1 = 0 :=
    tendsto_nhds_unique (zcCutoffLimit c _ hvbar0_u1_int) (squeeze_zero_norm hbound_n hlim_zero)
  -- Decompose `tr.v τ` into `hfluct + hmean`
  have hfl0_mem := (memLp_comp_le_cellL2 hfluct_cont hfluct_l2 0).1
  have hfl1_mem := (memLp_comp_le_cellL2 hfluct_cont hfluct_l2 1).1
  have hfl_int : IntegrableOn
      (fun x => (PartI.hfluct c (tr.v τ) x 0 : ℂ) * u x 1 +
        (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u x 0) (B0579.cell c) := by
    have i0 : IntegrableOn (fun x => (PartI.hfluct c (tr.v τ) x 0 : ℂ) * u x 1) (B0579.cell c) :=
      hfl0_mem.ofReal.integrable_mul (hu.1 1)
    have i1 : IntegrableOn (fun x => (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u x 0) (B0579.cell c) :=
      hfl1_mem.ofReal.integrable_mul (hu.1 0)
    exact i0.add i1
  have hpt_split : (fun x : ℝ × ℝ => (tr.v τ x 0 : ℂ) * u x 1 + (tr.v τ x 1 : ℂ) * u x 0) =
      fun x => ((PartI.hfluct c (tr.v τ) x 0 : ℂ) * u x 1 +
        (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u x 0) + (vbar0 x : ℂ) * u x 1 := by
    funext x
    have hv1_mean : PartI.hmean c (tr.v τ) x.2 1 = 0 := by
      rw [hmean_vec_apply hv_cont x.2 1, (hMeanEq x.2).2.2]
    have h0 : tr.v τ x 0 = PartI.hfluct c (tr.v τ) x 0 + vbar0 x := by
      unfold PartI.hfluct vbar0
      simp
    have h1 : tr.v τ x 1 = PartI.hfluct c (tr.v τ) x 1 := by
      unfold PartI.hfluct
      simp [hv1_mean]
    rw [h0, h1]
    push_cast; ring
  rw [hpt_split, integral_add hfl_int hvbar0_u1_int, hvbar0_zero, add_zero]

private lemma cellL2_hfluct_le_of_le {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    {f : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec}
    (hf : Continuous f) (hl2 : UnforcedLeray.Train.cellL2 c f ≤ ENNReal.ofReal B) :
    UnforcedLeray.Train.cellL2 c (PartI.hfluct c f) ≤ ENNReal.ofReal (2 * B) := by
  have hg_cont : Continuous (fun z : ℝ × ℝ => PartI.hmean c f z.2) :=
    (hmean_vec_continuous hf).comp continuous_snd
  have htri : UnforcedLeray.Train.cellL2 c (PartI.hfluct c f) ≤
      UnforcedLeray.Train.cellL2 c f +
        UnforcedLeray.Train.cellL2 c (fun z => PartI.hmean c f z.2) := by
    unfold UnforcedLeray.Train.cellL2 PartI.hfluct
    exact eLpNorm_sub_le hf.aestronglyMeasurable hg_cont.aestronglyMeasurable one_le_two
  have hmean_le : UnforcedLeray.Train.cellL2 c (fun z => PartI.hmean c f z.2) ≤
      ENNReal.ofReal B :=
    (cellL2_hmean_le hc hf (hl2.trans_lt ENNReal.ofReal_lt_top)).trans hl2
  calc UnforcedLeray.Train.cellL2 c (PartI.hfluct c f)
      ≤ ENNReal.ofReal B + ENNReal.ofReal B := htri.trans (add_le_add hl2 hmean_le)
    _ = ENNReal.ofReal (2 * B) := by rw [← ENNReal.ofReal_add hB hB, two_mul]

private lemma cellL2_hfluct_postOverlap_le {ν c C_ov lam s : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hs0 : 0 ≤ s) (hs : B0146.overlapAge ν c ≤ s)
    (hOv0 : ∀ T : ℝ, 0 ≤ T →
      UnforcedLeray.Train.cellL2 1
          (UnforcedLeray.Train.jet 0 (PartI.hfluct 1 (PartI.overlapField ν c tr.v T))) ≤
        ENNReal.ofReal (C_ov * Real.exp (-(lam * T)))) :
    UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v s)) ≤
      ENNReal.ofReal (C_ov * (c ^ 2)⁻¹ *
        Real.exp (-((lam * ν / c ^ 2) * (s - B0146.overlapAge ν c)))) := by
  set s_c := B0146.overlapAge ν c
  set T := ν * (s - s_c) / c ^ 2
  have hT : 0 ≤ T := div_nonneg (mul_nonneg hν.le (sub_nonneg.2 hs)) (sq_nonneg c)
  have hs_eq : s_c + c ^ 2 * T / ν = s := by
    have hν0 : ν ≠ 0 := hν.ne'
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
    dsimp [T]; field_simp; ring
  have hU_eq : PartI.overlapField ν c tr.v T = PartI.scaleField c (tr.v s) := by
    funext y; simp [PartI.overlapField, PartI.scaleField, s_c, hs_eq]
  have hfl_scale : PartI.hfluct 1 (PartI.scaleField c (tr.v s)) =
      PartI.scaleField c (PartI.hfluct c (tr.v s)) := by
    funext y
    unfold PartI.hfluct PartI.scaleField
    have h1 : PartI.hmean 1 (fun w : ℝ × ℝ => c ^ 3 • tr.v s (c • w)) y.2 =
        c ^ 3 • PartI.hmean c (tr.v s) (c * y.2) := by
      have hsm : PartI.hmean 1 (fun w : ℝ × ℝ => c ^ 3 • tr.v s (c • w)) y.2 =
          c ^ 3 • PartI.hmean 1 (fun w : ℝ × ℝ => tr.v s (c • w)) y.2 := by
        unfold PartI.hmean
        rw [integral_smul, smul_comm]
      rw [hsm, PartI.hmean_scale_unit hc (tr.v s) y.2]
    rw [h1]
    simp [Prod.smul_snd, smul_eq_mul, smul_sub]
  have hg_cont : Continuous (PartI.hfluct c (tr.v s)) :=
    hfluct_vec_continuous (continuous_train_v_slice tr hs0)
  have hsc_norm : UnforcedLeray.Train.cellL2 1 (PartI.scaleField c (PartI.hfluct c (tr.v s))) =
      ENNReal.ofReal (c ^ 2) * UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v s)) := by
    have hfun : PartI.scaleField c (PartI.hfluct c (tr.v s)) =
        (c ^ 3 : ℝ) • fun y : ℝ × ℝ => PartI.hfluct c (tr.v s) (c • y) := rfl
    unfold UnforcedLeray.Train.cellL2
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    change ENNReal.ofReal (c ^ 3) *
      UnforcedLeray.Train.cellL2 1 (fun y : ℝ × ℝ => PartI.hfluct c (tr.v s) (c • y)) = _
    rw [PartI.cellL2_one_comp_smul hc hg_cont]
    unfold UnforcedLeray.Train.cellL2
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
  have hjet0 : ∀ g : ℝ × ℝ → UnforcedLeray.Train.Vec,
      UnforcedLeray.Train.cellL2 1 (UnforcedLeray.Train.jet 0 g) =
        UnforcedLeray.Train.cellL2 1 g := by
    intro g
    unfold UnforcedLeray.Train.cellL2
    rw [← eLpNorm_norm (UnforcedLeray.Train.jet 0 g), ← eLpNorm_norm g]
    have hnorm : (fun y : ℝ × ℝ => ‖UnforcedLeray.Train.jet 0 g y‖) = fun y => ‖g y‖ :=
      funext fun _ => norm_iteratedFDeriv_zero
    rw [hnorm]
  have h1 := hOv0 T hT
  rw [hjet0, hU_eq, hfl_scale, hsc_norm] at h1
  have hc2_pos : 0 < c ^ 2 := sq_pos_of_pos hc
  have hmul := mul_le_mul_of_nonneg_left h1 (zero_le : 0 ≤ ENNReal.ofReal (c ^ 2)⁻¹)
  have hlhs : ENNReal.ofReal (c ^ 2)⁻¹ *
      (ENNReal.ofReal (c ^ 2) * UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v s))) =
      UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v s)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc2_pos.le),
      inv_mul_cancel₀ hc2_pos.ne', ENNReal.ofReal_one, one_mul]
  rw [hlhs, ← ENNReal.ofReal_mul (inv_nonneg.2 hc2_pos.le)] at hmul
  refine hmul.trans (le_of_eq ?_)
  congr 1; dsimp [T]; ring_nf

private lemma train_uniform_all_age_bounds :
    ∃ (C_L2 C_fl ν_fl : ℝ), 0 < C_L2 ∧ 0 < C_fl ∧ 0 < ν_fl ∧
      ∀ ν ∈ Ioc 0 ν_fl, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        PartI.IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
          UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤ ENNReal.ofReal C_L2 ∧
          UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ))
              (PartI.hfluct (ν ^ (-2 : ℝ)) (tr.v s)) ≤
            ENNReal.ofReal (C_fl * (1 + ν * s)⁻¹) := by
  obtain ⟨C_L2, ν_L2, hC_L2, hν_L2, hL2⟩ := T22Sub.trainL2Decay_unconditional 2 (by norm_num)
  obtain ⟨C_ov, lam, ν_ov, hC_ov, hlam, hν_ov, hOv⟩ :=
    T22Sub.trainOverlap_unconditional 2 (by norm_num) 0
  set C_fl : ℝ := max (2 * C_L2) (C_ov * Real.exp lam / lam)
  set ν_fl : ℝ := min ν_L2 (min ν_ov (1 / 2))
  refine ⟨C_L2, C_fl, ν_fl, hC_L2, lt_of_lt_of_le (by positivity) (le_max_left _ _),
    lt_min hν_L2 (lt_min hν_ov (by norm_num)), fun ν hν tr htr s hs => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν1 : ν ≤ ν_L2 := hν.2.trans (min_le_left _ _)
  have hν2 : ν ≤ ν_ov := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  have hc_gt1 : 1 < c := by
    have h4 : (4 : ℝ) ≤ c := by
      have hle : ((1 / 2 : ℝ) ^ (-2 : ℝ)) ≤ c :=
        Real.rpow_le_rpow_of_nonpos hν_pos hν_half (by norm_num)
      have heval : ((1 / 2 : ℝ) ^ (-2 : ℝ)) = 4 := by norm_num
      linarith
    linarith
  have hsc_pos : 0 < B0146.overlapAge ν c := by
    unfold B0146.overlapAge
    have : 1 < c ^ 2 := by nlinarith
    exact div_pos (by linarith) hν_pos
  have hL2_s := hL2 ν hν_pos hν1 tr htr s hs
  have ha_ge1 : 1 ≤ 1 + ν * s := by nlinarith
  constructor
  · by_cases hle : s ≤ B0146.overlapAge ν c
    · refine (hL2_s.1 hle).trans (ENNReal.ofReal_le_ofReal ?_)
      have hw : UnforcedLeray.Train.width ν s = 1 + ν * s := rfl
      rw [hw]
      have hinv : (1 + ν * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha_ge1
      nlinarith
    · push Not at hle
      refine (hL2_s.2 hle.le).trans (ENNReal.ofReal_le_ofReal ?_)
      change C_L2 * c ^ (-2 : ℝ) * (s / B0146.overlapAge ν c) ^ (-(3 / 4 : ℝ)) ≤ C_L2
      have hc_inv : c ^ (-2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hc_gt1.le (by norm_num)
      have hrat : 1 ≤ s / B0146.overlapAge ν c := (one_le_div hsc_pos).2 hle.le
      have hrpow : (s / B0146.overlapAge ν c) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hrat (by norm_num)
      have hprod : c ^ (-2 : ℝ) * (s / B0146.overlapAge ν c) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
        mul_le_one₀ hc_inv (by positivity) hrpow
      nlinarith
  · by_cases hle : s ≤ B0146.overlapAge ν c
    · have hpre := hL2_s.1 hle
      have hw : UnforcedLeray.Train.width ν s = 1 + ν * s := rfl
      rw [hw] at hpre
      refine (cellL2_hfluct_le_of_le hc_pos (by positivity)
        (continuous_train_v_slice tr hs) hpre).trans (ENNReal.ofReal_le_ofReal ?_)
      have hmax : 2 * C_L2 ≤ C_fl := le_max_left _ _
      calc 2 * (C_L2 * (1 + ν * s)⁻¹) = (2 * C_L2) * (1 + ν * s)⁻¹ := by ring
        _ ≤ C_fl * (1 + ν * s)⁻¹ := mul_le_mul_of_nonneg_right hmax (by positivity)
    · push Not at hle
      have hOv0 : ∀ T : ℝ, 0 ≤ T →
          UnforcedLeray.Train.cellL2 1
              (UnforcedLeray.Train.jet 0 (PartI.hfluct 1 (PartI.overlapField ν c tr.v T))) ≤
            ENNReal.ofReal (C_ov * Real.exp (-(lam * T))) :=
        fun T hT => (hOv ν hν_pos hν2 tr htr T hT).2.2.2.2.1
      refine (cellL2_hfluct_postOverlap_le hν_pos hc_pos tr hs hle.le hOv0).trans
        (ENNReal.ofReal_le_ofReal ?_)
      set y : ℝ := lam * (1 + ν * s) / c ^ 2
      have hy_pos : 0 < y := by positivity
      have hexp_eq : -((lam * ν / c ^ 2) * (s - B0146.overlapAge ν c)) = lam - y := by
        dsimp only [y, B0146.overlapAge]
        have hν_ne := hν_pos.ne'
        have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc_pos.ne'
        field_simp; ring
      have hexp_neg_y : Real.exp (-y) ≤ c ^ 2 / (lam * (1 + ν * s)) := by
        rw [Real.exp_neg]
        have hyle : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
        calc (Real.exp y)⁻¹ ≤ y⁻¹ := inv_anti₀ hy_pos hyle
          _ = c ^ 2 / (lam * (1 + ν * s)) := by dsimp only [y]; rw [inv_div]
      rw [hexp_eq, sub_eq_add_neg, Real.exp_add]
      calc C_ov * (c ^ 2)⁻¹ * (Real.exp lam * Real.exp (-y))
          ≤ C_ov * (c ^ 2)⁻¹ * (Real.exp lam * (c ^ 2 / (lam * (1 + ν * s)))) := by
            gcongr
        _ = (C_ov * Real.exp lam / lam) * (1 + ν * s)⁻¹ := by
            have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc_pos.ne'
            have hlam_ne := hlam.ne'
            have ha_ne : 1 + ν * s ≠ 0 := by linarith
            field_simp
        _ ≤ C_fl * (1 + ν * s)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private lemma xNorm_toReal_bounded_on_Icc {ν c m t s₁ : ℝ} (_hts₁ : t ≤ s₁)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t f w u) :
    ∃ B_w : ℝ, 0 ≤ B_w ∧ ∀ τ ∈ Icc t s₁, (xNorm c m (w τ)).toReal ≤ B_w := by
  have hcont : ContinuousOn (fun τ => (xNorm c m (w τ)).toReal) (Ici t) := by
    intro s hs
    rw [ContinuousWithinAt]
    have hlim : Tendsto (fun s' => (xNorm c m (w s' - w s)).toReal) (𝓝[Ici t] s)
        (𝓝 (0 : ℝ≥0∞).toReal) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hw.strongCont s hs)
    rw [ENNReal.toReal_zero] at hlim
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [self_mem_nhdsWithin, (Metric.tendsto_nhds.1 hlim) ε hε] with s' hs' hd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hd
    rw [Real.dist_eq]
    have hmem_s := hw.memX s hs
    have hmem_s' := hw.memX s' hs'
    have hsub_mem : MemLp (w s' - w s) 2 (B0579.cellMeasure c m) := hmem_s'.sub hmem_s
    have hle1 : (xNorm c m (w s')).toReal - (xNorm c m (w s)).toReal ≤
        (xNorm c m (w s' - w s)).toReal := by
      have heq : w s' = (w s' - w s) + w s := by ext x; simp
      have htri : xNorm c m (w s') ≤ xNorm c m (w s' - w s) + xNorm c m (w s) := by
        unfold xNorm
        conv_lhs => rw [heq]
        exact eLpNorm_add_le hsub_mem.1 hmem_s.1 one_le_two
      have htr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsub_mem.2.ne, hmem_s.2.ne⟩) htri
      rw [ENNReal.toReal_add hsub_mem.2.ne hmem_s.2.ne] at htr
      unfold xNorm at *
      linarith
    have hle2 : (xNorm c m (w s)).toReal - (xNorm c m (w s')).toReal ≤
        (xNorm c m (w s' - w s)).toReal := by
      have heq : w s = w s' - (w s' - w s) := by ext x; simp
      have htri : xNorm c m (w s) ≤ xNorm c m (w s') + xNorm c m (w s' - w s) := by
        unfold xNorm
        conv_lhs => rw [heq]
        exact eLpNorm_sub_le hmem_s'.1 hsub_mem.1 one_le_two
      have htr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmem_s'.2.ne, hsub_mem.2.ne⟩) htri
      rw [ENNReal.toReal_add hmem_s'.2.ne hsub_mem.2.ne] at htr
      unfold xNorm at *
      linarith
    exact (abs_sub_le_iff.2 ⟨hle1, hle2⟩).trans_lt hd
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := t) (b := s₁)).exists_bound_of_continuousOn
    (hcont.mono Icc_subset_Ici_self)
  refine ⟨max M₀ 0, le_max_right _ _, fun τ hτ => ?_⟩
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM₀ τ hτ).trans (le_max_left _ _))

private lemma intervalIntegral_inv_one_add_mul {ν r θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ)
    (hr : 0 < r) (hsr_nn : 0 ≤ clockAge ν r) (hsr_le : clockAge ν r ≤ clockAge ν θ) :
    (∫ τ in clockAge ν r..clockAge ν θ, (1 + ν * τ)⁻¹) = ν⁻¹ * Real.log (r / θ) := by
  set s_r := clockAge ν r
  set s_θ := clockAge ν θ
  have hpos_on : ∀ τ ∈ uIcc s_r s_θ, 0 < 1 + ν * τ := by
    intro τ hτ
    rw [uIcc_of_le hsr_le] at hτ
    have : 0 ≤ τ := hsr_nn.trans hτ.1
    positivity
  have hderiv : ∀ τ ∈ uIcc s_r s_θ,
      HasDerivAt (fun t : ℝ => ν⁻¹ * Real.log (1 + ν * t)) ((1 + ν * τ)⁻¹) τ := by
    intro τ hτ
    have h1pos := hpos_on τ hτ
    have hlin : HasDerivAt (fun t : ℝ => 1 + ν * t) ν τ :=
      (((hasDerivAt_id' τ).const_mul ν).const_add (1 : ℝ)).congr_deriv (by ring)
    have hlog := (hlin.log h1pos.ne').const_mul ν⁻¹
    refine hlog.congr_deriv ?_
    have hν_ne := hν.ne'
    have h1_ne := h1pos.ne'
    field_simp
  have hint : IntervalIntegrable (fun τ : ℝ => (1 + ν * τ)⁻¹) volume s_r s_θ := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_inv₀.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
      fun τ hτ => (hpos_on τ hτ).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, ← mul_sub]
  congr 1
  have ha_θ : 1 + ν * s_θ = (ν * θ)⁻¹ := T22Sub.clockA_clockAge hν hθ
  have ha_r : 1 + ν * s_r = (ν * r)⁻¹ := T22Sub.clockA_clockAge hν hr
  rw [ha_θ, ha_r, ← Real.log_div (by positivity) (by positivity)]
  congr 1
  have hν_ne := hν.ne'
  have hθ_ne := hθ.ne'
  have hr_ne := hr.ne'
  field_simp

/-! ## Section 4: Proof of `CTPartialMoment` -/

private theorem ctPartialMoment_core : CTPartialMoment := by
  intro P hP m hm
  obtain ⟨b₀_kin, hKinB⟩ := ctKineticImpulse P hP m hm
  obtain ⟨C_L2, C_fl, ν_fl, hC_L2, hC_fl, hν_fl, hFluct⟩ := train_uniform_all_age_bounds
  obtain ⟨K₁, hK₁_nn, hCellL1⟩ := cellL1_le_xNorm (m := m) (by linarith)
  refine ⟨max b₀_kin 1, fun b hb => ?_⟩
  have hb_kin : b₀_kin ≤ b := (le_max_left _ _).trans hb
  have hb_ge1 : 1 ≤ b := (le_max_right _ _).trans hb
  have hb_pos : 0 < b := by linarith
  obtain ⟨C_kin_raw, ν_kin, hν_kin, hKin⟩ := hKinB b hb_kin
  set C_kin : ℝ := max C_kin_raw 1
  have hC_kin_pos : 0 < C_kin := lt_of_lt_of_le one_pos (le_max_right _ _)
  set C_pm : ℝ := max 1 ((8 / Real.pi) * C_fl * C_kin)
  have hC_pm_pos : 0 < C_pm := lt_of_lt_of_le one_pos (le_max_left _ _)
  set ν₀ : ℝ := min ν_kin (min ν_fl (min (1 / 2) ((3 * b)⁻¹)))
  have hν₀_pos : 0 < ν₀ :=
    lt_min hν_kin (lt_min hν_fl (lt_min (by norm_num) (inv_pos.2 (by positivity))))
  refine ⟨C_pm, ν₀, hν₀_pos,
    fun ν hν tr htr r θ hθ hθr hrb h Zh hh_mem hh_zc hh_even hEvol => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_k : ν ≤ ν_kin := hν.2.trans (min_le_left _ _)
  have hν_f : ν ≤ ν_fl := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_3b : ν ≤ (3 * b)⁻¹ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr_pos : 0 < r := lt_of_lt_of_le hθ hθr
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  set s_r : ℝ := clockAge ν r
  set s_θ : ℝ := clockAge ν θ
  have hage_anti : ∀ {x y : ℝ}, 0 < x → x ≤ y → clockAge ν y ≤ clockAge ν x := by
    intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    have heq : ∀ {z : ℝ}, z ≠ 0 → clockAge ν z = (ν ^ 2 * z)⁻¹ - ν⁻¹ := by
      intro z hz; unfold clockAge; have := hν_pos.ne'; field_simp
    rw [heq hy.ne', heq hx.ne']
    have hinv : (ν ^ 2 * y)⁻¹ ≤ (ν ^ 2 * x)⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hxy (sq_nonneg ν))
    linarith
  have hsb_pos : 0 < clockAge ν b := by
    unfold clockAge
    have hνb : ν * b ≤ 1 / 3 := by
      calc ν * b ≤ (3 * b)⁻¹ * b := mul_le_mul_of_nonneg_right hν_3b hb_pos.le
        _ = 1 / 3 := by have := hb_pos.ne'; field_simp
    exact div_pos (by linarith) (by positivity)
  have hsr_pos : 0 < s_r := lt_of_lt_of_le hsb_pos (hage_anti hr_pos hrb)
  have hsr_le_sθ : s_r ≤ s_θ := hage_anti hθ hθr
  -- Unpack `HeatEvolvesTo` and verify `quadQ` rescaling at `s_θ` and `s_r`
  obtain ⟨w, u, hw, rfl⟩ := hEvol
  have hd_θ_eq : dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹) = c := dOfTheta_mul_sqrt_inv hν_pos hθ
  have hd_r_eq : c * Real.sqrt (ν * r) = dOfTheta ν r := c_mul_sqrt_eq_dOfTheta hν_pos hr_pos
  have hf₀_eq : Jscale (ν * r)⁻¹ h = JscaleInv (ν * r) h := by
    simpa only [inv_inv] using jscale_eq_jscaleInv_inv (inv_pos.2 (mul_pos hν_pos hr_pos)) h
  have hw_θ_mom : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s_θ x) (B0579.cell c) :=
    integrableOn_etaSq_mul (by linarith) (hw.memX s_θ hsr_le_sθ)
  have hQ_θ : quadQ (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ)) = quadQ c (w s_θ) := by
    have hh_sc : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s_θ x)
        (B0579.cell (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹))) := by
      rwa [hd_θ_eq]
    exact (integrableOn_and_quadQ_jscaleInv (inv_pos.2 (mul_pos hν_pos hθ)) hh_sc).2.trans
      (by rw [hd_θ_eq])
  have hh_mom : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * h x)
      (B0579.cell (c * Real.sqrt (ν * r))) := by
    rw [hd_r_eq]
    exact integrableOn_etaSq_mul (by linarith) hh_mem
  obtain ⟨hf₀_mom, hQ_f₀⟩ := integrableOn_and_quadQ_jscaleInv (mul_pos hν_pos hr_pos) hh_mom
  rw [← hf₀_eq] at hf₀_mom hQ_f₀
  rw [hd_r_eq] at hQ_f₀
  -- Case 1: `θ = r`
  rcases eq_or_lt_of_le hθr with rfl | hθ_lt_r
  · have hQ_sr : quadQ c (w s_r) = quadQ (dOfTheta ν θ) h :=
      (quadQ_congr_ae hw.initial).trans hQ_f₀
    rw [hQ_θ, hQ_sr]
    exact le_self_add
  -- Case 2: `θ < r` and no Biot-Savart velocity exists for `h`
  by_cases hex_uh : ∃ u_h, IsBiotSavart (dOfTheta ν r) h u_h
  swap
  · have hex' : ∀ u_h, ¬ IsBiotSavart (dOfTheta ν r) h u_h := not_exists.mp hex_uh
    have hkin_top : kinNorm (dOfTheta ν r) h = ⊤ := by unfold kinNorm; simp [hex']
    have hlog_pos : 0 < Real.log (r / θ) := Real.log_pos ((one_lt_div hθ).2 hθ_lt_r)
    have hcoeff_ne : ENNReal.ofReal (C_pm * r * Real.log (r / θ)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (mul_pos (mul_pos hC_pm_pos hr_pos) hlog_pos)).ne'
    rw [hkin_top, ENNReal.mul_top hcoeff_ne, add_top]
    exact le_top
  -- Case 3: `θ < r` and `h` admits a Biot-Savart velocity `u_h` (`kinNorm < ⊤`)
  obtain ⟨u_h, hu_h⟩ := hex_uh
  have hd_r_pos : 0 < dOfTheta ν r := Real.sqrt_pos.2 (by positivity)
  have hkin_fin : kinNorm (dOfTheta ν r) h < ⊤ := by
    rw [kinNorm_eq_velNorm hd_r_pos hu_h]
    exact velNorm_lt_top hu_h
  set K_r : ℝ := (kinNorm (dOfTheta ν r) h).toReal
  have hK_r_nn : 0 ≤ K_r := ENNReal.toReal_nonneg
  have hf₀_zc : HasZeroCirculation c (Jscale (ν * r)⁻¹ h) := by
    rw [hf₀_eq]
    apply hasZeroCirculation_jscaleInv (mul_pos hν_pos hr_pos)
    rwa [hd_r_eq]
  -- Bound `velNorm c (u τ)` for every `τ ≥ s_r` via `ctKineticImpulse` at `θ' = clockTheta ν τ`
  have hvel_bd : ∀ τ : ℝ, s_r ≤ τ →
      velNorm c (u τ) ≤ ENNReal.ofReal (C_kin * ν * r) * kinNorm (dOfTheta ν r) h := by
    intro τ hτ
    have hτ_pos : 0 < τ := lt_of_lt_of_le hsr_pos hτ
    have ha_τ_pos : 0 < clockA ν τ := by unfold clockA; positivity
    set θ' : ℝ := clockTheta ν τ
    have hθ'_pos : 0 < θ' := by unfold θ' clockTheta; positivity
    have hage_θ' : clockAge ν θ' = τ := T22Sub.clockAge_clockTheta hν_pos ha_τ_pos
    have hθ'_le_r : θ' ≤ r := by
      have ha_le : clockA ν s_r ≤ clockA ν τ := by unfold clockA; nlinarith
      rw [T22Sub.clockA_clockAge hν_pos hr_pos] at ha_le
      have hinv : r⁻¹ ≤ θ'⁻¹ := by
        unfold θ' clockTheta
        rw [inv_inv]
        calc r⁻¹ = ν * (ν * r)⁻¹ := by have := hν_pos.ne'; field_simp
          _ ≤ ν * clockA ν τ := mul_le_mul_of_nonneg_left ha_le hν_pos.le
      exact (inv_le_inv₀ hr_pos hθ'_pos).1 hinv
    set Zh' : ℝ × ℝ → ℂ := JscaleInv (ν * θ')⁻¹ (w τ)
    have hEvol' : HeatEvolvesTo ν m tr r θ' h Zh' :=
      ⟨w, u, hw, by dsimp only [Zh']; rw [hage_θ']⟩
    have hkin_raw := hKin ν ⟨hν_pos, hν_k⟩ tr htr r θ' hθ'_pos hθ'_le_r hrb h Zh'
      hh_mem hh_zc hh_even hEvol'
    have hkin_le : kinNorm (dOfTheta ν θ') Zh' ≤
        ENNReal.ofReal (C_kin * (r / θ')) * kinNorm (dOfTheta ν r) h := by
      refine hkin_raw.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hd_θ'_pos : 0 < dOfTheta ν θ' := Real.sqrt_pos.2 (by positivity)
    have hd_θ'_eq : dOfTheta ν θ' * Real.sqrt ((ν * θ')⁻¹) = c :=
      dOfTheta_mul_sqrt_inv hν_pos hθ'_pos
    have hw_τ_l2 : MemLp (w τ) 2
        (volume.restrict (B0579.cell (dOfTheta ν θ' * Real.sqrt ((ν * θ')⁻¹)))) := by
      rw [hd_θ'_eq]
      exact (hw.memX τ hτ).mono_measure (B0581.cellVol_le_cellMeasure c (by linarith))
    have hbs_θ' : IsBiotSavart (dOfTheta ν θ') Zh' (rescaleVel (ν * θ')⁻¹ (u τ)) := by
      apply isBiotSavart_jscaleInv (inv_pos.2 (mul_pos hν_pos hθ'_pos)) hw_τ_l2
      rw [hd_θ'_eq]; exact hw.biotSavart τ hτ
    have hkin_eq : kinNorm (dOfTheta ν θ') Zh' =
        ENNReal.ofReal ((ν * θ')⁻¹) * velNorm c (u τ) := by
      rw [kinNorm_eq_velNorm hd_θ'_pos hbs_θ',
        velNorm_rescaleVel (inv_pos.2 (mul_pos hν_pos hθ'_pos))
          (fun j => by rw [hd_θ'_eq]; exact (hw.biotSavart τ hτ).1 j),
        hd_θ'_eq]
    rw [hkin_eq] at hkin_le
    have hmul := mul_le_mul_of_nonneg_left hkin_le (zero_le : 0 ≤ ENNReal.ofReal (ν * θ'))
    have hlhs : ENNReal.ofReal (ν * θ') * (ENNReal.ofReal ((ν * θ')⁻¹) * velNorm c (u τ)) =
        velNorm c (u τ) := by
      have hp : 0 < ν * θ' := mul_pos hν_pos hθ'_pos
      rw [← mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne',
        ENNReal.ofReal_one, one_mul]
    have hrhs : ENNReal.ofReal (ν * θ') *
        (ENNReal.ofReal (C_kin * (r / θ')) * kinNorm (dOfTheta ν r) h) =
        ENNReal.ofReal (C_kin * ν * r) * kinNorm (dOfTheta ν r) h := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have := hθ'_pos.ne'
      field_simp
    rwa [hlhs, hrhs] at hmul
  have hvel_toReal : ∀ τ : ℝ, s_r ≤ τ → (velNorm c (u τ)).toReal ≤ C_kin * ν * r * K_r := by
    intro τ hτ
    have hbd := hvel_bd τ hτ
    rw [← ENNReal.ofReal_toReal hkin_fin.ne, ← ENNReal.ofReal_mul (by positivity)] at hbd
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbd
  -- Pass `n → ∞` in `hw.weak (φ_n)` on `[s_r, s_θ]`
  obtain ⟨hg_smooth, hg_band, hg_cut, ⟨M₂, hM₂_nn, hg_dd_bd⟩, hg_dd_ev⟩ := quadCut1_Properties
  set φ_seq : ℕ → ℝ × ℝ → ℝ := fun n x => quadCut1 n x.2
  have hφ_test : ∀ n : ℕ, B0579.IsCylTest c (φ_seq n) :=
    fun n => (isCylTest_of_snd (c := c) (hg_smooth n) (hg_band n)).1
  set G_seq : ℕ → ℝ → ℂ := fun n τ =>
    ∫ x in B0579.cell c, flowIntegrand tr (w τ) (u τ) τ (φ_seq n) x
  set I_fluct : ℝ → ℂ := fun τ =>
    ∫ x in B0579.cell c,
      ((PartI.hfluct c (tr.v τ) x 0 : ℂ) * u τ x 1 +
        (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u τ x 0)
  obtain ⟨B_w, hB_w_nn, hB_w⟩ := xNorm_toReal_bounded_on_Icc hsr_le_sθ hw
  -- Pointwise-in-`τ` limit `G_seq n τ → 2 * I_fluct τ` and uniform domination on `Icc s_r s_θ`
  set M_dom : ℝ := ν * (M₂ * (K₁ * B_w)) + M₂ * (2 * C_L2 * (C_kin * ν * r * K_r))
  have hG_dom_and_lim : ∀ τ ∈ Icc s_r s_θ,
      (∀ n : ℕ, ‖G_seq n τ‖ ≤ M_dom) ∧
        Tendsto (fun n : ℕ => G_seq n τ) atTop (𝓝 (2 * I_fluct τ)) := by
    intro τ hτ
    have hsr_τ : s_r ≤ τ := hτ.1
    have hτ_pos : 0 < τ := lt_of_lt_of_le hsr_pos hsr_τ
    have hw_τ_mem := hw.memX τ hsr_τ
    have hw_τ_l2 : MemLp (w τ) 2 (volume.restrict (B0579.cell c)) :=
      hw_τ_mem.mono_measure (B0581.cellVol_le_cellMeasure c (by linarith))
    have hw_τ_int : IntegrableOn (w τ) (B0579.cell c) := zcCellIntegrable c m (by linarith) _ hw_τ_mem
    have hw_τ_zc : HasZeroCirculation c (w τ) :=
      zeroCirculationPreserved ν c m hc_pos (by linarith) tr s_r _ w u hw hf₀_zc τ hsr_τ
    have hv_τ_bd := (hFluct ν ⟨hν_pos, hν_f⟩ tr htr τ hτ_pos.le).1
    have hv_τ_fin : UnforcedLeray.Train.cellL2 c (tr.v τ) < ⊤ :=
      hv_τ_bd.trans_lt ENNReal.ofReal_lt_top
    have hv_cont := continuous_train_v_slice tr hτ_pos.le
    have hv0_mem := memLp_comp_le_cellL2 hv_cont hv_τ_fin 0
    have hv1_mem := memLp_comp_le_cellL2 hv_cont hv_τ_fin 1
    set F_v : ℝ × ℝ → ℂ := fun x => (tr.v τ x 0 : ℂ) * u τ x 1 + (tr.v τ x 1 : ℂ) * u τ x 0
    have hFv0_int : IntegrableOn (fun x => (tr.v τ x 0 : ℂ) * u τ x 1) (B0579.cell c) :=
      hv0_mem.1.ofReal.integrable_mul ((hw.biotSavart τ hsr_τ).1 1)
    have hFv1_int : IntegrableOn (fun x => (tr.v τ x 1 : ℂ) * u τ x 0) (B0579.cell c) :=
      hv1_mem.1.ofReal.integrable_mul ((hw.biotSavart τ hsr_τ).1 0)
    have hFv_int : IntegrableOn F_v (B0579.cell c) := hFv0_int.add hFv1_int
    have hG_eq : ∀ n : ℕ, G_seq n τ =
        (ν : ℂ) * (∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ) :=
      fun n => flowIntegrand_snd_identity hτ_pos.le tr hw_τ_l2 (hw.biotSavart τ hsr_τ)
        (hg_smooth n) (hg_band n)
    constructor
    · intro n
      rw [hG_eq n]
      have hvisc_le :
          ‖(ν : ℂ) * ∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ)‖ ≤
          ν * (M₂ * (K₁ * B_w)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν_pos.le]
        refine mul_le_mul_of_nonneg_left ?_ hν_pos.le
        have h1 : ‖∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ)‖ ≤
            ∫ x in B0579.cell c, M₂ * ‖w τ x‖ := by
          refine (norm_integral_le_integral_norm _).trans
            (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hw_τ_int.norm.const_mul M₂) (Eventually.of_forall fun x => ?_))
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)
        rw [integral_const_mul] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left
          ((hCellL1 c (w τ) hw_τ_mem).trans
            (mul_le_mul_of_nonneg_left (hB_w τ hτ) hK₁_nn)) hM₂_nn)
      have hadv_le : ‖∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ)‖ ≤
          M₂ * (2 * C_L2 * (C_kin * ν * r * K_r)) := by
        have h1 : ‖∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ)‖ ≤
            M₂ * ∫ x in B0579.cell c, (‖(tr.v τ x 0 : ℂ) * u τ x 1‖ + ‖(tr.v τ x 1 : ℂ) * u τ x 0‖) := by
          rw [← integral_const_mul]
          refine (norm_integral_le_integral_norm _).trans
            (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((hFv0_int.norm.add hFv1_int.norm).const_mul M₂) (Eventually.of_forall fun x => ?_))
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact (mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (norm_add_le _ _) hM₂_nn)
        have hcs0 : ∫ x in B0579.cell c, ‖(tr.v τ x 0 : ℂ) * u τ x 1‖ ≤
            C_L2 * (C_kin * ν * r * K_r) := by
          have hu1_mem : MemLp (fun x => ‖u τ x 1‖) (ENNReal.ofReal 2)
              (volume.restrict (B0579.cell c)) := by
            rw [ENNReal.ofReal_ofNat]
            exact ((hw.biotSavart τ hsr_τ).1 1).norm
          have hv0_mem' : MemLp (fun x => tr.v τ x 0) (ENNReal.ofReal 2)
              (volume.restrict (B0579.cell c)) := by
            rw [ENNReal.ofReal_ofNat]
            exact hv0_mem.1
          have hle : ∫ x in B0579.cell c, ‖(tr.v τ x 0 : ℂ) * u τ x 1‖ ≤
              (eLpNorm (fun x => tr.v τ x 0) 2 (volume.restrict (B0579.cell c))).toReal *
                (eLpNorm (fun x => u τ x 1) 2 (volume.restrict (B0579.cell c))).toReal := by
            calc ∫ x in B0579.cell c, ‖(tr.v τ x 0 : ℂ) * u τ x 1‖
                = ∫ x in B0579.cell c, ‖tr.v τ x 0‖ * ‖‖u τ x 1‖‖ := by
                  simp only [norm_mul, Complex.norm_real, norm_norm]
              _ ≤ (∫ x in B0579.cell c, ‖tr.v τ x 0‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
                    (∫ x in B0579.cell c, ‖‖u τ x 1‖‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
                  integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hv0_mem' hu1_mem
              _ = (eLpNorm (fun x => tr.v τ x 0) 2 (volume.restrict (B0579.cell c))).toReal *
                    (eLpNorm (fun x => u τ x 1) 2 (volume.restrict (B0579.cell c))).toReal := by
                  simp only [norm_norm]
                  rw [zc_eLpNorm_two_toReal hv0_mem.1,
                    zc_eLpNorm_two_toReal ((hw.biotSavart τ hsr_τ).1 1)]
          exact hle.trans (mul_le_mul
            (ENNReal.toReal_le_of_le_ofReal hC_L2.le (hv0_mem.2.trans hv_τ_bd))
            ((ENNReal.toReal_mono (velNorm_lt_top (hw.biotSavart τ hsr_τ)).ne
              (eLpNorm_le_velNorm (u τ) 1)).trans (hvel_toReal τ hsr_τ))
            ENNReal.toReal_nonneg hC_L2.le)
        have hcs1 : ∫ x in B0579.cell c, ‖(tr.v τ x 1 : ℂ) * u τ x 0‖ ≤
            C_L2 * (C_kin * ν * r * K_r) := by
          have hu0_mem : MemLp (fun x => ‖u τ x 0‖) (ENNReal.ofReal 2)
              (volume.restrict (B0579.cell c)) := by
            rw [ENNReal.ofReal_ofNat]
            exact ((hw.biotSavart τ hsr_τ).1 0).norm
          have hv1_mem' : MemLp (fun x => tr.v τ x 1) (ENNReal.ofReal 2)
              (volume.restrict (B0579.cell c)) := by
            rw [ENNReal.ofReal_ofNat]
            exact hv1_mem.1
          have hle : ∫ x in B0579.cell c, ‖(tr.v τ x 1 : ℂ) * u τ x 0‖ ≤
              (eLpNorm (fun x => tr.v τ x 1) 2 (volume.restrict (B0579.cell c))).toReal *
                (eLpNorm (fun x => u τ x 0) 2 (volume.restrict (B0579.cell c))).toReal := by
            calc ∫ x in B0579.cell c, ‖(tr.v τ x 1 : ℂ) * u τ x 0‖
                = ∫ x in B0579.cell c, ‖tr.v τ x 1‖ * ‖‖u τ x 0‖‖ := by
                  simp only [norm_mul, Complex.norm_real, norm_norm]
              _ ≤ (∫ x in B0579.cell c, ‖tr.v τ x 1‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
                    (∫ x in B0579.cell c, ‖‖u τ x 0‖‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
                  integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hv1_mem' hu0_mem
              _ = (eLpNorm (fun x => tr.v τ x 1) 2 (volume.restrict (B0579.cell c))).toReal *
                    (eLpNorm (fun x => u τ x 0) 2 (volume.restrict (B0579.cell c))).toReal := by
                  simp only [norm_norm]
                  rw [zc_eLpNorm_two_toReal hv1_mem.1,
                    zc_eLpNorm_two_toReal ((hw.biotSavart τ hsr_τ).1 0)]
          exact hle.trans (mul_le_mul
            (ENNReal.toReal_le_of_le_ofReal hC_L2.le (hv1_mem.2.trans hv_τ_bd))
            ((ENNReal.toReal_mono (velNorm_lt_top (hw.biotSavart τ hsr_τ)).ne
              (eLpNorm_le_velNorm (u τ) 0)).trans (hvel_toReal τ hsr_τ))
            ENNReal.toReal_nonneg hC_L2.le)
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hM₂_nn)
        rw [integral_add hFv0_int.norm hFv1_int.norm]
        linarith
      exact (norm_add_le _ _).trans (add_le_add hvisc_le hadv_le)
    · -- Limit as `n → ∞`
      have hlim_visc : Tendsto
          (fun n : ℕ => ∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ))
          atTop (𝓝 0) := by
        have h1 : Tendsto
            (fun n : ℕ => ∫ x in B0579.cell c, w τ x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ))
            atTop (𝓝 (∫ x in B0579.cell c, w τ x * (2 : ℂ))) := by
          refine tendsto_integral_of_dominated_convergence (fun x => M₂ * ‖w τ x‖)
            (fun n => hw_τ_int.aestronglyMeasurable.mul
              (Complex.continuous_ofReal.comp
                (lapP_of_snd (c := c) (hg_smooth n) (hg_band n)).2.1.continuous).aestronglyMeasurable)
            (hw_τ_int.norm.const_mul M₂)
            (fun n => Eventually.of_forall fun x => ?_)
            (Eventually.of_forall fun x => ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)
          · refine tendsto_const_nhds.congr' ?_
            filter_upwards [hg_dd_ev x.2] with n hn
            rw [hn]; norm_num
        rw [integral_mul_const, hw_τ_zc.2, zero_mul] at h1
        exact h1
      have hlim_adv : Tendsto
          (fun n : ℕ => ∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ))
          atTop (𝓝 (2 * I_fluct τ)) := by
        have h1 : Tendsto
            (fun n : ℕ => ∫ x in B0579.cell c, F_v x * ((deriv (deriv (quadCut1 n)) x.2 : ℝ) : ℂ))
            atTop (𝓝 (∫ x in B0579.cell c, F_v x * (2 : ℂ))) := by
          refine tendsto_integral_of_dominated_convergence (fun x => M₂ * ‖F_v x‖)
            (fun n => hFv_int.aestronglyMeasurable.mul
              (Complex.continuous_ofReal.comp
                (lapP_of_snd (c := c) (hg_smooth n) (hg_band n)).2.1.continuous).aestronglyMeasurable)
            (hFv_int.norm.const_mul M₂)
            (fun n => Eventually.of_forall fun x => ?_)
            (Eventually.of_forall fun x => ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_dd_bd n x.2) (norm_nonneg _)
          · refine tendsto_const_nhds.congr' ?_
            filter_upwards [hg_dd_ev x.2] with n hn
            rw [hn]; norm_num
        have heq_target : (∫ x in B0579.cell c, F_v x * (2 : ℂ)) = 2 * I_fluct τ := by
          rw [integral_mul_const, mul_comm]
          congr 1
          exact integral_train_mul_u_eq_fluct hν_pos hc_pos hτ_pos tr htr hv_τ_fin
            (hw.biotSavart τ hsr_τ)
        rwa [heq_target] at h1
      have hsum := (hlim_visc.const_mul (ν : ℂ)).add hlim_adv
      rw [mul_zero, zero_add] at hsum
      exact hsum.congr fun n => (hG_eq n).symm
  -- Dominated convergence on `s_r..s_θ`
  have hlim_time : Tendsto (fun n : ℕ => ∫ τ in s_r..s_θ, G_seq n τ) atTop
      (𝓝 (∫ τ in s_r..s_θ, 2 * I_fluct τ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M_dom)
      (Eventually.of_forall fun n => (hw.timeIntegrable (φ_seq n) (hφ_test n) s_θ hsr_le_sθ).def'.aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun τ hτ => ?_)
      intervalIntegrable_const
      (Eventually.of_forall fun τ hτ => ?_)
    · rw [uIoc_of_le hsr_le_sθ] at hτ
      exact (hG_dom_and_lim τ ⟨hτ.1.le, hτ.2⟩).1 n
    · rw [uIoc_of_le hsr_le_sθ] at hτ
      exact (hG_dom_and_lim τ ⟨hτ.1.le, hτ.2⟩).2
  have hlim_lhs : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, w s_θ x * (φ_seq n x : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s_θ x)) := by
    refine (zcCutoffLimit c _ hw_θ_mom).congr fun n => integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [φ_seq]
    rw [hg_cut n x]; push_cast; ring
  have hlim_init : Tendsto
      (fun n : ℕ => ∫ x in B0579.cell c, Jscale (ν * r)⁻¹ h x * (φ_seq n x : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * Jscale (ν * r)⁻¹ h x)) := by
    refine (zcCutoffLimit c _ hf₀_mom).congr fun n => integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [φ_seq]
    rw [hg_cut n x]; push_cast; ring
  have hlim_rhs : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, w s_θ x * (φ_seq n x : ℂ)) atTop
      (𝓝 ((∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * Jscale (ν * r)⁻¹ h x) +
        ∫ τ in s_r..s_θ, 2 * I_fluct τ)) :=
    (hlim_init.add hlim_time).congr fun n => (hw.weak (φ_seq n) (hφ_test n) s_θ hsr_le_sθ).symm
  have hmom_id : ∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * w s_θ x =
      (∫ x in B0579.cell c, ((x.2 ^ 2 : ℝ) : ℂ) * Jscale (ν * r)⁻¹ h x) +
        ∫ τ in s_r..s_θ, 2 * I_fluct τ :=
    tendsto_nhds_unique hlim_lhs hlim_rhs
  -- Pointwise bound on `‖2 * I_fluct τ‖` for `τ ∈ Ioc s_r s_θ` via `zcCauchySchwarz`
  set B_fl : ℝ := 4 * C_fl * C_kin * ν * r * K_r
  have hI_fluct_bd : ∀ τ ∈ Ioc s_r s_θ, ‖2 * I_fluct τ‖ ≤ B_fl * (1 + ν * τ)⁻¹ := by
    intro τ hτ
    have hsr_τ : s_r ≤ τ := hτ.1.le
    have hτ_nn : 0 ≤ τ := (hsr_pos.trans hτ.1).le
    have hfl_bd := (hFluct ν ⟨hν_pos, hν_f⟩ tr htr τ hτ_nn).2
    have hfl_fin : UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v τ)) < ⊤ :=
      hfl_bd.trans_lt ENNReal.ofReal_lt_top
    have hfl_cont : Continuous (PartI.hfluct c (tr.v τ)) :=
      hfluct_vec_continuous (continuous_train_v_slice tr hτ_nn)
    have hfl0 := memLp_comp_le_cellL2 hfl_cont hfl_fin 0
    have hfl1 := memLp_comp_le_cellL2 hfl_cont hfl_fin 1
    have hfl_tr : (UnforcedLeray.Train.cellL2 c (PartI.hfluct c (tr.v τ))).toReal ≤
        C_fl * (1 + ν * τ)⁻¹ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hfl_bd
    have hu_bs := hw.biotSavart τ hsr_τ
    have i0 : IntegrableOn (fun x => (PartI.hfluct c (tr.v τ) x 0 : ℂ) * u τ x 1) (B0579.cell c) :=
      hfl0.1.ofReal.integrable_mul (hu_bs.1 1)
    have i1 : IntegrableOn (fun x => (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u τ x 0) (B0579.cell c) :=
      hfl1.1.ofReal.integrable_mul (hu_bs.1 0)
    have hcs0 : ‖∫ x in B0579.cell c, (PartI.hfluct c (tr.v τ) x 0 : ℂ) * u τ x 1‖ ≤
        (C_kin * ν * r * K_r) * (C_fl * (1 + ν * τ)⁻¹) := by
      rw [integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)]
      refine (zcCauchySchwarz _ _ _ (hu_bs.1 1) hfl0.1).trans ?_
      exact mul_le_mul
        ((ENNReal.toReal_mono (velNorm_lt_top hu_bs).ne (eLpNorm_le_velNorm (u τ) 1)).trans
          (hvel_toReal τ hsr_τ))
        ((ENNReal.toReal_mono hfl_fin.ne hfl0.2).trans hfl_tr)
        ENNReal.toReal_nonneg (by positivity)
    have hcs1 : ‖∫ x in B0579.cell c, (PartI.hfluct c (tr.v τ) x 1 : ℂ) * u τ x 0‖ ≤
        (C_kin * ν * r * K_r) * (C_fl * (1 + ν * τ)⁻¹) := by
      rw [integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)]
      refine (zcCauchySchwarz _ _ _ (hu_bs.1 0) hfl1.1).trans ?_
      exact mul_le_mul
        ((ENNReal.toReal_mono (velNorm_lt_top hu_bs).ne (eLpNorm_le_velNorm (u τ) 0)).trans
          (hvel_toReal τ hsr_τ))
        ((ENNReal.toReal_mono hfl_fin.ne hfl1.2).trans hfl_tr)
        ENNReal.toReal_nonneg (by positivity)
    dsimp only [I_fluct]
    rw [integral_add i0 i1, norm_mul, Complex.norm_ofNat]
    have hsum := (norm_add_le _ _).trans (add_le_add hcs0 hcs1)
    calc _ ≤ 2 * ((C_kin * ν * r * K_r) * (C_fl * (1 + ν * τ)⁻¹) +
            (C_kin * ν * r * K_r) * (C_fl * (1 + ν * τ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hsum zero_le_two
      _ = B_fl * (1 + ν * τ)⁻¹ := by dsimp only [B_fl]; ring
  -- Integrate `(1 + ν τ)⁻¹` over `s_r..s_θ`
  have hint_inv : IntervalIntegrable (fun τ : ℝ => B_fl * (1 + ν * τ)⁻¹) volume s_r s_θ := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.mul (continuousOn_inv₀.comp
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) fun τ hτ => ?_)
    rw [uIcc_of_le hsr_le_sθ] at hτ
    have : 0 ≤ τ := hsr_pos.le.trans hτ.1
    exact (by positivity : 0 < 1 + ν * τ).ne'
  have htime_norm : ‖∫ τ in s_r..s_θ, 2 * I_fluct τ‖ ≤
      4 * C_fl * C_kin * r * Real.log (r / θ) * K_r := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hsr_le_sθ
      (Eventually.of_forall hI_fluct_bd) hint_inv
    have hint_eq : (∫ t in s_r..s_θ, (1 + ν * t)⁻¹) = ν⁻¹ * Real.log (r / θ) :=
      intervalIntegral_inv_one_add_mul hν_pos hθ hr_pos hsr_pos.le hsr_le_sθ
    rw [intervalIntegral.integral_const_mul B_fl, hint_eq] at h1
    refine h1.trans_eq ?_
    dsimp only [B_fl]
    have := hν_pos.ne'
    field_simp
  -- Assemble the `quadQ` bound
  have hQ_eq : quadQ c (w s_θ) =
      quadQ (dOfTheta ν r) h - ((2 / Real.pi : ℝ) : ℂ) * ∫ τ in s_r..s_θ, 2 * I_fluct τ := by
    rw [← hQ_f₀]
    unfold quadQ
    rw [hmom_id]
    ring
  have hlog_nn : 0 ≤ Real.log (r / θ) := Real.log_nonneg ((one_le_div hθ).2 hθr)
  have hnorm_Q : ‖quadQ (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ))‖ ≤
      ‖quadQ (dOfTheta ν r) h‖ + (C_pm * r * Real.log (r / θ)) * K_r := by
    rw [hQ_θ, hQ_eq]
    have h2pi_nn : (0 : ℝ) ≤ 2 / Real.pi := by positivity
    calc ‖quadQ (dOfTheta ν r) h - ((2 / Real.pi : ℝ) : ℂ) * ∫ τ in s_r..s_θ, 2 * I_fluct τ‖
        ≤ ‖quadQ (dOfTheta ν r) h‖ +
            ‖((2 / Real.pi : ℝ) : ℂ) * ∫ τ in s_r..s_θ, 2 * I_fluct τ‖ := norm_sub_le _ _
      _ = ‖quadQ (dOfTheta ν r) h‖ + (2 / Real.pi) * ‖∫ τ in s_r..s_θ, 2 * I_fluct τ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h2pi_nn]
      _ ≤ ‖quadQ (dOfTheta ν r) h‖ +
            (2 / Real.pi) * (4 * C_fl * C_kin * r * Real.log (r / θ) * K_r) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left htime_norm h2pi_nn)
      _ = ‖quadQ (dOfTheta ν r) h‖ +
            (((8 / Real.pi) * C_fl * C_kin) * r * Real.log (r / θ)) * K_r := by ring
      _ ≤ ‖quadQ (dOfTheta ν r) h‖ + (C_pm * r * Real.log (r / θ)) * K_r := by
          gcongr
          exact le_max_right _ _
  calc ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ))‖
      ≤ ENNReal.ofReal (‖quadQ (dOfTheta ν r) h‖ + (C_pm * r * Real.log (r / θ)) * K_r) :=
        ENNReal.ofReal_le_ofReal hnorm_Q
    _ = ENNReal.ofReal ‖quadQ (dOfTheta ν r) h‖ +
          ENNReal.ofReal (C_pm * r * Real.log (r / θ)) * kinNorm (dOfTheta ν r) h := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hkin_fin.ne]

/-! ## Section 5: 1D `θ^{p-1}` integrals via monotone convergence and proof of `CTTestedImpulse` -/

private lemma setLIntegral_Ioo_le_of_hasDerivAt {r : ℝ} (hr : 0 < r) {f F : ℝ → ℝ}
    (hf_nn : ∀ θ ∈ Ioc 0 r, 0 ≤ f θ) (hf_cont : ContinuousOn f (Ioc 0 r))
    (hF_nn : ∀ θ ∈ Ioc 0 r, 0 ≤ F θ) (hderiv : ∀ θ ∈ Ioc 0 r, HasDerivAt F (f θ) θ) :
    ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (f θ) ≤ ENNReal.ofReal (F r) := by
  set ε : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  have hε_pos : ∀ n : ℕ, 0 < ε n := fun n => div_pos hr (by positivity)
  have hε_lt : ∀ n : ℕ, ε n < r := fun n => div_lt_self hr (by linarith)
  have hε_anti : Antitone ε := fun m n hmn =>
    div_le_div_of_nonneg_left hr.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 2)
  set g_seq : ℕ → ℝ → ℝ≥0∞ := fun n => (Ioo (ε n) r).indicator fun θ => ENNReal.ofReal (f θ)
  have hg_mono : Monotone g_seq := fun m n hmn θ => by
    dsimp only [g_seq]
    by_cases hm : θ ∈ Ioo (ε m) r
    · have hn : θ ∈ Ioo (ε n) r := ⟨(hε_anti hmn).trans_lt hm.1, hm.2⟩
      simp [hm, hn]
    · simp [hm]
  have hg_aem : ∀ n : ℕ, AEMeasurable (g_seq n) volume := by
    intro n
    rw [aemeasurable_indicator_iff measurableSet_Ioo]
    have hsub : Ioo (ε n) r ⊆ Ioc 0 r := fun x hx => ⟨(hε_pos n).trans hx.1, hx.2.le⟩
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hf_cont.mono hsub).aestronglyMeasurable measurableSet_Ioo).aemeasurable
  have hg_sup : ∀ θ : ℝ,
      (Ioo 0 r).indicator (fun x => ENNReal.ofReal (f x)) θ = ⨆ n : ℕ, g_seq n θ := by
    intro θ
    by_cases hθ : θ ∈ Ioo 0 r
    · rw [indicator_of_mem hθ]
      apply le_antisymm
      · obtain ⟨n₀, hn₀⟩ := exists_nat_gt (r / θ)
        have hmem : θ ∈ Ioo (ε n₀) r := by
          refine ⟨?_, hθ.2⟩
          dsimp only [ε]
          rw [div_lt_iff₀ (by positivity)]
          have : r < (n₀ : ℝ) * θ := (div_lt_iff₀ hθ.1).1 hn₀
          nlinarith [hθ.1]
        exact le_trans (by simp [g_seq, hmem]) (le_iSup (fun n => g_seq n θ) n₀)
      · refine iSup_le fun n => ?_
        by_cases hm : θ ∈ Ioo (ε n) r <;> simp [g_seq, hm]
    · rw [indicator_of_notMem hθ]
      apply le_antisymm zero_le
      refine iSup_le fun n => ?_
      have hnot : θ ∉ Ioo (ε n) r := fun hm => hθ ⟨(hε_pos n).trans hm.1, hm.2⟩
      simp [g_seq, hnot]
  rw [← lintegral_indicator measurableSet_Ioo, lintegral_congr hg_sup,
    lintegral_iSup' hg_aem (Eventually.of_forall fun x m n hmn => hg_mono hmn x)]
  refine iSup_le fun n => ?_
  rw [lintegral_indicator measurableSet_Ioo]
  have hsub_Icc : Icc (ε n) r ⊆ Ioc 0 r := fun x hx => ⟨lt_of_lt_of_le (hε_pos n) hx.1, hx.2⟩
  have hf_int_on : IntegrableOn f (Ioc (ε n) r) volume :=
    ((hf_cont.mono hsub_Icc).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hf_ii : IntervalIntegrable f volume (ε n) r :=
    (hf_cont.mono (by rwa [uIcc_of_le (hε_lt n).le])).intervalIntegrable
  have hderiv_n : ∀ θ ∈ uIcc (ε n) r, HasDerivAt F (f θ) θ := by
    rw [uIcc_of_le (hε_lt n).le]
    exact fun θ hθ => hderiv θ (hsub_Icc hθ)
  have hftc : ∫ θ in (ε n)..r, f θ = F r - F (ε n) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_n hf_ii
  calc ∫⁻ θ in Ioo (ε n) r, ENNReal.ofReal (f θ)
      ≤ ∫⁻ θ in Ioc (ε n) r, ENNReal.ofReal (f θ) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ θ in Ioc (ε n) r, f θ) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hf_int_on]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
        exact hf_nn θ ⟨(hε_pos n).trans hθ.1, hθ.2⟩
    _ = ENNReal.ofReal (F r - F (ε n)) := by
        rw [← intervalIntegral.integral_of_le (hε_lt n).le, hftc]
    _ ≤ ENNReal.ofReal (F r) := by
        apply ENNReal.ofReal_le_ofReal
        have hFε : 0 ≤ F (ε n) := hF_nn (ε n) ⟨hε_pos n, (hε_lt n).le⟩
        linarith

private lemma setLIntegral_rpow_sub_one_le {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ (p - 1)) ≤ ENNReal.ofReal (r ^ p / p) := by
  refine setLIntegral_Ioo_le_of_hasDerivAt (F := fun θ => θ ^ p / p) hr
    (fun θ hθ => Real.rpow_nonneg hθ.1.le _)
    (continuousOn_id.rpow_const fun θ hθ => Or.inl hθ.1.ne')
    (fun θ hθ => div_nonneg (Real.rpow_nonneg hθ.1.le _) hp.le)
    (fun θ hθ => ?_)
  refine ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hθ.1.ne')).div_const p).congr_deriv ?_
  exact mul_div_cancel_left₀ _ hp.ne'

private lemma setLIntegral_rpow_sub_one_mul_log_le {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ (p - 1) * Real.log (r / θ)) ≤
      ENNReal.ofReal (r ^ p / p ^ 2) := by
  set F : ℝ → ℝ := fun θ => (θ ^ p / p) * Real.log (r / θ) + θ ^ p / p ^ 2
  have hFr : F r = r ^ p / p ^ 2 := by
    dsimp only [F]
    rw [div_self hr.ne', Real.log_one, mul_zero, zero_add]
  rw [← hFr]
  refine setLIntegral_Ioo_le_of_hasDerivAt hr
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg hθ.1.le _)
      (Real.log_nonneg ((one_le_div hθ.1).2 hθ.2)))
    ((continuousOn_id.rpow_const fun θ hθ => Or.inl hθ.1.ne').mul
      ((continuousOn_const.div continuousOn_id fun θ hθ => hθ.1.ne').log
        fun θ hθ => (div_pos hr hθ.1).ne'))
    (fun θ hθ => add_nonneg
      (mul_nonneg (div_nonneg (Real.rpow_nonneg hθ.1.le _) hp.le)
        (Real.log_nonneg ((one_le_div hθ.1).2 hθ.2)))
      (div_nonneg (Real.rpow_nonneg hθ.1.le _) (sq_nonneg p)))
    (fun θ hθ => ?_)
  have hd1 : HasDerivAt (fun t : ℝ => t ^ p / p) (θ ^ (p - 1)) θ := by
    refine ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hθ.1.ne')).div_const p).congr_deriv ?_
    exact mul_div_cancel_left₀ _ hp.ne'
  have hd_log : HasDerivAt (fun t : ℝ => Real.log (r / t)) (-θ⁻¹) θ := by
    have hd_div : HasDerivAt (fun t : ℝ => r / t) (-(r / θ ^ 2)) θ :=
      ((hasDerivAt_const θ r).fun_div (hasDerivAt_id' θ) hθ.1.ne').congr_deriv (by ring)
    refine (hd_div.log (div_pos hr hθ.1).ne').congr_deriv ?_
    have hr_ne := hr.ne'
    have hθ_ne := hθ.1.ne'
    field_simp
  have hd2 : HasDerivAt (fun t : ℝ => t ^ p / p ^ 2) (θ ^ (p - 1) / p) θ := by
    refine ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hθ.1.ne')).div_const (p ^ 2)).congr_deriv ?_
    have hp_ne := hp.ne'
    field_simp
  refine ((hd1.mul hd_log).add hd2).congr_deriv ?_
  have hrpow : θ ^ p * θ⁻¹ = θ ^ (p - 1) := by
    rw [Real.rpow_sub_one hθ.1.ne' p, div_eq_mul_inv]
  calc θ ^ (p - 1) * Real.log (r / θ) + θ ^ p / p * -θ⁻¹ + θ ^ (p - 1) / p
      = θ ^ (p - 1) * Real.log (r / θ) - (θ ^ p * θ⁻¹) / p + θ ^ (p - 1) / p := by ring
    _ = θ ^ (p - 1) * Real.log (r / θ) := by rw [hrpow]; ring

private theorem ctTestedImpulse_of_partialMoment (hPM : CTPartialMoment) : CTTestedImpulse := by
  intro P hP m hm
  obtain ⟨b₀, hB⟩ := hPM P hP m hm
  refine ⟨b₀, fun b hb p hp => ?_⟩
  obtain ⟨C_raw, ν₀, hν₀, hBound⟩ := hB b hb
  set C_pm : ℝ := max C_raw 0
  have hC_pm_nn : 0 ≤ C_pm := le_max_right _ _
  set C : ℝ := max (1 / p) (C_pm / p ^ 2)
  have hC_pos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, ν₀, hν₀, fun ν hν tr htr r hr_pos hrb h hh_mem hh_zc hh_even Zh hZh => ?_⟩
  by_cases hkin_top : kinNorm (dOfTheta ν r) h = ⊤
  · have hr_ne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr_pos).ne'
    have hCr_ne : ENNReal.ofReal (C * r ^ p) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (mul_pos hC_pos (Real.rpow_pos_of_pos hr_pos p))).ne'
    rw [hkin_top, ENNReal.mul_top hr_ne, add_top, ENNReal.mul_top hCr_ne]
    exact le_top
  · set Q₀ : ℝ := ‖quadQ (dOfTheta ν r) h‖
    set K₀ : ℝ := (kinNorm (dOfTheta ν r) h).toReal
    have hK₀_nn : 0 ≤ K₀ := ENNReal.toReal_nonneg
    have hpt : ∀ θ ∈ Ioo 0 r,
        ENNReal.ofReal (θ ^ (p - 1)) * ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (Zh θ)‖ ≤
          ENNReal.ofReal Q₀ * ENNReal.ofReal (θ ^ (p - 1)) +
            ENNReal.ofReal (C_pm * r * K₀) * ENNReal.ofReal (θ ^ (p - 1) * Real.log (r / θ)) := by
      intro θ hθ
      have hpm := hBound ν hν tr htr r θ hθ.1 hθ.2.le hrb h (Zh θ) hh_mem hh_zc hh_even
        (hZh θ ⟨hθ.1, hθ.2.le⟩)
      have hlog_nn : 0 ≤ Real.log (r / θ) := Real.log_nonneg ((one_le_div hθ.1).2 hθ.2.le)
      have hpm' : ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (Zh θ)‖ ≤
          ENNReal.ofReal Q₀ + ENNReal.ofReal (C_pm * r * Real.log (r / θ)) * ENNReal.ofReal K₀ := by
        rw [ENNReal.ofReal_toReal hkin_top]
        refine hpm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal ?_) zero_le))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hr_pos.le) hlog_nn
      have hθp_nn : 0 ≤ θ ^ (p - 1) := Real.rpow_nonneg hθ.1.le _
      calc ENNReal.ofReal (θ ^ (p - 1)) * ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (Zh θ)‖
          ≤ ENNReal.ofReal (θ ^ (p - 1)) *
              (ENNReal.ofReal Q₀ +
                ENNReal.ofReal (C_pm * r * Real.log (r / θ)) * ENNReal.ofReal K₀) :=
            mul_le_mul_of_nonneg_left hpm' zero_le
        _ = ENNReal.ofReal Q₀ * ENNReal.ofReal (θ ^ (p - 1)) +
              ENNReal.ofReal (C_pm * r * K₀) *
                ENNReal.ofReal (θ ^ (p - 1) * Real.log (r / θ)) := by
            rw [mul_add, mul_comm (ENNReal.ofReal (θ ^ (p - 1))) (ENNReal.ofReal Q₀)]
            congr 1
            rw [← mul_assoc, ← ENNReal.ofReal_mul hθp_nn,
              ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    have hmeas1 : Measurable fun θ : ℝ => ENNReal.ofReal Q₀ * ENNReal.ofReal (θ ^ (p - 1)) := by
      fun_prop
    have hstep1 := (MeasureTheory.setLIntegral_mono' (μ := volume) measurableSet_Ioo hpt).trans_eq
      (lintegral_add_left hmeas1 _)
    have hI1 : ∫⁻ θ in Ioo 0 r, ENNReal.ofReal Q₀ * ENNReal.ofReal (θ ^ (p - 1)) ≤
        ENNReal.ofReal (C * r ^ p) * ENNReal.ofReal Q₀ := by
      rw [lintegral_const_mul _ (by fun_prop)]
      refine (mul_le_mul_of_nonneg_left (setLIntegral_rpow_sub_one_le hp hr_pos) zero_le).trans ?_
      rw [mul_comm (ENNReal.ofReal (C * r ^ p))]
      refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
      calc r ^ p / p = (1 / p) * r ^ p := by ring
        _ ≤ C * r ^ p := mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hr_pos.le p)
    have hI2 : ∫⁻ θ in Ioo 0 r,
        ENNReal.ofReal (C_pm * r * K₀) * ENNReal.ofReal (θ ^ (p - 1) * Real.log (r / θ)) ≤
        ENNReal.ofReal (C * r ^ p) * (ENNReal.ofReal r * kinNorm (dOfTheta ν r) h) := by
      rw [lintegral_const_mul _ (by fun_prop)]
      refine (mul_le_mul_of_nonneg_left
        (setLIntegral_rpow_sub_one_mul_log_le hp hr_pos) zero_le).trans ?_
      rw [← ENNReal.ofReal_toReal hkin_top, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hr_pos.le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc C_pm * r * K₀ * (r ^ p / p ^ 2)
          = (C_pm / p ^ 2) * r ^ p * (r * K₀) := by ring
        _ ≤ C * r ^ p * (r * K₀) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr_pos.le p))
              (mul_nonneg hr_pos.le hK₀_nn)
    calc ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ (p - 1)) * ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (Zh θ)‖
        ≤ (∫⁻ θ in Ioo 0 r, ENNReal.ofReal Q₀ * ENNReal.ofReal (θ ^ (p - 1))) +
            ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (C_pm * r * K₀) *
              ENNReal.ofReal (θ ^ (p - 1) * Real.log (r / θ)) := hstep1
      _ ≤ ENNReal.ofReal (C * r ^ p) * ENNReal.ofReal Q₀ +
            ENNReal.ofReal (C * r ^ p) * (ENNReal.ofReal r * kinNorm (dOfTheta ν r) h) :=
          add_le_add hI1 hI2
      _ = ENNReal.ofReal (C * r ^ p) *
            (ENNReal.ofReal Q₀ + ENNReal.ofReal r * kinNorm (dOfTheta ν r) h) :=
          (mul_add _ _ _).symm

end TestedImpulseAux

/-- **`eq:ct-partial-moment` and `eq:ct-tested-impulse`** (SP 3252-3274, task `PartIII-a:T22/3`). -/
theorem ctTestedImpulsePair :
    UnforcedLeray.Short.IIIa.CTPartialMoment ∧ UnforcedLeray.Short.IIIa.CTTestedImpulse :=
  ⟨TestedImpulseAux.ctPartialMoment_core,
    TestedImpulseAux.ctTestedImpulse_of_partialMoment TestedImpulseAux.ctPartialMoment_core⟩

theorem ctPartialMoment : CTPartialMoment := ctTestedImpulsePair.1

theorem ctTestedImpulse : CTTestedImpulse := ctTestedImpulsePair.2

end UnforcedLeray.Short.IIIa
