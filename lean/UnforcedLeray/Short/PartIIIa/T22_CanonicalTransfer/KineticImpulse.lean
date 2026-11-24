import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2_3_1
import UnforcedLeray.Short.PartIIIa.T07_ScalingJaInv
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness.MollLimitCore
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.TailEnergyBound
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.BiotSavartH1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.BiotSavartSlice
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Represent
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd
import UnforcedLeray.Short.PartIIIa.Clock.Existence.BiotSavartField
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLip
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ZeroModeLinearity

/-!
# Part III-a, `PartIII-a:T22/1`: Kinetic impulse bound (`eq:ct-kinetic-impulse`)

Source of record: `the November 2 reference manuscript` (SP), lines 3242-3251.

Proves `ctKineticImpulse : UnforcedLeray.Short.IIIa.CTKineticImpulse`:
for `m > 8`, `b ≥ 1`, sufficiently small `ν > 0`, any BUC train `tr`, and `0 < θ ≤ r ≤ b`,
if `h ∈ X_{m, d(r)}` has zero circulation and `HeatEvolvesTo ν m tr r θ h Zh`, then
`kinNorm (dOfTheta ν θ) Zh ≤ ENNReal.ofReal (C * (r / θ)) * kinNorm (dOfTheta ν r) h`.

Proof route:
1. Rescale between heat-clock cells `d(x)` and the physical cell `c = ν⁻²` via `JscaleInv`:
   `kinNorm (d(θ)) Zh ≤ (νθ)⁻¹ * velNorm c (u s_θ)` and
   `velNorm c (u s_r) = (νr) * velNorm (d(r)) u_h` for every Biot-Savart velocity `u_h` of `h`.
2. Embed the strongly continuous linearised vorticity trajectory `w` on `[s_r, s_θ]` into `ZC8 c`
   (clamped outside `[0, T + 1]`, `T = s_θ - s_r`), apply the continuous Biot-Savart velocity and
   weak-gradient maps together with `exists_stronglyMeasurable_rep_of_continuousOn` to obtain a
   jointly measurable velocity/gradient pair `(b_sh, G_sh)` satisfying `CoreTruncData c ν (T + 1) 0`
   with forcing `F_sh = -(v ⊗ b_sh + b_sh ⊗ v)` (verified via `V1.pointwise_TI`, `ladProductRule`,
   and transverse stream-cutoff approximation).
3. Apply `coreIdentity_trunc`, the mollified solenoidal advection bound `moll_slice_advection_le`,
   smooth-cutoff Grönwall integration on `[0, T]`, and the late strain integral bound
   `tail_strain_integral_bound` (`s_r ≥ coreEnd ν b > 2 > coreEnd ν b - 1`) to deduce
   `velNorm c (u s_θ) ≤ exp(2 C_strain b) * velNorm c (u s_r)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace KineticImpulseAux

/-! ## Section 1: `JscaleInv` rescaling of Biot-Savart velocities and cell norms -/

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
        · dsimp
          field_simp [hR_ne]
        · rfl
      rw [heq]
      exact hψ.periodic _
    · intro x hx
      apply hR_band
      have h1 : |R| < |(Real.sqrt a)⁻¹ * x.2| := by
        rw [abs_mul, abs_inv, abs_of_pos hR]
        have : |R| * Real.sqrt a < |x.2| := hx
        calc |R| = |R| * Real.sqrt a * (Real.sqrt a)⁻¹ := by field_simp [hR_ne]
          _ < |x.2| * (Real.sqrt a)⁻¹ := mul_lt_mul_of_pos_right this (inv_pos.2 hR)
          _ = (Real.sqrt a)⁻¹ * |x.2| := mul_comm _ _
      exact (le_abs_self R).trans_lt h1
  refine ⟨htest, fun j y => ?_⟩
  have hLy : L (Real.sqrt a • y) = y := by
    dsimp [L]
    exact inv_smul_smul₀ hR_ne y
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
      have hp0 := hpd_sc 0 y
      have hp1 := hpd_sc 1 y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hp0]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hp1]; field_simp [hR_ne]
      dsimp only [rescaleVel, g_div]
      rw [hp0', hp1', ← ha_pow]
      push_cast
      ring
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
      have hp0 := hpd_sc 0 y
      have hp1 := hpd_sc 1 y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hp0]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hp1]; field_simp [hR_ne]
      dsimp only [rescaleVel, g_rhs]
      rw [hp0', hp1', ← ha_pow]
      push_cast
      ring
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
  have hR_ne : Real.sqrt ((ν * r)⁻¹) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [Real.sqrt_inv] at h hR_ne
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

/-! ## Section 2: Weight monotonicity, `ZC8 c` Biot-Savart `→L[ℝ]` maps, and `CoreTruncData` -/

private lemma cellMeasure_le_of_le (c : ℝ) {m₁ m₂ : ℝ} (hm : m₁ ≤ m₂) :
    B0579.cellMeasure c m₁ ≤ B0579.cellMeasure c m₂ := by
  unfold B0579.cellMeasure
  refine withDensity_mono (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [T07.density_coe, T07.density_coe]
  apply ENNReal.ofReal_le_ofReal
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  exact Real.rpow_le_rpow_of_exponent_le hjb1 hm

private lemma memLp_unweighted_of_memX_pos {c m : ℝ} (hm : 0 ≤ m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    MemLp f 2 (volume.restrict (B0579.cell c)) :=
  hf.mono_measure (B0581.cellVol_le_cellMeasure c hm)

private abbrev XC8 (c : ℝ) : Type := Lp ℂ 2 (B0579.cellMeasure c 8)

private def reLp8 (c : ℝ) : XC8 c →L[ℝ] B0579.X c 8 :=
  Complex.reCLM.compLpL 2 (B0579.cellMeasure c 8)

private def imLp8 (c : ℝ) : XC8 c →L[ℝ] B0579.X c 8 :=
  Complex.imCLM.compLpL 2 (B0579.cellMeasure c 8)

private lemma coeFn_reLp8 (c : ℝ) (W : XC8 c) :
    (reLp8 c W : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c 8] fun x => (W x).re :=
  Complex.reCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c 8) W

private lemma coeFn_imLp8 (c : ℝ) (W : XC8 c) :
    (imLp8 c W : ℝ × ℝ → ℝ) =ᵐ[B0579.cellMeasure c 8] fun x => (W x).im :=
  Complex.imCLM.coeFn_compLpL (p := 2) (μ := B0579.cellMeasure c 8) W

private lemma norm_reLp8_le (c : ℝ) (W : XC8 c) : ‖reLp8 c W‖ ≤ ‖W‖ := by
  have hop : ‖reLp8 c‖ ≤ 1 := by
    refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  exact (reLp8 c).le_opNorm W |>.trans (by nlinarith [norm_nonneg W])

private lemma norm_imLp8_le (c : ℝ) (W : XC8 c) : ‖imLp8 c W‖ ≤ ‖W‖ := by
  have hop : ‖imLp8 c‖ ≤ 1 := by
    refine (ContinuousLinearMap.norm_compLpL_le _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm z
  exact (imLp8 c).le_opNorm W |>.trans (by nlinarith [norm_nonneg W])

private def circRe8 (c : ℝ) : XC8 c →L[ℝ] ℝ :=
  (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM
    (c := c) (m := 8) (by norm_num)).comp (reLp8 c)

private def circIm8 (c : ℝ) : XC8 c →L[ℝ] ℝ :=
  (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.circulationCLM
    (c := c) (m := 8) (by norm_num)).comp (imLp8 c)

private lemma circRe8_apply (c : ℝ) (W : XC8 c) :
    circRe8 c W = ∫ x in B0579.cell c, reLp8 c W x := by
  simp [circRe8]

private lemma circIm8_apply (c : ℝ) (W : XC8 c) :
    circIm8 c W = ∫ x in B0579.cell c, imLp8 c W x := by
  simp [circIm8]

private lemma integrableOn_of_XC8 (c : ℝ) (W : XC8 c) :
    IntegrableOn (W : ℝ × ℝ → ℂ) (B0579.cell c) := by
  have hre : Integrable (reLp8 c W) (volume.restrict (B0579.cell c)) :=
    UnforcedLeray.B0583.integrable_of_X (c := c) (m := 8) (by norm_num) (reLp8 c W)
  have him : Integrable (imLp8 c W) (volume.restrict (B0579.cell c)) :=
    UnforcedLeray.B0583.integrable_of_X (c := c) (m := 8) (by norm_num) (imLp8 c W)
  have hreC : Integrable (fun x => ((reLp8 c W x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.integrable_comp hre
  have himC : Integrable (fun x => ((imLp8 c W x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.integrable_comp him
  refine Integrable.congr (hreC.add (himC.const_mul Complex.I)) ?_
  filter_upwards [(B0579.ac_cellMeasure c 8).ae_le (coeFn_reLp8 c W),
    (B0579.ac_cellMeasure c 8).ae_le (coeFn_imLp8 c W)] with x hx1 hx2
  dsimp only [Pi.add_apply]
  rw [hx1, hx2]
  conv_rhs => rw [← Complex.re_add_im (W x)]
  ring

private lemma integral_XC8_eq (c : ℝ) (W : XC8 c) :
    ∫ x in B0579.cell c, (W : ℝ × ℝ → ℂ) x =
      (circRe8 c W : ℂ) + Complex.I * (circIm8 c W : ℂ) := by
  have hre : Integrable (reLp8 c W) (volume.restrict (B0579.cell c)) :=
    UnforcedLeray.B0583.integrable_of_X (c := c) (m := 8) (by norm_num) (reLp8 c W)
  have him : Integrable (imLp8 c W) (volume.restrict (B0579.cell c)) :=
    UnforcedLeray.B0583.integrable_of_X (c := c) (m := 8) (by norm_num) (imLp8 c W)
  have hreC : Integrable (fun x => ((reLp8 c W x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.integrable_comp hre
  have himC : Integrable (fun x => ((imLp8 c W x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.integrable_comp him
  have hae : (W : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => ((reLp8 c W x : ℝ) : ℂ) + Complex.I * ((imLp8 c W x : ℝ) : ℂ) := by
    filter_upwards [(B0579.ac_cellMeasure c 8).ae_le (coeFn_reLp8 c W),
      (B0579.ac_cellMeasure c 8).ae_le (coeFn_imLp8 c W)] with x hx1 hx2
    simp only [hx1, hx2]
    conv_lhs => rw [← Complex.re_add_im (W x)]
    ring
  rw [integral_congr_ae hae, integral_add hreC (himC.const_mul Complex.I),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    circRe8_apply, circIm8_apply]

private def circRCLM8 (c : ℝ) : XC8 c →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun W => (circRe8 c W : ℂ) + Complex.I * (circIm8 c W : ℂ)
      map_add' := fun W₁ W₂ => by simp only [map_add, Complex.ofReal_add]; ring
      map_smul' := fun a W => by
        simp only [RingHom.id_apply, map_smul, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
        ring }
    (‖circRe8 c‖ + ‖circIm8 c‖)
    (fun W => by
      calc ‖(circRe8 c W : ℂ) + Complex.I * (circIm8 c W : ℂ)‖
          ≤ ‖(circRe8 c W : ℂ)‖ + ‖Complex.I * (circIm8 c W : ℂ)‖ := norm_add_le _ _
        _ = ‖circRe8 c W‖ + ‖circIm8 c W‖ := by simp
        _ ≤ ‖circRe8 c‖ * ‖W‖ + ‖circIm8 c‖ * ‖W‖ :=
            add_le_add ((circRe8 c).le_opNorm W) ((circIm8 c).le_opNorm W)
        _ = (‖circRe8 c‖ + ‖circIm8 c‖) * ‖W‖ := by ring)

private def ZC8 (c : ℝ) : Submodule ℝ (XC8 c) := LinearMap.ker (circRCLM8 c).toLinearMap

private instance isClosed_ZC8 (c : ℝ) : IsClosed (ZC8 c : Set (XC8 c)) := by
  change IsClosed {W : XC8 c | circRCLM8 c W = 0}
  exact isClosed_singleton.preimage (circRCLM8 c).continuous

private instance completeSpace_ZC8 (c : ℝ) : CompleteSpace (ZC8 c) :=
  (isClosed_ZC8 c).completeSpace_coe

private lemma zc8_circRe_zero (c : ℝ) (W : ZC8 c) : ∫ x in B0579.cell c, reLp8 c W.1 x = 0 := by
  rw [← circRe8_apply]
  have h0 : (circRe8 c W.1 : ℂ) + Complex.I * (circIm8 c W.1 : ℂ) = 0 := W.2
  simpa using congrArg Complex.re h0

private lemma zc8_circIm_zero (c : ℝ) (W : ZC8 c) : ∫ x in B0579.cell c, imLp8 c W.1 x = 0 := by
  rw [← circIm8_apply]
  have h0 : (circRe8 c W.1 : ℂ) + Complex.I * (circIm8 c W.1 : ℂ) = 0 := W.2
  simpa using congrArg Complex.im h0

private def toZC8 {c : ℝ} {h : ℝ × ℝ → ℂ} (hmem : MemLp h 2 (B0579.cellMeasure c 8))
    (hzc : HasZeroCirculation c h) : ZC8 c :=
  ⟨hmem.toLp h, by
    change circRCLM8 c (hmem.toLp h) = 0
    change (circRe8 c (hmem.toLp h) : ℂ) + Complex.I * (circIm8 c (hmem.toLp h) : ℂ) = 0
    rw [← integral_XC8_eq]
    have hae : (hmem.toLp h : ℝ × ℝ → ℂ) =ᵐ[volume.restrict (B0579.cell c)] h :=
      (B0579.ac_cellMeasure c 8).ae_le (MemLp.coeFn_toLp hmem)
    rw [integral_congr_ae hae]
    exact hzc.2⟩

private lemma norm_sub_toZC8 {c : ℝ} {h₁ h₂ : ℝ × ℝ → ℂ}
    (hm₁ : MemLp h₁ 2 (B0579.cellMeasure c 8)) (hz₁ : HasZeroCirculation c h₁)
    (hm₂ : MemLp h₂ 2 (B0579.cellMeasure c 8)) (hz₂ : HasZeroCirculation c h₂) :
    ‖toZC8 hm₁ hz₁ - toZC8 hm₂ hz₂‖ = (xNorm c 8 (h₁ - h₂)).toReal := by
  change ‖hm₁.toLp h₁ - hm₂.toLp h₂‖ = (xNorm c 8 (h₁ - h₂)).toReal
  rw [← MemLp.toLp_sub hm₁ hm₂, Lp.norm_toLp, xNorm]

section BiotSavartRCLM

variable (c : ℝ) [hc : Fact (0 < c)]

private lemma gradQ_nonzeroPart_local (w : Lp ℂ 2 (B0581.cellVol c)) :
    B0583.gradQ c (B0581.nonzeroPart c w) = B0583.gradQ c w := by
  rw [B0583.gradQ_apply, B0583.gradQ_apply]
  congr 1; ext1; funext k
  change B0583.qModeCLM c k ((B0581.modes c (B0581.nonzeroPart c w) : B0581.ModeSeq ℂ) k) =
    B0583.qModeCLM c k ((B0581.modes c w : B0581.ModeSeq ℂ) k)
  rw [B0581.modes_nonzeroPart]
  split_ifs with hk
  · subst hk; simp [B0583.qModeCLM_apply, B0581.bsModeCLM_zero]
  · rfl

private lemma gradEta_nonzeroPart_local (w : Lp ℂ 2 (B0581.cellVol c)) :
    B0583.gradEta c (B0581.nonzeroPart c w) = B0583.gradEta c w := by
  rw [B0583.gradEta_apply, B0583.gradEta_apply]
  congr 1; ext1; funext k
  change B0583.etaModeCLM c k ((B0581.modes c (B0581.nonzeroPart c w) : B0581.ModeSeq ℂ) k) =
    B0583.etaModeCLM c k ((B0581.modes c w : B0581.ModeSeq ℂ) k)
  rw [B0581.modes_nonzeroPart]
  split_ifs with hk
  · subst hk; simp [B0583.etaModeCLM_zero]
  · rfl

private lemma zeroVelEtaLp8_add (w z : B0579.X c 8)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.zeroVelEtaLp c (by norm_num) (w + z) hwz0 =
      B0583.zeroVelEtaLp c (by norm_num) w hw0 + B0583.zeroVelEtaLp c (by norm_num) z hz0 := by
  have hbar := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.omegaBar_add_ae
    (c := c) (m := 8) (by norm_num) w z
  have hbar_cell : (fun x : B0579.Plane => B0583.omegaBar c ((w + z : B0579.X c 8) : B0579.Plane → ℝ) x.2)
      =ᵐ[B0581.cellVol c]
        fun x => B0583.omegaBar c w x.2 + B0583.omegaBar c z x.2 := by
    rw [B0581.cellVol_eq]
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp hbar
  apply Lp.ext
  filter_upwards [B0583.coeFn_zeroVelEtaLp c (by norm_num) (w + z) hwz0,
    B0583.coeFn_zeroVelEtaLp c (by norm_num) w hw0,
    B0583.coeFn_zeroVelEtaLp c (by norm_num) z hz0,
    Lp.coeFn_add (B0583.zeroVelEtaLp c (by norm_num) w hw0)
      (B0583.zeroVelEtaLp c (by norm_num) z hz0),
    hbar_cell] with x hsum hw hz hadd hb
  rw [hsum, hadd, Pi.add_apply, hw, hz]
  change B0583.zeroVelEta c ((w + z : B0579.X c 8) : B0579.Plane → ℝ) x =
    B0583.zeroVelEta c w x + B0583.zeroVelEta c z x
  simp only [B0583.zeroVelEta, B0583.profField]
  rw [hb]
  simp only [neg_add, Complex.ofReal_add, add_smul]

private lemma zeroVelEtaLp8_smul (a : ℝ) (w : B0579.X c 8)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.zeroVelEtaLp c (by norm_num) (a • w) haw0 =
      a • B0583.zeroVelEtaLp c (by norm_num) w hw0 := by
  have hbar := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.omegaBar_smul_ae
    (c := c) (m := 8) (by norm_num) a w
  have hbar_cell : (fun x : B0579.Plane => B0583.omegaBar c ((a • w : B0579.X c 8) : B0579.Plane → ℝ) x.2)
      =ᵐ[B0581.cellVol c]
        fun x => a * B0583.omegaBar c w x.2 := by
    rw [B0581.cellVol_eq]
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp hbar
  apply Lp.ext
  filter_upwards [B0583.coeFn_zeroVelEtaLp c (by norm_num) (a • w) haw0,
    B0583.coeFn_zeroVelEtaLp c (by norm_num) w hw0,
    Lp.coeFn_smul a (B0583.zeroVelEtaLp c (by norm_num) w hw0),
    hbar_cell] with x hsc hw hsm hb
  rw [hsc, hsm, Pi.smul_apply, hw]
  change B0583.zeroVelEta c ((a • w : B0579.X c 8) : B0579.Plane → ℝ) x =
    a • B0583.zeroVelEta c w x
  simp only [B0583.zeroVelEta, B0583.profField]
  rw [hb]
  ext i
  fin_cases i <;> simp [Complex.ofReal_mul, smul_eq_mul]

private lemma velocity8_add_real (w z : B0579.X c 8)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.velocity c (by norm_num) (w + z) hwz0 =
      B0583.velocity c (by norm_num) w hw0 + B0583.velocity c (by norm_num) z hz0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 8 (by norm_num)
  have heq : ∀ (u : B0579.X c 8) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velocity c (by norm_num) u hu0 =
        B0581.velNe c (cx u) + B0583.zeroVelLp c (by norm_num) u hu0 := by
    intro u hu0; unfold B0583.velocity; rw [B0581.velNe_nonzeroPart]; rfl
  rw [heq (w + z) hwz0, heq w hw0, heq z hz0, cx.map_add, (B0581.velNe c).map_add,
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.zeroVelLp_add (by norm_num) w z hw0 hz0 hwz0]
  abel

private lemma velocity8_smul_real (a : ℝ) (w : B0579.X c 8)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.velocity c (by norm_num) (a • w) haw0 =
      a • B0583.velocity c (by norm_num) w hw0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 8 (by norm_num)
  have heq : ∀ (u : B0579.X c 8) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velocity c (by norm_num) u hu0 =
        B0581.velNe c (cx u) + B0583.zeroVelLp c (by norm_num) u hu0 := by
    intro u hu0; unfold B0583.velocity; rw [B0581.velNe_nonzeroPart]; rfl
  have hsm : B0581.velNe c (a • cx w) = a • B0581.velNe c (cx w) :=
    ((B0581.velNe c).restrictScalars ℝ).map_smul a (cx w)
  rw [heq (a • w) haw0, heq w hw0, cx.map_smul, hsm,
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.zeroVelLp_smul (by norm_num) a w hw0 haw0,
    smul_add]

private lemma velGradQ8_add_real (w z : B0579.X c 8) :
    B0583.velGradQ c (by norm_num) (w + z) =
      B0583.velGradQ c (by norm_num) w + B0583.velGradQ c (by norm_num) z := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 8 (by norm_num)
  have heq : ∀ u : B0579.X c 8, B0583.velGradQ c (by norm_num) u = B0583.gradQ c (cx u) := by
    intro u; unfold B0583.velGradQ; rw [gradQ_nonzeroPart_local c]; rfl
  rw [heq (w + z), heq w, heq z, cx.map_add, (B0583.gradQ c).map_add]

private lemma velGradQ8_smul_real (a : ℝ) (w : B0579.X c 8) :
    B0583.velGradQ c (by norm_num) (a • w) = a • B0583.velGradQ c (by norm_num) w := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 8 (by norm_num)
  have heq : ∀ u : B0579.X c 8, B0583.velGradQ c (by norm_num) u = B0583.gradQ c (cx u) := by
    intro u; unfold B0583.velGradQ; rw [gradQ_nonzeroPart_local c]; rfl
  have hsm : B0583.gradQ c (a • cx w) = a • B0583.gradQ c (cx w) :=
    ((B0583.gradQ c).restrictScalars ℝ).map_smul a (cx w)
  rw [heq (a • w), heq w, cx.map_smul, hsm]

private lemma velGradEta8_add_real (w z : B0579.X c 8)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (hz0 : ∫ x in B0579.cell c, z x = 0)
    (hwz0 : ∫ x in B0579.cell c, (w + z) x = 0) :
    B0583.velGradEta c (by norm_num) (w + z) hwz0 =
      B0583.velGradEta c (by norm_num) w hw0 + B0583.velGradEta c (by norm_num) z hz0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 8 (by norm_num)
  have heq : ∀ (u : B0579.X c 8) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velGradEta c (by norm_num) u hu0 =
        B0583.gradEta c (cx u) + B0583.zeroVelEtaLp c (by norm_num) u hu0 := by
    intro u hu0; unfold B0583.velGradEta; rw [gradEta_nonzeroPart_local c]; rfl
  rw [heq (w + z) hwz0, heq w hw0, heq z hz0, cx.map_add, (B0583.gradEta c).map_add,
    zeroVelEtaLp8_add c w z hw0 hz0 hwz0]
  abel

private lemma velGradEta8_smul_real (a : ℝ) (w : B0579.X c 8)
    (hw0 : ∫ x in B0579.cell c, w x = 0) (haw0 : ∫ x in B0579.cell c, (a • w) x = 0) :
    B0583.velGradEta c (by norm_num) (a • w) haw0 =
      a • B0583.velGradEta c (by norm_num) w hw0 := by
  let cx := UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.complexifyXCLM c 8 (by norm_num)
  have heq : ∀ (u : B0579.X c 8) (hu0 : ∫ x in B0579.cell c, u x = 0),
      B0583.velGradEta c (by norm_num) u hu0 =
        B0583.gradEta c (cx u) + B0583.zeroVelEtaLp c (by norm_num) u hu0 := by
    intro u hu0; unfold B0583.velGradEta; rw [gradEta_nonzeroPart_local c]; rfl
  have hsm : B0583.gradEta c (a • cx w) = a • B0583.gradEta c (cx w) :=
    ((B0583.gradEta c).restrictScalars ℝ).map_smul a (cx w)
  rw [heq (a • w) haw0, heq w hw0, cx.map_smul, hsm,
    zeroVelEtaLp8_smul c a w hw0 haw0, smul_add]

private def velRCLM : ZC8 c →L[ℝ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W =>
        B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W) +
          Complex.I • B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
      map_add' := fun W₁ W₂ => by
        have hre : reLp8 c (W₁ + W₂).1 = reLp8 c W₁.1 + reLp8 c W₂.1 := (reLp8 c).map_add W₁.1 W₂.1
        have him : imLp8 c (W₁ + W₂).1 = imLp8 c W₁.1 + imLp8 c W₂.1 := (imLp8 c).map_add W₁.1 W₂.1
        have h1 : B0583.velocity c (by norm_num) (reLp8 c (W₁ + W₂).1) (zc8_circRe_zero c (W₁ + W₂)) =
            B0583.velocity c (by norm_num) (reLp8 c W₁.1) (zc8_circRe_zero c W₁) +
              B0583.velocity c (by norm_num) (reLp8 c W₂.1) (zc8_circRe_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (reLp8 c W₁.1 + reLp8 c W₂.1) x = 0 := by
            rw [← hre]; exact zc8_circRe_zero c (W₁ + W₂)
          simpa [hre] using velocity8_add_real c (reLp8 c W₁.1) (reLp8 c W₂.1)
            (zc8_circRe_zero c W₁) (zc8_circRe_zero c W₂) hc12
        have h2 : B0583.velocity c (by norm_num) (imLp8 c (W₁ + W₂).1) (zc8_circIm_zero c (W₁ + W₂)) =
            B0583.velocity c (by norm_num) (imLp8 c W₁.1) (zc8_circIm_zero c W₁) +
              B0583.velocity c (by norm_num) (imLp8 c W₂.1) (zc8_circIm_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (imLp8 c W₁.1 + imLp8 c W₂.1) x = 0 := by
            rw [← him]; exact zc8_circIm_zero c (W₁ + W₂)
          simpa [him] using velocity8_add_real c (imLp8 c W₁.1) (imLp8 c W₂.1)
            (zc8_circIm_zero c W₁) (zc8_circIm_zero c W₂) hc12
        rw [h1, h2, smul_add]; abel
      map_smul' := fun a W => by
        simp only [RingHom.id_apply]
        have haW : (a • W : ZC8 c).1 = a • W.1 := rfl
        have hre : reLp8 c (a • W : ZC8 c).1 = a • reLp8 c W.1 := by rw [haW, (reLp8 c).map_smul]
        have him : imLp8 c (a • W : ZC8 c).1 = a • imLp8 c W.1 := by rw [haW, (imLp8 c).map_smul]
        have h1 : B0583.velocity c (by norm_num) (reLp8 c (a • W : ZC8 c).1) (zc8_circRe_zero c (a • W)) =
            a • B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W) := by
          have hca : ∫ x in B0579.cell c, (a • reLp8 c W.1) x = 0 := by
            rw [← hre]; exact zc8_circRe_zero c (a • W)
          simpa [hre] using velocity8_smul_real c a (reLp8 c W.1) (zc8_circRe_zero c W) hca
        have h2 : B0583.velocity c (by norm_num) (imLp8 c (a • W : ZC8 c).1) (zc8_circIm_zero c (a • W)) =
            a • B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W) := by
          have hca : ∫ x in B0579.cell c, (a • imLp8 c W.1) x = 0 := by
            rw [← him]; exact zc8_circIm_zero c (a • W)
          simpa [him] using velocity8_smul_real c a (imLp8 c W.1) (zc8_circIm_zero c W) hca
        rw [h1, h2, smul_comm Complex.I a, smul_add] }
    (2 * (c / (2 * Real.pi) + 2))
    (fun W => by
      have hcpos : 0 < c := hc.out
      have hC : 0 ≤ c / (2 * Real.pi) + 2 := by positivity
      calc ‖B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W) +
              Complex.I • B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)‖
          ≤ ‖B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)‖ +
              ‖B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)‖ := by
            refine (norm_add_le _ _).trans_eq ?_; rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ (c / (2 * Real.pi) + 2) * ‖reLp8 c W.1‖ + (c / (2 * Real.pi) + 2) * ‖imLp8 c W.1‖ :=
            add_le_add (B0583.norm_velocity_le c (by norm_num) _ _)
              (B0583.norm_velocity_le c (by norm_num) _ _)
        _ ≤ (c / (2 * Real.pi) + 2) * ‖W.1‖ + (c / (2 * Real.pi) + 2) * ‖W.1‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_reLp8_le c W.1) hC)
              (mul_le_mul_of_nonneg_left (norm_imLp8_le c W.1) hC)
        _ = 2 * (c / (2 * Real.pi) + 2) * ‖W‖ := by change _ = _ * ‖W.1‖; ring)

private def gqRCLM : ZC8 c →L[ℝ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W =>
        B0583.velGradQ c (by norm_num) (reLp8 c W.1) +
          Complex.I • B0583.velGradQ c (by norm_num) (imLp8 c W.1)
      map_add' := fun W₁ W₂ => by
        change B0583.velGradQ c (by norm_num) (reLp8 c (W₁.1 + W₂.1)) +
            Complex.I • B0583.velGradQ c (by norm_num) (imLp8 c (W₁.1 + W₂.1)) = _
        rw [(reLp8 c).map_add, (imLp8 c).map_add, velGradQ8_add_real c, velGradQ8_add_real c, smul_add]
        abel
      map_smul' := fun a W => by
        simp only [RingHom.id_apply]
        change B0583.velGradQ c (by norm_num) (reLp8 c ((a : ℝ) • W.1)) +
            Complex.I • B0583.velGradQ c (by norm_num) (imLp8 c ((a : ℝ) • W.1)) = _
        rw [(reLp8 c).map_smul, (imLp8 c).map_smul, velGradQ8_smul_real c, velGradQ8_smul_real c,
          smul_comm Complex.I a, smul_add] }
    2
    (fun W => by
      calc ‖B0583.velGradQ c (by norm_num) (reLp8 c W.1) +
              Complex.I • B0583.velGradQ c (by norm_num) (imLp8 c W.1)‖
          ≤ ‖B0583.velGradQ c (by norm_num) (reLp8 c W.1)‖ +
              ‖B0583.velGradQ c (by norm_num) (imLp8 c W.1)‖ := by
            refine (norm_add_le _ _).trans_eq ?_; rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ ‖reLp8 c W.1‖ + ‖imLp8 c W.1‖ :=
            add_le_add (B0583.norm_velGradQ_le c (by norm_num) _)
              (B0583.norm_velGradQ_le c (by norm_num) _)
        _ ≤ ‖W.1‖ + ‖W.1‖ := add_le_add (norm_reLp8_le c W.1) (norm_imLp8_le c W.1)
        _ = 2 * ‖W‖ := by change _ = 2 * ‖W.1‖; ring)

private def geRCLM : ZC8 c →L[ℝ] Lp B0581.Vel 2 (B0581.cellVol c) :=
  LinearMap.mkContinuous
    { toFun := fun W =>
        B0583.velGradEta c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W) +
          Complex.I • B0583.velGradEta c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
      map_add' := fun W₁ W₂ => by
        have hre : reLp8 c (W₁ + W₂).1 = reLp8 c W₁.1 + reLp8 c W₂.1 := (reLp8 c).map_add W₁.1 W₂.1
        have him : imLp8 c (W₁ + W₂).1 = imLp8 c W₁.1 + imLp8 c W₂.1 := (imLp8 c).map_add W₁.1 W₂.1
        have h1 : B0583.velGradEta c (by norm_num) (reLp8 c (W₁ + W₂).1) (zc8_circRe_zero c (W₁ + W₂)) =
            B0583.velGradEta c (by norm_num) (reLp8 c W₁.1) (zc8_circRe_zero c W₁) +
              B0583.velGradEta c (by norm_num) (reLp8 c W₂.1) (zc8_circRe_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (reLp8 c W₁.1 + reLp8 c W₂.1) x = 0 := by
            rw [← hre]; exact zc8_circRe_zero c (W₁ + W₂)
          simpa [hre] using velGradEta8_add_real c (reLp8 c W₁.1) (reLp8 c W₂.1)
            (zc8_circRe_zero c W₁) (zc8_circRe_zero c W₂) hc12
        have h2 : B0583.velGradEta c (by norm_num) (imLp8 c (W₁ + W₂).1) (zc8_circIm_zero c (W₁ + W₂)) =
            B0583.velGradEta c (by norm_num) (imLp8 c W₁.1) (zc8_circIm_zero c W₁) +
              B0583.velGradEta c (by norm_num) (imLp8 c W₂.1) (zc8_circIm_zero c W₂) := by
          have hc12 : ∫ x in B0579.cell c, (imLp8 c W₁.1 + imLp8 c W₂.1) x = 0 := by
            rw [← him]; exact zc8_circIm_zero c (W₁ + W₂)
          simpa [him] using velGradEta8_add_real c (imLp8 c W₁.1) (imLp8 c W₂.1)
            (zc8_circIm_zero c W₁) (zc8_circIm_zero c W₂) hc12
        rw [h1, h2, smul_add]; abel
      map_smul' := fun a W => by
        simp only [RingHom.id_apply]
        have haW : (a • W : ZC8 c).1 = a • W.1 := rfl
        have hre : reLp8 c (a • W : ZC8 c).1 = a • reLp8 c W.1 := by rw [haW, (reLp8 c).map_smul]
        have him : imLp8 c (a • W : ZC8 c).1 = a • imLp8 c W.1 := by rw [haW, (imLp8 c).map_smul]
        have h1 : B0583.velGradEta c (by norm_num) (reLp8 c (a • W : ZC8 c).1) (zc8_circRe_zero c (a • W)) =
            a • B0583.velGradEta c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W) := by
          have hca : ∫ x in B0579.cell c, (a • reLp8 c W.1) x = 0 := by
            rw [← hre]; exact zc8_circRe_zero c (a • W)
          simpa [hre] using velGradEta8_smul_real c a (reLp8 c W.1) (zc8_circRe_zero c W) hca
        have h2 : B0583.velGradEta c (by norm_num) (imLp8 c (a • W : ZC8 c).1) (zc8_circIm_zero c (a • W)) =
            a • B0583.velGradEta c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W) := by
          have hca : ∫ x in B0579.cell c, (a • imLp8 c W.1) x = 0 := by
            rw [← him]; exact zc8_circIm_zero c (a • W)
          simpa [him] using velGradEta8_smul_real c a (imLp8 c W.1) (zc8_circIm_zero c W) hca
        rw [h1, h2, smul_comm Complex.I a, smul_add] }
    4
    (fun W => by
      calc ‖B0583.velGradEta c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W) +
              Complex.I • B0583.velGradEta c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)‖
          ≤ ‖B0583.velGradEta c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)‖ +
              ‖B0583.velGradEta c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)‖ := by
            refine (norm_add_le _ _).trans_eq ?_; rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ 2 * ‖reLp8 c W.1‖ + 2 * ‖imLp8 c W.1‖ :=
            add_le_add (B0583.norm_velGradEta_le c (by norm_num) _ _)
              (B0583.norm_velGradEta_le c (by norm_num) _ _)
        _ ≤ 2 * ‖W.1‖ + 2 * ‖W.1‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_reLp8_le c W.1) (by norm_num))
              (mul_le_mul_of_nonneg_left (norm_imLp8_le c W.1) (by norm_num))
        _ = 4 * ‖W‖ := by change _ = 4 * ‖W.1‖; ring)

private lemma isBiotSavart_velRCLM (W : ZC8 c) :
    IsBiotSavart c (W.1 : ℝ × ℝ → ℂ) (fun x i => (velRCLM c W : B0579.Plane → B0581.Vel) x i) := by
  let U₁ := B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)
  let U₂ := B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
  let u₁ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (U₁ : B0579.Plane → B0581.Vel) x i
  let u₂ : ℝ × ℝ → Fin 2 → ℂ := fun x i => (U₂ : B0579.Plane → B0581.Vel) x i
  let u_sum : ℝ × ℝ → Fin 2 → ℂ := fun x i => u₁ x i + Complex.I * u₂ x i
  obtain ⟨hm₁, hdiv₁, hcurl₁⟩ :=
    CTE.velocityIsBiotSavart c 8 (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)
  obtain ⟨hm₂, hdiv₂, hcurl₂⟩ :=
    CTE.velocityIsBiotSavart c 8 (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
  have hae_vel : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (fun i => (velRCLM c W : B0579.Plane → B0581.Vel) x i) = u_sum x := by
    have h1 : velRCLM c W = U₁ + Complex.I • U₂ := rfl
    rw [h1]
    filter_upwards [Lp.coeFn_add U₁ (Complex.I • U₂), Lp.coeFn_smul Complex.I U₂] with x hx1 hx2
    funext i; rw [hx1, Pi.add_apply, hx2]; rfl
  have ae₁ := (B0579.ac_cellMeasure c 8).ae_le (coeFn_reLp8 c W.1)
  have ae₂ := (B0579.ac_cellMeasure c 8).ae_le (coeFn_imLp8 c W.1)
  refine ⟨fun j => BiotSavartH1Aux.memLp_lp_coord (velRCLM c W) j, ?_, ?_⟩
  · intro ψ hψ
    have hA : IntegrableOn
        (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 0)).add
        (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 1))
    have hB : IntegrableOn
        (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 0)).add
        (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 1))
    have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (velRCLM c W x 0 * (B0579.pd 0 ψ x : ℂ) + velRCLM c W x 1 * (B0579.pd 1 ψ x : ℂ)) =
          (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) +
            Complex.I * (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      filter_upwards [hae_vel] with x hx
      have hx0 := congrFun hx 0; have hx1 := congrFun hx 1
      dsimp [u_sum] at hx0 hx1; rw [hx0, hx1]; ring
    rw [integral_congr_ae hcongr, integral_add hA (hB.const_mul Complex.I), integral_const_mul,
      hdiv₁ ψ hψ, hdiv₂ ψ hψ]
    ring
  · intro ψ hψ
    have hI1 : IntegrableOn
        (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 0 (hψ.pd 1)).sub
        (CTE.T20_7.integrableOn_comp_test u₁ hm₁ 1 (hψ.pd 0))
    have hI2 : IntegrableOn
        (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell c) :=
      (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 0 (hψ.pd 1)).sub
        (CTE.T20_7.integrableOn_comp_test u₂ hm₂ 1 (hψ.pd 0))
    have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (W.1 : ℝ × ℝ → ℂ) x * (ψ x : ℂ) = ((reLp8 c W.1 x : ℝ) : ℂ) * (ψ x : ℂ) +
          Complex.I * (((imLp8 c W.1 x : ℝ) : ℂ) * (ψ x : ℂ)) := by
      filter_upwards [ae₁, ae₂] with x h₁ h₂
      simp only [h₁, h₂]
      conv_lhs => rw [← Complex.re_add_im (W.1 x)]
      ring
    have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        (velRCLM c W x 0 * (B0579.pd 1 ψ x : ℂ) - velRCLM c W x 1 * (B0579.pd 0 ψ x : ℂ)) =
          (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) +
            Complex.I * (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      filter_upwards [hae_vel] with x hx
      have hx0 := congrFun hx 0; have hx1 := congrFun hx 1
      dsimp [u_sum] at hx0 hx1; rw [hx0, hx1]; ring
    have hJ1 : IntegrableOn (fun x => ((reLp8 c W.1 x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) :=
      CTE.T20_7.integrableOn_X_test_complex (reLp8 c W.1) hψ
    have hJ2 : IntegrableOn (fun x => ((imLp8 c W.1 x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) :=
      CTE.T20_7.integrableOn_X_test_complex (imLp8 c W.1) hψ
    rw [integral_congr_ae hpt, integral_add hJ1 (hJ2.const_mul Complex.I),
      integral_const_mul, hcurl₁ ψ hψ, hcurl₂ ψ hψ,
      integral_congr_ae hcongr, integral_add hI1 (hI2.const_mul Complex.I), integral_const_mul]

private lemma hasWeakCellDerivC_velRCLM_q (W : ZC8 c) (i : Fin 2) :
    HasWeakCellDerivC c 0 (fun x => (velRCLM c W : B0579.Plane → B0581.Vel) x i)
      (fun x => (gqRCLM c W : B0579.Plane → B0581.Vel) x i) := by
  set U₁ := B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)
  set U₂ := B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
  set GQ₁ := B0583.velGradQ c (by norm_num) (reLp8 c W.1)
  set GQ₂ := B0583.velGradQ c (by norm_num) (imLp8 c W.1)
  have h0 := BiotSavartH1Aux.hasWeakCellDerivC_add_I 0
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 0 U₁ GQ₁
      (B0583.hasWeakVelDeriv_velocity_q c (by norm_num) _ _) i)
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 0 U₂ GQ₂
      (B0583.hasWeakVelDeriv_velocity_q c (by norm_num) _ _) i)
  refine HasWeakCellDerivC.congr_ae ?_ ?_ h0
  · filter_upwards [Lp.coeFn_add U₁ (Complex.I • U₂), Lp.coeFn_smul Complex.I U₂] with x hx1 hx2
    change (U₁ + Complex.I • U₂ : Lp _ _ _) x i = U₁ x i + Complex.I * U₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl
  · filter_upwards [Lp.coeFn_add GQ₁ (Complex.I • GQ₂), Lp.coeFn_smul Complex.I GQ₂] with x hx1 hx2
    change (GQ₁ + Complex.I • GQ₂ : Lp _ _ _) x i = GQ₁ x i + Complex.I * GQ₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl

private lemma hasWeakCellDerivC_velRCLM_eta (W : ZC8 c) (i : Fin 2) :
    HasWeakCellDerivC c 1 (fun x => (velRCLM c W : B0579.Plane → B0581.Vel) x i)
      (fun x => (geRCLM c W : B0579.Plane → B0581.Vel) x i) := by
  set U₁ := B0583.velocity c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)
  set U₂ := B0583.velocity c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
  set GE₁ := B0583.velGradEta c (by norm_num) (reLp8 c W.1) (zc8_circRe_zero c W)
  set GE₂ := B0583.velGradEta c (by norm_num) (imLp8 c W.1) (zc8_circIm_zero c W)
  have h1 := BiotSavartH1Aux.hasWeakCellDerivC_add_I 1
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 1 U₁ GE₁
      (B0583.hasWeakVelDeriv_velocity_eta c (by norm_num) _ _) i)
    (BiotSavartH1Aux.hasWeakCellDerivC_of_velDeriv 1 U₂ GE₂
      (B0583.hasWeakVelDeriv_velocity_eta c (by norm_num) _ _) i)
  refine HasWeakCellDerivC.congr_ae ?_ ?_ h1
  · filter_upwards [Lp.coeFn_add U₁ (Complex.I • U₂), Lp.coeFn_smul Complex.I U₂] with x hx1 hx2
    change (U₁ + Complex.I • U₂ : Lp _ _ _) x i = U₁ x i + Complex.I * U₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl
  · filter_upwards [Lp.coeFn_add GE₁ (Complex.I • GE₂), Lp.coeFn_smul Complex.I GE₂] with x hx1 hx2
    change (GE₁ + Complex.I • GE₂ : Lp _ _ _) x i = GE₁ x i + Complex.I * GE₂ x i
    rw [hx1, Pi.add_apply, hx2]; rfl

end BiotSavartRCLM

/-! ### Clamped shift and flat-test helpers -/

private def clampTau (H' τ : ℝ) : ℝ := max 0 (min τ H')

private lemma continuous_clampTau (H' : ℝ) : Continuous (clampTau H') :=
  continuous_const.max (continuous_id.min continuous_const)

private lemma clampTau_mem_Icc {H' : ℝ} (hH' : 0 ≤ H') (τ : ℝ) :
    clampTau H' τ ∈ Icc 0 H' :=
  ⟨le_max_left _ _, max_le hH' (min_le_right _ _)⟩

private lemma clampTau_eq_of_mem {H' τ : ℝ} (hτ : τ ∈ Icc 0 H') :
    clampTau H' τ = τ := by
  unfold clampTau
  rw [min_eq_left hτ.2, max_eq_right hτ.1]

private lemma pd_eq_of_eventuallyEq {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h : f =ᶠ[𝓝 x] g) (k : Fin 2) : B0579.pd k f x = B0579.pd k g x := by
  unfold B0579.pd; rw [h.fderiv_eq]

private lemma pd_eq_zero_of_eventuallyEq {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h : f =ᶠ[𝓝 x] 0) (k : Fin 2) : B0579.pd k f x = 0 := by
  unfold B0579.pd; rw [h.fderiv_eq]; simp

private lemma norm_le_vnorm2_local (v : Fin 2 → ℂ) (i : Fin 2) :
    ‖v i‖ ≤ vnorm2 v := by
  rw [← Real.sqrt_sq (norm_nonneg (v i))]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_two]
  fin_cases i
  · change ‖v 0‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2; linarith [sq_nonneg ‖v 1‖]
  · change ‖v 1‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2; linarith [sq_nonneg ‖v 0‖]

private lemma deriv_pd_comm {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (j : Fin 2) (τ : ℝ) (x : ℝ × ℝ) :
    deriv (fun τ' => B0579.pd j (ψ τ') x) τ =
      B0579.pd j (fun y => deriv (fun τ' => ψ τ' y) τ) x := by
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun p => ψ p.1 p.2
  set v₁ : ℝ × (ℝ × ℝ) := (1, (0, 0))
  set v₂ : ℝ × (ℝ × ℝ) := (0, B0579.dir j)
  have hΨ_diff : Differentiable ℝ Ψ := hψ.differentiable (by simp)
  have hfd_diff : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h_pd : ∀ τ' : ℝ, B0579.pd j (ψ τ') x = fderiv ℝ Ψ (τ', x) v₂ := by
    intro τ'; unfold B0579.pd
    have hcomp : HasFDerivAt (ψ τ')
        ((fderiv ℝ Ψ (τ', x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
      (hΨ_diff (τ', x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right τ' x)
    rw [hcomp.fderiv]; rfl
  have h_dt : ∀ y : ℝ × ℝ, deriv (fun τ' => ψ τ' y) τ = fderiv ℝ Ψ (τ, y) v₁ := by
    intro y
    have h1 : HasDerivAt (fun τ' : ℝ => (τ', y)) v₁ τ :=
      (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
    exact ((hΨ_diff (τ, y)).hasFDerivAt.comp_hasDerivAt τ h1).deriv
  simp_rw [h_pd, h_dt]
  have hLHS : HasDerivAt (fun τ' => fderiv ℝ Ψ (τ', x) v₂)
      (fderiv ℝ (fderiv ℝ Ψ) (τ, x) v₁ v₂) τ := by
    have h1 : HasDerivAt (fun τ' : ℝ => (τ', x)) v₁ τ :=
      (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
    have h2 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p v₂)
        ((ContinuousLinearMap.apply ℝ ℝ v₂).comp (fderiv ℝ (fderiv ℝ Ψ) (τ, x))) (τ, x) :=
      (ContinuousLinearMap.apply ℝ ℝ v₂).hasFDerivAt.comp (τ, x) (hfd_diff (τ, x)).hasFDerivAt
    exact h2.comp_hasDerivAt τ h1
  have hRHS : B0579.pd j (fun y => fderiv ℝ Ψ (τ, y) v₁) x =
      fderiv ℝ (fderiv ℝ Ψ) (τ, x) v₂ v₁ := by
    unfold B0579.pd
    have h2 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ψ p v₁)
        ((ContinuousLinearMap.apply ℝ ℝ v₁).comp (fderiv ℝ (fderiv ℝ Ψ) (τ, x))) (τ, x) :=
      (ContinuousLinearMap.apply ℝ ℝ v₁).hasFDerivAt.comp (τ, x) (hfd_diff (τ, x)).hasFDerivAt
    have hcomp := h2.comp x (hasFDerivAt_prodMk_right τ x)
    exact DFunLike.congr_fun hcomp.fderiv (B0579.dir j)
  rw [hLHS.deriv, hRHS]
  exact ((hψ.contDiffAt (x := (τ, x))).isSymmSndFDerivAt (by simp)).eq v₁ v₂

private lemma isCylTest_slice {c R₁ : ℝ} {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + c, x.2) = ψ s x)
    (hband : ∀ s x, R₁ < |x.2| → ψ s x = 0) (τ : ℝ) :
    B0579.IsCylTest c (ψ τ) where
  smooth := hψ.comp (contDiff_const.prodMk contDiff_id)
  periodic x := hper τ x
  band := ⟨R₁, fun x hx => hband τ x hx⟩

private lemma isCylTest_dt_slice {c R₁ : ℝ} {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + c, x.2) = ψ s x)
    (hband : ∀ s x, R₁ < |x.2| → ψ s x = 0) (τ : ℝ) :
    B0579.IsCylTest c (fun x => deriv (fun τ' => ψ τ' x) τ) := by
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun p => ψ p.1 p.2
  have h_dt_eq : (fun x : ℝ × ℝ => deriv (fun τ' => ψ τ' x) τ) =
      fun x => fderiv ℝ Ψ (τ, x) (1, (0, 0)) := by
    funext x
    have h1 : HasDerivAt (fun τ' : ℝ => (τ', x)) (1, (0, 0)) τ :=
      (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
    exact ((hψ.differentiable (by simp) (τ, x)).hasFDerivAt.comp_hasDerivAt τ h1).deriv
  refine ⟨?_, ?_, ⟨R₁, ?_⟩⟩
  · rw [h_dt_eq]
    exact ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).comp
      (contDiff_const.prodMk contDiff_id)
  · intro x; simp only [hper _ x]
  · intro x hx
    have heq : (fun τ' => ψ τ' x) = fun _ => 0 := funext fun τ' => hband τ' x hx
    simp [heq]

private lemma contDiff_perpF_comp {ψ : ℝ → ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)) :
    ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => V1.perpF (ψ p.1) p.2 i) := by
  intro i
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

private lemma supp_perpF_comp {s₁ s₂ R₁ : ℝ} {ψ : ℝ → ℝ × ℝ → ℝ}
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
      exact pd_eq_zero_of_eventuallyEq
        (Filter.eventually_of_mem hUx fun y hy => hsupp s y (Or.inr (Or.inr hy))) k
  fin_cases i
  · exact hpd0 1
  · simp [V1.perpF_one, hpd0 0]

private lemma flatIntegrand_sub_test_zero (ν : ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ₁ Φ₂ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (h₁ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ₁ p.1 p.2 i))
    (h₂ : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ₂ p.1 p.2 i))
    (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν 0 (fun _ _ _ => 0) F b (fun s x i => Φ₁ s x i - Φ₂ s x i) p =
      flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ₁ p -
        flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ₂ p := by
  have hdt : ∀ i : Fin 2, flatDt (fun s x i => Φ₁ s x i - Φ₂ s x i) p.1 p.2 i =
      flatDt Φ₁ p.1 p.2 i - flatDt Φ₂ p.1 p.2 i := by
    intro i; unfold flatDt
    exact deriv_sub
      (((h₁ i).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1)
      (((h₂ i).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1)
  have hgr : ∀ i j : Fin 2, flatGrad (fun s x i => Φ₁ s x i - Φ₂ s x i) p.1 p.2 i j =
      flatGrad Φ₁ p.1 p.2 i j - flatGrad Φ₂ p.1 p.2 i j := by
    intro i j; unfold flatGrad B0579.pd
    have hd1 : DifferentiableAt ℝ (fun y => Φ₁ p.1 y i) p.2 :=
      ((h₁ i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
    have hd2 : DifferentiableAt ℝ (fun y => Φ₂ p.1 y i) p.2 :=
      ((h₂ i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
    change (fderiv ℝ ((fun y => Φ₁ p.1 y i) - (fun y => Φ₂ p.1 y i)) p.2) (B0579.dir j) = _
    rw [fderiv_sub hd1 hd2, sub_apply]
  have hlp : ∀ i : Fin 2, flatLap (fun s x i => Φ₁ s x i - Φ₂ s x i) p.1 p.2 i =
      flatLap Φ₁ p.1 p.2 i - flatLap Φ₂ p.1 p.2 i := by
    intro i; unfold flatLap lapP
    have hc1 : ContDiff ℝ ∞ (fun y => Φ₁ p.1 y i) :=
      (h₁ i).comp (contDiff_const.prodMk contDiff_id)
    have hc2 : ContDiff ℝ ∞ (fun y => Φ₂ p.1 y i) :=
      (h₂ i).comp (contDiff_const.prodMk contDiff_id)
    have hpd_sub : ∀ k : Fin 2, B0579.pd k (fun y => Φ₁ p.1 y i - Φ₂ p.1 y i) =
        fun y => B0579.pd k (fun z => Φ₁ p.1 z i) y - B0579.pd k (fun z => Φ₂ p.1 z i) y := by
      intro k; funext y; unfold B0579.pd
      change (fderiv ℝ ((fun z => Φ₁ p.1 z i) - (fun z => Φ₂ p.1 z i)) y) (B0579.dir k) = _
      rw [fderiv_sub (hc1.differentiable (by simp) y) (hc2.differentiable (by simp) y), sub_apply]
    have hpd2 : ∀ k : Fin 2,
        B0579.pd k (fun y => B0579.pd k (fun z => Φ₁ p.1 z i) y -
          B0579.pd k (fun z => Φ₂ p.1 z i) y) p.2 =
        B0579.pd k (B0579.pd k (fun z => Φ₁ p.1 z i)) p.2 -
          B0579.pd k (B0579.pd k (fun z => Φ₂ p.1 z i)) p.2 := by
      intro k; unfold B0579.pd
      have d1 : DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => Φ₁ p.1 z i) y (B0579.dir k)) p.2 :=
        ((hc1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) p.2
      have d2 : DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => Φ₂ p.1 z i) y (B0579.dir k)) p.2 :=
        ((hc2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) p.2
      change (fderiv ℝ ((fun z => fderiv ℝ (fun w => Φ₁ p.1 w i) z (B0579.dir k)) -
        (fun z => fderiv ℝ (fun w => Φ₂ p.1 w i) z (B0579.dir k))) p.2) (B0579.dir k) = _
      rw [fderiv_sub d1 d2, sub_apply]
    rw [hpd_sub 0, hpd_sub 1, hpd2 0, hpd2 1]; ring
  simp only [flatIntegrand, hdt, hgr, hlp, Fin.sum_univ_two]
  push_cast; ring

private def etaPrim (R₀ : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ τ in (-(R₀ + 1))..x.2, Φ s (x.1, τ) 0

private lemma etaPrim_props {c s₁ s₂ R₀ : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
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
        DfcQPrimSmoothAux.ipsContDiff (ℝ × (ℝ × ℝ)) 0 1 n ℝ H_in (contDiff_infty.1 hH_in n)
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
      have hlt : R₀ < |τ| := by rw [abs_of_neg (by linarith [hτ.2, hR₀])]; linarith [hτ.2]
      exact hsupp s (x.1, τ) 0 (Or.inr (Or.inr hlt))
    rw [intervalIntegral.integral_congr h0]; simp
  have hpd1 : ∀ s x, B0579.pd 1 (etaPrim R₀ Φ s) x = Φ s x 0 := by
    intro s ⟨q, η⟩
    have hslice_sm : ContDiff ℝ ∞ (etaPrim R₀ Φ s) := hsm.comp (contDiff_const.prodMk contDiff_id)
    rw [DfcQPrimDerivAux.pd1_eq _ q η (hslice_sm.differentiable (by simp) (q, η))]
    have hfc : Continuous fun τ : ℝ => Φ s (q, τ) 0 :=
      (hΦ.smooth 0).continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    exact (intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt).deriv
  have hpd0 : ∀ s x, B0579.pd 0 (etaPrim R₀ Φ s) x = -Φ s x 1 := by
    intro s ⟨q, η⟩
    have hslice_sm : ContDiff ℝ ∞ (etaPrim R₀ Φ s) := hsm.comp (contDiff_const.prodMk contDiff_id)
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
          (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).differentiable (by simp) τ
      rw [DfcQPrimDerivAux.pd1_eq (fun y => Φ s y 1) q τ
        (((hΦ.smooth 1).comp (contDiff_const.prodMk contDiff_id)).differentiable
          (by simp) (q, τ))]
      exact hf1_τ.hasDerivAt.neg
    have hint_f1 : IntervalIntegrable
        (fun τ => -B0579.pd 1 (fun y => Φ s y 1) (q, τ)) volume (-(R₀ + 1)) η := by
      have hc1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B0579.pd 1 (fun y => Φ p.1 y 1) p.2) := by
        have heq : (fun p : ℝ × (ℝ × ℝ) => B0579.pd 1 (fun y => Φ p.1 y 1) p.2) =
            fun p => fderiv ℝ (fun q' : ℝ × (ℝ × ℝ) => Φ q'.1 q'.2 1) p (0, B0579.dir 1) := by
          funext p; unfold B0579.pd
          have hcomp := (((hΦ.smooth 1).differentiable (by simp) (p.1, p.2)).hasFDerivAt.comp p.2
            (hasFDerivAt_prodMk_right p.1 p.2))
          exact DFunLike.congr_fun hcomp.fderiv (B0579.dir 1)
        rw [heq]
        exact ((hΦ.smooth 1).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact ((hc1.continuous.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))).neg).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint_f1]
    have hbot1 : Φ s (q, -(R₀ + 1)) 1 = 0 :=
      hsupp s (q, -(R₀ + 1)) 1 (Or.inr (Or.inr (by rw [abs_of_neg (by linarith)]; linarith)))
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
        exact hsupp s (x.1, τ) 0 (Or.inr (Or.inr (by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.1])))
      rw [intervalIntegral.integral_congr h0]; simp
    rw [hsplit]
    set hq : ℝ → ℝ := fun q => etaPrim R₀ Φ s (q, R₀ + 1)
    have hq_diff : Differentiable ℝ hq :=
      (hsm.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).differentiable (by simp)
    have hq_deriv : ∀ q : ℝ, deriv hq q = 0 := by
      intro q
      have hslice_sm : ContDiff ℝ ∞ (etaPrim R₀ Φ s) := hsm.comp (contDiff_const.prodMk contDiff_id)
      rw [← DfcQPrimDerivAux.pd0_eq _ q (R₀ + 1) (hslice_sm.differentiable (by simp) (q, R₀ + 1)),
        hpd0 s (q, R₀ + 1)]
      have h0 : Φ s (q, R₀ + 1) 1 = 0 :=
        hsupp s (q, R₀ + 1) 1 (Or.inr (Or.inr (by rw [abs_of_pos (by linarith)]; linarith)))
      simp [h0]
    exact is_const_of_deriv_eq_zero hq_diff hq_deriv x.1 0
  exact ⟨hsm, hper, hts, hbot, hpd1, hpd0, htop⟩

/-! ### Integrability & vanishing of `flatIntegrand` for shifted linearised flow -/

private lemma integrableOn_flatIntegrand_supported {c ν H' s₁ s₂ R₁ M_E M_v : ℝ}
    (hc : 0 < c) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂H : s₂ < H') (hR₁ : 0 < R₁)
    (_hME : 0 ≤ M_E) (hMv : 0 ≤ M_v)
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hb_meas : ∀ i, Measurable fun p => b p i)
    (hF_meas : ∀ i j, Measurable fun p => F p i j)
    (hE_bd : ∀ τ, ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (τ, x)) ^ 2) ≤ ENNReal.ofReal M_E)
    (hF_bd : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Icc 0 H' → ∀ i j, ‖F p i j‖ ≤ 2 * M_v * vnorm2 (b p))
    {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hΦ_sm : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Φ p.1 p.2 i))
    (hΦ_supp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → Φ s x i = 0) :
    IntegrableOn (flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ p =
        ∫ p in Ioo (0 : ℝ) H' ×ˢ B0579.cell c, flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ p ∧
      IntegrableOn (fun p => vnorm2 (b p) ^ 2) (Icc s₁ s₂ ×ˢ B0579.cell c) := by
  set K_box : Set (ℝ × (ℝ × ℝ)) :=
    Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R₁) R₁)
  have hK_meas : MeasurableSet K_box :=
    measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
  have hK_sub_strip : K_box ⊆ Icc s₁ s₂ ×ˢ B0579.cell c :=
    prod_mono Subset.rfl (prod_mono Subset.rfl (subset_univ _))
  have hK_sub_Ioo : K_box ⊆ Ioo (0 : ℝ) H' ×ˢ B0579.cell c :=
    fun p hp => ⟨⟨lt_of_lt_of_le hs₁ hp.1.1, lt_of_le_of_lt hp.1.2 hs₂H⟩, hp.2.1, trivial⟩
  have hK_sub_Ioi : K_box ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
    hK_sub_Ioo.trans (prod_mono Ioo_subset_Ioi_self Subset.rfl)
  -- `b` is `L²` on `Icc s₁ s₂ ×ˢ cell c` and `L¹` on `K_box`
  have hb_norm_meas : Measurable fun p => vnorm2 (b p) := by
    unfold vnorm2
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum Finset.univ fun i _ => (hb_meas i).norm.pow_const 2)
  have hb_sq_int : IntegrableOn (fun p => vnorm2 (b p) ^ 2) (Icc s₁ s₂ ×ˢ B0579.cell c) := by
    refine ⟨(hb_norm_meas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _),
      Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod _ (hb_norm_meas.pow_const 2).ennreal_ofReal.aemeasurable]
    calc ∫⁻ τ in Icc s₁ s₂, ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (τ, x)) ^ 2)
        ≤ ∫⁻ _ in Icc s₁ s₂, ENNReal.ofReal M_E := lintegral_mono fun τ => hE_bd τ
      _ = ENNReal.ofReal M_E * volume (Icc s₁ s₂) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hvol_K : volume K_box < ⊤ := by
    dsimp [K_box]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hb_K_int : IntegrableOn (fun p => vnorm2 (b p)) K_box := by
    have h1 : IntegrableOn (fun p => 1 + vnorm2 (b p) ^ 2) K_box :=
      (integrableOn_const hvol_K.ne).add (hb_sq_int.mono_set hK_sub_strip)
    refine h1.mono' hb_norm_meas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hv_nn : 0 ≤ vnorm2 (b p) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg hv_nn]
    nlinarith [sq_nonneg (vnorm2 (b p) - 1)]
  -- Continuity of derivatives of `Φ`
  have hdt_cont : ∀ i, Continuous fun p : ℝ × (ℝ × ℝ) => flatDt Φ p.1 p.2 i := by
    intro i
    have heq : (fun p : ℝ × (ℝ × ℝ) => flatDt Φ p.1 p.2 i) =
        fun p => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => Φ q.1 q.2 i) p (1, (0, 0)) := by
      funext p; unfold flatDt
      have h1 : HasDerivAt (fun s' : ℝ => (s', p.2)) (1, (0, 0)) p.1 :=
        (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
      exact (((hΦ_sm i).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1 h1).deriv
    rw [heq]
    exact (((hΦ_sm i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hpd_sm : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (fun y => Φ p.1 y i) p.2) := by
    intro i j
    have heq : (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (fun y => Φ p.1 y i) p.2) =
        fun p => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => Φ q.1 q.2 i) p (0, B0579.dir j) := by
      funext p; unfold B0579.pd
      have hcomp := (((hΦ_sm i).differentiable (by simp) (p.1, p.2)).hasFDerivAt.comp p.2
        (hasFDerivAt_prodMk_right p.1 p.2))
      exact DFunLike.congr_fun hcomp.fderiv (B0579.dir j)
    rw [heq]
    exact ((hΦ_sm i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hgr_cont : ∀ i j, Continuous fun p : ℝ × (ℝ × ℝ) => flatGrad Φ p.1 p.2 i j :=
    fun i j => (hpd_sm i j).continuous
  have hlp_cont : ∀ i, Continuous fun p : ℝ × (ℝ × ℝ) => flatLap Φ p.1 p.2 i := by
    intro i
    have hpd2 : ∀ k : Fin 2, Continuous fun p : ℝ × (ℝ × ℝ) =>
        B0579.pd k (B0579.pd k (fun y => Φ p.1 y i)) p.2 := by
      intro k
      have heq : (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (B0579.pd k (fun y => Φ p.1 y i)) p.2) =
          fun p => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => B0579.pd k (fun y => Φ q.1 y i) q.2) p
            (0, B0579.dir k) := by
        funext p; unfold B0579.pd
        have hcomp := (((hpd_sm i k).differentiable (by simp) (p.1, p.2)).hasFDerivAt.comp p.2
          (hasFDerivAt_prodMk_right p.1 p.2))
        exact DFunLike.congr_fun hcomp.fderiv (B0579.dir k)
      rw [heq]
      exact (((hpd_sm i k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    unfold flatLap lapP
    exact (hpd2 0).add (hpd2 1)
  -- Measurability of `flatIntegrand`
  have hmeas_fi : Measurable (flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ) := by
    have hfi_eq : flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ = fun p =>
        ∑ i : Fin 2, (-(b p i * (flatDt Φ p.1 p.2 i : ℂ)) -
          (ν : ℂ) * b p i * (flatLap Φ p.1 p.2 i : ℂ) +
          ∑ j : Fin 2, F p i j * (flatGrad Φ p.1 p.2 i j : ℂ)) := by
      funext p; unfold flatIntegrand; simp
    rw [hfi_eq]
    refine Finset.measurable_sum Finset.univ fun i _ => ?_
    have hm1 : Measurable fun p : ℝ × (ℝ × ℝ) => -(b p i * (flatDt Φ p.1 p.2 i : ℂ)) :=
      ((hb_meas i).mul (Complex.continuous_ofReal.measurable.comp (hdt_cont i).measurable)).neg
    have hm3 : Measurable fun p : ℝ × (ℝ × ℝ) => (ν : ℂ) * b p i * (flatLap Φ p.1 p.2 i : ℂ) :=
      (measurable_const.mul (hb_meas i)).mul
        (Complex.continuous_ofReal.measurable.comp (hlp_cont i).measurable)
    have hm4 : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ∑ j : Fin 2, F p i j * (flatGrad Φ p.1 p.2 i j : ℂ) :=
      Finset.measurable_sum Finset.univ fun j _ =>
        (hF_meas i j).mul (Complex.continuous_ofReal.measurable.comp (hgr_cont i j).measurable)
    exact (hm1.sub hm3).add hm4
  -- Vanishing outside `K_box`
  have hzero_off : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ K_box,
      flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ p = 0 := by
    intro p hp
    have hout : p.1 < s₁ ∨ s₂ < p.1 ∨ R₁ < |p.2.2| := by
      by_contra hnot
      simp only [not_or, not_lt] at hnot
      exact hp.2 ⟨⟨hnot.1, hnot.2.1⟩, hp.1.2.1, abs_le.1 hnot.2.2⟩
    let U_out : Set (ℝ × (ℝ × ℝ)) := {q | q.1 < s₁ ∨ s₂ < q.1 ∨ R₁ < |q.2.2|}
    have hU_open : IsOpen U_out :=
      (isOpen_lt continuous_fst continuous_const).union
        ((isOpen_lt continuous_const continuous_fst).union
          (isOpen_lt continuous_const (continuous_abs.comp continuous_snd.snd)))
    have hU_mem := hU_open.mem_nhds hout
    have h0 : ∀ i, Φ p.1 p.2 i = 0 := fun i => hΦ_supp p.1 p.2 i hout
    have hdt0 : ∀ i, flatDt Φ p.1 p.2 i = 0 := by
      intro i; unfold flatDt
      have hev : (fun s' => Φ s' p.2 i) =ᶠ[𝓝 p.1] 0 :=
        Filter.eventually_of_mem ((continuousAt_id.prodMk continuousAt_const) hU_mem)
          fun s' hs' => hΦ_supp s' p.2 i hs'
      rw [hev.deriv_eq]; simp
    let V_x : Set (ℝ × ℝ) := {y | (p.1, y) ∈ U_out}
    have hVx_open : IsOpen V_x := hU_open.preimage (continuous_const.prodMk continuous_id)
    have hpd_zero_on : ∀ y ∈ V_x, ∀ i j, B0579.pd j (fun z => Φ p.1 z i) y = 0 := fun y hy i j =>
      pd_eq_zero_of_eventuallyEq
        (Filter.eventually_of_mem (hVx_open.mem_nhds hy) fun z hz => hΦ_supp p.1 z i hz) j
    have hgr0 : ∀ i j, flatGrad Φ p.1 p.2 i j = 0 := fun i j => hpd_zero_on p.2 hout i j
    have hlp0 : ∀ i, flatLap Φ p.1 p.2 i = 0 := by
      intro i; unfold flatLap lapP
      have hpd_ev : ∀ j, B0579.pd j (fun y => Φ p.1 y i) =ᶠ[𝓝 p.2] 0 := fun j =>
        Filter.eventually_of_mem (hVx_open.mem_nhds hout) fun y hy => hpd_zero_on y hy i j
      rw [pd_eq_zero_of_eventuallyEq (hpd_ev 0) 0, pd_eq_zero_of_eventuallyEq (hpd_ev 1) 1, add_zero]
    simp [flatIntegrand, h0, hdt0, hgr0, hlp0]
  -- Bound on `K_box`
  set K_cl : Set (ℝ × (ℝ × ℝ)) :=
    Icc s₁ s₂ ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R₁) R₁)
  have hKcl_compact : IsCompact K_cl :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_sub_cl : K_box ⊆ K_cl :=
    prod_mono Subset.rfl (prod_mono Ico_subset_Icc_self Subset.rfl)
  set φ_sup : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    ∑ i : Fin 2, (|flatDt Φ p.1 p.2 i| + |ν| * |flatLap Φ p.1 p.2 i| +
      2 * M_v * ∑ j : Fin 2, |flatGrad Φ p.1 p.2 i j|)
  have hφ_cont : Continuous φ_sup := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (((hdt_cont i).abs).add (continuous_const.mul ((hlp_cont i).abs))).add
      (continuous_const.mul (continuous_finsetSum _ fun j _ => (hgr_cont i j).abs))
  obtain ⟨C_Φ, hC_Φ⟩ := hKcl_compact.exists_bound_of_continuousOn hφ_cont.continuousOn
  have hC_Φ0 : 0 ≤ C_Φ := by
    have hp0 : (s₁, (0, 0)) ∈ K_cl :=
      ⟨⟨le_rfl, hs₁₂.le⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    exact (norm_nonneg _).trans (hC_Φ _ hp0)
  have hint_K : IntegrableOn (flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ) K_box := by
    refine (hb_K_int.const_mul C_Φ).mono' hmeas_fi.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hK_meas] with p hp
    have hp_Icc : p.1 ∈ Icc 0 H' := ⟨(hs₁.le.trans hp.1.1), hp.1.2.trans hs₂H.le⟩
    have hφ_le : φ_sup p ≤ C_Φ := by
      have h := hC_Φ p (hK_sub_cl hp)
      have hnn : 0 ≤ φ_sup p := Finset.sum_nonneg fun i _ => by
        refine add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))) ?_
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      rwa [Real.norm_of_nonneg hnn] at h
    calc ‖flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ p‖
        ≤ ∑ i : Fin 2, (‖b p i‖ * |flatDt Φ p.1 p.2 i| +
            |ν| * ‖b p i‖ * |flatLap Φ p.1 p.2 i| +
            ∑ j : Fin 2, ‖F p i j‖ * |flatGrad Φ p.1 p.2 i j|) := by
          unfold flatIntegrand
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          simp only [ zero_div, zero_mul, add_zero, Complex.ofReal_zero, mul_zero, sub_zero]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                Complex.norm_real, Real.norm_eq_abs]
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin 2, (vnorm2 (b p) * |flatDt Φ p.1 p.2 i| +
            |ν| * vnorm2 (b p) * |flatLap Φ p.1 p.2 i| +
            ∑ j : Fin 2, (2 * M_v * vnorm2 (b p)) * |flatGrad Φ p.1 p.2 i j|) := by
          refine Finset.sum_le_sum fun i _ => add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_of_nonneg_right (norm_le_vnorm2_local (b p) i) (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (norm_le_vnorm2_local (b p) i) (abs_nonneg _)) (abs_nonneg _)
          · exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (hF_bd p hp_Icc i j) (abs_nonneg _)
      _ = φ_sup p * vnorm2 (b p) := by
          dsimp [φ_sup]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fin.sum_univ_two, Fin.sum_univ_two]
          ring
      _ ≤ C_Φ * vnorm2 (b p) := mul_le_mul_of_nonneg_right hφ_le (Real.sqrt_nonneg _)
  have hint_Ioi : IntegrableOn (flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
    rw [← integrable_indicator_iff (measurableSet_Ioi.prod (B0579.measurableSet_cell c))]
    have heq : (Ioi (0 : ℝ) ×ˢ B0579.cell c).indicator (flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ) =
        K_box.indicator (flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ) := by
      funext p
      by_cases hp : p ∈ K_box
      · simp [hp, hK_sub_Ioi hp]
      · by_cases hp' : p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c
        · simp [hp, hp', hzero_off p ⟨hp', hp⟩]
        · simp [hp, hp']
    rw [heq, integrable_indicator_iff hK_meas]
    exact hint_K
  have heq_Ioo : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ p =
      ∫ p in Ioo (0 : ℝ) H' ×ˢ B0579.cell c, flatIntegrand ν 0 (fun _ _ _ => 0) F b Φ p := by
    have h1 := MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume)
      (measurableSet_Ioi.prod (B0579.measurableSet_cell c)).nullMeasurableSet
      hK_sub_Ioi (Eventually.of_forall hzero_off)
    have h2 := MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume)
      (measurableSet_Ioo.prod (B0579.measurableSet_cell c)).nullMeasurableSet
      hK_sub_Ioo (Eventually.of_forall fun p hp =>
        hzero_off p ⟨(Set.prod_mono Ioo_subset_Ioi_self Subset.rfl) hp.1, hp.2⟩)
    exact h1.trans h2.symm
  exact ⟨hint_Ioi, heq_Ioo, hb_sq_int⟩

private lemma shifted_perpF_slice_eq {ν s_r τ : ℝ} (hs_r : 0 ≤ s_r) (hτ : 0 < τ)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {b_s : ℝ × ℝ → Fin 2 → ℂ} {G_s : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    {w_ρ : ℝ × ℝ → ℂ} {u_ρ : ℝ × ℝ → Fin 2 → ℂ}
    (hb_bs : IsBiotSavart (ν ^ (-2 : ℝ)) w_ρ b_s)
    (hu_bs : IsBiotSavart (ν ^ (-2 : ℝ)) w_ρ u_ρ)
    (hb_wg : ∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j (fun x => b_s x i) (fun x => G_s x i j))
    (hw_l2 : MemLp w_ρ 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    {ψ : ℝ → ℝ × ℝ → ℝ} {R₁ : ℝ}
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x)
    (hband : ∀ s x, R₁ < |x.2| → ψ s x = 0)
    (hν : 0 < ν) :
    let c : ℝ := ν ^ (-2 : ℝ)
    let ρ : ℝ := s_r + τ
    let F_s : Fin 2 → Fin 2 → ℝ × ℝ → ℂ := fun i j x =>
      -((trainVel tr ρ x i : ℂ) * b_s x j + b_s x i * (trainVel tr ρ x j : ℂ))
    ∫ x in B0579.cell c,
        flatIntegrand ν 0 (fun _ _ _ => 0) (fun p i j => F_s i j p.2) (fun p => b_s p.2)
          (fun s y => V1.perpF (ψ s) y) (τ, x) =
      -((∫ x in B0579.cell c, flowIntegrand tr w_ρ u_ρ ρ (ψ τ) x) +
        ∫ x in B0579.cell c, w_ρ x * ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ)) := by
  intro c ρ F_s
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hmc := B0579.measurableSet_cell c
  have hφ : B0579.IsCylTest c (ψ τ) := isCylTest_slice hψ hper hband τ
  have hdtφ : B0579.IsCylTest c (fun y => deriv (fun τ' => ψ τ' y) τ) :=
    isCylTest_dt_slice hψ hper hband τ
  -- 1. Pointwise identity `flatIntegrand = -hInt (dt ψ) - jInt`
  have hpt_fi : ∀ x : ℝ × ℝ,
      flatIntegrand ν 0 (fun _ _ _ => 0) (fun p i j => F_s i j p.2) (fun p => b_s p.2)
          (fun s y => V1.perpF (ψ s) y) (τ, x) =
        -V1.hInt (fun q => b_s q.2) (fun y => deriv (fun τ' => ψ τ' y) τ) (ρ, x) -
          V1.jInt tr (fun q => b_s q.2) (V1.wF (fun _ _ => 0) (fun q => b_s q.2)) (ψ τ) (ρ, x) := by
    intro x
    have hdt0 : flatDt (fun s y => V1.perpF (ψ s) y) τ x 0 =
        V1.perpF (fun y => deriv (fun τ' => ψ τ' y) τ) x 0 := by
      unfold flatDt; simp only [V1.perpF_zero]; exact deriv_pd_comm hψ 1 τ x
    have hdt1 : flatDt (fun s y => V1.perpF (ψ s) y) τ x 1 =
        V1.perpF (fun y => deriv (fun τ' => ψ τ' y) τ) x 1 := by
      unfold flatDt; simp only [V1.perpF_one]
      change deriv (-(fun s' => B0579.pd 0 (ψ s') x)) τ = _
      rw [deriv.neg, deriv_pd_comm hψ 0 τ x]
    unfold flatIntegrand V1.hInt V1.jInt V1.wF
    dsimp only [F_s]
    simp only [Fin.sum_univ_two, hdt0, hdt1, flatGrad, flatLap, Complex.ofReal_zero]
    ring
  -- 2. First term: `∫ hInt (dt ψ) = ∫ w_ρ * dt ψ`
  have hI_dt : IntegrableOn
      (fun x => V1.hInt (fun q => b_s q.2) (fun y => deriv (fun τ' => ψ τ' y) τ) (ρ, x))
      (B0579.cell c) ∧
      ∫ x in B0579.cell c,
        V1.hInt (fun q => b_s q.2) (fun y => deriv (fun τ' => ψ τ' y) τ) (ρ, x) =
      ∫ x in B0579.cell c, w_ρ x * ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ) := by
    have heq : (fun x => V1.hInt (fun q => b_s q.2) (fun y => deriv (fun τ' => ψ τ' y) τ) (ρ, x)) =
        fun x => b_s x 0 * (B0579.pd 1 (fun y => deriv (fun τ' => ψ τ' y) τ) x : ℂ) -
          b_s x 1 * (B0579.pd 0 (fun y => deriv (fun τ' => ψ τ' y) τ) x : ℂ) := by
      funext x; simp [V1.hInt, Fin.sum_univ_two, V1.perpF_zero, V1.perpF_one]; ring
    rw [heq]
    exact ⟨(((hb_wg 0 1).1 _ hdtφ).1).sub (((hb_wg 1 0).1 _ hdtφ).1),
      (hb_bs.2.2 _ hdtφ).symm⟩
  -- 3. Second term: `V1.pointwise_TI` at `γ = 0`, `μ' = 0`, `b₀ = 0`, `G₀ = 0`
  have hwk_iz : ∀ (i j : Fin 2) {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ),
      V1.IZ c (fun x => G_s x i j * (χ x : ℂ) + b_s x i * (B0579.pd j χ x : ℂ)) := by
    intro i j χ hχ
    obtain ⟨h1, h2⟩ := (hb_wg i j).1 χ hχ
    exact ⟨h2.add h1, by rw [integral_add h2 h1, (hb_wg i j).2 χ hχ]; ring⟩
  have hdv_iz : ∀ {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ),
      V1.IZ c (fun x => b_s x 0 * (B0579.pd 0 χ x : ℂ) + b_s x 1 * (B0579.pd 1 χ x : ℂ)) :=
    fun hχ => ⟨(((hb_wg 0 0).1 _ hχ).1).add (((hb_wg 1 1).1 _ hχ).1), hb_bs.2.1 _ hχ⟩
  have hzero_iz : V1.IZ c (fun _ => (0 : ℂ)) := ⟨integrableOn_zero, by simp⟩
  have hZs_IZ : V1.IZ c
      (V1.Zs tr (fun _ _ => 0) (fun q => b_s q.2) (fun _ _ _ => 0) (fun q => G_s q.2) ρ (ψ τ)) := by
    have hψ_t := V1.psiF_test tr hρ.le hφ
    have hwk0 : ∀ (i j : Fin 2) (χ : ℝ × ℝ → ℝ),
        V1.Wk (fun _ _ _ => (0 : ℂ)) (fun _ _ => (0 : ℂ)) ρ i j χ = fun _ => 0 := by
      intro i j χ; funext x; simp [V1.Wk]
    have hdv0 : ∀ (χ : ℝ × ℝ → ℝ),
        V1.Dv (fun _ _ => (0 : ℂ)) ρ χ = fun _ => 0 := by
      intro χ; funext x; simp [V1.Dv]
    unfold V1.Zs
    refine ((((((((((hwk_iz 1 0 hψ_t).sub ?_).sub (hwk_iz 0 1 hψ_t)).add ?_).add ?_).add ?_).sub ?_).sub ?_).sub
      (hdv_iz (V1.chiwF_test tr hρ.le hφ))).add ?_).sub ?_
    all_goals
      first
      | (rw [hwk0]; exact hzero_iz)
      | (rw [hdv0]; exact hzero_iz)
  obtain ⟨R, hR⟩ := hφ.band
  have hB : V1.Band R (ψ τ) := hR
  have hB0 : V1.Band R (B0579.pd 0 (ψ τ)) := hB.pd 0
  have hB1 : V1.Band R (B0579.pd 1 (ψ τ)) := hB.pd 1
  have hJ_int : IntegrableOn
      (fun x => V1.jInt tr (fun q => b_s q.2) (V1.wF (fun _ _ => 0) (fun q => b_s q.2)) (ψ τ) (ρ, x))
      (B0579.cell c) := by
    have cL : ∀ j : Fin 2, Continuous (lapP (B0579.pd j (ψ τ))) := fun j =>
      (V1.cylTest_lapP (hφ.pd j)).continuous
    have cf : ∀ i j : Fin 2, Continuous (B0579.pd i (B0579.pd j (ψ τ))) := fun i j =>
      ((hφ.pd j).pd i).continuous
    have cv : ∀ k : Fin 2, Continuous (V1.vC tr ρ k) :=
      fun k => (V1.vC_contDiff tr hρ.le k).continuous
    have bL0 : V1.Band R (lapP (B0579.pd 0 (ψ τ))) := hB0.lapP
    have bL1 : V1.Band R (lapP (B0579.pd 1 (ψ τ))) := hB1.lapP
    have b00 : V1.Band R (B0579.pd 0 (B0579.pd 0 (ψ τ))) := hB0.pd 0
    have b10 : V1.Band R (B0579.pd 1 (B0579.pd 0 (ψ τ))) := hB0.pd 1
    have b01 : V1.Band R (B0579.pd 0 (B0579.pd 1 (ψ τ))) := hB1.pd 0
    have b11 : V1.Band R (B0579.pd 1 (B0579.pd 1 (ψ τ))) := hB1.pd 1
    set M0 : ℝ × ℝ → ℝ := fun x => ν * lapP (B0579.pd 1 (ψ τ)) x +
      2 * V1.vC tr ρ 0 x * B0579.pd 0 (B0579.pd 1 (ψ τ)) x +
      V1.vC tr ρ 1 x * B0579.pd 1 (B0579.pd 1 (ψ τ)) x -
      V1.vC tr ρ 1 x * B0579.pd 0 (B0579.pd 0 (ψ τ)) x with hM0
    set M1 : ℝ × ℝ → ℝ := fun x => -(ν * lapP (B0579.pd 0 (ψ τ)) x) +
      V1.vC tr ρ 0 x * B0579.pd 1 (B0579.pd 1 (ψ τ)) x -
      V1.vC tr ρ 0 x * B0579.pd 0 (B0579.pd 0 (ψ τ)) x -
      2 * V1.vC tr ρ 1 x * B0579.pd 1 (B0579.pd 0 (ψ τ)) x with hM1
    have cM0 : Continuous M0 :=
      (((continuous_const.mul (cL 1)).add ((continuous_const.mul (cv 0)).mul (cf 0 1))).add
        ((cv 1).mul (cf 1 1))).sub ((cv 1).mul (cf 0 0))
    have cM1 : Continuous M1 :=
      ((((continuous_const.mul (cL 0)).neg).add ((cv 0).mul (cf 1 1))).sub
        ((cv 0).mul (cf 0 0))).sub ((continuous_const.mul (cv 1)).mul (cf 1 0))
    have bM0 : V1.Band R M0 := fun x hx => by
      simp only [hM0, bL1 x hx, b01 x hx, b11 x hx, b00 x hx]; ring
    have bM1 : V1.Band R M1 := fun x hx => by
      simp only [hM1, bL0 x hx, b11 x hx, b00 x hx, b10 x hx]; ring
    refine IntegrableOn.congr_fun
      ((V1.intL2 (hb_bs.1 0) cM0 bM0).add (V1.intL2 (hb_bs.1 1) cM1 bM1)) (fun x _ => ?_) hmc
    have hperp1 : (fun y => V1.perpF (ψ τ) y 1) = fun y => -B0579.pd 0 (ψ τ) y := rfl
    have hperp0 : (fun y => V1.perpF (ψ τ) y 0) = B0579.pd 1 (ψ τ) := rfl
    simp only [V1.jInt, V1.wF, Fin.sum_univ_two, hperp0, hperp1, V1.trainVel_of_nonneg tr hρ.le]
    rw [V1.pd_neg, V1.pd_neg, V1.lapP_neg (hφ.pd 0)]
    simp only [hM0, hM1, V1.vC_apply, Pi.add_apply]
    push_cast; ring
  have hpt_TI : ∀ x : ℝ × ℝ,
      flowIntegrand tr (fun y => G_s y 1 0 - G_s y 0 1) b_s ρ (ψ τ) x =
        V1.jInt tr (fun q => b_s q.2) (V1.wF (fun _ _ => 0) (fun q => b_s q.2)) (ψ τ) (ρ, x) +
          V1.Zs tr (fun _ _ => 0) (fun q => b_s q.2) (fun _ _ _ => 0) (fun q => G_s q.2) ρ (ψ τ) x := by
    intro x
    have h := V1.pointwise_TI tr (γ := 0) (μ := 0)
      (b₀ := fun _ _ => 0) (b_sol := fun q => b_s q.2)
      (G₀ := fun _ _ _ => 0) (G_sol := fun q => G_s q.2) hρ hφ x
    have hg1 : gainG 0 ν ρ = 1 := by simp [gainG]
    have hSI0 : coreAdvSlice 0 tr (fun _ _ => 0) (fun _ _ _ => 0) ρ x = 0 := by
      funext k; simp [coreAdvSlice, advStretch, gainConj]
    have hvort : corePerturbVort 0 ν (fun _ _ _ => 0) (fun q => G_s q.2) ρ =
        fun y => G_s y 1 0 - G_s y 0 1 := by
      funext y; simp [corePerturbVort, corePerturbGrad, gainConj, hg1]
    have hvel : (fun y => (((ρ : ℂ) ^ (0 : ℂ) * (gainG 0 ν ρ : ℂ)) •
        corePerturbVel 0 ν (fun _ _ => 0) (fun q => b_s q.2) (ρ, y))) = b_s := by
      funext y i; simp [corePerturbVel, gainConj, hg1]
    rw [hvort, hvel] at h
    simp only [Complex.cpow_zero, hg1, Complex.ofReal_one, one_mul,
      hSI0, Pi.zero_apply, zero_mul, sub_zero, add_zero] at h
    exact h
  -- Identify `∫ flowIntegrand (G_s 1 0 - G_s 0 1) b_s` with `∫ flowIntegrand w_ρ u_ρ`
  have hbs_curl : IsBiotSavart c (fun y => G_s y 1 0 - G_s y 0 1) b_s :=
    isBiotSavart_of_weakGrad hb_bs.1 hb_bs.2.1 hb_wg
  have hψ_t : B0579.IsCylTest c (V1.psiF tr ρ (ψ τ)) := V1.psiF_test tr hρ.le hφ
  have hcurl_psiF :
      ∫ x in B0579.cell c, (G_s x 1 0 - G_s x 0 1) * (V1.psiF tr ρ (ψ τ) x : ℂ) =
        ∫ x in B0579.cell c, w_ρ x * (V1.psiF tr ρ (ψ τ) x : ℂ) :=
    (hbs_curl.2.2 _ hψ_t).trans (hb_bs.2.2 _ hψ_t).symm
  have hbu_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), b_s x = u_ρ x :=
    CTE.isBiotSavart_unique c hc w_ρ b_s u_ρ hb_bs hu_bs
  have hforce_int_b : IntegrableOn
      (fun x => (b_s x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
        b_s x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) * (ψ τ x : ℂ))
      (B0579.cell c) := by
    have hE : ∀ k : Fin 2, Continuous (fun x => B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) x * ψ τ x) :=
      fun k => ((V1.pdE_contDiff tr hρ.le k).continuous).mul hφ.continuous
    have hEb : ∀ k : Fin 2, V1.Band R (fun x => B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) x * ψ τ x) :=
      fun k x hx => by simp [hB x hx]
    refine IntegrableOn.congr_fun
      ((V1.intL2 (hb_bs.1 0) (hE 0) (hEb 0)).add (V1.intL2 (hb_bs.1 1) (hE 1) (hEb 1)))
      (fun x _ => ?_) hmc
    dsimp; push_cast; ring
  have hG_curl_int : IntegrableOn
      (fun x => (G_s x 1 0 - G_s x 0 1) * (V1.psiF tr ρ (ψ τ) x : ℂ)) (B0579.cell c) := by
    have h10 := ((hb_wg 1 0).1 _ hψ_t).2
    have h01 := ((hb_wg 0 1).1 _ hψ_t).2
    exact (h10.sub h01).congr_fun (fun _ _ => by dsimp; ring) hmc
  have hw_psiF_int : IntegrableOn
      (fun x => w_ρ x * (V1.psiF tr ρ (ψ τ) x : ℂ)) (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_cylTest_mul hψ_t hw_l2
  have hforce_int_u : IntegrableOn
      (fun x => (u_ρ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
        u_ρ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) * (ψ τ x : ℂ))
      (B0579.cell c) := by
    refine hforce_int_b.congr_fun_ae ?_
    filter_upwards [hbu_ae] with x hx
    rw [hx]
  have hJ_eq : ∫ x in B0579.cell c,
      V1.jInt tr (fun q => b_s q.2) (V1.wF (fun _ _ => 0) (fun q => b_s q.2)) (ψ τ) (ρ, x) =
      ∫ x in B0579.cell c, flowIntegrand tr w_ρ u_ρ ρ (ψ τ) x := by
    have hFI_int : IntegrableOn
        (flowIntegrand tr (fun y => G_s y 1 0 - G_s y 0 1) b_s ρ (ψ τ)) (B0579.cell c) :=
      (hJ_int.add hZs_IZ.1).congr_fun (fun x _ => (hpt_TI x).symm) hmc
    have h1 : ∫ x in B0579.cell c,
          flowIntegrand tr (fun y => G_s y 1 0 - G_s y 0 1) b_s ρ (ψ τ) x =
        ∫ x in B0579.cell c,
          V1.jInt tr (fun q => b_s q.2) (V1.wF (fun _ _ => 0) (fun q => b_s q.2)) (ψ τ) (ρ, x) := by
      rw [integral_congr_ae (Eventually.of_forall hpt_TI), integral_add hJ_int hZs_IZ.1,
        hZs_IZ.2, add_zero]
    rw [← h1]
    have hdef1 : flowIntegrand tr (fun y => G_s y 1 0 - G_s y 0 1) b_s ρ (ψ τ) =
        fun x => (G_s x 1 0 - G_s x 0 1) * (V1.psiF tr ρ (ψ τ) x : ℂ) -
          (b_s x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
            b_s x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) * (ψ τ x : ℂ) := by
      funext x; unfold flowIntegrand V1.psiF V1.vC; rfl
    have hdef2 : flowIntegrand tr w_ρ u_ρ ρ (ψ τ) =
        fun x => w_ρ x * (V1.psiF tr ρ (ψ τ) x : ℂ) -
          (u_ρ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
            u_ρ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) * (ψ τ x : ℂ) := by
      funext x; unfold flowIntegrand V1.psiF V1.vC; rfl
    have hforce_eq :
        ∫ x in B0579.cell c,
            (b_s x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
              b_s x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) * (ψ τ x : ℂ) =
          ∫ x in B0579.cell c,
            (u_ρ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) +
              u_ρ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) * (ψ τ x : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hbu_ae] with x hx; rw [hx]
    rw [hdef1, hdef2, integral_sub hG_curl_int hforce_int_b,
      integral_sub hw_psiF_int hforce_int_u, hcurl_psiF, hforce_eq]
  -- 4. Combine
  have hcongr : (fun x =>
      flatIntegrand ν 0 (fun _ _ _ => 0) (fun p i j => F_s i j p.2) (fun p => b_s p.2)
        (fun s y => V1.perpF (ψ s) y) (τ, x)) =
      fun x => -(V1.hInt (fun q => b_s q.2) (fun y => deriv (fun τ' => ψ τ' y) τ) (ρ, x) +
        V1.jInt tr (fun q => b_s q.2) (V1.wF (fun _ _ => 0) (fun q => b_s q.2)) (ψ τ) (ρ, x)) := by
    funext x; rw [hpt_fi x]; ring
  rw [hcongr, integral_neg, integral_add hI_dt.1 hJ_int, hI_dt.2, hJ_eq]
  ring

private lemma shifted_stream_time_eq_zero {ν m s_r H' : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (hc1 : 1 ≤ ν ^ (-2 : ℝ)) (hs_r : 0 ≤ s_r) (hH' : 0 < H')
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf₀_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) f₀)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr s_r f₀ w u)
    {ψ : ℝ → ℝ × ℝ → ℝ} {τ₁ τ₂ R₁ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ < τ₂) (hτ₂H : τ₂ < H') (hR₁ : 0 < R₁)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2))
    (hper : ∀ s x, ψ s (x.1 + ν ^ (-2 : ℝ), x.2) = ψ s x)
    (hsupp : ∀ s x, (s < τ₁ ∨ τ₂ < s ∨ R₁ < |x.2|) → ψ s x = 0) :
    ∫ τ in Ioo (0 : ℝ) H',
      ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w (s_r + τ)) (u (s_r + τ)) (s_r + τ) (ψ τ) x) +
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          w (s_r + τ) x * ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ)) = 0 := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  -- Apply `ladProductRule` on `Ico s_r (s_r + H' + 1)` with `φ_phys ρ x := (ψ (ρ - s_r) x : ℂ)` and `R := R₁ + 1`
  set s_end : ℝ := s_r + H' + 1
  set R : ℝ := R₁ + 1
  have hR_pos : 0 < R := by dsimp [R]; linarith
  set φ_phys : ℝ → ℝ × ℝ → ℂ := fun ρ x => (ψ (ρ - s_r) x : ℂ)
  have hφ_sm : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ_phys p.1 p.2) :=
    Complex.ofRealCLM.contDiff.comp (hψ.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd))
  have hφ_per : ∀ r ∈ Ico s_r s_end, ∀ x : ℝ × ℝ, φ_phys r (x.1 + c, x.2) = φ_phys r x := by
    intro r _ x; dsimp [φ_phys]; rw [hper]
  have hv_lip := ladVelLip m hm ν c tr s_r f₀ w u hc1 hf₀_zc hw
  obtain ⟨hint_rate, hpr_eq⟩ := ladProductRule ν c m tr s_r s_end f₀ w u φ_phys
    hν hc hs_r (by dsimp [s_end]; linarith) hw hv_lip hφ_sm.contDiffOn hφ_per R hR_pos
    (s_r + H') ⟨by linarith, by dsimp [s_end]; linarith⟩
  -- Cutoff `ladCut R x = 1` on `|x.2| ≤ R₁`, while `ψ` vanishes on `|x.2| > R₁`
  have hcut_eq : ∀ ρ x, ladCutPhi φ_phys R ρ x = φ_phys ρ x := by
    intro ρ x
    unfold ladCutPhi
    by_cases hx : |x.2| ≤ R₁
    · have h1 : 1 ≤ 2 - x.2 ^ 2 / R ^ 2 := by
        have hsq : x.2 ^ 2 ≤ R ^ 2 := by
          have : |x.2| ≤ |R| := by rw [abs_of_pos hR_pos]; dsimp [R]; linarith
          exact sq_le_sq.2 this
        have : x.2 ^ 2 / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hR_pos)).2 hsq
        linarith
      rw [ladCut, Real.smoothTransition.one_of_one_le h1, Complex.ofReal_one, one_mul]
    · have hx' : R₁ < |x.2| := not_le.mp hx
      dsimp [φ_phys]
      rw [hsupp _ x (Or.inr (Or.inr hx'))]
      simp
  -- Endpoint pairings at `s_r` and `s_r + H'` vanish
  have hP0 : ladCutPair c R w φ_phys s_r = 0 := by
    unfold ladCutPair
    have h0 : ∀ x, ladCutPhi φ_phys R s_r x = 0 := by
      intro x; rw [hcut_eq]; dsimp [φ_phys]
      rw [sub_self, hsupp 0 x (Or.inl hτ₁), Complex.ofReal_zero]
    simp [h0]
  have hPH : ladCutPair c R w φ_phys (s_r + H') = 0 := by
    unfold ladCutPair
    have h0 : ∀ x, ladCutPhi φ_phys R (s_r + H') x = 0 := by
      intro x; rw [hcut_eq]; dsimp [φ_phys]
      rw [add_sub_cancel_left, hsupp H' x (Or.inr (Or.inl hτ₂H)), Complex.ofReal_zero]
    simp [h0]
  rw [hPH, hP0, sub_zero] at hpr_eq
  -- Identify `ladRate tr w u φ_phys R (s_r + τ)` with the slice expression for `τ ∈ Ioo 0 H'`
  have hband : ∀ s x, R₁ < |x.2| → ψ s x = 0 := fun s x hx => hsupp s x (Or.inr (Or.inr hx))
  have hrate_eq : ∀ τ : ℝ,
      ladRate tr w u φ_phys R (s_r + τ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w (s_r + τ)) (u (s_r + τ)) (s_r + τ) (ψ τ) x) +
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w (s_r + τ) x * ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ) := by
    intro τ
    unfold ladRate
    have hφ_tau : ladCutPhi φ_phys R (s_r + τ) = fun x => (ψ τ x : ℂ) := by
      funext x; rw [hcut_eq]; dsimp [φ_phys]; rw [add_sub_cancel_left]
    have htest_tau : B0579.IsCylTest (ν ^ (-2 : ℝ)) (ψ τ) := isCylTest_slice hψ hper hband τ
    have hflow_eq : ∀ x, ladFlowCx tr (w (s_r + τ)) (u (s_r + τ)) (s_r + τ)
        (ladCutPhi φ_phys R (s_r + τ)) x =
        flowIntegrand tr (w (s_r + τ)) (u (s_r + τ)) (s_r + τ) (ψ τ) x := by
      intro x
      rw [hφ_tau]
      unfold ladFlowCx ladForce flowIntegrand
      rw [LadPRWeakAux.ladLapCx_ofReal htest_tau x,
        LadPRWeakAux.ladTransport_ofReal tr (s_r + τ) htest_tau x]
      push_cast; ring
    have hdt_eq : ∀ x, (ladCut R x : ℂ) * ladDt φ_phys (s_r + τ) x =
        ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ) := by
      intro x
      have hdiff_ψ : DifferentiableAt ℝ (fun τ' => ψ τ' x) τ :=
        (hψ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) τ
      have hderiv_φ : HasDerivAt (fun r => φ_phys r x)
          ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ) (s_r + τ) := by
        have h2 : HasDerivAt (fun τ' : ℝ => (ψ τ' x : ℂ))
            ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ) ((s_r + τ) - s_r) := by
          rw [add_sub_cancel_left]
          exact hdiff_ψ.hasDerivAt.ofReal_comp
        exact HasDerivAt.comp_sub_const (s_r + τ) s_r h2
      rw [ladDt_eq_of_hasDerivAt hderiv_φ]
      by_cases hx : |x.2| ≤ R₁
      · have h1 : 1 ≤ 2 - x.2 ^ 2 / R ^ 2 := by
          have hsq : x.2 ^ 2 ≤ R ^ 2 := by
            have : |x.2| ≤ |R| := by rw [abs_of_pos hR_pos]; dsimp [R]; linarith
            exact sq_le_sq.2 this
          have : x.2 ^ 2 / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hR_pos)).2 hsq
          linarith
        rw [ladCut, Real.smoothTransition.one_of_one_le h1, Complex.ofReal_one, one_mul]
      · have hx' : R₁ < |x.2| := not_le.mp hx
        have hzero : (fun τ' => ψ τ' x) = 0 := funext fun τ' => hband τ' x hx'
        rw [hzero]; simp
    simp_rw [hflow_eq, hdt_eq]
  -- Change variables `ρ = s_r + τ` from `s_r..(s_r + H')` to `0..H'` = `Ioo 0 H'`
  have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := H')
    (f := fun ρ => ladRate tr w u φ_phys R ρ) s_r
  rw [add_zero] at hshift
  rw [← hpr_eq] at hshift
  simp_rw [hrate_eq] at hshift
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hH'.le]
  exact hshift

private lemma shifted_flatTest_eq_zero {ν m s_r H' H₀ M_E M_v : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (hc1 : 1 ≤ ν ^ (-2 : ℝ)) (hs_r : 0 ≤ s_r)
    (hH₀ : H₀ < H') (hH'_pos : 0 < H') (hME : 0 ≤ M_E) (hMv : 0 ≤ M_v)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf₀_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) f₀)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr s_r f₀ w u)
    {F_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b_sh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hb_meas : ∀ i, Measurable fun p => b_sh p i)
    (hF_meas : ∀ i j, Measurable fun p => F_sh p i j)
    (hE_bd : ∀ τ, ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
      ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2) ≤ ENNReal.ofReal M_E)
    (hF_eq : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Icc 0 H' → ∀ i j,
      F_sh p i j = -((trainVel tr (s_r + p.1) p.2 i : ℂ) * b_sh p j +
        b_sh p i * (trainVel tr (s_r + p.1) p.2 j : ℂ)))
    (hMv_bd : ∀ τ ∈ Icc 0 H', ∀ x i, ‖(trainVel tr (s_r + τ) x i : ℂ)‖ ≤ M_v)
    (hbs_slice : ∀ τ ∈ Icc 0 H', IsBiotSavart (ν ^ (-2 : ℝ)) (w (s_r + τ)) (fun x => b_sh (τ, x)))
    (hwg_slice : ∀ τ, ∀ i j,
      HasWeakCellDerivC (ν ^ (-2 : ℝ)) j (fun x => b_sh (τ, x) i) (fun x => G_sh (τ, x) i j))
    {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest (ν ^ (-2 : ℝ)) Φ)
    (hΦ_H₀ : ∀ s x i, H₀ ≤ s → Φ s x i = 0) :
    IntegrableOn (flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell (ν ^ (-2 : ℝ))) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell (ν ^ (-2 : ℝ)),
        flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh Φ p = 0 := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hF_bd : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Icc 0 H' → ∀ i j,
      ‖F_sh p i j‖ ≤ 2 * M_v * vnorm2 (b_sh p) := by
    intro p hp i j
    rw [hF_eq p hp i j, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hv_i := hMv_bd p.1 hp p.2 i
    have hv_j := hMv_bd p.1 hp p.2 j
    have hb_i := norm_le_vnorm2_local (b_sh p) i
    have hb_j := norm_le_vnorm2_local (b_sh p) j
    calc ‖(trainVel tr (s_r + p.1) p.2 i : ℂ)‖ * ‖b_sh p j‖ +
          ‖b_sh p i‖ * ‖(trainVel tr (s_r + p.1) p.2 j : ℂ)‖
        ≤ M_v * vnorm2 (b_sh p) + vnorm2 (b_sh p) * M_v :=
          add_le_add (mul_le_mul hv_i hb_j (norm_nonneg _) hMv)
            (mul_le_mul hb_i hv_j (norm_nonneg _) (Real.sqrt_nonneg _))
      _ = 2 * M_v * vnorm2 (b_sh p) := by ring
  obtain ⟨s₁_raw, s₂_raw, R_raw, hs₁_raw, hsupp_raw⟩ := hΦ.support
  set H₀' : ℝ := max H₀ (H' / 2)
  have hH₀'_pos : 0 < H₀' := lt_of_lt_of_le (half_pos hH'_pos) (le_max_right _ _)
  have hH₀'_lt : H₀' < H' := max_lt hH₀ (by linarith)
  set s₁ : ℝ := min (s₁_raw / 2) (H₀' / 2)
  set s₂ : ℝ := (H₀' + H') / 2
  set R₀ : ℝ := max R_raw 1
  have hs₁ : 0 < s₁ := lt_min (half_pos hs₁_raw) (half_pos hH₀'_pos)
  have hs₁₂ : s₁ < s₂ := by
    have : s₁ ≤ H₀' / 2 := min_le_right _ _
    dsimp [s₂]; linarith
  have hs₂H : s₂ < H' := by dsimp [s₂]; linarith
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ R₀ < |x.2|) → Φ s x i = 0 := by
    intro s x i hout
    rcases hout with h1 | h2 | h3
    · exact hsupp_raw s x i (Or.inl (lt_of_lt_of_le h1 ((min_le_left _ _).trans (by linarith))))
    · exact hΦ_H₀ s x i (by dsimp [s₂, H₀'] at h2; linarith [le_max_left H₀ (H' / 2)])
    · exact hsupp_raw s x i (Or.inr (Or.inr (lt_of_le_of_lt (le_max_left _ _) h3)))
  obtain ⟨hint_Φ, _, hb_sq_int⟩ := integrableOn_flatIntegrand_supported hc hs₁ hs₁₂ hs₂H hR₀
    hME hMv hb_meas hF_meas hE_bd hF_bd hΦ.smooth hsupp
  refine ⟨hint_Φ, ?_⟩
  -- Stream test integral vanishes
  have hstream_zero : ∀ {ψ : ℝ → ℝ × ℝ → ℝ} {R₁ : ℝ},
      0 < R₁ →
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) →
      (∀ s x, ψ s (x.1 + c, x.2) = ψ s x) →
      (∀ s x, (s < s₁ ∨ s₂ < s ∨ R₁ < |x.2|) → ψ s x = 0) →
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (fun s y => V1.perpF (ψ s) y) p = 0 := by
    intro ψ R₁ hR₁ hψ hper hψ_supp
    have hperp_sm := contDiff_perpF_comp hψ
    have hperp_sp := supp_perpF_comp hψ_supp
    obtain ⟨hint_Ioi, heq_Ioo, _⟩ := integrableOn_flatIntegrand_supported hc hs₁ hs₁₂ hs₂H hR₁
      hME hMv hb_meas hF_meas hE_bd hF_bd hperp_sm hperp_sp
    have hint_Ioo : IntegrableOn
        (flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (fun s y => V1.perpF (ψ s) y))
        (Ioo (0 : ℝ) H' ×ˢ B0579.cell c) :=
      hint_Ioi.mono_set (prod_mono Ioo_subset_Ioi_self Subset.rfl)
    rw [heq_Ioo]
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint_Ioo
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint_Ioo]
    have hband : ∀ s x, R₁ < |x.2| → ψ s x = 0 := fun s x hx => hψ_supp s x (Or.inr (Or.inr hx))
    have hslice_eq : ∀ τ ∈ Ioo (0 : ℝ) H',
        (∫ x in B0579.cell c,
          flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (fun s y => V1.perpF (ψ s) y) (τ, x)) =
        -((∫ x in B0579.cell c, flowIntegrand tr (w (s_r + τ)) (u (s_r + τ)) (s_r + τ) (ψ τ) x) +
          ∫ x in B0579.cell c, w (s_r + τ) x * ((deriv (fun τ' => ψ τ' x) τ : ℝ) : ℂ)) := by
      intro τ hτ
      have hτ_Icc : τ ∈ Icc 0 H' := ⟨hτ.1.le, hτ.2.le⟩
      have hsr_le : s_r ≤ s_r + τ := by linarith [hτ.1]
      have hw_l2 : MemLp (w (s_r + τ)) 2 (volume.restrict (B0579.cell c)) :=
        memLp_unweighted_of_memX_pos (by linarith : 0 ≤ m) (hw.memX (s_r + τ) hsr_le)
      have hpt_congr : ∀ x : ℝ × ℝ,
          flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (fun s y => V1.perpF (ψ s) y) (τ, x) =
            flatIntegrand ν 0 (fun _ _ _ => 0)
              (fun p i j => -((trainVel tr (s_r + τ) p.2 i : ℂ) * b_sh (τ, p.2) j +
                b_sh (τ, p.2) i * (trainVel tr (s_r + τ) p.2 j : ℂ)))
              (fun p => b_sh (τ, p.2)) (fun s y => V1.perpF (ψ s) y) (τ, x) := by
        intro x
        unfold flatIntegrand
        dsimp only
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hF_eq (τ, x) hτ_Icc i j]
      rw [integral_congr_ae (Eventually.of_forall hpt_congr)]
      exact shifted_perpF_slice_eq hs_r hτ.1 (hbs_slice τ hτ_Icc)
        (hw.biotSavart (s_r + τ) hsr_le) (hwg_slice τ) hw_l2 hψ hper hband hν
    rw [setIntegral_congr_fun measurableSet_Ioo hslice_eq, integral_neg,
      shifted_stream_time_eq_zero hm hν hc1 hs_r hH'_pos hf₀_zc hw hs₁ hs₁₂ hs₂H hR₁
        hψ hper hψ_supp, neg_zero]
  -- Approximate general `Φ` by `V1.perpF (χ_seq k x.2 * etaPrim R₀ Φ τ x)` as `k → ∞`
  obtain ⟨hΘ_sm, hΘ_per, hΘ_ts, hΘ_bot, hΘ_pd1, hΘ_pd0, hΘ_top⟩ := etaPrim_props hΦ hsupp hR₀
  set Θ := etaPrim R₀ Φ
  set m_s : ℝ → ℝ := fun s => Θ s (0, R₀ + 1)
  have hm_sm : ContDiff ℝ ∞ m_s := hΘ_sm.comp (contDiff_id.prodMk contDiff_const)
  have hm_diff : Differentiable ℝ m_s := hm_sm.differentiable (by simp)
  have hdm_sm : ContDiff ℝ ∞ (deriv m_s) := (contDiff_infty_iff_deriv.mp hm_sm).2
  obtain ⟨M_m, hM_m⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hm_sm.continuous.abs.add hdm_sm.continuous.abs).continuousOn
  have hM_m0 : 0 ≤ M_m := (norm_nonneg _).trans (hM_m s₁ ⟨le_rfl, hs₁₂.le⟩)
  let b_bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb_sm : ContDiff ℝ ∞ (⇑b_bump) := b_bump.contDiff
  have hdb1_sm : ContDiff ℝ ∞ (deriv (⇑b_bump)) := (contDiff_infty_iff_deriv.mp hb_sm).2
  have hdb2_sm : ContDiff ℝ ∞ (deriv (deriv (⇑b_bump))) := (contDiff_infty_iff_deriv.mp hdb1_sm).2
  have hdb3_sm : ContDiff ℝ ∞ (deriv (deriv (deriv (⇑b_bump)))) :=
    (contDiff_infty_iff_deriv.mp hdb2_sm).2
  obtain ⟨Cb1, hCb1⟩ := hdb1_sm.continuous.bounded_above_of_compact_support b_bump.hasCompactSupport.deriv
  obtain ⟨Cb2, hCb2⟩ := hdb2_sm.continuous.bounded_above_of_compact_support b_bump.hasCompactSupport.deriv.deriv
  obtain ⟨Cb3, hCb3⟩ := hdb3_sm.continuous.bounded_above_of_compact_support b_bump.hasCompactSupport.deriv.deriv.deriv
  have hCb_nn : 0 ≤ Cb1 + Cb2 + Cb3 := by
    linarith [(norm_nonneg _).trans (hCb1 0), (norm_nonneg _).trans (hCb2 0), (norm_nonneg _).trans (hCb3 0)]
  have hb_one : ∀ t : ℝ, |t| ≤ 1 → b_bump t = 1 := fun t ht =>
    b_bump.one_of_mem_closedBall (by simpa [b_bump, Metric.mem_closedBall, Real.dist_eq] using ht)
  have hb_zero : ∀ t : ℝ, 2 ≤ |t| → b_bump t = 0 := fun t ht =>
    b_bump.zero_of_le_dist (by simpa [b_bump, Real.dist_eq] using ht)
  set R_seq : ℕ → ℝ := fun k => R₀ + 2 + (k : ℝ)
  set χ_seq : ℕ → ℝ → ℝ := fun k η => b_bump (η / R_seq k)
  set ψ_seq : ℕ → ℝ → ℝ × ℝ → ℝ := fun k s x => χ_seq k x.2 * Θ s x
  set E_seq : ℕ → ℝ → ℝ × ℝ → Fin 2 → ℝ := fun k s x i => V1.perpF (ψ_seq k s) x i - Φ s x i
  set E_tot : ℝ := ∫ p in Icc s₁ s₂ ×ˢ B0579.cell c, vnorm2 (b_sh p) ^ 2
  set C_err : ℝ := (1 + |ν| + 2 * M_v) * (Cb1 + Cb2 + Cb3) * M_m
  have hCerr_nn : 0 ≤ C_err := mul_nonneg (mul_nonneg (by positivity) hCb_nn) hM_m0
  have hb_norm_meas : Measurable fun p => vnorm2 (b_sh p) := by
    unfold vnorm2
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum Finset.univ fun i _ => (hb_meas i).norm.pow_const 2)
  have hbound_k : ∀ k : ℕ,
      ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh Φ p‖ ≤
        C_err * (((s₂ - s₁) * c + E_tot) / (2 * Real.sqrt (R_seq k))) := by
    intro k
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hRk_ge1 : 1 ≤ R_seq k := by dsimp [R_seq]; linarith
    have hRk_pos : 0 < R_seq k := by linarith
    have hRk_gt : R₀ + 1 < R_seq k := by dsimp [R_seq]; linarith
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
          rw [abs_div, abs_of_pos hRk_pos, le_div_iff₀ hRk_pos]; exact hx.le
        rw [hb_zero _ h2, zero_mul]
    have hperp_int_zero := hstream_zero (by positivity : 0 < 2 * R_seq k) hψk_sm hψk_per hψk_supp
    have hperp_sm := contDiff_perpF_comp hψk_sm
    have hperp_sp := supp_perpF_comp hψk_supp
    obtain ⟨hint_perp, _, _⟩ := integrableOn_flatIntegrand_supported hc hs₁ hs₁₂ hs₂H
      (by positivity : 0 < 2 * R_seq k) hME hMv hb_meas hF_meas hE_bd hF_bd hperp_sm hperp_sp
    have hEk_sm : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => E_seq k p.1 p.2 i) :=
      fun i => (hperp_sm i).sub (hΦ.smooth i)
    have hEk_sp_coarse : ∀ s x i,
        (s < s₁ ∨ s₂ < s ∨ 2 * R_seq k < |x.2|) → E_seq k s x i = 0 := by
      intro s x i hout
      dsimp [E_seq]
      rw [hperp_sp s x i hout,
        hsupp s x i (hout.imp id (Or.imp id fun h => lt_trans (by linarith) h)), sub_zero]
    obtain ⟨hint_Ek, _, _⟩ := integrableOn_flatIntegrand_supported hc hs₁ hs₁₂ hs₂H
      (by positivity : 0 < 2 * R_seq k) hME hMv hb_meas hF_meas hE_bd hF_bd hEk_sm hEk_sp_coarse
    have hint_eq : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh Φ p =
        -∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p := by
      have hsub_fn : flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) =
          fun p => flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh
              (fun s y => V1.perpF (ψ_seq k s) y) p -
            flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh Φ p :=
        funext fun p => flatIntegrand_sub_test_zero ν F_sh b_sh _ Φ hperp_sm hΦ.smooth p
      rw [hsub_fn, integral_sub hint_perp hint_Φ, hperp_int_zero, zero_sub, neg_neg]
    -- Bounds on derivatives of `χ_seq k`
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
      intro η; have h := hCb1 (η / R_seq k); rw [Real.norm_eq_abs] at h
      rw [hdχ1, abs_mul, abs_of_pos hinv_pos, mul_one_div]
      exact div_le_div_of_nonneg_right h hRk_pos.le
    have hdχ2_bd : ∀ η, |deriv (deriv (χ_seq k)) η| ≤ Cb2 / R_seq k := by
      intro η; have h := hCb2 (η / R_seq k); rw [Real.norm_eq_abs] at h
      rw [hdχ2, abs_mul, abs_mul, abs_of_pos hinv_pos]
      calc |deriv (deriv (⇑b_bump)) (η / R_seq k)| * (1 / R_seq k) * (1 / R_seq k)
          ≤ Cb2 * 1 * (1 / R_seq k) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul h hinv_le1 hinv_pos.le ((norm_nonneg _).trans (hCb2 0))) hinv_pos.le
        _ = Cb2 / R_seq k := by ring
    have hdχ3_bd : ∀ η, |deriv (deriv (deriv (χ_seq k))) η| ≤ Cb3 / R_seq k := by
      intro η; have h := hCb3 (η / R_seq k); rw [Real.norm_eq_abs] at h
      rw [hdχ3, abs_mul, abs_mul, abs_mul, abs_of_pos hinv_pos]
      have hCb3_0 := (norm_nonneg _).trans (hCb3 0)
      calc |deriv (deriv (deriv (⇑b_bump))) (η / R_seq k)| *
              (1 / R_seq k) * (1 / R_seq k) * (1 / R_seq k)
          ≤ Cb3 * 1 * 1 * (1 / R_seq k) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (mul_le_mul h hinv_le1 hinv_pos.le hCb3_0)
                hinv_le1 hinv_pos.le (by positivity)) hinv_pos.le
        _ = Cb3 / R_seq k := by ring
    -- `E_seq k` vanishes outside `S_k := [s₁, s₂] × [-c/2, c/2) × [R_seq k, 2 * R_seq k]`
    have hEk_zero_region : ∀ s (x : ℝ × ℝ) i,
        (s < s₁ ∨ s₂ < s ∨ x.2 < R_seq k ∨ 2 * R_seq k < x.2) → E_seq k s x i = 0 := by
      intro s x i hout
      rcases hout with hs | hs | hx_lt | hx_gt
      · exact hEk_sp_coarse s x i (Or.inl hs)
      · exact hEk_sp_coarse s x i (Or.inr (Or.inl hs))
      · by_cases hlow : -(R₀ + 1) - 1 / 2 < x.2
        · have habs : |x.2| < R_seq k := abs_lt.2 ⟨by dsimp [R_seq]; linarith, hx_lt⟩
          have hU : {y : ℝ × ℝ | |y.2| < R_seq k} ∈ 𝓝 x :=
            (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).mem_nhds habs
          have hev : ψ_seq k s =ᶠ[𝓝 x] Θ s := by
            filter_upwards [hU] with y hy
            dsimp [ψ_seq, χ_seq]
            have h1 : |y.2 / R_seq k| ≤ 1 := by
              rw [abs_div, abs_of_pos hRk_pos, div_le_one hRk_pos]; exact hy.le
            rw [hb_one _ h1, one_mul]
          have hpd_eq : ∀ j : Fin 2, B0579.pd j (ψ_seq k s) x = B0579.pd j (Θ s) x :=
            fun j => pd_eq_of_eventuallyEq hev j
          dsimp [E_seq]
          fin_cases i
          · simp [V1.perpF_zero, hpd_eq 1, hΘ_pd1]
          · simp [V1.perpF_one, hpd_eq 0, hΘ_pd0]
        · have hx_neg : x.2 < -(R₀ + 1) := by linarith
          have hU : {y : ℝ × ℝ | y.2 < -(R₀ + 1)} ∈ 𝓝 x :=
            (isOpen_lt continuous_snd continuous_const).mem_nhds hx_neg
          have hev : ψ_seq k s =ᶠ[𝓝 x] 0 := by
            filter_upwards [hU] with y hy; dsimp [ψ_seq]; rw [hΘ_bot s y hy, mul_zero]
          have hpd0 : ∀ j : Fin 2, B0579.pd j (ψ_seq k s) x = 0 :=
            fun j => pd_eq_zero_of_eventuallyEq hev j
          have hΦ0 : Φ s x i = 0 :=
            hsupp s x i (Or.inr (Or.inr (by rw [abs_of_neg (by linarith)]; linarith)))
          dsimp [E_seq]; rw [hΦ0, sub_zero]
          fin_cases i <;> simp [V1.perpF_zero, V1.perpF_one, hpd0 0, hpd0 1]
      · exact hEk_sp_coarse s x i (Or.inr (Or.inr (lt_of_lt_of_le hx_gt (le_abs_self x.2))))
    set S_k : Set (ℝ × (ℝ × ℝ)) :=
      Icc s₁ s₂ ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (R_seq k) (2 * R_seq k))
    have hSk_meas : MeasurableSet S_k :=
      measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
    have hSk_sub_Ioi : S_k ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
      fun p hp => ⟨lt_of_lt_of_le hs₁ hp.1.1, hp.2.1, trivial⟩
    have hSk_sub_strip : S_k ⊆ Icc s₁ s₂ ×ˢ B0579.cell c :=
      prod_mono Subset.rfl (prod_mono Subset.rfl (subset_univ _))
    have hEk_zero_off : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ S_k,
        flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p = 0 := by
      intro p hp
      have hout : p.1 < s₁ ∨ s₂ < p.1 ∨ p.2.2 < R_seq k ∨ 2 * R_seq k < p.2.2 := by
        by_contra hnot; simp only [not_or, not_lt] at hnot
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
        have hev : (fun s' => E_seq k s' p.2 i) =ᶠ[𝓝 p.1] 0 :=
          Filter.eventually_of_mem ((continuousAt_id.prodMk continuousAt_const) hU_mem)
            fun s' hs' => hEk_zero_region s' p.2 i hs'
        rw [hev.deriv_eq]; simp
      let V_x : Set (ℝ × ℝ) := {y | (p.1, y) ∈ U_out}
      have hVx_open : IsOpen V_x := hU_open.preimage (continuous_const.prodMk continuous_id)
      have hpd_zero_on : ∀ y ∈ V_x, ∀ i j, B0579.pd j (fun z => E_seq k p.1 z i) y = 0 :=
        fun y hy i j => pd_eq_zero_of_eventuallyEq
          (Filter.eventually_of_mem (hVx_open.mem_nhds hy) fun z hz => hEk_zero_region p.1 z i hz) j
      have hgr0 : ∀ i j, flatGrad (E_seq k) p.1 p.2 i j = 0 := fun i j => hpd_zero_on p.2 hout i j
      have hlp0 : ∀ i, flatLap (E_seq k) p.1 p.2 i = 0 := by
        intro i; unfold flatLap lapP
        have hpd_ev : ∀ j, B0579.pd j (fun y => E_seq k p.1 y i) =ᶠ[𝓝 p.2] 0 := fun j =>
          Filter.eventually_of_mem (hVx_open.mem_nhds hout) fun y hy => hpd_zero_on y hy i j
        rw [pd_eq_zero_of_eventuallyEq (hpd_ev 0) 0, pd_eq_zero_of_eventuallyEq (hpd_ev 1) 1, add_zero]
      simp [flatIntegrand, h0, hdt0, hgr0, hlp0]
    have hint_Ek_Sk : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p =
        ∫ p in S_k, flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p :=
      MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        (measurableSet_Ioi.prod (B0579.measurableSet_cell c)).nullMeasurableSet
        hSk_sub_Ioi (Eventually.of_forall hEk_zero_off)
    have hEk_top : ∀ s (y : ℝ × ℝ), R₀ + 1 < y.2 →
        E_seq k s y 0 = deriv (χ_seq k) y.2 * m_s s ∧ E_seq k s y 1 = 0 := by
      intro s y hy
      have hU : {z : ℝ × ℝ | R₀ + 1 < z.2} ∈ 𝓝 y :=
        (isOpen_lt continuous_const continuous_snd).mem_nhds hy
      have hev_ψ : ψ_seq k s =ᶠ[𝓝 y] fun z => χ_seq k z.2 * m_s s := by
        filter_upwards [hU] with z hz; dsimp [ψ_seq, m_s]; rw [hΘ_top s z hz.le]
      have hΦ0 : ∀ i, Φ s y i = 0 :=
        fun i => hsupp s y i (Or.inr (Or.inr (by rw [abs_of_pos (by linarith)]; linarith)))
      have hd_χ : Differentiable ℝ (χ_seq k) := hχ_sm.differentiable (by simp)
      have hpd0_ψ : B0579.pd 0 (ψ_seq k s) y = 0 := by
        rw [pd_eq_of_eventuallyEq hev_ψ 0,
          DfcCutPdAux.pdSndMul 0 (χ_seq k) (fun _ => m_s s) hd_χ (differentiable_const _) y,
          DfcCutPdAux.dir0_snd]
        unfold B0579.pd; simp
      have hpd1_ψ : B0579.pd 1 (ψ_seq k s) y = deriv (χ_seq k) y.2 * m_s s := by
        rw [pd_eq_of_eventuallyEq hev_ψ 1,
          DfcCutPdAux.pdSndMul 1 (χ_seq k) (fun _ => m_s s) hd_χ (differentiable_const _) y,
          DfcCutPdAux.dir1_snd]
        have hpd_c : B0579.pd 1 (fun _ : ℝ × ℝ => m_s s) y = 0 := by unfold B0579.pd; simp
        rw [hpd_c]; ring
      exact ⟨by simp [E_seq, V1.perpF_zero, hpd1_ψ, hΦ0 0],
        by simp [E_seq, V1.perpF_one, hpd0_ψ, hΦ0 1]⟩
    have hpt_Sk : ∀ p ∈ S_k,
        ‖flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p‖ ≤
          C_err * (vnorm2 (b_sh p) / R_seq k) := by
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
        have hfn : (fun s' => E_seq k s' p.2 1) = 0 := funext fun s' => (hEk_top s' p.2 hp_top).2
        rw [hfn]; simp
      have hpd0_0 : B0579.pd 0 (fun y => deriv (χ_seq k) y.2 * m_s p.1) = 0 := by
        funext z
        rw [DfcCutPdAux.pdSndMul 0 (deriv (χ_seq k)) (fun _ => m_s p.1) hd1_χ
          (differentiable_const _) z, DfcCutPdAux.dir0_snd]
        unfold B0579.pd; simp
      have hpd1_0 : B0579.pd 1 (fun y => deriv (χ_seq k) y.2 * m_s p.1) =
          fun z => deriv (deriv (χ_seq k)) z.2 * m_s p.1 := by
        funext z
        rw [DfcCutPdAux.pdSndMul 1 (deriv (χ_seq k)) (fun _ => m_s p.1) hd1_χ
          (differentiable_const _) z, DfcCutPdAux.dir1_snd]
        have hc0 : B0579.pd 1 (fun _ : ℝ × ℝ => m_s p.1) z = 0 := by unfold B0579.pd; simp
        rw [hc0]; ring
      have hgr00 : flatGrad (E_seq k) p.1 p.2 0 0 = 0 := by
        unfold flatGrad; rw [pd_eq_of_eventuallyEq hev0 0, hpd0_0]; rfl
      have hgr01 : flatGrad (E_seq k) p.1 p.2 0 1 = deriv (deriv (χ_seq k)) p.2.2 * m_s p.1 := by
        unfold flatGrad; rw [pd_eq_of_eventuallyEq hev0 1, hpd1_0]
      have hgr1 : ∀ j, flatGrad (E_seq k) p.1 p.2 1 j = 0 :=
        fun j => pd_eq_zero_of_eventuallyEq hev1 j
      have hlp0 : flatLap (E_seq k) p.1 p.2 0 =
          deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 := by
        unfold flatLap lapP
        have hev_pd0 : B0579.pd 0 (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 p.2] 0 := by
          filter_upwards [hU] with z hz
          have hz0 : (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 z] fun y => deriv (χ_seq k) y.2 * m_s p.1 :=
            Filter.eventually_of_mem (hU_top_open.mem_nhds hz) fun y hy => (hEk_top p.1 y hy).1
          rw [pd_eq_of_eventuallyEq hz0 0, hpd0_0]
        have hev_pd1 : B0579.pd 1 (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 p.2]
            fun z => deriv (deriv (χ_seq k)) z.2 * m_s p.1 := by
          filter_upwards [hU] with z hz
          have hz0 : (fun y => E_seq k p.1 y 0) =ᶠ[𝓝 z] fun y => deriv (χ_seq k) y.2 * m_s p.1 :=
            Filter.eventually_of_mem (hU_top_open.mem_nhds hz) fun y hy => (hEk_top p.1 y hy).1
          rw [pd_eq_of_eventuallyEq hz0 1, hpd1_0]
        have h00 := pd_eq_zero_of_eventuallyEq hev_pd0 0
        have h11 : B0579.pd 1 (B0579.pd 1 (fun y => E_seq k p.1 y 0)) p.2 =
            deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 := by
          rw [pd_eq_of_eventuallyEq hev_pd1 1,
            DfcCutPdAux.pdSndMul 1 (deriv (deriv (χ_seq k))) (fun _ => m_s p.1) hd2_χ
              (differentiable_const _) p.2, DfcCutPdAux.dir1_snd]
          have hc0 : B0579.pd 1 (fun _ : ℝ × ℝ => m_s p.1) p.2 = 0 := by unfold B0579.pd; simp
          rw [hc0]; ring
        rw [h00, h11, zero_add]
      have hlp1 : flatLap (E_seq k) p.1 p.2 1 = 0 := by
        unfold flatLap lapP
        have hev_pd : ∀ j, B0579.pd j (fun y => E_seq k p.1 y 1) =ᶠ[𝓝 p.2] 0 := fun j => by
          filter_upwards [hU] with z hz
          exact pd_eq_zero_of_eventuallyEq
            (Filter.eventually_of_mem (hU_top_open.mem_nhds hz) fun y hy => (hEk_top p.1 y hy).2) j
        rw [pd_eq_zero_of_eventuallyEq (hev_pd 0) 0, pd_eq_zero_of_eventuallyEq (hev_pd 1) 1, add_zero]
      have hm_le : |m_s p.1| + |deriv m_s p.1| ≤ M_m := by
        have h := hM_m p.1 hp.1; simp only [Pi.add_apply] at h
        rwa [Real.norm_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at h
      have hm0_le : |m_s p.1| ≤ M_m := (le_add_of_nonneg_right (abs_nonneg _)).trans hm_le
      have hdm_le : |deriv m_s p.1| ≤ M_m := (le_add_of_nonneg_left (abs_nonneg _)).trans hm_le
      set B : ℝ := vnorm2 (b_sh p)
      have hB0 : 0 ≤ B := Real.sqrt_nonneg _
      have hb0_le : ‖b_sh p 0‖ ≤ B := norm_le_vnorm2_local _ 0
      have hp_Icc : p.1 ∈ Icc 0 H' := ⟨hs₁.le.trans hp.1.1, hp.1.2.trans hs₂H.le⟩
      have hF01 : ‖F_sh p 0 1‖ ≤ 2 * M_v * B := hF_bd p hp_Icc 0 1
      have hE0 := (hEk_top p.1 p.2 hp_top).1
      have hE1 := (hEk_top p.1 p.2 hp_top).2
      have hCb_tot : ∀ {C_i : ℝ}, C_i ≤ Cb1 + Cb2 + Cb3 →
          (C_i / R_seq k) * M_m ≤ (Cb1 + Cb2 + Cb3) * M_m / R_seq k := by
        intro C_i hCi; rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hM_m0) hRk_pos.le
      have hCb1_nn : 0 ≤ Cb1 := (norm_nonneg _).trans (hCb1 0)
      have hCb2_nn : 0 ≤ Cb2 := (norm_nonneg _).trans (hCb2 0)
      have hCb3_nn : 0 ≤ Cb3 := (norm_nonneg _).trans (hCb3 0)
      unfold flatIntegrand
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [hE0, hE1, hdt0, hdt1, hgr00, hgr01, hgr1, hlp0, hlp1,
        zero_div, zero_mul, Complex.ofReal_zero, mul_zero, sub_zero, zero_add, add_zero, neg_zero]
      have ht1 : ‖-(b_sh p 0 * ((deriv (χ_seq k) p.2.2 * deriv m_s p.1 : ℝ) : ℂ))‖ ≤
          1 * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 := (mul_le_mul (hdχ1_bd p.2.2) hdm_le (abs_nonneg _) (by positivity)).trans
          (hCb_tot (by linarith))
        calc ‖b_sh p 0‖ * (|deriv (χ_seq k) p.2.2| * |deriv m_s p.1|)
            ≤ B * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) := mul_le_mul hb0_le h1 (by positivity) hB0
          _ = 1 * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have ht3 : ‖(ν : ℂ) * b_sh p 0 *
            ((deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          |ν| * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 := (mul_le_mul (hdχ3_bd p.2.2) hm0_le (abs_nonneg _) (by positivity)).trans
          (hCb_tot (by linarith))
        calc |ν| * ‖b_sh p 0‖ * (|deriv (deriv (deriv (χ_seq k))) p.2.2| * |m_s p.1|)
            ≤ |ν| * B * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hb0_le (abs_nonneg _)) h1 (by positivity) (by positivity)
          _ = |ν| * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have ht4 : ‖F_sh p 0 1 * ((deriv (deriv (χ_seq k)) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          (2 * M_v) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h1 := (mul_le_mul (hdχ2_bd p.2.2) hm0_le (abs_nonneg _) (by positivity)).trans
          (hCb_tot (by linarith))
        calc ‖F_sh p 0 1‖ * (|deriv (deriv (χ_seq k)) p.2.2| * |m_s p.1|)
            ≤ (2 * M_v * B) * ((Cb1 + Cb2 + Cb3) * M_m / R_seq k) :=
              mul_le_mul hF01 h1 (by positivity) (by positivity)
          _ = (2 * M_v) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by ring
      have htri : ‖-(b_sh p 0 * ((deriv (χ_seq k) p.2.2 * deriv m_s p.1 : ℝ) : ℂ)) -
          (ν : ℂ) * b_sh p 0 * ((deriv (deriv (deriv (χ_seq k))) p.2.2 * m_s p.1 : ℝ) : ℂ) +
          F_sh p 0 1 * ((deriv (deriv (χ_seq k)) p.2.2 * m_s p.1 : ℝ) : ℂ)‖ ≤
          1 * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) +
            |ν| * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) +
            (2 * M_v) * ((Cb1 + Cb2 + Cb3) * M_m) * (B / R_seq k) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ht4)
        exact (norm_sub_le _ _).trans (add_le_add ht1 ht3)
      refine htri.trans_eq ?_; dsimp [C_err]; ring
    -- AM-GM bound on `S_k`
    set r_k : ℝ := Real.sqrt (R_seq k)
    have hrk_pos : 0 < r_k := Real.sqrt_pos.2 hRk_pos
    have hrk_sq : r_k ^ 2 = R_seq k := Real.sq_sqrt hRk_pos.le
    have hvol_Sk_eq : volume S_k = ENNReal.ofReal ((s₂ - s₁) * c * R_seq k) := by
      dsimp [S_k]
      rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_Icc, Real.volume_Ico, Real.volume_Icc]
      have h1 : c / 2 - -(c / 2) = c := by ring
      have h2 : 2 * R_seq k - R_seq k = R_seq k := by ring
      rw [h1, h2, ← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (sub_nonneg.2 hs₁₂.le)]
      ring_nf
    have hvol_Sk_lt : volume S_k < ⊤ := by rw [hvol_Sk_eq]; exact ENNReal.ofReal_lt_top
    have hc_Sk : IntegrableOn (fun _ : ℝ × (ℝ × ℝ) => (1 / (2 * r_k ^ 3) : ℝ)) S_k :=
      integrableOn_const hvol_Sk_lt.ne
    have hg_Sk : IntegrableOn (fun p => vnorm2 (b_sh p) ^ 2 / (2 * r_k)) S_k :=
      (hb_sq_int.mono_set hSk_sub_strip).div_const _
    have hamgm : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (b_sh p) / R_seq k ≤ 1 / (2 * r_k ^ 3) + vnorm2 (b_sh p) ^ 2 / (2 * r_k) := by
      intro p
      set y := vnorm2 (b_sh p)
      have hdiff : 1 / (2 * r_k ^ 3) + y ^ 2 / (2 * r_k) - y / R_seq k =
          (r_k * y - 1) ^ 2 / (2 * r_k ^ 3) := by
        rw [← hrk_sq]; field_simp [hrk_pos.ne']; ring
      linarith [div_nonneg (sq_nonneg (r_k * y - 1)) (by positivity : (0 : ℝ) ≤ 2 * r_k ^ 3)]
    have hint_B_Sk : IntegrableOn (fun p => vnorm2 (b_sh p) / R_seq k) S_k := by
      refine (hc_Sk.add hg_Sk).mono' (hb_norm_meas.div_const _).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      have hv_nn : 0 ≤ vnorm2 (b_sh p) := Real.sqrt_nonneg _
      dsimp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (div_nonneg hv_nn hRk_pos.le)]
      exact hamgm p
    have hint_B_le : ∫ p in S_k, vnorm2 (b_sh p) / R_seq k ≤
        ((s₂ - s₁) * c + E_tot) / (2 * r_k) := by
      calc ∫ p in S_k, vnorm2 (b_sh p) / R_seq k
          ≤ ∫ p in S_k, (1 / (2 * r_k ^ 3) + vnorm2 (b_sh p) ^ 2 / (2 * r_k)) :=
            setIntegral_mono_on hint_B_Sk (hc_Sk.add hg_Sk) hSk_meas fun p _ => hamgm p
        _ = (∫ _ in S_k, (1 / (2 * r_k ^ 3) : ℝ)) +
              (∫ p in S_k, vnorm2 (b_sh p) ^ 2) / (2 * r_k) := by
            rw [integral_add hc_Sk hg_Sk]; congr 1; exact integral_div (2 * r_k) _
        _ ≤ ((s₂ - s₁) * c * r_k ^ 2) * (1 / (2 * r_k ^ 3)) + E_tot / (2 * r_k) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, hvol_Sk_eq,
              ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (sub_nonneg.2 hs₁₂.le) hc.le) hRk_pos.le),
              ← hrk_sq]
            refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ (by positivity))
            exact setIntegral_mono_set hb_sq_int (Eventually.of_forall fun _ => sq_nonneg _)
              hSk_sub_strip.eventuallyLE
        _ = ((s₂ - s₁) * c + E_tot) / (2 * r_k) := by field_simp [hrk_pos.ne']
    rw [hint_eq, norm_neg, hint_Ek_Sk]
    calc ‖∫ p in S_k, flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p‖
        ≤ ∫ p in S_k, ‖flatIntegrand ν 0 (fun _ _ _ => 0) F_sh b_sh (E_seq k) p‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ p in S_k, C_err * (vnorm2 (b_sh p) / R_seq k) :=
          setIntegral_mono_on (hint_Ek.mono_set hSk_sub_Ioi).norm
            (hint_B_Sk.const_mul C_err) hSk_meas hpt_Sk
      _ = C_err * ∫ p in S_k, vnorm2 (b_sh p) / R_seq k := integral_const_mul _ _
      _ ≤ C_err * (((s₂ - s₁) * c + E_tot) / (2 * r_k)) :=
          mul_le_mul_of_nonneg_left hint_B_le hCerr_nn
  have hlim_zero : Tendsto
      (fun k : ℕ => C_err * (((s₂ - s₁) * c + E_tot) / (2 * Real.sqrt (R_seq k))))
      atTop (𝓝 0) := by
    have hR_top : Tendsto R_seq atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := R₀ + 2))).congr
        fun k => by dsimp [R_seq]; ring
    have hsqrt_top : Tendsto (fun k : ℕ => 2 * Real.sqrt (R_seq k)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop two_pos (Real.tendsto_sqrt_atTop.comp hR_top)
    simpa only [mul_zero] using (tendsto_const_nhds.div_atTop hsqrt_top).const_mul C_err
  exact norm_le_zero_iff.mp (ge_of_tendsto' hlim_zero hbound_k)

/-! ## Section 3: Slice advection bound and smooth-cutoff Grönwall on `[0, T]` -/

private lemma shifted_slice_advection_le {c ν s_r τ : ℝ} (hc : 0 < c) (hs_r : 0 ≤ s_r) (hτ : 0 < τ)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {H' : ℝ} {F_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b_sh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' 0 F_sh b_sh G_sh)
    (hgs : LMGoodSlice c F_sh G_sh b_sh τ)
    (hF_slice : ∀ x i j, F_sh (τ, x) i j =
      -((tr.v (s_r + τ) x i : ℂ) * b_sh (τ, x) j + b_sh (τ, x) i * (tr.v (s_r + τ) x j : ℂ))) :
    -(UnforcedLeray.B0277.supNormD 1 (tr.v (s_r + τ))).toReal * energyE c b_sh τ ≤
      energyR c F_sh G_sh τ := by
  obtain ⟨J, hJ⟩ := hasLMMollifier c hc
  set ρ : ℝ := s_r + τ
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let v : B0579.Plane → UnforcedLeray.Train.Vec := tr.v ρ
  let L : ℝ := (UnforcedLeray.B0277.supNormD 1 v).toReal
  have ⟨hb, hcol, _⟩ := hgs
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound hρ.le
  set M_v : ℝ := max M₀ 0 + 1
  have hMv_pos : 0 < M_v := by dsimp [M_v]; positivity
  have hv_bdd : ∀ (i : Fin 2) (x : B0579.Plane), |v x i| ≤ M_v := fun i x => by
    have h1 : |v x i| ≤ ‖v x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (v x) i
    have h2 : ‖v x‖ ≤ max M₀ 0 := (hM₀ ρ ⟨hρ.le, le_rfl⟩ x).trans (le_max_left _ _)
    dsimp [M_v]; linarith
  let H : B0579.Plane → Fin 2 → Fin 2 → ℂ :=
    fun x i j => (v x i : ℂ) * b_sh (τ, x) j + b_sh (τ, x) i * (v x j : ℂ)
  let H_k : ℕ → B0579.Plane → Fin 2 → Fin 2 → ℂ :=
    fun k x i j => (v x i : ℂ) * LMMollU J b_sh k τ x j + LMMollU J b_sh k τ x i * (v x j : ℂ)
  let G_k : ℕ → B0579.Plane → Fin 2 → Fin 2 → ℂ :=
    fun k x i j => J k (fun y i' => G_sh (τ, y) i' j) x i
  -- Every occurrence of `AdvectionEnergyAux.lmP_pair` replaced by `lmP_pair`
  have hmul_memL2 : ∀ {u : LMSpField}, LMCellL2 c u → ∀ i j : Fin 2,
      MemLp (fun x => (v x i : ℂ) * u x j + u x i * (v x j : ℂ)) 2
        (volume.restrict (B0579.cell c)) := by
    intro u hu i j
    have hv_sm : ContDiff ℝ ∞ v := AdvectionEnergyAux.contDiff_train_slice tr hρ.le
    have hv_meas : ∀ m : Fin 2, AEStronglyMeasurable (fun x => (v x m : ℂ))
        (volume.restrict (B0579.cell c)) := fun m =>
      (Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj m : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
          hv_sm.continuous)).aestronglyMeasurable
    have h1 : MemLp (fun x => (v x i : ℂ) * u x j) 2 (volume.restrict (B0579.cell c)) :=
      MemLp.of_le_mul (c := M_v) (hu j) ((hv_meas i).mul (hu j).1) (Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hv_bdd i x) (norm_nonneg _))
    have h2 : MemLp (fun x => u x i * (v x j : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
      MemLp.of_le_mul (c := M_v) (hu i) ((hu i).1.mul (hv_meas j)) (Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hv_bdd j x) (norm_nonneg _))
    exact h1.add h2
  have hH_L2 : ∀ j : Fin 2, LMCellL2 c (fun x i => H x i j) := fun j i => hmul_memL2 hb i j
  have hHk_L2 : ∀ (k : ℕ) (j : Fin 2), LMCellL2 c (fun x i => H_k k x i j) :=
    fun k j i => hmul_memL2 (hJ.memL2 k _ hb) i j
  have hGk_L2 : ∀ (k : ℕ) (j : Fin 2), LMCellL2 c (fun x i => G_k k x i j) :=
    fun k j => hJ.memL2 k _ (hcol j)
  have hpd : ∀ (k : ℕ) (x : B0579.Plane) (i j : Fin 2),
      LMPd j (fun y => LMMollU J b_sh k τ y i) x = G_k k x i j :=
    fun k x i j => lmMoll_pd_eq hJ hb hcol (fun i' j' => hD.weakGrad τ hτ i' j') k i j x
  -- Apply `moll_slice_advection_le` at physical age `ρ` to time-constant `b_const (_, y) := b_sh (τ, y)`
  have hbd_k : ∀ k : ℕ,
      (∫ x in B0579.cell c, lmP_pair (H_k k) (G_k k) x) ≤
        L * energyE c b_sh τ := by
    intro k
    let b_const : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun q => b_sh (τ, q.2)
    have h1 := AdvectionEnergyAux.moll_slice_advection_le hc tr htr hJ (b := b_const) hρ hb
      (hD.divFree τ hτ) k
    have hmollU_eq : LMMollU J b_const k ρ = LMMollU J b_sh k τ := rfl
    have hmollE_eq : LMMollE c J b_const k ρ = LMMollE c J b_sh k τ := rfl
    rw [hmollU_eq, hmollE_eq] at h1
    have heq : (fun x => lmP_pair (H_k k)
        (fun x i j => LMPd j (fun y => LMMollU J b_sh k τ y i) x) x) =
        fun x => lmP_pair (H_k k) (G_k k) x := by
      funext x; unfold lmP_pair; simp only [hpd]
    rw [heq] at h1
    have hdom := (domEN_trunc hD hJ hτ hgs k).2.1
    exact h1.trans (mul_le_mul_of_nonneg_left hdom ENNReal.toReal_nonneg)
  have h_tendsto_HGk : Tendsto
      (fun k : ℕ => ∫ x in B0579.cell c, lmP_pair H (G_k k) x)
      atTop (𝓝 (-energyR c F_sh G_sh τ)) := by
    have h1 := lm_tendsto_tpair (c := c)
      (T := G_k) (T₀ := fun x i j => G_sh (τ, x) i j) (H := H)
      hGk_L2 hcol hH_L2 (fun j => hJ.tendsto _ (hcol j))
    have hneg_eq : (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
          ((H x i j).re * (G_sh (τ, x) i j).re + (H x i j).im * (G_sh (τ, x) i j).im)) =
        -energyR c F_sh G_sh τ := by
      unfold energyR
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hf := hF_slice x i j
      have hre : (F_sh (τ, x) i j).re = -(H x i j).re := by rw [hf]; simp [H, v]
      have him : (F_sh (τ, x) i j).im = -(H x i j).im := by rw [hf]; simp [H, v]
      rw [hre, him]; ring
    rw [← hneg_eq]
    exact h1
  have h_tendsto_diff : Tendsto (fun k : ℕ =>
      (∫ x in B0579.cell c, lmP_pair (H_k k) (G_k k) x) -
        ∫ x in B0579.cell c, lmP_pair H (G_k k) x) atTop (𝓝 0) := by
    have hH_diff_pt : ∀ (k : ℕ) (x : B0579.Plane) (i j : Fin 2),
        ‖H_k k x i j - H x i j‖ ^ 2 ≤
          8 * M_v ^ 2 * ∑ m : Fin 2, ‖LMMollU J b_sh k τ x m - b_sh (τ, x) m‖ ^ 2 := by
      intro k x i j
      have hsub : H_k k x i j - H x i j =
          (v x i : ℂ) * (LMMollU J b_sh k τ x j - b_sh (τ, x) j) +
            (LMMollU J b_sh k τ x i - b_sh (τ, x) i) * (v x j : ℂ) := by
        dsimp [H_k, H]; ring
      have h_le_sum : ∀ m : Fin 2, ‖LMMollU J b_sh k τ x m - b_sh (τ, x) m‖ ≤
          ‖LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0‖ + ‖LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1‖ := by
        intro m; fin_cases m
        · change ‖LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0‖ ≤ _
          linarith [norm_nonneg (LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1)]
        · change ‖LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1‖ ≤ _
          linarith [norm_nonneg (LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0)]
      have h1 : ‖H_k k x i j - H x i j‖ ≤
          2 * M_v * (‖LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0‖ +
            ‖LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1‖) := by
        rw [hsub]
        have ha : ‖(v x i : ℂ) * (LMMollU J b_sh k τ x j - b_sh (τ, x) j)‖ ≤
            M_v * (‖LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0‖ + ‖LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact (mul_le_mul_of_nonneg_right (hv_bdd i x) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (h_le_sum j) hMv_pos.le)
        have hb' : ‖(LMMollU J b_sh k τ x i - b_sh (τ, x) i) * (v x j : ℂ)‖ ≤
            M_v * (‖LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0‖ + ‖LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact (mul_le_mul_of_nonneg_right (hv_bdd j x) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (h_le_sum i) hMv_pos.le)
        linarith [norm_add_le ((v x i : ℂ) * (LMMollU J b_sh k τ x j - b_sh (τ, x) j))
          ((LMMollU J b_sh k τ x i - b_sh (τ, x) i) * (v x j : ℂ))]
      rw [Fin.sum_univ_two]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖LMMollU J b_sh k τ x 0 - b_sh (τ, x) 0‖ -
        ‖LMMollU J b_sh k τ x 1 - b_sh (τ, x) 1‖)]
    have hD_int : ∀ k : ℕ, Integrable
        (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2)
        (volume.restrict (B0579.cell c)) := fun k =>
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
        lmP_sq_integrable ((hHk_L2 k j i).sub (hH_L2 j i))
    have hU_int : ∀ k : ℕ, Integrable
        (fun x => ∑ m : Fin 2, ‖LMMollU J b_sh k τ x m - b_sh (τ, x) m‖ ^ 2)
        (volume.restrict (B0579.cell c)) := fun k =>
      integrable_finsetSum _ fun m _ => lmP_sq_integrable ((hJ.memL2 k _ hb m).sub (hb m))
    have hD_lim : Tendsto (fun k : ℕ => ∫ x in B0579.cell c,
        ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2) atTop (𝓝 0) := by
      have hU_lim : Tendsto (fun k : ℕ => 32 * M_v ^ 2 * ∫ x in B0579.cell c,
          ∑ m : Fin 2, ‖LMMollU J b_sh k τ x m - b_sh (τ, x) m‖ ^ 2) atTop (𝓝 0) := by
        simpa only [mul_zero, LMMollU] using (hJ.tendsto _ hb).const_mul (32 * M_v ^ 2)
      refine squeeze_zero (fun k => integral_nonneg fun x =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun k => ?_) hU_lim
      rw [← integral_const_mul (32 * M_v ^ 2)]
      refine integral_mono (hD_int k) ((hU_int k).const_mul _) fun x => ?_
      rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      linarith [hH_diff_pt k x 0 0, hH_diff_pt k x 0 1, hH_diff_pt k x 1 0, hH_diff_pt k x 1 1]
    set M_N : ℝ := energyN c G_sh τ
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hMN0 : 0 ≤ M_N := integral_nonneg fun _ => sq_nonneg _
    let l : ℝ := ε / (2 * (M_N + 1))
    have hlpos : 0 < l := div_pos hε (by linarith)
    have hlM : l * M_N ≤ ε / 2 := by
      have e : ε = 2 * (l * M_N) + 2 * l := by dsimp [l]; field_simp
      linarith
    filter_upwards [hD_lim.eventually (gt_mem_nhds (mul_pos hlpos hε))] with k hk
    have hP1 : Integrable (lmP_pair (H_k k) (G_k k))
        (volume.restrict (B0579.cell c)) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        lmP_mul_integrable (hHk_L2 k j i) (hGk_L2 k j i)
    have hP2 : Integrable (lmP_pair H (G_k k))
        (volume.restrict (B0579.cell c)) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        lmP_mul_integrable (hH_L2 j i) (hGk_L2 k j i)
    have hGk_sq_int : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2)
        (volume.restrict (B0579.cell c)) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => lmP_sq_integrable (hGk_L2 k j i)
    have hpt_comm : ∀ x, 2 * l * |lmP_pair (H_k k) (G_k k) x -
        lmP_pair H (G_k k) x| ≤
        l ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) +
          ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2 := by
      intro x
      have hcomm1 : lmP_pair (H_k k) (G_k k) x =
          lmP_pair (G_k k) (H_k k) x := by
        unfold lmP_pair; congr 1; funext i; congr 1; funext j; ring
      have hcomm2 : lmP_pair H (G_k k) x =
          lmP_pair (G_k k) H x := by
        unfold lmP_pair; congr 1; funext i; congr 1; funext j; ring
      rw [hcomm1, hcomm2]
      exact lmP_pt_bound (G_k k x) (H_k k x) (H x) l hlpos
    have key1 := lmP_abs_integral_sub_le (lmP_pair (H_k k) (G_k k))
      (lmP_pair H (G_k k))
      (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2)
      (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ‖H_k k x i j - H x i j‖ ^ 2)
      l hlpos hP1 hP2 hGk_sq_int (hD_int k) hpt_comm
    have hGk_le_MN : (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) ≤ M_N := by
      have heq_N : (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) =
          LMMollN c J b_sh k τ := by
        unfold LMMollN
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only; rw [domEN_tnorm2_sq]; simp only [hpd]
      rw [heq_N]
      exact (domEN_trunc hD hJ hτ hgs k).2.2.2
    have h3 : l ^ 2 * (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2) ≤
        l * ε / 2 := by
      calc l ^ 2 * (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖G_k k x i j‖ ^ 2)
          ≤ l ^ 2 * M_N := mul_le_mul_of_nonneg_left hGk_le_MN (sq_nonneg l)
        _ = l * (l * M_N) := by ring
        _ ≤ l * (ε / 2) := mul_le_mul_of_nonneg_left hlM hlpos.le
        _ = l * ε / 2 := by ring
    have h4 : 2 * l * |(∫ x in B0579.cell c, lmP_pair (H_k k) (G_k k) x) -
        (∫ x in B0579.cell c, lmP_pair H (G_k k) x)| < 2 * l * ε := by
      linarith [key1, h3, hk, mul_pos hlpos hε]
    rw [Real.dist_eq, sub_zero]
    exact lt_of_mul_lt_mul_left h4 (by linarith)
  have h_tendsto : Tendsto
      (fun k : ℕ => ∫ x in B0579.cell c, lmP_pair (H_k k) (G_k k) x)
      atTop (𝓝 (-energyR c F_sh G_sh τ)) := by
    have h1 := h_tendsto_diff.add h_tendsto_HGk
    rw [zero_add] at h1
    exact h1.congr fun k => sub_add_cancel _ _
  have hlim_le : -energyR c F_sh G_sh τ ≤ L * energyE c b_sh τ :=
    le_of_tendsto' h_tendsto hbd_k
  linarith

/-! ### Smooth-cutoff Grönwall inequality for continuous `E` -/

private def gronwallCut (T δ τ : ℝ) : ℝ :=
  Real.smoothTransition ((τ - δ) / δ) * Real.smoothTransition ((T - δ - τ) / δ)

private lemma gronwallCut_props {T δ : ℝ} (hδ : 0 < δ) (hT : 4 * δ < T) :
    ContDiff ℝ ∞ (gronwallCut T δ) ∧
      HasCompactSupport (gronwallCut T δ) ∧
      tsupport (gronwallCut T δ) ⊆ Icc δ (T - δ) ∧
      (∀ τ, 0 ≤ gronwallCut T δ τ ∧ gronwallCut T δ τ ≤ 1) ∧
      gronwallCut T δ δ = 0 ∧
      gronwallCut T δ (2 * δ) = 1 ∧
      gronwallCut T δ (T - 2 * δ) = 1 ∧
      gronwallCut T δ (T - δ) = 0 ∧
      (∀ τ ∈ Icc δ (2 * δ), 0 ≤ deriv (gronwallCut T δ) τ) ∧
      (∀ τ ∈ Ioo (2 * δ) (T - 2 * δ), deriv (gronwallCut T δ) τ = 0) ∧
      (∀ τ ∈ Icc (T - 2 * δ) (T - δ), deriv (gronwallCut T δ) τ ≤ 0) := by
  have hsm : ContDiff ℝ ∞ (gronwallCut T δ) := by
    unfold gronwallCut
    exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
      (Real.smoothTransition.contDiff.comp
        (((contDiff_const (c := T - δ)).sub contDiff_id).div_const δ))
  have hzero_out : ∀ τ, τ ∉ Icc δ (T - δ) → gronwallCut T δ τ = 0 := by
    intro τ hτ; unfold gronwallCut
    by_cases h1 : τ ≤ δ
    · have hnp : (τ - δ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      rw [Real.smoothTransition.zero_of_nonpos hnp, zero_mul]
    · have h2 : T - δ ≤ τ := by
        by_contra hc; exact hτ ⟨by linarith, by linarith⟩
      have hnp : (T - δ - τ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      rw [Real.smoothTransition.zero_of_nonpos hnp, mul_zero]
  have hts : tsupport (gronwallCut T δ) ⊆ Icc δ (T - δ) := by
    refine closure_minimal (fun τ hτ => ?_) isClosed_Icc
    by_contra hc; exact hτ (hzero_out τ hc)
  have hcs : HasCompactSupport (gronwallCut T δ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
  have h01 : ∀ τ, 0 ≤ gronwallCut T δ τ ∧ gronwallCut T δ τ ≤ 1 := fun τ =>
    ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
      mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)⟩
  have hval_δ : gronwallCut T δ δ = 0 := by
    unfold gronwallCut; simp [Real.smoothTransition.zero_of_nonpos]
  have hval_2δ : gronwallCut T δ (2 * δ) = 1 := by
    unfold gronwallCut
    have h1 : 1 ≤ (2 * δ - δ) / δ := by rw [le_div_iff₀ hδ]; linarith
    have h2 : 1 ≤ (T - δ - 2 * δ) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]
  have hval_T2δ : gronwallCut T δ (T - 2 * δ) = 1 := by
    unfold gronwallCut
    have h1 : 1 ≤ (T - 2 * δ - δ) / δ := by rw [le_div_iff₀ hδ]; linarith
    have h2 : 1 ≤ (T - δ - (T - 2 * δ)) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]
  have hval_Tδ : gronwallCut T δ (T - δ) = 0 := by
    unfold gronwallCut; simp [Real.smoothTransition.zero_of_nonpos]
  have hd_left : ∀ τ ∈ Icc δ (2 * δ), 0 ≤ deriv (gronwallCut T δ) τ := by
    intro τ hτ
    have hlt : τ < T - 2 * δ := by linarith [hτ.2]
    have hev : gronwallCut T δ =ᶠ[𝓝 τ] fun s => Real.smoothTransition ((s - δ) / δ) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      have hs' : s < T - 2 * δ := hs
      have h2 : 1 ≤ (T - δ - s) / δ := by rw [le_div_iff₀ hδ]; linarith
      unfold gronwallCut
      rw [Real.smoothTransition.one_of_one_le h2, mul_one]
    rw [hev.deriv_eq]
    have hin : HasDerivAt (fun s : ℝ => (s - δ) / δ) (1 / δ) τ :=
      ((hasDerivAt_id' τ).sub_const δ).div_const δ
    have hdσ : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition ((τ - δ) / δ)) ((τ - δ) / δ) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    change 0 ≤ deriv (Real.smoothTransition ∘ fun s => (s - δ) / δ) τ
    rw [(HasDerivAt.comp τ hdσ hin).deriv]
    exact mul_nonneg (Monotone.deriv_nonneg Real.smoothTransition.monotone) (by positivity)
  have hd_mid : ∀ τ ∈ Ioo (2 * δ) (T - 2 * δ), deriv (gronwallCut T δ) τ = 0 := by
    intro τ hτ
    have hev : gronwallCut T δ =ᶠ[𝓝 τ] fun _ => (1 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with s hs
      have h1 : 1 ≤ (s - δ) / δ := by rw [le_div_iff₀ hδ]; linarith [hs.1]
      have h2 : 1 ≤ (T - δ - s) / δ := by rw [le_div_iff₀ hδ]; linarith [hs.2]
      unfold gronwallCut
      rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]
    rw [hev.deriv_eq]; simp
  have hd_right : ∀ τ ∈ Icc (T - 2 * δ) (T - δ), deriv (gronwallCut T δ) τ ≤ 0 := by
    intro τ hτ
    have hgt : 2 * δ < τ := by linarith [hτ.1]
    have hev : gronwallCut T δ =ᶠ[𝓝 τ] fun s => Real.smoothTransition ((T - δ - s) / δ) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      have hs' : 2 * δ < s := hs
      have h1 : 1 ≤ (s - δ) / δ := by rw [le_div_iff₀ hδ]; linarith
      unfold gronwallCut
      rw [Real.smoothTransition.one_of_one_le h1, one_mul]
    rw [hev.deriv_eq]
    have hin : HasDerivAt (fun s : ℝ => (T - δ - s) / δ) ((0 - 1) / δ) τ :=
      ((hasDerivAt_const τ (T - δ)).sub (hasDerivAt_id' τ)).div_const δ
    have hdσ : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition ((T - δ - τ) / δ)) ((T - δ - τ) / δ) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    change deriv (Real.smoothTransition ∘ fun s => (T - δ - s) / δ) τ ≤ 0
    rw [(HasDerivAt.comp τ hdσ hin).deriv]
    have h1 : 0 ≤ deriv Real.smoothTransition ((T - δ - τ) / δ) :=
      Monotone.deriv_nonneg Real.smoothTransition.monotone
    have h2 : (0 - 1) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hδ.le
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  exact ⟨hsm, hcs, hts, h01, hval_δ, hval_2δ, hval_T2δ, hval_Tδ, hd_left, hd_mid, hd_right⟩

private lemma gronwall_energy_le {c ν T H' M_L : ℝ} (hT : 0 < T) (hH' : H' = T + 1)
    (hML : 0 ≤ M_L)
    {F_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b_sh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' 0 F_sh b_sh G_sh)
    (hE_cont : Continuous (energyE c b_sh))
    (hN_cont : Continuous (energyN c G_sh))
    {L_sh : ℝ → ℝ} (hL_meas : Measurable L_sh)
    (hL_nn : ∀ τ ∈ Icc 0 T, 0 ≤ L_sh τ) (hL_bd : ∀ τ ∈ Icc 0 T, L_sh τ ≤ M_L)
    (hR_adv : ∀ τ ∈ Ioo 0 T, -L_sh τ * energyE c b_sh τ ≤ energyR c F_sh G_sh τ) :
    energyE c b_sh T ≤ Real.exp (2 * ∫ τ in Icc 0 T, L_sh τ) * energyE c b_sh 0 := by
  set E := energyE c b_sh
  set N := energyN c G_sh
  set R := energyR c F_sh G_sh
  have hE_nn : ∀ τ, 0 ≤ E τ := fun τ => integral_nonneg fun _ => sq_nonneg _
  have hN_nn : ∀ τ, 0 ≤ N τ := fun τ => integral_nonneg fun _ => sq_nonneg _
  set L_0 : ℝ → ℝ := (Icc 0 T).indicator L_sh
  have hL0_meas : Measurable L_0 := hL_meas.indicator measurableSet_Icc
  have hL0_nn : ∀ τ, 0 ≤ L_0 τ := fun τ => by
    by_cases hτ : τ ∈ Icc 0 T
    · simp [L_0, hτ, hL_nn τ hτ]
    · simp [L_0, hτ]
  have hL0_bd : ∀ τ, L_0 τ ≤ M_L := fun τ => by
    by_cases hτ : τ ∈ Icc 0 T
    · simp [L_0, hτ, hL_bd τ hτ]
    · simp [L_0, hτ, hML]
  have hL0_int : Integrable L_0 volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    refine (integrableOn_const (C := M_L) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
      hL_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [Real.norm_of_nonneg (hL_nn τ hτ)]
    exact hL_bd τ hτ
  have hL0_loc : LocallyIntegrable L_0 volume := hL0_int.locallyIntegrable
  set L_n : ℕ → ℝ → ℝ := fun n => SmoothToC1Aux.sm L_0 n
  have hLn_sm : ∀ n, ContDiff ℝ ∞ (L_n n) :=
    fun n => TailEnergyBoundAux.sm_contDiff_of_locallyIntegrable hL0_loc n
  have hLn_nn : ∀ n τ, 0 ≤ L_n n τ :=
    fun n τ => SmoothToC1Aux.sm_nonneg L_0 hL0_nn n τ
  have hLn_bd : ∀ n τ, L_n n τ ≤ M_L :=
    fun n τ => TailEnergyBoundAux.sm_le_of_le hL0_meas hL0_nn hL0_bd n τ
  have hLn_ae : ∀ᵐ τ ∂volume, Tendsto (fun n => L_n n τ) atTop (𝓝 (L_0 τ)) :=
    TailEnergyBoundAux.sm_ae_tendsto_of_locallyIntegrable hL0_loc
  set A_0 : ℝ → ℝ := fun τ => Real.exp (-2 * ∫ σ in (0 : ℝ)..τ, L_0 σ)
  set A_n : ℕ → ℝ → ℝ := fun n τ => Real.exp (-2 * ∫ σ in (0 : ℝ)..τ, L_n n σ)
  -- Pointwise convergence `A_n τ → A_0 τ` for `τ ≥ 0`
  have hAn_tendsto : ∀ τ : ℝ, 0 ≤ τ → Tendsto (fun n => A_n n τ) atTop (𝓝 (A_0 τ)) := by
    intro τ hτ
    have hint_lim : Tendsto (fun n => ∫ σ in (0 : ℝ)..τ, L_n n σ) atTop
        (𝓝 (∫ σ in (0 : ℝ)..τ, L_0 σ)) := by
      simp_rw [intervalIntegral.integral_of_le hτ]
      refine tendsto_integral_of_dominated_convergence (fun _ => M_L)
        (fun n => (hLn_sm n).continuous.aestronglyMeasurable.restrict)
        (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        (fun n => Eventually.of_forall fun σ => by
          rw [Real.norm_of_nonneg (hLn_nn n σ)]; exact hLn_bd n σ)
        (ae_restrict_of_ae hLn_ae)
    exact Real.continuous_exp.continuousAt.tendsto.comp (hint_lim.const_mul (-2))
  have hAn_01 : ∀ n τ, 0 ≤ τ → 0 < A_n n τ ∧ A_n n τ ≤ 1 := by
    intro n τ hτ
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
    have : 0 ≤ ∫ σ in (0 : ℝ)..τ, L_n n σ :=
      intervalIntegral.integral_nonneg hτ fun σ _ => hLn_nn n σ
    linarith
  have hA0_01 : ∀ τ, 0 ≤ τ → 0 < A_0 τ ∧ A_0 τ ≤ 1 := by
    intro τ hτ
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
    have : 0 ≤ ∫ σ in (0 : ℝ)..τ, L_0 σ :=
      intervalIntegral.integral_nonneg hτ fun σ _ => hL0_nn σ
    linarith
  have hA0_cont : Continuous A_0 := by
    refine Real.continuous_exp.comp (continuous_const.mul ?_)
    exact intervalIntegral.continuous_primitive (fun _ _ => hL0_int.intervalIntegrable) 0
  set I_L : ℝ := ∫ τ in Icc 0 T, L_sh τ
  have hIL_eq : ∫ σ in (0 : ℝ)..T, L_0 σ = I_L := by
    rw [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    simp [L_0, hσ]
  have hA0_ge_AT : ∀ τ ∈ Icc 0 T, Real.exp (-2 * I_L) ≤ A_0 τ := by
    intro τ hτ
    dsimp [A_0]
    rw [← hIL_eq]
    apply Real.exp_le_exp.2
    have hsub : ∫ σ in (0 : ℝ)..τ, L_0 σ ≤ ∫ σ in (0 : ℝ)..T, L_0 σ := by
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hL0_int.intervalIntegrable (a := 0) (b := τ))
        (hL0_int.intervalIntegrable (a := τ) (b := T))
      rw [← hadj]
      have : 0 ≤ ∫ σ in τ..T, L_0 σ :=
        intervalIntegral.integral_nonneg hτ.2 fun σ _ => hL0_nn σ
      linarith
    linarith
  -- Key `ε`-inequality: for every `ε > 0`, `exp(-2 * I_L) * (E T - ε) ≤ E 0 + ε`
  have h_eps : ∀ ε > 0, Real.exp (-2 * I_L) * (E T - ε) ≤ E 0 + ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hE0_close⟩ := Metric.continuousAt_iff.1 (hE_cont.continuousAt (x := 0)) ε hε
    obtain ⟨δ₂, hδ₂, hET_close⟩ := Metric.continuousAt_iff.1 (hE_cont.continuousAt (x := T)) ε hε
    set δ : ℝ := min (min (δ₁ / 3) (δ₂ / 3)) (T / 5)
    have hδ : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hδ1 : 2 * δ < δ₁ := by
      have : δ ≤ δ₁ / 3 := (min_le_left _ _).trans (min_le_left _ _)
      linarith
    have hδ2 : 2 * δ < δ₂ := by
      have : δ ≤ δ₂ / 3 := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    have h4δT : 4 * δ < T := by
      have : δ ≤ T / 5 := min_le_right _ _
      linarith
    obtain ⟨hχ_sm, hχ_cs, hχ_ts, hχ_01, hχ_δ, hχ_2δ, hχ_T2δ, hχ_Tδ, hd_left, hd_mid, hd_right⟩ :=
      gronwallCut_props hδ h4δT
    set χ := gronwallCut T δ
    -- Test `coreIdentity_trunc` with `w_n τ := A_n n τ * χ τ`
    have h_ineq_n : ∀ n : ℕ,
        ∫ τ in Icc δ (T - δ), (-2 * L_n n τ * A_n n τ * χ τ + A_n n τ * deriv χ τ) * E τ ≥
          ∫ τ in Icc δ (T - δ), A_n n τ * χ τ * (-2 * L_0 τ * E τ) := by
      intro n
      set w_n : ℝ → ℝ := fun τ => A_n n τ * χ τ
      have hAn_sm : ContDiff ℝ ∞ (A_n n) := by
        have hprim : ContDiff ℝ ∞ (fun τ => ∫ σ in (0 : ℝ)..τ, L_n n σ) := by
          rw [contDiff_infty_iff_deriv]
          have hderiv_eq : deriv (fun τ => ∫ σ in (0 : ℝ)..τ, L_n n σ) = L_n n := by
            funext τ
            exact ((L_n n) |> fun f => intervalIntegral.integral_hasDerivAt_right
              ((hLn_sm n).continuous.intervalIntegrable 0 τ)
              ((hLn_sm n).continuous.stronglyMeasurableAtFilter _ _)
              (hLn_sm n).continuous.continuousAt).deriv
          refine ⟨fun τ => (intervalIntegral.integral_hasDerivAt_right
            ((hLn_sm n).continuous.intervalIntegrable 0 τ)
            ((hLn_sm n).continuous.stronglyMeasurableAtFilter _ _)
            (hLn_sm n).continuous.continuousAt).differentiableAt, ?_⟩
          rw [hderiv_eq]; exact hLn_sm n
        exact Real.contDiff_exp.comp (contDiff_const.mul hprim)
      have hwn_sm : ContDiff ℝ ∞ w_n := hAn_sm.mul hχ_sm
      have hwn_ts : tsupport w_n ⊆ Icc δ (T - δ) :=
        Subset.trans tsupport_mul_subset_right hχ_ts
      have hwn_cs : HasCompactSupport w_n :=
        isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hwn_ts
      have hwn_Ioo : tsupport w_n ⊆ Ioo 0 H' :=
        Subset.trans hwn_ts fun τ hτ => ⟨lt_of_lt_of_le hδ hτ.1, by rw [hH']; linarith [hτ.2]⟩
      have hid := coreIdentity_trunc hD hwn_sm hwn_cs hwn_Ioo
      have hderiv_wn : ∀ τ : ℝ, deriv w_n τ =
          -2 * L_n n τ * A_n n τ * χ τ + A_n n τ * deriv χ τ := by
        intro τ
        have hd_int : HasDerivAt (fun τ' => ∫ σ in (0 : ℝ)..τ', L_n n σ) (L_n n τ) τ :=
          intervalIntegral.integral_hasDerivAt_right
            ((hLn_sm n).continuous.intervalIntegrable 0 τ)
            ((hLn_sm n).continuous.stronglyMeasurableAtFilter _ _)
            (hLn_sm n).continuous.continuousAt
        have hd_An : HasDerivAt (A_n n) (-2 * L_n n τ * A_n n τ) τ := by
          have h1 := (hd_int.const_mul (-2)).exp
          simpa [A_n, mul_comm, mul_left_comm, mul_assoc] using h1
        have hd_χ : HasDerivAt χ (deriv χ τ) τ := (hχ_sm.differentiable (by simp) τ).hasDerivAt
        exact (hd_An.mul hd_χ).deriv
      have hsub_Ioi : Icc δ (T - δ) ⊆ Ioi (0 : ℝ) := fun τ hτ => lt_of_lt_of_le hδ hτ.1
      have hLHS_eq : ∫ τ in Ioi (0 : ℝ), deriv w_n τ * E τ =
          ∫ τ in Icc δ (T - δ), (-2 * L_n n τ * A_n n τ * χ τ + A_n n τ * deriv χ τ) * E τ := by
        have h1 := MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume)
          (f := fun τ => deriv w_n τ * E τ)
          measurableSet_Ioi.nullMeasurableSet hsub_Ioi
          (Eventually.of_forall fun τ hτ => by
            have hnot : τ ∉ tsupport (deriv w_n) :=
              fun hm => hτ.2 (hwn_ts (tsupport_deriv_subset hm))
            rw [image_eq_zero_of_notMem_tsupport (f := deriv w_n) hnot, zero_mul])
        rw [h1]
        exact setIntegral_congr_fun measurableSet_Icc fun τ _ => by rw [hderiv_wn τ]
      have hR_int : IntegrableOn R (Icc δ (T - δ)) := by
        have hδT : δ < T - δ := by linarith
        have hF_loc := hD.l2loc δ (T - δ) hδ hδT
        have hG_loc := hD.energyLoc δ (T - δ) hδ hδT
        have hF_meas_sq : Measurable fun p => tnorm2 (F_sh p) ^ 2 := by
          unfold tnorm2
          exact (Real.continuous_sqrt.measurable.comp (Finset.measurable_sum Finset.univ fun i _ =>
            Finset.measurable_sum Finset.univ fun j _ => (hD.meas i j).norm.pow_const 2)).pow_const 2
        have hG_meas_sq : Measurable fun p => tnorm2 (G_sh p) ^ 2 := by
          unfold tnorm2
          exact (Real.continuous_sqrt.measurable.comp (Finset.measurable_sum Finset.univ fun i _ =>
            Finset.measurable_sum Finset.univ fun j _ => (hD.gradMeasurable i j).norm.pow_const 2)).pow_const 2
        have hF_int : IntegrableOn (fun p => tnorm2 (F_sh p) ^ 2) (Icc δ (T - δ) ×ˢ B0579.cell c) :=
          ⟨hF_meas_sq.aestronglyMeasurable,
            (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).2 hF_loc⟩
        have hG_int : IntegrableOn (fun p => tnorm2 (G_sh p) ^ 2) (Icc δ (T - δ) ×ˢ B0579.cell c) := by
          refine ⟨hG_meas_sq.aestronglyMeasurable,
            (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).2 ?_⟩
          refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) hG_loc
          linarith [sq_nonneg (vnorm2 (b_sh p))]
        rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hF_int hG_int
        have hpair_meas : Measurable fun p : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ∑ j : Fin 2,
            ((F_sh p i j).re * (G_sh p i j).re + (F_sh p i j).im * (G_sh p i j).im) := by
          refine Finset.measurable_sum Finset.univ fun i _ => Finset.measurable_sum Finset.univ fun j _ => ?_
          exact ((Complex.continuous_re.measurable.comp (hD.meas i j)).mul
            (Complex.continuous_re.measurable.comp (hD.gradMeasurable i j))).add
            ((Complex.continuous_im.measurable.comp (hD.meas i j)).mul
              (Complex.continuous_im.measurable.comp (hD.gradMeasurable i j)))
        have hprod_int : Integrable
            (fun p => ∑ i : Fin 2, ∑ j : Fin 2,
              ((F_sh p i j).re * (G_sh p i j).re + (F_sh p i j).im * (G_sh p i j).im))
            ((volume.restrict (Icc δ (T - δ))).prod (volume.restrict (B0579.cell c))) := by
          refine (hF_int.add hG_int).mono' hpair_meas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
          have htF : tnorm2 (F_sh p) ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖F_sh p i j‖ ^ 2 :=
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          have htG : tnorm2 (G_sh p) ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖G_sh p i j‖ ^ 2 :=
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          rw [Pi.add_apply, htF, htG, ← Finset.sum_add_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [Real.norm_eq_abs, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
            Complex.normSq_apply, Complex.normSq_apply]
          have h1 := sq_nonneg ((F_sh p i j).re - (G_sh p i j).re)
          have h2 := sq_nonneg ((F_sh p i j).im - (G_sh p i j).im)
          have h3 := sq_nonneg ((F_sh p i j).re + (G_sh p i j).re)
          have h4 := sq_nonneg ((F_sh p i j).im + (G_sh p i j).im)
          exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
        exact hprod_int.integral_prod_left
      have hRHS_eq : ∫ τ in Ioi (0 : ℝ), w_n τ * (2 * (0 : ℂ).re / τ * E τ + 2 * ν * N τ + 2 * R τ) =
          ∫ τ in Icc δ (T - δ), w_n τ * (2 * ν * N τ + 2 * R τ) := by
        have h1 := MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume)
          (f := fun τ => w_n τ * (2 * (0 : ℂ).re / τ * E τ + 2 * ν * N τ + 2 * R τ))
          measurableSet_Ioi.nullMeasurableSet hsub_Ioi
          (Eventually.of_forall fun τ hτ => by
            have hnot : τ ∉ tsupport w_n := fun hm => hτ.2 (hwn_ts hm)
            rw [image_eq_zero_of_notMem_tsupport (f := w_n) hnot, zero_mul])
        rw [h1]
        exact setIntegral_congr_fun measurableSet_Icc fun τ _ => by simp
      rw [hLHS_eq, hRHS_eq] at hid
      rw [hid]
      have hint_lhs : IntegrableOn (fun τ => A_n n τ * χ τ * (-2 * L_0 τ * E τ)) (Icc δ (T - δ)) := by
        have hc_part : ContinuousOn (fun τ => A_n n τ * χ τ * E τ) (Icc δ (T - δ)) :=
          ((hwn_sm.continuous).mul hE_cont).continuousOn
        obtain ⟨M_c, hM_c⟩ :=
          isCompact_Icc.exists_bound_of_continuousOn (s := Icc δ (T - δ)) hc_part
        refine (hL0_int.restrict.const_mul (2 * M_c)).mono'
          ((hwn_sm.continuous.measurable.mul ((measurable_const.mul hL0_meas).mul
            hE_cont.measurable)).aestronglyMeasurable.restrict) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        have hc_le := hM_c τ hτ
        have hMc0 : 0 ≤ M_c := (norm_nonneg _).trans hc_le
        have h1 : ‖A_n n τ * χ τ * (-2 * L_0 τ * E τ)‖ =
            2 * L_0 τ * ‖A_n n τ * χ τ * E τ‖ := by
          rw [show A_n n τ * χ τ * (-2 * L_0 τ * E τ) = (-2 * L_0 τ) * (A_n n τ * χ τ * E τ) by ring,
            norm_mul, Real.norm_eq_abs, abs_mul, (show |(-2 : ℝ)| = 2 by norm_num),
            abs_of_nonneg (hL0_nn τ)]
        rw [h1]
        calc 2 * L_0 τ * ‖A_n n τ * χ τ * E τ‖
            ≤ 2 * L_0 τ * M_c := mul_le_mul_of_nonneg_left hc_le (mul_nonneg (by norm_num) (hL0_nn τ))
          _ = 2 * M_c * L_0 τ := by ring
      have hint_rhs : IntegrableOn (fun τ => w_n τ * (2 * ν * N τ + 2 * R τ)) (Icc δ (T - δ)) := by
        have h1 : IntegrableOn (fun τ => w_n τ * (2 * ν * N τ)) (Icc δ (T - δ)) :=
          (hwn_sm.continuous.mul (continuous_const.mul hN_cont)).continuousOn.integrableOn_Icc
        obtain ⟨M_w, hM_w⟩ :=
          isCompact_Icc.exists_bound_of_continuousOn (s := Icc δ (T - δ)) hwn_sm.continuous.continuousOn
        have h2 : IntegrableOn (fun τ => w_n τ * (2 * R τ)) (Icc δ (T - δ)) := by
          refine (hR_int.norm.const_mul (2 * M_w)).mono'
            ((hwn_sm.continuous.aestronglyMeasurable.restrict).mul (hR_int.1.const_mul 2)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
          rw [norm_mul (w_n τ) (2 * R τ), norm_mul (2 : ℝ) (R τ),
            Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          calc ‖w_n τ‖ * (2 * ‖R τ‖) ≤ M_w * (2 * ‖R τ‖) :=
                mul_le_mul_of_nonneg_right (hM_w τ hτ) (by positivity)
            _ = 2 * M_w * ‖R τ‖ := by ring
        exact (h1.add h2).congr_fun (fun τ _ => by dsimp; ring) measurableSet_Icc
      refine setIntegral_mono_on hint_lhs hint_rhs measurableSet_Icc fun τ hτ => ?_
      have hwn_nn : 0 ≤ w_n τ :=
        mul_nonneg (hAn_01 n τ (hδ.le.trans hτ.1)).1.le (hχ_01 τ).1
      have hτ_Ioo : τ ∈ Ioo 0 T := ⟨lt_of_lt_of_le hδ hτ.1, lt_of_le_of_lt hτ.2 (by linarith)⟩
      have hτ_Icc0T : τ ∈ Icc 0 T := ⟨hτ_Ioo.1.le, hτ_Ioo.2.le⟩
      have hL0_eq : L_0 τ = L_sh τ := indicator_of_mem hτ_Icc0T L_sh
      have hadv := hR_adv τ hτ_Ioo
      have hN0 : 0 ≤ 2 * ν * N τ := mul_nonneg (mul_nonneg (by norm_num) hD.pos_ν.le) (hN_nn τ)
      dsimp only [w_n]
      rw [hL0_eq]
      exact mul_le_mul_of_nonneg_left (by linarith) hwn_nn
    -- Pass `n → ∞` on `Icc δ (T - δ)` via dominated convergence
    obtain ⟨M_E, hM_E⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (s := Icc δ (T - δ)) hE_cont.continuousOn
    have hME_nn : 0 ≤ M_E := (norm_nonneg _).trans (hM_E δ ⟨le_rfl, by linarith⟩)
    have hdχ_cont : Continuous (deriv χ) := ((contDiff_infty_iff_deriv.mp hχ_sm).2).continuous
    obtain ⟨M_dχ, hM_dχ⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (s := Icc δ (T - δ)) hdχ_cont.continuousOn
    have hMdχ_nn : 0 ≤ M_dχ := (norm_nonneg _).trans (hM_dχ δ ⟨le_rfl, by linarith⟩)
    have hlim_lhs : Tendsto
        (fun n => ∫ τ in Icc δ (T - δ), A_n n τ * χ τ * (-2 * L_0 τ * E τ))
        atTop (𝓝 (∫ τ in Icc δ (T - δ), A_0 τ * χ τ * (-2 * L_0 τ * E τ))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => 2 * M_L * M_E)
        (fun n => (((Real.continuous_exp.comp (continuous_const.mul
          (intervalIntegral.continuous_primitive
            (fun a b => (hLn_sm n).continuous.intervalIntegrable a b) 0))).measurable.mul
          hχ_sm.continuous.measurable).mul
          ((measurable_const.mul hL0_meas).mul hE_cont.measurable)).aestronglyMeasurable.restrict)
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        (fun n => ?_) ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        have hτ0 : 0 ≤ τ := hδ.le.trans hτ.1
        have hA_le := (hAn_01 n τ hτ0).2
        have hA_nn := (hAn_01 n τ hτ0).1.le
        have hχ_le := (hχ_01 τ).2
        have hχ_nn := (hχ_01 τ).1
        have hE_le : E τ ≤ M_E := by
          have := hM_E τ hτ; rwa [Real.norm_of_nonneg (hE_nn τ)] at this
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg hA_nn, abs_of_nonneg hχ_nn, abs_of_nonneg (hE_nn τ),
          abs_mul, (show |(-2 : ℝ)| = 2 by norm_num), abs_of_nonneg (hL0_nn τ)]
        calc A_n n τ * χ τ * (2 * L_0 τ * E τ)
            ≤ 1 * 1 * (2 * M_L * M_E) :=
              mul_le_mul (mul_le_mul hA_le hχ_le hχ_nn zero_le_one)
                (mul_le_mul (mul_le_mul_of_nonneg_left (hL0_bd τ) (by norm_num)) hE_le
                  (hE_nn τ) (by positivity))
                (mul_nonneg (mul_nonneg (by norm_num) (hL0_nn τ)) (hE_nn τ)) (by norm_num)
          _ = 2 * M_L * M_E := by ring
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        exact ((hAn_tendsto τ (hδ.le.trans hτ.1)).mul_const (χ τ)).mul_const (-2 * L_0 τ * E τ)
    have hlim_rhs : Tendsto
        (fun n => ∫ τ in Icc δ (T - δ), (-2 * L_n n τ * A_n n τ * χ τ + A_n n τ * deriv χ τ) * E τ)
        atTop (𝓝 (∫ τ in Icc δ (T - δ), (-2 * L_0 τ * A_0 τ * χ τ + A_0 τ * deriv χ τ) * E τ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (2 * M_L + M_dχ) * M_E)
        (fun n => ((((measurable_const.mul (hLn_sm n).continuous.measurable).mul
          (Real.continuous_exp.comp (continuous_const.mul
            (intervalIntegral.continuous_primitive
              (fun a b => (hLn_sm n).continuous.intervalIntegrable a b) 0))).measurable).mul
          hχ_sm.continuous.measurable).add
          ((Real.continuous_exp.comp (continuous_const.mul
            (intervalIntegral.continuous_primitive
              (fun a b => (hLn_sm n).continuous.intervalIntegrable a b) 0))).measurable.mul
            hdχ_cont.measurable) |>.mul hE_cont.measurable).aestronglyMeasurable.restrict)
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        (fun n => ?_) ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        have hτ0 : 0 ≤ τ := hδ.le.trans hτ.1
        have hA_le := (hAn_01 n τ hτ0).2
        have hA_nn := (hAn_01 n τ hτ0).1.le
        have hχ_le := (hχ_01 τ).2
        have hχ_nn := (hχ_01 τ).1
        have hE_le : E τ ≤ M_E := by
          have := hM_E τ hτ; rwa [Real.norm_of_nonneg (hE_nn τ)] at this
        have hdχ_le : ‖deriv χ τ‖ ≤ M_dχ := hM_dχ τ hτ
        rw [norm_mul, Real.norm_of_nonneg (hE_nn τ)]
        have hsum_le : ‖-2 * L_n n τ * A_n n τ * χ τ + A_n n τ * deriv χ τ‖ ≤ 2 * M_L + M_dχ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, (show |(-2 : ℝ)| = 2 by norm_num),
              Real.norm_of_nonneg (hLn_nn n τ), Real.norm_of_nonneg hA_nn, Real.norm_of_nonneg hχ_nn]
            calc 2 * L_n n τ * A_n n τ * χ τ
                ≤ 2 * M_L * 1 * 1 :=
                  mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hLn_bd n τ) (by norm_num))
                    hA_le hA_nn (by positivity)) hχ_le hχ_nn (by positivity)
              _ = 2 * M_L := by ring
          · rw [norm_mul, Real.norm_of_nonneg hA_nn]
            calc A_n n τ * ‖deriv χ τ‖ ≤ 1 * M_dχ :=
                  mul_le_mul hA_le hdχ_le (norm_nonneg _) zero_le_one
              _ = M_dχ := one_mul _
        exact mul_le_mul hsum_le hE_le (hE_nn τ) (by positivity)
      · filter_upwards [ae_restrict_of_ae hLn_ae, ae_restrict_mem measurableSet_Icc] with τ hL_lim hτ
        have hA_lim := hAn_tendsto τ (hδ.le.trans hτ.1)
        exact (((((hL_lim.const_mul (-2)).mul hA_lim).mul_const (χ τ)).add
          (hA_lim.mul_const (deriv χ τ))).mul_const (E τ))
    have hlim_ineq := le_of_tendsto_of_tendsto hlim_lhs hlim_rhs (Eventually.of_forall h_ineq_n)
    -- Cancel `-2 * L_0 τ * A_0 τ * χ τ * E τ`
    have hint_cancel : IntegrableOn (fun τ => A_0 τ * χ τ * (-2 * L_0 τ * E τ)) (Icc δ (T - δ)) := by
      refine (integrableOn_const (C := 2 * M_L * M_E)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
        (((hA0_cont.measurable.mul hχ_sm.continuous.measurable).mul
          ((measurable_const.mul hL0_meas).mul hE_cont.measurable)).aestronglyMeasurable.restrict) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      have hτ0 : 0 ≤ τ := hδ.le.trans hτ.1
      have hE_le : E τ ≤ M_E := by have := hM_E τ hτ; rwa [Real.norm_of_nonneg (hE_nn τ)] at this
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (hA0_01 τ hτ0).1.le, abs_of_nonneg (hχ_01 τ).1, abs_of_nonneg (hE_nn τ),
        abs_mul, (show |(-2 : ℝ)| = 2 by norm_num), abs_of_nonneg (hL0_nn τ)]
      calc A_0 τ * χ τ * (2 * L_0 τ * E τ)
          ≤ 1 * 1 * (2 * M_L * M_E) :=
            mul_le_mul (mul_le_mul (hA0_01 τ hτ0).2 (hχ_01 τ).2 (hχ_01 τ).1 zero_le_one)
              (mul_le_mul (mul_le_mul_of_nonneg_left (hL0_bd τ) (by norm_num)) hE_le
                (hE_nn τ) (by positivity))
              (mul_nonneg (mul_nonneg (by norm_num) (hL0_nn τ)) (hE_nn τ)) (by norm_num)
        _ = 2 * M_L * M_E := by ring
    have hint_main : IntegrableOn (fun τ => A_0 τ * deriv χ τ * E τ) (Icc δ (T - δ)) :=
      ((hA0_cont.mul hdχ_cont).mul hE_cont).continuousOn.integrableOn_Icc
    have hrhs_split : ∫ τ in Icc δ (T - δ), (-2 * L_0 τ * A_0 τ * χ τ + A_0 τ * deriv χ τ) * E τ =
        (∫ τ in Icc δ (T - δ), A_0 τ * χ τ * (-2 * L_0 τ * E τ)) +
          ∫ τ in Icc δ (T - δ), A_0 τ * deriv χ τ * E τ := by
      have heq : (fun τ => (-2 * L_0 τ * A_0 τ * χ τ + A_0 τ * deriv χ τ) * E τ) =
          fun τ => A_0 τ * χ τ * (-2 * L_0 τ * E τ) + A_0 τ * deriv χ τ * E τ := by
        funext τ; ring
      rw [heq, integral_add hint_cancel hint_main]
    rw [hrhs_split] at hlim_ineq
    have hnonneg_main : 0 ≤ ∫ τ in Icc δ (T - δ), A_0 τ * deriv χ τ * E τ := by linarith
    -- Split `∫_{Icc δ (T - δ)}` into `δ..2δ`, `2δ..(T-2δ)`, `(T-2δ)..(T-δ)`
    have hf_cont : Continuous (fun τ => A_0 τ * deriv χ τ * E τ) :=
      (hA0_cont.mul hdχ_cont).mul hE_cont
    have hsplit_3 : ∫ τ in Icc δ (T - δ), A_0 τ * deriv χ τ * E τ =
        (∫ τ in δ..(2 * δ), A_0 τ * deriv χ τ * E τ) +
          (∫ τ in (2 * δ)..(T - 2 * δ), A_0 τ * deriv χ τ * E τ) +
          (∫ τ in (T - 2 * δ)..(T - δ), A_0 τ * deriv χ τ * E τ) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable δ (T - 2 * δ)) (hf_cont.intervalIntegrable (T - 2 * δ) (T - δ)),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable δ (2 * δ)) (hf_cont.intervalIntegrable (2 * δ) (T - 2 * δ))]
    -- Middle piece is 0
    have hmid_zero : ∫ τ in (2 * δ)..(T - 2 * δ), A_0 τ * deriv χ τ * E τ = 0 := by
      rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
      rw [hd_mid τ hτ, mul_zero, zero_mul]
    -- Left piece `≤ E 0 + ε`
    have hleft_le : ∫ τ in δ..(2 * δ), A_0 τ * deriv χ τ * E τ ≤ E 0 + ε := by
      have hmono : ∫ τ in δ..(2 * δ), A_0 τ * deriv χ τ * E τ ≤
          ∫ τ in δ..(2 * δ), deriv χ τ * (E 0 + ε) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          (hf_cont.intervalIntegrable _ _)
          ((hdχ_cont.mul continuous_const).intervalIntegrable _ _) fun τ hτ => ?_
        have hd_nn := hd_left τ hτ
        have hA_le := (hA0_01 τ (hδ.le.trans hτ.1)).2
        have hdist : dist τ 0 < δ₁ := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδ.le.trans hτ.1)]
          linarith [hτ.2]
        have hE_le : E τ ≤ E 0 + ε := by
          have h := hE0_close hdist
          rw [Real.dist_eq] at h
          linarith [(abs_lt.1 h).2]
        calc A_0 τ * deriv χ τ * E τ
            ≤ 1 * deriv χ τ * E τ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA_le hd_nn) (hE_nn τ)
          _ = deriv χ τ * E τ := by ring
          _ ≤ deriv χ τ * (E 0 + ε) := mul_le_mul_of_nonneg_left hE_le hd_nn
      have hftc : ∫ τ in δ..(2 * δ), deriv χ τ = 1 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun τ _ => (hχ_sm.differentiable (by simp) τ).hasDerivAt)
          (hdχ_cont.intervalIntegrable _ _), hχ_2δ, hχ_δ, sub_zero]
      calc ∫ τ in δ..(2 * δ), A_0 τ * deriv χ τ * E τ
          ≤ ∫ τ in δ..(2 * δ), deriv χ τ * (E 0 + ε) := hmono
        _ = (∫ τ in δ..(2 * δ), deriv χ τ) * (E 0 + ε) := intervalIntegral.integral_mul_const _ _
        _ = E 0 + ε := by rw [hftc, one_mul]
    -- Right piece `≤ -exp(-2 * I_L) * (E T - ε)`
    have hright_le : ∫ τ in (T - 2 * δ)..(T - δ), A_0 τ * deriv χ τ * E τ ≤
        -(Real.exp (-2 * I_L) * (E T - ε)) := by
      have hmono : ∫ τ in (T - 2 * δ)..(T - δ), A_0 τ * deriv χ τ * E τ ≤
          ∫ τ in (T - 2 * δ)..(T - δ), -(Real.exp (-2 * I_L) * ((-deriv χ τ) * (E T - ε))) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          (hf_cont.intervalIntegrable _ _)
          ((continuous_const.mul (hdχ_cont.neg.mul continuous_const)).neg.intervalIntegrable _ _)
          fun τ hτ => ?_
        have hd_np := hd_right τ hτ
        have hnd_nn : 0 ≤ -deriv χ τ := neg_nonneg.2 hd_np
        have hA_ge := hA0_ge_AT τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have hdist : dist τ T < δ₂ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith [hτ.2])]
          linarith [hτ.1]
        have hE_ge : E T - ε ≤ E τ := by
          have h := hET_close hdist
          rw [Real.dist_eq] at h
          linarith [(abs_lt.1 h).1]
        have h1 : Real.exp (-2 * I_L) * ((-deriv χ τ) * (E T - ε)) ≤
            Real.exp (-2 * I_L) * ((-deriv χ τ) * E τ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE_ge hnd_nn) (Real.exp_pos _).le
        have h2 : Real.exp (-2 * I_L) * ((-deriv χ τ) * E τ) ≤ A_0 τ * ((-deriv χ τ) * E τ) :=
          mul_le_mul_of_nonneg_right hA_ge (mul_nonneg hnd_nn (hE_nn τ))
        linarith
      have hftc : ∫ τ in (T - 2 * δ)..(T - δ), (-deriv χ τ) = 1 := by
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun τ _ => (hχ_sm.differentiable (by simp) τ).hasDerivAt)
            (hdχ_cont.intervalIntegrable _ _), hχ_Tδ, hχ_T2δ]
        ring
      calc ∫ τ in (T - 2 * δ)..(T - δ), A_0 τ * deriv χ τ * E τ
          ≤ ∫ τ in (T - 2 * δ)..(T - δ), -(Real.exp (-2 * I_L) * ((-deriv χ τ) * (E T - ε))) := hmono
        _ = -(Real.exp (-2 * I_L) * ((∫ τ in (T - 2 * δ)..(T - δ), (-deriv χ τ)) * (E T - ε))) := by
            rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_mul_const]
        _ = -(Real.exp (-2 * I_L) * (E T - ε)) := by rw [hftc, one_mul]
    rw [hsplit_3, hmid_zero, add_zero] at hnonneg_main
    linarith
  -- Deduce `exp(-2 * I_L) * E T ≤ E 0` by letting `ε` be small
  have h_lim : Real.exp (-2 * I_L) * E T ≤ E 0 := by
    by_contra hlt
    have hlt' : E 0 < Real.exp (-2 * I_L) * E T := not_le.mp hlt
    set gap : ℝ := Real.exp (-2 * I_L) * E T - E 0
    have hgap : 0 < gap := sub_pos.2 hlt'
    set ε : ℝ := gap / (2 * (1 + Real.exp (-2 * I_L)))
    have hden_pos : 0 < 2 * (1 + Real.exp (-2 * I_L)) := by positivity
    have hε : 0 < ε := div_pos hgap hden_pos
    have hineq := h_eps ε hε
    have hcalc : (1 + Real.exp (-2 * I_L)) * ε = gap / 2 := by
      dsimp [ε]; field_simp [hden_pos.ne']
    have : gap ≤ (1 + Real.exp (-2 * I_L)) * ε := by dsimp [gap]; linarith
    linarith
  calc E T = Real.exp (2 * I_L) * (Real.exp (-2 * I_L) * E T) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (2 * I_L) * E 0 := mul_le_mul_of_nonneg_left h_lim (Real.exp_pos _).le

/-! ### Coordinate projections and `L²(cell c)` norm helpers for Section 2→3 assembly -/

private def projVelLp8 (c : ℝ) (i : Fin 2) :
    Lp B0581.Vel 2 (B0581.cellVol c) →L[ℂ] Lp ℂ 2 (B0581.cellVol c) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i : B0581.Vel →L[ℂ] ℂ).compLpL 2 (B0581.cellVol c)

private lemma coeFn_projVelLp8 (c : ℝ) (i : Fin 2) (U : Lp B0581.Vel 2 (B0581.cellVol c)) :
    (projVelLp8 c i U : ℝ × ℝ → ℂ) =ᵐ[B0581.cellVol c] fun x => U x i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i : B0581.Vel →L[ℂ] ℂ).coeFn_compLpL
    (p := 2) (μ := B0581.cellVol c) U

private lemma vnorm2_sq_integral_and_velNorm {c : ℝ} {v : ℝ × ℝ → Fin 2 → ℂ}
    (hv : ∀ i, Measurable fun x => v x i)
    {U : Lp B0581.Vel 2 (B0581.cellVol c)}
    (hae : ∀ i : Fin 2, (fun x => v x i) =ᵐ[B0581.cellVol c] fun x => U x i) :
    (∀ i, MemLp (fun x => v x i) 2 (volume.restrict (B0579.cell c))) ∧
      (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (v x) ^ 2)) =
        ENNReal.ofReal (∑ i : Fin 2, ‖projVelLp8 c i U‖ ^ 2) ∧
      (∫ x in B0579.cell c, vnorm2 (v x) ^ 2) = ∑ i : Fin 2, ‖projVelLp8 c i U‖ ^ 2 ∧
      velNorm c v = ENNReal.ofReal (Real.sqrt (∫ x in B0579.cell c, vnorm2 (v x) ^ 2)) := by
  have hm_v : ∀ i : Fin 2, MemLp (fun x => v x i) 2 (volume.restrict (B0579.cell c)) := by
    intro i
    have hproj_ae := (coeFn_projVelLp8 c i U).trans (hae i).symm
    exact (Lp.memLp (projVelLp8 c i U)).ae_eq hproj_ae
  have heLp_eq : ∀ i : Fin 2,
      eLpNorm (fun x => v x i) 2 (volume.restrict (B0579.cell c)) =
        ENNReal.ofReal ‖projVelLp8 c i U‖ := by
    intro i
    have hproj_ae := (hae i).trans (coeFn_projVelLp8 c i U).symm
    have h1 : eLpNorm (fun x => v x i) 2 (B0581.cellVol c) =
        eLpNorm (projVelLp8 c i U) 2 (B0581.cellVol c) := eLpNorm_congr_ae hproj_ae
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact h1
  have hlint : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (v x) ^ 2) =
      ENNReal.ofReal (∑ i : Fin 2, ‖projVelLp8 c i U‖ ^ 2) := by
    rw [BiotSavartH1Aux.lintegral_vnorm2_sq_eq_velNorm_sq c v hv]
    unfold velNorm
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    simp_rw [heLp_eq, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  have hmeas_sq : Measurable fun x => vnorm2 (v x) ^ 2 := by
    unfold vnorm2
    exact (Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum Finset.univ fun i _ => (hv i).norm.pow_const 2)).pow_const 2
  have hint_eq : ∫ x in B0579.cell c, vnorm2 (v x) ^ 2 = ∑ i : Fin 2, ‖projVelLp8 c i U‖ ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      hmeas_sq.aestronglyMeasurable, hlint,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hvel : velNorm c v = ENNReal.ofReal (Real.sqrt (∫ x in B0579.cell c, vnorm2 (v x) ^ 2)) := by
    have hsq := BiotSavartH1Aux.lintegral_vnorm2_sq_eq_velNorm_sq c v hv
    rw [hlint] at hsq
    have h1 : ((velNorm c v) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = velNorm c v := by
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    rw [← h1, ← hsq, ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow, hint_eq]
  exact ⟨hm_v, hlint, hint_eq, hvel⟩

/-! ### Physical-cell evolution bound along `[s_r, s_θ]` -/

private lemma linearised_velNorm_evolution_bound {ν m C_strain b s_r s_θ : ℝ}
    (hm : 8 < m) (hC_strain : 0 ≤ C_strain) (hb : 1 ≤ b)
    (hν : 0 < ν) (hc1 : 1 ≤ ν ^ (-2 : ℝ))
    (hs_r_gt : coreEnd ν b - 1 < s_r) (hs_r0 : 0 < s_r) (hs_rθ : s_r ≤ s_θ)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hStrain_bd : ∫⁻ s in Ioi (coreEnd ν b - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤
      ENNReal.ofReal (2 * C_strain * b))
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf₀_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) f₀)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr s_r f₀ w u) :
    velNorm (ν ^ (-2 : ℝ)) (u s_θ) ≤
      ENNReal.ofReal (Real.exp (2 * C_strain * b)) * velNorm (ν ^ (-2 : ℝ)) (u s_r) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have : Fact (0 < c) := ⟨hc⟩
  have hb0 : 0 < b := by linarith
  rcases eq_or_lt_of_le hs_rθ with rfl | hlt
  · have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (2 * C_strain * b)) :=
      ENNReal.one_le_ofReal.2 (Real.one_le_exp (by positivity))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 (bot_le : (0 : ℝ≥0∞) ≤ _)
  -- Non-degenerate interval `0 < T := s_θ - s_r`, `H' := T + 1`
  set T : ℝ := s_θ - s_r
  have hT : 0 < T := sub_pos.2 hlt
  set H' : ℝ := T + 1
  have hH' : 0 < H' := by dsimp [H']; linarith
  have hw_zc : ∀ s, s_r ≤ s → HasZeroCirculation c (w s) :=
    ladFlowZeroCirc m (by linarith : 1 < m) ν c tr s_r f₀ w u hc1 hf₀_zc hw
  have hclamp_ge : ∀ τ : ℝ, s_r ≤ s_r + clampTau H' τ :=
    fun τ => le_add_of_nonneg_right (clampTau_mem_Icc hH'.le τ).1
  have hw_mem8 : ∀ τ : ℝ, MemLp (w (s_r + clampTau H' τ)) 2 (B0579.cellMeasure c 8) :=
    fun τ => (hw.memX _ (hclamp_ge τ)).mono_measure (cellMeasure_le_of_le c hm.le)
  set W_ext : ℝ → ZC8 c := fun τ => toZC8 (hw_mem8 τ) (hw_zc _ (hclamp_ge τ))
  -- Global continuity of `W_ext : ℝ → ZC8 c`
  have hW_cont : Continuous W_ext := by
    rw [continuous_iff_continuousAt]
    intro τ
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have hmap_tendsto : Tendsto (fun τ' : ℝ => s_r + clampTau H' τ')
        (𝓝 τ) (𝓝[Ici s_r] (s_r + clampTau H' τ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_const.add (continuous_clampTau H')).tendsto τ)
        (Eventually.of_forall hclamp_ge)
    have hlim_m : Tendsto
        (fun τ' : ℝ => xNorm c m (w (s_r + clampTau H' τ') - w (s_r + clampTau H' τ)))
        (𝓝 τ) (𝓝 0) :=
      (hw.strongCont _ (hclamp_ge τ)).comp hmap_tendsto
    have hlim_8 : Tendsto
        (fun τ' : ℝ => xNorm c 8 (w (s_r + clampTau H' τ') - w (s_r + clampTau H' τ)))
        (𝓝 τ) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_m
        (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun τ' => ?_)
      exact eLpNorm_mono_measure _ (cellMeasure_le_of_le c hm.le)
    have hlim_real : Tendsto
        (fun τ' : ℝ => (xNorm c 8 (w (s_r + clampTau H' τ') - w (s_r + clampTau H' τ))).toReal)
        (𝓝 τ) (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim_8
      rwa [ENNReal.toReal_zero] at h1
    filter_upwards [hlim_real.eventually (gt_mem_nhds hε)] with τ' hτ'
    rwa [dist_eq_norm, norm_sub_toZC8]
  -- Jointly strongly measurable representatives of `velRCLM`, `gqRCLM`, `geRCLM` along `W_ext`
  obtain ⟨b_rep, hb_sm, hb_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (s := (univ : Set ℝ)) MeasurableSet.univ
      ((velRCLM c).continuous.comp hW_cont).continuousOn
  obtain ⟨gq_rep, hgq_sm, hgq_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (s := (univ : Set ℝ)) MeasurableSet.univ
      ((gqRCLM c).continuous.comp hW_cont).continuousOn
  obtain ⟨ge_rep, hge_sm, hge_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (s := (univ : Set ℝ)) MeasurableSet.univ
      ((geRCLM c).continuous.comp hW_cont).continuousOn
  set b_sh : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b_rep p i
  set G_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun p i j => if j = 0 then gq_rep p i else ge_rep p i
  set F_sh : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j =>
    -((trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ) * b_sh p j +
      b_sh p i * (trainVel tr (s_r + clampTau H' p.1) p.2 j : ℂ))
  have hb_meas : ∀ i, Measurable fun p => b_sh p i := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hb_sm).measurable
  have hG_meas : ∀ i j, Measurable fun p => G_sh p i j := by
    intro i j; fin_cases j
    · exact ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hgq_sm).measurable
    · exact ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hge_sm).measurable
  have hvel_clamped_meas : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) =>
      (trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ) := by
    intro i
    have hpos : ∀ p : ℝ × (ℝ × ℝ), 0 ≤ s_r + clampTau H' p.1 :=
      fun p => le_trans hs_r0.le (hclamp_ge p.1)
    have heq : (fun p : ℝ × (ℝ × ℝ) => (trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ)) =
        fun p => (tr.v (s_r + clampTau H' p.1) p.2 i : ℂ) := by
      funext p; simp only [trainVel, hpos p, ↓reduceIte]
    rw [heq]
    have hv_cont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => tr.v q.1 q.2 i) (Ici 0 ×ˢ univ) := by
      have hsm := tr.isTrain.smooth_v
      exact ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp_continuousOn
        hsm.continuousOn)
    have hmap_cont : Continuous fun p : ℝ × (ℝ × ℝ) => (s_r + clampTau H' p.1, p.2) :=
      (continuous_const.add ((continuous_clampTau H').comp continuous_fst)).prodMk continuous_snd
    have hcomp_cont : Continuous fun p : ℝ × (ℝ × ℝ) => tr.v (s_r + clampTau H' p.1) p.2 i :=
      hv_cont.comp_continuous hmap_cont fun p => ⟨hpos p, trivial⟩
    exact (Complex.continuous_ofReal.comp hcomp_cont).measurable
  have hF_meas : ∀ i j, Measurable fun p => F_sh p i j := fun i j =>
    (((hvel_clamped_meas i).mul (hb_meas j)).add ((hb_meas i).mul (hvel_clamped_meas j))).neg
  -- Slice a.e. identifications, norms, Biot-Savart, and weak gradients at EVERY `τ : ℝ`
  have hb_ae_coord : ∀ τ i, (fun x => b_sh (τ, x) i) =ᵐ[B0581.cellVol c]
      fun x => velRCLM c (W_ext τ) x i := by
    intro τ i
    filter_upwards [hb_ae τ trivial] with x hx
    exact congrArg (fun z : B0581.Vel => z i) hx
  have hgq_ae_coord : ∀ τ i, (fun x => G_sh (τ, x) i 0) =ᵐ[B0581.cellVol c]
      fun x => gqRCLM c (W_ext τ) x i := by
    intro τ i
    filter_upwards [hgq_ae τ trivial] with x hx
    exact congrArg (fun z : B0581.Vel => z i) hx
  have hge_ae_coord : ∀ τ i, (fun x => G_sh (τ, x) i 1) =ᵐ[B0581.cellVol c]
      fun x => geRCLM c (W_ext τ) x i := by
    intro τ i
    filter_upwards [hge_ae τ trivial] with x hx
    exact congrArg (fun z : B0581.Vel => z i) hx
  have hb_slice_meas : ∀ τ i, Measurable fun x => b_sh (τ, x) i :=
    fun τ i => (hb_meas i).comp (measurable_const.prodMk measurable_id)
  have hG_slice_meas : ∀ τ i j, Measurable fun x => G_sh (τ, x) i j :=
    fun τ i j => (hG_meas i j).comp (measurable_const.prodMk measurable_id)
  have hb_energy_eq : ∀ τ,
      (∀ i, MemLp (fun x => b_sh (τ, x) i) 2 (volume.restrict (B0579.cell c))) ∧
      (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2)) =
        ENNReal.ofReal (∑ i : Fin 2, ‖projVelLp8 c i (velRCLM c (W_ext τ))‖ ^ 2) ∧
      energyE c b_sh τ = ∑ i : Fin 2, ‖projVelLp8 c i (velRCLM c (W_ext τ))‖ ^ 2 ∧
      velNorm c (fun x => b_sh (τ, x)) = ENNReal.ofReal (Real.sqrt (energyE c b_sh τ)) :=
    fun τ => vnorm2_sq_integral_and_velNorm (hb_slice_meas τ) (hb_ae_coord τ)
  have hG_energy_eq : ∀ τ,
      (∀ i j, MemLp (fun x => G_sh (τ, x) i j) 2 (volume.restrict (B0579.cell c))) ∧
      (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G_sh (τ, x)) ^ 2)) =
        ENNReal.ofReal ((∑ i : Fin 2, ‖projVelLp8 c i (gqRCLM c (W_ext τ))‖ ^ 2) +
          ∑ i : Fin 2, ‖projVelLp8 c i (geRCLM c (W_ext τ))‖ ^ 2) ∧
      energyN c G_sh τ =
        (∑ i : Fin 2, ‖projVelLp8 c i (gqRCLM c (W_ext τ))‖ ^ 2) +
          ∑ i : Fin 2, ‖projVelLp8 c i (geRCLM c (W_ext τ))‖ ^ 2 := by
    intro τ
    obtain ⟨hm0, hl0, hi0, _⟩ :=
      vnorm2_sq_integral_and_velNorm (fun i => hG_slice_meas τ i 0) (hgq_ae_coord τ)
    obtain ⟨hm1, hl1, hi1, _⟩ :=
      vnorm2_sq_integral_and_velNorm (fun i => hG_slice_meas τ i 1) (hge_ae_coord τ)
    have hpt_t : ∀ x, tnorm2 (G_sh (τ, x)) ^ 2 =
        vnorm2 (fun i => G_sh (τ, x) i 0) ^ 2 + vnorm2 (fun i => G_sh (τ, x) i 1) ^ 2 := by
      intro x
      unfold tnorm2 vnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
        Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      ring
    have hm0_meas : Measurable fun x => vnorm2 (fun i => G_sh (τ, x) i 0) ^ 2 := by
      unfold vnorm2
      exact (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ fun i _ => (hG_slice_meas τ i 0).norm.pow_const 2)).pow_const 2
    have hm1_meas : Measurable fun x => vnorm2 (fun i => G_sh (τ, x) i 1) ^ 2 := by
      unfold vnorm2
      exact (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ fun i _ => (hG_slice_meas τ i 1).norm.pow_const 2)).pow_const 2
    have hlint : ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G_sh (τ, x)) ^ 2) =
        ENNReal.ofReal ((∑ i : Fin 2, ‖projVelLp8 c i (gqRCLM c (W_ext τ))‖ ^ 2) +
          ∑ i : Fin 2, ‖projVelLp8 c i (geRCLM c (W_ext τ))‖ ^ 2) := by
      have hpt_ofReal : ∀ x, ENNReal.ofReal (tnorm2 (G_sh (τ, x)) ^ 2) =
          ENNReal.ofReal (vnorm2 (fun i => G_sh (τ, x) i 0) ^ 2) +
            ENNReal.ofReal (vnorm2 (fun i => G_sh (τ, x) i 1) ^ 2) := by
        intro x; rw [hpt_t x, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      simp_rw [hpt_ofReal]
      rw [lintegral_add_left hm0_meas.ennreal_ofReal, hl0, hl1,
        ← ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hint : energyN c G_sh τ =
        (∑ i : Fin 2, ‖projVelLp8 c i (gqRCLM c (W_ext τ))‖ ^ 2) +
          ∑ i : Fin 2, ‖projVelLp8 c i (geRCLM c (W_ext τ))‖ ^ 2 := by
      unfold energyN
      have hmeas_t : Measurable fun x => tnorm2 (G_sh (τ, x)) ^ 2 := by
        rw [funext hpt_t]
        exact hm0_meas.add hm1_meas
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
        hmeas_t.aestronglyMeasurable, hlint,
        ENNReal.toReal_ofReal (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
    exact ⟨fun i j => by fin_cases j; exact hm0 i; exact hm1 i, hlint, hint⟩
  have hE_cont : Continuous (energyE c b_sh) := by
    have heq : energyE c b_sh = fun τ => ∑ i : Fin 2, ‖projVelLp8 c i (velRCLM c (W_ext τ))‖ ^ 2 :=
      funext fun τ => (hb_energy_eq τ).2.2.1
    rw [heq]
    exact continuous_finsetSum _ fun i _ =>
      (((projVelLp8 c i).continuous.comp ((velRCLM c).continuous.comp hW_cont)).norm).pow 2
  have hN_cont : Continuous (energyN c G_sh) := by
    have heq : energyN c G_sh = fun τ =>
        (∑ i : Fin 2, ‖projVelLp8 c i (gqRCLM c (W_ext τ))‖ ^ 2) +
          ∑ i : Fin 2, ‖projVelLp8 c i (geRCLM c (W_ext τ))‖ ^ 2 :=
      funext fun τ => (hG_energy_eq τ).2.2
    rw [heq]
    exact (continuous_finsetSum _ fun i _ =>
      (((projVelLp8 c i).continuous.comp ((gqRCLM c).continuous.comp hW_cont)).norm).pow 2).add
      (continuous_finsetSum _ fun i _ =>
        (((projVelLp8 c i).continuous.comp ((geRCLM c).continuous.comp hW_cont)).norm).pow 2)
  -- Uniform bounds on `energyE`, `energyN`, and `trainVel` via compactness of `[0, H']`
  obtain ⟨M_E0, hM_E0⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 H') hE_cont.continuousOn
  obtain ⟨M_N0, hM_N0⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 H') hN_cont.continuousOn
  set M_E : ℝ := max M_E0 0
  set M_N : ℝ := max M_N0 0
  have hME_nn : 0 ≤ M_E := le_max_right _ _
  have hMN_nn : 0 ≤ M_N := le_max_right _ _
  have hE_le_global : ∀ τ : ℝ, energyE c b_sh τ ≤ M_E := by
    intro τ
    have hcl_eq : W_ext τ = W_ext (clampTau H' τ) := by
      dsimp [W_ext]; congr 1
      have : clampTau H' (clampTau H' τ) = clampTau H' τ :=
        clampTau_eq_of_mem (clampTau_mem_Icc hH'.le τ)
      simp [this]
    have hEq : energyE c b_sh τ = energyE c b_sh (clampTau H' τ) := by
      rw [(hb_energy_eq τ).2.2.1, (hb_energy_eq (clampTau H' τ)).2.2.1, hcl_eq]
    rw [hEq]
    have h1 := hM_E0 (clampTau H' τ) (clampTau_mem_Icc hH'.le τ)
    have hnn : 0 ≤ energyE c b_sh (clampTau H' τ) := integral_nonneg fun _ => sq_nonneg _
    rw [Real.norm_of_nonneg hnn] at h1
    exact h1.trans (le_max_left _ _)
  have hN_le_global : ∀ τ : ℝ, energyN c G_sh τ ≤ M_N := by
    intro τ
    have hcl_eq : W_ext τ = W_ext (clampTau H' τ) := by
      dsimp [W_ext]; congr 1
      have : clampTau H' (clampTau H' τ) = clampTau H' τ :=
        clampTau_eq_of_mem (clampTau_mem_Icc hH'.le τ)
      simp [this]
    have hEq : energyN c G_sh τ = energyN c G_sh (clampTau H' τ) := by
      rw [(hG_energy_eq τ).2.2, (hG_energy_eq (clampTau H' τ)).2.2, hcl_eq]
    rw [hEq]
    have h1 := hM_N0 (clampTau H' τ) (clampTau_mem_Icc hH'.le τ)
    have hnn : 0 ≤ energyN c G_sh (clampTau H' τ) := integral_nonneg fun _ => sq_nonneg _
    rw [Real.norm_of_nonneg hnn] at h1
    exact h1.trans (le_max_left _ _)
  have hE_lint_bd : ∀ τ, ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2) ≤
      ENNReal.ofReal M_E := by
    intro τ
    rw [(hb_energy_eq τ).2.1, ← (hb_energy_eq τ).2.2.1]
    exact ENNReal.ofReal_le_ofReal (hE_le_global τ)
  obtain ⟨M_v, hMv_nn, hMv_all⟩ := core_trainVel_bound_le tr htr (by linarith : 0 ≤ s_r + H')
  have hMv_clamped : ∀ p : ℝ × (ℝ × ℝ), ∀ i : Fin 2,
      ‖(trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ)‖ ≤ M_v :=
    fun p i => hMv_all _ (by linarith [(clampTau_mem_Icc hH'.le p.1).2]) p.2 i
  -- Biot-Savart and weak gradient on every slice `τ`
  have hbs_all : ∀ τ : ℝ, IsBiotSavart c (w (s_r + clampTau H' τ)) (fun x => b_sh (τ, x)) := by
    intro τ
    have hbs_W := isBiotSavart_velRCLM c (W_ext τ)
    have hW_ae : (W_ext τ : XC8 c) =ᵐ[volume.restrict (B0579.cell c)] w (s_r + clampTau H' τ) :=
      (B0579.ac_cellMeasure c 8).ae_le (MemLp.coeFn_toLp (hw_mem8 τ))
    refine ⟨(hb_energy_eq τ).1, ?_, ?_⟩
    · intro ψ hψ
      have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
          (b_sh (τ, x) 0 * (B0579.pd 0 ψ x : ℂ) + b_sh (τ, x) 1 * (B0579.pd 1 ψ x : ℂ)) =
            (velRCLM c (W_ext τ) x 0 * (B0579.pd 0 ψ x : ℂ) +
              velRCLM c (W_ext τ) x 1 * (B0579.pd 1 ψ x : ℂ)) := by
        filter_upwards [hb_ae_coord τ 0, hb_ae_coord τ 1] with x hx0 hx1
        rw [hx0, hx1]
      rw [integral_congr_ae hcongr]
      exact hbs_W.2.1 ψ hψ
    · intro ψ hψ
      have hcongr_l : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
          w (s_r + clampTau H' τ) x * (ψ x : ℂ) = (W_ext τ : XC8 c) x * (ψ x : ℂ) := by
        filter_upwards [hW_ae] with x hx; rw [hx]
      have hcongr_r : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
          (b_sh (τ, x) 0 * (B0579.pd 1 ψ x : ℂ) - b_sh (τ, x) 1 * (B0579.pd 0 ψ x : ℂ)) =
            (velRCLM c (W_ext τ) x 0 * (B0579.pd 1 ψ x : ℂ) -
              velRCLM c (W_ext τ) x 1 * (B0579.pd 0 ψ x : ℂ)) := by
        filter_upwards [hb_ae_coord τ 0, hb_ae_coord τ 1] with x hx0 hx1
        rw [hx0, hx1]
      rw [integral_congr_ae hcongr_l, integral_congr_ae hcongr_r]
      exact hbs_W.2.2 ψ hψ
  have hbs_Icc : ∀ τ ∈ Icc 0 H', IsBiotSavart c (w (s_r + τ)) (fun x => b_sh (τ, x)) := by
    intro τ hτ
    have h := hbs_all τ
    rwa [clampTau_eq_of_mem hτ] at h
  have hwg_all : ∀ τ i j,
      HasWeakCellDerivC c j (fun x => b_sh (τ, x) i) (fun x => G_sh (τ, x) i j) := by
    intro τ i j
    fin_cases j
    · exact HasWeakCellDerivC.congr_ae (hb_ae_coord τ i) (hgq_ae_coord τ i)
        (hasWeakCellDerivC_velRCLM_q c (W_ext τ) i)
    · exact HasWeakCellDerivC.congr_ae (hb_ae_coord τ i) (hge_ae_coord τ i)
        (hasWeakCellDerivC_velRCLM_eta c (W_ext τ) i)
  -- Assemble `CoreTruncData c ν H' 0 F_sh b_sh G_sh`
  have hF_sq_le : ∀ p : ℝ × (ℝ × ℝ), tnorm2 (F_sh p) ^ 2 ≤ 8 * M_v ^ 2 * vnorm2 (b_sh p) ^ 2 := by
    intro p
    have ht : tnorm2 (F_sh p) ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖F_sh p i j‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hv : vnorm2 (b_sh p) ^ 2 = ∑ i : Fin 2, ‖b_sh p i‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [ht, hv]
    have hij : ∀ i j : Fin 2, ‖F_sh p i j‖ ^ 2 ≤
        2 * M_v ^ 2 * ‖b_sh p j‖ ^ 2 + 2 * M_v ^ 2 * ‖b_sh p i‖ ^ 2 := by
      intro i j
      dsimp only [F_sh]
      rw [norm_neg]
      have hsum := norm_add_le
        ((trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ) * b_sh p j)
        (b_sh p i * (trainVel tr (s_r + clampTau H' p.1) p.2 j : ℂ))
      rw [norm_mul, norm_mul] at hsum
      have h1 : ‖(trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ)‖ * ‖b_sh p j‖ ≤ M_v * ‖b_sh p j‖ :=
        mul_le_mul_of_nonneg_right (hMv_clamped p i) (norm_nonneg _)
      have h2 : ‖b_sh p i‖ * ‖(trainVel tr (s_r + clampTau H' p.1) p.2 j : ℂ)‖ ≤ ‖b_sh p i‖ * M_v :=
        mul_le_mul_of_nonneg_left (hMv_clamped p j) (norm_nonneg _)
      have hle : ‖(trainVel tr (s_r + clampTau H' p.1) p.2 i : ℂ) * b_sh p j +
          b_sh p i * (trainVel tr (s_r + clampTau H' p.1) p.2 j : ℂ)‖ ≤
          M_v * ‖b_sh p j‖ + M_v * ‖b_sh p i‖ := by linarith
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
      nlinarith [sq_nonneg (M_v * ‖b_sh p j‖ - M_v * ‖b_sh p i‖)]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    linarith [hij 0 0, hij 0 1, hij 1 0, hij 1 1]
  have hD : CoreTruncData c ν H' 0 F_sh b_sh G_sh := by
    have hb_norm_sq : Measurable fun p => vnorm2 (b_sh p) ^ 2 := by
      unfold vnorm2
      exact (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ fun i _ => (hb_meas i).norm.pow_const 2)).pow_const 2
    have hG_norm_sq : Measurable fun p => tnorm2 (G_sh p) ^ 2 := by
      unfold tnorm2
      exact (Real.continuous_sqrt.measurable.comp (Finset.measurable_sum Finset.univ fun i _ =>
        Finset.measurable_sum Finset.univ fun j _ => (hG_meas i j).norm.pow_const 2)).pow_const 2
    have hF_eq_Icc : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Icc 0 H' → ∀ i j,
        F_sh p i j = -((trainVel tr (s_r + p.1) p.2 i : ℂ) * b_sh p j +
          b_sh p i * (trainVel tr (s_r + p.1) p.2 j : ℂ)) := by
      intro p hp i j; dsimp [F_sh]; rw [clampTau_eq_of_mem hp]
    have hMv_Icc : ∀ τ ∈ Icc 0 H', ∀ x i, ‖(trainVel tr (s_r + τ) x i : ℂ)‖ ≤ M_v :=
      fun τ hτ x i => hMv_all _ (by linarith [hτ.2]) x i
    refine
      { pos_c := hc
        pos_ν := hν
        pos_H' := hH'
        l2loc := fun s₁ s₂ _ _ => by
          calc ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F_sh p) ^ 2)
              ≤ ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
                  ENNReal.ofReal (8 * M_v ^ 2 * vnorm2 (b_sh p) ^ 2) :=
                lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hF_sq_le p)
            _ = ∫⁻ τ in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
                  ENNReal.ofReal (8 * M_v ^ 2) * ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2) := by
                rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
                  lintegral_prod _ (hb_norm_sq.const_mul _).ennreal_ofReal.aemeasurable]
                refine lintegral_congr fun τ => lintegral_congr fun x => ?_
                exact ENNReal.ofReal_mul (by positivity)
            _ ≤ ∫⁻ _ in Icc s₁ s₂, ENNReal.ofReal (8 * M_v ^ 2) * ENNReal.ofReal M_E := by
                refine lintegral_mono fun τ => ?_
                have hm_b : Measurable fun x => vnorm2 (b_sh (τ, x)) ^ 2 :=
                  hb_norm_sq.comp (measurable_const.prodMk measurable_id)
                rw [lintegral_const_mul _ hm_b.ennreal_ofReal]
                exact mul_le_mul_of_nonneg_left (hE_lint_bd τ) bot_le
            _ < ⊤ := by
                simp only [lintegral_const]
                exact ENNReal.mul_lt_top
                  (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
                  (by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
        meas := hF_meas
        measurable := hb_meas
        gradMeasurable := hG_meas
        energyLoc := fun s₁ s₂ _ _ => by
          have hmeas_sum : Measurable fun p => vnorm2 (b_sh p) ^ 2 + tnorm2 (G_sh p) ^ 2 :=
            hb_norm_sq.add hG_norm_sq
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod _ hmeas_sum.ennreal_ofReal.aemeasurable]
          calc ∫⁻ τ in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
                ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2 + tnorm2 (G_sh (τ, x)) ^ 2)
              ≤ ∫⁻ _ in Icc s₁ s₂, ENNReal.ofReal M_E + ENNReal.ofReal M_N := by
                refine lintegral_mono fun τ => ?_
                have hm_b : Measurable fun x => vnorm2 (b_sh (τ, x)) ^ 2 :=
                  hb_norm_sq.comp (measurable_const.prodMk measurable_id)
                have hm_G : Measurable fun x => tnorm2 (G_sh (τ, x)) ^ 2 :=
                  hG_norm_sq.comp (measurable_const.prodMk measurable_id)
                have hadd : ∀ x, ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2 + tnorm2 (G_sh (τ, x)) ^ 2) =
                    ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2) +
                      ENNReal.ofReal (tnorm2 (G_sh (τ, x)) ^ 2) :=
                  fun x => ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
                simp_rw [hadd]
                rw [lintegral_add_left hm_b.ennreal_ofReal]
                refine add_le_add (hE_lint_bd τ) ?_
                rw [(hG_energy_eq τ).2.1, ← (hG_energy_eq τ).2.2]
                exact ENNReal.ofReal_le_ofReal (hN_le_global τ)
            _ < ⊤ := by
                simp only [lintegral_const]
                exact ENNReal.mul_lt_top
                  (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
                  (by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
        divFree := fun τ _ ψ hψ => (hbs_all τ).2.1 ψ hψ
        weakGrad := fun τ _ i j => hwg_all τ i j
        integrable_core := fun H₀ hH₀ Φ hΦ hΦ_H₀ =>
          (shifted_flatTest_eq_zero hm hν hc1 hs_r0.le hH₀ hH' hME_nn hMv_nn hf₀_zc hw
            hb_meas hF_meas hE_lint_bd hF_eq_Icc hMv_Icc hbs_Icc hwg_all hΦ hΦ_H₀).1
        weak_core := fun H₀ hH₀ Φ hΦ hΦ_H₀ =>
          (shifted_flatTest_eq_zero hm hν hc1 hs_r0.le hH₀ hH' hME_nn hMv_nn hf₀_zc hw
            hb_meas hF_meas hE_lint_bd hF_eq_Icc hMv_Icc hbs_Icc hwg_all hΦ hΦ_H₀).2 }
  -- Every `τ ∈ Ioo 0 T` is a good slice of `(F_sh, G_sh, b_sh)`
  have hgood_all : ∀ τ ∈ Ioo 0 T, LMGoodSlice c F_sh G_sh b_sh τ := by
    intro τ _
    refine ⟨(hb_energy_eq τ).1, fun j i => (hG_energy_eq τ).1 i j, fun j i => ?_⟩
    refine ⟨((hF_meas i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    have hpt : ∀ x, ‖F_sh (τ, x) i j‖ₑ ^ ENNReal.toReal 2 ≤
        ENNReal.ofReal (8 * M_v ^ 2 * vnorm2 (b_sh (τ, x)) ^ 2) := by
      intro x
      have htr2 : ENNReal.toReal 2 = (2 : ℝ) := by simp
      rw [htr2, ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
      apply ENNReal.ofReal_le_ofReal
      have hle := hF_sq_le (τ, x)
      have hterm : ‖F_sh (τ, x) i j‖ ^ 2 ≤ tnorm2 (F_sh (τ, x)) ^ 2 := by
        rw [show tnorm2 (F_sh (τ, x)) ^ 2 = ∑ i' : Fin 2, ∑ j' : Fin 2, ‖F_sh (τ, x) i' j'‖ ^ 2 from
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        exact (Finset.single_le_sum (f := fun j' => ‖F_sh (τ, x) i j'‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 2, ‖F_sh (τ, x) i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))
      exact hterm.trans hle
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    have hm_b : Measurable fun x => vnorm2 (b_sh (τ, x)) ^ 2 := by
      unfold vnorm2
      exact (Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum Finset.univ fun k _ => (hb_slice_meas τ k).norm.pow_const 2)).pow_const 2
    have hmul : ∀ x, ENNReal.ofReal (8 * M_v ^ 2 * vnorm2 (b_sh (τ, x)) ^ 2) =
        ENNReal.ofReal (8 * M_v ^ 2) * ENNReal.ofReal (vnorm2 (b_sh (τ, x)) ^ 2) :=
      fun x => ENNReal.ofReal_mul (by positivity)
    simp_rw [hmul]
    rw [lintegral_const_mul _ hm_b.ennreal_ofReal]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (hE_lint_bd τ) ENNReal.ofReal_lt_top)
  -- Shifted strain rate `L_sh` and Grönwall bound on `[0, T]`
  set L_sh : ℝ → ℝ := fun τ =>
    if 0 < s_r + τ then (UnforcedLeray.B0277.supNormD 1 (tr.v (s_r + τ))).toReal else 0
  have hL_meas : Measurable L_sh := by
    have hm := AdvectionEnergyAux.measurable_supNormD_one_toReal_ite tr
    exact hm.comp (measurable_const.add measurable_id)
  obtain ⟨M_L, hML_nn, hML_bd⟩ := AdvectionEnergyAux.supNormD_one_bound_on tr htr (by linarith : 0 ≤ s_r + T)
  have hL_nn : ∀ τ ∈ Icc 0 T, 0 ≤ L_sh τ := fun τ _ => by
    dsimp [L_sh]; split_ifs <;> positivity
  have hL_bd : ∀ τ ∈ Icc 0 T, L_sh τ ≤ M_L := by
    intro τ hτ
    have hp : 0 < s_r + τ := by linarith [hτ.1]
    simp only [L_sh, hp, ↓reduceIte]
    exact (hML_bd (s_r + τ) ⟨hp.le, by linarith [hτ.2]⟩).2.1
  have hR_adv : ∀ τ ∈ Ioo 0 T, -L_sh τ * energyE c b_sh τ ≤ energyR c F_sh G_sh τ := by
    intro τ hτ
    have hp : 0 < s_r + τ := by linarith [hτ.1]
    have hL_eq : L_sh τ = (UnforcedLeray.B0277.supNormD 1 (tr.v (s_r + τ))).toReal := by
      simp only [L_sh, hp, ↓reduceIte]
    rw [hL_eq]
    refine shifted_slice_advection_le hc hs_r0.le hτ.1 tr htr hD (hgood_all τ hτ) fun x i j => ?_
    dsimp [F_sh]
    have hcl : clampTau H' τ = τ := clampTau_eq_of_mem ⟨hτ.1.le, by dsimp [H']; linarith [hτ.2]⟩
    rw [hcl]
    simp only [trainVel, hp.le, ↓reduceIte]
  have hET_le := gronwall_energy_le hT rfl hML_nn hD hE_cont hN_cont hL_meas hL_nn hL_bd hR_adv
  -- Bound `∫_{Icc 0 T} L_sh ≤ 2 * C_strain * b` via `hStrain_bd`
  have hIL_le : ∫ τ in Icc 0 T, L_sh τ ≤ 2 * C_strain * b := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    have hcongr : EqOn L_sh (fun τ => (UnforcedLeray.B0277.supNormD 1 (tr.v (s_r + τ))).toReal)
        (uIcc 0 T) := by
      intro τ hτ; rw [uIcc_of_le hT.le] at hτ
      have hp : 0 < s_r + τ := by linarith [hτ.1]
      simp only [L_sh, hp, ↓reduceIte]
    rw [intervalIntegral.integral_congr hcongr]
    set g_str : ℝ → ℝ := fun s =>
      if 0 < s then (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal else 0
    have hcongr2 : EqOn (fun τ => (UnforcedLeray.B0277.supNormD 1 (tr.v (s_r + τ))).toReal)
        (fun τ => g_str (s_r + τ)) (uIcc 0 T) := by
      intro τ hτ; rw [uIcc_of_le hT.le] at hτ
      have hp : 0 < s_r + τ := by linarith [hτ.1]
      simp only [g_str, hp, ↓reduceIte]
    rw [intervalIntegral.integral_congr hcongr2]
    have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := T) g_str s_r
    have hend : s_r + T = s_θ := by dsimp [T]; ring
    rw [hshift, add_zero, hend, intervalIntegral.integral_of_le hs_rθ]
    have hg_meas : Measurable g_str := AdvectionEnergyAux.measurable_supNormD_one_toReal_ite tr
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun s => by dsimp [g_str]; split_ifs <;> positivity)
      hg_meas.aestronglyMeasurable.restrict]
    have hlint_le : ∫⁻ s in Ioc s_r s_θ, ENNReal.ofReal (g_str s) ≤
        ENNReal.ofReal (2 * C_strain * b) := by
      have hsub_Ioi : Ioc s_r s_θ ⊆ Ioi (coreEnd ν b - 1) :=
        fun s hs => lt_trans hs_r_gt hs.1
      calc ∫⁻ s in Ioc s_r s_θ, ENNReal.ofReal (g_str s)
          ≤ ∫⁻ s in Ioc s_r s_θ, UnforcedLeray.B0277.supNormD 1 (tr.v s) := by
            refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
            have hp : 0 < s := lt_trans hs_r0 hs.1
            simp only [g_str, hp, ↓reduceIte]
            exact ENNReal.ofReal_toReal_le
        _ ≤ ∫⁻ s in Ioi (coreEnd ν b - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) :=
            lintegral_mono_set hsub_Ioi
        _ ≤ ENNReal.ofReal (2 * C_strain * b) := hStrain_bd
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint_le
  have hET_le2 : energyE c b_sh T ≤ Real.exp (4 * C_strain * b) * energyE c b_sh 0 := by
    calc energyE c b_sh T
        ≤ Real.exp (2 * ∫ τ in Icc 0 T, L_sh τ) * energyE c b_sh 0 := hET_le
      _ ≤ Real.exp (4 * C_strain * b) * energyE c b_sh 0 :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith))
            (integral_nonneg fun _ => sq_nonneg _)
  -- Relate `energyE c b_sh T` and `energyE c b_sh 0` to `velNorm c (u s_θ)` and `velNorm c (u s_r)`
  have hu_θ_eq : velNorm c (u s_θ) = ENNReal.ofReal (Real.sqrt (energyE c b_sh T)) := by
    have hT_Icc : T ∈ Icc 0 H' := ⟨hT.le, by dsimp [H']; linarith⟩
    have hbs_T : IsBiotSavart c (w s_θ) (fun x => b_sh (T, x)) := by
      have h := hbs_Icc T hT_Icc; rwa [show s_r + T = s_θ by dsimp [T]; ring] at h
    have hae := CTE.isBiotSavart_unique c hc (w s_θ) (u s_θ) (fun x => b_sh (T, x))
      (hw.biotSavart s_θ hs_rθ) hbs_T
    rw [velNorm_congr_ae hae, (hb_energy_eq T).2.2.2]
  have hu_r_eq : velNorm c (u s_r) = ENNReal.ofReal (Real.sqrt (energyE c b_sh 0)) := by
    have h0_Icc : (0 : ℝ) ∈ Icc 0 H' := ⟨le_rfl, hH'.le⟩
    have hbs_0 : IsBiotSavart c (w s_r) (fun x => b_sh (0, x)) := by
      have h := hbs_Icc 0 h0_Icc; rwa [add_zero] at h
    have hae := CTE.isBiotSavart_unique c hc (w s_r) (u s_r) (fun x => b_sh (0, x))
      (hw.biotSavart s_r le_rfl) hbs_0
    rw [velNorm_congr_ae hae, (hb_energy_eq 0).2.2.2]
  rw [hu_θ_eq, hu_r_eq, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hexp_sq : Real.sqrt (Real.exp (4 * C_strain * b)) = Real.exp (2 * C_strain * b) := by
    have h : Real.exp (4 * C_strain * b) = (Real.exp (2 * C_strain * b)) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h, Real.sqrt_sq (Real.exp_pos _).le]
  calc Real.sqrt (energyE c b_sh T)
      ≤ Real.sqrt (Real.exp (4 * C_strain * b) * energyE c b_sh 0) := Real.sqrt_le_sqrt hET_le2
    _ = Real.exp (2 * C_strain * b) * Real.sqrt (energyE c b_sh 0) := by
        rw [Real.sqrt_mul (Real.exp_pos _).le, hexp_sq]

end KineticImpulseAux

open KineticImpulseAux in
/-- **`eq:ct-kinetic-impulse`** (SP 3242-3251): for `0 < θ ≤ r ≤ b`,
`‖K_{d(θ)} 𝒰_Z(θ, r) h‖₂ ≤ C_b (r/θ) ‖K_{d(r)} h‖₂`. -/
theorem ctKineticImpulse : UnforcedLeray.Short.IIIa.CTKineticImpulse := by
  intro _P _hP m hm
  refine ⟨1, fun b hb => ?_⟩
  have hb_pos : 0 < b := by linarith
  obtain ⟨C_strain, ν_strain, hC_strain, hν_strain, hStrain⟩ := tail_strain_integral_bound b hb
  set C : ℝ := Real.exp (2 * C_strain * b)
  have hC_pos : 0 < C := Real.exp_pos _
  set ν₀ : ℝ := min ν_strain (min (1 / 2) ((3 * b)⁻¹))
  have hν₀_pos : 0 < ν₀ :=
    lt_min hν_strain (lt_min (by norm_num) (inv_pos.2 (by positivity)))
  refine ⟨C, ν₀, hν₀_pos, fun ν hν tr htr r θ hθ hθr hrb h Zh hh_mem hh_zc _hh_even hEvol => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_str : ν ≤ ν_strain := hν.2.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_3b : ν ≤ (3 * b)⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr_pos : 0 < r := lt_of_lt_of_le hθ hθr
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  have hc1 : 1 ≤ c :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν_pos (by linarith) (by norm_num)
  -- Late strain bound and age ordering `2 < coreEnd ν b = s_b ≤ s_r ≤ s_θ`
  obtain ⟨hH_gt2, hStrain_raw, hStrain_sum⟩ := hStrain ν ⟨hν_pos, hν_str⟩ tr htr
  have hStrain_bd : ∫⁻ s in Ioi (coreEnd ν b - 1), UnforcedLeray.B0277.supNormD 1 (tr.v s) ≤
      ENNReal.ofReal (2 * C_strain * b) :=
    hStrain_raw.trans (ENNReal.ofReal_le_ofReal hStrain_sum)
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
  have hsb_le_sr : coreEnd ν b ≤ s_r := by
    rw [← T22Sub.clockAge_eq_coreEnd hν_pos hb_pos]
    exact hage_anti hr_pos hrb
  have hsr_le_sθ : s_r ≤ s_θ := hage_anti hθ hθr
  have hsr_gt_H1 : coreEnd ν b - 1 < s_r := by linarith
  have hsr_pos : 0 < s_r := by linarith
  -- Unpack `HeatEvolvesTo`
  obtain ⟨w, u, hw, rfl⟩ := hEvol
  -- Zero circulation of initial physical datum `Jscale (ν * r)⁻¹ h`
  have hf₀_eq : Jscale (ν * r)⁻¹ h = JscaleInv (ν * r) h := by
    simpa only [inv_inv] using jscale_eq_jscaleInv_inv (inv_pos.2 (mul_pos hν_pos hr_pos)) h
  have hd_r_eq : c * Real.sqrt (ν * r) = dOfTheta ν r := c_mul_sqrt_eq_dOfTheta hν_pos hr_pos
  have hf₀_zc : HasZeroCirculation c (Jscale (ν * r)⁻¹ h) := by
    rw [hf₀_eq]
    apply hasZeroCirculation_jscaleInv (mul_pos hν_pos hr_pos)
    rwa [hd_r_eq]
  -- Step 1: Upper bound on `kinNorm (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ))`
  have ha_θ_pos : 0 < (ν * θ)⁻¹ := inv_pos.2 (mul_pos hν_pos hθ)
  have hd_θ_eq : dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹) = c := dOfTheta_mul_sqrt_inv hν_pos hθ
  have hw_θ_l2 : MemLp (w s_θ) 2 (volume.restrict (B0579.cell (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹)))) := by
    rw [hd_θ_eq]
    exact memLp_unweighted_of_memX_pos (by linarith : 0 ≤ m) (hw.memX s_θ hsr_le_sθ)
  have hu_θ_bs_d : IsBiotSavart (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ))
      (rescaleVel (ν * θ)⁻¹ (u s_θ)) := by
    have hbs_c : IsBiotSavart (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹)) (w s_θ) (u s_θ) := by
      rw [hd_θ_eq]; exact hw.biotSavart s_θ hsr_le_sθ
    exact isBiotSavart_jscaleInv ha_θ_pos hw_θ_l2 hbs_c
  have hkin_θ_le : kinNorm (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ)) ≤
      ENNReal.ofReal ((ν * θ)⁻¹) * velNorm c (u s_θ) := by
    calc kinNorm (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ))
        ≤ velNorm (dOfTheta ν θ) (rescaleVel (ν * θ)⁻¹ (u s_θ)) :=
          iInf₂_le (rescaleVel (ν * θ)⁻¹ (u s_θ)) hu_θ_bs_d
      _ = ENNReal.ofReal ((ν * θ)⁻¹) * velNorm (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹)) (u s_θ) := by
          refine velNorm_rescaleVel ha_θ_pos fun j => ?_
          rw [hd_θ_eq]; exact (hw.biotSavart s_θ hsr_le_sθ).1 j
      _ = ENNReal.ofReal ((ν * θ)⁻¹) * velNorm c (u s_θ) := by rw [hd_θ_eq]
  -- Step 2: Physical evolution bound `velNorm c (u s_θ) ≤ ofReal C * velNorm c (u s_r)`
  have hvel_evol : velNorm c (u s_θ) ≤ ENNReal.ofReal C * velNorm c (u s_r) :=
    linearised_velNorm_evolution_bound hm hC_strain hb hν_pos hc1 hsr_gt_H1 hsr_pos hsr_le_sθ
      htr hStrain_bd hf₀_zc hw
  -- Step 3: For every `u_h` with `IsBiotSavart (dOfTheta ν r) h u_h`,
  -- `velNorm c (u s_r) = ofReal (ν * r) * velNorm (dOfTheta ν r) u_h`
  have hper_uh : ∀ u_h : ℝ × ℝ → Fin 2 → ℂ, IsBiotSavart (dOfTheta ν r) h u_h →
      kinNorm (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ)) ≤
        ENNReal.ofReal (C * (r / θ)) * velNorm (dOfTheta ν r) u_h := by
    intro u_h huh
    have ha_r_pos : 0 < ν * r := mul_pos hν_pos hr_pos
    have hh_l2 : MemLp h 2 (volume.restrict (B0579.cell (c * Real.sqrt (ν * r)))) := by
      rw [hd_r_eq]
      exact memLp_unweighted_of_memX_pos (by linarith : 0 ≤ m) hh_mem
    have huh_bs : IsBiotSavart (c * Real.sqrt (ν * r)) h u_h := by rwa [hd_r_eq]
    have hsc_bs : IsBiotSavart c (Jscale (ν * r)⁻¹ h) (rescaleVel (ν * r) u_h) := by
      rw [hf₀_eq]
      exact isBiotSavart_jscaleInv ha_r_pos hh_l2 huh_bs
    have hur_bs : IsBiotSavart c (Jscale (ν * r)⁻¹ h) (u s_r) := by
      have hbs0 := hw.biotSavart s_r le_rfl
      refine ⟨hbs0.1, hbs0.2.1, fun ψ hψ => ?_⟩
      rw [← hbs0.2.2 ψ hψ]
      exact integral_congr_ae (hw.initial.symm.mono fun x hx => by dsimp only; rw [hx])
    have hae_ur := CTE.isBiotSavart_unique c hc_pos _ (u s_r) (rescaleVel (ν * r) u_h) hur_bs hsc_bs
    have hur_eq : velNorm c (u s_r) = ENNReal.ofReal (ν * r) * velNorm (dOfTheta ν r) u_h := by
      rw [velNorm_congr_ae hae_ur, velNorm_rescaleVel ha_r_pos huh_bs.1, hd_r_eq]
    have hcoeff : ENNReal.ofReal ((ν * θ)⁻¹) * (ENNReal.ofReal C * ENNReal.ofReal (ν * r)) =
        ENNReal.ofReal (C * (r / θ)) := by
      rw [← ENNReal.ofReal_mul hC_pos.le, ← ENNReal.ofReal_mul ha_θ_pos.le]
      congr 1
      have hν_ne := hν_pos.ne'
      have hθ_ne := hθ.ne'
      field_simp
    calc kinNorm (dOfTheta ν θ) (JscaleInv (ν * θ)⁻¹ (w s_θ))
        ≤ ENNReal.ofReal ((ν * θ)⁻¹) * velNorm c (u s_θ) := hkin_θ_le
      _ ≤ ENNReal.ofReal ((ν * θ)⁻¹) * (ENNReal.ofReal C * velNorm c (u s_r)) :=
          mul_le_mul_of_nonneg_left hvel_evol bot_le
      _ = (ENNReal.ofReal ((ν * θ)⁻¹) * (ENNReal.ofReal C * ENNReal.ofReal (ν * r))) *
            velNorm (dOfTheta ν r) u_h := by
          rw [hur_eq, mul_assoc, mul_assoc]
      _ = ENNReal.ofReal (C * (r / θ)) * velNorm (dOfTheta ν r) u_h := by rw [hcoeff]
  -- Conclude for `kinNorm (dOfTheta ν r) h` (splitting on existence of a Biot-Savart velocity `u_h`)
  by_cases hex : ∃ u_h, IsBiotSavart (dOfTheta ν r) h u_h
  · obtain ⟨u_0, hu_0⟩ := hex
    let S := {u_h : ℝ × ℝ → Fin 2 → ℂ // IsBiotSavart (dOfTheta ν r) h u_h}
    have : Nonempty S := ⟨⟨u_0, hu_0⟩⟩
    have hkin_eq : kinNorm (dOfTheta ν r) h = ⨅ s : S, velNorm (dOfTheta ν r) s.1 := by
      unfold kinNorm
      exact iInf_subtype' (p := IsBiotSavart (dOfTheta ν r) h)
        (f := fun u_h _ => velNorm (dOfTheta ν r) u_h)
    rw [hkin_eq, ENNReal.mul_iInf (fun htop => (ENNReal.ofReal_ne_top htop).elim)]
    exact le_iInf fun s => hper_uh s.1 s.2
  · have hex' : ∀ u_h, ¬ IsBiotSavart (dOfTheta ν r) h u_h := not_exists.mp hex
    have hkin_top : kinNorm (dOfTheta ν r) h = ⊤ := by
      unfold kinNorm; simp [hex']
    have hcoeff_pos : 0 < C * (r / θ) := mul_pos hC_pos (div_pos hr_pos hθ)
    have hcoeff_ne : ENNReal.ofReal (C * (r / θ)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hcoeff_pos).ne'
    rw [hkin_top, ENNReal.mul_top hcoeff_ne]
    exact le_top

end UnforcedLeray.Short.IIIa
