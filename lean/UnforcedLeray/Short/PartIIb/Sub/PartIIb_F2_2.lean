import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2
import UnforcedLeray.Short.PartIIb.Tasks.FreeCylinderBound
import UnforcedLeray.Units.B0610

/-!
# `PartII-b:F2/2` (`Sub/PartII-b_F2_2.lean`): Free and coupled cylinder vorticity propagators

Source of record: `the November 2 reference manuscript` (SP), lines 2076–2083,
2141–2155 (`short-bg:coupled-prop`).

This module provides:
1. Algebraic and regularity closure of weak free cylinder solutions `IsFreeCylFlow`
   (`IsFreeCylFlow.congr_initial`, `IsFreeCylFlow.add`, `IsFreeCylFlow.smul`,
   `IsFreeCylFlow.restrict`);
2. `exists_freeCylPropagator_of_flow` and `exists_freeCylPropagator_of_trainCloseM`: lifting the
   unique weak free cylinder evolution from `freeCylinderBound_proof` (`PartII-b:T24`) to a
   two-parameter continuous linear operator family `Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)`
   satisfying `IsFreeCylPropagator m p Sc` and `‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))` on
   `0 ≤ s ≤ t ≤ p.H`, together with `IsFreeCylPropagator.integrable`,
   `IsFreeCylPropagator.integrable_self`, `IsFreeCylPropagator.timeIntegrable`, and
   `IsFreeCylPropagator.weak`;
3. `cellCircCLM` and `cellTestCLM`: continuous linear functionals on `Xmc c m` (`1 / 2 < m`)
   realizing `w ↦ ∫_{cell c} w` and `w ↦ ∫_{cell c} w φ`, with interval-integral preservation of
   `HasZeroCirculationR c` (`hasZeroCirculationR_intervalIntegral`) and unconditional proof of
   `IsCoupledPropagator.integrable` (`integrableOn_cylCoupledIntegrand_of_freeProp`);
4. `IsMildDuhamelPropagator`, `IsMildDuhamelPropagator.zeroCirc_of_free_and_interaction`, and
   `IsMildDuhamelPropagator.weak_of_fubini`: reduction of `IsCoupledDuhamelPropagator` to:
   * `MildDuhamelEvolutionStep` (`PartII-b:F2/2/1`, SP 2076–2083, 2147–2155),
   * `FreeAndInteractionZeroCircStep` (`PartII-b:F2/2/2`, SP 2076–2083, 2117–2123),
   * `MildDuhamelWeakStep` (`PartII-b:F2/2/3`, SP 2076–2083, 2147–2155),
   and the unconditional assembly theorem `coupledPropagatorStep_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Measure, circulation, and test-pairing functionals on `B0579.cell c` -/

theorem ae_restrict_cell_of_cellMeasure {c m : ℝ} {f g : B0579.Plane → ℝ}
    (h : f =ᵐ[B0579.cellMeasure c m] g) :
    f =ᵐ[volume.restrict (B0579.cell c)] g :=
  (B0579.ac_cellMeasure c m).ae_le h

theorem ae_cellMeasure_of_restrict_cell {c m : ℝ} {f g : B0579.Plane → ℝ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    f =ᵐ[B0579.cellMeasure c m] g :=
  (B0579.cellMeasure_ac c m).ae_le h

/-- Every function `g` in `MemLp g 2 (B0579.cellMeasure c m)` is integrable against any cylinder
test `B0579.IsCylTest c φ` on `B0579.cell c`. -/
theorem integrableOn_mul_cylTest_of_memLp {c m : ℝ} {g φ : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hφ : B0579.IsCylTest c φ) :
    IntegrableOn (fun x => g x * φ x) (B0579.cell c) volume := by
  let w : Xmc c m := hg.toLp g
  have hw_int : IntegrableOn (fun x => w x * φ x) (B0579.cell c) volume := by
    have h := B0579.integrableOn_source c m w (B0579.testH1 c (-m) hφ)
    refine h.congr_fun_ae ?_
    filter_upwards [B0579.coeFn_testLp c (-m) hφ] with x hx
    rw [B0579.testH1_value, hx]
  have hw_ae : (w : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] g :=
    ae_restrict_cell_of_cellMeasure (MemLp.coeFn_toLp hg)
  refine hw_int.congr_fun_ae ?_
  filter_upwards [hw_ae] with x hx
  rw [hx]

namespace PartIIbF22Aux

/-- Continuous linear functional `w ↦ ∫ x in B0579.cell c, w x` on `Xmc c m` for `1 / 2 < m`. -/
def cellCircCLM (c m : ℝ) (hm : 1 / 2 < m) : Xmc c m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (B0610.oneH1 c m hm)).comp (B0579.sourceCLM c m)

@[simp] theorem cellCircCLM_apply (c m : ℝ) (hm : 1 / 2 < m) (w : Xmc c m) :
    cellCircCLM c m hm w = ∫ x in B0579.cell c, w x :=
  B0610.sourceCLM_oneH1 hm w

/-- Every `w : Xmc c m` (`1 / 2 < m`) is integrable on `B0579.cell c`. -/
theorem integrableOn_cell_of_Xmc (c m : ℝ) (hm : 1 / 2 < m) (w : Xmc c m) :
    IntegrableOn w (B0579.cell c) volume := by
  have h := B0579.integrableOn_source c m w (B0610.oneH1 c m hm)
  refine h.congr_fun_ae ?_
  filter_upwards [B0610.coeFn_oneX (c := c) hm] with x hx
  rw [B0610.oneH1_value, hx, mul_one]

/-- For `w : Xmc c m` (`1 / 2 < m`), `HasZeroCirculationR c w` holds iff `cellCircCLM c m hm w = 0`. -/
theorem hasZeroCirculationR_iff_cellCircCLM (c m : ℝ) (hm : 1 / 2 < m) (w : Xmc c m) :
    HasZeroCirculationR c w ↔ cellCircCLM c m hm w = 0 := by
  unfold HasZeroCirculationR
  rw [cellCircCLM_apply]
  exact ⟨fun h => h.2, fun h => ⟨integrableOn_cell_of_Xmc c m hm w, h⟩⟩

theorem hasZeroCirculationR_add {c m : ℝ} (hm : 1 / 2 < m) {u v : Xmc c m}
    (hu : HasZeroCirculationR c u) (hv : HasZeroCirculationR c v) :
    HasZeroCirculationR c (u + v : Xmc c m) := by
  rw [hasZeroCirculationR_iff_cellCircCLM c m hm] at hu hv ⊢
  rw [map_add, hu, hv, add_zero]

/-- Interval Bochner integration on `Xmc c m` (`1 / 2 < m`) preserves `HasZeroCirculationR c`. -/
theorem hasZeroCirculationR_intervalIntegral {c m s t : ℝ} (hm : 1 / 2 < m) (hst : s ≤ t)
    {g : ℝ → Xmc c m} (hg_int : IntervalIntegrable g volume s t)
    (hg_circ : ∀ r ∈ Icc s t, HasZeroCirculationR c (g r)) :
    HasZeroCirculationR c (∫ r in s..t, g r : Xmc c m) := by
  rw [hasZeroCirculationR_iff_cellCircCLM c m hm]
  rw [← (cellCircCLM c m hm).intervalIntegral_comp_comm hg_int]
  have h0 : ∫ r in s..t, cellCircCLM c m hm (g r) = ∫ _ in s..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hst] at hr
    exact (hasZeroCirculationR_iff_cellCircCLM c m hm (g r)).1 (hg_circ r ⟨hr.1.le, hr.2⟩)
  rw [h0, intervalIntegral.integral_zero]

/-- Continuous linear functional `w ↦ ∫ x in B0579.cell c, w x * φ x` on `Xmc c m` for a cylinder
test function `B0579.IsCylTest c φ`. -/
def cellTestCLM (c m : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    Xmc c m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (B0579.testH1 c (-m) hφ)).comp (B0579.sourceCLM c m)

@[simp] theorem cellTestCLM_apply (c m : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (w : Xmc c m) :
    cellTestCLM c m hφ w = ∫ x in B0579.cell c, w x * φ x :=
  B0579.toDistribution_sourceCLM c m w ⟨φ, hφ⟩

end PartIIbF22Aux

open PartIIbF22Aux

/-! ## 2. Linearity, initial congruence, and cocycle restriction of `IsFreeCylFlow` -/

theorem IsFreeCylFlow.memLp_initial {ν c m t₀ : ℝ} {tr : B0140.TrainSol ν c}
    {f : B0579.Plane → ℝ} {ω : ℝ → B0579.Plane → ℝ}
    (hω : IsFreeCylFlow m tr t₀ f ω) :
    MemLp f 2 (B0579.cellMeasure c m) :=
  (hω.memX t₀ le_rfl).ae_eq (ae_cellMeasure_of_restrict_cell hω.initial)

theorem IsFreeCylFlow.congr_initial {ν c m t₀ : ℝ} {tr : B0140.TrainSol ν c}
    {f₁ f₂ : B0579.Plane → ℝ} {ω : ℝ → B0579.Plane → ℝ}
    (hω : IsFreeCylFlow m tr t₀ f₁ ω)
    (hf : f₁ =ᵐ[volume.restrict (B0579.cell c)] f₂) :
    IsFreeCylFlow m tr t₀ f₂ ω where
  initial := hω.initial.trans hf
  memX := hω.memX
  strongCont := hω.strongCont
  integrable := hω.integrable
  timeIntegrable := hω.timeIntegrable
  weak := by
    intro φ hφ s hs
    have h_init_eq : (∫ x in B0579.cell c, f₁ x * φ x) = ∫ x in B0579.cell c, f₂ x * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hf] with x hx
      rw [hx]
    rw [← h_init_eq]
    exact hω.weak φ hφ s hs

theorem IsFreeCylFlow.add {ν c m t₀ : ℝ} {tr : B0140.TrainSol ν c}
    {f₁ f₂ : B0579.Plane → ℝ} {ω₁ ω₂ : ℝ → B0579.Plane → ℝ}
    (h₁ : IsFreeCylFlow m tr t₀ f₁ ω₁) (h₂ : IsFreeCylFlow m tr t₀ f₂ ω₂) :
    IsFreeCylFlow m tr t₀ (fun x => f₁ x + f₂ x) (fun t x => ω₁ t x + ω₂ t x) where
  initial := by
    filter_upwards [h₁.initial, h₂.initial] with x hx₁ hx₂
    exact congrArg₂ (· + ·) hx₁ hx₂
  memX := fun s hs => (h₁.memX s hs).add (h₂.memX s hs)
  strongCont := by
    intro s hs
    have h_zero : Tendsto (fun s' =>
        eLpNorm (ω₁ s' - ω₁ s) 2 (B0579.cellMeasure c m) +
          eLpNorm (ω₂ s' - ω₂ s) 2 (B0579.cellMeasure c m)) (𝓝[Ici t₀] s) (𝓝 0) := by
      simpa using (h₁.strongCont s hs).add (h₂.strongCont s hs)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_zero
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    have heq : (fun x => (ω₁ s' x + ω₂ s' x) - (ω₁ s x + ω₂ s x)) =
        (ω₁ s' - ω₁ s) + (ω₂ s' - ω₂ s) := by
      funext x; simp [Pi.add_apply, Pi.sub_apply]; ring
    rw [show ((fun t x => ω₁ t x + ω₂ t x) s' - (fun t x => ω₁ t x + ω₂ t x) s) =
        fun x => (ω₁ s' x + ω₂ s' x) - (ω₁ s x + ω₂ s x) from rfl, heq]
    exact eLpNorm_add_le
      (((h₁.memX s' hs').sub (h₁.memX s hs)).aestronglyMeasurable)
      (((h₂.memX s' hs').sub (h₂.memX s hs)).aestronglyMeasurable)
      (by norm_num)
  integrable := by
    intro φ hφ r hr
    have heq : cylFreeIntegrand tr (fun x => ω₁ r x + ω₂ r x) r φ =
        fun x => cylFreeIntegrand tr (ω₁ r) r φ x + cylFreeIntegrand tr (ω₂ r) r φ x := by
      funext x; unfold cylFreeIntegrand; ring
    rw [heq]
    exact (h₁.integrable φ hφ r hr).add (h₂.integrable φ hφ r hr)
  timeIntegrable := by
    intro φ hφ s hs
    have h_sum := (h₁.timeIntegrable φ hφ s hs).add (h₂.timeIntegrable φ hφ s hs)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs] at h_sum ⊢
    refine h_sum.congr_fun (fun r hr => ?_) measurableSet_Ioc
    have heq : cylFreeIntegrand tr (fun x => ω₁ r x + ω₂ r x) r φ =
        fun x => cylFreeIntegrand tr (ω₁ r) r φ x + cylFreeIntegrand tr (ω₂ r) r φ x := by
      funext x; unfold cylFreeIntegrand; ring
    simp only [heq]
    exact (integral_add (h₁.integrable φ hφ r hr.1.le) (h₂.integrable φ hφ r hr.1.le)).symm
  weak := by
    intro φ hφ s hs
    have hω₁_int := integrableOn_mul_cylTest_of_memLp (h₁.memX s hs) hφ
    have hω₂_int := integrableOn_mul_cylTest_of_memLp (h₂.memX s hs) hφ
    have hf₁_int := integrableOn_mul_cylTest_of_memLp h₁.memLp_initial hφ
    have hf₂_int := integrableOn_mul_cylTest_of_memLp h₂.memLp_initial hφ
    have h_lhs : (∫ x in B0579.cell c, (ω₁ s x + ω₂ s x) * φ x) =
        (∫ x in B0579.cell c, ω₁ s x * φ x) + ∫ x in B0579.cell c, ω₂ s x * φ x := by
      have h_mul : (fun x => (ω₁ s x + ω₂ s x) * φ x) =
          fun x => ω₁ s x * φ x + ω₂ s x * φ x := by funext x; ring
      rw [h_mul, integral_add hω₁_int hω₂_int]
    have h_init : (∫ x in B0579.cell c, (f₁ x + f₂ x) * φ x) =
        (∫ x in B0579.cell c, f₁ x * φ x) + ∫ x in B0579.cell c, f₂ x * φ x := by
      have h_mul : (fun x => (f₁ x + f₂ x) * φ x) =
          fun x => f₁ x * φ x + f₂ x * φ x := by funext x; ring
      rw [h_mul, integral_add hf₁_int hf₂_int]
    have h_time : (∫ r in t₀..s, ∫ x in B0579.cell c,
          cylFreeIntegrand tr (fun x => ω₁ r x + ω₂ r x) r φ x) =
        (∫ r in t₀..s, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω₁ r) r φ x) +
          ∫ r in t₀..s, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω₂ r) r φ x := by
      rw [← intervalIntegral.integral_add (h₁.timeIntegrable φ hφ s hs)
        (h₂.timeIntegrable φ hφ s hs)]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
      rw [uIoc_of_le hs] at hr
      have heq : cylFreeIntegrand tr (fun x => ω₁ r x + ω₂ r x) r φ =
          fun x => cylFreeIntegrand tr (ω₁ r) r φ x + cylFreeIntegrand tr (ω₂ r) r φ x := by
        funext x; unfold cylFreeIntegrand; ring
      rw [heq, integral_add (h₁.integrable φ hφ r hr.1.le) (h₂.integrable φ hφ r hr.1.le)]
    rw [h_lhs, h_init, h_time, h₁.weak φ hφ s hs, h₂.weak φ hφ s hs]
    ring

theorem IsFreeCylFlow.smul {ν c m t₀ : ℝ} {tr : B0140.TrainSol ν c} (a : ℝ)
    {f : B0579.Plane → ℝ} {ω : ℝ → B0579.Plane → ℝ}
    (hω : IsFreeCylFlow m tr t₀ f ω) :
    IsFreeCylFlow m tr t₀ (fun x => a * f x) (fun t x => a * ω t x) where
  initial := by
    filter_upwards [hω.initial] with x hx
    exact congrArg (a * ·) hx
  memX := fun s hs => (hω.memX s hs).const_mul a
  strongCont := by
    intro s hs
    have h_zero : Tendsto (fun s' =>
        ENNReal.ofReal |a| * eLpNorm (ω s' - ω s) 2 (B0579.cellMeasure c m))
        (𝓝[Ici t₀] s) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hω.strongCont s hs) (Or.inr ENNReal.ofReal_ne_top)
    refine h_zero.congr fun s' => ?_
    have heq : ((fun t x => a * ω t x) s' - (fun t x => a * ω t x) s) =
        a • (ω s' - ω s) := by
      funext x; simp [Pi.sub_apply, Pi.smul_apply]; ring
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  integrable := by
    intro φ hφ r hr
    have heq : cylFreeIntegrand tr (fun x => a * ω r x) r φ =
        fun x => a * cylFreeIntegrand tr (ω r) r φ x := by
      funext x; unfold cylFreeIntegrand; ring
    rw [heq]
    exact (hω.integrable φ hφ r hr).const_mul a
  timeIntegrable := by
    intro φ hφ s hs
    have h_smul := (hω.timeIntegrable φ hφ s hs).const_mul a
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs] at h_smul ⊢
    refine h_smul.congr_fun (fun r hr => ?_) measurableSet_Ioc
    have heq : cylFreeIntegrand tr (fun x => a * ω r x) r φ =
        fun x => a * cylFreeIntegrand tr (ω r) r φ x := by
      funext x; unfold cylFreeIntegrand; ring
    simp only [heq, integral_const_mul]
  weak := by
    intro φ hφ s hs
    have h_lhs : (∫ x in B0579.cell c, (a * ω s x) * φ x) =
        a * ∫ x in B0579.cell c, ω s x * φ x := by
      have h_mul : (fun x => (a * ω s x) * φ x) = fun x => a * (ω s x * φ x) := by
        funext x; ring
      rw [h_mul, integral_const_mul]
    have h_init : (∫ x in B0579.cell c, (a * f x) * φ x) =
        a * ∫ x in B0579.cell c, f x * φ x := by
      have h_mul : (fun x => (a * f x) * φ x) = fun x => a * (f x * φ x) := by
        funext x; ring
      rw [h_mul, integral_const_mul]
    have h_time : (∫ r in t₀..s, ∫ x in B0579.cell c,
          cylFreeIntegrand tr (fun x => a * ω r x) r φ x) =
        a * ∫ r in t₀..s, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r φ x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r _ => ?_)
      have heq : cylFreeIntegrand tr (fun x => a * ω r x) r φ =
          fun x => a * cylFreeIntegrand tr (ω r) r φ x := by
        funext x; unfold cylFreeIntegrand; ring
      rw [heq, integral_const_mul]
    rw [h_lhs, h_init, h_time, hω.weak φ hφ s hs]
    ring

theorem IsFreeCylFlow.restrict {ν c m t₀ t₁ : ℝ} {tr : B0140.TrainSol ν c}
    {f : B0579.Plane → ℝ} {ω : ℝ → B0579.Plane → ℝ}
    (hω : IsFreeCylFlow m tr t₀ f ω) (ht₁ : t₀ ≤ t₁) :
    IsFreeCylFlow m tr t₁ (ω t₁) ω where
  initial := EventuallyEq.rfl
  memX := fun s hs => hω.memX s (ht₁.trans hs)
  strongCont := fun s hs =>
    (hω.strongCont s (ht₁.trans hs)).mono_left (nhdsWithin_mono s (Ici_subset_Ici.mpr ht₁))
  integrable := fun φ hφ r hr => hω.integrable φ hφ r (ht₁.trans hr)
  timeIntegrable := by
    intro φ hφ s hs
    have h_full := hω.timeIntegrable φ hφ s (ht₁.trans hs)
    refine h_full.mono_set ?_
    rw [uIcc_of_le hs, uIcc_of_le (ht₁.trans hs)]
    exact Icc_subset_Icc_left ht₁
  weak := by
    intro φ hφ s hs
    have h_s := hω.weak φ hφ s (ht₁.trans hs)
    have h_t₁ := hω.weak φ hφ t₁ ht₁
    have h_int₁ : IntervalIntegrable
        (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r φ x) volume t₀ t₁ :=
      hω.timeIntegrable φ hφ t₁ ht₁
    have h_int₂ : IntervalIntegrable
        (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r φ x) volume t₁ s := by
      refine (hω.timeIntegrable φ hφ s (ht₁.trans hs)).mono_set ?_
      rw [uIcc_of_le hs, uIcc_of_le (ht₁.trans hs)]
      exact Icc_subset_Icc_left ht₁
    have h_adj := intervalIntegral.integral_add_adjacent_intervals h_int₁ h_int₂
    linarith [h_s, h_t₁, h_adj]

/-! ## 3. Lifting `FreeCylinderBound` to `IsFreeCylPropagator` -/

section FreePropagatorLift

variable {m : ℝ} {p : Params} {K₀ : ℝ}

/-- Hypothesis packaging existence, cell-a.e. uniqueness, and exponential `L²` growth of
`IsFreeCylFlow m p.train s f ω` on `0 ≤ s ≤ t ≤ p.H`. -/
def HasFreeCylFlowFamily (m : ℝ) (p : Params) (K₀ : ℝ) : Prop :=
  ∀ s ∈ Icc 0 p.H, ∀ f : B0579.Plane → ℝ, MemLp f 2 (B0579.cellMeasure p.c m) →
    ∃ ω : ℝ → B0579.Plane → ℝ,
      IsFreeCylFlow m p.train s f ω ∧
      (∀ ω' : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω' →
        ∀ t' : ℝ, s ≤ t' → ω' t' =ᵐ[volume.restrict (B0579.cell p.c)] ω t') ∧
      ∀ t ∈ Icc s p.H,
        eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≤
          ENNReal.ofReal (Real.exp (K₀ * (t - s))) * eLpNorm f 2 (B0579.cellMeasure p.c m)

/-- Chosen weak free cylinder trajectory starting from `(s, f)` for `s ∈ Icc 0 p.H`. -/
def chosenFreeFlow (hF : HasFreeCylFlowFamily m p K₀)
    {s : ℝ} (hs : s ∈ Icc 0 p.H) (f : Xmc p.c m) : ℝ → B0579.Plane → ℝ :=
  Classical.choose (hF s hs f (Lp.memLp f))

theorem chosenFreeFlow_spec (hF : HasFreeCylFlowFamily m p K₀)
    {s : ℝ} (hs : s ∈ Icc 0 p.H) (f : Xmc p.c m) :
    IsFreeCylFlow m p.train s f (chosenFreeFlow hF hs f) ∧
    (∀ ω' : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω' →
      ∀ t' : ℝ, s ≤ t' → ω' t' =ᵐ[volume.restrict (B0579.cell p.c)] chosenFreeFlow hF hs f t') ∧
    ∀ t ∈ Icc s p.H,
      eLpNorm (chosenFreeFlow hF hs f t) 2 (B0579.cellMeasure p.c m) ≤
        ENNReal.ofReal (Real.exp (K₀ * (t - s))) * eLpNorm f 2 (B0579.cellMeasure p.c m) :=
  Classical.choose_spec (hF s hs f (Lp.memLp f))

/-- Element of `Xmc p.c m` representing the free cylinder evolution at time `t ∈ Icc s p.H`. -/
def freeCylPropagatorVal (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) (f : Xmc p.c m) : Xmc p.c m :=
  ((chosenFreeFlow_spec hF hs f).1.memX t ht.1).toLp (chosenFreeFlow hF hs f t)

theorem coeFn_freeCylPropagatorVal_cellMeasure (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) (f : Xmc p.c m) :
    (freeCylPropagatorVal hF hs ht f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m]
      chosenFreeFlow hF hs f t :=
  MemLp.coeFn_toLp _

theorem coeFn_freeCylPropagatorVal (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) (f : Xmc p.c m) :
    (freeCylPropagatorVal hF hs ht f : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
      chosenFreeFlow hF hs f t :=
  ae_restrict_cell_of_cellMeasure (coeFn_freeCylPropagatorVal_cellMeasure hF hs ht f)

theorem freeCylPropagatorVal_eq_of_isFreeCylFlow (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) (f : Xmc p.c m)
    {ω' : ℝ → B0579.Plane → ℝ} (hω' : IsFreeCylFlow m p.train s f ω') :
    (freeCylPropagatorVal hF hs ht f : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] ω' t := by
  have h_uniq := (chosenFreeFlow_spec hF hs f).2.1 ω' hω' t ht.1
  exact (coeFn_freeCylPropagatorVal_cellMeasure hF hs ht f).trans
    (ae_cellMeasure_of_restrict_cell h_uniq.symm)

theorem norm_freeCylPropagatorVal_le (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) (f : Xmc p.c m) :
    ‖freeCylPropagatorVal hF hs ht f‖ ≤ Real.exp (K₀ * (t - s)) * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have h_toLp : eLpNorm (freeCylPropagatorVal hF hs ht f) 2 (B0579.cellMeasure p.c m) =
      eLpNorm (chosenFreeFlow hF hs f t) 2 (B0579.cellMeasure p.c m) :=
    eLpNorm_congr_ae (coeFn_freeCylPropagatorVal_cellMeasure hF hs ht f)
  rw [h_toLp]
  have h_bd := (chosenFreeFlow_spec hF hs f).2.2 t ht
  have h_fin : ENNReal.ofReal (Real.exp (K₀ * (t - s))) *
      eLpNorm f 2 (B0579.cellMeasure p.c m) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_lt_top f).ne
  have h_le := (ENNReal.toReal_le_toReal
    ((chosenFreeFlow_spec hF hs f).1.memX t ht.1).eLpNorm_lt_top.ne h_fin).2 h_bd
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h_le
  exact h_le

/-- Continuous linear map `Sc t s` for `s ∈ Icc 0 p.H` and `t ∈ Icc s p.H`. -/
def freeCylPropagatorCLM (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) :
    Xmc p.c m →L[ℝ] Xmc p.c m :=
  LinearMap.mkContinuous
    { toFun := freeCylPropagatorVal hF hs ht
      map_add' := fun f g => by
        refine Lp.ext ?_
        have h_add_flow : IsFreeCylFlow m p.train s (f + g : Xmc p.c m)
            (fun r x => chosenFreeFlow hF hs f r x + chosenFreeFlow hF hs g r x) := by
          have h12 := (chosenFreeFlow_spec hF hs f).1.add (chosenFreeFlow_spec hF hs g).1
          exact h12.congr_initial (ae_restrict_cell_of_cellMeasure (Lp.coeFn_add f g).symm)
        have h_fg := freeCylPropagatorVal_eq_of_isFreeCylFlow hF hs ht (f + g) h_add_flow
        have h_f := coeFn_freeCylPropagatorVal_cellMeasure hF hs ht f
        have h_g := coeFn_freeCylPropagatorVal_cellMeasure hF hs ht g
        filter_upwards [h_fg, Lp.coeFn_add (freeCylPropagatorVal hF hs ht f)
          (freeCylPropagatorVal hF hs ht g), h_f, h_g] with x hx_fg hx_add hx_f hx_g
        rw [hx_fg, hx_add, Pi.add_apply, hx_f, hx_g]
      map_smul' := fun a f => by
        refine Lp.ext ?_
        have h_smul_flow : IsFreeCylFlow m p.train s (a • f : Xmc p.c m)
            (fun r x => a * chosenFreeFlow hF hs f r x) := by
          have h1 := (chosenFreeFlow_spec hF hs f).1.smul a
          exact h1.congr_initial (ae_restrict_cell_of_cellMeasure (Lp.coeFn_smul a f).symm)
        have h_af := freeCylPropagatorVal_eq_of_isFreeCylFlow hF hs ht (a • f) h_smul_flow
        have h_f := coeFn_freeCylPropagatorVal_cellMeasure hF hs ht f
        filter_upwards [h_af, Lp.coeFn_smul a (freeCylPropagatorVal hF hs ht f), h_f]
          with x hx_af hx_smul hx_f
        rw [RingHom.id_apply, hx_af, hx_smul, Pi.smul_apply, smul_eq_mul, hx_f] }
    (Real.exp (K₀ * (t - s)))
    (norm_freeCylPropagatorVal_le hF hs ht)

@[simp] theorem freeCylPropagatorCLM_apply (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) (f : Xmc p.c m) :
    freeCylPropagatorCLM hF hs ht f = freeCylPropagatorVal hF hs ht f :=
  rfl

theorem norm_freeCylPropagatorCLM_le (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) :
    ‖freeCylPropagatorCLM hF hs ht‖ ≤ Real.exp (K₀ * (t - s)) :=
  LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _

/-- Two-parameter free cylinder propagator `Sc t s : Xmc p.c m →L[ℝ] Xmc p.c m`. -/
def freeCylPropagator (hF : HasFreeCylFlowFamily m p K₀) (t s : ℝ) :
    Xmc p.c m →L[ℝ] Xmc p.c m :=
  if h : s ∈ Icc 0 p.H ∧ t ∈ Icc s p.H then
    freeCylPropagatorCLM hF h.1 h.2
  else
    ContinuousLinearMap.id ℝ (Xmc p.c m)

theorem freeCylPropagator_eq_of_mem (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : s ∈ Icc 0 p.H) (ht : t ∈ Icc s p.H) :
    freeCylPropagator hF t s = freeCylPropagatorCLM hF hs ht := by
  simp [freeCylPropagator, hs, ht]

theorem isFreeCylPropagator_freeCylPropagator (hF : HasFreeCylFlowFamily m p K₀) :
    IsFreeCylPropagator m p (freeCylPropagator hF) where
  id_self := by
    intro s hs
    have hs_self : s ∈ Icc s p.H := ⟨le_rfl, hs.2⟩
    rw [freeCylPropagator_eq_of_mem hF hs hs_self]
    ext1 f
    refine Lp.ext ?_
    have h_ae := coeFn_freeCylPropagatorVal hF hs hs_self f
    have h_init := (chosenFreeFlow_spec hF hs f).1.initial
    exact ae_cellMeasure_of_restrict_cell (h_ae.trans h_init)
  comp_cocycle := by
    intro s r t hs0 hsr hrt htH
    have hs : s ∈ Icc 0 p.H := ⟨hs0, (hsr.trans hrt).trans htH⟩
    have hr : r ∈ Icc 0 p.H := ⟨hs0.trans hsr, hrt.trans htH⟩
    have hr_s : r ∈ Icc s p.H := ⟨hsr, hrt.trans htH⟩
    have ht_r : t ∈ Icc r p.H := ⟨hrt, htH⟩
    have ht_s : t ∈ Icc s p.H := ⟨hsr.trans hrt, htH⟩
    rw [freeCylPropagator_eq_of_mem hF hr ht_r,
      freeCylPropagator_eq_of_mem hF hs hr_s,
      freeCylPropagator_eq_of_mem hF hs ht_s]
    ext1 f
    simp only [ContinuousLinearMap.comp_apply, freeCylPropagatorCLM_apply]
    refine Lp.ext ?_
    set g : Xmc p.c m := freeCylPropagatorVal hF hs hr_s f
    have hg_ae : chosenFreeFlow hF hs f r =ᵐ[volume.restrict (B0579.cell p.c)] g :=
      (coeFn_freeCylPropagatorVal hF hs hr_s f).symm
    have h_rest : IsFreeCylFlow m p.train r g (chosenFreeFlow hF hs f) :=
      ((chosenFreeFlow_spec hF hs f).1.restrict hsr).congr_initial hg_ae
    have h_tr := freeCylPropagatorVal_eq_of_isFreeCylFlow hF hr ht_r g h_rest
    have h_ts := coeFn_freeCylPropagatorVal_cellMeasure hF hs ht_s f
    exact h_tr.trans h_ts.symm
  strongCont := by
    intro s hs f t ht
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have h_cont := (chosenFreeFlow_spec hF hs f).1.strongCont t ht.1
    have h_mem : Iio (ENNReal.ofReal ε) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε)
    have h_nhds : {t' : ℝ | eLpNorm (chosenFreeFlow hF hs f t' - chosenFreeFlow hF hs f t) 2
        (B0579.cellMeasure p.c m) < ENNReal.ofReal ε} ∈ 𝓝[Icc s p.H] t :=
      nhdsWithin_mono t Icc_subset_Ici_self (h_cont h_mem)
    rw [Metric.mem_nhdsWithin_iff] at h_nhds
    obtain ⟨δ, hδ, h_ball⟩ := h_nhds
    refine ⟨δ, hδ, fun t' ht'_mem ht'_dist => ?_⟩
    have ht'_sub : eLpNorm (chosenFreeFlow hF hs f t' - chosenFreeFlow hF hs f t) 2
        (B0579.cellMeasure p.c m) < ENNReal.ofReal ε :=
      h_ball ⟨ht'_dist, ht'_mem⟩
    rw [dist_eq_norm, freeCylPropagator_eq_of_mem hF hs ht'_mem,
      freeCylPropagator_eq_of_mem hF hs ht,
      freeCylPropagatorCLM_apply, freeCylPropagatorCLM_apply, Lp.norm_def]
    have h_ae_sub : ((freeCylPropagatorVal hF hs ht'_mem f -
        freeCylPropagatorVal hF hs ht f : Xmc p.c m) : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m]
        chosenFreeFlow hF hs f t' - chosenFreeFlow hF hs f t := by
      filter_upwards [Lp.coeFn_sub (freeCylPropagatorVal hF hs ht'_mem f)
        (freeCylPropagatorVal hF hs ht f),
        coeFn_freeCylPropagatorVal_cellMeasure hF hs ht'_mem f,
        coeFn_freeCylPropagatorVal_cellMeasure hF hs ht f] with x hx_sub hx₁ hx₂
      rw [hx_sub, Pi.sub_apply, hx₁, hx₂, Pi.sub_apply]
    rw [eLpNorm_congr_ae h_ae_sub]
    have h_lt := (ENNReal.toReal_lt_toReal
      (lt_of_lt_of_le ht'_sub le_top).ne ENNReal.ofReal_ne_top).mpr ht'_sub
    rwa [ENNReal.toReal_ofReal hε.le] at h_lt
  flow := by
    intro s hs f
    refine ⟨chosenFreeFlow hF hs f, (chosenFreeFlow_spec hF hs f).1, fun t ht => ?_⟩
    rw [freeCylPropagator_eq_of_mem hF hs ht, freeCylPropagatorCLM_apply]
    exact coeFn_freeCylPropagatorVal hF hs ht f

theorem norm_freeCylPropagator_le (hF : HasFreeCylFlowFamily m p K₀)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ p.H) :
    ‖freeCylPropagator hF t s‖ ≤ Real.exp (K₀ * (t - s)) := by
  have hs_mem : s ∈ Icc 0 p.H := ⟨hs, hst.trans ht⟩
  have ht_mem : t ∈ Icc s p.H := ⟨hst, ht⟩
  rw [freeCylPropagator_eq_of_mem hF hs_mem ht_mem]
  exact norm_freeCylPropagatorCLM_le hF hs_mem ht_mem

end FreePropagatorLift

/-! ## 4. Weak equation and integrability properties of `IsFreeCylPropagator` and `cylCoupledIntegrand` -/

theorem IsFreeCylPropagator.integrable {m : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hSc : IsFreeCylPropagator m p Sc)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ)
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ p.H) (f : Xmc p.c m) :
    IntegrableOn (cylFreeIntegrand p.train (Sc r s f) r φ) (B0579.cell p.c) volume := by
  obtain ⟨ω, hω, hω_ae⟩ := hSc.flow s ⟨hs, hsr.trans hr⟩ f
  have h_int := hω.integrable φ hφ r hsr
  refine h_int.congr_fun_ae ?_
  filter_upwards [hω_ae r ⟨hsr, hr⟩] with x hx
  unfold cylFreeIntegrand
  rw [hx]

/-- Evaluating `IsFreeCylPropagator.integrable` at `s = r` via `hSc.id_self` shows that for every
`r ∈ Icc 0 p.H` and `w : Xmc p.c m`, `cylFreeIntegrand p.train w r φ` is integrable on
`B0579.cell p.c`. -/
theorem IsFreeCylPropagator.integrable_self {m : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hSc : IsFreeCylPropagator m p Sc)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ)
    {r : ℝ} (hr : r ∈ Icc 0 p.H) (w : Xmc p.c m) :
    IntegrableOn (cylFreeIntegrand p.train w r φ) (B0579.cell p.c) volume := by
  have h := hSc.integrable hφ hr.1 le_rfl hr.2 w
  rwa [hSc.id_self r hr, ContinuousLinearMap.id_apply] at h

theorem IsFreeCylPropagator.integral_cylFreeIntegrand_eq {m : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (_hSc : IsFreeCylPropagator m p Sc)
    {φ : B0579.Plane → ℝ} {s r : ℝ} (hsr : s ≤ r) (hr : r ≤ p.H) (f : Xmc p.c m)
    {ω : ℝ → B0579.Plane → ℝ}
    (hω_ae : ∀ t ∈ Icc s p.H, (Sc t s f : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)] ω t) :
    (∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) =
      ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (ω r) r φ x := by
  refine integral_congr_ae ?_
  filter_upwards [hω_ae r ⟨hsr, hr⟩] with x hx
  unfold cylFreeIntegrand
  rw [hx]

theorem IsFreeCylPropagator.timeIntegrable {m : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hSc : IsFreeCylPropagator m p Sc)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ p.H) (f : Xmc p.c m) :
    IntervalIntegrable
      (fun r => ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) volume s t := by
  obtain ⟨ω, hω, hω_ae⟩ := hSc.flow s ⟨hs, hst.trans ht⟩ f
  have h_ti := hω.timeIntegrable φ hφ t hst
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst] at h_ti ⊢
  refine h_ti.congr_fun (fun r hr => ?_) measurableSet_Ioc
  exact (hSc.integral_cylFreeIntegrand_eq hr.1.le (hr.2.trans ht) f hω_ae).symm

theorem IsFreeCylPropagator.weak {m : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hSc : IsFreeCylPropagator m p Sc)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ p.H) (f : Xmc p.c m) :
    ∫ x in B0579.cell p.c, (Sc t s f) x * φ x =
      (∫ x in B0579.cell p.c, f x * φ x) +
        ∫ r in s..t, ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x := by
  obtain ⟨ω, hω, hω_ae⟩ := hSc.flow s ⟨hs, hst.trans ht⟩ f
  have h_lhs : (∫ x in B0579.cell p.c, (Sc t s f) x * φ x) =
      ∫ x in B0579.cell p.c, ω t x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hω_ae t ⟨hst, ht⟩] with x hx
    rw [hx]
  have h_rhs : (∫ r in s..t, ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) =
      ∫ r in s..t, ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (ω r) r φ x := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hst] at hr
    exact hSc.integral_cylFreeIntegrand_eq hr.1.le (hr.2.trans ht) f hω_ae
  rw [h_lhs, h_rhs, hω.weak φ hφ t hst]

/-- Under `IsCylInteractionOp p.train m r A` and `B0579.IsCylTest p.c φ`, `x ↦ cylAc p.train r w x * φ x`
is integrable on `B0579.cell p.c` and its integral equals `cellTestCLM p.c m hφ (A w)`. -/
theorem integrableOn_cylAc_mul_test_of_cylOp {m r : ℝ} {p : Params}
    {A : Xmc p.c m →L[ℝ] Xmc p.c m} (hA : IsCylInteractionOp p.train m r A)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ) (w : Xmc p.c m) :
    IntegrableOn (fun x => cylAc p.train r w x * φ x) (B0579.cell p.c) volume ∧
    (∫ x in B0579.cell p.c, cylAc p.train r w x * φ x) = cellTestCLM p.c m hφ (A w) := by
  have h_ae : (fun x => (A w) x * φ x) =ᵐ[volume.restrict (B0579.cell p.c)]
      fun x => cylAc p.train r w x * φ x := by
    filter_upwards [ae_restrict_cell_of_cellMeasure (hA w)] with x hx
    rw [hx]
  have h_int : IntegrableOn (fun x => (A w) x * φ x) (B0579.cell p.c) volume :=
    integrableOn_mul_cylTest_of_memLp (Lp.memLp (A w)) hφ
  refine ⟨h_int.congr_fun_ae h_ae, ?_⟩
  rw [cellTestCLM_apply]
  exact integral_congr_ae h_ae.symm

/-- Unconditional integrability of `cylCoupledIntegrand p.train w r φ` on `B0579.cell p.c` and
decomposition of its cell integral into the free term and `cellTestCLM p.c m hφ (Ac r w)`. -/
theorem integrableOn_cylCoupledIntegrand_of_freeProp {m : ℝ} {p : Params}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)} (hSc : IsFreeCylPropagator m p Sc)
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hAc : ∀ r ∈ Icc 0 p.H, IsCylInteractionOp p.train m r (Ac r))
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ)
    {r : ℝ} (hr : r ∈ Icc 0 p.H) (w : Xmc p.c m) :
    IntegrableOn (cylCoupledIntegrand p.train w r φ) (B0579.cell p.c) volume ∧
    (∫ x in B0579.cell p.c, cylCoupledIntegrand p.train w r φ x) =
      (∫ x in B0579.cell p.c, cylFreeIntegrand p.train w r φ x) +
        cellTestCLM p.c m hφ (Ac r w) := by
  have h_free := hSc.integrable_self hφ hr w
  obtain ⟨h_ac_int, h_ac_eq⟩ := integrableOn_cylAc_mul_test_of_cylOp (hAc r hr) hφ w
  refine ⟨h_free.add h_ac_int, ?_⟩
  unfold cylCoupledIntegrand
  rw [integral_add h_free h_ac_int, h_ac_eq]

/-- From `freeCylinderBound_proof` (`PartII-b:T24`), for every `m > 8` and `Sig > 0` there is a
growth rate `K₀ > 0` such that under `BgRegime p d dm dp`, `p.ν ≤ 1`, `p.ageCut = Sig`,
`0 < δ ≤ 1`, and `TrainCloseM m p.train Sig δ`, there exists a free cylinder propagator `Sc`
satisfying `IsFreeCylPropagator m p Sc` and `‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))` on
`0 ≤ s ≤ t ≤ p.H`. -/
theorem exists_freeCylPropagator_of_trainCloseM
    {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.ageCut = Sig →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → TrainCloseM m p.train Sig δ →
        ∃ Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m),
          IsFreeCylPropagator m p Sc ∧
          ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
            ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s)) := by
  obtain ⟨Cm, C, b, hCm, hC, hb, hFree⟩ := freeCylinderBound_proof m hm Sig hSig
  set K₀ : ℝ := Cm + C + C
  have hK₀_pos : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨K₀, hK₀_pos, ?_⟩
  intro p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM
  have hTC : TrainClose p.train Sig δ := hTCM.toTrainClose (by linarith)
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have hRate_le : Cm * p.ν + C * δ + C * Real.exp (-b * p.c ^ 2) ≤ K₀ := by
    have hexp_le : Real.exp (-b * p.c ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ b * p.c ^ 2 := mul_nonneg hb.le (sq_nonneg _)
      linarith
    dsimp [K₀]
    nlinarith [hCm.le, hC.le, hν1, hδ1, hexp_le]
  have hFam : HasFreeCylFlowFamily m p K₀ := by
    intro s hs f hf
    have hs_Sig : s ≤ Sig / p.ν := by linarith [hs.2, hH_eq]
    obtain ⟨ω, hω, hω_uniq, _⟩ := hFree p d dm dp hbg δ hδ0.le hTC s s hs.1 le_rfl hs_Sig f hf
    refine ⟨ω, hω, hω_uniq, fun t ht => ?_⟩
    have ht_Sig : t ≤ Sig / p.ν := by linarith [ht.2, hH_eq]
    obtain ⟨ω_t, hω_t, _, hω_t_bd⟩ :=
      hFree p d dm dp hbg δ hδ0.le hTC s t hs.1 ht.1 ht_Sig f hf
    have h_ae : ω_t t =ᵐ[B0579.cellMeasure p.c m] ω t :=
      ae_cellMeasure_of_restrict_cell (hω_uniq ω_t hω_t t ht.1)
    rw [← eLpNorm_congr_ae h_ae]
    refine hω_t_bd.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right hRate_le (sub_nonneg.mpr ht.1)
  exact ⟨freeCylPropagator hFam, isFreeCylPropagator_freeCylPropagator hFam,
    fun s t hs hst ht => norm_freeCylPropagator_le hFam hs hst ht⟩

/-! ## 5. Mild Duhamel propagator package and reductions for `IsCoupledDuhamelPropagator` -/

/-- Package of the mild Volterra/Dyson properties of the coupled propagator `U` constructed from
`Sc` and `Ac` on `[0, p.H]` (SP 2076–2083, 2147–2155): evolution-family cocycle laws (`id_self`,
`comp_cocycle`), strong continuity in the final time (`strongCont`), Bochner interval-integrability
and mild Duhamel equation `U t s f = Sc t s f + ∫ r in s..t, Sc t r (Ac r (U r s f))`, and the
exponential bound `‖U t s‖ ≤ Real.exp ((K₀ + M_A) * (t - s))`. -/
structure IsMildDuhamelPropagator (m : ℝ) (p : Params) (K₀ M_A : ℝ)
    (Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
    (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
    (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) : Prop where
  id_self : ∀ s ∈ Icc 0 p.H, U s s = ContinuousLinearMap.id ℝ (Xmc p.c m)
  comp_cocycle : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ p.H →
    (U t r).comp (U r s) = U t s
  strongCont : ∀ s ∈ Icc 0 p.H, ∀ f : Xmc p.c m,
    ContinuousOn (fun t => U t s f) (Icc s p.H)
  duhamel_integrable : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
    IntervalIntegrable (fun r => Sc t r (Ac r (U r s f))) volume s t
  duhamel_eq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
    U t s f = Sc t s f + ∫ r in s..t, Sc t r (Ac r (U r s f))
  norm_le : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
    ‖U t s‖ ≤ Real.exp ((K₀ + M_A) * (t - s))

/-- Zero circulation of `U t s f` follows from `IsMildDuhamelPropagator`, zero circulation
preservation of `Sc`, and zero circulation of `Ac r g` by commuting `cellCircCLM` with the mild
Duhamel Bochner integral. -/
theorem IsMildDuhamelPropagator.zeroCirc_of_free_and_interaction
    {m : ℝ} (hm : 8 < m) {p : Params} {K₀ M_A : ℝ}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hMild : IsMildDuhamelPropagator m p K₀ M_A Sc Ac U)
    (hSc_circ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
      ∀ f : Xmc p.c m, HasZeroCirculationR p.c f → HasZeroCirculationR p.c (Sc t s f))
    (hAc_circ : ∀ r ∈ Icc 0 p.H, ∀ g : Xmc p.c m, HasZeroCirculationR p.c (Ac r g))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ p.H)
    {f : Xmc p.c m} (hf : HasZeroCirculationR p.c f) :
    HasZeroCirculationR p.c (U t s f) := by
  have hm_half : 1 / 2 < m := by linarith
  rw [hMild.duhamel_eq s t hs hst ht f]
  refine hasZeroCirculationR_add hm_half (hSc_circ s t hs hst ht f hf) ?_
  refine hasZeroCirculationR_intervalIntegral hm_half hst
    (hMild.duhamel_integrable s t hs hst ht f) fun r hr => ?_
  have hr_Icc : r ∈ Icc 0 p.H := ⟨hs.trans hr.1, hr.2.trans ht⟩
  exact hSc_circ r t hr_Icc.1 hr.2 ht (Ac r (U r s f)) (hAc_circ r hr_Icc (U r s f))

/-- Reduction of `IsCoupledPropagator.timeIntegrable` and `IsCoupledPropagator.weak` for a mild
Duhamel propagator `U` to a family of continuous linear functionals
`L_free : ℝ → (Xmc p.c m →L[ℝ] ℝ)` realizing `w ↦ ∫ x in B0579.cell p.c, cylFreeIntegrand p.train w r φ x`
and the triangle Fubini swap on `s ≤ τ ≤ r ≤ t`. -/
theorem IsMildDuhamelPropagator.weak_of_fubini
    {m : ℝ} {p : Params} {K₀ M_A : ℝ}
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hSc : IsFreeCylPropagator m p Sc)
    (hAc : ∀ r ∈ Icc 0 p.H, IsCylInteractionOp p.train m r (Ac r))
    (hMild : IsMildDuhamelPropagator m p K₀ M_A Sc Ac U)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest p.c φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ p.H) (f : Xmc p.c m)
    (L_free : ℝ → (Xmc p.c m →L[ℝ] ℝ))
    (hL_free : ∀ r ∈ Icc s t, ∀ w : Xmc p.c m,
      L_free r w = ∫ x in B0579.cell p.c, cylFreeIntegrand p.train w r φ x)
    (hAc_ti : IntervalIntegrable
      (fun r => cellTestCLM p.c m hφ (Ac r (U r s f))) volume s t)
    (hFub_ti : IntervalIntegrable
      (fun r => ∫ τ in s..r, L_free r (Sc r τ (Ac τ (U τ s f)))) volume s t)
    (hFub_eq :
      (∫ τ in s..t, ∫ r in τ..t, L_free r (Sc r τ (Ac τ (U τ s f)))) =
        ∫ r in s..t, ∫ τ in s..r, L_free r (Sc r τ (Ac τ (U τ s f)))) :
    IntervalIntegrable
      (fun r => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x) volume s t ∧
    (∫ x in B0579.cell p.c, (U t s f) x * φ x) =
      (∫ x in B0579.cell p.c, f x * φ x) +
        ∫ r in s..t, ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x := by
  let g : ℝ → Xmc p.c m := fun τ => Ac τ (U τ s f)
  -- 1. Express L_free r (U r s f) via the Duhamel equation at r ∈ Icc s t
  have hL_U_eq : ∀ r ∈ Icc s t,
      (∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x) =
        (∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) +
          (∫ τ in s..r, L_free r (Sc r τ (g τ))) +
          cellTestCLM p.c m hφ (g r) := by
    intro r hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hs.trans hr.1, hr.2.trans ht⟩
    have h_free_u : (∫ x in B0579.cell p.c, cylFreeIntegrand p.train (U r s f) r φ x) =
        (∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) +
          (∫ τ in s..r, L_free r (Sc r τ (g τ))) := by
      rw [← hL_free r hr (U r s f), hMild.duhamel_eq s r hs hr.1 hr_Icc.2 f, map_add,
        hL_free r hr (Sc r s f),
        (L_free r).intervalIntegral_comp_comm (hMild.duhamel_integrable s r hs hr.1 hr_Icc.2 f)]
    rw [(integrableOn_cylCoupledIntegrand_of_freeProp hSc hAc hφ hr_Icc (U r s f)).2, h_free_u]
  -- 2. IntervalIntegrable of the coupled integrand
  have hFree_ti : IntervalIntegrable
      (fun r => ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) volume s t :=
    hSc.timeIntegrable hφ hs hst ht f
  have hSum_ti : IntervalIntegrable
      (fun r =>
        (∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) +
          (∫ τ in s..r, L_free r (Sc r τ (g τ))) +
          cellTestCLM p.c m hφ (g r)) volume s t :=
    (hFree_ti.add hFub_ti).add hAc_ti
  have hCoupled_ti : IntervalIntegrable
      (fun r => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x) volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst] at hSum_ti ⊢
    refine hSum_ti.congr_fun (fun r hr => ?_) measurableSet_Ioc
    exact (hL_U_eq r ⟨hr.1.le, hr.2⟩).symm
  refine ⟨hCoupled_ti, ?_⟩
  -- 3. Weak equation at t
  have h_lhs : (∫ x in B0579.cell p.c, (U t s f) x * φ x) =
      cellTestCLM p.c m hφ (Sc t s f) +
        ∫ τ in s..t, cellTestCLM p.c m hφ (Sc t τ (g τ)) := by
    rw [← cellTestCLM_apply p.c m hφ (U t s f), hMild.duhamel_eq s t hs hst ht f, map_add,
      (cellTestCLM p.c m hφ).intervalIntegral_comp_comm (hMild.duhamel_integrable s t hs hst ht f)]
  have h_Sc_f : cellTestCLM p.c m hφ (Sc t s f) =
      (∫ x in B0579.cell p.c, f x * φ x) +
        ∫ r in s..t, ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x := by
    rw [cellTestCLM_apply, hSc.weak hφ hs hst ht f]
  have h_Sc_g_eq : ∀ τ ∈ Icc s t,
      cellTestCLM p.c m hφ (Sc t τ (g τ)) =
        cellTestCLM p.c m hφ (g τ) + ∫ r in τ..t, L_free r (Sc r τ (g τ)) := by
    intro τ hτ
    rw [cellTestCLM_apply, hSc.weak hφ (hs.trans hτ.1) hτ.2 ht (g τ), cellTestCLM_apply]
    congr 1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hτ.2] at hr
    exact (hL_free r ⟨hτ.1.trans hr.1.le, hr.2⟩ (Sc r τ (g τ))).symm
  have h_Sc_g_ti : IntervalIntegrable
      (fun τ => cellTestCLM p.c m hφ (Sc t τ (g τ))) volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact (cellTestCLM p.c m hφ).integrable_comp
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst).1
        (hMild.duhamel_integrable s t hs hst ht f))
  have h_inner_ti : IntervalIntegrable
      (fun τ => ∫ r in τ..t, L_free r (Sc r τ (g τ))) volume s t := by
    have h_sub := h_Sc_g_ti.sub hAc_ti
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst] at h_sub ⊢
    refine h_sub.congr_fun (fun τ hτ => ?_) measurableSet_Ioc
    change cellTestCLM p.c m hφ (Sc t τ (g τ)) - cellTestCLM p.c m hφ (g τ) =
      ∫ r in τ..t, L_free r (Sc r τ (g τ))
    rw [h_Sc_g_eq τ ⟨hτ.1.le, hτ.2⟩, add_sub_cancel_left]
  have h_int_Sc_g :
      (∫ τ in s..t, cellTestCLM p.c m hφ (Sc t τ (g τ))) =
        (∫ r in s..t, cellTestCLM p.c m hφ (g r)) +
          ∫ r in s..t, ∫ τ in s..r, L_free r (Sc r τ (g τ)) := by
    have h_congr : (∫ τ in s..t, cellTestCLM p.c m hφ (Sc t τ (g τ))) =
        ∫ τ in s..t, (cellTestCLM p.c m hφ (g τ) + ∫ r in τ..t, L_free r (Sc r τ (g τ))) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun τ hτ => ?_)
      rw [uIoc_of_le hst] at hτ
      exact h_Sc_g_eq τ ⟨hτ.1.le, hτ.2⟩
    rw [h_congr, intervalIntegral.integral_add hAc_ti h_inner_ti, hFub_eq]
  have h_rhs_eq :
      (∫ r in s..t, ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x) =
        ((∫ r in s..t, ∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r φ x) +
          ∫ r in s..t, ∫ τ in s..r, L_free r (Sc r τ (g τ))) +
          ∫ r in s..t, cellTestCLM p.c m hφ (g r) := by
    rw [← intervalIntegral.integral_add hFree_ti hFub_ti,
      ← intervalIntegral.integral_add (hFree_ti.add hFub_ti) hAc_ti]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hst] at hr
    exact hL_U_eq r ⟨hr.1.le, hr.2⟩
  rw [h_lhs, h_Sc_f, h_int_Sc_g, h_rhs_eq]
  ring

/-! ## 6. Leaf propositions (`PartII-b:F2/2/1` .. `PartII-b:F2/2/3`) and assembly -/

/-- **Leaf 1 (`PartII-b:F2/2/1`, mild Volterra/Dyson evolution family on `Xmc p.c m`,
SP 2076–2083, 2147–2155)**: given `m > 8`, `Sig > 0`, a regime point `BgRegime p d dm dp` with
`p.ν ≤ 1`, `p.ageCut = Sig`, `0 < δ ≤ 1`, `TrainCloseM m p.train Sig δ`, a free cylinder propagator
`Sc` (`IsFreeCylPropagator m p Sc`) bounded by `‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))` on
`0 ≤ s ≤ t ≤ p.H`, and a cylinder interaction family `Ac` (`IsCylInteractionOp p.train m s (Ac s)`
and `‖Ac s‖ ≤ M_A` on `Icc 0 p.H`), there exists a two-parameter continuous linear operator family
`U` satisfying `IsMildDuhamelPropagator m p K₀ M_A Sc Ac U`. -/
def MildDuhamelEvolutionStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig →
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.ageCut = Sig →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → TrainCloseM m p.train Sig δ →
    ∀ (K₀ : ℝ) (Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)), 0 < K₀ →
      IsFreeCylPropagator m p Sc →
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))) →
      ∀ (M_A : ℝ) (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)), 0 ≤ M_A →
        (∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s) ∧ ‖Ac s‖ ≤ M_A) →
        ∃ U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m),
          IsMildDuhamelPropagator m p K₀ M_A Sc Ac U

/-- **Leaf 2 (`PartII-b:F2/2/2`, zero-circulation preservation of `Sc` and zero circulation of `Ac`,
SP 2076–2083, 2117–2123)**: under `m > 8`, `Sig > 0`, `BgRegime p d dm dp`, `p.ν ≤ 1`,
`p.ageCut = Sig`, `0 < δ ≤ 1`, `TrainCloseM m p.train Sig δ`:
1. the free cylinder propagator `Sc` (`IsFreeCylPropagator m p Sc`) preserves
   `HasZeroCirculationR p.c` on `0 ≤ s ≤ t ≤ p.H`;
2. every cylinder interaction output `Ac r g` (`r ∈ Icc 0 p.H`, `IsCylInteractionOp p.train m r (Ac r)`)
   satisfies `HasZeroCirculationR p.c (Ac r g)`. -/
def FreeAndInteractionZeroCircStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig →
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.ageCut = Sig →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → TrainCloseM m p.train Sig δ →
    ∀ (Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)), IsFreeCylPropagator m p Sc →
    ∀ (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
      (∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s)) →
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
        ∀ f : Xmc p.c m, HasZeroCirculationR p.c f → HasZeroCirculationR p.c (Sc t s f)) ∧
      (∀ r ∈ Icc 0 p.H, ∀ g : Xmc p.c m, HasZeroCirculationR p.c (Ac r g))

/-- **Leaf 3 (`PartII-b:F2/2/3`, weak coupled cylinder vorticity equation for the mild Duhamel
propagator `U`, SP 2076–2083, 2147–2155)**: under `m > 8`, `Sig > 0`, `BgRegime p d dm dp`,
`p.ν ≤ 1`, `p.ageCut = Sig`, `0 < δ ≤ 1`, `TrainCloseM m p.train Sig δ`, any mild Duhamel
propagator `U` (`IsMildDuhamelPropagator m p K₀ M_A Sc Ac U`) satisfies `IsCoupledPropagator.timeIntegrable`
and `IsCoupledPropagator.weak` against every cylinder test function `B0579.IsCylTest p.c φ`. -/
def MildDuhamelWeakStep : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig →
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.ageCut = Sig →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → TrainCloseM m p.train Sig δ →
    ∀ (K₀ : ℝ) (Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)), 0 < K₀ →
      IsFreeCylPropagator m p Sc →
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))) →
    ∀ (M_A : ℝ) (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)), 0 ≤ M_A →
      (∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s) ∧ ‖Ac s‖ ≤ M_A) →
    ∀ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
      IsMildDuhamelPropagator m p K₀ M_A Sc Ac U →
      ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
        IntervalIntegrable
          (fun r => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x)
          volume s t ∧
        (∫ x in B0579.cell p.c, (U t s f) x * φ x) =
          (∫ x in B0579.cell p.c, f x * φ x) +
            ∫ r in s..t, ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x

/-- **Full assembly of `CoupledPropagatorStep` (`PartII-b:F2/2`)** from the proved free cylinder
propagator lift `exists_freeCylPropagator_of_trainCloseM` and the three leaves
`MildDuhamelEvolutionStep` (`PartII-b:F2/2/1`), `FreeAndInteractionZeroCircStep` (`PartII-b:F2/2/2`),
and `MildDuhamelWeakStep` (`PartII-b:F2/2/3`). -/
theorem coupledPropagatorStep_of
    (hMild : MildDuhamelEvolutionStep)
    (hCirc : FreeAndInteractionZeroCircStep)
    (hWeak : MildDuhamelWeakStep) :
    CoupledPropagatorStep := by
  intro m hm Sig hSig
  obtain ⟨K₀, hK₀, hFree⟩ := exists_freeCylPropagator_of_trainCloseM hm hSig
  refine ⟨K₀, hK₀, ?_⟩
  intro p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM M_A Ac hMA hAc
  obtain ⟨Sc, hSc, hSc_bd⟩ := hFree p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM
  have hAc_op : ∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s) :=
    fun s hs => (hAc s hs).1
  obtain ⟨U, hU_mild⟩ :=
    hMild m hm Sig hSig p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM K₀ Sc hK₀ hSc hSc_bd M_A Ac hMA hAc
  obtain ⟨hSc_circ, hAc_circ⟩ :=
    hCirc m hm Sig hSig p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM Sc hSc Ac hAc_op
  have hU_weak :=
    hWeak m hm Sig hSig p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM
      K₀ Sc hK₀ hSc hSc_bd M_A Ac hMA hAc U hU_mild
  have hU_coupled : IsCoupledPropagator m p U :=
    { id_self := hU_mild.id_self
      comp_cocycle := hU_mild.comp_cocycle
      strongCont := hU_mild.strongCont
      zeroCirc := fun s t hs hst ht f hf =>
        hU_mild.zeroCirc_of_free_and_interaction hm hSc_circ hAc_circ hs hst ht hf
      integrable := fun φ hφ s r hs hsr hr f =>
        (integrableOn_cylCoupledIntegrand_of_freeProp hSc hAc_op hφ ⟨hs.trans hsr, hr⟩ (U r s f)).1
      timeIntegrable := fun φ hφ s t hs hst ht f =>
        (hU_weak φ hφ s t hs hst ht f).1
      weak := fun φ hφ s t hs hst ht f =>
        (hU_weak φ hφ s t hs hst ht f).2 }
  refine ⟨Sc, U, ?_, fun s t hs hst ht => ⟨hSc_bd s t hs hst ht, hU_mild.norm_le s t hs hst ht⟩⟩
  exact
    { free_prop := hSc
      cyl_op := hAc_op
      coupled_prop := hU_coupled
      duhamel_integrable := hU_mild.duhamel_integrable
      duhamel_eq := hU_mild.duhamel_eq }

end UnforcedLeray.Short.IIb

end
