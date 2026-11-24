import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Phase space `Y_q`, phase tests and the phase pairing (INF25 T25.1)

Blueprint units B0005 (tex 136–147), B0411 (tex 7304–7337), B0412 (tex 5085–5091).

model

  `Y_q := Lp (Lp CVec3 q volume) q haarAddCircle`,

the Bochner space `L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` of tex 7313–7317. The Haar measure on
`AddCircle P` has total mass one, so `‖f‖_{Y_q}^q = P⁻¹ ∫₀ᴾ ‖f(τ)‖_q^q dτ`, which is the
period-averaged norm of tex 7315.

Distributional identities are pairings against smooth `P`-periodic tests `Φ(τ, y)` with
bounded `y`-support (scoping note INF15-INF17-INF25 §4, B25-1). The pairing is

  `⟪Φ, f⟫ = ∫ τ, ∫ y, ∑ᵢ Φᵢ(τ, y) fᵢ(τ)(y) dy dhaar(τ)`,

the bilinear distribution pairing, built from Mathlib's `ContinuousLinearMap.lpPairing`
twice (inner over `ℝ³`, outer over the circle), with the test placed in the Hölder-dual
Bochner space `Y_{q'}`, `q' = conjExp q`. Periodic tests restricted to one period are the
test functions of the circle times `ℝ³`, so these are the manuscript's distributional
identities. Junk values: `testElem` returns `0` for a function that is not a periodic
slice-continuous function; every theorem below assumes `IsPhaseTest`, so the junk branch is
never used in a statement.

Status: this file is infrastructure. It proves no manuscript unit, and Theorem A is not
proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

/-- Complex three-vectors `ℂ³` (tex 7314: `L^q(ℝ³; ℂ³)`). -/
abbrev CVec3 : Type := EuclideanSpace ℂ (Fin 3)

/-- The Hölder-conjugate exponent `q' = (1 - 1/q)⁻¹`; `conjExp 1 = ∞`, `conjExp ∞ = 1`. -/
def conjExp (q : ℝ≥0∞) : ℝ≥0∞ := (1 - q⁻¹)⁻¹

theorem conjExp_inv (q : ℝ≥0∞) : (conjExp q)⁻¹ = 1 - q⁻¹ := by
  simp [conjExp]

instance conjExp_fact {q : ℝ≥0∞} : Fact (1 ≤ conjExp q) :=
  ⟨by
    unfold conjExp
    exact ENNReal.one_le_inv.mpr tsub_le_self⟩

instance conjExp_holderConjugate {q : ℝ≥0∞} [hq : Fact (1 ≤ q)] :
    ENNReal.HolderConjugate (conjExp q) q := by
  rw [ENNReal.holderConjugate_iff, conjExp_inv]
  exact tsub_add_cancel_of_le (ENNReal.inv_le_one.mpr hq.out)

/-- The phase space `Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` with the normalised (probability) Haar
measure on the phase circle (decision D2; tex 7313–7317, 136–139, 5085–5091). -/
abbrev Yq (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] : Type :=
  Lp (Lp CVec3 q (volume : Measure Space)) q (AddCircle.haarAddCircle (T := P))

/-- The bilinear dot product `a · b = ∑ᵢ aᵢ bᵢ` on `ℂ³` (no complex conjugation). -/
def dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).smulRight
    (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ)

theorem dotL_apply (a b : CVec3) : dotL a b = ∑ i : Fin 3, a i * b i := by
  simp [dotL]

/-! ### Phase tests -/

/-- A phase test (scoping note INF25 T25.1, bypass B25-1): smooth on `ℝ × ℝ³`,
`P`-periodic in the phase `τ`, and vanishing for `‖y‖` beyond some radius. Generic in the
value space so that scalar tests (for the divergence) and vector tests share the API. -/
structure IsPhaseTest {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : ℝ) (Φ : ℝ × Space → F) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  periodic : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)
  bounded_support : ∃ R, ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0

/-- The slices of `Φ` lie in `L^r(ℝ³)` and depend continuously on the phase there. -/
structure SliceCont (r : ℝ≥0∞) [Fact (1 ≤ r)] (Φ : ℝ × Space → CVec3) : Prop where
  memLp : ∀ τ, MemLp (fun y => Φ (τ, y)) r volume
  continuous : Continuous fun τ => MemLp.toLp _ (memLp τ)

/-- `P`-periodic and slice-continuous into `L^r`: what is needed to place `Φ` in `Y_r`. -/
def IsSliceTest (P : ℝ) (r : ℝ≥0∞) [Fact (1 ≤ r)] (Φ : ℝ × Space → CVec3) : Prop :=
  (∀ τ y, Φ (τ + P, y) = Φ (τ, y)) ∧ SliceCont r Φ

section Slices

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- The slice map `τ ↦ Φ(τ, ·) ∈ L^r`. -/
def sliceMap {Φ : ℝ × Space → CVec3} (h : SliceCont r Φ) (τ : ℝ) : Lp CVec3 r (volume : Measure Space) :=
  MemLp.toLp _ (h.memLp τ)

theorem sliceMap_periodic {P : ℝ} {Φ : ℝ × Space → CVec3} (h : IsSliceTest P r Φ) :
    Function.Periodic (sliceMap h.2) P := by
  intro τ
  unfold sliceMap
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y => h.1 τ y)

variable {P : ℝ}

/-- The slice map descended to the phase circle, as a continuous map. -/
def circleSlice {Φ : ℝ × Space → CVec3} (h : IsSliceTest P r Φ) :
    C(AddCircle P, Lp CVec3 r (volume : Measure Space)) :=
  ⟨(sliceMap_periodic h).lift, continuous_coinduced_dom.mpr h.2.continuous⟩

theorem circleSlice_coe {Φ : ℝ × Space → CVec3} (h : IsSliceTest P r Φ) (τ : ℝ) :
    circleSlice h (τ : AddCircle P) = sliceMap h.2 τ := rfl

variable [Fact (0 < P)]

open Classical in
/-- The element of `Y_r` defined by a periodic slice-continuous function (junk `0`
otherwise; never used in a statement without the hypothesis). -/
def testElem (P : ℝ) [Fact (0 < P)] (r : ℝ≥0∞) [Fact (1 ≤ r)] (Φ : ℝ × Space → CVec3) :
    Yq P r :=
  if h : IsSliceTest P r Φ then
    ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r AddCircle.haarAddCircle ℂ (circleSlice h)
  else 0

theorem testElem_of {Φ : ℝ × Space → CVec3} (h : IsSliceTest P r Φ) :
    testElem P r Φ =
      ContinuousMap.toLp (E := Lp CVec3 r (volume : Measure Space)) r AddCircle.haarAddCircle ℂ
        (circleSlice h) := by
  simp [testElem, h]

theorem circleSlice_ext {Φ Ψ : ℝ × Space → CVec3} (hΦ : IsSliceTest P r Φ)
    (hΨ : IsSliceTest P r Ψ) (h : ∀ τ, sliceMap hΦ.2 τ = sliceMap hΨ.2 τ) :
    circleSlice hΦ = circleSlice hΨ := by
  ext1 τ
  induction τ using QuotientAddGroup.induction_on with
  | H t => exact h t

end Slices

/-! ### Closure properties of phase tests -/

namespace IsPhaseTest

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {P : ℝ} {Φ Ψ : ℝ × Space → F}

theorem continuous (hΦ : IsPhaseTest P Φ) : Continuous Φ := hΦ.smooth.continuous

theorem zero : IsPhaseTest P (0 : ℝ × Space → F) where
  smooth := contDiff_const
  periodic _ _ := rfl
  bounded_support := ⟨0, fun _ _ _ => rfl⟩

theorem add (hΦ : IsPhaseTest P Φ) (hΨ : IsPhaseTest P Ψ) : IsPhaseTest P (Φ + Ψ) where
  smooth := hΦ.smooth.add hΨ.smooth
  periodic τ y := by simp [hΦ.periodic, hΨ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    obtain ⟨S, hS⟩ := hΨ.bounded_support
    exact ⟨max R S, fun τ y hy => by
      simp [hR τ y (lt_of_le_of_lt (le_max_left _ _) hy),
        hS τ y (lt_of_le_of_lt (le_max_right _ _) hy)]⟩

/-- Post-composition with a continuous `ℝ`-linear map. -/
theorem clm_comp (hΦ : IsPhaseTest P Φ) (L : F →L[ℝ] G) : IsPhaseTest P (fun p => L (Φ p)) where
  smooth := L.contDiff.comp hΦ.smooth
  periodic τ y := by simp [hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

theorem neg (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (-Φ) where
  smooth := hΦ.smooth.neg
  periodic τ y := by simp [hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

theorem sub (hΦ : IsPhaseTest P Φ) (hΨ : IsPhaseTest P Ψ) : IsPhaseTest P (Φ - Ψ) := by
  simpa [sub_eq_add_neg] using hΦ.add hΨ.neg

theorem const_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (hΦ : IsPhaseTest P Φ) (c : 𝕜) : IsPhaseTest P (c • Φ) where
  smooth := hΦ.smooth.const_smul c
  periodic τ y := by simp [hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

theorem sum {ι : Type*} (s : Finset ι) {Φ : ι → ℝ × Space → F}
    (h : ∀ i ∈ s, IsPhaseTest P (Φ i)) : IsPhaseTest P (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsPhaseTest P (0 : ℝ × Space → F))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Multiplication by the spatial coordinate `y_j`. -/
theorem coord_smul (hΦ : IsPhaseTest P Φ) (j : Fin 3) :
    IsPhaseTest P (fun p => (p.2 j) • Φ p) where
  smooth := by
    have hc : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 j) :=
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
    exact hc.smul hΦ.smooth
  periodic τ y := by simp [hΦ.periodic]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

/-- A directional derivative of a phase test is a phase test. -/
theorem fderiv_apply (hΦ : IsPhaseTest P Φ) (v : ℝ × Space) :
    IsPhaseTest P (fun p => fderiv ℝ Φ p v) where
  smooth := (hΦ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  periodic τ y := by
    have hfun : (fun p : ℝ × Space => Φ (p + ((P : ℝ), (0 : Space)))) = Φ := by
      funext p
      obtain ⟨t, z⟩ := p
      simpa using hΦ.periodic t z
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (x := ((τ : ℝ), y))
      ((P : ℝ), (0 : Space))
    rw [hfun] at h
    have hp : ((τ, y) : ℝ × Space) + (P, 0) = (τ + P, y) := by simp
    rw [hp] at h
    rw [← h]
  bounded_support := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    have hev : Φ =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
      have hopen : IsOpen {p : ℝ × Space | R < ‖p.2‖} :=
        isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
      filter_upwards [hopen.mem_nhds (show R < ‖((τ, y) : ℝ × Space).2‖ from hy)] with p hp
      exact hR p.1 p.2 hp
    simp [hev.fderiv_eq]

theorem hasCompactSupport_slice (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    HasCompactSupport (fun y => Φ (τ, y)) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => hR τ y ?_
  simpa [mem_closedBall, dist_zero_right, not_le] using hy

theorem continuous_slice (hΦ : IsPhaseTest P Φ) (τ : ℝ) : Continuous (fun y => Φ (τ, y)) :=
  hΦ.continuous.comp (Continuous.prodMk_right τ)

end IsPhaseTest

/-- An `L^r` bound for a function vanishing off a closed ball. -/
theorem eLpNorm_le_of_ball {r : ℝ≥0∞} (g : Space → CVec3) (R η : ℝ)
    (hsupp : ∀ y, R < ‖y‖ → g y = 0) (hb : ∀ y, ‖y‖ ≤ R → ‖g y‖ ≤ η) :
    eLpNorm g r volume ≤
      volume (closedBall (0 : Space) R) ^ r.toReal⁻¹ * ENNReal.ofReal η := by
  have hind : (closedBall (0 : Space) R).indicator g = g := by
    funext y
    by_cases hy : y ∈ closedBall (0 : Space) R
    · simp [hy]
    · have : R < ‖y‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hy
      simp [hy, hsupp y this]
  rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (closedBall (0 : Space) R)) (p := r)
    (f := g) (C := η) (ae_restrict_of_forall_mem measurableSet_closedBall fun y hy =>
      hb y (by simpa [mem_closedBall, dist_zero_right] using hy))
  simpa [Measure.restrict_apply_univ] using h

/-- Phase tests are slice-continuous into every `L^r`, `1 ≤ r ≤ ∞`. -/
theorem IsPhaseTest.sliceCont {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] : SliceCont r Φ where
  memLp τ := (hΦ.continuous_slice τ).memLp_of_hasCompactSupport (hΦ.hasCompactSupport_slice τ)
  continuous := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    rw [Metric.continuous_iff]
    intro b ε hε
    set M : ℝ≥0∞ := volume (closedBall (0 : Space) R) ^ r.toReal⁻¹ with hMdef
    have hM : M ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        measure_closedBall_lt_top.ne
    set ε₁ : ℝ := ε / (M.toReal + 1) with hε₁def
    have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
    have hε₁ : 0 < ε₁ := by positivity
    let f : ℝ → closedBall (0 : Space) R → CVec3 := fun a y => Φ (a, y)
    have hf : Continuous ↿f :=
      hΦ.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hu := Continuous.tendstoUniformly f hf b
    rw [Metric.tendstoUniformly_iff] at hu
    have hev := hu ε₁ hε₁
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hδ'⟩ := hev
    refine ⟨δ, hδ, fun a ha => ?_⟩
    have hy := hδ' ha
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    have hbound : eLpNorm ((fun y => Φ (a, y)) - fun y => Φ (b, y)) r volume ≤
        M * ENNReal.ofReal ε₁ := by
      refine eLpNorm_le_of_ball _ R ε₁ (fun y hy' => by simp [hR a y hy', hR b y hy'])
        fun y hy' => ?_
      have h1 := hy ⟨y, by simpa [mem_closedBall, dist_zero_right] using hy'⟩
      rw [dist_comm, dist_eq_norm] at h1
      exact h1.le
    have hfin : M * ENNReal.ofReal ε₁ ≠ ⊤ := ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top
    calc (eLpNorm ((fun y => Φ (a, y)) - fun y => Φ (b, y)) r volume).toReal
        ≤ (M * ENNReal.ofReal ε₁).toReal := ENNReal.toReal_mono hfin hbound
      _ = M.toReal * ε₁ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε₁.le]
      _ < ε := by
        rw [hε₁def, mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

theorem IsPhaseTest.isSliceTest {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] : IsSliceTest P r Φ :=
  ⟨hΦ.periodic, hΦ.sliceCont r⟩

end UnforcedLeray.PhaseSpace
