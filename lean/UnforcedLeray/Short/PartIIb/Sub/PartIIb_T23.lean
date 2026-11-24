import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.Basic
import UnforcedLeray.Short.PartIIb.Sub.T22
import UnforcedLeray.Short.PartIIb.Sub.T22_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.Regular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.EtaCosh
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.DuhamelToPde
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N5
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.LocBase
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.LocStep
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.LocAssemble
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.JointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.Barrier
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.ExistsMax
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.Spatial
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.DriftC2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.TrainDriftSmoothBdd
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradLocalSub
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradZRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradZTerminal
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.LapLocalSub
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.LapZRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.LapZTerminal

/-!
# Part II-b, task `PartII-b:T23`: existence and uniqueness of the free cylinder flow `IsFreeCylFlow`

Source of record: `the November 2 reference manuscript`, lines 2074-2118.

## What is proved here (complete proofs, no sorry)

1. **`cylCoeff_of_buc`** and **`driftC2Bdd_of_buc`**: for any train `tr : B0140.TrainSol ν c` in the
   Gallay-Slijepcevic class `PartI.IsBUCTrain tr` (supplied by `BgRegime.train_buc`), the velocity
   `tr.v` satisfies `CylPDE.CylCoeff c T tr.v` and `DriftC2Bdd tr.v T V` on every `[0, T]`.
2. **`bwdSolve_of_buc`**: the backward transport-diffusion problem with terminal datum `ψ`
   (`B0579.IsCylTest c ψ`) at any age `t ≥ s ≥ 0` has a smooth `η`-decaying solution
   (`CylEtaSpatial c s t φ`) under `PartI.IsBUCTrain tr`.
3. **`free_cyl_unique : FreeCylUnique`** and **`free_cyl_unique_of_trainClose`**: uniqueness of weak
   solutions `IsFreeCylFlow m tr s f ω` for arbitrary `f` (not just smooth data), on all `[s, ∞)`
   under `PartI.IsBUCTrain tr` and on `[s, Σ/ν]` under `TrainClose tr Σ δ`, proved by duality using
   `cylWeakTimeDep`, `bwdSolve_of_buc` / `cylBackwardSolve`, `cyl_rhs_zero`, and `cylFundLemma`.
4. **`cylRegularExists_of_buc`**: for every smooth cylinder test datum `B0579.IsCylTest c f` and
   every `T ≥ s ≥ 0`, there is a classical `η`-decaying solution `IsRegularCylFlow c ν tr.v s T u`
   with `u s = f` (from `DuhamelExists`, `DuhamelToPde`, `EtaPowLeCosh`).
5. **`free_cyl_test_approx : FreeCylTestApprox`**: `B0579.IsCylTest c` is dense in
   `X_{m,c} = L²(B0579.cellMeasure c m)`, proved via Hilbert-space orthogonal complement
   (`Submodule.topologicalClosure_eq_top_iff`), the weight isometry `B0579.mulW`, and
   `B0579Check.eq_zero_of_forall_test`.
6. **`free_cyl_exists_unique_of`**: assembles `FreeCylExistsUnique` from `free_cyl_unique`,
   `free_cyl_test_approx`, and the two remaining existence leaves (`FreeCylSmoothExists`,
   `FreeCylApproxLimit`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-! ## Statements -/

/-- Uniqueness of the weak free cylinder flow `IsFreeCylFlow m tr s f ω` on `[s, ∞)` for a
BUC train `tr` and an arbitrary datum `f`. -/
def FreeCylUnique : Prop :=
  ∀ (m ν c : ℝ), 8 < m → 0 < ν → 0 < c →
    ∀ tr : B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s → ∀ f : B0579.Plane → ℝ,
    ∀ ω₁ ω₂ : ℝ → B0579.Plane → ℝ,
      IsFreeCylFlow m tr s f ω₁ → IsFreeCylFlow m tr s f ω₂ →
      ∀ t : ℝ, s ≤ t → ω₁ t =ᵐ[volume.restrict (B0579.cell c)] ω₂ t

/-- Density of smooth periodic cylinder test functions `B0579.IsCylTest c` in the weighted space
`X_{m,c} = L²(B0579.cellMeasure c m)`. -/
def FreeCylTestApprox : Prop :=
  ∀ (c m : ℝ), 0 < c → ∀ f : B0579.Plane → ℝ, MemLp f 2 (B0579.cellMeasure c m) →
    ∃ fn : ℕ → B0579.Plane → ℝ, (∀ n, B0579.IsCylTest c (fn n)) ∧
      Tendsto (fun n => eLpNorm (fn n - f) 2 (B0579.cellMeasure c m)) atTop (𝓝 0)

/-- **Leaf 1 for existence (`PartII-b:T23/1`)**: for a smooth cylinder test datum
`B0579.IsCylTest c f` and a BUC train `tr`, the global Picard/Duhamel solution on `[s, ∞)` is a
weak solution `IsFreeCylFlow m tr s f ω` whose restriction to every `[s, T]` is a regular flow
`IsRegularCylFlow c ν tr.v s T ω` with `ω s = f`. -/
def FreeCylSmoothExists : Prop :=
  ∀ (m ν c : ℝ), 8 < m → 0 < ν → 0 < c →
    ∀ tr : B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s → ∀ f : B0579.Plane → ℝ, B0579.IsCylTest c f →
      ∃ w : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s f w ∧ w s = f ∧
        ∀ T : ℝ, s ≤ T → IsRegularCylFlow c ν tr.v s T w

/-- **Leaf 2 for existence (`PartII-b:T23/2`)**: passage to the limit from smooth cylinder test
approximants `fn n → f` in `X_{m,c}` via the `X_{m,c}` energy bound for differences of regular
flows (`t22_dissipation` + `cyl_gronwall_of_rate` on `ωn n - ωn k`), yielding a weak solution `w`
with `ωn n t → w t` in `X_{m,c}` for every `t ≥ s`. -/
def FreeCylApproxLimit : Prop :=
  ∀ (m ν c : ℝ), 8 < m → 0 < ν → 0 < c →
    ∀ tr : B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s → ∀ f : B0579.Plane → ℝ, MemLp f 2 (B0579.cellMeasure c m) →
    ∀ (fn : ℕ → B0579.Plane → ℝ) (ωn : ℕ → ℝ → B0579.Plane → ℝ),
      (∀ n, B0579.IsCylTest c (fn n)) →
      Tendsto (fun n => eLpNorm (fn n - f) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) →
      (∀ n, IsFreeCylFlow m tr s (fn n) (ωn n) ∧ ωn n s = fn n ∧
        ∀ T : ℝ, s ≤ T → IsRegularCylFlow c ν tr.v s T (ωn n)) →
      ∃ w : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s f w ∧
        ∀ t : ℝ, s ≤ t →
          Tendsto (fun n => eLpNorm (ωn n t - w t) 2 (B0579.cellMeasure c m)) atTop (𝓝 0)

/-- **Target of `PartII-b:T23`** (SP 2100-2118): for every `f ∈ X_{m,c}` (`m > 8`) and BUC train
`tr`, there exists a weak solution `IsFreeCylFlow m tr s f w` and it is unique a.e. on the cell at
every age `t ≥ s`. -/
def FreeCylExistsUnique : Prop :=
  ∀ (m ν c : ℝ), 8 < m → 0 < ν → 0 < c →
    ∀ tr : B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s : ℝ, 0 ≤ s → ∀ f : B0579.Plane → ℝ, MemLp f 2 (B0579.cellMeasure c m) →
      (∃ w : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s f w) ∧
      ∀ ω₁ ω₂ : ℝ → B0579.Plane → ℝ,
        IsFreeCylFlow m tr s f ω₁ → IsFreeCylFlow m tr s f ω₂ →
        ∀ t : ℝ, s ≤ t → ω₁ t =ᵐ[volume.restrict (B0579.cell c)] ω₂ t

/-! ## BUC train regularity and backward solver -/

/-- A BUC train has `CylCoeff c T tr.v` on every `[0, T]`. -/
theorem cylCoeff_of_buc {ν c T : ℝ} {tr : B0140.TrainSol ν c}
    (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T) :
    CylPDE.CylCoeff c T tr.v := by
  obtain ⟨hs, hc0, hd0⟩ := CylPDE.tcRegular ν c tr T hT
  obtain ⟨M0, hM0⟩ := hbu.sup_bound hT
  obtain ⟨M1, hM1⟩ := hbu.deriv_bound hT 1
  refine ⟨hs, hc0, hd0, fun σ hσ x => tr.isTrain.periodic_v σ hσ.1 x, ⟨M0, hM0⟩, ⟨M1, ?_⟩⟩
  intro σ hσ x
  have h := hM1 σ hσ x
  rwa [norm_iteratedFDeriv_one] at h

/-- A BUC train satisfies `DriftC2Bdd tr.v T V` on every `[0, T]`. -/
theorem driftC2Bdd_of_buc {ν c T : ℝ} {tr : B0140.TrainSol ν c}
    (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T) :
    ∃ V : ℝ, 0 ≤ V ∧ DriftC2Bdd tr.v T V := by
  obtain ⟨M0, h0⟩ := hbu.deriv_bound hT 0
  obtain ⟨M1, h1⟩ := hbu.deriv_bound hT 1
  obtain ⟨M2, h2⟩ := hbu.deriv_bound hT 2
  refine ⟨|M0| + |M1| + |M2|, by positivity, fun r hr x i => ?_⟩
  have hvd : ContDiff ℝ ∞ (tr.v r) := by
    have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun z _ => ⟨mem_Ici.2 hr.1, mem_univ z⟩)
    exact contDiffOn_univ.1 h
  have hv2 : ContDiff ℝ 2 (tr.v r) := hvd.of_le (WithTop.coe_le_coe.2 le_top)
  have k0 := h0 r hr x
  have k1 := h1 r hr x
  have k2 := h2 r hr x
  have a0 := le_abs_self M0
  have a1 := le_abs_self M1
  have a2 := le_abs_self M2
  have n0 := abs_nonneg M0
  have n1 := abs_nonneg M1
  have n2 := abs_nonneg M2
  refine ⟨?_, fun j => ?_, fun j k => ?_⟩
  · have := (pd_bridge (tr.v r) hv2 x i 0 0).1
    linarith
  · have := (pd_bridge (tr.v r) hv2 x i j 0).2.1
    linarith
  · have := (pd_bridge (tr.v r) hv2 x i j k).2.2
    linarith

/-- Classical regular forward solution on `[s, T]` for a BUC train and cylinder test datum. -/
theorem cylRegularExists_of_buc {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) {f : B0579.Plane → ℝ} (hf : B0579.IsCylTest c f) :
    ∃ u : ℝ → B0579.Plane → ℝ, IsRegularCylFlow c ν tr.v s T u ∧ u s = f := by
  have hT : 0 ≤ T := le_trans hs hsT
  have hcoef := cylCoeff_of_buc hbu hT
  have hA := CylPDE.duhamelExists_of_parts CylPDE.picardIterates CylPDE.picardLimit
  obtain ⟨u, hu⟩ := hA c ν s T tr.v hc hν hs hsT hcoef f hf
  obtain ⟨B, hB'⟩ := hu.cls
  have hSle : ∀ (g : B0579.Plane → ℝ) (x : B0579.Plane),
      |g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x| ≤ CylPDE.W2 g x := by
    intro g x
    unfold CylPDE.W2 lapP
    have h1 := abs_add_le (B0579.pd 0 (B0579.pd 0 g) x) (B0579.pd 1 (B0579.pd 1 g) x)
    have := abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x)
    have := abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x)
    linarith
  have hdec : ∀ N : ℝ, ∃ C : ℝ, ∀ σ ∈ Icc s T, ∀ x : B0579.Plane,
      (|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
        (1 + x.2 ^ 2) ^ N ≤ C := by
    intro N
    obtain ⟨C0, hC0⟩ := CylPDE.etaPowLeCosh N
    refine ⟨C0 * B, fun σ hσ x => ?_⟩
    have hC00 : 0 ≤ C0 := by
      have h0 := hC0 0
      simp only [Real.cosh_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero, Real.one_rpow] at h0
      exact le_trans zero_le_one h0
    have hS : 0 ≤ |u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x| := by
      positivity
    calc (|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
          (1 + x.2 ^ 2) ^ N
        ≤ (|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
            (C0 * Real.cosh x.2) := mul_le_mul_of_nonneg_left (hC0 x.2) hS
      _ = C0 * ((|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
            Real.cosh x.2) := by ring
      _ ≤ C0 * (CylPDE.W2 (u σ) x * Real.cosh x.2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hSle _ _) (Real.cosh_pos _).le) hC00
      _ ≤ C0 * B := mul_le_mul_of_nonneg_left (hB'.bound σ hσ x) hC00
  refine ⟨u, ⟨hB'.cont0, fun σ hσ => ⟨hB'.c2 σ hσ, hB'.periodic σ hσ, fun N => ?_⟩, hdec,
    CylPDE.duhamelToPde c ν s T tr.v hc hν hs hsT hcoef f hf u hu⟩, ?_⟩
  · obtain ⟨C, hC⟩ := hdec N
    exact ⟨C, fun x => hC σ hσ x⟩
  · funext x
    have h := hu.duhamel s ⟨le_rfl, hsT⟩ x
    simp only [CylPDE.duhamelMap, CylPDE.duhamelConv, CylPDE.heatSG, sub_self, mul_zero, le_refl,
      ↓reduceIte, intervalIntegral.integral_same, sub_zero] at h
    exact h

/-- Existence of a bounded classical backward solution on `[s, t]` for a BUC train. -/
theorem bwdSol_of_buc {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∃ φ : ℝ → B0579.Plane → ℝ, BwdSol ν c s t tr.v ψ φ := by
  have ht : 0 ≤ t := le_trans hs hst
  have hT : 0 ≤ t - s := sub_nonneg.2 hst
  set w := BwdRoute.revDrift t tr.v with hw_def
  have hcoef : CylPDE.CylCoeff c (t - s) w :=
    BwdRoute.cylCoeff_revDrift (cylCoeff_of_buc hbu ht) hs hst le_rfl
  have hws := BwdRoute.revDrift_smooth tr (t := t) hs
  have hB := CylPDE.duhamelExists_of_parts CylPDE.picardIterates CylPDE.picardLimit
  obtain ⟨u, hu⟩ := hB c ν 0 (t - s) w hc hν le_rfl hT hcoef ψ hψ
  have hpde : BwdRoute.FwdPde ν (t - s) w u :=
    CylPDE.duhamelToPde c ν 0 (t - s) w hc hν le_rfl hT hcoef ψ hψ u hu
  have hd : BwdRoute.FwdData c ν (t - s) w ψ u := ⟨hc, hν, hT, hcoef, hws, hψ, hu, hpde⟩
  have hsm := BwdRoute.fwdJointSmooth ν (t - s) w u hT hws
    (BwdRoute.spSmooth_of locBase BwdRoute.locStep BwdRoute.locAssemble hd) hpde
  obtain ⟨B, hB'⟩ := hu.cls
  have hmem : ∀ r ∈ Icc s t, t - r ∈ Icc (0 : ℝ) (t - s) := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨fun r => u (t - r), ?_, ?_, ?_, ⟨B, ?_⟩, ?_⟩
  · show u (t - t) = ψ
    rw [sub_self]
    funext x
    have h := hu.duhamel 0 ⟨le_rfl, hT⟩ x
    simp only [CylPDE.duhamelMap, CylPDE.duhamelConv, CylPDE.heatSG, sub_self, mul_zero, le_refl,
      ↓reduceIte, intervalIntegral.integral_same, sub_zero] at h
    exact h
  · have hmaps : MapsTo (fun z : ℝ × B0579.Plane => (t - z.1, z.2)) (Icc s t ×ˢ univ)
        (Icc 0 (t - s) ×ˢ univ) := fun z hz => ⟨hmem z.1 hz.1, mem_univ _⟩
    exact hsm.comp (BwdRoute.contDiff_rev t).contDiffOn hmaps
  · intro r hr x
    exact hB'.periodic (t - r) (hmem r hr) x
  · intro r hr x
    have hb := hB'.bound (t - r) (hmem r hr) x
    have h0 : 0 ≤ CylPDE.W2 (u (t - r)) x := le_trans (abs_nonneg _) (BwdRoute.abs_le_W2 _ _)
    calc |u (t - r) x| ≤ CylPDE.W2 (u (t - r)) x := BwdRoute.abs_le_W2 _ _
      _ ≤ CylPDE.W2 (u (t - r)) x * Real.cosh x.2 := le_mul_of_one_le_right h0 (Real.one_le_cosh _)
      _ ≤ B := hb
  · intro r hr x
    have hσ : t - r ∈ Ioo (0 : ℝ) (t - s) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h1 := (hpde (t - r) (Ioo_subset_Icc_self hσ) x).hasDerivAt (Icc_mem_nhds hσ.1 hσ.2)
    have h2 : HasDerivAt (fun r' : ℝ => t - r') (-1) r := (hasDerivAt_id' r).const_sub t
    have h3 := HasDerivAt.comp r h1 h2
    have e : ∀ i : Fin 2, w (t - r) x i = -tr.v r x i := fun i => by
      simp only [hw_def, BwdRoute.revDrift, sub_sub_cancel, PiLp.neg_apply]
    have h4 : (ν * lapP (u (t - r)) x - (w (t - r) x 0 * B0579.pd 0 (u (t - r)) x +
        w (t - r) x 1 * B0579.pd 1 (u (t - r)) x)) * -1 =
        -(ν * lapP (u (t - r)) x + (tr.v r x 0 * B0579.pd 0 (u (t - r)) x +
          tr.v r x 1 * B0579.pd 1 (u (t - r)) x)) := by
      rw [e 0, e 1]
      ring
    exact h3.congr_deriv h4

/-- Backward solver producing a `CylEtaSpatial` solution on `[s, t]` for a BUC train. -/
theorem bwdSolve_of_buc {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    ∃ φ : ℝ → B0579.Plane → ℝ, φ t = ψ ∧ CylEtaSpatial c s t φ ∧
      ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
        HasDerivAt (fun r' => φ r' x)
          (-(ν * lapP (φ r) x + (tr.v r x 0 * B0579.pd 0 (φ r) x +
            tr.v r x 1 * B0579.pd 1 (φ r) x))) r := by
  obtain ⟨φ, hφ⟩ := bwdSol_of_buc hν hc hbu hs hst hψ
  set Sg : ℝ := ν * (t + 1) with hSg_def
  have ht0 : 0 ≤ t := le_trans hs hst
  have hSg : 0 < Sg := mul_pos hν (by linarith)
  have htSg : t ≤ Sg / ν := by
    rw [hSg_def, mul_div_cancel_left₀ _ hν.ne']
    linarith
  have hTSg : 0 ≤ Sg / ν := le_trans ht0 htSg
  obtain ⟨V, hV0, hV2⟩ := driftC2Bdd_of_buc (tr := tr) hbu hTSg
  have hDS := trainDriftSmoothBdd Sg ν c V tr hV2 s t hs htSg
  have hMP := bwdMaxPrincipleSub_of mpExistsMax mpSpatial
  -- WeightedSup via localized_decay or bwdMaxPrinciple + bwdBarrier
  have hWS : WeightedSup s t φ := by
    intro N
    set N' : ℝ := max N 0
    obtain ⟨K1, K2, hK⟩ := bwdBarrier ν V N' hν hV0
    obtain ⟨M, hM⟩ := hφ.bounded
    have hMt : ∀ x, |ψ x| ≤ M := fun x => by simpa [hφ.terminal] using hM t ⟨hst, le_rfl⟩ x
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMt (0, 0))
    obtain ⟨R, hR⟩ := hψ.band
    set A : ℝ := M * (1 + R ^ 2) ^ N' with hA
    have hA0 : 0 ≤ A := by positivity
    have hbdd : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |tr.v r x 0| ≤ V ∧ |tr.v r x 1| ≤ V :=
      fun r hr x => ⟨(hDS.2 r hr x 0).1, (hDS.2 r hr x 1).1⟩
    have key : ∀ ε : ℝ, 0 < ε → ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
        |φ r x| ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') +
          ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
      intro ε hε
      refine bwdMaxPrinciple ν c s t (fun r x => tr.v r x 0) (fun r x => tr.v r x 1) φ _ hν hc hst
        (hφ.smooth.of_le (WithTop.coe_le_coe.2 le_top)) hφ.periodic ⟨M, hM⟩ hφ.pde
        (hK c s t _ _ hbdd A ε hA0 hε.le) ?_ ?_
      · intro M'
        set m0 : ℝ := Real.exp (-(|K2| * (t - s)))
        have hm0 : 0 < m0 := Real.exp_pos _
        have hεm : 0 < ε * m0 := mul_pos hε hm0
        refine ⟨|M'| / (ε * m0), fun r hr x hx => ?_⟩
        have hexp : m0 ≤ Real.exp (K2 * (t - r)) := by
          apply Real.exp_le_exp.2
          have h1 : -|K2| ≤ K2 := neg_abs_le K2
          have h2 : K2 ≤ |K2| := le_abs_self K2
          have h3 : 0 ≤ t - r := by linarith [hr.2]
          have h4 : t - r ≤ t - s := by linarith [hr.1]
          nlinarith [mul_nonneg (sub_nonneg.2 h2) h3, mul_nonneg (abs_nonneg K2) (sub_nonneg.2 h4),
            mul_nonneg (sub_nonneg.2 h1) h3]
        have hsq : |x.2| ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
          rw [← Real.sqrt_eq_rpow]
          calc |x.2| = Real.sqrt (x.2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
        have hg : 0 ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') := by positivity
        have h5 : |M'| / (ε * m0) ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := le_trans hx hsq
        have h6 : |M'| ≤ ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
          have : |M'| ≤ (ε * m0) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
            have := (div_le_iff₀ hεm).1 h5
            linarith
          refine le_trans this ?_
          have hp : 0 ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by positivity
          have : ε * m0 ≤ ε * Real.exp (K2 * (t - r)) := by gcongr
          exact mul_le_mul_of_nonneg_right this hp
        show M' ≤ _
        linarith [le_abs_self M']
      · intro x
        have e1 : Real.exp (K1 * (t - t)) = 1 := by simp
        have e2 : Real.exp (K2 * (t - t)) = 1 := by simp
        show |φ t x| ≤ A * Real.exp (K1 * (t - t)) * (1 + x.2 ^ 2) ^ (-N') +
          ε * Real.exp (K2 * (t - t)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2)
        rw [e1, e2, hφ.terminal]
        have hp : 0 ≤ ε * 1 * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by positivity
        by_cases hx : R < |x.2|
        · rw [hR x hx]; simp only [abs_zero]; positivity
        · rw [not_lt] at hx
          have hpos : 0 < 1 + x.2 ^ 2 := by positivity
          have hle : (1 + R ^ 2) ^ (-N') ≤ (1 + x.2 ^ 2) ^ (-N') :=
            Real.rpow_le_rpow_of_nonpos hpos
              (by nlinarith [sq_abs x.2, abs_nonneg x.2,
                mul_nonneg (sub_nonneg.2 hx) (add_nonneg (abs_nonneg x.2) (le_trans (abs_nonneg _) hx))])
              (by linarith [le_max_right N 0])
          have hRpos : 0 < (1 + R ^ 2) := by positivity
          have hid : (1 + R ^ 2) ^ N' * (1 + R ^ 2) ^ (-N') = 1 := by
            rw [← Real.rpow_add hRpos]; simp
          calc |ψ x| ≤ M := hMt x
            _ = A * (1 + R ^ 2) ^ (-N') := by rw [hA, mul_assoc, hid, mul_one]
            _ ≤ A * (1 + x.2 ^ 2) ^ (-N') := by gcongr
            _ ≤ _ := by linarith
    refine ⟨A * Real.exp (|K1| * (t - s)), fun r hr x => ?_⟩
    have hpos : 0 < 1 + x.2 ^ 2 := by positivity
    have hb : |φ r x| ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') := by
      set Phi : ℝ := Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) with hPhi
      refine le_of_forall_pos_le_add fun e he => ?_
      have := key (e / (Phi + 1)) (by positivity) r hr x
      have h2 : e / (Phi + 1) * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) ≤ e := by
        rw [mul_assoc, ← hPhi, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [ show 0 ≤ Phi by positivity ]
      linarith
    have hN : (1 + x.2 ^ 2) ^ N ≤ (1 + x.2 ^ 2) ^ N' :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x.2]) (le_max_left _ _)
    have hid : (1 + x.2 ^ 2) ^ (-N') * (1 + x.2 ^ 2) ^ N' = 1 := by
      rw [← Real.rpow_add hpos]; simp
    have hK1 : Real.exp (K1 * (t - r)) ≤ Real.exp (|K1| * (t - s)) := by
      apply Real.exp_le_exp.2
      have h3 : 0 ≤ t - r := by linarith [hr.2]
      have h4 : t - r ≤ t - s := by linarith [hr.1]
      nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self K1)) h3,
        mul_nonneg (abs_nonneg K1) (sub_nonneg.2 h4)]
    calc |φ r x| * (1 + x.2 ^ 2) ^ N ≤ |φ r x| * (1 + x.2 ^ 2) ^ N' := by gcongr
      _ ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') * (1 + x.2 ^ 2) ^ N' := by gcongr
      _ = A * Real.exp (K1 * (t - r)) := by rw [mul_assoc, hid, mul_one]
      _ ≤ A * Real.exp (|K1| * (t - s)) := by gcongr
  -- Gradient decay via localized_decay
  obtain ⟨lam, hlam0, hsubG⟩ := gradLocalSub ν c s t V tr.v ψ φ hν hV0 hDS hφ
  obtain ⟨MG, RG, hMRG⟩ := gradZTerminal ν c s t tr.v ψ φ hc hψ hφ lam
  have hregG := gradZRegular ν c s t tr.v ψ φ hc hφ lam
  have hdecG := localized_decay hMP bwdBarrier ν c s t V (fun r x => tr.v r x 0)
    (fun r x => tr.v r x 1) hν hc hst hV0
    (fun r hr x => ⟨(hDS.2 r hr x 0).1, (hDS.2 r hr x 1).1⟩)
    (fun η0 => gradZ lam η0 φ) (fun η0 => (hregG η0).1) (fun η0 => (hregG η0).2.1)
    (fun η0 => (hregG η0).2.2.1) (fun η0 => (hregG η0).2.2.2) hsubG MG RG hMRG (gradSq φ)
    (fun r _ x => by
      have h1 : cutζ x.2 x = 1 := by simp [cutζ, cutProps.2.1]
      have h2 : 0 ≤ lam * (φ r x * φ r x) := mul_nonneg hlam0 (mul_self_nonneg _)
      show gradSq φ r x ≤ cutζ x.2 x * gradSq φ r x + lam * (φ r x * φ r x)
      rw [h1, one_mul]; linarith)
  have hGrad : ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
      (|B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x|) * (1 + x.2 ^ 2) ^ N ≤ C := by
    intro N
    obtain ⟨C, hC⟩ := hdecG (2 * N)
    refine ⟨1 + 2 * C, fun r hr x => ?_⟩
    have hw2 : (1 + x.2 ^ 2) ^ (2 * N) = ((1 + x.2 ^ 2) ^ N) ^ 2 := by
      rw [show (2 : ℝ) * N = N * 2 by ring, Real.rpow_mul (by positivity), Real.rpow_two]
    have hCx := hC r hr x
    rw [hw2] at hCx
    simp only [gradSq] at hCx
    generalize B0579.pd 0 (φ r) x = p0 at hCx ⊢
    generalize B0579.pd 1 (φ r) x = p1 at hCx ⊢
    generalize (1 + x.2 ^ 2) ^ N = w at hCx ⊢
    have ha : (|p0| + |p1|) ^ 2 ≤ 2 * (p0 * p0 + p1 * p1) := by
      nlinarith [sq_nonneg (|p0| - |p1|), sq_abs p0, sq_abs p1]
    have hq : ((|p0| + |p1|) * w) ^ 2 ≤ 2 * ((p0 * p0 + p1 * p1) * w ^ 2) := by
      rw [mul_pow]; nlinarith [sq_nonneg w]
    nlinarith [sq_nonneg ((|p0| + |p1|) * w - 1), sq_nonneg ((|p0| + |p1|) * w)]
  -- Laplacian decay via localized_decay
  have hgb : ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, gradSq φ r x ≤ C := by
    obtain ⟨C0, hC0⟩ := hGrad 0
    refine ⟨C0 ^ 2, fun r hr x => ?_⟩
    have h := hC0 r hr x
    simp only [Real.rpow_zero, mul_one] at h
    simp only [gradSq]
    generalize B0579.pd 0 (φ r) x = p0 at h ⊢
    generalize B0579.pd 1 (φ r) x = p1 at h ⊢
    have h1 := abs_nonneg p0
    have h2 := abs_nonneg p1
    nlinarith [sq_abs p0, sq_abs p1, mul_nonneg h1 h2,
      mul_le_mul h h (add_nonneg h1 h2) (le_trans (add_nonneg h1 h2) h)]
  obtain ⟨mu, kap, hmu0, hkap0, hsubL⟩ := lapLocalSub ν c s t V tr.v ψ φ hν hV0 hDS hφ
  obtain ⟨ML, RL, hMRL⟩ := lapZTerminal ν c s t tr.v ψ φ hc hψ hφ mu kap
  have hregL := lapZRegular ν c s t tr.v ψ φ hc hφ hgb mu kap hmu0
  have hdecL := localized_decay hMP bwdBarrier ν c s t V (fun r x => tr.v r x 0)
    (fun r x => tr.v r x 1) hν hc hst hV0
    (fun r hr x => ⟨(hDS.2 r hr x 0).1, (hDS.2 r hr x 1).1⟩)
    (fun η0 => lapZ mu kap η0 φ) (fun η0 => (hregL η0).1) (fun η0 => (hregL η0).2.1)
    (fun η0 => (hregL η0).2.2.1) (fun η0 => (hregL η0).2.2.2) hsubL ML RL hMRL (lapSq φ)
    (fun r _ x => by
      have h1 : cutζ x.2 x = 1 := by simp [cutζ, cutProps.2.1]
      have h2 : 0 ≤ mu * gradSq φ r x :=
        mul_nonneg hmu0 (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      have h3 : 0 ≤ kap * (φ r x * φ r x) := mul_nonneg hkap0 (mul_self_nonneg _)
      show lapSq φ r x ≤ cutζ x.2 x * lapSq φ r x + (mu * gradSq φ r x + kap * (φ r x * φ r x))
      rw [h1, one_mul]; linarith)
  refine ⟨φ, hφ.terminal, ⟨hφ.smooth, hφ.periodic, fun N => ?_⟩, hφ.pde⟩
  obtain ⟨C0, hC0⟩ := hWS N
  obtain ⟨C1, hC1⟩ := hGrad N
  obtain ⟨C2, hC2⟩ := hdecL (2 * N)
  refine ⟨C0 + C1 + (1 + C2), fun r hr x => ?_⟩
  have hw2 : (1 + x.2 ^ 2) ^ (2 * N) = ((1 + x.2 ^ 2) ^ N) ^ 2 := by
    rw [show (2 : ℝ) * N = N * 2 by ring, Real.rpow_mul (by positivity), Real.rpow_two]
  have hCx := hC2 r hr x
  rw [hw2] at hCx
  simp only [lapSq] at hCx
  have hL : |lapP (φ r) x| * (1 + x.2 ^ 2) ^ N ≤ 1 + C2 := by
    generalize lapP (φ r) x = l at hCx ⊢
    generalize (1 + x.2 ^ 2) ^ N = w at hCx ⊢
    have hq : (|l| * w) ^ 2 = l * l * w ^ 2 := by rw [mul_pow, sq_abs]; ring
    nlinarith [sq_nonneg (|l| * w - 1), sq_nonneg (|l| * w)]
  linarith [hC0 r hr x, hC1 r hr x, hL]

/-! ## Uniqueness of weak solutions (`FreeCylUnique`) -/

/-- **Uniqueness of `IsFreeCylFlow` under `PartI.IsBUCTrain`** (valid at every age `t ≥ s` and for
every datum `f`). -/
theorem free_cyl_unique : FreeCylUnique := by
  intro m ν c hm hν hc tr hbu s hs f ω₁ ω₂ hω₁ hω₂ t hst
  have ht0 : 0 ≤ t := le_trans hs hst
  obtain ⟨V, _, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu ht0
  have hMr : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ 2 * V := by
    intro r hr x
    have h0 := (hV r ⟨le_trans hs hr.1, hr.2⟩ x 0).1
    have h1 := (hV r ⟨le_trans hs hr.1, hr.2⟩ x 1).1
    linarith
  refine cylFundLemma c m hc (by linarith) (ω₁ t) (ω₂ t) (hω₁.memX t hst) (hω₂.memX t hst) ?_
  intro ψ hψ
  obtain ⟨φ, hφt, hφ0, hPDE⟩ := bwdSolve_of_buc hν hc hbu hs hst hψ
  have hφ : CylEtaTest c s t φ := hφ0.toCylEtaTest hν.le tr.v hMr hPDE
  have k1 := cylWeakTimeDep m hm ν c tr s f ω₁ hc hω₁ t φ hst hφ ⟨2 * V, hMr⟩
  have k2 := cylWeakTimeDep m hm ν c tr s f ω₂ hc hω₂ t φ hst hφ ⟨2 * V, hMr⟩
  rw [cyl_rhs_zero hst ω₁ φ tr.v _ hPDE, hφt] at k1
  rw [cyl_rhs_zero hst ω₂ φ tr.v _ hPDE, hφt] at k2
  linarith

/-- **Uniqueness of `IsFreeCylFlow` on `[s, Σ/ν]` under `TrainClose`** (for any datum `f`). -/
theorem free_cyl_unique_of_trainClose {m Sg ν c δ : ℝ} (hm : 8 < m) (hSg : 0 < Sg)
    (hν : 0 < ν) (hc : 0 < c) (hδ : 0 ≤ δ) {tr : B0140.TrainSol ν c} (htr : TrainClose tr Sg δ)
    {s : ℝ} (hs : 0 ≤ s) {f : B0579.Plane → ℝ} {ω₁ ω₂ : ℝ → B0579.Plane → ℝ}
    (hω₁ : IsFreeCylFlow m tr s f ω₁) (hω₂ : IsFreeCylFlow m tr s f ω₂)
    {t : ℝ} (hst : s ≤ t) (ht : t ≤ Sg / ν) :
    ω₁ t =ᵐ[volume.restrict (B0579.cell c)] ω₂ t := by
  obtain ⟨M, hM⟩ := cylTrainBound Sg ν c δ hSg hν hc hδ tr htr
  have hMr : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M :=
    fun r hr x => hM r (le_trans hs hr.1) (le_trans hr.2 ht) x
  refine cylFundLemma c m hc (by linarith) (ω₁ t) (ω₂ t) (hω₁.memX t hst) (hω₂.memX t hst) ?_
  intro ψ hψ
  obtain ⟨φ, hφt, hφ0, hPDE⟩ := cylBackwardSolve Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ
  have hφ : CylEtaTest c s t φ := hφ0.toCylEtaTest hν.le tr.v hMr hPDE
  have k1 := cylWeakTimeDep m hm ν c tr s f ω₁ hc hω₁ t φ hst hφ ⟨M, hMr⟩
  have k2 := cylWeakTimeDep m hm ν c tr s f ω₂ hc hω₂ t φ hst hφ ⟨M, hMr⟩
  rw [cyl_rhs_zero hst ω₁ φ tr.v _ hPDE, hφt] at k1
  rw [cyl_rhs_zero hst ω₂ φ tr.v _ hPDE, hφt] at k2
  linarith

/-! ## Density of smooth cylinder tests in `X_{m,c}` (`FreeCylTestApprox`) -/

private theorem isCylTest_zero (c : ℝ) : B0579.IsCylTest c (fun _ => 0) where
  smooth := contDiff_const
  periodic _ := rfl
  band := ⟨0, fun _ _ => rfl⟩

private theorem isCylTest_add {c : ℝ} {φ ψ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun x => φ x + ψ x) where
  smooth := hφ.smooth.add hψ.smooth
  periodic x := by simp only [hφ.periodic x, hψ.periodic x]
  band := by
    obtain ⟨R₁, hR₁⟩ := hφ.band
    obtain ⟨R₂, hR₂⟩ := hψ.band
    refine ⟨max R₁ R₂, fun x hx => ?_⟩
    rw [hR₁ x (lt_of_le_of_lt (le_max_left _ _) hx),
      hR₂ x (lt_of_le_of_lt (le_max_right _ _) hx), add_zero]

private theorem isCylTest_smul {c : ℝ} (a : ℝ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) : B0579.IsCylTest c (fun x => a * φ x) where
  smooth := contDiff_const.mul hφ.smooth
  periodic x := by simp only [hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by rw [hR x hx, mul_zero]⟩

/-- The submodule of `X c m` consisting of cylinder test functions. -/
private def cylTestSubmodule (c m : ℝ) : Submodule ℝ (B0579.X c m) where
  carrier := {g : B0579.X c m | ∃ (φ : B0579.Plane → ℝ) (hφ : B0579.IsCylTest c φ),
    g = B0579.testLp c m hφ}
  zero_mem' := by
    refine ⟨fun _ => 0, isCylTest_zero c, ?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m),
      MemLp.coeFn_toLp ((isCylTest_zero c).memLp m)] with x h1 h2
    rw [h1]
    dsimp [B0579.testLp]
    rw [h2]
  add_mem' := by
    rintro g₁ g₂ ⟨φ₁, hφ₁, rfl⟩ ⟨φ₂, hφ₂, rfl⟩
    refine ⟨fun x => φ₁ x + φ₂ x, isCylTest_add hφ₁ hφ₂, ?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (B0579.testLp c m hφ₁) (B0579.testLp c m hφ₂),
      MemLp.coeFn_toLp (hφ₁.memLp m), MemLp.coeFn_toLp (hφ₂.memLp m),
      MemLp.coeFn_toLp ((isCylTest_add hφ₁ hφ₂).memLp m)] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply]
    dsimp [B0579.testLp]
    rw [h2, h3, h4]
  smul_mem' := by
    rintro a g ⟨φ, hφ, rfl⟩
    refine ⟨fun x => a * φ x, isCylTest_smul a hφ, ?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul a (B0579.testLp c m hφ),
      MemLp.coeFn_toLp (hφ.memLp m),
      MemLp.coeFn_toLp ((isCylTest_smul a hφ).memLp m)] with x h1 h2 h3
    rw [h1, Pi.smul_apply]
    dsimp [B0579.testLp]
    rw [h2, h3]

private theorem inner_testLp_eq_mulW (c m : ℝ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (g : B0579.X c m) :
    inner ℝ (B0579.testLp c m hφ) g =
      ∫ x in B0579.cell c, (B0579.mulW c m (-m) g : B0579.Plane → ℝ) x * φ x := by
  rw [L2.inner_def, B0579.integral_cellMeasure]
  have h1 : (B0579.testLp c m hφ : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] φ :=
    B0579.coeFn_testLp c m hφ
  have h2 : (B0579.mulW c m (-m) g : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => B0579.jb x ^ ((m - -m) / 2) * g x :=
    (B0579.ac_cellMeasure c (-m)).ae_le (B0579.coeFn_mulW c m (-m) g)
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [Real.inner_apply, NNReal.smul_def, smul_eq_mul, B0579.coe_density, hx1, hx2]
  have hm : (m - -m) / 2 = m := by ring
  rw [hm]
  ring

private theorem cylTestSubmodule_dense {c : ℝ} (hc : 0 < c) (m : ℝ) :
    Dense (cylTestSubmodule c m : Set (B0579.X c m)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  have h0 : B0579.mulW c m (-m) g = 0 := by
    apply UnforcedLeray.B0579Check.eq_zero_of_forall_test hc
    intro φ hφ
    have hmem : B0579.testLp c m hφ ∈ cylTestSubmodule c m := ⟨φ, hφ, rfl⟩
    have hin : inner ℝ (B0579.testLp c m hφ) g = 0 :=
      (Submodule.mem_orthogonal (cylTestSubmodule c m) g).1 hg _ hmem
    rwa [inner_testLp_eq_mulW c m hφ g] at hin
  calc g = B0579.mulW c (-m) m (B0579.mulW c m (-m) g) := by
        rw [B0579.mulW_mulW, B0579.mulW_self]
    _ = B0579.mulW c (-m) m 0 := by rw [h0]
    _ = 0 := map_zero _

/-- **Density of `B0579.IsCylTest c` in `X_{m,c}`** (`FreeCylTestApprox`). -/
theorem free_cyl_test_approx : FreeCylTestApprox := by
  intro c m hc f hf
  set F : B0579.X c m := hf.toLp f
  have hdense := cylTestSubmodule_dense hc m
  have hex : ∀ n : ℕ, ∃ φ : B0579.Plane → ℝ, ∃ hφ : B0579.IsCylTest c φ,
      ‖B0579.testLp c m hφ - F‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨g, hg_mem, hg_dist⟩ := Metric.mem_closure_iff.1 (hdense.closure_eq.symm ▸ mem_univ F)
      (1 / ((n : ℝ) + 1)) hpos
    obtain ⟨φ, hφ, rfl⟩ := hg_mem
    rw [dist_comm, dist_eq_norm] at hg_dist
    exact ⟨φ, hφ, hg_dist⟩
  choose fn hfn hdist using hex
  refine ⟨fn, hfn, ?_⟩
  have heq : ∀ n : ℕ, eLpNorm (fn n - f) 2 (B0579.cellMeasure c m) =
      ENNReal.ofReal ‖B0579.testLp c m (hfn n) - F‖ := by
    intro n
    rw [Lp.norm_def]
    have hae : (fn n - f) =ᵐ[B0579.cellMeasure c m]
        ((B0579.testLp c m (hfn n) - F : B0579.X c m) : B0579.Plane → ℝ) := by
      filter_upwards [Lp.coeFn_sub (B0579.testLp c m (hfn n)) F,
        MemLp.coeFn_toLp ((hfn n).memLp m), MemLp.coeFn_toLp hf] with x h1 h2 h3
      rw [Pi.sub_apply, h1, Pi.sub_apply]
      dsimp [B0579.testLp, F]
      rw [h2, h3]
    rw [eLpNorm_congr_ae hae,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (B0579.testLp c m (hfn n) - F))]
  simp_rw [heq]
  rw [← ENNReal.ofReal_zero]
  refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hdist n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Assembly of `FreeCylExistsUnique` -/

/-- Existence of a weak free cylinder flow `w` together with its smooth test approximants
`(fn n, ωn n)` converging to `(f, w)` in `X_{m,c}` at every age `t ≥ s` (used by `PartII-b:T24`
to transfer the `FreeCylEnergy` bound from `fn n` to arbitrary `f ∈ X_{m,c}`). -/
theorem free_cyl_exists_approx_of (hSm : FreeCylSmoothExists) (hLim : FreeCylApproxLimit)
    (m ν c : ℝ) (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (s : ℝ) (hs : 0 ≤ s) (f : B0579.Plane → ℝ) (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    ∃ (w : ℝ → B0579.Plane → ℝ) (fn : ℕ → B0579.Plane → ℝ) (ωn : ℕ → ℝ → B0579.Plane → ℝ),
      IsFreeCylFlow m tr s f w ∧
      (∀ n, B0579.IsCylTest c (fn n)) ∧
      Tendsto (fun n => eLpNorm (fn n - f) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) ∧
      (∀ n, IsFreeCylFlow m tr s (fn n) (ωn n)) ∧
      (∀ t : ℝ, s ≤ t →
        Tendsto (fun n => eLpNorm (ωn n t - w t) 2 (B0579.cellMeasure c m)) atTop (𝓝 0)) := by
  obtain ⟨fn, hfn, hconv⟩ := free_cyl_test_approx c m hc f hf
  choose ωn hωn using fun n => hSm m ν c hm hν hc tr hbu s hs (fn n) (hfn n)
  obtain ⟨w, hw, hw_conv⟩ := hLim m ν c hm hν hc tr hbu s hs f hf fn ωn hfn hconv hωn
  exact ⟨w, fn, ωn, hw, hfn, hconv, fun n => (hωn n).1, hw_conv⟩

/-- **Conditional assembly of `PartII-b:T23`** from the two remaining existence leaves
(`FreeCylSmoothExists`, `FreeCylApproxLimit`), using the proved `free_cyl_unique` and
`free_cyl_test_approx`. -/
theorem free_cyl_exists_unique_of (hSm : FreeCylSmoothExists) (hLim : FreeCylApproxLimit) :
    FreeCylExistsUnique := by
  intro m ν c hm hν hc tr hbu s hs f hf
  refine ⟨?_, free_cyl_unique m ν c hm hν hc tr hbu s hs f⟩
  obtain ⟨w, _, _, hw, _, _, _, _⟩ :=
    free_cyl_exists_approx_of hSm hLim m ν c hm hν hc tr hbu s hs f hf
  exact ⟨w, hw⟩

end UnforcedLeray.Short.IIb

end
