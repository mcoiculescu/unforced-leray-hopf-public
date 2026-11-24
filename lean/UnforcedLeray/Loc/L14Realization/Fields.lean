import UnforcedLeray.Loc.L14Realization.Symmetry
import UnforcedLeray.Loc.L14Realization.TestCalculus
import UnforcedLeray.Blueprint.Localization.Realization
import UnforcedLeray.Loc.L01Coefficient.Basic
import UnforcedLeray.Analysis.Heat.Energy
import UnforcedLeray.Analysis.Heat.Solenoidal
import UnforcedLeray.Analysis.Pressure.VelocityForcing
import Mathlib.Data.Real.ConjExponents

/-!
# Step L14, helpers: the total field `e^{htΔ}u₀ + ρ(t)` and its regularity

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 532–546, `loc:eq:total-field` and `loc:eq:regularity`; blueprint units B1028, B1029).

For `h > 0`, a datum `u₀ ∈ L²` and a strong remainder `ρ` (`IsPhysicalStrongRemainder`):

* `totalH2 h u₀ ρ t = e^{htΔ}u₀ + ρ(t) ∈ H²` (the compiled `Heat.heatH2Path` at time `ht`),
  whose value is the `L²` class of `physicalVelocity h u₀ ρ t` for `t > 0`
  (`toL2_physicalVelocity`);
* the `L²` path is continuous on `[0,T]` with value `u₀` at `0`
  (`continuousOn_toL2_physicalVelocity`; the remainder vanishes at `0` by the rate
  `‖ρ(t)‖ ≤ C t^{1/4}` of line 540);
* `totalH2` is continuous on `(0,T]` (`continuousOn_totalH2`), the total field is solenoidal
  (`isSolenoidal_physicalVelocity`) and `𝒪`-invariant (`isAxisymmetricNoSwirl_physicalVelocity`);
* the `L²` derivative on `(0,T)` is `h Δ u + N` (`hasDerivAt_totalH2_value`), from
  `Heat.heatOperator_hasDerivAt_laplace` and the strong equation of lines 546–547;
* for an `H²` field the convective forcing `(u·∇)u` is in `L²`
  (`velocityForcing_memLp_two_of_H2`: `u ∈ L⁶`, `∇u ∈ L³`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Blueprint.L14

open SobolevGraph PressureAnalysis

section Defs

variable (h : ℝ) (u₀ : SpatialField) (ρ : ℝ → H2)

/-- The heat part `e^{htΔ}u₀` as an `H²` path (zero for `t ≤ 0`). -/
def heatH2 (t : ℝ) : H2 := Heat.heatH2Path (toL2 u₀) (h * t)

/-- The total field `e^{htΔ}u₀ + ρ(t)` in `H²` (line 532). -/
def totalH2 (t : ℝ) : H2 := heatH2 h u₀ t + ρ t

/-- The gradient fields of the total field. -/
def gradField0 : FirstDerivatives := fun t i => ((totalH2 h u₀ ρ t).first i : SpatialField)

/-- The ordered second derivative fields of the total field. -/
def secondField0 : SecondDerivatives :=
  fun t i j => ((totalH2 h u₀ ρ t).second i j : SpatialField)

end Defs

variable {h : ℝ} {u₀ : SpatialField} {ρ : ℝ → H2}

theorem totalH2_value (t : ℝ) :
    (totalH2 h u₀ ρ t).value = (heatH2 h u₀ t).value + (ρ t).value :=
  map_add H2.valueCLM _ _

theorem heatH2_value (hh : 0 < h) {t : ℝ} (ht : 0 < t) :
    (heatH2 h u₀ t).value = Heat.heatOperator (h * t) (toL2 u₀) :=
  Heat.heatH2Path_value _ (mul_pos hh ht)

theorem physicalVelocity_pos {t : ℝ} (ht : 0 < t) :
    physicalVelocity h u₀ ρ t = Heat.flow u₀ (h * t) + ((ρ t).value : SpatialField) := by
  simp only [physicalVelocity, ht, ite_true]

@[simp] theorem physicalVelocity_zero : physicalVelocity h u₀ ρ 0 = u₀ := by
  simp [physicalVelocity]

theorem memLp_physicalVelocity (hu₀ : MemLp u₀ 2 volume) (t : ℝ) :
    MemLp (physicalVelocity h u₀ ρ t) 2 volume := by
  unfold physicalVelocity
  split_ifs
  · exact (Heat.flow_memLp hu₀ _).add (Lp.memLp _)
  · exact hu₀

theorem toL2_physicalVelocity (hh : 0 < h) (hu₀ : MemLp u₀ 2 volume) {t : ℝ} (ht : 0 < t) :
    toL2 (physicalVelocity h u₀ ρ t) = (totalH2 h u₀ ρ t).value := by
  rw [physicalVelocity_pos ht, L10.toL2_add' (Heat.flow_memLp hu₀ _) (Lp.memLp _),
    Heat.toL2_flow hu₀, ViscosityTransport.toL2_coe, totalH2_value, heatH2_value hh ht]

theorem physicalVelocity_ae (hh : 0 < h) (hu₀ : MemLp u₀ 2 volume) {t : ℝ} (ht : 0 < t) :
    physicalVelocity h u₀ ρ t =ᵐ[volume] ((totalH2 h u₀ ρ t).value : SpatialField) := by
  rw [← toL2_physicalVelocity hh hu₀ ht]
  exact (coeFn_toL2 (memLp_physicalVelocity hu₀ t)).symm

theorem continuousOn_totalH2 (hh : 0 < h) {T : ℝ} (hρ : ContinuousOn ρ (Ioc 0 T)) :
    ContinuousOn (totalH2 h u₀ ρ) (Ioc 0 T) := by
  have h1 : ContinuousOn (heatH2 h u₀) (Ioc 0 T) := by
    show ContinuousOn (fun t => Heat.heatH2Path (toL2 u₀) (h * t)) (Ioc 0 T)
    exact (Heat.heatH2Path_continuousOn (toL2 u₀)).comp
      (continuous_const.mul continuous_id).continuousOn (fun t ht => mul_pos hh ht.1)
  exact h1.add hρ

/-- The `L²` path of the total field is continuous on `[0, T]`, with value `u₀` at `0`. -/
theorem continuousOn_toL2_physicalVelocity (hh : 0 < h) (hu₀ : MemLp u₀ 2 volume) {T C : ℝ}
    (hρ : ContinuousOn ρ (Ioc 0 T))
    (hrate : ∀ t ∈ Ioc (0 : ℝ) T, ‖(ρ t).value‖ ≤ C * t ^ (1 / 4 : ℝ)) :
    ContinuousOn (fun t => toL2 (physicalVelocity h u₀ ρ t)) (Icc 0 T) := by
  classical
  set R : ℝ → L2Space := fun t => if 0 < t then (ρ t).value else 0 with hRdef
  have hR : ContinuousOn R (Icc 0 T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      have hR0 : R 0 = 0 := by simp [hRdef]
      rw [ContinuousWithinAt, hR0]
      have hlim : Tendsto (fun s : ℝ => C * s ^ (1 / 4 : ℝ)) (𝓝[Icc 0 T] 0) (𝓝 0) := by
        have hc : Continuous (fun s : ℝ => C * s ^ (1 / 4 : ℝ)) :=
          continuous_const.mul (Real.continuous_rpow_const (by norm_num))
        have := hc.tendsto 0
        simp only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with s hs
      by_cases hs0 : 0 < s
      · simp only [hRdef, hs0, ite_true]
        exact hrate s ⟨hs0, hs.2⟩
      · have : s = 0 := le_antisymm (not_lt.mp hs0) hs.1
        subst this
        simp [hRdef, Real.zero_rpow]
    · have hc : ContinuousWithinAt (fun s => (ρ s).value) (Ioc 0 T) t :=
        (H2.valueCLM.continuous.comp_continuousOn hρ) t ⟨hpos, ht.2⟩
      have hmem : Ioc 0 T ∈ 𝓝[Icc 0 T] t :=
        mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, hpos, fun s hs => ⟨hs.1, hs.2.2⟩⟩
      have h1 := hc.mono_of_mem_nhdsWithin hmem
      refine h1.congr_of_eventuallyEq ?_ (by simp [hRdef, hpos])
      filter_upwards [hmem] with s hs
      simp [hRdef, hs.1]
  have hheat : ContinuousOn (fun t => Heat.heatOperator (h * t) (toL2 u₀)) (Icc 0 T) :=
    ((Heat.heatOperator_strongly_continuous (toL2 u₀)).comp
      (continuous_const.mul continuous_id)).continuousOn
  refine (hheat.add hR).congr fun t ht => ?_
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    show toL2 (physicalVelocity h u₀ ρ 0) = Heat.heatOperator (h * 0) (toL2 u₀) + R 0
    simp [hRdef, physicalVelocity_zero, Heat.heatOperator_zero]
  · show toL2 (physicalVelocity h u₀ ρ t) = Heat.heatOperator (h * t) (toL2 u₀) + R t
    rw [toL2_physicalVelocity hh hu₀ hpos, totalH2_value, heatH2_value hh hpos, hRdef]
    simp [hpos]

theorem isSolenoidal_physicalVelocity (hh : 0 < h) (hdat : IsInitialDatum u₀) {T : ℝ}
    (hsol : ∀ t ∈ Ioc (0 : ℝ) T, (ρ t).value ∈ Leray.solenoidalSubspace)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : IsSolenoidal (physicalVelocity h u₀ ρ t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    rw [physicalVelocity_zero]
    exact hdat.solenoidal
  · apply (Leray.mem_solenoidalSubspace_toL2_iff (memLp_physicalVelocity hdat.memLp t)).mp
    rw [toL2_physicalVelocity hh hdat.memLp hpos, totalH2_value, heatH2_value hh hpos]
    refine Submodule.add_mem _ ?_ (hsol t ⟨hpos, ht.2⟩)
    apply (Leray.mem_solenoidalSubspace_iff _).mpr
    exact Heat.heatOperator_solenoidal _
      (Leray.solenoidal_congr_ae hdat.solenoidal (coeFn_toL2 hdat.memLp).symm)

theorem isAxisymmetricNoSwirl_physicalVelocity (hh : 0 < h) (hsym : IsAxisymmetricNoSwirl u₀)
    {T : ℝ} (hρs : ∀ t ∈ Ioc (0 : ℝ) T, IsAxisymmetricNoSwirl ((ρ t).value : SpatialField))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : IsAxisymmetricNoSwirl (physicalVelocity h u₀ ρ t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    rw [physicalVelocity_zero]
    exact hsym
  · rw [physicalVelocity_pos hpos]
    exact isAxisymmetricNoSwirl_add (isAxisymmetricNoSwirl_flow hsym (mul_pos hh hpos))
      (hρs t ⟨hpos, ht.2⟩)

theorem hasWeak_physicalVelocity (hh : 0 < h) (hu₀ : MemLp u₀ 2 volume) {t : ℝ} (ht : 0 < t)
    (i : Fin 3) :
    HasWeakSpatialDerivative i (physicalVelocity h u₀ ρ t) (gradField0 h u₀ ρ t i) :=
  ((totalH2 h u₀ ρ t).hasWeakFirst i).congr (physicalVelocity_ae hh hu₀ ht).symm
    EventuallyEq.rfl

/-- The `L²` derivative of the total field: `∂ₜu = hΔu + N`. -/
theorem hasDerivAt_totalH2_value (hh : 0 < h) {T C : ℝ} {N : ℝ → L2Space}
    (hρ : IsPhysicalStrongRemainder h T u₀ ρ N C) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => (totalH2 h u₀ ρ s).value)
      (h • H2.laplace (totalH2 h u₀ ρ t) + N t) t := by
  have hht : 0 < h * t := mul_pos hh ht.1
  have hheat : HasDerivAt (fun s => Heat.heatOperator (h * s) (toL2 u₀))
      (h • H2.laplace (heatH2 h u₀ t)) t := by
    have h1 := Heat.heatOperator_hasDerivAt_laplace hht (toL2 u₀)
    have h2 : HasDerivAt (fun s : ℝ => h * s) h t := by
      simpa using (hasDerivAt_id t).const_mul h
    exact h1.scomp t h2
  have hheat' : HasDerivAt (fun s => (heatH2 h u₀ s).value)
      (h • H2.laplace (heatH2 h u₀ t)) t := by
    refine hheat.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds ht.1] with s hs
    exact heatH2_value hh hs
  have hsum := hheat'.add (hρ.equation t ht)
  have he : (fun s => (totalH2 h u₀ ρ s).value) =
      fun s => (heatH2 h u₀ s).value + (ρ s).value := funext fun s => totalH2_value s
  have hl : H2.laplace (totalH2 h u₀ ρ t) = H2.laplace (heatH2 h u₀ t) + H2.laplace (ρ t) :=
    map_add H2.laplaceCLM _ _
  rw [he, hl, smul_add, add_assoc]
  exact hsum

/-- An `H²` field has `(u·∇)u ∈ L²` (`u ∈ L⁶`, `∇u ∈ L³`). -/
theorem velocityForcing_memLp_two_of_H2 (W : H2) {v : SpatialField}
    (hv : v =ᵐ[volume] (W.value : SpatialField)) {g : Fin 3 → SpatialField}
    (hg : ∀ j, g j =ᵐ[volume] (W.first j : SpatialField)) (i : Fin 3) :
    MemLp (velocityForcing v g i) 2 volume := by
  have h6 : MemLp (W.value : SpatialField) 6 volume :=
    SobolevEmbedding.weak_memLp_six (Lp.memLp W.value) (fun j => Lp.memLp (W.first j))
      (fun j => W.hasWeakFirst j)
  have h3 : ∀ j, MemLp (W.first j : SpatialField) 3 volume := fun j => by
    have := L01.h1_memLp_three (L10.h2PartialH1 W j)
    simpa [L10.h2PartialH1, H1.value_ofWeakDerivatives] using this
  have hT : ENNReal.HolderTriple 6 3 2 := by
    apply ENNReal.HolderTriple.of_toReal
    rw [Real.holderTriple_iff]
    norm_num
  exact velocityForcing_memLp (h6.ae_eq hv.symm) (fun j => (h3 j).ae_eq (hg j).symm) i

end UnforcedLeray.Blueprint.L14
