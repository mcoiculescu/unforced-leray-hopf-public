import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_2
import UnforcedLeray.Short.PartIIa.Tasks.F14WeakStressExists
import UnforcedLeray.Short.PartIIa.Tasks.F15WeakStressUnique
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.StressInvH1Grad.Lift
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.StressInvH1Grad.Slice
import UnforcedLeray.Lib.PhaseTrace.Trace

/-!
# `StressInvH1Grad` (Task `PartIII-b:IIIb-D5/2/1`; source 1556-1583, 4145, 5975-5978)

Source of record: `the November 2 reference manuscript`, lines 1556-1583
(`free:weak-stress`, `free:stress-energy`: `‖∇S_μT‖_{Y_2} ≤ ν⁻¹‖T‖_{Y_2}`; "the weak solution is
unique among distributional `Y_2` solutions"), 4145 (`S_μ = R_μℙdiv`), 5975-5978
(`b = -S_σT'`, `b, ∇b ∈ Y_2`).

At a level `L` with period `P = 2εc ≤ 1` and `μ > -1/4`, for a concrete weak stress inverse `S`
(`IsWeakStressInverse`) and a stress `T`:

1. the physical stress `𝒩_T(T₁ + T₂)` lifts to `T_sym ∈ Y_2(Sym_3)` with
   `⟨∇Φ, T_sym⟩ = stressPair` (`StressLiftY.exists_symY2_lift`);
2. the abstract inverse `S_μ` of `PartIIa.weakStressExists` has a gradient `∇S_μT_sym ∈ Y_2`;
3. `toY (𝒩_v (S T))` is phase-solenoidal and solves the weak equation of `T_sym`, so it equals
   `S_μT_sym` (`PartIIa.weakStressUnique`);
4. the distributional gradient slices into the phases (`GradSlice.ae_forall_grad`) and gives
   `HasWeakSpatialDerivative` for the real parts of jointly measurable representatives
   (`GradSlice.hasWeak_of_pair`, `IIb.exists_isInYr_hasRepY_q`).

`stressInvH1Grad_level` is the per-level statement (hypothesis `P ≤ 1`, needed by the
`Y_2` theory of `free-foundation.tex` in its Lean form: `WeakStressExists`, `WeakStressUnique`
are stated for `P ≤ 1`).  `stressInvH1Grad_proved` is `Wiring.ModeAux.StressInvH1Grad`
(which carries the `P ≤ 1` hypothesis).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08
open Wiring.ModeAux

/-- **Per-level `Y_2` gradient of the stress inverse** (source 1556-1583, 4145, 5975-5978): at a
level with `P = 2εc ≤ 1`, `m_Z ≥ 0`, `ρ_b > 0` and `μ > -1/4`, for a concrete weak stress inverse
`S` and a stress `T`, the lifted velocity `modeBstar L (S T)` has three weak spatial derivatives,
jointly measurable and square integrable on one period. -/
theorem stressInvH1Grad_level {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hmZ : 0 ≤ K.mZ) (hρ : 0 < L.ρb Pl K) (hP1 : 2 * L.ε * cOf L.ν ≤ 1) (hμ : 0 < μ + 1 / 4)
    (S : LStr Pl K L →L[ℝ] LVel Pl L) (hS : IsWeakStressInverse S L.ε μ) (T : LStr Pl K L) :
    ∃ G : Fin 3 → ℝ → SpatialField, ∀ i : Fin 3,
      AEStronglyMeasurable (fun x : SpaceTime => G i x.1 x.2) volume ∧
      MemLp (fun x : SpaceTime => G i x.1 x.2) 2
        (volume.restrict (periodSlab (2 * L.ε * cOf L.ν))) ∧
      ∀ᵐ τ, HasWeakSpatialDerivative i (modeBstar L (S T) τ) (G i τ) := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hP0 : 0 < 2 * L.ε * cOf L.ν := mul_pos (mul_pos two_pos L.ε_pos) hc
  have : Fact (0 < 2 * L.ε * cOf L.ν) := ⟨hP0⟩
  -- 1. the lift of the physical stress into `Y_2(Sym_3)`
  have hrow : ∀ i, UnforcedLeray.Short.IIb.IsInYr (2 * L.ε * cOf L.ν) 2
      (StressLiftY.rowsOf (strPhys L.ε⁻¹ (cOf L.ν) (strSum T)) i) := fun i =>
    StressLiftY.isInYr_rowsOf_strPhys L.ε_pos hc (StressLiftY.measurable_strSum T)
      (StressLiftY.memLp_strSum L.ν_pos hmZ hρ T) i
  obtain ⟨Ts, hTs⟩ := StressLiftY.exists_symY2_lift (strPhys L.ε⁻¹ (cOf L.ν) (strSum T))
    (fun x i j => StressLiftY.strPhys_symm _ _ _ x i j) hrow
  -- 2. the abstract weak stress inverse and its gradient
  have hμc : 0 < ((μ : ℂ)).re + 1 / 4 := by simpa using hμ
  obtain ⟨Sa, hSa, hbd⟩ :=
    UnforcedLeray.Short.PartIIa.weakStressExists (2 * L.ε * cOf L.ν) hP1 L.ν L.ν_pos (μ : ℂ) hμc
  obtain ⟨-, g, hg, -⟩ := hbd Ts
  -- 3. identification by distributional uniqueness
  have hsol : IsPhaseSolenoidal (B0005.toY (2 * L.ε * cOf L.ν) (modeBstar L (S T))) :=
    isPhaseSolenoidal_toY_modeBstar L (S T) (hS T).solenoidal
  have heq : ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * L.ε * cOf L.ν) Φ →
      (∀ p, ∑ j, dy j Φ p j = 0) →
      phasePair (2 * L.ε * cOf L.ν) 2 ((μ : ℂ) • Φ + L0T L.ν Φ)
          (B0005.toY (2 * L.ε * cOf L.ν) (modeBstar L (S T))) =
        -UnforcedLeray.Short.PartIIa.tensorGradPair (2 * L.ε * cOf L.ν) Φ
          (Ts : UnforcedLeray.Short.PartIIa.Y2Sym (2 * L.ε * cOf L.ν)) := by
    intro Φ hΦ hdiv
    have hΦ' : IsPhaseTest (2 * L.ε * cOf L.ν) ((μ : ℂ) • Φ + L0T L.ν Φ) :=
      (hΦ.const_smul (μ : ℂ)).add (isPhaseTest_L0T hΦ L.ν)
    rw [phasePair_toY_modeBstar L (S T) hΦ', hTs Φ hΦ]
    have hfun : ((μ : ℂ) • Φ + L0T L.ν Φ) = fun x => L0T L.ν Φ x + (μ : ℂ) • Φ x := by
      funext x
      simp [add_comm]
    rw [hfun]
    exact (hS T).equation Φ ⟨hΦ, hdiv⟩
  have hwS : B0005.toY (2 * L.ε * cOf L.ν) (modeBstar L (S T)) = Sa Ts :=
    UnforcedLeray.Short.PartIIa.weakStressUnique (2 * L.ε * cOf L.ν) hP1 L.ν L.ν_pos (μ : ℂ) hμc
      Sa hSa Ts _ hsol heq
  rw [← hwS] at hg
  -- 4. jointly measurable representatives of the gradient and slicing
  have hrep : ∀ i, ∃ W : ℝ × Space → CVec3,
      UnforcedLeray.Short.IIb.IsInYr (2 * L.ε * cOf L.ν) 2 W ∧
        UnforcedLeray.Short.IIb.HasRepY (g i) W := fun i => by
    obtain ⟨W, hW, hWr, -⟩ := UnforcedLeray.Short.IIb.exists_isInYr_hasRepY_q
      (2 * L.ε * cOf L.ν) 2 two_pos (q := 2) ENNReal.ofNat_ne_top (by norm_num) (g i)
    exact ⟨W, hW, hWr⟩
  choose W hWY hWr using hrep
  refine ⟨fun i t y => B0005.reL (W i (t, y)), fun i => ⟨?_, ?_, ?_⟩⟩
  · exact B0005.reL.continuous.comp_aestronglyMeasurable (hWY i).meas
  · have hm := UnforcedLeray.Short.IIb.memLp_phaseCell_of_phaseLpNorm hP0 two_pos (hWY i).meas
      (hWY i).finite
    rw [ENNReal.ofReal_ofNat] at hm
    exact B0005.reL.comp_memLp' hm
  · have hf := modeBstar_isY2 L (S T)
    have h1 := UnforcedLeray.PhaseTrace.ae_comp_mk
      (GradSlice.ae_forall_grad (P := 2 * L.ε * cOf L.ν) ENNReal.one_lt_two (hg i))
    filter_upwards [h1, hf.toY_ae, hf.ae_pathOf_eq hP0, (hWr i).slice] with t ht hy hp hs
    refine GradSlice.hasWeak_of_pair ht ?_ ?_
    · rw [hy]
      exact hp
    · filter_upwards [hs] with y hy'
      rw [← hy']

/-- **`StressInvH1Grad` at the levels with `P = 2εc ≤ 1`** (the regime of `bg:common-body-graph`,
source 1356: "`0 < P ≤ 1`"; along the sequence `P ≤ 1` holds for large `n`,
`pf2b_period_le_one`).  `Wiring.ModeAux.StressInvH1Grad` with the extra hypothesis
`2 * (D.level n).ε * cOf (D.level n).ν ≤ 1`. -/
def StressInvH1GradP : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → ∀ n : ℕ, D.IsActualLevel dm dp n →
    2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 →
    ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) →
      RegimePins D.Pl D.K (D.level n) (D.mu n z) →
      0 < D.mu n z → D.mu n z < 1 / 4 →
      ∀ (S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)),
        IsWeakStressInverse S (D.level n).ε (D.mu n z) →
      ∀ (T : LStr D.Pl D.K (D.level n)),
        ∃ G : Fin 3 → ℝ → SpatialField, ∀ i : Fin 3,
          AEStronglyMeasurable (fun x : SpaceTime => G i x.1 x.2) volume ∧
          MemLp (fun x : SpaceTime => G i x.1 x.2) 2
            (volume.restrict (periodSlab (2 * (D.level n).ε * cOf (D.level n).ν))) ∧
          ∀ᵐ τ, HasWeakSpatialDerivative i (modeBstar (D.level n) (S T) τ) (G i τ)

/-- **`StressInvH1GradP` holds** (source 1556-1583, 4145, 5975-5978). -/
theorem stressInvH1GradP_proved : StressInvH1GradP := by
  intro D dm dp hst n _hact hP1 z _hz _hne _hp hμ0 _hμ1 S hS T
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hρ : 0 < (D.level n).ρb D.Pl D.K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 : 0 < ((D.level n).params D.Pl).ν := (D.level n).ν_pos
    have h2 : 0 < ((D.level n).params D.Pl).ε := (D.level n).ε_pos
    have := hst.C0_pos
    positivity
  exact stressInvH1Grad_level hmZ hρ hP1 (by linarith) S hS T

/-- **`StressInvH1Grad` (with the `P ≤ 1` hypothesis of `bg:common-body-graph`, source 1356)**. -/
theorem stressInvH1Grad_proved : Wiring.ModeAux.StressInvH1Grad :=
  stressInvH1GradP_proved

end UnforcedLeray.Short.PartIIIb.Concrete
