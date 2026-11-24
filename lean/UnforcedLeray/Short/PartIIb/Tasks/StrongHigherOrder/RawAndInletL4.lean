import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7.Decay
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4.Inlet
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4.Raw
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.WtdJetInterp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.MeanJetsFixed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1.MeanJetFormula
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1_2.PsiJetInterior
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.TrainStreamWtdBdd_Sub
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromMixed1D
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Mean

/-!
# `PartII-b:S2/3`: uniform `L⁴` bounds on `D^k U_raw(τ)` and `D^k E_i(τ)`

Source of record: `the November 2 reference manuscript`, lines 2543-2551,
2557-2559, 2607-2610 ("The inverse-distance bounds and the all-age expansion give
`D^jV ∈ C_per L^4`").

A field with `(1+|y|)‖G(y)‖ ≤ B` off the (null) axis lies in `L⁴(ℝ³)` with norm `≤ B·decayK`
(`eLpNorm_le_of_decay_off_axis`, from `PartIIIb.Concrete.eLpNorm_le_of_decay`).

* Inlet columns, every order, threshold `ν₀ = 1`: `RawAndInletL4.inletDecayAll`
  (unconditional; `inletIteratedL4Bound`).
* Raw lift, every order, one threshold: `RawAndInletL4.rawDecayAll_of`, from the fixed-parameter
  weighted train bounds `PartIIIb.Concrete.TrainStreamWtdBdd` (SP 439-467) and
  `PartIIIb.Concrete.TrainHeatRemWtd` (SP 439-458).  These are the only inputs not in the library:
  the proved Part I bounds (`TrainFluctuationDecay`, `TrainMeanExpansion`, `TrainTransverseTails`)
  give a threshold `ν₀` depending on the derivative orders, while the target fixes `ν₀` before the
  order `k`.

`rawAndInletIteratedL4Bound_of` assembles the target from these two train inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RawAndInletL4

open UnforcedLeray

/-- A field with `(1+|y|)‖G(y)‖ ≤ B` off the axis has `‖G‖_{L⁴} ≤ B · decayK`. -/
theorem eLpNorm_le_of_decay_off_axis {V : Type*} [NormedAddCommGroup V] (G : Space → V)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ y : Space, y ∉ Axi.axis → (1 + ‖y‖) * ‖G y‖ ≤ B) :
    eLpNorm G 4 (volume : Measure Space) ≤
      ENNReal.ofReal (B * PartIIIb.Concrete.decayK) := by
  classical
  set G' : Space → V := fun y => if y ∈ Axi.axis then 0 else G y with hG'
  have hae : G =ᵐ[volume] G' := by
    filter_upwards [Axi.ae_not_mem_axis] with y hy
    simp [hG', hy]
  rw [eLpNorm_congr_ae hae]
  refine PartIIIb.Concrete.eLpNorm_le_of_decay G' hB fun y => ?_
  have hp : 0 < 1 + ‖y‖ := by positivity
  by_cases hy : y ∈ Axi.axis
  · simp only [hG', hy, ite_true, norm_zero]
    positivity
  · simp only [hG', hy, ite_false]
    rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
    exact h y hy

theorem one_le_R_of {p : UnforcedLeray.Cons.C03.Concrete.Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) : 1 ≤ p.R := by
  have hε1 : p.ε ≤ 1 := by
    have hd0 : 0 ≤ d := le_trans hreg.dm_pos.le hreg.dm_le
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg hd0 p.ν_pos.le)
  show 1 ≤ p.ε⁻¹
  exact (one_le_inv₀ p.ε_pos).2 hε1

theorem one_le_c_of {p : UnforcedLeray.Cons.C03.Concrete.Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) : 1 ≤ p.c := by
  rw [hreg.c_eq]
  exact (one_le_inv₀ (pow_pos p.ν_pos 2)).2 (pow_le_one₀ p.ν_pos.le hν1)

/-- **The inlet half, unconditionally** (source 2543-2551, 2607-2608): for every order `k` the
inlet columns `D^kE_i(τ)` are bounded in `L⁴(ℝ³)` uniformly in `τ` and `i`, for `ν ≤ 1`. -/
theorem inletIteratedL4Bound (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile)
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) (dm dp : ℝ)
    (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ : ℝ) (i : Fin 2),
      eLpNorm (fun y => iteratedFDeriv ℝ k (p.inlet i τ) y) 4 volume ≤ ENNReal.ofReal M := by
  obtain ⟨Bi, hBi0, hBi⟩ :=
    inletDecayAll lam q hq k p hmode (one_le_c_of hreg hν1) (one_le_R_of hreg)
  exact ⟨Bi * PartIIIb.Concrete.decayK, mul_nonneg hBi0 ENNReal.toReal_nonneg,
    fun τ i => eLpNorm_le_of_decay_off_axis _ hBi0 fun y hy => hBi i τ y hy⟩

/-- `PsiJetWtd` from the proved Part I overlap transverse tails and `psiJetInterior`. -/
theorem psiJetWtd_s23 : PartIIIb.Concrete.PsiJetWtd := by
  have hFD0 : Short.PartI.OverlapFluctuationDecay :=
    Short.PartI.overlap_fluctuation_decay Short.PartI.overlap_highnorm_uniform
  have hOv : Short.PartI.TrainOverlap :=
    Short.PartI.trainOverlap_proof hFD0
      (Short.PartI.overlap_mean_decay Short.PartI.overlap_highnorm_uniform hFD0
        Short.PartI.overlap_mean_primitive)
  have hVort : Short.PartI.TrainVorticityGaussianTail :=
    Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : Short.PartI.TrainStreamVelocityPressureTails :=
    Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  exact PartIIIb.Concrete.psiJetWtd_of
    (Short.PartI.trainTransverseTails_proof hVort hTails) _root_.psiJetInterior

/-- Bounded-age form of `WeightedTrainFluctAgeJetFixed` (restated against `..._org_1_1_1`). -/
theorem trainFluctWtdAgeJet_of_s23
    (h : PartIIIb.Concrete.WeightedTrainFluctAgeJetFixed) :
    PartIIIb.Concrete.TrainFluctWtdAgeJet := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, h'⟩ := h ρ hρ
  refine ⟨ν₀, hν₀, fun ν c hν hle hc tr htr m ℓ j S => ?_⟩
  subst hc
  obtain ⟨C, κ, hκ, hC⟩ := h' ν hν hle tr htr m ℓ j
  refine ⟨|C|, fun s hs _ z => ?_⟩
  have he0 : 0 ≤ Real.exp (-(κ * s)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(κ * s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hκ.le hs.le))
  calc (1 + |z.2|) ^ m * ‖Short.PartI.ageJet ℓ j
          (fun r w => tr.ψ r w - Short.PartI.hmean (Short.PartI.trainPeriod ρ ν) (tr.ψ r) w.2) s z‖
      ≤ C * Real.exp (-(κ * s)) := hC s hs z
    _ ≤ |C| * Real.exp (-(κ * s)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) he0
    _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) he1

/-- `TrainMeanWtdBdd` (one threshold for all orders), closed unconditionally. -/
theorem trainMeanWtdBdd_s23 : PartIIIb.Concrete.TrainMeanWtdBdd :=
  PartIIIb.Concrete.trainMeanWtdBdd_of
    (PartIIIb.Concrete.trainMeanWtdMixed_of psiJetWtd_s23 PartIIIb.Concrete.meanJetFormula)
    (PartIIIb.Concrete.meanJetsFixed_of Short.PartI.trainJetsBoundedFixed)
    PartIIIb.Concrete.wtdJetInterp

end UnforcedLeray.Short.IIb.RawAndInletL4

namespace UnforcedLeray.Short.IIb

/-- **`RawAndInletIteratedL4Bound` from the fixed-parameter weighted train bounds**
(`PartII-b:S2/3`; source 2543-2551, 2557-2559, 2607-2610). -/
theorem rawAndInletIteratedL4Bound_of (hS : PartIIIb.Concrete.TrainStreamWtdBdd)
    (hN : PartIIIb.Concrete.TrainHeatRemWtd) :
    UnforcedLeray.Short.IIb.RawAndInletIteratedL4Bound := by
  intro Sig lam q _ hq dm dp _
  obtain ⟨ν₁, hν₁, Hraw⟩ := RawAndInletL4.rawDecayAll_of hS hN dm dp
  refine ⟨min ν₁ 1, lt_min hν₁ one_pos, fun p d hreg hν _ hmode k => ?_⟩
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  obtain ⟨Br, hBr0, hBr⟩ := Hraw p d hreg (hν.trans (min_le_left _ _)) k
  obtain ⟨Bi, hBi0, hBi⟩ := RawAndInletL4.inletDecayAll lam q hq k p hmode
    (RawAndInletL4.one_le_c_of hreg hν1) (RawAndInletL4.one_le_R_of hreg)
  have hM0 : 0 ≤ max Br Bi := le_max_of_le_left hBr0
  refine ⟨max Br Bi * PartIIIb.Concrete.decayK, mul_nonneg hM0 ENNReal.toReal_nonneg,
    fun τ => ⟨?_, fun i => ?_⟩⟩
  · exact RawAndInletL4.eLpNorm_le_of_decay_off_axis _ hM0
      fun y hy => (hBr τ y hy).trans (le_max_left _ _)
  · exact RawAndInletL4.eLpNorm_le_of_decay_off_axis _ hM0
      fun y hy => (hBi i τ y hy).trans (le_max_right _ _)

/-- **The same, from the four fixed-parameter weighted Part I leaves** (SP 439-467 at fixed
parameters, SP 427-435): `TrainStreamWtdBdd` from `trainStreamWtdBdd_of`, `TrainHeatRemWtd` from
`trainHeatRemWtd_of` (with the proved `trainStreamSmooth`, `trainMeanEquations_proof`,
`heatTermSmooth`). -/
theorem rawAndInletIteratedL4Bound_of_leaves (hFW : PartIIIb.Concrete.TrainFluctWtdFixed)
    (hMR : PartIIIb.Concrete.TrainMeanRemWtdFixed) (hFB : PartIIIb.Concrete.TrainFluctWtdBdd)
    (hMB : PartIIIb.Concrete.TrainMeanWtdBdd) :
    UnforcedLeray.Short.IIb.RawAndInletIteratedL4Bound :=
  rawAndInletIteratedL4Bound_of (PartIIIb.Concrete.trainStreamWtdBdd_of hFB hMB)
    (PartIIIb.Concrete.trainHeatRemWtd_of PartI.trainStreamSmooth PartI.trainMeanEquations_proof
      heatTermSmooth hFW hMR)

/-- **Uniform `L⁴` bounds on `D^k U_raw(τ)` and `D^k E_i(τ)` (`PartII-b:S2/3`)**:
source lines 2543-2551, 2557-2559, 2607-2610. -/
theorem rawAndInletIteratedL4Bound_proof :
    UnforcedLeray.Short.IIb.RawAndInletIteratedL4Bound := by
  have hF : PartIIIb.Concrete.WeightedTrainFluctAgeJetFixed :=
    PartIIIb.Concrete.weightedTrainFluctAgeJetFixed_of
      PartI.trainFluctAgeJetFixed fluctDoubledWeightPoly_proof
  exact rawAndInletIteratedL4Bound_of_leaves
    (PartIIIb.Concrete.trainFluctWtdFixed_of PartI.trainStreamSmooth
      PartI.trainMeanEquations_proof PartI.jointFromAgeJets hF)
    (PartIIIb.Concrete.trainMeanRemWtdFixed_of PartI.trainMeanEquations_proof
      heatTermSmooth PartI.jointFromMixed1D weightedTrainMeanRemMixedFixed_proof)
    (PartIIIb.Concrete.trainFluctWtdBdd_of (RawAndInletL4.trainFluctWtdAgeJet_of_s23 hF))
    RawAndInletL4.trainMeanWtdBdd_s23

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.rawAndInletIteratedL4Bound_proof
#print axioms UnforcedLeray.Short.IIb.rawAndInletIteratedL4Bound_of_leaves
#print axioms UnforcedLeray.Short.IIb.rawAndInletIteratedL4Bound_of
#print axioms UnforcedLeray.Short.IIb.RawAndInletL4.inletIteratedL4Bound
