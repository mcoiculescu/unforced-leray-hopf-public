import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetSupBridge
import UnforcedLeray.Lib.Cylinder.CellModes
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `PartI:T13` (`Sub/PartI_T13.lean`): exponential decay of the overlap fluctuation

Source of record: `the November 2 reference manuscript`, lines 304-313, 389-396
(old 354-362).

This module defines the two leaf obligations for `PartI:T13`:
* `OverlapFluctuationSmoothL2` (`PartI:T13/1`, source lines 304-313, 389-396)
* `OverlapFluctuationEnergyBalance` (`PartI:T13/2`, source lines 390-394)

and proves:
1. **Unit-cylinder Wirtinger gap for `jetEnergy`** (`PartI_T13.unitCyl_wirtinger_jetEnergy`):
   for `U : Plane → Vec` with `CellSmoothL2 1 U` and `W = hfluct 1 U` with `CellSmoothL2 1 W`,
   `4 * π² * jetEnergy 1 0 W ≤ jetEnergy 1 1 W`, proved from `Cyl.lintegral_cell_sub_qAvg_le`
   (`Lib/Cylinder/CellModes.lean`).
2. **Real-analysis Gronwall exponential decay** (`PartI_T13.overlapFluctuation_gronwall`):
   if `E(0) ≤ C₀` and `d/dT E(T) ≤ -2 * lam * E(T)` on `[0, ∞)`, then
   `E(T) ≤ C₀ * exp(-2 * lam * T)` for all `T ≥ 0`.
3. **1-step unit-cylinder `jetEnergy` interpolation** (`PartI_T13.jetEnergy_succ_le_unit`):
   for `f : Plane → Vec` with `CellSmoothL2 1 f`,
   `jetEnergy 1 (j + 1) f ≤ 2 * 2 ^ (j + 1) * 16 * √(jetEnergy 1 j f) * √(jetEnergy 1 (j + 2) f)`,
   proved from `cylGradInterpL2_proof` (`PartI:T07`) and `jsb_scalar_jet` (`JetSupBridge`).
4. **All-order `jetEnergy` exponential decay** (`PartI_T13.overlapFluctuation_jetEnergy_decay`) and
   **conditional assembly of `OverlapFluctuationDecay`** (`overlap_fluctuation_decay_of`),
   combining the `L²` base decay, induction on `j`, `jetL2Bridge_proof`, and `jetSupBridge_proof`
   from `OverlapFluctuationSmoothL2` (`PartI:T13/1`) and `OverlapFluctuationEnergyBalance`
   (`PartI:T13/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1. Leaves for `PartI:T13` -/

/-- **Leaf 1 (`PartI:T13/1`)**: smoothness, `L²` word-jet membership, and uniform word-jet energy
bound for the overlap horizontal fluctuation `W(T) = hfluct 1 (overlapField ν c tr.v T)` on the
unit cylinder (source lines 304-313, 389-396). -/
def OverlapFluctuationSmoothL2 : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 < c →
    ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
      ∀ T : ℝ, 0 ≤ T →
        let U := overlapField ν c tr.v T
        let W := hfluct 1 U
        CellSmoothL2 1 U ∧
        CellSmoothL2 1 W ∧
        ∀ j : ℕ, jetEnergy 1 j W ≤ 2 * 2 ^ j * (cellL2 1 (jet j U)).toReal ^ 2

/-- **Leaf 2 (`PartI:T13/2`)**: exact fluctuation energy identity on the unit cylinder
`(1/2) d/dT ‖W‖₂² + ‖∇W‖₂² = -e_c ∫ W₁ W₂ ∂_Y b` (using `\bar U₂ = 0` from
`trainMeanEquations_proof`) and shear-production bound
`|∫ W₁ W₂ ∂_Y b| ≤ (supNormD 1 U).toReal * ‖W‖₂²` (source lines 390-394). -/
def OverlapFluctuationEnergyBalance : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 < c →
    ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
      ∀ T : ℝ, 0 ≤ T →
        let U := overlapField ν c tr.v
        let W := fun t => hfluct 1 (U t)
        let b := fun Y => hmean 1 (U T) Y 0
        HasDerivAt (fun t => jetEnergy 1 0 (W t))
          (2 * (-jetEnergy 1 1 (W T) -
            eC ν c * ∫ z in Cyl.cell 1, W T z 0 * W T z 1 * deriv b z.2)) T ∧
        |∫ z in Cyl.cell 1, W T z 0 * W T z 1 * deriv b z.2| ≤
          (B0277.supNormD 1 (U T)).toReal * jetEnergy 1 0 (W T)

namespace PartI_T13

/-! ### 2. Unit-cylinder Wirtinger inequality for `hfluct 1 U` -/

private theorem qAvg_one_ofReal_eq_hmean (g : Plane → ℝ) (η : ℝ) :
    Cyl.qAvg 1 (fun z : Plane => Complex.ofReal (g z)) η = Complex.ofReal (hmean 1 g η) := by
  unfold Cyl.qAvg hmean
  simp only [Complex.ofReal_one, inv_one, one_mul, one_smul]
  rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact integral_ofReal

private theorem partialQ_ofReal (g : Plane → ℝ) (z : Plane) :
    Cyl.partialQ (fun w : Plane => Complex.ofReal (g w)) z = Complex.ofReal (Cyl.partialQ g z) := by
  unfold Cyl.partialQ
  change deriv (Complex.ofRealCLM ∘ fun x : ℝ => g (x, z.2)) z.1 =
    Complex.ofRealCLM (deriv (fun x : ℝ => g (x, z.2)) z.1)
  by_cases hd : DifferentiableAt ℝ (fun x : ℝ => g (x, z.2)) z.1
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt z.1 hd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hd, map_zero]
    apply deriv_zero_of_not_differentiableAt
    intro hdC
    apply hd
    have hre : (fun x : ℝ => g (x, z.2)) = Complex.reCLM ∘ (fun x : ℝ => Complex.ofReal (g (x, z.2))) :=
      rfl
    rw [hre]
    exact Complex.reCLM.differentiableAt.comp z.1 hdC

private theorem enorm_ofReal_eq (x : ℝ) : ‖Complex.ofReal x‖ₑ = ‖x‖ₑ := by
  simp [enorm_eq_nnnorm]

private theorem hfluct_apply_vec_unit {a : Plane → Vec} (ha : Continuous a) (z : Plane)
    (k : Fin 2) :
    (hfluct 1 a z) k = hfluct 1 (fun w => a w k) z := by
  have hint : Integrable (fun q : ℝ => a (q, z.2)) (volume.restrict (Ioc (-1 / 2) (1 / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hfluct hmean
  rw [PiLp.sub_apply, PiLp.smul_apply]
  congr 2
  simpa using h.symm

private theorem partialQ_hfluct_unit {g : Plane → ℝ} (hg : Differentiable ℝ g) (z : Plane) :
    Cyl.partialQ (hfluct 1 g) z = Cyl.partialQ g z := by
  unfold Cyl.partialQ hfluct
  have hd1 : HasDerivAt (fun x : ℝ => g (x, z.2)) (deriv (fun x : ℝ => g (x, z.2)) z.1) z.1 :=
    (hg.differentiableAt.comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))).hasDerivAt
  have hd2 : HasDerivAt (fun _ : ℝ => hmean 1 g z.2) 0 z.1 := hasDerivAt_const z.1 (hmean 1 g z.2)
  exact (hd1.sub hd2).deriv.trans (sub_zero _)

private theorem lintegral_enorm_sq_eq_ofReal_integral {g : Plane → ℝ}
    (hg : MemLp g 2 (Cyl.cellμ 1)) :
    ∫⁻ z in Cyl.cell 1, ‖g z‖ₑ ^ 2 = ENNReal.ofReal (∫ z in Cyl.cell 1, g z ^ 2) := by
  have hint : Integrable (fun z => g z ^ 2) (volume.restrict (Cyl.cell 1)) := hg.integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg (g z))]
  refine lintegral_congr fun z => ?_
  rw [UnforcedLeray.B0151.enorm_sq_eq, abs_of_nonneg (sq_nonneg (g z))]

private theorem wordsOfLength_zero_eq : wordsOfLength 0 = {[]} := by
  ext w
  rw [cgn_mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]

/-- **Unit-cylinder Wirtinger inequality for `jetEnergy`**:
for `U : Plane → Vec` with `CellSmoothL2 1 U` and `W = hfluct 1 U` with `CellSmoothL2 1 W`,
`4 * π² * jetEnergy 1 0 W ≤ jetEnergy 1 1 W`. -/
theorem unitCyl_wirtinger_jetEnergy {U : Plane → Vec} (hU : CellSmoothL2 1 U)
    (hW : CellSmoothL2 1 (hfluct 1 U)) :
    4 * Real.pi ^ 2 * jetEnergy 1 0 (hfluct 1 U) ≤ jetEnergy 1 1 (hfluct 1 U) := by
  set W := hfluct 1 U
  have hcomp_bound : ∀ k : Fin 2,
      4 * Real.pi ^ 2 * ∫ z in Cyl.cell 1, wordComp [] W k z ^ 2 ≤
        ∫ z in Cyl.cell 1, wordComp [true] W k z ^ 2 := by
    intro k
    let g : Plane → ℝ := fun z => U z k
    have hg_sm : ContDiff ℝ ∞ g :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hU.1
    have hg_c1 : ContDiff ℝ 1 (fun z : Plane => Complex.ofReal (g z)) :=
      (Complex.ofRealCLM.contDiff.comp hg_sm).of_le (by simp)
    have hg_per : Cyl.IsPeriodic 1 (fun z : Plane => Complex.ofReal (g z)) := by
      intro z
      exact congrArg Complex.ofReal (congrArg (fun v : Vec => v k) (hU.2.1 z))
    have hwirt := Cyl.lintegral_cell_sub_qAvg_le one_pos hg_c1 hg_per
    have hsub_eq : ∀ z : Plane,
        ‖Complex.ofReal (g z) - Cyl.qAvg 1 (fun w : Plane => Complex.ofReal (g w)) z.2‖ₑ =
          ‖wordComp [] W k z‖ₑ := by
      intro z
      rw [qAvg_one_ofReal_eq_hmean, ← Complex.ofReal_sub]
      have hWk : wordComp [] W k z = g z - hmean 1 g z.2 := by
        change W z k = g z - hmean 1 g z.2
        rw [hfluct_apply_vec_unit hU.1.continuous z k]
        rfl
      rw [hWk, enorm_ofReal_eq]
    have hpq_eq : ∀ z : Plane,
        ‖Cyl.partialQ (fun w : Plane => Complex.ofReal (g w)) z‖ₑ = ‖wordComp [true] W k z‖ₑ := by
      intro z
      rw [partialQ_ofReal, enorm_ofReal_eq]
      have hWk : (fun w : Plane => W w k) = hfluct 1 g := by
        funext w
        exact hfluct_apply_vec_unit hU.1.continuous w k
      have hd : wordComp [true] W k z = Cyl.partialQ g z := by
        change Cyl.partialQ (fun w => W w k) z = Cyl.partialQ g z
        rw [hWk, partialQ_hfluct_unit (hg_sm.differentiable (by simp)) z]
      rw [hd]
    simp_rw [hsub_eq, hpq_eq] at hwirt
    rw [lintegral_enorm_sq_eq_ofReal_integral (hW.2.2 [] k),
      lintegral_enorm_sq_eq_ofReal_integral (hW.2.2 [true] k),
      ← ENNReal.ofReal_mul (by positivity)] at hwirt
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg _))).1 hwirt
    have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hreal hpi.le
    have hcancel : 4 * Real.pi ^ 2 * ((1 / (2 * Real.pi)) ^ 2 *
        ∫ z in Cyl.cell 1, wordComp [true] W k z ^ 2) =
        ∫ z in Cyl.cell 1, wordComp [true] W k z ^ 2 := by
      have hne : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    linarith
  have hJ0 : jetEnergy 1 0 W =
      (∫ z in Cyl.cell 1, wordComp [] W 0 z ^ 2) +
        (∫ z in Cyl.cell 1, wordComp [] W 1 z ^ 2) := by
    unfold jetEnergy jetPair
    simp_rw [wordsOfLength_zero_eq, Finset.sum_singleton, Fin.sum_univ_two, ← sq]
    have hi0 : Integrable (fun z => wordComp [] W 0 z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hW.2.2 [] 0).integrable_sq
    have hi1 : Integrable (fun z => wordComp [] W 1 z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hW.2.2 [] 1).integrable_sq
    exact integral_add hi0 hi1
  have hJ1 : jetEnergy 1 1 W =
      ((∫ z in Cyl.cell 1, wordComp [true] W 0 z ^ 2) +
        (∫ z in Cyl.cell 1, wordComp [true] W 1 z ^ 2)) +
      ((∫ z in Cyl.cell 1, wordComp [false] W 0 z ^ 2) +
        (∫ z in Cyl.cell 1, wordComp [false] W 1 z ^ 2)) := by
    unfold jetEnergy jetPair
    have hsum : ∀ z : Plane,
        (∑ w ∈ wordsOfLength 1, ∑ k : Fin 2, wordComp w W k z * wordComp w W k z) =
          (wordComp [true] W 0 z ^ 2 + wordComp [true] W 1 z ^ 2) +
          (wordComp [false] W 0 z ^ 2 + wordComp [false] W 1 z ^ 2) := by
      intro z
      rw [gradInterp_sum_wordsOfLength_one, Fin.sum_univ_two, Fin.sum_univ_two]
      ring
    simp_rw [hsum]
    have hi_t0 : Integrable (fun z => wordComp [true] W 0 z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hW.2.2 [true] 0).integrable_sq
    have hi_t1 : Integrable (fun z => wordComp [true] W 1 z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hW.2.2 [true] 1).integrable_sq
    have hi_f0 : Integrable (fun z => wordComp [false] W 0 z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hW.2.2 [false] 0).integrable_sq
    have hi_f1 : Integrable (fun z => wordComp [false] W 1 z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hW.2.2 [false] 1).integrable_sq
    have hadd := integral_add (hi_t0.add hi_t1) (hi_f0.add hi_f1)
    dsimp only [Pi.add_apply] at hadd
    rw [hadd, integral_add hi_t0 hi_t1, integral_add hi_f0 hi_f1]
  have hf0 : 0 ≤ ∫ z in Cyl.cell 1, wordComp [false] W 0 z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hf1 : 0 ≤ ∫ z in Cyl.cell 1, wordComp [false] W 1 z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hb0 := hcomp_bound 0
  have hb1 := hcomp_bound 1
  rw [hJ0, hJ1, mul_add]
  linarith

/-! ### 3. Exponential Gronwall lemma on `[0, ∞)` -/

/-- **Exponential Gronwall inequality on `[0, ∞)`**:
if `E(0) ≤ C₀` and `d/dT E(T) ≤ -2 * lam * E(T)` for all `T ≥ 0`, then
`E(T) ≤ C₀ * exp(-(2 * lam * T))` for all `T ≥ 0`. -/
theorem overlapFluctuation_gronwall {E : ℝ → ℝ} {C₀ lam : ℝ}
    (hE0 : E 0 ≤ C₀)
    (hderiv : ∀ T : ℝ, 0 ≤ T → ∃ D : ℝ, HasDerivAt E D T ∧ D ≤ -(2 * lam) * E T) :
    ∀ T : ℝ, 0 ≤ T → E T ≤ C₀ * Real.exp (-(2 * lam * T)) := by
  let g : ℝ → ℝ := fun t => E t * Real.exp (2 * lam * t)
  have hg_step : ∀ t : ℝ, 0 ≤ t →
      ∃ G : ℝ, HasDerivAt g G t ∧ G ≤ 0 := by
    intro t ht0
    obtain ⟨D, hD, hDle⟩ := hderiv t ht0
    have hexp : HasDerivAt (fun s => Real.exp (2 * lam * s))
        (Real.exp (2 * lam * t) * (2 * lam * 1)) t :=
      HasDerivAt.exp ((hasDerivAt_id t).const_mul (2 * lam))
    refine ⟨D * Real.exp (2 * lam * t) + E t * (Real.exp (2 * lam * t) * (2 * lam * 1)),
      hD.mul hexp, ?_⟩
    have hexp_pos : 0 < Real.exp (2 * lam * t) := Real.exp_pos _
    nlinarith
  have hanti : AntitoneOn g (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      obtain ⟨G, hG, _⟩ := hg_step t ht
      exact hG.continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨G, hG, _⟩ := hg_step t (mem_Ici.1 (interior_subset ht))
      exact hG.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨G, hG, hGle⟩ := hg_step t (mem_Ici.1 (interior_subset ht))
      rwa [hG.deriv]
  intro T hT
  have hgT : g T ≤ g 0 := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hT) hT
  have hg0 : g 0 = E 0 := by simp [g]
  rw [hg0] at hgT
  have hgT' : E T * Real.exp (2 * lam * T) ≤ C₀ := hgT.trans hE0
  have hmul := mul_le_mul_of_nonneg_right hgT' (Real.exp_nonneg (-(2 * lam * T)))
  calc E T = E T * (Real.exp (2 * lam * T) * Real.exp (-(2 * lam * T))) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ = (E T * Real.exp (2 * lam * T)) * Real.exp (-(2 * lam * T)) := by ring
    _ ≤ C₀ * Real.exp (-(2 * lam * T)) := hmul

/-! ### 4. Unit-cylinder 1-step `jetEnergy` interpolation -/

/-- **1-step `jetEnergy` interpolation on the unit cylinder**:
for `f : Plane → Vec` with `CellSmoothL2 1 f` and any `j : ℕ`,
`jetEnergy 1 (j + 1) f ≤ 2 * 2 ^ (j + 1) * 16 * √(jetEnergy 1 j f) * √(jetEnergy 1 (j + 2) f)`. -/
theorem jetEnergy_succ_le_unit (j : ℕ) {f : Plane → Vec} (hf : CellSmoothL2 1 f) :
    jetEnergy 1 (j + 1) f ≤
      2 * 2 ^ (j + 1) * 16 * Real.sqrt (jetEnergy 1 j f) *
        Real.sqrt (jetEnergy 1 (j + 2) f) := by
  have hword : ∀ v ∈ wordsOfLength (j + 1), ∀ k : Fin 2,
      ∫ z in Cyl.cell 1, wordComp v f k z ^ 2 ≤
        16 * Real.sqrt (jetEnergy 1 j f) * Real.sqrt (jetEnergy 1 (j + 2) f) := by
    intro v hv k
    have hv_len : v.length = j + 1 := (jsb_mem_wordsOfLength.1 hv)
    rcases v with _ | ⟨b, w⟩
    · simp at hv_len
    have hw_len : w.length = j := by simpa using hv_len
    have hw_mem : w ∈ wordsOfLength j := jsb_mem_wordsOfLength.2 hw_len
    let g : Plane → ℝ := wordComp w f k
    have hk : ContDiff ℝ ∞ (fun x => f x k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hf.1
    have hgs : ContDiff ℝ ∞ g := B0151.contDiff_derivWord hk w
    have hper : Cyl.IsPeriodic 1 g := by
      apply jsb_periodic_derivWord 1 w
      intro y
      exact congrArg (fun u : Vec => u k) (hf.2.1 y)
    have hL2 : MemLp g 2 (Cyl.cellμ 1) := hf.2.2 w k
    have B1 := jsb_scalar_jet 1 j 1 f hf w hw_len k
    have B2 := jsb_scalar_jet 1 j 2 f hf w hw_len k
    have M1 : MemLp (Train.jet 1 g) 2 (Cyl.cellμ 1) :=
      jsb_memLp_jet 1 1 g hgs _ B1 ENNReal.ofReal_ne_top
    have M2 : MemLp (Train.jet 2 g) 2 (Cyl.cellμ 1) :=
      jsb_memLp_jet 1 2 g hgs _ B2 ENNReal.ofReal_ne_top
    have hgrad := cylGradInterpL2_proof 1 one_pos g hgs hper hL2 M1 M2
    have hA : Train.cellL2 1 g ≤ ENNReal.ofReal (Real.sqrt (jetEnergy 1 j f)) := by
      unfold Train.cellL2
      have e : eLpNorm (fun z => |g z|) 2 (Cyl.cellμ 1) = eLpNorm g 2 (Cyl.cellμ 1) := by
        simpa only [Real.norm_eq_abs] using eLpNorm_norm (p := 2) (μ := Cyl.cellμ 1) g
      rw [← e, jl2_abs_eLpNorm _ _ hL2]
      exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (jl2_energy_le 1 j f hf w hw_mem k))
    have hpt : ∀ z : Plane, |wordComp (b :: w) f k z| ≤ ‖Train.jet 1 g z‖ := by
      intro z
      have hbw : wordComp (b :: w) f k z = B0151.derivWord [b] g z := by
        cases b <;> rfl
      rw [hbw]
      exact (cylJetWord_proof g hgs 1 z).1 [b] rfl
    have hmono : eLpNorm (fun z => |wordComp (b :: w) f k z|) 2 (Cyl.cellμ 1) ≤
        Train.cellL2 1 (Train.jet 1 g) := by
      unfold Train.cellL2
      rw [← eLpNorm_norm (Train.jet 1 g)]
      exact eLpNorm_mono_real fun z => by
        simpa only [Real.norm_eq_abs, abs_abs, norm_norm] using hpt z
    have hsq_le : eLpNorm (fun z => |wordComp (b :: w) f k z|) 2 (Cyl.cellμ 1) ^ 2 ≤
        ENNReal.ofReal (16 * Real.sqrt (jetEnergy 1 j f) * Real.sqrt (jetEnergy 1 (j + 2) f)) := by
      calc eLpNorm (fun z => |wordComp (b :: w) f k z|) 2 (Cyl.cellμ 1) ^ 2
          ≤ Train.cellL2 1 (Train.jet 1 g) ^ 2 := by gcongr
        _ ≤ 4 * (Train.cellL2 1 g * Train.cellL2 1 (Train.jet 2 g)) := hgrad
        _ ≤ 4 * (ENNReal.ofReal (Real.sqrt (jetEnergy 1 j f)) *
              ENNReal.ofReal ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy 1 (j + 2) f))) := by
            gcongr
        _ = ENNReal.ofReal (16 * Real.sqrt (jetEnergy 1 j f) *
              Real.sqrt (jetEnergy 1 (j + 2) f)) := by
            have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
            rw [h4, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
    rw [jl2_abs_eLpNorm _ _ (hf.2.2 (b :: w) k), sq,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      Real.mul_self_sqrt (integral_nonneg fun z => sq_nonneg _)] at hsq_le
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).1 hsq_le
  have hint : ∀ (v : List Bool) (k : Fin 2),
      Integrable (fun z => wordComp v f k z * wordComp v f k z) (volume.restrict (Cyl.cell 1)) := by
    intro v k
    have hsq : Integrable (fun z => wordComp v f k z ^ 2) (volume.restrict (Cyl.cell 1)) :=
      (hf.2.2 v k).integrable_sq
    simpa only [sq] using hsq
  have hJ : jetEnergy 1 (j + 1) f =
      ∑ i ∈ wordsOfLength (j + 1) ×ˢ (Finset.univ : Finset (Fin 2)),
        ∫ z in Cyl.cell 1, wordComp i.1 f i.2 z ^ 2 := by
    unfold jetEnergy jetPair
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun k _ => hint v k)),
      Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint v k)]
    simp only [sq]
  have hcard : ((wordsOfLength (j + 1) ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) ≤
      2 * 2 ^ (j + 1) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hW : (wordsOfLength (j + 1)).card ≤ 2 ^ (j + 1) := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin (j + 1) → Bool)).card := Finset.card_image_le
        _ = 2 ^ (j + 1) := by simp
    have hW' : ((wordsOfLength (j + 1)).card : ℝ) ≤ 2 ^ (j + 1) := by exact_mod_cast hW
    push_cast
    linarith
  have hK_nn : 0 ≤ 16 * Real.sqrt (jetEnergy 1 j f) * Real.sqrt (jetEnergy 1 (j + 2) f) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  calc jetEnergy 1 (j + 1) f
      = ∑ i ∈ wordsOfLength (j + 1) ×ˢ (Finset.univ : Finset (Fin 2)),
          ∫ z in Cyl.cell 1, wordComp i.1 f i.2 z ^ 2 := hJ
    _ ≤ ∑ _i ∈ wordsOfLength (j + 1) ×ˢ (Finset.univ : Finset (Fin 2)),
          (16 * Real.sqrt (jetEnergy 1 j f) * Real.sqrt (jetEnergy 1 (j + 2) f)) :=
        Finset.sum_le_sum fun i hi => hword i.1 (Finset.mem_product.1 hi).1 i.2
    _ = ((wordsOfLength (j + 1) ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) *
          (16 * Real.sqrt (jetEnergy 1 j f) * Real.sqrt (jetEnergy 1 (j + 2) f)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * 2 ^ (j + 1)) *
          (16 * Real.sqrt (jetEnergy 1 j f) * Real.sqrt (jetEnergy 1 (j + 2) f)) :=
        mul_le_mul_of_nonneg_right hcard hK_nn
    _ = 2 * 2 ^ (j + 1) * 16 * Real.sqrt (jetEnergy 1 j f) *
          Real.sqrt (jetEnergy 1 (j + 2) f) := by ring

/-! ### 5. Base `L²` decay and inductive `jetEnergy` decay -/

/-- Base `j = 0` exponential decay of `jetEnergy 1 0 (hfluct 1 (overlapField ν c tr.v T))`. -/
theorem overlapFluctuation_jetEnergy_zero_decay
    (hSmooth : OverlapFluctuationSmoothL2) (hBal : OverlapFluctuationEnergyBalance)
    (hHN : OverlapHighNormUniform) (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    ∃ C₀ lam₀ ν₀ : ℝ, 0 < C₀ ∧ 0 < lam₀ ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ T : ℝ, 0 ≤ T →
            jetEnergy 1 0 (hfluct 1 (overlapField ν (trainPeriod ρ ν) tr.v T)) ≤
              C₀ * Real.exp (-(lam₀ * T)) := by
  obtain ⟨C₁, ν₁, hC₁, hν₁, hU₁⟩ := hHN ρ hρ 1
  let R : ℝ := max 2 (C₁ / (2 * Real.pi ^ 2))
  have hR_pos : 0 < R := lt_max_of_lt_left two_pos
  obtain ⟨νp, hνp, _, hp⟩ := trainPeriodAsymptotics_proof ρ hρ R hR_pos
  refine ⟨2 * C₁ ^ 2, 2 * Real.pi ^ 2, min (min ν₁ νp) (1 / 2),
    by positivity, by positivity, lt_min (lt_min hν₁ hνp) (by norm_num), ?_⟩
  intro ν hν hν_le tr htr T hT
  have hν_1 : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_p : ν ≤ νp := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc1 : 1 < c := by
    unfold c trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  obtain ⟨_, hνc2_ge⟩ := hp ν hν hν_p
  let U := overlapField ν c tr.v
  let W := fun t => hfluct 1 (U t)
  have hE0 : jetEnergy 1 0 (W 0) ≤ 2 * C₁ ^ 2 := by
    have hsm0 := (hSmooth ν c hν hc1 tr htr 0 le_rfl).2.2 0
    have hU0 := (hU₁ ν hν hν_1 tr htr 0 le_rfl 0 (Nat.zero_le 1)).1
    have htoReal : (cellL2 1 (jet 0 (U 0))).toReal ≤ C₁ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU0
      rwa [ENNReal.toReal_ofReal hC₁.le] at this
    have hsq : (cellL2 1 (jet 0 (U 0))).toReal ^ 2 ≤ C₁ ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg htoReal 2
    simpa using hsm0.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
  have hderiv : ∀ t : ℝ, 0 ≤ t →
      ∃ D : ℝ, HasDerivAt (fun s => jetEnergy 1 0 (W s)) D t ∧
        D ≤ -(2 * Real.pi ^ 2) * jetEnergy 1 0 (W t) := by
    intro t ht
    obtain ⟨hUs, hWs, _⟩ := hSmooth ν c hν hc1 tr htr t ht
    obtain ⟨hd, hprod⟩ := hBal ν c hν hc1 tr htr t ht
    have hwirt : 4 * Real.pi ^ 2 * jetEnergy 1 0 (W t) ≤ jetEnergy 1 1 (W t) :=
      unitCyl_wirtinger_jetEnergy hUs hWs
    have hUt1 := (hU₁ ν hν hν_1 tr htr t ht 1 le_rfl).2
    have hsup_le : (B0277.supNormD 1 (U t)).toReal ≤ C₁ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUt1
      rwa [ENNReal.toReal_ofReal hC₁.le] at this
    have heC_C1 : eC ν c * C₁ ≤ 2 * Real.pi ^ 2 := by
      unfold eC
      have hR_le : C₁ / (2 * Real.pi ^ 2) ≤ ν * c ^ 2 :=
        (le_max_right 2 _).trans hνc2_ge
      have hpi2 : 0 < 2 * Real.pi ^ 2 := by positivity
      have hνc2_pos : 0 < ν * c ^ 2 := lt_of_lt_of_le hR_pos hνc2_ge
      rw [inv_mul_le_iff₀ hνc2_pos]
      exact (div_le_iff₀ hpi2).1 hR_le
    have heC_nn : 0 ≤ eC ν c := by unfold eC; positivity
    have hJ0_nn : 0 ≤ jetEnergy 1 0 (W t) := jetEnergy_nonneg 1 0 (W t)
    set I := ∫ z in Cyl.cell 1, W t z 0 * W t z 1 * deriv (fun Y => hmean 1 (U t) Y 0) z.2
    have hI_bound : -(eC ν c * I) ≤ 2 * Real.pi ^ 2 * jetEnergy 1 0 (W t) := by
      calc -(eC ν c * I) ≤ eC ν c * |I| := by
            have := neg_le_abs I
            nlinarith
        _ ≤ eC ν c * ((B0277.supNormD 1 (U t)).toReal * jetEnergy 1 0 (W t)) :=
            mul_le_mul_of_nonneg_left hprod heC_nn
        _ ≤ eC ν c * (C₁ * jetEnergy 1 0 (W t)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsup_le hJ0_nn) heC_nn
        _ = (eC ν c * C₁) * jetEnergy 1 0 (W t) := by ring
        _ ≤ 2 * Real.pi ^ 2 * jetEnergy 1 0 (W t) :=
            mul_le_mul_of_nonneg_right heC_C1 hJ0_nn
    change HasDerivAt (fun s => jetEnergy 1 0 (W s))
      (2 * (-jetEnergy 1 1 (W t) - eC ν c * I)) t at hd
    have hpiJ0 : 0 ≤ Real.pi ^ 2 * jetEnergy 1 0 (W t) :=
      mul_nonneg (sq_nonneg _) hJ0_nn
    refine ⟨2 * (-jetEnergy 1 1 (W t) - eC ν c * I), hd, ?_⟩
    linarith
  have hgron := overlapFluctuation_gronwall (lam := Real.pi ^ 2) hE0 hderiv T hT
  simpa [mul_assoc] using hgron

/-- Inductive exponential decay of `jetEnergy 1 j (hfluct 1 (overlapField ν c tr.v T))`
for every `j : ℕ`. -/
theorem overlapFluctuation_jetEnergy_decay
    (hSmooth : OverlapFluctuationSmoothL2) (hBal : OverlapFluctuationEnergyBalance)
    (hHN : OverlapHighNormUniform) (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ Cj lamj νj : ℝ, 0 < Cj ∧ 0 < lamj ∧ 0 < νj ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ νj →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ T : ℝ, 0 ≤ T →
            jetEnergy 1 j (hfluct 1 (overlapField ν (trainPeriod ρ ν) tr.v T)) ≤
              Cj * Real.exp (-(lamj * T)) := by
  induction j with
  | zero => exact overlapFluctuation_jetEnergy_zero_decay hSmooth hBal hHN ρ hρ
  | succ j ih =>
    obtain ⟨Cj, lamj, νj, hCj, hlamj, hνj, hIj⟩ := ih
    obtain ⟨CM, νM, hCM, hνM, hUM⟩ := hHN ρ hρ (j + 2)
    let M : ℝ := 2 * 2 ^ (j + 2) * CM ^ 2
    have hM_pos : 0 < M := by positivity
    let C_next : ℝ := 2 * 2 ^ (j + 1) * 16 * Real.sqrt Cj * Real.sqrt M
    refine ⟨C_next, lamj / 2, min (min νj νM) (1 / 2),
      by positivity, by positivity, lt_min (lt_min hνj hνM) (by norm_num), ?_⟩
    intro ν hν hν_le tr htr T hT
    have hν_j : ν ≤ νj := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hν_M : ν ≤ νM := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
    let c := trainPeriod ρ ν
    have hc1 : 1 < c := by
      unfold c trainPeriod
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
    let U := overlapField ν c tr.v T
    let W := hfluct 1 U
    obtain ⟨_, hWs, hWj_bound⟩ := hSmooth ν c hν hc1 tr htr T hT
    have hJj := hIj ν hν hν_j tr htr T hT
    have hU_j2 := (hUM ν hν hν_M tr htr T hT (j + 2) le_rfl).1
    have htoReal : (cellL2 1 (jet (j + 2) U)).toReal ≤ CM := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU_j2
      rwa [ENNReal.toReal_ofReal hCM.le] at this
    have hJj2 : jetEnergy 1 (j + 2) W ≤ M := by
      calc jetEnergy 1 (j + 2) W
          ≤ 2 * 2 ^ (j + 2) * (cellL2 1 (jet (j + 2) U)).toReal ^ 2 := hWj_bound (j + 2)
        _ ≤ 2 * 2 ^ (j + 2) * CM ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ ENNReal.toReal_nonneg htoReal 2) (by positivity)
    have hsqrt_j : Real.sqrt (jetEnergy 1 j W) ≤ Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
      calc Real.sqrt (jetEnergy 1 j W)
          ≤ Real.sqrt (Cj * Real.exp (-(lamj * T))) := Real.sqrt_le_sqrt hJj
        _ = Real.sqrt Cj * Real.sqrt (Real.exp (-(lamj * T))) := Real.sqrt_mul hCj.le _
        _ = Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
            congr 1
            ring
    have hsqrt_j2 : Real.sqrt (jetEnergy 1 (j + 2) W) ≤ Real.sqrt M := Real.sqrt_le_sqrt hJj2
    calc jetEnergy 1 (j + 1) W
        ≤ 2 * 2 ^ (j + 1) * 16 * Real.sqrt (jetEnergy 1 j W) *
            Real.sqrt (jetEnergy 1 (j + 2) W) := jetEnergy_succ_le_unit j hWs
      _ ≤ 2 * 2 ^ (j + 1) * 16 * (Real.sqrt Cj * Real.exp (-(lamj / 2 * T))) * Real.sqrt M := by
          gcongr
      _ = C_next * Real.exp (-(lamj / 2 * T)) := by
          unfold C_next
          ring

end PartI_T13

/-- **Conditional proof of `OverlapFluctuationDecay` (`PartI:T13`)** (source lines 304-313,
389-396): combines `OverlapFluctuationSmoothL2`, `OverlapFluctuationEnergyBalance`, and
`OverlapHighNormUniform`. -/
theorem overlap_fluctuation_decay_of
    (hSmooth : OverlapFluctuationSmoothL2) (hBal : OverlapFluctuationEnergyBalance)
    (hHN : OverlapHighNormUniform) : OverlapFluctuationDecay := by
  intro ρ hρ j
  obtain ⟨Cj, lamj, νj, hCj, hlamj, hνj, hEj⟩ :=
    PartI_T13.overlapFluctuation_jetEnergy_decay hSmooth hBal hHN ρ hρ j
  obtain ⟨CM, νM, hCM, hνM, hUM⟩ := hHN ρ hρ (j + 2)
  obtain ⟨CL2, hCL2, hBrL2⟩ := jetL2Bridge_proof j
  obtain ⟨CSup, hCSup, hBrSup⟩ := jetSupBridge_proof j
  let M : ℝ := 2 * 2 ^ (j + 2) * CM ^ 2
  have hM_pos : 0 < M := by positivity
  let C_L2 : ℝ := (CL2 + 1) * Real.sqrt Cj
  let C_Sup : ℝ := 2 * (CSup + 1) * (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ)
  refine ⟨max C_L2 C_Sup, lamj / 4, min (min νj νM) (1 / 2),
    lt_max_of_lt_left (by positivity), by positivity,
    lt_min (lt_min hνj hνM) (by norm_num), ?_⟩
  intro ν hν hν_le tr htr T hT
  have hν_j : ν ≤ νj := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_M : ν ≤ νM := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc1 : 1 < c := by
    unfold c trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  let U := overlapField ν c tr.v T
  let W := hfluct 1 U
  obtain ⟨_, hWs, hW_bound⟩ := hSmooth ν c hν hc1 tr htr T hT
  have hJj := hEj ν hν hν_j tr htr T hT
  have hsqrt_j : Real.sqrt (jetEnergy 1 j W) ≤ Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
    calc Real.sqrt (jetEnergy 1 j W)
        ≤ Real.sqrt (Cj * Real.exp (-(lamj * T))) := Real.sqrt_le_sqrt hJj
      _ = Real.sqrt Cj * Real.sqrt (Real.exp (-(lamj * T))) := Real.sqrt_mul hCj.le _
      _ = Real.sqrt Cj * Real.exp (-(lamj / 2 * T)) := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
          congr 1
          ring
  have hexp_half_le_quarter : Real.exp (-(lamj / 2 * T)) ≤ Real.exp (-(lamj / 4 * T)) := by
    apply Real.exp_le_exp.2
    linarith [mul_nonneg hlamj.le hT]
  have hM_bound : ∀ k : ℕ, k ≤ j + 2 → jetEnergy 1 k W ≤ M := by
    intro k hk
    have hUk := (hUM ν hν hν_M tr htr T hT k hk).1
    have htoReal : (cellL2 1 (jet k U)).toReal ≤ CM := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUk
      rwa [ENNReal.toReal_ofReal hCM.le] at this
    have hpow2 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (j + 2) :=
      pow_le_pow_right₀ (by norm_num) hk
    calc jetEnergy 1 k W
        ≤ 2 * 2 ^ k * (cellL2 1 (jet k U)).toReal ^ 2 := hW_bound k
      _ ≤ 2 * 2 ^ (j + 2) * CM ^ 2 := by
          apply mul_le_mul
          · linarith
          · exact pow_le_pow_left₀ ENNReal.toReal_nonneg htoReal 2
          · exact sq_nonneg _
          · positivity
  refine ⟨?_, ?_⟩
  · -- `cellL2 1 (jet j W)` bound
    have hL2 := hBrL2 1 le_rfl W hWs
    refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
    calc CL2 * Real.sqrt (jetEnergy 1 j W)
        ≤ (CL2 + 1) * (Real.sqrt Cj * Real.exp (-(lamj / 2 * T))) := by
          apply mul_le_mul (by linarith) hsqrt_j (Real.sqrt_nonneg _) (by linarith)
      _ = C_L2 * Real.exp (-(lamj / 2 * T)) := by unfold C_L2; ring
      _ ≤ C_L2 * Real.exp (-(lamj / 4 * T)) :=
          mul_le_mul_of_nonneg_left hexp_half_le_quarter (by positivity)
      _ ≤ max C_L2 C_Sup * Real.exp (-(lamj / 4 * T)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · -- `supNormD j W` bound
    have hSup := (hBrSup 1 le_rfl W hWs).2
    refine hSup.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsqrt_j1 : Real.sqrt (jetEnergy 1 (j + 1) W) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt (hM_bound (j + 1) (by omega))
    have hsqrt_j2 : Real.sqrt (jetEnergy 1 (j + 2) W) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt (hM_bound (j + 2) le_rfl)
    have hrpow_bound : ∀ K : ℝ, 0 ≤ K → Real.sqrt K ≤ Real.sqrt M →
        (Real.sqrt (jetEnergy 1 j W) * Real.sqrt K) ^ (1 / 2 : ℝ) ≤
          (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) * Real.exp (-(lamj / 4 * T)) := by
      intro K _ hK
      have hprod : Real.sqrt (jetEnergy 1 j W) * Real.sqrt K ≤
          (Real.sqrt Cj * Real.sqrt M) * Real.exp (-(lamj / 2 * T)) := by
        calc Real.sqrt (jetEnergy 1 j W) * Real.sqrt K
            ≤ (Real.sqrt Cj * Real.exp (-(lamj / 2 * T))) * Real.sqrt M :=
              mul_le_mul hsqrt_j hK (Real.sqrt_nonneg _) (by positivity)
          _ = (Real.sqrt Cj * Real.sqrt M) * Real.exp (-(lamj / 2 * T)) := by ring
      calc (Real.sqrt (jetEnergy 1 j W) * Real.sqrt K) ^ (1 / 2 : ℝ)
          ≤ ((Real.sqrt Cj * Real.sqrt M) * Real.exp (-(lamj / 2 * T))) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
              hprod (by norm_num)
        _ = (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) *
              (Real.exp (-(lamj / 2 * T))) ^ (1 / 2 : ℝ) :=
            Real.mul_rpow (by positivity) (Real.exp_nonneg _)
        _ = (Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) * Real.exp (-(lamj / 4 * T)) := by
            congr 1
            rw [← Real.exp_mul]
            congr 1
            ring
    have hb1 := hrpow_bound (jetEnergy 1 (j + 1) W) (jetEnergy_nonneg 1 (j + 1) W) hsqrt_j1
    have hb2 := hrpow_bound (jetEnergy 1 (j + 2) W) (jetEnergy_nonneg 1 (j + 2) W) hsqrt_j2
    unfold supRhs
    rw [Real.one_rpow, one_mul]
    calc CSup * ((Real.sqrt (jetEnergy 1 j W) * Real.sqrt (jetEnergy 1 (j + 2) W)) ^ (1 / 2 : ℝ) +
            (Real.sqrt (jetEnergy 1 j W) * Real.sqrt (jetEnergy 1 (j + 1) W)) ^ (1 / 2 : ℝ))
        ≤ (CSup + 1) * (2 * ((Real.sqrt Cj * Real.sqrt M) ^ (1 / 2 : ℝ) *
            Real.exp (-(lamj / 4 * T)))) := by
          apply mul_le_mul (by linarith) (by linarith)
            (add_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _))
            (by linarith)
      _ = C_Sup * Real.exp (-(lamj / 4 * T)) := by unfold C_Sup; ring
      _ ≤ max C_L2 C_Sup * Real.exp (-(lamj / 4 * T)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

end UnforcedLeray.Short.PartI
