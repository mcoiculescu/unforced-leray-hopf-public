import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# Part I, task `PartI:T08/4/1/1/1` (`TrainErrJetLocalL2`): decomposition into leaves

Source `the November 2 reference manuscript` lines 261-288, 326-329.

`e(r) = v(r) - V_c(r)`. Smoothness of `e(r)` for `r > 0` comes from the smoothness of `v` and of
`V_c` (leaf `VcSmoothPos`). The `L²(cell)` bounds on word derivatives of `e` near `s` are reduced
to two leaves: the time-local `L²` bound for the velocity words (`VelJetLocalL2`, the positive-time
finite-energy regularity of the train, not yet in the library) and the same for `V_c`
(`VcJetLocalL2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- `V_c(r)` is smooth for every `r > 0` (proved below). -/
def VcSmoothPosE : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (Vc ν c r)

/-- Leaf: time-local `L²(cell)` bound on word derivatives of the velocity for `r` near `s > 0`. -/
def VelJetLocalL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ s : ℝ, 0 < s → ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ,
      ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2 ≤ K

/-- Leaf: time-local `L²(cell)` bound on word derivatives of `V_c` for `r` near `s > 0`. -/
def VcJetLocalL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ s : ℝ, 0 < s → ∀ (w : List Bool) (k : Fin 2),
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (wordComp w (Vc ν c r) k) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (wordComp w (Vc ν c r) k z) ^ 2 ≤ K

theorem vcSmoothPosE_proof : VcSmoothPosE := by
  intro ν c hν hc r hr
  have : 0 < width ν r := by simp only [UnforcedLeray.Train.width]; nlinarith
  exact UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc this

/-- Conditional proof of `TrainErrJetLocalL2` from the three leaves. -/
theorem trainErrJetLocalL2_of (hV : VcJetLocalL2) (hv : VelJetLocalL2) :
    TrainErrJetLocalL2 := by
  intro ν c hν hc tr htr
  have hc0 : 0 < c := by linarith
  refine ⟨fun r hr => ?_, fun s hs w k => ?_⟩
  · have hsm : ContDiff ℝ ∞ (tr.v r) :=
      TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hr.le
    exact hsm.sub (vcSmoothPosE_proof ν c hν hc0 r hr)
  · obtain ⟨ev, hev, Kv, hKv⟩ := hv ν c hν hc tr htr s hs w k
    obtain ⟨eW, heW, KW, hKW⟩ := hV ν c hν hc s hs w k
    refine ⟨min ev eW, lt_min hev heW, 2 * (Kv + KW), ?_⟩
    intro r hr hrs
    have hr1 : |r - s| < ev := lt_of_lt_of_le hrs (min_le_left _ _)
    have hr2 : |r - s| < eW := lt_of_lt_of_le hrs (min_le_right _ _)
    obtain ⟨m1, i1⟩ := hKv r hr hr1
    obtain ⟨m2, i2⟩ := hKW r hr hr2
    have hsm : ContDiff ℝ ∞ (tr.v r) :=
      TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hr.le
    have hVc : ContDiff ℝ ∞ (Vc ν c r) := vcSmoothPosE_proof ν c hν hc0 r hr
    have hcompV : ContDiff ℝ ∞ (fun x => tr.v r x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm
    have hcompW : ContDiff ℝ ∞ (fun x => Vc ν c r x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hVc
    have e : wordComp w (trainErr tr r) k =
        fun x => wordComp w (tr.v r) k x - wordComp w (Vc ν c r) k x := by
      funext x
      have h := derivWord_sub_smooth hcompV hcompW w x
      simpa [wordComp, trainErr] using h
    rw [e]
    refine ⟨m1.sub m2, ?_⟩
    set f := wordComp w (tr.v r) k
    set g := wordComp w (Vc ν c r) k
    have hf : Integrable (fun z => f z ^ 2) (Cyl.cellμ c) := m1.integrable_sq
    have hg : Integrable (fun z => g z ^ 2) (Cyl.cellμ c) := m2.integrable_sq
    have hfg : Integrable (fun z => (f z - g z) ^ 2) (Cyl.cellμ c) :=
      (m1.sub m2).integrable_sq
    have hpt : ∀ z, (f z - g z) ^ 2 ≤ 2 * f z ^ 2 + 2 * g z ^ 2 :=
      fun z => by nlinarith [sq_nonneg (f z + g z)]
    have hmono : ∫ z, (f z - g z) ^ 2 ∂(Cyl.cellμ c) ≤
        ∫ z, (2 * f z ^ 2 + 2 * g z ^ 2) ∂(Cyl.cellμ c) :=
      integral_mono hfg ((hf.const_mul 2).add (hg.const_mul 2)) hpt
    rw [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul,
      integral_const_mul] at hmono
    change ∫ z, (f z - g z) ^ 2 ∂(Cyl.cellμ c) ≤ _
    have i1' : ∫ z, f z ^ 2 ∂(Cyl.cellμ c) ≤ Kv := i1
    have i2' : ∫ z, g z ^ 2 ∂(Cyl.cellμ c) ≤ KW := i2
    linarith

end UnforcedLeray.Short.PartI
