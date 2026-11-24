import UnforcedLeray.Short.PartI.Sub.PartI_T08_1

/-!
# Part I, task `PartI:T08/2` (`TrainErrJetL2`): decomposition

Source: `the November 2 reference manuscript` lines 261-288 (datum in `BUC ∩ H^k`
for every `k`; the train is the finite-energy mild solution; "Approximation and transverse cutoffs
then give the velocity and vorticity energy identities"), line 294 (`V_c^p`), line 344 (`E_N`
finite).

`e = v - V_c^p`; a word derivative of `e` is the difference of those of `v` and `V_c^p`.
Leaves: `VcWordL2` (Haiku) and `TrainVelocityJetL2` (the energy argument for the train).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- **Leaf (L² of the word derivatives of `V_c^p`)** (lines 326-329). From `Train.Vc_bounds` with
weight `m = 1`: `|∂_w Vc_k| (1 + η²/a) ≤ C a^{-(3+|w|)/2}`, and `(1+η²/a)^{-2}` is integrable in `η`
(`∫ = O(√a)`) over the cell of width `c`. -/
def VcWordL2 : Prop :=
  ∀ ν c s : ℝ, 0 < c → 1 ≤ width ν s → width ν s ≤ c ^ 2 →
    ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (Vc ν c s) k) 2 (Cyl.cellμ c)

/-- **Leaf (L² of the word derivatives of the train velocity)** (lines 261-288, 344).
At every age `s > 0` of a BUC train, every word derivative of every component of `v(s)` is in
`L²` of one cell. This is the cutoff-energy argument: the datum is in `H^∞`
(`Train.jet_datum`); for `g = ∂_w v` the cutoff energy `∫ χ_R |g|²` satisfies
`d/dt + 2ν ∫ χ_R |∇g|² ≤ C(M_s) ∫ χ_R |D^{≤|w|} v|² + O(1/R)` by induction on `|w|`
(the pressure term is `-∫ (∇χ_R · g) ∂_w p`), Gronwall, `R → ∞`. -/
def TrainVelocityJetL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (tr.v s) k) 2 (Cyl.cellμ c)

theorem trainErrJetL2_of (h1 : VcWordL2) (h2 : TrainVelocityJetL2) : TrainErrJetL2 := by
  intro ν c hν hc tr htr s hs hac w k
  have hc0 : 0 < c := by linarith
  have hνs : 0 ≤ ν * s := (mul_pos hν hs).le
  have ha1 : 1 ≤ width ν s := by simp only [Train.width]; linarith
  have hw : 0 < width ν s := by linarith
  have hv : ContDiff ℝ ∞ (tr.v s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs.le
  have hV : ContDiff ℝ ∞ (Vc ν c s) := Spine.vcReg_contDiff_Vc hc0 hw
  have hvk : ContDiff ℝ ∞ (fun x => tr.v s x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hVk : ContDiff ℝ ∞ (fun x => Vc ν c s x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV
  have e : wordComp w (trainErr tr s) k =
      fun z => wordComp w (tr.v s) k z - wordComp w (Vc ν c s) k z :=
    funext fun z => derivWord_sub_smooth hvk hVk w z
  rw [e]
  exact (h2 ν c hν hc tr htr s hs hac w k).sub (h1 ν c s hc0 ha1 hac w k)

end UnforcedLeray.Short.PartI
