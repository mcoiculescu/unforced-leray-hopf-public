import UnforcedLeray.Short.PartI.Sub.T08Statement
import UnforcedLeray.Short.PartI.Tasks.TrainErrorEquation
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity

/-!
# Part I, task `PartI:T08/1` (`TrainErrBasic`): decomposition

Source: `the November 2 reference manuscript` lines 261-288 (train in `BUC`),
294 (`V_c^p`), 326-329 (`Q_c`).

Proved here: smoothness, periodicity, divergence of `e = v - V_c^p`, smoothness of `V_c^p`, and the
boundedness of the words of `e` from the boundedness of the words of `v` (leaf `TrainWordBounded`).
Leaves: `TrainWordBounded`, `QcSmooth`, `QcPeriodic`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf (bounded words of the train velocity)** (lines 270-288: `BUC`: all spatial derivatives
bounded on `[0, S]`). For a train of the BUC class and `s ≥ 0`, every word derivative of every
component of `v(s)` is bounded. Route: `IsBUCTrain.deriv_bound` at `S = s`, `cylJetWord_proof`
(`|∂_w g| ≤ ‖D^{|w|} g‖`) for `g = (EuclideanSpace.proj k) ∘ v(s)`, and
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le`-type bound `‖D^l (π_k ∘ v)‖ ≤ ‖D^l v‖`. -/
def TrainWordBounded : Prop :=
  ∀ ν c : ℝ, ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
    ∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w (tr.v s) k z| ≤ M

/-- **Leaf (smoothness of `Q_c`)** (lines 326-329; `Qc_fun_eq`, `B0146.crossStress_fun`:
`Q_kl = latticeSum u_k · latticeSum u_l - latticeSum (u_k u_l)`, lattice sums of Gaussian profiles
are smooth, `B0147.GP.derivWord_lattice`, `B0146.hasDerivAt_latticeSum_x/_y`,
`B0151.contDiff_derivWord`). -/
def QcSmooth : Prop :=
  ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Qc ν c s z k l)

/-- **Leaf (periodicity of `Q_c`)**: `c`-periodic (reindex `n ↦ n + 1` in `B0146.latticeSum`,
`B0146.shift`). -/
def QcPeriodic : Prop :=
  ∀ ν c s : ℝ, ∀ k l : Fin 2, Cyl.IsPeriodic c (fun z => Qc ν c s z k l)

theorem derivWord_sub_smooth {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ∀ (w : List Bool) (z : Plane),
      B0151.derivWord w (fun x => f x - g x) z = B0151.derivWord w f z - B0151.derivWord w g z
  | [], z => rfl
  | true :: w, z => by
      have h1 := B0151.contDiff_derivWord hf w
      have h2 := B0151.contDiff_derivWord hg w
      have h3 := B0151.contDiff_derivWord (hf.sub hg) w
      have e : B0151.derivWord w (fun x => f x - g x) =
          fun x => B0151.derivWord w f x - B0151.derivWord w g x := funext (derivWord_sub_smooth hf hg w)
      show GaussianVortex.partialX (B0151.derivWord w (fun x => f x - g x)) z = _
      rw [e]
      rw [B0151.partialX_eq_fderiv ((h1.sub h2).differentiable (by simp))]
      rw [fderiv_fun_sub (h1.differentiable (by simp) z) (h2.differentiable (by simp) z)]
      rw [ContinuousLinearMap.sub_apply]
      rw [← B0151.partialX_eq_fderiv (h1.differentiable (by simp)),
        ← B0151.partialX_eq_fderiv (h2.differentiable (by simp))]
      rfl
  | false :: w, z => by
      have h1 := B0151.contDiff_derivWord hf w
      have h2 := B0151.contDiff_derivWord hg w
      have e : B0151.derivWord w (fun x => f x - g x) =
          fun x => B0151.derivWord w f x - B0151.derivWord w g x := funext (derivWord_sub_smooth hf hg w)
      show GaussianVortex.partialY (B0151.derivWord w (fun x => f x - g x)) z = _
      rw [e]
      rw [B0151.partialY_eq_fderiv ((h1.sub h2).differentiable (by simp))]
      rw [fderiv_fun_sub (h1.differentiable (by simp) z) (h2.differentiable (by simp) z)]
      rw [ContinuousLinearMap.sub_apply]
      rw [← B0151.partialY_eq_fderiv (h1.differentiable (by simp)),
        ← B0151.partialY_eq_fderiv (h2.differentiable (by simp))]
      rfl

theorem trainErrBasic_of (h1 : TrainWordBounded) (h2 : QcSmooth) (h3 : QcPeriodic) :
    TrainErrBasic := by
  intro ν c hν hc tr htr s hs hac
  have hc0 : 0 < c := by linarith
  have hνs : 0 ≤ ν * s := (mul_pos hν hs).le
  have ha1 : 1 ≤ width ν s := by simp only [Train.width]; linarith
  have hw : 0 < width ν s := by linarith
  have hv : ContDiff ℝ ∞ (tr.v s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs.le
  have hV : ContDiff ℝ ∞ (Vc ν c s) := Spine.vcReg_contDiff_Vc hc0 hw
  have he : ContDiff ℝ ∞ (trainErr tr s) := hv.sub hV
  refine ⟨he, ?_, ?_, ?_, hV, fun k l => h2 ν c s hν hc0 hs.le k l, fun k l => h3 ν c s k l⟩
  · intro z
    simp only [trainErr]
    rw [tr.isTrain.periodic_v s hs.le z, Train.Vc_periodic ν c s z]
  · intro z
    have hvk : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => tr.v s x k) := fun k =>
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
    have hVk : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => Vc ν c s x k) := fun k =>
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV
    have hdiv := tr.isTrain.solenoidal s hs.le z
    have hdV := Train.Vc_div hν hc0.ne' hs.le z
    have key : ∀ k : Fin 2, ∀ β : Bool, B0151.derivWord [β] (fun x => trainErr tr s x k) z =
        B0151.derivWord [β] (fun x => tr.v s x k) z - B0151.derivWord [β] (fun x => Vc ν c s x k) z :=
      fun k β => derivWord_sub_smooth (hvk k) (hVk k) [β] z
    unfold Cyl.divergence at hdiv hdV ⊢
    have hQ : Cyl.partialQ (fun w => trainErr tr s w 0) z =
        Cyl.partialQ (fun w => tr.v s w 0) z - Cyl.partialQ (fun w => Vc ν c s w 0) z := key 0 true
    have hE : Cyl.partialEta (fun w => trainErr tr s w 1) z =
        Cyl.partialEta (fun w => tr.v s w 1) z - Cyl.partialEta (fun w => Vc ν c s w 1) z := key 1 false
    rw [hQ, hE]
    linarith
  · intro w k
    obtain ⟨M1, hM1⟩ := h1 ν c tr htr s hs.le w k
    obtain ⟨C, -, hC⟩ := Vc_word_bound w.length
    refine ⟨M1 + C * width ν s ^ (-(3 + (w.length : ℝ)) / 2), fun z => ?_⟩
    have hvk : ContDiff ℝ ∞ (fun x => tr.v s x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
    have hVk : ContDiff ℝ ∞ (fun x => Vc ν c s x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV
    have := derivWord_sub_smooth hvk hVk w z
    have e : wordComp w (trainErr tr s) k z =
        wordComp w (tr.v s) k z - wordComp w (Vc ν c s) k z := this
    rw [e]
    calc _ ≤ |wordComp w (tr.v s) k z| + |wordComp w (Vc ν c s) k z| := abs_sub _ _
      _ ≤ _ := add_le_add (hM1 z) (hC ν c s hc0 ha1 hac w rfl k z)

end UnforcedLeray.Short.PartI
