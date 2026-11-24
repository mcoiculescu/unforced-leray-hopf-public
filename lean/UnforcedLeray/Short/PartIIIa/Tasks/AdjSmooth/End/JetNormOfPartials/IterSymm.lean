import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_4
import UnforcedLeray.Units.B0121.WeakDeriv
import UnforcedLeray.Lib.Kernels.PlanarBS.Defs.Infra.Sobolev
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`, task `iterSymm`: symmetry of the iterated derivative

Proves `IterSymm` (defined in `Sub/PartIII-a_T21_2_7_2_1_2_1_4.lean`, SP 3060-3073, calculus only).
Route (a): multiply by a bump function equal to `1` near `p` and supported in `U`, giving a globally
`C^∞` function `G` with `G = F` near `p`. For global `C^∞` functions the `n`-th Fréchet derivative
applied to vectors is the iterated directional derivative along the list of vectors
(`siIter`), which only depends on the list up to permutation (`UnforcedLeray.B0121.iterDirDeriv_perm`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIIa

/-- The `n`-th Fréchet derivative of a global `C^∞` function on vectors is the iterated directional
derivative along the list of vectors. -/
theorem siIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → ℂ)
    (hG : ContDiff ℝ ∞ G) :
    ∀ (n : ℕ) (vs : Fin n → E) (x : E),
      iteratedFDeriv ℝ n G x vs = UnforcedLeray.PlanarBS.Sob.iterDirDeriv (List.ofFn vs) G x
  | 0, vs, x => by
    simp [UnforcedLeray.PlanarBS.Sob.iterDirDeriv]
  | n + 1, vs, x => by
    have ih := siIter G hG n
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n G) x :=
      hG.differentiable_iteratedFDeriv (by exact_mod_cast (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n))) x
    have hfun : UnforcedLeray.PlanarBS.Sob.iterDirDeriv (List.ofFn (fun i : Fin n => vs i.succ)) G =
        fun y => iteratedFDeriv ℝ n G y (fun i : Fin n => vs i.succ) :=
      funext fun y => (ih _ y).symm
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, UnforcedLeray.PlanarBS.Sob.iterDirDeriv_cons,
      UnforcedLeray.PlanarBS.Sob.dirDeriv, hfun, fderiv_continuousMultilinear_apply_const_apply hdiff]
    rfl

/-- Symmetry of the iterated derivative of a global `C^∞` function. -/
theorem siSymmGlobal (G : ℝ × (ℝ × ℝ) → ℂ) (hG : ContDiff ℝ ∞ G) (n : ℕ) (x : ℝ × (ℝ × ℝ))
    (v : Fin n → ℝ × (ℝ × ℝ)) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n G x (fun k => v (σ k)) = iteratedFDeriv ℝ n G x v := by
  rw [siIter G hG n (fun k => v (σ k)) x, siIter G hG n v x]
  exact congrFun (UnforcedLeray.B0121.iterDirDeriv_perm (Equiv.Perm.ofFn_comp_perm σ v) hG) x

/-- A `C^∞` function on an open set agrees near a point with a global `C^∞` function. -/
theorem siExt (F : ℝ × (ℝ × ℝ) → ℂ) (U : Set (ℝ × (ℝ × ℝ))) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ U) :
    ∃ G : ℝ × (ℝ × ℝ) → ℂ, ContDiff ℝ ∞ G ∧ G =ᶠ[nhds p] F := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
  let χ : ContDiffBump p :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  refine ⟨fun q => ((χ q : ℝ) : ℂ) * F q, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt.mul
        (hF.contDiffAt (hU.mem_nhds hx)))
    · have hx' : x ∉ tsupport χ := by
        rw [ContDiffBump.tsupport_eq]
        intro hmem
        exact hx (hball (Metric.closedBall_subset_ball (by show r / 2 < r; linarith) hmem))
      have hev : (fun q => ((χ q : ℝ) : ℂ) * F q) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx'] with q hq
        have h0 : χ q = 0 := by
          by_contra hne
          exact hq (subset_tsupport χ hne)
        simp [h0]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · filter_upwards [Metric.closedBall_mem_nhds p (by linarith : (0 : ℝ) < r / 4)] with q hq
    have h1 : χ q = 1 := χ.one_of_mem_closedBall hq
    simp [h1]

theorem iterSymm : UnforcedLeray.Short.IIIa.IterSymm := by
  intro n φ' U hU hF p hp σ v
  obtain ⟨G, hG, hGF⟩ := siExt (fun p => φ' p.1 p.2) U hU hF p hp
  have hEq : iteratedFDeriv ℝ n G p =
      iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hGF n).eq_of_nhds
  rw [← hEq]
  exact siSymmGlobal G hG n p v σ

end UnforcedLeray.Short.IIIa
