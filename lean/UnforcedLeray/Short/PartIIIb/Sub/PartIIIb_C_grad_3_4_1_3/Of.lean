import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.HpS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.HpX
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.MixedS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.MixedX
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.PsiS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.SSecond
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.XSecond
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# `PartIII-b:C/grad/3/4/1/3`: `GradLatticeSmooth` from the three Gaussian-majorant leaves

Source `the November 2 reference manuscript`
4963-4980 (lattice sums `h^p_A, ψ^p_A`), 5036-5039, 5063-5079 ("the sums and their required
derivatives converge by Gaussian decay").  The lattice terms depend on `A` only through
`A^y(s')`, so a smooth cutoff of `A^y` near `s` (where `A^y` is `C²`) reduces the claim to the
global-regularity versions `*_glob` (files `HpS, HpX, MixedS, MixedX, PsiS, SSecond, XSecond` in
this folder, obtained from the proved `Sub/PartIII-b_C_grad_2/*` and `SPart` by replacing
`IsAffElem A` with `ContDiffOn ℝ 2 (Ay ν χf A) (Ioi 0)`).

Proved: `gradLatticeSmooth_of (HpTermMajorant) (PAMXSVBound) (PAMXBallMajor)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Smooth cutoff of a function that is `C²` at `s > 0`: a function `C²` on `(0,∞)` agreeing with
it near `s`. -/
theorem exists_cutoff (g : ℝ → Mat3) (s : ℝ) (h : ContDiffAt ℝ 2 g s) :
    ∃ g' : ℝ → Mat3, ContDiffOn ℝ 2 g' (Ioi 0) ∧ ∀ᶠ t in 𝓝 s, g' t = g t := by
  have hev : ∀ᶠ y in 𝓝 s, ContDiffAt ℝ 2 g y := h.eventually (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  let f : ContDiffBump s := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun t => f t • g t, ?_, ?_⟩
  · intro t _
    by_cases ht : t ∈ Metric.closedBall s (ε / 2)
    · have hgt : ContDiffAt ℝ 2 g t := hball t (by
        rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at ht; linarith)
      exact ((f.contDiff.contDiffAt).smul hgt).contDiffWithinAt
    · have hnot : t ∉ tsupport f := by
        rw [f.tsupport_eq]; exact ht
      have h0 : f =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
      have h1 : (fun t => f t • g t) =ᶠ[𝓝 t] fun _ => (0 : Mat3) := by
        filter_upwards [h0] with u hu
        simp [hu]
      exact (contDiffAt_const.congr_of_eventuallyEq h1).contDiffWithinAt
  · filter_upwards [Metric.ball_mem_nhds s (by positivity : (0:ℝ) < ε / 4)] with t ht
    have : f t = 1 := f.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall]; exact (Metric.mem_ball.mp ht).le)
    simp [this]

theorem Ay_one (ν : ℝ) (g : ℝ → Mat3) : Ay ν (fun _ => (1 : ℝ)) g = g := by
  funext t; simp [Ay]

theorem psipA_congr (ν : ℝ) (χ χ' : ℝ → ℝ) (A A' : ℝ → Mat3) (t : ℝ)
    (h : Ay ν χ A t = Ay ν χ' A' t) : psipA ν χ A t = psipA ν χ' A' t := by
  funext x; unfold psipA; rw [h]

theorem hpA_congr (ν : ℝ) (χ χ' : ℝ → ℝ) (A A' : ℝ → Mat3) (t : ℝ)
    (h : Ay ν χ A t = Ay ν χ' A' t) : hpA ν χ A t = hpA ν χ' A' t := by
  funext x; unfold hpA; rw [h]

theorem gradLatticeSmooth_of (h1 : HpTermMajorant) (h2 : PAMXSVBound) (h3 : PAMXBallMajor) :
    GradLatticeSmooth := by
  intro ν s χf A hd x u hu
  obtain ⟨hν, hν1, hs, hsT, hA⟩ := hd
  obtain ⟨g', hg', hgev⟩ := exists_cutoff (Ay ν χf A) s hA
  set A' : ℝ → Mat3 := g' with hA'
  have hC : ContDiffOn ℝ 2 (Ay ν (fun _ => (1 : ℝ)) A') (Ioi 0) := by
    rw [Ay_one]; exact hg'
  have hAy : ∀ᶠ t in 𝓝 s, Ay ν χf A t = Ay ν (fun _ => (1 : ℝ)) A' t := by
    filter_upwards [hgev] with t ht
    rw [Ay_one]; exact ht.symm
  have eps : ∀ᶠ t in 𝓝 s, psipA ν χf A t = psipA ν (fun _ => (1 : ℝ)) A' t :=
    hAy.mono fun t ht => psipA_congr ν _ _ A A' t ht
  have eph : ∀ᶠ t in 𝓝 s, hpA ν χf A t = hpA ν (fun _ => (1 : ℝ)) A' t :=
    hAy.mono fun t ht => hpA_congr ν _ _ A A' t ht
  have ha : 0 < ageA ν s := by unfold ageA; positivity
  -- the six differentiability facts
  have a0 : DifferentiableAt ℝ (hpA ν χf A s) x := hpADiffX_glob h1 ν hν χf A s hs x
  have a1 : DifferentiableAt ℝ (fun s' => hpA ν χf A s' x) s := by
    refine (hpADiffS_glob ν hν (fun _ => (1 : ℝ)) A' hC s hs x).congr_of_eventuallyEq ?_
    exact eph.mono fun t ht => by simp [ht]
  have a2 : DifferentiableAt ℝ (psipA ν χf A s) x := by
    have : psipA ν χf A s = fun z : ℝ × ℝ => ∑' j : ℤ, psiPhi ν s (Ay ν χf A s) (xj ν j z) :=
      funext fun z => psipA_eq_phi ν χf A s z ha
    rw [this]
    exact psiPhiXDiff ν s hν hs _ x
  have a3 : DifferentiableAt ℝ (fun s' => psipA ν χf A s' x) s := by
    refine (psipA_hasDerivAt_glob ν hν (fun _ => (1 : ℝ)) A' hC s hs x).differentiableAt
      |>.congr_of_eventuallyEq ?_
    exact eps.mono fun t ht => by simp [ht]
  have a4 : DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y (ei 1)) x :=
    psipAXSecond_glob ν hν χf A s hs x
  have a5 : DifferentiableAt ℝ (fun y => deriv (fun s' => psipA ν χf A s' y) s) x := by
    have hfun : (fun y => deriv (fun s' => psipA ν χf A s' y) s) =
        fun y => deriv (fun s' => psipA ν (fun _ => (1 : ℝ)) A' s' y) s := by
      funext y
      exact Filter.EventuallyEq.deriv_eq (eps.mono fun t ht => by simp [ht])
    rw [hfun]
    exact psipAMixedX_glob h2 h3 ν hν (fun _ => (1 : ℝ)) A' hC s hs x
  have a6 : DifferentiableAt ℝ (fun s' => fderiv ℝ (psipA ν χf A s') x (ei 1)) s := by
    refine (psipAMixedS_glob ν hν (fun _ => (1 : ℝ)) A' hC s hs x).congr_of_eventuallyEq ?_
    exact eps.mono fun t ht => by simp [ht]
  have a7 : DifferentiableAt ℝ (fun s' => deriv (fun s'' => psipA ν χf A s'' x) s') s := by
    refine (psipASSecond_glob ν hν (fun _ => (1 : ℝ)) A' hC s hs x).congr_of_eventuallyEq ?_
    filter_upwards [eps.eventually_nhds] with t ht
    exact Filter.EventuallyEq.deriv_eq (ht.mono fun u hu => by simp [hu])
  rcases hu with rfl | rfl | rfl | rfl
  · exact ⟨by unfold hpR; exact a0.fst, by unfold hpR; exact a1.fst⟩
  · exact ⟨by unfold hpZ; exact a0.snd, by unfold hpZ; exact a1.snd⟩
  · exact ⟨a2, a3⟩
  · constructor
    · show DifferentiableAt ℝ (fun y => Kop (fun s' z => psipA ν χf A s' z) s y) x
      unfold Kop
      exact (differentiableAt_snd.mul a4).add (a5.const_mul _)
    · show DifferentiableAt ℝ (fun s' => Kop (fun s'' z => psipA ν χf A s'' z) s' x) s
      unfold Kop
      exact (a6.const_mul _).add ((differentiableAt_id.const_mul 2).mul a7)

end UnforcedLeray.Short.PartIIIb.Concrete
