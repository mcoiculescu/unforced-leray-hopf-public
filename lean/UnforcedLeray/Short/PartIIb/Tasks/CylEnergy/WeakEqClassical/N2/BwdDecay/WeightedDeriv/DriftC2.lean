import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2
import UnforcedLeray.Short.PartIIb.Sub.TrainCloseCell
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.DriftC2.VcBound

/-!
# `PartII-b:T22/2/3/2/2/3`: the train drift and its first two derivatives are bounded

Source: `the November 2 reference manuscript` lines 2085-2093.

`v = (v - V_c) + V_c`.  `TrainClose.plane_bound` bounds `D^j (v - V_c)` on the plane by `δ`;
`Vc_iter_bound` (`DriftC2/VcBound.lean`) bounds `D^j V_c` for every period `c > 0` and a bounded
range of ages.  The components and the classical partials `B0579.pd` are bounded by the
iterated Fréchet derivatives (`pd_bridge`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

theorem norm_dir_le (j : Fin 2) : ‖B0579.dir j‖ ≤ 1 := by
  fin_cases j <;> simp [B0579.dir, Prod.norm_def]

/-- Components and classical partials of a `C²` vector field are bounded by the iterated
Fréchet derivatives. -/
theorem pd_bridge (g : B0579.Plane → Train.Vec) (hg : ContDiff ℝ 2 g) (x : B0579.Plane)
    (i j k : Fin 2) :
    |g x i| ≤ ‖iteratedFDeriv ℝ 0 g x‖ ∧
    |B0579.pd j (fun y => g y i) x| ≤ ‖iteratedFDeriv ℝ 1 g x‖ ∧
    |B0579.pd j (B0579.pd k (fun y => g y i)) x| ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfd : ∀ y, fderiv ℝ (fun y => g y i) y = (EuclideanSpace.proj i : Train.Vec →L[ℝ] ℝ).comp
      (fderiv ℝ g y) := fun y =>
    ((EuclideanSpace.proj i : Train.Vec →L[ℝ] ℝ).hasFDerivAt.comp y (hd y).hasFDerivAt).fderiv
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_zero]
    simpa using PiLp.norm_apply_le (g x) i
  · rw [norm_iteratedFDeriv_one]
    unfold B0579.pd
    rw [hfd]
    have h1 : |(fderiv ℝ g x (B0579.dir j)) i| ≤ ‖fderiv ℝ g x (B0579.dir j)‖ := by
      simpa using PiLp.norm_apply_le (fderiv ℝ g x (B0579.dir j)) i
    refine h1.trans ((fderiv ℝ g x).le_opNorm _ |>.trans ?_)
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_dir_le j)
  · have hd2 : Differentiable ℝ (fderiv ℝ g) :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    set L : (B0579.Plane →L[ℝ] Train.Vec) →L[ℝ] ℝ :=
      (EuclideanSpace.proj i : Train.Vec →L[ℝ] ℝ).comp
        (ContinuousLinearMap.apply ℝ Train.Vec (B0579.dir k)) with hL
    have hfun : B0579.pd k (fun y => g y i) = fun y => L (fderiv ℝ g y) := by
      funext y
      unfold B0579.pd
      rw [hfd]
      rfl
    have hder : fderiv ℝ (fun y => L (fderiv ℝ g y)) x = L.comp (fderiv ℝ (fderiv ℝ g) x) :=
      (L.hasFDerivAt.comp x (hd2 x).hasFDerivAt).fderiv
    have e2 : ‖iteratedFDeriv ℝ 2 g x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [e2]
    unfold B0579.pd at *
    rw [hfun, hder]
    have h1 : |((fderiv ℝ (fderiv ℝ g) x (B0579.dir j)) (B0579.dir k)) i| ≤
        ‖(fderiv ℝ (fderiv ℝ g) x (B0579.dir j)) (B0579.dir k)‖ := by
      simpa using PiLp.norm_apply_le ((fderiv ℝ (fderiv ℝ g) x (B0579.dir j)) (B0579.dir k)) i
    have h2 : ‖(fderiv ℝ (fderiv ℝ g) x (B0579.dir j)) (B0579.dir k)‖ ≤
        ‖fderiv ℝ (fderiv ℝ g) x (B0579.dir j)‖ * ‖B0579.dir k‖ :=
      (fderiv ℝ (fderiv ℝ g) x (B0579.dir j)).le_opNorm _
    have h3 : ‖fderiv ℝ (fderiv ℝ g) x (B0579.dir j)‖ ≤
        ‖fderiv ℝ (fderiv ℝ g) x‖ * ‖B0579.dir j‖ := (fderiv ℝ (fderiv ℝ g) x).le_opNorm _
    have hj := norm_dir_le j
    have hk := norm_dir_le k
    have hn := norm_nonneg (fderiv ℝ (fderiv ℝ g) x)
    have hn1 := norm_nonneg (fderiv ℝ (fderiv ℝ g) x (B0579.dir j))
    show |((fderiv ℝ (fderiv ℝ g) x (B0579.dir j)) (B0579.dir k)) i| ≤ _
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) x‖ * ‖B0579.dir j‖ * ‖B0579.dir k‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) x‖ := by
          have hjk : ‖B0579.dir j‖ * ‖B0579.dir k‖ ≤ 1 :=
            mul_le_one₀ hj (norm_nonneg _) hk
          calc _ = ‖fderiv ℝ (fderiv ℝ g) x‖ * (‖B0579.dir j‖ * ‖B0579.dir k‖) := by ring
            _ ≤ ‖fderiv ℝ (fderiv ℝ g) x‖ * 1 := mul_le_mul_of_nonneg_left hjk hn
            _ = _ := mul_one _

/-- **Leaf `/3`** (SP 2085-2093): the train drift and its first two derivatives are bounded. -/
theorem bwdDriftC2Bound : UnforcedLeray.Short.IIb.BwdDriftC2Bound := by
  intro Sg ν c δ hSg hν hc hδ tr htr
  obtain ⟨M0, h0⟩ := Vc_iter_bound ν c Sg hν hc hSg.le 0
  obtain ⟨M1, h1⟩ := Vc_iter_bound ν c Sg hν hc hSg.le 1
  obtain ⟨M2, h2⟩ := Vc_iter_bound ν c Sg hν hc hSg.le 2
  refine ⟨3 * δ + |M0| + |M1| + |M2|, fun r hr x i => ?_⟩
  obtain ⟨hr0, hr1⟩ := hr
  have hνr : ν * r ≤ Sg := by
    have := (le_div_iff₀ hν).1 hr1
    linarith
  have hvd : ContDiff ℝ ∞ (tr.v r) := by
    have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun z _ => ⟨mem_Ici.2 hr0, mem_univ z⟩)
    exact contDiffOn_univ.1 h
  have hGd : ContDiff ℝ ∞ (Train.Vc ν c r) :=
    Short.Spine.vcReg_contDiff_Vc hc (Short.Spine.vcReg_width_pos hν hr0)
  have hFd : ContDiff ℝ ∞ (fun z => tr.v r z - Train.Vc ν c r z) := hvd.sub hGd
  have hsplit : tr.v r = (fun z => tr.v r z - Train.Vc ν c r z) + Train.Vc ν c r := by
    funext z; simp
  have key : ∀ k : ℕ, k ≤ 2 → ∀ M : ℝ, (∀ z, ‖iteratedFDeriv ℝ k (Train.Vc ν c r) z‖ ≤ M) →
      ‖iteratedFDeriv ℝ k (tr.v r) x‖ ≤ δ + M := by
    intro k hk M hM
    have hF' := hFd.of_le (show ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ from mod_cast le_top)
    have hG' := hGd.of_le (show ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ from mod_cast le_top)
    have e := iteratedFDeriv_add_apply (x := x) hF'.contDiffAt hG'.contDiffAt
    rw [← hsplit] at e
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hM x))
    exact TrainClose.plane_bound hc htr hr0 hr1 x (j := k) (by omega)
  have k0 := key 0 (by norm_num) M0 (fun z => h0 r hr0 hνr z |>.trans (le_refl _))
  have k1 := key 1 (by norm_num) M1 (fun z => h1 r hr0 hνr z)
  have k2 := key 2 (by norm_num) M2 (fun z => h2 r hr0 hνr z)
  have hv2 : ContDiff ℝ 2 (tr.v r) := hvd.of_le (WithTop.coe_le_coe.2 le_top)
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

end UnforcedLeray.Short.IIb
