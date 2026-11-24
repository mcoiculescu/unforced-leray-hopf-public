import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DiffHat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.HpADiffS

/-!
# `ConvSDiff`: `s`-differentiability at `s > 0` of the four planar pieces
(`trPl`, `trHe`, `hpPl`, `kEz`), source 2049, 2075-2077, 4978-4980.
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The train velocity is differentiable in `s` at `s > 0` (fixed `x`). -/
private theorem trainV_diffS {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (hs : 0 < s)
    (x : ℝ × ℝ) : DifferentiableAt ℝ (fun t => tr.v t x) s := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (Ici (0 : ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) ∈ nhds (s, x) :=
    Filter.mem_of_superset (hopen.mem_nhds (show (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from
      ⟨hs, mem_univ _⟩))
      (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hc := tr.isTrain.smooth_v.contDiffAt hmem
  have h2 := hc.comp (x := s) (contDiffAt_id.prodMk contDiffAt_const)
  exact h2.differentiableAt (by simp)

/-- `t ↦ raisedStream ψ t x` is differentiable at `s > 0` (joint `C^∞` of `ψ` on `(0,∞) × ℝ²`). -/
private theorem raisedStream_diffS (ψ : ℝ → ℝ × ℝ → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (ℝ × ℝ) => ψ z.1 z.2) (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => UnforcedLeray.Cons.C03.raisedStream ψ t x.1 x.2) s := by
  set g : ℝ × (ℝ × ℝ) → ℝ := fun z => ψ z.1 z.2 with hgdef
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hcd : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 → ContDiffAt ℝ (⊤ : ℕ∞) g z := fun z hz =>
    hg.contDiffAt (hopen.mem_nhds ⟨hz, mem_univ _⟩)
  have hdg : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 → DifferentiableAt ℝ g z := fun z hz =>
    (hcd z hz).differentiableAt (by simp)
  have hDg : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 → DifferentiableAt ℝ (fderiv ℝ g) z := fun z hz =>
    ((hcd z hz).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hη : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 →
      deriv (fun τ => ψ z.1 (z.2.1, τ)) z.2.2 = fderiv ℝ g z (0, (0, 1)) := by
    intro z hz
    have hgd : HasDerivAt (fun τ : ℝ => ((z.1, (z.2.1, τ)) : ℝ × (ℝ × ℝ)))
        ((0, (0, 1)) : ℝ × (ℝ × ℝ)) z.2.2 :=
      (hasDerivAt_const z.2.2 z.1).prodMk ((hasDerivAt_const z.2.2 z.2.1).prodMk (hasDerivAt_id z.2.2))
    exact ((hdg z hz).hasFDerivAt.comp_hasDerivAt z.2.2 hgd).deriv
  have hs' : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 →
      deriv (fun τ => ψ τ z.2) z.1 = fderiv ℝ g z (1, (0, 0)) := by
    intro z hz
    have hgd : HasDerivAt (fun τ : ℝ => ((τ, z.2) : ℝ × (ℝ × ℝ))) ((1, (0, 0)) : ℝ × (ℝ × ℝ)) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    exact ((hdg z hz).hasFDerivAt.comp_hasDerivAt z.1 hgd).deriv
  have hdgw : DifferentiableAt ℝ g (s, x) := hdg (s, x) hs
  have hDgw : DifferentiableAt ℝ (fderiv ℝ g) (s, x) := hDg (s, x) hs
  have hA1 : DifferentiableAt ℝ (fun w : ℝ × (ℝ × ℝ) => fderiv ℝ g w (0, (0, 1))) (s, x) :=
    hDgw.clm_apply (differentiableAt_const _)
  have hA2 : DifferentiableAt ℝ (fun w : ℝ × (ℝ × ℝ) => fderiv ℝ g w (1, (0, 0))) (s, x) :=
    hDgw.clm_apply (differentiableAt_const _)
  have hsnd : DifferentiableAt ℝ (fun w : ℝ × (ℝ × ℝ) => w.2.2) (s, x) := by fun_prop
  have hfst : DifferentiableAt ℝ (fun w : ℝ × (ℝ × ℝ) => w.1) (s, x) := by fun_prop
  have hFd : DifferentiableAt ℝ (fun w : ℝ × (ℝ × ℝ) => g w -
      (w.2.2 * fderiv ℝ g w (0, (0, 1)) + 2 * w.1 * fderiv ℝ g w (1, (0, 0)))) (s, x) :=
    hdgw.sub ((hsnd.mul hA1).add (((differentiableAt_const (2 : ℝ)).mul hfst).mul hA2))
  have hemb : DifferentiableAt ℝ (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) s :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  refine (hFd.comp s hemb).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with t ht
  have e1 : deriv (fun τ => ψ t (x.1, τ)) x.2 = fderiv ℝ g (t, x) (0, (0, 1)) := hη (t, x) ht
  have e2 : deriv (fun τ => ψ τ (x.1, x.2)) t = fderiv ℝ g (t, x) (1, (0, 0)) := hs' (t, x) ht
  unfold UnforcedLeray.Cons.C03.raisedStream
  rw [e1, e2]
  rfl

theorem convSDiff (as : ℝ) (χf : ℝ → ℝ) : ConvSDiff as χf := by
  intro hχ dm dp hdm p d hbg A hA s hs x
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hu := trainV_diffS p.train s hs x
    have h0 : DifferentiableAt ℝ (fun t => p.train.v t x 0) s :=
      ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt).comp s hu
    have h1 : DifferentiableAt ℝ (fun t => p.train.v t x 1) s :=
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt).comp s hu
    exact h0.prodMk h1
  · have := raisedStream_diffS p.train.ψ hbg.train_stream_smooth s hs x
    exact (differentiableAt_const (0 : ℝ)).prodMk this
  · exact hpADiffS as χf hχ p.ν p.ν_pos A hA s hs x
  · have hG : ContDiffAt ℝ 2 (fun q : Chart => psipA p.ν χf A q.1 q.2) (s, x) :=
      (psiRingSmooth_proof as χf hχ p.ν p.ν_pos A hA).contDiffAt
        (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) ⟨hs, mem_univ _⟩)
    have hemb : DifferentiableAt ℝ (fun t : ℝ => ((t, x) : Chart)) s :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have hPsiC : DifferentiableAt ℝ (fun q : Chart => psipA p.ν χf A q.1 q.2) (s, x) :=
      hG.differentiableAt (by norm_num)
    have hX1C : DifferentiableAt ℝ (fun q : Chart => fderiv ℝ (psipA p.ν χf A q.1) q.2 (ei 1))
        (s, x) := diff_slice_x hG (ei 1)
    have hTC : DifferentiableAt ℝ (fun q : Chart => deriv (fun t' => psipA p.ν χf A t' q.2) q.1)
        (s, x) := diff_slice_s hG
    have hPsi : DifferentiableAt ℝ (fun t : ℝ => psipA p.ν χf A t x) s :=
      DifferentiableAt.comp (g := fun q : Chart => psipA p.ν χf A q.1 q.2)
        (f := fun t : ℝ => ((t, x) : Chart)) s hPsiC hemb
    have hX1 : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ (psipA p.ν χf A t) x (ei 1)) s :=
      DifferentiableAt.comp (g := fun q : Chart => fderiv ℝ (psipA p.ν χf A q.1) q.2 (ei 1))
        (f := fun t : ℝ => ((t, x) : Chart)) s hX1C hemb
    have hT : DifferentiableAt ℝ (fun t : ℝ => deriv (fun t' => psipA p.ν χf A t' x) t) s :=
      DifferentiableAt.comp (g := fun q : Chart => deriv (fun t' => psipA p.ν χf A t' q.2) q.1)
        (f := fun t : ℝ => ((t, x) : Chart)) s hTC hemb
    have hK : DifferentiableAt ℝ (fun t : ℝ => psipA p.ν χf A t x -
        (x.2 * fderiv ℝ (psipA p.ν χf A t) x (ei 1) +
          2 * t * deriv (fun t' => psipA p.ν χf A t' x) t)) s :=
      hPsi.sub ((hX1.const_mul x.2).add (((differentiableAt_const (2 : ℝ)).mul differentiableAt_id).mul hT))
    exact (differentiableAt_const (0 : ℝ)).prodMk hK

end UnforcedLeray.Short.PartIIIb.Concrete
