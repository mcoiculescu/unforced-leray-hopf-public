import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DivZero
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2.PsipAMixedX

/-!
# `convDiffParts` (`PartIII-b:C/asrc/ra/9/2/2/5`)

Source 2075-2077 (`He = H e_z`, `H = (1-𝒦)ψ`), 4978-4980 (`ĥ_A`, `k = (1-𝒦)ψ^p_A`).
Differentiability in `x` at `s > 0` of `trPl`, `trHe`, `hpPl`, `kEz`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Partial derivatives of a jointly smooth `ψ s (q, η)` are `x`-differentiable at `s > 0`;
hence `raisedStream` is. -/
theorem raisedStream_diffX (ψ : ℝ → ℝ × ℝ → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (ℝ × ℝ) => ψ z.1 z.2) (Ioi 0 ×ˢ univ))
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fun y : ℝ × ℝ => UnforcedLeray.Cons.C03.raisedStream ψ s y.1 y.2) x := by
  set g : ℝ × (ℝ × ℝ) → ℝ := fun z => ψ z.1 z.2 with hgdef
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hcd : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 → ContDiffAt ℝ (⊤ : ℕ∞) g z := fun z hz =>
    hg.contDiffAt (hopen.mem_nhds ⟨hz, mem_univ _⟩)
  have hdg : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 → DifferentiableAt ℝ g z := fun z hz =>
    (hcd z hz).differentiableAt (by simp)
  have hDg : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 → DifferentiableAt ℝ (fderiv ℝ g) z := fun z hz =>
    ((hcd z hz).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hemb : DifferentiableAt ℝ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) x :=
    (differentiableAt_const s).prodMk differentiableAt_id
  have hDg' : DifferentiableAt ℝ (fun y : ℝ × ℝ => fderiv ℝ g (s, y)) x :=
    (hDg (s, x) hs).comp x hemb
  have hη : ∀ y : ℝ × ℝ, deriv (fun t => ψ s (y.1, t)) y.2 = fderiv ℝ g (s, y) (0, (0, 1)) := by
    intro y
    have hgd : HasDerivAt (fun t : ℝ => ((s, (y.1, t)) : ℝ × (ℝ × ℝ))) ((0, (0, 1)) : ℝ × (ℝ × ℝ)) y.2 :=
      (hasDerivAt_const y.2 s).prodMk ((hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2))
    have := (hdg (s, (y.1, y.2)) hs).hasFDerivAt.comp_hasDerivAt y.2 hgd
    exact this.deriv
  have hs' : ∀ y : ℝ × ℝ, deriv (fun t => ψ t y) s = fderiv ℝ g (s, y) (1, (0, 0)) := by
    intro y
    have hgd : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × (ℝ × ℝ))) ((1, (0, 0)) : ℝ × (ℝ × ℝ)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
    have := (hdg (s, y) hs).hasFDerivAt.comp_hasDerivAt s hgd
    exact this.deriv
  have hψ : DifferentiableAt ℝ (ψ s) x := by
    have := (hdg (s, x) hs).comp x hemb
    exact this
  have hη' : DifferentiableAt ℝ (fun y : ℝ × ℝ => fderiv ℝ g (s, y) (0, (0, 1))) x :=
    hDg'.clm_apply (differentiableAt_const _)
  have hs'' : DifferentiableAt ℝ (fun y : ℝ × ℝ => fderiv ℝ g (s, y) (1, (0, 0))) x :=
    hDg'.clm_apply (differentiableAt_const _)
  unfold UnforcedLeray.Cons.C03.raisedStream
  simp only [hη, hs']
  have hψ' : DifferentiableAt ℝ (fun y : ℝ × ℝ => ψ s (y.1, y.2)) x := hψ
  exact hψ'.sub ((differentiableAt_snd.mul hη').add (hs''.const_mul _))

theorem convDiffParts (as : ℝ) (χf : ℝ → ℝ) : ConvDiffParts as χf := by
  intro hχ dm dp hdm p d hbg A hA s hs x
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hu := trainV_diffAt p.train s hs x
    have h0 : DifferentiableAt ℝ (fun y => p.train.v s y 0) x :=
      ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt).comp x hu
    have h1 : DifferentiableAt ℝ (fun y => p.train.v s y 1) x :=
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt).comp x hu
    exact h0.prodMk h1
  · have := raisedStream_diffX p.train.ψ hbg.train_stream_smooth s hs x
    exact (differentiableAt_const (0 : ℝ)).prodMk this
  · exact hpADiffX as χf hχ p.ν p.ν_pos A hA s hs x
  · have h1 := psipADiff as χf hχ p.ν p.ν_pos A hA s hs x
    have h2 := psipAXSecond as χf hχ p.ν p.ν_pos A hA s hs x
    have h3 := psipAMixedX as χf hχ p.ν p.ν_pos A hA s hs x
    have h4 : DifferentiableAt ℝ (fun y => fderiv ℝ (psipA p.ν χf A s) y (ei 1)) x := h2
    refine (differentiableAt_const (0 : ℝ)).prodMk ?_
    show DifferentiableAt ℝ (fun y => psipA p.ν χf A s y - Kop (fun s' y => psipA p.ν χf A s' y) s y) x
    unfold Kop
    exact h1.1.sub ((differentiableAt_snd.mul h4).add (h3.const_mul _))

end UnforcedLeray.Short.PartIIIb.Concrete
