import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6

/-!
# `PartII-a:N01/9/1/2/4/6` (decomposition): `derivForceSmooth`

Source `the November 2 reference manuscript`
lines 1684-1689 (smooth compactly supported forces).  The cell derivative `∂_j F` of a smooth force
`F` is again a smooth force: it is `C^∞` (a partial derivative of a `C^∞` map is `C^∞`), it is
`c`-periodic in `q` (translation invariance of the slice derivative), and it vanishes wherever `F`
vanishes on an open neighbourhood of the slice (the same support constants `s₁, s₂, R` work).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The derivative of a `τ`-invariant function is `τ`-invariant (`τ` a translation). -/
theorem fderiv_add_const_eq {g : ℝ × ℝ → ℂ} {a : ℝ × ℝ} (hg : ∀ x, g (x + a) = g x)
    (x : ℝ × ℝ) : fderiv ℝ g (x + a) = fderiv ℝ g x := by
  have h1 : fderiv ℝ (fun t => g (t + a)) x = fderiv ℝ g (x + a) :=
    fderiv_comp_add_right a
  have h2 : (fun t => g (t + a)) = g := funext hg
  rw [← h1, h2]

/-- The slice derivative in `z` of `G (p.1, ·)` at `p.2` is the `z`-derivative of `G` at `p`
in the direction `(0, v)`. -/
theorem fderiv_slice_eq (G : Profile → ℂ) (hG : Differentiable ℝ G) (p : Profile)
    (v : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => G (p.1, z)) p.2 v = fderiv ℝ G p (0, v) := by
  have hφ : HasFDerivAt (fun z : ℝ × ℝ => (p.1, z)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hG' : HasFDerivAt G (fderiv ℝ G (p.1, p.2)) (p.1, p.2) := (hG (p.1, p.2)).hasFDerivAt
  have hc := hG'.comp p.2 hφ
  have hfd : fderiv ℝ (fun z : ℝ × ℝ => G (p.1, z)) p.2
      = (fderiv ℝ G (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := hc.fderiv
  rw [hfd]
  simp

/-- A partial `z`-derivative (in a fixed direction) of a `C^∞` function on the profile space is
`C^∞`. -/
theorem contDiff_partial_fderiv (G : Profile → ℂ) (hG : ContDiff ℝ ∞ G) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ (fun z : ℝ × ℝ => G (p.1, z)) p.2 v) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ G) := (contDiff_infty_iff_fderiv.1 hG).2
  have hK : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ G p (0, v)) :=
    hD.clm_apply contDiff_const
  have hdiff : Differentiable ℝ G := hG.differentiable (by simp)
  have key : (fun p : Profile => fderiv ℝ (fun z : ℝ × ℝ => G (p.1, z)) p.2 v)
      = fun p : Profile => fderiv ℝ G p (0, v) :=
    funext fun p => fderiv_slice_eq G hdiff p v
  rw [key]
  exact hK

/-- The cell derivative of a `C^∞` force is `C^∞`. -/
theorem derivForce_contDiff (F : Profile → MeridC) (hF : ContDiff ℝ ∞ F) (j : Fin 2) :
    ContDiff ℝ ∞ (derivForce j F) := by
  have hcomp : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : Profile => F x i) := fun i =>
    (contDiff_apply ℝ ℂ i).comp (PiLp.contDiff_ofLp.comp hF)
  have hcomp2 : ContDiff ℝ ∞ (fun p : Profile => fun i : Fin 2 =>
      fderiv ℝ (fun z : ℝ × ℝ => F (p.1, z) i) p.2 (UnforcedLeray.B0579.dir j)) :=
    contDiff_pi.2 fun i => contDiff_partial_fderiv (fun x : Profile => F x i) (hcomp i) _
  exact PiLp.contDiff_toLp.comp hcomp2

theorem derivForceSmooth : DerivForceSmooth := by
  intro c F hF j
  obtain ⟨hC, hper, s₁, s₂, R, hs₁, hsupp⟩ := hF
  refine ⟨derivForce_contDiff F hC j, ?_, s₁, s₂, R, hs₁, ?_⟩
  · -- `c`-periodicity in `q`
    intro p
    have hg : ∀ (x : ℝ × ℝ) (i : Fin 2), F (p.1, x + (c, 0)) i = F (p.1, x) i := by
      intro x i
      have h : F (p.1, x.1 + c, x.2) = F (p.1, x) := hper (p.1, x)
      have e' : x + (c, 0) = (x.1 + c, x.2) := by ext <;> simp
      rw [e', h]
    have e : (p.2.1 + c, p.2.2) = p.2 + (c, 0) := by
      ext <;> simp
    unfold derivForce
    dsimp only
    congr 1
    funext i
    rw [e]
    rw [fderiv_add_const_eq (a := (c, 0)) (fun x => hg x i) p.2]
  · -- support
    intro p hp
    rcases hp with h | h | h
    · ext i
      have h0 : ∀ z : ℝ × ℝ, F (p.1, z) = 0 := fun z => hsupp (p.1, z) (Or.inl h)
      simp [derivForce, h0]
    · ext i
      have h0 : ∀ z : ℝ × ℝ, F (p.1, z) = 0 := fun z => hsupp (p.1, z) (Or.inr (Or.inl h))
      simp [derivForce, h0]
    · have hU : IsOpen {z : ℝ × ℝ | R < |z.2|} :=
        isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
      have hmem : {z : ℝ × ℝ | R < |z.2|} ∈ 𝓝 p.2 := hU.mem_nhds h
      ext i
      have hev : (fun z : ℝ × ℝ => F (p.1, z) i) =ᶠ[𝓝 p.2] (fun _ => (0 : ℂ)) :=
        Filter.eventually_of_mem hmem
          (fun z hz => by simp [hsupp (p.1, z) (Or.inr (Or.inr hz))])
      simp only [derivForce]
      rw [hev.fderiv_eq]
      simp

end UnforcedLeray.Short.PartIIa.N01
