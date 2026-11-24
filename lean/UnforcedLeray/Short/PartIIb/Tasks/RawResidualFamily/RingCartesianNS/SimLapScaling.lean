import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `SimLapScaling`: the Laplacian of the similarity profile

Target: `UnforcedLeray.Short.IIb.SimLapScaling` (`Sub/R1_7.lean`), the leaf of the ring residual
`RingResidualCartesianNS` assembled in `ringResidualCartesianNS_of`.

Source of record: `the November 2 reference manuscript`, lines 1196-1263
(similarity residual `F_R`); `paper/main.tex` line 2917 (`B0190.simProfile`).

Claim: for `u(t,x)` of class `C²` near `(e^τ, e^{τ/2} y)`, the profile
`W(τ,y) = realC (e^{τ/2} u(e^τ, e^{τ/2} y))` satisfies
`Δ_y W(τ,y) = realC (e^{3τ/2} Δu(e^τ, e^{τ/2} y))`, with `Δ = Axi.vecLap`.

Proof outline. With `Φ(q) = (e^{q₁}, e^{q₁/2} q₂)` and `W = realC ∘ (q ↦ e^{q₁/2} F(Φ q))`,
the first derivative in direction `(0, e)` is `e^{q₁} · ∂_e F(Φ q)` (chain rule along lines).
The second derivative adds one more factor `e^{τ/2}` from `Φ` and the constant `e^{τ}` gives
`e^{3τ/2}`. The slice identity turns `∂_e ∂_e F` at `(t,x)` into the `j`-th term of `vecLap (u t) x`.
No hypothesis beyond the `C²` hypothesis of the target is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-! ## Helper objects -/

/-- `realC` as a continuous real-linear map `ℝ³ →L[ℝ] ℂ³`. -/
def simLap_CL : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => realC x
      map_add' := fun a b => by ext i; simp [realC_apply]
      map_smul' := fun c a => by ext i; simp [realC_apply] }

theorem simLap_CL_apply (x : Space) : simLap_CL x = realC x := rfl

/-- The similarity map `Φ(q) = (e^{q₁}, e^{q₁/2} q₂)`. -/
def simLap_Phi (q : ℝ × Space) : ℝ × Space :=
  (Real.exp q.1, Real.exp (q.1 / 2) • q.2)

/-- The complexified weighted profile `W(q) = realC (e^{q₁/2} F(Φ q))`. -/
def simLap_W (F : ℝ × Space → Space) (q : ℝ × Space) : CVec3 :=
  realC (Real.exp (q.1 / 2) • F (simLap_Phi q))

/-- The map `p ↦ ∂_{(0,e)} F(p)`. -/
def simLap_H (F : ℝ × Space → Space) (e : Space) (p : ℝ × Space) : Space :=
  fderiv ℝ F p ((0 : ℝ), e)

/-- The map `p ↦ realC (e^{p₁/2} · e^{p₁/2} · ∂_{(0,e)} F(Φ p))`. -/
def simLap_K (F : ℝ × Space → Space) (e : Space) (p : ℝ × Space) : CVec3 :=
  realC (Real.exp (p.1 / 2) • Real.exp (p.1 / 2) • simLap_H F e (simLap_Phi p))

/-! ## Elementary facts -/

theorem simLap_realC_sum (c : ℝ) (f : Fin 3 → Space) :
    ∑ j : Fin 3, realC (c • f j) = realC (c • ∑ j : Fin 3, f j) := by
  simp only [← simLap_CL_apply, map_sum, map_smul, Finset.smul_sum]

theorem simLap_Phi_differentiableAt (w : ℝ × Space) : DifferentiableAt ℝ simLap_Phi w := by
  unfold simLap_Phi
  fun_prop

theorem simLap_Phi_continuous : Continuous simLap_Phi := by
  unfold simLap_Phi
  fun_prop

theorem simLap_fst_line (w : ℝ × Space) (e : Space) (s : ℝ) :
    (w + s • ((0 : ℝ), e)).1 = w.1 := by
  simp

theorem simLap_pair_smul (c : ℝ) (e : Space) :
    ((0 : ℝ), c • e) = c • ((0 : ℝ), e) := by
  simp

theorem simLap_Phi_line (w : ℝ × Space) (e : Space) (s : ℝ) :
    simLap_Phi (w + s • ((0 : ℝ), e)) = simLap_Phi w + s • ((0 : ℝ), Real.exp (w.1 / 2) • e) := by
  refine Prod.ext ?_ ?_
  · simp [simLap_Phi]
  · simp only [simLap_Phi, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul, mul_zero, add_zero, smul_add]
    rw [smul_comm (Real.exp (w.1 / 2)) s e]

/-- Directional derivative along a line: `d/ds f (w + s v)` at `s = 0` is `fderiv f w v`. -/
theorem simLap_hasDerivAt_line {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : E → Y) (w v : E) (hf : DifferentiableAt ℝ f w) :
    HasDerivAt (fun s : ℝ => f (w + s • v)) (fderiv ℝ f w v) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => w + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h2 : HasFDerivAt f (fderiv ℝ f w) ((fun s : ℝ => w + s • v) 0) := by
    simpa using hf.hasFDerivAt
  exact h2.comp_hasDerivAt (x := (0 : ℝ)) h1

theorem simLap_hasDerivAt_realC (h : ℝ → Space) (h' : Space) (x : ℝ)
    (hh : HasDerivAt h h' x) :
    HasDerivAt (fun s => realC (h s)) (realC h') x :=
  simLap_CL.hasFDerivAt.comp_hasDerivAt (x := x) hh

theorem simLap_G_differentiableAt (F : ℝ × Space → Space) (w : ℝ × Space)
    (hF : DifferentiableAt ℝ F (simLap_Phi w)) :
    DifferentiableAt ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2) • F (simLap_Phi q)) w := by
  have hc : DifferentiableAt ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2)) w := by
    fun_prop
  exact hc.smul (DifferentiableAt.comp w hF (simLap_Phi_differentiableAt w))

/-- First derivative of `q ↦ e^{q₁/2} F(Φ q)` in direction `(0, e)`. -/
theorem simLap_fderiv_G (F : ℝ × Space → Space) (w : ℝ × Space) (e : Space)
    (hF : DifferentiableAt ℝ F (simLap_Phi w)) :
    fderiv ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2) • F (simLap_Phi q)) w ((0 : ℝ), e) =
      Real.exp (w.1 / 2) • Real.exp (w.1 / 2) • fderiv ℝ F (simLap_Phi w) ((0 : ℝ), e) := by
  have hG := simLap_G_differentiableAt F w hF
  have h1 : HasDerivAt
      (fun s : ℝ => Real.exp ((w + s • ((0 : ℝ), e)).1 / 2) •
        F (simLap_Phi (w + s • ((0 : ℝ), e))))
      (fderiv ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2) • F (simLap_Phi q)) w ((0 : ℝ), e)) 0 :=
    simLap_hasDerivAt_line (fun q : ℝ × Space => Real.exp (q.1 / 2) • F (simLap_Phi q)) w
      ((0 : ℝ), e) hG
  have h2 : HasDerivAt
      (fun s : ℝ => Real.exp (w.1 / 2) •
        F (simLap_Phi w + s • ((0 : ℝ), Real.exp (w.1 / 2) • e)))
      (Real.exp (w.1 / 2) • fderiv ℝ F (simLap_Phi w) ((0 : ℝ), Real.exp (w.1 / 2) • e)) 0 :=
    (simLap_hasDerivAt_line F (simLap_Phi w) ((0 : ℝ), Real.exp (w.1 / 2) • e) hF).const_smul
      (Real.exp (w.1 / 2))
  have hfun : (fun s : ℝ => Real.exp ((w + s • ((0 : ℝ), e)).1 / 2) •
        F (simLap_Phi (w + s • ((0 : ℝ), e)))) =
      (fun s : ℝ => Real.exp (w.1 / 2) •
        F (simLap_Phi w + s • ((0 : ℝ), Real.exp (w.1 / 2) • e))) := by
    funext s
    rw [simLap_fst_line, simLap_Phi_line]
  rw [hfun] at h1
  have hu := h1.unique h2
  rw [hu, simLap_pair_smul, map_smul]

/-- First derivative of `W = realC ∘ (q ↦ e^{q₁/2} F(Φ q))` in direction `(0, e)`. -/
theorem simLap_fderiv_W (F : ℝ × Space → Space) (w : ℝ × Space) (e : Space)
    (hF : DifferentiableAt ℝ F (simLap_Phi w)) :
    fderiv ℝ (simLap_W F) w ((0 : ℝ), e) = simLap_K F e w := by
  have hG := simLap_G_differentiableAt F w hF
  have h1 : HasFDerivAt (simLap_W F)
      (simLap_CL.comp
        (fderiv ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2) • F (simLap_Phi q)) w)) w :=
    simLap_CL.hasFDerivAt.comp w hG.hasFDerivAt
  rw [h1.fderiv, ContinuousLinearMap.comp_apply, simLap_fderiv_G F w e hF]
  rfl

/-! ## The slice identity -/

/-- For `F` of class `C²` at `(t,x)`, the `e`-directional second derivative in the phase variable
equals the `e`-second derivative of the slice `z ↦ F(t,z)` at `x`. -/
theorem simLap_slice (F : ℝ × Space → Space) (t : ℝ) (x e : Space)
    (hF : ContDiffAt ℝ 2 F (t, x)) :
    fderiv ℝ (simLap_H F e) (t, x) ((0 : ℝ), e) =
      fderiv ℝ (fun x' : Space => fderiv ℝ (fun z : Space => F (t, z)) x' e) x e := by
  have hD2 : ∀ᶠ p in 𝓝 (t, x), ContDiffAt ℝ 2 F p := hF.eventually (by norm_num)
  have hDF : ∀ᶠ p in 𝓝 (t, x), DifferentiableAt ℝ F p :=
    hD2.mono fun p hp => hp.differentiableAt (by norm_num)
  have hslice : Continuous (fun z : Space => ((t, z) : ℝ × Space)) := by
    fun_prop
  have hDz : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F (t, z) :=
    (hslice.tendsto' x (t, x) rfl).eventually hDF
  have hb : ∀ z : Space, DifferentiableAt ℝ F (t, z) →
      fderiv ℝ (fun z' : Space => F (t, z')) z e = fderiv ℝ F (t, z) ((0 : ℝ), e) := by
    intro z hz
    have hsl : DifferentiableAt ℝ (fun z' : Space => ((t, z') : ℝ × Space)) z := by
      fun_prop
    have hg : DifferentiableAt ℝ (fun z' : Space => F (t, z')) z :=
      DifferentiableAt.comp z hz hsl
    have h1 := simLap_hasDerivAt_line F (t, z) ((0 : ℝ), e) hz
    have h2 := simLap_hasDerivAt_line (fun z' : Space => F (t, z')) z e hg
    have hpt : ∀ s : ℝ, ((t, z) + s • ((0 : ℝ), e) : ℝ × Space) = (t, z + s • e) := by
      intro s
      ext <;> simp
    have h2' : HasDerivAt (fun s : ℝ => F ((t, z) + s • ((0 : ℝ), e)))
        (fderiv ℝ (fun z' : Space => F (t, z')) z e) 0 := by
      simp only [hpt]
      exact h2
    exact (h1.unique h2').symm
  have hEvq : (fun x' : Space => fderiv ℝ (fun z : Space => F (t, z)) x' e) =ᶠ[𝓝 x]
      (fun x' : Space => simLap_H F e (t, x')) := by
    filter_upwards [hDz] with z hz
    exact hb z hz
  rw [hEvq.fderiv_eq]
  have hHd : DifferentiableAt ℝ (simLap_H F e) (t, x) := by
    have hD1 : DifferentiableAt ℝ (fderiv ℝ F) (t, x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hD1.clm_apply (differentiableAt_const ((0 : ℝ), e))
  have hsl2 : DifferentiableAt ℝ (fun x' : Space => ((t, x') : ℝ × Space)) x := by
    fun_prop
  have hQ : DifferentiableAt ℝ (fun x' : Space => simLap_H F e (t, x')) x :=
    DifferentiableAt.comp x hHd hsl2
  have h1 := simLap_hasDerivAt_line (simLap_H F e) (t, x) ((0 : ℝ), e) hHd
  have h2 := simLap_hasDerivAt_line (fun x' : Space => simLap_H F e (t, x')) x e hQ
  have hpt : ∀ s : ℝ, ((t, x) + s • ((0 : ℝ), e) : ℝ × Space) = (t, x + s • e) := by
    intro s
    ext <;> simp
  have h2' : HasDerivAt (fun s : ℝ => simLap_H F e ((t, x) + s • ((0 : ℝ), e)))
      (fderiv ℝ (fun x' : Space => simLap_H F e (t, x')) x e) 0 := by
    simp only [hpt]
    exact h2
  exact h1.unique h2'

/-! ## The second derivative of the profile -/

theorem simLap_second (F : ℝ × Space → Space) (τ : ℝ) (y e : Space)
    (hF : ContDiffAt ℝ 2 F (Real.exp τ, Real.exp (τ / 2) • y)) :
    fderiv ℝ (fun p : ℝ × Space => fderiv ℝ (simLap_W F) p ((0 : ℝ), e)) (τ, y) ((0 : ℝ), e) =
      realC (Real.exp (τ / 2) ^ 3 •
        fderiv ℝ (fun x' : Space => fderiv ℝ (fun z : Space => F (Real.exp τ, z)) x' e)
          (Real.exp (τ / 2) • y) e) := by
  have hD2 : ∀ᶠ p in 𝓝 (Real.exp τ, Real.exp (τ / 2) • y), ContDiffAt ℝ 2 F p :=
    hF.eventually (by norm_num)
  have hΦev : ∀ᶠ w in 𝓝 (τ, y), ContDiffAt ℝ 2 F (simLap_Phi w) :=
    (simLap_Phi_continuous.tendsto' (τ, y) (Real.exp τ, Real.exp (τ / 2) • y) rfl).eventually
      hD2
  have hEq : (fun p : ℝ × Space => fderiv ℝ (simLap_W F) p ((0 : ℝ), e)) =ᶠ[𝓝 (τ, y)]
      simLap_K F e := by
    filter_upwards [hΦev] with w hw
    exact simLap_fderiv_W F w e (hw.differentiableAt (by norm_num))
  rw [hEq.fderiv_eq]
  have hH : DifferentiableAt ℝ (simLap_H F e) (simLap_Phi (τ, y)) := by
    have hD1 : DifferentiableAt ℝ (fderiv ℝ F) (Real.exp τ, Real.exp (τ / 2) • y) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hD1.clm_apply (differentiableAt_const ((0 : ℝ), e))
  have hK : DifferentiableAt ℝ (simLap_K F e) (τ, y) := by
    have hΦd : DifferentiableAt ℝ simLap_Phi (τ, y) := simLap_Phi_differentiableAt _
    have hc : DifferentiableAt ℝ (fun p : ℝ × Space => Real.exp (p.1 / 2)) (τ, y) := by
      fun_prop
    have hI : DifferentiableAt ℝ (fun p : ℝ × Space => simLap_H F e (simLap_Phi p)) (τ, y) :=
      DifferentiableAt.comp (τ, y) hH hΦd
    have h1 : DifferentiableAt ℝ
        (fun p : ℝ × Space =>
          Real.exp (p.1 / 2) • Real.exp (p.1 / 2) • simLap_H F e (simLap_Phi p)) (τ, y) :=
      hc.smul (hc.smul hI)
    exact simLap_CL.differentiableAt.comp (τ, y) h1
  have hKd : HasDerivAt (fun s : ℝ => simLap_K F e ((τ, y) + s • ((0 : ℝ), e)))
      (fderiv ℝ (simLap_K F e) (τ, y) ((0 : ℝ), e)) 0 :=
    simLap_hasDerivAt_line (simLap_K F e) (τ, y) ((0 : ℝ), e) hK
  have hHl : HasDerivAt
      (fun s : ℝ => simLap_H F e (simLap_Phi (τ, y) + s • ((0 : ℝ), Real.exp (τ / 2) • e)))
      (fderiv ℝ (simLap_H F e) (simLap_Phi (τ, y)) ((0 : ℝ), Real.exp (τ / 2) • e)) 0 :=
    simLap_hasDerivAt_line (simLap_H F e) (simLap_Phi (τ, y)) ((0 : ℝ), Real.exp (τ / 2) • e) hH
  have hRl : HasDerivAt
      (fun s : ℝ => realC (Real.exp (τ / 2) • Real.exp (τ / 2) •
        simLap_H F e (simLap_Phi (τ, y) + s • ((0 : ℝ), Real.exp (τ / 2) • e))))
      (realC (Real.exp (τ / 2) • Real.exp (τ / 2) •
        fderiv ℝ (simLap_H F e) (simLap_Phi (τ, y)) ((0 : ℝ), Real.exp (τ / 2) • e))) 0 :=
    simLap_hasDerivAt_realC _ _ 0 ((hHl.const_smul (Real.exp (τ / 2))).const_smul
      (Real.exp (τ / 2)))
  have hfun : (fun s : ℝ => simLap_K F e ((τ, y) + s • ((0 : ℝ), e))) =
      (fun s : ℝ => realC (Real.exp (τ / 2) • Real.exp (τ / 2) •
        simLap_H F e (simLap_Phi (τ, y) + s • ((0 : ℝ), Real.exp (τ / 2) • e)))) := by
    funext s
    simp only [simLap_K, simLap_fst_line, simLap_Phi_line]
  rw [hfun] at hKd
  have hmain := hKd.unique hRl
  have hlin : fderiv ℝ (simLap_H F e) (simLap_Phi (τ, y)) ((0 : ℝ), Real.exp (τ / 2) • e) =
      Real.exp (τ / 2) • fderiv ℝ (simLap_H F e) (simLap_Phi (τ, y)) ((0 : ℝ), e) := by
    rw [simLap_pair_smul, map_smul]
  have hslice : fderiv ℝ (simLap_H F e) (simLap_Phi (τ, y)) ((0 : ℝ), e) =
      fderiv ℝ (fun x' : Space => fderiv ℝ (fun z : Space => F (Real.exp τ, z)) x' e)
        (Real.exp (τ / 2) • y) e :=
    simLap_slice F (Real.exp τ) (Real.exp (τ / 2) • y) e hF
  rw [hmain, hlin, hslice]
  congr 1
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-! ## The Laplacian of the profile -/

theorem simLap_main (F : ℝ × Space → Space) (τ : ℝ) (y : Space)
    (hF : ContDiffAt ℝ 2 F (Real.exp τ, Real.exp (τ / 2) • y)) :
    lapT (simLap_W F) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 • ∑ j : Fin 3,
        fderiv ℝ (fun x' : Space =>
          fderiv ℝ (fun z : Space => F (Real.exp τ, z)) x' (coordinateVector j))
          (Real.exp (τ / 2) • y) (coordinateVector j)) := by
  have hterm : ∀ j : Fin 3, PhaseSpace.dy j (PhaseSpace.dy j (simLap_W F)) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 • fderiv ℝ (fun x' : Space =>
          fderiv ℝ (fun z : Space => F (Real.exp τ, z)) x' (coordinateVector j))
          (Real.exp (τ / 2) • y) (coordinateVector j)) :=
    fun j => simLap_second F τ y (coordinateVector j) hF
  show ∑ j : Fin 3, PhaseSpace.dy j (PhaseSpace.dy j (simLap_W F)) (τ, y) = _
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  exact simLap_realC_sum _ _

/-! ## The target -/

/-- **Scaling of the Laplacian** (`SimLapScaling`, `Sub/R1_7.lean`): for a physical field `u(t,x)`,
`C²` jointly near `(e^τ, e^{τ/2} y)`, `Δ_y W(τ,y) = realC (e^{3τ/2} Δu(e^τ, e^{τ/2} y))`. -/
theorem simLapScaling : UnforcedLeray.Short.IIb.SimLapScaling := by
  unfold SimLapScaling
  intro u tau y hu
  have hW : (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1 u q.1 q.2)) =
      simLap_W (fun p : ℝ × Space => u p.1 p.2) := by
    funext q
    simp [simLap_W, simLap_Phi, UnforcedLeray.B0190.simProfile]
  rw [hW]
  exact simLap_main (fun p : ℝ × Space => u p.1 p.2) tau y hu

end UnforcedLeray.Short.IIb

end
