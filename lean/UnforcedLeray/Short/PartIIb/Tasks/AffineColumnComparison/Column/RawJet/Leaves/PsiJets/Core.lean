import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand

/-!
# Helpers for the stream jets (`PsiJets/`), SP 261-291 and 2419-2423

Mixed partial derivatives of a jointly smooth function on `(0,∞) × ℝ²`, commuted with `n`
age derivatives. The age-slice formula is `vb_slice_iteratedDeriv_eq` (VelBand).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Joint smoothness of `(s,w) ↦ ∂_r^n K(r,w)|_{r=s}` at `s > 0`, of any order `m`. -/
theorem psiJet_slice_contDiffAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ℝ × V → ℝ) (hK : ContDiffOn ℝ ∞ K (Ioi (0 : ℝ) ×ˢ (univ : Set V))) (n m : ℕ)
    {s : ℝ} (hs : 0 < s) (w : V) :
    ContDiffAt ℝ (m : WithTop ℕ∞) (fun x : ℝ × V => iteratedDeriv n (fun r => K (r, x.2)) x.1)
      (s, w) := by
  have hKa : ContDiffAt ℝ ∞ K (s, w) :=
    hK.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (iteratedFDeriv ℝ n K) (s, w) :=
    hKa.iteratedFDeriv_right (m := (m : WithTop ℕ∞)) (i := n) (mod_cast le_top)
  have h3 : ContDiffAt ℝ (m : WithTop ℕ∞)
      (fun x : ℝ × V => iteratedFDeriv ℝ n K x (fun _ => (1, 0))) (s, w) :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × V) ℝ
      (fun _ => (1, 0))).contDiff.contDiffAt).comp (s, w) h1
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hs] with x hx
  exact vb_slice_iteratedDeriv_eq K hK n hx x.2

private theorem psi_fderiv_apply_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {y : E} (hF : DifferentiableAt ℝ (fderiv ℝ F) y) (v e : E) :
    fderiv ℝ (fun z => fderiv ℝ F z v) y e = fderiv ℝ (fderiv ℝ F) y e v := by
  rw [fderiv_clm_apply hF (differentiableAt_const v)]
  simp

/-- One mixed-derivative step: for `F` of class `C^2` on `(0,∞) × ℝ` (second slot `τ`), if the
`τ`-derivative of `F(r,·)` is `G(r,·)` for `r > 0`, then the `τ`-derivative of `∂_r F(s,·)` is
`∂_r G(·,τ)` at `s`. Schwarz symmetry of the second derivative of `F` at `(s,τ)`. -/
theorem psi_swap_step {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))
    {s : ℝ} (hs : 0 < s)
    (hG : ∀ r : ℝ, 0 < r → ∀ τ : ℝ, HasDerivAt (fun τ' => F (r, τ')) (G (r, τ)) τ) (τ : ℝ) :
    HasDerivAt (fun τ' => deriv (fun r => F (r, τ')) s) (deriv (fun r => G (r, τ)) s) τ := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ∀ x : ℝ × ℝ, 0 < x.1 → x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    fun x hx => ⟨hx, Set.mem_univ _⟩
  have hc : ∀ x : ℝ × ℝ, 0 < x.1 → ContDiffAt ℝ 2 F x := fun x hx =>
    hF.contDiffAt (hU.mem_nhds (hmem x hx))
  have hd : ∀ x : ℝ × ℝ, 0 < x.1 → DifferentiableAt ℝ F x := fun x hx =>
    (hc x hx).differentiableAt (by norm_num)
  have hfd : ∀ x : ℝ × ℝ, 0 < x.1 → DifferentiableAt ℝ (fderiv ℝ F) x := fun x hx =>
    ((hc x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : ∀ x : ℝ × ℝ, 0 < x.1 → IsSymmSndFDerivAt ℝ F x := fun x hx =>
    (hc x hx).isSymmSndFDerivAt (by simp)
  have hR : ∀ r τ' : ℝ, HasDerivAt (fun r' : ℝ => ((r', τ') : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) r :=
    fun r τ' => (hasDerivAt_id' r).prodMk (hasDerivAt_const r τ')
  have hT : ∀ r τ' : ℝ, HasDerivAt (fun τ'' : ℝ => ((r, τ'') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) τ' :=
    fun r τ' => (hasDerivAt_const τ' r).prodMk (hasDerivAt_id' τ')
  have hpr : ∀ r τ' : ℝ, 0 < r →
      HasDerivAt (fun r' : ℝ => F (r', τ')) (fderiv ℝ F (r, τ') (1, 0)) r := by
    intro r τ' hr
    exact (hd (r, τ') hr).hasFDerivAt.comp_hasDerivAt r (hR r τ')
  have h1 : (fun τ' => deriv (fun r => F (r, τ')) s) = fun τ' => fderiv ℝ F (s, τ') (1, 0) :=
    funext fun τ' => (hpr s τ' hs).deriv
  have h2 : HasDerivAt (fun τ' => fderiv ℝ F (s, τ') (1, 0))
      (fderiv ℝ (fderiv ℝ F) (s, τ) (0, 1) (1, 0)) τ := by
    have hΦ : DifferentiableAt ℝ (fun x : ℝ × ℝ => fderiv ℝ F x (1, 0)) (s, τ) :=
      (hfd (s, τ) hs).clm_apply (differentiableAt_const _)
    have h := hΦ.hasFDerivAt.comp_hasDerivAt τ (hT s τ)
    rw [psi_fderiv_apply_symm (hfd (s, τ) hs) (1, 0) (0, 1)] at h
    exact h
  have hΨd : DifferentiableAt ℝ (fun x : ℝ × ℝ => fderiv ℝ F x (0, 1)) (s, τ) :=
    (hfd (s, τ) hs).clm_apply (differentiableAt_const _)
  have hGeq : ∀ r : ℝ, 0 < r → fderiv ℝ F (r, τ) (0, 1) = G (r, τ) := by
    intro r hr
    have h := (hd (r, τ) hr).hasFDerivAt.comp_hasDerivAt τ (hT r τ)
    exact h.unique (hG r hr τ)
  have hev : (fun r => fderiv ℝ F (r, τ) (0, 1)) =ᶠ[𝓝 s] (fun r => G (r, τ)) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact hGeq r hr
  have hkey : deriv (fun r => G (r, τ)) s = fderiv ℝ (fderiv ℝ F) (s, τ) (1, 0) (0, 1) := by
    rw [← hev.deriv_eq]
    have hΨr : HasDerivAt (fun r' : ℝ => fderiv ℝ F (r', τ) (0, 1))
        (fderiv ℝ (fun x : ℝ × ℝ => fderiv ℝ F x (0, 1)) (s, τ) (1, 0)) s :=
      by
        have h := hΨd.hasFDerivAt.comp_hasDerivAt s (hR s τ)
        exact h
    rw [hΨr.deriv, psi_fderiv_apply_symm (hfd (s, τ) hs) (0, 1) (1, 0)]
  rw [h1, hkey]
  have hs' := hsym (s, τ) hs (0, 1) (1, 0)
  rw [← hs']
  exact h2

/-- Mixed partials commute with `n` age derivatives: for `Kp` jointly smooth on `(0,∞) × ℝ`,
`τ`-derivative of `∂_r^n Kp(·,τ)` is `∂_r^n ∂_τ Kp`. -/
theorem psi_swap_core (Kp : ℝ × ℝ → ℝ) (hKp : ContDiffOn ℝ ∞ Kp (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (n : ℕ) :
    ∀ s : ℝ, 0 < s → ∀ τ : ℝ,
      HasDerivAt (fun τ' => iteratedDeriv n (fun r => Kp (r, τ')) s)
        (iteratedDeriv n (fun r => deriv (fun τ' => Kp (r, τ')) τ) s) τ := by
  induction n with
  | zero =>
    intro s hs τ
    have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hKd : DifferentiableAt ℝ Kp (s, τ) :=
      (hKp.contDiffAt (hU.mem_nhds (show (s, τ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from
        ⟨hs, Set.mem_univ _⟩))).differentiableAt (by simp)
    have hsl : DifferentiableAt ℝ (fun τ' => Kp (s, τ')) τ :=
      hKd.comp τ ((differentiableAt_const s).prodMk differentiableAt_id)
    simp only [iteratedDeriv_zero]
    exact hsl.hasDerivAt
  | succ n ih =>
    intro s hs τ
    have hF : ContDiffOn ℝ 2
        (fun x : ℝ × ℝ => iteratedDeriv n (fun r => Kp (r, x.2)) x.1)
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
      intro x hx
      exact (psiJet_slice_contDiffAt Kp hKp n 2 hx.1 x.2).contDiffWithinAt
    have hG : ∀ r : ℝ, 0 < r → ∀ τ' : ℝ,
        HasDerivAt (fun τ'' => iteratedDeriv n (fun r' => Kp (r', τ'')) r)
          (iteratedDeriv n (fun r' => deriv (fun τ''' => Kp (r', τ''')) τ') r) τ' :=
      fun r hr τ' => ih r hr τ'
    simp only [iteratedDeriv_succ]
    exact psi_swap_step (F := fun x : ℝ × ℝ => iteratedDeriv n (fun r => Kp (r, x.2)) x.1)
      (G := fun x : ℝ × ℝ => iteratedDeriv n (fun r => deriv (fun τ' => Kp (r, τ')) x.2) x.1)
      hF hs hG τ

/-- Component of an age derivative: `∂_r^n (V(r,w))_i = (∂_r^n V(r,w))_i`, `s > 0`. -/
theorem psi_iteratedDeriv_apply (V : ℝ × (ℝ × ℝ) → UnforcedLeray.Train.Vec)
    (hV : ContDiffOn ℝ ∞ V (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (i : Fin 2) (n : ℕ) {s : ℝ}
    (hs : 0 < s) (w : ℝ × ℝ) :
    iteratedDeriv n (fun r => V (r, w) i) s = iteratedDeriv n (fun r => V (r, w)) s i := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hx : (s, w) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hs, Set.mem_univ _⟩
  let L : UnforcedLeray.Train.Vec →L[ℝ] ℝ := EuclideanSpace.proj i
  have hW : ContDiffOn ℝ ∞ (fun x => L (V x)) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    L.contDiff.comp_contDiffOn hV
  have e1 : iteratedDeriv n (fun r => L (V (r, w))) s =
      iteratedFDeriv ℝ n (fun x => L (V x)) (s, w) (fun _ => (1, 0)) :=
    vb_slice_iteratedDeriv_eq (fun x => L (V x)) hW n hs w
  have e2 : iteratedDeriv n (fun r => V (r, w)) s =
      iteratedFDeriv ℝ n V (s, w) (fun _ => (1, 0)) :=
    vb_slice_iteratedDeriv_eq V hV n hs w
  have hcomp : iteratedFDeriv ℝ n (fun x => L (V x)) (s, w) =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ n V (s, w)) := by
    have h := ContinuousLinearMap.iteratedFDerivWithin_comp_left L (hV.contDiffWithinAt hx)
      hU.uniqueDiffOn hx (i := n) (mod_cast le_top)
    rwa [iteratedFDerivWithin_of_isOpen n hU hx, iteratedFDerivWithin_of_isOpen n hU hx] at h
  have e3 : iteratedDeriv n (fun r => V (r, w) i) s = iteratedDeriv n (fun r => L (V (r, w))) s :=
    rfl
  rw [e3, e1, hcomp, e2]
  rfl

end UnforcedLeray.Short.IIb
