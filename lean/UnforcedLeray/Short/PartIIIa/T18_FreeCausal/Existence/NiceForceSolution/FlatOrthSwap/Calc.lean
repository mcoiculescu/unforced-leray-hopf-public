import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4

/-!
# Helper for `PartIII-a:T18/2/4/4` (`FlatOrthSwap`): directional derivatives on `ℝ × (ℝ × ℝ)`

`Dv a f p = ∂_a f(p)` for a real function `f` of `(s, (q, η))`. Used for the divergence identity
of the slice-wise `ψ¹ = -∂_sΦ - νΔΦ`: the symmetry of second derivatives of smooth functions
(`IsSymmSndFDerivAt`) gives the commutations needed, and `ALG` is the resulting algebraic identity.
No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.FOS

/-- The space-time variable `(s, (q, η))`. -/
abbrev V3 : Type := ℝ × (ℝ × ℝ)

/-- Directional derivative `∂_a f` of a real function on `V3`. -/
def Dv (a : V3) (f : V3 → ℝ) : V3 → ℝ := fun p => fderiv ℝ f p a

/-- The time direction. -/
def eT : V3 := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))

/-- The `q` direction (spatial, first coordinate of the cylinder). -/
def eQ : V3 := ((0 : ℝ), B0579.dir 0)

/-- The `η` direction (spatial, second coordinate of the cylinder). -/
def eH : V3 := ((0 : ℝ), B0579.dir 1)

lemma contDiff_fderiv_fos {f : V3 → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  (contDiff_infty_iff_fderiv.1 hf).2

lemma differentiable_fos {f : V3 → ℝ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

lemma contDiff_Dv {f : V3 → ℝ} (hf : ContDiff ℝ ∞ f) (a : V3) : ContDiff ℝ ∞ (Dv a f) := by
  unfold Dv
  exact (contDiff_fderiv_fos hf).clm_apply contDiff_const

lemma dv_dv_eq {f : V3 → ℝ} (hf : ContDiff ℝ ∞ f) (a b p : V3) :
    Dv a (Dv b f) p = fderiv ℝ (fderiv ℝ f) p a b := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((contDiff_fderiv_fos hf).differentiable (by simp)) p
  have h1 : fderiv ℝ (fun y => fderiv ℝ f y b) p = (fderiv ℝ (fderiv ℝ f) p).flip b := by
    have := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ f) (u := fun _ => b) hc
      (differentiableAt_const b)
    simpa using this
  unfold Dv
  rw [h1]
  rfl

/-- Symmetry of the second derivative: `∂_a ∂_b f = ∂_b ∂_a f` pointwise for smooth `f`. -/
lemma dv_comm_pt {f : V3 → ℝ} (hf : ContDiff ℝ ∞ f) (a b p : V3) :
    Dv a (Dv b f) p = Dv b (Dv a f) p := by
  rw [dv_dv_eq hf, dv_dv_eq hf]
  have hs : IsSymmSndFDerivAt ℝ f p := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  exact hs a b

lemma dv_comm_fn {f : V3 → ℝ} (hf : ContDiff ℝ ∞ f) (a b : V3) :
    Dv a (Dv b f) = Dv b (Dv a f) :=
  funext fun p => dv_comm_pt hf a b p

lemma dv_affine {f k : V3 → ℝ} (a : V3) (hf : Differentiable ℝ f) (hk : Differentiable ℝ k)
    (c d : ℝ) (p : V3) :
    Dv a (fun q => c * f q + d * k q) p = c * Dv a f p + d * Dv a k p := by
  unfold Dv
  rw [fderiv_fun_add ((hf p).const_mul c) ((hk p).const_mul d), fderiv_const_mul (hf p),
    fderiv_const_mul (hk p)]
  simp

lemma dv_add_pt {f k : V3 → ℝ} (a : V3) (hf : Differentiable ℝ f) (hk : Differentiable ℝ k)
    (p : V3) : Dv a (fun q => f q + k q) p = Dv a f p + Dv a k p := by
  unfold Dv
  rw [fderiv_fun_add (hf p) (hk p)]
  rfl

/-- If `K0 + K1 = 0` pointwise, then `∂_a K0 + ∂_a K1 = 0` pointwise (no smoothness needed). -/
lemma dv_sum_zero {K0 K1 : V3 → ℝ} (h : ∀ q, K0 q + K1 q = 0) (a q : V3) :
    Dv a K0 q + Dv a K1 q = 0 := by
  have e : K1 = fun r => -K0 r := funext fun r => by linarith [h r]
  unfold Dv
  rw [e, fderiv_fun_neg]
  simp

lemma deriv_time_fos {g : V3 → ℝ} (hg : Differentiable ℝ g) (s : ℝ) (x : ℝ × ℝ) :
    deriv (fun s' => g (s', x)) s = fderiv ℝ g (s, x) eT := by
  have hf : HasDerivAt (fun s' : ℝ => ((s', x) : V3)) ((1, (0, 0)) : V3) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  exact ((hg (s, x)).hasFDerivAt.comp_hasDerivAt s hf).deriv

lemma fderiv_slice_fos {g : V3 → ℝ} (hg : Differentiable ℝ g) (s : ℝ) (x w : ℝ × ℝ) :
    fderiv ℝ (fun y => g (s, y)) x w = fderiv ℝ g (s, x) (0, w) := by
  have hin : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : V3))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have hcomp := (hg (s, x)).hasFDerivAt.comp x hin
  have e : (fun y => g (s, y)) = g ∘ (fun y : ℝ × ℝ => ((s, y) : V3)) := rfl
  rw [e, hcomp.fderiv]
  simp

lemma pd_slice_fos {g : V3 → ℝ} (hg : Differentiable ℝ g) (j : Fin 2) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd j (fun y => g (s, y)) x = Dv (0, B0579.dir j) g (s, x) := by
  unfold B0579.pd Dv
  exact fderiv_slice_fos hg s x _

lemma pd_slice_Q {g : V3 → ℝ} (hg : Differentiable ℝ g) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd 0 (fun y => g (s, y)) x = Dv eQ g (s, x) :=
  pd_slice_fos hg 0 s x

lemma pd_slice_H {g : V3 → ℝ} (hg : Differentiable ℝ g) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd 1 (fun y => g (s, y)) x = Dv eH g (s, x) :=
  pd_slice_fos hg 1 s x

lemma lapP_slice {g : V3 → ℝ} (hg : ContDiff ℝ ∞ g) (s : ℝ) (x : ℝ × ℝ) :
    lapP (fun y => g (s, y)) x = Dv eQ (Dv eQ g) (s, x) + Dv eH (Dv eH g) (s, x) := by
  have hd : Differentiable ℝ g := differentiable_fos hg
  have h0 : B0579.pd 0 (fun y => g (s, y)) = fun y => Dv eQ g (s, y) :=
    funext fun y => pd_slice_Q hd s y
  have h1 : B0579.pd 1 (fun y => g (s, y)) = fun y => Dv eH g (s, y) :=
    funext fun y => pd_slice_H hd s y
  unfold lapP
  rw [h0, h1, pd_slice_Q (differentiable_fos (contDiff_Dv hg eQ)) s x,
    pd_slice_H (differentiable_fos (contDiff_Dv hg eH)) s x]

/-- The algebraic core of the divergence identity: for the slice fields
`F_i = -∂_T g_i - ν(∂_Q∂_Q + ∂_H∂_H) g_i` (with `(-1)`, `(-ν)` coefficients), the divergence
`∂_Q F_0 + ∂_H F_1` vanishes at `p` whenever `∂_Q g_0 + ∂_H g_1 = 0` identically. -/
lemma alg_div_fos (g0 g1 : V3 → ℝ) (h0 : ContDiff ℝ ∞ g0) (h1 : ContDiff ℝ ∞ g1) (ν : ℝ)
    (hC : ∀ q, Dv eQ g0 q + Dv eH g1 q = 0) (p : V3) :
    Dv eQ (fun q => (-1) * Dv eT g0 q + (-ν) * (Dv eQ (Dv eQ g0) q + Dv eH (Dv eH g0) q)) p +
      Dv eH (fun q => (-1) * Dv eT g1 q + (-ν) * (Dv eQ (Dv eQ g1) q + Dv eH (Dv eH g1) q)) p
      = 0 := by
  have dT0 : Differentiable ℝ (Dv eT g0) := differentiable_fos (contDiff_Dv h0 eT)
  have dHH0 : Differentiable ℝ (Dv eH (Dv eH g0)) :=
    differentiable_fos (contDiff_Dv (contDiff_Dv h0 eH) eH)
  have dQQ0 : Differentiable ℝ (Dv eQ (Dv eQ g0)) :=
    differentiable_fos (contDiff_Dv (contDiff_Dv h0 eQ) eQ)
  have dT1 : Differentiable ℝ (Dv eT g1) := differentiable_fos (contDiff_Dv h1 eT)
  have dHH1 : Differentiable ℝ (Dv eH (Dv eH g1)) :=
    differentiable_fos (contDiff_Dv (contDiff_Dv h1 eH) eH)
  have dQQ1 : Differentiable ℝ (Dv eQ (Dv eQ g1)) :=
    differentiable_fos (contDiff_Dv (contDiff_Dv h1 eQ) eQ)
  have dK0 : Differentiable ℝ (fun q => Dv eQ (Dv eQ g0) q + Dv eH (Dv eH g0) q) :=
    fun x => (dQQ0 x).add (dHH0 x)
  have dK1 : Differentiable ℝ (fun q => Dv eQ (Dv eQ g1) q + Dv eH (Dv eH g1) q) :=
    fun x => (dQQ1 x).add (dHH1 x)
  have E0 : Dv eQ (fun q => (-1) * Dv eT g0 q + (-ν) * (Dv eQ (Dv eQ g0) q + Dv eH (Dv eH g0) q)) p
      = (-1) * Dv eQ (Dv eT g0) p +
        (-ν) * (Dv eQ (Dv eQ (Dv eQ g0)) p + Dv eQ (Dv eH (Dv eH g0)) p) := by
    rw [dv_affine eQ dT0 dK0 (-1) (-ν) p, dv_add_pt eQ dQQ0 dHH0 p]
  have E1 : Dv eH (fun q => (-1) * Dv eT g1 q + (-ν) * (Dv eQ (Dv eQ g1) q + Dv eH (Dv eH g1) q)) p
      = (-1) * Dv eH (Dv eT g1) p +
        (-ν) * (Dv eH (Dv eQ (Dv eQ g1)) p + Dv eH (Dv eH (Dv eH g1)) p) := by
    rw [dv_affine eH dT1 dK1 (-1) (-ν) p, dv_add_pt eH dQQ1 dHH1 p]
  have C1 : Dv eQ (Dv eT g0) = Dv eT (Dv eQ g0) := dv_comm_fn h0 eQ eT
  have C2 : Dv eH (Dv eT g1) = Dv eT (Dv eH g1) := dv_comm_fn h1 eH eT
  have C3 : Dv eQ (Dv eH (Dv eH g0)) = Dv eH (Dv eH (Dv eQ g0)) := by
    rw [dv_comm_fn (contDiff_Dv h0 eH) eQ eH, dv_comm_fn h0 eQ eH]
  have C4 : Dv eH (Dv eQ (Dv eQ g1)) = Dv eQ (Dv eQ (Dv eH g1)) := by
    rw [dv_comm_fn (contDiff_Dv h1 eQ) eH eQ, dv_comm_fn h1 eH eQ]
  rw [E0, E1, C1, C2, C3, C4]
  have z1 : ∀ a q, Dv a (Dv eQ g0) q + Dv a (Dv eH g1) q = 0 := fun a q => dv_sum_zero hC a q
  have z2 : ∀ a b q, Dv a (Dv b (Dv eQ g0)) q + Dv a (Dv b (Dv eH g1)) q = 0 :=
    fun a b q => dv_sum_zero (fun r => z1 b r) a q
  have A := z1 eT p
  have B := z2 eQ eQ p
  have Cc := z2 eH eH p
  linear_combination (-1 : ℝ) * A + (-ν) * B + (-ν) * Cc

end UnforcedLeray.Short.IIIa.FOS
