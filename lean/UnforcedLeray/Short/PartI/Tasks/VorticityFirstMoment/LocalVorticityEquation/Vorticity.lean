import UnforcedLeray.Units.B0238.VorticityEq
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation.Layer

/-!
# `LocalVorticityEquation` helper: the vorticity equation on an open set

Generic form of `Units/B0238/VorticityEq.lean` (`vorticityResidual_eq_zero`): the region `s > 0`
is replaced by an open set `O ⊆ ℝ × Plane`. The slab hypothesis `hslab` (membership in `O` does not
depend on `z`) replaces the fact that `{s > 0}` is independent of `z`; it is used only to take
`z`-slices of partial derivatives. For `O = Ioo 0 T ×ˢ univ` it holds trivially.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI.LV

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

/-- Component `k` of a velocity field, as a space-time function. -/
def lvFc (u : ℝ → Plane → Vec) (k : Fin 2) : ℝ × Plane → ℝ := fun x => u x.1 x.2 k

/-- A scalar field, as a space-time function. -/
def lvFs (p : ℝ → Plane → ℝ) : ℝ × Plane → ℝ := fun x => p x.1 x.2

/-- The vorticity `∂_q u₂ - ∂_η u₁` in space-time directional derivatives. -/
def lvWv (u : ℝ → Plane → Vec) : ℝ × Plane → ℝ :=
  fun y => lvDir lvEQ (lvFc u 1) y - lvDir lvEE (lvFc u 0) y

theorem lvFc_apply (u : ℝ → Plane → Vec) (k : Fin 2) (s : ℝ) (z : Plane) :
    lvFc u k (s, z) = u s z k := rfl

section Fields

variable {O : Set (ℝ × Plane)} {u : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}

theorem lvSm_Fc (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) O) (k : Fin 2) :
    lvSm O (lvFc u k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn hu

theorem lvSm_Fs (hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) O) : lvSm O (lvFs p) :=
  hp

variable (hO : IsOpen O) (hslab : ∀ (s : ℝ) (z z' : Plane), (s, z) ∈ O → (s, z') ∈ O)
  (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) O)
include hO hslab hu

theorem lvSm_Wv : lvSm O (lvWv u) :=
  lvSm.sub (lvSm.dir hO (lvSm_Fc hu 1) lvEQ) (lvSm.dir hO (lvSm_Fc hu 0) lvEE)

theorem lvPQ {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) (k : Fin 2) :
    Cyl.partialQ (fun w => u s w k) z = lvDir lvEQ (lvFc u k) (s, z) :=
  lvSliceQ (lvSm.differentiableAt hO (lvSm_Fc hu k) hx)

theorem lvPE {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) (k : Fin 2) :
    Cyl.partialEta (fun w => u s w k) z = lvDir lvEE (lvFc u k) (s, z) :=
  lvSliceE (lvSm.differentiableAt hO (lvSm_Fc hu k) hx)

theorem lvPQQ {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) (k : Fin 2) :
    Cyl.partialQ (Cyl.partialQ (fun w => u s w k)) z =
      lvDir lvEQ (lvDir lvEQ (lvFc u k)) (s, z) := by
  have h : Cyl.partialQ (fun w => u s w k) = fun z' => lvDir lvEQ (lvFc u k) (s, z') :=
    funext fun z' => lvPQ hO hslab hu (hslab s z z' hx) k
  rw [h]
  exact lvSliceQ (lvSm.differentiableAt hO (lvSm.dir hO (lvSm_Fc hu k) lvEQ) hx)

theorem lvPEE {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) (k : Fin 2) :
    Cyl.partialEta (Cyl.partialEta (fun w => u s w k)) z =
      lvDir lvEE (lvDir lvEE (lvFc u k)) (s, z) := by
  have h : Cyl.partialEta (fun w => u s w k) = fun z' => lvDir lvEE (lvFc u k) (s, z') :=
    funext fun z' => lvPE hO hslab hu (hslab s z z' hx) k
  rw [h]
  exact lvSliceE (lvSm.differentiableAt hO (lvSm.dir hO (lvSm_Fc hu k) lvEE) hx)

theorem lvPT {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) (k : Fin 2) :
    (deriv (fun t => u t z) s) k = lvDir lvEt (lvFc u k) (s, z) := by
  have hU0 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) O := hu
  have hU : DifferentiableAt ℝ (fun x : ℝ × Plane => u x.1 x.2) (s, z) :=
    (ContDiffOn.contDiffAt hU0 (hO.mem_nhds hx)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun t => u t z)
      (fderiv ℝ (fun x : ℝ × Plane => u x.1 x.2) (s, z) lvEt) s := by
    have h0 : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × Plane)) lvEt s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s z)
    exact hU.hasFDerivAt.comp_hasDerivAt s h0
  rw [h1.deriv]
  have h2 : HasFDerivAt (lvFc u k)
      ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ (fun x : ℝ × Plane => u x.1 x.2) (s, z)))
      (s, z) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp (s, z) hU.hasFDerivAt
  simp only [lvDir]
  rw [h2.fderiv]
  rfl

theorem lvCurl_slice {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) :
    Cyl.curl (u s) z = lvWv u (s, z) := by
  rw [Cyl.curl, lvPQ hO hslab hu hx, lvPE hO hslab hu hx]
  rfl

end Fields

/-- **The vorticity equation on an open set `O`** (generic form of `vorticityResidual_eq_zero`).
If `u, p` are `C^∞` on `O`, `div u = 0` and the momentum equation holds on `O`, then
`∂_s ω + u·∇ω - νΔω = 0` at every point of `O`, where `ω(s) = curl u(s)`. -/
theorem lvVorticityResidual_eq_zero {O : Set (ℝ × Plane)} (hO : IsOpen O)
    (hslab : ∀ (s : ℝ) (z z' : Plane), (s, z) ∈ O → (s, z') ∈ O)
    {ν : ℝ} {u : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) O)
    (hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) O)
    (hdiv : ∀ (s : ℝ) (z : Plane), (s, z) ∈ O → Cyl.divergence (u s) z = 0)
    (hmom : ∀ (s : ℝ) (z : Plane), (s, z) ∈ O → Train.momentumResidual ν u p s z = 0)
    {s : ℝ} {z : Plane} (hx : (s, z) ∈ O) :
    UnforcedLeray.B0238.vorticityResidual ν u s z = 0 := by
  have h0 := lvSm_Fc hu 0
  have h1 := lvSm_Fc hu 1
  have hP := lvSm_Fs hp
  have hW := lvSm_Wv hO hslab hu
  -- the time slice of `O` through `(s, z)` is a neighbourhood of `s`
  have hnhds : ∀ᶠ t in 𝓝 s, (t, z) ∈ O := by
    have hc : Continuous (fun t : ℝ => (t, z)) := by fun_prop
    exact (hO.preimage hc).mem_nhds (show s ∈ (fun t : ℝ => (t, z)) ⁻¹' O from hx)
  -- the vorticity as a space-time function
  have hcurl : Cyl.curl (u s) = fun z' => lvWv u (s, z') :=
    funext fun z' => lvCurl_slice hO hslab hu (hslab s z z' hx)
  have hT : deriv (fun t => Cyl.curl (u t) z) s = lvDir lvEt (lvWv u) (s, z) := by
    have he : (fun t => Cyl.curl (u t) z) =ᶠ[𝓝 s] fun t => lvWv u (t, z) := by
      filter_upwards [hnhds] with t ht using lvCurl_slice hO hslab hu ht
    rw [he.deriv_eq]
    exact lvSliceT (lvSm.differentiableAt hO hW hx)
  have hQ : Cyl.partialQ (Cyl.curl (u s)) z = lvDir lvEQ (lvWv u) (s, z) := by
    rw [hcurl]
    exact lvSliceQ (lvSm.differentiableAt hO hW hx)
  have hE : Cyl.partialEta (Cyl.curl (u s)) z = lvDir lvEE (lvWv u) (s, z) := by
    rw [hcurl]
    exact lvSliceE (lvSm.differentiableAt hO hW hx)
  have hLap : Train.lapS (Cyl.curl (u s)) z =
      lvDir lvEQ (lvDir lvEQ (lvWv u)) (s, z) + lvDir lvEE (lvDir lvEE (lvWv u)) (s, z) := by
    have hq : Cyl.partialQ (fun z' => lvWv u (s, z')) = fun z' => lvDir lvEQ (lvWv u) (s, z') :=
      funext fun z' => lvSliceQ (lvSm.differentiableAt hO hW (hslab s z z' hx))
    have he : Cyl.partialEta (fun z' => lvWv u (s, z')) = fun z' => lvDir lvEE (lvWv u) (s, z') :=
      funext fun z' => lvSliceE (lvSm.differentiableAt hO hW (hslab s z z' hx))
    rw [Train.lapS, hcurl, hq, he,
      lvSliceQ (lvSm.differentiableAt hO (lvSm.dir hO hW lvEQ) hx),
      lvSliceE (lvSm.differentiableAt hO (lvSm.dir hO hW lvEE) hx)]
  rw [UnforcedLeray.B0238.vorticityResidual, hT, hQ, hE, hLap]
  -- expansion of the vorticity
  have eT1 : lvDir lvEt (lvWv u) (s, z) =
      lvDir lvEt (lvDir lvEQ (lvFc u 1)) (s, z) - lvDir lvEt (lvDir lvEE (lvFc u 0)) (s, z) :=
    lvDir_sub hO (lvSm.dir hO h1 lvEQ) (lvSm.dir hO h0 lvEE) hx lvEt
  have eQ1 : lvDir lvEQ (lvWv u) (s, z) =
      lvDir lvEQ (lvDir lvEQ (lvFc u 1)) (s, z) - lvDir lvEQ (lvDir lvEE (lvFc u 0)) (s, z) :=
    lvDir_sub hO (lvSm.dir hO h1 lvEQ) (lvSm.dir hO h0 lvEE) hx lvEQ
  have eE1 : lvDir lvEE (lvWv u) (s, z) =
      lvDir lvEE (lvDir lvEQ (lvFc u 1)) (s, z) - lvDir lvEE (lvDir lvEE (lvFc u 0)) (s, z) :=
    lvDir_sub hO (lvSm.dir hO h1 lvEQ) (lvSm.dir hO h0 lvEE) hx lvEE
  have eQQ : lvDir lvEQ (lvDir lvEQ (lvWv u)) (s, z) =
      lvDir lvEQ (lvDir lvEQ (lvDir lvEQ (lvFc u 1))) (s, z) -
        lvDir lvEQ (lvDir lvEQ (lvDir lvEE (lvFc u 0))) (s, z) := by
    rw [lvDir_congr hO (H₁ := lvDir lvEQ (lvWv u))
      (H₂ := fun y => lvDir lvEQ (lvDir lvEQ (lvFc u 1)) y - lvDir lvEQ (lvDir lvEE (lvFc u 0)) y)
      (fun y hy => lvDir_sub hO (lvSm.dir hO h1 lvEQ) (lvSm.dir hO h0 lvEE) hy lvEQ) hx]
    exact lvDir_sub hO (lvSm.dir hO (lvSm.dir hO h1 lvEQ) lvEQ)
      (lvSm.dir hO (lvSm.dir hO h0 lvEE) lvEQ) hx lvEQ
  have eEE : lvDir lvEE (lvDir lvEE (lvWv u)) (s, z) =
      lvDir lvEE (lvDir lvEE (lvDir lvEQ (lvFc u 1))) (s, z) -
        lvDir lvEE (lvDir lvEE (lvDir lvEE (lvFc u 0))) (s, z) := by
    rw [lvDir_congr hO (H₁ := lvDir lvEE (lvWv u))
      (H₂ := fun y => lvDir lvEE (lvDir lvEQ (lvFc u 1)) y - lvDir lvEE (lvDir lvEE (lvFc u 0)) y)
      (fun y hy => lvDir_sub hO (lvSm.dir hO h1 lvEQ) (lvSm.dir hO h0 lvEE) hy lvEE) hx]
    exact lvDir_sub hO (lvSm.dir hO (lvSm.dir hO h1 lvEQ) lvEE)
      (lvSm.dir hO (lvSm.dir hO h0 lvEE) lvEE) hx lvEE
  -- the momentum equation in space-time form, on `O`
  have M1 : ∀ y ∈ O, lvDir lvEt (lvFc u 1) y + (lvFc u 0 y * lvDir lvEQ (lvFc u 1) y +
      lvFc u 1 y * lvDir lvEE (lvFc u 1) y) - ν * (lvDir lvEQ (lvDir lvEQ (lvFc u 1)) y +
      lvDir lvEE (lvDir lvEE (lvFc u 1)) y) + lvDir lvEE (lvFs p) y = 0 := by
    rintro ⟨t, w⟩ ht
    have m := congrArg (fun X : Vec => X 1) (hmom t w ht)
    simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
      Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Train.toVec_one, PiLp.zero_apply] at m
    have hpE : Cyl.partialEta (p t) w = lvDir lvEE (lvFs p) (t, w) :=
      lvSliceE (H := lvFs p) (lvSm.differentiableAt hO hP ht)
    rw [lvPQQ hO hslab hu ht, lvPEE hO hslab hu ht, lvPT hO hslab hu ht, lvPQ hO hslab hu ht,
      lvPE hO hslab hu ht, hpE] at m
    exact m
  have M0 : ∀ y ∈ O, lvDir lvEt (lvFc u 0) y + (lvFc u 0 y * lvDir lvEQ (lvFc u 0) y +
      lvFc u 1 y * lvDir lvEE (lvFc u 0) y) - ν * (lvDir lvEQ (lvDir lvEQ (lvFc u 0)) y +
      lvDir lvEE (lvDir lvEE (lvFc u 0)) y) + lvDir lvEQ (lvFs p) y = 0 := by
    rintro ⟨t, w⟩ ht
    have m := congrArg (fun X : Vec => X 0) (hmom t w ht)
    simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
      Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Train.toVec_zero, PiLp.zero_apply] at m
    have hpQ : Cyl.partialQ (p t) w = lvDir lvEQ (lvFs p) (t, w) :=
      lvSliceQ (H := lvFs p) (lvSm.differentiableAt hO hP ht)
    rw [lvPQQ hO hslab hu ht, lvPEE hO hslab hu ht, lvPT hO hslab hu ht, lvPQ hO hslab hu ht,
      lvPE hO hslab hu ht, hpQ] at m
    exact m
  have dM1 := (lvDir_mom hO (lvSm.dir hO h1 lvEt) h0 (lvSm.dir hO h1 lvEQ) h1
    (lvSm.dir hO h1 lvEE) (lvSm.dir hO (lvSm.dir hO h1 lvEQ) lvEQ)
    (lvSm.dir hO (lvSm.dir hO h1 lvEE) lvEE) (lvSm.dir hO hP lvEE) ν hx lvEQ).symm.trans
    (lvDir_eq_zero hO (H := fun y => lvDir lvEt (lvFc u 1) y + (lvFc u 0 y * lvDir lvEQ (lvFc u 1) y +
      lvFc u 1 y * lvDir lvEE (lvFc u 1) y) - ν * (lvDir lvEQ (lvDir lvEQ (lvFc u 1)) y +
      lvDir lvEE (lvDir lvEE (lvFc u 1)) y) + lvDir lvEE (lvFs p) y) M1 hx lvEQ)
  have dM0 := (lvDir_mom hO (lvSm.dir hO h0 lvEt) h0 (lvSm.dir hO h0 lvEQ) h1
    (lvSm.dir hO h0 lvEE) (lvSm.dir hO (lvSm.dir hO h0 lvEQ) lvEQ)
    (lvSm.dir hO (lvSm.dir hO h0 lvEE) lvEE) (lvSm.dir hO hP lvEQ) ν hx lvEE).symm.trans
    (lvDir_eq_zero hO (H := fun y => lvDir lvEt (lvFc u 0) y + (lvFc u 0 y * lvDir lvEQ (lvFc u 0) y +
      lvFc u 1 y * lvDir lvEE (lvFc u 0) y) - ν * (lvDir lvEQ (lvDir lvEQ (lvFc u 0)) y +
      lvDir lvEE (lvDir lvEE (lvFc u 0)) y) + lvDir lvEQ (lvFs p) y) M0 hx lvEE)
  -- divergence free
  have hD : lvDir lvEQ (lvFc u 0) (s, z) + lvDir lvEE (lvFc u 1) (s, z) = 0 := by
    have h := hdiv s z hx
    rw [Cyl.divergence, lvPQ hO hslab hu hx, lvPE hO hslab hu hx] at h
    exact h
  -- symmetry of second and third derivatives
  have S1 : lvDir lvEQ (lvDir lvEt (lvFc u 1)) (s, z) =
      lvDir lvEt (lvDir lvEQ (lvFc u 1)) (s, z) :=
    lvDir_symm hO h1 hx _ _
  have S2 : lvDir lvEE (lvDir lvEt (lvFc u 0)) (s, z) =
      lvDir lvEt (lvDir lvEE (lvFc u 0)) (s, z) :=
    lvDir_symm hO h0 hx _ _
  have S3 : lvDir lvEQ (lvDir lvEE (lvFc u 1)) (s, z) =
      lvDir lvEE (lvDir lvEQ (lvFc u 1)) (s, z) :=
    lvDir_symm hO h1 hx _ _
  have S4 : lvDir lvEE (lvDir lvEQ (lvFc u 0)) (s, z) =
      lvDir lvEQ (lvDir lvEE (lvFc u 0)) (s, z) :=
    lvDir_symm hO h0 hx _ _
  have S5 : lvDir lvEQ (lvDir lvEE (lvFs p)) (s, z) =
      lvDir lvEE (lvDir lvEQ (lvFs p)) (s, z) :=
    lvDir_symm hO hP hx _ _
  have S6 : lvDir lvEQ (lvDir lvEE (lvDir lvEE (lvFc u 1))) (s, z) =
      lvDir lvEE (lvDir lvEE (lvDir lvEQ (lvFc u 1))) (s, z) := by
    rw [lvDir_symm hO (lvSm.dir hO h1 lvEE) hx lvEQ lvEE]
    exact lvDir_congr hO (fun y hy => lvDir_symm hO h1 hy lvEQ lvEE) hx lvEE
  have S7 : lvDir lvEE (lvDir lvEQ (lvDir lvEQ (lvFc u 0))) (s, z) =
      lvDir lvEQ (lvDir lvEQ (lvDir lvEE (lvFc u 0))) (s, z) := by
    rw [lvDir_symm hO (lvSm.dir hO h0 lvEQ) hx lvEE lvEQ]
    exact lvDir_congr hO (fun y hy => lvDir_symm hO h0 hy lvEE lvEQ) hx lvEQ
  rw [S1, S3, S5, S6] at dM1
  rw [S2, S4, S7] at dM0
  rw [eT1, eQ1, eE1, eQQ, eEE, ← lvFc_apply u 0 s z, ← lvFc_apply u 1 s z]
  linear_combination dM1 - dM0 - (lvDir lvEQ (lvFc u 1) (s, z) - lvDir lvEE (lvFc u 0) (s, z)) * hD

end UnforcedLeray.Short.PartI.LV
