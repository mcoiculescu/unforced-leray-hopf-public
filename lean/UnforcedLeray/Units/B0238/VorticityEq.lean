import UnforcedLeray.Units.B0238.SpaceTime

/-!
# B0238 helpers: the vorticity form of the exact evolution

Helper module of blueprint unit **B0238** (`unlabeled:4127`, `paper/main.tex` lines 4125–4134:
"let `(V_c, E_c)` be its exact two-dimensional Navier–Stokes evolution"; the train facts of
tex 2141–2161 and 2181: "the conservative vorticity equation").

For a velocity `u` and pressure `p` that are `C^∞` on `[0,∞) × ℝ²` (one-sided at `s = 0`), divergence
free and solving the momentum equation `∂_s u + u·∇u - νΔu + ∇p = 0` for `s > 0`
(`Train.momentumResidual`), the vorticity `ω = curl u = ∂_q u₂ - ∂_η u₁` solves
`∂_s ω + u·∇ω - νΔω = 0` for `s > 0` (`vorticityResidual_eq_zero`). Proof: take the curl of the
momentum equation; the pressure drops by symmetry of second derivatives, the time and Laplacian
terms commute with the curl (symmetry of second and third derivatives), and the advection term
gives `u·∇ω + (div u) ω`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0238

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

/-- Component `k` of a velocity field, as a space–time function. -/
def Fc (u : ℝ → Plane → Vec) (k : Fin 2) : ST → ℝ := fun x => u x.1 x.2 k

/-- A scalar field, as a space–time function. -/
def Fs (p : ℝ → Plane → ℝ) : ST → ℝ := fun x => p x.1 x.2

/-- The vorticity `∂_q u₂ - ∂_η u₁` in space–time directional derivatives. -/
def Wv (u : ℝ → Plane → Vec) : ST → ℝ := fun y => dir eQ (Fc u 1) y - dir eE (Fc u 0) y

theorem Fc_apply (u : ℝ → Plane → Vec) (k : Fin 2) (s : ℝ) (z : Plane) :
    Fc u k (s, z) = u s z k := rfl

/-- **The vorticity residual** `∂_s ω + u·∇ω - νΔω`, `ω(s) = curl u(s)`, with classical
partials. -/
def vorticityResidual (ν : ℝ) (u : ℝ → Plane → Vec) (s : ℝ) (z : Plane) : ℝ :=
  deriv (fun t => Cyl.curl (u t) z) s +
    (u s z 0 * Cyl.partialQ (Cyl.curl (u s)) z + u s z 1 * Cyl.partialEta (Cyl.curl (u s)) z) -
    ν * Train.lapS (Cyl.curl (u s)) z

section Fields

variable {ν : ℝ} {u : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}

theorem sm_Fc (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) (Ici 0 ×ˢ univ))
    (k : Fin 2) : Sm (Fc u k) := by
  have h : ContDiffOn ℝ ∞ (fun x : ST => u x.1 x.2) Opos :=
    hu.mono fun x hx => ⟨mem_Ici.2 (le_of_lt hx), mem_univ _⟩
  exact (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn h

theorem sm_Fs (hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Ici 0 ×ˢ univ)) :
    Sm (Fs p) :=
  hp.mono fun _x hx => ⟨mem_Ici.2 (le_of_lt hx), mem_univ _⟩

variable (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) (Ici 0 ×ˢ univ))
include hu

theorem pQ {s : ℝ} (hs : 0 < s) (k : Fin 2) (z : Plane) :
    Cyl.partialQ (fun w => u s w k) z = dir eQ (Fc u k) (s, z) :=
  sliceQ ((sm_Fc hu k).differentiableAt (x := (s, z)) hs)

theorem pE {s : ℝ} (hs : 0 < s) (k : Fin 2) (z : Plane) :
    Cyl.partialEta (fun w => u s w k) z = dir eE (Fc u k) (s, z) :=
  sliceE ((sm_Fc hu k).differentiableAt (x := (s, z)) hs)

theorem pQQ {s : ℝ} (hs : 0 < s) (k : Fin 2) (z : Plane) :
    Cyl.partialQ (Cyl.partialQ (fun w => u s w k)) z = dir eQ (dir eQ (Fc u k)) (s, z) := by
  have h : Cyl.partialQ (fun w => u s w k) = fun z' => dir eQ (Fc u k) (s, z') :=
    funext fun z' => pQ hu hs k z'
  rw [h]
  exact sliceQ (((sm_Fc hu k).dir eQ).differentiableAt (x := (s, z)) hs)

theorem pEE {s : ℝ} (hs : 0 < s) (k : Fin 2) (z : Plane) :
    Cyl.partialEta (Cyl.partialEta (fun w => u s w k)) z = dir eE (dir eE (Fc u k)) (s, z) := by
  have h : Cyl.partialEta (fun w => u s w k) = fun z' => dir eE (Fc u k) (s, z') :=
    funext fun z' => pE hu hs k z'
  rw [h]
  exact sliceE (((sm_Fc hu k).dir eE).differentiableAt (x := (s, z)) hs)

theorem pT {s : ℝ} (hs : 0 < s) (k : Fin 2) (z : Plane) :
    (deriv (fun t => u t z) s) k = dir eT (Fc u k) (s, z) := by
  have hU0 : ContDiffOn ℝ ∞ (fun x : ST => u x.1 x.2) Opos :=
    hu.mono fun x hx => ⟨mem_Ici.2 (le_of_lt hx), mem_univ _⟩
  have hU : DifferentiableAt ℝ (fun x : ST => u x.1 x.2) (s, z) :=
    (hU0.contDiffAt (isOpen_Opos.mem_nhds (show ((s, z) : ST) ∈ Opos from hs))).differentiableAt
      (by simp)
  have h1 : HasDerivAt (fun t => u t z) (fderiv ℝ (fun x : ST => u x.1 x.2) (s, z) eT) s := by
    have h0 : HasDerivAt (fun t : ℝ => ((t, z) : ST)) eT s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s z)
    exact hU.hasFDerivAt.comp_hasDerivAt s h0
  rw [h1.deriv]
  have h2 : HasFDerivAt (Fc u k)
      ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ (fun x : ST => u x.1 x.2) (s, z))) (s, z) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp (s, z) hU.hasFDerivAt
  simp only [dir]
  rw [h2.fderiv]
  rfl

theorem curl_slice {s : ℝ} (hs : 0 < s) (z : Plane) : Cyl.curl (u s) z = Wv u (s, z) := by
  rw [Cyl.curl, pQ hu hs, pE hu hs]; rfl

theorem sm_Wv : Sm (Wv u) := ((sm_Fc hu 1).dir eQ).sub ((sm_Fc hu 0).dir eE)

end Fields

/-- **The vorticity equation** (tex 2181, O1 of `INF16-Cylinder2DNS.md` §2.1). If `u, p` are
`C^∞` on `[0,∞) × ℝ²`, `div u = 0` and `∂_s u + u·∇u - νΔu + ∇p = 0` for `s > 0`, then
`ω(s) = curl u(s)` solves `∂_s ω + u·∇ω - νΔω = 0` for `s > 0`. -/
theorem vorticityResidual_eq_zero {ν : ℝ} {u : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => u x.1 x.2) (Ici 0 ×ˢ univ))
    (hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Ici 0 ×ˢ univ))
    (hdiv : ∀ s : ℝ, 0 < s → ∀ z, Cyl.divergence (u s) z = 0)
    (hmom : ∀ s : ℝ, 0 < s → ∀ z, Train.momentumResidual ν u p s z = 0)
    {s : ℝ} (hs : 0 < s) (z : Plane) : vorticityResidual ν u s z = 0 := by
  have h0 := sm_Fc hu 0
  have h1 := sm_Fc hu 1
  have hP := sm_Fs hp
  have hW := sm_Wv hu
  have hx : ((s, z) : ST) ∈ Opos := hs
  -- the vorticity as a space–time function
  have hcurl : Cyl.curl (u s) = fun z' => Wv u (s, z') := funext fun z' => curl_slice hu hs z'
  have hT : deriv (fun t => Cyl.curl (u t) z) s = dir eT (Wv u) (s, z) := by
    have he : (fun t => Cyl.curl (u t) z) =ᶠ[𝓝 s] fun t => Wv u (t, z) := by
      filter_upwards [lt_mem_nhds hs] with t ht using curl_slice hu ht z
    rw [he.deriv_eq]
    exact sliceT (hW.differentiableAt hx)
  have hQ : Cyl.partialQ (Cyl.curl (u s)) z = dir eQ (Wv u) (s, z) := by
    rw [hcurl]; exact sliceQ (hW.differentiableAt hx)
  have hE : Cyl.partialEta (Cyl.curl (u s)) z = dir eE (Wv u) (s, z) := by
    rw [hcurl]; exact sliceE (hW.differentiableAt hx)
  have hLap : Train.lapS (Cyl.curl (u s)) z =
      dir eQ (dir eQ (Wv u)) (s, z) + dir eE (dir eE (Wv u)) (s, z) := by
    have hq : Cyl.partialQ (fun z' => Wv u (s, z')) = fun z' => dir eQ (Wv u) (s, z') :=
      funext fun z' => sliceQ (hW.differentiableAt (x := (s, z')) hs)
    have he : Cyl.partialEta (fun z' => Wv u (s, z')) = fun z' => dir eE (Wv u) (s, z') :=
      funext fun z' => sliceE (hW.differentiableAt (x := (s, z')) hs)
    rw [Train.lapS, hcurl, hq, he, sliceQ ((hW.dir eQ).differentiableAt hx),
      sliceE ((hW.dir eE).differentiableAt hx)]
  rw [vorticityResidual, hT, hQ, hE, hLap]
  -- expansion of the vorticity
  have eT1 : dir eT (Wv u) (s, z) =
      dir eT (dir eQ (Fc u 1)) (s, z) - dir eT (dir eE (Fc u 0)) (s, z) :=
    dir_sub (h1.dir eQ) (h0.dir eE) hx eT
  have eQ1 : dir eQ (Wv u) (s, z) =
      dir eQ (dir eQ (Fc u 1)) (s, z) - dir eQ (dir eE (Fc u 0)) (s, z) :=
    dir_sub (h1.dir eQ) (h0.dir eE) hx eQ
  have eE1 : dir eE (Wv u) (s, z) =
      dir eE (dir eQ (Fc u 1)) (s, z) - dir eE (dir eE (Fc u 0)) (s, z) :=
    dir_sub (h1.dir eQ) (h0.dir eE) hx eE
  have eQQ : dir eQ (dir eQ (Wv u)) (s, z) =
      dir eQ (dir eQ (dir eQ (Fc u 1))) (s, z) - dir eQ (dir eQ (dir eE (Fc u 0))) (s, z) := by
    rw [dir_congr (H₁ := dir eQ (Wv u))
      (H₂ := fun y => dir eQ (dir eQ (Fc u 1)) y - dir eQ (dir eE (Fc u 0)) y)
      (fun y hy => dir_sub (h1.dir eQ) (h0.dir eE) hy eQ) hx]
    exact dir_sub ((h1.dir eQ).dir eQ) ((h0.dir eE).dir eQ) hx eQ
  have eEE : dir eE (dir eE (Wv u)) (s, z) =
      dir eE (dir eE (dir eQ (Fc u 1))) (s, z) - dir eE (dir eE (dir eE (Fc u 0))) (s, z) := by
    rw [dir_congr (H₁ := dir eE (Wv u))
      (H₂ := fun y => dir eE (dir eQ (Fc u 1)) y - dir eE (dir eE (Fc u 0)) y)
      (fun y hy => dir_sub (h1.dir eQ) (h0.dir eE) hy eE) hx]
    exact dir_sub ((h1.dir eQ).dir eE) ((h0.dir eE).dir eE) hx eE
  -- the momentum equation in space–time form, on `s > 0`
  have M1 : ∀ y ∈ Opos, dir eT (Fc u 1) y + (Fc u 0 y * dir eQ (Fc u 1) y +
      Fc u 1 y * dir eE (Fc u 1) y) - ν * (dir eQ (dir eQ (Fc u 1)) y +
      dir eE (dir eE (Fc u 1)) y) + dir eE (Fs p) y = 0 := by
    rintro ⟨t, w⟩ ht
    have m := congrArg (fun X : Vec => X 1) (hmom t ht w)
    simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
      Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Train.toVec_one, PiLp.zero_apply] at m
    have ht' : 0 < t := ht
    have hpE : Cyl.partialEta (p t) w = dir eE (Fs p) (t, w) :=
      sliceE (H := Fs p) (hP.differentiableAt (x := (t, w)) ht)
    rw [pQQ hu ht', pEE hu ht', pT hu ht', pQ hu ht', pE hu ht', hpE] at m
    exact m
  have M0 : ∀ y ∈ Opos, dir eT (Fc u 0) y + (Fc u 0 y * dir eQ (Fc u 0) y +
      Fc u 1 y * dir eE (Fc u 0) y) - ν * (dir eQ (dir eQ (Fc u 0)) y +
      dir eE (dir eE (Fc u 0)) y) + dir eQ (Fs p) y = 0 := by
    rintro ⟨t, w⟩ ht
    have m := congrArg (fun X : Vec => X 0) (hmom t ht w)
    simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
      Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Train.toVec_zero, PiLp.zero_apply] at m
    have ht' : 0 < t := ht
    have hpQ : Cyl.partialQ (p t) w = dir eQ (Fs p) (t, w) :=
      sliceQ (H := Fs p) (hP.differentiableAt (x := (t, w)) ht)
    rw [pQQ hu ht', pEE hu ht', pT hu ht', pQ hu ht', pE hu ht', hpQ] at m
    exact m
  have dM1 := (dir_mom (h1.dir eT) h0 (h1.dir eQ) h1 (h1.dir eE) ((h1.dir eQ).dir eQ)
    ((h1.dir eE).dir eE) (hP.dir eE) ν hx eQ).symm.trans
    (dir_eq_zero (H := fun y => dir eT (Fc u 1) y + (Fc u 0 y * dir eQ (Fc u 1) y +
      Fc u 1 y * dir eE (Fc u 1) y) - ν * (dir eQ (dir eQ (Fc u 1)) y +
      dir eE (dir eE (Fc u 1)) y) + dir eE (Fs p) y) M1 hx eQ)
  have dM0 := (dir_mom (h0.dir eT) h0 (h0.dir eQ) h1 (h0.dir eE) ((h0.dir eQ).dir eQ)
    ((h0.dir eE).dir eE) (hP.dir eQ) ν hx eE).symm.trans
    (dir_eq_zero (H := fun y => dir eT (Fc u 0) y + (Fc u 0 y * dir eQ (Fc u 0) y +
      Fc u 1 y * dir eE (Fc u 0) y) - ν * (dir eQ (dir eQ (Fc u 0)) y +
      dir eE (dir eE (Fc u 0)) y) + dir eQ (Fs p) y) M0 hx eE)
  -- divergence free
  have hD : dir eQ (Fc u 0) (s, z) + dir eE (Fc u 1) (s, z) = 0 := by
    have h := hdiv s hs z
    rw [Cyl.divergence, pQ hu hs, pE hu hs] at h
    exact h
  -- symmetry of second and third derivatives
  have S1 : dir eQ (dir eT (Fc u 1)) (s, z) = dir eT (dir eQ (Fc u 1)) (s, z) :=
    dir_symm h1 hx _ _
  have S2 : dir eE (dir eT (Fc u 0)) (s, z) = dir eT (dir eE (Fc u 0)) (s, z) :=
    dir_symm h0 hx _ _
  have S3 : dir eQ (dir eE (Fc u 1)) (s, z) = dir eE (dir eQ (Fc u 1)) (s, z) :=
    dir_symm h1 hx _ _
  have S4 : dir eE (dir eQ (Fc u 0)) (s, z) = dir eQ (dir eE (Fc u 0)) (s, z) :=
    dir_symm h0 hx _ _
  have S5 : dir eQ (dir eE (Fs p)) (s, z) = dir eE (dir eQ (Fs p)) (s, z) :=
    dir_symm hP hx _ _
  have S6 : dir eQ (dir eE (dir eE (Fc u 1))) (s, z) =
      dir eE (dir eE (dir eQ (Fc u 1))) (s, z) := by
    rw [dir_symm (h1.dir eE) hx eQ eE]
    exact dir_congr (fun y hy => dir_symm h1 hy eQ eE) hx eE
  have S7 : dir eE (dir eQ (dir eQ (Fc u 0))) (s, z) =
      dir eQ (dir eQ (dir eE (Fc u 0))) (s, z) := by
    rw [dir_symm (h0.dir eQ) hx eE eQ]
    exact dir_congr (fun y hy => dir_symm h0 hy eE eQ) hx eQ
  rw [S1, S3, S5, S6] at dM1
  rw [S2, S4, S7] at dM0
  rw [eT1, eQ1, eE1, eQQ, eEE, ← Fc_apply u 0 s z, ← Fc_apply u 1 s z]
  linear_combination dM1 - dM0 - (dir eQ (Fc u 1) (s, z) - dir eE (Fc u 0) (s, z)) * hD

end UnforcedLeray.B0238
