import UnforcedLeray.Short.PartI.Sub.T02_1_5

/-!
# Part I, task `PartI:T02/1/5/1`: the one-sided force of a Leray velocity is smooth

Source of record: `the November 2 reference manuscript`, lines 261-288 (the force
of Leaf 2 in `Short/PartI/Sub/T02_1_5.lean`).

Target: `lerayForceSmooth : LerayForceSmooth`.  With `V x = v x.1 x.2` on the closed set
`S = [0,T] × ℝ²`, the one-sided derivatives `D = fderivWithin ℝ V S` and `D2 = fderivWithin ℝ D S`
are `C^∞` on `S` (`ContDiffOn.fderivWithin`, applied twice).  The force is the momentum residual
written with `D` and `D2` in place of the derivatives.  On `(0,T) × ℝ²`, which is open and
contained in `S`, the within-derivatives are ordinary derivatives, and the chain rule identifies the
force with `Train.momentumResidual` at zero pressure.  Periodicity: `V (x + p) = V x` on `S` for
`p = (0,(c,0))`, and `fderivWithin` is invariant under this translation of `S` (its linear part is
the identity).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec toVecL)
open UnforcedLeray.Cyl (Plane)

namespace ForceSmoothAux

/-- The closed set `[0,T] × ℝ²` on which the one-sided calculus is taken. -/
abbrev Sset (T : ℝ) : Set (ℝ × Plane) := Icc (0 : ℝ) T ×ˢ (univ : Set Plane)

/-- The velocity as a function of the space-time point `x = (s, z)`. -/
def Vf (v : ℝ → Plane → Vec) : ℝ × Plane → Vec := fun x => v x.1 x.2

/-- The one-sided first derivative of `Vf` on `[0,T] × ℝ²`. -/
def Dfw (v : ℝ → Plane → Vec) (T : ℝ) : ℝ × Plane → ((ℝ × Plane) →L[ℝ] Vec) :=
  fderivWithin ℝ (Vf v) (Sset T)

/-- The one-sided second derivative. -/
def D2fw (v : ℝ → Plane → Vec) (T : ℝ) :
    ℝ × Plane → ((ℝ × Plane) →L[ℝ] ((ℝ × Plane) →L[ℝ] Vec)) :=
  fderivWithin ℝ (Dfw v T) (Sset T)

/-- The spatial translation vector `(0, (c, 0))` of `ℝ × Plane`. -/
def pvec (c : ℝ) : ℝ × Plane := (0, (c, 0))

theorem add_pvec (c : ℝ) (y : ℝ × Plane) : y + pvec c = (y.1, (y.2.1 + c, y.2.2)) := by
  ext <;> simp [pvec]

/-- The one-sided force: the momentum residual with the one-sided derivatives `Dfw`, `D2fw`. -/
def Gfun (ν : ℝ) (v : ℝ → Plane → Vec) (T : ℝ) (x : ℝ × Plane) : Vec :=
  Dfw v T x (1, 0)
    + toVec (Vf v x 0 * Dfw v T x (0, (1, 0)) 0 + Vf v x 1 * Dfw v T x (0, (0, 1)) 0,
        Vf v x 0 * Dfw v T x (0, (1, 0)) 1 + Vf v x 1 * Dfw v T x (0, (0, 1)) 1)
    - ν • toVec (D2fw v T x (0, (1, 0)) (0, (1, 0)) 0 + D2fw v T x (0, (0, 1)) (0, (0, 1)) 0,
        D2fw v T x (0, (1, 0)) (0, (1, 0)) 1 + D2fw v T x (0, (0, 1)) (0, (0, 1)) 1)

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniqueDiffOn_Sset {T : ℝ} (hT : 0 < T) : UniqueDiffOn ℝ (Sset T) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

theorem mem_Sset_of_Ioo {T s : ℝ} (z : Plane) (hs : s ∈ Ioo (0 : ℝ) T) : (s, z) ∈ Sset T :=
  ⟨Ioo_subset_Icc_self hs, mem_univ _⟩

theorem Sset_mem_nhds {T s : ℝ} (z : Plane) (hs : s ∈ Ioo (0 : ℝ) T) : Sset T ∈ 𝓝 (s, z) := by
  have hU : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hmem : (s, z) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) := ⟨hs, mem_univ _⟩
  exact Filter.mem_of_superset (hU.mem_nhds hmem) (Set.prod_mono Ioo_subset_Icc_self subset_rfl)

theorem contDiffOn_Dfw {v : ℝ → Plane → Vec} {T : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T)) : ContDiffOn ℝ ∞ (Dfw v T) (Sset T) :=
  hV.fderivWithin (uniqueDiffOn_Sset hT) (by simp)

theorem contDiffOn_D2fw {v : ℝ → Plane → Vec} {T : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T)) : ContDiffOn ℝ ∞ (D2fw v T) (Sset T) :=
  (contDiffOn_Dfw hT hV).fderivWithin (uniqueDiffOn_Sset hT) (by simp)

theorem differentiableAt_Vf {v : ℝ → Plane → Vec} {T s : ℝ}
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T)) (z : Plane) (hs : s ∈ Ioo (0 : ℝ) T) :
    DifferentiableAt ℝ (Vf v) (s, z) :=
  ((hV.differentiableOn (by simp)) (s, z) (mem_Sset_of_Ioo z hs)).differentiableAt
    (Sset_mem_nhds z hs)

theorem differentiableAt_Dfw {v : ℝ → Plane → Vec} {T s : ℝ}
    (hD : ContDiffOn ℝ ∞ (Dfw v T) (Sset T)) (z : Plane) (hs : s ∈ Ioo (0 : ℝ) T) :
    DifferentiableAt ℝ (Dfw v T) (s, z) :=
  ((hD.differentiableOn (by simp)) (s, z) (mem_Sset_of_Ioo z hs)).differentiableAt
    (Sset_mem_nhds z hs)

theorem Dfw_eq_fderiv {v : ℝ → Plane → Vec} {T s : ℝ} (z : Plane) (hs : s ∈ Ioo (0 : ℝ) T) :
    Dfw v T (s, z) = fderiv ℝ (Vf v) (s, z) := by
  unfold Dfw
  exact fderivWithin_of_mem_nhds (Sset_mem_nhds z hs)

theorem D2fw_eq_fderiv {v : ℝ → Plane → Vec} {T s : ℝ} (z : Plane) (hs : s ∈ Ioo (0 : ℝ) T) :
    D2fw v T (s, z) = fderiv ℝ (Dfw v T) (s, z) := by
  unfold D2fw
  exact fderivWithin_of_mem_nhds (Sset_mem_nhds z hs)

/-! ### Slice derivatives of a function on `ℝ × Plane` -/

theorem deriv_time_slice (F : ℝ × Plane → E) (s : ℝ) (z : Plane)
    (hF : DifferentiableAt ℝ F (s, z)) :
    deriv (fun t : ℝ => F (t, z)) s = fderiv ℝ F (s, z) (1, 0) := by
  have h0 : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × Plane)) ((1 : ℝ), (0 : Plane)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  exact (hF.hasFDerivAt.comp_hasDerivAt s h0).deriv

theorem partialQ_slice (F : ℝ × Plane → E) (s : ℝ) (z : Plane)
    (hF : DifferentiableAt ℝ F (s, z)) :
    Cyl.partialQ (fun w => F (s, w)) z = fderiv ℝ F (s, z) (0, (1, 0)) := by
  have h0 : HasDerivAt (fun q : ℝ => ((s, (q, z.2)) : ℝ × Plane))
      ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) z.1 :=
    (hasDerivAt_const z.1 s).prodMk ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  exact (hF.hasFDerivAt.comp_hasDerivAt z.1 h0).deriv

theorem partialEta_slice (F : ℝ × Plane → E) (s : ℝ) (z : Plane)
    (hF : DifferentiableAt ℝ F (s, z)) :
    Cyl.partialEta (fun w => F (s, w)) z = fderiv ℝ F (s, z) (0, (0, 1)) := by
  have h0 : HasDerivAt (fun η : ℝ => ((s, (z.1, η)) : ℝ × Plane))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) z.2 :=
    (hasDerivAt_const z.2 s).prodMk ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact (hF.hasFDerivAt.comp_hasDerivAt z.2 h0).deriv

/-! ### Components of `Vec`-valued functions -/

theorem hasFDerivAt_proj {F : ℝ × Plane → Vec} {x : ℝ × Plane} (hF : DifferentiableAt ℝ F x)
    (i : Fin 2) :
    HasFDerivAt (fun y => F y i) ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ F x)) x :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt

theorem fderiv_proj {F : ℝ × Plane → Vec} {x : ℝ × Plane} (hF : DifferentiableAt ℝ F x)
    (i : Fin 2) (u : ℝ × Plane) :
    fderiv ℝ (fun y => F y i) x u = fderiv ℝ F x u i := by
  rw [(hasFDerivAt_proj hF i).fderiv]
  rfl

theorem hasFDerivAt_apply_proj {L : ℝ × Plane → ((ℝ × Plane) →L[ℝ] Vec)} {x : ℝ × Plane}
    (hL : DifferentiableAt ℝ L x) (w : ℝ × Plane) (i : Fin 2) :
    HasFDerivAt (fun y => L y w i)
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp ((fderiv ℝ L x).flip w)) x := by
  have h1 : HasFDerivAt (fun y => L y w) ((fderiv ℝ L x).flip w) x := by
    have h := hL.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using h
  exact (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp x h1

theorem fderiv_apply_proj {L : ℝ × Plane → ((ℝ × Plane) →L[ℝ] Vec)} {x : ℝ × Plane}
    (hL : DifferentiableAt ℝ L x) (w u : ℝ × Plane) (i : Fin 2) :
    fderiv ℝ (fun y => L y w i) x u = fderiv ℝ L x u w i := by
  rw [(hasFDerivAt_apply_proj hL w i).fderiv]
  rfl

/-! ### Smoothness on `S` -/

theorem contDiffOn_proj {S' : Set (ℝ × Plane)} {L : ℝ × Plane → Vec} (hL : ContDiffOn ℝ ∞ L S')
    (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => L x i) S' :=
  (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hL

theorem contDiffOn_toVec_pair {S' : Set (ℝ × Plane)} {a b : ℝ × Plane → ℝ}
    (ha : ContDiffOn ℝ ∞ a S') (hb : ContDiffOn ℝ ∞ b S') :
    ContDiffOn ℝ ∞ (fun x => toVec (a x, b x)) S' :=
  toVecL.contDiff.comp_contDiffOn (ha.prodMk hb)

theorem contDiffOn_Gfun {ν : ℝ} {v : ℝ → Plane → Vec} {T : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T)) : ContDiffOn ℝ ∞ (Gfun ν v T) (Sset T) := by
  have hD := contDiffOn_Dfw hT hV
  have hD2 := contDiffOn_D2fw hT hV
  have hq : ContDiffOn ℝ ∞ (fun x => Dfw v T x (0, (1, 0))) (Sset T) :=
    hD.clm_apply contDiffOn_const
  have he : ContDiffOn ℝ ∞ (fun x => Dfw v T x (0, (0, 1))) (Sset T) :=
    hD.clm_apply contDiffOn_const
  have hA : ContDiffOn ℝ ∞ (fun x => Dfw v T x (1, 0)) (Sset T) :=
    hD.clm_apply contDiffOn_const
  have hqq : ContDiffOn ℝ ∞ (fun x => D2fw v T x (0, (1, 0)) (0, (1, 0))) (Sset T) :=
    (hD2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hee : ContDiffOn ℝ ∞ (fun x => D2fw v T x (0, (0, 1)) (0, (0, 1))) (Sset T) :=
    (hD2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hV0 : ContDiffOn ℝ ∞ (fun x => Vf v x 0) (Sset T) := contDiffOn_proj hV 0
  have hV1 : ContDiffOn ℝ ∞ (fun x => Vf v x 1) (Sset T) := contDiffOn_proj hV 1
  have hA0 : ContDiffOn ℝ ∞ (fun x => Vf v x 0 * Dfw v T x (0, (1, 0)) 0
      + Vf v x 1 * Dfw v T x (0, (0, 1)) 0) (Sset T) :=
    (hV0.mul (contDiffOn_proj hq 0)).add (hV1.mul (contDiffOn_proj he 0))
  have hA1 : ContDiffOn ℝ ∞ (fun x => Vf v x 0 * Dfw v T x (0, (1, 0)) 1
      + Vf v x 1 * Dfw v T x (0, (0, 1)) 1) (Sset T) :=
    (hV0.mul (contDiffOn_proj hq 1)).add (hV1.mul (contDiffOn_proj he 1))
  have hL0 : ContDiffOn ℝ ∞ (fun x => D2fw v T x (0, (1, 0)) (0, (1, 0)) 0
      + D2fw v T x (0, (0, 1)) (0, (0, 1)) 0) (Sset T) :=
    (contDiffOn_proj hqq 0).add (contDiffOn_proj hee 0)
  have hL1 : ContDiffOn ℝ ∞ (fun x => D2fw v T x (0, (1, 0)) (0, (1, 0)) 1
      + D2fw v T x (0, (0, 1)) (0, (0, 1)) 1) (Sset T) :=
    (contDiffOn_proj hqq 1).add (contDiffOn_proj hee 1)
  unfold Gfun
  exact (hA.add (contDiffOn_toVec_pair hA0 hA1)).sub
    (ContDiffOn.const_smul ν (contDiffOn_toVec_pair hL0 hL1))

/-! ### Periodicity in `q` -/

theorem fderivWithin_add_periodic {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : ℝ × Plane → E'} {S' : Set (ℝ × Plane)} {p : ℝ × Plane}
    (hS : UniqueDiffOn ℝ S') (hSp : ∀ y ∈ S', y + p ∈ S') (hF : DifferentiableOn ℝ F S')
    (hper : ∀ y ∈ S', F (y + p) = F y) {x : ℝ × Plane} (hx : x ∈ S') :
    fderivWithin ℝ F S' x = fderivWithin ℝ F S' (x + p) := by
  have hA : DifferentiableWithinAt ℝ (fun y : ℝ × Plane => y + p) S' x :=
    ((hasFDerivAt_id x).add_const p).differentiableAt.differentiableWithinAt
  have hid : fderivWithin ℝ (fun y : ℝ × Plane => y + p) S' x
      = ContinuousLinearMap.id ℝ (ℝ × Plane) :=
    ((hasFDerivAt_id x).add_const p).hasFDerivWithinAt.fderivWithin (hS x hx)
  have key : fderivWithin ℝ (F ∘ fun y : ℝ × Plane => y + p) S' x
      = (fderivWithin ℝ F S' (x + p)).comp
          (fderivWithin ℝ (fun y : ℝ × Plane => y + p) S' x) :=
    fderivWithin_comp (f := fun y : ℝ × Plane => y + p) (g := F) x (hF (x + p) (hSp x hx)) hA
      (fun y hy => hSp y hy) (hS x hx)
  have hcongr : fderivWithin ℝ (fun y => F (y + p)) S' x = fderivWithin ℝ F S' x :=
    fderivWithin_congr (fun y hy => hper y hy) (hper x hx)
  rw [hid, ContinuousLinearMap.comp_id] at key
  rw [← hcongr]
  exact key

theorem add_pvec_mem_Sset (T c : ℝ) : ∀ y ∈ Sset T, y + pvec c ∈ Sset T := by
  intro y hy
  rw [add_pvec]
  exact ⟨(Set.mem_prod.mp hy).1, mem_univ _⟩

theorem Vf_periodic {v : ℝ → Plane → Vec} {T c : ℝ}
    (hper : ∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (v s)) :
    ∀ y ∈ Sset T, Vf v (y + pvec c) = Vf v y := by
  intro y hy
  rw [add_pvec]
  exact hper y.1 (Set.mem_prod.mp hy).1 y.2

theorem Dfw_periodic {v : ℝ → Plane → Vec} {T c : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T))
    (hper : ∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (v s)) :
    ∀ y ∈ Sset T, Dfw v T (y + pvec c) = Dfw v T y := by
  intro y hy
  exact (fderivWithin_add_periodic (F := Vf v) (uniqueDiffOn_Sset hT)
    (add_pvec_mem_Sset T c) (hV.differentiableOn (by simp)) (Vf_periodic hper) hy).symm

theorem D2fw_periodic {v : ℝ → Plane → Vec} {T c : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T))
    (hper : ∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (v s)) :
    ∀ y ∈ Sset T, D2fw v T (y + pvec c) = D2fw v T y := by
  intro y hy
  exact (fderivWithin_add_periodic (F := Dfw v T) (uniqueDiffOn_Sset hT)
    (add_pvec_mem_Sset T c) ((contDiffOn_Dfw hT hV).differentiableOn (by simp))
    (Dfw_periodic hT hV hper) hy).symm

theorem Gfun_add_pvec {ν : ℝ} {v : ℝ → Plane → Vec} {T c : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T))
    (hper : ∀ s ∈ Icc (0 : ℝ) T, Cyl.IsPeriodic c (v s)) :
    ∀ y ∈ Sset T, Gfun ν v T (y + pvec c) = Gfun ν v T y := by
  intro y hy
  have hD := Dfw_periodic hT hV hper y hy
  have hD2 := D2fw_periodic hT hV hper y hy
  have hV' := Vf_periodic hper y hy
  unfold Gfun
  rw [hD, hD2, hV']

/-! ### The force equals the momentum residual on `(0,T)` -/

theorem momentumResidual_eq_Gfun {ν : ℝ} {v : ℝ → Plane → Vec} {T s : ℝ} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Vf v) (Sset T)) (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Train.momentumResidual ν v (fun _ _ => (0 : ℝ)) s z = Gfun ν v T (s, z) := by
  have hD := contDiffOn_Dfw hT hV
  have hPq : ∀ (i : Fin 2) (w : Plane),
      Cyl.partialQ (fun u => v s u i) w = Dfw v T (s, w) (0, (1, 0)) i := by
    intro i w
    have h1 := partialQ_slice (fun y : ℝ × Plane => (Vf v y i : ℝ)) s w
      (hasFDerivAt_proj (differentiableAt_Vf hV w hs) i).differentiableAt
    have h2 := fderiv_proj (differentiableAt_Vf hV w hs) i (0, (1, 0))
    rw [Dfw_eq_fderiv (v := v) w hs]
    exact h1.trans h2
  have hPe : ∀ (i : Fin 2) (w : Plane),
      Cyl.partialEta (fun u => v s u i) w = Dfw v T (s, w) (0, (0, 1)) i := by
    intro i w
    have h1 := partialEta_slice (fun y : ℝ × Plane => (Vf v y i : ℝ)) s w
      (hasFDerivAt_proj (differentiableAt_Vf hV w hs) i).differentiableAt
    have h2 := fderiv_proj (differentiableAt_Vf hV w hs) i (0, (0, 1))
    rw [Dfw_eq_fderiv (v := v) w hs]
    exact h1.trans h2
  have hPqq : ∀ i : Fin 2,
      Cyl.partialQ (Cyl.partialQ (fun u => v s u i)) z
        = D2fw v T (s, z) (0, (1, 0)) (0, (1, 0)) i := by
    intro i
    have hfun : Cyl.partialQ (fun u => v s u i) = fun w => Dfw v T (s, w) (0, (1, 0)) i :=
      funext (hPq i)
    have h1 := partialQ_slice (fun y : ℝ × Plane => (Dfw v T y (0, (1, 0)) i : ℝ)) s z
      (hasFDerivAt_apply_proj (differentiableAt_Dfw hD z hs) (0, (1, 0)) i).differentiableAt
    have h2 := fderiv_apply_proj (differentiableAt_Dfw hD z hs) (0, (1, 0)) (0, (1, 0)) i
    rw [hfun, D2fw_eq_fderiv (v := v) z hs]
    exact h1.trans h2
  have hPee : ∀ i : Fin 2,
      Cyl.partialEta (Cyl.partialEta (fun u => v s u i)) z
        = D2fw v T (s, z) (0, (0, 1)) (0, (0, 1)) i := by
    intro i
    have hfun : Cyl.partialEta (fun u => v s u i) = fun w => Dfw v T (s, w) (0, (0, 1)) i :=
      funext (hPe i)
    have h1 := partialEta_slice (fun y : ℝ × Plane => (Dfw v T y (0, (0, 1)) i : ℝ)) s z
      (hasFDerivAt_apply_proj (differentiableAt_Dfw hD z hs) (0, (0, 1)) i).differentiableAt
    have h2 := fderiv_apply_proj (differentiableAt_Dfw hD z hs) (0, (0, 1)) (0, (0, 1)) i
    rw [hfun, D2fw_eq_fderiv (v := v) z hs]
    exact h1.trans h2
  have hP1 : deriv (fun t => v t z) s = Dfw v T (s, z) (1, 0) := by
    rw [Dfw_eq_fderiv (v := v) z hs]
    exact deriv_time_slice (Vf v) s z (differentiableAt_Vf hV z hs)
  have hgrad : Train.gradS (fun _ : Plane => (0 : ℝ)) z = 0 := by
    have h1 : Cyl.partialQ (fun _ : Plane => (0 : ℝ)) z = 0 := by simp [Cyl.partialQ]
    have h2 : Cyl.partialEta (fun _ : Plane => (0 : ℝ)) z = 0 := by simp [Cyl.partialEta]
    unfold Train.gradS
    rw [h1, h2]
    exact map_zero toVecL
  unfold Train.momentumResidual Train.advection Train.vecLaplacian Train.lapS
  rw [hgrad, hP1, hPq 0 z, hPq 1 z, hPe 0 z, hPe 1 z, hPqq 0, hPqq 1, hPee 0, hPee 1, add_zero]
  unfold Gfun
  rfl

end Calculus

end ForceSmoothAux

open ForceSmoothAux in
/-- **`PartI:T02/1/5/1`.**  The one-sided force of a Leray velocity is smooth on `[0,T] × ℝ²`,
`c`-periodic in `q` on each time slice, and equal to the momentum residual with zero pressure on
`(0,T)`. -/
theorem lerayForceSmooth : LerayForceSmooth := by
  intro ν c T v hν hc1 hT hL
  have hV : ContDiffOn ℝ ∞ (Vf v) (Sset T) := hL.smooth_v
  refine ⟨fun s z => Gfun ν v T (s, z), contDiffOn_Gfun hT hV, ?_, ?_⟩
  · intro s hs z
    have hz : (s, z) ∈ Sset T := ⟨hs, mem_univ _⟩
    have h := Gfun_add_pvec (ν := ν) hT hV hL.periodic_v (s, z) hz
    rw [add_pvec] at h
    exact h
  · intro s hs z
    exact (momentumResidual_eq_Gfun hT hV hs z).symm
