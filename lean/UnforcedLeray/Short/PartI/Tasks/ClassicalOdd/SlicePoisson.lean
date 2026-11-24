import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Units.B0238.SpaceTime

/-!
# Part I, task `PartI:T02/3` helper: the pressure Poisson identity on every slice

Source of record: `the November 2 reference manuscript`, lines 270-288 (the bounded
periodic pressure of the classical solution; the divergence of the momentum equation gives the
pressure Poisson equation). Target: `SlicePoisson` (`Short/PartI/Sub/T02_3.lean`).

## Method

On the open set `spO T = (0,T) × ℝ²` the classical partials are space-time directional derivatives
`B0238.dir` (the `B0238/SpaceTime.lean` operators, generalised here from `{s > 0}` to `(0,T) × ℝ²`).
Taking the divergence of each momentum component, using `div v = 0` (and its `s`, `q`, `η`
derivatives) and the symmetry of mixed derivatives, gives
`Δp = -(∂_q v_q)² - 2 ∂_q v_η ∂_η v_q - (∂_η v_η)²` on `spO T`.

The endpoints `s = 0` and `s = T` are reached by continuity: `spD T w H` is the derivative within the
closed region `spS T = [0,T] × ℝ²`, it is continuous there (`ContDiffOn` on a set with unique
differentiability), and `spO T` is dense in `spS T`.

Helpers are prefixed `sp`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0238 (ST dir eQ eE eT sliceQ sliceE)

/-! ### Regions, components and closed-set derivatives -/

/-- The closed region `[0,T] × ℝ²` of space-time points. -/
def spS (T : ℝ) : Set ST := Icc (0 : ℝ) T ×ˢ univ

/-- The open region `(0,T) × ℝ²`. -/
def spO (T : ℝ) : Set ST := Ioo (0 : ℝ) T ×ˢ univ

theorem spO_subset (T : ℝ) : spO T ⊆ spS T := prod_mono Ioo_subset_Icc_self subset_rfl

theorem isOpen_spO (T : ℝ) : IsOpen (spO T) := isOpen_Ioo.prod isOpen_univ

theorem spO_mem {T s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) : ((s, z) : ST) ∈ spO T :=
  ⟨hs, mem_univ z⟩

theorem spS_mem {T s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) : ((s, z) : ST) ∈ spS T :=
  ⟨hs, mem_univ z⟩

theorem uniqueDiffOn_spS {T : ℝ} (hT : 0 < T) : UniqueDiffOn ℝ (spS T) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

/-- Component `k` of a velocity field as a space-time function. -/
def spC (v : ℝ → Plane → Vec) (k : Fin 2) : ST → ℝ := fun x => v x.1 x.2 k

/-- A pressure as a space-time function. -/
def spP (p : ℝ → Plane → ℝ) : ST → ℝ := fun x => p x.1 x.2

/-- The `w`-derivative of `H` within the closed region `spS T`. -/
def spD (T : ℝ) (w : ST) (H : ST → ℝ) (x : ST) : ℝ := fderivWithin ℝ H (spS T) x w

/-- Left-hand side of the Poisson identity minus the right-hand side, on `spS T`. -/
def spL (T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) : ST → ℝ := fun x =>
  spD T eQ (spD T eQ (spP p)) x + spD T eE (spD T eE (spP p)) x +
    (spD T eQ (spC v 0) x ^ 2 + 2 * (spD T eQ (spC v 1) x * spD T eE (spC v 0) x) +
      spD T eE (spC v 1) x ^ 2)

theorem spC_cdo {S : Set ST} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) S) (k : Fin 2) :
    ContDiffOn ℝ ∞ (spC v k) S :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn hv

/-- The closed-set derivative of a `C^∞` function is `C^∞` on `spS T`. -/
theorem spD_contDiffOn {T : ℝ} (hT : 0 < T) (w : ST) {H : ST → ℝ}
    (h : ContDiffOn ℝ ∞ H (spS T)) : ContDiffOn ℝ ∞ (spD T w H) (spS T) :=
  (h.fderivWithin (uniqueDiffOn_spS hT) (by simp)).clm_apply contDiffOn_const

/-- The `q`-partial of a slice of `H` on `[0,T]` is the closed-set derivative `spD T eQ H`. -/
theorem spD_slice_Q {T : ℝ} {H : ST → ℝ} (h : ContDiffOn ℝ ∞ H (spS T)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) :
    Cyl.partialQ (fun w => H (s, w)) z = spD T eQ H (s, z) := by
  have hd : DifferentiableWithinAt ℝ H (spS T) (s, z) :=
    h.differentiableOn (by simp) (s, z) (spS_mem hs z)
  have h2 : HasFDerivWithinAt H (fderivWithin ℝ H (spS T) (s, z)) (spS T) (s, z) :=
    hd.hasFDerivWithinAt
  have h1 : HasDerivWithinAt (fun t : ℝ => ((s, (t, z.2)) : ST)) eQ univ z.1 :=
    ((hasDerivAt_const z.1 s).prodMk
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).hasDerivWithinAt
  have hmap : MapsTo (fun t : ℝ => ((s, (t, z.2)) : ST)) univ (spS T) :=
    fun t _ => ⟨hs, mem_univ _⟩
  have h3 : HasDerivWithinAt (H ∘ fun t : ℝ => ((s, (t, z.2)) : ST))
      (fderivWithin ℝ H (spS T) (s, z) eQ) univ z.1 :=
    h2.comp_hasDerivWithinAt z.1 h1 hmap
  have h4 : HasDerivAt (H ∘ fun t : ℝ => ((s, (t, z.2)) : ST))
      (fderivWithin ℝ H (spS T) (s, z) eQ) z.1 :=
    hasDerivWithinAt_univ.mp h3
  exact h4.deriv

/-- The `η`-partial of a slice of `H` on `[0,T]` is the closed-set derivative `spD T eE H`. -/
theorem spD_slice_E {T : ℝ} {H : ST → ℝ} (h : ContDiffOn ℝ ∞ H (spS T)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) :
    Cyl.partialEta (fun w => H (s, w)) z = spD T eE H (s, z) := by
  have hd : DifferentiableWithinAt ℝ H (spS T) (s, z) :=
    h.differentiableOn (by simp) (s, z) (spS_mem hs z)
  have h2 : HasFDerivWithinAt H (fderivWithin ℝ H (spS T) (s, z)) (spS T) (s, z) :=
    hd.hasFDerivWithinAt
  have h1 : HasDerivWithinAt (fun t : ℝ => ((s, (z.1, t)) : ST)) eE univ z.2 :=
    ((hasDerivAt_const z.2 s).prodMk
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).hasDerivWithinAt
  have hmap : MapsTo (fun t : ℝ => ((s, (z.1, t)) : ST)) univ (spS T) :=
    fun t _ => ⟨hs, mem_univ _⟩
  have h3 : HasDerivWithinAt (H ∘ fun t : ℝ => ((s, (z.1, t)) : ST))
      (fderivWithin ℝ H (spS T) (s, z) eE) univ z.2 :=
    h2.comp_hasDerivWithinAt z.2 h1 hmap
  have h4 : HasDerivAt (H ∘ fun t : ℝ => ((s, (z.1, t)) : ST))
      (fderivWithin ℝ H (spS T) (s, z) eE) z.2 :=
    hasDerivWithinAt_univ.mp h3
  exact h4.deriv

/-- On the open region the closed-set derivative is the space-time directional derivative. -/
theorem spD_eq_dir (T : ℝ) (H : ST → ℝ) (w : ST) {x : ST} (hx : x ∈ spO T) :
    spD T w H x = dir w H x := by
  show fderivWithin ℝ H (spS T) x w = fderiv ℝ H x w
  rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset ((isOpen_spO T).mem_nhds hx)
    (spO_subset T))]

/-! ### Directional calculus on the open region `(0,T) × ℝ²` -/

theorem spO_diffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} {H : ST → E}
    (h : ContDiffOn ℝ ∞ H (spO T)) {x : ST} (hx : x ∈ spO T) : DifferentiableAt ℝ H x :=
  (h.contDiffAt ((isOpen_spO T).mem_nhds hx)).differentiableAt (by simp)

theorem spO_fderiv {T : ℝ} {H : ST → ℝ} (h : ContDiffOn ℝ ∞ H (spO T)) :
    ContDiffOn ℝ ∞ (fderiv ℝ H) (spO T) :=
  h.fderiv_of_isOpen (isOpen_spO T) (by simp)

theorem spO_dir_cdo {T : ℝ} {H : ST → ℝ} (h : ContDiffOn ℝ ∞ H (spO T)) (w : ST) :
    ContDiffOn ℝ ∞ (dir w H) (spO T) :=
  (spO_fderiv h).clm_apply contDiffOn_const

theorem spO_dir_dir {T : ℝ} {H : ST → ℝ} (h : ContDiffOn ℝ ∞ H (spO T)) {x : ST}
    (hx : x ∈ spO T) (a b : ST) :
    dir a (dir b H) x = fderiv ℝ (fderiv ℝ H) x a b := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ H) x :=
    ((spO_fderiv h).contDiffAt ((isOpen_spO T).mem_nhds hx)).differentiableAt (by simp)
  have h2 : HasFDerivAt (dir b H)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ H) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hdf.hasFDerivAt
  change fderiv ℝ (dir b H) x a = _
  rw [h2.fderiv]
  rfl

/-- Symmetry of second directional derivatives on `(0,T) × ℝ²`. -/
theorem spO_dir_symm {T : ℝ} {H : ST → ℝ} (h : ContDiffOn ℝ ∞ H (spO T)) {x : ST}
    (hx : x ∈ spO T) (a b : ST) :
    dir a (dir b H) x = dir b (dir a H) x := by
  rw [spO_dir_dir h hx, spO_dir_dir h hx]
  exact (h.contDiffAt ((isOpen_spO T).mem_nhds hx)).isSymmSndFDerivAt (by simp) a b

/-- Locality: functions agreeing on `(0,T) × ℝ²` have the same directional derivatives there. -/
theorem spO_dir_congr {T : ℝ} {H₁ H₂ : ST → ℝ} (h : ∀ y ∈ spO T, H₁ y = H₂ y) {x : ST}
    (hx : x ∈ spO T) (w : ST) : dir w H₁ x = dir w H₂ x := by
  simp only [dir]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem ((isOpen_spO T).mem_nhds hx) h)]

theorem spO_dir_zero {T : ℝ} {H : ST → ℝ} (h : ∀ y ∈ spO T, H y = 0) {x : ST}
    (hx : x ∈ spO T) (w : ST) : dir w H x = 0 := by
  rw [spO_dir_congr (H₂ := fun _ => 0) h hx]
  simp [dir]

theorem spO_dir_add {T : ℝ} {H₁ H₂ : ST → ℝ} (h₁ : ContDiffOn ℝ ∞ H₁ (spO T))
    (h₂ : ContDiffOn ℝ ∞ H₂ (spO T)) {x : ST} (hx : x ∈ spO T) (w : ST) :
    dir w (fun y => H₁ y + H₂ y) x = dir w H₁ x + dir w H₂ x := by
  have H : HasFDerivAt (fun y => H₁ y + H₂ y) (fderiv ℝ H₁ x + fderiv ℝ H₂ x) x :=
    (spO_diffAt h₁ hx).hasFDerivAt.add (spO_diffAt h₂ hx).hasFDerivAt
  simp only [dir]
  rw [H.fderiv]
  rfl

/-- If two smooth functions sum to zero on `(0,T) × ℝ²`, so do their directional derivatives. -/
theorem spO_sum_zero {T : ℝ} {H₁ H₂ : ST → ℝ} (h₁ : ContDiffOn ℝ ∞ H₁ (spO T))
    (h₂ : ContDiffOn ℝ ∞ H₂ (spO T)) (h : ∀ y ∈ spO T, H₁ y + H₂ y = 0) {x : ST}
    (hx : x ∈ spO T) (w : ST) : dir w H₁ x + dir w H₂ x = 0 :=
  (spO_dir_add h₁ h₂ hx w).symm.trans (spO_dir_zero h hx w)

/-- The product and sum rule in the shape of a momentum component. -/
theorem spO_dir_mom {T : ℝ} {a b c d e f g k : ST → ℝ}
    (ha : ContDiffOn ℝ ∞ a (spO T)) (hb : ContDiffOn ℝ ∞ b (spO T))
    (hc : ContDiffOn ℝ ∞ c (spO T)) (hd : ContDiffOn ℝ ∞ d (spO T))
    (he : ContDiffOn ℝ ∞ e (spO T)) (hf : ContDiffOn ℝ ∞ f (spO T))
    (hg : ContDiffOn ℝ ∞ g (spO T)) (hk : ContDiffOn ℝ ∞ k (spO T))
    (ν : ℝ) {x : ST} (hx : x ∈ spO T) (w : ST) :
    dir w (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y) x =
      dir w a x + (dir w b x * c x + b x * dir w c x + (dir w d x * e x + d x * dir w e x)) -
        ν * (dir w f x + dir w g x) + dir w k x := by
  have H : HasFDerivAt (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y)
      (fderiv ℝ a x + ((b x • fderiv ℝ c x + c x • fderiv ℝ b x) +
        (d x • fderiv ℝ e x + e x • fderiv ℝ d x)) - ν • (fderiv ℝ f x + fderiv ℝ g x) +
        fderiv ℝ k x) x :=
    (((spO_diffAt ha hx).hasFDerivAt.add
      (((spO_diffAt hb hx).hasFDerivAt.mul (spO_diffAt hc hx).hasFDerivAt).add
        ((spO_diffAt hd hx).hasFDerivAt.mul (spO_diffAt he hx).hasFDerivAt))).sub
      (((spO_diffAt hf hx).hasFDerivAt.add (spO_diffAt hg hx).hasFDerivAt).const_mul
        ν)).add (spO_diffAt hk hx).hasFDerivAt
  simp only [dir]
  rw [H.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-! ### Slices on the open region -/

theorem spO_pQ {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T)) (k : Fin 2) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Cyl.partialQ (fun w => v s w k) z = dir eQ (spC v k) (s, z) :=
  sliceQ (H := spC v k) (spO_diffAt (spC_cdo hv k) (spO_mem hs z))

theorem spO_pE {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T)) (k : Fin 2) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Cyl.partialEta (fun w => v s w k) z = dir eE (spC v k) (s, z) :=
  sliceE (H := spC v k) (spO_diffAt (spC_cdo hv k) (spO_mem hs z))

theorem spO_pQQ {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T)) (k : Fin 2) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Cyl.partialQ (Cyl.partialQ (fun w => v s w k)) z = dir eQ (dir eQ (spC v k)) (s, z) := by
  have h : Cyl.partialQ (fun w => v s w k) = fun w => dir eQ (spC v k) (s, w) :=
    funext fun w => spO_pQ hv k hs w
  rw [h]
  exact sliceQ (H := dir eQ (spC v k))
    (spO_diffAt (spO_dir_cdo (spC_cdo hv k) eQ) (spO_mem hs z))

theorem spO_pEE {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T)) (k : Fin 2) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Cyl.partialEta (Cyl.partialEta (fun w => v s w k)) z = dir eE (dir eE (spC v k)) (s, z) := by
  have h : Cyl.partialEta (fun w => v s w k) = fun w => dir eE (spC v k) (s, w) :=
    funext fun w => spO_pE hv k hs w
  rw [h]
  exact sliceE (H := dir eE (spC v k))
    (spO_diffAt (spO_dir_cdo (spC_cdo hv k) eE) (spO_mem hs z))

/-- The time derivative of the component `k` of the velocity on `(0,T) × ℝ²`. -/
theorem spO_pT {v : ℝ → Plane → Vec} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T)) (k : Fin 2) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    (deriv (fun t => v t z) s) k = dir eT (spC v k) (s, z) := by
  have hU : DifferentiableAt ℝ (fun x : ST => v x.1 x.2) (s, z) :=
    spO_diffAt hv (spO_mem hs z)
  have h1 : HasDerivAt (fun t => v t z) (fderiv ℝ (fun x : ST => v x.1 x.2) (s, z) eT) s := by
    have h0 : HasDerivAt (fun t : ℝ => ((t, z) : ST)) eT s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s z)
    exact hU.hasFDerivAt.comp_hasDerivAt s h0
  rw [h1.deriv]
  have h2 : HasFDerivAt (spC v k)
      ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ (fun x : ST => v x.1 x.2) (s, z)))
      (s, z) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp (s, z) hU.hasFDerivAt
  simp only [dir]
  rw [h2.fderiv]
  rfl

theorem spO_pQP {p : ℝ → Plane → ℝ} {T : ℝ} (hp : ContDiffOn ℝ ∞ (spP p) (spO T)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Cyl.partialQ (p s) z = dir eQ (spP p) (s, z) :=
  sliceQ (H := spP p) (spO_diffAt hp (spO_mem hs z))

theorem spO_pEP {p : ℝ → Plane → ℝ} {T : ℝ} (hp : ContDiffOn ℝ ∞ (spP p) (spO T)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) T) (z : Plane) :
    Cyl.partialEta (p s) z = dir eE (spP p) (s, z) :=
  sliceE (H := spP p) (spO_diffAt hp (spO_mem hs z))

/-! ### The momentum equation in directional form on `(0,T) × ℝ²` -/

theorem spO_M0 {ν : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T))
    (hp : ContDiffOn ℝ ∞ (spP p) (spO T))
    (hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Train.momentumResidual ν v p t w = 0) :
    ∀ y ∈ spO T, dir eT (spC v 0) y + (spC v 0 y * dir eQ (spC v 0) y +
      spC v 1 y * dir eE (spC v 0) y) - ν * (dir eQ (dir eQ (spC v 0)) y +
      dir eE (dir eE (spC v 0)) y) + dir eQ (spP p) y = 0 := by
  rintro ⟨t, w⟩ hy
  have ht : t ∈ Ioo (0 : ℝ) T := (Set.mem_prod.mp hy).1
  have m := congrArg (fun X : Vec => X 0) (hmom t ht w)
  simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
    Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    Train.toVec_zero, PiLp.zero_apply] at m
  rw [spO_pQQ hv 0 ht w, spO_pEE hv 0 ht w, spO_pT hv 0 ht w, spO_pQ hv 0 ht w,
    spO_pE hv 0 ht w, spO_pQP hp ht w] at m
  exact m

theorem spO_M1 {ν : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T))
    (hp : ContDiffOn ℝ ∞ (spP p) (spO T))
    (hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Train.momentumResidual ν v p t w = 0) :
    ∀ y ∈ spO T, dir eT (spC v 1) y + (spC v 0 y * dir eQ (spC v 1) y +
      spC v 1 y * dir eE (spC v 1) y) - ν * (dir eQ (dir eQ (spC v 1)) y +
      dir eE (dir eE (spC v 1)) y) + dir eE (spP p) y = 0 := by
  rintro ⟨t, w⟩ hy
  have ht : t ∈ Ioo (0 : ℝ) T := (Set.mem_prod.mp hy).1
  have m := congrArg (fun X : Vec => X 1) (hmom t ht w)
  simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
    Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    Train.toVec_one, PiLp.zero_apply] at m
  rw [spO_pQQ hv 1 ht w, spO_pEE hv 1 ht w, spO_pT hv 1 ht w, spO_pQ hv 1 ht w,
    spO_pE hv 1 ht w, spO_pEP hp ht w] at m
  exact m

/-- **The divergence identity on `(0,T) × ℝ²`**: `Δp = -(∂_i v_j ∂_j v_i)` pointwise. -/
theorem spO_identity {ν : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T))
    (hp : ContDiffOn ℝ ∞ (spP p) (spO T))
    (hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Train.momentumResidual ν v p t w = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Cyl.divergence (v t) w = 0)
    {s : ℝ} {z : Plane} (hx : ((s, z) : ST) ∈ spO T) :
    dir eQ (dir eQ (spP p)) (s, z) + dir eE (dir eE (spP p)) (s, z) +
      (dir eQ (spC v 0) (s, z) ^ 2 + 2 * (dir eQ (spC v 1) (s, z) * dir eE (spC v 0) (s, z)) +
        dir eE (spC v 1) (s, z) ^ 2) = 0 := by
  have hv0 := spC_cdo hv 0
  have hv1 := spC_cdo hv 1
  -- divergence free on `(0,T) × ℝ²`
  have hDv : ∀ y ∈ spO T, dir eQ (spC v 0) y + dir eE (spC v 1) y = 0 := by
    rintro ⟨t, w⟩ hy
    have ht : t ∈ Ioo (0 : ℝ) T := (Set.mem_prod.mp hy).1
    have h := hdiv t ht w
    unfold Cyl.divergence at h
    rw [spO_pQ hv 0 ht w, spO_pE hv 1 ht w] at h
    exact h
  -- first and second `q`, `η` derivatives of the divergence vanish
  have hDQ : ∀ y ∈ spO T, dir eQ (dir eQ (spC v 0)) y + dir eQ (dir eE (spC v 1)) y = 0 :=
    fun y hy => spO_sum_zero (spO_dir_cdo hv0 eQ) (spO_dir_cdo hv1 eE) hDv hy eQ
  have hDE : ∀ y ∈ spO T, dir eE (dir eQ (spC v 0)) y + dir eE (dir eE (spC v 1)) y = 0 :=
    fun y hy => spO_sum_zero (spO_dir_cdo hv0 eQ) (spO_dir_cdo hv1 eE) hDv hy eE
  have DQ1 : dir eQ (dir eQ (spC v 0)) (s, z) + dir eQ (dir eE (spC v 1)) (s, z) = 0 :=
    spO_sum_zero (spO_dir_cdo hv0 eQ) (spO_dir_cdo hv1 eE) hDv hx eQ
  have DE1 : dir eE (dir eQ (spC v 0)) (s, z) + dir eE (dir eE (spC v 1)) (s, z) = 0 :=
    spO_sum_zero (spO_dir_cdo hv0 eQ) (spO_dir_cdo hv1 eE) hDv hx eE
  have DT1 : dir eT (dir eQ (spC v 0)) (s, z) + dir eT (dir eE (spC v 1)) (s, z) = 0 :=
    spO_sum_zero (spO_dir_cdo hv0 eQ) (spO_dir_cdo hv1 eE) hDv hx eT
  have DQQ : dir eQ (dir eQ (dir eQ (spC v 0))) (s, z) +
      dir eQ (dir eQ (dir eE (spC v 1))) (s, z) = 0 :=
    spO_sum_zero (spO_dir_cdo (spO_dir_cdo hv0 eQ) eQ) (spO_dir_cdo (spO_dir_cdo hv1 eE) eQ)
      hDQ hx eQ
  have DEE : dir eE (dir eE (dir eQ (spC v 0))) (s, z) +
      dir eE (dir eE (dir eE (spC v 1))) (s, z) = 0 :=
    spO_sum_zero (spO_dir_cdo (spO_dir_cdo hv0 eQ) eE) (spO_dir_cdo (spO_dir_cdo hv1 eE) eE)
      hDE hx eE
  -- symmetry of mixed derivatives
  have Sa : dir eQ (dir eT (spC v 0)) (s, z) = dir eT (dir eQ (spC v 0)) (s, z) :=
    spO_dir_symm hv0 hx eQ eT
  have Sb : dir eE (dir eT (spC v 1)) (s, z) = dir eT (dir eE (spC v 1)) (s, z) :=
    spO_dir_symm hv1 hx eE eT
  have Sc : dir eQ (dir eE (spC v 0)) (s, z) = dir eE (dir eQ (spC v 0)) (s, z) :=
    spO_dir_symm hv0 hx eQ eE
  have Sd : dir eE (dir eQ (spC v 1)) (s, z) = dir eQ (dir eE (spC v 1)) (s, z) :=
    spO_dir_symm hv1 hx eE eQ
  have Se : dir eQ (dir eE (dir eE (spC v 0))) (s, z) =
      dir eE (dir eE (dir eQ (spC v 0))) (s, z) :=
    (spO_dir_symm (spO_dir_cdo hv0 eE) hx eQ eE).trans
      (spO_dir_congr (H₁ := dir eQ (dir eE (spC v 0))) (H₂ := dir eE (dir eQ (spC v 0)))
        (fun y hy => spO_dir_symm hv0 hy eQ eE) hx eE)
  have Sf : dir eE (dir eQ (dir eQ (spC v 1))) (s, z) =
      dir eQ (dir eQ (dir eE (spC v 1))) (s, z) :=
    (spO_dir_symm (spO_dir_cdo hv1 eQ) hx eE eQ).trans
      (spO_dir_congr (H₁ := dir eE (dir eQ (spC v 1))) (H₂ := dir eQ (dir eE (spC v 1)))
        (fun y hy => spO_dir_symm hv1 hy eE eQ) hx eQ)
  -- the momentum equation, differentiated in `q` (component 0) and in `η` (component 1)
  have hM0 := spO_M0 hv hp hmom
  have hM1 := spO_M1 hv hp hmom
  have E0 := (spO_dir_mom (spO_dir_cdo hv0 eT) hv0 (spO_dir_cdo hv0 eQ) hv1
    (spO_dir_cdo hv0 eE) (spO_dir_cdo (spO_dir_cdo hv0 eQ) eQ)
    (spO_dir_cdo (spO_dir_cdo hv0 eE) eE) (spO_dir_cdo hp eQ) ν hx eQ).symm.trans
    (spO_dir_zero hM0 hx eQ)
  have E1 := (spO_dir_mom (spO_dir_cdo hv1 eT) hv0 (spO_dir_cdo hv1 eQ) hv1
    (spO_dir_cdo hv1 eE) (spO_dir_cdo (spO_dir_cdo hv1 eQ) eQ)
    (spO_dir_cdo (spO_dir_cdo hv1 eE) eE) (spO_dir_cdo hp eE) ν hx eE).symm.trans
    (spO_dir_zero hM1 hx eE)
  linear_combination E0 + E1 - Sa - Sb - DT1 - spC v 0 (s, z) * DQ1 - spC v 0 (s, z) * Sd
    - spC v 1 (s, z) * Sc - spC v 1 (s, z) * DE1 + ν * (DQQ + Se + DEE + Sf)

/-- The identity `L = 0` on the open region, with the closed-set derivatives converted. -/
theorem spL_zero_on_O {ν : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spO T))
    (hp : ContDiffOn ℝ ∞ (spP p) (spO T))
    (hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Train.momentumResidual ν v p t w = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Cyl.divergence (v t) w = 0) :
    ∀ x ∈ spO T, spL T v p x = 0 := by
  rintro ⟨s, z⟩ hx
  have c1 : spD T eQ (spD T eQ (spP p)) (s, z) = dir eQ (dir eQ (spP p)) (s, z) := by
    rw [spD_eq_dir T _ _ hx]
    exact spO_dir_congr (fun y hy => spD_eq_dir T _ _ hy) hx eQ
  have c2 : spD T eE (spD T eE (spP p)) (s, z) = dir eE (dir eE (spP p)) (s, z) := by
    rw [spD_eq_dir T _ _ hx]
    exact spO_dir_congr (fun y hy => spD_eq_dir T _ _ hy) hx eE
  have c3 : spD T eQ (spC v 0) (s, z) = dir eQ (spC v 0) (s, z) := spD_eq_dir T _ _ hx
  have c4 : spD T eQ (spC v 1) (s, z) = dir eQ (spC v 1) (s, z) := spD_eq_dir T _ _ hx
  have c5 : spD T eE (spC v 0) (s, z) = dir eE (spC v 0) (s, z) := spD_eq_dir T _ _ hx
  have c6 : spD T eE (spC v 1) (s, z) = dir eE (spC v 1) (s, z) := spD_eq_dir T _ _ hx
  simp only [spL]
  rw [c1, c2, c3, c4, c5, c6]
  exact spO_identity hv hp hmom hdiv hx

theorem spL_continuousOn {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} {T : ℝ} (hT : 0 < T)
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spS T))
    (hp : ContDiffOn ℝ ∞ (spP p) (spS T)) : ContinuousOn (spL T v p) (spS T) := by
  have hPQ := spD_contDiffOn hT eQ hp
  have hPE := spD_contDiffOn hT eE hp
  have hPQQ := spD_contDiffOn hT eQ hPQ
  have hPEE := spD_contDiffOn hT eE hPE
  have ha0 := spC_cdo hv 0
  have ha1 := spC_cdo hv 1
  have hQ0 := spD_contDiffOn hT eQ ha0
  have hE0 := spD_contDiffOn hT eE ha0
  have hQ1 := spD_contDiffOn hT eQ ha1
  have hE1 := spD_contDiffOn hT eE ha1
  unfold spL
  exact (hPQQ.continuousOn.add hPEE.continuousOn).add
    (((hQ0.continuousOn.pow 2).add
      (continuousOn_const.mul (hQ1.continuousOn.mul hE0.continuousOn))).add
      (hE1.continuousOn.pow 2))

/-- The Poisson identity `L = 0` on the closed region `[0,T] × ℝ²`, by continuity from `(0,T)`. -/
theorem spL_eq_zero {ν : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} {T : ℝ} (hT : 0 < T)
    (hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spS T))
    (hp : ContDiffOn ℝ ∞ (spP p) (spS T))
    (hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Train.momentumResidual ν v p t w = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Cyl.divergence (v t) w = 0) :
    EqOn (spL T v p) 0 (spS T) := by
  have hOS : spO T ⊆ spS T := spO_subset T
  have hcl : spS T ⊆ closure (spO T) := by
    have h : closure (spO T) = spS T := by
      unfold spO spS
      rw [closure_prod_eq, closure_Ioo hT.ne, closure_univ]
    exact h.symm.subset
  have hO : EqOn (spL T v p) 0 (spO T) := fun x hx =>
    spL_zero_on_O (hv.mono hOS) (hp.mono hOS) hmom hdiv x hx
  exact Set.EqOn.of_subset_closure hO (spL_continuousOn hT hv hp) continuous_zero.continuousOn
    hOS hcl

/-! ### The target -/

theorem slicePoisson : SlicePoisson := by
  unfold SlicePoisson
  intro ν c T v p _hν _hc hT hcl s hs z
  have hv : ContDiffOn ℝ ∞ (fun x : ST => v x.1 x.2) (spS T) := hcl.smooth_v
  have hp : ContDiffOn ℝ ∞ (spP p) (spS T) := hcl.smooth_p
  have hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Train.momentumResidual ν v p t w = 0 :=
    fun t ht w => hcl.momentum t ht w
  have hdiv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ w, Cyl.divergence (v t) w = 0 :=
    fun t ht w => hcl.solenoidal t (Ioo_subset_Icc_self ht) w
  have hL : spL T v p (s, z) = 0 :=
    spL_eq_zero hT hv hp hmom hdiv (spS_mem hs z)
  have hG := spD_contDiffOn hT eQ hp
  have hH := spD_contDiffOn hT eE hp
  have ha0 := spC_cdo hv 0
  have ha1 := spC_cdo hv 1
  have eP1 : Cyl.partialQ (p s) = fun w => spD T eQ (spP p) (s, w) :=
    funext fun w => spD_slice_Q hp hs w
  have eP2 : Cyl.partialEta (p s) = fun w => spD T eE (spP p) (s, w) :=
    funext fun w => spD_slice_E hp hs w
  have hlap : Train.lapS (p s) z =
      spD T eQ (spD T eQ (spP p)) (s, z) + spD T eE (spD T eE (spP p)) (s, z) := by
    rw [Train.lapS, eP1, eP2, spD_slice_Q hG hs z, spD_slice_E hH hs z]
  have q0 : Cyl.partialQ (fun w => v s w 0) z = spD T eQ (spC v 0) (s, z) :=
    spD_slice_Q ha0 hs z
  have q1 : Cyl.partialQ (fun w => v s w 1) z = spD T eQ (spC v 1) (s, z) :=
    spD_slice_Q ha1 hs z
  have e0 : Cyl.partialEta (fun w => v s w 0) z = spD T eE (spC v 0) (s, z) :=
    spD_slice_E ha0 hs z
  have e1 : Cyl.partialEta (fun w => v s w 1) z = spD T eE (spC v 1) (s, z) :=
    spD_slice_E ha1 hs z
  have hpois : poissonSource (v s) z = spD T eQ (spC v 0) (s, z) ^ 2 +
      2 * (spD T eQ (spC v 1) (s, z) * spD T eE (spC v 0) (s, z)) +
      spD T eE (spC v 1) (s, z) ^ 2 := by
    unfold poissonSource
    rw [q0, q1, e0, e1]
  rw [hlap, hpois]
  simp only [spL] at hL
  linear_combination hL

end UnforcedLeray.Short.PartI
