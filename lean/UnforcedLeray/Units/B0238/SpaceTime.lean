import UnforcedLeray.Units.B0238.Partials
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# B0238 helpers: space–time directional derivatives on the region `s > 0`

Helper module of blueprint unit **B0238** (`unlabeled:4127`, `paper/main.tex` lines 4125–4134),
used to derive the vorticity form of the exact evolution `(V_c, E_c)` (`B0238/VorticityEq.lean`).
On `ST = ℝ × Plane` (points `(s, z)`), `dir w H x = DH(x) w` is the directional derivative and
`Sm H` means `H` is `C^∞` on the open region `Opos = {s > 0}`. Proved: closure of `Sm` under
`dir`, subtraction; symmetry of second derivatives (`dir_symm`, from Mathlib's
`ContDiffAt.isSymmSndFDerivAt`); locality (`dir_congr`, `dir_eq_zero`); the product/sum rule in
the shape of the momentum equation (`dir_mom`); and that the classical partials of the slices
`z ↦ H(s,z)`, `t ↦ H(t,z)` are `dir eQ H`, `dir eE H`, `dir eT H` (`sliceQ`, `sliceE`, `sliceT`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0238

open UnforcedLeray.Cyl (Plane)

/-- Space–time points `(s, z)`. -/
abbrev ST := ℝ × Plane

/-- The open region of positive ages. -/
def Opos : Set ST := {x | 0 < x.1}

theorem isOpen_Opos : IsOpen Opos := isOpen_lt continuous_const continuous_fst

/-- The directional derivative `∂_w H(x) = DH(x) w`. -/
def dir (w : ST) (H : ST → ℝ) (x : ST) : ℝ := fderiv ℝ H x w

/-- The age direction. -/
def eT : ST := (1, 0)

/-- The `q` direction. -/
def eQ : ST := (0, (1, 0))

/-- The `η` direction. -/
def eE : ST := (0, (0, 1))

/-- `H` is `C^∞` on the region of positive ages. -/
def Sm (H : ST → ℝ) : Prop := ContDiffOn ℝ ∞ H Opos

theorem Sm.contDiffAt {H : ST → ℝ} (h : Sm H) {x : ST} (hx : x ∈ Opos) : ContDiffAt ℝ ∞ H x :=
  ContDiffOn.contDiffAt h (isOpen_Opos.mem_nhds hx)

theorem Sm.differentiableAt {H : ST → ℝ} (h : Sm H) {x : ST} (hx : x ∈ Opos) :
    DifferentiableAt ℝ H x :=
  (h.contDiffAt hx).differentiableAt (by simp)

theorem Sm.fderiv {H : ST → ℝ} (h : Sm H) : ContDiffOn ℝ ∞ (fderiv ℝ H) Opos :=
  ContDiffOn.fderiv_of_isOpen h isOpen_Opos (by simp)

theorem Sm.dir {H : ST → ℝ} (h : Sm H) (w : ST) : Sm (dir w H) :=
  h.fderiv.clm_apply contDiffOn_const

theorem Sm.sub {H₁ H₂ : ST → ℝ} (h₁ : Sm H₁) (h₂ : Sm H₂) : Sm (fun x => H₁ x - H₂ x) :=
  ContDiffOn.sub h₁ h₂

/-- `∂_a ∂_b H = D²H(a, b)`. -/
theorem dir_dir_eq {H : ST → ℝ} (h : Sm H) {x : ST} (hx : x ∈ Opos) (a b : ST) :
    dir a (dir b H) x = fderiv ℝ (fderiv ℝ H) x a b := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ H) x :=
    (h.fderiv.contDiffAt (isOpen_Opos.mem_nhds hx)).differentiableAt (by simp)
  have h2 : HasFDerivAt (dir b H)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ H) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hdf.hasFDerivAt
  change fderiv ℝ (dir b H) x a = _
  rw [h2.fderiv]
  rfl

/-- **Symmetry of second derivatives**: `∂_a ∂_b H = ∂_b ∂_a H` on `s > 0`. -/
theorem dir_symm {H : ST → ℝ} (h : Sm H) {x : ST} (hx : x ∈ Opos) (a b : ST) :
    dir a (dir b H) x = dir b (dir a H) x := by
  rw [dir_dir_eq h hx, dir_dir_eq h hx]
  exact (h.contDiffAt hx).isSymmSndFDerivAt (by simp) a b

/-- Locality: functions agreeing on `s > 0` have the same directional derivatives there. -/
theorem dir_congr {H₁ H₂ : ST → ℝ} (h : ∀ y ∈ Opos, H₁ y = H₂ y) {x : ST} (hx : x ∈ Opos)
    (w : ST) : dir w H₁ x = dir w H₂ x := by
  simp only [dir]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_Opos.mem_nhds hx) h)]

theorem dir_eq_zero {H : ST → ℝ} (h : ∀ y ∈ Opos, H y = 0) {x : ST} (hx : x ∈ Opos) (w : ST) :
    dir w H x = 0 := by
  rw [dir_congr (H₂ := fun _ => 0) h hx]
  simp [dir]

theorem dir_sub {H₁ H₂ : ST → ℝ} (h₁ : Sm H₁) (h₂ : Sm H₂) {x : ST} (hx : x ∈ Opos) (w : ST) :
    dir w (fun y => H₁ y - H₂ y) x = dir w H₁ x - dir w H₂ x := by
  have H : HasFDerivAt (fun y => H₁ y - H₂ y) (fderiv ℝ H₁ x - fderiv ℝ H₂ x) x :=
    (h₁.differentiableAt hx).hasFDerivAt.sub (h₂.differentiableAt hx).hasFDerivAt
  simp only [dir]
  rw [H.fderiv]
  rfl

/-- The product and sum rule in the shape of a momentum component
`a + (b c + d e) - ν (f + g) + k`. -/
theorem dir_mom {a b c d e f g k : ST → ℝ} (ha : Sm a) (hb : Sm b) (hc : Sm c) (hd : Sm d)
    (he : Sm e) (hf : Sm f) (hg : Sm g) (hk : Sm k) (ν : ℝ) {x : ST} (hx : x ∈ Opos) (w : ST) :
    dir w (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y) x =
      dir w a x + (dir w b x * c x + b x * dir w c x + (dir w d x * e x + d x * dir w e x)) -
        ν * (dir w f x + dir w g x) + dir w k x := by
  have H : HasFDerivAt (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y)
      (fderiv ℝ a x + ((b x • fderiv ℝ c x + c x • fderiv ℝ b x) +
        (d x • fderiv ℝ e x + e x • fderiv ℝ d x)) - ν • (fderiv ℝ f x + fderiv ℝ g x) +
        fderiv ℝ k x) x :=
    (((ha.differentiableAt hx).hasFDerivAt.add
      (((hb.differentiableAt hx).hasFDerivAt.mul (hc.differentiableAt hx).hasFDerivAt).add
        ((hd.differentiableAt hx).hasFDerivAt.mul (he.differentiableAt hx).hasFDerivAt))).sub
      (((hf.differentiableAt hx).hasFDerivAt.add (hg.differentiableAt hx).hasFDerivAt).const_mul
        ν)).add (hk.differentiableAt hx).hasFDerivAt
  simp only [dir]
  rw [H.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-! ### Slices -/

/-- The `q`-partial of the slice `z ↦ H(s, z)` is `∂_{eQ} H`. -/
theorem sliceQ {H : ST → ℝ} {s : ℝ} {z : Plane} (hd : DifferentiableAt ℝ H (s, z)) :
    Cyl.partialQ (fun z' => H (s, z')) z = dir eQ H (s, z) := by
  have h1 : HasDerivAt (fun t : ℝ => ((s, (t, z.2)) : ST)) eQ z.1 :=
    (hasDerivAt_const z.1 s).prodMk ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have h2 : HasFDerivAt H (fderiv ℝ H (s, z)) (s, (z.1, z.2)) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt z.1 h1).deriv

/-- The `η`-partial of the slice `z ↦ H(s, z)` is `∂_{eE} H`. -/
theorem sliceE {H : ST → ℝ} {s : ℝ} {z : Plane} (hd : DifferentiableAt ℝ H (s, z)) :
    Cyl.partialEta (fun z' => H (s, z')) z = dir eE H (s, z) := by
  have h1 : HasDerivAt (fun t : ℝ => ((s, (z.1, t)) : ST)) eE z.2 :=
    (hasDerivAt_const z.2 s).prodMk ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have h2 : HasFDerivAt H (fderiv ℝ H (s, z)) (s, (z.1, z.2)) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt z.2 h1).deriv

/-- The age derivative of the slice `t ↦ H(t, z)` is `∂_{eT} H`. -/
theorem sliceT {H : ST → ℝ} {s : ℝ} {z : Plane} (hd : DifferentiableAt ℝ H (s, z)) :
    deriv (fun t => H (t, z)) s = dir eT H (s, z) := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, z) : ST)) eT s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  exact (hd.hasFDerivAt.comp_hasDerivAt s h1).deriv

end UnforcedLeray.B0238
