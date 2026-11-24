import UnforcedLeray.Units.B0238.Partials
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# `LocalVorticityEquation` helper: space-time layer on an open set

Copy of `Units/B0238/SpaceTime.lean` with the open region `Opos = {s > 0}` replaced by an arbitrary
open set `O ⊆ ℝ × Plane` (used with `O = Ioo 0 T ×ˢ univ`, source lines 276-288 of
`the November 2 reference manuscript`). `lvSm O H` means that `H` is `C^∞` on `O`;
every lemma that differentiates takes the openness hypothesis `hO : IsOpen O` explicitly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI.LV

open UnforcedLeray.Cyl (Plane)

/-- The directional derivative `∂_w H(x) = DH(x) w` on `ℝ × Plane`. -/
def lvDir (w : ℝ × Plane) (H : ℝ × Plane → ℝ) (x : ℝ × Plane) : ℝ := fderiv ℝ H x w

/-- The age direction. -/
def lvEt : ℝ × Plane := (1, 0)

/-- The `q` direction. -/
def lvEQ : ℝ × Plane := (0, (1, 0))

/-- The `η` direction. -/
def lvEE : ℝ × Plane := (0, (0, 1))

/-- `H` is `C^∞` on the set `O`. -/
def lvSm (O : Set (ℝ × Plane)) (H : ℝ × Plane → ℝ) : Prop := ContDiffOn ℝ ∞ H O

theorem lvSm.contDiffAt {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O)
    (h : lvSm O H) {x : ℝ × Plane} (hx : x ∈ O) : ContDiffAt ℝ ∞ H x :=
  ContDiffOn.contDiffAt h (hO.mem_nhds hx)

theorem lvSm.differentiableAt {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O)
    (h : lvSm O H) {x : ℝ × Plane} (hx : x ∈ O) : DifferentiableAt ℝ H x :=
  (lvSm.contDiffAt hO h hx).differentiableAt (by simp)

theorem lvSm.fderiv {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O) (h : lvSm O H) :
    ContDiffOn ℝ ∞ (fderiv ℝ H) O :=
  ContDiffOn.fderiv_of_isOpen h hO (by simp)

theorem lvSm.dir {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O) (h : lvSm O H)
    (w : ℝ × Plane) : lvSm O (lvDir w H) :=
  (lvSm.fderiv hO h).clm_apply contDiffOn_const

theorem lvSm.sub {O : Set (ℝ × Plane)} {H₁ H₂ : ℝ × Plane → ℝ} (h₁ : lvSm O H₁)
    (h₂ : lvSm O H₂) : lvSm O (fun x => H₁ x - H₂ x) :=
  ContDiffOn.sub h₁ h₂

/-- `∂_a ∂_b H = D²H(a, b)` on `O`. -/
theorem lvDir_dir_eq {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O) (h : lvSm O H)
    {x : ℝ × Plane} (hx : x ∈ O) (a b : ℝ × Plane) :
    lvDir a (lvDir b H) x = fderiv ℝ (fderiv ℝ H) x a b := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ H) x :=
    (ContDiffOn.contDiffAt (lvSm.fderiv hO h) (hO.mem_nhds hx)).differentiableAt (by simp)
  have h2 : HasFDerivAt (lvDir b H)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ H) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hdf.hasFDerivAt
  change fderiv ℝ (lvDir b H) x a = _
  rw [h2.fderiv]
  rfl

/-- **Symmetry of second derivatives** on `O`: `∂_a ∂_b H = ∂_b ∂_a H`. -/
theorem lvDir_symm {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O) (h : lvSm O H)
    {x : ℝ × Plane} (hx : x ∈ O) (a b : ℝ × Plane) :
    lvDir a (lvDir b H) x = lvDir b (lvDir a H) x := by
  rw [lvDir_dir_eq hO h hx, lvDir_dir_eq hO h hx]
  exact (lvSm.contDiffAt hO h hx).isSymmSndFDerivAt (by simp) a b

/-- Locality: functions agreeing on `O` have the same directional derivatives at points of `O`. -/
theorem lvDir_congr {O : Set (ℝ × Plane)} {H₁ H₂ : ℝ × Plane → ℝ} (hO : IsOpen O)
    (h : ∀ y ∈ O, H₁ y = H₂ y) {x : ℝ × Plane} (hx : x ∈ O) (w : ℝ × Plane) :
    lvDir w H₁ x = lvDir w H₂ x := by
  simp only [lvDir]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hO.mem_nhds hx) h)]

theorem lvDir_eq_zero {O : Set (ℝ × Plane)} {H : ℝ × Plane → ℝ} (hO : IsOpen O)
    (h : ∀ y ∈ O, H y = 0) {x : ℝ × Plane} (hx : x ∈ O) (w : ℝ × Plane) :
    lvDir w H x = 0 := by
  rw [lvDir_congr (H₂ := fun _ => 0) hO h hx]
  simp [lvDir]

theorem lvDir_sub {O : Set (ℝ × Plane)} {H₁ H₂ : ℝ × Plane → ℝ} (hO : IsOpen O)
    (h₁ : lvSm O H₁) (h₂ : lvSm O H₂) {x : ℝ × Plane} (hx : x ∈ O) (w : ℝ × Plane) :
    lvDir w (fun y => H₁ y - H₂ y) x = lvDir w H₁ x - lvDir w H₂ x := by
  have H : HasFDerivAt (fun y => H₁ y - H₂ y) (fderiv ℝ H₁ x - fderiv ℝ H₂ x) x :=
    (lvSm.differentiableAt hO h₁ hx).hasFDerivAt.sub (lvSm.differentiableAt hO h₂ hx).hasFDerivAt
  simp only [lvDir]
  rw [H.fderiv]
  rfl

/-- The product and sum rule in the shape `a + (b c + d e) - ν (f + g) + k` on `O`. -/
theorem lvDir_mom {O : Set (ℝ × Plane)} (hO : IsOpen O)
    {a b c d e f g k : ℝ × Plane → ℝ} (ha : lvSm O a) (hb : lvSm O b) (hc : lvSm O c)
    (hd : lvSm O d) (he : lvSm O e) (hf : lvSm O f) (hg : lvSm O g) (hk : lvSm O k) (ν : ℝ)
    {x : ℝ × Plane} (hx : x ∈ O) (w : ℝ × Plane) :
    lvDir w (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y) x =
      lvDir w a x + (lvDir w b x * c x + b x * lvDir w c x + (lvDir w d x * e x + d x * lvDir w e x)) -
        ν * (lvDir w f x + lvDir w g x) + lvDir w k x := by
  have H : HasFDerivAt (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y)
      (fderiv ℝ a x + ((b x • fderiv ℝ c x + c x • fderiv ℝ b x) +
        (d x • fderiv ℝ e x + e x • fderiv ℝ d x)) - ν • (fderiv ℝ f x + fderiv ℝ g x) +
        fderiv ℝ k x) x :=
    (((lvSm.differentiableAt hO ha hx).hasFDerivAt.add
      (((lvSm.differentiableAt hO hb hx).hasFDerivAt.mul
        (lvSm.differentiableAt hO hc hx).hasFDerivAt).add
        ((lvSm.differentiableAt hO hd hx).hasFDerivAt.mul
          (lvSm.differentiableAt hO he hx).hasFDerivAt))).sub
      (((lvSm.differentiableAt hO hf hx).hasFDerivAt.add
        (lvSm.differentiableAt hO hg hx).hasFDerivAt).const_mul ν)).add
      (lvSm.differentiableAt hO hk hx).hasFDerivAt
  simp only [lvDir]
  rw [H.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-! ### Slices -/

/-- The `q`-partial of the slice `z ↦ H(s, z)` is `∂_{eQ} H`. -/
theorem lvSliceQ {H : ℝ × Plane → ℝ} {s : ℝ} {z : Plane} (hd : DifferentiableAt ℝ H (s, z)) :
    Cyl.partialQ (fun z' => H (s, z')) z = lvDir lvEQ H (s, z) := by
  have h1 : HasDerivAt (fun t : ℝ => ((s, (t, z.2)) : ℝ × Plane)) lvEQ z.1 :=
    (hasDerivAt_const z.1 s).prodMk ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have h2 : HasFDerivAt H (fderiv ℝ H (s, z)) (s, (z.1, z.2)) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt z.1 h1).deriv

/-- The `η`-partial of the slice `z ↦ H(s, z)` is `∂_{eE} H`. -/
theorem lvSliceE {H : ℝ × Plane → ℝ} {s : ℝ} {z : Plane} (hd : DifferentiableAt ℝ H (s, z)) :
    Cyl.partialEta (fun z' => H (s, z')) z = lvDir lvEE H (s, z) := by
  have h1 : HasDerivAt (fun t : ℝ => ((s, (z.1, t)) : ℝ × Plane)) lvEE z.2 :=
    (hasDerivAt_const z.2 s).prodMk ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have h2 : HasFDerivAt H (fderiv ℝ H (s, z)) (s, (z.1, z.2)) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt z.2 h1).deriv

/-- The age derivative of the slice `t ↦ H(t, z)` is `∂_{eT} H`. -/
theorem lvSliceT {H : ℝ × Plane → ℝ} {s : ℝ} {z : Plane} (hd : DifferentiableAt ℝ H (s, z)) :
    deriv (fun t => H (t, z)) s = lvDir lvEt H (s, z) := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × Plane)) lvEt s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  exact (hd.hasFDerivAt.comp_hasDerivAt s h1).deriv

end UnforcedLeray.Short.PartI.LV
