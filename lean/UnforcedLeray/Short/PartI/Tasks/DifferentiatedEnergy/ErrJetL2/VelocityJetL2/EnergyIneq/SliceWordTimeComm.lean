import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation.Layer

/-!
# Part I, task `PartI:T08/2/2/2/4/1` (`SliceWordTimeComm`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (smooth for
positive time).

Route, with `O = Ioi 0 ×ˢ univ` (open):
* `swtcWord u H` is the space-time word: iterated `lvDir lvEQ` (letter `true`) and `lvDir lvEE`
  (letter `false`) applied to `H`, in the same order as `B0151.derivWord`.
* `swtc_sm`: the space-time words of a `C^∞` function on `O` are `C^∞` on `O`.
* `swtc_slice`: for `t > 0`, the spatial word of the slice `z ↦ H(t, z)` is the slice of the
  space-time word.
* `swtc_comm`: `∂_t` commutes with the space-time words on `O` (`lvDir_symm`).
* `swtc_main`: differentiate in `s` using the eventual equality of slices near `s`, then apply
  `swtc_comm`, and identify the right side with `swtc_slice` at time `s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The open space-time region `(0, ∞) × ℝ²`. -/
abbrev swtcO : Set (ℝ × Plane) := Ioi (0:ℝ) ×ˢ (univ : Set Plane)

theorem swtcO_isOpen : IsOpen swtcO := isOpen_Ioi.prod isOpen_univ

theorem swtc_mem {t : ℝ} (z : Plane) (ht : 0 < t) : (t, z) ∈ swtcO :=
  Set.mk_mem_prod (Set.mem_Ioi.mpr ht) (Set.mem_univ z)

/-- The space-time word: `true` is `∂_q`, `false` is `∂_η`, the head of the list is applied last,
exactly as in `B0151.derivWord`. -/
def swtcWord : List Bool → (ℝ × Plane → ℝ) → (ℝ × Plane → ℝ)
  | [], H => H
  | true :: w, H => LV.lvDir LV.lvEQ (swtcWord w H)
  | false :: w, H => LV.lvDir LV.lvEE (swtcWord w H)

theorem swtcWord_nil (H : ℝ × Plane → ℝ) : swtcWord [] H = H := rfl

theorem swtcWord_true (w : List Bool) (H : ℝ × Plane → ℝ) :
    swtcWord (true :: w) H = LV.lvDir LV.lvEQ (swtcWord w H) := rfl

theorem swtcWord_false (w : List Bool) (H : ℝ × Plane → ℝ) :
    swtcWord (false :: w) H = LV.lvDir LV.lvEE (swtcWord w H) := rfl

theorem swtc_sm (u : List Bool) (H : ℝ × Plane → ℝ) (h : LV.lvSm swtcO H) :
    LV.lvSm swtcO (swtcWord u H) := by
  induction u with
  | nil => rw [swtcWord_nil]; exact h
  | cons b w ih =>
    cases b
    · rw [swtcWord_false]; exact LV.lvSm.dir swtcO_isOpen ih _
    · rw [swtcWord_true]; exact LV.lvSm.dir swtcO_isOpen ih _

theorem swtc_slice (u : List Bool) : ∀ (H : ℝ × Plane → ℝ), LV.lvSm swtcO H →
    ∀ (t : ℝ), 0 < t → ∀ z : Plane,
      B0151.derivWord u (fun z' => H (t, z')) z = swtcWord u H (t, z) := by
  induction u with
  | nil => intro H _ t _ z; rfl
  | cons b w ih =>
    intro H h t ht z
    have hfun : B0151.derivWord w (fun z' => H (t, z')) = fun z' => swtcWord w H (t, z') :=
      funext (fun z' => ih H h t ht z')
    have hd : DifferentiableAt ℝ (swtcWord w H) (t, z) :=
      LV.lvSm.differentiableAt swtcO_isOpen (swtc_sm w H h) (swtc_mem z ht)
    cases b
    · rw [swtcWord_false]
      change UnforcedLeray.GaussianVortex.partialY (B0151.derivWord w (fun z' => H (t, z'))) z = _
      rw [hfun]
      exact LV.lvSliceE hd
    · rw [swtcWord_true]
      change UnforcedLeray.GaussianVortex.partialX (B0151.derivWord w (fun z' => H (t, z'))) z = _
      rw [hfun]
      exact LV.lvSliceQ hd

theorem swtc_comm (u : List Bool) (H : ℝ × Plane → ℝ) (h : LV.lvSm swtcO H) :
    ∀ x ∈ swtcO, LV.lvDir LV.lvEt (swtcWord u H) x = swtcWord u (LV.lvDir LV.lvEt H) x := by
  induction u with
  | nil => intro x _; rfl
  | cons b w ih =>
    intro x hx
    have hw : LV.lvSm swtcO (swtcWord w H) := swtc_sm w H h
    cases b
    · rw [swtcWord_false, swtcWord_false]
      rw [LV.lvDir_symm swtcO_isOpen hw hx LV.lvEt LV.lvEE]
      exact LV.lvDir_congr (H₁ := LV.lvDir LV.lvEt (swtcWord w H))
        (H₂ := swtcWord w (LV.lvDir LV.lvEt H)) swtcO_isOpen ih hx LV.lvEE
    · rw [swtcWord_true, swtcWord_true]
      rw [LV.lvDir_symm swtcO_isOpen hw hx LV.lvEt LV.lvEQ]
      exact LV.lvDir_congr (H₁ := LV.lvDir LV.lvEt (swtcWord w H))
        (H₂ := swtcWord w (LV.lvDir LV.lvEt H)) swtcO_isOpen ih hx LV.lvEQ

theorem swtc_main (F : ℝ × Plane → ℝ) (hF : ContDiffOn ℝ ∞ F swtcO) (u : List Bool)
    (s : ℝ) (z : Plane) (hs : 0 < s) :
    deriv (fun t => B0151.derivWord u (fun z' => F (t, z')) z) s =
      B0151.derivWord u (fun z' => deriv (fun t => F (t, z')) s) z := by
  have hsm : LV.lvSm swtcO F := hF
  have hev : (fun t => B0151.derivWord u (fun z' => F (t, z')) z) =ᶠ[𝓝 s]
      (fun t => swtcWord u F (t, z)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact swtc_slice u F hsm t ht z
  have hdiff : DifferentiableAt ℝ (swtcWord u F) (s, z) :=
    LV.lvSm.differentiableAt swtcO_isOpen (swtc_sm u F hsm) (swtc_mem z hs)
  rw [hev.deriv_eq, LV.lvSliceT hdiff, swtc_comm u F hsm (s, z) (swtc_mem z hs)]
  have hfun : (fun z' => deriv (fun t => F (t, z')) s) =
      (fun z' => LV.lvDir LV.lvEt F (s, z')) := by
    funext z'
    exact LV.lvSliceT (LV.lvSm.differentiableAt swtcO_isOpen hsm (swtc_mem z' hs))
  rw [hfun, swtc_slice u (LV.lvDir LV.lvEt F) (LV.lvSm.dir swtcO_isOpen hsm LV.lvEt) s hs z]

theorem sliceWordTimeComm_proof : UnforcedLeray.Short.PartI.SliceWordTimeComm := by
  unfold SliceWordTimeComm
  intro F hF u s z hs
  exact swtc_main F hF u s z hs

end UnforcedLeray.Short.PartI
