import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation.Layer

/-!
# Part I, `PartI:T04/10/1/2/1/2` (`SliceWordTimeCommOn`)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Copy of the `SliceWordTimeComm` route with the open strip `O = Ioo a b ×ˢ univ` in place of
`Ioi 0 ×ˢ univ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The open space-time strip `(a, b) × ℝ²`. -/
abbrev swoO (a b : ℝ) : Set (ℝ × Plane) := Ioo a b ×ˢ (univ : Set Plane)

theorem swoO_isOpen (a b : ℝ) : IsOpen (swoO a b) := isOpen_Ioo.prod isOpen_univ

theorem swo_mem {a b t : ℝ} (z : Plane) (ht : t ∈ Ioo a b) : (t, z) ∈ swoO a b :=
  Set.mk_mem_prod ht (Set.mem_univ z)

/-- The space-time word on the strip (same convention as `B0151.derivWord`). -/
def swoWord : List Bool → (ℝ × Plane → ℝ) → (ℝ × Plane → ℝ)
  | [], H => H
  | true :: w, H => LV.lvDir LV.lvEQ (swoWord w H)
  | false :: w, H => LV.lvDir LV.lvEE (swoWord w H)

theorem swoWord_nil (H : ℝ × Plane → ℝ) : swoWord [] H = H := rfl

theorem swoWord_true (w : List Bool) (H : ℝ × Plane → ℝ) :
    swoWord (true :: w) H = LV.lvDir LV.lvEQ (swoWord w H) := rfl

theorem swoWord_false (w : List Bool) (H : ℝ × Plane → ℝ) :
    swoWord (false :: w) H = LV.lvDir LV.lvEE (swoWord w H) := rfl

theorem swo_sm (a b : ℝ) (u : List Bool) (H : ℝ × Plane → ℝ) (h : LV.lvSm (swoO a b) H) :
    LV.lvSm (swoO a b) (swoWord u H) := by
  induction u with
  | nil => rw [swoWord_nil]; exact h
  | cons bb w ih =>
    cases bb
    · rw [swoWord_false]; exact LV.lvSm.dir (swoO_isOpen a b) ih _
    · rw [swoWord_true]; exact LV.lvSm.dir (swoO_isOpen a b) ih _

theorem swo_slice (a b : ℝ) (u : List Bool) : ∀ (H : ℝ × Plane → ℝ), LV.lvSm (swoO a b) H →
    ∀ (t : ℝ), t ∈ Ioo a b → ∀ z : Plane,
      B0151.derivWord u (fun z' => H (t, z')) z = swoWord u H (t, z) := by
  induction u with
  | nil => intro H _ t _ z; rfl
  | cons bb w ih =>
    intro H h t ht z
    have hfun : B0151.derivWord w (fun z' => H (t, z')) = fun z' => swoWord w H (t, z') :=
      funext (fun z' => ih H h t ht z')
    have hd : DifferentiableAt ℝ (swoWord w H) (t, z) :=
      LV.lvSm.differentiableAt (swoO_isOpen a b) (swo_sm a b w H h) (swo_mem z ht)
    cases bb
    · rw [swoWord_false]
      change UnforcedLeray.GaussianVortex.partialY (B0151.derivWord w (fun z' => H (t, z'))) z = _
      rw [hfun]
      exact LV.lvSliceE hd
    · rw [swoWord_true]
      change UnforcedLeray.GaussianVortex.partialX (B0151.derivWord w (fun z' => H (t, z'))) z = _
      rw [hfun]
      exact LV.lvSliceQ hd

theorem swo_comm (a b : ℝ) (u : List Bool) (H : ℝ × Plane → ℝ) (h : LV.lvSm (swoO a b) H) :
    ∀ x ∈ swoO a b, LV.lvDir LV.lvEt (swoWord u H) x = swoWord u (LV.lvDir LV.lvEt H) x := by
  induction u with
  | nil => intro x _; rfl
  | cons bb w ih =>
    intro x hx
    have hw : LV.lvSm (swoO a b) (swoWord w H) := swo_sm a b w H h
    cases bb
    · rw [swoWord_false, swoWord_false]
      rw [LV.lvDir_symm (swoO_isOpen a b) hw hx LV.lvEt LV.lvEE]
      exact LV.lvDir_congr (H₁ := LV.lvDir LV.lvEt (swoWord w H))
        (H₂ := swoWord w (LV.lvDir LV.lvEt H)) (swoO_isOpen a b) ih hx LV.lvEE
    · rw [swoWord_true, swoWord_true]
      rw [LV.lvDir_symm (swoO_isOpen a b) hw hx LV.lvEt LV.lvEQ]
      exact LV.lvDir_congr (H₁ := LV.lvDir LV.lvEt (swoWord w H))
        (H₂ := swoWord w (LV.lvDir LV.lvEt H)) (swoO_isOpen a b) ih hx LV.lvEQ

theorem swo_main (a b : ℝ) (F : ℝ × Plane → ℝ) (hF : ContDiffOn ℝ ∞ F (swoO a b))
    (u : List Bool) (s : ℝ) (z : Plane) (hs : s ∈ Ioo a b) :
    deriv (fun t => B0151.derivWord u (fun z' => F (t, z')) z) s =
      B0151.derivWord u (fun z' => deriv (fun t => F (t, z')) s) z := by
  have hsm : LV.lvSm (swoO a b) F := hF
  have hev : (fun t => B0151.derivWord u (fun z' => F (t, z')) z) =ᶠ[𝓝 s]
      (fun t => swoWord u F (t, z)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact swo_slice a b u F hsm t ht z
  have hdiff : DifferentiableAt ℝ (swoWord u F) (s, z) :=
    LV.lvSm.differentiableAt (swoO_isOpen a b) (swo_sm a b u F hsm) (swo_mem z hs)
  rw [hev.deriv_eq, LV.lvSliceT hdiff, swo_comm a b u F hsm (s, z) (swo_mem z hs)]
  have hfun : (fun z' => deriv (fun t => F (t, z')) s) =
      (fun z' => LV.lvDir LV.lvEt F (s, z')) := by
    funext z'
    exact LV.lvSliceT (LV.lvSm.differentiableAt (swoO_isOpen a b) hsm (swo_mem z' hs))
  rw [hfun, swo_slice a b u (LV.lvDir LV.lvEt F) (LV.lvSm.dir (swoO_isOpen a b) hsm LV.lvEt) s hs z]

theorem sliceWordTimeCommOn_proof : SliceWordTimeCommOn := by
  intro a b F hF u
  refine ⟨?_, ?_⟩
  · have hsm : LV.lvSm (swoO a b) F := hF
    have hc : LV.lvSm (swoO a b) (swoWord u F) := swo_sm a b u F hsm
    exact hc.congr (fun x hx => swo_slice a b u F hsm x.1 hx.1 x.2)
  · intro s hs z
    exact swo_main a b F hF u s z hs

end UnforcedLeray.Short.PartI
