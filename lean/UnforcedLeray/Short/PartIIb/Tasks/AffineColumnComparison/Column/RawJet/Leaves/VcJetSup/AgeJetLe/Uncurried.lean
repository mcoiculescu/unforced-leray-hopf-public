import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe.LapJet

/-!
Helper for task `PartII-b:G4/3/6/1/5/1`: calculus of jointly smooth fields `F : ℝ × Plane → Vec`
on the open set `s > 0`: directional derivatives `Dx`, the spatial Laplacian `LapU`, symmetry of
second derivatives (`∂_s` commutes with `Δ`), and the link to slices.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Train UnforcedLeray.Cyl

/-- The open set of positive ages. -/
def UU : Set (ℝ × Plane) := Ioi 0 ×ˢ univ

theorem isOpen_UU : IsOpen UU := isOpen_Ioi.prod isOpen_univ

theorem mem_UU {t : ℝ} {w : Plane} (ht : 0 < t) : (t, w) ∈ UU := ⟨ht, mem_univ w⟩

noncomputable def Dx (v : ℝ × Plane) (F : ℝ × Plane → Vec) : ℝ × Plane → Vec :=
  fun x => fderiv ℝ F x v

def eT : ℝ × Plane := (1, 0)
def eQ : ℝ × Plane := (0, ((1 : ℝ), (0 : ℝ)))
def eE : ℝ × Plane := (0, ((0 : ℝ), (1 : ℝ)))

noncomputable def LapU (F : ℝ × Plane → Vec) : ℝ × Plane → Vec :=
  fun x => Dx eQ (Dx eQ F) x + Dx eE (Dx eE F) x

def Sm (F : ℝ × Plane → Vec) : Prop := ContDiffOn ℝ ∞ F UU

theorem Sm.dx {F : ℝ × Plane → Vec} (hF : Sm F) (v : ℝ × Plane) : Sm (Dx v F) :=
  (hF.fderiv_of_isOpen isOpen_UU (by simp)).clm_apply contDiffOn_const

theorem Sm.lap {F : ℝ × Plane → Vec} (hF : Sm F) : Sm (LapU F) :=
  ((hF.dx _).dx _).add ((hF.dx _).dx _)

theorem Sm.diffAt {F : ℝ × Plane → Vec} (hF : Sm F) {x : ℝ × Plane} (hx : x ∈ UU) :
    DifferentiableAt ℝ F x :=
  (hF.differentiableOn (by simp)).differentiableAt (isOpen_UU.mem_nhds hx)

theorem Sm.symm {F : ℝ × Plane → Vec} (hF : Sm F) {x : ℝ × Plane} (hx : x ∈ UU)
    (v w : ℝ × Plane) : Dx w (Dx v F) x = Dx v (Dx w F) x := by
  have hc : ContDiffAt ℝ ∞ F x := hF.contDiffAt (isOpen_UU.mem_nhds hx)
  have hc2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) F x := hc.of_le (by simp)
  have hn : minSmoothness ℝ 2 ≤ ((2 : ℕ) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    simp
  have hs := ContDiffAt.isSymmSndFDerivAt hc2 hn
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen (m := ∞) isOpen_UU (by simp)).differentiableOn (by simp)).differentiableAt
      (isOpen_UU.mem_nhds hx)
  have key : ∀ a b : ℝ × Plane, Dx a (Dx b F) x = fderiv ℝ (fderiv ℝ F) x a b := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ F y b) x a = _
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [key, key]
  exact hs w v

theorem Dx_congr {F F' : ℝ × Plane → Vec} (h : EqOn F F' UU) (v : ℝ × Plane) :
    EqOn (Dx v F) (Dx v F') UU := by
  intro x hx
  have : F =ᶠ[nhds x] F' := h.eventuallyEq_of_mem (isOpen_UU.mem_nhds hx)
  show fderiv ℝ F x v = fderiv ℝ F' x v
  rw [this.fderiv_eq]

theorem Dx_smul {F : ℝ × Plane → Vec} (hF : Sm F) (c : ℝ) (v : ℝ × Plane) :
    EqOn (Dx v (fun y => c • F y)) (fun y => c • Dx v F y) UU := by
  intro x hx
  show fderiv ℝ (fun y => c • F y) x v = c • fderiv ℝ F x v
  have h : HasFDerivAt (fun y => c • F y) (c • fderiv ℝ F x) x :=
    (hF.diffAt hx).hasFDerivAt.const_smul c
  rw [h.fderiv]
  rfl

theorem LapU_congr {F F' : ℝ × Plane → Vec} (h : EqOn F F' UU) : EqOn (LapU F) (LapU F') UU := by
  intro x hx
  have h1 := Dx_congr (Dx_congr h eQ) eQ hx
  have h2 := Dx_congr (Dx_congr h eE) eE hx
  show Dx eQ (Dx eQ F) x + Dx eE (Dx eE F) x = Dx eQ (Dx eQ F') x + Dx eE (Dx eE F') x
  rw [h1, h2]

theorem LapU_smul {F : ℝ × Plane → Vec} (hF : Sm F) (c : ℝ) :
    EqOn (LapU (fun y => c • F y)) (fun y => c • LapU F y) UU := by
  intro x hx
  have a1 : Dx eQ (Dx eQ fun y => c • F y) x = c • Dx eQ (Dx eQ F) x := by
    rw [Dx_congr (Dx_smul hF c eQ) eQ hx]
    exact Dx_smul (hF.dx eQ) c eQ hx
  have a2 : Dx eE (Dx eE fun y => c • F y) x = c • Dx eE (Dx eE F) x := by
    rw [Dx_congr (Dx_smul hF c eE) eE hx]
    exact Dx_smul (hF.dx eE) c eE hx
  show Dx eQ (Dx eQ fun y => c • F y) x + Dx eE (Dx eE fun y => c • F y) x =
    c • (Dx eQ (Dx eQ F) x + Dx eE (Dx eE F) x)
  rw [a1, a2, smul_add]

theorem Dx_add {A B : ℝ × Plane → Vec} (hA : Sm A) (hB : Sm B) (v : ℝ × Plane) :
    EqOn (Dx v (fun y => A y + B y)) (fun y => Dx v A y + Dx v B y) UU := by
  intro x hx
  show fderiv ℝ (fun y => A y + B y) x v = fderiv ℝ A x v + fderiv ℝ B x v
  have h : HasFDerivAt (fun y => A y + B y) (fderiv ℝ A x + fderiv ℝ B x) x :=
    (hA.diffAt hx).hasFDerivAt.add (hB.diffAt hx).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem Dx_comm_sq {F : ℝ × Plane → Vec} (hF : Sm F) (e : ℝ × Plane) {x : ℝ × Plane}
    (hx : x ∈ UU) : Dx eT (Dx e (Dx e F)) x = Dx e (Dx e (Dx eT F)) x := by
  have hG : Sm (Dx e F) := hF.dx e
  have h1 : Dx eT (Dx e (Dx e F)) x = Dx e (Dx eT (Dx e F)) x := hG.symm hx e eT
  have h2 : EqOn (Dx eT (Dx e F)) (Dx e (Dx eT F)) UU := fun y hy => hF.symm hy e eT
  rw [h1]
  exact Dx_congr h2 e hx

/-- `∂_s` commutes with the spatial Laplacian. -/
theorem LapU_comm_t {F : ℝ × Plane → Vec} (hF : Sm F) :
    EqOn (Dx eT (LapU F)) (LapU (Dx eT F)) UU := by
  intro x hx
  have hQ : Sm (Dx eQ (Dx eQ F)) := (hF.dx _).dx _
  have hE : Sm (Dx eE (Dx eE F)) := (hF.dx _).dx _
  have := Dx_add hQ hE eT hx
  show Dx eT (fun y => Dx eQ (Dx eQ F) y + Dx eE (Dx eE F) y) x = _
  rw [this]
  show Dx eT (Dx eQ (Dx eQ F)) x + Dx eT (Dx eE (Dx eE F)) x = _
  rw [Dx_comm_sq hF eQ hx, Dx_comm_sq hF eE hx]
  rfl

end UnforcedLeray.Short.IIb
