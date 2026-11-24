import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Units.B0151.DivCurl

/-!
# Part I, task `PartI:T08/2/2/2/7`: `DerivWordConsAppend` (Schwarz for spatial words)

Target: `theorem derivWordConsAppend_proof : UnforcedLeray.Short.PartI.DerivWordConsAppend`.

Source of record: `the November 2 reference manuscript`, lines 276-288; the leaf
statement is in `Sub/PartI_T08_2_2/EnergyIneq.lean`.

Route: the partial derivatives of a smooth function commute (`B0151.partialX_partialY_comm`), hence
`∂_b (derivWord u f) = derivWord u (∂_b f)` for smooth `f`, and `derivWord (u ++ v) f =
derivWord u (derivWord v f)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Single letters commute on smooth functions. -/
theorem dwcaSingle_comm {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Bool) :
    B0151.derivWord [a] (B0151.derivWord [b] g) = B0151.derivWord [b] (B0151.derivWord [a] g) := by
  have h2 : ContDiff ℝ 2 g := hg.of_le (by simp)
  cases a <;> cases b
  · rfl
  · exact funext fun z => (B0151.partialX_partialY_comm h2 z).symm
  · exact funext fun z => B0151.partialX_partialY_comm h2 z
  · rfl

theorem dwcaAppend (f : Plane → ℝ) (u v : List Bool) :
    B0151.derivWord (u ++ v) f = B0151.derivWord u (B0151.derivWord v f) := by
  induction u with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp [B0151.derivWord, ih]

/-- Partial derivatives commute with `derivWord` on smooth functions. -/
theorem dwcaComm (b : Bool) (u : List Bool) :
    ∀ f : Plane → ℝ, ContDiff ℝ ∞ f →
      B0151.derivWord [b] (B0151.derivWord u f) = B0151.derivWord u (B0151.derivWord [b] f) := by
  induction u with
  | nil => intro f hf; rfl
  | cons a w ih =>
    intro f hf
    have hw : ContDiff ℝ ∞ (B0151.derivWord w f) := B0151.contDiff_derivWord hf w
    have e1 : B0151.derivWord [b] (B0151.derivWord (a :: w) f) =
        B0151.derivWord [b] (B0151.derivWord [a] (B0151.derivWord w f)) := by cases a <;> rfl
    have e2 : B0151.derivWord (a :: w) (B0151.derivWord [b] f) =
        B0151.derivWord [a] (B0151.derivWord w (B0151.derivWord [b] f)) := by cases a <;> rfl
    rw [e1, e2, ← ih f hf]
    exact dwcaSingle_comm hw b a

theorem derivWordConsAppend_proof : UnforcedLeray.Short.PartI.DerivWordConsAppend := by
  intro f hf b u
  have h1 : B0151.derivWord (b :: u) f = B0151.derivWord [b] (B0151.derivWord u f) := by cases b <;> rfl
  have h2 : B0151.derivWord (u ++ [b]) f = B0151.derivWord u (B0151.derivWord [b] f) :=
    dwcaAppend f u [b]
  rw [h1, h2]
  exact dwcaComm b u f hf

end UnforcedLeray.Short.PartI
