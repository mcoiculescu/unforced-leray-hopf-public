import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10

/-!
# Part II-b, task `PartII-b:T10/3` (`WeakVecCongr`): `HasWeakVec` sees the profile only on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 1912-1921.

Target: `weakVecCongr_proof : UnforcedLeray.Short.IIb.WeakVecCongr`.

Proof outline. A coordinate test `φ` is supported in `{s > 0}`, so its transpose
`coordTranspose v d φ` vanishes off `{s > 0}`. Hence the integrands `u · coordTranspose φ` and
`g · φ` only see `u` on `{s > 0}`, where `b = b'` almost everywhere on `posReg`. The argument is
the same as `WeakFOCongr` (`Tasks/GradLapNvC/LapSmooth/WeakCongr.lean`), componentwise over `Fin 2`,
with the hypothesis first converted from `posReg`-a.e. to an a.e. statement on `Coord`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace WeakVecCongrHelp

/-- The transpose of a coordinate test vanishes off `{s > 0}`. -/
lemma coordTranspose_eq_zero_of_nonpos (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    {φ : Coord → ℝ} (hφ : IsCoordTest φ) {x : Coord} (hx : ¬ (0 < x.1)) :
    coordTranspose v d φ x = 0 := by
  have hx_not : x ∉ tsupport φ := fun h => hx (Set.mem_prod.1 (hφ.supp h)).1
  have hφx : φ x = 0 := by
    by_contra hne
    exact hx_not (subset_tsupport φ (Function.mem_support.2 hne))
  have hD : ∀ j : Fin 3, fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) = 0 := by
    intro j
    have hψsub : x ∉ tsupport (fun y : Coord => v y j * φ y) := fun h =>
      hx_not ((tsupport_mul_subset_right (f := fun y : Coord => v y j) (g := φ)) h)
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hψsub]
    simp
  unfold coordTranspose cpd
  simp [hD, hφx]

/-- Scalar version: the weak clause only sees `u` on `{s > 0}`, up to a.e. equality. -/
lemma weakFO_congr_scalar (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u u' g : Coord → ℂ)
    (hae : ∀ᵐ x : Coord, 0 < x.1 → u x = u' x) (hw : HasWeakFO v d u g) :
    HasWeakFO v d u' g := by
  obtain ⟨h1, h2⟩ := hw
  have hEq : ∀ φ : Coord → ℝ, IsCoordTest φ →
      (fun x => u x * (coordTranspose v d φ x : ℂ)) =ᵐ[volume]
        (fun x => u' x * (coordTranspose v d φ x : ℂ)) := by
    intro φ hφ
    filter_upwards [hae] with x hx
    by_cases hpos : 0 < x.1
    · rw [hx hpos]
    · rw [coordTranspose_eq_zero_of_nonpos v d hφ hpos]
      simp
  refine ⟨fun φ hφ => ⟨(h1 φ hφ).1.congr (hEq φ hφ), (h1 φ hφ).2⟩, fun φ hφ => ?_⟩
  rw [h2 φ hφ]
  exact integral_congr_ae (hEq φ hφ)

/-- The `posReg`-a.e. hypothesis gives the a.e. hypothesis on `Coord` with `0 < x.1`. -/
lemma ae_of_posReg {u u' : Coord → ℂ} (h : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))),
    u x = u' x) : ∀ᵐ x : Coord, 0 < x.1 → u x = u' x := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  refine (ae_restrict_iff' hS).1 h |>.mono fun x hx hpos => hx ⟨hpos, trivial⟩

end WeakVecCongrHelp

open WeakVecCongrHelp in
theorem weakVecCongr_proof : UnforcedLeray.Short.IIb.WeakVecCongr := by
  intro v d b b' g hbb hw
  unfold HasWeakVec at hw ⊢
  intro i
  exact weakFO_congr_scalar v d (fun x => b x i) (fun x => b' x i) (fun x => g x i)
    (ae_of_posReg (by
      have h := hbb
      filter_upwards [h] with x hx
      show b x i = b' x i
      rw [hx]))
    (hw i)

end UnforcedLeray.Short.IIb
