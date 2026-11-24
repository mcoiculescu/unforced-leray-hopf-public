import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2
import UnforcedLeray.Loc.Hyp.ModeIdentification.Slices

/-!
# `sliceH1Real`: decomposition into the real `H¹` core and real/complex bridges

Source `the November 2 reference manuscript` lines 1351-1362 (one-slice `H¹`
bound).  For real-valued `f, h ∈ L²(ℝ³;ℂ³)` (viewed as `ℝ³`-valued fields `reV f`, `reV h`) the
complex identity `SliceLapPair f h` restricts to real vector tests, the real elliptic `H¹`
regularity (`Blueprint.ModeId.laplacianH1Regularity` plus the energy identity from
`HasWeakLaplacian`) gives real `Gⱼ ∈ L²`, and complex tests split as `θ = embR(re θ) + i embR(im θ)`.

Proved here: the norm / `L²` bookkeeping for the embeddings and the assembly
`sliceH1Real_of`.  The Props `RealH1Core`, `RealTestBridge`, `WeakDerBridge` are the remaining
source facts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Real part of a `ℂ³`-field as an `ℝ³`-field. -/
def reV (f : Space → CVec3) : Space → Space := fun y => WithLp.toLp 2 fun i => (f y i).re

/-- Real `ℝ³`-field embedded in `ℂ³`. -/
def embR (u : Space → Space) : Space → CVec3 := fun y => WithLp.toLp 2 fun i => ((u y i : ℝ) : ℂ)

namespace D2SliceRe

/-- `reV` as a continuous linear map. -/
def reL : CVec3 →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => (x i).re
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

end D2SliceRe

/-- `embR` as a continuous linear map. -/
def embL : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => ((x i : ℝ) : ℂ)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

theorem reV_eq (f : Space → CVec3) : reV f = fun y => D2SliceRe.reL (f y) := rfl
theorem embR_eq (u : Space → Space) : embR u = fun y => embL (u y) := rfl

theorem norm_embR (u : Space → Space) (y : Space) : ‖embR u y‖ = ‖u y‖ := by
  simp [embR, EuclideanSpace.norm_eq]

theorem norm_reV_of_real {f : Space → CVec3} (hf : IsRealV f) (y : Space) :
    ‖reV f y‖ = ‖f y‖ := by
  have : ∀ i, ‖f y i‖ = |(f y i).re| := fun i => by
    have h : f y i = (((f y i).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hf y i)
    conv_lhs => rw [h]
    simp
  simp [reV, EuclideanSpace.norm_eq, this]

theorem isRealV_embR (u : Space → Space) : IsRealV (embR u) := fun y i => by simp [embR]

theorem memLp_embR {u : Space → Space} (hu : MemLp u 2 volume) : MemLp (embR u) 2 volume := by
  rw [embR_eq]; exact embL.comp_memLp' hu

theorem memLp_reV {f : Space → CVec3} (hf : MemLp f 2 volume) : MemLp (reV f) 2 volume := by
  rw [reV_eq]; exact D2SliceRe.reL.comp_memLp' hf

theorem integral_norm_sq_embR (u : Space → Space) :
    (∫ y : Space, ‖embR u y‖ ^ 2) = ∫ y : Space, ‖u y‖ ^ 2 := by
  simp_rw [norm_embR]

theorem integral_norm_sq_reV {f : Space → CVec3} (hf : IsRealV f) :
    (∫ y : Space, ‖reV f y‖ ^ 2) = ∫ y : Space, ‖f y‖ ^ 2 := by
  simp_rw [norm_reV_of_real hf]

/-- (A) Real elliptic `H¹` core (source 1351-1362; library `Blueprint.ModeId.laplacianH1Regularity`
gives `F ∈ H¹` with `HasWeakLaplacian F v`, whose energy identity `⟨∇F,∇F⟩ = -⟨u, v⟩` and
Cauchy–Schwarz give the bound): for `u, v ∈ L²(ℝ³;ℝ³)` with `⟨u, Δφ⟩ = ⟨v, φ⟩` for all real vector
tests there are `Gⱼ ∈ L²` with `-⟨u, ∂ⱼφ⟩ = ⟨Gⱼ, φ⟩` and `∑ⱼ‖Gⱼ‖² ≤ ‖u‖‖v‖`. -/
def RealH1Core : Prop :=
  ∀ u v : Space → Space, MemLp u 2 volume → MemLp v 2 volume →
    (∀ φ : Space → Space, UnforcedLeray.Blueprint.IsVectorTest φ →
      (∫ y : Space, inner ℝ (u y) (UnforcedLeray.Blueprint.ModeId.testLap φ y))
        = ∫ y : Space, inner ℝ (v y) (φ y)) →
    ∃ G : Fin 3 → Space → Space, (∀ j, MemLp (G j) 2 volume) ∧
      (∀ (j : Fin 3) (φ : Space → Space), UnforcedLeray.Blueprint.IsVectorTest φ →
        -(∫ y : Space, inner ℝ (u y) (UnforcedLeray.Blueprint.testPartial φ j y))
          = ∫ y : Space, inner ℝ (G j y) (φ y)) ∧
      ∑ j : Fin 3, (∫ y : Space, ‖G j y‖ ^ 2)
        ≤ (∫ y : Space, ‖u y‖ ^ 2) ^ (1 / 2 : ℝ) * (∫ y : Space, ‖v y‖ ^ 2) ^ (1 / 2 : ℝ)

/-- (B) Restriction of the complex slice identity to real tests (source 1351-1362): for real `f, h`
and real vector test `φ`, test `SliceLapPair` with `θ = embR φ`
(`lapS (embR φ) = embR (testLap φ)` by the chain rule for the continuous linear map `embL`, and
`∑ᵢ f y i * (embR ψ y i) = ((inner (reV f y) (ψ y) : ℝ) : ℂ)` for real `f`); take real parts. -/
def RealTestBridge : Prop :=
  ∀ f h : Space → CVec3, IsRealV f → IsRealV h → MemLp f 2 volume → MemLp h 2 volume →
    SliceLapPair f h →
    ∀ φ : Space → Space, UnforcedLeray.Blueprint.IsVectorTest φ →
      (∫ y : Space, inner ℝ (reV f y) (UnforcedLeray.Blueprint.ModeId.testLap φ y))
        = ∫ y : Space, inner ℝ (reV h y) (φ y)

/-- (C) Real weak derivative to complex weak derivative (source 1351-1362): if `f` is real and
`-⟨reV f, ∂ⱼφ⟩ = ⟨G, φ⟩` for real vector tests `φ`, then `WeakDer f j (embR G)`: a complex test
splits as `θ = embR (reV θ) + i embR (imV θ)` with both parts real vector tests
(`fderiv` of `fun z => θ z i` commutes with `re`, `im` by `reL`, `imL`), and `f` real kills the
imaginary part of the pairing. -/
def WeakDerBridge : Prop :=
  ∀ (f : Space → CVec3) (G : Space → Space) (j : Fin 3), IsRealV f → MemLp f 2 volume →
    MemLp G 2 volume →
    (∀ φ : Space → Space, UnforcedLeray.Blueprint.IsVectorTest φ →
      -(∫ y : Space, inner ℝ (reV f y) (UnforcedLeray.Blueprint.testPartial φ j y))
        = ∫ y : Space, inner ℝ (G y) (φ y)) →
    WeakDer f j (embR G)

theorem sliceH1Real_of (hA : RealH1Core) (hB : RealTestBridge) (hC : WeakDerBridge) :
    SliceH1Real := by
  intro f h hf hh mf mh hid
  obtain ⟨G, mG, wG, bG⟩ := hA (reV f) (reV h) (memLp_reV mf) (memLp_reV mh)
    (hB f h hf hh mf mh hid)
  refine ⟨fun j => embR (G j), fun j => memLp_embR (mG j), fun j => isRealV_embR _,
    fun j => hC f (G j) j hf mf (mG j) (wG j), ?_⟩
  simp only [integral_norm_sq_embR]
  rw [integral_norm_sq_reV hf, integral_norm_sq_reV hh] at bG
  exact bG

end UnforcedLeray.Short.PartIIIb.Concrete
