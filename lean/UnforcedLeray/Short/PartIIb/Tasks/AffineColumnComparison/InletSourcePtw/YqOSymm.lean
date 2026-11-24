import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1

/-!


`isOInvariant_iff` reduces `F ∈ Osym` to an a.e. identity on phases `θ ∈ ℝ/Pℤ`. The hypothesis
gives the identity on the line `ℝ` for a.e. `τ` (through the slice relation of `HasRep`), and
`ae_circle_of_ae_real` transports an a.e. statement from `ℝ` to the phase circle (the
preimage of a set under the measurable equivalence `AddCircle.measurableEquivIoc` is the set
itself, and its volume is the volume of the image in `Ioc`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412

/-- An almost-everywhere statement on the line, for a.e. `t`, transports to the phase circle. -/
theorem ae_circle_of_ae_real_yo {P : ℝ} [hP : Fact (0 < P)] {p : AddCircle P → Prop}
    (h : ∀ᵐ t : ℝ, p (t : AddCircle P)) : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), p θ := by
  rw [ae_iff] at h ⊢
  set S : Set (AddCircle P) := {θ | ¬ p θ} with hS
  have hmp : MeasurePreserving (AddCircle.measurableEquivIoc P 0) volume
      (Measure.comap Subtype.val volume) :=
    AddCircle.measurePreserving_equivIoc P
  set T : Set (Ioc (0 : ℝ) (0 + P)) := {x | ((x : ℝ) : AddCircle P) ∈ S} with hT
  have hpre : (AddCircle.measurableEquivIoc P 0) ⁻¹' T = S := by
    ext θ
    show ((((AddCircle.equivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ) : AddCircle P) ∈ S) ↔ θ ∈ S
    rw [AddCircle.coe_equivIoc]
  have hvol : (volume : Measure (AddCircle P)) S = 0 := by
    rw [← hpre, hmp.measure_preimage_equiv T,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    apply measure_mono_null _ h
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul,
    mul_eq_zero] at hvol
  exact hvol.resolve_left (ENNReal.ofReal_pos.2 hP.out).ne'

/-- **Packaging leaf** (SP 2370-2383): a pointwise `𝒪`-invariant representative lies in `Osym`. -/
theorem yqOSymm : UnforcedLeray.Short.IIb.YqOSymm := by
  intro P _ F W hW hWO
  rw [mem_Osym, isOInvariant_iff]
  intro g hg
  have hmp : MeasurePreserving g.symm volume volume := LinearIsometryEquiv.measurePreserving g.symm
  refine ae_circle_of_ae_real_yo
    (p := fun θ => ∀ᵐ y ∂(volume : Measure Space), gC g (F θ (g.symm y)) = F θ y) ?_
  filter_upwards [hW.slice] with t ht
  have h1 : ∀ᵐ y ∂(volume : Measure Space), W (t, y) = F (t : AddCircle P) y := ht
  have h2 : ∀ᵐ y ∂(volume : Measure Space), W (t, g.symm y) = F (t : AddCircle P) (g.symm y) :=
    (hmp.quasiMeasurePreserving).ae
      (p := fun z => W (t, z) = F (t : AddCircle P) z) h1
  filter_upwards [h1, h2] with y e1 e2
  rw [← e2, hWO g hg t y, e1]

end UnforcedLeray.Short.IIb
