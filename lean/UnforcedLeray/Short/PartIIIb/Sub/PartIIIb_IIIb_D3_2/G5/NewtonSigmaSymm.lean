import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonOrg
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtReflect

/-!
# Planar reflection and swap symmetries of `sigmaInt` (`PartIII-b:IIIb-D3/2/G5/2/1`)

Source of record: `the November 2 reference manuscript`, lines 4859-4862.
Proves `sigmaIntSymm`: off-diagonal entries of `sigmaInt c ν chio M` vanish and
`sigmaInt c ν chio M 0 0 = sigmaInt c ν chio M 1 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- Negation on `ℝ × ℝ` as a measurable equivalence. -/
def negE : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  MeasurableEquiv.neg (ℝ × ℝ)

theorem negE_apply (y : ℝ × ℝ) : negE y = -y := rfl

theorem negE_measurePreserving : MeasurePreserving negE volume volume :=
  Measure.measurePreserving_neg (volume : Measure (ℝ × ℝ))

/-- Coordinate swap on `ℝ × ℝ` as a measurable equivalence. -/
def swapE : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  MeasurableEquiv.prodComm

theorem swapE_apply (y : ℝ × ℝ) : swapE y = Prod.swap y := rfl

theorem swapE_measurePreserving : MeasurePreserving swapE volume volume := by
  have h : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    Measure.measurePreserving_swap
  exact h

/-- If `f (e y) = - f y` for a measure-preserving measurable equivalence `e`, then `∫ y, f y = 0`. -/
theorem integral_eq_zero_of_odd {e : ℝ × ℝ ≃ᵐ ℝ × ℝ} (he : MeasurePreserving e volume volume)
    {f : ℝ × ℝ → ℝ} (hf : ∀ y, f (e y) = -f y) :
    (∫ y : ℝ × ℝ, f y) = 0 := by
  have h1 : (∫ y : ℝ × ℝ, f (e y)) = ∫ y : ℝ × ℝ, f y := he.integral_comp' f
  have h2 : (∫ y : ℝ × ℝ, f (e y)) = -∫ y : ℝ × ℝ, f y := by
    simp only [hf, integral_neg]
  linarith

theorem sigmaM_negE_zero_two (c ν : ℝ) (chio : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν chio M (negE y) 0 2 = -sigmaM c ν chio M y 0 2 := by
  rw [negE_apply, sigmaM_zero_two, sigmaM_zero_two]
  have hsq : (-y).1 ^ 2 + (-y).2 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    simp [Prod.fst_neg, Prod.snd_neg]
  rw [hsq, Prod.fst_neg]
  ring

theorem sigmaM_negE_two_zero (c ν : ℝ) (chio : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν chio M (negE y) 2 0 = -sigmaM c ν chio M y 2 0 := by
  rw [negE_apply, sigmaM_two_zero, sigmaM_two_zero]
  have hsq : (-y).1 ^ 2 + (-y).2 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    simp [Prod.fst_neg, Prod.snd_neg]
  rw [hsq, Prod.fst_neg]
  ring

theorem sigmaM_swapE_zero_zero (c ν : ℝ) (chio : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν chio M (swapE y) 0 0 = sigmaM c ν chio M y 1 1 := by
  rw [swapE_apply, sigmaM_zero_zero, sigmaM_one_one]
  have hsq : (Prod.swap y).1 ^ 2 + (Prod.swap y).2 ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    simp [Prod.fst_swap, Prod.snd_swap, add_comm]
  rw [hsq, Prod.fst_swap]

/-- Off-diagonal entries of `sigmaInt c ν chio M` vanish and
`sigmaInt c ν chio M 0 0 = sigmaInt c ν chio M 1 1` (source 4859-4862). -/
theorem sigmaIntSymm (chio : ℝ → ℝ) : FlatUnif.G5.SigmaIntSymm chio := by
  intro c ν _hc _hν _hχ M _hM
  refine ⟨?_, ?_⟩
  · intro a b hab
    unfold sigmaInt
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · refine integral_eq_zero_of_odd XmtRefl.sigE_measurePreserving fun y => ?_
      simp [XmtRefl.sigmaM_sigE, XmtRefl.sg]
    · exact integral_eq_zero_of_odd negE_measurePreserving (sigmaM_negE_zero_two c ν chio M)
    · refine integral_eq_zero_of_odd XmtRefl.sigE_measurePreserving fun y => ?_
      simp [XmtRefl.sigmaM_sigE, XmtRefl.sg]
    · exact absurd rfl hab
    · refine integral_eq_zero_of_odd XmtRefl.sigE_measurePreserving fun y => ?_
      simp [XmtRefl.sigmaM_sigE, XmtRefl.sg]
    · exact integral_eq_zero_of_odd negE_measurePreserving (sigmaM_negE_two_zero c ν chio M)
    · refine integral_eq_zero_of_odd XmtRefl.sigE_measurePreserving fun y => ?_
      simp [XmtRefl.sigmaM_sigE, XmtRefl.sg]
    · exact absurd rfl hab
  · unfold sigmaInt
    rw [← swapE_measurePreserving.integral_comp' (fun y => sigmaM c ν chio M y 0 0)]
    congr 1
    funext y
    exact sigmaM_swapE_zero_zero c ν chio M y

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
