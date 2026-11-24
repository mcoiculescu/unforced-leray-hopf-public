import UnforcedLeray.Lib.TrainB.InitialDatumH3Graph
import UnforcedLeray.Lib.TrainB.P0RoughH3
import UnforcedLeray.Units.B0141.Datum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The classical fields used as the ordered components of the datum's H³ graph. -/
def datumH3Field {c : ℝ} (α : Sob.Idx 2 3) : Plane → Vec2 :=
  Sob.iterD ((Sob.cylinder c).word α) (Train.datum c)

private theorem datumH3_measure_eq_cell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW c (0 : ℝ), Cyl.wμ]
  simp [Cyl.ρw]

theorem datumH3Field_memLp {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) :
    MemLp (datumH3Field (c := c) α) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [datumH3_measure_eq_cell]
  exact memLp_datum_word_derivative hc α

theorem datumH3Field_hasWeakDeriv {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) :
    Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
      (datumH3Field (c := c) Sob.Idx.zero) (datumH3Field (c := c) α) := by
  simpa only [datumH3Field, Sob.TestDomain.word_zero, Sob.iterD_nil] using
    hasWeakDeriv_cylinder_word_of_smooth_periodic hc
      (Train.datum_contDiff hc.ne') (Train.datum_periodic c)
      ((Sob.cylinder c).word α)

/-- The actual periodized Gaussian Train datum belongs to the centered unweighted cylinder H³
space. Its graph components are its genuine classical derivatives, with weak-derivative
identities supplied by compactly supported cylinder tests. -/
noncomputable def datumVecH3 {c : ℝ} (hc : 0 < c) : VecH3 c :=
  Sob.W.ofFields (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) (datumH3Field (c := c))
    (datumH3Field_memLp hc) (datumH3Field_hasWeakDeriv hc)

theorem datumVecH3_value_ae {c : ℝ} (hc : 0 < c) :
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2
      (datumVecH3 hc) : Plane → Vec2) =ᵐ[Cyl.cellμ c] Train.datum c := by
  unfold datumVecH3
  rw [Sob.W.value_ofFields]
  rw [← datumH3_measure_eq_cell c]
  have h0 : datumH3Field (c := c) Sob.Idx.zero = Train.datum c := by
    simp [datumH3Field, Sob.TestDomain.word_zero, Sob.iterD]
  simpa only [h0] using
    (datumH3Field_memLp hc Sob.Idx.zero).coeFn_toLp

#print axioms UnforcedLeray.TrainB.datumVecH3
#print axioms UnforcedLeray.TrainB.datumVecH3_value_ae

end UnforcedLeray.TrainB
