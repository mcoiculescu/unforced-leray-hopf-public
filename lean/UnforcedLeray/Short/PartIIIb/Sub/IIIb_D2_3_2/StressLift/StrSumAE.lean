import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs

/-!
# Exact multiplier identity for the stress sum, a.e. for `ageμ c (-1/2)` (source 4147, 2700, 3876-3877)

From `IsExactMultiplier`, the thin and repair components of `M w` agree a.e. with the chart tensors
`ten3Of (symOuter (chartCoeff R V p) (w p))` and `ten3Of (symOuter (chartCoeff R rb p) (w p))`
for the gain measures `gainZ1Measure` and `gainHTMeasure`. Both gain measures dominate
`ageμ c (-1/2)` through the density roots `root_z1`, `root_gainZ1`, `root_htRho`, `root_gainHT`,
so the equalities transfer to `ageμ c (-1/2)`. The sum of the two chart tensors is the chart tensor
of `V + rb`, by additivity of `chartCoeff`, bilinearity of `symOuter` and additivity of `ten3Of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem embedMerid_add (a b : Merid) : IIIa.embedMerid (a + b) = IIIa.embedMerid a + IIIa.embedMerid b := by
  funext i
  fin_cases i <;> simp [IIIa.embedMerid]

theorem symOuter_add_left (a b c : Merid) :
    IIIa.symOuter (a + b) c = IIIa.symOuter a c + IIIa.symOuter b c := by
  ext i j
  simp only [IIIa.symOuter, Matrix.add_apply, embedMerid_add, Pi.add_apply]
  ring

theorem chartCoeff_add_local (R : ℝ) (A B : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (pt : ℝ × (ℝ × ℝ)) :
    IIIa.chartCoeff R (fun t y => A t y + B t y) pt = IIIa.chartCoeff R A pt + IIIa.chartCoeff R B pt := by
  ext i
  fin_cases i <;> simp [IIIa.chartCoeff] <;> ring

theorem ten3Of_add (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    NearInst.ten3Of (M + N) = NearInst.ten3Of M + NearInst.ten3Of N := by
  ext ab
  simp [NearInst.ten3Of]

theorem strSumExactAE_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c)
    (hρb : 0 < ρb) (ε : ℝ) (V rb : ℝ → SpatialField) :
    StrSumExactAE B hc hρb ε V rb := by
  intro hM w
  -- absolute continuity of `ageμ c (-1/2)` with respect to the two gain measures
  have hac1 : ageμ c (-1 / 2) ≪ gainZ1Measure c mZ γ ν :=
    (NearInst.root_z1 c mZ).absCont.trans (NearInst.root_gainZ1 c mZ γ ν).absCont
  have hac2 : ageμ c (-1 / 2) ≪ gainHTMeasure c ρb γ ν :=
    (NearInst.root_htRho hρb).absCont.trans (NearInst.root_gainHT c ρb γ ν).absCont
  have h1 := hac1.ae_le (hM w).1
  have h2 := hac2.ae_le (hM w).2
  filter_upwards [h1, h2] with p hp1 hp2
  have hsum : IIIa.chartCoeff ε⁻¹ (fun τ y => V τ y + rb τ y) p =
      IIIa.chartCoeff ε⁻¹ V p + IIIa.chartCoeff ε⁻¹ rb p := by
    exact chartCoeff_add_local ε⁻¹ V rb p
  unfold strSum
  show ((B.M w).fst : Chart → Ten3) p + ((B.M w).snd : Chart → Ten3) p = _
  rw [hp1, hp2, hsum, symOuter_add_left, ten3Of_add]

end UnforcedLeray.Short.PartIIIb.Concrete
