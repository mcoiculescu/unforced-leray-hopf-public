import UnforcedLeray.Lib.TrainB.P0W1

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A representative-transparent isometry from the weighted W value carrier to centered-cell
L², built using identity measure preservation rather than an Lp type cast. -/
noncomputable def weightedToCellL2Isometry (c : ℝ) :
    Lp UnforcedLeray.Cyl.Vec2 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) →ₗᵢ[ℝ]
    UnforcedLeray.Cyl.L2v c := by
  let hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  exact Lp.compMeasurePreservingₗᵢ ℝ id hMP

/-- The H¹ value projection using the representative-transparent cell isometry. -/
noncomputable def vecH1ValueCellCLM_MP {c : ℝ} :
    VecH1 c →L[ℝ] UnforcedLeray.Cyl.L2v c :=
  (weightedToCellL2Isometry c).toContinuousLinearMap.comp
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ UnforcedLeray.Cyl.Vec2 1 2)

/-- The horizontal derivative projection using identity measure preservation. -/
noncomputable def vecH1DqCellCLM_MP {c : ℝ} :
    VecH1 c →L[ℝ] UnforcedLeray.Cyl.L2v c :=
  (weightedToCellL2Isometry c).toContinuousLinearMap.comp
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ UnforcedLeray.Cyl.Vec2 1 2 (Sob.Idx.cons 0 Sob.Idx.zero))

/-- The axial derivative projection using identity measure preservation. -/
noncomputable def vecH1DetaCellCLM_MP {c : ℝ} :
    VecH1 c →L[ℝ] UnforcedLeray.Cyl.L2v c :=
  (weightedToCellL2Isometry c).toContinuousLinearMap.comp
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ UnforcedLeray.Cyl.Vec2 1 2 (Sob.Idx.cons 1 Sob.Idx.zero))

/-- The centered-cell value class of a smooth representative is carried by the identity
measure-preserving map. This form exposes its representative through the Lp composition theorem. -/
theorem vecH1ValueCellCLM_MP_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2}
    (hu : Sob.IsCylSmooth c u) :
    vecH1ValueCellCLM_MP
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) =
      Lp.compMeasurePreserving id
        (show MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) from by
            rw [← vecH1_measure_eq_cell c]
            exact MeasurePreserving.id _)
        ((hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2).toLp u) := by
  let hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hvalue : Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ UnforcedLeray.Cyl.Vec2 1 2
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) =
      (hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2).toLp u := by
    apply Lp.ext
    filter_upwards [Sob.W.value_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu,
      (hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2).coeFn_toLp] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  change (Lp.compMeasurePreservingₗᵢ ℝ id hMP)
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
        ℝ UnforcedLeray.Cyl.Vec2 1 2
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu)) =
    Lp.compMeasurePreserving id hMP
      ((hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2).toLp u)
  rw [hvalue]
  rfl

/-- Pointwise representative of the transported smooth value projection on the centered cell. -/
theorem vecH1ValueCellCLM_MP_ofCylSmooth_ae {c : ℝ} (hc : 0 < c)
    {u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2}
    (hu : Sob.IsCylSmooth c u) :
    (vecH1ValueCellCLM_MP
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) :
      UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] u := by
  let hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  let hmW := hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hclass := vecH1ValueCellCLM_MP_ofCylSmooth hc hu
  have hmap := Lp.coeFn_compMeasurePreserving (hmW.toLp u) hMP
  have hcoe : (hmW.toLp u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] u := by
    rw [← vecH1_measure_eq_cell c]
    exact hmW.coeFn_toLp
  change (vecH1ValueCellCLM_MP
    (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) :
    UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] u
  rw [hclass]
  filter_upwards [hmap, hcoe] with z hz₁ hz₂
  simpa using hz₁.trans hz₂

/-- Every smooth W¹ weak derivative is represented after transport by its actual classical word
derivative on the centered cell. -/
theorem weightedToCellL2Isometry_deriv_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2}
    (hu : Sob.IsCylSmooth c u) (α : Sob.Idx 2 1) :
    weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
        ℝ UnforcedLeray.Cyl.Vec2 1 2 α
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu)) =
      Lp.compMeasurePreserving id
        (show MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) from by
            rw [← vecH1_measure_eq_cell c]
            exact MeasurePreserving.id _)
        (((hu.iterD ((Sob.cylinder c).word α)).memLp
          (Cyl.ρwW c ^ (0 : ℝ)) 2).toLp (Sob.iterD ((Sob.cylinder c).word α) u)) := by
  let hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  let hd := (hu.iterD ((Sob.cylinder c).word α)).memLp
    (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hderiv : Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ UnforcedLeray.Cyl.Vec2 1 2 α
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) =
      hd.toLp (Sob.iterD ((Sob.cylinder c).word α) u) := by
    apply Lp.ext
    filter_upwards [Sob.W.deriv_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu α,
      hd.coeFn_toLp] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  change Lp.compMeasurePreserving id hMP
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ UnforcedLeray.Cyl.Vec2 1 2 α
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu)) = _
  rw [hderiv]

/-- The transported horizontal weak derivative of a smooth W¹ class is its actual classical
horizontal derivative on the centered cell. -/
theorem vecH1DqCellCLM_MP_ofCylSmooth_ae {c : ℝ} (hc : 0 < c)
    {u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2}
    (hu : Sob.IsCylSmooth c u) :
    (vecH1DqCellCLM_MP
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) :
      UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      Cyl.partialQ u := by
  let hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  let α : Sob.Idx 2 1 := Sob.Idx.cons 0 Sob.Idx.zero
  let v := Sob.iterD ((Sob.cylinder c).word α) u
  let hmW := (hu.iterD ((Sob.cylinder c).word α)).memLp
    (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hclass := weightedToCellL2Isometry_deriv_ofCylSmooth hc hu α
  have hmap := Lp.coeFn_compMeasurePreserving (hmW.toLp v) hMP
  have hcoe : (hmW.toLp v : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] v := by
    rw [← vecH1_measure_eq_cell c]
    exact hmW.coeFn_toLp
  have hword : v = Cyl.partialQ u := by
    have hdirections : (Sob.cylinder c).word α = [(1, 0)] := by
      simp [α, Sob.TestDomain.word_cons, Sob.TestDomain.word_zero, Sob.cylinder, Sob.cylDir]
    change Sob.iterD ((Sob.cylinder c).word α) u = Cyl.partialQ u
    rw [hdirections]
    funext z
    simp only [Sob.iterD, List.foldr_cons, List.foldr_nil]
    exact (Cyl.partialQ_eq_fderiv (hu.smooth.differentiable (by simp)) z).symm
  change (vecH1DqCellCLM_MP
    (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) :
    UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c]
    Cyl.partialQ u
  change (weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ
        UnforcedLeray.Cyl.Vec2 1 2 α
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu)) :
      UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] _
  rw [hclass]
  filter_upwards [hmap, hcoe] with z hz₁ hz₂
  rw [Function.comp_apply, id_eq] at hz₁
  exact hz₁.trans (hz₂.trans (congrFun hword z))

/-- The transported axial weak derivative of a smooth W¹ class is its actual classical
axial derivative on the centered cell. -/
theorem vecH1DetaCellCLM_MP_ofCylSmooth_ae {c : ℝ} (hc : 0 < c)
    {u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2}
    (hu : Sob.IsCylSmooth c u) :
    (vecH1DetaCellCLM_MP
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) :
      UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      Cyl.partialEta u := by
  let hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  let α : Sob.Idx 2 1 := Sob.Idx.cons 1 Sob.Idx.zero
  let v := Sob.iterD ((Sob.cylinder c).word α) u
  let hmW := (hu.iterD ((Sob.cylinder c).word α)).memLp
    (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hclass := weightedToCellL2Isometry_deriv_ofCylSmooth hc hu α
  have hmap := Lp.coeFn_compMeasurePreserving (hmW.toLp v) hMP
  have hcoe : (hmW.toLp v : UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] v := by
    rw [← vecH1_measure_eq_cell c]
    exact hmW.coeFn_toLp
  have hword : v = Cyl.partialEta u := by
    have hdirections : (Sob.cylinder c).word α = [(0, 1)] := by
      simp [α, Sob.TestDomain.word_cons, Sob.TestDomain.word_zero, Sob.cylinder, Sob.cylDir]
    change Sob.iterD ((Sob.cylinder c).word α) u = Cyl.partialEta u
    rw [hdirections]
    funext z
    simp only [Sob.iterD, List.foldr_cons, List.foldr_nil]
    exact (Cyl.partialEta_eq_fderiv (hu.smooth.differentiable (by simp)) z).symm
  change (vecH1DetaCellCLM_MP
    (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu) :
    UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c]
    Cyl.partialEta u
  change (weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ
        UnforcedLeray.Cyl.Vec2 1 2 α
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := UnforcedLeray.Cyl.Vec2) (k := 1) (p := 2) hc u hu)) :
      UnforcedLeray.Cyl.Plane → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] _
  rw [hclass]
  filter_upwards [hmap, hcoe] with z hz₁ hz₂
  rw [Function.comp_apply, id_eq] at hz₁
  exact hz₁.trans (hz₂.trans (congrFun hword z))

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.weightedToCellL2Isometry
#print axioms UnforcedLeray.TrainB.vecH1ValueCellCLM_MP
#print axioms UnforcedLeray.TrainB.vecH1DqCellCLM_MP
#print axioms UnforcedLeray.TrainB.vecH1DetaCellCLM_MP
#print axioms UnforcedLeray.TrainB.vecH1ValueCellCLM_MP_ofCylSmooth
#print axioms UnforcedLeray.TrainB.vecH1ValueCellCLM_MP_ofCylSmooth_ae
#print axioms UnforcedLeray.TrainB.weightedToCellL2Isometry_deriv_ofCylSmooth
#print axioms UnforcedLeray.TrainB.vecH1DqCellCLM_MP_ofCylSmooth_ae
#print axioms UnforcedLeray.TrainB.vecH1DetaCellCLM_MP_ofCylSmooth_ae
