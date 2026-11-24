import UnforcedLeray.Lib.TrainB.P0H1Projection

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The centered-cell L² class of a classical cylinder derivative word. -/
private noncomputable def smoothWordCell {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (vs : List Plane) : L2v c := by
  let hm := (hu.iterD vs).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  let hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  exact Lp.compMeasurePreserving id hMP (hm.toLp (Sob.iterD vs u))

private theorem smoothWordCell_ae {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    (smoothWordCell u hu vs : Plane → Vec2) =ᵐ[cellμ c] Sob.iterD vs u := by
  let hm := (hu.iterD vs).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hm.toLp (Sob.iterD vs u)) hMP
  have hcoe : (hm.toLp (Sob.iterD vs u) : Plane → Vec2) =ᵐ[cellμ c] Sob.iterD vs u := by
    exact hMP.quasiMeasurePreserving.ae hm.coeFn_toLp
  filter_upwards [hcomp, hcoe] with z hz₁ hz₂
  change ((Lp.compMeasurePreserving id hMP (hm.toLp (Sob.iterD vs u)) : L2v c) : Plane → Vec2) z = _
  simpa [smoothWordCell, Function.comp_id] using hz₁.trans hz₂

private theorem smoothWordCell_memLp {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    MemLp (smoothWordCell u hu vs : Plane → Vec2) 2 (cellμ c) := by
  exact Lp.memLp (smoothWordCell u hu vs)

private theorem weightedToCell_of_toLp_local {c : ℝ} (u : L2v c)
    {F : Plane → Vec2} (hF : MemLp F 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))
    (hFae : (u : Plane → Vec2) =ᵐ[cellμ c] F) :
    weightedToCellL2Isometry c (hF.toLp F) = u := by
  apply Lp.ext
  let hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hF.toLp F) hMP
  have hFcell := hMP.quasiMeasurePreserving.ae hF.coeFn_toLp
  filter_upwards [hcomp, hFcell, hFae] with z hzComp hzF hzU
  calc
    ((Lp.compMeasurePreserving id hMP (hF.toLp F) : L2v c) : Plane → Vec2) z =
        (hF.toLp F : Lp Vec2 2
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
            simpa [Function.comp_id] using hzComp
    _ = F z := hzF
    _ = (u : Plane → Vec2) z := hzU.symm

/-- Centered-cell realization of one ordered derivative of an H³ cylinder field. -/
noncomputable def vecH3CellDerivCLM {c : ℝ} (α : Sob.Idx 2 3) :
    Cyl.H ℝ Vec2 c 0 3 →L[ℝ] L2v c :=
  (weightedToCellL2Isometry c).toContinuousLinearMap.comp
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
      ℝ Vec2 3 2 α)

/-- The single-step projected derivative of a smooth classical word, using the H¹ projection
theorem for the suffix word. -/
private theorem projectedSmoothQSingleton {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) (vs : List Plane)
    :
    Sob.HasWeakDeriv (Sob.cylinder c) [((1 : ℝ), (0 : ℝ))]
      (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2)
      (Cyl.P0 c (smoothWordCell u hu ((1, 0) :: vs)) : Plane → Vec2) := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (Sob.iterD vs u) (hu.iterD vs)
  have hval : vecH1ValueCellCLM_MP x = smoothWordCell u hu vs := by
    apply Lp.ext
    have h := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCell_ae u hu vs
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have hq : vecH1DqCellCLM_MP x = smoothWordCell u hu ((1, 0) :: vs) := by
    apply Lp.ext
    have h := vecH1DqCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCell_ae u hu ((1, 0) :: vs)
    have hword : Cyl.partialQ (Sob.iterD vs u) = Sob.iterD ((1, 0) :: vs) u := by
      funext z
      simp only [Sob.iterD_cons]
      exact (Cyl.partialQ_eq_fderiv ((hu.iterD vs).smooth.differentiable (by simp)) z)
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans ((congrFun hword z).trans hz₂.symm)
  have hw := hasWeakDeriv_P0_q_of_vecH1 hc x
  have hsource : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2) := by
    rw [hval]
  have htarget : (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCell u hu ((1, 0) :: vs)) : Plane → Vec2) := by
    rw [hq]
  have hcell : MeasurePreserving id (Sob.cylinder c).μ (cellμ c) := by
    rw [Cyl.cylinder_μ_eq]
    exact MeasurePreserving.id _
  have hsource' : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2) := by
    exact hcell.quasiMeasurePreserving.ae hsource
  have htarget' : (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCell u hu ((1, 0) :: vs)) : Plane → Vec2) := by
    exact hcell.quasiMeasurePreserving.ae htarget
  exact hw.congr_ae hsource' htarget'

private theorem projectedSmoothEtaSingleton {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((0 : ℝ), (1 : ℝ))]
      (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2)
      (Cyl.P0 c (smoothWordCell u hu ((0, 1) :: vs)) : Plane → Vec2) := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (Sob.iterD vs u) (hu.iterD vs)
  have hval : vecH1ValueCellCLM_MP x = smoothWordCell u hu vs := by
    apply Lp.ext
    have h := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCell_ae u hu vs
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have he : vecH1DetaCellCLM_MP x = smoothWordCell u hu ((0, 1) :: vs) := by
    apply Lp.ext
    have h := vecH1DetaCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCell_ae u hu ((0, 1) :: vs)
    have hword : Cyl.partialEta (Sob.iterD vs u) = Sob.iterD ((0, 1) :: vs) u := by
      funext z
      simp only [Sob.iterD_cons]
      exact (Cyl.partialEta_eq_fderiv ((hu.iterD vs).smooth.differentiable (by simp)) z)
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans ((congrFun hword z).trans hz₂.symm)
  have hw := hasWeakDeriv_P0_eta_of_vecH1 hc x
  have hsource : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2) := by rw [hval]
  have htarget : (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCell u hu ((0, 1) :: vs)) : Plane → Vec2) := by rw [he]
  have hcell : MeasurePreserving id (Sob.cylinder c).μ (cellμ c) := by
    rw [Cyl.cylinder_μ_eq]
    exact MeasurePreserving.id _
  have hsource' : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2) :=
    hcell.quasiMeasurePreserving.ae hsource
  have htarget' : (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCell u hu ((0, 1) :: vs)) : Plane → Vec2) :=
    hcell.quasiMeasurePreserving.ae htarget
  exact hw.congr_ae hsource' htarget'

private theorem projectedSmoothWordWeak {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) :
    ∀ vs : List Plane,
      (∀ v ∈ vs, v = (1, 0) ∨ v = (0, 1)) →
      Sob.HasWeakDeriv (Sob.cylinder c) vs
        (Cyl.P0 c (smoothWordCell u hu []) : Plane → Vec2)
        (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2) := by
  intro vs
  induction vs with
  | nil =>
      intro _
      apply Sob.HasWeakDeriv.nil
      intro φ hφ
      exact Sob.integrable_smul_of_memLp (p := 2) (Sob.CompactlyBounded.of_adm hφ)
        (memLp_cell_to_weighted (Cyl.P0 c (smoothWordCell u hu [])))
  | cons v vs ih =>
      intro hvs
      have hv := hvs v (by simp)
      have hrest : ∀ w ∈ vs, w = (1, 0) ∨ w = (0, 1) := by
        intro w hw
        exact hvs w (by simp [hw])
      have htail := ih hrest
      have hsingle : Sob.HasWeakDeriv (Sob.cylinder c) [v]
          (Cyl.P0 c (smoothWordCell u hu vs) : Plane → Vec2)
          (Cyl.P0 c (smoothWordCell u hu (v :: vs)) : Plane → Vec2) := by
        rcases hv with hq | he
        · rw [hq]
          simpa using projectedSmoothQSingleton hc u hu vs
        · rw [he]
          simpa using projectedSmoothEtaSingleton hc u hu vs
      exact htail.cons hsingle

private noncomputable def projectedSmoothWord {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (α : Sob.Idx 2 3) : L2v c :=
  Cyl.P0 c (smoothWordCell u hu ((Sob.cylinder c).word α))

private theorem projectedSmoothWord_memLp_weighted {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (α : Sob.Idx 2 3) :
    MemLp (projectedSmoothWord u hu α : Plane → Vec2) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
  memLp_cell_to_weighted (projectedSmoothWord u hu α)

/-- P₀ of a smooth periodic field belongs to the actual unweighted H³ graph, with every ordered
derivative represented by P₀ of the corresponding classical derivative. -/
theorem exists_projectedSmoothVecH3 {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) :
    ∃ y : Cyl.H ℝ Vec2 c 0 3,
      (∀ α : Sob.Idx 2 3,
        vecH3CellDerivCLM α y = Cyl.P0 c (vecH3CellDerivCLM α
          (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
            (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) hc u hu))) ∧
      ‖y‖ ≤ ‖Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) hc u hu‖ := by
  let g : Sob.Idx 2 3 → Plane → Vec2 := fun α z => (projectedSmoothWord u hu α : Plane → Vec2) z
  have hmem : ∀ α, MemLp (g α) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    exact projectedSmoothWord_memLp_weighted u hu α
  have hdirs (α : Sob.Idx 2 3) : ∀ v ∈ (Sob.cylinder c).word α,
      v = (1, 0) ∨ v = (0, 1) := by
    intro v hv
    simp only [Sob.TestDomain.word, List.mem_ofFn] at hv
    rcases hv with ⟨i, hi⟩
    generalize hidx : α.2 i = j at hi
    change Sob.cylDir j = v at hi
    fin_cases j
    · left
      simpa [Sob.cylDir] using hi.symm
    · right
      simpa [Sob.cylDir] using hi.symm
  have hweak : ∀ α : Sob.Idx 2 3,
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
        (g Sob.Idx.zero) (g α) := by
    intro α
    have h := projectedSmoothWordWeak hc u hu ((Sob.cylinder c).word α) (hdirs α)
    simpa [g, projectedSmoothWord, Sob.TestDomain.word_zero] using h
  let y : Cyl.H ℝ Vec2 c 0 3 := Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := 3) (p := 2) g hmem hweak
  have hcomponent (α : Sob.Idx 2 3) :
      weightedToCellL2Isometry c
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α y) =
        projectedSmoothWord u hu α := by
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp_local (projectedSmoothWord u hu α) (hmem α)
      (ae_of_all _ fun z => rfl)
  let x : Cyl.H ℝ Vec2 c 0 3 := Sob.W.ofCylSmooth
    (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) hc u hu
  have hinput (α : Sob.Idx 2 3) :
      weightedToCellL2Isometry c
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α x) =
        smoothWordCell u hu ((Sob.cylinder c).word α) := by
    let hm := (hu.iterD ((Sob.cylinder c).word α)).memLp
      (Cyl.ρwW c ^ (0 : ℝ)) 2
    have hderiv : Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
        ℝ Vec2 3 2 α x = hm.toLp (Sob.iterD ((Sob.cylinder c).word α) u) := by
      apply Lp.ext
      filter_upwards [Sob.W.deriv_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) hc u hu α,
        hm.coeFn_toLp] with z hz₁ hz₂
      exact hz₁.trans hz₂.symm
    rw [hderiv]
    rfl
  have hP0 (z : L2v c) : ‖Cyl.P0 c z‖ ≤ ‖z‖ := by
    calc
      ‖Cyl.P0 c z‖ ≤ ‖Cyl.P0 c‖ * ‖z‖ := (Cyl.P0 c).le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right Cyl.norm_P0_le (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  have hnormSq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [Sob.W.norm_sq, Sob.W.norm_sq]
    apply Finset.sum_le_sum
    intro α _
    rw [← (weightedToCellL2Isometry c).norm_map
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α y),
      ← (weightedToCellL2Isometry c).norm_map
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α x),
      hcomponent, hinput]
    have hle := hP0 (smoothWordCell u hu ((Sob.cylinder c).word α))
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hle
  refine ⟨y, ?_, ?_⟩
  · intro α
    change weightedToCellL2Isometry c
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α y) =
      Cyl.P0 c (weightedToCellL2Isometry c
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α x))
    rw [hcomponent α, hinput α]
    rfl
  · exact (sq_le_sq₀ (norm_nonneg y) (norm_nonneg x)).mp hnormSq

#print axioms UnforcedLeray.TrainB.exists_projectedSmoothVecH3

end UnforcedLeray.TrainB
