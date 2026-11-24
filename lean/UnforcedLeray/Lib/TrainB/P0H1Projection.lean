import UnforcedLeray.Lib.TrainB.P0WeakProjection

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A centered-cell L² class is also in the order-zero cylinder Sobolev measure. -/
theorem memLp_cell_to_weighted {c : ℝ} (u : L2v c) :
    MemLp (u : Plane → Vec2) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
  let hMP : MeasurePreserving id
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) (cellμ c) := by
    rw [vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  let v : Lp Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    Lp.compMeasurePreserving id hMP u
  have hv : MemLp (v : Plane → Vec2) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := Lp.memLp v
  have hae : (v : Plane → Vec2) =ᵐ[Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))]
      (u : Plane → Vec2) := by
    simpa [v, Function.comp_id] using Lp.coeFn_compMeasurePreserving u hMP
  exact MemLp.ae_eq hae hv

private noncomputable def projectedH1Component {c : ℝ} (x : VecH1 c)
    (α : Sob.Idx 2 1) : L2v c :=
  if α = (Sob.Idx.zero : Sob.Idx 2 1) then
    Cyl.P0 c (vecH1ValueCellCLM_MP x)
  else if α = (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) then
    Cyl.P0 c (vecH1DqCellCLM_MP x)
  else
    Cyl.P0 c (vecH1DetaCellCLM_MP x)

private theorem weightedToCell_of_toLp {c : ℝ} (u : L2v c)
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

/-- `P₀` maps the actual H¹ cylinder graph to itself and commutes with both first derivatives. -/
theorem exists_projectedVecH1 {c : ℝ} (hc : 0 < c) (x : VecH1 c) :
    ∃ y : VecH1 c,
      vecH1ValueCellCLM_MP y = Cyl.P0 c (vecH1ValueCellCLM_MP x) ∧
      vecH1DqCellCLM_MP y = Cyl.P0 c (vecH1DqCellCLM_MP x) ∧
      vecH1DetaCellCLM_MP y = Cyl.P0 c (vecH1DetaCellCLM_MP x) := by
  let component : Sob.Idx 2 1 → L2v c := projectedH1Component x
  let g : Sob.Idx 2 1 → Plane → Vec2 := fun α z => (component α : Plane → Vec2) z
  have hmem : ∀ α, MemLp (g α) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    exact memLp_cell_to_weighted (component α)
  have hcomponent0 : component Sob.Idx.zero =
      Cyl.P0 c (vecH1ValueCellCLM_MP x) := by
    simp [component, projectedH1Component]
  have hcomponentQ : component (Sob.Idx.cons 0 Sob.Idx.zero) =
      Cyl.P0 c (vecH1DqCellCLM_MP x) := by
    simp only [component, projectedH1Component]
    have hne : (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.zero := by
      intro h
      exact Cyl.idx_ne.1 h.symm
    simp [hne]
  have hcomponentEta : component (Sob.Idx.cons 1 Sob.Idx.zero) =
      Cyl.P0 c (vecH1DetaCellCLM_MP x) := by
    simp only [component, projectedH1Component]
    have hne0 : (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.zero := by
      intro h
      exact Cyl.idx_ne.2.1 h.symm
    have hneq : (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) ≠
        Sob.Idx.cons 0 Sob.Idx.zero := by
      intro h
      exact Cyl.idx_ne.2.2 h.symm
    simp [hne0, hneq]
  have hweak : ∀ α : Sob.Idx 2 1,
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
        (g Sob.Idx.zero) (g α) := by
    intro α
    have hcases : α = (Sob.Idx.zero : Sob.Idx 2 1) ∨
        α = Cyl.iQ ∨ α = Cyl.iEta := by
      have hm : α ∈ (Finset.univ : Finset (Sob.Idx 2 1)) := Finset.mem_univ α
      rw [Cyl.univ_idx_two_one] at hm
      simpa [Cyl.iQ, Cyl.iEta] using hm
    rcases hcases with hzero | hq | heta
    · subst α
      rw [Cyl.word_zero]
      apply Sob.HasWeakDeriv.nil
      intro φ hφ
      exact Sob.integrable_smul_of_memLp (p := 2)
        (Sob.CompactlyBounded.of_adm hφ) (hmem Sob.Idx.zero)
    · subst α
      rw [Cyl.word_iQ]
      have hsource : g Sob.Idx.zero =
          (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) := by
        funext z
        exact congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponent0) z
      have htarget : g Cyl.iQ =
          (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) := by
        funext z
        exact congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentQ) z
      exact (hasWeakDeriv_P0_q_of_vecH1 hc x).congr_ae
        (ae_of_all _ fun z => (congrFun hsource z).symm)
        (ae_of_all _ fun z => (congrFun htarget z).symm)
    · subst α
      rw [Cyl.word_iEta]
      have hsource : g Sob.Idx.zero =
          (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) := by
        funext z
        exact congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponent0) z
      have htarget : g Cyl.iEta =
          (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) := by
        funext z
        exact congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentEta) z
      exact (hasWeakDeriv_P0_eta_of_vecH1 hc x).congr_ae
        (ae_of_all _ fun z => (congrFun hsource z).symm)
        (ae_of_all _ fun z => (congrFun htarget z).symm)
  let y : VecH1 c := Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := 1) (p := 2) g hmem hweak
  have hzero : (g Sob.Idx.zero : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) := by
    have heq := congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponent0
    filter_upwards with z
    exact congrFun heq z
  have hq : (g (Sob.Idx.cons 0 Sob.Idx.zero) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) := by
    have heq := congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentQ
    filter_upwards with z
    exact congrFun heq z
  have heta : (g (Sob.Idx.cons 1 Sob.Idx.zero) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) := by
    have heq := congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentEta
    filter_upwards with z
    exact congrFun heq z
  have hval : vecH1ValueCellCLM_MP y = Cyl.P0 c (vecH1ValueCellCLM_MP x) := by
    change weightedToCellL2Isometry c
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 y) = _
    rw [Sob.W.value_ofFields]
    exact weightedToCell_of_toLp _ (hmem Sob.Idx.zero) hzero
  have hqval : vecH1DqCellCLM_MP y = Cyl.P0 c (vecH1DqCellCLM_MP x) := by
    change weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
        (Sob.Idx.cons 0 Sob.Idx.zero) y) = _
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp _ (hmem (Sob.Idx.cons 0 Sob.Idx.zero)) hq
  have hetaval : vecH1DetaCellCLM_MP y = Cyl.P0 c (vecH1DetaCellCLM_MP x) := by
    change weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
        (Sob.Idx.cons 1 Sob.Idx.zero) y) = _
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp _ (hmem (Sob.Idx.cons 1 Sob.Idx.zero)) heta
  exact ⟨y, hval, hqval, hetaval⟩

/-- The H¹ graph projection has contraction constant one, independent of the period. -/
theorem exists_projectedVecH1_contractive {c : ℝ} (hc : 0 < c) (x : VecH1 c) :
    ∃ y : VecH1 c,
      vecH1ValueCellCLM_MP y = Cyl.P0 c (vecH1ValueCellCLM_MP x) ∧
      vecH1DqCellCLM_MP y = Cyl.P0 c (vecH1DqCellCLM_MP x) ∧
      vecH1DetaCellCLM_MP y = Cyl.P0 c (vecH1DetaCellCLM_MP x) ∧
      ‖y‖ ≤ ‖x‖ := by
  obtain ⟨y, hy0, hyq, hye⟩ := exists_projectedVecH1 hc x
  have hP0 (u : L2v c) : ‖Cyl.P0 c u‖ ≤ ‖u‖ := by
    calc
      ‖Cyl.P0 c u‖ ≤ ‖Cyl.P0 c‖ * ‖u‖ := (Cyl.P0 c).le_opNorm u
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right Cyl.norm_P0_le (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  have h0 := (sq_le_sq₀ (norm_nonneg (Cyl.P0 c (vecH1ValueCellCLM_MP x)))
    (norm_nonneg (vecH1ValueCellCLM_MP x))).mpr (hP0 _)
  have hq := (sq_le_sq₀ (norm_nonneg (Cyl.P0 c (vecH1DqCellCLM_MP x)))
    (norm_nonneg (vecH1DqCellCLM_MP x))).mpr (hP0 _)
  have he := (sq_le_sq₀ (norm_nonneg (Cyl.P0 c (vecH1DetaCellCLM_MP x)))
    (norm_nonneg (vecH1DetaCellCLM_MP x))).mpr (hP0 _)
  have hnormV (z : VecH1 c) : ‖Cyl.H.val z‖ = ‖vecH1ValueCellCLM_MP z‖ := by
    change ‖Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 z‖ =
      ‖weightedToCellL2Isometry c
        (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 z)‖
    exact ((weightedToCellL2Isometry c).norm_map _).symm
  have hnormQ (z : VecH1 c) :
      ‖Cyl.H.der (Cyl.iQ (k := 0)) z‖ = ‖vecH1DqCellCLM_MP z‖ := by
    change ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
        (Sob.Idx.cons 0 Sob.Idx.zero) z‖ =
      ‖weightedToCellL2Isometry c
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
          (Sob.Idx.cons 0 Sob.Idx.zero) z)‖
    exact ((weightedToCellL2Isometry c).norm_map _).symm
  have hnormEta (z : VecH1 c) :
      ‖Cyl.H.der (Cyl.iEta (k := 0)) z‖ = ‖vecH1DetaCellCLM_MP z‖ := by
    change ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
        (Sob.Idx.cons 1 Sob.Idx.zero) z‖ =
      ‖weightedToCellL2Isometry c
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
          (Sob.Idx.cons 1 Sob.Idx.zero) z)‖
    exact ((weightedToCellL2Isometry c).norm_map _).symm
  have hnormSq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [Cyl.H.norm_sq_one y, Cyl.H.norm_sq_one x,
      hnormV y, hnormQ y, hnormEta y,
      hnormV x, hnormQ x, hnormEta x, hy0, hyq, hye]
    nlinarith
  refine ⟨y, hy0, hyq, hye, ?_⟩
  exact (sq_le_sq₀ (norm_nonneg y) (norm_nonneg x)).mp hnormSq

#print axioms UnforcedLeray.TrainB.memLp_cell_to_weighted
#print axioms UnforcedLeray.TrainB.exists_projectedVecH1
#print axioms UnforcedLeray.TrainB.exists_projectedVecH1_contractive

end UnforcedLeray.TrainB
