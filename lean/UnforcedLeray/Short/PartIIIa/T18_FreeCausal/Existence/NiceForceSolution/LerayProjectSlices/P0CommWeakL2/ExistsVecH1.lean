import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2_10
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.TestBridge

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/2/10/1`: packaging `L²` fields with `L²` weak derivatives

Target: `ExistsVecH1OfWeak` (`Sub/T18_2_4_2_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 3442-3465.

Proof: the three fields are glued into an element of `Sob.W` of order one with
`Sob.W.ofFields` on the three multi-indices `zero`, `iQ`, `iEta`
(`Cyl.univ_idx_two_one`), exactly as in `TrainB.exists_projectedVecH1`. The weak-derivative
clauses are the hypotheses. Values and derivatives are transported to the centred cell by
`TrainB.weightedToCellL2Isometry`, whose measure is `Cyl.cellμ c`
(`TrainB.vecH1_measure_eq_cell`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A cell class which agrees a.e. with the value of an `L²` isometry image is its preimage. -/
private theorem weightedToCell_of_toLp' {c : ℝ} (u : Cyl.L2v c)
    {F : ℝ × ℝ → Cyl.Vec2}
    (hF : MemLp F 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))
    (hFae : (u : ℝ × ℝ → Cyl.Vec2) =ᵐ[Cyl.cellμ c] F) :
    TrainB.weightedToCellL2Isometry c (hF.toLp F) = u := by
  apply Lp.ext
  let hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← TrainB.vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hF.toLp F) hMP
  have hFcell := hMP.quasiMeasurePreserving.ae hF.coeFn_toLp
  filter_upwards [hcomp, hFcell, hFae] with z hzComp hzF hzU
  calc
    ((Lp.compMeasurePreserving id hMP (hF.toLp F) : Cyl.L2v c) : Cyl.Plane → Cyl.Vec2) z =
        (hF.toLp F : Lp Cyl.Vec2 2
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
            simpa [Function.comp_id] using hzComp
    _ = F z := hzF
    _ = (u : ℝ × ℝ → Cyl.Vec2) z := hzU.symm

theorem existsVecH1OfWeak : ExistsVecH1OfWeak := by
  intro c hc f w hw
  let g : Sob.Idx 2 1 → ℝ × ℝ → Cyl.Vec2 := fun α =>
    if α = (Sob.Idx.zero : Sob.Idx 2 1) then (f : ℝ × ℝ → Cyl.Vec2)
    else if α = Cyl.iQ then (w 0 : ℝ × ℝ → Cyl.Vec2)
    else (w 1 : ℝ × ℝ → Cyl.Vec2)
  have hmem : ∀ α, MemLp (g α) 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    rw [TrainB.vecH1_measure_eq_cell c]
    dsimp only [g]
    split_ifs
    · exact Lp.memLp f
    · exact Lp.memLp (w 0)
    · exact Lp.memLp (w 1)
  have hg0 : g (Sob.Idx.zero : Sob.Idx 2 1) = (f : ℝ × ℝ → Cyl.Vec2) := by
    simp [g]
  have hne1 : (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.zero :=
    fun h => Cyl.idx_ne.1 h.symm
  have hne3 : (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.zero :=
    fun h => Cyl.idx_ne.2.1 h.symm
  have hne4 : (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) ≠ Cyl.iQ :=
    fun h => Cyl.idx_ne.2.2 h.symm
  have hne2 : (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) = Cyl.iQ := rfl
  have hgQ : g (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) = (w 0 : ℝ × ℝ → Cyl.Vec2) := by
    have hne1' : (Cyl.iQ : Sob.Idx 2 1) ≠ Sob.Idx.zero := hne2 ▸ hne1
    simp [g, hne1', hne2]
  have hgE : g (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) = (w 1 : ℝ × ℝ → Cyl.Vec2) := by
    simp [g, hne3, hne4]
  have hgQ' : g (Cyl.iQ : Sob.Idx 2 1) = (w 0 : ℝ × ℝ → Cyl.Vec2) := hgQ
  have hgE' : g (Cyl.iEta : Sob.Idx 2 1) = (w 1 : ℝ × ℝ → Cyl.Vec2) := hgE
  have hweak : ∀ α : Sob.Idx 2 1,
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α) (g Sob.Idx.zero) (g α) := by
    intro α
    have hcases : α = (Sob.Idx.zero : Sob.Idx 2 1) ∨ α = Cyl.iQ ∨ α = Cyl.iEta := by
      have hm : α ∈ (Finset.univ : Finset (Sob.Idx 2 1)) := Finset.mem_univ α
      rw [Cyl.univ_idx_two_one] at hm
      simpa [Cyl.iQ, Cyl.iEta] using hm
    rcases hcases with hzero | hq | heta
    · subst hzero
      rw [Cyl.word_zero]
      apply Sob.HasWeakDeriv.nil
      intro φ hφ
      exact Sob.integrable_smul_of_memLp (p := 2)
        (Sob.CompactlyBounded.of_adm hφ) (hmem Sob.Idx.zero)
    · subst hq
      rw [Cyl.word_iQ c, hg0, hgQ']
      exact hw 0
    · subst heta
      rw [Cyl.word_iEta c, hg0, hgE']
      exact hw 1
  let y : TrainB.VecH1 c := Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
    (k := 1) (p := 2) g hmem hweak
  have hval : TrainB.vecH1ValueCellCLM_MP y = f := by
    change TrainB.weightedToCellL2Isometry c
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 1 2 y) = f
    rw [Sob.W.value_ofFields]
    exact weightedToCell_of_toLp' f (hmem Sob.Idx.zero)
      (ae_of_all _ fun z => (congrFun hg0 z).symm)
  have hqval : TrainB.vecH1DqCellCLM_MP y = w 0 := by
    change TrainB.weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 1 2
        (Sob.Idx.cons 0 Sob.Idx.zero) y) = w 0
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp' (w 0) (hmem (Sob.Idx.cons 0 Sob.Idx.zero))
      (ae_of_all _ fun z => (congrFun hgQ z).symm)
  have hetaval : TrainB.vecH1DetaCellCLM_MP y = w 1 := by
    change TrainB.weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 1 2
        (Sob.Idx.cons 1 Sob.Idx.zero) y) = w 1
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp' (w 1) (hmem (Sob.Idx.cons 1 Sob.Idx.zero))
      (ae_of_all _ fun z => (congrFun hgE z).symm)
  exact ⟨y, hval, hqval, hetaval⟩

end UnforcedLeray.Short.IIIa
