import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap.Lift
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap.Lin

/-!
# Part II-b, task `PartII-b:G4/3/3` (`InletLapPtw`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1651-1658
(`A_ε = -S + ν s[(Q_ε² + ∂_η²)I - ε²E]`), 1919-1921, 2367-2369
(`L_ε = Δ - 2ε(K+1)∂_q + ε²[(K+1)² - diag(1,0)]`).

The only leaf is the off-axis chart identity `νΔ(N_v b) = N_v(lapProf ...)` for a smooth complex
profile `b` (`InletLapGen`: the off-axis branch of `lapPtwise_of`, `Sub/PartII-b_T09_5_5.lean`;
it needs `LapSplit`, `LapNvReal`, `LapCommRe`, which take only `ContDiff ℝ ∞ b`).

Proved here (all in `Tasks/AffineColumnComparison/Column/InletLap/`):
`classQ_cplx` (`Q_ε` of the complex lift is `qEps`), `qEps_qEps_eq` (`Q_ε² + ∂_η² - ε²diag(1,0) =
L_ε` on smooth profiles, symmetry of second derivatives), `lapProf_cplx`, `vecDiffEps_lin`;
and here `inletLapPtw_of`: `InletLapGen → InletLapPtw`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **Leaf `G4/3/3/1`** (SP 1651-1658, 1919-1921, `Δ(f e_r + g e_z) = (Δf - f/ρ²)e_r + (Δg)e_z`,
`∂_ρ(√s F) = s Q_ε F`, `∂_z(√s F) = s ∂_η F`, `1/ρ = ε√s`): off the axis, for a smooth complex
profile `b` (no support condition), `νΔ(N_v b) = N_v(lapProf ν ε b (Q_ε²b) (∂_η²b))`.
This is the off-axis branch of `lapPtwise_of` (`Sub/PartII-b_T09_5_5.lean`), with `lapSplit`,
`lapNvReal`, `lapCommRe` (`Tasks/GradLapNvC/LapSmooth/Ptwise/*`), which take only `ContDiff ℝ ∞ b`. -/
def InletLapGen : Prop :=
  ∀ (ε ν : ℝ) (b : CProf), 0 < ε → ContDiff ℝ ∞ b →
    ∀ (t : ℝ) (y : Space), y ∉ Axi.axis →
      nuLapT ν (NvC ε⁻¹ b) (t, y) =
        NvC ε⁻¹ (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b))) (t, y)

open UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.Short.IIb.InletT0
  UnforcedLeray.Short.IIb.InletLap in
/-- **`InletLapPtw` from the off-axis chart identity `InletLapGen`.** -/
theorem inletLapPtw_of (hgen : InletLapGen) : InletLapPtw := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hSig' hmode α τ y hy
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hBc : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inletProfile i) := by
    intro i
    have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
      unfold Params.cutStream
      exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul ((hfro i).comp contDiff_snd)
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  have hS : ContDiff ℝ ∞ (sumProf p α) := by
    unfold sumProf
    exact ((hBc 0).const_smul (α 0)).add ((hBc 1).const_smul (α 1))
  have hSc : ContDiff ℝ ∞ (cplx (sumProf p α)) := by
    rw [cplx_eq_mToC]
    exact mToC.contDiff.comp hS
  rw [inletC_eq p α]
  have hR : p.R = p.ε⁻¹ := rfl
  rw [hR, hgen p.ε p.ν _ p.ε_pos hSc τ y hy, lapProf_cplx hS p.ε p.ν]
  congr 1
  funext m
  have hlin : vecDiffEps p.ε (sumProf p α) m =
      α 0 • vecDiffEps p.ε (p.inletProfile 0) m + α 1 • vecDiffEps p.ε (p.inletProfile 1) m :=
    vecDiffEps_lin (hBc 0) (hBc 1) p.ε (α 0) (α 1) m
  have hsum : m.1 • (p.ν • vecDiffEps p.ε (sumProf p α) m) =
      α 0 • (m.1 • (p.ν • vecDiffEps p.ε (p.inletProfile 0) m)) +
        α 1 • (m.1 • (p.ν • vecDiffEps p.ε (p.inletProfile 1) m)) := by
    rw [hlin]
    module
  have h1 := congrFun (cplx_eq_mToC (fun y => y.1 • (p.ν • vecDiffEps p.ε (sumProf p α) y))) m
  have h2 : ∀ i : Fin 2, cplx (fun x => x.1 • (p.ν • vecDiffEps p.ε (p.inletProfile i) x)) m =
      mToC (m.1 • (p.ν • vecDiffEps p.ε (p.inletProfile i) m)) :=
    fun i => congrFun (cplx_eq_mToC _) m
  rw [h1, hsum, Fin.sum_univ_two, h2, h2]
  ext j
  simp [mToC_apply, Complex.real_smul]

end UnforcedLeray.Short.IIb
