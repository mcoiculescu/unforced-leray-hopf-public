import UnforcedLeray.Lib.PhaseSpace.Ops
import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# Distributional operators and the free graph `D_(ν,q)` (INF25 T25.2)

Blueprint units B0411 (`eq:free-stress-1`, tex 7313–7337), B0005 (tex 136–147), B0412
(`background:eq:2.3`, tex 5085–5091), B0427 (tex 7540–7542), B0429(i) (tex 3591–3621).

`HasPhaseOp Lt f g` says that `L f = g` in distributions, where `Lt` is the transpose of
`L` on phase tests: `⟪Lt Φ, f⟫ = ⟪Φ, g⟫` for every phase test `Φ`. The free graph is

  `D_(ν,q) = {(w, a, b) ∈ Y_q³ : νΔw = a, T₀w = b in distributions}`,

with `T₀ = ∂_τ − ½ y·∇` (tex 7318). Only the sums `νΔw` and `T₀w` are required in `Y_q`; the
two summands of `T₀w` are not (tex 7329–7330), and there is no boundary condition at the
origin, an axis or infinity (tex 7331): tests are arbitrary smooth periodic fields of
bounded support. The solenoidal graph adds `div w = 0` in distributions
(`⟪∇φ, w⟫ = 0` for scalar phase tests `φ`, tex 7333–7334).

Each condition is an intersection of kernels of continuous linear functionals, so both
graphs are closed (`isClosed_freeGraph`, `isClosed_solenoidalFreeGraph`) and complete:
"convergence of `w`, `νΔw` and `T₀w` in `Y_q` passes each distributional identity to the
limit" (tex 7540–7542, B0427). The graph norm `‖w‖ + ‖a‖ + ‖b‖` of tex 7326 is equivalent
to Mathlib's max norm on the product, so the topology and completeness are the manuscript's.

Status: infrastructure only. B0427 asserts completeness of `D_(ν,q)` as a space of `w`; that
`a` and `b` are determined by `w` (uniqueness of distributions in `Y_q`) is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `L f = g` in distributions, where `Lt` is the transpose of `L` on phase tests. -/
def HasPhaseOp (Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3) (f g : Yq P q) : Prop :=
  ∀ Φ, IsPhaseTest P Φ → phasePair P q (Lt Φ) f = phasePair P q Φ g

/-- `div f = 0` in distributions: `⟪∇φ, f⟫ = 0` for every scalar phase test `φ`. -/
def IsPhaseSolenoidal (f : Yq P q) : Prop :=
  ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → phasePair P q (gradT φ) f = 0

theorem isClosed_hasPhaseOp (Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3) :
    IsClosed {x : Yq P q × Yq P q | HasPhaseOp Lt x.1 x.2} := by
  have h : {x : Yq P q × Yq P q | HasPhaseOp Lt x.1 x.2} =
      ⋂ Φ : ℝ × Space → CVec3, ⋂ _ : IsPhaseTest P Φ,
        {x : Yq P q × Yq P q | phasePair P q (Lt Φ) x.1 = phasePair P q Φ x.2} := by
    ext x
    simp [HasPhaseOp]
  rw [h]
  exact isClosed_iInter fun Φ => isClosed_iInter fun _ =>
    isClosed_eq ((phasePair P q (Lt Φ)).continuous.comp continuous_fst)
      ((phasePair P q Φ).continuous.comp continuous_snd)

theorem isClosed_isPhaseSolenoidal : IsClosed {f : Yq P q | IsPhaseSolenoidal f} := by
  have h : {f : Yq P q | IsPhaseSolenoidal f} =
      ⋂ φ : ℝ × Space → ℂ, ⋂ _ : IsPhaseTest P φ,
        {f : Yq P q | phasePair P q (gradT φ) f = 0} := by
    ext f
    simp [IsPhaseSolenoidal]
  rw [h]
  exact isClosed_iInter fun φ => isClosed_iInter fun _ =>
    isClosed_eq (phasePair P q (gradT φ)).continuous continuous_const

theorem HasPhaseOp.add {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3} {f g f' g' : Yq P q}
    (h : HasPhaseOp Lt f g) (h' : HasPhaseOp Lt f' g') : HasPhaseOp Lt (f + f') (g + g') :=
  fun Φ hΦ => by simp [map_add, h Φ hΦ, h' Φ hΦ]

theorem HasPhaseOp.smul {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3} {f g : Yq P q}
    (h : HasPhaseOp Lt f g) (c : ℂ) : HasPhaseOp Lt (c • f) (c • g) :=
  fun Φ hΦ => by simp [map_smul, h Φ hΦ]

theorem HasPhaseOp.zero (Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3) :
    HasPhaseOp Lt (0 : Yq P q) 0 :=
  fun Φ _ => by simp

theorem IsPhaseSolenoidal.add {f f' : Yq P q} (h : IsPhaseSolenoidal f)
    (h' : IsPhaseSolenoidal f') : IsPhaseSolenoidal (f + f') :=
  fun φ hφ => by simp [map_add, h φ hφ, h' φ hφ]

theorem IsPhaseSolenoidal.smul {f : Yq P q} (h : IsPhaseSolenoidal f) (c : ℂ) :
    IsPhaseSolenoidal (c • f) :=
  fun φ hφ => by simp [map_smul, h φ hφ]

/-- The transpose of `νΔ`: `Φ ↦ ν Δ Φ`. -/
def nuLapT (ν : ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := ν • lapT Φ

variable (P) in
/-- **The free graph** `D_(ν,q)` (B0411, `eq:free-stress-1`, tex 7322–7327): triples
`(w, a, b) ∈ Y_q³` with `νΔw = a` and `T₀w = b` in distributions. -/
def freeGraph (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Submodule ℂ (Yq P q × Yq P q × Yq P q) where
  carrier := {x | HasPhaseOp (nuLapT ν) x.1 x.2.1 ∧ HasPhaseOp driftT x.1 x.2.2}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨HasPhaseOp.zero _, HasPhaseOp.zero _⟩
  smul_mem' := fun c _ hx => ⟨hx.1.smul c, hx.2.smul c⟩

theorem mem_freeGraph {ν : ℝ} {w a b : Yq P q} :
    (w, a, b) ∈ freeGraph P ν q ↔ HasPhaseOp (nuLapT ν) w a ∧ HasPhaseOp driftT w b :=
  Iff.rfl

variable (P) in
/-- The solenoidal free graph `D_(ν,q),σ` (tex 7333–7334): add `div w = 0` in
distributions. -/
def solenoidalFreeGraph (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Submodule ℂ (Yq P q × Yq P q × Yq P q) where
  carrier := {x | x ∈ freeGraph P ν q ∧ IsPhaseSolenoidal x.1}
  add_mem' := fun ha hb => ⟨(freeGraph P ν q).add_mem ha.1 hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨(freeGraph P ν q).zero_mem, fun φ _ => by simp⟩
  smul_mem' := fun c _ hx => ⟨(freeGraph P ν q).smul_mem c hx.1, hx.2.smul c⟩

/-- **B0427**: the free graph is closed in `Y_q³` (tex 7540–7542). -/
theorem isClosed_freeGraph (ν : ℝ) : IsClosed (freeGraph P ν q : Set (Yq P q × Yq P q × Yq P q)) := by
  have h1 : IsClosed {x : Yq P q × Yq P q × Yq P q | HasPhaseOp (nuLapT ν) x.1 x.2.1} :=
    (isClosed_hasPhaseOp (nuLapT ν)).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : IsClosed {x : Yq P q × Yq P q × Yq P q | HasPhaseOp driftT x.1 x.2.2} :=
    (isClosed_hasPhaseOp driftT).preimage
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact h1.inter h2

/-- The solenoidal free graph is closed (tex 7540–7542). -/
theorem isClosed_solenoidalFreeGraph (ν : ℝ) :
    IsClosed (solenoidalFreeGraph P ν q : Set (Yq P q × Yq P q × Yq P q)) :=
  (isClosed_freeGraph ν).inter (isClosed_isPhaseSolenoidal.preimage continuous_fst)

/-- `D_(ν,q)` with the graph norm is a Banach space (B0427). -/
instance freeGraph_completeSpace (ν : ℝ) : CompleteSpace (freeGraph P ν q) :=
  (isClosed_freeGraph ν).completeSpace_coe

instance solenoidalFreeGraph_completeSpace (ν : ℝ) : CompleteSpace (solenoidalFreeGraph P ν q) :=
  (isClosed_solenoidalFreeGraph ν).completeSpace_coe

/-- The graph-norm of a triple, `‖w‖ + ‖a‖ + ‖b‖` (tex 7326). -/
def graphNorm (x : Yq P q × Yq P q × Yq P q) : ℝ := ‖x.1‖ + ‖x.2.1‖ + ‖x.2.2‖

theorem norm_le_graphNorm (x : Yq P q × Yq P q × Yq P q) : ‖x‖ ≤ graphNorm x := by
  obtain ⟨w, a, b⟩ := x
  simp only [graphNorm, Prod.norm_def]
  refine max_le (by linarith [norm_nonneg a, norm_nonneg b]) (max_le ?_ ?_) <;>
    linarith [norm_nonneg w, norm_nonneg a, norm_nonneg b]

theorem graphNorm_le (x : Yq P q × Yq P q × Yq P q) : graphNorm x ≤ 3 * ‖x‖ := by
  obtain ⟨w, a, b⟩ := x
  simp only [graphNorm, Prod.norm_def]
  have h1 : ‖w‖ ≤ max ‖w‖ (max ‖a‖ ‖b‖) := le_max_left _ _
  have h2 : ‖a‖ ≤ max ‖w‖ (max ‖a‖ ‖b‖) := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : ‖b‖ ≤ max ‖w‖ (max ‖a‖ ‖b‖) := (le_max_right _ _).trans (le_max_right _ _)
  linarith

end UnforcedLeray.PhaseSpace
