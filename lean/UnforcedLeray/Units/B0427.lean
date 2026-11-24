import UnforcedLeray.Units.B0411

/-!
# Unit B0427: completeness of the graph `D_(ν,q)`

Blueprint unit `B0427` (label `unlabeled:7541`), `paper/main.tex` lines 7540–7542
(§`sec:st18-9105`, "Core, uniqueness, and exact domain"), within the source range 7268–8686.
Depends on `B0411` (`eq:free-stress-1`, tex 7304–7337); consumed by `B0473` (tex 7774–7788).

**Statement (tex 7540–7542).** "The graph is complete because its derivative operators are
distributionally closed." In the blueprint's words: `D_(ν,q)` with its graph norm
`‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}` (tex 7326) is a Banach space, and `D_(ν,q),σ` is a
closed subspace; convergence of `w`, `νΔw` and `T₀w` in `Y_q` passes each distributional
identity to the limit.

**Formalization.**
* `GraphD P ν q` is the space `D_(ν,q)` of unit B0411 (`B0411.D`, a subspace of
  `Y_q = PhaseSpace.Yq P q`) as a type of its own, carrying the manuscript's graph norm
  `‖w‖ = B0411.graphNormD w = ‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}` (`norm_def`), not the
  norm of `Y_q`. It is a normed space over `ℂ` (`NormedSpace.Core` from linearity of `νΔ`,
  `T₀` on `D_(ν,q)`, i.e. `B0411.nuLapL`, `B0411.T0L`), and **it is complete**
  (instance `instCompleteSpace`, theorem `completeSpace_graphD`; with the norm written out:
  `exists_limit_of_cauchy`): the graph map
  `w ↦ (w, νΔw, T₀w)` is a continuous linear isomorphism `graphCLE` onto the closed
  subspace `PhaseSpace.freeGraph` of `Y_q³` (`PhaseSpace.isClosed_freeGraph`), with
  bounds `1` and `3` between the graph norm and the max norm of `Y_q³`.
* The derivative operators are closed (tex 7541): `tendsto_mem_D` says that if `w_i ∈ D_(ν,q)`
  and `w_i → w`, `νΔw_i → a`, `T₀w_i → b` in `Y_q`, then `w ∈ D_(ν,q)`, `νΔw = a`, `T₀w = b`;
  the reason (proof outline) is that each identity `⟪Lᵗ Φ, w⟫ = ⟪Φ, Lw⟫` involves only
  continuous pairings on `Y_q` (`isClosed_hasPhaseOp_nuLap`, `isClosed_hasPhaseOp_drift`,
  `isClosed_isPhaseSolenoidal'`).
* `DsigmaG P ν q` is `D_(ν,q),σ = {w ∈ D_(ν,q) : div w = 0}` as a subspace of the graph-normed
  space (`mem_DsigmaG_iff`: the same elements as `B0411.Dsigma`); it is closed
  (`isClosed_DsigmaG`) and hence complete (instance, `completeSpace_DsigmaG`).
* For the consumers, `νΔ`, `T₀`, `L₀ : D_(ν,q) → Y_q` and the inclusion `D_(ν,q) → Y_q` are
  bounded linear maps of norm at most `1` for the graph norm (`nuLapG`, `T0G`, `L0G`,
  `incl`).

Hypotheses: every statement holds for every real `ν`, every `P > 0` (the instance `Y_q`
requires) and every `1 ≤ q ≤ ∞`, which contains the manuscript's standing assumptions
`ν > 0`, `0 < P ≤ 1` (tex 7306–7308). No junk values occur: no integrals, divisions or
`toReal` appear in the statements; the only scalar is `(1/2 : ℂ)` in `L₀`.

Status: the unit is proved in full. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0427

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section GraphSpace

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)] {ν : ℝ}

/-! ### Properties of the graph norm on `D_(ν,q)` (tex 7326) -/

theorem graphNormD_nonneg (w : D P ν q) : 0 ≤ graphNormD w := by
  unfold graphNormD
  positivity

theorem norm_le_graphNormD (w : D P ν q) : ‖(w : Yq P q)‖ ≤ graphNormD w := by
  unfold graphNormD
  linarith [norm_nonneg (nuLapD w), norm_nonneg (T0D w)]

theorem norm_nuLapD_le_graphNormD (w : D P ν q) : ‖nuLapD w‖ ≤ graphNormD w := by
  unfold graphNormD
  linarith [norm_nonneg (w : Yq P q), norm_nonneg (T0D w)]

theorem norm_T0D_le_graphNormD (w : D P ν q) : ‖T0D w‖ ≤ graphNormD w := by
  unfold graphNormD
  linarith [norm_nonneg (w : Yq P q), norm_nonneg (nuLapD w)]

theorem norm_L0D_le_graphNormD (w : D P ν q) : ‖L0D w‖ ≤ graphNormD w := by
  have hc : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have h1 : ‖(1 / 2 : ℂ) • (w : Yq P q)‖ ≤ ‖(w : Yq P q)‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  have h2 := norm_sub_le (T0D w - nuLapD w) ((1 / 2 : ℂ) • (w : Yq P q))
  have h3 := norm_sub_le (T0D w) (nuLapD w)
  unfold L0D graphNormD
  linarith

theorem graphNormD_smul (c : ℂ) (w : D P ν q) : graphNormD (c • w) = ‖c‖ * graphNormD w := by
  simp only [graphNormD, ← nuLapL_apply, ← T0L_apply, map_smul, Submodule.coe_smul, norm_smul]
  ring

theorem graphNormD_add_le (w w' : D P ν q) :
    graphNormD (w + w') ≤ graphNormD w + graphNormD w' := by
  simp only [graphNormD, ← nuLapL_apply, ← T0L_apply, map_add, Submodule.coe_add]
  linarith [norm_add_le (w : Yq P q) (w' : Yq P q), norm_add_le (nuLapL w) (nuLapL w'),
    norm_add_le (T0L w) (T0L w')]

theorem graphNormD_eq_zero_iff (w : D P ν q) : graphNormD w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h0 : ‖(w : Yq P q)‖ = 0 :=
      le_antisymm (h ▸ norm_le_graphNormD w) (norm_nonneg _)
    exact Subtype.ext (norm_eq_zero.1 h0)
  · rintro rfl
    simp only [graphNormD, ← nuLapL_apply, ← T0L_apply, map_zero, ZeroMemClass.coe_zero,
      norm_zero, add_zero]

/-! ### `D_(ν,q)` as a normed space with the graph norm -/

variable (P) in
/-- **`D_(ν,q)` with its graph norm** (B0427, tex 7540–7542; graph norm of tex 7326, unit
B0411): the subspace `B0411.D P ν q` of `Y_q` as a type of its own, normed by
`‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}` instead of the norm of `Y_q`. -/
def GraphD (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Type := D P ν q

instance : AddCommGroup (GraphD P ν q) := inferInstanceAs (AddCommGroup (D P ν q))

instance : Module ℂ (GraphD P ν q) := inferInstanceAs (Module ℂ (D P ν q))

/-- The identification of `GraphD P ν q` with the subspace `D_(ν,q)` of `Y_q`. -/
def toD : GraphD P ν q ≃ₗ[ℂ] D P ν q := LinearEquiv.refl ℂ (D P ν q)

/-- The graph norm (tex 7326). -/
instance : Norm (GraphD P ν q) := ⟨fun w => graphNormD (toD w)⟩

/-- **The norm of `GraphD` is the graph norm** `‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}`
(tex 7326). -/
theorem norm_def (w : GraphD P ν q) : ‖w‖ = graphNormD (toD w) := rfl

theorem norm_def' (w : GraphD P ν q) :
    ‖w‖ = ‖((toD w : D P ν q) : Yq P q)‖ + ‖nuLapD (toD w)‖ + ‖T0D (toD w)‖ := rfl

/-- The axioms of a normed space for the graph norm. -/
theorem normedSpaceCore : NormedSpace.Core ℂ (GraphD P ν q) where
  norm_nonneg w := graphNormD_nonneg (toD w)
  norm_smul c w := by
    rw [norm_def, norm_def, map_smul, graphNormD_smul]
  norm_triangle w w' := by
    rw [norm_def, norm_def, norm_def, map_add]
    exact graphNormD_add_le _ _
  norm_eq_zero_iff w := (graphNormD_eq_zero_iff (toD w)).trans toD.map_eq_zero_iff

instance : NormedAddCommGroup (GraphD P ν q) := NormedAddCommGroup.ofCore normedSpaceCore

instance : NormedSpace ℂ (GraphD P ν q) := NormedSpace.ofCore normedSpaceCore

/-! ### Bounded operators on the graph-normed space -/

/-- The inclusion `D_(ν,q) → Y_q`, as a linear map. -/
def inclL : GraphD P ν q →ₗ[ℂ] Yq P q := (D P ν q).subtype ∘ₗ (toD : GraphD P ν q ≃ₗ[ℂ] _).toLinearMap

theorem inclL_apply (w : GraphD P ν q) : inclL w = ((toD w : D P ν q) : Yq P q) := rfl

theorem norm_inclL_le (w : GraphD P ν q) : ‖inclL w‖ ≤ ‖w‖ :=
  norm_le_graphNormD (toD w)

/-- The inclusion `D_(ν,q) → Y_q` is bounded by `1` for the graph norm. -/
def incl : GraphD P ν q →L[ℂ] Yq P q :=
  inclL.mkContinuous 1 fun w => by rw [one_mul]; exact norm_inclL_le w

theorem incl_apply (w : GraphD P ν q) : incl w = ((toD w : D P ν q) : Yq P q) := rfl

/-- `νΔ : D_(ν,q) → Y_q`, bounded by `1` for the graph norm. -/
def nuLapG : GraphD P ν q →L[ℂ] Yq P q :=
  (nuLapL ∘ₗ (toD : GraphD P ν q ≃ₗ[ℂ] _).toLinearMap).mkContinuous 1 fun w => by
    rw [one_mul]; exact norm_nuLapD_le_graphNormD (toD w)

theorem nuLapG_apply (w : GraphD P ν q) : nuLapG w = nuLapD (toD w) := rfl

/-- `T₀ : D_(ν,q) → Y_q`, bounded by `1` for the graph norm. -/
def T0G : GraphD P ν q →L[ℂ] Yq P q :=
  (T0L ∘ₗ (toD : GraphD P ν q ≃ₗ[ℂ] _).toLinearMap).mkContinuous 1 fun w => by
    rw [one_mul]; exact norm_T0D_le_graphNormD (toD w)

theorem T0G_apply (w : GraphD P ν q) : T0G w = T0D (toD w) := rfl

/-- `L₀ = T₀ − νΔ − ½ : D_(ν,q) → Y_q` (tex 7319), bounded by `1` for the graph norm. -/
def L0G : GraphD P ν q →L[ℂ] Yq P q :=
  (L0L ∘ₗ (toD : GraphD P ν q ≃ₗ[ℂ] _).toLinearMap).mkContinuous 1 fun w => by
    rw [one_mul]; exact norm_L0D_le_graphNormD (toD w)

theorem L0G_apply (w : GraphD P ν q) : L0G w = L0D (toD w) := rfl

/-! ### Completeness (tex 7540–7542) -/

/-- The graph map `w ↦ (w, νΔw, T₀w)` of B0411 (`graphEquiv`), on the graph-normed space. -/
def graphLE : GraphD P ν q ≃ₗ[ℂ] freeGraph P ν q := toD.trans graphEquiv

/-- **The graph map** `w ↦ (w, νΔw, T₀w)` is a continuous linear isomorphism of the
graph-normed `D_(ν,q)` onto the closed subspace `freeGraph P ν q` of `Y_q³`
(`‖graphCLE w‖ ≤ ‖w‖ ≤ 3 ‖graphCLE w‖`). -/
def graphCLE : GraphD P ν q ≃L[ℂ] freeGraph P ν q :=
  (graphLE : GraphD P ν q ≃ₗ[ℂ] freeGraph P ν q).toContinuousLinearEquivOfBounds 1 3
    (fun w => by
      rw [one_mul]
      exact norm_graphEquiv_le (toD w))
    (fun x => by
      have h := graphNormD_le (toD ((graphLE : GraphD P ν q ≃ₗ[ℂ] freeGraph P ν q).symm x))
      have e : graphEquiv (toD ((graphLE : GraphD P ν q ≃ₗ[ℂ] freeGraph P ν q).symm x)) = x :=
        (graphLE : GraphD P ν q ≃ₗ[ℂ] freeGraph P ν q).apply_symm_apply x
      rw [e] at h
      exact h)

theorem graphCLE_apply (w : GraphD P ν q) :
    (graphCLE w : Yq P q × Yq P q × Yq P q) =
      (((toD w : D P ν q) : Yq P q), nuLapD (toD w), T0D (toD w)) := rfl

/-- **B0427: `D_(ν,q)` with its graph norm is a Banach space** (tex 7540–7542). -/
instance instCompleteSpace : CompleteSpace (GraphD P ν q) := by
  have : CompleteSpace (freeGraph P ν q) := (isClosed_freeGraph ν).completeSpace_coe
  have he : IsUniformEmbedding (graphCLE : GraphD P ν q ≃L[ℂ] freeGraph P ν q) :=
    ContinuousLinearEquiv.isUniformEmbedding _
  exact (he.isUniformInducing.completeSpace_congr
    (graphCLE : GraphD P ν q ≃L[ℂ] freeGraph P ν q).surjective).2 this

theorem completeSpace_graphD : CompleteSpace (GraphD P ν q) := instCompleteSpace

/-- **Completeness, with the norm written out** (tex 7540–7542, graph norm of tex 7326): a
sequence in `D_(ν,q)` that is Cauchy for `‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}` converges for
that norm to an element of `D_(ν,q)`. (This restates `instCompleteSpace` without reference
to the uniform structure.) -/
theorem exists_limit_of_cauchy (u : ℕ → GraphD P ν q)
    (hu : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, graphNormD (toD (u m - u n)) < ε) :
    ∃ w : GraphD P ν q, ∀ ε > 0, ∃ N, ∀ n ≥ N, graphNormD (toD (u n - w)) < ε := by
  have hc : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun n hn => by rw [dist_eq_norm, norm_def]; exact hN n hn N le_rfl⟩
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hw ε hε
  exact ⟨N, fun n hn => by have := hN n hn; rwa [dist_eq_norm, norm_def] at this⟩

/-! ### Closedness of the derivative operators (tex 7541) -/

/-- `νΔw = a` in distributions is a closed condition on `(w, a) ∈ Y_q²`: test pairings are
continuous on `Y_q` (proof outline of B0427). -/
theorem isClosed_hasPhaseOp_nuLap (ν : ℝ) :
    IsClosed {x : Yq P q × Yq P q | HasPhaseOp (nuLapT ν) x.1 x.2} :=
  isClosed_hasPhaseOp (nuLapT ν)

/-- `T₀w = b` in distributions is a closed condition on `(w, b) ∈ Y_q²`. -/
theorem isClosed_hasPhaseOp_drift :
    IsClosed {x : Yq P q × Yq P q | HasPhaseOp driftT x.1 x.2} :=
  isClosed_hasPhaseOp driftT

/-- `div w = 0` in distributions is a closed condition on `w ∈ Y_q`. -/
theorem isClosed_isPhaseSolenoidal' : IsClosed {f : Yq P q | IsPhaseSolenoidal f} :=
  isClosed_isPhaseSolenoidal

/-- **The derivative operators are closed** (tex 7541): if `w_i ∈ D_(ν,q)` and `w_i → w`,
`νΔw_i → a`, `T₀w_i → b` in `Y_q`, then `w ∈ D_(ν,q)` with `νΔw = a` and `T₀w = b`. -/
theorem tendsto_mem_D {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → D P ν q} {w a b : Yq P q}
    (hw : Tendsto (fun i => (u i : Yq P q)) l (𝓝 w))
    (ha : Tendsto (fun i => nuLapD (u i)) l (𝓝 a))
    (hb : Tendsto (fun i => T0D (u i)) l (𝓝 b)) :
    ∃ hw' : w ∈ D P ν q, nuLapD ⟨w, hw'⟩ = a ∧ T0D ⟨w, hw'⟩ = b := by
  have hmem : (w, a, b) ∈ freeGraph P ν q :=
    (isClosed_freeGraph ν).mem_of_tendsto (hw.prodMk_nhds (ha.prodMk_nhds hb))
      (Eventually.of_forall fun i => graphTriple_mem (u i))
  exact mem_freeGraph_iff.1 hmem

/-- The solenoidal condition passes to `Y_q`-limits as well: if moreover `div w_i = 0`, then
`w ∈ D_(ν,q),σ`. -/
theorem tendsto_mem_Dsigma {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → D P ν q}
    {w a b : Yq P q} (hσ : ∀ i, (u i : Yq P q) ∈ Ysigma P q)
    (hw : Tendsto (fun i => (u i : Yq P q)) l (𝓝 w))
    (ha : Tendsto (fun i => nuLapD (u i)) l (𝓝 a))
    (hb : Tendsto (fun i => T0D (u i)) l (𝓝 b)) :
    ∃ hw' : w ∈ Dsigma P ν q, nuLapD ⟨w, hw'.1⟩ = a ∧ T0D ⟨w, hw'.1⟩ = b := by
  obtain ⟨hD, h1, h2⟩ := tendsto_mem_D hw ha hb
  exact ⟨⟨hD, isClosed_Ysigma.mem_of_tendsto hw (Eventually.of_forall hσ)⟩, h1, h2⟩

/-! ### The solenoidal subspace `D_(ν,q),σ` (tex 7333–7334, 7540–7542) -/

variable (P) in
/-- **`D_(ν,q),σ`** as a subspace of the graph-normed space `GraphD P ν q`: the `w` with
`div w = 0` in distributions (tex 7333–7334, unit B0411). -/
def DsigmaG (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (GraphD P ν q) :=
  (Ysigma P q).comap inclL

theorem mem_DsigmaG {w : GraphD P ν q} : w ∈ DsigmaG P ν q ↔ inclL w ∈ Ysigma P q := Iff.rfl

/-- `DsigmaG` has the same elements as `B0411.Dsigma`. -/
theorem mem_DsigmaG_iff {w : GraphD P ν q} :
    w ∈ DsigmaG P ν q ↔ ((toD w : D P ν q) : Yq P q) ∈ Dsigma P ν q :=
  ⟨fun h => ⟨(toD w).2, h⟩, fun h => h.2⟩

/-- **B0427: `D_(ν,q),σ` is a closed subspace of `D_(ν,q)`** for the graph norm
(tex 7540–7542). -/
theorem isClosed_DsigmaG : IsClosed (DsigmaG P ν q : Set (GraphD P ν q)) :=
  isClosed_Ysigma.preimage (incl : GraphD P ν q →L[ℂ] Yq P q).continuous

instance instCompleteSpaceDsigmaG : CompleteSpace (DsigmaG P ν q) :=
  isClosed_DsigmaG.completeSpace_coe

/-- `D_(ν,q),σ` with the graph norm is a Banach space. -/
theorem completeSpace_DsigmaG : CompleteSpace (DsigmaG P ν q) := instCompleteSpaceDsigmaG

end GraphSpace

/-! ### The unit, bundled -/

section Bundle

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- **B0427 (tex 7540–7542), bundled.** For every `ν` and every `1 ≤ q ≤ ∞` (in particular
under the standing assumptions `ν > 0`, `0 < P ≤ 1` of tex 7306–7308):
1. the norm of `GraphD P ν q` is the graph norm `‖w‖ + ‖νΔw‖ + ‖T₀w‖` of tex 7326;
2. `D_(ν,q)` with this norm is complete (a Banach space), also stated with the norm written
   out (Cauchy sequences for the graph norm converge for the graph norm);
3. `D_(ν,q),σ` is a closed subspace of it, hence also complete;
4. convergence of `w`, `νΔw`, `T₀w` in `Y_q` passes the distributional identities to the
   limit. -/
theorem B0427_spec (ν : ℝ) :
    (∀ w : GraphD P ν q,
      ‖w‖ = ‖((toD w : D P ν q) : Yq P q)‖ + ‖nuLapD (toD w)‖ + ‖T0D (toD w)‖) ∧
    CompleteSpace (GraphD P ν q) ∧
    (∀ u : ℕ → GraphD P ν q,
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, graphNormD (toD (u m - u n)) < ε) →
      ∃ w : GraphD P ν q, ∀ ε > 0, ∃ N, ∀ n ≥ N, graphNormD (toD (u n - w)) < ε) ∧
    IsClosed (DsigmaG P ν q : Set (GraphD P ν q)) ∧
    CompleteSpace (DsigmaG P ν q) ∧
    (∀ (u : ℕ → D P ν q) (w a b : Yq P q),
      Tendsto (fun n => (u n : Yq P q)) atTop (𝓝 w) →
      Tendsto (fun n => nuLapD (u n)) atTop (𝓝 a) →
      Tendsto (fun n => T0D (u n)) atTop (𝓝 b) →
      ∃ hw : w ∈ D P ν q, nuLapD ⟨w, hw⟩ = a ∧ T0D ⟨w, hw⟩ = b) :=
  ⟨norm_def', completeSpace_graphD, exists_limit_of_cauchy, isClosed_DsigmaG, completeSpace_DsigmaG,
    fun _ _ _ _ hw ha hb => tendsto_mem_D hw ha hb⟩

end Bundle

end UnforcedLeray.B0427
