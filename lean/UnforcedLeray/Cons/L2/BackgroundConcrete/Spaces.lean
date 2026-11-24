import UnforcedLeray.Units.B0412

/-!
# Theorem B3, concrete scheme: the spaces `Y_{q₀}` and `Z = X_{q₀} × ℝ²`

`paper/main.tex`, Section `sec:background`, lines 5070–5091 (`background:eq:2.1`–`2.3`, units
B0281, B0416, B0412), line 5210 ("with its sum graph norm and the symmetry (2.2)"), lines
5383–5386 (`background:eq:2.32`: "Here `f` is solenoidal"), lines 5697–5698 (unit B0458:
`A = R^{2/p}α`, `‖(w, A)‖_Z = ‖w‖_{X_p} + |A|`).

## The force space `Y`

The body sources of the ordinary system (2.32) are solenoidal (line 5385), real, and in the
class (2.2) (line 5080: "Restrict the fields to the axisymmetric class without swirl"):
`forceSpace P = Y_{q₀,σ} ∩ {real} ∩ {𝒪-invariant}`, an `ℝ`-subspace of B0411's complex
`Y_{q₀} = PhaseSpace.Yq P q₀` (decision D2: complex values, the real fields being those whose
pairings with real tests are real, `realSub`). It is closed (`isClosed_forceSpace`).

## The state space `Z`

`Z = X_{q₀} × ℝ²` with `‖(w, A)‖ = ‖w‖_X + |A|`, `‖w‖_X = ‖w‖ + ‖νΔw‖ + ‖T₀w‖` (B0412's
`normX`). It is realised as the closed `ℝ`-subspace `graphSpace P ν` of the ambient space
`Amb P = Y × Y × Y × ℝ²` with the `ℓ¹` norm (`WithLp 1`), cut out by "the triple is a graph
triple of `X_{q₀}`" (B0412's `XGraph`) and "`w` is real". The norm of `z` is exactly
`normX w + |A|` (`norm_eq_normX_add`), and `Z` is complete (`isClosed_graphSpace`).

No statement here depends on a junk value: `realSub` is defined through pairings with phase
tests, which are genuine for tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412

/-! ## Real elements of `Y_q` -/

section Real

variable (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- The real elements of `Y_q`: every pairing with a real phase test is real. -/
def realSub : Submodule ℝ (Yq P q) where
  carrier := {w | ∀ φ : ℝ × Space → Space, IsPhaseTest P φ →
    (phasePair P q (fun x => realC (φ x)) w).im = 0}
  add_mem' := by
    intro a b ha hb φ hφ
    rw [map_add, Complex.add_im, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := by
    intro φ _
    simp
  smul_mem' := by
    intro r a ha φ hφ
    have h : (phasePair P q (fun x => realC (φ x))) (r • a) =
        (r : ℂ) * (phasePair P q (fun x => realC (φ x))) a := by
      rw [ContinuousLinearMap.map_smul_of_tower, Complex.real_smul]
    rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha φ hφ]
    ring

theorem mem_realSub {w : Yq P q} : w ∈ realSub P q ↔ ∀ φ : ℝ × Space → Space,
    IsPhaseTest P φ → (phasePair P q (fun x => realC (φ x)) w).im = 0 := Iff.rfl

theorem isClosed_realSub : IsClosed (realSub P q : Set (Yq P q)) := by
  have h : (realSub P q : Set (Yq P q)) = ⋂ φ : ℝ × Space → Space, ⋂ (_ : IsPhaseTest P φ),
      {w | (phasePair P q (fun x => realC (φ x)) w).im = 0} := by
    ext w
    simp only [SetLike.mem_coe, mem_realSub, mem_iInter, mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun φ => isClosed_iInter fun _ =>
    isClosed_eq (Complex.continuous_im.comp (phasePair P q _).continuous) continuous_const

end Real

/-! ## The force space `Y` -/

section Force

variable (P : ℝ) [Fact (0 < P)]

/-- **The body source space** of (2.32) (lines 5085, 5383–5386): the real, solenoidal,
`𝒪`-invariant elements of `Y_{q₀}`. -/
def forceSpace : Submodule ℝ (Yq P q0E) :=
  realSub P q0E ⊓ (Ysigma P q0E).restrictScalars ℝ ⊓ (Osym P q0E).restrictScalars ℝ

theorem mem_forceSpace {f : Yq P q0E} :
    f ∈ forceSpace P ↔ f ∈ realSub P q0E ∧ f ∈ Ysigma P q0E ∧ f ∈ Osym P q0E := by
  simp only [forceSpace, Submodule.mem_inf, Submodule.restrictScalars_mem, and_assoc]

theorem isClosed_forceSpace : IsClosed (forceSpace P : Set (Yq P q0E)) := by
  have h : (forceSpace P : Set (Yq P q0E)) = (realSub P q0E : Set (Yq P q0E)) ∩
      (Ysigma P q0E : Set (Yq P q0E)) ∩ (Osym P q0E : Set (Yq P q0E)) := by
    ext f
    simp only [SetLike.mem_coe, mem_forceSpace, mem_inter_iff, and_assoc]
  rw [h]
  exact ((isClosed_realSub P q0E).inter isClosed_Ysigma).inter isClosed_Osym

instance : CompleteSpace (forceSpace P) := (isClosed_forceSpace P).completeSpace_coe

end Force

/-! ## The ambient space and the graph space `Z` -/

/-- `ℝ²`, the inlet coordinates `A = R^{2/p}α` with the Euclidean norm `|A|`. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

section Graph

variable (P : ℝ) [Fact (0 < P)]

/-- The ambient space `Y × Y × Y × ℝ²` with the `ℓ¹` norm. -/
abbrev Amb : Type :=
  WithLp 1 (Yq P q0E × WithLp 1 (Yq P q0E × WithLp 1 (Yq P q0E × E2)))

/-- The first component `w`. -/
def cw : Amb P →L[ℝ] Yq P q0E := WithLp.fstL 1 ℝ _ _

/-- The second component `νΔw`. -/
def cΔ : Amb P →L[ℝ] Yq P q0E :=
  (WithLp.fstL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ (Yq P q0E) _)

/-- The third component `T₀w`. -/
def cT : Amb P →L[ℝ] Yq P q0E :=
  (WithLp.fstL 1 ℝ _ _).comp
    ((WithLp.sndL 1 ℝ (Yq P q0E) _).comp (WithLp.sndL 1 ℝ (Yq P q0E) _))

/-- The inlet coordinates `A`. -/
def cA : Amb P →L[ℝ] E2 :=
  (WithLp.sndL 1 ℝ (Yq P q0E) _).comp
    ((WithLp.sndL 1 ℝ (Yq P q0E) _).comp (WithLp.sndL 1 ℝ (Yq P q0E) _))

/-- The graph triple `(w, νΔw, T₀w)`. -/
def cTriple : Amb P →L[ℝ] Yq P q0E × Yq P q0E × Yq P q0E :=
  (cw P).prod ((cΔ P).prod (cT P))

theorem norm_amb (g : Amb P) : ‖g‖ = ‖cw P g‖ + ‖cΔ P g‖ + ‖cT P g‖ + ‖cA P g‖ := by
  rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1]
  simp only [cw, cΔ, cT, cA, ContinuousLinearMap.comp_apply, WithLp.fstL_apply,
    WithLp.sndL_apply]
  ring

/-- **The state space `Z = X_{q₀} × ℝ²`** (line 5698), inside `Amb P`: graph triples of
`X_{q₀}` (`XGraph`, B0412) with real `w`, and any `A ∈ ℝ²`. -/
def graphSpace (ν : ℝ) : Submodule ℝ (Amb P) :=
  ((XGraph P ν q0E).restrictScalars ℝ).comap (cTriple P).toLinearMap ⊓
    (realSub P q0E).comap (cw P).toLinearMap

theorem mem_graphSpace {ν : ℝ} {g : Amb P} :
    g ∈ graphSpace P ν ↔ (cw P g, cΔ P g, cT P g) ∈ XGraph P ν q0E ∧ cw P g ∈ realSub P q0E := by
  simp only [graphSpace, Submodule.mem_inf, Submodule.mem_comap,
    Submodule.restrictScalars_mem, ContinuousLinearMap.coe_coe, cTriple,
    ContinuousLinearMap.prod_apply]

theorem isClosed_graphSpace (ν : ℝ) : IsClosed (graphSpace P ν : Set (Amb P)) := by
  have h : (graphSpace P ν : Set (Amb P)) =
      cTriple P ⁻¹' (XGraph P ν q0E : Set (Yq P q0E × Yq P q0E × Yq P q0E)) ∩
        cw P ⁻¹' (realSub P q0E : Set (Yq P q0E)) := by
    ext g
    simp only [SetLike.mem_coe, mem_graphSpace, mem_inter_iff, mem_preimage, cTriple,
      ContinuousLinearMap.prod_apply]
  rw [h]
  exact (isClosed_XGraph.preimage (cTriple P).continuous).inter
    ((isClosed_realSub P q0E).preimage (cw P).continuous)

instance (ν : ℝ) : CompleteSpace (graphSpace P ν) := (isClosed_graphSpace P ν).completeSpace_coe

/-- The operator space `Z → Y` is normed (stated as instances: the nested operator norm on
`Z → Z → Y` is otherwise not found by instance search). -/
instance (ν : ℝ) : NormedAddCommGroup (graphSpace P ν →L[ℝ] forceSpace P) := inferInstance

instance (ν : ℝ) : NormedSpace ℝ (graphSpace P ν →L[ℝ] forceSpace P) := inferInstance

variable {P}

/-- The correction `w ∈ X_{q₀}` of a state. -/
theorem cw_mem_X {ν : ℝ} (z : graphSpace P ν) : cw P z ∈ X P ν q0E := by
  obtain ⟨hw, -⟩ := (mem_XGraph_iff.1 ((mem_graphSpace P).1 z.2).1)
  exact hw

/-- **The norm of `Z`** (line 5698): `‖(w, A)‖ = ‖w‖_{X_{q₀}} + |A|`. -/
theorem norm_eq_normX_add {ν : ℝ} (z : graphSpace P ν) :
    ‖z‖ = normX (⟨cw P z, cw_mem_X z⟩ : X P ν q0E) + ‖cA P z‖ := by
  obtain ⟨hw, ha, hb⟩ := mem_XGraph_iff.1 ((mem_graphSpace P).1 z.2).1
  rw [Submodule.coe_norm, norm_amb, normX, ← ha, ← hb]

end Graph

end UnforcedLeray.Cons.C03.Concrete
