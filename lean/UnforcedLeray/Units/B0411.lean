import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.Units.B0411.Operators
import UnforcedLeray.Lib.PhaseSpace.Charts

/-!
# Unit B0411 (`eq:free-stress-1`): the phase space `Y_q`, the drift `T₀`, the operator `L₀`
# and the distributional graph `D_(ν,q)`

Blueprint unit `B0411`, label `eq:free-stress-1`, `paper/main.tex` lines 7304–7337
(§`sec:st18-8873`, "Physical free graph and weak stress extension").

**Statement (tex 7306–7334).** Throughout, `ν > 0` and `0 < P ≤ 1`, and phase integrals are
normalised by `P⁻¹`. Set
`Y_q = L^q(ℝ/Pℤ; L^q(ℝ³))`, `‖f‖_{Y_q}^q = P⁻¹ ∫₀ᴾ ‖f(τ)‖_{L^q}^q dτ`,
`T₀ = ∂_τ − ½ y·∇`, `L₀ = T₀ − νΔ − ½`. The distributional graph is
`D_(ν,q) = {w ∈ Y_q : νΔw ∈ Y_q, T₀w ∈ Y_q}` with
`‖w‖_{D_(ν,q)} = ‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}`. The two summands of `T₀w` need not
lie in `Y_q` separately; there is no boundary condition at the origin, on an axis or at
infinity. A subscript `σ` denotes the closed subspaces cut out by `div w = 0` in
distributions.


built on `Lib/PhaseSpace`).**
* `Y_q` is `PhaseSpace.Yq P q = Lp (Lp CVec3 q volume) q haarAddCircle`, the Bochner space
  `L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))` with the probability Haar measure on the phase circle; complex
  three-vector values as in the blueprint (complex `μ` appears in the consumers).
  `enorm_rpow_Yq` / `norm_rpow_Yq` prove the normalisation `‖f‖^q = P⁻¹ ∫₀ᴾ ‖f(τ)‖^q dτ`
  (tex 7315) for `1 ≤ q < ∞`.
* Distributions on `(ℝ/Pℤ) × ℝ³` are pairings with phase tests (smooth, `P`-periodic,
  bounded `y`-support: `IsPhaseTest`), and `L w = g` in distributions is
  `HasPhaseOp Lᵗ w g : ∀ Φ, ⟪Lᵗ Φ, w⟫ = ⟪Φ, g⟫`, with `Lᵗ` the transpose. The transposes are
  `νΔ ↦ nuLapT ν` (`νΔ` is symmetric), `T₀ ↦ driftT = −∂_τ + ½ y·∇ + 3/2` (since
  `div y = 3`), `L₀ ↦ L0T ν = driftT − νΔ − ½`. The forward operators on smooth fields are
  `T0` and `L0` (tex 7318–7319); `driftT_eq_transpose_parts` records that `driftT` is the
  combination `∂_τᵗ − ½ (y·∇)ᵗ` of the transposes of the two summands, and the pointwise
  Lagrange identities `lagrange_T0`, `lagrange_L0` (file `B0411/Operators.lean`) show
  `T₀ᵗΦ·u − Φ·T₀u` and `L₀ᵗΦ·u − Φ·L₀u` to be `τ`- and `y`-derivatives of smooth functions,
  i.e. `driftT`, `L0T` are the formal transposes of `T₀`, `L₀`.
* Phase tests separate the points of `Y_q` (`eq_zero_of_forall_phasePair`, file
  `B0411/Separation.lean`, for every `1 ≤ q ≤ ∞`), so the distributions `νΔw`, `T₀w`, `L₀w`
  have at most one representative in `Y_q` (`hasPhaseOp_unique`). This is what makes the
  manuscript's `D_(ν,q)` a space of `w` with a well-defined graph norm.
* `D P ν q : Submodule ℂ (Yq P q)` is `{w | ∃ a, νΔw = a ∧ ∃ b, T₀w = b}` in distributions
  (`mem_D`); `nuLapD`, `T0D`, `L0D` are the operators on it (linear: `nuLapL`, `T0L`, `L0L`),
  characterised by `nuLapD_eq`, `T0D_eq`, `L0D_eq`; `graphNormD w = ‖w‖ + ‖νΔw‖ + ‖T₀w‖`
  (tex 7326). `graphEquiv : D P ν q ≃ₗ[ℂ] freeGraph P ν q` identifies `D_(ν,q)` with the
  closed graph `freeGraph` of `Lib/PhaseSpace/Graph.lean` (the object the scoping plan freezes
  for the consumers, D17), and `graphNormD_eq` matches the norms.
* Only the combination `T₀w` is required in `Y_q` (tex 7329–7330): `driftT` tests the
  combined operator, and `hasPhaseOp_driftT_of_parts` shows that separate regularity of
  `∂_τ w` and `y·∇w` is a special case, not a requirement.
* No boundary condition (tex 7331): the tests are all smooth periodic fields of bounded
  support, with no restriction near the origin or an axis and no decay condition on `w`.
* `Ysigma P q` (`Y_{q,σ}`) and `Dsigma P ν q` (`D_(ν,q),σ`) impose `div w = 0` in
  distributions (`IsPhaseSolenoidal`); `isClosed_Ysigma` and `isClosed_Dsigma` give
  closedness in `Y_q`, and `graphEquiv` carries `Dsigma` onto the closed
  `solenoidalFreeGraph` (`mem_solenoidalFreeGraph_iff`, `isClosed_solenoidalFreeGraph`).
* The standing assumptions are recorded as `Standing ν P`. None of the facts proved here uses
  `ν > 0` or `P ≤ 1`; `0 < P` is the instance `Fact (0 < P)` that `Y_q` requires, and `q ≥ 1`
  is the instance `Fact (1 ≤ q)`. Every statement therefore holds under weaker hypotheses than
  the manuscript's.

Junk values: no statement depends on Lean conventions. `testElem` has a junk branch but is
only applied to phase tests; the norm identity is stated with lower Lebesgue integrals
(`∫⁻`), which have no junk value, and its real form uses `ENNReal.toReal` of a finite
quantity (`lintegral_Ioc_lt_top`).

Status: the unit is a definition; every asserted fact above is proved. The integrated
transposition identity `⟪T₀ᵗΦ, u⟫ = ⟪Φ, T₀u⟫` for smooth `u` (integrating the Lagrange
identities over a period and over `ℝ³`) is not carried out in Lean; it is not used here, since
`T₀w` for `w ∈ Y_q` is *defined* through `driftT`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0411

open UnforcedLeray.PhaseSpace

/-! ### Standing assumptions (tex 7306–7308) -/

/-- The standing assumptions of §`sec:st18-8873` (tex 7306–7308): `ν > 0` and `0 < P ≤ 1`. -/
structure Standing (ν P : ℝ) : Prop where
  nu_pos : 0 < ν
  period_pos : 0 < P
  period_le_one : P ≤ 1

/-! ### The phase space `Y_q` and its normalised norm (tex 7313–7315) -/

section Norm

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- **Normalisation of `Y_q`** (tex 7315): `‖f‖_{Y_q}^q = P⁻¹ ∫₀ᴾ ‖f(τ)‖_{L^q}^q dτ` for
`1 ≤ q < ∞`, as an identity of extended reals. -/
theorem enorm_rpow_Yq (f : Yq P q) (hq' : q ≠ ⊤) :
    ‖f‖ₑ ^ q.toReal = ENNReal.ofReal P⁻¹ *
      ∫⁻ t in Ioc (0 : ℝ) P, ‖f (t : AddCircle P)‖ₑ ^ q.toReal := by
  rw [← lintegral_enorm_rpow_Yq f hq']
  have h1 := AddCircle.lintegral_preimage (T := P) 0 (fun τ => ‖f τ‖ₑ ^ q.toReal)
  rw [zero_add] at h1
  rw [h1, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hP.out.le), inv_mul_cancel₀ hP.out.ne',
    ENNReal.ofReal_one, one_mul]

/-- The period integral of `‖f(τ)‖^q` is finite. -/
theorem lintegral_Ioc_lt_top (f : Yq P q) (hq' : q ≠ ⊤) :
    ∫⁻ t in Ioc (0 : ℝ) P, ‖f (t : AddCircle P)‖ₑ ^ q.toReal < ⊤ := by
  have h1 := AddCircle.lintegral_preimage (T := P) 0 (fun τ => ‖f τ‖ₑ ^ q.toReal)
  rw [zero_add] at h1
  rw [h1, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul,
    lintegral_enorm_rpow_Yq f hq']
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg enorm_ne_top)

/-- **Normalisation of `Y_q`, real form** (tex 7315): for `1 ≤ q < ∞`,
`‖f‖^q = P⁻¹ ∫₀ᴾ ‖f(τ)‖_{L^q}^q dτ`; the period integral is finite (`lintegral_Ioc_lt_top`). -/
theorem norm_rpow_Yq (f : Yq P q) (hq' : q ≠ ⊤) :
    ‖f‖ ^ q.toReal =
      P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, ‖f (t : AddCircle P)‖ₑ ^ q.toReal).toReal := by
  have h := congrArg ENNReal.toReal (enorm_rpow_Yq f hq')
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hP.out.le),
    ← ENNReal.toReal_rpow, toReal_enorm] at h

end Norm

/-! ### The operators `T₀` and `L₀` (tex 7318–7319) and their transposes

The forward operators `T0`, `L0` on smooth fields, the transposes `dτT`, `radialTT`, `L0T`, the
identity `driftT_eq_transpose_parts` and the Lagrange identities `lagrange_T0`,
`lagrange_lap`, `lagrange_L0` (which certify that `driftT` and `L0T` are the formal transposes
of `T₀` and `L₀`) are in `B0411/Operators.lean`. -/

section Ops

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

omit hP in
theorem isPhaseTest_dτT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (dτT Φ) :=
  hΦ.dτ.neg

omit hP in
theorem isPhaseTest_radialTT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (radialTT Φ) :=
  hΦ.radialT.neg.sub (hΦ.const_smul (3 : ℝ))

omit hP in
theorem isPhaseTest_nuLapT {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (ν : ℝ) :
    IsPhaseTest P (nuLapT ν Φ) :=
  hΦ.lapT.const_smul ν

omit hP in
theorem isPhaseTest_L0T {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (ν : ℝ) :
    IsPhaseTest P (L0T ν Φ) :=
  (hΦ.driftT.sub (isPhaseTest_nuLapT hΦ ν)).sub (hΦ.const_smul _)

/-- **The two summands of `T₀w` are not required separately** (tex 7329–7330): if
`∂_τ w = c` and `y·∇w = d` in distributions, then `T₀w = c − ½ d`. So the graph contains
every `w` whose two summands lie in `Y_q`, but asks only for their combination. -/
theorem hasPhaseOp_driftT_of_parts {w c d : Yq P q} (hc : HasPhaseOp dτT w c)
    (hd : HasPhaseOp radialTT w d) : HasPhaseOp driftT w (c - (1 / 2 : ℂ) • d) := by
  intro Φ hΦ
  rw [driftT_eq_transpose_parts, phasePair_sub (isPhaseTest_dτT hΦ) ((isPhaseTest_radialTT hΦ).const_smul _),
    phasePair_real_smul (isPhaseTest_radialTT hΦ), hc Φ hΦ, hd Φ hΦ, map_sub, map_smul, smul_eq_mul]
  push_cast
  ring

/-- `L₀w = T₀w − νΔw − ½w` in distributions whenever `νΔw = a` and `T₀w = b`. -/
theorem hasPhaseOp_L0T {ν : ℝ} {w a b : Yq P q} (ha : HasPhaseOp (nuLapT ν) w a)
    (hb : HasPhaseOp driftT w b) : HasPhaseOp (L0T ν) w (b - a - (1 / 2 : ℂ) • w) := by
  intro Φ hΦ
  rw [L0T, phasePair_sub (hΦ.driftT.sub (isPhaseTest_nuLapT hΦ ν)) (hΦ.const_smul _),
    phasePair_sub hΦ.driftT (isPhaseTest_nuLapT hΦ ν), phasePair_real_smul hΦ, hb Φ hΦ, ha Φ hΦ,
    map_sub, map_sub, map_smul, smul_eq_mul]
  push_cast
  ring

end Ops

/-! ### The distributional graph `D_(ν,q)` (tex 7322–7327) -/

section Graph

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

variable (P) in
/-- **The distributional graph** `D_(ν,q) = {w ∈ Y_q : νΔw ∈ Y_q, T₀w ∈ Y_q}`
(`eq:free-stress-1`, tex 7322–7327), as a subspace of `Y_q`: the projection of the triple
graph `freeGraph P ν q` to its first component. -/
def D (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (Yq P q) :=
  (freeGraph P ν q).map (LinearMap.fst ℂ (Yq P q) (Yq P q × Yq P q))

/-- Membership in `D_(ν,q)`: the distributions `νΔw` and `T₀w` are elements of `Y_q`. -/
theorem mem_D {ν : ℝ} {w : Yq P q} :
    w ∈ D P ν q ↔ (∃ a, HasPhaseOp (nuLapT ν) w a) ∧ ∃ b, HasPhaseOp driftT w b := by
  constructor
  · rintro ⟨⟨w', a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(w, a, b), ⟨ha, hb⟩, rfl⟩

variable {ν : ℝ}

/-- `νΔw ∈ Y_q` for `w ∈ D_(ν,q)` (its unique representative: `nuLapD_eq`). -/
def nuLapD (w : D P ν q) : Yq P q := Classical.choose (mem_D.1 w.2).1

/-- `T₀w ∈ Y_q` for `w ∈ D_(ν,q)` (its unique representative: `T0D_eq`). -/
def T0D (w : D P ν q) : Yq P q := Classical.choose (mem_D.1 w.2).2

theorem hasPhaseOp_nuLapD (w : D P ν q) : HasPhaseOp (nuLapT ν) (w : Yq P q) (nuLapD w) :=
  Classical.choose_spec (mem_D.1 w.2).1

theorem hasPhaseOp_T0D (w : D P ν q) : HasPhaseOp driftT (w : Yq P q) (T0D w) :=
  Classical.choose_spec (mem_D.1 w.2).2

/-- `νΔw` is determined by `w`. -/
theorem nuLapD_eq {w : D P ν q} {a : Yq P q} (h : HasPhaseOp (nuLapT ν) (w : Yq P q) a) :
    nuLapD w = a :=
  hasPhaseOp_unique (hasPhaseOp_nuLapD w) h

/-- `T₀w` is determined by `w`. -/
theorem T0D_eq {w : D P ν q} {b : Yq P q} (h : HasPhaseOp driftT (w : Yq P q) b) :
    T0D w = b :=
  hasPhaseOp_unique (hasPhaseOp_T0D w) h

/-- `L₀w = T₀w − νΔw − ½w ∈ Y_q` for `w ∈ D_(ν,q)` (tex 7319). -/
def L0D (w : D P ν q) : Yq P q := T0D w - nuLapD w - (1 / 2 : ℂ) • (w : Yq P q)

/-- `L0D w` is `L₀w` in distributions. -/
theorem hasPhaseOp_L0D (w : D P ν q) : HasPhaseOp (L0T ν) (w : Yq P q) (L0D w) :=
  hasPhaseOp_L0T (hasPhaseOp_nuLapD w) (hasPhaseOp_T0D w)

/-- `L₀w` is determined by `w`. -/
theorem L0D_eq {w : D P ν q} {g : Yq P q} (h : HasPhaseOp (L0T ν) (w : Yq P q) g) :
    L0D w = g :=
  hasPhaseOp_unique (hasPhaseOp_L0D w) h

/-- `νΔ : D_(ν,q) → Y_q` as a linear map. -/
def nuLapL : D P ν q →ₗ[ℂ] Yq P q where
  toFun := nuLapD
  map_add' w w' := nuLapD_eq ((hasPhaseOp_nuLapD w).add (hasPhaseOp_nuLapD w'))
  map_smul' c w := nuLapD_eq ((hasPhaseOp_nuLapD w).smul c)

/-- `T₀ : D_(ν,q) → Y_q` as a linear map. -/
def T0L : D P ν q →ₗ[ℂ] Yq P q where
  toFun := T0D
  map_add' w w' := T0D_eq ((hasPhaseOp_T0D w).add (hasPhaseOp_T0D w'))
  map_smul' c w := T0D_eq ((hasPhaseOp_T0D w).smul c)

/-- `L₀ : D_(ν,q) → Y_q` as a linear map. -/
def L0L : D P ν q →ₗ[ℂ] Yq P q where
  toFun := L0D
  map_add' w w' := L0D_eq ((hasPhaseOp_L0D w).add (hasPhaseOp_L0D w'))
  map_smul' c w := L0D_eq ((hasPhaseOp_L0D w).smul c)

theorem nuLapL_apply (w : D P ν q) : nuLapL w = nuLapD w := rfl

theorem T0L_apply (w : D P ν q) : T0L w = T0D w := rfl

theorem L0L_apply (w : D P ν q) : L0L w = L0D w := rfl

/-- **The graph norm** `‖w‖_{D_(ν,q)} = ‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}` (tex 7326). -/
def graphNormD (w : D P ν q) : ℝ := ‖(w : Yq P q)‖ + ‖nuLapD w‖ + ‖T0D w‖

/-- The graph triple `(w, νΔw, T₀w)` lies in the triple graph `freeGraph`. -/
theorem graphTriple_mem (w : D P ν q) :
    ((w : Yq P q), nuLapD w, T0D w) ∈ freeGraph P ν q :=
  ⟨hasPhaseOp_nuLapD w, hasPhaseOp_T0D w⟩

/-- A triple lies in `freeGraph` exactly when it is the graph triple of an element of
`D_(ν,q)`. -/
theorem mem_freeGraph_iff {w a b : Yq P q} :
    (w, a, b) ∈ freeGraph P ν q ↔
      ∃ hw : w ∈ D P ν q, nuLapD ⟨w, hw⟩ = a ∧ T0D ⟨w, hw⟩ = b := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨mem_D.2 ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, nuLapD_eq ha, T0D_eq hb⟩
  · rintro ⟨hw, rfl, rfl⟩
    exact graphTriple_mem ⟨w, hw⟩

/-- **`D_(ν,q)` is the triple graph.** The graph map `w ↦ (w, νΔw, T₀w)` is a linear
isomorphism of `D_(ν,q)` onto the closed subspace `freeGraph P ν q` of `Y_q³`. -/
def graphEquiv : D P ν q ≃ₗ[ℂ] freeGraph P ν q where
  toFun w := ⟨((w : Yq P q), nuLapD w, T0D w), graphTriple_mem w⟩
  map_add' w w' := by
    ext1
    simp only [Submodule.coe_add, Prod.mk_add_mk]
    rw [← nuLapL_apply, ← T0L_apply, ← nuLapL_apply, ← T0L_apply, ← nuLapL_apply,
      ← T0L_apply, map_add, map_add]
  map_smul' c w := by
    ext1
    simp only [Submodule.coe_smul, Prod.smul_mk, RingHom.id_apply]
    rw [← nuLapL_apply, ← T0L_apply, ← nuLapL_apply, ← T0L_apply, map_smul, map_smul]
  invFun x := ⟨x.1.1, (mem_freeGraph_iff.1 x.2).1⟩
  left_inv w := rfl
  right_inv x := by
    obtain ⟨⟨w, a, b⟩, hx⟩ := x
    obtain ⟨hw, ha, hb⟩ := mem_freeGraph_iff.1 hx
    ext1
    simp only
    rw [ha, hb]

theorem graphEquiv_apply (w : D P ν q) :
    (graphEquiv w : Yq P q × Yq P q × Yq P q) = ((w : Yq P q), nuLapD w, T0D w) := rfl

/-- The graph norm of `w` is the sum norm `‖w‖ + ‖a‖ + ‖b‖` of its graph triple, which is
equivalent to the product norm on `freeGraph` (`norm_le_graphNorm`, `graphNorm_le`). -/
theorem graphNormD_eq (w : D P ν q) :
    graphNormD w = graphNorm (graphEquiv w : Yq P q × Yq P q × Yq P q) := rfl

theorem norm_graphEquiv_le (w : D P ν q) :
    ‖(graphEquiv w : Yq P q × Yq P q × Yq P q)‖ ≤ graphNormD w := by
  rw [graphNormD_eq]
  exact norm_le_graphNorm _

theorem graphNormD_le (w : D P ν q) :
    graphNormD w ≤ 3 * ‖(graphEquiv w : Yq P q × Yq P q × Yq P q)‖ := by
  rw [graphNormD_eq]
  exact graphNorm_le _

end Graph

/-! ### Solenoidal subspaces (tex 7333–7334) -/

section Sigma

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

variable (P) in
/-- `Y_{q,σ}`: the elements of `Y_q` with `div f = 0` in distributions (tex 7333–7334). -/
def Ysigma (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (Yq P q) where
  carrier := {f | IsPhaseSolenoidal f}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := fun φ _ => by simp
  smul_mem' := fun c _ hx => hx.smul c

theorem mem_Ysigma {f : Yq P q} : f ∈ Ysigma P q ↔ IsPhaseSolenoidal f := Iff.rfl

/-- `Y_{q,σ}` is a closed subspace of `Y_q`. -/
theorem isClosed_Ysigma : IsClosed (Ysigma P q : Set (Yq P q)) :=
  isClosed_isPhaseSolenoidal

variable (P) in
/-- `D_(ν,q),σ = D_(ν,q) ∩ Y_{q,σ}` (tex 7333–7334). -/
def Dsigma (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (Yq P q) := D P ν q ⊓ Ysigma P q

variable {ν : ℝ}

/-- `D_(ν,q),σ` is closed in `D_(ν,q)`, already for the (weaker) topology of `Y_q`, hence
also for the graph norm. -/
theorem isClosed_Dsigma :
    IsClosed {w : D P ν q | (w : Yq P q) ∈ Ysigma P q} :=
  isClosed_Ysigma.preimage continuous_subtype_val

/-- The graph map carries `D_(ν,q),σ` onto the solenoidal triple graph, which is closed in
`Y_q³` (`isClosed_solenoidalFreeGraph`). -/
theorem mem_solenoidalFreeGraph_iff {w a b : Yq P q} :
    (w, a, b) ∈ solenoidalFreeGraph P ν q ↔
      ∃ hw : w ∈ Dsigma P ν q, nuLapD ⟨w, hw.1⟩ = a ∧ T0D ⟨w, hw.1⟩ = b := by
  constructor
  · rintro ⟨hx, hdiv⟩
    obtain ⟨hw, ha, hb⟩ := mem_freeGraph_iff.1 hx
    exact ⟨⟨hw, hdiv⟩, ha, hb⟩
  · rintro ⟨hw, ha, hb⟩
    exact ⟨mem_freeGraph_iff.2 ⟨hw.1, ha, hb⟩, hw.2⟩

theorem isClosed_solenoidalFreeGraph' :
    IsClosed (solenoidalFreeGraph P ν q : Set (Yq P q × Yq P q × Yq P q)) :=
  isClosed_solenoidalFreeGraph ν

end Sigma

/-! ### The unit, bundled -/

section Bundle

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq : Fact (1 ≤ q)]

/-- **B0411 (`eq:free-stress-1`, tex 7304–7337), bundled.** For every `ν` and every
`1 ≤ q ≤ ∞` (so in particular under the standing assumptions `ν > 0`, `0 < P ≤ 1`):
1. the `Y_q` norm is the period-normalised one, `‖f‖^q = P⁻¹ ∫₀ᴾ ‖f(τ)‖^q dτ`, for `q < ∞`;
2. `D_(ν,q) = {w ∈ Y_q : νΔw ∈ Y_q, T₀w ∈ Y_q}` in distributions;
3. `νΔw`, `T₀w` and `L₀w = T₀w − νΔw − ½w` are uniquely determined elements of `Y_q` for
   `w ∈ D_(ν,q)`, and the graph norm is `‖w‖ + ‖νΔw‖ + ‖T₀w‖`;
4. `T₀w ∈ Y_q` whenever `∂_τ w, y·∇w ∈ Y_q`, but only the combination is required;
5. `Y_{q,σ}` is closed in `Y_q`, and `D_(ν,q),σ` is closed in `D_(ν,q)`. -/
theorem B0411_spec (ν : ℝ) :
    (∀ f : Yq P q, q ≠ ⊤ →
      ‖f‖ ^ q.toReal =
        P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, ‖f (t : AddCircle P)‖ₑ ^ q.toReal).toReal) ∧
    (∀ w : Yq P q,
      w ∈ D P ν q ↔ (∃ a, HasPhaseOp (nuLapT ν) w a) ∧ ∃ b, HasPhaseOp driftT w b) ∧
    (∀ w : D P ν q, ∀ a b g : Yq P q, HasPhaseOp (nuLapT ν) (w : Yq P q) a →
      HasPhaseOp driftT (w : Yq P q) b → HasPhaseOp (L0T ν) (w : Yq P q) g →
      nuLapD w = a ∧ T0D w = b ∧ L0D w = g ∧ g = b - a - (1 / 2 : ℂ) • (w : Yq P q) ∧
        graphNormD w = ‖(w : Yq P q)‖ + ‖a‖ + ‖b‖) ∧
    (∀ w c d : Yq P q, HasPhaseOp dτT w c → HasPhaseOp radialTT w d →
      HasPhaseOp driftT w (c - (1 / 2 : ℂ) • d)) ∧
    IsClosed (Ysigma P q : Set (Yq P q)) ∧
    IsClosed {w : D P ν q | (w : Yq P q) ∈ Ysigma P q} := by
  refine ⟨fun f hq' => norm_rpow_Yq f hq', fun w => mem_D, ?_,
    fun w c d hc hd => hasPhaseOp_driftT_of_parts hc hd, isClosed_Ysigma, isClosed_Dsigma⟩
  intro w a b g ha hb hg
  have h1 := nuLapD_eq ha
  have h2 := T0D_eq hb
  have h3 := L0D_eq hg
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rw [← h3, L0D, h1, h2]
  · rw [graphNormD, h1, h2]

end Bundle

end UnforcedLeray.B0411
