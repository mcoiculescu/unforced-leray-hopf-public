import UnforcedLeray.Units.B0412.Action
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0281

/-!
# Unit B0412 (`background:eq:2.3`): the correction graph `X_{q₀}`

Blueprint unit `B0412`, `paper/main.tex` lines 5085–5091 (§`sec:st18-5857`), with
`q₀ = 11/4` from (2.1) (tex 5072, unit B0281) and the class (2.2) (tex 5081–5084, unit B0416):

> The correction graph is
> `X_{q₀} = {w ∈ Y_{q₀,div} : νΔw, T₀w ∈ Y_{q₀}}`,
> `‖w‖_{X_{q₀}} = ‖w‖_{Y_{q₀}} + ‖νΔw‖_{Y_{q₀}} + ‖T₀w‖_{Y_{q₀}}`.
> Phase norms use the period average; no separate phase or dilation derivative is imposed.

The fields are restricted to the class (2.2) (tex 5080–5083), the derivatives are
distributional and `w` is periodic (tex 3609). The unrestricted version `X̃_p`, the same graph
without the symmetry and with the norm of `X_p` (tex 3593–3604, 5764–5765), is used later
(tex 5764–5828, B0413).

## Formalization (decision D2; built on `Lib/PhaseSpace` and B0411)

| Manuscript | Lean |
|---|---|
| `Y_q`, period average | `PhaseSpace.Yq P q`; `B0411.norm_rpow_Yq` (`‖f‖^q = P⁻¹∫₀ᴾ‖f(τ)‖^q`) |
| `q₀ = 11/4` | `q0E = ENNReal.ofReal B0281.q0` (`q0E_toReal`, `one_lt_q0E`, `q0E_lt_three`) |
| `Y_{q,div}` | `B0411.Ysigma P q` (`div w = 0` in distributions) |
| `νΔw, T₀w ∈ Y_q` in distributions | `HasPhaseOp (nuLapT ν) w a`, `HasPhaseOp driftT w b` |
| `X̃_p` (no symmetry) | `Xtilde P ν q = B0411.Dsigma P ν q` |
| class (2.2) | `Osym P q`, `IsOInvariant` (file `B0412/Action.lean`) |
| `X_{q}`, `X_{q₀}` | `X P ν q = Xtilde P ν q ⊓ Osym P q`, `Xq0 P ν = X P ν q0E` |
| `νΔw`, `T₀w` on `X` | `nuLapX`, `T0X` (linear; unique: `nuLapX_eq`, `T0X_eq`) |
| `‖w‖_X` | `normX w = ‖w‖ + ‖νΔw‖ + ‖T₀w‖`; `normXtilde` on `X̃` |
| graph triples | `XGraph P ν q ⊆ Y_q³` (closed, complete; `mem_XGraph_iff`) |

* `mem_X` lists the only conditions: `div w = 0`, `νΔw ∈ Y_q`, `T₀w ∈ Y_q` (the combined drift,
  tested through `driftT`, never `∂_τ w` or `y·∇w` separately), and `𝒪`-invariance. No
  boundary or decay condition is imposed.
* `normX` is a norm (`normX_add_le`, `normX_smul`, `normX_eq_zero_iff`) and it is complete
  (`normX_complete`: a `normX`-Cauchy sequence in `X` converges in `normX` to an element of
  `X`), because convergence of `w`, `νΔw`, `T₀w` in `Y_q` passes each distributional identity,
  the divergence condition and the `𝒪`-invariance to the limit. `normXtilde_complete` is the
  same for `X̃`.
* `normX w = normXtilde w` for `w ∈ X ⊆ X̃` (`normX_eq_normXtilde`): `X̃_p` carries "the norm
  of `X_p`" (tex 5765).

Scalars are complex, as in B0411 (decision D2); the real background corrections of Theorem B3
are the elements of `X_{q₀}` with real values, so nothing is lost. The definitions are made
for every `ν` and every exponent `1 ≤ q ≤ ∞` and period `P > 0`; the manuscript's standing
ranges (`ν > 0`, `0 < P ≤ 1`, `1 < p < 3`, `B0411.Standing`) are not used by any fact proved
here, so every statement holds under weaker hypotheses than the manuscript's.

Junk values: `q0E` is `ENNReal.ofReal (11/4)`, a genuine finite exponent; norms have no junk
value; the period-average identity uses lower Lebesgue integrals (`∫⁻`).

Status: the unit is a definition, and every asserted fact above is proved. Theorem A is not
proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0412

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ### The exponent `q₀ = 11/4` (tex 5072) -/

/-- The exponent `q₀ = 11/4` of (2.1) (tex 5072, `B0281.q0`) as a Lebesgue exponent. -/
def q0E : ℝ≥0∞ := ENNReal.ofReal B0281.q0

instance q0E_fact : Fact (1 ≤ q0E) :=
  ⟨ENNReal.one_le_ofReal.2 (by norm_num [B0281.q0])⟩

theorem q0E_toReal : q0E.toReal = 11 / 4 := by
  rw [q0E, ENNReal.toReal_ofReal (by norm_num [B0281.q0]), B0281.q0]

theorem q0E_ne_top : q0E ≠ ⊤ := ENNReal.ofReal_ne_top

theorem one_lt_q0E : 1 < q0E := ENNReal.one_lt_ofReal.2 (by norm_num [B0281.q0])

theorem q0E_lt_three : q0E < 3 := by
  rw [q0E, ← ENNReal.ofReal_ofNat 3]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num [B0281.q0])

/-! ### The spaces `X̃_q` and `X_q` (tex 5085–5091, 3593–3604) -/

section Spaces

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (P) in
/-- **The unrestricted graph `X̃_q`** (tex 3593–3604, 5764–5765): `w ∈ Y_{q,σ}` with
`νΔw, T₀w ∈ Y_q` in distributions, no symmetry. It is B0411's `D_(ν,q),σ`. -/
def Xtilde (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (Yq P q) := Dsigma P ν q

variable (P) in
/-- **The correction graph `X_q`** (`background:eq:2.3`, tex 5085–5088): the elements of `X̃_q`
in the class (2.2), `g · w = w` for every `g ∈ 𝒪`. -/
def X (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (Yq P q) := Xtilde P ν q ⊓ Osym P q

variable (P) in
/-- **`X_{q₀}`**, `q₀ = 11/4` (tex 5072, 5085–5088). -/
abbrev Xq0 (ν : ℝ) : Submodule ℂ (Yq P q0E) := X P ν q0E

variable {ν : ℝ}

/-- Membership in `X̃_q`: `div w = 0`, `νΔw ∈ Y_q` and `T₀w ∈ Y_q`, all in distributions. -/
theorem mem_Xtilde {w : Yq P q} :
    w ∈ Xtilde P ν q ↔
      IsPhaseSolenoidal w ∧ (∃ a, HasPhaseOp (nuLapT ν) w a) ∧ ∃ b, HasPhaseOp driftT w b := by
  rw [Xtilde, Dsigma, Submodule.mem_inf, mem_D, mem_Ysigma]
  constructor
  · rintro ⟨⟨ha, hb⟩, hs⟩
    exact ⟨hs, ha, hb⟩
  · rintro ⟨hs, ha, hb⟩
    exact ⟨⟨ha, hb⟩, hs⟩

/-- **Membership in `X_q`** (tex 5085–5091): `div w = 0`, `νΔw ∈ Y_q`, `T₀w ∈ Y_q` in
distributions, and `w` in the class (2.2). These are the only conditions: no separate phase
derivative `∂_τ w` or dilation derivative `y·∇w` is imposed. -/
theorem mem_X {w : Yq P q} :
    w ∈ X P ν q ↔
      IsPhaseSolenoidal w ∧ (∃ a, HasPhaseOp (nuLapT ν) w a) ∧
        (∃ b, HasPhaseOp driftT w b) ∧ IsOInvariant w := by
  rw [X, Submodule.mem_inf, mem_Xtilde, mem_Osym]
  constructor
  · rintro ⟨⟨hs, ha, hb⟩, hO⟩
    exact ⟨hs, ha, hb, hO⟩
  · rintro ⟨hs, ha, hb, hO⟩
    exact ⟨⟨hs, ha, hb⟩, hO⟩

theorem Xtilde_le_D : Xtilde P ν q ≤ D P ν q := inf_le_left

theorem X_le_Xtilde : X P ν q ≤ Xtilde P ν q := inf_le_left

theorem X_le_D : X P ν q ≤ D P ν q := X_le_Xtilde.trans Xtilde_le_D

theorem X_le_Osym : X P ν q ≤ Osym P q := inf_le_right

/-! ### The operators and the graph norm (tex 5087) -/

/-- `X̃_q ⊆ D_(ν,q)`. -/
def XtildeToD : Xtilde P ν q →ₗ[ℂ] D P ν q := Submodule.inclusion Xtilde_le_D

/-- `X_q ⊆ X̃_q`. -/
def XToXtilde : X P ν q →ₗ[ℂ] Xtilde P ν q := Submodule.inclusion X_le_Xtilde

/-- `X_q ⊆ D_(ν,q)`. -/
def XToD : X P ν q →ₗ[ℂ] D P ν q := Submodule.inclusion X_le_D

/-- `νΔ : X_q → Y_q`. -/
def nuLapX : X P ν q →ₗ[ℂ] Yq P q := nuLapL.comp XToD

/-- `T₀ : X_q → Y_q`. -/
def T0X : X P ν q →ₗ[ℂ] Yq P q := T0L.comp XToD

theorem hasPhaseOp_nuLapX (w : X P ν q) : HasPhaseOp (nuLapT ν) (w : Yq P q) (nuLapX w) :=
  hasPhaseOp_nuLapD (XToD w)

theorem hasPhaseOp_T0X (w : X P ν q) : HasPhaseOp driftT (w : Yq P q) (T0X w) :=
  hasPhaseOp_T0D (XToD w)

/-- `νΔw` is determined by `w`. -/
theorem nuLapX_eq {w : X P ν q} {a : Yq P q} (h : HasPhaseOp (nuLapT ν) (w : Yq P q) a) :
    nuLapX w = a :=
  nuLapD_eq (w := XToD w) h

/-- `T₀w` is determined by `w`. -/
theorem T0X_eq {w : X P ν q} {b : Yq P q} (h : HasPhaseOp driftT (w : Yq P q) b) :
    T0X w = b :=
  T0D_eq (w := XToD w) h

/-- **The norm of `X_q`** (tex 5087): `‖w‖_X = ‖w‖_{Y_q} + ‖νΔw‖_{Y_q} + ‖T₀w‖_{Y_q}`. -/
def normX (w : X P ν q) : ℝ := ‖(w : Yq P q)‖ + ‖nuLapX w‖ + ‖T0X w‖

/-- The norm of `X̃_q` (tex 5765, "the norm of `X_p`"): the graph norm of B0411. -/
def normXtilde (w : Xtilde P ν q) : ℝ := graphNormD (XtildeToD w)

theorem normX_eq_graphNormD (w : X P ν q) : normX w = graphNormD (XToD w) := rfl

/-- `X_q ⊆ X̃_q` isometrically: `X̃_q` carries the norm of `X_q`. -/
theorem normX_eq_normXtilde (w : X P ν q) : normX w = normXtilde (XToXtilde w) := rfl

/-- The norm computed from any distributional representatives of `νΔw` and `T₀w`. -/
theorem normX_eq {w : X P ν q} {a b : Yq P q} (ha : HasPhaseOp (nuLapT ν) (w : Yq P q) a)
    (hb : HasPhaseOp driftT (w : Yq P q) b) : normX w = ‖(w : Yq P q)‖ + ‖a‖ + ‖b‖ := by
  rw [normX, nuLapX_eq ha, T0X_eq hb]

theorem normX_nonneg (w : X P ν q) : 0 ≤ normX w := by
  unfold normX
  positivity

theorem norm_le_normX (w : X P ν q) : ‖(w : Yq P q)‖ ≤ normX w := by
  unfold normX
  linarith [norm_nonneg (nuLapX w), norm_nonneg (T0X w)]

theorem normX_add_le (w w' : X P ν q) : normX (w + w') ≤ normX w + normX w' := by
  unfold normX
  rw [map_add, map_add, Submodule.coe_add]
  linarith [norm_add_le (w : Yq P q) w', norm_add_le (nuLapX w) (nuLapX w'),
    norm_add_le (T0X w) (T0X w')]

theorem normX_smul (c : ℂ) (w : X P ν q) : normX (c • w) = ‖c‖ * normX w := by
  unfold normX
  rw [map_smul, map_smul, Submodule.coe_smul, norm_smul, norm_smul, norm_smul]
  ring

theorem normX_eq_zero_iff (w : X P ν q) : normX w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h1 : ‖(w : Yq P q)‖ = 0 :=
      le_antisymm (h ▸ norm_le_normX w) (norm_nonneg _)
    exact Subtype.ext (by simpa using h1)
  · rintro rfl
    simp [normX]

/-! ### Graph triples, closedness and completeness (tex 3609–3611, 5085–5091) -/

variable (P) in
/-- The graph triples `(w, νΔw, T₀w)` of `X_q`, as a subspace of `Y_q³`. -/
def XGraph (ν : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule ℂ (Yq P q × Yq P q × Yq P q) :=
  solenoidalFreeGraph P ν q ⊓ (Osym P q).comap (LinearMap.fst ℂ (Yq P q) (Yq P q × Yq P q))

theorem mem_XGraph_iff {w a b : Yq P q} :
    (w, a, b) ∈ XGraph P ν q ↔ ∃ hw : w ∈ X P ν q, nuLapX ⟨w, hw⟩ = a ∧ T0X ⟨w, hw⟩ = b := by
  constructor
  · rintro ⟨hx, hO⟩
    obtain ⟨hw, ha, hb⟩ := mem_solenoidalFreeGraph_iff.1 hx
    exact ⟨⟨hw, hO⟩, ha, hb⟩
  · rintro ⟨hw, ha, hb⟩
    exact ⟨mem_solenoidalFreeGraph_iff.2 ⟨hw.1, ha, hb⟩, hw.2⟩

/-- The graph triples of `X_q` form a closed subspace of `Y_q³`. -/
theorem isClosed_XGraph : IsClosed (XGraph P ν q : Set (Yq P q × Yq P q × Yq P q)) :=
  (isClosed_solenoidalFreeGraph ν).inter (isClosed_Osym.preimage continuous_fst)

instance XGraph_completeSpace : CompleteSpace (XGraph P ν q) :=
  isClosed_XGraph.completeSpace_coe

/-- Completeness of a graph `M = D_(ν,q) ∩ C` cut out of `D_(ν,q)` by a closed condition `C`
on `w`: a sequence that is Cauchy for the graph norm converges in the graph norm, because
convergence of `w`, `νΔw`, `T₀w` in `Y_q` passes each distributional identity and the
condition `C` to the limit (tex 3609–3611). -/
theorem complete_of_isClosed {M : Submodule ℂ (Yq P q)} (hMD : M ≤ D P ν q) {C : Set (Yq P q)}
    (hC : IsClosed C) (hMC : ∀ w, w ∈ M ↔ w ∈ D P ν q ∧ w ∈ C) (w : ℕ → M)
    (hw : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      graphNormD (Submodule.inclusion hMD (w m - w n)) < ε) :
    ∃ w' : M, Tendsto (fun n => graphNormD (Submodule.inclusion hMD (w n - w'))) atTop (𝓝 0) := by
  have key : ∀ u v : M, graphNormD (Submodule.inclusion hMD (u - v)) =
      graphNorm ((graphEquiv (Submodule.inclusion hMD u) : Yq P q × Yq P q × Yq P q) -
        (graphEquiv (Submodule.inclusion hMD v) : Yq P q × Yq P q × Yq P q)) := by
    intro u v
    rw [graphNormD_eq, map_sub, map_sub, Submodule.coe_sub]
  set t : ℕ → Yq P q × Yq P q × Yq P q :=
    fun n => (graphEquiv (Submodule.inclusion hMD (w n)) : Yq P q × Yq P q × Yq P q) with ht
  have hcau : CauchySeq t := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hw ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 := hN m hm n hn
    rw [key] at h1
    exact (norm_le_graphNorm _).trans_lt h1
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcau
  have haG : a ∈ freeGraph P ν q :=
    (isClosed_freeGraph ν).mem_of_tendsto ha
      (Eventually.of_forall fun n => (graphEquiv (Submodule.inclusion hMD (w n))).2)
  have haC : a.1 ∈ C :=
    hC.mem_of_tendsto ((continuous_fst.tendsto a).comp ha)
      (Eventually.of_forall fun n => ((hMC _).1 (w n).2).2)
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨hD, h2, h3⟩ := B0411.mem_freeGraph_iff.1 haG
  refine ⟨⟨a1, (hMC a1).2 ⟨hD, haC⟩⟩, ?_⟩
  have hpt : (graphEquiv (Submodule.inclusion hMD ⟨a1, (hMC a1).2 ⟨hD, haC⟩⟩) :
      Yq P q × Yq P q × Yq P q) = (a1, a2, a3) := by
    rw [graphEquiv_apply]
    exact Prod.ext rfl (Prod.ext h2 h3)
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.1 ha).const_mul 3
  rw [mul_zero] at hlim
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · unfold graphNormD
    positivity
  · rw [key, hpt]
    exact graphNorm_le _

/-- **`X_q` is complete for its norm** (tex 3609–3611, 5085–5091): a sequence of `X_q` that is
Cauchy for `‖·‖_X` converges for `‖·‖_X` to an element of `X_q`. -/
theorem normX_complete (w : ℕ → X P ν q)
    (hw : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, normX (w m - w n) < ε) :
    ∃ w' : X P ν q, Tendsto (fun n => normX (w n - w')) atTop (𝓝 0) :=
  complete_of_isClosed X_le_D (isClosed_Ysigma.inter isClosed_Osym)
    (fun _ => ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩) w hw

/-- **`X̃_q` is complete for its norm** (tex 3609–3611, 5764–5765). -/
theorem normXtilde_complete (w : ℕ → Xtilde P ν q)
    (hw : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, normXtilde (w m - w n) < ε) :
    ∃ w' : Xtilde P ν q, Tendsto (fun n => normXtilde (w n - w')) atTop (𝓝 0) :=
  complete_of_isClosed Xtilde_le_D isClosed_Ysigma (fun _ => Iff.rfl) w hw

/-- The class (2.2) is closed in `Y_q`, so `X_q` is closed in `X̃_q`, already for the weaker
topology of `Y_q`. -/
theorem isClosed_X_in_Xtilde :
    IsClosed {w : Xtilde P ν q | (w : Yq P q) ∈ Osym P q} :=
  isClosed_Osym.preimage continuous_subtype_val

end Spaces

/-! ### The unit, bundled -/

section Bundle

variable {P : ℝ} [Fact (0 < P)]

/-- **B0412 (`background:eq:2.3`, tex 5085–5091), bundled**, for `q₀ = 11/4` and every `ν`
(in particular under the standing assumptions `ν > 0`, `0 < P ≤ 1`):
1. `q₀ = 11/4` lies in `(1, 3)`;
2. the phase norm is the period average, `‖f‖^{q₀} = P⁻¹ ∫₀ᴾ ‖f(τ)‖^{q₀} dτ`;
3. `X_{q₀} = {w ∈ Y_{q₀,div} : νΔw, T₀w ∈ Y_{q₀}}` in the class (2.2), with no other
   condition (no separate phase or dilation derivative);
4. the class (2.2) is `g w(τ)(g⁻¹y) = w(τ)(y)` for `g ∈ 𝒪`, a.e. `τ`, a.e. `y`;
5. `νΔw`, `T₀w` are determined by `w ∈ X_{q₀}`, and
   `‖w‖_X = ‖w‖_{Y_{q₀}} + ‖νΔw‖_{Y_{q₀}} + ‖T₀w‖_{Y_{q₀}}`;
6. `‖·‖_X` is a norm on `X_{q₀}`, complete;
7. `X_{q₀} ⊆ X̃_{q₀}` with the same norm, and `X̃_{q₀}` is complete. -/
theorem B0412_spec (ν : ℝ) :
    (1 < q0E ∧ q0E < 3 ∧ q0E.toReal = 11 / 4) ∧
    (∀ f : Yq P q0E,
      ‖f‖ ^ q0E.toReal =
        P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, ‖f (t : AddCircle P)‖ₑ ^ q0E.toReal).toReal) ∧
    (∀ w : Yq P q0E, w ∈ Xq0 P ν ↔
      IsPhaseSolenoidal w ∧ (∃ a, HasPhaseOp (nuLapT ν) w a) ∧
        (∃ b, HasPhaseOp driftT w b) ∧ IsOInvariant w) ∧
    (∀ w : Yq P q0E, IsOInvariant w ↔ ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        ∀ᵐ y ∂(volume : Measure Space), gC g (w τ (g.symm y)) = w τ y) ∧
    (∀ w : Xq0 P ν, ∀ a b : Yq P q0E, HasPhaseOp (nuLapT ν) (w : Yq P q0E) a →
      HasPhaseOp driftT (w : Yq P q0E) b →
        nuLapX w = a ∧ T0X w = b ∧ normX w = ‖(w : Yq P q0E)‖ + ‖a‖ + ‖b‖) ∧
    (∀ w w' : Xq0 P ν, normX (w + w') ≤ normX w + normX w') ∧
    (∀ (c : ℂ) (w : Xq0 P ν), normX (c • w) = ‖c‖ * normX w) ∧
    (∀ w : Xq0 P ν, normX w = 0 ↔ w = 0) ∧
    (∀ w : ℕ → Xq0 P ν, (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, normX (w m - w n) < ε) →
      ∃ w' : Xq0 P ν, Tendsto (fun n => normX (w n - w')) atTop (𝓝 0)) ∧
    (∀ w : Xq0 P ν, normX w = normXtilde (XToXtilde w)) ∧
    (∀ w : ℕ → Xtilde P ν q0E,
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, normXtilde (w m - w n) < ε) →
      ∃ w' : Xtilde P ν q0E, Tendsto (fun n => normXtilde (w n - w')) atTop (𝓝 0)) :=
  ⟨⟨one_lt_q0E, q0E_lt_three, q0E_toReal⟩, fun f => norm_rpow_Yq f q0E_ne_top,
    fun _ => mem_X, isOInvariant_iff,
    fun _ _ _ ha hb => ⟨nuLapX_eq ha, T0X_eq hb, normX_eq ha hb⟩, normX_add_le, normX_smul,
    normX_eq_zero_iff, normX_complete, normX_eq_normXtilde, normXtilde_complete⟩

end Bundle

end UnforcedLeray.B0412
