import UnforcedLeray.Units.B0063.Pairing
import UnforcedLeray.Lib.Semigroups.ExpSemigroup

/-!
# B0063: strong continuity and generator of the transport group on `H^j_M`

Blueprint unit **B0063** (lemma, unlabeled), `paper/main.tex` lines 1238–1243, in the proof of
"Generator realization and resolvent estimates" (§"The weighted generator and its discrete
growing spectrum"). Dependency: **B0062** (`eq:st18-t00051`, tex 1228–1237): the group
`T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)` (`eq:st18-t00050`) on `H^j_M` with `‖T(t)‖ ≤ C_j(1+|t|)^j`


**Statement (tex 1238–1243).** Density of compact smooth functions proves strong continuity. Its
generator is exactly `-D_E` with distributional domain `{f : D_E f ∈ H^j_M}`. One direction
follows by distributional differentiation of `eq:st18-t00050`. For the converse, if
`D_E f ∈ H^j_M`, the distributional flow identity is `T(t)f - f = -∫_0^t T(s) D_E f ds`; it follows
first by testing against compact smooth functions and changing variables in the flow; both
sides are in `H^j_M`, so the identity holds there. Strong continuity makes its quotient tend to
`-D_E f`.

**Formalization.**
* `D_E = Ω∂_ϑ` and its distributional domain are those of unit B0009
  (`UnforcedLeray.B0009.HasWeakTransport`, `transportDomain`, `transportLM`,
  `paper/main.tex:664-670`): `HasWeakTransport f g` means `∫ f Ω∂_ϑφ = -∫ g φ` for all test
  functions `φ`. `DE j M` is `D_E` as a partial linear operator on `H^j_M` with domain
  `{f ∈ H^j_M : D_E f ∈ H^j_M}`.
* The generator of the group (`generator j M`) is defined as in Engel–Nagel (Def. II.1.2):
  `A f = lim_{h ↓ 0} (T(h)f - f)/h` (a right derivative at `0`, `derivWithin … (Ici 0) 0`), on
  the subspace `generatorDomain j M` of `f` for which the limit exists;
  `hasDerivWithinAt_iff_tendsto_quotient` identifies it with the difference-quotient limit.
* **Strong continuity**: `continuous_transport_apply` (helper `B0063/Strong.lean`). The manuscript
  invokes density of `C_c^∞` in `H^j_M`; the library has no such density theorem, so the proof
  uses B0062's iterated chain rule and the continuity of `g ↦ g ∘ Φ_t` on
  `L²(⟨y⟩^{2M}dy)` (Mathlib, by density of simple functions).
* **Generator**: `generator_eq_neg_DE : generator j M = -DE j M` (equal domains and values), and
  the two-sided form `hasDerivAt_transport_iff`: `d/dt|_{t=0} T(t)f = -g` in `H^j_M` iff
  `D_E f = g` distributionally.
* The flow identity `transport_sub_eq_integral`: `T(t)f - f = -∫_0^t T(s) D_E f ds` (Bochner
  integral in `H^j_M`), proved by testing (helper `B0063/Pairing.lean`).
* `transportSemigroup`: the forward group as an `ExpSemigroup` (INF07,
  `Lib/Semigroups/ExpSemigroup.lean`) with growth bound `C_j e^{jt}`.

No hypothesis on `M` is needed (the manuscript works with `M > 1`); `j ≥ 0` is arbitrary.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0062

namespace UnforcedLeray.B0063

variable {j : ℕ} {M : ℝ}

theorem uniqueDiffWithinAt_Ici_zero : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 :=
  uniqueDiffOn_Ici 0 0 self_mem_Ici

/-! ### `D_E` and the generator as partial operators -/

variable (j M) in
/-- `D_E = Ω∂_ϑ` on `H^j_M` with its distributional domain `{f ∈ H^j_M : D_E f ∈ H^j_M}`
(unit B0009, `paper/main.tex:667`, `1239`). -/
def DE : HjM j M →ₗ.[ℂ] HjM j M := ⟨B0009.transportDomain j M, B0009.transportLM j M⟩

variable (j M) in
/-- The domain of the generator of the transport group: the `f ∈ H^j_M` for which
`(T(h)f - f)/h` converges in `H^j_M` as `h ↓ 0`. -/
def generatorDomain : Submodule ℂ (HjM j M) where
  carrier := {F | DifferentiableWithinAt ℝ (fun t => transport j M t F) (Ici 0) 0}
  add_mem' := by
    intro F F' hF hF'
    have e : (fun t => transport j M t (F + F')) =
        fun t => transport j M t F + transport j M t F' := funext fun t => map_add _ _ _
    simp only [Set.mem_ofPred_eq, e]
    exact hF.add hF'
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact differentiableWithinAt_const _
  smul_mem' := by
    intro c F hF
    have e : (fun t => transport j M t (c • F)) = fun t => c • transport j M t F :=
      funext fun t => map_smul _ _ _
    simp only [Set.mem_ofPred_eq, e]
    exact hF.const_smul c

variable (j M) in
/-- **The generator of the transport group** `A f = lim_{h ↓ 0} (T(h)f - f)/h`
(Engel–Nagel Def. II.1.2), as a partial linear operator on `H^j_M`. -/
def generator : HjM j M →ₗ.[ℂ] HjM j M where
  domain := generatorDomain j M
  toFun :=
    { toFun := fun F => derivWithin (fun t => transport j M t F.1) (Ici 0) 0
      map_add' := fun F F' => by
        have h := (F.2.hasDerivWithinAt.add F'.2.hasDerivWithinAt).derivWithin
          uniqueDiffWithinAt_Ici_zero
        have e : (fun t => transport j M t ((F + F' : generatorDomain j M) : HjM j M)) =
            fun t => transport j M t F.1 + transport j M t F'.1 := funext fun t => map_add _ _ _
        simp only [e]
        exact h
      map_smul' := fun c F => by
        have h := (F.2.hasDerivWithinAt.const_smul c).derivWithin uniqueDiffWithinAt_Ici_zero
        have e : (fun t => transport j M t ((c • F : generatorDomain j M) : HjM j M)) =
            fun t => c • transport j M t F.1 := funext fun t => map_smul _ _ _
        simp only [e, RingHom.id_apply]
        exact h }

/-- The right derivative at `0` is the limit of the difference quotients `(T(h)f - f)/h`,
`h ↓ 0`. -/
theorem hasDerivWithinAt_iff_tendsto_quotient (F G : HjM j M) :
    HasDerivWithinAt (fun t => transport j M t F) G (Ici 0) 0 ↔
      Tendsto (fun h : ℝ => h⁻¹ • (transport j M h F - F)) (𝓝[>] 0) (𝓝 G) := by
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext x
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hs]
  have e : slope (fun t => transport j M t F) 0 = fun h : ℝ => h⁻¹ • (transport j M h F - F) := by
    funext h
    rw [slope_def_module, sub_zero, transport_zero, ContinuousLinearMap.id_apply]
  rw [e]

/-! ### One direction: distributional differentiation of the group formula -/

/-- If `(T(h)f - f)/h → -g` as `h ↓ 0`, then `D_E f = g` distributionally. -/
theorem hasWeakTransport_of_hasDerivWithinAt {F G : HjM j M}
    (h : HasDerivWithinAt (fun t => transport j M t F) (-G) (Ici 0) 0) :
    B0009.HasWeakTransport F.value G.value := by
  intro φ hφ
  set ℓ := pairing j M ⟨φ, hφ⟩
  have h1 : HasDerivWithinAt (fun t => ℓ (transport j M t F)) (ℓ (-G)) (Ici 0) 0 := by
    exact (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) h
  have h2 : HasDerivAt (fun t => ℓ (transport j M t F))
      (∫ x, F.value x * B0009.transportOf φ (flow (-0) x)) 0 := by
    have := hasDerivAt_integral_comp_flow_neg (locallyIntegrable_L2w M F.value) hφ 0
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact pairing_transport ⟨φ, hφ⟩ t F
  have := uniqueDiffWithinAt_Ici_zero.eq_deriv _ h1 h2.hasDerivWithinAt
  rw [map_neg, pairing_apply] at this
  simp only [neg_zero, flow_zero] at this
  exact this.symm

/-! ### The converse: the flow identity -/

/-- **The flow identity** (`paper/main.tex:1240-1242`): if `D_E f = g ∈ H^j_M` distributionally,
then `T(t)f - f = -∫_0^t T(s) g ds` in `H^j_M` (Bochner integral of the continuous orbit). -/
theorem transport_sub_eq_integral {F G : HjM j M} (hFG : B0009.HasWeakTransport F.value G.value)
    (t : ℝ) : transport j M t F - F = -∫ s in (0 : ℝ)..t, transport j M s G := by
  apply eq_of_pairing
  intro φ
  set ℓ := pairing j M φ
  have hcont : Continuous fun s => transport j M s G := continuous_transport_apply G
  rw [map_sub, map_neg, ← ℓ.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 t)]
  have hP : ∀ s, HasDerivAt (fun τ => ℓ (transport j M τ F)) (-ℓ (transport j M s G)) s := by
    intro s
    have h := hasDerivAt_integral_comp_flow_neg (locallyIntegrable_L2w M F.value) φ.2 s
    have e1 : (fun τ => ℓ (transport j M τ F)) = fun τ => ∫ x, F.value x * φ.1 (flow (-τ) x) :=
      funext fun τ => pairing_transport φ τ F
    rw [e1]
    refine HasDerivAt.congr_deriv h ?_
    have hψ : IsTestFn univ (fun y => φ.1 (flow (-s) y)) := (smoothMP_flow (-s)).testFn_comp φ.2
    have hw := hFG _ hψ
    simp_rw [transportOf_comp_flow_neg φ.2.smooth s] at hw
    rw [hw, pairing_transport]
  have hint : IntervalIntegrable (fun s => -ℓ (transport j M s G)) volume 0 t :=
    ((ℓ.continuous.comp hcont).neg).intervalIntegrable 0 t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hP s) hint
  rw [intervalIntegral.integral_neg] at hftc
  have h0 : ℓ (transport j M 0 F) = ℓ F := by
    rw [transport_zero]
    rfl
  rw [h0] at hftc
  exact hftc.symm

/-- If `D_E f = g ∈ H^j_M` distributionally, then `t ↦ T(t)f` is differentiable at `0` with
derivative `-g` (two-sided). -/
theorem hasDerivAt_transport_of_hasWeakTransport {F G : HjM j M}
    (hFG : B0009.HasWeakTransport F.value G.value) :
    HasDerivAt (fun t => transport j M t F) (-G) 0 := by
  have hcont := continuous_transport_apply G
  have hI := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt
  rw [transport_zero, ContinuousLinearMap.id_apply] at hI
  have e : (fun t => transport j M t F) = fun t => F - ∫ s in (0 : ℝ)..t, transport j M s G := by
    funext t
    have h := transport_sub_eq_integral hFG t
    calc transport j M t F = (transport j M t F - F) + F := by abel
      _ = F - ∫ s in (0 : ℝ)..t, transport j M s G := by rw [h]; abel
  rw [e]
  exact hI.const_sub F

/-! ### The generator is exactly `-D_E` -/

/-- **Generator, pointwise form** (`paper/main.tex:1238-1243`): for `f, g ∈ H^j_M` the following
are equivalent: `(T(h)f - f)/h → -g` as `h ↓ 0`; `t ↦ T(t)f` has derivative `-g` at `t = 0`;
`D_E f = g` distributionally. -/
theorem hasDerivAt_transport_iff (F G : HjM j M) :
    (HasDerivWithinAt (fun t => transport j M t F) (-G) (Ici 0) 0 ↔
        B0009.HasWeakTransport F.value G.value) ∧
      (HasDerivAt (fun t => transport j M t F) (-G) 0 ↔
        B0009.HasWeakTransport F.value G.value) :=
  ⟨⟨hasWeakTransport_of_hasDerivWithinAt,
      fun h => (hasDerivAt_transport_of_hasWeakTransport h).hasDerivWithinAt⟩,
    ⟨fun h => hasWeakTransport_of_hasDerivWithinAt h.hasDerivWithinAt,
      hasDerivAt_transport_of_hasWeakTransport⟩⟩

/-- The domain of the generator is the distributional domain
`{f ∈ H^j_M : D_E f ∈ H^j_M}` of B0009. -/
theorem generatorDomain_eq : generatorDomain j M = B0009.transportDomain j M := by
  ext F
  constructor
  · intro hF
    refine ⟨-derivWithin (fun t => transport j M t F) (Ici 0) 0,
      hasWeakTransport_of_hasDerivWithinAt ?_⟩
    rw [neg_neg]
    exact hF.hasDerivWithinAt
  · rintro ⟨G, hG⟩
    exact (hasDerivAt_transport_of_hasWeakTransport hG).hasDerivWithinAt.differentiableWithinAt

variable (j M) in
/-- **Unit B0063, generator** (`paper/main.tex:1238-1239`): the generator of the transport group
on `H^j_M` is exactly `-D_E = -Ω∂_ϑ` with distributional domain `{f ∈ H^j_M : D_E f ∈ H^j_M}`. -/
theorem generator_eq_neg_DE : generator j M = -DE j M := by
  refine LinearPMap.ext generatorDomain_eq ?_
  intro F hF hF'
  rw [LinearPMap.neg_apply]
  change derivWithin (fun t => transport j M t F) (Ici 0) 0 =
    -B0009.transport (⟨F, hF'⟩ : B0009.transportDomain j M)
  have hW := B0009.hasWeakTransport_transport (⟨F, hF'⟩ : B0009.transportDomain j M)
  exact (hasDerivAt_transport_of_hasWeakTransport hW).hasDerivWithinAt.derivWithin
    uniqueDiffWithinAt_Ici_zero

/-! ### The transport semigroup -/

theorem norm_transport_le_const (t : ℝ) : ‖transport j M t‖ ≤ transportConst j * (1 + |t|) ^ j :=
  LinearMap.mkContinuous_norm_le _ (by have := transportConst_nonneg j; positivity) _

variable (j M) in
/-- The forward transport group `(T(t))_{t ≥ 0}` as a strongly continuous, exponentially
bounded semigroup (`ExpSemigroup`, INF07): `‖T(t)‖ ≤ C_j (1+t)^j ≤ C_j e^{jt}`. -/
def transportSemigroup : UnforcedLeray.Infra.ExpSemigroup (HjM j M) where
  T := transport j M
  T_zero := by
    rw [transport_zero]
    rfl
  T_add s t _ _ := transport_add s t
  T_cont F := (continuous_transport_apply F).continuousOn
  M := transportConst j
  ω := j
  M_nonneg := transportConst_nonneg j
  T_le t ht := by
    refine (norm_transport_le_const t).trans ?_
    have hC := transportConst_nonneg j
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [abs_of_nonneg ht]
    calc (1 + t) ^ j ≤ Real.exp t ^ j :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) j
      _ = Real.exp (j * t) := (Real.exp_nat_mul t j).symm

variable (j M) in
/-- **Unit B0063, all claims together** (`paper/main.tex:1238-1243`): the transport group
`T(t)f = f ∘ Φ_t` of B0062 is strongly continuous on `H^j_M`; for `f, g ∈ H^j_M`,
`(T(h)f - f)/h → -g` (`h ↓ 0`) iff `T(t)f` is differentiable at `0` with derivative `-g` iff
`D_E f = g` distributionally; the generator `lim_{h↓0}(T(h)f - f)/h` is exactly `-D_E` with
domain `{f ∈ H^j_M : D_E f ∈ H^j_M}`; and the flow identity `T(t)f - f = -∫_0^t T(s)D_Ef ds`
holds in `H^j_M`. -/
theorem strongContinuity_and_generator :
    (∀ F : HjM j M, Continuous fun t => transport j M t F) ∧
    (∀ F G : HjM j M,
      (Tendsto (fun h : ℝ => h⁻¹ • (transport j M h F - F)) (𝓝[>] 0) (𝓝 (-G)) ↔
        B0009.HasWeakTransport F.value G.value) ∧
      (HasDerivAt (fun t => transport j M t F) (-G) 0 ↔
        B0009.HasWeakTransport F.value G.value)) ∧
    generatorDomain j M = B0009.transportDomain j M ∧
    generator j M = -DE j M ∧
    (∀ F G : HjM j M, B0009.HasWeakTransport F.value G.value → ∀ t : ℝ,
      transport j M t F - F = -∫ s in (0 : ℝ)..t, transport j M s G) :=
  ⟨continuous_transport_apply,
    fun F G => ⟨(hasDerivWithinAt_iff_tendsto_quotient F (-G)).symm.trans
      (hasDerivAt_transport_iff F G).1, (hasDerivAt_transport_iff F G).2⟩,
    generatorDomain_eq, generator_eq_neg_DE j M,
    fun _ _ hFG t => transport_sub_eq_integral hFG t⟩

end UnforcedLeray.B0063
