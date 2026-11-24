import UnforcedLeray.Loc.L03Evolution.Abstract
import UnforcedLeray.Loc.L03Evolution.Free
import UnforcedLeray.Loc.L03Evolution.ZBound
import UnforcedLeray.Loc.L03Evolution.ZContinuity

/-!
# Step L3: the periodic evolution `E(τ,s)` (`EvolutionStep`)

`paper/main.tex` lines 299–306 (blueprint unit B0713): "Volterra iteration with
`loc:eq:coefficient-maps` therefore constructs a jointly strongly continuous evolution
`E(τ,s)`, periodic in both time arguments. On each strip of bounded elapsed time it is
uniformly bounded on `L², X, Z`, with `L² → X` and `X → Z` norms `C(τ-s)^{-1/2}` at short
times. The weighted Volterra estimate uses the integrable convolution of two square-root
kernels; iteration of the strip gives exponential boundedness."

The step `UnforcedLeray.Blueprint.EvolutionStep` (`Blueprint/Localization/Linear.lean`) is
proved here by instantiating `UnforcedLeray.Infra.VolterraEvolution` twice:

* on `X = H¹_div` with `S₀`, the smoothing `S₀ : L²_div → X` and `𝓑_* : X → L²_div`
  (`xData`); this gives `E(τ,s)`, the evolution law, double periodicity, joint strong
  continuity (`Infra.EvolutionContinuity`), and, through `Abstract.global_duhamel`, the
  Duhamel identity of line 299 for every `s ≤ τ`;
* on `Z = H²_div` with `S₀|_Z`, the smoothing `S₀ : X → Z` and `𝓑_* : Z → X` (`zData`);
  `Abstract.intertwine` identifies it with `E` on `Z`.

The `L² → X` and `X → Z` operators `E_L(τ,s)`, `E_Z(τ,s)` are the continuous extensions of
`E(τ,s)` from the dense subspaces `ι_X(X) ⊂ L²_div` and `ι_Z(Z) ⊂ X`
(`LinearMap.extendOfNorm`), bounded by the singular Gronwall estimate
`Abstract.smoothing_bound` (lines 302–304).

## The free evolution on `Z`

`IsFreeEvolution` (step L2, line 297) records `S₀` on `X`, `L² → X`, `X → Z`, but not on
`Z → Z`. The `Z`-bound `‖(E_Z(τ,s)) ι_Z‖ ≤ C` of `IsEvolution.strip_bounds` needs the free
evolution bounded on `Z` for short times, and the `Z`-valued Volterra iteration needs it
strongly continuous at `0` on `Z`. Both are proved here (`freeEvolutionZBound`,
`freeEvolutionZContinuity`): the bound from the commutation of the heat operator and the
dilation with weak derivatives (`L03Evolution/ZBound.lean`), the continuity from the bound by
a Hilbert-space density argument (`L03Evolution/ZContinuity.lean`). The main theorem is
`evolutionStep`, with no hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Loc.L03Evolution

open UnforcedLeray.Blueprint UnforcedLeray.Infra.VolterraEvolution
open UnforcedLeray.Infra.EvolutionContinuity

/-! ## The free evolution on `Z` -/

/-- **Free evolution bounded on `Z = H²_div`** (proved below: `freeEvolutionZBound`). For
`h > 0` and the free evolution `S₀(t) f(y) = e^{t/2}[e^{h(e^t-1)Δ} f](e^{t/2} y)`
(`paper/main.tex` lines 292–298, B0712), the restriction to `Z` is bounded for short times:
`‖S₀(t) g‖_{H²} ≤ C ‖g‖_{H²}` for `g ∈ H²_div`, `0 < t ≤ 1`.
Stated for every `S` with `IsFreeEvolution h S` (whose `X → Z` part `S.S0Z` is pinned to the
compiled `AncientLocalization.freeEvolution` a.e., hence unique). Proof: the heat
semigroup commutes with weak derivatives and contracts `L²`; the dilation multiplies
`k`-th derivatives by `e^{kt/2}` and `L²` norms by `e^{-t/4}`. Needed for
`IsEvolution.strip_bounds` (`‖E_Z(τ,s) ι_Z‖ ≤ C`, line 302 "uniformly bounded on
`L², X, Z`"). -/
def FreeEvolutionZBound : Prop :=
  ∀ h : ℝ, 0 < h → ∀ S : FreeEvolution, IsFreeEvolution h S →
    ∃ C : ℝ, ∀ t, 0 < t → t ≤ 1 → ‖(S.S0Z t).comp ιZ‖ ≤ C

/-- **Free evolution strongly continuous on `Z = H²_div` at `0`** (proved below:
`freeEvolutionZContinuity`). For `h > 0`, `g ∈ H²_div` and `S` with `IsFreeEvolution h S`,
`S₀(t) g → g` in `H²` as `t → 0⁺` (`paper/main.tex` lines 292–300, B0712, B0713). Proof: the
vectors with `S₀(t) g → g` form a closed subspace (by the `Z`-bound) containing `S₀(t) Z`
for `t > 0`, and `S₀(t) g → g` weakly in `Z`, so its orthogonal complement is `0`.
Needed for the `Z`-valued Volterra iteration (line 300). -/
def FreeEvolutionZContinuity : Prop :=
  ∀ h : ℝ, 0 < h → ∀ S : FreeEvolution, IsFreeEvolution h S →
    ∀ g : Z, Tendsto (fun t => S.S0Z t (ιZ g)) (𝓝[>] 0) (𝓝 g)

/-- `FreeEvolutionZBound` holds, with `C = 1 + 12 e` (`L03Evolution/ZBound.lean`). -/
theorem freeEvolutionZBound : FreeEvolutionZBound :=
  fun _ _ _ hS => exists_norm_S0Z_comp_ιZ_le hS

/-- `FreeEvolutionZContinuity` holds: it follows from the `Z`-bound
(`L03Evolution/ZContinuity.lean`). -/
theorem freeEvolutionZContinuity : FreeEvolutionZContinuity :=
  fun h hh S hS g => tendsto_S0Z_of_bound hS hh.le (freeEvolutionZBound h hh S hS) g

/-! ## The two Volterra problems -/

/-- The Volterra data on `X = H¹_div`: `S₀`, `S₀ : L²_div → X`, `𝓑_* : X → L²_div`
(line 300). -/
def xData (S : FreeEvolution) (c : Coefficients) (C β : ℝ)
    (hS0 : ∀ t, 0 ≤ t → t ≤ 1 → ‖S.S0 t‖ ≤ C)
    (hS0L : ∀ t, 0 < t → t ≤ 1 → ‖S.S0L t‖ ≤ C * t ^ (-(1 / 2 : ℝ)))
    (hB : ∀ t, ‖c.B t‖ ≤ β)
    (hcS0 : ∀ x, ContinuousOn (fun t => S.S0 t x) (Icc 0 1))
    (hcS0L : ∀ y, ContinuousOn (fun t => S.S0L t y) (Ioc 0 1))
    (hcB : ∀ x, Continuous (fun t => c.B t x)) : VolterraData ℝ X L2div where
  S₀ := S.S0
  S := S.S0L
  B := c.B
  M₀ := C
  C₀ := C
  β := β
  norm_S₀_le := hS0
  norm_S_le := hS0L
  norm_B_le := hB
  continuousOn_S₀ := hcS0
  continuousOn_S := hcS0L
  continuous_B := hcB

/-- The Volterra data on `Z = H²_div`: `S₀|_Z`, `S₀ : X → Z`, `𝓑_* : Z → X` (line 300,
`loc:eq:coefficient-maps`). -/
def zData (S : FreeEvolution) (c : Coefficients) (M C β : ℝ)
    (hS0 : ∀ t, 0 ≤ t → t ≤ 1 → ‖S0ZZ S t‖ ≤ M)
    (hS0Z : ∀ t, 0 < t → t ≤ 1 → ‖S.S0Z t‖ ≤ C * t ^ (-(1 / 2 : ℝ)))
    (hB : ∀ t, ‖c.BZ t‖ ≤ β)
    (hcS0 : ∀ g, ContinuousOn (fun t => S0ZZ S t g) (Icc 0 1))
    (hcS0Z : ∀ y, ContinuousOn (fun t => S.S0Z t y) (Ioc 0 1))
    (hcB : ∀ g, Continuous (fun t => c.BZ t g)) : VolterraData ℝ Z X where
  S₀ := S0ZZ S
  S := S.S0Z
  B := c.BZ
  M₀ := M
  C₀ := C
  β := β
  norm_S₀_le := hS0
  norm_S_le := hS0Z
  norm_B_le := hB
  continuousOn_S₀ := hcS0
  continuousOn_S := hcS0Z
  continuous_B := hcB

/-- The evolution of line 299: `E = ` the `X`-level Volterra evolution, `E_L`, `E_Z` its
continuous extensions from `ι_X(X) ⊂ L²_div` and from `ι_Z(Z) ⊂ X` (the latter through the
`Z`-level evolution). -/
def evOf (V : VolterraData ℝ X L2div) (VZ : VolterraData ℝ Z X) : Evolution where
  E τ s := V.evolution τ s
  EL τ s := (V.evolution τ s : X →ₗ[ℝ] X).extendOfNorm (ιX : X →ₗ[ℝ] L2div)
  EZ τ s := (VZ.evolution τ s : Z →ₗ[ℝ] Z).extendOfNorm (ιZ : Z →ₗ[ℝ] X)

/-! ## The characterization -/

/-- **`IsEvolution` for the Volterra evolutions** (lines 299–306). -/
theorem isEvolution_evOf {D : BackgroundData} {c : Coefficients} {S : FreeEvolution}
    (hh : 0 ≤ D.h) (hc : IsCoefficients D c) (hS : IsFreeEvolution D.h S)
    (V : VolterraData ℝ X L2div) (hVS₀ : V.S₀ = S.S0) (hVS : V.S = S.S0L) (hVB : V.B = c.B)
    (VZ : VolterraData ℝ Z X) (hZS₀ : VZ.S₀ = S0ZZ S) (hZS : VZ.S = S.S0Z)
    (hZB : VZ.B = c.BZ) : IsEvolution D c S (evOf V VZ) := by
  -- compatibility of both Volterra problems
  have hVc : V.Compatible :=
    ⟨fun a b ha hb _ => by rw [hVS₀]; exact S0_comp_S0 hS hh ha hb,
      fun a b ha hb _ => by rw [hVS₀, hVS]; exact S0_comp_S0L hS hh ha hb⟩
  have hV0 : V.S₀ 0 = 1 := by rw [hVS₀, S0_zero hS]; rfl
  have hZc : VZ.Compatible :=
    ⟨fun a b ha hb _ => by rw [hZS₀]; exact S0ZZ_comp_S0ZZ hS hh ha hb,
      fun a b ha hb _ => by rw [hZS₀, hZS]; exact S0ZZ_comp_S0Z hS hh ha hb⟩
  have hιX : ∀ t, 0 < t → t ≤ 1 → V.S₀ t = (V.S t).comp ιX := fun t ht _ => by
    rw [hVS₀, hVS]; exact (S0L_comp_ιX hS ht).symm
  have hιZ : ∀ t, 0 < t → t ≤ 1 → VZ.S₀ t = (VZ.S t).comp ιZ := fun t ht _ => by
    rw [hZS₀, hZS]; exact S0ZZ_of_pos S ht
  -- the `Z`-level evolution is `E` on `Z`
  have hint : ∀ s τ, s ≤ τ → ∀ g, ιZ (VZ.evolution τ s g) = V.evolution τ s (ιZ g) := by
    refine intertwine VZ hZc V hVc ιZ (fun t ht _ w => ?_) (fun t r ht _ w => ?_)
    · rw [hZS₀, hVS₀]
      exact ιZ_S0ZZ hS ht w
    · rw [hZS, hZB, hVS, hVB, ← hc.BZ_compat r w, ← ContinuousLinearMap.comp_apply ιZ,
        ιZ_comp_S0Z hS ht, ← ContinuousLinearMap.comp_apply (S.S0L t), S0L_comp_ιX hS ht]
  -- global Duhamel
  have hG := global_duhamel V hVc (fun a b ha hb => by rw [hVS₀]; exact S0_comp_S0 hS hh ha hb)
    (fun a b ha hb => by rw [hVS₀, hVS]; exact S0_comp_S0L hS hh ha hb)
  -- the smoothing bounds in the form of `extendOfNorm`
  have hXb : ∀ s τ, s < τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : X,
      ‖V.evolution τ s x‖ ≤ K * ‖ιX x‖ := by
    intro s τ hsτ
    obtain ⟨K, hK0, hK⟩ := smoothing_bound V hVc ιX hιX (τ - s) (by linarith)
    refine ⟨K * (τ - s) ^ (-(1 / 2 : ℝ)), mul_nonneg hK0 (Real.rpow_nonneg (by linarith) _),
      fun x => ?_⟩
    refine (hK s τ hsτ (by linarith) x).trans (le_of_eq ?_)
    ring
  have hZb : ∀ s τ, s < τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Z,
      ‖VZ.evolution τ s g‖ ≤ K * ‖ιZ g‖ := by
    intro s τ hsτ
    obtain ⟨K, hK0, hK⟩ := smoothing_bound VZ hZc ιZ hιZ (τ - s) (by linarith)
    refine ⟨K * (τ - s) ^ (-(1 / 2 : ℝ)), mul_nonneg hK0 (Real.rpow_nonneg (by linarith) _),
      fun g => ?_⟩
    refine (hK s τ hsτ (by linarith) g).trans (le_of_eq ?_)
    ring
  have hELeq : ∀ s τ, s < τ → ∀ x : X, (evOf V VZ).EL τ s (ιX x) = V.evolution τ s x := by
    intro s τ hsτ x
    obtain ⟨K, -, hK⟩ := hXb s τ hsτ
    exact LinearMap.extendOfNorm_eq (denseRange_ιX hS) ⟨K, hK⟩ x
  have hEZeq : ∀ s τ, s < τ → ∀ g : Z, (evOf V VZ).EZ τ s (ιZ g) = VZ.evolution τ s g := by
    intro s τ hsτ g
    obtain ⟨K, -, hK⟩ := hZb s τ hsτ
    exact LinearMap.extendOfNorm_eq (denseRange_ιZ hS) ⟨K, hK⟩ g
  refine
    { at_diag := fun s => ?_
      law := fun s r τ h1 h2 => VolterraData.evolution_comp hVc h1 h2
      periodic := fun τ s => V.evolution_periodic (fun r => by rw [hVB]; exact hc.B_periodic r) τ s
      strongly_continuous := fun f => continuousOn_evolution_prod hVc hV0 f
      duhamel_integrable := fun s τ hsτ f => ?_
      duhamel := fun s τ hsτ f => ?_
      EL_compat := fun s τ hsτ => ?_
      EZ_compat := fun s τ hsτ => ?_
      strip_bounds := fun L hL => ?_ }
  · show V.evolution s s = _
    rw [evolution_self hVc hV0 s]
    rfl
  · have h1 := (hG s τ hsτ f).1
    rw [hVS, hVB] at h1
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hsτ).mp h1
  · have h2 := (hG s τ hsτ f).2
    rw [hVS₀, hVS, hVB, intervalIntegral.integral_of_le hsτ, integral_Ioc_eq_integral_Ioo] at h2
    exact h2
  · ext1 x
    rw [ContinuousLinearMap.comp_apply]
    exact hELeq s τ hsτ x
  · apply DFunLike.coe_injective
    refine (denseRange_ιZ hS).equalizer (ιZ.comp ((evOf V VZ).EZ τ s)).continuous
      (V.evolution τ s).continuous (funext fun g => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hEZeq s τ hsτ g]
    exact hint s τ hsτ.le g
  · obtain ⟨M, ω, hM, hω, hMω⟩ := V.exists_norm_evolution_le
    obtain ⟨MZ, ωZ, hMZ, hωZ, hMωZ⟩ := VZ.exists_norm_evolution_le
    obtain ⟨KX, hKX0, hKX⟩ := smoothing_bound V hVc ιX hιX L hL
    obtain ⟨KZ, hKZ0, hKZ⟩ := smoothing_bound VZ hZc ιZ hιZ L hL
    have hM0 : 0 ≤ M * Real.exp (ω * L) := mul_nonneg (by linarith) (Real.exp_pos _).le
    have hMZ0 : 0 ≤ MZ * Real.exp (ωZ * L) := mul_nonneg (by linarith) (Real.exp_pos _).le
    refine ⟨M * Real.exp (ω * L) + KX + KZ + MZ * Real.exp (ωZ * L),
      fun s τ hsτ hτ => ⟨?_, fun hlt => ⟨?_, ?_, ?_⟩⟩⟩
    · show ‖V.evolution τ s‖ ≤ _
      refine (hMω s τ hsτ).trans ?_
      have : M * Real.exp (ω * (τ - s)) ≤ M * Real.exp (ω * L) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hω))
          (by linarith)
      linarith
    · have hts : 0 < τ - s := by linarith
      have hp0 : 0 ≤ (τ - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hts.le _
      rw [div_sqrt_eq_mul_rpow _ hts]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
      refine (LinearMap.norm_extendOfNorm_apply_le (denseRange_ιX hS) (KX * (τ - s) ^ (-(1 / 2 : ℝ)))
        (fun x => ?_) F).trans ?_
      · refine (hKX s τ hlt hτ x).trans (le_of_eq ?_)
        show KX * ‖ιX x‖ * (τ - s) ^ (-(1 / 2 : ℝ)) = KX * (τ - s) ^ (-(1 / 2 : ℝ)) * ‖ιX x‖
        ring
      · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hp0) (norm_nonneg _)
        linarith
    · have hts : 0 < τ - s := by linarith
      have hp0 : 0 ≤ (τ - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hts.le _
      rw [div_sqrt_eq_mul_rpow _ hts]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
      refine (LinearMap.norm_extendOfNorm_apply_le (denseRange_ιZ hS) (KZ * (τ - s) ^ (-(1 / 2 : ℝ)))
        (fun g => ?_) F).trans ?_
      · refine (hKZ s τ hlt hτ g).trans (le_of_eq ?_)
        show KZ * ‖ιZ g‖ * (τ - s) ^ (-(1 / 2 : ℝ)) = KZ * (τ - s) ^ (-(1 / 2 : ℝ)) * ‖ιZ g‖
        ring
      · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hp0) (norm_nonneg _)
        linarith
    · have heq : ((evOf V VZ).EZ τ s).comp ιZ = VZ.evolution τ s := by
        ext1 g
        rw [ContinuousLinearMap.comp_apply]
        exact hEZeq s τ hlt g
      rw [heq]
      refine (hMωZ s τ hsτ).trans ?_
      have : MZ * Real.exp (ωZ * (τ - s)) ≤ MZ * Real.exp (ωZ * L) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hωZ)) (by linarith)
      linarith

/-! ## Step L3 -/

/-- Step L3 from the two properties of the free evolution on `Z = H²_div`
(`paper/main.tex` lines 299–306, blueprint unit B0713). -/
theorem evolutionStep_of (hZb : FreeEvolutionZBound) (hZc : FreeEvolutionZContinuity) :
    EvolutionStep := by
  intro D hD c S hc hS
  have hh : 0 < D.h := hD.1.h_pos
  have hP : 0 < D.period := hD.1.period_pos
  obtain ⟨C, -, hS0, hS0L, hS0Z⟩ := free_bounds hS
  obtain ⟨β, hβ⟩ := exists_norm_le_of_periodic hP.ne' hc.B_periodic hc.B_continuous
  obtain ⟨βZ, hβZ⟩ := exists_norm_le_of_periodic hP.ne' hc.BZ_periodic hc.BZ_continuous
  obtain ⟨CZ, hCZ⟩ := hZb D.h hh S hS
  have hZZ : ∀ t, 0 ≤ t → t ≤ 1 → ‖S0ZZ S t‖ ≤ max CZ 1 := by
    intro t ht ht1
    rcases eq_or_lt_of_le ht with h0 | hpos
    · rw [← h0, S0ZZ_of_nonpos S le_rfl]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
    · rw [S0ZZ_of_pos S hpos]
      exact (hCZ t hpos ht1).trans (le_max_left _ _)
  let V := xData S c C β (fun t ht _ => hS0 t ht) hS0L hβ
    (fun x => (hS.strongly_continuous x).mono Icc_subset_Ici_self)
    (fun y => (continuousOn_S0L hS hh.le y).mono fun t ht => ht.1)
    (fun x => hc.B_continuous.clm_apply continuous_const)
  let VZ := zData S c (max CZ 1) C βZ hZZ hS0Z hβZ
    (continuousOn_S0ZZ hS hh.le (hZc D.h hh S hS))
    (fun y => (continuousOn_S0Z hS hh.le y).mono fun t ht => ht.1)
    (fun g => hc.BZ_continuous.clm_apply continuous_const)
  exact ⟨evOf V VZ, isEvolution_evOf hh.le hc hS V rfl rfl rfl VZ rfl rfl rfl⟩

/-- **Step L3** (`EvolutionStep`, `paper/main.tex` lines 299–306, blueprint unit B0713):
for every unstable background, coefficients `𝓑_*` and free evolution `S₀` with their
characterizations, the Volterra evolution `E(τ,s)` exists with all clauses of
`IsEvolution`. -/
theorem evolutionStep : EvolutionStep :=
  evolutionStep_of freeEvolutionZBound freeEvolutionZContinuity

end UnforcedLeray.Loc.L03Evolution
