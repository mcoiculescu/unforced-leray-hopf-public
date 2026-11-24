import UnforcedLeray.Short.PartI.Compose
import UnforcedLeray.Short.PartI.Sub.C02
import UnforcedLeray.Lib.EvolutionC.ConstPert
import UnforcedLeray.Lib.EvolutionFamilies.Mild
import UnforcedLeray.Lib.PlanarSpectralB.CompactPerturb

/-!
# Part I, task `PartI:C03`: the block limit of the complementary evolution (conditional)

Source of record: `the November 2 reference manuscript`, lines 1031-1049
(proof of Lemma `lem:short-diffusion-complement`): "On a fixed block, `exp(D∫_s^tβ) → I` strongly
as `β_* ↓ 0`, uniformly over all admissible coefficients. The Dyson series give the corresponding
direct and adjoint strong limits for the free and full evolutions. For the adjoints, reverse time
on the block; the class of admissible coefficients is unchanged. Lemma `short-compact-duhamel`
therefore gives `U_β(s+B,s) - F_β(s+B,s) → e^{B(L-λ-P)} - e^{B(T-λ)}` in norm uniformly in `s`
and `β`."

## Well-formed reading of the original target


(see `Short/PartI/Tasks/ComplementBlockLimit.lean`): for every `B, ε > 0` there is `β_* > 0`
such that for every measurable `0 ≤ β ≤ β_*`, every `U` with `IsMildComplementEvolution`
(`StatementsCanonical.lean`) and every `F` with `IsFreeDiffusionEvolution` (`Sub/C02.lean`) and
every `s`, the block remainder `(U - F)(s+B, s)` is within `ε` (operator norm) of
`exp(B(L₀-λ-P)) - exp(B(T-λ))`.  `T = (-2i)Ω` is `complementT`.

## Proof structure

The theorem `complement_block_limit_of` is a contradiction argument along `β_n ≤ 1/(n+1)`:
the family `(F_{β_n}, A_n = (L₀-T-P) + β_n R_f, U_{β_n})` is fed to `compactDuhamelLemma`
(`Compose.lean`, from `B0104.compact_duhamel_dyson`) with the one-point index set `Unit`, the
limit data `F₀ = e^{(t-s)(T-λ)}`, `A₀ = L₀-T-P`, `U₀ = e^{(t-s)(L₀-λ-P)}`.  Its hypotheses are
discharged by six `Prop`s (open leaves, each with a docstring) and the compactness of
`L₀ - T - P`, which is proved here (`complementBaseCompact`):

* `FreeSharpBoundAll` (sharp norm bound of *every* free evolution, measurable `β`);
* `FreeStrongSmall`, `FreeAdjointSmall` (uniform direct and adjoint strong convergence
  `F_β → e^{(t-s)(T-λ)}` on blocks as `β_* → 0`);
* `DysonBridge`, `FreeEvolutionFamily`, `ComplementDysonFamily` (the evolutions `F_β`, `U_β`
  are Dyson sums, in the `B0104` form `DysonDefined` / `IsDysonSum` required by
  `compactDuhamelLemma`; the limit data is the Dyson series of a bounded generator,
  `Evolution.dyson_ofExp_const`).

The unconditional target is task `PartI:C03` (`Short/PartI/Tasks/ComplementBlockLimit.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Infra.Dunford (rankOneProj)

/-- The bounded transport `T = -2iΩ` (source line 967). -/
def complementT : B0010.XG →L[ℂ] B0010.XG := (-2 * Complex.I) • B0012.omegaOp

/-- The inviscid free generator `T - λ` (the `β = 0` case of the free generator
`T - λ - βκ + βD`, source lines 1014-1030). -/
def freeLimitGen (lam : ℂ) : B0010.XG →L[ℂ] B0010.XG :=
  complementT - lam • (1 : B0010.XG →L[ℂ] B0010.XG)

/-- The Dyson interaction of the complementary evolution relative to the free evolution:
`A_β(r) = (L₀ - T - P) + β(r) R_f` (source lines 1014-1030: "interaction `A - P + βR_f`"),
with `P = rankOneProj ℓ q` and `Rf = seedRf ℓ q qd hq hqd`. -/
def complementInteraction (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) (β : ℝ → ℝ) (r : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  (Planar.L0 - complementT - rankOneProj l q) + (β r : ℂ) • Rf

/-! ### The six open leaves and the compactness fact -/

/-- **Leaf 1** (sharp bound for every free evolution; source lines 1024-1028): for measurable
`0 ≤ β ≤ β_*`, *every* `F` with `IsFreeDiffusionEvolution` satisfies
`‖F(t,s)‖ ≤ exp(-Re λ (t-s) + |Re κ| β_* (t-s))`.  (`FreeDiffusionSharpBoundContinuous` is the
case of continuous `β`; `exists_freeDiffusionEvolution` gives one `F` with the bound for
measurable `β`; two free evolutions coincide because both are the Dyson sum of the block,
`fds_hasSum` in `Tasks/FreeDiffusionEvolution/Stability.lean`.) -/
def FreeSharpBoundAll : Prop :=
  ∀ (lam kappa : ℂ) (βs : ℝ) (β : ℝ → ℝ), Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∀ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F →
      ∀ s t : ℝ, s ≤ t →
        ‖F t s‖ ≤ Real.exp (-(lam.re * (t - s)) + |kappa.re| * βs * (t - s))

/-- **Leaf 2** (uniform strong convergence of the free evolutions; source lines 1031-1034,
"`exp(D∫_s^tβ) → I` strongly as `β_* ↓ 0`, uniformly over all admissible coefficients. The Dyson
series give the corresponding direct strong limits for the free evolutions"): for every vector
`x` and `ε > 0` there is `δ > 0` such that for all measurable `0 ≤ β ≤ δ`, all free evolutions
`F` and all `s ≤ t ≤ s + B`, `‖F(t,s)x - e^{(t-s)(T-λ)}x‖ < ε`.  The threshold `δ` does not
depend on `s`, `β`, `F` (nor on `κ`'s block). -/
def FreeStrongSmall : Prop :=
  ∀ (lam kappa : ℂ) (B : ℝ) (x : B0010.XG) (ε : ℝ), 0 < B → 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ δ) →
      ∀ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F →
        ∀ s t : ℝ, s ≤ t → t ≤ s + B →
          ‖F t s x - NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam) x‖ < ε

/-- **Leaf 3** (uniform adjoint strong convergence of the free evolutions; source lines
1034-1036, "For the adjoints, reverse time on the block"): as `FreeStrongSmall`, for the Hilbert
space adjoints, `‖F(t,s)†y - (e^{(t-s)(T-λ)})†y‖ < ε`. -/
def FreeAdjointSmall : Prop :=
  ∀ (lam kappa : ℂ) (B : ℝ) (y : B0010.XG) (ε : ℝ), 0 < B → 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ δ) →
      ∀ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F →
        ∀ s t : ℝ, s ≤ t → t ≤ s + B →
          ‖ContinuousLinearMap.adjoint (F t s) y -
            ContinuousLinearMap.adjoint
              (NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam)) y‖ < ε

/-- **Compact remainder** (source lines 1040-1041 and 1003, "compact family"): the frozen
interaction `L₀ - T - P` is a compact operator on `X_G`, for every rank-one `P`.
(`L₀ - T = (2i) kROp` is compact, `Planar.isCompactOperator_L0_sub_mul`, and `P` has finite rank,
`Infra.CompactPerturb.isCompactOperator_rankOneProj`.) -/
def ComplementBaseCompact : Prop :=
  ∀ (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG),
    IsCompactOperator (Planar.L0 - complementT - rankOneProj l q)

theorem complementBaseCompact : ComplementBaseCompact := fun l q =>
  Planar.isCompactOperator_L0_sub_mul.sub
    (UnforcedLeray.Infra.CompactPerturb.isCompactOperator_rankOneProj l q)

/-- **Leaf 4** (bridge from evolution families to the `B0104` Dyson predicates; source lines
1031-1049, the hypotheses `DysonDefined`, `IsDysonSum` of `compactDuhamelLemma`): if for every
block `[s, s+B]` the global family `F` agrees on the triangle with an `Evolution.EvolutionFamily`
`E`, the interaction `A` is the interaction of a `BoundedPert` `Ap` and `U` agrees with
`Evolution.dyson E Ap` on the triangle, then `U` is the Dyson sum of `(F, A)` in the sense of
`B0104.DysonDefined` / `B0104.IsDysonSum` (index set `Unit`). -/
def DysonBridge : Prop :=
  ∀ (B : ℝ) (F U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG) (A : ℝ → B0010.XG →L[ℂ] B0010.XG),
    (∀ s : ℝ, ∃ (E : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s (s + B))
        (Ap : UnforcedLeray.Evolution.BoundedPert B0010.XG s (s + B)),
      (∀ r, Ap.A r = A r) ∧
      (∀ u v, s ≤ u → u ≤ v → v ≤ s + B → E.U v u = F v u) ∧
      (∀ u v, s ≤ u → u ≤ v → v ≤ s + B →
        (UnforcedLeray.Evolution.dyson E Ap).U v u = U v u)) →
    B0104.DysonDefined B (fun _ : Unit => F) (fun _ => A) ∧
    B0104.IsDysonSum B (fun _ : Unit => F) (fun _ => A) (fun _ => U)

/-- **Leaf 5** (a free evolution is an evolution family; source lines 1019-1021): for measurable
`0 ≤ β ≤ β_*` and `F` with `IsFreeDiffusionEvolution`, on every `[a,b]` there is an
`Evolution.EvolutionFamily` `E` with `E.U = F` on the triangle `a ≤ u ≤ v ≤ b`.  (`E` is the
Dyson family of the block `[a,b]`, `fdeAuxBlock` in `Tasks/FreeDiffusionEvolution/Exists.lean`;
`F = E.U` on the triangle by `Evolution.dyson_unique` with `hF.cont`, `hF.duhamel`, as in
`fds_hasSum`.) -/
def FreeEvolutionFamily : Prop :=
  ∀ (lam kappa : ℂ) (βs : ℝ) (β : ℝ → ℝ), Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∀ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F →
      ∀ a b : ℝ, ∃ E : UnforcedLeray.Evolution.EvolutionFamily B0010.XG a b,
        ∀ u v, a ≤ u → u ≤ v → v ≤ b → E.U v u = F v u

/-- **Leaf 6** (the mild complementary evolution is the Dyson sum of the free evolution with
the interaction `A_β`; source lines 1014-1030, "the evolution exists for measurable `β` by the
Dyson series based on `exp(D∫β)`"): if `E` is an evolution family agreeing with the free
evolution `F` on the triangle of `[a,b]` and `Ap` is a `BoundedPert` with
`Ap.A r = complementInteraction ℓ q R_f β r`, then the mild evolution `U` equals
`Evolution.dyson E Ap` on the triangle.  (Proof: the generator of `IsMildComplementEvolution`
is `(T-λ-βκ) + A_β`; `Evolution.mild_transfer` and `Evolution.dyson_sum_regroup`/`dyson_base_congr`
(`Cons/L2/CanonicalBranch/CanonicalDysonRegroup.lean`, `CanonicalDysonBaseChange.lean`) move the
base from `e^{D∫β}` to `F`, then `Evolution.mild_unique`.) -/
def ComplementDysonFamily : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ) (qd : B0010.XG)
    (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (βs : ℝ) (β : ℝ → ℝ),
    Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
    ∀ U F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG,
      IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U →
      IsFreeDiffusionEvolution lam (seedKappa l q hq) β F →
      ∀ (a b : ℝ) (E : UnforcedLeray.Evolution.EvolutionFamily B0010.XG a b)
        (Ap : UnforcedLeray.Evolution.BoundedPert B0010.XG a b),
        (∀ u v, a ≤ u → u ≤ v → v ≤ b → E.U v u = F v u) →
        (∀ r, Ap.A r = complementInteraction l q (seedRf l q qd hq hqd) β r) →
        ∀ u v, a ≤ u → u ≤ v → v ≤ b →
          (UnforcedLeray.Evolution.dyson E Ap).U v u = U v u

/-! ### Elementary estimates for the interaction -/

theorem norm_complementInteraction_le (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {β : ℝ → ℝ} {βs : ℝ} (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs)
    (r : ℝ) :
    ‖complementInteraction l q Rf β r‖ ≤
      ‖Planar.L0 - complementT - rankOneProj l q‖ + βs * ‖Rf‖ := by
  unfold complementInteraction
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ r).1]
  exact mul_le_mul_of_nonneg_right (hβ r).2 (norm_nonneg _)

theorem norm_complementInteraction_sub_le (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {β : ℝ → ℝ} {βs : ℝ} (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs)
    (r : ℝ) :
    ‖complementInteraction l q Rf β r - (Planar.L0 - complementT - rankOneProj l q)‖ ≤
      βs * ‖Rf‖ := by
  unfold complementInteraction
  rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hβ r).1]
  exact mul_le_mul_of_nonneg_right (hβ r).2 (norm_nonneg _)

theorem aestronglyMeasurable_complementInteraction (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (Rf : B0010.XG →L[ℂ] B0010.XG) {β : ℝ → ℝ} (hβ : Measurable β) (μ : Measure ℝ) :
    AEStronglyMeasurable (complementInteraction l q Rf β) μ := by
  have h : AEStronglyMeasurable (fun r => (β r : ℂ)) μ :=
    (Complex.measurable_ofReal.comp hβ).aestronglyMeasurable
  have hc : Continuous (fun c : ℂ => (Planar.L0 - complementT - rankOneProj l q) + c • Rf) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact hc.comp_aestronglyMeasurable h

/-! ### Dyson data of the complementary evolution and of the limit -/

/-- The `B0104` Dyson data of the complementary evolution `U` over the free evolution `F`. -/
theorem complement_dyson_of (h5 : DysonBridge) (h6 : FreeEvolutionFamily)
    (h7 : ComplementDysonFamily) {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    {qd : B0010.XG} (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (B βs : ℝ)
    {β : ℝ → ℝ} (hβm : Measurable β) (hβb : ∀ t, 0 ≤ β t ∧ β t ≤ βs)
    {U F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hU : IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U)
    (hF : IsFreeDiffusionEvolution lam (seedKappa l q hq) β F) :
    B0104.DysonDefined B (fun _ : Unit => F)
        (fun _ => complementInteraction l q (seedRf l q qd hq hqd) β) ∧
      B0104.IsDysonSum B (fun _ : Unit => F)
        (fun _ => complementInteraction l q (seedRf l q qd hq hqd) β) (fun _ => U) := by
  refine h5 B F U _ (fun s => ?_)
  obtain ⟨E, hE⟩ := h6 lam (seedKappa l q hq) βs β hβm hβb F hF s (s + B)
  let Ap : UnforcedLeray.Evolution.BoundedPert B0010.XG s (s + B) :=
    UnforcedLeray.Evolution.BoundedPert.ofAEStronglyMeasurable
      (complementInteraction l q (seedRf l q qd hq hqd) β)
      (aestronglyMeasurable_complementInteraction l q _ hβm _)
      ⟨‖Planar.L0 - complementT - rankOneProj l q‖ + βs * ‖seedRf l q qd hq hqd‖,
        fun r _ => norm_complementInteraction_le l q _ hβb r⟩
  exact ⟨E, Ap, fun r => rfl, hE, fun u v hu huv hv =>
    h7 lam q l qd hq hqd βs β hβm hβb U F hU hF s (s + B) E Ap hE (fun r => rfl) u v hu huv hv⟩

/-- The `B0104` Dyson data of the limit: `e^{(t-s)(L₀-λ-P)}` is the Dyson series of the free
group `e^{(t-s)(T-λ)}` with the constant interaction `L₀ - T - P`
(`Evolution.dyson_ofExp_const`). -/
theorem limit_dyson_of (h5 : DysonBridge) (lam : ℂ) (l : B0010.XG →L[ℂ] ℂ) (q : B0010.XG)
    (B : ℝ) :
    B0104.DysonDefined B
        (fun _ : Unit => fun t s : ℝ =>
          NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam))
        (fun _ : Unit => fun _ : ℝ => Planar.L0 - complementT - rankOneProj l q) ∧
      B0104.IsDysonSum B
        (fun _ : Unit => fun t s : ℝ =>
          NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam))
        (fun _ : Unit => fun _ : ℝ => Planar.L0 - complementT - rankOneProj l q)
        (fun _ : Unit => fun t s : ℝ =>
          NormedSpace.exp (((t - s : ℝ) : ℂ) •
            (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - rankOneProj l q))) := by
  refine h5 B _ _ _ (fun s => ?_)
  have hsum : freeLimitGen lam + (Planar.L0 - complementT - rankOneProj l q) =
      Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - rankOneProj l q := by
    unfold freeLimitGen
    abel
  refine ⟨UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup
      (UnforcedLeray.Infra.ExpSemigroup.ofExp (freeLimitGen lam)) s (s + B),
    UnforcedLeray.Evolution.BoundedPert.const (Planar.L0 - complementT - rankOneProj l q),
    fun r => rfl, fun u v _ _ _ => rfl, fun u v hu huv hv => ?_⟩
  rw [UnforcedLeray.Evolution.dyson_ofExp_const _ _ u v hu huv hv, hsum]

/-! ### Elementary filter facts -/

theorem eventually_one_div_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ :=
  (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (ge_mem_nhds hδ)

theorem eventually_const_mul_one_div_lt (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) * c < ε := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const c
  rw [zero_mul] at h
  exact h.eventually (gt_mem_nhds hε)

theorem one_div_succ_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ### The conditional theorem -/

/-- **`PartI:C03` from the six leaves** (source lines 1031-1049): the block remainder
`(U_β - F_β)(s+B,s)` is uniformly close to `e^{B(L₀-λ-P)} - e^{B(T-λ)}` for small `β_*`.
Contradiction argument along `β_n ≤ 1/(n+1)` with `compactDuhamelLemma` on the index set `Unit`. -/
theorem complement_block_limit_of
    (h1 : FreeSharpBoundAll) (h2 : FreeStrongSmall) (h3 : FreeAdjointSmall)
    (h5 : DysonBridge) (h6 : FreeEvolutionFamily) (h7 : ComplementDysonFamily)
    {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ} (_hI : IsSeedXG lam q l)
    {qd : B0010.XG} (_hl : ∀ f, l f = inner ℂ qd f) (hq : q ∈ B0094.D.domain)
    (hqd : qd ∈ B0094.D.domain) (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ βs > 0, ∀ β : ℝ → ℝ, Measurable β → (∀ t, 0 ≤ β t ∧ β t ≤ βs) →
      ∀ U F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG,
      IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U →
      IsFreeDiffusionEvolution lam (seedKappa l q hq) β F →
      ∀ s : ℝ, ‖(U (s + B) s - F (s + B) s) -
        (NormedSpace.exp ((B : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
            rankOneProj l q)) -
          NormedSpace.exp ((B : ℂ) • ((-2 * Complex.I) • B0012.omegaOp -
            lam • (1 : B0010.XG →L[ℂ] B0010.XG))))‖ < ε := by
  by_contra hcon
  push Not at hcon
  choose β hβm hβb U F hU hF s hs using
    fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hβ1 : ∀ n t, 0 ≤ β n t ∧ β n t ≤ 1 := fun n t =>
    ⟨(hβb n t).1, (hβb n t).2.trans (one_div_succ_le_one n)⟩
  have key := compactDuhamelLemma B0010.XG Unit
    (B := B)
    (F := fun n (_ : Unit) => F n)
    (F₀ := fun (_ : Unit) (t s : ℝ) => NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam))
    (A := fun n (_ : Unit) => complementInteraction l q (seedRf l q qd hq hqd) (β n))
    (A₀ := fun (_ : Unit) (_ : ℝ) => Planar.L0 - complementT - rankOneProj l q)
    (U := fun n (_ : Unit) => U n)
    (U₀ := fun (_ : Unit) (t s : ℝ) => NormedSpace.exp (((t - s : ℝ) : ℂ) •
      (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - rankOneProj l q)))
    ?bd ?str ?adj ?Abd ?Aconv ?cpt ?tb (fun n => (complement_dyson_of h5 h6 h7 hq hqd B _
      (hβm n) (hβb n) (hU n) (hF n)).1) (limit_dyson_of h5 lam l q B).1
    (fun n => (complement_dyson_of h5 h6 h7 hq hqd B _ (hβm n) (hβb n) (hU n) (hF n)).2)
    (limit_dyson_of h5 lam l q B).2
  case bd =>
    refine ⟨Real.exp (|lam.re| * B + |(seedKappa l q hq).re| * B) +
      Real.exp (B * ‖freeLimitGen lam‖), ?_⟩
    intro n _ t s hst hts
    have hτ0 : 0 ≤ t - s := sub_nonneg.2 hst
    have hτB : t - s ≤ B := by linarith
    constructor
    · have h := h1 lam (seedKappa l q hq) _ (β n) (hβm n) (hβb n) (F n) (hF n) s t hst
      have e1 : -(lam.re * (t - s)) ≤ |lam.re| * B := by
        calc -(lam.re * (t - s)) = (-lam.re) * (t - s) := by ring
          _ ≤ |lam.re| * (t - s) := mul_le_mul_of_nonneg_right (neg_le_abs _) hτ0
          _ ≤ |lam.re| * B := mul_le_mul_of_nonneg_left hτB (abs_nonneg _)
      have e2 : |(seedKappa l q hq).re| * (1 / ((n : ℝ) + 1)) * (t - s) ≤
          |(seedKappa l q hq).re| * B := by
        calc |(seedKappa l q hq).re| * (1 / ((n : ℝ) + 1)) * (t - s)
            ≤ |(seedKappa l q hq).re| * 1 * (t - s) := by
              gcongr
              exact one_div_succ_le_one n
          _ ≤ |(seedKappa l q hq).re| * 1 * B := by gcongr
          _ = |(seedKappa l q hq).re| * B := by ring
      refine h.trans ?_
      refine le_add_of_le_of_nonneg (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
    · have h := UnforcedLeray.Infra.BanachExp.norm_exp_smul_le (freeLimitGen lam) (t - s)
      refine h.trans ?_
      refine le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 ?_)
      rw [abs_of_nonneg hτ0]
      exact mul_le_mul_of_nonneg_right hτB (norm_nonneg _)
  case str =>
    intro x ε' hε'
    obtain ⟨δ, hδ, hδp⟩ := h2 lam (seedKappa l q hq) B x ε' hB hε'
    filter_upwards [eventually_one_div_le hδ] with n hn p t s hst hts
    exact hδp (β n) (hβm n) (fun r => ⟨(hβb n r).1, (hβb n r).2.trans hn⟩) (F n) (hF n)
      s t hst hts
  case adj =>
    intro y ε' hε'
    obtain ⟨δ, hδ, hδp⟩ := h3 lam (seedKappa l q hq) B y ε' hB hε'
    filter_upwards [eventually_one_div_le hδ] with n hn p t s hst hts
    exact hδp (β n) (hβm n) (fun r => ⟨(hβb n r).1, (hβb n r).2.trans hn⟩) (F n) (hF n)
      s t hst hts
  case Abd =>
    refine ⟨‖Planar.L0 - complementT - rankOneProj l q‖ + 1 * ‖seedRf l q qd hq hqd‖, ?_⟩
    intro n _ r
    exact norm_complementInteraction_le l q _ (hβ1 n) r
  case Aconv =>
    intro ε' hε'
    filter_upwards [eventually_const_mul_one_div_lt ‖seedRf l q qd hq hqd‖ hε'] with n hn p r
    exact (norm_complementInteraction_sub_le l q _ (hβb n) r).trans_lt
      (by simpa [mul_comm] using hn)
  case cpt =>
    exact fun _ _ => complementBaseCompact l q
  case tb =>
    refine (Set.finite_singleton (Planar.L0 - complementT - rankOneProj l q)).totallyBounded.subset ?_
    rintro _ ⟨x, rfl⟩
    rfl
  obtain ⟨n, hn⟩ := (key.2.2 ε hε).exists
  have h := hn () (s n + B) (s n) (by linarith) le_rfl
  have e : s n + B - s n = B := by ring
  simp only [e] at h
  exact absurd h (not_lt.2 (hs n))

end UnforcedLeray.Short.PartI
