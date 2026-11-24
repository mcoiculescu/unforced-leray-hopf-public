import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.CorrSliceContDiff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Lin2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawGood
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftBdd_Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletL0Transpose
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletAdvTranspose1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletAdvTranspose2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletPairSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2_1

/-!
# `Sub/PartII-b_S2_1.lean`: Decomposition of `IteratedDiffEqInYq` (`PartII-b:S2/1`, SP 2541-2559)

Source of record: `the November 2 reference manuscript`
(SP), lines 2541-2559.

## Proved here (zero `sorry`)

1. **Unconditional discharge of three upstream leaves**:
   * `ringLiftSmoothExt_s2_proof : RingLiftSmoothExt` from `PartIIa.ringAxisSmooth` (`PartII-a:R06`)
     and `ringLiftSmoothExt_of` (`PartII-b:R1/6`).
   * `rawResidualWeakIdentity_s2_proof : RawResidualWeakIdentity` from
     `PartIIIb.rawResidualWeakIdentity_of_lift` and `ringLiftSmoothExt_s2_proof`.
   * `PartIIIb.Concrete.rawJointSmooth : RawJointSmooth` (`PartIII-b:C/ward/12/3/1/2/6/1/1`).
2. **Iterated spatial derivatives on phase tests (`iterDy`, `iterDyRev`)**:
   * `isPhaseTest_iterDy`, `isSolTest_iterDy`, `contDiff_iterDy`, `iterDy_snoc`,
     `contDiff_iterDyRev`, `iterDyRev_snoc`.
3. **Solenoidality of all iterated phase gradients (`wOf_mem_Ysigma`, `isIteratedPhaseGrad_mem_Ysigma`,
   `next_phaseGrad_mem_Ysigma`)**:
   * `p.wOf z ∈ B0411.Ysigma p.period q0E`, and by induction on `k` via `HessEqSub.mem_Ysigma_of_dy`,
     every `gk α` and `G α j` lies in `B0411.Ysigma p.period q0E`.
4. **Order-0 weak form and `(k+1)`-st commutator identity on solenoidal tests
   (`projectedEquation_weak_zero`, `isIteratedPhaseGrad_l0T_sol`, `next_phaseGrad_l0T_sol`)**:
   * Iterating `HessComm.l0T_dy_fun` (`[∂_l, A₀] = ½ ∂_l`) along `IsIteratedPhaseGrad` and `G α j`
     gives the exact `(k + 1)`-st differentiated equation on solenoidal tests:
     `⟪L₀ᵗ Φ, G α j⟫ = ((k + 1)/2) ⟪Φ, G α j⟫ + (-1)^{k+1} projRHS p z gF gQ (iterDy (Fin.snoc α j) Φ)`.
5. **Full `(k + 2)`-order distributional derivative tower (`HasPhaseGradTower`,
   `wOf_hasPhaseGradTower`), `rawAllDerivsBdd_of_offAxis`, and all-orders linear convection
   (`convT_iterDy_pair_yq`, `iteratedLinDerivY_of_bdd`)**:
   * `rawAllDerivsBdd_of_offAxis` reduces `RawAllDerivsBdd` to `PartIIIb.Concrete.RingLiftOffAxisDerivBdd`
     via `ringBoundedDerivsUnif`, `ringAxisSmooth`, `ringLiftDerivBddOfSmooth_of`, and `raw_eq_of`.
   * `HessEqSub.freeGraphHessian_thm` upgrades `gk α ∈ D_p` and `G α j` to `(k + 2)`-nd derivatives
     in `Y_{q₀}`, giving `HasPhaseGradTower p.period q0E (k + 1) (p.wOf z)`.
   * By induction on `m` using `Lin2Sub.step_convT`, `Lin2Sub.convT_pair_yq`,
     `Lin2Sub.partialV_smoothPer`, and `Lin2Sub.iteratedFDeriv_partialV_le`, any smooth periodic
     field `V` with bounded spatial derivatives up to order `m + 1` satisfies
     `pairF P (convT V (iterDy β Φ)) (rep v) = phasePair P q0E Φ Fl` for some `Fl ∈ Y_{q₀}`.
6. **All-orders integration by parts on smooth fields (`pairF_iterDy_of_smooth`) and cylindrical
   envelope reductions (`iteratedRawDerivY_of_env`, `iteratedInletDerivY_of_envelope`)**:
   * `iteratedRawDerivY_of_env` proves `IteratedRawDerivY` from `RawResidualIteratedEnvelope` alone
     (discharging `RawResidualWeakIdentity` and `RingLiftSmoothExt` unconditionally).
   * `iteratedInletDerivY_of_envelope` reduces `IteratedInletDerivY` to `RawAllDerivsBdd` and the
     cylindrical decay envelope `InletResidualIteratedEnvelope` (`‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤ C * cylProfile R0 y`).
7. **Top-level assembly** (SP 2552-2557: "Inductively, if derivatives through order `k` are in
   the graph"). `IteratedQuadDerivY` and the step `IteratedDiffEqInYqAll` assume every order
   `j ≤ k` in `D_p`. `iteratedDiffEqInYqAll_of_sub` proves the step from the four leaves
   * `RawAllDerivsBdd` (`PartII-b:S2/1/1`),
   * `RawResidualIteratedEnvelope` (`PartII-b:S2/1/2`),
   * `IteratedInletDerivY` (`PartII-b:S2/1/3`),
   * `IteratedQuadDerivY` (`PartII-b:S2/1/4`);
   `iteratedDiffEqInYq_of_all` (cumulative induction `isIteratedPhaseGrad_all_of_upTo`, started by
   `StrongFirstDerivative`) gives the single-order `IteratedDiffEqInYq`, and
   `iteratedDiffEqInYq_of_sub` composes the two.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint
open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Iterated spatial derivatives on phase tests (`iterDy`, `iterDyRev`) -/

/-- Iterated spatial partial derivative `∂_{α(0)} ⋯ ∂_{α(k-1)} Φ` on `ℝ × Space → CVec3`, ordered so
that `iterDy (Fin.snoc α j) Φ = iterDy α (dy j Φ)`. -/
def iterDy : ∀ {k : ℕ}, (Fin k → Fin 3) → (ℝ × Space → CVec3) → (ℝ × Space → CVec3)
  | 0, _, Φ => Φ
  | k + 1, β, Φ => iterDy (Fin.init β) (dy (β (Fin.last k)) Φ)

/-- Reverse-ordered iterated spatial derivative `∂_{α(k-1)} ⋯ ∂_{α(0)} G` for integration by parts
against `iterDy α Φ`. -/
def iterDyRev : ∀ {k : ℕ}, (Fin k → Fin 3) → (ℝ × Space → CVec3) → (ℝ × Space → CVec3)
  | 0, _, G => G
  | k + 1, β, G => dy (β (Fin.last k)) (iterDyRev (Fin.init β) G)

/-- `HasPhaseGradTower P q m v`: `v : Yq P q` has distributional spatial derivatives in `Yq P q`
of all orders `1, …, m + 1`. -/
def HasPhaseGradTower (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ℕ → Yq P q → Prop
  | 0, v => ∃ v' : Fin 3 → Yq P q, ∀ l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ) v (v' l)
  | m + 1, v =>
      ∃ v' : Fin 3 → Yq P q,
        (∀ l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ) v (v' l)) ∧
        (∀ l : Fin 3, HasPhaseGradTower P q m (v' l))

namespace IterDiffEqSub

@[simp]
theorem iterDy_zero (α : Fin 0 → Fin 3) (Φ : ℝ × Space → CVec3) :
    iterDy α Φ = Φ :=
  rfl

@[simp]
theorem iterDy_snoc {k : ℕ} (α : Fin k → Fin 3) (j : Fin 3) (Φ : ℝ × Space → CVec3) :
    iterDy (Fin.snoc α j) Φ = iterDy α (dy j Φ) := by
  simp [iterDy]

theorem isPhaseTest_iterDy {P : ℝ} :
    ∀ {k : ℕ} (α : Fin k → Fin 3) {Φ : ℝ × Space → CVec3},
      IsPhaseTest P Φ → IsPhaseTest P (iterDy α Φ)
  | 0, _, _, hΦ => hΦ
  | k + 1, β, _, hΦ => isPhaseTest_iterDy (Fin.init β) (hΦ.dy (β (Fin.last k)))

theorem isSolTest_iterDy {P : ℝ} :
    ∀ {k : ℕ} (α : Fin k → Fin 3) {Φ : ℝ × Space → CVec3},
      IsSolTest P Φ → IsSolTest P (iterDy α Φ)
  | 0, _, _, hΦ => hΦ
  | k + 1, β, _, hΦ => isSolTest_iterDy (Fin.init β) (gEW_isSolTest_dy hΦ (β (Fin.last k)))

theorem contDiff_iterDy :
    ∀ {k : ℕ} (α : Fin k → Fin 3) {Φ : ℝ × Space → CVec3},
      ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ (iterDy α Φ)
  | 0, _, _, hΦ => hΦ
  | k + 1, β, _, hΦ =>
      contDiff_iterDy (Fin.init β) (UnforcedLeray.PhaseSpace.contDiff_dy hΦ (β (Fin.last k)))

@[simp]
theorem iterDyRev_snoc {k : ℕ} (α : Fin k → Fin 3) (j : Fin 3) (G : ℝ × Space → CVec3) :
    iterDyRev (Fin.snoc α j) G = dy j (iterDyRev α G) := by
  simp [iterDyRev]

theorem contDiff_iterDyRev :
    ∀ {k : ℕ} (α : Fin k → Fin 3) {G : ℝ × Space → CVec3},
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ (iterDyRev α G)
  | 0, _, _, hG => hG
  | k + 1, β, _, hG =>
      UnforcedLeray.PhaseSpace.contDiff_dy (contDiff_iterDyRev (Fin.init β) hG) (β (Fin.last k))

/-! ## 2. Solenoidality of all iterated phase gradients -/

theorem wOf_mem_Ysigma (p : Params) (z : p.Z) :
    p.wOf z ∈ B0411.Ysigma p.period q0E := by
  rw [B0411.mem_Ysigma]
  have hwX : p.wOf z ∈ B0412.X p.period p.ν q0E := (p.graphX z).property
  rcases B0412.mem_X.mp hwX with ⟨hdiv, _, _, _⟩
  simpa [Params.graphX] using hdiv

theorem isIteratedPhaseGrad_mem_Ysigma {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {u : Yq P q} (hu : u ∈ B0411.Ysigma P q) :
    ∀ {k : ℕ} {g : (Fin k → Fin 3) → Yq P q},
      IsIteratedPhaseGrad P q k u g → ∀ α : Fin k → Fin 3, g α ∈ B0411.Ysigma P q
  | 0, g, hg, α => by
      have hα : α = Fin.elim0 := Subsingleton.elim α Fin.elim0
      rw [hα, hg]
      exact hu
  | k + 1, g, ⟨g₀, hg₀, hop⟩, β => by
      have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last k)) := (Fin.snoc_init_self β).symm
      rw [hβ]
      exact HessEqSub.mem_Ysigma_of_dy (β (Fin.last k))
        (isIteratedPhaseGrad_mem_Ysigma hu hg₀ (Fin.init β))
        (hop (Fin.init β) (β (Fin.last k)))

theorem next_phaseGrad_mem_Ysigma {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {u : Yq P q} (hu : u ∈ B0411.Ysigma P q) {k : ℕ} {g : (Fin k → Fin 3) → Yq P q}
    (hg : IsIteratedPhaseGrad P q k u g) {G : (Fin k → Fin 3) → Fin 3 → Yq P q}
    (hG : ∀ (α : Fin k → Fin 3) (j : Fin 3), HasPhaseOp (fun Φ => -dy j Φ) (g α) (G α j))
    (α : Fin k → Fin 3) (j : Fin 3) :
    G α j ∈ B0411.Ysigma P q :=
  HessEqSub.mem_Ysigma_of_dy j (isIteratedPhaseGrad_mem_Ysigma hu hg α) (hG α j)

/-! ## 3. Order-0 weak form and `(k + 1)`-st commutator identity on solenoidal tests -/

/-- Order-0 source functional of the projected equation on solenoidal tests `Ψ`. -/
def projRHS (p : Params) (z : p.Z) (gF gQ : Yq p.period q0E)
    (Ψ : ℝ × Space → CVec3) : ℂ :=
  -(phasePair p.period q0E Ψ gF +
    phasePair p.period q0E Ψ gQ +
    pairF p.period (convT p.raw Ψ) (fun x => rep (p.wOf z) x.1 x.2) +
    ∑ i : Fin 2, (p.coord z i : ℂ) *
      (pairF p.period (B0411.L0T p.ν Ψ) (p.Efun i) +
        pairF p.period (convT p.raw Ψ) (p.Efun i)))

/-- Order-0 weak form of `ProjectedEquation p z` on solenoidal phase tests `Φ`. -/
theorem projectedEquation_weak_zero (p : Params) (z : p.Z)
    {gF gL gQ : Yq p.period q0E}
    (_hF : p.RawRel gF) (hL : p.OrdRel z gL) (_hQ : p.QuadRel z z gQ)
    (hsum : gF + gL + gQ = 0)
    (Φ : ℝ × Space → CVec3) (hΦ : IsSolTest p.period Φ) :
    phasePair p.period q0E (B0411.L0T p.ν Φ) (p.wOf z) =
      (0 : ℂ) * phasePair p.period q0E Φ (p.wOf z) + projRHS p z gF gQ Φ := by
  have HB := A0_phasePair_eq_L0T p (z := z) hΦ.1
  have HC := hL Φ hΦ
  have HS := congrArg (phasePair p.period q0E Φ) hsum
  rw [map_add, map_add, map_zero] at HS
  unfold projRHS
  linear_combination -HB - HC + HS

/-- Iterated commutator identity along `IsIteratedPhaseGrad` on solenoidal tests. -/
theorem isIteratedPhaseGrad_l0T_sol (p : Params) (z : p.Z)
    {gF gL gQ : Yq p.period q0E}
    (hF : p.RawRel gF) (hL : p.OrdRel z gL) (hQ : p.QuadRel z z gQ)
    (hsum : gF + gL + gQ = 0) :
    ∀ {k : ℕ} {g : (Fin k → Fin 3) → Yq p.period q0E},
      IsIteratedPhaseGrad p.period q0E k (p.wOf z) g →
      ∀ (α : Fin k → Fin 3) (Φ : ℝ × Space → CVec3), IsSolTest p.period Φ →
        phasePair p.period q0E (B0411.L0T p.ν Φ) (g α) =
          ((k : ℂ) / 2) * phasePair p.period q0E Φ (g α) +
            (-1 : ℂ) ^ k * projRHS p z gF gQ (iterDy α Φ)
  | 0, g, hg, α, Φ, hΦ => by
      have hα : α = Fin.elim0 := Subsingleton.elim α Fin.elim0
      rw [hα, hg]
      simpa using projectedEquation_weak_zero p z hF hL hQ hsum Φ hΦ
  | k + 1, g, ⟨g₀, hg₀, hop⟩, β, Φ, hΦ => by
      have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last k)) := (Fin.snoc_init_self β).symm
      set α : Fin k → Fin 3 := Fin.init β
      set l : Fin 3 := β (Fin.last k)
      rw [hβ]
      have key := HessComm.l0T_dy_fun (P := p.period) (q := q0E) p.ν
        (IsSolTest p.period) (fun _ h => h.1) (fun _ h l' => gEW_isSolTest_dy h l')
        l ((k : ℂ) / 2)
        (fun Ψ => (-1 : ℂ) ^ k * projRHS p z gF gQ (iterDy α Ψ))
        (u := g₀ α) (v := g (Fin.snoc α l))
        (fun Ψ hΨ => isIteratedPhaseGrad_l0T_sol p z hF hL hQ hsum hg₀ α Ψ hΨ)
        (hop α l) Φ hΦ
      beta_reduce at key
      rw [key, iterDy_snoc]
      push_cast
      ring

/-- The `(k + 1)`-st differentiated equation on solenoidal phase tests for `G α j`. -/
theorem next_phaseGrad_l0T_sol (p : Params) (z : p.Z)
    {gF gL gQ : Yq p.period q0E}
    (hF : p.RawRel gF) (hL : p.OrdRel z gL) (hQ : p.QuadRel z z gQ)
    (hsum : gF + gL + gQ = 0)
    {k : ℕ} {g : (Fin k → Fin 3) → Yq p.period q0E}
    (hg : IsIteratedPhaseGrad p.period q0E k (p.wOf z) g)
    {G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E}
    (hG : ∀ (α : Fin k → Fin 3) (j : Fin 3), HasPhaseOp (fun Φ => -dy j Φ) (g α) (G α j))
    (α : Fin k → Fin 3) (j : Fin 3) (Φ : ℝ × Space → CVec3) (hΦ : IsSolTest p.period Φ) :
    phasePair p.period q0E (B0411.L0T p.ν Φ) (G α j) =
      (((k + 1 : ℕ) : ℂ) / 2) * phasePair p.period q0E Φ (G α j) +
        (-1 : ℂ) ^ (k + 1) * projRHS p z gF gQ (iterDy (Fin.snoc α j) Φ) := by
  have key := HessComm.l0T_dy_fun (P := p.period) (q := q0E) p.ν
    (IsSolTest p.period) (fun _ h => h.1) (fun _ h l' => gEW_isSolTest_dy h l')
    j ((k : ℂ) / 2)
    (fun Ψ => (-1 : ℂ) ^ k * projRHS p z gF gQ (iterDy α Ψ))
    (u := g α) (v := G α j)
    (fun Ψ hΨ => isIteratedPhaseGrad_l0T_sol p z hF hL hQ hsum hg α Ψ hΨ)
    (hG α j) Φ hΦ
  beta_reduce at key
  rw [key, iterDy_snoc]
  push_cast
  ring

/-! ## 4. Distributional derivative tower and all-orders linear convection (`IteratedLinDerivY`) -/

theorem hasPhaseGradTower_pred {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] :
    ∀ {m : ℕ} {v : Yq P q}, HasPhaseGradTower P q (m + 1) v → HasPhaseGradTower P q m v
  | 0, _, ⟨v', hv', _⟩ => ⟨v', hv'⟩
  | _ + 1, _, ⟨v', hv', hrec⟩ => ⟨v', hv', fun l => hasPhaseGradTower_pred (hrec l)⟩

theorem hasPhaseGradTower_zero {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] :
    ∀ {m : ℕ} {v : Yq P q}, HasPhaseGradTower P q m v →
      ∃ v' : Fin 3 → Yq P q, ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) v (v' j)
  | 0, _, ⟨v', hv'⟩ => ⟨v', hv'⟩
  | _ + 1, _, ⟨v', hv', _⟩ => ⟨v', hv'⟩

theorem hasPhaseGradTower_of_isIteratedPhaseGrad {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] :
    ∀ {r : ℕ} {u : Yq P q} {gr : (Fin r → Fin 3) → Yq P q},
      IsIteratedPhaseGrad P q r u gr →
      ∀ {s : ℕ}, (∀ α : Fin r → Fin 3, HasPhaseGradTower P q s (gr α)) →
        HasPhaseGradTower P q (r + s) u
  | 0, u, gr, hgr, s, hs => by
      have h0 : HasPhaseGradTower P q s u := hgr ▸ hs Fin.elim0
      simpa using h0
  | r + 1, u, gr, ⟨g₀, hg₀, hop⟩, s, hs => by
      have hstep : ∀ α : Fin r → Fin 3, HasPhaseGradTower P q (s + 1) (g₀ α) :=
        fun α => ⟨fun j => gr (Fin.snoc α j), fun j => hop α j, fun j => hs (Fin.snoc α j)⟩
      have hrec := hasPhaseGradTower_of_isIteratedPhaseGrad hg₀ hstep
      have heq : r + (s + 1) = r + 1 + s := by omega
      rwa [heq] at hrec

/-- From `gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E` satisfying `IsIteratedPhaseGrad` and its
first derivatives `G α j : Yq p.period q0E`, `HessEqSub.freeGraphHessian_thm` upgrades `p.wOf z` to
`HasPhaseGradTower p.period q0E (k + 1) (p.wOf z)` when `p.period ≤ 1`. -/
theorem wOf_hasPhaseGradTower (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) (k : ℕ)
    (gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E)
    (hgk : IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (gk α : Yq p.period q0E)))
    (G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E)
    (hG : ∀ (α : Fin k → Fin 3) (j : Fin 3),
      HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (G α j)) :
    HasPhaseGradTower p.period q0E (k + 1) (p.wOf z) := by
  obtain ⟨_, -, hB⟩ := HessEqSub.freeGraphHessian_thm q0E q0E_gt_one B0412.q0E_lt_three
  have hgk_tower : ∀ α : Fin k → Fin 3,
      HasPhaseGradTower p.period q0E 1 (gk α : Yq p.period q0E) := by
    intro α
    obtain ⟨h, hh, -⟩ := hB p.period hP1 p.ν p.ν_pos 0
      (by simpa using gammaR_q0E_pos) (gk α) (G α) (fun j => hG α j)
    exact ⟨G α, fun j => hG α j, fun j => ⟨h j, fun m => hh j m⟩⟩
  exact hasPhaseGradTower_of_isIteratedPhaseGrad hgk hgk_tower

/-- Unconditional periodicity of `p.raw` on all of `ℝ × Space` (from `raw_periodic_off` and
`axisExt`). -/
theorem raw_periodic_everywhere (p : Params) (τ : ℝ) (y : Space) :
    p.raw (τ + p.period) y = p.raw τ y := by
  by_cases hy : y ∈ Axi.axis
  · have hev : (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
        (τ + p.period)) =ᶠ[𝓝[Axi.axisᶜ] y]
        (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have h1 := raw_periodic_off (p := p) τ hz
      rwa [p.raw_eq_off_axis _ z hz, p.raw_eq_off_axis _ z hz] at h1
    show UnforcedLeray.Cons.C03.Concrete.axisExt _ y = UnforcedLeray.Cons.C03.Concrete.axisExt _ y
    unfold UnforcedLeray.Cons.C03.Concrete.axisExt
    simp only [hy, ↓reduceIte, limUnder]
    rw [Filter.map_congr hev]
  · exact raw_periodic_off τ hy

/-- Spatial derivatives of `V` up to order `N` are uniformly bounded on `ℝ × Space`. -/
def HasBddUpTo (N : ℕ) (V : ℝ → SpatialField) : Prop :=
  ∀ n : ℕ, n ≤ N → ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ n (V τ) y‖ ≤ C

theorem hasBddUpTo_mono {M N : ℕ} (hMN : M ≤ N) {V : ℝ → SpatialField} (hV : HasBddUpTo N V) :
    HasBddUpTo M V :=
  fun n hn => hV n (hn.trans hMN)

theorem hasBdd01_of_hasBddUpTo_one {V : ℝ → SpatialField} (hV : HasBddUpTo 1 V) :
    Lin2Sub.HasBdd01 V :=
  ⟨hV 0 (Nat.zero_le 1), hV 1 le_rfl⟩

theorem partialV_hasBddUpTo {P : ℝ} {V : ℝ → SpatialField} (hVs : IsSmoothPer P V)
    {N : ℕ} (hVb : HasBddUpTo (N + 1) V) (l : Fin 3) :
    HasBddUpTo N (Lin2Sub.partialV V l) := by
  intro n hn
  obtain ⟨C, hC⟩ := hVb (n + 1) (Nat.add_le_add_right hn 1)
  exact ⟨C, fun τ y => (Lin2Sub.iteratedFDeriv_partialV_le hVs.1 l n τ y).trans (hC τ y)⟩

theorem iterDy_dy_comm :
    ∀ {m : ℕ} (α : Fin m → Fin 3) (l : Fin 3) {Φ : ℝ × Space → CVec3},
      ContDiff ℝ ∞ Φ → iterDy α (dy l Φ) = dy l (iterDy α Φ)
  | 0, _, _, _, _ => rfl
  | m + 1, α, l, Φ, hΦ => by
      simp only [iterDy]
      rw [PhaseSpace.dy_dy_comm hΦ (α (Fin.last m)) l,
        iterDy_dy_comm (Fin.init α) l (UnforcedLeray.PhaseSpace.contDiff_dy hΦ (α (Fin.last m)))]

/-- All-orders linear convection pairing in `Y_{q₀}`: if `V` is smooth, `P`-periodic, and has
bounded spatial derivatives up to order `m + 1`, and `v` satisfies `HasPhaseGradTower P q0E m v`,
then `pairF P (convT V (iterDy β Φ)) (rep v)` is represented by an element of `Yq P q0E` for every
`β : Fin m → Fin 3`. -/
theorem convT_iterDy_pair_yq {P : ℝ} [Fact (0 < P)] :
    ∀ {m : ℕ} {V : ℝ → SpatialField},
      IsSmoothPer P V → HasBddUpTo (m + 1) V →
      ∀ {v : Yq P q0E}, HasPhaseGradTower P q0E m v →
      ∀ (β : Fin m → Fin 3),
        ∃ F : Yq P q0E, ∀ Φ, IsPhaseTest P Φ →
          pairF P (convT V (iterDy β Φ)) (fun x => rep v x.1 x.2) =
            phasePair P q0E Φ F
  | 0, V, hVs, hVb, v, ⟨v', hv'⟩, β => by
      simpa only [iterDy_zero] using
        Lin2Sub.convT_pair_yq hVs (hasBdd01_of_hasBddUpTo_one hVb) v v' hv'
  | m + 1, V, hVs, hVb, v, hvt, β => by
      obtain ⟨v', hv', hrec⟩ := hvt
      set α : Fin m → Fin 3 := Fin.init β
      set l : Fin 3 := β (Fin.last m)
      have hβ : β = Fin.snoc α l := (Fin.snoc_init_self β).symm
      obtain ⟨F₁, hF₁⟩ := convT_iterDy_pair_yq hVs
        (hasBddUpTo_mono (Nat.le_succ (m + 1)) hVb) (hrec l) α
      obtain ⟨F₂, hF₂⟩ := convT_iterDy_pair_yq (Lin2Sub.partialV_smoothPer hVs l)
        (partialV_hasBddUpTo hVs hVb l) (hasPhaseGradTower_pred ⟨v', hv', hrec⟩) α
      refine ⟨-(F₁ + F₂), fun Φ hΦ => ?_⟩
      have hΨ : IsPhaseTest P (iterDy α Φ) := isPhaseTest_iterDy α hΦ
      have hstep : pairF P (convT V (iterDy β Φ)) (fun x => rep v x.1 x.2) =
          -pairF P (convT V (iterDy α Φ)) (fun x => rep (v' l) x.1 x.2) -
            pairF P (convT (Lin2Sub.partialV V l) (iterDy α Φ)) (fun x => rep v x.1 x.2) := by
        rw [hβ, iterDy_snoc, iterDy_dy_comm α l hΦ.smooth]
        exact Lin2Sub.step_convT hVs v v' hv' l (iterDy α Φ) hΨ
      rw [hstep, hF₁ Φ hΦ, hF₂ Φ hΦ, map_neg, map_add]
      ring

/-- Iterated integration by parts in `y` for `pairF` against any smooth field `G`:
`pairF P (iterDy β Φ) G = (-1)^m * pairF P Φ (iterDyRev β G)`. -/
theorem pairF_iterDy_of_smooth (P : ℝ) :
    ∀ {m : ℕ} (β : Fin m → Fin 3) {Φ G : ℝ × Space → CVec3},
      IsPhaseTest P Φ → ContDiff ℝ ∞ G →
      pairF P (iterDy β Φ) G = (-1 : ℂ) ^ m * pairF P Φ (iterDyRev β G)
  | 0, _, _, _, _, _ => by simp [iterDy, iterDyRev]
  | m + 1, β, Φ, G, hΦ, hG => by
      set α : Fin m → Fin 3 := Fin.init β
      set l : Fin 3 := β (Fin.last m)
      have hβ : β = Fin.snoc α l := (Fin.snoc_init_self β).symm
      rw [hβ, iterDy_snoc, iterDyRev_snoc,
        pairF_iterDy_of_smooth P α (hΦ.dy l) hG,
        pairF_dy_of_smooth P l hΦ (contDiff_iterDyRev α hG)]
      have hneg : pairF P Φ (-(dy l (iterDyRev α G))) = -pairF P Φ (dy l (iterDyRev α G)) := by
        unfold pairF phaseInt
        simp only [Pi.neg_apply, map_neg, integral_neg, smul_neg]
      rw [hneg, pow_succ]
      ring

theorem iterDyRev_eq_off_axis {F1 F2 : ℝ × Space → CVec3}
    (h : ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 → F1 x = F2 x) :
    ∀ {m : ℕ} (β : Fin m → Fin 3) {x : ℝ × Space}, Axi.ϱ x.2 ≠ 0 →
      iterDyRev β F1 x = iterDyRev β F2 x
  | 0, _, _, hx => h _ hx
  | m + 1, β, _, hx =>
      RawDeriv2EnvSub.dy_eq_off_axis
        (fun _ hz => iterDyRev_eq_off_axis h (Fin.init β) hz) (β (Fin.last m)) hx

/-- Unconditional proof of `RingLiftSmoothExt` from `PartIIa.ringAxisSmooth` (`PartII-a:R06`)
and `ringLiftSmoothExt_of` (`PartII-b:R1/6`). -/
theorem ringLiftSmoothExt_s2_proof : RingLiftSmoothExt :=
  ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth

/-- Unconditional proof of `RawResidualWeakIdentity` from `rawResidualWeakIdentity_of_lift`
and `ringLiftSmoothExt_s2_proof`. -/
theorem rawResidualWeakIdentity_s2_proof : RawResidualWeakIdentity :=
  UnforcedLeray.Short.PartIIIb.rawResidualWeakIdentity_of_lift ringLiftSmoothExt_s2_proof

end IterDiffEqSub

open IterDiffEqSub

/-! ## 5. Leaf propositions and reductions for `IteratedDiffEqInYq` (`PartII-b:S2/1`) -/

/-- **Globally bounded spatial derivatives of `p.raw τ` of all orders `n : ℕ` (`RawAllDerivsBdd`,
`PartII-b:S2/1/1`)** (`the November 2 reference manuscript`,
lines 1217-1219, 1322-1325, 2541-2559): below one threshold `ν₀` in the background regime, every
spatial derivative order `n : ℕ` of `p.raw τ` is uniformly bounded on `ℝ × Space`. -/
def RawAllDerivsBdd : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ n : ℕ, ∃ C : ℝ, ∀ (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ n (p.raw τ) y‖ ≤ C

/-- Reduction of `RawAllDerivsBdd` to `PartIIIb.Concrete.RingBoundedDerivsUnif` via `raw_eq_of`. -/
theorem rawAllDerivsBdd_of_unif (h : UnforcedLeray.Short.PartIIIb.Concrete.RingBoundedDerivsUnif) :
    RawAllDerivsBdd := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨min (ν₀ / 2) dm, lt_min (by linarith) hdm, fun p d hreg hν n => ?_⟩
  have hb := hreg.train_buc
  have hν1 : p.ν ≤ ν₀ / 2 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ dm := hν.trans (min_le_right _ _)
  obtain ⟨U, hU, hoff, C, hC⟩ := H p.ν ⟨p.ν_pos, by linarith⟩ _ _
    (isExactPlanarTrain_params_rpow p hb hreg.c_eq) p.R (R_ge_two hreg hν2) n
  refine ⟨C, fun τ y => ?_⟩
  have heq : p.raw τ = U τ :=
    raw_eq_of hb (fun x => U x.1 x.2) (fun t => (hU t).continuous) (fun x hx => hoff x.1 x.2 hx) τ
  rw [heq]
  exact hC τ y

/-- Reduction of `RawAllDerivsBdd` to `PartIIIb.Concrete.RingLiftOffAxisDerivBdd` using
`PartIIa.ringAxisSmooth` (`PartII-a:R06`), `ringLiftDerivBddOfSmooth_of`, and
`ringBoundedDerivsUnif`. -/
theorem rawAllDerivsBdd_of_offAxis
    (hOff : UnforcedLeray.Short.PartIIIb.Concrete.RingLiftOffAxisDerivBdd) :
    RawAllDerivsBdd :=
  rawAllDerivsBdd_of_unif
    (ringBoundedDerivsUnif UnforcedLeray.Short.PartIIa.ringAxisSmooth
      (ringLiftDerivBddOfSmooth_of hOff))

/-- `RawAllDerivsBdd` implies `PartIIIb.Concrete.RawDerivBdd` (orders `k : Fin 3`). -/
theorem rawDerivBdd_of_all (h : RawAllDerivsBdd) :
    UnforcedLeray.Short.PartIIIb.Concrete.RawDerivBdd := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h dm dp hdm
  exact ⟨ν₀, hν₀, fun p d hreg hν k => H p d hreg hν (k : ℕ)⟩

/-- All-orders linear convection leaf: for `k ≥ 1`, `gk α ∈ D_p`, and `G α j = ∂_j(gk α)`,
`pairF p.period (convT p.raw (iterDy β Φ)) (rep (p.wOf z))` is represented in `Yq p.period q0E`
for every `β : Fin (k + 1) → Fin 3`. -/
def IteratedLinDerivY : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      ∀ (z : p.Z) (k : ℕ), 1 ≤ k →
      ∀ gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (gk α : Yq p.period q0E)) →
      ∀ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
        (∀ (α : Fin k → Fin 3) (j : Fin 3),
          HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (G α j)) →
      ∀ β : Fin (k + 1) → Fin 3,
        ∃ Fl : Yq p.period q0E, ∀ Φ, IsSolTest p.period Φ →
          pairF p.period (convT p.raw (iterDy β Φ)) (fun x => rep (p.wOf z) x.1 x.2) =
            phasePair p.period q0E Φ Fl

/-- Complete proof of `IteratedLinDerivY` from `PartIIIb.Concrete.RawJointSmooth` and
`RawAllDerivsBdd`. -/
theorem iteratedLinDerivY_of (hSmooth : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth)
    (hBdd : RawAllDerivsBdd) :
    IteratedLinDerivY := by
  intro lam q _ dm dp hdm
  obtain ⟨ν₁, hν₁, HS⟩ := hSmooth dm dp hdm
  obtain ⟨ν₂, hν₂, HB⟩ := hBdd dm dp hdm
  have hν3 : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min ν₁ ν₂) (dm ^ 3 / 12), lt_min (lt_min hν₁ hν₂) hν3, ?_⟩
  intro p d hreg hν _ z k _ gk hgk G hG β
  have e1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : p.ν ≤ dm ^ 3 / 12 := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg e3
  have hVs : IsSmoothPer p.period p.raw := ⟨HS p d hreg e1, raw_periodic_everywhere p⟩
  have hVb : HasBddUpTo (k + 2) p.raw := fun n _ => HB p d hreg e2 n
  have hvt : HasPhaseGradTower p.period q0E (k + 1) (p.wOf z) :=
    wOf_hasPhaseGradTower p hP1 z k gk hgk G hG
  obtain ⟨Fl, hFl⟩ := convT_iterDy_pair_yq hVs hVb hvt β
  exact ⟨Fl, fun Φ hΦ => hFl Φ hΦ.1⟩

/-- Proof of `IteratedLinDerivY` from `RawAllDerivsBdd` alone (using the proved
`PartIIIb.Concrete.rawJointSmooth`). -/
theorem iteratedLinDerivY_of_bdd (hBdd : RawAllDerivsBdd) : IteratedLinDerivY :=
  iteratedLinDerivY_of UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth hBdd

/-- **All-orders cylindrical envelope of the raw ring residual off the axis
(`RawResidualIteratedEnvelope`, `PartII-b:S2/1/2`)**
(`the November 2 reference manuscript`,
lines 2542-2551). -/
def RawResidualIteratedEnvelope : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
    ∀ (m : ℕ) (β : Fin m → Fin 3),
      ∃ C R0 : ℝ, 0 < R0 ∧
        ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space,
          Axi.ϱ y ≠ 0 →
          ‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤ C * cylProfile R0 y

/-- All-orders raw residual leaf: `phasePair p.period q0E (iterDy β Φ) gF = phasePair p.period q0E Φ Fr`
on solenoidal phase tests for `p.RawRel gF` and `β : Fin (k + 1) → Fin 3` (SP 2542-2551). -/
def IteratedRawDerivY : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      ∀ gF : Yq p.period q0E, p.RawRel gF →
      ∀ (k : ℕ), 1 ≤ k → ∀ β : Fin (k + 1) → Fin 3,
        ∃ Fr : Yq p.period q0E, ∀ Φ, IsSolTest p.period Φ →
          phasePair p.period q0E (iterDy β Φ) gF = phasePair p.period q0E Φ Fr

/-- Proof of `IteratedRawDerivY` from `RawResidualWeakIdentity`, `RingLiftSmoothExt`, and
`RawResidualIteratedEnvelope` (all-orders generalization of `gERaw2_of` and
`rawResidualDeriv2Y_of_smooth_env`). -/
theorem iteratedRawDerivY_of_smooth_env
    (hWeak : RawResidualWeakIdentity)
    (hExt : RingLiftSmoothExt)
    (hEnv : RawResidualIteratedEnvelope) :
    IteratedRawDerivY := by
  obtain ⟨ν₁, hν₁, HWeak⟩ := hWeak
  obtain ⟨ν₂, hν₂, HExt⟩ := hExt
  obtain ⟨ν₃, hν₃, HEnv⟩ := hEnv
  intro lam q _ dm dp hdm
  have hν4 : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min (ν₁ / 2) (min (ν₂ / 2) (ν₃ / 2))) (min dm (dm ^ 3 / 12)),
    lt_min (lt_min (half_pos hν₁) (lt_min (half_pos hν₂) (half_pos hν₃))) (lt_min hdm hν4), ?_⟩
  intro p d hreg hν _ gF hF k _ β
  have e1 : p.ν ≤ ν₁ / 2 := (hν.trans (min_le_left _ _)).trans (min_le_left _ _)
  have e2 : p.ν ≤ ν₂ / 2 :=
    (hν.trans (min_le_left _ _)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ ν₃ / 2 :=
    (hν.trans (min_le_left _ _)).trans ((min_le_right _ _).trans (min_le_right _ _))
  have e4 : p.ν ≤ dm := (hν.trans (min_le_right _ _)).trans (min_le_left _ _)
  have e5 : p.ν ≤ dm ^ 3 / 12 := (hν.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hR : 2 ≤ p.R := two_le_R_of_regime hreg e4
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg e5
  obtain ⟨U, Pw, hU, hPw, -, -, hext⟩ :=
    HExt p.ν ⟨p.ν_pos, by linarith⟩ (trainStream p) (trainPressure p)
      (isExactPlanarTrain_params_rpow p hreg.train_buc hreg.c_eq) p.R hR
  obtain ⟨C, R0, hR0, henv⟩ :=
    HEnv p hreg.train_buc (by linarith) hreg.c_eq hR hP1 (k + 1) β
  let Fc : ℝ × Space → CVec3 :=
    fun x => B0411.L0 p.ν U x + advT U U x + gradT Pw x
  have hFc : ContDiff ℝ ∞ Fc := RawDeriv2EnvSub.contDiff_ns_rhs p.ν hU hPw
  have hoff : ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 → rawResidualC p x = Fc x := fun x hx =>
    ringResidualCartesianNS_proof p.ν p.c p.R (trainStream p) (trainPressure p)
      p.ν_pos p.c_pos hR (isExactPlanarTrain_params p hreg.train_buc) U Pw hU hPw hext x.1 x.2 hx
  let Fn : ℝ × Space → CVec3 := iterDyRev β Fc
  have hFn_smooth : ContDiff ℝ ∞ Fn := contDiff_iterDyRev β hFc
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p.period)) := ⟨by simp⟩
  have hg1 : MemLp (fun x : ℝ × Space => C * cylProfile R0 x.2) q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) :=
    ((cylProfile_memLp R0 hR0).const_mul C).comp_snd (volume.restrict (Ioc (0 : ℝ) p.period))
  have hFn_lp : MemLp Fn q0E ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) := by
    refine hg1.mono' hFn_smooth.continuous.aestronglyMeasurable ?_
    have hae1 : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod (volume : Measure Space)),
        x.1 ∈ Ioc (0 : ℝ) p.period :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hae2 : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod (volume : Measure Space)),
        x.2 ∉ Axi.axis :=
      Measure.quasiMeasurePreserving_snd.ae Axi.ae_not_mem_axis
    filter_upwards [hae1, hae2] with x hx1 hx2
    have hx0 : Axi.ϱ x.2 ≠ 0 := mt (Axi.mem_axis_iff x.2).mpr hx2
    have hd := iterDyRev_eq_off_axis hoff β hx0
    show ‖Fn x‖ ≤ C * cylProfile R0 x.2
    rw [show Fn x = iterDyRev β (rawResidualC p) x from hd.symm]
    exact henv x.1 hx1 x.2 hx0
  obtain ⟨G, hG⟩ := inletRepYq p.period Fn hFn_lp
  refine ⟨(-1 : ℂ) ^ (k + 1) • G, fun Φ hΦ => ?_⟩
  have hΨ : IsSolTest p.period (iterDy β Φ) := isSolTest_iterDy β hΦ
  rw [hF (iterDy β Φ) hΨ, HWeak p hreg.train_buc (by linarith) hreg.c_eq hR (iterDy β Φ) hΨ,
    RawDeriv2EnvSub.pairF_congr_off_axis p.period (iterDy β Φ) (rawResidualC p) Fc hoff,
    pairF_iterDy_of_smooth p.period β hΦ.1 hFc, map_smul, smul_eq_mul]
  congr 1
  rw [phasePair_eq_pairF_rep hΦ.1 G]
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hG] with t ht' ht
  refine integral_congr_ae ?_
  filter_upwards [ht' ht] with y hy
  rw [hy]

/-- Proof of `IteratedRawDerivY` from `RawResidualIteratedEnvelope` alone (using
`rawResidualWeakIdentity_s2_proof` and `ringLiftSmoothExt_s2_proof`). -/
theorem iteratedRawDerivY_of_env (hEnv : RawResidualIteratedEnvelope) : IteratedRawDerivY :=
  iteratedRawDerivY_of_smooth_env rawResidualWeakIdentity_s2_proof ringLiftSmoothExt_s2_proof hEnv

/-- **All-orders inlet source leaf (`IteratedInletDerivY`, `PartII-b:S2/1/3`)**
(`the November 2 reference manuscript`,
lines 2542-2551): for each column `i : Fin 2` and `β : Fin (k + 1) → Fin 3`,
`pairF p.period (L0T p.ν (iterDy β Φ)) (p.Efun i) + pairF p.period (convT p.raw (iterDy β Φ)) (p.Efun i)`
is represented in `Yq p.period q0E` on solenoidal phase tests. -/
def IteratedInletDerivY : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      ∀ (z : p.Z) (g0 : Fin 3 → Yq p.period q0E), GEData p z g0 →
      ∀ (i : Fin 2) (k : ℕ), 1 ≤ k → ∀ β : Fin (k + 1) → Fin 3,
        ∃ Fi : Yq p.period q0E, ∀ Φ, IsSolTest p.period Φ →
          pairF p.period (B0411.L0T p.ν (iterDy β Φ)) (p.Efun i) +
            pairF p.period (convT p.raw (iterDy β Φ)) (p.Efun i) =
              phasePair p.period q0E Φ Fi

/-- All-orders cylindrical envelope of the inlet source `inletSrc p i` (SP 2542-2551). -/
def InletResidualIteratedEnvelope : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      ∀ (i : Fin 2) (m : ℕ) (β : Fin m → Fin 3),
        ∃ C R0 : ℝ, 0 < R0 ∧
          ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space,
            ‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤ C * cylProfile R0 y

/-- Reduction of `IteratedInletDerivY` to `InletBackgroundBounds` (`PartIII-b:C/ward/12/3/1/2/5/1/2/2`)
and `InletResidualIteratedEnvelope` via `inletFieldRegularInf_of`, `inletL0Transpose_of`,
`inletAdvTranspose1_of`, `inletAdvTranspose2_of`, `inletPairSplit_of`, `pairF_iterDy_of_smooth`,
`cylProfile_memLp`, and `inletRepYq`. -/
theorem iteratedInletDerivY_of_envelope
    (hBg : InletBackgroundBounds)
    (hEnv : InletResidualIteratedEnvelope) :
    IteratedInletDerivY := by
  have hReg : InletFieldRegular :=
    inletFieldRegularInf_of UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth
  have hL0 := inletL0Transpose_of hReg
  have hA1 := inletAdvTranspose1_of hReg
  have hA2 := inletAdvTranspose2_of hReg
  have hPS := inletPairSplit_of hReg
  intro lam q hq dm dp hdm
  obtain ⟨ν_rj, hν_rj, HRJ⟩ := UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := hBg lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := hL0 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := hA1 lam q hq dm dp hdm
  obtain ⟨ν₃, hν₃, H3⟩ := hA2 lam q hq dm dp hdm
  obtain ⟨ν₄, hν₄, H4⟩ := hPS lam q hq dm dp hdm
  obtain ⟨ν₅, hν₅, HEnv⟩ := hEnv lam q hq dm dp hdm
  refine ⟨min (min ν_rj 1) (min (min ν₀ ν₁) (min (min ν₂ ν₃) (min ν₄ ν₅))),
    lt_min (lt_min hν_rj one_pos)
      (lt_min (lt_min hν₀ hν₁) (lt_min (lt_min hν₂ hν₃) (lt_min hν₄ hν₅))), ?_⟩
  intro p d hreg hν hm z g0 hg0 i k _ β
  have hν_rj' : p.ν ≤ ν_rj := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_1 : p.ν ≤ 1 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν0 : p.ν ≤ ν₀ :=
    hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν1 : p.ν ≤ ν₁ :=
    hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν2 : p.ν ≤ ν₂ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))))
  have hν3 : p.ν ≤ ν₃ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))))
  have hν4 : p.ν ≤ ν₄ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hν5 : p.ν ≤ ν₅ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨hraw_bg, hE_bg⟩ := H0 p d hreg hν0 hm z g0 hg0
  have hR_smooth : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) := HRJ p d hreg hν_rj'
  have hI_smooth : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    inlet_contDiff hq hreg hν_1 hm i
  have hE_smooth : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_comp hI_smooth
  have hSrc_smooth : ContDiff ℝ ∞ (inletSrc p i) := inletSrc_contDiff hE_smooth hR_smooth
  let Fn : ℝ × Space → CVec3 := iterDyRev β (inletSrc p i)
  have hFn_smooth : ContDiff ℝ ∞ Fn := contDiff_iterDyRev β hSrc_smooth
  obtain ⟨C, R0, hR0, henv⟩ := HEnv p d hreg hν5 hm i (k + 1) β
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p.period)) := ⟨by simp⟩
  have hg1 : MemLp (fun x : ℝ × Space => C * cylProfile R0 x.2) q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) :=
    ((cylProfile_memLp R0 hR0).const_mul C).comp_snd (volume.restrict (Ioc (0 : ℝ) p.period))
  have hFn_lp : MemLp Fn q0E ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) := by
    refine hg1.mono' hFn_smooth.continuous.aestronglyMeasurable ?_
    have hae : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod (volume : Measure Space)),
        x.1 ∈ Ioc (0 : ℝ) p.period :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with x hx
    exact henv x.1 hx x.2
  obtain ⟨G, hG⟩ := inletRepYq p.period Fn hFn_lp
  refine ⟨(-1 : ℂ) ^ (k + 1) • G, fun Φ hΦ => ?_⟩
  set ψ : ℝ × Space → CVec3 := iterDy β Φ
  have hψ : IsPhaseTest p.period ψ := isPhaseTest_iterDy β hΦ.1
  have hconv := UnforcedLeray.Cons.C03.Concrete.pairF_convT_boundedSolenoidal_convection_identity
    (P := p.period) hψ hraw_bg (hE_bg i).1 (hE_bg i).2
  have hconv' :
      pairF p.period (convT p.raw ψ) (p.Efun i) +
      pairF p.period (advT (p.Efun i) ψ) (fun x => realC (p.raw x.1 x.2)) +
      pairF p.period (advT (fun x => realC (p.raw x.1 x.2)) ψ) (p.Efun i) = 0 := hconv
  have e1 := H1 p d hreg hν1 hm z g0 hg0 i ψ hψ
  have e2 := H2 p d hreg hν2 hm z g0 hg0 i ψ hψ
  have e3 := H3 p d hreg hν3 hm z g0 hg0 i ψ hψ
  have e4 := H4 p d hreg hν4 hm z g0 hg0 i ψ hψ
  have hsrc_eq :
      pairF p.period (B0411.L0T p.ν ψ) (p.Efun i) + pairF p.period (convT p.raw ψ) (p.Efun i) =
        pairF p.period ψ (inletSrc p i) := by
    rw [e1]
    linear_combination hconv' - e2 - e3 - e4
  rw [hsrc_eq, pairF_iterDy_of_smooth p.period β hΦ.1 hSrc_smooth, map_smul, smul_eq_mul]
  congr 1
  rw [phasePair_eq_pairF_rep hΦ.1 G]
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hG] with t ht' ht
  refine integral_congr_ae ?_
  filter_upwards [ht' ht] with y hy
  rw [hy]

/-- **All-orders quadratic advection leaf (`IteratedQuadDerivY`, `PartII-b:S2/1/4`)**
(`the November 2 reference manuscript`,
lines 2552-2559): for `k ≥ 1`, if the iterated distributional spatial derivatives of `p.wOf z` of
every order `j ≤ k` lie in the maximal graph `D_p` (`g j hj`; "if derivatives through order `k` are
in the graph", lines 2552-2553), `G α l = ∂_l (g k le_rfl α)`, and `p.QuadRel z z gQ`
(`gQ = 𝐏(u · ∇u)`, `u = E_εα + w`), then
`phasePair p.period q0E (iterDy β Φ) gQ = phasePair p.period q0E Φ Fq` on solenoidal phase tests
for some `Fq : Yq p.period q0E`. Source argument (lines 2553-2556): all factors through order `k`
are bounded (`contRep_iterated_sum_sup_bound` on each `g j hj`), derivatives through order `k + 2`
are in `Y_p` (`wOf_hasPhaseGradTower`); in each order-`(k+1)` derivative of `u · ∇u` one factor has
order at most `k` and goes in `L^∞`, the other in `Y_p`. The age cut `Sig` is carried, as in the
consumer `IteratedDiffEqInYqAll`, so that all-order inlet bounds stated at fixed `Sig` apply. -/
def IteratedQuadDerivY : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (z : p.Z) (k : ℕ), 1 ≤ k →
      ∀ g : (j : ℕ) → j ≤ k → (Fin j → Fin 3) → B0411.D p.period p.ν q0E,
        (∀ (j : ℕ) (hj : j ≤ k), IsIteratedPhaseGrad p.period q0E j (p.wOf z)
          (fun α => (g j hj α : Yq p.period q0E))) →
      ∀ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
        (∀ (α : Fin k → Fin 3) (l : Fin 3),
          HasPhaseOp (fun Φ => -dy l Φ) (g k le_rfl α : Yq p.period q0E) (G α l)) →
      ∀ gQ : Yq p.period q0E, p.QuadRel z z gQ →
      ∀ β : Fin (k + 1) → Fin 3,
        ∃ Fq : Yq p.period q0E, ∀ Φ, IsSolTest p.period Φ →
          phasePair p.period q0E (iterDy β Φ) gQ = phasePair p.period q0E Φ Fq

/-! ## 6. Top-level assembly of `IteratedDiffEqInYq` (`PartII-b:S2/1`) -/

/-- **Induction step of `PartII-b:S2/1` with all lower orders in the graph
(`IteratedDiffEqInYqAll`)** (`the November 2 reference manuscript`,
lines 2541-2559): the hypotheses and conclusion of `IteratedDiffEqInYq`, except that the iterated
spatial derivatives of `p.wOf z` of every order `j ≤ k` (not only of order `k`) are assumed in
`D_p` ("Inductively, if derivatives through order `k` are in the graph", lines 2552-2553). -/
def IteratedDiffEqInYqAll : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig →
    Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      ∀ (k : ℕ), 1 ≤ k →
      ∀ g : (j : ℕ) → j ≤ k → (Fin j → Fin 3) → B0411.D p.period p.ν q0E,
        (∀ (j : ℕ) (hj : j ≤ k), IsIteratedPhaseGrad p.period q0E j (p.wOf z)
          (fun α => (g j hj α : Yq p.period q0E))) →
      ∀ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
        (∀ (α : Fin k → Fin 3) (l : Fin 3),
          HasPhaseOp (fun Φ => -dy l Φ) (g k le_rfl α : Yq p.period q0E) (G α l)) →
        ∀ (α : Fin k → Fin 3) (l : Fin 3), ∃ F : Yq p.period q0E,
          HasPhaseOp (fun Φ => (0 : ℂ) • Φ + B0411.L0T p.ν Φ) (G α l) F

/-- Assembly of `IteratedDiffEqInYqAll` from `IteratedRawDerivY`, `IteratedInletDerivY`,
`IteratedLinDerivY`, and `IteratedQuadDerivY`, via the `(k+1)`-st commutator identity
`next_phaseGrad_l0T_sol`, solenoidality `next_phaseGrad_mem_Ysigma`, and the solenoidal lift
`HessEqSub.solLift_of gEBodyUniqueSol_proof` (SP 2552-2557). -/
theorem iteratedDiffEqInYqAll_of
    (hRaw : IteratedRawDerivY)
    (hInlet : IteratedInletDerivY)
    (hLin : IteratedLinDerivY)
    (hQuad : IteratedQuadDerivY) :
    IteratedDiffEqInYqAll := by
  intro Sig lam q hSig hq m _ dm dp hdm _ C₁ k₁ _
  obtain ⟨ν_r, hν_r, HRaw⟩ := hRaw lam q hq dm dp hdm
  obtain ⟨ν_i, hν_i, HInlet⟩ := hInlet lam q hq dm dp hdm
  obtain ⟨ν_l, hν_l, HLin⟩ := hLin lam q hq dm dp hdm
  obtain ⟨ν_q, hν_q, HQuad⟩ := hQuad Sig lam q hSig hq dm dp hdm
  have hν_p : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min (min ν_r ν_i) (min ν_l ν_q)) (dm ^ 3 / 12),
    lt_min (lt_min (lt_min hν_r hν_i) (lt_min hν_l hν_q)) hν_p, ?_⟩
  intro p d hreg hν hSg hmode z hPE _ k hk g hg G hG α j
  have er : p.ν ≤ ν_r :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have ei : p.ν ≤ ν_i :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have el : p.ν ≤ ν_l :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have eq : p.ν ≤ ν_q :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ep : p.ν ≤ dm ^ 3 / 12 := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg ep
  have hgk := hg k le_rfl
  obtain ⟨g0, hg0⟩ :=
    hasPhaseGradTower_zero (wOf_hasPhaseGradTower p hP1 z k (g k le_rfl) hgk G hG)
  have hg_data : GEData p z g0 := ⟨hPE, hg0⟩
  obtain ⟨gF, gL, gQ, hF, hL, hQ, hsum⟩ := hPE
  set β : Fin (k + 1) → Fin 3 := Fin.snoc α j
  obtain ⟨Fr, hFr⟩ := HRaw p d hreg er hmode gF hF k hk β
  choose Fi hFi using fun i : Fin 2 => HInlet p d hreg ei hmode z g0 hg_data i k hk β
  obtain ⟨Fl, hFl⟩ := HLin p d hreg el hmode z k hk (g k le_rfl) hgk G hG β
  obtain ⟨Fq, hFq⟩ := HQuad p d hreg eq hSg hmode z k hk g hg G hG gQ hQ β
  let F_src : Yq p.period q0E :=
    Fr + Fq + Fl + ∑ i : Fin 2, (p.coord z i : ℂ) • Fi i
  let F_rhs : Yq p.period q0E :=
    (((k + 1 : ℕ) : ℂ) / 2) • G α j - (-1 : ℂ) ^ (k + 1) • F_src
  have hsol : ∀ Φ, IsSolTest p.period Φ →
      phasePair p.period q0E (B0411.L0T p.ν Φ) (G α j) =
        phasePair p.period q0E Φ F_rhs := by
    intro Φ hΦ
    have hcomm := next_phaseGrad_l0T_sol p z hF hL hQ hsum hgk hG α j Φ hΦ
    change phasePair p.period q0E (B0411.L0T p.ν Φ) (G α j) =
      (((k + 1 : ℕ) : ℂ) / 2) * phasePair p.period q0E Φ (G α j) +
        (-1 : ℂ) ^ (k + 1) * projRHS p z gF gQ (iterDy β Φ) at hcomm
    have hRHS : projRHS p z gF gQ (iterDy β Φ) = -phasePair p.period q0E Φ F_src := by
      unfold projRHS F_src
      rw [hFr Φ hΦ, hFq Φ hΦ, hFl Φ hΦ,
        Finset.sum_congr rfl (fun i _ => by rw [hFi i Φ hΦ])]
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
    rw [hcomm, hRHS]
    dsimp only [F_rhs]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hGσ : G α j ∈ B0411.Ysigma p.period q0E :=
    next_phaseGrad_mem_Ysigma (wOf_mem_Ysigma p z) hgk hG α j
  exact ⟨_, HessEqSub.solLift_of gEBodyUniqueSol_proof p.period p.ν hP1 p.ν_pos (G α j) F_rhs hGσ hsol⟩

/-- **Assembly of `IteratedDiffEqInYqAll` (`PartII-b:S2/1`, SP 2541-2559)** from the four remaining
leaves `RawAllDerivsBdd` (`PartII-b:S2/1/1`), `RawResidualIteratedEnvelope` (`PartII-b:S2/1/2`),
`IteratedInletDerivY` (`PartII-b:S2/1/3`), and `IteratedQuadDerivY` (`PartII-b:S2/1/4`),
discharging `RawResidualWeakIdentity`, `RingLiftSmoothExt`, and `RawJointSmooth` unconditionally. -/
theorem iteratedDiffEqInYqAll_of_sub
    (hRawBdd : RawAllDerivsBdd)
    (hRawEnv : RawResidualIteratedEnvelope)
    (hInlet : IteratedInletDerivY)
    (hQuad : IteratedQuadDerivY) :
    IteratedDiffEqInYqAll :=
  iteratedDiffEqInYqAll_of
    (iteratedRawDerivY_of_smooth_env rawResidualWeakIdentity_s2_proof ringLiftSmoothExt_s2_proof
      hRawEnv)
    hInlet
    (iteratedLinDerivY_of UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth hRawBdd)
    hQuad

namespace IterDiffEqSub

/-- Splice a family `gk` of order `k` into a family `gA` of all orders. -/
def spliceTop {D : ℕ → Type*} (k : ℕ) (gk : D k) (gA : ∀ j, D j) (j : ℕ) : D j :=
  if h : j = k then h ▸ gk else gA j

theorem spliceTop_self {D : ℕ → Type*} (k : ℕ) (gk : D k) (gA : ∀ j, D j) :
    spliceTop k gk gA k = gk := by
  unfold spliceTop
  rw [dif_pos rfl]

theorem spliceTop_prop {D : ℕ → Type*} (P : ∀ j, D j → Prop) (k : ℕ) (gk : D k)
    (gA : ∀ j, D j) (hk : P k gk) (hA : ∀ j, P j (gA j)) (j : ℕ) :
    P j (spliceTop k gk gA j) := by
  unfold spliceTop
  by_cases h : j = k
  · rw [dif_pos h]
    subst h
    exact hk
  · rw [dif_neg h]
    exact hA j

/-- Cumulative bootstrap (SP 2552-2557): from first derivatives `g₁` in `D_p`
(`StrongFirstDerivative`, `PartII-b:S1`) and the induction step with all lower orders in the graph,
the iterated spatial derivatives of `p.wOf z` of every order `n` lie in `D_p`. -/
theorem isIteratedPhaseGrad_all_of_upTo (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (g₁ : Fin 3 → B0411.D p.period p.ν q0E)
    (hg₁ : ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g₁ j : Yq p.period q0E))
    (hStep : ∀ (k : ℕ), 1 ≤ k →
      ∀ g : (j : ℕ) → j ≤ k → (Fin j → Fin 3) → B0411.D p.period p.ν q0E,
        (∀ (j : ℕ) (hj : j ≤ k), IsIteratedPhaseGrad p.period q0E j (p.wOf z)
          (fun α => (g j hj α : Yq p.period q0E))) →
      ∀ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
        (∀ (α : Fin k → Fin 3) (l : Fin 3),
          HasPhaseOp (fun Φ => -dy l Φ) (g k le_rfl α : Yq p.period q0E) (G α l)) →
        ∀ (α : Fin k → Fin 3) (l : Fin 3), ∃ F : Yq p.period q0E,
          HasPhaseOp (fun Φ => (0 : ℂ) • Φ + B0411.L0T p.ν Φ) (G α l) F) :
    ∀ n : ℕ, ∃ g : (Fin n → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E n (p.wOf z) (fun α => (g α : Yq p.period q0E)) := by
  have hcum : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → ∃ g : (Fin j → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E j (p.wOf z) (fun α => (g α : Yq p.period q0E)) := by
    intro n
    induction n with
    | zero =>
        intro j hj
        obtain rfl : j = 0 := Nat.le_zero.mp hj
        exact ⟨fun _ => B0412.XToD (p.graphX z), isIteratedPhaseGrad_zero p z⟩
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n + 1) with hlt | hge
        · exact ih j (Nat.lt_succ_iff.mp hlt)
        · obtain rfl : j = n + 1 := le_antisymm hj hge
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · exact ⟨fun α => g₁ (α 0), isIteratedPhaseGrad_one_of_first p z g₁ hg₁⟩
          · choose g hg using ih
            obtain ⟨G, hG⟩ := exists_next_phaseGrad_in_Yq p hP1 n (g n le_rfl)
            exact isIteratedPhaseGrad_succ_of_eq p hP1 z n (g n le_rfl) (hg n le_rfl) G hG
              (hStep n hn g hg G hG)
  exact fun n => hcum n n le_rfl

end IterDiffEqSub

/-- **`IteratedDiffEqInYq` from the all-lower-orders step (`PartII-b:S2/1`, SP 2541-2559)**: the
induction of SP 2552-2557, started at order one by `StrongFirstDerivative` (`PartII-b:S1`, display
`short-bg:strong`, SP 2525-2541), puts every lower order in `D_p`; splicing the given order-`k`
family on top and applying `IteratedDiffEqInYqAll` gives the single-order statement. -/
theorem iteratedDiffEqInYq_of_all (hAll : IteratedDiffEqInYqAll)
    (hS1 : StrongFirstDerivative) : IteratedDiffEqInYq := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨_, _, ν_s, _, hν_s, HS1⟩ := hS1 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν_a, hν_a, HAll⟩ := hAll Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  have hν_p : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min ν_s ν_a) (dm ^ 3 / 12), lt_min (lt_min hν_s hν_a) hν_p, ?_⟩
  intro p d hreg hν hSg hmode z hPE hz k hk gk hgk G hG
  have es : p.ν ≤ ν_s := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ea : p.ν ≤ ν_a := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg (hν.trans (min_le_right _ _))
  obtain ⟨⟨g₁, hg₁⟩, -⟩ := HS1 p d hreg es hSg hmode z hPE hz
  have hstep := HAll p d hreg ea hSg hmode z hPE hz
  choose gA hgA using isIteratedPhaseGrad_all_of_upTo p hP1 z g₁ hg₁ hstep
  have hall : ∀ j : ℕ, IsIteratedPhaseGrad p.period q0E j (p.wOf z)
      (fun α => (spliceTop (D := fun j => (Fin j → Fin 3) → B0411.D p.period p.ν q0E)
        k gk gA j α : Yq p.period q0E)) :=
    spliceTop_prop (D := fun j => (Fin j → Fin 3) → B0411.D p.period p.ν q0E)
      (fun j g => IsIteratedPhaseGrad p.period q0E j (p.wOf z) (fun α => (g α : Yq p.period q0E)))
      k gk gA hgk hgA
  have htop : spliceTop (D := fun j => (Fin j → Fin 3) → B0411.D p.period p.ν q0E) k gk gA k = gk :=
    spliceTop_self (D := fun j => (Fin j → Fin 3) → B0411.D p.period p.ν q0E) k gk gA
  refine hstep k hk
    (fun j _ => spliceTop (D := fun j => (Fin j → Fin 3) → B0411.D p.period p.ν q0E) k gk gA j)
    (fun j _ => hall j) G ?_
  intro α l
  simp only [htop]
  exact hG α l

/-- **Assembly of `IteratedDiffEqInYq` (`PartII-b:S2/1`, SP 2541-2559)** from the four remaining
leaves `RawAllDerivsBdd` (`PartII-b:S2/1/1`), `RawResidualIteratedEnvelope` (`PartII-b:S2/1/2`),
`IteratedInletDerivY` (`PartII-b:S2/1/3`), and `IteratedQuadDerivY` (`PartII-b:S2/1/4`), together
with `StrongFirstDerivative` (`PartII-b:S1`), which starts the induction at order one. -/
theorem iteratedDiffEqInYq_of_sub
    (hRawBdd : RawAllDerivsBdd)
    (hRawEnv : RawResidualIteratedEnvelope)
    (hInlet : IteratedInletDerivY)
    (hQuad : IteratedQuadDerivY)
    (hS1 : StrongFirstDerivative) :
    IteratedDiffEqInYq :=
  iteratedDiffEqInYq_of_all (iteratedDiffEqInYqAll_of_sub hRawBdd hRawEnv hInlet hQuad) hS1

end UnforcedLeray.Short.IIb

end
