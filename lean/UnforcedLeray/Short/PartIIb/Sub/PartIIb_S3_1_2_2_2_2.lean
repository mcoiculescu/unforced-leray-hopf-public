import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2_1

/-!
# `PartII-b:S3/1/2/2/2/2` decomposition (`Sub/PartII-b_S3_1_2_2_2_2.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives, so $U$ is jointly smooth through the axis."

## Proved here (zero `sorry`)

1. **All-order iterated radial-drift commutator recurrence and `L⁴(ℝ³)` bound**
   (`namespace BaseIteratedRadialDriftSub`):
   - `iterate_spatialRadialDrift_dirSpatialJet_succ`:
     for every smooth `F : SpatialField`, `ws : List Space`, and `m j : ℕ`,
     `(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m + 1]) F) ws) = (spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) + (ws.length : ℝ) • (spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws)`;
   - `eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le` and
     `eLpNorm_dirSpatialJet_iterate_spatialRadialDrift_coordWord_le`:
     by induction on `m : ℕ` (generalizing `j : ℕ`), bounds the `L⁴(ℝ³)` norm of
     `dirSpatialJet ((spatialRadialDrift^[r]) F) (coordWord α)` by
     `ENNReal.ofReal ((1 + (k : ℝ)) ^ r * M)` whenever all order-`0` iterated radial drifts
     `(spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α))` (`i ≤ r`) have `L⁴(ℝ³)` norm at most
     `ENNReal.ofReal M`;
   - `exists_iteratedFDeriv_iterate_spatialRadialDrift_l4_of_coordJet`:
     combines `RadialDriftL4Sub.eLpNorm_iteratedFDeriv_le_sum_coordWord` with
     `eLpNorm_dirSpatialJet_iterate_spatialRadialDrift_coordWord_le` to reduce uniform `L⁴(ℝ³)` bounds
     on `iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) (U₀ τ))` across all `r, k : ℕ` to order-`0`
     `L⁴(ℝ³)` bounds on `(spatialRadialDrift^[i]) (dirSpatialJet (U₀ τ) (coordWord α))`.
2. **Background piece decomposition for `(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)`**:
   - `iterate_spatialRadialDrift_dirSpatialJet_bgField_eq`,
     `norm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le`, and
     `eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le`:
     decomposes `(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)` into the sum of the
     `i`-fold radial drifts of the `p.raw`, `p.inlet l`, and `p.corr z` spatial jets and bounds its
     `L⁴(ℝ³)` norm by the sum of the piece `L⁴(ℝ³)` norms.
3. **Atomic piece leaves and conditional assembly of `BgBaseIteratedRadialDriftSlice`**:
   - `BgCoordJetIteratedRadialDriftL4`,
     `RawAndInletCoordJetIteratedRadialDriftL4` (`PartII-b:S3/1/2/2/2/2/1`), and
     `CorrCoordJetIteratedRadialDriftL4` (`PartII-b:S3/1/2/2/2/2/2`);
   - `bgCoordJetIteratedRadialDriftL4_of_pieces`, `bgBaseIteratedRadialDriftSlice_of`, and
     `bgBaseIteratedRadialDriftSlice_of_pieces`: conditional assembly of
     `BgBaseIteratedRadialDriftSlice` (`PartII-b:S3/1/2/2/2/2`) via
     `RadialDriftTowerSub.isIteratedRadialDriftSliceFamily_of_succ_succ_l4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

local instance fact_one_le_four_bird : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace BaseIteratedRadialDriftSub

open PhaseDerivStepSub SmoothLeraySliceSub ProjectedEvolutionSub
  RadialDriftL4Sub RadialDriftTowerSub

/-! ## 1. All-order iterated radial-drift commutator recurrence and `L⁴(ℝ³)` reduction -/

/-- Exact two-parameter commutator recurrence for `(spatialRadialDrift^[j])` and `dirSpatialJet · ws`
applied to `(spatialRadialDrift^[m + 1]) F`:
`(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m + 1]) F) ws) = (spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) + (ws.length : ℝ) • (spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws)`. -/
theorem iterate_spatialRadialDrift_dirSpatialJet_succ
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (ws : List Space) (m j : ℕ) :
    (spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m + 1]) F) ws) =
      (spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) +
        (ws.length : ℝ) •
          (spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) := by
  set G : SpatialField := (spatialRadialDrift^[m]) F
  have hG : ContDiff ℝ ∞ G := contDiff_infty_iterate_spatialRadialDrift m hF
  have hjetG : ContDiff ℝ ∞ (dirSpatialJet G ws) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hG ws
  have hrad_jetG : ContDiff ℝ ∞ (spatialRadialDrift (dirSpatialJet G ws)) :=
    HigherPhaseSub.contDiff_infty_spatialRadialDrift hjetG
  have hsmul_jetG : ContDiff ℝ ∞ ((ws.length : ℝ) • dirSpatialJet G ws) :=
    hjetG.const_smul (ws.length : ℝ)
  have hsucc : (spatialRadialDrift^[m + 1]) F = spatialRadialDrift G :=
    Function.iterate_succ_apply' spatialRadialDrift m F
  rw [hsucc, PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift hG ws,
    iterate_spatialRadialDrift_add j hrad_jetG hsmul_jetG,
    iterate_spatialRadialDrift_smul j (ws.length : ℝ) hjetG,
    ← Function.iterate_succ_apply spatialRadialDrift j (dirSpatialJet G ws)]

/-- Pointwise bound on `(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y`
by induction on `m : ℕ` (generalizing `j : ℕ`). -/
theorem norm_iterate_spatialRadialDrift_dirSpatialJet_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (ws : List Space) (y : Space) :
    ∀ (m j : ℕ) {B : ℝ}, 0 ≤ B →
      (∀ i ≤ m + j, ‖(spatialRadialDrift^[i]) (dirSpatialJet F ws) y‖ ≤ B) →
      ‖(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y‖ ≤
        (1 + (ws.length : ℝ)) ^ m * B
  | 0, j, B, _, hB => by
      simpa using hB j (by omega)
  | m + 1, j, B, hB0, hB => by
      have hrec := congrFun (iterate_spatialRadialDrift_dirSpatialJet_succ hF ws m j) y
      rw [hrec, Pi.add_apply, Pi.smul_apply]
      have ih1 :
          ‖(spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y‖ ≤
            (1 + (ws.length : ℝ)) ^ m * B :=
        norm_iterate_spatialRadialDrift_dirSpatialJet_le hF ws y m (j + 1) hB0
          (fun i hi => hB i (by omega))
      have ih2 :
          ‖(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y‖ ≤
            (1 + (ws.length : ℝ)) ^ m * B :=
        norm_iterate_spatialRadialDrift_dirSpatialJet_le hF ws y m j hB0
          (fun i hi => hB i (by omega))
      calc ‖(spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y +
              (ws.length : ℝ) •
                (spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y‖
          ≤ ‖(spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y‖ +
              (ws.length : ℝ) *
                ‖(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) y‖ := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
        _ ≤ (1 + (ws.length : ℝ)) ^ m * B +
              (ws.length : ℝ) * ((1 + (ws.length : ℝ)) ^ m * B) :=
            add_le_add ih1 (mul_le_mul_of_nonneg_left ih2 (Nat.cast_nonneg _))
        _ = (1 + (ws.length : ℝ)) ^ (m + 1) * B := by
            rw [pow_succ']
            ring

/-- `L⁴(ℝ³)` bound on `(spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws)`
by induction on `m : ℕ` (generalizing `j : ℕ`). -/
theorem eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (ws : List Space) :
    ∀ (m j : ℕ) {M : ℝ}, 0 ≤ M →
      (∀ i ≤ m + j,
        eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet F ws)) 4 volume ≤ ENNReal.ofReal M) →
      eLpNorm ((spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws)) 4 volume ≤
        ENNReal.ofReal ((1 + (ws.length : ℝ)) ^ m * M)
  | 0, j, M, _, hM => by
      simpa using hM j (by omega)
  | m + 1, j, M, hM0, hM => by
      rw [iterate_spatialRadialDrift_dirSpatialJet_succ hF ws m j]
      set g₁ : SpatialField :=
        (spatialRadialDrift^[j + 1]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws)
      set g₂ : SpatialField :=
        (spatialRadialDrift^[j]) (dirSpatialJet ((spatialRadialDrift^[m]) F) ws)
      have hjet_cd : ContDiff ℝ ∞ (dirSpatialJet ((spatialRadialDrift^[m]) F) ws) :=
        JointSmoothSub.contDiff_infty_dirSpatialJet
          (contDiff_infty_iterate_spatialRadialDrift m hF) ws
      have hg₁_meas : AEStronglyMeasurable g₁ volume :=
        (contDiff_infty_iterate_spatialRadialDrift (j + 1) hjet_cd).continuous.aestronglyMeasurable
      have hg₂_meas : AEStronglyMeasurable ((ws.length : ℝ) • g₂) volume :=
        ((contDiff_infty_iterate_spatialRadialDrift j hjet_cd).const_smul
          (ws.length : ℝ)).continuous.aestronglyMeasurable
      have ih1 : eLpNorm g₁ 4 volume ≤ ENNReal.ofReal ((1 + (ws.length : ℝ)) ^ m * M) :=
        eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le hF ws m (j + 1) hM0
          (fun i hi => hM i (by omega))
      have ih2 : eLpNorm g₂ 4 volume ≤ ENNReal.ofReal ((1 + (ws.length : ℝ)) ^ m * M) :=
        eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le hF ws m j hM0
          (fun i hi => hM i (by omega))
      have htri : eLpNorm (g₁ + (ws.length : ℝ) • g₂) 4 volume ≤
          eLpNorm g₁ 4 volume + ENNReal.ofReal (ws.length : ℝ) * eLpNorm g₂ 4 volume := by
        refine (eLpNorm_add_le hg₁_meas hg₂_meas (by norm_num)).trans (add_le_add le_rfl ?_)
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg (Nat.cast_nonneg _)]
      have hA0 : 0 ≤ (1 + (ws.length : ℝ)) ^ m * M := by positivity
      calc eLpNorm (g₁ + (ws.length : ℝ) • g₂) 4 volume
          ≤ eLpNorm g₁ 4 volume + ENNReal.ofReal (ws.length : ℝ) * eLpNorm g₂ 4 volume := htri
        _ ≤ ENNReal.ofReal ((1 + (ws.length : ℝ)) ^ m * M) +
              ENNReal.ofReal (ws.length : ℝ) *
                ENNReal.ofReal ((1 + (ws.length : ℝ)) ^ m * M) :=
            add_le_add ih1 (mul_le_mul_of_nonneg_left ih2 zero_le)
        _ = ENNReal.ofReal ((1 + (ws.length : ℝ)) ^ (m + 1) * M) := by
            rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ← ENNReal.ofReal_add hA0 (mul_nonneg (Nat.cast_nonneg _) hA0), pow_succ']
            congr 1
            ring

/-- Specialization to `j = 0`, `m = r`, and `ws = coordWord α` (`α : Fin k → Fin 3`). -/
theorem eLpNorm_dirSpatialJet_iterate_spatialRadialDrift_coordWord_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (r : ℕ) {k : ℕ} (α : Fin k → Fin 3)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i ≤ r,
      eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α))) 4 volume ≤
        ENNReal.ofReal M) :
    eLpNorm (dirSpatialJet ((spatialRadialDrift^[r]) F) (coordWord α)) 4 volume ≤
      ENNReal.ofReal ((1 + (k : ℝ)) ^ r * M) := by
  have h := eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le hF (coordWord α) r 0 hM0
    (by simpa using hM)
  simpa [coordWord_length] using h

/-- All-order `L⁴(ℝ³)` bound on `iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) F)` from order-`0`
bounds on `(spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α))` for `i ≤ r`. -/
theorem eLpNorm_iteratedFDeriv_iterate_spatialRadialDrift_le
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (r k : ℕ)
    {M : (Fin k → Fin 3) → ℝ} (hM0 : ∀ α : Fin k → Fin 3, 0 ≤ M α)
    (hM : ∀ (α : Fin k → Fin 3) (i : ℕ), i ≤ r →
      eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α))) 4 volume ≤
        ENNReal.ofReal (M α)) :
    eLpNorm (fun y => iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) F) y) 4 volume ≤
      ENNReal.ofReal ((1 + (k : ℝ)) ^ r * ∑ α : Fin k → Fin 3, M α) := by
  have hrad : ContDiff ℝ ∞ ((spatialRadialDrift^[r]) F) :=
    contDiff_infty_iterate_spatialRadialDrift r hF
  calc eLpNorm (fun y => iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) F) y) 4 volume
      ≤ ∑ α : Fin k → Fin 3,
          eLpNorm (dirSpatialJet ((spatialRadialDrift^[r]) F) (coordWord α)) 4 volume :=
        eLpNorm_iteratedFDeriv_le_sum_coordWord hrad k
    _ ≤ ∑ α : Fin k → Fin 3, ENNReal.ofReal ((1 + (k : ℝ)) ^ r * M α) :=
        Finset.sum_le_sum fun α _ =>
          eLpNorm_dirSpatialJet_iterate_spatialRadialDrift_coordWord_le hF r α (hM0 α) (hM α)
    _ = ENNReal.ofReal ((1 + (k : ℝ)) ^ r * ∑ α : Fin k → Fin 3, M α) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        intro α _
        exact mul_nonneg (by positivity) (hM0 α)

/-- Given order-`0` `L⁴(ℝ³)` bounds on `(spatialRadialDrift^[i]) (dirSpatialJet (U₀ τ) (coordWord α))`
for every `i, k : ℕ` and `α : Fin k → Fin 3`, `iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) (U₀ τ))`
is uniformly bounded in `L⁴(ℝ³)` across `τ : ℝ` for every `r, k : ℕ`. -/
theorem exists_iteratedFDeriv_iterate_spatialRadialDrift_l4_of_coordJet
    {U₀ : ℝ → SpatialField} (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hJet : ∀ (i k : ℕ) (α : Fin k → Fin 3), ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (U₀ τ) (coordWord α))) 4 volume ≤
        ENNReal.ofReal M) :
    ∀ (r k : ℕ), ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k ((spatialRadialDrift^[r]) (U₀ τ)) y) 4 volume ≤
        ENNReal.ofReal M := by
  intro r k
  choose M_iα hM_iα using fun (i : ℕ) (α : Fin k → Fin 3) => hJet i k α
  let M_α : (Fin k → Fin 3) → ℝ :=
    fun α => ∑ i ∈ Finset.range (r + 1), max (M_iα i α) 0
  have hM_α0 : ∀ α : Fin k → Fin 3, 0 ≤ M_α α :=
    fun α => Finset.sum_nonneg fun i _ => le_max_right (M_iα i α) 0
  refine ⟨(1 + (k : ℝ)) ^ r * ∑ α : Fin k → Fin 3, M_α α, fun τ => ?_⟩
  have hF : ContDiff ℝ ∞ (U₀ τ) := HigherPhaseSub.sliceFamily_contDiff_infty hU₀ τ
  refine eLpNorm_iteratedFDeriv_iterate_spatialRadialDrift_le hF r k hM_α0 fun α i hi => ?_
  have hi_mem : i ∈ Finset.range (r + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hi)
  have hle : max (M_iα i α) 0 ≤ M_α α :=
    Finset.single_le_sum (fun j _ => le_max_right (M_iα j α) 0) hi_mem
  exact (hM_iα i α τ).trans (ENNReal.ofReal_le_ofReal ((le_max_left (M_iα i α) 0).trans hle))

/-! ## 2. Piece decomposition of `(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)` -/

/-- Piece decomposition of `(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)`. -/
theorem iterate_spatialRadialDrift_dirSpatialJet_bgField_eq
    (p : Params) (z : p.Z) (τ : ℝ) (i : ℕ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ l : Fin 2, ContDiff ℝ ∞ (p.inlet l τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) :
    (spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws) =
      (spatialRadialDrift^[i]) (dirSpatialJet (p.raw τ) ws) +
        (fun y => ∑ l : Fin 2,
          p.coord z l • (spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) ws) y) +
        (spatialRadialDrift^[i]) (dirSpatialJet (p.corr z τ) ws) := by
  let sumInJet : SpatialField := fun y => ∑ l : Fin 2, p.coord z l • dirSpatialJet (p.inlet l τ) ws y
  have hRawJet : ContDiff ℝ ∞ (dirSpatialJet (p.raw τ) ws) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hRaw ws
  have hInJet : ∀ l : Fin 2, ContDiff ℝ ∞ (dirSpatialJet (p.inlet l τ) ws) :=
    fun l => JointSmoothSub.contDiff_infty_dirSpatialJet (hInlet l) ws
  have hSumJet : ContDiff ℝ ∞ sumInJet :=
    ContDiff.sum fun l _ => (hInJet l).const_smul (p.coord z l)
  have hRawSumJet : ContDiff ℝ ∞ (dirSpatialJet (p.raw τ) ws + sumInJet) :=
    hRawJet.add hSumJet
  have hCorrJet : ContDiff ℝ ∞ (dirSpatialJet (p.corr z τ) ws) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hCorr ws
  have hJetEq : dirSpatialJet (bgField p z τ) ws =
      (dirSpatialJet (p.raw τ) ws + sumInJet) + dirSpatialJet (p.corr z τ) ws :=
    dirSpatialJet_bgField_eq p z τ hRaw hInlet hCorr ws
  rw [hJetEq,
    iterate_spatialRadialDrift_add i hRawSumJet hCorrJet,
    iterate_spatialRadialDrift_add i hRawJet hSumJet]
  congr 2
  rw [iterate_spatialRadialDrift_sum i Finset.univ
    (F := fun l y => p.coord z l • dirSpatialJet (p.inlet l τ) ws y)
    (fun l _ => (hInJet l).const_smul (p.coord z l))]
  funext y
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrFun (iterate_spatialRadialDrift_smul i (p.coord z l) (hInJet l)) y

/-- Pointwise triangle inequality for `(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)`
across the raw, inlet, and correction pieces. -/
theorem norm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le
    (p : Params) (z : p.Z) (τ : ℝ) (i : ℕ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ l : Fin 2, ContDiff ℝ ∞ (p.inlet l τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) (y : Space) :
    ‖(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws) y‖ ≤
      ‖(spatialRadialDrift^[i]) (dirSpatialJet (p.raw τ) ws) y‖ +
        (∑ l : Fin 2,
          |p.coord z l| * ‖(spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) ws) y‖) +
        ‖(spatialRadialDrift^[i]) (dirSpatialJet (p.corr z τ) ws) y‖ := by
  have hEq := congrFun
    (iterate_spatialRadialDrift_dirSpatialJet_bgField_eq p z τ i hRaw hInlet hCorr ws) y
  rw [hEq, Pi.add_apply, Pi.add_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_sum_le Finset.univ _).trans ?_
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_smul, Real.norm_eq_abs]

/-- `L⁴(ℝ³)` triangle inequality for `(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)`
across the raw, inlet, and correction pieces. -/
theorem eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le
    (p : Params) (z : p.Z) (τ : ℝ) (i : ℕ)
    (hRaw : ContDiff ℝ ∞ (p.raw τ))
    (hInlet : ∀ l : Fin 2, ContDiff ℝ ∞ (p.inlet l τ))
    (hCorr : ContDiff ℝ ∞ (p.corr z τ)) (ws : List Space) :
    eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)) 4 volume ≤
      eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.raw τ) ws)) 4 volume +
        (∑ l : Fin 2, ENNReal.ofReal |p.coord z l| *
          eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) ws)) 4 volume) +
        eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.corr z τ) ws)) 4 volume := by
  let gRaw : Space → ℝ := fun y => ‖(spatialRadialDrift^[i]) (dirSpatialJet (p.raw τ) ws) y‖
  let gIn : Fin 2 → Space → ℝ :=
    fun l y => ‖(spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) ws) y‖
  let gSum : Space → ℝ := ∑ l : Fin 2, |p.coord z l| • gIn l
  let gCorr : Space → ℝ := fun y => ‖(spatialRadialDrift^[i]) (dirSpatialJet (p.corr z τ) ws) y‖
  have hpt : ∀ y : Space,
      ‖(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws) y‖ ≤
        ‖((gRaw + gSum) + gCorr) y‖ := by
    intro y
    have hSumNonneg : 0 ≤ ∑ l : Fin 2, |p.coord z l| * gIn l y :=
      Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hTotNonneg : 0 ≤ (gRaw y + ∑ l : Fin 2, |p.coord z l| * gIn l y) + gCorr y :=
      add_nonneg (add_nonneg (norm_nonneg _) hSumNonneg) (norm_nonneg _)
    have hval : ((gRaw + gSum) + gCorr) y =
        (gRaw y + ∑ l : Fin 2, |p.coord z l| * gIn l y) + gCorr y := by
      simp [gSum, smul_eq_mul]
    rw [hval, Real.norm_of_nonneg hTotNonneg]
    exact norm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le p z τ i hRaw hInlet hCorr ws y
  have hRawMeas : AEStronglyMeasurable gRaw volume :=
    (contDiff_infty_iterate_spatialRadialDrift i
      (JointSmoothSub.contDiff_infty_dirSpatialJet hRaw ws)).continuous.norm.aestronglyMeasurable
  have hInMeas : ∀ l : Fin 2, AEStronglyMeasurable (gIn l) volume :=
    fun l => (contDiff_infty_iterate_spatialRadialDrift i
      (JointSmoothSub.contDiff_infty_dirSpatialJet (hInlet l) ws)).continuous.norm.aestronglyMeasurable
  have hSumMeas : AEStronglyMeasurable gSum volume :=
    Finset.aestronglyMeasurable_sum Finset.univ fun l _ => (hInMeas l).const_smul |p.coord z l|
  have hCorrMeas : AEStronglyMeasurable gCorr volume :=
    (contDiff_infty_iterate_spatialRadialDrift i
      (JointSmoothSub.contDiff_infty_dirSpatialJet hCorr ws)).continuous.norm.aestronglyMeasurable
  have htri1 := eLpNorm_add_le (hRawMeas.add hSumMeas) hCorrMeas (by norm_num) (p := (4 : ℝ≥0∞))
  have htri2 := eLpNorm_add_le hRawMeas hSumMeas (by norm_num) (p := (4 : ℝ≥0∞))
  have htri_sum :
      eLpNorm gSum 4 volume ≤
        ∑ l : Fin 2, ENNReal.ofReal |p.coord z l| *
          eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) ws)) 4 volume := by
    refine (eLpNorm_sum_le (fun l _ => (hInMeas l).const_smul |p.coord z l|) (by norm_num)).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (abs_nonneg _)]
    simp [gIn, eLpNorm_norm]
  calc eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) ws)) 4 volume
      ≤ eLpNorm ((gRaw + gSum) + gCorr) 4 volume := eLpNorm_mono hpt
    _ ≤ (eLpNorm gRaw 4 volume + eLpNorm gSum 4 volume) + eLpNorm gCorr 4 volume :=
        htri1.trans (add_le_add htri2 le_rfl)
    _ ≤ (eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.raw τ) ws)) 4 volume +
          ∑ l : Fin 2, ENNReal.ofReal |p.coord z l| *
            eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) ws)) 4 volume) +
        eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet (p.corr z τ) ws)) 4 volume := by
        simp only [gRaw, gCorr, eLpNorm_norm]
        exact add_le_add (add_le_add le_rfl htri_sum) le_rfl

end BaseIteratedRadialDriftSub

/-! ## 3. Atomic piece leaves and conditional assembly of `BgBaseIteratedRadialDriftSlice` -/

/-- **Order-`0` iterated radial-drift `L⁴(ℝ³)` bound on coordinate spatial jets of `bgField p z`**:
under the hypotheses of `BgBaseIteratedRadialDriftSlice`, for every iteration order `i : ℕ` and
multi-index `α : Fin k → Fin 3`,
`(spatialRadialDrift^[i]) (dirSpatialJet (bgField p z τ) (PhaseDerivStepSub.coordWord α))` is
bounded in `L⁴(ℝ³)` uniformly across `τ : ℝ`. -/
def BgCoordJetIteratedRadialDriftL4 : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ l : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet l x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
        ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ l : Fin 2, Blueprint.IsBoundedBackground (p.inlet l) ∧
        ∀ τ, IsSolenoidal (p.inlet l τ)) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasPhaseJetDeriv (bgField p z) U₁ →
        U₁ = bgPhaseDerivTower p.ν (bgField p z) 1 →
        ∀ (i k : ℕ) (α : Fin k → Fin 3), ∃ M : ℝ, ∀ τ : ℝ,
          eLpNorm ((spatialRadialDrift^[i])
            (dirSpatialJet (bgField p z τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
            ENNReal.ofReal M

/-- **Leaf 1 (`PartII-b:S3/1/2/2/2/2/1`, `RawAndInletCoordJetIteratedRadialDriftL4`)**
(`the November 2 reference manuscript`,
lines 2543-2559 and 2594-2610): for every iteration order `i : ℕ` and multi-index
`α : Fin k → Fin 3`, `(spatialRadialDrift^[i]) (dirSpatialJet (p.raw τ) (coordWord α))` and
`(spatialRadialDrift^[i]) (dirSpatialJet (p.inlet l τ) (coordWord α))` are uniformly bounded in
`L⁴(ℝ³)` across `τ : ℝ`.
Composed by task `PartII-b:S3/1/2/2/2/2` via `bgBaseIteratedRadialDriftSlice_of_pieces`. -/
def RawAndInletCoordJetIteratedRadialDriftL4 : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ l : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet l x.1 x.2)) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ l : Fin 2, Blueprint.IsBoundedBackground (p.inlet l) ∧
        ∀ τ, IsSolenoidal (p.inlet l τ)) →
      ∀ (i k : ℕ) (α : Fin k → Fin 3), ∃ M_V : ℝ, 0 ≤ M_V ∧ ∀ τ : ℝ,
        eLpNorm ((spatialRadialDrift^[i])
          (dirSpatialJet (p.raw τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
          ENNReal.ofReal M_V ∧
        ∀ l : Fin 2,
          eLpNorm ((spatialRadialDrift^[i])
            (dirSpatialJet (p.inlet l τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
            ENNReal.ofReal M_V

/-- **Leaf 2 (`PartII-b:S3/1/2/2/2/2/2`, `CorrCoordJetIteratedRadialDriftL4`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2552-2562): under the hypotheses of `BgBaseIteratedRadialDriftSlice`, for a
solution `z` of `ProjectedEquation p z` with all iterated spatial derivatives `g α` in the maximal
graph `B0411.D p.period p.ν q0E`, for every iteration order `i : ℕ` and multi-index
`α : Fin k → Fin 3`, `(spatialRadialDrift^[i]) (dirSpatialJet (p.corr z τ) (coordWord α))` is
uniformly bounded in `L⁴(ℝ³)` across `τ : ℝ`.
Composed by task `PartII-b:S3/1/2/2/2/2` via `bgBaseIteratedRadialDriftSlice_of_pieces`. -/
def CorrCoordJetIteratedRadialDriftL4 : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ l : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet l x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
        ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ l : Fin 2, Blueprint.IsBoundedBackground (p.inlet l) ∧
        ∀ τ, IsSolenoidal (p.inlet l τ)) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasPhaseJetDeriv (bgField p z) U₁ →
        U₁ = bgPhaseDerivTower p.ν (bgField p z) 1 →
        ∀ (i k : ℕ) (α : Fin k → Fin 3), ∃ M_w : ℝ, 0 ≤ M_w ∧ ∀ τ : ℝ,
          eLpNorm ((spatialRadialDrift^[i])
            (dirSpatialJet (p.corr z τ) (PhaseDerivStepSub.coordWord α))) 4 volume ≤
            ENNReal.ofReal M_w

/-- Assembly of `BgCoordJetIteratedRadialDriftL4` from `RawAndInletCoordJetIteratedRadialDriftL4`
and `CorrCoordJetIteratedRadialDriftL4` via
`BaseIteratedRadialDriftSub.eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le`. -/
theorem bgCoordJetIteratedRadialDriftL4_of_pieces
    (hV : RawAndInletCoordJetIteratedRadialDriftL4)
    (hW : CorrCoordJetIteratedRadialDriftL4) :
    BgCoordJetIteratedRadialDriftL4 := by
  intro hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hV'⟩ := hV Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₂, hν₂, hW'⟩ := hW hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet
    hBg U₁ hU₁Smooth hU₁Deriv hU₁Eq i k α
  obtain ⟨M_V, hMV0, hMV⟩ :=
    hV' p d hReg (hν.trans (min_le_left _ _)) hAge hMode hRawCD hInCD hRaw hInlet i k α
  obtain ⟨M_w, hMw0, hMw⟩ :=
    hW' p d hReg (hν.trans (min_le_right _ _)) hAge hMode hRawCD hInCD z hProj hz hGraph hSlice
      hRaw hInlet hBg U₁ hU₁Smooth hU₁Deriv hU₁Eq i k α
  refine ⟨M_V + (∑ l : Fin 2, |p.coord z l| * M_V) + M_w, ?_⟩
  intro τ
  have hRawSlice : ContDiff ℝ ∞ (p.raw τ) :=
    PhaseDerivStepSub.contDiff_slice_of_joint (F := p.raw) hRawCD τ
  have hInSlice : ∀ l : Fin 2, ContDiff ℝ ∞ (p.inlet l τ) :=
    fun l => PhaseDerivStepSub.contDiff_slice_of_joint (F := p.inlet l) (hInCD l) τ
  have hBgSlice : ContDiff ℝ ∞ (bgField p z τ) :=
    HigherPhaseSub.sliceFamily_contDiff_infty hBg τ
  have hCorrSlice : ContDiff ℝ ∞ (p.corr z τ) :=
    RadialDriftL4Sub.contDiff_infty_corr_of_bgField p z τ hRawSlice hInSlice hBgSlice
  have htri :=
    BaseIteratedRadialDriftSub.eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_bgField_le
      p z τ i hRawSlice hInSlice hCorrSlice (PhaseDerivStepSub.coordWord α)
  have hsum :
      (∑ l : Fin 2, ENNReal.ofReal |p.coord z l| *
        eLpNorm ((spatialRadialDrift^[i])
          (dirSpatialJet (p.inlet l τ) (PhaseDerivStepSub.coordWord α))) 4 volume) ≤
        ENNReal.ofReal (∑ l : Fin 2, |p.coord z l| * M_V) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (abs_nonneg _) hMV0)]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((hMV τ).2 l) zero_le
  have htot := add_le_add (add_le_add (hMV τ).1 hsum) (hMw τ)
  have hsum0 : 0 ≤ ∑ l : Fin 2, |p.coord z l| * M_V :=
    Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) hMV0
  rw [← ENNReal.ofReal_add hMV0 hsum0, ← ENNReal.ofReal_add (add_nonneg hMV0 hsum0) hMw0] at htot
  exact htri.trans htot

/-- Reduction of `BgBaseIteratedRadialDriftSlice` (`PartII-b:S3/1/2/2/2/2`) to
`BgCoordJetIteratedRadialDriftL4` via
`RadialDriftTowerSub.isIteratedRadialDriftSliceFamily_of_succ_succ_l4` and
`BaseIteratedRadialDriftSub.exists_iteratedFDeriv_iterate_spatialRadialDrift_l4_of_coordJet`. -/
theorem bgBaseIteratedRadialDriftSlice_of
    (hJet : BgCoordJetIteratedRadialDriftL4) :
    BgBaseIteratedRadialDriftSlice := by
  intro hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, hJ⟩ := hJet hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet
    hBg U₁ hU₁Smooth hU₁Deriv hU₁Eq
  have hAllL4 :=
    BaseIteratedRadialDriftSub.exists_iteratedFDeriv_iterate_spatialRadialDrift_l4_of_coordJet hBg
      (hJ p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet
        hBg U₁ hU₁Smooth hU₁Deriv hU₁Eq)
  exact RadialDriftTowerSub.isIteratedRadialDriftSliceFamily_of_succ_succ_l4
    hLeray p.ν hBg hU₁Smooth hU₁Eq (fun r k => hAllL4 (r + 2) k)

/-- Conditional assembly of `BgBaseIteratedRadialDriftSlice` (`PartII-b:S3/1/2/2/2/2`) from
`RawAndInletCoordJetIteratedRadialDriftL4` (`PartII-b:S3/1/2/2/2/2/1`) and
`CorrCoordJetIteratedRadialDriftL4` (`PartII-b:S3/1/2/2/2/2/2`). -/
theorem bgBaseIteratedRadialDriftSlice_of_pieces
    (hV : RawAndInletCoordJetIteratedRadialDriftL4)
    (hW : CorrCoordJetIteratedRadialDriftL4) :
    BgBaseIteratedRadialDriftSlice :=
  bgBaseIteratedRadialDriftSlice_of (bgCoordJetIteratedRadialDriftL4_of_pieces hV hW)

end UnforcedLeray.Short.IIb

end
