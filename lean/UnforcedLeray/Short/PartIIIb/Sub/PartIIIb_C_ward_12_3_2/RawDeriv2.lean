import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1.FarDecay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1.NearBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.Reduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY.IBP
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SliceFieldElem
import UnforcedLeray.Loc.L01Coefficient.Basic

/-!
# `RawResidualDeriv2Y` from the order-2 slice derivative bound and slice IBP

Task `PartIII-b:C/ward/12/3/2/2/1`.  Source of record
`the November 2 reference manuscript`,
lines 2542-2551 at `k = 2` and 1204-1225, 1305-1325.

Order-2 analogue of `derivY_of` (`DerivY/Reduction.lean:62`): given `RingResidualDeriv2Bound`
(first weak derivative `G = ∂_l F_R` and second weak derivative `H = ∂_j∂_l F_R` slice-wise in
`L^{q₀}`, `L^{q₀}`-continuous, and `p.period`-periodic), two applications of
`sliceIntegrationByParts_thm` (first in `y_l` at `∂_jΦ`, then in `y_j` at `Φ`) cancel the two
minus signs to give `⟪∂_l∂_jΦ, F_R⟫ = ⟪Φ, H⟫`, and `sliceFieldElem_proof` represents `H` in
`Y_{q₀}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF)
open UnforcedLeray.Short.IIb (trainStream trainPressure sliceFieldElem_proof)
open UnforcedLeray.Short.PartIIa (ringResidual)

/-- **Second spatial derivatives of the ring residual** (source 2542-2551 at `k = 2`, 1204-1225,
1305-1325; order-2 analogue of `RingResidualDerivBound`, `DerivY/Reduction.lean:31`).  For the BUC
train, `c = ν⁻²`, `R ≥ 2`, `ν` small, period `≤ 1`, and all `j, l`, the ring residual `F_R(τ)` and
its weak spatial derivatives `G(τ) = ∂_l F_R(τ)` and `H(τ) = ∂_j G(τ) = ∂_j∂_l F_R(τ)` are
`p.period`-periodic, slice-wise in `L^{q₀}`, and `L^{q₀}`-continuous in `τ`. -/
def RingResidualDeriv2Bound : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j l : Fin 3,
      ∃ G H : ℝ → SpatialField,
        (∀ τ, ringResidual p.R p.ν (trainStream p) (trainPressure p) (τ + p.period) =
          ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) ∧
        (∀ τ, G (τ + p.period) = G τ) ∧
        (∀ τ, H (τ + p.period) = H τ) ∧
        (∀ τ, MemLp (ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) q0E volume) ∧
        (∀ τ, MemLp (G τ) q0E volume) ∧
        (∀ τ, MemLp (H τ) q0E volume) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (ringResidual p.R p.ν (trainStream p)
            (trainPressure p) τ - ringResidual p.R p.ν (trainStream p) (trainPressure p) τ₀)
            q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (G τ - G τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (H τ - H τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ, HasWeakSpatialDerivative l
          (ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) (G τ)) ∧
        (∀ τ, HasWeakSpatialDerivative j (G τ) (H τ))

namespace RawDeriv2Sub

theorem realC_neg (v : Space) : realC (-v) = -realC v := by
  ext i
  simp [realC_apply]

theorem pairF_realC_neg (P : ℝ) (Ψ : ℝ × UnforcedLeray.Space → CVec3) (F : ℝ → SpatialField) :
    pairF P Ψ (fun x => realC (-(F x.1 x.2))) = -pairF P Ψ (fun x => realC (F x.1 x.2)) := by
  simp only [pairF, UnforcedLeray.Cons.C03.Concrete.phaseInt, realC_neg, map_neg, integral_neg,
    smul_neg]

end RawDeriv2Sub

/-- `RawResidualDeriv2Y` from `RingResidualDeriv2Bound` (order-2 analogue of `derivY_of`). -/
theorem rawResidualDeriv2Y_of (h : RingResidualDeriv2Bound) : RawResidualDeriv2Y := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP j l => ?_⟩
  obtain ⟨G, K, hFper, hGper, hKper, hFmem, hGmem, hKmem, hFc, hGc, hKc, hw1, hw2⟩ :=
    H p htr hν hc hR hP j l
  obtain ⟨f, hf, -, -, -⟩ := sliceFieldElem_proof p K hKper hKmem hKc
  refine ⟨f, fun Φ hΦ => ?_⟩
  have hΦt : IsPhaseTest p.period Φ := hΦ.1
  have hdyΦ : IsPhaseTest p.period (dy j Φ) := hΦt.dy j
  have ibp1 := sliceIntegrationByParts_thm p.period p.period_pos l
    (ringResidual p.R p.ν (trainStream p) (trainPressure p)) G
    hFper hGper hFmem hGmem hFc hGc hw1 (dy j Φ) hdyΦ
  have ibp2 := sliceIntegrationByParts_thm p.period p.period_pos j G K
    hGper hKper hGmem hKmem hGc hKc hw2 Φ hΦt
  rw [hf Φ hΦt]
  show pairF p.period (dy l (dy j Φ))
      (fun x => realC (ringResidual p.R p.ν (trainStream p) (trainPressure p) x.1 x.2)) =
    pairF p.period Φ (fun x => realC (K x.1 x.2))
  rw [ibp1, RawDeriv2Sub.pairF_realC_neg, ibp2, RawDeriv2Sub.pairF_realC_neg, neg_neg]

/-- **Unperiodized `C_per W^{2,q₀}` bound on the ring residual** (source 2542-2551 at `k = 2`,
1204-1225, 1305-1325): requires only periodicity of `F_R` itself and slice-wise `MemLp` /
`L^{q₀}`-continuity of `F_R`, its first weak derivative `G`, and its second weak derivative `H`
(no periodicity hypothesis on `G` or `H`, which is deduced automatically by `weakDerivative_ae_eq`
and floor periodization in `ringResidualDeriv2Bound_of_w2`). -/
def RingResidualW2Bound : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j l : Fin 3,
      ∃ G H : ℝ → SpatialField,
        (∀ τ, ringResidual p.R p.ν (trainStream p) (trainPressure p) (τ + p.period) =
          ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) ∧
        (∀ τ, MemLp (ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) q0E volume) ∧
        (∀ τ, MemLp (G τ) q0E volume) ∧
        (∀ τ, MemLp (H τ) q0E volume) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (ringResidual p.R p.ν (trainStream p)
            (trainPressure p) τ - ringResidual p.R p.ν (trainStream p) (trainPressure p) τ₀)
            q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (G τ - G τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ₀, Tendsto (fun τ => (eLpNorm (H τ - H τ₀) q0E volume).toReal) (𝓝 τ₀) (𝓝 0)) ∧
        (∀ τ, HasWeakSpatialDerivative l
          (ringResidual p.R p.ν (trainStream p) (trainPressure p) τ) (G τ)) ∧
        (∀ τ, HasWeakSpatialDerivative j (G τ) (H τ))

/-- Deduces strict `p.period`-periodicity of both weak derivatives `G = ∂_l F_R` and
`H = ∂_j ∂_l F_R` from periodicity of `F_R` via `weakDerivative_ae_eq` and fundamental-domain
floor periodization `τ ↦ τ - P ⌊τ / P⌋`. -/
theorem ringResidualDeriv2Bound_of_w2 (h : RingResidualW2Bound) : RingResidualDeriv2Bound := by
  obtain ⟨ν₀, hν₀, H0⟩ := h
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP j l => ?_⟩
  obtain ⟨G, H, hFper, hFmem, hGmem, hHmem, hFc, hGc, hHc, hw1, hw2⟩ :=
    H0 p htr hν hc hR hP j l
  have hP0 : 0 < p.period := p.period_pos
  have hq1 : (1 : ℝ≥0∞) ≤ q0E := Fact.out
  have hGloc : ∀ τ, LocallyIntegrable (G τ) volume := fun τ => (hGmem τ).locallyIntegrable hq1
  have hHloc : ∀ τ, LocallyIntegrable (H τ) volume := fun τ => (hHmem τ).locallyIntegrable hq1
  have haeG1 : ∀ τ, G (τ + p.period) =ᵐ[volume] G τ := fun τ => by
    refine UnforcedLeray.Blueprint.L01.weakDerivative_ae_eq (i := l) ?_ (hw1 τ) (hGloc _) (hGloc _)
    have hw := hw1 (τ + p.period)
    rwa [hFper τ] at hw
  have haeH1 : ∀ τ, H (τ + p.period) =ᵐ[volume] H τ := fun τ => by
    refine UnforcedLeray.Blueprint.L01.weakDerivative_ae_eq (i := j) ?_ (hw2 τ) (hHloc _) (hHloc _)
    exact (hw2 (τ + p.period)).congr (haeG1 τ) (Filter.EventuallyEq.refl _ _)
  have haeZ : ∀ (K : ℝ → SpatialField), (∀ τ, K (τ + p.period) =ᵐ[volume] K τ) →
      ∀ (n : ℤ) (τ : ℝ), K (τ + n * p.period) =ᵐ[volume] K τ := by
    intro K hK1 n
    induction n using Int.induction_on with
    | zero => intro τ; simp
    | succ n ih =>
      intro τ
      have e : τ + ((n : ℤ) + 1 : ℤ) * p.period = (τ + n * p.period) + p.period := by
        push_cast; ring
      rw [e]
      exact (hK1 _).trans (ih τ)
    | pred n ih =>
      intro τ
      have e : τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * p.period + p.period =
          τ + ((-(n : ℤ) : ℤ) : ℝ) * p.period := by
        push_cast; ring
      have h1 := hK1 (τ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * p.period)
      rw [e] at h1
      exact h1.symm.trans (ih τ)
  set P := p.period
  let Gf : ℝ → SpatialField := fun τ => G (τ - P * (⌊τ / P⌋ : ℤ))
  let Hf : ℝ → SpatialField := fun τ => H (τ - P * (⌊τ / P⌋ : ℤ))
  have haeG : ∀ τ, Gf τ =ᵐ[volume] G τ := fun τ => by
    have e : τ - P * (⌊τ / P⌋ : ℤ) = τ + ((-⌊τ / P⌋ : ℤ) : ℝ) * P := by push_cast; ring
    show G (τ - P * (⌊τ / P⌋ : ℤ)) =ᵐ[volume] G τ
    rw [e]; exact haeZ G haeG1 _ τ
  have haeH : ∀ τ, Hf τ =ᵐ[volume] H τ := fun τ => by
    have e : τ - P * (⌊τ / P⌋ : ℤ) = τ + ((-⌊τ / P⌋ : ℤ) : ℝ) * P := by push_cast; ring
    show H (τ - P * (⌊τ / P⌋ : ℤ)) =ᵐ[volume] H τ
    rw [e]; exact haeZ H haeH1 _ τ
  have hshift : ∀ τ : ℝ, τ + P - P * (⌊(τ + P) / P⌋ : ℤ) = τ - P * (⌊τ / P⌋ : ℤ) := by
    intro τ
    have hfl : ⌊(τ + P) / P⌋ = ⌊τ / P⌋ + 1 := by
      rw [show (τ + P) / P = τ / P + 1 by field_simp, Int.floor_add_one]
    rw [hfl]
    push_cast; ring
  refine ⟨Gf, Hf, hFper,
    fun τ => by show G (τ + P - P * (⌊(τ + P) / P⌋ : ℤ)) = Gf τ; rw [hshift],
    fun τ => by show H (τ + P - P * (⌊(τ + P) / P⌋ : ℤ)) = Hf τ; rw [hshift],
    hFmem,
    fun τ => (hGmem τ).ae_eq (haeG τ).symm,
    fun τ => (hHmem τ).ae_eq (haeH τ).symm,
    hFc,
    fun τ₀ => (hGc τ₀).congr (fun τ => by rw [eLpNorm_congr_ae ((haeG τ).sub (haeG τ₀))]),
    fun τ₀ => (hHc τ₀).congr (fun τ => by rw [eLpNorm_congr_ae ((haeH τ).sub (haeH τ₀))]),
    fun τ => (hw1 τ).congr (Filter.EventuallyEq.refl _ _) (haeG τ).symm,
    fun τ => (hw2 τ).congr (haeG τ).symm (haeH τ).symm⟩

/-- `RawResidualDeriv2Y` from the unperiodized `C_per W^{2,q₀}` bound `RingResidualW2Bound`. -/
theorem rawResidualDeriv2Y_of_w2 (h : RingResidualW2Bound) : RawResidualDeriv2Y :=
  rawResidualDeriv2Y_of (ringResidualDeriv2Bound_of_w2 h)

/-- `RawResidualDeriv2Y` (task `PartIII-b:C/ward/12/3/2/2/1`). -/
theorem rawResidualDeriv2Y : RawResidualDeriv2Y :=
  rawResidualDeriv2Y_of_env (UnforcedLeray.Short.IIb.ringLiftSmoothExt_of
    UnforcedLeray.Short.PartIIa.ringAxisSmooth) rawResidualD2FarDecay rawResidualD2NearBound

end UnforcedLeray.Short.PartIIIb.Concrete
