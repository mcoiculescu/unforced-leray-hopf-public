import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# Decomposition of `youngEndResponse_of` (item `PartIII-b:C/near/delta/10`)

Source of record `the November 2 reference manuscript`,
4011-4015.  The output region `s < s₋` of `g⁻¹(S_N - S₀)g` splits as the `S_N` part and the `S₀`
part.  The `S₀` part is bounded by the flat free gain bound (`FlatFreeGainBound`, 3420-3440, item
`PartIII-b:C/near/delta/7`) since the output restriction `1_A` commutes with `g⁻¹` and has norm
`≤ 1`; no support information on `S₀` is needed.  The `S_N` part is `YoungMaskedPiece`, the
`MaskedLowerPiece` of `Masked/Lemmas.lean` with a free output cut `s₋ = ε^a` (`a > 0` independent
of the mask level `S = ε^{-b}`).

Also the shared helper lemmas for the two ends (`gainRestrS` is dominated by `gainConjS`, and the
combination of the `S_N` bound with the `S₀` bound).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-! ## Helpers: `1_A` has norm `≤ 1` and commutes with the gain -/

theorem restrLp_norm_le_one {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : Set Chart} (hA : MeasurableSet A) :
    ‖restrLp μ E A‖ ≤ 1 := by
  rw [restrLp_of_meas hA]
  unfold mulBdd
  exact (LinearMap.mkContinuous_norm_le _ (by norm_num) _).trans (by simp)

theorem outRestr_norm_le_one (c : ℝ) {A : Set Chart} (hA : MeasurableSet A) :
    ‖outRestr c A‖ ≤ 1 :=
  restrLp_norm_le_one hA

theorem gainH_ae (c γ : ℝ) {ν : ℝ} (hν : 0 < ν) (u : Hsp c) :
    (gainH c γ hν u : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      gainFun γ ν • (u : Chart → EuclideanSpace ℝ (Fin 2)) := by
  unfold gainH gainLp
  exact mulBdd_apply_ae (gainFun γ ν) (gainFun_measurable γ ν) (Real.exp (|γ| / ν))
    (gainFun_le hν) u

theorem outRestr_ae (c : ℝ) {A : Set Chart} (hA : MeasurableSet A) (u : Hsp c) :
    (outRestr c A u : Chart → EuclideanSpace ℝ (Fin 2)) =ᵐ[ageμ c (-3 / 2)]
      ind A • (u : Chart → EuclideanSpace ℝ (Fin 2)) :=
  restrLp_ae hA u

theorem gainH_outRestr (c γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A : Set Chart} (hA : MeasurableSet A)
    (u : Hsp c) : gainH c γ hν (outRestr c A u) = outRestr c A (gainH c γ hν u) := by
  apply Lp.ext
  filter_upwards [gainH_ae c γ hν (outRestr c A u), outRestr_ae c hA u, gainH_ae c γ hν u,
    outRestr_ae c hA (gainH c γ hν u)] with x h1 h2 h3 h4
  rw [h1, h4]
  change gainFun γ ν x • ((outRestr c A u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) x =
    ind A x • ((gainH c γ hν u : Hsp c) : Chart → EuclideanSpace ℝ (Fin 2)) x
  rw [h2, h3]
  change gainFun γ ν x • (ind A x • (u : Chart → EuclideanSpace ℝ (Fin 2)) x) =
    ind A x • (gainFun γ ν x • (u : Chart → EuclideanSpace ℝ (Fin 2)) x)
  rw [smul_comm]

theorem gainH_symm_outRestr (c γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A : Set Chart}
    (hA : MeasurableSet A) (u : Hsp c) :
    (gainH c γ hν).symm (outRestr c A u) = outRestr c A ((gainH c γ hν).symm u) := by
  apply (gainH c γ hν).injective
  rw [(gainH c γ hν).apply_symm_apply, gainH_outRestr c γ hν hA, (gainH c γ hν).apply_symm_apply]

/-- `‖g⁻¹ 1_A X G‖ ≤ ‖g⁻¹ X G‖`. -/
theorem gainRestrS_norm_le (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A : Set Chart}
    (hA : MeasurableSet A) (X : Zsp c mZ ρb →L[ℝ] Hsp c) :
    ‖gainRestrS γ hν A X‖ ≤ ‖gainConjS γ hν X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun F => ?_
  have h1 : gainRestrS γ hν A X F = outRestr c A (gainConjS γ hν X F) := by
    simp only [gainRestrS, gainConjS_apply, ContinuousLinearMap.comp_apply]
    exact gainH_symm_outRestr c γ hν hA _
  rw [h1]
  calc ‖outRestr c A (gainConjS γ hν X F)‖ ≤ ‖outRestr c A‖ * ‖gainConjS γ hν X F‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖gainConjS γ hν X F‖ := by
        gcongr
        exact outRestr_norm_le_one c hA
    _ ≤ ‖gainConjS γ hν X‖ * ‖F‖ := by
        rw [one_mul]; exact ContinuousLinearMap.le_opNorm _ _

theorem gainRestrS_sub (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (A : Set Chart)
    (X Y : Zsp c mZ ρb →L[ℝ] Hsp c) :
    gainRestrS γ hν A (X - Y) = gainRestrS γ hν A X - gainRestrS γ hν A Y := by
  ext1 F
  simp [gainRestrS, gainConjS_apply]

/-- Combination: the `S_N` bound and the `S₀` bound give the bound for `S_N - S₀` on the region
`A` (for `ν ≤ 1`). -/
theorem gainRestrS_combine (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {A : Set Chart}
    (hA : MeasurableSet A) (SN S0 : Zsp c mZ ρb →L[ℝ] Hsp c) {C1 C2 : ℝ} {k1 k2 : ℕ}
    (h1 : ‖gainRestrS γ hν A SN‖ ≤ C1 * ν⁻¹ ^ k1)
    (h2 : ‖gainConjS γ hν S0‖ ≤ C2 * ν⁻¹ ^ k2) :
    ‖gainRestrS γ hν A (SN - S0)‖ ≤ (|C1| + |C2|) * ν⁻¹ ^ (k1 + k2) := by
  have hv : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hp1 : ν⁻¹ ^ k1 ≤ ν⁻¹ ^ (k1 + k2) := pow_le_pow_right₀ hv (Nat.le_add_right _ _)
  have hp2 : ν⁻¹ ^ k2 ≤ ν⁻¹ ^ (k1 + k2) := pow_le_pow_right₀ hv (Nat.le_add_left _ _)
  have hp0 : 0 ≤ ν⁻¹ ^ k1 := by positivity
  have hq0 : 0 ≤ ν⁻¹ ^ k2 := by positivity
  rw [gainRestrS_sub]
  calc ‖gainRestrS γ hν A SN - gainRestrS γ hν A S0‖
      ≤ ‖gainRestrS γ hν A SN‖ + ‖gainRestrS γ hν A S0‖ := norm_sub_le _ _
    _ ≤ C1 * ν⁻¹ ^ k1 + C2 * ν⁻¹ ^ k2 :=
        add_le_add h1 ((gainRestrS_norm_le c mZ ρb γ hν hA S0).trans h2)
    _ ≤ |C1| * ν⁻¹ ^ (k1 + k2) + |C2| * ν⁻¹ ^ (k1 + k2) := by
        gcongr
        · exact (le_abs_self _)
        · exact le_abs_self _
    _ = _ := by ring

/-! ## The young end -/

/-- **The young `S_N` piece** (source 4011-4015, 4027-4028): for `a, b, δ`, the output region
`s < s₋ = ε^a` of `g⁻¹S_N g` has norm `≤ C ν^{-k}`.  Route (source): retained inputs have
`t < e^δ s₋` (`Masked.MaskedSupport`), where `g ≤ e^{γe^δ s₋}` and `g⁻¹ ≤ 1` (gain ratio
`1 + o(1)`, `Masked.GainBlockBound`); `1_{s<s₋}S_N1_{t<e^δ s₋} = 1_{s<s₋}S_ε1_{t<e^δ s₋} -
1_{s<s₋}S_far1_{t<e^δ s₋}`, the first bounded by the free energy (`Masked.RealStressBound`), the
second by `Masked.ForbiddenBlockBound` (`s₋ = ε^a ≤ 1 ≤ ε^{-b} = S`).  This is
`Masked.MaskedLowerPiece` with the cut `ε^a` in place of `ε^b`. -/
def YoungMaskedPiece : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ a b δ : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN →
          ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBelow (p.ε ^ a)) SN‖ ≤ C * p.ν⁻¹ ^ k

/-- The young end from the young `S_N` piece and the flat free gain bound (`S₀` part). -/
theorem youngEndResponse_of_pieces (hF : FlatFreeGainBound) (hL : YoungMaskedPiece) :
    YoungEndResponse := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm a b δ ha hb hb1 hδ
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hL P hP Kset hK hKs mZ hmZ dm dp hdm a b δ ha hb hb1 hδ
  obtain ⟨C2, k2, ν2, hν2, h2⟩ := hF P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨|C1| + |C2|, k1 + k2, min (min ν1 ν2) 1, lt_min (lt_min hν1 hν2) one_pos, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ SN S0 hSN hS0
  have hν1' : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2' : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  exact gainRestrS_combine p.c mZ ρb P.eigenvalue.re p.ν_pos hν3 (measurableSet_ageBelow _) SN S0
    (h1 p d hreg hν1' ρb hρ hρ1 μ hμ SN hSN) (h2 p d hreg hν2' ρb hρ hρ1 μ hμ S0 hS0)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
