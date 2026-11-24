import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6

/-!
# `PartIII-b:C/rep/8/2/6/1` (decomposition): term 1 `2U·∇Y` of the ring substitution

Source `the November 2 reference manuscript` 5470-5472 (error of `2U·∇Y`),
5438-5448 (mean jets), 5449-5453 (clock), 5460-5465 (ring-chart rules).

`RingTerm1` follows from two lemmas:

* `BjetYoung` (`|B_j(s)| ≤ P_ν ε³ s^{3/2} N` on the young range; from `ActualJet`, `JetClock`:
  `B_j = B_T - clock`, `B_T = A_T' + μA_T/s`, `A_y = A_T` for `s ≤ 1/ν`);
* `Term1Pointwise` (the pointwise bookkeeping at one regime: `U = √s(emb v + O(ε𝔴₃))`,
  `∂_jY = sB_{·j} + O(ε⁴s^{5/2}|η|N)`, `fderiv Y U = Σ_j U_j ∂_jY`, `|v| ≤ 𝔴₃`,
  `𝔴₃(1+|η|) ≤ 𝔴₄`, `ν, ε ≤ 1`).

The two proved helpers `fderiv_eq_sum_physPd` and `coefOf_enorm_le` are used by `Term1Pointwise`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Coordinate expansion of the derivative: `Df(y)u = Σ_j u_j ∂_jf(y)`. -/
theorem fderiv_eq_sum_physPd (f : Space → Space) (y u : Space) :
    fderiv ℝ f y u = ∑ j : Fin 3, u j • physPd f j y := by
  have hu : u = ∑ j : Fin 3, u j • coordinateVector j := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

/-- Componentwise bound of the chart coefficient: if the two meridional components of `F` at the
chart point are at most `√s·b`, then `‖coefOf R F p‖ₑ ≤ 2b`. -/
private theorem coefOf_enorm_le (R : ℝ) (F : ℝ → Space → Space) (p : Chart) (hp : 0 < p.1) (b : ℝ≥0∞)
    (h0 : ‖F (NearInst.chartTau R p) (NearInst.chartY R p) 0‖ₑ ≤ ENNReal.ofReal (Real.sqrt p.1) * b)
    (h2 : ‖F (NearInst.chartTau R p) (NearInst.chartY R p) 2‖ₑ ≤ ENNReal.ofReal (Real.sqrt p.1) * b) :
    ‖coefOf R F p‖ₑ ≤ 2 * b := by
  set a0 := F (NearInst.chartTau R p) (NearInst.chartY R p) 0 with ha0
  set a2 := F (NearInst.chartTau R p) (NearInst.chartY R p) 2 with ha2
  have hs : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hn : ‖(!₂[a0, a2] : Merid)‖ ≤ |a0| + |a2| := by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    simp [Fin.sum_univ_two]
    nlinarith [abs_nonneg a0, abs_nonneg a2, sq_abs a0, sq_abs a2]
  have hE : ‖(!₂[a0, a2] : Merid)‖ₑ ≤ ‖a0‖ₑ + ‖a2‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hn.trans ?_)
    simp
  unfold coefOf
  rw [enorm_smul]
  have hinv : ‖(Real.sqrt p.1)⁻¹‖ₑ = (ENNReal.ofReal (Real.sqrt p.1))⁻¹ := by
    rw [← ofReal_norm, norm_inv, Real.norm_of_nonneg hs.le,
      ENNReal.ofReal_inv_of_pos hs]
  rw [hinv]
  have hne : ENNReal.ofReal (Real.sqrt p.1) ≠ 0 := by simpa using hs
  have hft : ENNReal.ofReal (Real.sqrt p.1) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc (ENNReal.ofReal (Real.sqrt p.1))⁻¹ * ‖(!₂[a0, a2] : Merid)‖ₑ
      ≤ (ENNReal.ofReal (Real.sqrt p.1))⁻¹ *
          (ENNReal.ofReal (Real.sqrt p.1) * b + ENNReal.ofReal (Real.sqrt p.1) * b) :=
        mul_le_mul' le_rfl (hE.trans (add_le_add h0 h2))
    _ = 2 * b := by
        have e : ENNReal.ofReal (Real.sqrt p.1) * b + ENNReal.ofReal (Real.sqrt p.1) * b =
            ENNReal.ofReal (Real.sqrt p.1) * (2 * b) := by ring
        rw [e, ← mul_assoc, ENNReal.inv_mul_cancel hne hft, one_mul]


/-- **Lemma 1 at one regime** (source 5446, 5449-5453, 5400-5413): on the young range
`|B_j(s)| ≤ P_ν ε³ s^{3/2} N`.  (`B_j = B_T - (ν/s)D_yΔ_yX^mt` by `JetClockAt`, `B_T = A_T' + μA_T/s`
with `A_y = A_T` for `s ≤ 1/ν`, and `|(s∂_s)^jA_T| ≤ Cε³s^{5/2}N`, `ActualJetAt`.) -/
def BjetYoungBoundAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (C : ℝ)
    (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ s : ℝ, 0 < s → s ≤ 1 / L.ν →
    ENNReal.ofReal (frob (Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 3 * s ^ (3 / 2 : ℝ)) * oldN1 Pl K L T

namespace SeqData

/-- Lemma 1 along the sequence. -/
def BjetYoung (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    BjetYoungBoundAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-- **Lemma 2** (source 5470-5472, 5460-5465, 5438-5448): the pointwise bookkeeping of term 1 at
one regime with `ν, ε ≤ 1`: the constants `(C, k)` of `RingTerm1At` depend only on the constants
of the four hypotheses. -/
def Term1Pointwise : Prop :=
  ∀ (CR CM CW CB : ℝ) (kR kM kW kB : ℕ), ∃ (C : ℝ) (k : ℕ),
    ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ),
      L.ν ≤ 1 → L.ε ≤ 1 → RingChartRulesAt Pl L CR kR → MeanJetAt Pl K L μ CM kM →
      TrainMomentAt L CW kW → BjetYoungBoundAt Pl K L μ CB kB → RingTerm1At Pl K L μ C k

/-- `RingTerm1` from the two lemmas. -/
theorem ringTerm1_of_lemmas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hB : D.BjetYoung) (hP : Term1Pointwise) (h1 : D.RingChartRules) (h2 : D.MeanJet)
    (h3 : D.TrainMoment) : D.RingTerm1 := by
  obtain ⟨CR, kR, eR⟩ := h1
  obtain ⟨CM, kM, eM⟩ := h2
  obtain ⟨CW, kW, eW⟩ := h3
  obtain ⟨CB, kB, eB⟩ := hB
  obtain ⟨C, k, hC⟩ := hP CR CM CW CB kR kM kW kB
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨C, k, ?_⟩
  filter_upwards [eR, eM, eW, eB, hle] with n a b c d hl z hz
  exact hC _ _ _ _ hl.1 hl.2 a (b z hz) c (d z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
