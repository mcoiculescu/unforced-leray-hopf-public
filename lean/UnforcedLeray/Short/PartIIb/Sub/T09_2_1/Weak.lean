import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_3

/-!
# Part II-b, `T09/2` redesign: the divergence route through the weak graph closeness

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`div(√s b) = s[(∂_q - εK) b_r + ∂_η b_z]`, `Q_ε = ∂_q - ε(K+1)`), 1898-1918 (`H_r`,
`bg:profile-graph`, `∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`) and 1941/1957 (`r = 23/8`).

## Why the old route fails (organizer `oa1`, task `PartII-b:T09/2/1/1/org`)

`DivApprox` (`T09/2`, density of nice profiles in the graph norm
`‖b‖ + ‖√s Q_ε b‖ + ‖√s ∂_η b‖`) and hence `DivSCutApprox` (`T09/2/1`) are false for every
`r > 2`.  For `b = θ(s) s^{-1/2} h(η/√s) e_r` (`θ = 0` on `s ≤ 1/2`, `θ = 1` on `s ≥ 1`) one has
`(K+1)(s^{-1/2} h(η/√s)) = 0`, so `Q_ε b = -2ε s θ'(s) s^{-1/2} h(η/√s) e_r` is supported in
`[1/2, 1]` and `b` is in the graph class; its lift is `θ(R²/ρ²) h(z) e_r`, whose radial
component has the axis trace `h(z) ≠ 0`.  The functional
`Λ(b, Qb) = ∫_{s>0, cell} (Qb_r ψ - b_r Q_εᵗψ)`, `ψ = σ(s) s⁻¹ h(η/√s)` (`σ = 0` near `0`,
`σ = 1` on `s ≥ 1/2`), is bounded by `‖b‖_{H_r} + ‖√s Qb‖_{H_r}` exactly when `r > 2`, vanishes on
nice profiles (integration by parts, no boundary at the axis) and equals `-2ε‖h‖₂²` on `b`.  The
refutations are stated and compiled in `Sub/T09_2_1/Refute.lean`.  The source never claims
`√s T_εF ∈ H_r` (SP 1912-1918; for `T_εF` from the Cartesian graph only the hoop term `w_r/ρ`
is controlled, `w_z/ρ ∉ L^r` near the axis), so adding `√s b ∈ H_r` to the class is not an option.

## The corrected route (this file)

The divergence functional only sees `s Q_ε b_r`.  The phase pairing of `s·G` is bounded by
`‖G‖_{H_r}` (`DivHolderB`, `T09/3/2`, accepted) and that of `s·(Q, ε b, E)` by the graph norm
(`DivBound`, `T09/3/3`, accepted).  So it suffices to approximate with `Q_ε b` measured in the sum
space `s^{-1/2} H_r + H_r`: `DivCloseW`.  The `s`-cutoff error `-2ε (S χ_n) b` is small in `H_r`
(no `√s` needed), so `DivSCutApproxW` holds; the `η`-cutoff and mollification stages
(`DivEtaCutApprox`, `DivMollApprox`, accepted) are strong-norm statements and compose
(`divCloseW_trans_close`).

Proved here: `divApproxW_of`, `divContW_of`, `divFormulaW_of`, `hasPtw_div_NvC_ofW` (same
conclusion as `hasPtw_div_NvC_of` of `Sub/T09.lean`, with `DivApproxW`, `DivContW` in place of the
false `DivApprox` and the then unused `DivCont`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- **Weak graph closeness** (SP 1912-1918): `‖b' - b‖_{H_r} < δ`, `‖√s (Eb' - Eb)‖_{H_r} < δ`, and
`Qb' - Qb = G + H` with `‖√s G‖_{H_r} + ‖H‖_{H_r} < δ` (the `Q_ε`-difference measured in the sum
space `s^{-1/2} H_r + H_r`). -/
def DivCloseW (c r : ℝ) (b Qb Eb b' Qb' Eb' : CProf) (δ : ℝ) : Prop :=
  hNorm c r (fun x => b' x - b x) < ENNReal.ofReal δ ∧
    (∃ G H : CProf, InHr c r (sqrtS G) ∧ InHr c r H ∧ (∀ x, Qb' x - Qb x = G x + H x) ∧
      hNorm c r (sqrtS G) + hNorm c r H < ENNReal.ofReal δ) ∧
    hNorm c r (sqrtS fun x => Eb' x - Eb x) < ENNReal.ofReal δ

/-- **Stage 1, corrected (`T09/2/1`)**: the `s`-cutoff approximates in the weak graph norm.
Multiply by `χ_n(s) = bump(log s / n)`: `Q_ε(χ_n b) = χ_n Q_ε b - 2ε (Sχ_n) b`, where
`G = (χ_n - 1) Q_ε b` (small in `s^{-1/2} H_r`) and `H = -2ε(Sχ_n) b` (small in `H_r`,
`|Sχ_n| ≤ M/n`). -/
def DivSCutApproxW : Prop :=
  ∀ (c r ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    ∀ δ : ℝ, 0 < δ → ∃ b' Qb' Eb' : CProf, DivDataS c r ε b' Qb' Eb' ∧
      DivCloseW c r b Qb Eb b' Qb' Eb' δ

/-- **`T09/2`, corrected**: nice profiles approximate every graph triple in the weak graph norm. -/
def DivApproxW : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    ∃ bn Qbn Ebn : ℕ → CProf, (∀ n, NiceProf c (bn n) ∧ DivData c r ε (bn n) (Qbn n) (Ebn n)) ∧
      ∀ n : ℕ, DivCloseW c r b Qb Eb (bn n) (Qbn n) (Ebn n) (1 / ((n : ℝ) + 1))

/-- Continuity of the divergence functional `(b, Qb, Eb) ↦ ⟪φ, s[(Qb + εb)_r + Eb_z]⟫` along
weak-graph-norm approximations (SP 1658-1660, 1912-1916). -/
def DivContW : Prop :=
  ∀ (c ε r : ℝ) (φ : ℝ × Space → ℂ) (b Qb Eb : CProf) (bn Qbn Ebn : ℕ → CProf),
    0 < c → 0 < ε → 2 < r → IsPhaseTest (2 * ε * c) φ → DivData c r ε b Qb Eb →
    (∀ n, DivData c r ε (bn n) (Qbn n) (Ebn n)) →
    (∀ n : ℕ, DivCloseW c r b Qb Eb (bn n) (Qbn n) (Ebn n) (1 / ((n : ℝ) + 1))) →
    Tendsto (fun n => phaseInt (2 * ε * c)
        (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x)) atTop
      (𝓝 (phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x)))

theorem inHr_add_w {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r f) (hg : InHr c r g) :
    InHr c r (fun x => f x + g x) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  refine ⟨?_, hf.meas.add hg.meas, ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x h1 h2
    simp only [h1, h2]
  · have e : (fun x => f x + g x) = f + g := rfl
    unfold hNorm
    rw [e]
    exact lt_of_le_of_lt (eLpNorm_add_le hf.meas hg.meas hr1)
      (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

/-- Weak closeness followed by strong closeness is weak closeness. -/
theorem divCloseW_trans_close {c r ε : ℝ} (hr : 1 < r) {b Qb Eb b' Qb' Eb' b'' Qb'' Eb'' : CProf}
    {δ₁ δ₂ : ℝ} (h₀ : 0 ≤ δ₁) (h₁ : 0 ≤ δ₂)
    (d0 : DivData c r ε b Qb Eb) (d1 : DivData c r ε b' Qb' Eb')
    (d2 : DivData c r ε b'' Qb'' Eb'')
    (c1 : DivCloseW c r b Qb Eb b' Qb' Eb' δ₁) (c2 : DivClose c r b' Qb' Eb' b'' Qb'' Eb'' δ₂) :
    DivCloseW c r b Qb Eb b'' Qb'' Eb'' (δ₁ + δ₂) := by
  obtain ⟨G, H, hG, hH, hGH, hlt⟩ := c1.2.1
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have hD : InHr c r (sqrtS fun x => Qb'' x - Qb' x) := inHr_sqrtS_sub hr d2.inQ d1.inQ
  have eG : (sqrtS fun x => (Qb'' x - Qb' x) + G x) =
      (sqrtS fun x => Qb'' x - Qb' x) + sqrtS G := by
    funext x; simp [sqrtS, smul_add]
  have hG' : InHr c r (sqrtS fun x => (Qb'' x - Qb' x) + G x) := by
    rw [eG]; exact inHr_add_w hr hD hG
  refine ⟨lt_trans_close h₀ h₁ (hNorm_sub_trans_le hr d0.inHr d1.inHr d2.inHr) c2.1 c1.1,
    ⟨fun x => (Qb'' x - Qb' x) + G x, H, hG', hH, fun x => ?_, ?_⟩,
    lt_trans_close h₀ h₁ (hNorm_sub_trans_sqrt hr d0.inE d1.inE d2.inE) c2.2.2 c1.2.2⟩
  · show Qb'' x - Qb x = (Qb'' x - Qb' x + G x) + H x
    rw [add_assoc, ← hGH x]
    abel
  · have hle : hNorm c r (sqrtS fun x => (Qb'' x - Qb' x) + G x) ≤
        hNorm c r (sqrtS fun x => Qb'' x - Qb' x) + hNorm c r (sqrtS G) := by
      unfold hNorm
      rw [eG]
      exact eLpNorm_add_le hD.meas hG.meas hr1
    calc hNorm c r (sqrtS fun x => (Qb'' x - Qb' x) + G x) + hNorm c r H
        ≤ hNorm c r (sqrtS fun x => Qb'' x - Qb' x) + (hNorm c r (sqrtS G) + hNorm c r H) := by
          rw [← add_assoc]; exact add_le_add hle le_rfl
      _ < ENNReal.ofReal δ₂ + ENNReal.ofReal δ₁ := ENNReal.add_lt_add c2.2.1 hlt
      _ = ENNReal.ofReal (δ₁ + δ₂) := by rw [add_comm (ENNReal.ofReal δ₂), ENNReal.ofReal_add h₀ h₁]

/-- **`DivApproxW` from the corrected stage 1 and the (accepted) stages 2 and 3.** -/
theorem divApproxW_of (h1 : DivSCutApproxW) (h2 : DivEtaCutApprox) (h3 : DivMollApprox) :
    DivApproxW := by
  intro c ε r b Qb Eb hc hε hr hp
  have hr1 : 1 < r := by linarith
  have key : ∀ n : ℕ, ∃ b' Qb' Eb' : CProf, NiceProf c b' ∧ DivData c r ε b' Qb' Eb' ∧
      DivCloseW c r b Qb Eb b' Qb' Eb' (1 / ((n : ℝ) + 1)) := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hδ3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 3 := by positivity
    obtain ⟨b1, Q1, E1, hp1, hc1⟩ := h1 c r ε b Qb Eb hc hε hr hp _ hδ3
    obtain ⟨b2, Q2, E2, hp2, hc2⟩ := h2 c r ε b1 Q1 E1 hc hε hr hp1 _ hδ3
    obtain ⟨b3, Q3, E3, hn3, hp3, hc3⟩ := h3 c r ε b2 Q2 E2 hc hε hr hp2 _ hδ3
    refine ⟨b3, Q3, E3, hn3, hp3, ?_⟩
    have c12 := divCloseW_trans_close hr1 hδ3.le hδ3.le hp hp1.1 hp2.1.1 hc1 hc2
    have c123 := divCloseW_trans_close hr1 (by positivity) hδ3.le hp hp2.1.1 hp3 c12 hc3
    have e : 1 / ((n : ℝ) + 1) / 3 + 1 / ((n : ℝ) + 1) / 3 + 1 / ((n : ℝ) + 1) / 3 =
        1 / ((n : ℝ) + 1) := by ring
    rwa [e] at c123
  choose bn Qn En hn hp' hcl using key
  exact ⟨bn, Qn, En, fun n => ⟨hn n, hp' n⟩, hcl⟩

/-- **`DivContW` from the accepted Hölder bounds** `DivBound` (`T09/3/3`) and `DivHolderB`
(`T09/3/2`): split `Qbₙ - Qb = Gₙ + Hₙ`; the pairing of `gDiv(bₙ - b, Gₙ, Ebₙ - Eb)` is bounded by
`DivBound`, that of `s Hₙ,r` by `DivHolderB`. -/
theorem divContW_of (hB : DivBound) (hH : DivHolderB) : DivContW := by
  intro c ε r φ b Qb Eb bn Qbn Ebn hc hε hr hφ hd hdn hcl
  have hr1 : 1 < r := by linarith
  obtain ⟨K, hK⟩ := hB c ε r φ hc hε hr hφ
  obtain ⟨K', hK'⟩ := hH c ε r φ hc hε hr hφ
  choose G H hG hH hGH hlt using fun n => (hcl n).2.1
  have hδ0 : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hδlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := hK b Qb Eb hd.inHr hd.inQ hd.inE
  have hbn := fun n => hK (bn n) (Qbn n) (Ebn n) (hdn n).inHr (hdn n).inQ (hdn n).inE
  have hA := fun n => hK (fun x => bn n x - b x) (G n) (fun x => Ebn n x - Eb x)
    (inHr_sub hr1 (hdn n).inHr hd.inHr) (hG n) (inHr_sqrtS_sub hr1 (hdn n).inE hd.inE)
  have hHn := fun n => hK' (H n) 0 (hH n)
  have hpt : ∀ (n : ℕ) (z : ℝ × Space),
      φ z * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) z - φ z * sLift ε⁻¹ (gDiv ε b Qb Eb) z =
        φ z * sLift ε⁻¹ (gDiv ε (fun x => bn n x - b x) (G n) (fun x => Ebn n x - Eb x)) z +
          φ z * sLift ε⁻¹ (fun y => (y.1 : ℂ) * H n y 0) z := by
    intro n z
    have h0 := congrArg (fun v : CMerid => v 0) (hGH n (Axi.chart ε⁻¹ z.1 z.2))
    simp only [PiLp.sub_apply, PiLp.add_apply] at h0
    simp only [sLift, gDiv, PiLp.sub_apply]
    linear_combination φ z * ((Axi.chart ε⁻¹ z.1 z.2).1 : ℂ) * h0
  have hlin : ∀ n : ℕ,
      phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x) -
        phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) =
      phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹
          (gDiv ε (fun x => bn n x - b x) (G n) (fun x => Ebn n x - Eb x)) x) +
        phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (fun y => (y.1 : ℂ) * H n y 0) x) := by
    intro n
    have i1 := (hbn n).1
    have i2 := hb.1
    have i3 := (hA n).1
    have i4 := (hHn n).1
    rw [phaseInt_eq_slab i1, phaseInt_eq_slab i2, phaseInt_eq_slab i3, phaseInt_eq_slab i4,
      ← smul_sub, ← smul_add, ← integral_sub i1 i2, ← integral_add i3 i4]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => hpt n z)
  have hbound : ∀ n : ℕ,
      ‖phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x) -
        phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x)‖ ≤
      K * ((hNorm c r (fun x => bn n x - b x)).toReal + (hNorm c r (sqrtS (G n))).toReal +
          (hNorm c r (sqrtS fun x => Ebn n x - Eb x)).toReal) +
        K' * (hNorm c r (H n)).toReal := by
    intro n
    rw [hlin n]
    exact (norm_add_le _ _).trans (add_le_add (hA n).2 (hHn n).2)
  have e1 : ∀ n : ℕ, (hNorm c r (fun x => bn n x - b x)).toReal ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ENNReal.toReal_le_of_le_ofReal (hδ0 n) (hcl n).1.le
  have e2 : ∀ n : ℕ, (hNorm c r (sqrtS (G n))).toReal ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ENNReal.toReal_le_of_le_ofReal (hδ0 n) (le_trans le_self_add (hlt n).le)
  have e3 : ∀ n : ℕ, (hNorm c r (sqrtS fun x => Ebn n x - Eb x)).toReal ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ENNReal.toReal_le_of_le_ofReal (hδ0 n) (hcl n).2.2.le
  have e4 : ∀ n : ℕ, (hNorm c r (H n)).toReal ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ENNReal.toReal_le_of_le_ofReal (hδ0 n) (le_trans le_add_self (hlt n).le)
  have l1 := squeeze_zero (fun n => ENNReal.toReal_nonneg) e1 hδlim
  have l2 := squeeze_zero (fun n => ENNReal.toReal_nonneg) e2 hδlim
  have l3 := squeeze_zero (fun n => ENNReal.toReal_nonneg) e3 hδlim
  have l4 := squeeze_zero (fun n => ENNReal.toReal_nonneg) e4 hδlim
  have hS : Tendsto (fun n : ℕ =>
      K * ((hNorm c r (fun x => bn n x - b x)).toReal + (hNorm c r (sqrtS (G n))).toReal +
          (hNorm c r (sqrtS fun x => Ebn n x - Eb x)).toReal) +
        K' * (hNorm c r (H n)).toReal) atTop (𝓝 0) := by
    have := (((l1.add l2).add l3).const_mul K).add (l4.const_mul K')
    simpa using this
  have hdiff := squeeze_zero_norm hbound hS
  simpa using
    hdiff.add_const (phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x))

/-- The divergence formula on the whole graph class through the weak approximation. -/
theorem divFormulaW_of (h1 : DivSmooth) (h2 : DivApproxW) (h3 : DivContW) (h4 : DriftPairCont)
    {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r) {b Qb Eb : CProf}
    (hd : DivData c r ε b Qb Eb) (φ : ℝ × Space → ℂ) (hφ : IsPhaseTest (2 * ε * c) φ) :
    pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ b) =
      -phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) := by
  obtain ⟨bn, Qbn, Ebn, hn, hcl⟩ := h2 c ε r b Qb Eb hc hε hr hd
  have e : ∀ n, pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ (bn n)) =
      -phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x) :=
    fun n => h1 c ε (bn n) (Qbn n) (Ebn n) hc hε (hn n).1 (hn n).2.weakQ (hn n).2.weakE φ hφ
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have t1 : Tendsto (fun n => hNorm c r (fun x => bn n x - b x)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le)
      (fun n => (hcl n).1.le)
  have l1 := h4 c r ε (gradT φ) hc hε (by linarith) hφ.gradT b bn hd.inHr
    (fun n => (hn n).2.inHr) t1
  have l2 := (h3 c ε r φ b Qb Eb bn Qbn Ebn hc hε hr hφ hd (fun n => (hn n).2) hcl).neg
  simp only [e] at l1
  exact tendsto_nhds_unique l1 l2

/-- **Target `hasPtw_div_NvC`, corrected route**: same conclusion as `hasPtw_div_NvC_of`
(`Sub/T09.lean`), from `DivSmooth` (`T09/1`), `DivApproxW` (`T09/2`, corrected),
`DivContW` (`divContW_of divBound_proof divHolderB_proof`), `DriftPairCont` and `DivVanish`
(`T09/4`). -/
theorem hasPtw_div_NvC_ofW (h1 : DivSmooth) (h2 : DivApproxW) (h3 : DivContW)
    (h4 : DriftPairCont) (h5 : DivVanish) {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r)
    {b Qb Eb : CProf} (hd : DivData c r ε b Qb Eb) :
    (∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ →
        pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ b) = 0) ↔
      ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))),
        Qb x 0 + (ε : ℂ) * b x 0 + Eb x 1 = 0 := by
  rw [← h5 c ε r b Qb Eb hc hε hr hd]
  refine forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [divFormulaW_of h1 h2 h3 h4 hc hε hr hd φ hφ, neg_eq_zero]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divApproxW_of
#print axioms UnforcedLeray.Short.IIb.divContW_of
#print axioms UnforcedLeray.Short.IIb.hasPtw_div_NvC_ofW
