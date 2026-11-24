import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ent
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth

/-!
# The entrance coefficient change, pointwise: design (organizer task
`PartIII-b:C/rep/8/2/pres/4/org2/1/org`)

Source `the November 2 reference manuscript`
2347-2356 (periodized eigenstream `(π/c)²csc²(π(q+iη)/c)`: "the actual periodized stream and every
fixed derivative have exponential transverse decay, with polynomial `c` costs"; the rate is
`2π/c = 2πν²`), 2360-2366 (ring lift `e_ε` of the inlet stream), 2389-2390
(`‖E_εα‖_{W^{j,∞}} ≤ P_{ν,j}|α|`), 2516-2520 (`‖z‖_Z ≤ ρ_b`, `|α| = ε^{8/11}|A| ≤ P_ν e^{m/ν}ε`).

`EntWPt` (restated with the period rate `m₁ν²`, `Sub/PartIII-b_C_rep_8_2_pres_4_ent.lean`) is
proved here from two leaves:

* `InletChartJet` : at every chart point `x = (s, (q, η))`, `s > 0`, the Cartesian jets of order
  `≤ 2` of one inlet column `E_i = N_v e_ε` at `(τ, y) = (chartTau R x, chartY R x)` are
  `≤ C ν^{-k}(1+|η|)² e^{-κν²|η|}` (inlet-profile jets with decay `IIb.inletJetDecay`, rate
  `κ/c = κν²`; pointwise ring-lift jets `ringLiftPtJet` at every age; `chart R τ y = x`);
* `CoefChgSumLe` : the coefficient-change density of `U = W + Σ aᵢEᵢ` against `W` is
  `≤ Σ|aᵢ| Σ_{j ≤ 2}‖DʲEᵢ‖` at a point of an open set where `W, Eᵢ` are `C²` (linearity of
  `fderiv` and `secondJet`).

The coefficient bound `|αᵢ| ≤ C₀ν^{-k₀}e^{m₀/ν}ε` (2516-2520) is proved here from the ball split
(`IsActualLevel.ball`, `‖cA z‖ ≤ ‖z‖ ≤ ρ_b`), and the polynomial weight `(1+|η|)²` is absorbed by
halving the rate: `(1+t)²e^{-at} ≤ (1+4/a)²e^{-at/2}`, `a = κν²`, `(1+4/(κν²))² ≤ (1+4/κ)²ν^{-4}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Cartesian jets of a ring lift at a chart point, every age** (source 1206-1222, 2360-2366;
the chart-point form of the proved `RingLiftPtJet`): for `R ≥ 1` and a profile `b` that is `C^∞`
on `s > 0`, at `y = chartY R x`, `τ = chartTau R x`, `x = (s, (q, η))`, `s > 0` (so that
`chart R τ y = x`, `age R y = s`, `trans R y = η`),
`‖DʲN_v b(τ, y)‖ ≤ C (1+s)^k (1+|η|)^j Σ_{l ≤ j} ‖D^l b(x)‖`. -/
def RingLiftChartPt : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (R : ℝ) (b : Chart → Merid), 1 ≤ R → ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) →
      ∀ x : Chart, 0 < x.1 →
        ‖iteratedFDeriv ℝ j (Nv R b (NearInst.chartTau R x)) (NearInst.chartY R x)‖ ≤
          C * (1 + x.1) ^ k * (1 + |x.2.2|) ^ j *
            ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b x‖

/-- **Chart-point jets of one inlet column with the period decay rate** (source 2347-2356,
2360-2366, 2389-2390): for the growing eigenpair `(λ, q)` and slow age `Σ`, in the regime and for
small `ν`, at every chart point `x = (s, (q', η))` with `s > 0`, the Cartesian derivatives of order
`j ≤ 2` of `E_i(τ, ·) = N_v e_ε(τ, ·)` at `y = chartY R x`, `τ = chartTau R x` (`R = ε⁻¹`) satisfy
`‖DʲE_i(τ, y)‖ ≤ C ν^{-k}(1+|η|)² e^{-κν²|η|}`. -/
def InletChartJet : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C κ : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q → ∀ (i : Fin 2) (x : Chart), 0 < x.1 → ∀ j : ℕ, j ≤ 2 →
        ‖iteratedFDeriv ℝ j (p.inlet i (NearInst.chartTau p.R x)) (NearInst.chartY p.R x)‖ ≤
          C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ 2 * Real.exp (-(κ * p.ν ^ 2) * |x.2.2|)

/-- **The coefficient-change density of an affine perturbation** (pure calculus; source
5287-5289 with 2389-2390): if `U = W + Σᵢ aᵢ • Eᵢ` everywhere and `W`, `Eᵢ` are `C²` on an open set
containing `y`, then `|U - W| + |DU - DW| + |D²U - D²W|` at `y` (`coefChgDens`, with `secondJet`)
is at most `Σᵢ |aᵢ| Σ_{j ≤ 2} ‖DʲEᵢ(y)‖`. -/
def CoefChgSumLe : Prop :=
  ∀ (U W : Space → Space) (E : Fin 2 → Space → Space) (a : Fin 2 → ℝ) (s : Set Space)
    (y : Space), IsOpen s → y ∈ s → ContDiffOn ℝ 2 W s → (∀ i, ContDiffOn ℝ 2 (E i) s) →
    (∀ x, U x = W x + ∑ i : Fin 2, a i • E i x) →
    coefChgDens U W y ≤
      ∑ i : Fin 2, |a i| * ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j (E i) y‖

namespace EntWPtOrg

/-- Absorption of the polynomial weight by half of the rate. -/
private lemma absorb {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (1 + t) ^ 2 * Real.exp (-a * t) ≤ (1 + 4 / a) ^ 2 * Real.exp (-(a / 2) * t) := by
  have h0 := Real.add_one_le_exp (a * t / 4)
  have h2 : 1 ≤ Real.exp (a * t / 4) := Real.one_le_exp (by positivity)
  have h1 : t ≤ 4 / a * Real.exp (a * t / 4) := by
    have e : t = 4 / a * (a * t / 4) := by field_simp
    calc t = 4 / a * (a * t / 4) := e
      _ ≤ 4 / a * Real.exp (a * t / 4) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4a : 0 ≤ 4 / a := by positivity
  have h3 : 1 + t ≤ (1 + 4 / a) * Real.exp (a * t / 4) := by nlinarith
  have h4 : (1 + t) ^ 2 ≤ ((1 + 4 / a) * Real.exp (a * t / 4)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h3 2
  have he : Real.exp (a * t / 4) ^ 2 * Real.exp (-a * t) = Real.exp (-(a / 2) * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc (1 + t) ^ 2 * Real.exp (-a * t)
      ≤ ((1 + 4 / a) * Real.exp (a * t / 4)) ^ 2 * Real.exp (-a * t) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = (1 + 4 / a) ^ 2 * (Real.exp (a * t / 4) ^ 2 * Real.exp (-a * t)) := by ring
    _ = (1 + 4 / a) ^ 2 * Real.exp (-(a / 2) * t) := by rw [he]

/-- The absorption at the period rate `a = κν²`, `0 < ν ≤ 1`. -/
private lemma absorb_nu {κ ν t : ℝ} (hκ : 0 < κ) (hν : 0 < ν) (hν1 : ν ≤ 1) (ht : 0 ≤ t) :
    (1 + t) ^ 2 * Real.exp (-(κ * ν ^ 2) * t) ≤
      (1 + 4 / κ) ^ 2 * ν⁻¹ ^ 4 * Real.exp (-(κ / 2 * ν ^ 2) * t) := by
  have ha : 0 < κ * ν ^ 2 := by positivity
  have h := absorb ha ht
  have hνi : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hνi2 : 1 ≤ ν⁻¹ ^ 2 := one_le_pow₀ hνi
  have hq : 4 / (κ * ν ^ 2) = 4 / κ * ν⁻¹ ^ 2 := by
    rw [inv_pow, div_mul_eq_mul_div]
    field_simp
  have h4k : 0 ≤ 4 / κ := by positivity
  have hb : 1 + 4 / (κ * ν ^ 2) ≤ (1 + 4 / κ) * ν⁻¹ ^ 2 := by
    rw [hq]; nlinarith
  have hb2 : (1 + 4 / (κ * ν ^ 2)) ^ 2 ≤ (1 + 4 / κ) ^ 2 * ν⁻¹ ^ 4 := by
    calc (1 + 4 / (κ * ν ^ 2)) ^ 2 ≤ ((1 + 4 / κ) * ν⁻¹ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
      _ = (1 + 4 / κ) ^ 2 * ν⁻¹ ^ 4 := by ring
  have hr : -(κ * ν ^ 2 / 2) * t = -(κ / 2 * ν ^ 2) * t := by ring
  rw [hr] at h
  exact h.trans (mul_le_mul_of_nonneg_right hb2 (Real.exp_pos _).le)

/-- `|αᵢ| ≤ ε^{8/11}ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε` on a ball split (source 2516-2520). -/
private lemma coord_le (p : Params) (m0 C0 : ℝ) (k0 : ℕ) (z : p.Z)
    (hz : ‖z‖ ≤ UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) (i : Fin 2) :
    |p.coord z i| ≤ C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε := by
  have hε := p.ε_pos
  have hA : ‖UnforcedLeray.Cons.C03.Concrete.cA p.period (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)‖
      ≤ ‖z‖ := by
    have h := UnforcedLeray.Cons.C03.Concrete.norm_amb p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)
    have hz' : ‖(z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)‖ = ‖z‖ := rfl
    rw [← hz', h]
    have := norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cw p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))
    have := norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cΔ p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))
    have := norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cT p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))
    linarith
  have hi : |(UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le (UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i
    rw [Real.norm_eq_abs] at this
    exact this.trans hA
  have hpow : 0 < p.ε ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos hε _
  have he : p.ε ^ (8 / 11 : ℝ) * p.ε ^ (3 / 11 : ℝ) = p.ε := by
    rw [← Real.rpow_add hε]; norm_num
  unfold Params.coord
  rw [abs_mul, abs_of_pos hpow]
  calc p.ε ^ (8 / 11 : ℝ) * |(UnforcedLeray.Cons.C03.Concrete.cA p.period
        (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i|
      ≤ p.ε ^ (8 / 11 : ℝ) * UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 :=
        mul_le_mul_of_nonneg_left (hi.trans hz) hpow.le
    _ = C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * (p.ε ^ (8 / 11 : ℝ) * p.ε ^ (3 / 11 : ℝ)) := by
        unfold UnforcedLeray.Short.IIb.rhoB; ring
    _ = C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε := by rw [he]

/-- A phase slice of a field that is `C²` off the axis in `(τ, y)` is `C²` off the axis in `y`. -/
private lemma slice {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × Space → F)
    (h : ContDiffOn ℝ 2 f offAxis) (τ : ℝ) : ContDiffOn ℝ 2 (fun w : Space => f (τ, w)) axisᶜ :=
  h.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hw => hw)

/-- A phase slice of a jointly smooth field is `C²`. -/
private lemma slice' {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × Space → F)
    (h : ContDiff ℝ ∞ f) (τ : ℝ) : ContDiffOn ℝ 2 (fun w : Space => f (τ, w)) axisᶜ :=
  ((h.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)).contDiffOn

end EntWPtOrg

open EntWPtOrg in
/-- **`EntWPt` from the two leaves** (source 2347-2356, 2389-2390, 2516-2520): on an actual level,
`V - U_raw = Σᵢ αᵢEᵢ` (ball split), `|αᵢ| ≤ C₀ν^{-k₀}e^{m₀/ν}ε`, the jets of `Eᵢ` at the chart
point are `≤ Cν^{-k}(1+|η|)²e^{-κν²|η|}`, and the weight is absorbed at the rate `(κ/2)ν²`. -/
theorem entWPt_of (hJ : InletChartJet) (hB : CoefChgSumLe) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : EntWPt D := by
  obtain ⟨C, κ, k, ν₀, hC, hκ, hν₀, hJ'⟩ := hJ D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos
    hst.planar.eigenpair dm dp hst.dm_pos
  obtain ⟨ν₁, hν₁, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue
    D.Pl.mode D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < min (min ν₀ ν₁) 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (lt_min (lt_min hν₀ hν₁) one_pos))
  have hC0 : 0 < D.K.C0 := hst.C0_pos
  refine ⟨6 * D.K.C0 * C * (1 + 4 / κ) ^ 2, D.K.k0 + k + 4, κ / 2, by positivity, ?_⟩
  filter_upwards [hst.actual, hν] with n hn hνn x hx
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν0 : (D.level n).ν ≤ ν₀ := (hνn.le.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hν1' : (D.level n).ν ≤ ν₁ := (hνn.le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hν1 : (D.level n).ν ≤ 1 := hνn.le.trans (min_le_right _ _)
  obtain ⟨z, -, hVz, -, hz⟩ := hn.ball
  -- the chart point
  have hy : NearInst.chartY (D.level n).ε⁻¹ x ∉ axis := by
    intro h
    have h0 : NearInst.chartY (D.level n).ε⁻¹ x 0 = (D.level n).ε⁻¹ / Real.sqrt x.1 := by
      simp [NearInst.chartY]
    have hpos : 0 < (D.level n).ε⁻¹ / Real.sqrt x.1 :=
      div_pos (inv_pos.2 hεpos) (Real.sqrt_pos.2 hx)
    rw [← h0, h.1] at hpos
    exact lt_irrefl _ hpos
  -- smoothness of the raw lift and the inlet columns at the phase
  have hraw : ContDiffOn ℝ 2
      (((D.level n).params D.Pl).raw (NearInst.chartTau (D.level n).ε⁻¹ x)) axisᶜ := by
    have hR := rawU_contDiffOn_offAxis_of ((D.level n).params D.Pl) (D.level n).ε_pos
      ((D.level n).train_stream_smooth.of_le (by norm_num))
    exact slice (fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2) hR _
  have hinl : ∀ i : Fin 2, ContDiffOn ℝ 2
      (((D.level n).params D.Pl).inlet i (NearInst.chartTau (D.level n).ε⁻¹ x)) axisᶜ := by
    intro i
    have hi := hS ((D.level n).params D.Pl) _ hn.regime hν1' rfl rfl i
    exact slice' (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) hi _
  -- the affine bridge
  have hbr := hB ((D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ x))
    (((D.level n).params D.Pl).raw (NearInst.chartTau (D.level n).ε⁻¹ x))
    (fun i => ((D.level n).params D.Pl).inlet i (NearInst.chartTau (D.level n).ε⁻¹ x))
    (fun i => ((D.level n).params D.Pl).coord z i) axisᶜ (NearInst.chartY (D.level n).ε⁻¹ x)
    isOpen_compl_axis hy hraw hinl (fun w => hVz _ w)
  -- the two factors
  set A : ℝ := D.K.C0 * ((D.level n).ν ^ D.K.k0)⁻¹ * Real.exp (D.K.m0 / (D.level n).ν) *
    (D.level n).ε with hAdef
  set B : ℝ := C * ((D.level n).ν ^ k)⁻¹ * (1 + |x.2.2|) ^ 2 *
    Real.exp (-(κ * (D.level n).ν ^ 2) * |x.2.2|) with hBdef
  have hco : ∀ i : Fin 2, |((D.level n).params D.Pl).coord z i| ≤ A :=
    fun i => coord_le ((D.level n).params D.Pl) D.K.m0 D.K.C0 D.K.k0 z hz i
  have hjet : ∀ i : Fin 2, ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j
      (((D.level n).params D.Pl).inlet i (NearInst.chartTau (D.level n).ε⁻¹ x))
        (NearInst.chartY (D.level n).ε⁻¹ x)‖ ≤ 3 * B := by
    intro i
    have hb : ∀ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j
        (((D.level n).params D.Pl).inlet i (NearInst.chartTau (D.level n).ε⁻¹ x))
          (NearInst.chartY (D.level n).ε⁻¹ x)‖ ≤ B := by
      intro j hj
      exact hJ' ((D.level n).params D.Pl) _ hn.regime hν0 rfl rfl i x hx j
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    calc _ ≤ ∑ _j ∈ Finset.range 3, B := Finset.sum_le_sum hb
      _ = 3 * B := by simp
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hsum : ∑ i : Fin 2, |((D.level n).params D.Pl).coord z i| *
      ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j
        (((D.level n).params D.Pl).inlet i (NearInst.chartTau (D.level n).ε⁻¹ x))
          (NearInst.chartY (D.level n).ε⁻¹ x)‖ ≤ 6 * (A * B) := by
    calc _ ≤ ∑ _i : Fin 2, A * (3 * B) :=
          Finset.sum_le_sum fun i _ => mul_le_mul (hco i) (hjet i) (by positivity) hA0
      _ = 6 * (A * B) := by simp; ring
  have hkey := absorb_nu (t := |x.2.2|) hκ hνpos hν1 (abs_nonneg _)
  have hfin : 6 * (A * B) ≤ 6 * D.K.C0 * C * (1 + 4 / κ) ^ 2 * (D.level n).ν⁻¹ ^ (D.K.k0 + k + 4) *
      (Real.exp (D.K.m0 / (D.level n).ν) * (D.level n).ε) *
        Real.exp (-(κ / 2 * (D.level n).ν ^ 2) * |x.2.2|) := by
    have hP : 0 ≤ 6 * D.K.C0 * C * (D.level n).ν⁻¹ ^ D.K.k0 * (D.level n).ν⁻¹ ^ k *
        Real.exp (D.K.m0 / (D.level n).ν) * (D.level n).ε := by positivity
    calc 6 * (A * B) = (6 * D.K.C0 * C * (D.level n).ν⁻¹ ^ D.K.k0 * (D.level n).ν⁻¹ ^ k *
          Real.exp (D.K.m0 / (D.level n).ν) * (D.level n).ε) *
          ((1 + |x.2.2|) ^ 2 * Real.exp (-(κ * (D.level n).ν ^ 2) * |x.2.2|)) := by
          rw [hAdef, hBdef, inv_pow, inv_pow]; ring
      _ ≤ (6 * D.K.C0 * C * (D.level n).ν⁻¹ ^ D.K.k0 * (D.level n).ν⁻¹ ^ k *
          Real.exp (D.K.m0 / (D.level n).ν) * (D.level n).ε) *
          ((1 + 4 / κ) ^ 2 * (D.level n).ν⁻¹ ^ 4 *
            Real.exp (-(κ / 2 * (D.level n).ν ^ 2) * |x.2.2|)) :=
          mul_le_mul_of_nonneg_left hkey hP
      _ = _ := by rw [pow_add, pow_add]; ring
  exact hbr.trans (hsum.trans hfin)

end UnforcedLeray.Short.PartIIIb.Concrete
