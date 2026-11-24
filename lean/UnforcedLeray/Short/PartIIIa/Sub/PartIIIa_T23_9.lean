import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_10

/-!
# Part III-a, task `PartIII-a:T23/9` (audit decomposition): `stress-short:coefficients`

Source of record: `the November 2 reference manuscript`, lines 2664-2745
(coefficients 2703-2727: the fourth bound is the `L²_η L^∞_q` bound of `v = v_raw + Σ α_i v_i`).

The fourth bound needs the `L²_η` Minkowski inequality, which needs the `η`-profiles
`η ↦ essSup_q (W‖f(s,q,η)‖)` to be a.e. measurable. Two leaves supply this:

* `EtaProfileAEMeasurable` : a general fact, jointly measurable slice `(q,η) ↦ f(s,q,η)` implies the
  `η`-profile is a.e. measurable;
* `ChartSliceMeasurable` : the chart coefficients of the raw lift and of the inlet columns are Borel
  measurable on every slice `s > 0` (SP 2706: they equal the train profile `b_raw` and the inlet
  profile `e_i`, built from the smooth train/stream and fixed Gaussian profiles).

`stressCoefficients_of_leaves` is the assembly (bounds 1-4) from these and `RawCoeffLate`,
`RawCoeffEarly`, `InletCoeffBounds`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- Leaf 1: the `η`-profile `η ↦ essSup_q (W ‖f‖)` of a jointly measurable slice is a.e. measurable
(`essSup_a g = inf {t : |{g > t}| = 0}` over a countable dense set of `t`, and
`η ↦ |{q : g(q,η) > t}|` is measurable by Fubini/Tonelli). -/
def EtaProfileAEMeasurable : Prop :=
  ∀ (c mZ : ℝ) (f : ℝ × (ℝ × ℝ) → Merid) (s : ℝ),
    Measurable (fun x : ℝ × ℝ => f (s, x)) →
    AEMeasurable (fun η : ℝ => essSup (fun q : ℝ =>
      ENNReal.ofReal (transWeight mZ (s, (q, η))) * ‖f (s, (q, η))‖ₑ)
      (volume.restrict (Ico (-(c / 2)) (c / 2)))) volume

/-- Leaf 2: at every level of the regime and every age `s > 0` the chart coefficients of the raw
lift and of the inlet columns are Borel measurable in `(q, η)` (SP 2703-2711: at `s > 0` they are
the train profile `b_raw` and the inlet profile `e_i`; the train and its stream are smooth for
`s > 0`, `BgRegime.train_buc`, `train_stream_smooth`). -/
def ChartSliceMeasurable : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → ∀ s : ℝ, 0 < s →
    Measurable (fun x : ℝ × ℝ => chartCoeff p.R p.raw (s, x)) ∧
    ∀ i : Fin 2, Measurable (fun x : ℝ × ℝ => chartCoeff p.R (p.inlet i) (s, x))

lemma t9_norm_combine (F : ℝ) (hF : 0 ≤ F) (vr v0 v1 : Merid) (a0 a1 M Br B0 B1 : ℝ)
    (ha0 : |a0| ≤ M) (ha1 : |a1| ≤ M) (hr : F * ‖vr‖ ≤ Br) (h0 : F * ‖v0‖ ≤ B0)
    (h1 : F * ‖v1‖ ≤ B1) :
    F * ‖vr + a0 • v0 + a1 • v1‖ ≤ Br + M * B0 + M * B1 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans ha0
  have t1 := norm_add_le (vr + a0 • v0) (a1 • v1)
  have t2 := norm_add_le vr (a0 • v0)
  rw [norm_smul, Real.norm_eq_abs] at t1 t2
  have t3' : ‖vr + a0 • v0 + a1 • v1‖ ≤ ‖vr‖ + |a0| * ‖v0‖ + |a1| * ‖v1‖ := by linarith
  have t3 : F * ‖vr + a0 • v0 + a1 • v1‖ ≤ F * ‖vr‖ + |a0| * (F * ‖v0‖) + |a1| * (F * ‖v1‖) := by
    calc F * ‖vr + a0 • v0 + a1 • v1‖ ≤ F * (‖vr‖ + |a0| * ‖v0‖ + |a1| * ‖v1‖) :=
          mul_le_mul_of_nonneg_left t3' hF
      _ = _ := by ring
  have u0 : |a0| * (F * ‖v0‖) ≤ M * B0 :=
    mul_le_mul ha0 h0 (mul_nonneg hF (norm_nonneg _)) hM
  have u1 : |a1| * (F * ‖v1‖) ≤ M * B1 :=
    mul_le_mul ha1 h1 (mul_nonneg hF (norm_nonneg _)) hM
  linarith

lemma t9_absC (C y : ℝ) (hy : 0 ≤ y) : C * y ≤ |C| * y :=
  mul_le_mul_of_nonneg_right (le_abs_self C) hy

lemma t9_final (x T : ℝ) (hx : 1 ≤ x) (hT : 0 ≤ T) (k1 k2 k3 k0 : ℕ) (C1 C2 C3 C0 Br B0 B1 : ℝ)
    (hBr : Br ≤ 2 * (|C1| + |C2|) * x ^ (max k1 k2) * T)
    (hB0 : B0 ≤ |C3| * x ^ k3 * T) (hB1 : B1 ≤ |C3| * x ^ k3 * T) :
    Br + |C0| * x ^ k0 * B0 + |C0| * x ^ k0 * B1 ≤
      (2 * (|C1| + |C2|) + 2 * |C0| * |C3|) * x ^ (max (max k1 k2) k3 + k0) * T := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hm : x ^ (max k1 k2) ≤ x ^ (max (max k1 k2) k3 + k0) :=
    pow_le_pow_right₀ hx (by have := le_max_left (max k1 k2) k3; omega)
  have hk : x ^ k0 * x ^ k3 ≤ x ^ (max (max k1 k2) k3 + k0) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hx (by have := le_max_right (max k1 k2) k3; omega)
  have e0 : |C0| * x ^ k0 * B0 ≤ |C0| * x ^ k0 * (|C3| * x ^ k3 * T) :=
    mul_le_mul_of_nonneg_left hB0 (by positivity)
  have e1 : |C0| * x ^ k0 * B1 ≤ |C0| * x ^ k0 * (|C3| * x ^ k3 * T) :=
    mul_le_mul_of_nonneg_left hB1 (by positivity)
  have eA : 2 * (|C1| + |C2|) * x ^ (max k1 k2) * T ≤
      2 * (|C1| + |C2|) * x ^ (max (max k1 k2) k3 + k0) * T := by gcongr
  have eB : |C0| * x ^ k0 * (|C3| * x ^ k3 * T) ≤
      |C0| * |C3| * x ^ (max (max k1 k2) k3 + k0) * T := by
    calc |C0| * x ^ k0 * (|C3| * x ^ k3 * T) = |C0| * |C3| * (x ^ k0 * x ^ k3) * T := by ring
      _ ≤ _ := by gcongr
  nlinarith [e0, e1, eA, eB]

lemma t9_step (C xk xm T Tbd c : ℝ) (hxk : 0 ≤ xk) (hxm : xk ≤ xm) (hT : 0 ≤ T)
    (hTb : T ≤ Tbd) (hc : |C| ≤ c) : C * xk * T ≤ c * xm * Tbd := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hc
  have h1 : C * xk * T ≤ |C| * xk * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hxk) hT
  have h2 : |C| * xk * T ≤ c * xm * Tbd :=
    mul_le_mul (mul_le_mul hc hxm hxk hc0) hTb hT (mul_nonneg hc0 (hxk.trans hxm))
  exact h1.trans h2

theorem stressCoefficients_of_leaves (h1 : UnforcedLeray.Short.IIIa.RawCoeffLate)
    (h2 : UnforcedLeray.Short.IIIa.RawCoeffEarly)
    (h3 : UnforcedLeray.Short.IIIa.InletCoeffBounds)
    (hA : EtaProfileAEMeasurable) (hB : ChartSliceMeasurable) :
    UnforcedLeray.Short.IIIa.StressCoefficients := by
  intro dm dp hdm m0 C0 k0 hm0 hm0le mZ hmZ Sig lam q hSig hq
  obtain ⟨C1, k1, n1, hn1, H1⟩ := h1 dm dp hdm mZ hmZ
  obtain ⟨C2, k2, n2, hn2, H2⟩ := h2 dm dp hdm mZ hmZ
  obtain ⟨C3, k3, n3, hn3, H3⟩ := h3 dm dp hdm mZ hmZ Sig lam q hSig hq
  refine ⟨2 * (|C1| + |C2|) + 2 * |C0| * |C3|, max (max k1 k2) k3 + k0,
    min (min n1 n2) (min n3 1), lt_min (lt_min hn1 hn2) (lt_min hn3 one_pos), ?_⟩
  intro p d hreg hν hSg hmode S_in V rb hsplit
  dsimp only
  have hνpos : 0 < p.ν := p.ν_pos
  have hνa : p.ν ≤ n1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ n2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνc : p.ν ≤ n3 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
  have hεpos : 0 < p.ε := p.ε_pos
  have hεle : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    have := hreg.dm_pos; have := hreg.dm_le
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hνpos.le
  obtain ⟨z, _, hVz, _, hcoord⟩ := hsplit.state
  have hVeq : V = fun t y => p.raw t y + p.coord z 0 • p.inlet 0 t y + p.coord z 1 • p.inlet 1 t y := by
    funext τ y
    rw [hVz τ y, Fin.sum_univ_two, add_assoc]
  have hv : chartCoeff p.R V = fun pt => chartCoeff p.R p.raw pt +
      p.coord z 0 • chartCoeff p.R (p.inlet 0) pt + p.coord z 1 • chartCoeff p.R (p.inlet 1) pt := by
    funext pt
    rw [hVeq]
    exact chartCoeff_sum2 p.R _ _ p.raw (p.inlet 0) (p.inlet 1) pt
  have hρ := t10_rhoB_le p d dm dp m0 C0 k0 hreg hm0le
  have hM : ∀ i : Fin 2, |p.coord z i| ≤ |C0| * p.ν⁻¹ ^ k0 := by
    intro i
    have := (hcoord i).trans hρ
    rwa [inv_pow] at *
  rw [hv]
  obtain ⟨R1, R2⟩ := H1 p d hreg hνa
  obtain ⟨Q1, Q2⟩ := H2 p d hreg hνb
  have hI := H3 p d hreg hνc hSg hmode
  set x := p.ν⁻¹ with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxk : ∀ j : ℕ, 0 ≤ x ^ j := fun j => by positivity
  have hF : ∀ pt : ℝ × (ℝ × ℝ), 0 ≤ Real.sqrt pt.1 * transWeight mZ pt := fun pt =>
    mul_nonneg (Real.sqrt_nonneg _) (by unfold transWeight; positivity)
  -- raw and inlet pointwise bounds
  have hxm1 : x ^ k1 ≤ x ^ (max k1 k2) := pow_le_pow_right₀ hx1 (le_max_left _ _)
  have hxm2 : x ^ k2 ≤ x ^ (max k1 k2) := pow_le_pow_right₀ hx1 (le_max_right _ _)
  have hCC : |C1| + |C2| ≤ 2 * (|C1| + |C2|) := by
    linarith [abs_nonneg C1, abs_nonneg C2]
  have hC1 : |C1| ≤ |C1| + |C2| := by linarith [abs_nonneg C2]
  have hC2 : |C2| ≤ |C1| + |C2| := by linarith [abs_nonneg C1]
  have hC2' : |C2| ≤ 2 * (|C1| + |C2|) := by linarith [abs_nonneg C1, abs_nonneg C2]
  have hsq1 : ∀ s : ℝ, s ≤ 1 → Real.sqrt s ≤ 1 := fun s hs => by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hs
  have hinl0 : ∀ (i : Fin 2) (S : ℝ), S_in ≤ S → 0 < S → ∀ pt : ℝ × (ℝ × ℝ), S < pt.1 →
      chartCoeff p.R (p.inlet i) pt = 0 := by
    intro i S hS hS0 pt hpt
    have hs : 0 < pt.1 := hS0.trans hpt
    have hlt : S_in < pt.1 := lt_of_le_of_lt hS hpt
    have hcond : S_in * ((!₂[p.R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1] :
        EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
        (!₂[p.R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1] :
        EuclideanSpace ℝ (Fin 3)) 1 ^ 2) < p.R ^ 2 := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [div_pow, Real.sq_sqrt hs.le]
      have hR2 : 0 < p.R ^ 2 := pow_pos p.R_pos 2
      have : S_in * (p.R ^ 2 / pt.1 + 0 ^ 2) = S_in * p.R ^ 2 / pt.1 := by ring
      rw [this, div_lt_iff₀ hs]
      nlinarith [mul_pos (sub_pos.2 hlt) hR2]
    have hz := hsplit.inlet_support i (2 * pt.2.1 / p.R + Real.log pt.1)
      (!₂[p.R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1]) hcond
    simp [chartCoeff, hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bound 1
    intro pt hpt
    beta_reduce
    have hraw : Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ ≤
        2 * (|C1| + |C2|) * x ^ (max k1 k2) * 1 := by
      by_cases hs1 : 1 ≤ pt.1
      · have a := R1 pt hs1
        have b : pt.1 ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
        have := t9_step C1 (x ^ k1) (x ^ (max k1 k2)) (pt.1 ^ (-1 / 2 : ℝ) + p.ε) 2 (|C1| + |C2|)
          (hxk _) hxm1 (by positivity) (by linarith) hC1
        calc _ ≤ _ := a
          _ ≤ _ := this
          _ = _ := by ring
      · have hs1' : pt.1 ≤ 1 := (not_le.1 hs1).le
        have a := Q1 pt hpt hs1'
        have := t9_step C2 (x ^ k2) (x ^ (max k1 k2)) (Real.sqrt pt.1) 1 (2 * (|C1| + |C2|))
          (hxk _) hxm2 (Real.sqrt_nonneg _) (hsq1 _ hs1') hC2'
        exact a.trans this
    have hin : ∀ i : Fin 2, Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
        |C3| * x ^ k3 * 1 := by
      intro i
      have a := (hI i).1 pt hpt
      have := t9_absC C3 (x ^ k3) (hxk _)
      calc _ ≤ C3 * x ^ k3 := a
        _ ≤ |C3| * x ^ k3 := this
        _ = _ := (mul_one _).symm
    have := t9_norm_combine (Real.sqrt pt.1 * transWeight mZ pt) (hF pt) (chartCoeff p.R p.raw pt)
      (chartCoeff p.R (p.inlet 0) pt) (chartCoeff p.R (p.inlet 1) pt) (p.coord z 0) (p.coord z 1)
      (|C0| * x ^ k0) _ _ _ (hM 0) (hM 1) hraw (hin 0) (hin 1)
    have h2 := t9_final x 1 hx1 zero_le_one k1 k2 k3 k0 C1 C2 C3 C0 _ _ _ le_rfl le_rfl le_rfl
    simpa only [mul_one] using this.trans h2
  · -- bound 2
    intro S hSin hS pt hpt
    beta_reduce
    have hpos : 0 < pt.1 := hS.trans hpt
    have hSpt : 0 ≤ S ^ (-1 / 2 : ℝ) + p.ε := by positivity
    have hraw : Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ ≤
        2 * (|C1| + |C2|) * x ^ (max k1 k2) * (S ^ (-1 / 2 : ℝ) + p.ε) := by
      by_cases hs1 : 1 ≤ pt.1
      · have a := R1 pt hs1
        have b : S ^ (-1 / 2 : ℝ) ≥ pt.1 ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hS hpt.le (by norm_num)
        have := t9_step C1 (x ^ k1) (x ^ (max k1 k2)) (pt.1 ^ (-1 / 2 : ℝ) + p.ε)
          (S ^ (-1 / 2 : ℝ) + p.ε) (2 * (|C1| + |C2|)) (hxk _) hxm1 (by positivity)
          (by linarith) (hC1.trans hCC)
        exact a.trans this
      · have hs1' : pt.1 ≤ 1 := (not_le.1 hs1).le
        have a := Q1 pt hpos hs1'
        have hS1 : S ≤ 1 := hpt.le.trans hs1'
        have b : (1 : ℝ) ≤ S ^ (-1 / 2 : ℝ) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hS hS1 (by norm_num)
        have := t9_step C2 (x ^ k2) (x ^ (max k1 k2)) (Real.sqrt pt.1)
          (S ^ (-1 / 2 : ℝ) + p.ε) (2 * (|C1| + |C2|)) (hxk _) hxm2 (Real.sqrt_nonneg _)
          (by linarith [hsq1 _ hs1']) hC2'
        exact a.trans this
    have hin : ∀ i : Fin 2, Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
        |C3| * x ^ k3 * (S ^ (-1 / 2 : ℝ) + p.ε) := by
      intro i
      rw [hinl0 i S hSin hS pt hpt]
      simp only [norm_zero, mul_zero]
      positivity
    have := t9_norm_combine (Real.sqrt pt.1 * transWeight mZ pt) (hF pt) (chartCoeff p.R p.raw pt)
      (chartCoeff p.R (p.inlet 0) pt) (chartCoeff p.R (p.inlet 1) pt) (p.coord z 0) (p.coord z 1)
      (|C0| * x ^ k0) _ _ _ (hM 0) (hM 1) hraw (hin 0) (hin 1)
    exact this.trans (t9_final x _ hx1 hSpt k1 k2 k3 k0 C1 C2 C3 C0 _ _ _ le_rfl le_rfl le_rfl)
  · -- bound 3
    intro σ hσ hσ1 pt hpt0 hptσ
    beta_reduce
    have hs1' : pt.1 ≤ 1 := hptσ.le.trans hσ1
    have hsσ : Real.sqrt pt.1 ≤ Real.sqrt σ := Real.sqrt_le_sqrt hptσ.le
    have hraw : Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R p.raw pt‖ ≤
        2 * (|C1| + |C2|) * x ^ (max k1 k2) * Real.sqrt σ := by
      have a := Q1 pt hpt0 hs1'
      have := t9_step C2 (x ^ k2) (x ^ (max k1 k2)) (Real.sqrt pt.1) (Real.sqrt σ)
        (2 * (|C1| + |C2|)) (hxk _) hxm2 (Real.sqrt_nonneg _) hsσ hC2'
      exact a.trans this
    have hin : ∀ i : Fin 2, Real.sqrt pt.1 * transWeight mZ pt * ‖chartCoeff p.R (p.inlet i) pt‖ ≤
        |C3| * x ^ k3 * Real.sqrt σ := by
      intro i
      have a := (hI i).2.1 pt hpt0 hs1'
      have := t9_step C3 (x ^ k3) (x ^ k3) (Real.sqrt pt.1) (Real.sqrt σ) |C3| (hxk _) le_rfl
        (Real.sqrt_nonneg _) hsσ le_rfl
      exact a.trans this
    have := t9_norm_combine (Real.sqrt pt.1 * transWeight mZ pt) (hF pt) (chartCoeff p.R p.raw pt)
      (chartCoeff p.R (p.inlet 0) pt) (chartCoeff p.R (p.inlet 1) pt) (p.coord z 0) (p.coord z 1)
      (|C0| * x ^ k0) _ _ _ (hM 0) (hM 1) hraw (hin 0) (hin 1)
    exact this.trans (t9_final x _ hx1 (Real.sqrt_nonneg _) k1 k2 k3 k0 C1 C2 C3 C0 _ _ _ le_rfl
      le_rfl le_rfl)
  · -- bound 4
    intro s hs
    obtain ⟨hr, hi⟩ := hB p d dm dp hreg s hs
    have hs0 : Measurable (fun x : ℝ × ℝ => p.coord z 0 • chartCoeff p.R (p.inlet 0) (s, x)) :=
      (hi 0).const_smul (p.coord z 0)
    have hs1 : Measurable (fun x : ℝ × ℝ => p.coord z 1 • chartCoeff p.R (p.inlet 1) (s, x)) :=
      (hi 1).const_smul (p.coord z 1)
    have e2 := etaL2QSup_add_le_of_aemeasurable p.c mZ (chartCoeff p.R p.raw)
      (fun pt => p.coord z 0 • chartCoeff p.R (p.inlet 0) pt) s
      (hA p.c mZ _ s hr) (hA p.c mZ (fun pt => p.coord z 0 • chartCoeff p.R (p.inlet 0) pt) s hs0)
    have e1 := etaL2QSup_add_le_of_aemeasurable p.c mZ
      (fun pt => chartCoeff p.R p.raw pt + p.coord z 0 • chartCoeff p.R (p.inlet 0) pt)
      (fun pt => p.coord z 1 • chartCoeff p.R (p.inlet 1) pt) s
      (hA p.c mZ (fun pt => chartCoeff p.R p.raw pt + p.coord z 0 • chartCoeff p.R (p.inlet 0) pt) s (hr.add hs0))
      (hA p.c mZ (fun pt => p.coord z 1 • chartCoeff p.R (p.inlet 1) pt) s hs1)
    have e3 := etaL2QSup_smul_le p.c mZ (p.coord z 0) (chartCoeff p.R (p.inlet 0)) s
    have e4 := etaL2QSup_smul_le p.c mZ (p.coord z 1) (chartCoeff p.R (p.inlet 1)) s
    have hTn : (0 : ℝ) ≤ (1 + s) ^ (-3 / 4 : ℝ) := by positivity
    have hT1 : (0 : ℝ) ≤ p.ε * (1 + s) ^ (-1 / 4 : ℝ) := by positivity
    have hTle : (1 + s) ^ (-3 / 4 : ℝ) ≤ (1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ) := by
      linarith
    have hTpos : (0 : ℝ) ≤ (1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ) := by linarith
    have hrawE : etaL2QSup p.c mZ (chartCoeff p.R p.raw) s ≤ ENNReal.ofReal
        (2 * (|C1| + |C2|) * x ^ (max k1 k2) *
          ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ))) := by
      by_cases hs1 : 1 ≤ s
      · refine (R2 s hs1).trans (ENNReal.ofReal_le_ofReal ?_)
        exact t9_step C1 (x ^ k1) (x ^ (max k1 k2)) _ _ (2 * (|C1| + |C2|)) (hxk _) hxm1 hTpos
          le_rfl (hC1.trans hCC)
      · have hs1' : s ≤ 1 := (not_le.1 hs1).le
        refine (Q2 s hs hs1').trans (ENNReal.ofReal_le_ofReal ?_)
        have hp : 0 < (1 + s) ^ (3 / 4 : ℝ) := by positivity
        have hle : (1 + s) ^ (3 / 4 : ℝ) ≤ 2 := by
          calc (1 + s) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) :=
                Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
            _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        have hh : (2 : ℝ)⁻¹ ≤ ((1 + s) ^ (3 / 4 : ℝ))⁻¹ := inv_anti₀ hp hle
        have hh2 : (1 + s) ^ (-3 / 4 : ℝ) = ((1 + s) ^ (3 / 4 : ℝ))⁻¹ := by
          rw [← Real.rpow_neg (by linarith)]; norm_num
        have h1T : (1 : ℝ) ≤ 2 * ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ)) := by
          rw [hh2] at hTle ⊢
          linarith
        have := t9_step C2 (x ^ k2) (x ^ (max k1 k2)) 1
          (2 * ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ))) (|C1| + |C2|)
          (hxk _) hxm2 zero_le_one h1T hC2
        calc C2 * x ^ k2 ≤ _ := by simpa using this
          _ = _ := by ring
    have hinE : ∀ i : Fin 2, etaL2QSup p.c mZ (chartCoeff p.R (p.inlet i)) s ≤ ENNReal.ofReal
        (|C3| * x ^ k3 * ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ))) := by
      intro i
      refine ((hI i).2.2 s hs).trans (ENNReal.ofReal_le_ofReal ?_)
      exact t9_step C3 (x ^ k3) (x ^ k3) _ _ |C3| (hxk _) le_rfl hTn hTle le_rfl
    set T := (1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ) with hTdef
    set Rr := 2 * (|C1| + |C2|) * x ^ (max k1 k2) * T with hRr
    set Ri := |C3| * x ^ k3 * T with hRi
    have hRr0 : 0 ≤ Rr := by positivity
    have hRi0 : 0 ≤ Ri := by positivity
    have hc0 : ∀ i : Fin 2, 0 ≤ |p.coord z i| := fun i => abs_nonneg _
    calc etaL2QSup p.c mZ (fun pt => chartCoeff p.R p.raw pt +
            p.coord z 0 • chartCoeff p.R (p.inlet 0) pt +
            p.coord z 1 • chartCoeff p.R (p.inlet 1) pt) s
        ≤ etaL2QSup p.c mZ (fun pt => chartCoeff p.R p.raw pt +
            p.coord z 0 • chartCoeff p.R (p.inlet 0) pt) s +
          etaL2QSup p.c mZ (fun pt => p.coord z 1 • chartCoeff p.R (p.inlet 1) pt) s := e1
      _ ≤ (etaL2QSup p.c mZ (chartCoeff p.R p.raw) s +
            etaL2QSup p.c mZ (fun pt => p.coord z 0 • chartCoeff p.R (p.inlet 0) pt) s) +
          etaL2QSup p.c mZ (fun pt => p.coord z 1 • chartCoeff p.R (p.inlet 1) pt) s := by
            gcongr
      _ ≤ (ENNReal.ofReal Rr + ENNReal.ofReal |p.coord z 0| * ENNReal.ofReal Ri) +
          ENNReal.ofReal |p.coord z 1| * ENNReal.ofReal Ri := by
            exact add_le_add (add_le_add hrawE (e3.trans (mul_le_mul_right (hinE 0) _)))
              (e4.trans (mul_le_mul_right (hinE 1) _))
      _ = ENNReal.ofReal (Rr + |p.coord z 0| * Ri + |p.coord z 1| * Ri) := by
            rw [← ENNReal.ofReal_mul (hc0 0), ← ENNReal.ofReal_mul (hc0 1),
              ← ENNReal.ofReal_add hRr0 (mul_nonneg (hc0 0) hRi0),
              ← ENNReal.ofReal_add (add_nonneg hRr0 (mul_nonneg (hc0 0) hRi0))
                (mul_nonneg (hc0 1) hRi0)]
      _ ≤ ENNReal.ofReal ((2 * (|C1| + |C2|) + 2 * |C0| * |C3|) *
            x ^ (max (max k1 k2) k3 + k0) * T) := by
            apply ENNReal.ofReal_le_ofReal
            have hMx : ∀ i : Fin 2, |p.coord z i| * Ri ≤ |C0| * x ^ k0 * Ri := fun i =>
              mul_le_mul_of_nonneg_right (hM i) hRi0
            have := t9_final x T hx1 hTpos k1 k2 k3 k0 C1 C2 C3 C0 Rr Ri Ri le_rfl le_rfl le_rfl
            linarith [hMx 0, hMx 1]

end UnforcedLeray.Short.IIIa

end
