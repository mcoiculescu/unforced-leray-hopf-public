import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound.Field

/-!
# `L^{q₀}` bound of the differentiated quadratic field on the period cell
(helper for `PartII-b:S1/1/2`, source
`the November 2 reference manuscript`, lines 2528-2534)

From the pointwise bound `|F| ≤ ∑_k (2U(|D²e| + |D²w|) + 2L|D_ke| + 2|D_kw|² + 2L|D_je| + 2|D_jw|²)`
(with `|u| ≤ U` a.e. and `|De| ≤ L`), the triangle inequality in `L^{q₀}` of the period cell gives
`‖F‖ ≤ c · (3(2U B_hh + 2U C_g + 4L B_de + 4K))` whenever each piece is bounded by `c` times the
corresponding constant.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.QuadBoundSub

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params rep stronglyMeasurable_rep)
open UnforcedLeray.Short.PartIIIb.Concrete (GEQDu GEQDdu GEQuadField phaseμ)
open UnforcedLeray.B0412 (q0E)

theorem eLpNorm_cmul {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {C : ℝ}
    (hC : 0 ≤ C) (f : α → ℝ) :
    eLpNorm (fun x => C * f x) p μ = ENNReal.ofReal C * eLpNorm f p μ := by
  have : (fun x => C * f x) = C • f := rfl
  rw [this, eLpNorm_const_smul, Real.enorm_of_nonneg hC]

theorem eLpNorm_six_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f1 f2 f3 f4 f5 f6 : α → ℝ}
    (h1 : AEStronglyMeasurable f1 μ) (h2 : AEStronglyMeasurable f2 μ)
    (h3 : AEStronglyMeasurable f3 μ) (h4 : AEStronglyMeasurable f4 μ)
    (h5 : AEStronglyMeasurable f5 μ) (h6 : AEStronglyMeasurable f6 μ) :
    eLpNorm (f1 + f2 + f3 + f4 + f5 + f6) p μ ≤
      eLpNorm f1 p μ + eLpNorm f2 p μ + eLpNorm f3 p μ + eLpNorm f4 p μ + eLpNorm f5 p μ +
        eLpNorm f6 p μ := by
  refine (eLpNorm_add_le ((((h1.add h2).add h3).add h4).add h5) h6 hp).trans ?_
  gcongr
  refine (eLpNorm_add_le (((h1.add h2).add h3).add h4) h5 hp).trans ?_
  gcongr
  refine (eLpNorm_add_le ((h1.add h2).add h3) h4 hp).trans ?_
  gcongr
  refine (eLpNorm_add_le (h1.add h2) h3 hp).trans ?_
  gcongr
  exact eLpNorm_add_le h1 h2 hp

theorem cmul_ofReal_add (c : ℝ≥0∞) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c * ENNReal.ofReal a + c * ENNReal.ofReal b = c * ENNReal.ofReal (a + b) := by
  rw [← mul_add, ENNReal.ofReal_add ha hb]

theorem ofReal_mul_cmul (c : ℝ≥0∞) {a b : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a * (c * ENNReal.ofReal b) = c * ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_mul ha]; ring

theorem cmul_ofReal_six (c : ℝ≥0∞) {t1 t2 t3 t4 t5 t6 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2)
    (h3 : 0 ≤ t3) (h4 : 0 ≤ t4) (h5 : 0 ≤ t5) (h6 : 0 ≤ t6) :
    c * ENNReal.ofReal t1 + c * ENNReal.ofReal t2 + c * ENNReal.ofReal t3 + c * ENNReal.ofReal t4 +
      c * ENNReal.ofReal t5 + c * ENNReal.ofReal t6 =
      c * ENNReal.ofReal (t1 + t2 + t3 + t4 + t5 + t6) := by
  rw [ENNReal.ofReal_add (p := t1 + t2 + t3 + t4 + t5) (by linarith) h6,
    ENNReal.ofReal_add (p := t1 + t2 + t3 + t4) (by linarith) h5,
    ENNReal.ofReal_add (p := t1 + t2 + t3) (by linarith) h4,
    ENNReal.ofReal_add (p := t1 + t2) (by linarith) h3, ENNReal.ofReal_add h1 h2]
  ring

/-- **`L^{q₀}` bound of the differentiated quadratic field.** -/
theorem quadField_eLpNorm_le (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period q0E)
    (h : Fin 3 → Fin 3 → Yq p.period q0E) (j : Fin 3)
    (he : ContDiff ℝ ∞ (p.eFun (p.coord z))) (c : ℝ≥0∞) {U L Bhh Bde Cg KM : ℝ}
    (hU0 : 0 ≤ U) (hL0 : 0 ≤ L) (hBhh : 0 ≤ Bhh) (hBde : 0 ≤ Bde) (hCg : 0 ≤ Cg) (hKM : 0 ≤ KM)
    (hU : ∀ᵐ x ∂(phaseμ p.period), ‖p.uOf z x‖ ≤ U)
    (hL : ∀ (k : Fin 3) (x : ℝ × UnforcedLeray.Space), ‖dy k (p.eFun (p.coord z)) x‖ ≤ L)
    (hhh : ∀ k : Fin 3, eLpNorm (dy k (dy j (p.eFun (p.coord z)))) q0E (phaseμ p.period) ≤
      c * ENNReal.ofReal Bhh)
    (hh : ∀ k : Fin 3, eLpNorm (fun x : ℝ × UnforcedLeray.Space => rep (h k j) x.1 x.2) q0E
      (phaseμ p.period) ≤ c * ENNReal.ofReal Cg)
    (hde : ∀ k : Fin 3, eLpNorm (dy k (p.eFun (p.coord z))) q0E (phaseμ p.period) ≤
      c * ENNReal.ofReal Bde)
    (hg2 : ∀ k : Fin 3, eLpNorm (fun x : ℝ × UnforcedLeray.Space => ‖rep (g k) x.1 x.2‖ ^ 2) q0E
      (phaseμ p.period) ≤ c * ENNReal.ofReal KM) :
    eLpNorm (GEQuadField p z g h j) q0E (phaseμ p.period) ≤
      c * ENNReal.ofReal (3 * (2 * U * Bhh + 2 * U * Cg + 2 * L * Bde + 2 * KM +
        2 * L * Bde + 2 * KM)) := by
  set μ := phaseμ p.period with hμ
  set e := p.eFun (p.coord z) with he_def
  have hq1 : (1 : ℝ≥0∞) ≤ q0E := Fact.out
  -- the six families
  let a : Fin 3 → ℝ × UnforcedLeray.Space → ℝ := fun k x => ‖dy k (dy j e) x‖
  let b : Fin 3 → ℝ × UnforcedLeray.Space → ℝ := fun k x => ‖rep (h k j) x.1 x.2‖
  let cc : Fin 3 → ℝ × UnforcedLeray.Space → ℝ := fun k x => ‖dy k e x‖
  let d : Fin 3 → ℝ × UnforcedLeray.Space → ℝ := fun k x => ‖rep (g k) x.1 x.2‖ ^ 2
  have ma : ∀ k, AEStronglyMeasurable (a k) μ := fun k =>
    (contDiff_dy (contDiff_dy he j) k).continuous.norm.aestronglyMeasurable
  have mb : ∀ k, AEStronglyMeasurable (b k) μ := fun k =>
    (stronglyMeasurable_rep (h k j)).norm.aestronglyMeasurable
  have mc : ∀ k, AEStronglyMeasurable (cc k) μ := fun k =>
    (contDiff_dy he k).continuous.norm.aestronglyMeasurable
  have md : ∀ k, AEStronglyMeasurable (d k) μ := fun k =>
    ((stronglyMeasurable_rep (g k)).norm.aestronglyMeasurable).pow 2
  let φ : Fin 3 → ℝ × UnforcedLeray.Space → ℝ := fun k =>
    (fun x => (2 * U) * a k x) + (fun x => (2 * U) * b k x) + (fun x => (2 * L) * cc k x) +
      (fun x => 2 * d k x) + (fun x => (2 * L) * cc j x) + (fun x => 2 * d j x)
  have mφ : ∀ k, AEStronglyMeasurable (φ k) μ := fun k =>
    (((((ma k).const_mul _).add ((mb k).const_mul _)).add ((mc k).const_mul _)).add
      ((md k).const_mul _)).add ((mc j).const_mul _) |>.add ((md j).const_mul _)
  -- pointwise a.e. bound
  have hpt : ∀ᵐ x ∂μ, ‖GEQuadField p z g h j x‖ ≤ (∑ k : Fin 3, φ k) x := by
    filter_upwards [hU] with x hx
    refine (norm_quadField_le p z g h j x).trans ?_
    rw [Finset.sum_apply]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := norm_Ddu_le p z g h k j x
    have h2 := norm_Du_sq_le p z g k x (hL k x)
    have h3 := norm_Du_sq_le p z g j x (hL j x)
    have hD0 : 0 ≤ ‖GEQDdu p z g h k j x‖ := norm_nonneg _
    have hu0 : 0 ≤ ‖p.uOf z x‖ := norm_nonneg _
    have h4 : ‖GEQDdu p z g h k j x‖ * ‖p.uOf z x‖ ≤
        U * (‖dy k (dy j e) x‖ + ‖rep (h k j) x.1 x.2‖) :=
      calc ‖GEQDdu p z g h k j x‖ * ‖p.uOf z x‖ ≤ ‖GEQDdu p z g h k j x‖ * U :=
            mul_le_mul_of_nonneg_left hx hD0
        _ ≤ (‖dy k (dy j e) x‖ + ‖rep (h k j) x.1 x.2‖) * U :=
            mul_le_mul_of_nonneg_right h1 hU0
        _ = U * (‖dy k (dy j e) x‖ + ‖rep (h k j) x.1 x.2‖) := by ring
    simp only [φ, a, b, cc, d, Pi.add_apply]
    linarith
  have hE1 : eLpNorm (GEQuadField p z g h j) q0E μ ≤ eLpNorm (∑ k : Fin 3, φ k) q0E μ :=
    eLpNorm_mono_ae_real hpt
  have hE2 : eLpNorm (∑ k : Fin 3, φ k) q0E μ ≤ ∑ k : Fin 3, eLpNorm (φ k) q0E μ :=
    eLpNorm_sum_le (fun k _ => mφ k) hq1
  set β : ℝ := 2 * U * Bhh + 2 * U * Cg + 2 * L * Bde + 2 * KM + 2 * L * Bde + 2 * KM with hβ
  have hE3 : ∀ k, eLpNorm (φ k) q0E μ ≤ c * ENNReal.ofReal β := by
    intro k
    have s6 := eLpNorm_six_le hq1 ((ma k).const_mul (2 * U)) ((mb k).const_mul (2 * U))
      ((mc k).const_mul (2 * L)) ((md k).const_mul 2) ((mc j).const_mul (2 * L))
      ((md j).const_mul 2)
    refine s6.trans ?_
    have hU2 : 0 ≤ 2 * U := by positivity
    have hL2 : 0 ≤ 2 * L := by positivity
    rw [eLpNorm_cmul hU2, eLpNorm_cmul hU2, eLpNorm_cmul hL2, eLpNorm_cmul (by norm_num : (0:ℝ) ≤ 2),
      eLpNorm_cmul hL2, eLpNorm_cmul (by norm_num : (0:ℝ) ≤ 2)]
    have ea : eLpNorm (a k) q0E μ ≤ c * ENNReal.ofReal Bhh := by
      simp only [a]; rw [eLpNorm_norm]; exact hhh k
    have eb : eLpNorm (b k) q0E μ ≤ c * ENNReal.ofReal Cg := by
      simp only [b]; rw [eLpNorm_norm]; exact hh k
    have ec : ∀ m, eLpNorm (cc m) q0E μ ≤ c * ENNReal.ofReal Bde := by
      intro m; simp only [cc]; rw [eLpNorm_norm]; exact hde m
    have ed : ∀ m, eLpNorm (d m) q0E μ ≤ c * ENNReal.ofReal KM := fun m => hg2 m
    calc ENNReal.ofReal (2 * U) * eLpNorm (a k) q0E μ +
          ENNReal.ofReal (2 * U) * eLpNorm (b k) q0E μ +
          ENNReal.ofReal (2 * L) * eLpNorm (cc k) q0E μ +
          ENNReal.ofReal 2 * eLpNorm (d k) q0E μ +
          ENNReal.ofReal (2 * L) * eLpNorm (cc j) q0E μ +
          ENNReal.ofReal 2 * eLpNorm (d j) q0E μ
        ≤ ENNReal.ofReal (2 * U) * (c * ENNReal.ofReal Bhh) +
          ENNReal.ofReal (2 * U) * (c * ENNReal.ofReal Cg) +
          ENNReal.ofReal (2 * L) * (c * ENNReal.ofReal Bde) +
          ENNReal.ofReal 2 * (c * ENNReal.ofReal KM) +
          ENNReal.ofReal (2 * L) * (c * ENNReal.ofReal Bde) +
          ENNReal.ofReal 2 * (c * ENNReal.ofReal KM) := by
          gcongr
          · exact ec k
          · exact ed k
          · exact ec j
          · exact ed j
      _ = c * ENNReal.ofReal β := by
          rw [ofReal_mul_cmul c hU2, ofReal_mul_cmul c hU2, ofReal_mul_cmul c hL2,
            ofReal_mul_cmul c (by norm_num : (0:ℝ) ≤ 2), hβ]
          exact cmul_ofReal_six c (by positivity) (by positivity) (by positivity) (by positivity)
            (by positivity) (by positivity)
  have hβ0 : 0 ≤ β := by positivity
  calc eLpNorm (GEQuadField p z g h j) q0E μ ≤ ∑ k : Fin 3, eLpNorm (φ k) q0E μ := hE1.trans hE2
    _ ≤ ∑ _k : Fin 3, c * ENNReal.ofReal β := Finset.sum_le_sum fun k _ => hE3 k
    _ = c * ENNReal.ofReal (3 * β) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
        simp only [Nat.cast_ofNat, ENNReal.ofReal_ofNat]
        ring

end UnforcedLeray.Short.IIb.QuadBoundSub
