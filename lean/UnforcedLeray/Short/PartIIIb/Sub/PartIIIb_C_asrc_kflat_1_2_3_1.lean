import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3

/-!
# Decomposition of `tfkShortAll` (source 2836-2860, 3020-3022, 3064-3094, 3228-3240)

Source: `the November 2 reference manuscript`.

`tfkShortAll_of` derives `TFKShortAll m` from

  `PartIII-a:T21`),

* `TFKKcEmbed m`: the embedding `‖K_c ξ‖₂ ≤ C ‖J_a⁻¹ ξ‖_{X_{m,d}}`, `d = c/√a`
  (`eq:ct-embeddings` 3228-3240 at `d`, together with the scaling relation between `K_c` and `K_d`),
* `TFKDatumNorm m`: the finite norm comparison of the datum at the clock `a(1.1/ν) = 2.1`
  (`‖J_a⁻¹ w‖_{X_{m,d}} ≤ C ‖w‖_{X_{m,c}}`, constants may depend on `ν`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- `‖K_c ξ‖₂ ≤ C ‖J_a⁻¹ ξ‖_{X_{m,c/√a}}` for `1 ≤ a ≤ ν⁻¹`, `c = ν⁻²`, `ξ ∈ X_{m,c}`
(source 3228-3240 `eq:ct-embeddings` with the dilation `K_c = J` relation; `C` may depend on `ν`). -/
def TFKKcEmbed (m : ℝ) [Fact (1 < m)] : Prop :=
  8 < m → ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ c : ℝ, c = ν ^ (-2 : ℝ) → ∀ [Fact (0 < c)],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 1 ≤ a → a ≤ ν⁻¹ → ∀ ξ : Xmc c m,
      ENNReal.ofReal ‖kcLp ξ‖ ≤
        ENNReal.ofReal C * UnforcedLeray.Short.IIIa.xNorm (UnforcedLeray.Short.IIIa.cellLen c a) m
          (UnforcedLeray.Short.IIIa.JscaleInv a (xFn ξ))

/-- `‖J_a⁻¹ w‖_{X_{m,c/√a}} ≤ C ‖w‖_{X_{m,c}}` at the fixed clock `a = 1 + ν·(1.1/ν)`. -/
def TFKDatumNorm (m : ℝ) [Fact (1 < m)] : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, c = ν ^ (-2 : ℝ) → ∀ [Fact (0 < c)],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Xmc c m,
      UnforcedLeray.Short.IIIa.xNorm
          (UnforcedLeray.Short.IIIa.cellLen c (UnforcedLeray.Short.IIIa.clockA ν (11 / 10 / ν))) m
          (UnforcedLeray.Short.IIIa.JscaleInv (UnforcedLeray.Short.IIIa.clockA ν (11 / 10 / ν))
            (xFn w)) ≤ ENNReal.ofReal (C * ‖w‖)

theorem exists_bound_clock (k lam C θ0 b : ℝ) (hb : 0 < b) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ θ ∈ Icc b θ0,
      C * Real.exp (lam * (θ0 - θ)) * (θ0 / θ) ^ k ≤ E := by
  have hc : ContinuousOn (fun θ : ℝ => C * Real.exp (lam * (θ0 - θ)) * (θ0 / θ) ^ k) (Icc b θ0) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
    · refine ContinuousOn.rpow_const (continuousOn_const.div continuousOn_id ?_) ?_
      · intro x hx; exact (hb.trans_le hx.1).ne'
      · intro x hx
        exact Or.inl (div_ne_zero (hb.trans_le (hx.1.trans hx.2)).ne' (hb.trans_le hx.1).ne')
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, fun θ hθ => ?_⟩
  exact ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB θ hθ)).trans (le_max_left _ _)

/-- The short range at one `ν`, after identifying `c = ν^(-2)`. -/
theorem tfkShort_aux (m : ℝ) [Fact (1 < m)] (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hP : ∃ P, UnforcedLeray.Blueprint.Planar.IsPlanarReference P)
    (h2 : TFKKcEmbed m) (h3 : TFKDatumNorm m) (h8 : 8 < m) :
    ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧ TFKShort m b ν₀ := by
  obtain ⟨P, hPref⟩ := hP
  obtain ⟨b₀, hb₀⟩ := hLF P hPref m h8
  refine ⟨max b₀ 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨C, ν₁, hν₁, hC⟩ := hb₀ b ((le_max_left _ _).trans hb)
  refine ⟨min ν₁ 1, lt_min hν₁ one_pos, ?_⟩
  intro κ ν hν hle tr hbuc FI
  have hνa : ν ≤ ν₁ := hle.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hle.trans (min_le_right _ _)
  have hcOf : cOf ν = ν ^ (-2 : ℝ) := by
    rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI : FlatInstData κ ν c m tr),
      ∃ C' : ℝ, ∀ u : ℝ, 11 / 10 / ν ≤ u → u ≤ UnforcedLeray.Short.IIIa.coreEnd ν b →
        ∀ w : Xmc c m, ‖kcLp (FI.ev.U u (11 / 10 / ν) w)‖ ≤ C' * ‖w‖ := by
    intro c hc hfact tr hbuc FI
    subst hc
    obtain ⟨-, hLong⟩ := hC ν ⟨hν, hνa⟩ tr hbuc
    obtain ⟨K, hK0, hK⟩ := h2 h8 ν hν hν1 _ rfl
    obtain ⟨D, hD0, hD⟩ := h3 ν hν _ rfl
    set t0 : ℝ := 11 / 10 / ν with ht0
    have ht0nn : 0 ≤ t0 := by positivity
    set θ0 := UnforcedLeray.Short.IIIa.clockTheta ν t0 with hθ0
    obtain ⟨E, hE0, hE⟩ := exists_bound_clock P.kappa.re P.eigenvalue.re C θ0 b hbpos
    refine ⟨K * E * D, fun u hu1 hu2 w => ?_⟩
    have hu0 : 0 ≤ u := ht0nn.trans hu1
    have h1 : ν * u ≤ (ν * b)⁻¹ - 1 := by
      have := mul_le_mul_of_nonneg_left hu2 hν.le
      rwa [UnforcedLeray.Short.IIIa.coreEnd, mul_inv_cancel_left₀ hν.ne'] at this
    have ha1 : 1 ≤ UnforcedLeray.Short.IIIa.clockA ν u := by
      simp only [UnforcedLeray.Short.IIIa.clockA]; nlinarith [mul_nonneg hν.le hu0]
    have hνb : ν ≤ ν * b := by nlinarith
    have hale : UnforcedLeray.Short.IIIa.clockA ν u ≤ ν⁻¹ := by
      have : 1 + ν * u ≤ (ν * b)⁻¹ := by linarith
      exact this.trans (inv_anti₀ hν hνb)
    have hapos : 0 < UnforcedLeray.Short.IIIa.clockA ν u := one_pos.trans_le ha1
    have hθb : b ≤ UnforcedLeray.Short.IIIa.clockTheta ν u := by
      unfold UnforcedLeray.Short.IIIa.clockTheta
      rw [le_inv_comm₀ hbpos (mul_pos hν hapos)]
      have h4 : 1 + ν * u ≤ (ν * b)⁻¹ := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hν.le
      have h6 : ν * (ν * b)⁻¹ = b⁻¹ := by field_simp
      exact (show ν * (1 + ν * u) ≤ b⁻¹ from h5.trans_eq h6)
    have hθu : UnforcedLeray.Short.IIIa.clockTheta ν u ≤ θ0 := by
      have ha0 : 0 < UnforcedLeray.Short.IIIa.clockA ν t0 := by
        simp only [UnforcedLeray.Short.IIIa.clockA]; nlinarith [mul_nonneg hν.le ht0nn]
      unfold UnforcedLeray.Short.IIIa.clockTheta
      refine inv_anti₀ (mul_pos hν ha0) (mul_le_mul_of_nonneg_left ?_ hν.le)
      simp only [UnforcedLeray.Short.IIIa.clockA]
      nlinarith
    obtain ⟨u', hu'⟩ := FI.ev.flow t0 ht0nn w
    have hLF1 := hLong t0 u ht0nn hu1 hθb (xFn w) (xFn_memLp w) (xFn_zeroCirc w) _ _ hu'
    have hθpos : 0 < UnforcedLeray.Short.IIIa.clockTheta ν u := hbpos.trans_le hθb
    have hEb := hE _ ⟨hθb, hθu⟩
    have hstep1 := hK _ ha1 hale (FI.ev.U u t0 w)
    have hstep2 := hD w
    have hcalc : ENNReal.ofReal ‖kcLp (FI.ev.U u t0 w)‖ ≤ ENNReal.ofReal (K * E * D * ‖w‖) := by
      calc ENNReal.ofReal ‖kcLp (FI.ev.U u t0 w)‖
          ≤ ENNReal.ofReal K * UnforcedLeray.Short.IIIa.xNorm _ m
              (UnforcedLeray.Short.IIIa.JscaleInv _ (xFn (FI.ev.U u t0 w))) := hstep1
        _ ≤ ENNReal.ofReal K * (ENNReal.ofReal E * ENNReal.ofReal (D * ‖w‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ (bot_le)
            refine hLF1.trans (mul_le_mul' ?_ hstep2)
            exact ENNReal.ofReal_le_ofReal hEb
        _ = ENNReal.ofReal (K * E * D * ‖w‖) := by
            rw [← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_mul hK0]
            congr 1; ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  exact key (cOf ν) hcOf tr hbuc FI

/-- **`tfkShortAll`** from the long forward estimate, a planar reference and the two norm
comparisons (source 2836-2860, 3020-3022, 3228-3240). -/
theorem tfkShortAll_of (m : ℝ) [Fact (1 < m)] (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hP : ∃ P, UnforcedLeray.Blueprint.Planar.IsPlanarReference P)
    (h2 : TFKKcEmbed m) (h3 : TFKDatumNorm m) : TFKShortAll m :=
  fun h8 => tfkShort_aux m hLF hP h2 h3 h8

end UnforcedLeray.Short.PartIIIb.Concrete
