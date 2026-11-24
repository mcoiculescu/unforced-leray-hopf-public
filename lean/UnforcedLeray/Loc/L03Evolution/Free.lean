import UnforcedLeray.Blueprint.Localization.Linear
import UnforcedLeray.Units.B0418.Operator

/-!
# L3 helper: algebra and continuity of the free evolution `S₀`

`paper/main.tex` lines 292–298 (`loc:eq:free-evolution`, blueprint unit B0712) give
`S₀(s) f(y) = e^{s/2}[e^{h(e^s-1)Δ} f](e^{s/2} y)` on `X`, `L²_div → X` and `X → Z`. Step L3
(lines 299–306, B0713) uses its semigroup law. A `FreeEvolution` with `IsFreeEvolution h S`
is pinned to the compiled `AncientLocalization.freeEvolution` almost everywhere; since `H¹`
and `H²` elements are determined by their values (`H1.value_injective`,
`H2.value_injective`), the pointwise semigroup law of the compiled operator
(`B0418.freeEvolution_add`) transfers to the operators:

* `S0_zero`, `S0_comp_S0`, `S0_comp_S0L`, `S0L_comp_ιX`, `ιZ_comp_S0Z`, `S0Z_comp_S0`;
* strong continuity of `S₀ : L²_div → X` and `S₀ : X → Z` at positive times;
* the bounds of `IsFreeEvolution.bounds` in the `t^{-1/2}` form of the Volterra data;
* `ι_X(X)` is dense in `L²_div` (strong continuity of the compiled free evolution on `L²`,
  `B0418.tendsto_freeEvolution_sub_self`), and `ι_Z(Z)` is dense in `X` (`S₀(t) f → f`);
* `S0ZZ`: `S₀` on `Z` (`S₀(t) = S₀^{X→Z}(t) ι_Z` for `t > 0`, the identity at `t = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Loc.L03Evolution

open UnforcedLeray.Blueprint SobolevGraph
open UnforcedLeray.AncientLocalization (freeEvolution)

/-- An element of `X = H¹_div` is determined by its `L²` value. -/
theorem X_eq_of_ae {f g : X} (h : Xval f =ᵐ[volume] Xval g) : f = g := by
  have h1 : Xclass f = Xclass g := Lp.ext h
  exact Subtype.ext (H1.value_injective h1)

/-- An element of `Z = H²_div` is determined by its `L²` value. -/
theorem Z_eq_of_ae {f g : Z} (h : Zval f =ᵐ[volume] Zval g) : f = g := by
  have h1 : Zclass f = Zclass g := Lp.ext h
  exact Subtype.ext (H2.value_injective h1)

theorem ιZ_injective : Function.Injective ιZ := fun f g h => by
  apply Z_eq_of_ae
  have : Xval (ιZ f) = Xval (ιZ g) := by rw [h]
  exact EventuallyEq.of_eq this

theorem memLp_Xval (f : X) : MemLp (Xval f) 2 volume := Lp.memLp _

theorem memLp_Lval (F : L2div) : MemLp (Lval F) 2 volume := Lp.memLp _

/-- `C / √t = C t^{-1/2}` for `t > 0`. -/
theorem div_sqrt_eq_mul_rpow (C : ℝ) {t : ℝ} (ht : 0 < t) :
    C / Real.sqrt t = C * t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le, div_eq_mul_inv]

/-- Semigroup law of the compiled free evolution, through an a.e. representative. -/
theorem freeEvolution_comp_ae {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {F : SpatialField} (hF : MemLp F 2 volume) {G : SpatialField}
    (hG : G =ᵐ[volume] freeEvolution h b F) :
    freeEvolution h a G =ᵐ[volume] freeEvolution h (a + b) F :=
  (B0418.freeEvolution_congr_ae hG h a).trans
    (EventuallyEq.of_eq (B0418.freeEvolution_add hh ha hb (by norm_num) (by norm_num) hF))

section Free

variable {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S)
include hS

/-- `S₀(0) = 1` (line 293 at `s = 0`). -/
theorem S0_zero : S.S0 0 = ContinuousLinearMap.id ℝ X := by
  ext1 f
  rw [ContinuousLinearMap.id_apply]
  apply X_eq_of_ae
  have := hS.rep 0 le_rfl f
  rwa [AncientLocalization.freeEvolution_zero] at this

theorem S0_comp_S0 (hh : 0 ≤ h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (S.S0 a).comp (S.S0 b) = S.S0 (a + b) := by
  ext1 f
  apply X_eq_of_ae
  rw [ContinuousLinearMap.comp_apply]
  exact ((hS.rep a ha _).trans (freeEvolution_comp_ae hh ha hb (memLp_Xval f)
    (hS.rep b hb f))).trans (hS.rep (a + b) (by linarith) f).symm

theorem S0_comp_S0L (hh : 0 ≤ h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (S.S0 a).comp (S.S0L b) = S.S0L (a + b) := by
  ext1 F
  apply X_eq_of_ae
  rw [ContinuousLinearMap.comp_apply]
  exact ((hS.rep a ha _).trans (freeEvolution_comp_ae hh ha hb.le (memLp_Lval F)
    (hS.repL b hb F))).trans (hS.repL (a + b) (by linarith) F).symm

theorem S0L_comp_ιX {t : ℝ} (ht : 0 < t) : (S.S0L t).comp ιX = S.S0 t := by
  ext1 f
  apply X_eq_of_ae
  rw [ContinuousLinearMap.comp_apply]
  exact (hS.repL t ht (ιX f)).trans (hS.rep t ht.le f).symm

theorem ιZ_comp_S0Z {t : ℝ} (ht : 0 < t) : ιZ.comp (S.S0Z t) = S.S0 t := by
  ext1 f
  apply X_eq_of_ae
  rw [ContinuousLinearMap.comp_apply]
  exact (hS.repZ t ht f).trans (hS.rep t ht.le f).symm

theorem S0Z_comp_S0 (hh : 0 ≤ h) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (S.S0Z a).comp (S.S0 b) = S.S0Z (a + b) := by
  ext1 f
  apply Z_eq_of_ae
  rw [ContinuousLinearMap.comp_apply]
  exact ((hS.repZ a ha _).trans (freeEvolution_comp_ae hh ha.le hb (memLp_Xval f)
    (hS.rep b hb f))).trans (hS.repZ (a + b) (by linarith) f).symm

/-- Strong continuity of `S₀ : L²_div → X` at positive times. -/
theorem continuousOn_S0L (hh : 0 ≤ h) (F : L2div) :
    ContinuousOn (fun t => S.S0L t F) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hc : ContinuousAt (fun t => S.S0 (t - t₀ / 2) (S.S0L (t₀ / 2) F)) t₀ := by
    have h1 : ContinuousAt (fun u => S.S0 u (S.S0L (t₀ / 2) F)) (t₀ - t₀ / 2) :=
      (hS.strongly_continuous _).continuousAt (Ici_mem_nhds (by linarith))
    exact h1.comp (f := fun t : ℝ => t - t₀ / 2) (continuous_sub_right (t₀ / 2)).continuousAt
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds (half_lt_self ht₀')] with t ht
  have ht' : t₀ / 2 < t := ht
  rw [← ContinuousLinearMap.comp_apply, S0_comp_S0L hS hh (by linarith) (half_pos ht₀')]
  congr 2
  ring

/-- Strong continuity of `S₀ : X → Z` at positive times. -/
theorem continuousOn_S0Z (hh : 0 ≤ h) (f : X) :
    ContinuousOn (fun t => S.S0Z t f) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hc : ContinuousAt (fun t => S.S0Z (t₀ / 2) (S.S0 (t - t₀ / 2) f)) t₀ := by
    have h1 : ContinuousAt (fun u => S.S0 u f) (t₀ - t₀ / 2) :=
      (hS.strongly_continuous _).continuousAt (Ici_mem_nhds (by linarith))
    exact (S.S0Z (t₀ / 2)).continuous.continuousAt.comp
      (h1.comp (f := fun t : ℝ => t - t₀ / 2) (continuous_sub_right (t₀ / 2)).continuousAt)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds (half_lt_self ht₀')] with t ht
  have ht' : t₀ / 2 < t := ht
  rw [← ContinuousLinearMap.comp_apply, S0Z_comp_S0 hS hh (half_pos ht₀') (by linarith)]
  congr 2
  ring

/-- The bounds of `IsFreeEvolution` in the form used by the Volterra data. -/
theorem free_bounds : ∃ C : ℝ, 0 < C ∧ (∀ t, 0 ≤ t → ‖S.S0 t‖ ≤ C) ∧
    (∀ t, 0 < t → t ≤ 1 → ‖S.S0L t‖ ≤ C * t ^ (-(1 / 2 : ℝ))) ∧
    (∀ t, 0 < t → t ≤ 1 → ‖S.S0Z t‖ ≤ C * t ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC, h1, h2⟩ := hS.bounds
  refine ⟨C, hC, fun t ht => ?_, fun t ht ht1 => ?_, fun t ht ht1 => ?_⟩
  · refine (h1 t ht).trans (mul_le_of_le_one_right hC.le ?_)
    exact Real.exp_le_one_iff.mpr (by linarith)
  · rw [← div_sqrt_eq_mul_rpow C ht]
    exact (h2 t ht ht1).1
  · rw [← div_sqrt_eq_mul_rpow C ht]
    exact (h2 t ht ht1).2

/-- `ι_Z(Z)` is dense in `X`: `ι_Z S₀^{X→Z}(t) f = S₀(t) f → f` as `t → 0⁺`. -/
theorem denseRange_ιZ : DenseRange ιZ := by
  intro f
  have e : S.S0 0 f = f := by rw [S0_zero hS]; rfl
  have h0 := (hS.strongly_continuous f 0 (mem_Ici.mpr le_rfl)).tendsto
  rw [e] at h0
  have h1 : Tendsto (fun t => S.S0 t f) (𝓝[>] 0) (𝓝 f) :=
    h0.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : Tendsto (fun t => ιZ (S.S0Z t f)) (𝓝[>] 0) (𝓝 f) :=
    h1.congr' (eventually_nhdsWithin_of_forall fun t ht => by
      show S.S0 t f = ιZ (S.S0Z t f)
      rw [← ιZ_comp_S0Z hS ht]
      rfl)
  exact mem_closure_of_tendsto h2 (Eventually.of_forall fun t => mem_range_self _)

/-- `ι_X(X)` is dense in `L²_div`: `ι_X S₀^{L²→X}(t) F → F` in `L²` as `t → 0⁺`. -/
theorem denseRange_ιX : DenseRange ιX := by
  intro F
  have key : Tendsto (fun t => ‖ιX (S.S0L t F) - F‖) (𝓝[>] 0) (𝓝 0) := by
    have h0 := B0418.tendsto_freeEvolution_sub_self (ν := h) (p := 2) (by norm_num)
      (by norm_num) (memLp_Lval F)
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at h1
    have h2 := h1.mono_left (nhdsWithin_mono (0 : ℝ) (Ioi_subset_Ici_self (a := (0 : ℝ))))
    refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    show (eLpNorm (freeEvolution h t (Lval F) - Lval F) 2 volume).toReal =
      ‖Xclass (S.S0L t F) - Lclass F‖
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (Xclass (S.S0L t F)) (Lclass F), hS.repL t ht F]
      with x hx1 hx2
    rw [hx1]
    simp only [Pi.sub_apply]
    rw [← hx2]
    rfl
  have h2 : Tendsto (fun t => ιX (S.S0L t F)) (𝓝[>] 0) (𝓝 F) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr key
  exact mem_closure_of_tendsto h2 (Eventually.of_forall fun t => mem_range_self _)

end Free

/-! ## `S₀` on `Z` -/

/-- `S₀(t)` on `Z = H²_div`: `S₀^{X→Z}(t) ι_Z` for `t > 0`, the identity for `t ≤ 0`. -/
def S0ZZ (S : FreeEvolution) (t : ℝ) : Z →L[ℝ] Z :=
  if 0 < t then (S.S0Z t).comp ιZ else ContinuousLinearMap.id ℝ Z

theorem S0ZZ_of_pos (S : FreeEvolution) {t : ℝ} (ht : 0 < t) :
    S0ZZ S t = (S.S0Z t).comp ιZ := ite_eq_left ht

theorem S0ZZ_of_nonpos (S : FreeEvolution) {t : ℝ} (ht : t ≤ 0) :
    S0ZZ S t = ContinuousLinearMap.id ℝ Z := ite_eq_right (not_lt.mpr ht)

section FreeZ

variable {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S)
include hS

/-- `S₀` on `Z` is strongly continuous on `[0,1]`, given the strong continuity at `0`. -/
theorem continuousOn_S0ZZ (hh : 0 ≤ h)
    (hZc : ∀ g : Z, Tendsto (fun t => S.S0Z t (ιZ g)) (𝓝[>] 0) (𝓝 g)) (g : Z) :
    ContinuousOn (fun t => S0ZZ S t g) (Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    have h1 : ContinuousWithinAt (fun t => S0ZZ S t g) (Ioi 0) 0 := by
      show Tendsto (fun t => S0ZZ S t g) (𝓝[>] 0) (𝓝 (S0ZZ S 0 g))
      rw [S0ZZ_of_nonpos S le_rfl, ContinuousLinearMap.id_apply]
      exact (hZc g).congr' (eventually_nhdsWithin_of_forall fun t ht => by
        show S.S0Z t (ιZ g) = S0ZZ S t g
        rw [S0ZZ_of_pos S ht, ContinuousLinearMap.comp_apply])
    have h2 : ContinuousWithinAt (fun t => S0ZZ S t g) {0} 0 := continuousWithinAt_singleton
    refine (h1.union h2).mono fun t ht => ?_
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  · have hc : ContinuousAt (fun t => S.S0Z t (ιZ g)) t :=
      (continuousOn_S0Z hS hh (ιZ g)).continuousAt (Ioi_mem_nhds hpos)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [Ioi_mem_nhds hpos] with u hu
    rw [S0ZZ_of_pos S hu, ContinuousLinearMap.comp_apply]

theorem S0ZZ_comp_S0ZZ (hh : 0 ≤ h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (S0ZZ S a).comp (S0ZZ S b) = S0ZZ S (a + b) := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    rw [S0ZZ_of_nonpos S le_rfl, ContinuousLinearMap.id_comp, zero_add]
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0
    rw [S0ZZ_of_nonpos S le_rfl, ContinuousLinearMap.comp_id, add_zero]
  rw [S0ZZ_of_pos S ha0, S0ZZ_of_pos S hb0, S0ZZ_of_pos S (by linarith),
    ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc (S.S0Z a),
    ιZ_comp_S0Z hS hb0, S0Z_comp_S0 hS hh ha0 hb]

theorem S0ZZ_comp_S0Z (hh : 0 ≤ h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (S0ZZ S a).comp (S.S0Z b) = S.S0Z (a + b) := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    rw [S0ZZ_of_nonpos S le_rfl, ContinuousLinearMap.id_comp, zero_add]
  rw [S0ZZ_of_pos S ha0, ContinuousLinearMap.comp_assoc, ιZ_comp_S0Z hS hb,
    S0Z_comp_S0 hS hh ha0 hb.le]

theorem ιZ_S0ZZ {t : ℝ} (ht : 0 ≤ t) (g : Z) :
    ιZ (S0ZZ S t g) = S.S0 t (ιZ g) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    rw [S0ZZ_of_nonpos S le_rfl, S0_zero hS]
    rfl
  · rw [S0ZZ_of_pos S hpos, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply ιZ,
      ιZ_comp_S0Z hS hpos]

end FreeZ

end UnforcedLeray.Loc.L03Evolution
