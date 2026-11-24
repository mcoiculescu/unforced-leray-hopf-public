import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.TransInv

/-!
# Part II-b, task `PartII-b:T13/1/4/3/1/2` (`chmLocInt`): local integrability of a periodic
`L^r(cylMeas c)` function

Source: `the November 2 reference manuscript` (SP) lines 1933-1935.

Proof. Replace `u` by a measurable representative `v`.  Put `G = ‖v‖ₑ ^ r`; it is measurable and
a.e. `q`-periodic, and `∫⁻ G d cylMeas < ⊤`.  The `q`-strip integral `chmTIS c G b` does not depend on
`b` (`chmTI_const`), and `∫⁻ G d cylMeas` is `c⁻¹` times the strip integral.  A compact set lies in
a finite union of `q`-strips, so the `G`-integral over it is finite.  Hence `v ∈ L^r` on each compact
set, hence `L^1` on it (finite measure), and `u = v` a.e. gives local integrability.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal

/-- `cylMeas c` is absolutely continuous with respect to Lebesgue measure on `Coord`. -/
theorem chmL_cyl_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  intro s hs
  rw [chmTI_cyl_eq c, Measure.smul_apply, smul_eq_mul]
  have h1 : (volume : Measure Coord).restrict {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} s ≤
      volume s := Measure.restrict_apply_le _ _
  rw [hs] at h1
  rw [le_antisymm h1 zero_le, mul_zero]

/-- An a.e. equal modification of a `q`-periodic function is a.e. `q`-periodic. -/
theorem chmL_per {c : ℝ} {u v : Coord → ℂ} (hup : QPeriodicS c u) (hvu : u =ᵐ[volume] v) :
    ∀ᵐ x : Coord, v (qShift c x) = v x := by
  have hT := (measurePreserving_add_right (volume : Measure Coord)
    ((0 : ℝ), ((c : ℝ), (0 : ℝ)))).quasiMeasurePreserving
  have h1 : ∀ᵐ x : Coord, u (x + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) =
      v (x + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
    hT.ae (p := fun y => u y = v y) hvu
  filter_upwards [h1, hup, hvu] with x h1x hupx hvux
  have hq : x + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = qShift c x :=
    Prod.ext (by simp [qShift]) (Prod.ext (by simp [qShift]) (by simp [qShift]))
  rw [hq] at h1x
  rw [← h1x, hupx, hvux]

/-- The `q`-strips of length `n c` have integral `n` times the strip integral. -/
theorem chmL_sum {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞} (hG : Measurable G)
    (hGper : ∀ᵐ x : Coord, G (qShift c x) = G x) :
    ∀ n : ℕ, ∀ a : ℝ, ∫⁻ x, {x : Coord | x.2.1 ∈ Ico a (a + n * c)}.indicator G x
      = n * chmTIS c G a := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    have hn0 : (0 : ℝ) ≤ n * c := by positivity
    have hpq : a ≤ a + n * c := by linarith
    have hqr : a + n * c ≤ a + ((n + 1 : ℕ) : ℝ) * c := by push_cast; nlinarith
    have h2 : chmTIS c G (a + n * c) = chmTIS c G a := chmTI_const hc hG hGper _ _
    have e : a + ((n + 1 : ℕ) : ℝ) * c = a + n * c + c := by push_cast; ring
    have h3 : ∫⁻ x, {x : Coord | x.2.1 ∈ Ico (a + n * c) (a + ((n + 1 : ℕ) : ℝ) * c)}.indicator G x
        = chmTIS c G (a + n * c) := by
      unfold chmTIS
      rw [e]
    rw [chmTI_lint_split hG hpq hqr, ih a, h3, h2]
    simp only [Nat.cast_succ]
    ring

/-- A compact set lies in finitely many `q`-strips, so the `G`-integral over it is finite. -/
theorem chmL_bdd {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞} (hG : Measurable G)
    (hGper : ∀ᵐ x : Coord, G (qShift c x) = G x) (hT : chmTIS c G (-c / 2) < ⊤)
    {K : Set Coord} (hKc : IsCompact K) : ∫⁻ x, K.indicator G x < ⊤ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hKc.isBounded
  have hR : ∀ x ∈ K, |x.2.1| ≤ C := fun x hx =>
    calc |x.2.1| = ‖x.2.1‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x.2‖ := norm_fst_le x.2
      _ ≤ ‖x‖ := norm_snd_le x
      _ ≤ C := hC x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * C + 1) / c)
  have hnc : 2 * C + 1 ≤ n * c := by
    rw [div_lt_iff₀ hc] at hn
    linarith
  have hsub : K ⊆ {x : Coord | x.2.1 ∈ Ico (-C) (-C + n * c)} := by
    intro x hx
    obtain ⟨h1, h2⟩ := abs_le.1 (hR x hx)
    simp only [Set.mem_Ico]
    exact ⟨h1, by linarith⟩
  calc ∫⁻ x, K.indicator G x
      ≤ ∫⁻ x, {x : Coord | x.2.1 ∈ Ico (-C) (-C + n * c)}.indicator G x :=
        lintegral_mono fun x => indicator_le_indicator_of_subset hsub (fun _ => zero_le) x
    _ = n * chmTIS c G (-C) := chmL_sum hc hG hGper n (-C)
    _ < ⊤ := by
        rw [chmTI_const hc hG hGper (-C) (-c / 2)]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) hT

/-- The `q`-strip integral is finite when `∫⁻ G d cylMeas` is. -/
theorem chmL_fin {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞}
    (hcyl : ∫⁻ x, G x ∂(cylMeas c) < ⊤) : chmTIS c G (-c / 2) < ⊤ := by
  have hS : MeasurableSet {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} :=
    (measurable_fst.comp measurable_snd) measurableSet_Ico
  have hX : ∫⁻ x, {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)}.indicator G x < ⊤ := by
    rw [chmTI_cyl_eq c, lintegral_smul_measure, ← lintegral_indicator hS G] at hcyl
    have e : ∫⁻ x, {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)}.indicator G x
        = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ *
          ∫⁻ x, {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)}.indicator G x) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
        one_mul]
    rw [e]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcyl
  have hT0 : chmTIS c G (-c / 2) =
      ∫⁻ x, {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)}.indicator G x := by
    unfold chmTIS
    rw [show -c / 2 + c = c / 2 by ring]
  rw [hT0]
  exact hX

/-- **Leaf `PartII-b:T13/1/4/3/1/2`.** Local integrability of a `q`-periodic function in
`L^r(cylMeas c)`, `r > 1` (SP 1933-1935). -/
theorem chmLocInt : UnforcedLeray.Short.IIb.ChmLocInt := by
  intro c hc r hr u hup hum hun
  obtain ⟨v, hvs, hvu⟩ := hum
  have hv : Measurable v := hvs.measurable
  have hvper : ∀ᵐ x : Coord, v (qShift c x) = v x := chmL_per hup hvu
  have hr0 : (0 : ℝ) < r := by linarith
  have hpos : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hG : Measurable (fun x : Coord => ‖v x‖ₑ ^ r) := hv.enorm.pow_const r
  have hGper : ∀ᵐ x : Coord, (fun x : Coord => ‖v x‖ₑ ^ r) (qShift c x)
      = (fun x : Coord => ‖v x‖ₑ ^ r) x :=
    hvper.mono fun x hx => by simp only [hx]
  have hcyl : ∫⁻ x, ‖v x‖ₑ ^ r ∂(cylMeas c) < ⊤ := by
    have h2 : eLpNorm v (ENNReal.ofReal r) (cylMeas c) < ⊤ := by
      rw [← eLpNorm_congr_ae ((chmL_cyl_ac c).ae_eq hvu)]
      exact hun
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpos ENNReal.ofReal_ne_top] at h2
    rwa [ENNReal.toReal_ofReal hr0.le] at h2
  have hstrip : chmTIS c (fun x : Coord => ‖v x‖ₑ ^ r) (-c / 2) < ⊤ := chmL_fin hc hcyl
  have hKfin : ∀ K : Set Coord, IsCompact K → ∫⁻ x in K, ‖v x‖ₑ ^ r < ⊤ := by
    intro K hK
    rw [← lintegral_indicator hK.isClosed.measurableSet (fun x : Coord => ‖v x‖ₑ ^ r)]
    exact chmL_bdd hc hG hGper hstrip hK
  have hmem : ∀ K : Set Coord, IsCompact K → MemLp v (ENNReal.ofReal r) (volume.restrict K) := by
    intro K hK
    refine ⟨hv.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpos ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr0.le]
    exact hKfin K hK
  have hloc : ∀ K : Set Coord, IsCompact K → IntegrableOn u K volume := by
    intro K hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    have hint : Integrable v (volume.restrict K) :=
      (hmem K hK).integrable (ENNReal.one_le_ofReal.2 hr.le)
    exact hint.congr (ae_restrict_of_ae hvu.symm)
  exact locallyIntegrable_iff.2 hloc

end UnforcedLeray.Short.IIb

end
